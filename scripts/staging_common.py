"""Repository engineering helpers. No scientific verifier source is modified."""
from pathlib import Path, PurePosixPath
import hashlib
import io
import json
import os
import re
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def load(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))


def save(path, data):
    Path(path).write_text(json.dumps(data, indent=2, ensure_ascii=False)+'\n', encoding='utf-8')


def safe_relative(name):
    p = PurePosixPath(name)
    require(bool(name) and not p.is_absolute() and '..' not in p.parts
            and '\\' not in name and ':' not in name, 'Unsafe relative path: '+name)
    return p


def manifest_entries(text):
    rows = {}
    for line in text.splitlines():
        if not line.strip():
            continue
        match = re.fullmatch(r'([0-9a-f]{64})  (.+)', line)
        require(match is not None, 'Malformed SHA-256 manifest line')
        expected, name = match.groups()
        safe_relative(name)
        require(name not in rows, 'Duplicate manifest entry: '+name)
        rows[name] = expected
    require(bool(rows), 'Empty manifest')
    return rows


def verify_manifest(root, manifest):
    root = Path(root).resolve()
    rows = manifest_entries(Path(manifest).read_text(encoding='utf-8'))
    for name, expected in rows.items():
        path = (root/name).resolve()
        require(path.is_relative_to(root) and path.is_file() and not (root/name).is_symlink(),
                'Missing/unsafe manifest file: '+name)
        require(digest(path.read_bytes()) == expected, 'Hash mismatch: '+name)
    return rows


def unpack(data, strip_root=False):
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        names = archive.namelist()
        require(len(names) == len(set(names)), 'Duplicate ZIP members')
        require(archive.testzip() is None, 'ZIP CRC failure')
        files = {}
        for entry in archive.infolist():
            safe_relative(entry.filename.rstrip('/'))
            require((entry.external_attr >> 16) & 0o170000 != 0o120000, 'ZIP symlink')
            if not entry.is_dir():
                files[entry.filename] = archive.read(entry)
    if strip_root:
        prefix = next(iter(files)).split('/')[0]+'/'
        require(all(name.startswith(prefix) for name in files), 'Expected one archive root')
        files = {name[len(prefix):]: data for name,data in files.items()}
    return files


def materialize(files, root):
    root = Path(root).resolve()
    for name, data in files.items():
        safe_relative(name)
        path = root/name
        require(path.resolve().is_relative_to(root), 'Extraction escapes temporary root')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)


def byte_manifest(files, key):
    rows = manifest_entries(files[key].decode('utf-8'))
    for name, expected in rows.items():
        require(name in files and digest(files[name]) == expected, 'Nested hash mismatch: '+name)
    return len(rows)


def verify_repo(private=None):
    anchors = load(ROOT/'provenance/INPUT_ANCHORS.json')
    copies = load(ROOT/'provenance/COPY_MAP.json')
    for row in copies:
        safe_relative(row['path'])
        require(digest((ROOT/row['path']).read_bytes()) == row['sha256'], 'Changed copy: '+row['path'])
    public_assets = verify_manifest(ROOT/'release_assets', ROOT/'release_assets/RELEASE_ASSETS.sha256')
    actual = {p.name for p in (ROOT/'release_assets').iterdir() if p.is_file()}-{'RELEASE_ASSETS.sha256'}
    require(actual == set(public_assets), 'Public release-asset coverage mismatch')
    payload = unpack((ROOT/'release_assets/v3-reproduction-view.zip').read_bytes())
    byte_manifest(payload, 'VIEW_MANIFEST.sha256')
    expected_payload = {p.relative_to(ROOT/'src/frozen').as_posix():p.read_bytes()
                        for p in (ROOT/'src/frozen').rglob('*') if p.is_file()}
    require({n:d for n,d in payload.items() if n!='VIEW_MANIFEST.sha256'} == expected_payload,
            'Curated archive differs from byte-identical source view')
    source_zip = unpack((ROOT/'release_assets/paper-source.zip').read_bytes())
    expected_sources = {p.relative_to(ROOT/'paper').as_posix():p.read_bytes()
                        for p in (ROOT/'paper').rglob('*') if p.is_file()
                        and (p.suffix == '.tex' or p.name == 'references.bib')}
    require(source_zip == expected_sources, 'Paper source ZIP mismatch')
    require((ROOT/'release_assets/manuscript.pdf').read_bytes() == (ROOT/'paper/main.pdf').read_bytes(),
            'Staged PDF copies differ')
    private_rows = None
    if private is not None:
        private = Path(private).resolve()
        require(not private.is_relative_to(ROOT), 'Private assets must remain outside public repository')
        manifest = private/'PRIVATE_ASSETS.sha256'
        require(digest(manifest.read_bytes()) == anchors['private_manifest_sha256'], 'Private manifest identity changed')
        require(manifest.read_bytes() == (ROOT/'provenance/PRIVATE_ASSETS.sha256').read_bytes(),
                'Private manifest mirror mismatch')
        private_rows = verify_manifest(private, manifest)
        actual = {p.relative_to(private).as_posix() for p in private.rglob('*') if p.is_file()}-{'PRIVATE_ASSETS.sha256'}
        require(actual == set(private_rows), 'Private asset coverage mismatch')
        for name,key in [('Krylov_Paper_Draft.zip','input_paper_sha256'),
                         ('Krylov_Codex_COMPLETE_INPUT_BUNDLE_2026-09-23.zip','input_bundle_sha256'),
                         ('Krylov_PRL_WORK_FREEZE_2026-09-23_v3.zip','v3_sha256')]:
            require(private_rows[name] == anchors[key], 'Input anchor mismatch: '+name)
    return {'status':'PASS','byte_identical_copies':len(copies),'public_assets':len(public_assets),
            'private_assets':len(private_rows) if private_rows else None,
            'curated_view_matches_sources':True,'paper_source_archive_matches':True}


def output_directory(given, label, private=None):
    from datetime import datetime, timezone
    p = Path(given).resolve() if given else ROOT/'.local'/(
        label+'-'+datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'))
    if p.is_relative_to(ROOT):
        require(p.is_relative_to(ROOT/'.local') and p != ROOT/'.local', 'Outputs inside the repository must be under .local/')
    else:
        require(not ROOT.is_relative_to(p), 'Output cannot contain repository')
    if private:
        pr = Path(private).resolve()
        require(not p.is_relative_to(pr) and not pr.is_relative_to(p), 'Output overlaps private assets')
    require(not p.exists() or not any(p.iterdir()), 'Use a new/empty output directory: '+str(p))
    p.mkdir(parents=True, exist_ok=True)
    return p


def child_environment():
    env = os.environ.copy()
    env.update(OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1', MKL_NUM_THREADS='1',
               PYTHONHASHSEED='0', PYTHONDONTWRITEBYTECODE='1', PYTHONUTF8='1', PYTHONIOENCODING='utf-8')
    env.pop('PYTHONOPTIMIZE', None)
    return env


def check_snapshot():
    snapshot = load(ROOT/'paper/checks/REVIEWED_CONTENT.json')
    source_hashes = load(ROOT/'provenance/V3_SOURCE_HASHES.json')
    for row in snapshot['section_files']:
        data = (ROOT/'paper'/row['path']).read_text(encoding='utf-8').encode()
        require(digest(data) == row['sha256'], 'Manuscript changed since review: '+row['path'])
    for row in snapshot['displays']+snapshot['theorems']:
        for source in row['sources']:
            require(source_hashes[source['path']] == source['sha256'], 'Reviewed V3 source identity mismatch')
    return {'status':'PASS','reviewed_source_files_unchanged':len(snapshot['section_files']),
            'displays':len(snapshot['displays']),'formal_statements':len(snapshot['theorems']),
            'scope_lines':len(snapshot['quantifier_inventory']),
            'limit':'Replays the existing correspondence snapshot; not a new semantic or release-level claim audit.'}
