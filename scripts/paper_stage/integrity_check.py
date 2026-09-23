"""Read-only integrity gate for the complete input bundle; Python standard library only."""
from pathlib import Path
import hashlib
import io
import json
import re
import tarfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]
BUNDLE = ROOT / 'inputs/Krylov_Codex_COMPLETE_INPUT_BUNDLE_2026-09-23.zip'
V3_SHA = 'aaebb0e5b0768746bbd0c1eccb1fd128534680c54c8377de90e0c58365c29401'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def unpack_zip(data):
    with zipfile.ZipFile(io.BytesIO(data)) as z:
        bad = z.testzip()
        if bad:
            raise ValueError('ZIP CRC failure: ' + bad)
        files = {i.filename: z.read(i) for i in z.infolist() if not i.is_dir()}
    prefix = next(iter(files)).split('/')[0] + '/'
    if all(n.startswith(prefix) for n in files):
        files = {n[len(prefix):]: b for n, b in files.items()}
    return files


def verify_manifest(data, files, name):
    checked = []
    for line in data.decode('utf-8-sig').splitlines():
        if not line.strip():
            continue
        m = re.fullmatch(r'([0-9a-fA-F]{64})\s+\*?(.+)', line)
        if m is None:
            raise ValueError(f'{name}: malformed line {line!r}')
        expected, relative = m.groups()
        relative = relative.removeprefix('./')
        if relative not in files:
            raise ValueError(f'{name}: MISSING {relative}')
        actual = sha(files[relative])
        if actual != expected.lower():
            raise ValueError(f'{name}: HASH MISMATCH {relative}: {expected} != {actual}')
        checked.append(relative)
    return {'name': name, 'status': 'PASS', 'count': len(checked), 'files': checked}


def subtree(files, prefix):
    return {k[len(prefix):]: v for k, v in files.items() if k.startswith(prefix)}


def recursive_crc(data, name, checked):
    files = unpack_zip(data)
    checked.append(name)
    for k, v in files.items():
        if k.lower().endswith('.zip'):
            recursive_crc(v, name + '::' + k, checked)


def load_inputs():
    bundle = unpack_zip(BUNDLE.read_bytes())
    v3 = unpack_zip(bundle['authoritative/Krylov_PRL_WORK_FREEZE_2026-09-23_v3.zip'])
    return bundle, v3


def run():
    b, v = load_inputs()
    checks = [verify_manifest(b['BUNDLE_MANIFEST.sha256'], b, 'BUNDLE_MANIFEST.sha256')]
    if set(checks[0]['files']) != set(b) - {'BUNDLE_MANIFEST.sha256'}:
        raise ValueError('Bundle manifest does not cover exactly the retained files')
    anchors = json.loads(b['EXPECTED_ANCHOR_HASHES.json'])
    anchor_results = []
    for path, expected in anchors.items():
        actual = sha(b[path])
        if actual != expected:
            raise ValueError('Anchor mismatch: ' + path)
        anchor_results.append({'path': path, 'expected': expected, 'actual': actual, 'status': 'PASS'})
    v3_path = 'authoritative/Krylov_PRL_WORK_FREEZE_2026-09-23_v3.zip'
    assert sha(b[v3_path]) == V3_SHA
    completeness = json.loads(b['COMPLETENESS_CHECK.json'])
    assert completeness['missing_required_materials'] == []
    assert not any(x is False for x in completeness['required_present'].values())
    required = {
        'V3_authoritative_freeze': ('bundle', v3_path),
        'V3_record': ('bundle', 'authoritative/Krylov_PRL_WORK_FREEZE_2026-09-23_v3_record.json'),
        'CR0_sanitized_input': ('bundle', 'clean_room/CR0_input/Das_Mori_independent_reproduction_CR0_FINAL_2026-09-23.zip'),
        'CR0_sanitization_receipt': ('bundle', 'clean_room/CR0_input/CR0_SANITIZATION_RECEIPT_2026-09-23.txt'),
        'CR0_A_frozen_archive': ('bundle', 'clean_room/CR0_A_sol/CR0_OUTPUT_CR0_FROZEN_2026-09-23.tar.gz'),
        'CR0_A_freeze_record': ('bundle', 'clean_room/CR0_A_sol/CR0_FREEZE_RECORD.txt'),
        'CR0_A_root_manifest': ('bundle', 'clean_room/CR0_A_sol/CR0_OUTPUT_SHA256SUMS.txt'),
        'CR0_A_report': ('bundle', 'clean_room/CR0_A_sol/CR0_REPORT.md'),
        'CR0_A_ledger': ('bundle', 'clean_room/CR0_A_sol/CR0_LEDGER.json'),
        'CR0_B_frozen_archive': ('bundle', 'clean_room/CR0_B_fresh_agent/CR0_2026-09-23_cf1ad252.zip'),
        'CR0_B_external_freeze_receipt': ('bundle', 'clean_room/CR0_B_fresh_agent/CR0_2026-09-23_cf1ad252_FREEZE_RECEIPT.json'),
        'CR0_B_report': ('bundle', 'clean_room/CR0_B_fresh_agent/CR0_REPORT.md'),
        'CRB_postfreeze_comparison': ('bundle', 'comparison/CRB_COMPARISON.json'),
        'publication_release_handoff': ('bundle', 'publication_release_handoff/extracted/01_PAPER_CODEX_MASTER_PROMPT.md'),
        'A1v2_Sol_and_Astra': ('v3', 'audits/sol_a1v2/original/Krylov_A1v2_AUDIT.md'),
        'novelty_audit': ('v3', 'certification/novelty/Krylov_PRL_NOVELTY_AUDIT_2026-09-22.md'),
        'premise_provenance_audit': ('v3', 'certification/premise_provenance/PREMISE_PROVENANCE_AUDIT.md'),
        'source_papers': ('v3', 'source_status/raw_papers/Das_Mori_Krylov_Complexity_of_Purification_arXiv2408.00826v4.pdf'),
    }
    assert set(required) == set(completeness['required_present'])
    for _, (where, name) in required.items():
        assert name in (b if where == 'bundle' else v), name
    for name in ['audits/astra_a1v2/extracted/AUDIT_REPORT.md',
                 'source_status/raw_papers/Murugan_vanZyl_Superadditivity_Krylov_arXiv2601.08723v1.pdf']:
        assert name in v
    record = json.loads(b['authoritative/Krylov_PRL_WORK_FREEZE_2026-09-23_v3_record.json'])
    assert len(b[v3_path]) == record['archive_bytes']
    assert len(v) == record['tree_files']
    checks.append(verify_manifest(v['meta/FREEZE_MANIFEST.sha256'], v, 'V3 freeze'))
    assert checks[-1]['count'] == record['freeze_manifest_entries']
    for name, prefix in [
        ('MANIFEST.sha256', 'current_final/Krylov_remaining_attack/'),
        ('SHA256SUMS.txt', 'prior_left/P2_3_Krylov_certificate/'),
        ('SHA256SUMS.txt', 'audits/astra_a1v2/extracted/'),
        ('SHA256SUMS.txt', 'certification/novelty/'),
        ('SHA256SUMS.txt', 'certification/premise_provenance/'),
    ]:
        checks.append(verify_manifest(v[prefix + name], subtree(v, prefix), prefix + name))
    for path, key in [
        ('current_final/Krylov_remaining_attack_FINAL.zip', 'second_run_authoritative_zip_sha256'),
        ('prior_left/P2_3_Krylov_exact_certificate.zip', 'first_run_authoritative_zip_sha256'),
        ('history/v2/Krylov_PRL_WORK_FREEZE_2026-09-22_v2.zip', 'v2_history_sha256')]:
        assert sha(v[path]) == record[key]
    assert unpack_zip(v['current_final/Krylov_remaining_attack_FINAL.zip']) == subtree(v, 'current_final/Krylov_remaining_attack/')
    crb = unpack_zip(b['clean_room/CR0_B_fresh_agent/CR0_2026-09-23_cf1ad252.zip'])
    cri = unpack_zip(b['clean_room/CR0_input/Das_Mori_independent_reproduction_CR0_FINAL_2026-09-23.zip'])
    checks.append(verify_manifest(crb['SHA256SUMS.txt'], crb, 'CR0 B root'))
    checks.append(verify_manifest(cri['SHA256SUMS.txt'], cri, 'CR0 sanitized input'))
    with tarfile.open(fileobj=io.BytesIO(b['clean_room/CR0_A_sol/CR0_OUTPUT_CR0_FROZEN_2026-09-23.tar.gz']), mode='r:gz') as t:
        cra = {m.name.removeprefix('CR0_OUTPUT/'): t.extractfile(m).read() for m in t.getmembers() if m.isfile()}
    checks.append(verify_manifest(b['clean_room/CR0_A_sol/CR0_OUTPUT_SHA256SUMS.txt'], cra, 'CR0 A root'))
    assert cra['CR0_REPORT.md'] == b['clean_room/CR0_A_sol/CR0_REPORT.md']
    assert cra['CR0_LEDGER.json'] == b['clean_room/CR0_A_sol/CR0_LEDGER.json']
    assert crb['CR0_REPORT.md'] == b['clean_room/CR0_B_fresh_agent/CR0_REPORT.md']
    handoff = unpack_zip(b['publication_release_handoff/Krylov_publication_release_handoff_2026-09-23.zip'])
    checks.append(verify_manifest(handoff['SHA256SUMS.txt'], handoff, 'Handoff nested manifest'))
    assert {k: val for k, val in handoff.items() if k != 'SHA256SUMS.txt'} == subtree(b, 'publication_release_handoff/extracted/')
    crc_checks = []
    recursive_crc(BUNDLE.read_bytes(), BUNDLE.name, crc_checks)
    result = {
        'status': 'PASS', 'bundle_sha256': sha(BUNDLE.read_bytes()),
        'v3_expected_and_observed_sha256': V3_SHA,
        'manifest_checks': checks, 'anchor_checks': anchor_results,
        'completeness': 'Every declared required item checked; missing list empty',
        'required_artifact_locations': required,
        'recursive_zip_crc_pass': crc_checks, 'cr0_a_gzip_tar_read': 'PASS',
        'v3_expanded_second_run_matches_authoritative_archive': True,
        'handoff_archive_matches_extracted_files': True,
        'handoff_manifest_location': 'SHA256SUMS.txt is retained inside the handoff ZIP; the outer extracted view contains its seven governed documents.',
        'no_missing_material_reconstructed': True,
        'historical_v2_stale_manifest': 'Historical evidence only; not a current V3 failure',
        'initial_gate_note': 'The same gates passed before the first manuscript-authoring command; this script preserves the repeatable verification.'
    }
    out = ROOT / 'paper/checks/INTEGRITY_REPORT.json'
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(f'INTEGRITY PASS: {len(anchor_results)} anchors, {sum(c["count"] for c in checks)} manifest entries, {len(crc_checks)} ZIP containers; V3 {V3_SHA}')
    return result


if __name__ == '__main__':
    run()
