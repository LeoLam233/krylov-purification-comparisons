"""Read-only manifest and boundary verification."""
import argparse
import json
from staging_common import ROOT, require, verify_repo, verify_manifest, check_snapshot


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--private-assets')
    args = parser.parse_args()
    report = verify_repo(args.private_assets)
    report['paper_snapshot'] = check_snapshot()
    manifest = ROOT/'PUBLIC_TREE.sha256'
    if manifest.exists():
        rows = verify_manifest(ROOT,manifest)
        actual = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if p.is_file()
                  and not any(x in {'.git','.local','.venv','__pycache__'} for x in p.relative_to(ROOT).parts)
                  and p.name != 'PUBLIC_TREE.sha256'}
        require(actual == set(rows), 'Public-tree manifest coverage mismatch')
        report['public_tree_files'] = len(rows)
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
