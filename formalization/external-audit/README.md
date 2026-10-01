# Source inventory baseline

`CLAIM_AUDIT.tsv` preserves the 128-row source inventory used during adversarial
review. `scripts/check_source_ledger.py` checks that the current claim ledger retains
exactly its IDs, source locators and statements. Historical verdict columns describe
that earlier reviewed state, not the present release. See `../HISTORY.md` for repairs.
