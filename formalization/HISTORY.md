# Formalization history and evidence

The public repository version is distinct from internal formalization revisions.

- Early formalization translated exact witnesses, finite-dimensional inequalities,
  temporal families, and auxiliary calculations. Compilation by itself did not establish
  every source-level identification
- Adversarial review of the early v2 candidate found that explicit-chain calculations
  were not sufficiently connected to generic normalized Gram–Schmidt source quantities
- v3 introduced generic GS uniqueness, certified matrix/polynomial bridges, and
  source-level APIs. Its 94 production proof modules are preserved byte-for-byte
- Later review found that four canonical spread equalities existed but were not used
  by final family endpoints; perturbed source identification was specialized to delta=0.
  The earlier dependency test also traversed declaration types as well as proof values
- v4 added canonical family endpoints and delta-general perturbed endpoints, required
  per-root value-only bridge paths and rejecting controls, strengthened module-provenance
  trust auditing, and deterministic source-only release verification
- Independent GitHub Actions kernel execution of the frozen v4 RC2 payload passed
  [run 36866846382](https://github.com/LeoLam233/krylov-purification-comparisons/actions/runs/36866846382).
  The first CI attempt exposed a missing complex-order scope in one newly added module;
  that scope repair preceded RC2 and the passing run. Publication makes no further
  Lean-source change
- Public v0.2.0 places the frozen payload in `formalization/`, adds reader documentation
  and reruns the complete gates for the final layout before merging and releasing

The final frozen-candidate source/trust/regression review had three separate scopes
performed by one nonbuilder reviewer. Three fresh independent reviewers were unavailable;
no claim of three independent reviewers or a second local kernel replay is made.
Compilation, axiom provenance, dependency reachability, source correspondence and
human peer review are different forms of evidence. The first three are executable
here; source interpretation still requires reading the statements and mappings.

Historical intermediate versions are not retroactively credited with the later gates.
The original manuscript source and PDFs are unchanged by the Lean publication.
