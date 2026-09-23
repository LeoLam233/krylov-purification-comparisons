# Build the final public manuscript

Run from the public Git root `Krylov_purification_v0.1/`:

```text
python scripts/check_paper.py
python scripts/build_paper.py --engine tectonic
```

Full original paper-stage checks use the separately retained private inputs:

```text
python scripts/check_paper.py --private-assets ../Krylov_Private_Assets
```

Tectonic 0.17.0 is the tested compiler. For a populated cache, add
`--cache /path/to/tectonic-cache --offline`. The wrapper uses the unchanged
paper-stage build script in a temporary project. That script creates an empty
source/build directory, admits only TeX and BibTeX source, runs BibTeX and TeX
to convergence, checks errors, undefined references/citations and overfull boxes,
and requires all five bibliography entries to resolve.

Results go to a new `.local/paper-build-*` directory, including `main.pdf`,
`main.bbl`, `summary.json` and logs. The staged PDF is not replaced by this wrapper.
The original paper-stage build instructions remain in the private completed
paper archive. See the top-level REPRODUCIBILITY.md and docs/STAGING_PATHS.md.
