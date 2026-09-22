# Upstream source

- `wade/` is an unmodified snapshot of Andrew James Wade's MIT-0 licensed
  `turing_machine_explorer`. Its original README intentionally retains the stale
  410-state prose; the pinned example and table have 393 states.
  [Provenance and hashes](../reference/upstream.json), [license](wade/LICENSE).
- `cats/` contains the corrected ICS formula source and MIT license from
  CatsAreFluffy's October 2025 commit. We port its formula sequences while
  retaining Wade's enumeration and inference selection.
  [Scope](cats/README.md), [provenance and hashes](../reference/ics-upstream.json).

Local changes belong in `tools/`, not in these reference files. See the
[survey](../docs/SURVEY.md) and [current experiments](../docs/EXPERIMENTS.md).
