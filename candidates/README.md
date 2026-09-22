# Candidate tables

- **Current experimental candidate: 316 states**, in [ics-best.tm](ics-best.tm),
  with [configuration and table hash](ics-best.json). Uses ICS, ten active
  registers, and reversed binary formula payloads. Run `python3 tools/verify_ics.py`.
- **Conservative baseline: 392 states**, in [best.tm](best.tm), with
  [configuration](best.json). Retains all distinct Wade axiom clauses. Run
  `python3 tools/verify.py`.

Both tables use the upstream partial-transition text format and start on a blank
two-way binary tape. No post-compilation table reduction is needed for their
advertised counts. Neither is formally verified. The 392-state baseline is
retained because it avoids the ICS theory/encoding changes, making it a useful
comparison rather than a competing headline result.

See [experiments](../docs/EXPERIMENTS.md) and [verification scope](../docs/VERIFICATION.md).
