# Candidate tables

- **Current experimental candidate: 308 states**, in [ics-best.tm](ics-best.tm),
  with [configuration and hashes](ics-best.json) and the [final instruction tree](ics-tree.json). Uses ICS, ten active
  registers, reversed binary formula payloads, and the field order
  `param1, param3, param2, axiomcode` with delayed clears. Run `python3 tools/verify_ics.py`.
- **Conservative baseline: 392 states**, in [best.tm](best.tm), with
  [configuration](best.json). Retains all distinct Wade axiom clauses. Run
  `python3 tools/verify.py`.

Both tables use the upstream partial-transition text format and start on a blank
two-way binary tape. No post-compilation table reduction is needed for their
advertised counts. Neither has an end-to-end formal tape-machine proof. The
[Lean development](../formal/README.md) proves the current numeric source theorem
and component contracts, and imports the literal 308-state table. The 392-state baseline is
retained because it avoids the ICS theory/encoding changes, making it a useful
comparison rather than a competing headline result.

See [experiments](../docs/EXPERIMENTS.md) and [verification scope](../docs/VERIFICATION.md).
