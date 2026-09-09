# Development verification of the completed targets

Date: 2026-09-08. Proof sources: `8685c60b049dddf0e504251638f1cc0822508ec7`.

Comparator accepted `NKBesicovitch.criticalExponent_bounds` and
`NKBesicovitch.volume_pos_of_criticalExponent`, checked their dependencies
against the fixed challenge definitions, checked the permitted axioms, and
replayed the exported solution declarations in a fresh Lean kernel environment.
The process exited with status 0.

This was a macOS **development** run using Comparator's documented
`fake-landrun.sh` adapter. It did **not** provide Linux sandbox isolation and
did **not** run an independent kernel. It is evidence of statement matching,
axiom checking, and Lean kernel replay for these two targets; it is not the
final security or Palomar verification gate. The current `comparator.json`
requests these two targets with nanoda enabled. This report records the
historical run at the source revision above; it is not a fresh verification
of subsequent source edits.

## Fixed definitions

The original configuration incorrectly listed `IsBesicovitch` and
`criticalExponent` in `definition_names`. Comparator treats that list as
**definition holes**: their types and safety levels must match, but their
bodies may differ. Both definitions are fixed here, so this field has been
removed. They are now compared, including their bodies, as dependencies of
the theorem statements. See the pinned [comparison implementation](https://github.com/leanprover/comparator/blob/011e9d35a10a054ed4b66d8379115ad870f2b0ce/Comparator/Compare.lean).

## Tools and configuration

- Lean and Mathlib: `v4.34.0-rc1`.
- Comparator: `011e9d35a10a054ed4b66d8379115ad870f2b0ce` (`v4.34.0-rc1`).
- lean4export: `b18d673bd29b476466a51a3be1012df2ed322b10`, pinned by Comparator.
- Development adapter: the unmodified `scripts/fake-landrun.sh` from that checkout.
- Exported proofs were checked with only `propext`, `Quot.sound`, and `Classical.choice` permitted.

The temporary development configuration was:

```json
{
  "challenge_module": "Challenge",
  "solution_module": "Solution",
  "theorem_names": [
    "NKBesicovitch.criticalExponent_bounds",
    "NKBesicovitch.volume_pos_of_criticalExponent"
  ],
  "permitted_axioms": [
    "propext",
    "Quot.sound",
    "Classical.choice"
  ],
  "enable_nanoda": false
}
```

The retained local log is `tmp/verification/critical-range-development.log`
(SHA-256 `5608c2f3faa868170d39a56cf8a196b3e94b0179df7d40cf58334de8df13deb8`). Its final verifier output was:

```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

The log also explicitly records that the development adapter did not sandbox
its build and export commands. Full Linux isolation, independent-kernel
checking, and verification of the current retained targets remain pending.
