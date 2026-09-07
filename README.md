# NKBesicovitch

A [Lean 4](https://lean-lang.org/) project, built on
[mathlib](https://github.com/leanprover-community/mathlib4), for formalising work
around the **(n,k)-Besicovitch conjecture**.

## Status

Scaffolding only — no mathematics has been formalised yet.

## Building

Requires [`elan`](https://github.com/leanprover/elan). The toolchain is pinned in
`lean-toolchain` and installed automatically.

```bash
lake exe cache get   # fetch prebuilt mathlib oleans
lake build
```

## Layout

| Path | Contents |
| --- | --- |
| `NKBesicovitch.lean` | Root module; imports everything below |
| `NKBesicovitch/Basic.lean` | Starting module |
| `lakefile.toml` | Package configuration and the mathlib dependency |
| `lean-toolchain` | Pinned Lean toolchain |
