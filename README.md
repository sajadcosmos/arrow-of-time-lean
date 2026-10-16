# Lean 4 formalization: *An Arrow of Time That Efficient Observers Cannot Detect*

This repository contains the complete Lean 4 / Mathlib formalization accompanying

> S. A. Sheikh, M. Faizal, and A. Shabir,
> *An Arrow of Time That Efficient Observers Cannot Detect: Information-Preserving Records of Irreversible Dynamics* (2026).

The whole development is a single file, [`ArrowOfTime.lean`](ArrowOfTime.lean) (about 6,000 lines). It contains **no `sorry` and no `axiom` declarations**.

## What is formalized

Every labelled result of the paper is proved:

- **Propositions** III.1, III.2, VIII.1, IX.1, X.2, XII.1
- **Lemmas** IV.1, VII.1
- **Theorems** IV.2, V.1, VI.1, VII.2, X.1, X.3, X.4
- **Corollary** IX.2

The unlabelled identities and bounds of the main text and of Appendices A, B and E are also proved, and so are the exact numerical values quoted in Sec. XIII (checked exactly or with rigorous error bounds).

[`VERIFICATION.md`](VERIFICATION.md) maps each claim of the paper to its Lean theorem name.

## Inputs taken as hypotheses

As stated in Appendix F of the paper, five established inputs enter the Lean statements as **explicit hypotheses** of the theorems (never as global axioms):

1. **Physical description of the driven three-state ring.** This covers the path density, the conditional i.i.d. Bernoulli law of jump directions given the count, the Poisson jump count, and the identification of the log path-probability ratio with entropy production.
2. **The decisional hard-core assumption**, Eq. (11) of the paper (`HardCoreAssumption`).
3. **Circuit-composition overheads.** The cost of composing an observer with an efficient sampler or channel, stated as closure properties of the observer classes.
4. **The binomial central limit theorem**, used in Eq. (E6) (`weak_clt_TV`).
5. **The program-composition property of a universal machine**, used in Eq. (75) (`complexity_invariance`).

The formalization certifies that each conclusion follows from these inputs. It does not certify the inputs themselves. Inputs 1 and 2 carry the physical and cryptographic content of the paper.

## Building

Requirements: [Lean 4](https://lean-lang.org/) via `elan`. The toolchain version is pinned in `lean-toolchain` (`leanprover/lean4:v4.28.0`), and Mathlib is pinned to `v4.28.0` in `lakefile.toml`.

```bash
git clone https://github.com/<your-username>/arrow-of-time-lean.git
cd arrow-of-time-lean
lake update          # resolves Mathlib (creates lake-manifest.json if absent)
lake exe cache get   # downloads precompiled Mathlib
lake build
```

A successful `lake build` with no errors confirms that every proof checks.

To confirm that a theorem depends only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), add a line such as

```lean
#print axioms Arrow.universal_concealment
```

at the end of the file, or in a separate file that imports `ArrowOfTime`.

## Files

| File | Purpose |
|---|---|
| `ArrowOfTime.lean` | The complete formalization |
| `VERIFICATION.md` | Claim-by-claim map from the paper to Lean theorem names |
| `lakefile.toml` | Lake build configuration (Mathlib dependency) |
| `lean-toolchain` | Pinned Lean version |

## Contact

Corresponding author: Arshid Shabir (aslone186@gmail.com)
Sajad Ahmad Sheikh: sajadsheikh@uok.edu.in

## License

See [`LICENSE`](LICENSE).
