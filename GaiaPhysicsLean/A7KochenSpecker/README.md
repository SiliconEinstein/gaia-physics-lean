# A7 — Kochen–Specker Theorem (CEGA 18-vector witness)

> A Kochen–Specker set is a finite collection of rays in a Hilbert space together with a cover by complete orthonormal bases such that **no 0/1 valuation can assign exactly one '1' per basis**. KS sets exist for $\mathbb{C}^d$ with $d \ge 3$.

This file proves it concretely using the Cabello–Estebaranz–García-Alcaine (CEGA) 18-vector construction in $\mathbb{R}^4$ — the minimum-known counterexample to non-contextual hidden-variable theories.

## Proof outline

A purely combinatorial parity argument:

- 9 orthonormal bases × 4 vectors each = 36 "slots"
- Each of the 18 vectors appears in **exactly 2** bases
- For any 0/1 valuation: $\sum_i (\text{basisCount}_i) = 2 \cdot (\text{trueCount})$ is **even**
- But the KS constraint demands $\sum_i (\text{basisCount}_i) = 9 \cdot 1 = 9$ (one '1' per basis), which is **odd**.

Contradiction. The proof is `decide`-checkable once the 18 vectors and 9 bases are encoded.

## Files

- [`Theorem.lean`](./Theorem.lean) — primary target `kochen_specker_18vec_no_valuation`
- [`CheckAxioms.lean`](./CheckAxioms.lean) — axiom check (only the standard 3)

## Verification

```bash
lake build GaiaPhysicsLean.A7KochenSpecker.Theorem
#  → rc=0, 0 axioms, 0 sorry
```

## Why it matters

Resolves the question "can a deterministic non-contextual hidden-variable theory reproduce quantum predictions for $d \ge 3$?" — **no**. Combined with Bell (proved by A10 Tsirelson here), this is the standard foundations-of-quantum-mechanics impossibility duo.

## BP plan

[`../../plans/A7KochenSpecker.plan.gaia.py`](../../plans/A7KochenSpecker.plan.gaia.py).

## Source

LKM claim `gcn_0b8cd733edc4459d`. Formalized by gaia-discovery v3.5 (iter 3, ~218 LOC).
