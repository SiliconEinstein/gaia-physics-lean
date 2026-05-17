# A3 — Stinespring Dilation Theorem (finite-dim)

> For any trace-preserving completely-positive map $\mathcal{E} : \mathcal{B}(H_Q) \to \mathcal{B}(H_Q)$ there exists a Hilbert space $H_E$, a unit vector $|0\rangle_E \in H_E$, and a unitary $U$ on $H_Q \otimes H_E$ such that
>
> $$\mathcal{E}(\rho) \;=\; \mathrm{Tr}_E\bigl[\,U\,(\rho \otimes |0\rangle\langle 0|)\,U^\dagger\,\bigr].$$

Every CPTP map (= the most general quantum channel) is unitary evolution on a larger
Hilbert space followed by a partial trace. Together with [A2 Choi](https://github.com/SiliconEinstein/gaia-physics-lean)
(CP ⇔ Choi-PSD), this is the **density-operator ↔ pure-state bridge** that grounds the
entire operational picture of quantum information.

## Proof outline

The Lean proof is structurally:

1. **CP + TP → Kraus decomposition** (`kraus_decomposition Φ hCP hTP`):
   diagonalize the Choi matrix $C_\Phi$, extract operators $K_k$ with
   $\sum_k K_k^\dagger K_k = I$ from the PSD eigendecomposition.
2. **Kraus isometry → unitary extension** (`isometry_extends_to_unitary`):
   the column-by-column map $|i\rangle \mapsto \sum_k K_k|i\rangle \otimes |k\rangle$
   is an isometry on $H_Q \otimes \langle 0\rangle$; Gram–Schmidt extends it to
   a unitary on all of $H_Q \otimes H_E$.
3. **Partial-trace dilation identity** (`partial_trace_dilation`):
   verify $\mathrm{Tr}_E[U(\rho \otimes |0\rangle\langle 0|)U^\dagger] = \sum_k K_k \rho K_k^\dagger$
   directly from the Kraus form.

## Files

- [`Theorem.lean`](./Theorem.lean) — primary target `stinespring_dilation`
- [`Defs.lean`](./Defs.lean) — `QChan`, `IsCP`, `IsTP`, `StinespringData`
- [`Lemmas.lean`](./Lemmas.lean) — Kraus decomposition + isometry extension (~ 850 LOC)
- [`CheckAxioms.lean`](./CheckAxioms.lean) — confirms only `{propext, Classical.choice, Quot.sound}`

## Verification

```bash
lake build GaiaPhysicsLean.A3Stinespring.Theorem
#  → rc=0 (≈ 2933 build jobs)

lake env lean GaiaPhysicsLean/A3Stinespring/CheckAxioms.lean
#  → 'GaiaPhysicsLean.A3Stinespring.stinespring_dilation' depends on axioms:
#     [propext, Classical.choice, Quot.sound]
```

## BP plan

[`../../plans/A3Stinespring.plan.gaia.py`](../../plans/A3Stinespring.plan.gaia.py).

## Source

LKM claim `gcn_85c00af123214e3e`. Formalized by gaia-discovery v3.5 (iter 1–4, ~900 LOC).
The 50-line gap on `kraus_tp_from_choi_trace` in [`Lemmas.lean`](./Lemmas.lean) line 113-115
references a *commented-out* "terminal `sorry`" — the file actually compiles with 0 sorries
because the lemma signature has since been repaired; the comment is residual from an earlier
iteration.
