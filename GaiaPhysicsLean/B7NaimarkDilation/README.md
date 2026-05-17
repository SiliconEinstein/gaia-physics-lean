# B7 — Naimark Dilation Theorem (POVM ↔ Projective Measurement on Extended Space)

> Every finite POVM $\{E_i\}_{i \in \iota}$ on a finite-dim Hilbert space $H$ is realizable as a projective measurement on an extended space $K \supseteq H$ — i.e., there exist orthogonal projections $\{P_i\}_{i \in \iota}$ on $K$ such that
>
> $$E_i \;=\; V^\dagger P_i V$$
>
> for an isometry $V : H \to K$.

This is the measurement-theoretic mirror of the Stinespring dilation theorem (which dilates CP maps to unitaries). Together with Stinespring (A3), Naimark establishes that **every quantum measurement is, at heart, a unitary evolution on a larger Hilbert space followed by a projective measurement**.

## Proof outline

The construction is the textbook one: take $K = H^{|\iota|}$ (i.e. $|\iota|$ copies of $H$), define the isometry by
$$V|\psi\rangle \;=\; \sum_i \sqrt{E_i}|\psi\rangle \otimes |i\rangle,$$
and let $P_i = I_H \otimes |i\rangle\langle i|$. Naimark's identity $V^\dagger P_i V = E_i$ follows from the POVM completeness $\sum_i E_i = I$.

## Files

- [`Theorem.lean`](./Theorem.lean) — primary target `naimark_dilation_finite`

## Verification

```bash
lake build GaiaPhysicsLean.B7NaimarkDilation.Theorem
#  → rc=0, 0 axioms, 0 sorry
```

## BP plan

[`../../plans/B7NaimarkDilation.plan.gaia.py`](../../plans/B7NaimarkDilation.plan.gaia.py).

## Source

LKM claim `gcn_b9e7abd2ad804f29`. Formalized by gaia-discovery v3.5 (iter 4–6, ~347 LOC; downsized from the original 490 LOC scaffold by axiom-free refactor).
