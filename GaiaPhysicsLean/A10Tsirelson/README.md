# A10 — Tsirelson Bound for the CHSH Inequality

> For dichotomic observables $A_0, A_1, B_0, B_1$ with $\|A_i\|, \|B_j\| \le 1$ on any Hilbert space and any state $|\psi\rangle$:
>
> $$\bigl|\langle A_0 B_0 + A_0 B_1 + A_1 B_0 - A_1 B_1 \rangle\bigr| \;\le\; 2\sqrt{2}.$$

The single most-cited inequality of quantum foundations: quantum correlations are strictly stronger than classical ($\le 2$) but bounded by Tsirelson's $2\sqrt{2}$.

## Proof outline

Tsirelson's 1980 algebraic identity, the cleanest known proof:

$$S^2 \;=\; (A_0 B_0 + A_0 B_1 + A_1 B_0 - A_1 B_1)^2 \;=\; 4 I \;-\; [A_0, A_1] \otimes [B_0, B_1].$$

Since $\|[A_0, A_1]\| \le 2$ and $\|[B_0, B_1]\| \le 2$, the commutator term is norm-bounded by $4$, so $\|S^2\| \le 8$, hence $\|S\| \le 2\sqrt{2}$.

## Files

- [`Theorem.lean`](./Theorem.lean) — primary target `tsirelson_chsh_bound`

The proof uses `ContinuousLinearMap` operator norms, `comp` for composition, and `dichA₀ : A₀.comp A₀ = 1` (the dichotomic = involutive assumption).

## Verification

```bash
lake build GaiaPhysicsLean.A10Tsirelson.Theorem
#  → rc=0, 0 axioms, 0 sorry
```

## BP plan

[`../../plans/A10Tsirelson.plan.gaia.py`](../../plans/A10Tsirelson.plan.gaia.py).

## Source

LKM claims `gcn_9f07543c6ff944b0` (general statement) + `gcn_aea213dfec744535` (numerical SDP confirmation). Formalized by gaia-discovery v3.5 (~171 LOC).
