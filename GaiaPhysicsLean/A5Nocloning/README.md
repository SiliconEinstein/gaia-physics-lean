# A5 — No-Cloning Theorem

> No unitary $U$ on $H \otimes H_\text{aux}$ satisfies $U(|\psi\rangle \otimes |0\rangle) = |\psi\rangle \otimes |\psi\rangle$ for all unit $|\psi\rangle \in H$ when $\dim H \ge 2$.

The first formally-proved no-go theorem of quantum information (Wootters & Zurek 1982, Dieks 1982). It rules out any universal quantum cloning machine.

## Proof outline

Inner-product preservation under unitary maps gives, for two unit states $|\psi\rangle, |\phi\rangle$:

$$\langle \psi | \phi \rangle \cdot \langle 0 | 0 \rangle \;=\; \langle \psi | \phi \rangle^{2}.$$

Hence $\langle \psi | \phi \rangle \in \{0, 1\}$, contradicting $\dim H \ge 2$ (we can always pick a third unit vector with non-trivial overlap to both).

## Files

- [`Theorem.lean`](./Theorem.lean) — primary target `no_cloning_theorem`
- [`CheckAxioms.lean`](./CheckAxioms.lean) — `#print axioms` confirms only `{propext, Classical.choice, Quot.sound}`

## Verification

```bash
lake build GaiaPhysicsLean.A5Nocloning.Theorem
#  → rc=0, 0 axioms, 0 sorry
```

## BP plan

The agentic discovery plan is at [`../../plans/A5Nocloning.plan.gaia.py`](../../plans/A5Nocloning.plan.gaia.py).

## Source

LKM claim `gcn_054b79cf1e5740d0`. Formalized by gaia-discovery v3.5 (iter 1, ~89 LOC).
