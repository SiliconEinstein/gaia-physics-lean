# A2 — Choi's theorem (CP ⇔ Choi-matrix PSD)

> A finite-dimensional linear map $\Phi : B(\mathcal{K}) \to B(\mathcal{H})$ is
> **completely positive** if and only if its **Choi matrix**
> $C_\Phi = (\mathrm{id} \otimes \Phi)(|\Omega\rangle\langle\Omega|)$ is positive
> semidefinite, where $|\Omega\rangle = \sum_a |a\rangle \otimes |a\rangle$ is
> the (unnormalised) maximally entangled state.

Choi 1975 (*Linear Algebra Appl.* **10**:285). The Choi–Jamiołkowski
isomorphism, the workhorse of quantum information theory: it reduces every
question about CP-ness of a channel to a finite-dimensional PSD check on a
single $(d_K d_H) \times (d_K d_H)$ matrix.

LKM source claims:
- `gcn_81765219a10f496c` (Choi 1975 premise)
- `gcn_e167099bb6614b7c` (Frembs 2022 Jordan reformulation)

## Honest scope

This is an **unconditional** formalization — no data-bundle hypotheses, no
axiom shortcuts, no Mathlib gaps left open on the main path.

* `lake build GaiaPhysicsLean.A2ChoiTheorem.Theorem` → **rc=0**
* `#print axioms choi_theorem_cp_iff_psd` → `[propext, Classical.choice, Quot.sound]`
* zero `sorry`, zero `axiom` across all four files

## Proof outline

The proof is a bidirectional equivalence:

### `Defs.lean` (106 LOC)
Channel definitions: `QChan dK dH` (linear map between matrix spaces),
`IsCP Φ` (complete positivity at every ancilla dimension), and the Choi
construction `Choi Φ` as the explicit $(d_K \times d_H) \times (d_K \times d_H)$
matrix $(\mathrm{id} \otimes \Phi)(|\Omega\rangle\langle\Omega|)$ pulled out
as a single `Matrix (Fin dK × Fin dH) (Fin dK × Fin dH) ℂ` definition.

### `Forward.lean` (91 LOC) — CP ⇒ Choi PSD
**Strategy.** Apply complete positivity at ancilla dimension $n = d_K$ to
the rank-1 PSD matrix $|\Omega\rangle\langle\Omega|$. Encode the maximally
entangled state as a rank-1 PSD via `vecMulVec ω (star ω)` where
$\omega : \mathrm{Fin}(d_K \cdot d_K) \to \mathbb{C}$ is the diagonal
indicator $\omega_{(a,b)} = \delta_{a,b}$. The CP image is exactly the
Choi matrix; the PSD certificate carries over by `LinearMap.cpMapAux`.

Key lemma: factorisation of nested sums to show
$\langle v, (\omega \otimes \omega^\dagger) v \rangle = |\langle \omega, v\rangle|^2 \ge 0$.

### `Reverse.lean` (159 LOC) — Choi PSD ⇒ CP
**Strategy.** Spectral decomposition of $C_\Phi$ gives
$C_\Phi = \sum_i \lambda_i |v_i\rangle\langle v_i|$ with $\lambda_i \ge 0$ and
orthonormal eigenvectors $v_i$. Each rank-1 PSD summand
$\lambda_i |v_i\rangle\langle v_i|$ is the Choi matrix of an explicit Kraus
operator $K_i = \sqrt{\lambda_i} \cdot \mathrm{reshape}(v_i)$ acting as
$\rho \mapsto K_i \rho K_i^\dagger$ — a CP map. Summing these gives Φ as a
sum of CP maps, hence CP at any ancilla.

Key infrastructure used from Mathlib:
- `Matrix.PosSemidef.spectralTheorem` (real spectrum of Hermitian matrix)
- `Equiv.finProdFinEquiv` (reshape between `Fin (dK*dH)` and `Fin dK × Fin dH`)
- `Matrix.PosSemidef.eigenvalues_nonneg`

### `Theorem.lean` (19 LOC)
Bundles forward + reverse into the iff.

## Verify

```bash
lake build GaiaPhysicsLean.A2ChoiTheorem.Theorem
lake env lean GaiaPhysicsLean/A2ChoiTheorem/CheckAxioms.lean
```

Expected output of the axiom check:
```
'GaiaPhysicsLean.A2ChoiTheorem.choi_theorem_cp_iff_psd' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```
