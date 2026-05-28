# B6 — FKG inequality for ferromagnetic Ising measures

LKM source claim: `gcn_46b3420ea41e4842`.

## Statement

For a finite lattice `Λ`, a ferromagnetic Ising Gibbs measure `μ` on
`{±1}^Λ`, and two increasing observables `f g : ConfigSpace Λ → ℝ`,
the FKG correlation inequality holds:

```lean
theorem fkg_inequality {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {β : ℝ} (hβ : 0 ≤ β)
    {J : Λ → Λ → ℝ}
    {μ : PMF (ConfigSpace Λ)}
    (hμ : IsingMeasure β J μ)
    {f g : ConfigSpace Λ → ℝ}
    (hf : Increasing f)
    (hg : Increasing g) :
    (∑ σ : ConfigSpace Λ, (μ σ).toReal * f σ * g σ)
      ≥ (∑ σ : ConfigSpace Λ, (μ σ).toReal * f σ)
        * (∑ τ : ConfigSpace Λ, (μ τ).toReal * g τ)
```

## Proof Outline

The proof follows Holley's lattice-condition route:

1. `Defs.lean` defines `ConfigSpace Λ := Λ → Fin 2`, increasing observables,
   ferromagnetic couplings, and the Ising Gibbs-measure predicate.
2. `isingHamiltonian_submodular` proves the finite Ising Hamiltonian is
   submodular under non-negative pairwise couplings.
3. `ising_lattice_condition` converts Hamiltonian submodularity into the
   Holley condition
   `μ σ * μ τ ≤ μ (σ ⊔ τ) * μ (σ ⊓ τ)`.
4. `fkg_from_lattice_condition` applies Mathlib's
   `Mathlib.Combinatorics.SetFamily.FourFunctions.fkg` lemma, shifting
   arbitrary real-valued increasing observables to non-negative ones and
   expanding back.
5. `fkg_inequality` instantiates the generic lattice-condition theorem for
   the Ising Gibbs measure.

## Verification

The swarm project verified the theorem with:

```bash
lake build PhysicsLean.B6FkgInequality.Theorem
# Build completed successfully (8396 jobs)
# 'PhysicsLean.B6FkgInequality.fkg_inequality' depends on axioms:
#   [propext, Classical.choice, Quot.sound]
```

The published module is the same proof under the `GaiaPhysicsLean` namespace.
It has no custom axioms and no `sorry` declarations in the proof tree.
