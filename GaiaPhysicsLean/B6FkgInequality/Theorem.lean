/- FKG inequality for lattice ferromagnetic Ising
   LKM source claim: gcn_46b3420ea41e4842
   Tier: B

   **Primary target**: `fkg_inequality`

   For a Gibbs measure on `{±1}^Λ` with non-negative pairwise couplings,
   increasing observables are positively correlated:
   `E[f g] ≥ E[f] · E[g]`.
-/

import Mathlib
import GaiaPhysicsLean.B6FkgInequality.Defs
import GaiaPhysicsLean.B6FkgInequality.Lemmas_v2

namespace GaiaPhysicsLean.B6FkgInequality

/-- **FKG Inequality for the ferromagnetic Ising model.**

For a Gibbs measure on `{±1}^Λ` with non-negative pairwise couplings, increasing
observables are positively correlated. The proof combines Hamiltonian
submodularity, Holley's lattice condition, and Mathlib's Ahlswede-Daykin/FKG
lemma. -/
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
        * (∑ τ : ConfigSpace Λ, (μ τ).toReal * g τ) := by
  apply fkg_from_lattice_condition
  · intro σ τ
    have hferro : Ferromagnetic J := hμ.1
    exact ising_lattice_condition hβ (isingHamiltonian_submodular hferro) hμ σ τ
  · exact hf
  · exact hg

#print axioms GaiaPhysicsLean.B6FkgInequality.fkg_inequality

end GaiaPhysicsLean.B6FkgInequality
