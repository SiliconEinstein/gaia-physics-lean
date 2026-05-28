/- FKG inequality proof using Mathlib's `fkg` lemma directly. -/

import Mathlib
import GaiaPhysicsLean.B6FkgInequality.Defs

namespace GaiaPhysicsLean.B6FkgInequality

/-- Holley lattice condition for the ferromagnetic Ising Gibbs measure:
`μ(σ) · μ(τ) ≤ μ(σ ∨ τ) · μ(σ ∧ τ)`.

This is a direct consequence of Hamiltonian submodularity and monotonicity of `Real.exp`. -/
theorem ising_lattice_condition {Λ : Type*} [Fintype Λ] [Lattice (ConfigSpace Λ)]
    {β : ℝ} (hβ : 0 ≤ β) {J : Λ → Λ → ℝ}
    (hsubmod : ∀ σ τ, isingHamiltonian J (σ ⊔ τ) + isingHamiltonian J (σ ⊓ τ)
                       ≤ isingHamiltonian J σ + isingHamiltonian J τ)
    {μ : PMF (ConfigSpace Λ)}
    (hμ : IsingMeasure β J μ)
    (σ τ : ConfigSpace Λ) :
    (μ σ).toReal * (μ τ).toReal ≤ (μ (σ ⊔ τ)).toReal * (μ (σ ⊓ τ)).toReal := by
  obtain ⟨_hferro, Z, hZpos, hμform⟩ := hμ
  set Hσ := isingHamiltonian J σ
  set Hτ := isingHamiltonian J τ
  set Hsup := isingHamiltonian J (σ ⊔ τ)
  set Hinf := isingHamiltonian J (σ ⊓ τ)
  rw [hμform σ, hμform τ, hμform (σ ⊔ τ), hμform (σ ⊓ τ)]
  have hZ_ne : Z ≠ 0 := ne_of_gt hZpos
  have hZsq_pos : 0 < Z * Z := mul_pos hZpos hZpos
  rw [div_mul_div_comm, div_mul_div_comm]
  rw [div_le_div_iff₀ hZsq_pos hZsq_pos]
  apply mul_le_mul_of_nonneg_right _ (le_of_lt hZsq_pos)
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsum : Hsup + Hinf ≤ Hσ + Hτ := hsubmod σ τ
  have hβneg : -β ≤ 0 := by linarith
  have hmul : -β * (Hσ + Hτ) ≤ -β * (Hsup + Hinf) :=
    mul_le_mul_of_nonpos_left hsum hβneg
  nlinarith [hmul]

/-- `ConfigSpace` has a distributive lattice structure inherited from the Pi instance. -/
noncomputable instance {Λ : Type*} : DistribLattice (ConfigSpace Λ) :=
  Pi.instDistribLattice

/-- FKG inequality from the Holley lattice condition using Mathlib's `fkg` lemma.

The proof shifts both real-valued increasing functions to non-negative functions, applies
the four-functions theorem, and then expands back to the original expectations. -/
theorem fkg_from_lattice_condition {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (μ : PMF (ConfigSpace Λ))
    (hlattice : ∀ σ τ : ConfigSpace Λ,
      (μ σ).toReal * (μ τ).toReal ≤ (μ (σ ⊔ τ)).toReal * (μ (σ ⊓ τ)).toReal)
    {f g : ConfigSpace Λ → ℝ}
    (hf : Increasing f)
    (hg : Increasing g) :
    (∑ σ : ConfigSpace Λ, (μ σ).toReal * f σ * g σ)
      ≥ (∑ σ : ConfigSpace Λ, (μ σ).toReal * f σ)
        * (∑ τ : ConfigSpace Λ, (μ τ).toReal * g τ) := by
  have hf_mono : Monotone f := fun a b hab => hf a b hab
  have hg_mono : Monotone g := fun a b hab => hg a b hab
  have hμ_nn : ∀ σ, 0 ≤ (μ σ).toReal := fun σ => ENNReal.toReal_nonneg
  classical
  haveI : Nonempty (ConfigSpace Λ) := ⟨fun _ => 0⟩
  let Cf : ℝ := (Finset.univ : Finset (ConfigSpace Λ)).inf' Finset.univ_nonempty f
  let Cg : ℝ := (Finset.univ : Finset (ConfigSpace Λ)).inf' Finset.univ_nonempty g
  let f' : ConfigSpace Λ → ℝ := fun σ => f σ - Cf
  let g' : ConfigSpace Λ → ℝ := fun σ => g σ - Cg
  have hf'_nn : ∀ σ, 0 ≤ f' σ := by
    intro σ
    have h : Cf ≤ f σ := Finset.inf'_le f (Finset.mem_univ σ)
    show 0 ≤ f σ - Cf
    linarith
  have hg'_nn : ∀ σ, 0 ≤ g' σ := by
    intro σ
    have h : Cg ≤ g σ := Finset.inf'_le g (Finset.mem_univ σ)
    show 0 ≤ g σ - Cg
    linarith
  have hf'_mono : Monotone f' := by
    intro a b hab
    have := hf_mono hab
    show f a - Cf ≤ f b - Cf
    linarith
  have hg'_mono : Monotone g' := by
    intro a b hab
    have := hg_mono hab
    show g a - Cg ≤ g b - Cg
    linarith
  have hμ_lat : ∀ a b : ConfigSpace Λ,
      (μ a).toReal * (μ b).toReal ≤ (μ (a ⊓ b)).toReal * (μ (a ⊔ b)).toReal := by
    intro a b
    have := hlattice a b
    have hcomm : (μ (a ⊔ b)).toReal * (μ (a ⊓ b)).toReal =
                 (μ (a ⊓ b)).toReal * (μ (a ⊔ b)).toReal := by ring
    linarith [this, hcomm]
  have hfkg : (∑ a, (μ a).toReal * f' a) * (∑ a, (μ a).toReal * g' a) ≤
              (∑ a, (μ a).toReal) * ∑ a, (μ a).toReal * (f' a * g' a) :=
    fkg f' g' (fun σ => (μ σ).toReal) hμ_nn hf'_nn hg'_nn hf'_mono hg'_mono hμ_lat
  have hsum_μ : ∑ σ : ConfigSpace Λ, (μ σ).toReal = 1 := by
    have h := μ.tsum_coe
    have h2 : ∑ σ : ConfigSpace Λ, μ σ = (1 : ENNReal) := by
      rw [← h]
      rw [tsum_eq_sum (s := Finset.univ)
        (f := fun σ => μ σ) (fun b hb => (hb (Finset.mem_univ _)).elim)]
    have hfin : ∀ σ : ConfigSpace Λ, μ σ ≠ ⊤ := fun σ => PMF.apply_ne_top μ σ
    have := congrArg ENNReal.toReal h2
    rw [ENNReal.toReal_sum (fun σ _ => hfin σ), ENNReal.toReal_one] at this
    exact this
  rw [hsum_μ, one_mul] at hfkg
  have hE_f' : (∑ a, (μ a).toReal * f' a) = (∑ a, (μ a).toReal * f a) - Cf := by
    have step : (∑ a, (μ a).toReal * f' a) =
        (∑ a, (μ a).toReal * f a) - Cf * (∑ a, (μ a).toReal) := by
      show (∑ a, (μ a).toReal * (f a - Cf)) =
        (∑ a, (μ a).toReal * f a) - Cf * (∑ a, (μ a).toReal)
      rw [Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [step, hsum_μ]
    ring
  have hE_g' : (∑ a, (μ a).toReal * g' a) = (∑ a, (μ a).toReal * g a) - Cg := by
    have step : (∑ a, (μ a).toReal * g' a) =
        (∑ a, (μ a).toReal * g a) - Cg * (∑ a, (μ a).toReal) := by
      show (∑ a, (μ a).toReal * (g a - Cg)) =
        (∑ a, (μ a).toReal * g a) - Cg * (∑ a, (μ a).toReal)
      rw [Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [step, hsum_μ]
    ring
  have hE_f'g' : (∑ a, (μ a).toReal * (f' a * g' a)) =
      (∑ a, (μ a).toReal * (f a * g a)) - Cf * (∑ a, (μ a).toReal * g a)
        - Cg * (∑ a, (μ a).toReal * f a) + Cf * Cg := by
    have step : (∑ a, (μ a).toReal * (f' a * g' a)) =
        (∑ a, (μ a).toReal * ((f a - Cf) * (g a - Cg))) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [step]
    have expand : ∀ a, (μ a).toReal * ((f a - Cf) * (g a - Cg)) =
        (μ a).toReal * (f a * g a) - Cf * ((μ a).toReal * g a)
          - Cg * ((μ a).toReal * f a) + Cf * Cg * (μ a).toReal := by
      intro a
      ring
    simp_rw [expand]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hsum_μ]
    ring
  rw [hE_f', hE_g', hE_f'g'] at hfkg
  have hreassoc : (∑ σ : ConfigSpace Λ, (μ σ).toReal * f σ * g σ)
      = (∑ σ : ConfigSpace Λ, (μ σ).toReal * (f σ * g σ)) := by
    apply Finset.sum_congr rfl
    intros
    ring
  linarith [hfkg, hreassoc]

end GaiaPhysicsLean.B6FkgInequality
