/-
  Quantum Relative Entropy — definitions and basic lemmas.

  S(ρ ‖ σ) = Tr(ρ (log ρ − log σ))

  where `CFC.log` is the operator logarithm defined via the continuous functional calculus.

  References:
  - Umegaki (1962), Ohya–Petz "Quantum Entropy and Its Use"
  - Mathlib: `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog`
  - Mathlib: `Mathlib.Analysis.Matrix.HermitianFunctionalCalculus`
-/

import Mathlib

open scoped MatrixOrder ComplexOrder

namespace GaiaPhysicsLean.A1Dpi

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {n : Type*} [Fintype n] [DecidableEq n]

/-!
## Definition of quantum relative entropy

We define `quantumRelativeEntropy ρ σ` as the real part of `Tr(ρ (log ρ − log σ))`.

When `ρ` and `σ` are positive semidefinite (Hermitian with nonneg spectrum), `CFC.log` is
well-defined via the continuous functional calculus for self-adjoint matrices.

Note: The standard physics convention sets S(ρ‖σ) = +∞ when supp(ρ) ⊄ supp(σ).
Here we use the algebraic formula directly; the value is a junk value when σ is not
invertible and ρ is not supported on σ's support.
-/

/-- The quantum relative entropy S(ρ ‖ σ) = Re Tr(ρ (log ρ − log σ)).

  Both `ρ` and `σ` are matrices over ℂ. The operator logarithm `CFC.log` is defined via
  the continuous functional calculus for self-adjoint (Hermitian) matrices. -/
noncomputable def quantumRelativeEntropy (ρ σ : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (ρ * (CFC.log ρ - CFC.log σ))).re

/-!
## Basic lemmas
-/

/-- The quantum relative entropy of a state with itself is zero: S(ρ ‖ ρ) = 0. -/
lemma qre_self_zero (ρ : Matrix n n ℂ) : quantumRelativeEntropy ρ ρ = 0 := by
  simp [quantumRelativeEntropy, sub_self]

/-- Conjugation by a unitary preserves the quantum relative entropy.
  S(U ρ U† ‖ U σ U†) = S(ρ ‖ σ).

  Proof sketch: CFC.log commutes with unitary conjugation because conjugation by U is a
  *-algebra automorphism and CFC is natural with respect to *-algebra homomorphisms
  (StarAlgHom.map_cfc). Then cyclic invariance of trace (Matrix.trace_mul_cycle) gives
  the result. A complete proof is in UnitaryInv.lean as `qre_unitary_invariant`.

  gap_kind: proof_gap
  difficulty: medium
  mathlib_lemma_needed: StarAlgHom.map_cfc applied to Unitary.conjStarAlgAut -/
lemma qre_unitary_conj (ρ σ : Matrix n n ℂ) (U : Matrix n n ℂ) (hU : U ∈ unitary (Matrix n n ℂ))
    (hρ : IsSelfAdjoint ρ) (hσ : IsSelfAdjoint σ) :
    quantumRelativeEntropy (U * ρ * star U) (U * σ * star U) = quantumRelativeEntropy ρ σ := by
  unfold quantumRelativeEntropy CFC.log
  set φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) ⟨U, hU⟩ with hφ_def
  have hφρ : φ ρ = U * ρ * star U := by
    simp [hφ_def, Unitary.conjStarAlgAut_apply]
  have hφσ : φ σ = U * σ * star U := by
    simp [hφ_def, Unitary.conjStarAlgAut_apply]
  have hφ_cont : Continuous φ :=
    (φ.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional).congr
      (fun x => by simp [StarAlgEquiv.coe_toAlgEquiv])
  have hlog_ρ : φ (cfc Real.log ρ) = cfc Real.log (φ ρ) :=
    StarAlgHomClass.map_cfc φ Real.log ρ
      (hf := ρ.finite_real_spectrum.continuousOn _) (hφ := hφ_cont)
  have hlog_σ : φ (cfc Real.log σ) = cfc Real.log (φ σ) :=
    StarAlgHomClass.map_cfc φ Real.log σ
      (hf := σ.finite_real_spectrum.continuousOn _) (hφ := hφ_cont)
  rw [← hφρ, ← hφσ]
  rw [← hlog_ρ, ← hlog_σ]
  rw [← map_sub φ, ← map_mul φ]
  congr 1
  simp only [hφ_def, Unitary.conjStarAlgAut_apply]
  set X := ρ * (cfc Real.log ρ - cfc Real.log σ)
  rw [Matrix.trace_mul_comm (U * X) (star U), ← Matrix.mul_assoc,
      Unitary.star_mul_self_of_mem hU, Matrix.one_mul]

end GaiaPhysicsLean.A1Dpi
