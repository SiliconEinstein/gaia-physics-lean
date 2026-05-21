/-
  Unitary invariance of quantum relative entropy.

  S(U ρ U† ‖ U σ U†) = S(ρ ‖ σ)

  for any unitary matrix U.

  Strategy:
  1. Use `Unitary.conjStarAlgAut` to get a StarAlgEquiv for conjugation by U.
  2. Apply `StarAlgHom.map_cfc` (via the StarAlgEquiv coercion) to show
     CFC.log commutes with unitary conjugation.
  3. Use `Matrix.trace_mul_comm` for cyclic invariance of trace.
-/

import Mathlib
import GaiaPhysicsLean.A1Dpi.Defs

open scoped MatrixOrder ComplexOrder

namespace GaiaPhysicsLean.A1Dpi

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Unitary conjugation preserves the quantum relative entropy:
    S(U ρ U† ‖ U σ U†) = S(ρ ‖ σ) for any unitary U. -/
theorem qre_unitary_invariant (ρ σ : Matrix n n ℂ) (U : Matrix n n ℂ)
    (hU : U ∈ unitary (Matrix n n ℂ))
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
