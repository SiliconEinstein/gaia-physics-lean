/-
PPT2.Cases.SpectralDim2 — 2×2 Hermitian/PSD spectral wrapper for P3 step (c).
-/
import PPT2.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Complex.Basic

namespace PPT2.SpectralDim2

open Matrix Complex
open scoped ComplexOrder

/-- A 2×2 complex matrix is Hermitian iff the off-diagonal entries are conjugate
    symmetric and the diagonal entries are real. -/
theorem isHermitian_iff_entries (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M.IsHermitian ↔ M 0 1 = star (M 1 0) ∧ (M 0 0).im = 0 ∧ (M 1 1).im = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have := congr_fun (congr_fun h 0) 1
      simp [Matrix.conjTranspose_apply] at this; exact this.symm
    · have := congr_fun (congr_fun h 0) 0
      simp [Matrix.conjTranspose_apply] at this; exact conj_eq_iff_im.mp this
    · have := congr_fun (congr_fun h 1) 1
      simp [Matrix.conjTranspose_apply] at this; exact conj_eq_iff_im.mp this
  · intro ⟨h01, h00, h11⟩
    unfold Matrix.IsHermitian Matrix.conjTranspose
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Complex.conj_eq_iff_im]
    · exact h00
    · exact h01.symm
    · rw [h01]; simp
    · exact h11

/-- A 2×2 complex matrix is positive semidefinite iff it is Hermitian with
    non-negative trace and non-negative determinant (Sylvester criterion d=2). -/
theorem posSemidef_iff_trace_det (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M.PosSemidef ↔ M.IsHermitian ∧
      (M 0 0 + M 1 1).re ≥ 0 ∧
      ((M 0 0) * (M 1 1) - (M 0 1) * (M 1 0)).re ≥ 0 := by
  constructor
  · intro hM
    refine ⟨hM.1, ?_, ?_⟩
    · have h := Matrix.PosSemidef.trace_nonneg hM
      rw [Matrix.trace_fin_two] at h
      exact_mod_cast (RCLike.nonneg_iff.mp h).1
    · have h := Matrix.PosSemidef.det_nonneg hM
      rw [Matrix.det_fin_two] at h
      exact_mod_cast (RCLike.nonneg_iff.mp h).1
  · intro ⟨hHerm, hTr, hDet⟩
    rw [hHerm.posSemidef_iff_eigenvalues_nonneg]
    have htr : hHerm.eigenvalues 0 + hHerm.eigenvalues 1 ≥ 0 := by
      have heq := hHerm.trace_eq_sum_eigenvalues (𝕜 := ℂ)
      rw [Matrix.trace_fin_two, Fin.sum_univ_two] at heq
      have hre : (M 0 0 + M 1 1).re = hHerm.eigenvalues 0 + hHerm.eigenvalues 1 := by
        rw [heq]; simp
      linarith
    have hdet : hHerm.eigenvalues 0 * hHerm.eigenvalues 1 ≥ 0 := by
      have heq := hHerm.det_eq_prod_eigenvalues (𝕜 := ℂ)
      rw [Matrix.det_fin_two, Fin.prod_univ_two] at heq
      have hre : ((M 0 0) * (M 1 1) - (M 0 1) * (M 1 0)).re =
          hHerm.eigenvalues 0 * hHerm.eigenvalues 1 := by
        rw [heq]; simp
      linarith
    have e0_nn : 0 ≤ hHerm.eigenvalues 0 := by
      nlinarith [sq_nonneg (hHerm.eigenvalues 0 - hHerm.eigenvalues 1)]
    have e1_nn : 0 ≤ hHerm.eigenvalues 1 := by
      nlinarith [sq_nonneg (hHerm.eigenvalues 0 - hHerm.eigenvalues 1)]
    intro i; fin_cases i <;> assumption

/-- Spectral decomposition for 2×2 PSD matrices: M = U · diag(λ) · Uᴴ with λ_k ≥ 0. -/
theorem posSemidef_spectral_decomp (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.PosSemidef) :
    ∃ (lam : Fin 2 → ℝ) (U : Matrix.unitaryGroup (Fin 2) ℂ),
      (∀ k, 0 ≤ lam k) ∧
      M = (U : Matrix (Fin 2) (Fin 2) ℂ) *
          diagonal (RCLike.ofReal ∘ lam) *
          star (U : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨hM.1.eigenvalues, hM.1.eigenvectorUnitary, fun k => hM.eigenvalues_nonneg k, ?_⟩
  conv_lhs => rw [hM.1.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply]

end PPT2.SpectralDim2
