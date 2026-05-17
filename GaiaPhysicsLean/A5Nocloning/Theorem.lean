/- No-cloning theorem
   LKM source claim: gcn_054b79cf1e5740d0
   Tier: A
   See: README.md (this directory)

   **Primary target**: `no_cloning_theorem`

   No unitary U on H⊗H_aux satisfies U(|ψ⟩⊗|0⟩) = |ψ⟩⊗|ψ⟩ for all unit |ψ⟩ ∈ H when dim H ≥ 2.
-/

import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Algebra.Star.Unitary
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace GaiaPhysicsLean.A5Nocloning

open InnerProductSpace TensorProduct Module

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- In a Hilbert space with dimension ≥ 2, there exist unit vectors with inner product ∉ {0,1}. -/
lemma exists_noncollinear (h_dim : finrank 𝕜 E ≥ 2) :
    ∃ (ψ φ : E), ‖ψ‖ = 1 ∧ ‖φ‖ = 1 ∧ inner 𝕜 ψ φ ≠ 0 ∧ inner 𝕜 ψ φ ≠ 1 := by
  have h0 : 0 < finrank 𝕜 E := by omega
  have h1 : 1 < finrank 𝕜 E := by omega
  let b := stdOrthonormalBasis 𝕜 E
  let i0 : Fin (finrank 𝕜 E) := ⟨0, h0⟩
  let i1 : Fin (finrank 𝕜 E) := ⟨1, h1⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1]
  have horth := b.orthonormal
  have hite := orthonormal_iff_ite.mp horth
  -- ψ = (1/√2)•(e₀+e₁), φ = e₀ gives ⟨ψ,φ⟩ = 1/√2 ∉ {0,1}
  let c : 𝕜 := ((Real.sqrt 2)⁻¹ : ℝ)
  refine ⟨c • (b i0 + b i1), b i0, ?_, horth.1 i0, ?_, ?_⟩
  · have h_inner_zero : inner 𝕜 (b i0) (b i1) = 0 := by simp [hite, h01]
    have h_norm_sum : ‖b i0 + b i1‖ = Real.sqrt 2 := by
      have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (b i0) (b i1) h_inner_zero
      rw [horth.1 i0, horth.1 i1] at this
      nlinarith [norm_nonneg (b i0 + b i1), Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),
                 Real.sqrt_nonneg 2]
    simp only [c, norm_smul, RCLike.norm_ofReal, h_norm_sum,
               abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg 2))]
    exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num))
  · simp only [c, inner_smul_left, inner_add_left, hite, h01.symm, if_true, if_false,
               add_zero, mul_one, RCLike.conj_ofReal]
    exact_mod_cast inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num))
  · simp only [c, inner_smul_left, inner_add_left, hite, h01.symm, if_true, if_false,
               add_zero, mul_one, RCLike.conj_ofReal]
    intro h
    have : (Real.sqrt 2)⁻¹ = 1 := by exact_mod_cast h
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), inv_eq_one.mp this]

/-- No-cloning theorem: No unitary operator can clone arbitrary quantum states.
    We state it as: there is no linear isometric equivalence U : E ⊗ F ≃ₗᵢ[𝕜] E ⊗ E
    that maps ψ ⊗ e₀ to ψ ⊗ ψ for all unit ψ. -/
theorem no_cloning_theorem (h_dim : finrank 𝕜 E ≥ 2) (e₀ : F) (he₀ : ‖e₀‖ = 1) :
    ¬∃ (U : (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] (E ⊗[𝕜] E)),
      ∀ (ψ : E), ‖ψ‖ = 1 → U (ψ ⊗ₜ[𝕜] e₀) = ψ ⊗ₜ[𝕜] ψ := by
  intro ⟨U, hclone⟩
  -- Get two non-collinear unit vectors
  obtain ⟨ψ, φ, hψ_norm, hφ_norm, hinner_ne0, hinner_ne1⟩ := exists_noncollinear h_dim
  -- Apply cloning property
  have hψ_clone : U (ψ ⊗ₜ[𝕜] e₀) = ψ ⊗ₜ[𝕜] ψ := hclone ψ hψ_norm
  have hφ_clone : U (φ ⊗ₜ[𝕜] e₀) = φ ⊗ₜ[𝕜] φ := hclone φ hφ_norm
  -- Compute: ⟨U(ψ⊗e₀), U(φ⊗e₀)⟩ = ⟨ψ⊗e₀, φ⊗e₀⟩ = ⟨ψ,φ⟩⟨e₀,e₀⟩ = ⟨ψ,φ⟩
  have lhs_eq : inner 𝕜 (U (ψ ⊗ₜ[𝕜] e₀)) (U (φ ⊗ₜ[𝕜] e₀)) = inner 𝕜 ψ φ := by
    rw [U.inner_map_map, inner_tmul 𝕜]
    simp [he₀]
  -- But U(ψ⊗e₀) = ψ⊗ψ and U(φ⊗e₀) = φ⊗φ, so LHS = ⟨ψ⊗ψ, φ⊗φ⟩ = ⟨ψ,φ⟩²
  rw [hψ_clone, hφ_clone, inner_tmul 𝕜] at lhs_eq
  -- We have ⟨ψ,φ⟩² = ⟨ψ,φ⟩
  have : (inner 𝕜 ψ φ) * (inner 𝕜 ψ φ) = inner 𝕜 ψ φ := lhs_eq
  -- This means ⟨ψ,φ⟩ * (⟨ψ,φ⟩ - 1) = 0
  have : inner 𝕜 ψ φ * (inner 𝕜 ψ φ - 1) = 0 := by ring_nf; linear_combination this
  -- So ⟨ψ,φ⟩ = 0 or ⟨ψ,φ⟩ = 1
  rcases mul_eq_zero.mp this with h | h
  · exact hinner_ne0 h
  · have : inner 𝕜 ψ φ = 1 := by linear_combination h
    exact hinner_ne1 this

end GaiaPhysicsLean.A5Nocloning
