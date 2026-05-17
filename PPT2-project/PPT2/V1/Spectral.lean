/-
V1.Spectral — Spectral-decomposition scaffold for ℂ-matrices at arbitrary d
(specialised to d = 4 for the Bennett et al. 1999 range criterion,
arXiv:quant-ph/9908070).

All statements live in the sandbox namespace `PPT2.V1.Spectral` so they can
coexist with — and eventually be pushed back into — the main PPT2 tree.
-/
import PPT2.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.UnitaryGroup

namespace PPT2.V1.Spectral

open Matrix Complex
open scoped ComplexOrder

/-- Spectral decomposition for arbitrary-dim PSD complex matrices:
    `M = U · diag λ · U†` with every `λ k ≥ 0`.  Direct generalisation of
    `PPT2.SpectralDim2.posSemidef_spectral_decomp` to any `d : ℕ`.
    Discharge route: wrapper over `Matrix.IsHermitian.spectral_theorem` +
    `Matrix.PosSemidef.eigenvalues_nonneg`. -/
theorem psd_spectral_decomp {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosSemidef) :
    ∃ (lam : Fin d → ℝ) (U : Matrix.unitaryGroup (Fin d) ℂ),
      (∀ k, 0 ≤ lam k) ∧
      M = (U : Matrix (Fin d) (Fin d) ℂ) *
          diagonal (RCLike.ofReal ∘ lam) *
          star (U : Matrix (Fin d) (Fin d) ℂ) := by
  refine ⟨hM.1.eigenvalues, hM.1.eigenvectorUnitary,
          fun k => hM.eigenvalues_nonneg k, ?_⟩
  conv_lhs => rw [hM.1.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply]

/-- Non-negativity of PSD eigenvalues re-exported for downstream use in the
    V1 range-criterion pipeline.  Trivial wrapper over
    `Matrix.PosSemidef.eigenvalues_nonneg`. -/
theorem psd_eigenvalues_nonneg {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosSemidef) (k : Fin d) :
    0 ≤ hM.1.eigenvalues k :=
  hM.eigenvalues_nonneg k

/-- Orthonormality of the PSD eigenvector basis.

    Mathlib's `Matrix.IsHermitian.eigenvectorBasis` is an `OrthonormalBasis`
    by construction. This theorem extracts the pairwise orthogonality property
    in the raw dot-product form needed by downstream V1 range-criterion code.

    Proof: `OrthonormalBasis.orthonormal` gives `Orthonormal ℂ hM.1.eigenvectorBasis`,
    which unfolds to pairwise `inner ℂ (basis i) (basis j) = 0` for i ≠ j.
    We then convert `inner` to `star ... ⬝ᵥ ...` via `EuclideanSpace.inner_eq_star_dotProduct`
    and `dotProduct_comm`.
    Cross-ref: Bhatia "Matrix Analysis" §1.4, Horn–Johnson §2.5.4. -/
theorem psd_eigenvector_orthonormal {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosSemidef) :
    ∀ i j : Fin d, i ≠ j →
      (star ((hM.1.eigenvectorBasis i) : EuclideanSpace ℂ (Fin d)) ⬝ᵥ
        ((hM.1.eigenvectorBasis j) : EuclideanSpace ℂ (Fin d))) = 0 := by
  intro i j hij
  have h_ortho := hM.1.eigenvectorBasis.orthonormal
  have h_pair := h_ortho.2
  simp only [Pairwise] at h_pair
  have h_ij := h_pair hij
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h_ij
  rw [dotProduct_comm] at h_ij
  exact h_ij

/-- Range characterisation of PSD complex matrices:
    `range(M)` equals the span of the eigenvectors associated with
    strictly-positive eigenvalues.  This is the central technical
    ingredient of the Bennett et al. 1999 range criterion
    (arXiv:quant-ph/9908070, Thm 3) specialised to d = 4.

    Proof strategy:
    1. Spectral decomposition: M = U · diag(λ) · U†
    2. range(M.mulVecLin) = range(U.mulVecLin ∘ diag(λ).mulVecLin ∘ U†.mulVecLin)
    3. U† is surjective (unitary), so range(diag(λ).mulVecLin ∘ U†.mulVecLin) = range(diag(λ).mulVecLin)
    4. range(diag(λ).mulVecLin) = ⨆ {i | λ i ≠ 0}, range(single i) (range_diagonal)
    5. Since eigenvalues are nonneg, {i | λ i ≠ 0} = {i | 0 < λ i}
    6. U is injective (unitary), so map U.mulVecLin distributes over span
    7. U *ᵥ Pi.single j 1 = eigenvectorBasis j (eigenvectorUnitary_mulVec)

    Cross-ref: Horn–Johnson §2.5.4, Thm 2.5.6 consequence. -/
theorem range_psd_spanned_by_positive_eigenvectors {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosSemidef) :
    LinearMap.range M.mulVecLin =
      Submodule.span ℂ
        ((fun i : Fin d => (fun j => hM.1.eigenvectorUnitary.1 j i)) ''
          {i | 0 < hM.1.eigenvalues i}) := by
  classical
  -- Step 1: M = U * diag(λ) * U†
  have hspec : M = hM.1.eigenvectorUnitary.1 *
      diagonal (RCLike.ofReal ∘ hM.1.eigenvalues) *
      star hM.1.eigenvectorUnitary.1 := by
    conv_lhs => rw [hM.1.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply]
  -- Step 2: rewrite LHS range using spectral decomposition
  have hmulvec : M.mulVecLin =
      hM.1.eigenvectorUnitary.1.mulVecLin.comp
        ((diagonal (RCLike.ofReal ∘ hM.1.eigenvalues)).mulVecLin.comp
          (star hM.1.eigenvectorUnitary.1).mulVecLin) := by
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul, ← mul_assoc, ← hspec]
  rw [show LinearMap.range M.mulVecLin =
      LinearMap.range (hM.1.eigenvectorUnitary.1.mulVecLin.comp
        ((diagonal (RCLike.ofReal ∘ hM.1.eigenvalues)).mulVecLin.comp
          (star hM.1.eigenvectorUnitary.1).mulVecLin)) from
    congr_arg LinearMap.range hmulvec]
  -- Step 3: U† is surjective (unitary), so range(diag ∘ U†) = range(diag)
  have hUstar_surj : Function.Surjective
      (star hM.1.eigenvectorUnitary.1).mulVecLin := by
    intro v
    refine ⟨hM.1.eigenvectorUnitary.1.mulVecLin v, ?_⟩
    simp only [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
    have : star hM.1.eigenvectorUnitary.1 * hM.1.eigenvectorUnitary.1 = 1 :=
      Unitary.coe_star_mul_self hM.1.eigenvectorUnitary
    simp [this]
  rw [LinearMap.range_comp,
      LinearMap.range_comp_of_range_eq_top _
        (LinearMap.range_eq_top.mpr hUstar_surj)]
  -- Step 4: range(diag(λ).mulVecLin) via range_diagonal
  -- range_diagonal uses toLin', which equals mulVecLin
  have hdiag_range : LinearMap.range (diagonal (RCLike.ofReal ∘ hM.1.eigenvalues)).mulVecLin =
      ⨆ i ∈ {i : Fin d | (RCLike.ofReal ∘ hM.1.eigenvalues) i ≠ (0 : ℂ)},
        LinearMap.range (LinearMap.single ℂ (fun _ => ℂ) i) := by
    rw [← Matrix.toLin'_apply', Matrix.range_diagonal]
  rw [hdiag_range]
  -- Step 5: eigenvalues are nonneg, so {i | λ i ≠ 0} = {i | 0 < λ i}
  have hset_eq : {i : Fin d | (RCLike.ofReal ∘ hM.1.eigenvalues) i ≠ (0 : ℂ)} =
      {i : Fin d | 0 < hM.1.eigenvalues i} := by
    ext i
    simp only [Set.mem_setOf_eq, Function.comp_apply, ne_eq, map_eq_zero]
    exact ⟨fun h => lt_of_le_of_ne (hM.eigenvalues_nonneg i) (Ne.symm h),
           fun h => ne_of_gt h⟩
  rw [show (⨆ i ∈ {i : Fin d | (RCLike.ofReal ∘ hM.1.eigenvalues) i ≠ (0 : ℂ)},
        LinearMap.range (LinearMap.single ℂ (fun _ => ℂ) i)) =
      (⨆ i ∈ {i : Fin d | 0 < hM.1.eigenvalues i},
        LinearMap.range (LinearMap.single ℂ (fun _ => ℂ) i)) from by
    simp_rw [hset_eq]]
  -- Step 6: map U.mulVecLin over the biSup
  rw [Submodule.map_iSup]
  simp_rw [Submodule.map_iSup]
  -- Step 7: for each i, map U.mulVecLin (range(single i)) = span {eigenvectorBasis i}
  -- range(single i) = span {Pi.single i 1}
  have hrange_single : ∀ i : Fin d,
      LinearMap.range (LinearMap.single ℂ (fun _ : Fin d => ℂ) i) =
      Submodule.span ℂ {Pi.single i 1} := by
    intro i; ext v
    simp only [LinearMap.mem_range, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩; exact ⟨c, by ext j; simp [LinearMap.single_apply, Pi.single_apply]⟩
    · rintro ⟨c, rfl⟩; exact ⟨c, by ext j; simp [LinearMap.single_apply, Pi.single_apply]⟩
  simp_rw [hrange_single, Submodule.map_span]
  -- Step 8: collapse biSup of singletons into span of image
  -- Goal: ⨆ i ∈ {i | 0 < lam i}, span (U.mulVecLin '' {Pi.single i 1})
  --     = span ((fun i j => U.1 j i) '' {i | 0 < lam i})
  rw [show (⨆ i ∈ {i : Fin d | 0 < hM.1.eigenvalues i},
        Submodule.span ℂ (hM.1.eigenvectorUnitary.1.mulVecLin '' {Pi.single i 1})) =
      Submodule.span ℂ (⋃ i ∈ {i : Fin d | 0 < hM.1.eigenvalues i},
        hM.1.eigenvectorUnitary.1.mulVecLin '' {Pi.single i 1}) from by
    rw [Submodule.span_iUnion₂]]
  congr 1
  ext v
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, hi, w, rfl, rfl⟩
    exact ⟨i, hi, by
      simp only [Matrix.mulVecLin_apply]
      funext j
      simp [Matrix.IsHermitian.eigenvectorUnitary_mulVec,
            Matrix.IsHermitian.eigenvectorUnitary_apply]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, Pi.single i 1, rfl, by
      simp only [Matrix.mulVecLin_apply]
      funext j
      simp [Matrix.IsHermitian.eigenvectorUnitary_mulVec,
            Matrix.IsHermitian.eigenvectorUnitary_apply]⟩

end PPT2.V1.Spectral
