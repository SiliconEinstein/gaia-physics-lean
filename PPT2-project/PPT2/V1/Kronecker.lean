/-
V1.Kronecker — PSD + range lemmas for the Kronecker product, specialised
to the V1 range-criterion pipeline at d = 4.

The pure PSD-preservation result is already in Mathlib
(`Matrix.PosSemidef.kronecker`), so that one is a theorem-wrapper.
The range-factorisation lemma
`range(A ⊗ B) = range A ⊗ range B` requires more machinery
(Horn–Johnson 1991 "Topics in Matrix Analysis" §4.2.12); we state it
precisely as a sandbox axiom with a full discharge route recorded
in README.md.
-/
import PPT2.Basic
import PPT2.MatrixTensor
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Matrix.Order

namespace PPT2.V1.Kron

open Matrix BigOperators
open scoped ComplexOrder Kronecker

/-- PSD-preservation of the Kronecker product: the tensor product of
    two PSD matrices is PSD.  Thin wrapper over Mathlib's
    `Matrix.PosSemidef.kronecker`. -/
theorem psd_kronecker {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A ⊗ₖ B).PosSemidef :=
  hA.kronecker hB

/-- PSD-preservation re-stated in the PPT2 `kron`-alias flavour used by
    the rest of the project (`PPT2.MatrixTensor.kron`). -/
theorem psd_kron {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (PPT2.kron A B).PosSemidef :=
  hA.kronecker hB

/-- Range-factorisation of the Kronecker product of PSD matrices:
      `range (A ⊗ B) = range A ⊗ range B`
    where the right-hand side is understood as the image in
    `(Fin d × Fin d → ℂ)` of the submodule obtained by taking all
    elementary tensors `a ⊗ b` with `a ∈ range A`, `b ∈ range B`.

    The V1 range criterion needs this in the form:
    a separable state `ρ = Σ p_i |ψ_i⟩⟨ψ_i| ⊗ |φ_i⟩⟨φ_i|` has
    `range ρ` spanned by product vectors `|ψ_i ⊗ φ_i⟩`.

    Proof: this is pure linear algebra, the PSD hypotheses are
    not actually needed.  We use `Matrix.range_mulVecLin` to
    rewrite each side in terms of column spans.  The forward
    direction is immediate from
    `(A ⊗ₖ B).col (j₁, j₂) p = A.col j₁ p.1 * B.col j₂ p.2`.
    The reverse direction uses the explicit lift
    `z (j₁, j₂) = x j₁ * y j₂` so that
    `(A ⊗ₖ B) *ᵥ z = fun p ↦ (A *ᵥ x) p.1 * (B *ᵥ y) p.2`,
    which follows from `Finset.sum_mul_sum`.
    Cross-ref: Horn–Johnson 1991 §4.2.12. -/
theorem range_kronecker_factors {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℂ)
    (_hA : A.PosSemidef) (_hB : B.PosSemidef) :
    LinearMap.range (A ⊗ₖ B).mulVecLin =
      Submodule.span ℂ
        { v : Fin d × Fin d → ℂ |
            ∃ a ∈ LinearMap.range A.mulVecLin,
              ∃ b ∈ LinearMap.range B.mulVecLin,
              v = fun p => a p.1 * b p.2 } := by
  set M := A ⊗ₖ B with hM_def
  -- Column structure of `M`.
  have hcol : ∀ j : Fin d × Fin d,
      M.col j = fun p => A.col j.1 p.1 * B.col j.2 p.2 := by
    rintro ⟨j₁, j₂⟩
    funext ⟨p₁, p₂⟩
    simp [hM_def, Matrix.col_apply]
  apply le_antisymm
  · -- (⊆) range of `A ⊗ₖ B` is the span of its columns; each column is a product.
    rw [Matrix.range_mulVecLin, Submodule.span_le]
    rintro v ⟨j, rfl⟩
    rw [hcol j]
    refine Submodule.subset_span ⟨A.col j.1, ?_, B.col j.2, ?_, rfl⟩
    · rw [Matrix.range_mulVecLin]
      exact Submodule.subset_span (Set.mem_range_self _)
    · rw [Matrix.range_mulVecLin]
      exact Submodule.subset_span (Set.mem_range_self _)
  · -- (⊇) every product `(A *ᵥ x) ⊗ (B *ᵥ y)` lies in range via the tensor lift.
    rw [Submodule.span_le]
    rintro v ⟨a, ha, b, hb, rfl⟩
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    refine ⟨fun q => x q.1 * y q.2, ?_⟩
    ext p
    show (M *ᵥ fun q => x q.1 * y q.2) p = _
    rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    have hreorg : ∀ j₁ j₂ : Fin d,
        M p (j₁, j₂) * (x j₁ * y j₂) =
          (A p.1 j₁ * x j₁) * (B p.2 j₂ * y j₂) := by
      intro j₁ j₂
      simp [hM_def]; ring
    simp_rw [hreorg]
    show _ = (A.mulVecLin x) p.1 * (B.mulVecLin y) p.2
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
        Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct,
        ← Finset.sum_mul_sum]



/-- Specialisation of the range-factorisation lemma to rank-1 PSD
    projectors `|ψ⟩⟨ψ|`, which is the only form actually consumed
    by the V1 range-criterion walk-through at d = 4.

    Direct proof (no longer dependent on `range_kronecker_factors`):
    every column of
    `vecMulVec ψ (star ψ) ⊗ₖ vecMulVec φ (star φ)`
    is a scalar multiple of the rank-1 product vector
    `fun p ↦ ψ p.1 * φ p.2`, and (when that vector is nonzero)
    the scalar is invertible at any column index where both
    `star ψ` and `star φ` are nonzero.  Combined with
    `Matrix.range_mulVecLin` this gives equality of the two spans.
    Cross-ref: Horn–Johnson 1991 §4.2.12 Cor. -/
theorem range_kronecker_rank_one {d : ℕ}
    (ψ φ : Fin d → ℂ) :
    LinearMap.range
        (vecMulVec ψ (star ψ) ⊗ₖ vecMulVec φ (star φ)).mulVecLin =
      Submodule.span ℂ ({fun p : Fin d × Fin d => ψ p.1 * φ p.2} : Set _) := by
  set M := vecMulVec ψ (star ψ) ⊗ₖ vecMulVec φ (star φ) with hM_def
  set g : Fin d × Fin d → ℂ := fun p => ψ p.1 * φ p.2 with hg_def
  -- Each column of M is a scalar multiple of g.
  have hcol : ∀ (j : Fin d × Fin d), M.col j = (star ψ j.1 * star φ j.2) • g := by
    rintro ⟨j₁, j₂⟩
    funext ⟨p₁, p₂⟩
    simp only [hM_def, Matrix.col_apply, Matrix.kronecker_apply,
               Matrix.vecMulVec_apply, hg_def, Pi.smul_apply, smul_eq_mul]
    ring
  rw [Matrix.range_mulVecLin]
  apply le_antisymm
  · -- (⊆) every column lies in `span {g}`.
    rw [Submodule.span_le]
    rintro x ⟨j, rfl⟩
    rw [hcol j]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · -- (⊇) `g` lies in `span (range M.col)`.
    rw [Submodule.span_le, Set.singleton_subset_iff]
    by_cases hg0 : g = 0
    · rw [hg0]; exact Submodule.zero_mem _
    · obtain ⟨p, hp⟩ : ∃ p, g p ≠ 0 := by
        by_contra h
        apply hg0
        funext q
        by_contra hq
        exact h ⟨q, hq⟩
      -- Both ψ p.1 and φ p.2 are nonzero, so the scalar at column `p` is nonzero.
      have hψp : ψ p.1 ≠ 0 := fun h => hp (by simp [hg_def, h])
      have hφp : φ p.2 ≠ 0 := fun h => hp (by simp [hg_def, h])
      have hsψ : star ψ p.1 ≠ 0 := by
        change star (ψ p.1) ≠ 0
        exact star_ne_zero.mpr hψp
      have hsφ : star φ p.2 ≠ 0 := by
        change star (φ p.2) ≠ 0
        exact star_ne_zero.mpr hφp
      have hc : star ψ p.1 * star φ p.2 ≠ 0 := mul_ne_zero hsψ hsφ
      have h1 : M.col p ∈ Submodule.span ℂ (Set.range M.col) :=
        Submodule.subset_span (Set.mem_range_self _)
      have h2 : g = (star ψ p.1 * star φ p.2)⁻¹ • M.col p := by
        rw [hcol p, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [h2]
      exact Submodule.smul_mem _ _ h1

end PPT2.V1.Kron
