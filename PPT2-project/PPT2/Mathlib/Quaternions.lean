/-
Copyright (c) 2026 Gaia Discovery. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaia Discovery Agent
-/
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Instances.Matrix

/-!
# SU(2) and Unit Quaternions

This file establishes the standard correspondence between SU(2) — the special
unitary group of `2 × 2` complex matrices — and the unit quaternions inside
`Quaternion ℝ`.

## Main definitions

* `Quaternion.norm`             — the Euclidean norm `sqrt (normSq q)` of a real quaternion;
* `Quaternion.UnitQuaternion`   — the submonoid of norm-one quaternions;
* `Quaternion.toMatrix`         — the SU(2)-style 2×2 complex matrix associated with a
  real quaternion;
* `Quaternion.fromMatrix`       — the real quaternion read off from a 2×2 complex matrix
  (left inverse of `toMatrix`);
* `Quaternion.toMatrix_fromMatrix_of_unitary` — the round-trip identity that holds
  on `SU(2)` (i.e. unitary matrices with determinant 1);
* `Quaternion.su2EquivUnitQuaternion` — the `Equiv` between SU(2) (as a subset of
  `unitaryGroup (Fin 2) ℂ`) and `{q : Quaternion ℝ // ‖q‖ = 1}`.

The map `q ↦ toMatrix q` is multiplicative (`toMatrix_mul`), unit-preserving
(`toMatrix_one`) and intertwines `star` with `Matrix.star`/conjugate-transpose
(`toMatrix_star`). Promoting `su2EquivUnitQuaternion` to a `MulEquiv` only
requires endowing the SU(2) subset with a `Group` instance pulled back from the
unitary group; that promotion is the next file in the development.

## Implementation notes

We work directly with `Quaternion ℝ` (Mathlib notation `ℍ[ℝ]`). For
`q = a + b·i + c·j + d·k`, we send it to
`!![ a + b·i,  c + d·i ; -c + d·i,  a - b·i ]`. This is the standard
quaternion-to-`SU(2)` representation; one checks directly that
`det = a² + b² + c² + d² = normSq q` and the matrix is unitary iff `‖q‖ = 1`.
-/

open scoped Quaternion ComplexConjugate

open Matrix Complex

namespace Quaternion

local notation "ℝℍ" => Quaternion ℝ

/-! ### Norm of a real quaternion -/

/-- Real-valued Euclidean norm of a quaternion. -/
noncomputable def «norm» (q : ℝℍ) : ℝ := Real.sqrt (normSq q)

@[simp]
theorem norm_sq_eq_normSq (q : ℝℍ) : (Quaternion.norm q) ^ 2 = normSq q := by
  rw [Quaternion.norm, sq]
  exact Real.mul_self_sqrt normSq_nonneg

theorem norm_nonneg (q : ℝℍ) : 0 ≤ Quaternion.norm q :=
  Real.sqrt_nonneg _

theorem norm_eq_zero_iff (q : ℝℍ) : Quaternion.norm q = 0 ↔ q = 0 := by
  rw [Quaternion.norm, Real.sqrt_eq_zero normSq_nonneg]
  exact normSq_eq_zero

theorem norm_mul (q₁ q₂ : ℝℍ) :
    Quaternion.norm (q₁ * q₂) = Quaternion.norm q₁ * Quaternion.norm q₂ := by
  rw [Quaternion.norm, Quaternion.norm, Quaternion.norm,
    ← Real.sqrt_mul normSq_nonneg, map_mul]

theorem norm_star (q : ℝℍ) : Quaternion.norm (star q) = Quaternion.norm q := by
  simp [Quaternion.norm, normSq_star]

theorem normSq_eq_one_of_norm_eq_one {q : ℝℍ} (hq : Quaternion.norm q = 1) :
    normSq q = 1 := by
  have h := norm_sq_eq_normSq q
  rw [hq, one_pow] at h
  exact h.symm

@[simp] theorem norm_one : Quaternion.norm (1 : ℝℍ) = 1 := by
  rw [Quaternion.norm]
  simp

/-- The submonoid of unit quaternions inside `Quaternion ℝ`. -/
def UnitQuaternion : Submonoid (Quaternion ℝ) where
  carrier := {q | Quaternion.norm q = 1}
  one_mem' := by show Quaternion.norm (1 : ℝℍ) = 1; simp
  mul_mem' := by
    intro a b ha hb
    show Quaternion.norm (a * b) = 1
    rw [Quaternion.norm_mul, ha, hb, mul_one]

@[simp] theorem mem_unitQuaternion {q : ℝℍ} :
    q ∈ UnitQuaternion ↔ Quaternion.norm q = 1 := Iff.rfl

/-! ### `toMatrix` and its algebraic properties -/

/-- The `2 × 2` complex matrix associated with a real quaternion
`q = a + b i + c j + d k`. -/
def toMatrix (q : ℝℍ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩;
     ⟨-q.imJ, q.imK⟩, ⟨q.re, -q.imI⟩]

@[simp] theorem toMatrix_apply_00 (q : ℝℍ) : toMatrix q 0 0 = ⟨q.re, q.imI⟩ := rfl
@[simp] theorem toMatrix_apply_01 (q : ℝℍ) : toMatrix q 0 1 = ⟨q.imJ, q.imK⟩ := rfl
@[simp] theorem toMatrix_apply_10 (q : ℝℍ) : toMatrix q 1 0 = ⟨-q.imJ, q.imK⟩ := rfl
@[simp] theorem toMatrix_apply_11 (q : ℝℍ) : toMatrix q 1 1 = ⟨q.re, -q.imI⟩ := rfl

theorem toMatrix_one : toMatrix (1 : ℝℍ) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [toMatrix, Matrix.one_apply, Complex.ext_iff]

theorem toMatrix_mul (q₁ q₂ : ℝℍ) :
    toMatrix (q₁ * q₂) = toMatrix q₁ * toMatrix q₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp only [toMatrix_apply_00, toMatrix_apply_01, toMatrix_apply_10, toMatrix_apply_11,
        Matrix.mul_apply, Fin.sum_univ_two, re_mul, imI_mul, imJ_mul, imK_mul]
      apply Complex.ext <;>
        · simp [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im]; ring

theorem toMatrix_star (q : ℝℍ) :
    toMatrix (star q) = star (toMatrix q) := by
  rw [Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp only [toMatrix_apply_00, toMatrix_apply_01, toMatrix_apply_10, toMatrix_apply_11,
        Matrix.conjTranspose_apply, re_star, imI_star, imJ_star, imK_star, neg_neg]
      apply Complex.ext <;> simp

/-- `det (toMatrix q) = (normSq q : ℂ)`. -/
theorem det_toMatrix (q : ℝℍ) : det (toMatrix q) = ((Quaternion.normSq q : ℝ) : ℂ) := by
  rw [det_fin_two]
  simp only [toMatrix_apply_00, toMatrix_apply_01, toMatrix_apply_10, toMatrix_apply_11]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.neg_im, Complex.neg_re,
      Complex.ofReal_re, Quaternion.normSq_def', Complex.ofReal_im]
    ring
  · simp only [Complex.mul_im, Complex.mul_re, Complex.sub_im, Complex.neg_im, Complex.neg_re,
      Complex.ofReal_im]
    ring

/-- A unit quaternion lands inside the unitary group. -/
theorem toMatrix_mem_unitaryGroup (q : ℝℍ) (hq : Quaternion.norm q = 1) :
    toMatrix q ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, ← toMatrix_star, ← toMatrix_mul]
  have hns : normSq q = 1 := normSq_eq_one_of_norm_eq_one hq
  have hsq : q * star q = (1 : ℝℍ) := by
    rw [Quaternion.self_mul_star, hns]
    push_cast
    rfl
  rw [hsq, toMatrix_one]

/-- A unit quaternion has determinant `1` in `ℂ`. -/
theorem det_toMatrix_of_norm_eq_one (q : ℝℍ) (hq : Quaternion.norm q = 1) :
    det (toMatrix q) = 1 := by
  rw [det_toMatrix, normSq_eq_one_of_norm_eq_one hq]
  simp

/-! ### `fromMatrix` and the round trip on SU(2) -/

/-- Recover a real quaternion from a `2 × 2` complex matrix.
A left inverse to `toMatrix`; right inverse on SU(2). -/
def fromMatrix (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝℍ :=
  ⟨(M 0 0).re, (M 0 0).im, (M 0 1).re, (M 0 1).im⟩

@[simp] theorem fromMatrix_re  (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (fromMatrix M).re  = (M 0 0).re := rfl
@[simp] theorem fromMatrix_imI (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (fromMatrix M).imI = (M 0 0).im := rfl
@[simp] theorem fromMatrix_imJ (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (fromMatrix M).imJ = (M 0 1).re := rfl
@[simp] theorem fromMatrix_imK (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (fromMatrix M).imK = (M 0 1).im := rfl

@[simp]
theorem fromMatrix_toMatrix (q : ℝℍ) : fromMatrix (toMatrix q) = q := by
  apply Quaternion.ext <;> simp [fromMatrix, toMatrix]

/-- The structural identity for SU(2): every 2×2 unitary matrix with `det = 1`
is exactly the matrix produced by `toMatrix` from its quaternion image. The
proof uses Cramer's rule (`adjugate_fin_two`) which states that for `M` with
`det M = 1`, we have `M⁻¹ = !![M 1 1, -M 0 1; -M 1 0, M 0 0]`; combined with
unitarity `M⁻¹ = star M`, this forces the SU(2) shape. -/
theorem toMatrix_fromMatrix_of_unitary {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : det M = 1) :
    toMatrix (fromMatrix M) = M := by
  -- Step 1: For unitary `M`, `M⁻¹ = star M`.
  have hMM : M * star M = 1 := Matrix.mem_unitaryGroup_iff.mp hM
  have hinv_eq_star : M⁻¹ = star M := Matrix.inv_eq_right_inv hMM
  -- Step 2: For `det M = 1`, Cramer's rule gives the cofactor formula.
  have hcof : M⁻¹ = !![M 1 1, -M 0 1; -M 1 0, M 0 0] := by
    rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul,
      show M = !![M 0 0, M 0 1; M 1 0, M 1 1] from by
        ext i j; fin_cases i <;> fin_cases j <;> rfl,
      Matrix.adjugate_fin_two_of]
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  -- Step 3: combine to get explicit form of `star M`.
  have hstar : star M = !![M 1 1, -M 0 1; -M 1 0, M 0 0] := by
    rw [← hinv_eq_star, hcof]
  -- Step 4: read off entry-wise consequences.
  have h11 : M 1 1 = conj (M 0 0) := by
    have h := congr_fun (congr_fun hstar 0) 0
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply] at h
    -- h : conj (M 0 0) = M 1 1
    exact h.symm
  have h10 : M 1 0 = -conj (M 0 1) := by
    have h := congr_fun (congr_fun hstar 0) 1
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply] at h
    -- h : conj (M 1 0) = -M 0 1
    -- Hence M 1 0 = conj (-M 0 1) = -conj (M 0 1).
    have hM10 : M 1 0 = conj (-M 0 1) := by
      have hcc : conj (conj (M 1 0)) = conj (-M 0 1) := congrArg conj h
      simpa using hcc
    rw [hM10, map_neg]
  -- Step 5: entry-by-entry comparison with `toMatrix (fromMatrix M)`.
  ext i j
  fin_cases i <;> fin_cases j
  · -- (0,0): from definition of `fromMatrix` and `toMatrix`
    show toMatrix (fromMatrix M) 0 0 = M 0 0
    rw [toMatrix_apply_00]
    apply Complex.ext <;> rfl
  · -- (0,1)
    show toMatrix (fromMatrix M) 0 1 = M 0 1
    rw [toMatrix_apply_01]
    apply Complex.ext <;> rfl
  · -- (1,0): use h10
    show toMatrix (fromMatrix M) 1 0 = M 1 0
    rw [toMatrix_apply_10, h10]
    apply Complex.ext
    · simp [Complex.neg_re, Complex.conj_re, fromMatrix_imJ]
    · simp [Complex.neg_im, Complex.conj_im, fromMatrix_imK]
  · -- (1,1): use h11
    show toMatrix (fromMatrix M) 1 1 = M 1 1
    rw [toMatrix_apply_11, h11]
    apply Complex.ext
    · simp [Complex.conj_re, fromMatrix_re]
    · simp [Complex.conj_im, fromMatrix_imI]

/-! ### `Equiv` between SU(2) and unit quaternions -/

/-- The `Equiv` between SU(2) (as a subset of `unitaryGroup (Fin 2) ℂ` cut out
by the determinant-one condition) and the unit quaternions.

To upgrade this to a `MulEquiv` one needs a `Group` structure on the SU(2)
subset; that is straightforward (the unitary group restricted to determinant
one is a subgroup) but is performed in the next file in the development. -/
noncomputable def su2EquivUnitQuaternion :
    {U : Matrix.unitaryGroup (Fin 2) ℂ //
      Matrix.det (U : Matrix (Fin 2) (Fin 2) ℂ) = 1} ≃
    {q : ℝℍ // q ∈ UnitQuaternion} where
  toFun U :=
    ⟨fromMatrix (U.1 : Matrix (Fin 2) (Fin 2) ℂ), by
      -- the image has norm one
      show Quaternion.norm _ = 1
      set M : Matrix (Fin 2) (Fin 2) ℂ := (U.1 : Matrix (Fin 2) (Fin 2) ℂ) with hM_def
      have hM_det : Matrix.det M = 1 := U.2
      have hns : normSq (fromMatrix M) = 1 := by
        -- From `M * star M = 1`, the (0,0)-entry gives `|M00|² + |M01|² = 1`.
        have hMM : M * star M = 1 :=
          Matrix.mem_unitaryGroup_iff.mp U.1.2
        have hinv_eq_star : M⁻¹ = star M :=
          Matrix.inv_eq_right_inv hMM
        have hcof : M⁻¹ =
            !![M 1 1, -M 0 1;
               -M 1 0, M 0 0] := by
          rw [Matrix.inv_def, hM_det, Ring.inverse_one, one_smul,
            show M = !![M 0 0, M 0 1; M 1 0, M 1 1] from by
              ext i j; fin_cases i <;> fin_cases j <;> rfl,
            Matrix.adjugate_fin_two_of]
          ext i j; fin_cases i <;> fin_cases j <;> rfl
        have hstar :
            star M = !![M 1 1, -M 0 1; -M 1 0, M 0 0] := by
          rw [← hinv_eq_star, hcof]
        -- From hstar, `(star M) 1 1 = M 0 0` so `conj (M 1 1) = M 0 0`, i.e. `|M 1 1|² = M00 * conj M00 = |M00|²`.
        -- Easier: use that `M 1 1 = conj (M 0 0)` (deduced from hstar(0,0) = M 1 1).
        have h11 : M 1 1 = conj (M 0 0) := by
          have h := congr_fun (congr_fun hstar 0) 0
          simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
            Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
            Matrix.cons_val_fin_one, Matrix.of_apply] at h
          exact h.symm
        have h10 : M 1 0 = -conj (M 0 1) := by
          have h := congr_fun (congr_fun hstar 0) 1
          simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
            Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.empty_val', Matrix.cons_val_fin_one,
            Matrix.of_apply] at h
          have hM10 : M 1 0 = conj (-M 0 1) := by
            have hcc : conj (conj (M 1 0)) = conj (-M 0 1) := congrArg conj h
            simpa using hcc
          rw [hM10, map_neg]
        -- det formula: det M = M00*M11 - M01*M10 = M00*conj M00 + M01*conj M01.
        have hdet_expand :
            M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
          rw [← det_fin_two]; exact hM_det
        rw [h11, h10] at hdet_expand
        -- M00 * conj M00 - M01 * (-conj M01) = M00 * conj M00 + M01 * conj M01
        have h_cs : M 0 0 * conj (M 0 0) + M 0 1 * conj (M 0 1) = 1 := by
          linear_combination hdet_expand
        -- This is `|M00|² + |M01|² = 1` as complex numbers, so as real numbers too.
        have hns00 : M 0 0 * conj (M 0 0) = (Complex.normSq (M 0 0) : ℂ) := by
          rw [mul_comm, Complex.normSq_eq_conj_mul_self]
        have hns01 : M 0 1 * conj (M 0 1) = (Complex.normSq (M 0 1) : ℂ) := by
          rw [mul_comm, Complex.normSq_eq_conj_mul_self]
        rw [hns00, hns01] at h_cs
        -- Now extract real equality.
        have hsum_complex : (Complex.normSq (M 0 0) : ℂ) +
               (Complex.normSq (M 0 1) : ℂ) = (1 : ℂ) := h_cs
        have hreal : Complex.normSq (M 0 0) + Complex.normSq (M 0 1) = (1 : ℝ) := by
          have hc : ((Complex.normSq (M 0 0) +
                       Complex.normSq (M 0 1) : ℝ) : ℂ) = (1 : ℂ) := by
            push_cast; exact hsum_complex
          exact_mod_cast hc
        -- Convert to `normSq (fromMatrix M)`.
        rw [Quaternion.normSq_def']
        simp only [fromMatrix_re, fromMatrix_imI, fromMatrix_imJ, fromMatrix_imK]
        have e0 : Complex.normSq (M 0 0) = (M 0 0).re ^ 2 + (M 0 0).im ^ 2 := by
          simp [Complex.normSq_apply, sq]
        have e1 : Complex.normSq (M 0 1) = (M 0 1).re ^ 2 + (M 0 1).im ^ 2 := by
          simp [Complex.normSq_apply, sq]
        linarith [hreal, e0, e1]
      rw [Quaternion.norm, hns, Real.sqrt_one]⟩
  invFun q :=
    ⟨⟨toMatrix q.1, toMatrix_mem_unitaryGroup q.1 q.2⟩,
      det_toMatrix_of_norm_eq_one q.1 q.2⟩
  left_inv U := by
    apply Subtype.ext
    apply Subtype.ext
    show toMatrix (fromMatrix (U.1 : Matrix (Fin 2) (Fin 2) ℂ)) =
        (U.1 : Matrix (Fin 2) (Fin 2) ℂ)
    exact toMatrix_fromMatrix_of_unitary U.1.2 U.2
  right_inv q := by
    apply Subtype.ext
    show fromMatrix (toMatrix q.1) = q.1
    exact fromMatrix_toMatrix q.1

/-- Multiplicativity of the SU(2) → UnitQuaternion direction at the matrix level.
This is the input needed to upgrade `su2EquivUnitQuaternion` to a `MulEquiv`. -/
theorem fromMatrix_mul_of_SU2 {U V : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hUd : det U = 1)
    (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hVd : det V = 1) :
    fromMatrix (U * V) = fromMatrix U * fromMatrix V := by
  -- `toMatrix` is injective via `fromMatrix_toMatrix`, and is multiplicative.
  have hUid : toMatrix (fromMatrix U) = U := toMatrix_fromMatrix_of_unitary hU hUd
  have hVid : toMatrix (fromMatrix V) = V := toMatrix_fromMatrix_of_unitary hV hVd
  -- The product is in SU(2).
  have hprod_unit : (U * V) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have hUu : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
    have hVu : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp hV
    rw [star_mul, ← mul_assoc, mul_assoc U V, hVu, mul_one, hUu]
  have hprod_det : det (U * V) = 1 := by rw [Matrix.det_mul, hUd, hVd, mul_one]
  have hprodid : toMatrix (fromMatrix (U * V)) = U * V :=
    toMatrix_fromMatrix_of_unitary hprod_unit hprod_det
  -- Apply `fromMatrix` to `toMatrix_mul`.
  have key : toMatrix (fromMatrix U * fromMatrix V) = U * V := by
    rw [toMatrix_mul, hUid, hVid]
  have : toMatrix (fromMatrix (U * V)) = toMatrix (fromMatrix U * fromMatrix V) := by
    rw [hprodid, key]
  have := congr_arg fromMatrix this
  simpa [fromMatrix_toMatrix] using this

/-- Public alias matching the requested `su2IsoUnitQuaternion` name.

Note: this is a plain `Equiv`, not a `MulEquiv`. Promotion to `MulEquiv` requires
endowing the SU(2) subset with a `Group` instance pulled back from
`Matrix.unitaryGroup`; the multiplicativity input
`fromMatrix_mul_of_SU2` is already proved here. -/
noncomputable abbrev su2IsoUnitQuaternion := su2EquivUnitQuaternion

end Quaternion
