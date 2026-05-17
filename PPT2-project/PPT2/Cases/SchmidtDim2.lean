/-
PPT2.Cases.SchmidtDim2 — Schmidt decomposition existence for ℂ² ⊗ ℂ².

P3 step (d) foundation lemma for the PPT → Separable proof at d = 2
(Peres–Horodecki 1996).  We use the brute-force "row decomposition" form:

  s k := ‖row k of v‖∞   (sup norm on Fin 2 → ℂ)
  a k := e_k             (standard basis vector)
  b k := (row k of v) / (s k)   (Lean: division by zero gives zero)

which gives `v (i, j) = ∑ k, s k · a k i · b k j` with `s k ≥ 0` and
`‖a k‖, ‖b k‖ ≤ 1` (sup-norm) — sufficient for downstream PPT→Separable use.
-/
import PPT2.Basic
import PPT2.Cases.SpectralDim2
import PPT2.Separable
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Constructions

namespace PPT2.SchmidtDim2

open Finset
open Matrix
open scoped Kronecker ComplexOrder

/--
**Schmidt decomposition existence (d = 2)**, constructive form.

Every vector in ℂ² ⊗ ℂ² (encoded as `v : Fin 2 × Fin 2 → ℂ`) admits a 2-term
decomposition
  `v (i, j) = ∑ k : Fin 2, (s k : ℂ) * a k i * b k j`
with `s k ≥ 0` and `‖a k‖ ≤ 1`, `‖b k‖ ≤ 1` (sup-norm on `Fin 2 → ℂ`).
-/
theorem schmidt_decomp_vector_dim2
    (v : Fin 2 × Fin 2 → ℂ) :
    ∃ (s : Fin 2 → ℝ) (a b : Fin 2 → Fin 2 → ℂ),
      (∀ k, 0 ≤ s k) ∧
      (∀ k, ‖fun i => a k i‖ ≤ 1) ∧
      (∀ k, ‖fun j => b k j‖ ≤ 1) ∧
      v = fun ⟨i, j⟩ => ∑ k : Fin 2, (s k : ℂ) * a k i * b k j := by
  -- Define the witnesses.
  refine ⟨fun k => ‖fun j => v (k, j)‖,
          fun k i => if i = k then (1 : ℂ) else 0,
          fun k j => v (k, j) / ((‖fun j' => v (k, j')‖ : ℝ) : ℂ),
          ?_, ?_, ?_, ?_⟩
  -- (1) s k ≥ 0
  · intro k; exact norm_nonneg _
  -- (2) ‖a k‖ ≤ 1
  · intro k
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    by_cases h : i = k
    · simp [h]
    · simp [h]
  -- (3) ‖b k‖ ≤ 1
  · intro k
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    by_cases hk : ‖fun j' => v (k, j')‖ = 0
    · simp [hk]
    · have hpos : 0 < ‖fun j' => v (k, j')‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hk)
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      exact div_le_one_of_le₀ (norm_le_pi_norm (fun j' => v (k, j')) j) hpos.le
  -- (4) v reconstruction: pointwise equality at (i, j).
  · funext ⟨i, j⟩
    -- For each k, (s k : ℂ) * (v (k, j) / (s k : ℂ)) = v (k, j), handling
    -- the s k = 0 case via norm_le_pi_norm forcing v (k, j) = 0.
    have key : ∀ k : Fin 2,
        ((‖fun j' => v (k, j')‖ : ℝ) : ℂ) *
          (v (k, j) / ((‖fun j' => v (k, j')‖ : ℝ) : ℂ)) = v (k, j) := by
      intro k
      by_cases hk : ‖fun j' => v (k, j')‖ = 0
      · have hvkj : v (k, j) = 0 := by
          have h1 : ‖v (k, j)‖ ≤ ‖fun j' => v (k, j')‖ :=
            norm_le_pi_norm (fun j' => v (k, j')) j
          rw [hk] at h1
          exact norm_eq_zero.mp (le_antisymm h1 (norm_nonneg _))
        simp [hvkj, hk]
      · have h : ((‖fun j' => v (k, j')‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk
        field_simp
    -- Per-summand simplification: the `a` indicator collapses the sum.
    have step : ∀ k : Fin 2,
        ((‖fun j' => v (k, j')‖ : ℝ) : ℂ) *
            (if i = k then (1 : ℂ) else 0) *
            (v (k, j) / ((‖fun j' => v (k, j')‖ : ℝ) : ℂ)) =
          if i = k then v (k, j) else 0 := by
      intro k
      by_cases h : i = k
      · subst h
        simp [key i]
      · simp [h]
    calc v (i, j)
        = ∑ k : Fin 2, (if i = k then v (k, j) else 0) := by
          rw [Finset.sum_ite_eq Finset.univ i (fun k => v (k, j))]
          simp
      _ = ∑ k : Fin 2,
            ((‖fun j' => v (k, j')‖ : ℝ) : ℂ) *
              (if i = k then (1 : ℂ) else 0) *
              (v (k, j) / ((‖fun j' => v (k, j')‖ : ℝ) : ℂ)) :=
          Finset.sum_congr rfl (fun k _ => (step k).symm)

/--
**Rank-1 Schmidt case is separable (d = 2)**.

The rank-1 bipartite density-like matrix
`s² · (a ⊗ b) (a ⊗ b)ᴴ`, written entrywise as
`(i, j) (k, l) ↦ s² · a i · b j · star (a k) · star (b l)`,
lies in the separable cone.  This is P3 step (e): the degraded single-term
version of the general Schmidt→Separable rank-≤2 argument.

Witness: `k = 1`, `p 0 = s²`, `A 0 = vecMulVec a (star a)` (the outer-product
`|a⟩⟨a|`), `B 0 = vecMulVec b (star b)` (the outer-product `|b⟩⟨b|`), both
PSD by `Matrix.posSemidef_vecMulVec_self_star`.
-/
theorem rank_one_schmidt_psd_separable_dim2
    (s : ℝ) (hs : 0 ≤ s) (a b : Fin 2 → ℂ) :
    PPT2.Separable (d := 2)
      (fun ⟨i, j⟩ ⟨k, l⟩ =>
        (s : ℂ)^2 * a i * b j * star (a k) * star (b l)) := by
  refine ⟨1,
          fun _ => s^2,
          fun _ => Matrix.vecMulVec a (star a),
          fun _ => Matrix.vecMulVec b (star b),
          ?hp, ?hA, ?hB, ?heq⟩
  · intro _; exact sq_nonneg s
  · intro _; exact Matrix.posSemidef_vecMulVec_self_star a
  · intro _; exact Matrix.posSemidef_vecMulVec_self_star b
  · ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Fin.sum_univ_one, Matrix.smul_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      smul_eq_mul]
    push_cast
    ring

/--
**Rank-≤2 Schmidt case is separable (d = 2)**.

A matrix that is the sum of two rank-1 Schmidt terms is separable.
This is P3 step (f): the 2-term generalisation of `rank_one_schmidt_psd_separable_dim2`.

Given nonneg scalars `s t` and vectors `a b c d : Fin 2 → ℂ`, the matrix
  `(i,j)(k,l) ↦ s² · a i · b j · star(a k) · star(b l)
              + t² · c i · d j · star(c k) · star(d l)`
is separable, by applying `Separable.add` to two rank-1 witnesses.
-/
theorem ppt_implies_separable_sum2_dim2
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (a b c d : Fin 2 → ℂ) :
    PPT2.Separable (d := 2)
      (fun ⟨i, j⟩ ⟨k, l⟩ =>
        (s : ℂ)^2 * a i * b j * star (a k) * star (b l) +
        (t : ℂ)^2 * c i * d j * star (c k) * star (d l)) := by
  have h1 : PPT2.Separable (d := 2)
      (fun ⟨i, j⟩ ⟨k, l⟩ =>
        (s : ℂ)^2 * a i * b j * star (a k) * star (b l)) :=
    rank_one_schmidt_psd_separable_dim2 s hs a b
  have h2 : PPT2.Separable (d := 2)
      (fun ⟨i, j⟩ ⟨k, l⟩ =>
        (t : ℂ)^2 * c i * d j * star (c k) * star (d l)) :=
    rank_one_schmidt_psd_separable_dim2 t ht c d
  have heq : (fun (ij : Fin 2 × Fin 2) (kl : Fin 2 × Fin 2) =>
        (s : ℂ)^2 * a ij.1 * b ij.2 * star (a kl.1) * star (b kl.2) +
        (t : ℂ)^2 * c ij.1 * d ij.2 * star (c kl.1) * star (d kl.2)) =
      (fun ⟨i, j⟩ ⟨k, l⟩ =>
        (s : ℂ)^2 * a i * b j * star (a k) * star (b l)) +
      (fun ⟨i, j⟩ ⟨k, l⟩ =>
        (t : ℂ)^2 * c i * d j * star (c k) * star (d l)) := by
    ext ⟨i, j⟩ ⟨k, l⟩; simp [Matrix.add_apply]
  rw [heq]
  exact Separable.add h1 h2

end PPT2.SchmidtDim2
