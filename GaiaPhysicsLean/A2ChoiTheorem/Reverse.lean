/-
GaiaPhysicsLean.A2ChoiTheorem.Reverse

Reverse direction of Choi's theorem (Choi-PSD ⇒ CP):
  `cp_of_choi_psd : (Choi Φ).PosSemidef → IsCP Φ`

Strategy
========
STEP A: Spectral decomposition of C_Φ = ∑ₖ μₖ |vₖ⟩⟨vₖ| with μₖ ≥ 0.
STEP B: Extract Kraus operators Kₖ from eigenvectors via reshape.
STEP C: Prove Φ(X) = ∑ₖ Kₖ X Kₖᴴ by checking on basis elements.
STEP D: Conclude IsCP via PosSemidef preservation under Kraus form.
-/
import GaiaPhysicsLean.A2ChoiTheorem.Defs
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Star.UnitaryStarAlgAut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 80000

namespace GaiaPhysicsLean.A2ChoiTheorem

open Matrix
open scoped ComplexOrder

-- Helper: Expand U D Uᴴ matrix multiplication
private lemma spectral_uduh_expand {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (d : ι → ℝ) (i j : ι) :
    (U * diagonal (fun k => (d k : ℂ)) * star U) i j =
    ∑ k, U i k * (d k : ℂ) * star (U j k) := by
  simp only [Matrix.mul_apply, Matrix.star_apply, diagonal_apply, mul_ite, mul_zero,
             Finset.sum_ite_eq', Finset.mem_univ, ite_true]

-- Helper: Convert spectral theorem U D Uᴴ form to rank-1 sum form
private lemma spectral_to_rank1_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    ∃ (μ : ι → ℝ) (v : ι → ι → ℂ),
      (∀ k, 0 ≤ μ k) ∧
      M = ∑ k, (μ k : ℂ) • vecMulVec (v k) (star (v k)) := by
  classical
  have hHerm := hM.1
  use hHerm.eigenvalues
  use fun k i => hHerm.eigenvectorUnitary i k
  constructor
  · intro k
    exact Matrix.PosSemidef.eigenvalues_nonneg hM k
  · ext i j
    have spec := hHerm.spectral_theorem
    conv_lhs => rw [spec]
    rw [Unitary.conjStarAlgAut_apply]
    rw [show (diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) : Matrix ι ι ℂ)
            = diagonal (fun k => (hHerm.eigenvalues k : ℂ)) from rfl]
    rw [spectral_uduh_expand (hHerm.eigenvectorUnitary : Matrix ι ι ℂ)
          hHerm.eigenvalues i j]
    simp only [sum_apply, vecMulVec_apply, Pi.star_apply, smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring

-- Helper: Reshape vector indexed by product type into matrix
private noncomputable def vecToKraus {dK dH : ℕ} (v : (Fin dK × Fin dH) → ℂ) (μ : ℝ) :
    Matrix (Fin dH) (Fin dK) ℂ :=
  fun a i => Real.sqrt μ • v (i, a)

-- Helper: Single Kraus term preserves PSD under ampliation
private lemma kraus_term_cp {dK dH : ℕ} (K : Matrix (Fin dH) (Fin dK) ℂ) :
    ∀ (n : ℕ) (M : Matrix (Fin n × Fin dK) (Fin n × Fin dK) ℂ),
      M.PosSemidef →
      (of fun (p : Fin n × Fin dH) (q : Fin n × Fin dH) =>
        (K * (of fun i j => M (p.1, i) (q.1, j)) * K.conjTranspose) p.2 q.2).PosSemidef := by
  intro n M hM
  -- Block-diagonal ampliation B = I_n ⊗ K
  let B : Matrix (Fin n × Fin dH) (Fin n × Fin dK) ℂ :=
    fun p q => if p.1 = q.1 then K p.2 q.2 else 0
  -- Rewrite ampliated matrix as B * M * Bᴴ
  have hEq : (of fun (p q : Fin n × Fin dH) =>
      (K * (of fun i j => M (p.1, i) (q.1, j)) * K.conjTranspose) p.2 q.2)
      = B * M * B.conjTranspose := by
    ext p r
    simp only [of_apply, Matrix.mul_apply, conjTranspose_apply, B]
    -- Expand the LHS using the definition of matrix multiplication
    symm
    simp_rw [Fintype.sum_prod_type]
    simp only [apply_ite star, star_zero, mul_ite, ite_mul, zero_mul, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero]
    conv_lhs => rw [Finset.sum_comm]
    simp_rw [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hEq]
  exact hM.mul_mul_conjTranspose_same B

/-- **Reverse direction of Choi's theorem.**  If the Choi matrix of
    `Φ : QChan dK dH` is positive semidefinite, then `Φ` is completely
    positive. -/
theorem cp_of_choi_psd {dK dH : ℕ} (Φ : QChan dK dH)
    (hPSD : (Choi Φ).PosSemidef) : IsCP Φ := by
  classical
  -- STEP A: Spectral decomposition C_Φ = ∑ₖ μₖ |vₖ⟩⟨vₖ|
  obtain ⟨μ, v, hμ_nonneg, hSpec⟩ := spectral_to_rank1_sum _ hPSD

  -- STEP B: Extract Kraus operators from eigenvectors
  let K : (Fin dK × Fin dH) → Matrix (Fin dH) (Fin dK) ℂ := fun k => vecToKraus (v k) (μ k)

  -- STEP C: Prove Φ(X) = ∑ₖ Kₖ X Kₖᴴ
  have hKraus : ∀ X : Matrix (Fin dK) (Fin dK) ℂ,
      Φ X = ∑ k, K k * X * (K k).conjTranspose := by
    intro X
    ext a b
    conv_lhs => rw [show X = ∑ i, ∑ j, Matrix.single i j (X i j) from Matrix.matrix_eq_sum_single X]
    simp only [map_sum, Matrix.sum_apply]
    have hsmul : ∀ i j, Φ (Matrix.single i j (X i j)) = X i j • Φ (Matrix.single i j 1) := by
      intro i j
      rw [show Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) from
        by simp [Matrix.smul_single]]
      exact map_smul Φ (X i j) (Matrix.single i j 1)
    simp_rw [hsmul, Matrix.smul_apply, smul_eq_mul, ← Choi_apply]
    rw [hSpec]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      smul_eq_mul, Finset.mul_sum]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, K, vecToKraus]
    simp only [star_smul, star_trivial]
    simp only [Complex.real_smul, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    have hsq : ∀ (k : Fin dK × Fin dH), (√(μ k) : ℂ) * (√(μ k) : ℂ) = (μ k : ℂ) := by
      intro k; norm_cast; exact Real.mul_self_sqrt (hμ_nonneg k)
    have hterm : ∀ (k : Fin dK × Fin dH) (i j : Fin dK),
        ↑√(μ k) * v k (i, a) * X i j * (↑√(μ k) * star (v k (j, b)))
        = X i j * (↑(μ k) * (v k (i, a) * star (v k (j, b)))) := by
      intro k i j; rw [← hsq k]; ring
    simp_rw [hterm]
    rw [Finset.sum_comm]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => ?_
    exact Finset.sum_comm

  -- STEP D: Conclude IsCP from Kraus form
  intro n M hM
  -- Rewrite using Kraus decomposition
  have hAmp : (of fun (p q : Fin n × Fin dH) =>
      Φ (of fun i j => M (p.1, i) (q.1, j)) p.2 q.2) =
    ∑ k, (of fun (p q : Fin n × Fin dH) =>
      (K k * (of fun i j => M (p.1, i) (q.1, j)) * (K k).conjTranspose) p.2 q.2) := by
    ext p q
    simp only [of_apply]
    rw [hKraus]
    simp only [sum_apply, of_apply]
  rw [hAmp]
  -- Sum of PSD matrices is PSD
  apply Matrix.posSemidef_sum
  intro k _
  exact kraus_term_cp (K k) n M hM

end GaiaPhysicsLean.A2ChoiTheorem
