/-
GaiaPhysicsLean.A1Dpi.KrausDecomposition

Kraus decomposition for general CPTP maps (dK → dH, not necessarily square).

**Primary target**: `kraus_decomposition_general`

For every CPTP map Λ : B(H_K) → B(H_H), there exist Kraus operators
K : Fin r → Matrix (Fin dH) (Fin dK) ℂ such that:
  1. Λ(ρ) = ∑ᵢ Kᵢ ρ Kᵢ†
  2. ∑ᵢ Kᵢ† Kᵢ = I_dK (trace-preservation)

Strategy:
- Use Choi matrix J_Λ : Matrix (Fin dK × Fin dH) (Fin dK × Fin dH) ℂ
- Apply spectral decomposition: J_Λ = ∑ᵢ λᵢ |vᵢ⟩⟨vᵢ|
- Extract Kraus operators: Kᵢ = √λᵢ · reshape(vᵢ) : Matrix (Fin dH) (Fin dK) ℂ
- Prove the Kraus identity and trace-preservation

References:
- Nielsen & Chuang, "Quantum Computation and Quantum Information", Theorem 8.1
- Watrous, "The Theory of Quantum Information", Theorem 2.22
- A3Stinespring/Lemmas.lean (square case dK = dK)
-/

import GaiaPhysicsLean.A2ChoiTheorem.Defs
import GaiaPhysicsLean.A2ChoiTheorem.Reverse
import GaiaPhysicsLean.A1Dpi.Stinespring
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Matrix.Mul
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Real.Sqrt

namespace GaiaPhysicsLean.A1Dpi

open Matrix
open GaiaPhysicsLean.A2ChoiTheorem
open scoped ComplexOrder

/-!
## Kraus form for general channels

A Kraus form witness for a quantum channel Φ : QChan dK dH of rank r:
a family K : Fin r → Matrix (Fin dH) (Fin dK) ℂ of Kraus operators satisfying:
  * ∑ k, (K k)ᴴ * K k = 1 (trace-preservation)
  * Φ X = ∑ k, K k * X * (K k)ᴴ for every input X
-/

structure KrausForm {dK dH : ℕ} (Φ : QChan dK dH) (r : ℕ) where
  /-- The Kraus operators. -/
  K : Fin r → Matrix (Fin dH) (Fin dK) ℂ
  /-- Trace-preservation: the Kraus operators form an isometric column block. -/
  tp : ∑ k, (K k).conjTranspose * (K k) = (1 : Matrix (Fin dK) (Fin dK) ℂ)
  /-- Channel identity: Φ X = ∑ k, K k * X * (K k)ᴴ. -/
  channel : ∀ X : Matrix (Fin dK) (Fin dK) ℂ,
    Φ X = ∑ k, (K k) * X * (K k).conjTranspose

/-!
## Kraus decomposition theorem (general case)

Every CPTP map admits a Kraus decomposition.
-/

/-- Helper: Convert spectral theorem U D Uᴴ form to rank-1 sum form for product-indexed matrices. -/
private lemma spectral_to_rank1_sum_reindexed {dK dH : ℕ} [DecidableEq (Fin dK)] [DecidableEq (Fin dH)]
    (M : Matrix (Fin dK × Fin dH) (Fin dK × Fin dH) ℂ) (hM : M.PosSemidef) :
    ∃ (μ : Fin (dK * dH) → ℝ) (v : Fin (dK * dH) → (Fin dK × Fin dH) → ℂ),
      (∀ k, 0 ≤ μ k) ∧
      M = ∑ k, (μ k : ℂ) • Matrix.vecMulVec (v k) (star (v k)) := by
  classical
  -- Reindex M to Fin (dK*dH) × Fin (dK*dH)
  let M' := Matrix.reindex finProdFinEquiv finProdFinEquiv M
  have hM' : M'.PosSemidef :=
    (Matrix.posSemidef_submatrix_equiv finProdFinEquiv.symm).mpr hM
  -- Apply spectral decomposition from A2ChoiTheorem.Reverse
  have hHerm := hM'.1
  use hHerm.eigenvalues
  -- Eigenvectors: columns of the unitary matrix, reindexed back to product type
  use fun k i => (hHerm.eigenvectorUnitary : Matrix (Fin (dK * dH)) (Fin (dK * dH)) ℂ) (finProdFinEquiv i) k
  constructor
  · intro k
    exact Matrix.PosSemidef.eigenvalues_nonneg hM' k
  · ext i j
    have hLHS : M i j = M' (finProdFinEquiv i) (finProdFinEquiv j) := by
      simp [M', Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [hLHS]
    have spec := hHerm.spectral_theorem
    conv_lhs => rw [spec]
    rw [Unitary.conjStarAlgAut_apply]
    rw [show (Matrix.diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) : Matrix (Fin (dK * dH)) (Fin (dK * dH)) ℂ)
            = Matrix.diagonal (fun k => (hHerm.eigenvalues k : ℂ)) from rfl]
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
               Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring

/-- Helper: Reshape vector indexed by product type into matrix (Kraus operator). -/
private noncomputable def vecToKraus {dK dH : ℕ} (v : (Fin dK × Fin dH) → ℂ) (μ : ℝ) :
    Matrix (Fin dH) (Fin dK) ℂ :=
  fun a i => Real.sqrt μ • v (i, a)

/-- **Kraus decomposition theorem (general case).**
    Every CPTP map Φ : QChan dK dH admits a Kraus decomposition:
    there exist Kraus operators K : Fin r → Matrix (Fin dH) (Fin dK) ℂ such that
      1. Φ X = ∑ᵢ Kᵢ X Kᵢ†
      2. ∑ᵢ Kᵢ† Kᵢ = I_dK

    The rank r is at most dK * dH (the dimension of the Choi matrix).

    **Proof strategy**:
    1. Show Choi matrix J_Λ is positive semidefinite (from IsCP)
    2. Apply spectral decomposition: J_Λ = ∑ᵢ λᵢ |vᵢ⟩⟨vᵢ|
    3. Extract Kraus operators: Kᵢ = √λᵢ · reshape(vᵢ)
    4. Prove Kraus identity using Choi-Kraus correspondence (from A2ChoiTheorem.Reverse)
    5. Prove trace-preservation from Tr(J_Λ) = dH (IsTP condition)

    **References**:
    - Nielsen & Chuang, Theorem 8.1
    - A3Stinespring/Lemmas.lean:363-416 (square case)
    - A2ChoiTheorem/Reverse.lean (spectral decomposition infrastructure) -/
theorem kraus_decomposition_general {dK dH : ℕ} [NeZero dK] [NeZero dH]
    (Φ : QChan dK dH)
    (hCP : IsCP Φ) (hTP : IsTracePreserving Φ) :
    ∃ (r : ℕ), 0 < r ∧ Nonempty (KrausForm Φ r) := by
  classical
  -- STEP 1: Show Choi matrix is PSD (from IsCP)
  -- Strategy: apply CP at ancilla dimension n = dK to the rank-1 outer product
  -- vecMulVec ω (star ω), where ω(a,b) = δ_{a,b} encodes the maximally-entangled
  -- vector |Ω⟩ = ∑_a |a⟩⊗|a⟩. The CP-image equals Choi Φ entrywise via Choi_apply.
  have hPSD : (Choi Φ).PosSemidef := by
    classical
    let ω : Fin dK × Fin dK → ℂ := fun p => if p.1 = p.2 then 1 else 0
    -- Rank-1 PSD witness via Mathlib's posSemidef_vecMulVec_self_star
    have hM_psd : (Matrix.vecMulVec ω (star ω)).PosSemidef :=
      Matrix.posSemidef_vecMulVec_self_star ω
    -- Apply CP at ancilla dimension n = dK
    have hN_psd := hCP dK (Matrix.vecMulVec ω (star ω)) hM_psd
    -- The inner ampliation block i,j ↦ M (pi,i) (qi,j) equals single pi qi 1
    have hBlock : ∀ (pi qi : Fin dK),
        (Matrix.of fun (i j : Fin dK) =>
          (Matrix.vecMulVec ω (star ω)) (pi, i) (qi, j)) = Matrix.single pi qi (1 : ℂ) := by
      intro pi qi
      ext i j
      have hω_pi_i : ω (pi, i) = if pi = i then (1 : ℂ) else 0 := rfl
      have hω_qi_j : ω (qi, j) = if qi = j then (1 : ℂ) else 0 := rfl
      simp only [Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply,
        Matrix.single_apply, hω_pi_i, hω_qi_j]
      by_cases h1 : pi = i <;> by_cases h2 : qi = j <;>
        simp [h1, h2, star_one, star_zero]
    -- Identify CP-output matrix with Choi Φ entrywise
    have hEq : (Matrix.of fun (p q : Fin dK × Fin dH) =>
        Φ (Matrix.of fun (i j : Fin dK) =>
            (Matrix.vecMulVec ω (star ω)) (p.1, i) (q.1, j)) p.2 q.2) = Choi Φ := by
      ext ⟨pi, pa⟩ ⟨qi, qa⟩
      simp only [Matrix.of_apply]
      rw [hBlock pi qi, Choi_apply]
    rw [← hEq]
    exact hN_psd

  -- STEP 2: Apply spectral decomposition
  obtain ⟨μ, v, hμ_nonneg, hSpec⟩ := spectral_to_rank1_sum_reindexed (Choi Φ) hPSD

  -- The rank is dK * dH (dimension of Choi matrix)
  use dK * dH
  refine ⟨Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne dK)) (Nat.pos_of_ne_zero (NeZero.ne dH)), ?_⟩

  -- STEP 3: Extract Kraus operators from eigenvectors
  let K : Fin (dK * dH) → Matrix (Fin dH) (Fin dK) ℂ :=
    fun k => vecToKraus (v k) (μ k)

  -- STEP 4: Prove Kraus identity Φ X = ∑ k, K k * X * (K k)†
  -- This follows the same proof structure as A2ChoiTheorem.Reverse.cp_of_choi_psd
  have hKraus : ∀ X : Matrix (Fin dK) (Fin dK) ℂ,
      Φ X = ∑ k, K k * X * (K k).conjTranspose := by
    intro X
    -- Strategy: reduce both sides to ∑ k i j, X i j * μ_k * v_k(i,a) * star(v_k(j,b))
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
    -- LHS = ∑ i, ∑ j, ∑ k, X i j * (μ k * (v k (i,a) * star (v k (j,b))))
    -- Expand the RHS
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, K, vecToKraus]
    simp only [star_smul, star_trivial]
    simp only [Complex.real_smul, Finset.sum_mul]
    have hsq : ∀ (k : Fin (dK * dH)), (√(μ k) : ℂ) * (√(μ k) : ℂ) = (μ k : ℂ) := by
      intro k; norm_cast; exact Real.mul_self_sqrt (hμ_nonneg k)
    have hterm : ∀ (k : Fin (dK * dH)) (i j : Fin dK),
        ↑√(μ k) * v k (i, a) * X i j * (↑√(μ k) * star (v k (j, b)))
        = X i j * (↑(μ k) * (v k (i, a) * star (v k (j, b)))) := by
      intro k i j; rw [← hsq k]; ring
    simp_rw [hterm]
    rw [Finset.sum_comm]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => ?_
    exact Finset.sum_comm

  -- STEP 5: Prove trace-preservation ∑ k, (K k)† * K k = I_dK
  -- Strategy: Show entry-wise that (∑_k K_k† K_k)(i,j) = δ_{i,j}
  -- by relating the sum to Choi matrix entries and using trace-preservation
  have hTP_kraus : ∑ k, (K k).conjTranspose * (K k) = (1 : Matrix (Fin dK) (Fin dK) ℂ) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
               Matrix.one_apply]
    -- LHS = ∑_k ∑_a conj(K_k(a,i)) * K_k(a,j)
    conv_lhs =>
      rw [Finset.sum_comm]
    simp only [K, vecToKraus]
    -- Rewrite using spectral decomposition
    have hEntry : ∑ a : Fin dH, ∑ k : Fin (dK * dH),
        starRingEnd ℂ ((Real.sqrt (μ k) : ℂ) * v k (i, a)) * ((Real.sqrt (μ k) : ℂ) * v k (j, a))
        = if i = j then 1 else 0 := by
      -- Step 1: Simplify star of product, consolidate sqrt
      have hterm : ∀ (a : Fin dH) (k : Fin (dK * dH)),
          starRingEnd ℂ ((↑√(μ k) : ℂ) * v k (i, a)) * ((↑√(μ k) : ℂ) * v k (j, a))
          = (μ k : ℂ) * (star (v k (i, a)) * v k (j, a)) := by
        intro a k
        have hsq : ((↑√(μ k) : ℂ)) * ((↑√(μ k) : ℂ)) = (μ k : ℂ) := by
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hμ_nonneg k)]
        rw [starRingEnd_apply, star_mul]
        have hstar_real : star (↑√(μ k) : ℂ) = ↑√(μ k) := by
          rw [RCLike.star_def, Complex.conj_ofReal]
        rw [hstar_real]
        have : star (v k (i, a)) * ↑√(μ k) * (↑√(μ k) * v k (j, a))
            = ↑√(μ k) * ↑√(μ k) * (star (v k (i, a)) * v k (j, a)) := by ring
        rw [this, hsq]
      simp_rw [hterm]
      -- Step 2: Connect to Choi matrix
      have hChoi_entry : ∀ a : Fin dH,
          ∑ k, (μ k : ℂ) * (star (v k (i, a)) * v k (j, a))
          = Choi Φ (j, a) (i, a) := by
        intro a
        have h1 := congr_fun (congr_fun hSpec (j, a)) (i, a)
        simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
          smul_eq_mul] at h1
        rw [h1]
        congr 1; ext k; ring
      simp_rw [hChoi_entry]
      -- Step 3: Use Choi_apply and trace-preservation
      simp_rw [Choi_apply]
      have : ∑ a : Fin dH, Φ (Matrix.single j i 1) a a =
          Matrix.trace (Φ (Matrix.single j i 1)) := rfl
      rw [this, hTP]
      by_cases h : i = j
      · subst h; simp [Matrix.trace_single_eq_same]
      · rw [if_neg h, Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm h)]
    exact hEntry

  constructor
  exact {
    K := K
    tp := hTP_kraus
    channel := hKraus
  }

end GaiaPhysicsLean.A1Dpi
