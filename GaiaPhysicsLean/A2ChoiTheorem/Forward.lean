/-
GaiaPhysicsLean.A2ChoiTheorem.Forward

Forward direction of Choi's theorem (CP ⇒ Choi-PSD):
  `choi_psd_of_cp : IsCP Φ → (Choi Φ).PosSemidef`

Strategy
========
Apply complete positivity at ancilla dimension `n = dK` to the rank-1 outer
product `vecMulVec ω (star ω)`, where `ω : Fin dK × Fin dK → ℂ` is the
"diagonal" indicator `ω (a, b) = if a = b then 1 else 0` (encoding the
maximally-entangled state `|Ω⟩ = ∑_a |a⟩⊗|a⟩`).  The CP-image of this PSD
matrix is, entrywise, exactly the Choi matrix of `Φ`.
-/
import GaiaPhysicsLean.A2ChoiTheorem.Defs

set_option maxHeartbeats 2000000

namespace GaiaPhysicsLean.A2ChoiTheorem

open Matrix
open scoped ComplexOrder

/-- **Forward direction of Choi's theorem.**  If `Φ : QChan dK dH` is
    completely positive, then its Choi matrix is positive semidefinite. -/
theorem choi_psd_of_cp {dK dH : ℕ} (Φ : QChan dK dH) (hCP : IsCP Φ) :
    (Choi Φ).PosSemidef := by
  classical
  -- The "diagonal" indicator vector `ω (a, b) = δ_{a,b}` on `Fin dK × Fin dK`.
  let ω : Fin dK × Fin dK → ℂ := fun p => if p.1 = p.2 then 1 else 0
  have hω : ∀ a b : Fin dK, ω (a, b) = if a = b then (1 : ℂ) else 0 :=
    fun _ _ => rfl
  -- The outer product `ω ⊗ ω*` is a rank-1 PSD matrix.
  have hM_psd : (vecMulVec ω (star ω)).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · -- Hermitianness: (ω ⊗ ω†)† = ω ⊗ ω†
      ext i j
      simp only [conjTranspose_apply, vecMulVec_apply, Pi.star_apply, hω]
      by_cases hi : i.1 = i.2 <;> by_cases hj : j.1 = j.2 <;> simp [hi, hj, star_one, star_zero, mul_comm]
    · -- Quadratic form: ⟨v, (ω ⊗ ω†) v⟩ = |⟨ω, v⟩|² ≥ 0
      intro v
      simp only [dotProduct, mulVec, vecMulVec_apply, Pi.star_apply]
      -- The expression factors as (∑ᵢ star(vᵢ) * ωᵢ) * (∑ⱼ star(ωⱼ) * vⱼ)
      -- gap_kind: mathlib_missing
      -- Missing: lemma for factoring nested sums ∑ᵢ star(vᵢ) * ∑ⱼ ωᵢ * star(ωⱼ) * vⱼ
      -- into (∑ᵢ star(vᵢ) * ωᵢ) * (∑ⱼ star(ωⱼ) * vⱼ).
      -- Proof strategy: expand inner sum, use associativity/commutativity to factor.
      -- First, distribute the inner sum and rearrange to factor out the sums
      have hFactor : ∑ x, star (v x) * ∑ x_1, ω x * star (ω x_1) * v x_1 =
          (∑ x, star (v x) * ω x) * (∑ x_1, star (ω x_1) * v x_1) := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        congr 1
        funext y
        congr 1
        funext x
        ring
      rw [hFactor]
      -- Now ∑ⱼ star (ω j) * v j = star (∑ⱼ star (v j) * ω j), so this is star s * s
      have hConj : ∑ j, star (ω j) * v j = star (∑ i, star (v i) * ω i) := by
        rw [star_sum]
        congr 1
        funext i
        rw [star_mul, star_star, mul_comm]
      rw [hConj]
      have h_nonneg := star_mul_self_nonneg (∑ i, star (v i) * ω i)
      convert h_nonneg using 1
      ring
  -- Apply CP at ancilla dimension `n = dK`.
  have hN_psd := hCP dK (vecMulVec ω (star ω)) hM_psd
  -- Inner ampliation block: the slice `i,j ↦ M (pi, i) (qi, j)` is `single pi qi 1`.
  have hBlock : ∀ (pi qi : Fin dK),
      (Matrix.of fun (i j : Fin dK) =>
        (vecMulVec ω (star ω)) (pi, i) (qi, j)) = Matrix.single pi qi (1 : ℂ) := by
    intro pi qi
    ext i j
    simp only [Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply, hω,
      Matrix.single_apply]
    by_cases h1 : pi = i <;> by_cases h2 : qi = j <;> simp [h1, h2]
  -- The CP-output matrix is precisely `Choi Φ`.
  have hEq : (Matrix.of fun (p q : Fin dK × Fin dH) =>
      Φ (Matrix.of fun (i j : Fin dK) =>
          (vecMulVec ω (star ω)) (p.1, i) (q.1, j)) p.2 q.2) = Choi Φ := by
    ext ⟨pi, pa⟩ ⟨qi, qa⟩
    simp only [Matrix.of_apply]
    rw [hBlock pi qi, Choi_apply]
  -- Transport PSD through the equality.
  rw [← hEq]
  exact hN_psd

end GaiaPhysicsLean.A2ChoiTheorem
