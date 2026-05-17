/- Tsirelson bound for CHSH (≤ 2√2)
   LKM source claim: gcn_9f07543c6ff944b0 (premise) + gcn_aea213dfec744535 (SDP conclusion)
   Tier: A
   See: README.md (this directory)

   **Primary target**: `tsirelson_chsh_bound`

   For dichotomic observables A_0, A_1, B_0, B_1 with ||A_i||,||B_j||≤1 on any Hilbert space and any state |ψ⟩, |⟨A_0 B_0 + A_0 B_1 + A_1 B_0 − A_1 B_1⟩| ≤ 2√2.
-/

import Mathlib

namespace GaiaPhysicsLean.A10Tsirelson

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Commutator of two operators -/
def comm (A B : E →L[ℂ] E) : E →L[ℂ] E := A.comp B - B.comp A

/-- Premise 2: Commutator norm bound for unit-norm operators -/
lemma commutator_norm_bound (A B : E →L[ℂ] E) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖comm A B‖ ≤ 4 := by
  unfold comm
  calc ‖A.comp B - B.comp A‖
      ≤ ‖A.comp B‖ + ‖B.comp A‖ := norm_sub_le _ _
    _ ≤ ‖A‖ * ‖B‖ + ‖B‖ * ‖A‖ := by
        apply add_le_add
        · exact ContinuousLinearMap.opNorm_comp_le _ _
        · exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 + 1 * 1 := by
        apply add_le_add
        · exact mul_le_mul hA hB (norm_nonneg _) (by linarith)
        · exact mul_le_mul hB hA (norm_nonneg _) (by linarith)
    _ = 2 := by norm_num
    _ ≤ 4 := by norm_num

/-- Premise 3: For self-adjoint X in E →L[ℂ] E, ‖X.comp X‖ = ‖X‖² via C*-identity -/
lemma norm_from_squared_selfadjoint (X : E →L[ℂ] E) (hX : IsSelfAdjoint X)
    (h : ‖X.comp X‖ ≤ 8) : ‖X‖ ≤ 2 * Real.sqrt 2 := by
  -- In the C*-algebra E →L[ℂ] E, mul = comp and ‖X*X‖ = ‖X‖² for self-adjoint X
  have hXX : ‖X‖ ^ 2 ≤ 8 := by
    have : ‖X * X‖ = ‖X‖ ^ 2 := hX.norm_mul_self
    rw [ContinuousLinearMap.mul_def] at this
    linarith [this ▸ h]
  have hXnn : 0 ≤ ‖X‖ := norm_nonneg _
  rw [show (2 : ℝ) * Real.sqrt 2 = Real.sqrt 8 by
    rw [show (8 : ℝ) = 2^2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]]
  rw [← Real.sqrt_sq hXnn]
  exact Real.sqrt_le_sqrt hXX

/-- Key bound: for unit vector x, ‖(B₀+B₁)x‖² + ‖(B₀-B₁)x‖² ≤ 4 -/
private lemma parallelogram_bound (B₀ B₁ : E →L[ℂ] E) (hB₀ : ‖B₀‖ ≤ 1) (hB₁ : ‖B₁‖ ≤ 1)
    (x : E) (hx : ‖x‖ ≤ 1) :
    ‖(B₀ + B₁) x‖ ^ 2 + ‖(B₀ - B₁) x‖ ^ 2 ≤ 4 := by
  have hB₀x : ‖B₀ x‖ ≤ 1 := by
    calc ‖B₀ x‖ ≤ ‖B₀‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * 1 := mul_le_mul hB₀ hx (norm_nonneg _) (by linarith)
      _ = 1 := by ring
  have hB₁x : ‖B₁ x‖ ≤ 1 := by
    calc ‖B₁ x‖ ≤ ‖B₁‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * 1 := mul_le_mul hB₁ hx (norm_nonneg _) (by linarith)
      _ = 1 := by ring
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  have para := @parallelogram_law_with_norm ℂ E _ _ _ (B₀ x) (B₁ x)
  -- para : ‖B₀x + B₁x‖² + ‖B₀x - B₁x‖² = 2*(‖B₀x‖² + ‖B₁x‖²)
  have hsum : ‖B₀ x‖ ^ 2 + ‖B₁ x‖ ^ 2 ≤ 2 := by
    have h1 : ‖B₀ x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (B₀ x)]
    have h2 : ‖B₁ x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (B₁ x)]
    linarith
  linarith

/-- AM-QM: a + b ≤ √2 * √(a² + b²) for nonneg a, b -/
private lemma add_le_sqrt_two_mul_sqrt_sq_add_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a + b ≤ Real.sqrt 2 * Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_sq (by linarith [ha, hb] : 0 ≤ a + b)]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (a - b)]

/-- Premise 1: CHSH operator norm bound via pointwise estimate -/
lemma chsh_operator_norm_bound (A₀ A₁ B₀ B₁ : E →L[ℂ] E)
    (hA₀ : ‖A₀‖ ≤ 1) (hA₁ : ‖A₁‖ ≤ 1) (hB₀ : ‖B₀‖ ≤ 1) (hB₁ : ‖B₁‖ ≤ 1)
    (dichA₀ : A₀.comp A₀ = ContinuousLinearMap.id ℂ E)
    (dichA₁ : A₁.comp A₁ = ContinuousLinearMap.id ℂ E)
    (dichB₀ : B₀.comp B₀ = ContinuousLinearMap.id ℂ E)
    (dichB₁ : B₁.comp B₁ = ContinuousLinearMap.id ℂ E) :
    let S := A₀.comp (B₀ + B₁) + A₁.comp (B₀ - B₁)
    ‖S‖ ≤ 2 * Real.sqrt 2 := by
  intro S
  apply ContinuousLinearMap.opNorm_le_bound'
  · positivity
  intro x hx
  -- ‖Sx‖ ≤ ‖A₀(B₀+B₁)x‖ + ‖A₁(B₀-B₁)x‖ ≤ ‖(B₀+B₁)x‖ + ‖(B₀-B₁)x‖
  simp only [S, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  have step1 : ‖A₀ ((B₀ + B₁) x) + A₁ ((B₀ - B₁) x)‖ ≤
      ‖(B₀ + B₁) x‖ + ‖(B₀ - B₁) x‖ := by
    calc ‖A₀ ((B₀ + B₁) x) + A₁ ((B₀ - B₁) x)‖
        ≤ ‖A₀ ((B₀ + B₁) x)‖ + ‖A₁ ((B₀ - B₁) x)‖ := norm_add_le _ _
      _ ≤ ‖A₀‖ * ‖(B₀ + B₁) x‖ + ‖A₁‖ * ‖(B₀ - B₁) x‖ := by
            apply add_le_add <;> exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖(B₀ + B₁) x‖ + 1 * ‖(B₀ - B₁) x‖ := by
            apply add_le_add <;> apply mul_le_mul_of_nonneg_right <;>
              [exact hA₀; exact norm_nonneg _; exact hA₁; exact norm_nonneg _]
      _ = ‖(B₀ + B₁) x‖ + ‖(B₀ - B₁) x‖ := by ring
  -- Now bound ‖(B₀+B₁)x‖ + ‖(B₀-B₁)x‖ ≤ 2√2 * ‖x‖
  have hxnn : 0 ≤ ‖x‖ := norm_nonneg _
  -- First handle x = 0 trivially, else normalize
  by_cases hx0 : x = 0
  · simp [hx0]
  -- For general x, use AM-QM and parallelogram law
  set a := ‖(B₀ + B₁) x‖
  set b := ‖(B₀ - B₁) x‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  -- Bound a² + b² ≤ 4 * ‖x‖²
  have hab_sq : a ^ 2 + b ^ 2 ≤ 4 * ‖x‖ ^ 2 := by
    simp only [a, b, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
    have para := @parallelogram_law_with_norm ℂ E _ _ _ (B₀ x) (B₁ x)
    simp only [ContinuousLinearMap.sub_apply] at para ⊢
    have hB₀x_sq : ‖B₀ x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      have h1 := ContinuousLinearMap.le_opNorm B₀ x
      have h2 : ‖B₀‖ * ‖x‖ ≤ ‖x‖ := by
        calc ‖B₀‖ * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hB₀ (norm_nonneg _)
          _ = ‖x‖ := one_mul _
      rw [sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
      exact le_trans h1 h2
    have hB₁x_sq : ‖B₁ x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      have h1 := ContinuousLinearMap.le_opNorm B₁ x
      have h2 : ‖B₁‖ * ‖x‖ ≤ ‖x‖ := by
        calc ‖B₁‖ * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hB₁ (norm_nonneg _)
          _ = ‖x‖ := one_mul _
      rw [sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
      exact le_trans h1 h2
    linarith
  -- AM-QM: a + b ≤ √2 * √(a²+b²) ≤ √2 * 2‖x‖ = 2√2 ‖x‖
  have step2 : a + b ≤ 2 * Real.sqrt 2 * ‖x‖ := by
    calc a + b
        ≤ Real.sqrt 2 * Real.sqrt (a ^ 2 + b ^ 2) := add_le_sqrt_two_mul_sqrt_sq_add_sq ha hb
      _ ≤ Real.sqrt 2 * Real.sqrt (4 * ‖x‖ ^ 2) := by
            apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hab_sq)
            positivity
      _ = 2 * Real.sqrt 2 * ‖x‖ := by
            rw [show (4 : ℝ) * ‖x‖ ^ 2 = (2 * ‖x‖) ^ 2 by ring,
                Real.sqrt_sq (by positivity)]
            ring
  calc ‖A₀ ((B₀ + B₁) x) + A₁ ((B₀ - B₁) x)‖
      ≤ a + b := step1
    _ ≤ 2 * Real.sqrt 2 * ‖x‖ := step2

/-- Primary target: Tsirelson bound for CHSH -/
theorem tsirelson_chsh_bound (A₀ A₁ B₀ B₁ : E →L[ℂ] E)
    (hA₀ : ‖A₀‖ ≤ 1) (hA₁ : ‖A₁‖ ≤ 1) (hB₀ : ‖B₀‖ ≤ 1) (hB₁ : ‖B₁‖ ≤ 1)
    (dichA₀ : A₀.comp A₀ = ContinuousLinearMap.id ℂ E)
    (dichA₁ : A₁.comp A₁ = ContinuousLinearMap.id ℂ E)
    (dichB₀ : B₀.comp B₀ = ContinuousLinearMap.id ℂ E)
    (dichB₁ : B₁.comp B₁ = ContinuousLinearMap.id ℂ E) :
    let S := A₀.comp B₀ + A₀.comp B₁ + A₁.comp B₀ - A₁.comp B₁
    ‖S‖ ≤ 2 * Real.sqrt 2 := by
  have h_rewrite : A₀.comp B₀ + A₀.comp B₁ + A₁.comp B₀ - A₁.comp B₁ =
                   A₀.comp (B₀ + B₁) + A₁.comp (B₀ - B₁) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.sub_apply]
    -- LHS: A₀(B₀ x) + A₀(B₁ x) + A₁(B₀ x) - A₁(B₁ x)
    -- RHS: A₀(B₀ x + B₁ x) + A₁(B₀ x - B₁ x)
    rw [ContinuousLinearMap.map_add A₀ (B₀ x) (B₁ x)]
    rw [ContinuousLinearMap.map_sub A₁ (B₀ x) (B₁ x)]
    abel
  rw [h_rewrite]
  exact chsh_operator_norm_bound A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁ dichA₀ dichA₁ dichB₀ dichB₁

end GaiaPhysicsLean.A10Tsirelson
