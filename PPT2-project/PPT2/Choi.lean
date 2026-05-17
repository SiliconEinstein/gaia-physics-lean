/-
PPT2.Choi — finite-dimensional quantum channel as a bare ℂ-linear map between
matrix algebras, plus the Choi matrix as the standard sum-of-tensors form.

后续 step 可把 `QChan` bundle 进 CPTP 子结构；本基础层只放裸 LinearMap，
便于 Choi / Separable / Partial Transpose 等下游 def 顺利落地。
-/
import PPT2.Basic
import PPT2.MatrixTensor
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Complex.Order

namespace PPT2

open Matrix

/-- A (bare) finite-dimensional quantum channel as a ℂ-linear map between
    matrix algebras. CPTP bundle is intentionally deferred.
    Marked `@[reducible]` so that `FunLike` application resolves for `LinearMap`. -/
@[reducible]
noncomputable def QChan (d₁ d₂ : Nat) : Type :=
  Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ

/-- Channel composition := LinearMap composition. -/
noncomputable def QChan.comp {d₁ d₂ d₃ : Nat}
    (Φ : QChan d₂ d₃) (Ψ : QChan d₁ d₂) : QChan d₁ d₃ :=
  LinearMap.comp Φ Ψ

/-- Choi matrix C_Φ = Σ_{i,j} |i⟩⟨j| ⊗ Φ(|i⟩⟨j|). -/
noncomputable def Choi {d : Nat} (Φ : QChan d d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ∑ i : Fin d, ∑ j : Fin d,
    kron (Matrix.single i j (1 : ℂ))
         (Φ (Matrix.single i j (1 : ℂ)))

/-- Entrywise complex conjugation of a matrix.
    Equivalent to `M.map star` (which is `M.map (starRingEnd ℂ)`). -/
def _root_.Matrix.conj {m n : Type*} (M : Matrix m n ℂ) : Matrix m n ℂ :=
  M.map (starRingEnd ℂ)

@[simp]
theorem _root_.Matrix.conj_apply {m n : Type*} (M : Matrix m n ℂ) (i : m) (j : n) :
    M.conj i j = star (M i j) := rfl

/-- Helper: `(M * (Matrix.single i j 1) * N) r c = M r i * N j c`. -/
private lemma mul_single_mul_apply
    {d : Nat} (M N : Matrix (Fin d) (Fin d) ℂ)
    (i j r c : Fin d) :
    (M * Matrix.single i j (1 : ℂ) * N) r c = M r i * N j c := by
  classical
  -- (M * single i j 1) r y = if y = j then M r i else 0
  have hMS : ∀ y : Fin d,
      (M * Matrix.single i j (1 : ℂ)) r y = if y = j then M r i else 0 := by
    intro y
    by_cases hy : y = j
    · -- y = j: pick out the i-th term in ∑ x, M r x * [i=x ∧ j=y]
      rw [if_pos hy]
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single i]
      · simp [Matrix.single_apply, hy]
      · intro x _ hx
        have : ¬ (i = x ∧ j = y) := fun h => hx h.1.symm
        simp [Matrix.single_apply, this]
      · intro h; exact absurd (Finset.mem_univ i) h
    · rw [if_neg hy]
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro x _
      have : ¬ (i = x ∧ j = y) := fun h => hy h.2.symm
      simp [Matrix.single_apply, this]
  -- Now expand the outer product.
  rw [Matrix.mul_apply]
  simp only [hMS, ite_mul, zero_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro y _ hy; simp [hy]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- For a unitary `U`, the maximally-entangled-like sum `∑_{i,j} E_{ij} ⊗ E_{ij}`
    is invariant under the basis change `(U) ⊗ (Ū)` acting by conjugation. -/
theorem choi_basis_change_invariance {d : Nat}
    (U : Matrix (Fin d) (Fin d) ℂ)
    (hUU : U * Uᴴ = 1) (_hUU' : Uᴴ * U = 1) :
    (∑ i : Fin d, ∑ j : Fin d,
      kron (U * Matrix.single i j (1 : ℂ) * Uᴴ)
           ((Matrix.conj U) * Matrix.single i j (1 : ℂ) * (Matrix.conj U)ᴴ))
    = ∑ i : Fin d, ∑ j : Fin d,
        kron (Matrix.single i j (1 : ℂ)) (Matrix.single i j (1 : ℂ)) := by
  classical
  ext ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
  -- Pointwise:  LHS entry =  ∑ i ∑ j, (Eᵢⱼ-stuff) (a,b)
  simp only [Matrix.sum_apply]
  -- Step 1: identify each LHS summand with a product of single-index factors.
  have hLeftSum :
      (∑ i : Fin d, ∑ j : Fin d,
          (kron (U * Matrix.single i j (1:ℂ) * Uᴴ)
                ((Matrix.conj U) * Matrix.single i j (1:ℂ) * (Matrix.conj U)ᴴ))
            (a₁, a₂) (b₁, b₂))
      = (∑ i : Fin d, U a₁ i * star (U a₂ i)) *
          (∑ j : Fin d, star (U b₁ j) * U b₂ j) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    -- Pointwise compute the kron entry.
    have e1 : (U * Matrix.single i j (1:ℂ) * Uᴴ) a₁ b₁ = U a₁ i * star (U b₁ j) := by
      rw [mul_single_mul_apply]; simp [Matrix.conjTranspose_apply]
    have e2 : ((Matrix.conj U) * Matrix.single i j (1:ℂ) * (Matrix.conj U)ᴴ) a₂ b₂
              = star (U a₂ i) * U b₂ j := by
      rw [mul_single_mul_apply]
      simp [Matrix.conjTranspose_apply, Matrix.conj_apply]
    show (U * Matrix.single i j (1:ℂ) * Uᴴ) a₁ b₁ *
            ((Matrix.conj U) * Matrix.single i j (1:ℂ) * (Matrix.conj U)ᴴ) a₂ b₂
        = U a₁ i * star (U a₂ i) * (star (U b₁ j) * U b₂ j)
    rw [e1, e2]; ring
  rw [hLeftSum]
  -- Step 2: identify the two sum factors with entries of `U * Uᴴ = 1`.
  have hLeft : (∑ i : Fin d, U a₁ i * star (U a₂ i))
              = (1 : Matrix (Fin d) (Fin d) ℂ) a₁ a₂ := by
    have := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M a₁ a₂) hUU
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using this
  have hRight : (∑ j : Fin d, star (U b₁ j) * U b₂ j)
              = (1 : Matrix (Fin d) (Fin d) ℂ) b₂ b₁ := by
    have hh := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M b₂ b₁) hUU
    have h1 : ∑ j : Fin d, U b₂ j * star (U b₁ j)
              = (1 : Matrix (Fin d) (Fin d) ℂ) b₂ b₁ := by
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using hh
    calc (∑ j : Fin d, star (U b₁ j) * U b₂ j)
        = ∑ j : Fin d, U b₂ j * star (U b₁ j) := by
              refine Finset.sum_congr rfl (fun j _ => ?_); ring
      _ = _ := h1
  rw [hLeft, hRight]
  -- Step 3: compute the RHS entry, also δ_{a₁ a₂} · δ_{b₁ b₂}.
  have hRHS :
      (∑ i : Fin d, ∑ j : Fin d,
          (kron (Matrix.single i j (1:ℂ)) (Matrix.single i j (1:ℂ)))
            (a₁, a₂) (b₁, b₂))
      = (1 : Matrix (Fin d) (Fin d) ℂ) a₁ a₂ *
          (1 : Matrix (Fin d) (Fin d) ℂ) b₂ b₁ := by
    -- Pointwise: kron(single i j 1, single i j 1) (a₁,a₂) (b₁,b₂)
    --  = (if i=a₁ ∧ j=b₁ then 1 else 0) * (if i=a₂ ∧ j=b₂ then 1 else 0)
    have hKron : ∀ i j : Fin d,
        (kron (Matrix.single i j (1:ℂ)) (Matrix.single i j (1:ℂ)))
          (a₁, a₂) (b₁, b₂)
        = (if i = a₁ ∧ j = b₁ then (1:ℂ) else 0) *
          (if i = a₂ ∧ j = b₂ then (1:ℂ) else 0) := by
      intro i j
      simp [kron, Matrix.kronecker_apply, Matrix.single_apply]
    have hsum : (∑ i : Fin d, ∑ j : Fin d,
        (kron (Matrix.single i j (1:ℂ)) (Matrix.single i j (1:ℂ)))
          (a₁, a₂) (b₁, b₂))
        = ∑ i : Fin d, ∑ j : Fin d,
            (if i = a₁ ∧ j = b₁ then (1:ℂ) else 0) *
            (if i = a₂ ∧ j = b₂ then (1:ℂ) else 0) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact hKron i j
    rw [hsum]
    by_cases ha : a₁ = a₂
    · by_cases hb : b₁ = b₂
      · subst ha; subst hb
        simp only [Matrix.one_apply_eq, mul_one]
        -- ∑ i ∑ j, [i=a₁∧j=b₁]·[i=a₁∧j=b₁] = ∑ i ∑ j, [i=a₁∧j=b₁] = 1
        have hsq : ∀ i j : Fin d,
            (if i = a₁ ∧ j = b₁ then (1:ℂ) else 0) *
            (if i = a₁ ∧ j = b₁ then (1:ℂ) else 0)
            = if i = a₁ ∧ j = b₁ then (1:ℂ) else 0 := by
          intro i j; by_cases h : i = a₁ ∧ j = b₁ <;> simp [h]
        simp_rw [hsq]
        rw [Finset.sum_eq_single a₁]
        · rw [Finset.sum_eq_single b₁]
          · simp
          · intro j _ hj; simp [hj]
          · intro h; exact absurd (Finset.mem_univ b₁) h
        · intro i _ hi
          apply Finset.sum_eq_zero
          intro j _
          have : ¬ (i = a₁ ∧ j = b₁) := fun h => hi h.1
          simp [this]
        · intro h; exact absurd (Finset.mem_univ a₁) h
      · -- b₁ ≠ b₂
        subst ha
        rw [Matrix.one_apply_eq, one_mul, Matrix.one_apply_ne (Ne.symm hb)]
        refine Finset.sum_eq_zero (fun i _ => ?_)
        refine Finset.sum_eq_zero (fun j _ => ?_)
        by_cases h1 : i = a₁ ∧ j = b₁
        · have h2 : ¬ (i = a₁ ∧ j = b₂) := by
            intro hh; exact hb (h1.2.symm.trans hh.2)
          rw [if_pos h1, if_neg h2, mul_zero]
        · rw [if_neg h1, zero_mul]
    · -- a₁ ≠ a₂
      rw [Matrix.one_apply_ne ha, zero_mul]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      refine Finset.sum_eq_zero (fun j _ => ?_)
      by_cases h1 : i = a₁ ∧ j = b₁
      · have h2 : ¬ (i = a₂ ∧ j = b₂) := by
          intro hh; exact ha (h1.1.symm.trans hh.1)
        rw [if_pos h1, if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
  rw [hRHS]

/-! ### Conjugation helpers (iter-… add). -/

/-- Entry of the Choi matrix: (Choi Φ)(a,b)(c,e) = (Φ(|a⟩⟨c|))_{b,e}. -/
lemma Choi_apply {d : ℕ} (Φ : QChan d d) (a b c e : Fin d) :
    (Choi Φ) (a, b) (c, e) = (Φ (Matrix.single a c (1 : ℂ))) b e := by
  unfold Choi
  simp only [Matrix.sum_apply, kron, Matrix.kronecker]
  simp [Matrix.single_apply, ite_and]

/-- Entrywise complex conjugation distributes over matrix multiplication. -/
theorem _root_.Matrix.conj_mul {n : Type*} [Fintype n]
    {m p : Type*} (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    (A * B).conj = A.conj * B.conj := by
  unfold Matrix.conj
  exact Matrix.map_mul

/-- Entrywise complex conjugation commutes with conjugate transpose. -/
theorem _root_.Matrix.conj_conjTranspose {m n : Type*} (A : Matrix m n ℂ) :
    (Aᴴ).conj = (A.conj)ᴴ := by
  funext i j
  simp [Matrix.conj_apply, Matrix.conjTranspose_apply]

/-- Entrywise complex conjugation fixes the identity matrix. -/
theorem _root_.Matrix.conj_one {n : Type*} [DecidableEq n] :
    (1 : Matrix n n ℂ).conj = 1 := by
  unfold Matrix.conj
  exact Matrix.map_one _ (map_zero _) (map_one _)

/-- The entrywise conjugate of a unitary matrix is unitary. -/
theorem _root_.Matrix.conj_unitary {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hUU : U * Uᴴ = 1) :
    U.conj * (U.conj)ᴴ = 1 := by
  rw [← Matrix.conj_conjTranspose, ← Matrix.conj_mul, hUU, Matrix.conj_one]

/-- The entrywise conjugate of a left-unitary matrix is left-unitary. -/
theorem _root_.Matrix.conj_unitary_left {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hUU' : Uᴴ * U = 1) :
    (U.conj)ᴴ * U.conj = 1 := by
  rw [← Matrix.conj_conjTranspose, ← Matrix.conj_mul, hUU', Matrix.conj_one]

/-- ℂ-linear cone helper: conjugation preserves zero. -/
theorem _root_.Matrix.conj_zero {m n : Type*} : (0 : Matrix m n ℂ).conj = 0 := by
  funext i j; simp [Matrix.conj_apply]

/-- ℂ-linear cone helper: conjugation distributes over addition. -/
theorem _root_.Matrix.conj_add {m n : Type*} (A B : Matrix m n ℂ) :
    (A + B).conj = A.conj + B.conj := by
  funext i j; simp [Matrix.conj_apply, Matrix.add_apply, star_add]

/-- ℂ-linear cone helper: conjugation is conjugate-ℂ-linear in scalar multiplication. -/
theorem _root_.Matrix.conj_smul {m n : Type*} (c : ℂ) (A : Matrix m n ℂ) :
    (c • A).conj = (star c) • A.conj := by
  funext i j
  simp [Matrix.conj_apply, Matrix.smul_apply, star_smul, star_mul, mul_comm]

/-- ℂ-linear cone helper: conjugation distributes over negation. -/
theorem _root_.Matrix.conj_neg {m n : Type*} (A : Matrix m n ℂ) :
    (-A).conj = - A.conj := by
  funext i j; simp [Matrix.conj_apply, Matrix.neg_apply, star_neg]

/-- Entrywise unfolding of Choi for a composed channel. -/
lemma choi_comp_apply {d : ℕ} (Φ Ψ : QChan d d) (a b c e : Fin d) :
    (Choi (Φ.comp Ψ)) (a, b) (c, e) =
    (Φ (Ψ (Matrix.single a c (1 : ℂ)))) b e := by
  rw [Choi_apply]; rfl

/-! ### Iterated sum reorder helpers.

Lean 4's `Finset.sum_comm` can fail with
`typeclass instance problem is stuck: AddCommMonoid ?m` on triple-nested
sums when the body itself contains further sums (so the elaborator cannot
yet pin the monoid for the inner aggregate). The lemmas below expose the
swap with an explicit `[AddCommMonoid M]` argument and an explicitly typed
body `f`, so call sites can write `rw [PPT2.sum_swap₂ (f := fun … => …)]`
or `rw [PPT2.sum_swap₃_outer …]` and have elaboration go through.

These helpers are pure rearrangements of `∑ … ∈ Finset.univ`; the proofs
reduce to `Finset.sum_comm` after type instances are fixed. -/

/-- Explicit-instance variant of `Finset.sum_comm`. Pinning the
`AddCommMonoid` argument and the body `f` helps the elaborator on nested
sums where the body's monoid would otherwise be left as a metavariable. -/
theorem sum_swap₂ {α β : Type*} [Fintype α] [Fintype β]
    {M : Type*} [AddCommMonoid M] (f : α → β → M) :
    ∑ x : α, ∑ y : β, f x y = ∑ y : β, ∑ x : α, f x y :=
  Finset.sum_comm

/-- Pull the innermost variable of a triple-nested iterated sum out to the
outermost position: `(x, y, z) ↦ (z, x, y)`. -/
theorem sum_swap₃_outer {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    {M : Type*} [AddCommMonoid M] (f : α → β → γ → M) :
    ∑ x : α, ∑ y : β, ∑ z : γ, f x y z
    = ∑ z : γ, ∑ x : α, ∑ y : β, f x y z := by
  have h1 : (∑ x : α, ∑ y : β, ∑ z : γ, f x y z)
          = ∑ x : α, ∑ z : γ, ∑ y : β, f x y z :=
    Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  rw [h1]
  exact Finset.sum_comm

/-- Swap the inner two variables of a triple-nested iterated sum:
`(x, y, z) ↦ (x, z, y)`. -/
theorem sum_swap₃_inner {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    {M : Type*} [AddCommMonoid M] (f : α → β → γ → M) :
    ∑ x : α, ∑ y : β, ∑ z : γ, f x y z
    = ∑ x : α, ∑ z : γ, ∑ y : β, f x y z :=
  Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)

/-- Full reverse of a triple-nested iterated sum: `(x, y, z) ↦ (z, y, x)`. -/
theorem sum_swap₃_rev {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    {M : Type*} [AddCommMonoid M] (f : α → β → γ → M) :
    ∑ x : α, ∑ y : β, ∑ z : γ, f x y z
    = ∑ z : γ, ∑ y : β, ∑ x : α, f x y z := by
  rw [sum_swap₃_outer (f := f)]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)

end PPT2

/-! ### Hilbert–Schmidt inner-product non-negativity helper.

`trace_mul_nonneg` : for two PSD complex matrices `A`, `B`, the real part of
`Tr(A * B)` is non-negative.  This is the finite-dimensional Hilbert–Schmidt
statement that `⟨A, B⟩ := Tr(A B) ≥ 0` when both operators are positive.

The proof uses the C*-characterisation: a matrix is `0 ≤ ·` in the matrix
order iff it is of the form `X⋆ * X`.  Writing `A = C⋆ C` and `B = D⋆ D`,
one has

  Tr(A B) = Tr((C⋆ C)(D⋆ D))
         = Tr(C D⋆ D C⋆)                -- cyclic trace
         = Tr((D C⋆)⋆ (D C⋆))           -- `(DC⋆)⋆ = C D⋆`
         ≥ 0                             -- `X⋆ X` is PSD, whose trace is real ≥ 0.
-/
open scoped MatrixOrder ComplexOrder in
theorem Matrix.PosSemidef.trace_mul_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  -- Step 1.  Write `A = C⋆ C` and `B = D⋆ D` via the C*-characterisation.
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  obtain ⟨D, hD⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  -- Step 2.  Cyclic shift.
  have hcyc : (A * B).trace
      = (star (D * star C) * (D * star C)).trace := by
    rw [hC, hD]
    -- Goal:  (star C * C * (star D * D)).trace
    --       = (star (D * star C) * (D * star C)).trace
    -- Rewrite RHS via star_mul / star_star.
    have h2 : (star (D * star C) : Matrix n n ℂ) * (D * star C)
              = (C * star D) * (D * star C) := by
      rw [star_mul, star_star]
    rw [h2]
    -- Rewrite LHS using associativity to Cstar * (C * Dstar) * D.
    have h1 : (star C : Matrix n n ℂ) * C * (star D * D)
              = star C * (C * star D) * D := by
      rw [Matrix.mul_assoc (star C) C (star D * D),
          ← Matrix.mul_assoc C (star D) D,
          Matrix.mul_assoc (star C) (C * star D) D]
    rw [h1]
    -- trace (starC * (C * starD) * D) = trace (D * starC * (C * starD))  by cyclic
    rw [Matrix.trace_mul_cycle (star C) (C * star D) D]
    -- trace (D * starC * (C * starD)) = trace ((C * starD) * (D * starC))  by comm
    -- Note: `D * star C * (C * star D)` is left-assoc: `((D * starC) * (C * starD))`.
    exact Matrix.trace_mul_comm (D * star C) (C * star D)
  -- Step 3.  `star X * X` is PSD, whose trace is ≥ 0 in ℂ.
  have hPSD : (star (D * star C) * (D * star C) : Matrix n n ℂ).PosSemidef := by
    -- Matrix.star_eq_conjTranspose rewrites `star M` to `Mᴴ`.
    rw [Matrix.star_eq_conjTranspose (D * star C)]
    exact Matrix.posSemidef_conjTranspose_mul_self (D * star C)
  have hTrNN : (0 : ℂ) ≤ (star (D * star C) * (D * star C) : Matrix n n ℂ).trace :=
    hPSD.trace_nonneg
  -- Step 4.  `0 ≤ z` in ℂ unfolds to `0 ≤ z.re ∧ 0 = z.im`.
  rw [hcyc]
  exact (Complex.nonneg_iff.mp hTrNN).1

/-! ### Matrix-unit decomposition (smul form).

`Matrix.eq_sum_single_smul` : every finite matrix equals the linear combination
of its matrix-unit basis weighted by its own entries.  Mathlib's
`Matrix.matrix_eq_sum_single` already gives `N = ∑ x, ∑ y, single x y (N x y)`;
this helper is the equivalent `N = ∑ x, ∑ y, N x y • single x y 1` form which
is the shape consumed by downstream Choi / PPT axiom-elimination work. -/
theorem Matrix.eq_sum_single_smul {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℂ) :
    N = ∑ x : n, ∑ y : n, N x y • Matrix.single x y (1 : ℂ) := by
  -- Convert each smul summand back to `single x y (N x y)`.
  have hcell : ∀ x y : n,
      (N x y) • Matrix.single x y (1 : ℂ) = Matrix.single x y (N x y) := by
    intro x y
    rw [Matrix.smul_single (N x y) x y (1 : ℂ), smul_eq_mul, mul_one]
  calc N = ∑ x : n, ∑ y : n, Matrix.single x y (N x y) :=
            Matrix.matrix_eq_sum_single N
    _ = ∑ x : n, ∑ y : n, N x y • Matrix.single x y (1 : ℂ) := by
            refine Finset.sum_congr rfl (fun x _ => ?_)
            refine Finset.sum_congr rfl (fun y _ => ?_)
            exact (hcell x y).symm



