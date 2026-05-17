/- Naimark dilation theorem (POVM realizability)
   LKM source claim: gcn_b9e7abd2ad804f29
   Tier: B
   See: README.md (this directory)

   **Primary target**: `naimark_dilation_finite`

   Every finite POVM {E_i} on Hilbert space H is realizable as a projective measurement
   on an extended space K for some finite-dim K. Mirror of Stinespring (A3) for POVMs.

   The construction uses K = H^{|ι|} (i.e., |ι| copies of H), so the extended index type
   is `n × ι`. We build an **isometry** V : H → K together with projections P_i on the
   extended space such that Vᴴ * P_i * V = E_i for every outcome i.

   This is the standard Naimark construction; previous iterations attempted a smaller K = ι
   which only works for PVMs and required two non-standard axioms (idempotency and
   orthogonality of POVM elements). Those axioms have been removed.
-/

import Mathlib

namespace GaiaPhysicsLean.B7NaimarkDilation

open Matrix
open scoped MatrixOrder ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## POVM Definition -/

/-- A POVM (Positive Operator-Valued Measure) is a finite collection of positive operators
    that sum to the identity. -/
structure POVM (𝕜 : Type*) [RCLike 𝕜] [StarRing 𝕜]
    (n : Type*) [Fintype n] [DecidableEq n]
    (ι : Type*) [Fintype ι] where
  /-- The POVM elements E_i -/
  elements : ι → Matrix n n 𝕜
  /-- Each element is positive semidefinite -/
  positive : ∀ i, (elements i).PosSemidef
  /-- The elements sum to identity -/
  sum_eq_one : ∑ i, elements i = 1

namespace POVM

variable {ι : Type*} [Fintype ι] [StarRing 𝕜] (E : POVM 𝕜 n ι)

/-- Each POVM element is Hermitian -/
lemma isHermitian (i : ι) : (E.elements i).IsHermitian :=
  (E.positive i).1

end POVM

/-! ## Extended Space and Construction

For the Naimark dilation of a general POVM, the auxiliary space K has dimension `n * |ι|`
(i.e., one copy of H per outcome). The extended index type is `n × ι`.
-/

section NaimarkDilation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : POVM 𝕜 n ι)

/-- For the Naimark dilation, each POVM element is bounded above by the identity. -/
lemma povm_element_le_one (i : ι) : E.elements i ≤ 1 := by
  have h := E.sum_eq_one
  rw [← h]
  apply Finset.single_le_sum
  · intro j _
    exact (E.positive j).nonneg
  · exact Finset.mem_univ i

/-- The defect operator I - E_i is positive semidefinite. -/
lemma defect_posSemidef (i : ι) : (1 - E.elements i).PosSemidef := by
  rw [← Matrix.le_iff]
  exact povm_element_le_one E i

/-- Square root of a POVM element via the continuous functional calculus. -/
noncomputable def sqrtElement (i : ι) : Matrix n n 𝕜 :=
  CFC.sqrt (E.elements i)

/-- The square root of a POVM element is positive semidefinite. -/
lemma sqrtElement_posSemidef (i : ι) : (sqrtElement E i).PosSemidef := by
  unfold sqrtElement
  exact (CFC.sqrt_nonneg (E.elements i)).posSemidef

/-- The square root of a POVM element is Hermitian. -/
lemma sqrtElement_isHermitian (i : ι) : (sqrtElement E i).IsHermitian :=
  (sqrtElement_posSemidef E i).1

/-- The square root squared returns the original element. -/
lemma sqrtElement_mul_self (i : ι) :
    (sqrtElement E i) * (sqrtElement E i) = E.elements i := by
  unfold sqrtElement
  exact CFC.sqrt_mul_sqrt_self (E.elements i) (E.positive i).nonneg

/-- Conjugate transpose of the square root equals the square root (it is Hermitian). -/
lemma sqrtElement_conjTranspose (i : ι) :
    (sqrtElement E i).conjTranspose = sqrtElement E i :=
  (sqrtElement_isHermitian E i)

/-! ### Isometry V : H → K with K = H^{|ι|}

We define V as the column matrix whose rows (indexed by `n × ι`) stack the square
roots of the POVM elements: `V (j, i) k = (sqrt E_i) j k`.
-/

/-- The Naimark isometry V : H → K, where K has index type `n × ι`.
    `V (j, i) k = (sqrt E_i) j k`. -/
noncomputable def naimarkIsometry : Matrix (n × ι) n 𝕜 :=
  Matrix.of (fun (p : n × ι) (k : n) => sqrtElement E p.2 p.1 k)

/-- The projections on the extended space: P_i is the diagonal indicator picking out
    the copy of H labelled by `i`. -/
noncomputable def naimarkProjection (_E : POVM 𝕜 n ι) (i : ι) :
    Matrix (n × ι) (n × ι) 𝕜 :=
  Matrix.diagonal (fun (p : n × ι) => if p.2 = i then (1 : 𝕜) else 0)

/-- `naimarkProjection i` is Hermitian. -/
lemma naimarkProjection_isHermitian (i : ι) :
    (naimarkProjection E i).IsHermitian := by
  unfold naimarkProjection
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  unfold IsSelfAdjoint
  ext p
  by_cases h : p.2 = i
  · simp [Pi.star_apply, h, star_one]
  · simp [Pi.star_apply, h, star_zero]

/-- `naimarkProjection i` is idempotent. -/
lemma naimarkProjection_mul_self (i : ι) :
    naimarkProjection E i * naimarkProjection E i = naimarkProjection E i := by
  unfold naimarkProjection
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  ext p
  by_cases h : p.2 = i
  · simp [h]
  · simp [h]

/-- `naimarkProjection i` and `naimarkProjection j` are orthogonal for `i ≠ j`. -/
lemma naimarkProjection_mul_orthogonal (i j : ι) (hij : i ≠ j) :
    naimarkProjection E i * naimarkProjection E j = 0 := by
  unfold naimarkProjection
  rw [Matrix.diagonal_mul_diagonal]
  rw [show (0 : Matrix (n × ι) (n × ι) 𝕜) = Matrix.diagonal (fun _ : n × ι => (0 : 𝕜))
        from (Matrix.diagonal_zero).symm]
  congr 1
  ext p
  by_cases hp : p.2 = i
  · have hpj : p.2 ≠ j := hp ▸ hij
    simp [hp, hpj, hij]
  · simp [hp]

/-- The naimark projections sum to the identity. -/
lemma naimarkProjection_sum_eq_one :
    ∑ i, naimarkProjection E i = 1 := by
  unfold naimarkProjection
  ext a b
  simp only [Matrix.sum_apply, Matrix.diagonal, Matrix.of_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    simp [Finset.sum_ite_eq']
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i _
    by_cases h2 : a.2 = i
    · by_cases h3 : b.2 = i
      · -- a ≠ b but a.2 = b.2 = i; need to show diagonal entry is 0 at (a,b)
        simp only [h2, if_true]
        exact if_neg h
      · simp [h2, h3, h]
    · simp [h2, h]

/-- The isometry property: Vᴴ * V = 1. -/
lemma naimarkIsometry_isometry :
    (naimarkIsometry E).conjTranspose * naimarkIsometry E = 1 := by
  unfold naimarkIsometry
  ext j k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
  -- LHS: ∑_{(p,i)} starRingEnd((sqrt E_i) p j) * (sqrt E_i) p k
  rw [show (∑ x : n × ι, (starRingEnd 𝕜) (sqrtElement E x.2 x.1 j) * sqrtElement E x.2 x.1 k)
        = ∑ i, ∑ p, (starRingEnd 𝕜) (sqrtElement E i p j) * sqrtElement E i p k from ?_]
  · -- ∑_p star((sqrt E_i) p j) * (sqrt E_i) p k = ((sqrt E_i)ᴴ * sqrt E_i) j k = (E_i) j k
    have heq : ∀ i,
        (∑ p, (starRingEnd 𝕜) (sqrtElement E i p j) * sqrtElement E i p k)
          = (sqrtElement E i * sqrtElement E i) j k := by
      intro i
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intros p _
      have hH : (sqrtElement E i).conjTranspose = sqrtElement E i :=
        sqrtElement_conjTranspose E i
      have hpj : (sqrtElement E i) j p = (starRingEnd 𝕜) ((sqrtElement E i) p j) := by
        have := congrArg (fun M => M j p) hH
        simp [Matrix.conjTranspose_apply, RCLike.star_def] at this
        exact this.symm
      rw [hpj]
    simp_rw [heq]
    simp_rw [sqrtElement_mul_self]
    rw [← Matrix.sum_apply]
    rw [E.sum_eq_one]
  · -- Convert ∑_{(p,i)} to ∑_i ∑_p
    rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- The compression property: Vᴴ * P_i * V = E_i. -/
lemma naimarkIsometry_compress (i : ι) :
    (naimarkIsometry E).conjTranspose * naimarkProjection E i * naimarkIsometry E
      = E.elements i := by
  unfold naimarkIsometry naimarkProjection
  ext j k
  -- Expand the matrix product: (Vᴴ * P_i * V) j k = ∑_a ∑_b Vᴴ j b * P_i b a * V a k
  -- P_i b a is nonzero only when b = a and a.2 = i; gives V a j conjugated times V a k.
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
             Matrix.diagonal, RCLike.star_def]
  -- After diagonal expansion, ∑_b star(V j b) * (diag b a) = star(V j a) * (if a.2 = i then 1 else 0)
  -- Then sum over a is restricted to a.2 = i.
  have step : ∀ a : n × ι,
      (∑ b : n × ι, (starRingEnd 𝕜) (sqrtElement E b.2 b.1 j)
                    * (if b = a then (if b.2 = i then (1 : 𝕜) else 0) else 0))
        = (starRingEnd 𝕜) (sqrtElement E a.2 a.1 j) * (if a.2 = i then (1 : 𝕜) else 0) := by
    intro a
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hba
      simp [hba]
    · intro h
      exact absurd (Finset.mem_univ a) h
  -- Substitute into outer sum
  rw [show (∑ a : n × ι, (∑ b : n × ι, (starRingEnd 𝕜) (sqrtElement E b.2 b.1 j)
                    * (if b = a then (if b.2 = i then (1 : 𝕜) else 0) else 0))
                  * sqrtElement E a.2 a.1 k)
        = ∑ a : n × ι, (starRingEnd 𝕜) (sqrtElement E a.2 a.1 j)
            * (if a.2 = i then (1 : 𝕜) else 0) * sqrtElement E a.2 a.1 k from ?_]
  · -- Now compute: sum is over a = (p, i') and zero unless i' = i
    rw [show (∑ a : n × ι, (starRingEnd 𝕜) (sqrtElement E a.2 a.1 j)
              * (if a.2 = i then (1 : 𝕜) else 0) * sqrtElement E a.2 a.1 k)
          = ∑ p : n, (starRingEnd 𝕜) (sqrtElement E i p j) * sqrtElement E i p k from ?_]
    · -- Recognize ∑_p star(sqrt(E_i) p j) * sqrt(E_i) p k = (sqrt(E_i) * sqrt(E_i)) j k = E_i j k
      have hH : (sqrtElement E i).conjTranspose = sqrtElement E i :=
        sqrtElement_conjTranspose E i
      have hpj : ∀ p, (sqrtElement E i) j p = (starRingEnd 𝕜) ((sqrtElement E i) p j) := by
        intro p
        have := congrArg (fun M => M j p) hH
        simp [Matrix.conjTranspose_apply, RCLike.star_def] at this
        exact this.symm
      have : (∑ p : n, (starRingEnd 𝕜) (sqrtElement E i p j) * sqrtElement E i p k)
              = (sqrtElement E i * sqrtElement E i) j k := by
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intros p _
        rw [hpj]
      rw [this, sqrtElement_mul_self]
    · -- Restrict sum over a = (p, i') to a.2 = i
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intros p _
      rw [Finset.sum_eq_single i]
      · simp
      · intro i' _ hii'
        simp [hii']
      · intro h
        exact absurd (Finset.mem_univ i) h
  · apply Finset.sum_congr rfl
    intros a _
    rw [step]

/-- The proper Naimark dilation: there exist orthogonal projections {P_i} on the extended
    space `n × ι` and an isometry V : H → K such that Vᴴ * P_i * V = E_i.
    This works for *general* POVMs, not just PVMs. -/
theorem naimark_dilation_finite_isometry :
    ∃ (P : ι → Matrix (n × ι) (n × ι) 𝕜)
      (V : Matrix (n × ι) n 𝕜),
      (∀ i, (P i).IsHermitian) ∧
      (∀ i, P i * P i = P i) ∧
      (∀ i j, i ≠ j → P i * P j = 0) ∧
      (∑ i, P i = 1) ∧
      V.conjTranspose * V = 1 ∧
      (∀ i, V.conjTranspose * P i * V = E.elements i) := by
  refine ⟨naimarkProjection E, naimarkIsometry E, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact naimarkProjection_isHermitian E
  · exact naimarkProjection_mul_self E
  · exact naimarkProjection_mul_orthogonal E
  · exact naimarkProjection_sum_eq_one E
  · exact naimarkIsometry_isometry E
  · exact naimarkIsometry_compress E

end NaimarkDilation

/-! ## Main Theorem -/

/-- **Naimark Dilation Theorem (isometry form)**.
    Every finite POVM {E_i} on a Hilbert space H is realised by a projective measurement
    on an extended space K = H^{|ι|} compressed by an isometry V.

    Concretely: given a POVM {E_i} with i ranging over a finite outcome set ι, there exist
    1. orthogonal projections {P_i} on K with index type `n × ι`, summing to identity, and
    2. an isometry V : H → K (so Vᴴ * V = 1),
    such that Vᴴ * P_i * V = E_i for every outcome i.

    This is the quantum measurement analogue of Stinespring dilation. Unlike the previous
    iteration which used the smaller K = ι and required POVM elements to be PVMs, this
    construction works for *general* POVMs without extra axioms. -/
theorem naimark_dilation_finite {ι : Type*} [Fintype ι] [DecidableEq ι] (E : POVM 𝕜 n ι) :
    ∃ (P : ι → Matrix (n × ι) (n × ι) 𝕜)
      (V : Matrix (n × ι) n 𝕜),
      (∀ i, (P i).IsHermitian) ∧
      (∀ i, P i * P i = P i) ∧
      (∀ i j, i ≠ j → P i * P j = 0) ∧
      (∑ i, P i = 1) ∧
      V.conjTranspose * V = 1 ∧
      (∀ i, V.conjTranspose * P i * V = E.elements i) :=
  naimark_dilation_finite_isometry E

end GaiaPhysicsLean.B7NaimarkDilation
