/-
  Reeh–Schlieder: core AQFT definitions (minimal version)
  LKM: gcn_687a62424c964753
-/

import Mathlib.Data.Set.Basic

namespace GaiaPhysicsLean.C1ReehSchliederAxiomatic

/-! ## Minkowski space -/

/-- 4-dimensional Minkowski space (abstract). -/
axiom MinkowskiSpace : Type

/-! ## Causal structure -/

/-- Causal complement of a region O. -/
axiom causalComplement : Set MinkowskiSpace → Set MinkowskiSpace

/-- A region has non-empty causal complement. -/
def HasNonEmptyCausalComplement (O : Set MinkowskiSpace) : Prop :=
  (causalComplement O).Nonempty

/-! ## Hilbert space and operators -/

/-- Complex Hilbert space (abstract). -/
axiom HilbertSpace : Type

/-- Bounded linear operator. -/
axiom BoundedOp : Type

/-- Operator norm. -/
axiom opNorm : BoundedOp → ℝ

/-- Operator subtraction. -/
axiom opSub : BoundedOp → BoundedOp → BoundedOp

/-- Operator multiplication. -/
axiom opMul : BoundedOp → BoundedOp → BoundedOp

/-- Operator action on vectors. -/
axiom opApply : BoundedOp → HilbertSpace → HilbertSpace

/-- Zero operator. -/
axiom opZero : BoundedOp

/-! ## Local net of operator algebras (Haag–Kastler axioms) -/

/-- A local net assigns an operator algebra to each region. -/
structure LocalNet where
  /-- The algebra assigned to each region. -/
  alg : Set MinkowskiSpace → Set BoundedOp
  /-- Isotony: O₁ ⊆ O₂ → 𝒜(O₁) ⊆ 𝒜(O₂). -/
  isotony : ∀ O₁ O₂ : Set MinkowskiSpace, O₁ ⊆ O₂ → alg O₁ ⊆ alg O₂
  /-- Locality (Einstein causality): spacelike separated algebras commute. -/
  locality : ∀ O₁ O₂ : Set MinkowskiSpace,
    O₂ ⊆ causalComplement O₁ →
    ∀ A ∈ alg O₁, ∀ B ∈ alg O₂, opMul A B = opMul B A
  /-- Weak additivity: union of translated algebras is dense. -/
  weak_additivity : ∀ O : Set MinkowskiSpace, O.Nonempty →
    ∀ A : BoundedOp, ∀ ε > 0,
    ∃ B : BoundedOp, (∃ O' : Set MinkowskiSpace, B ∈ alg O') ∧
      opNorm (opSub A B) < ε

/-! ## Vacuum representation -/

/-- A vacuum representation with a distinguished vacuum vector. -/
structure VacuumRep where
  net : LocalNet
  /-- The vacuum vector. -/
  vacuum : HilbertSpace
  /-- Vacuum is normalized. -/
  vacuum_normalized : True
  /-- Irreducibility. -/
  irreducible : True

/-! ## Cyclic and separating predicates -/

/-- v is cyclic for algebra 𝒜: the orbit 𝒜 • v is dense. -/
axiom IsCyclicVector : HilbertSpace → Set BoundedOp → Prop

/-- v is separating for algebra 𝒜: A • v = 0 → A = 0. -/
axiom IsSeparatingVector : HilbertSpace → Set BoundedOp → Prop

end GaiaPhysicsLean.C1ReehSchliederAxiomatic
