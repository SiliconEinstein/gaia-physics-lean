/-
  Reeh–Schlieder: core AQFT definitions (minimal version)
  LKM: gcn_687a62424c964753
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.MetricSpace.Closeds

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

/-- Bounded linear operator on a Hilbert space. -/
abbrev BoundedOp (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] := H →L[ℂ] H

/-! ## Local net of operator algebras (Haag–Kastler axioms) -/

/-- A local net assigns an operator algebra to each region. -/
structure LocalNet (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The algebra assigned to each region. -/
  alg : Set MinkowskiSpace → Set (BoundedOp H)
  /-- Isotony: O₁ ⊆ O₂ → 𝒜(O₁) ⊆ 𝒜(O₂). -/
  isotony : ∀ O₁ O₂ : Set MinkowskiSpace, O₁ ⊆ O₂ → alg O₁ ⊆ alg O₂
  /-- Locality (Einstein causality): spacelike separated algebras commute. -/
  locality : ∀ O₁ O₂ : Set MinkowskiSpace,
    O₂ ⊆ causalComplement O₁ →
    ∀ A ∈ alg O₁, ∀ B ∈ alg O₂, A * B = B * A
  /-- Weak additivity: union of translated algebras is dense. -/
  weak_additivity : ∀ O : Set MinkowskiSpace, O.Nonempty →
    ∀ A : BoundedOp H, ∀ ε > 0,
    ∃ B : BoundedOp H, (∃ O' : Set MinkowskiSpace, B ∈ alg O') ∧
      ‖A - B‖ < ε

/-! ## Vacuum representation -/

/-- A vacuum representation with a distinguished vacuum vector. -/
structure VacuumRep (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  net : LocalNet H
  /-- The vacuum vector. -/
  vacuum : H
  /-- Vacuum is normalized. -/
  vacuum_normalized : ‖vacuum‖ = 1
  /-- Irreducibility: the only closed invariant subspaces are `{0}` and `H`. -/
  irreducible : ∀ (S : Set H), IsClosed S →
    (∀ O : Set MinkowskiSpace, ∀ A ∈ net.alg O, ∀ v ∈ S, A v ∈ S) →
    S = {0} ∨ S = Set.univ

/-! ## Cyclic and separating predicates -/

/-- v is cyclic for algebra 𝒜: the orbit 𝒜 • v is dense in H. -/
def IsCyclicVector (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : H) (𝒜 : Set (BoundedOp H)) : Prop :=
  Dense {w : H | ∃ A ∈ 𝒜, w = A v}

/-- v is separating for algebra 𝒜: A • v = 0 → A = 0. -/
def IsSeparatingVector (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : H) (𝒜 : Set (BoundedOp H)) : Prop :=
  ∀ A ∈ 𝒜, A v = 0 → A = 0

end GaiaPhysicsLean.C1ReehSchliederAxiomatic
