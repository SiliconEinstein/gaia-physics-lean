/- 2D TQFT ↔ commutative Frobenius algebra — Definitions
   LKM source claim: gcn_c8351754bdb44e38 (Dumitrescu et al. 2015, has evidence chain)
   Tier: A
   See: /personal/lean_swarm/projects/a9_2d_tqft_frobenius/PROBLEM.md

   This file introduces the categorical-algebra definitions used to express
   Kock's Theorem 3.3.2: a (commutative) Frobenius object internal to a
   monoidal (resp. braided monoidal) category.

   Builds on Mathlib's `MonObj` / `ComonObj` (in `CategoryTheory.Monoidal.Mon`
   and `CategoryTheory.Monoidal.Comon_`) and `BraidedCategory`.
-/

import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

namespace GaiaPhysicsLean.A92dTqftFrobenius

open CategoryTheory MonoidalCategory
open scoped MonObj ComonObj

universe v u

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

/-- A **Frobenius object** in a monoidal category: a monoid object together
with a comonoid object structure on the same underlying object, satisfying
the Frobenius compatibility law

`(id ⊗ Δ) ≫ (μ ⊗ id) = μ ≫ Δ = (Δ ⊗ id) ≫ (id ⊗ μ)`

(with associators inserted to make the composites typecheck). -/
class FrobeniusObj (X : V) extends MonObj X, ComonObj X where
  /-- Frobenius compatibility, "left" form:
  `(id_X ⊗ Δ) ≫ assoc⁻¹ ≫ (μ ⊗ id_X) = μ ≫ Δ`. -/
  frob_left :
      (X ◁ Δ) ≫ (α_ X X X).inv ≫ (μ ▷ X) = μ ≫ Δ := by cat_disch
  /-- Frobenius compatibility, "right" form:
  `(Δ ⊗ id_X) ≫ assoc ≫ (id_X ⊗ μ) = μ ≫ Δ`. -/
  frob_right :
      (Δ ▷ X) ≫ (α_ X X X).hom ≫ (X ◁ μ) = μ ≫ Δ := by cat_disch

namespace FrobeniusObj

attribute [reassoc (attr := simp)] frob_left frob_right

end FrobeniusObj

variable [BraidedCategory V]

/-- A **commutative Frobenius object** in a braided monoidal category: a
Frobenius object whose multiplication is invariant under the braiding,
`β ≫ μ = μ`. In a symmetric monoidal category this is the usual notion
of commutativity. -/
class CommFrobeniusObj (X : V) extends FrobeniusObj X where
  /-- Commutativity of multiplication with respect to the braiding. -/
  mul_comm : (β_ X X).hom ≫ μ = μ := by cat_disch

namespace CommFrobeniusObj

attribute [reassoc (attr := simp)] mul_comm

end CommFrobeniusObj

section FunctorTransport

variable {W : Type*} [Category W] [MonoidalCategory W] [BraidedCategory W]
variable (F : V ⥤ W) [F.Braided]

/-- A braided monoidal functor transports a commutative Frobenius object.

The Frobenius and commutativity proofs reduce, via the lax/oplax coherences
(`Functor.LaxMonoidal.μ_natural_*`, `Functor.OplaxMonoidal.δ_natural_*`),
the monoidal-functor lemma `Functor.Monoidal.map_associator(_inv)`, and the
zig-zag identity `Functor.Monoidal.μ_δ`, to the V-side Frobenius / commutativity
laws applied under `F.map`. -/
instance CommFrobeniusObj.map (X : V) [CommFrobeniusObj X] :
    CommFrobeniusObj (F.obj X) where
  one := Functor.LaxMonoidal.ε F ≫ F.map η[X]
  mul := Functor.LaxMonoidal.μ F X X ≫ F.map μ[X]
  one_mul := by simp [← F.map_comp]
  mul_one := by simp [← F.map_comp]
  mul_assoc := by
    simp_rw [comp_whiskerRight, Category.assoc, Functor.LaxMonoidal.μ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, Functor.LaxMonoidal.μ_natural_right_assoc]
    slice_lhs 3 4 => rw [← F.map_comp, MonObj.mul_assoc]
    simp
  counit := F.map ε[X] ≫ Functor.OplaxMonoidal.η F
  comul := F.map Δ[X] ≫ Functor.OplaxMonoidal.δ F X X
  counit_comul := by
    simp_rw [comp_whiskerRight, Category.assoc, Functor.OplaxMonoidal.δ_natural_left_assoc,
      Functor.OplaxMonoidal.left_unitality, ← F.map_comp_assoc, ComonObj.counit_comul]
  comul_counit := by
    simp_rw [MonoidalCategory.whiskerLeft_comp, Category.assoc,
      Functor.OplaxMonoidal.δ_natural_right_assoc, Functor.OplaxMonoidal.right_unitality,
      ← F.map_comp_assoc, ComonObj.comul_counit]
  comul_assoc := by
    simp_rw [comp_whiskerRight, Category.assoc, Functor.OplaxMonoidal.δ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Functor.OplaxMonoidal.δ_natural_right_assoc,
      ← F.map_comp_assoc, ComonObj.comul_assoc, F.map_comp, Category.assoc,
      Functor.OplaxMonoidal.associativity]
  frob_left := by
    -- Strategy:
    --  1. Combine F.map μ ≫ F.map Δ; apply the V-side Frobenius law.
    --  2. Use μ_natural_right and δ_natural_left to bring F.map's outside.
    --  3. Expand F.map α⁻¹ via `Functor.Monoidal.map_associator_inv`.
    --  4. Collapse the resulting μ ≫ δ pairs via `Functor.Monoidal.μ_δ`.
    have hfl : μ[X] ≫ Δ[X]
        = (X ◁ Δ[X]) ≫ (α_ X X X).inv ≫ (μ[X] ▷ X) := (FrobeniusObj.frob_left).symm
    rw [Category.assoc, ← F.map_comp_assoc, hfl, F.map_comp, F.map_comp]
    simp only [Category.assoc]
    rw [← Functor.OplaxMonoidal.δ_natural_left,
        ← Functor.LaxMonoidal.μ_natural_right_assoc,
        Functor.Monoidal.map_associator_inv,
        MonoidalCategory.whiskerLeft_comp, comp_whiskerRight]
    simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
  frob_right := by
    -- Mirror of frob_left using Functor.Monoidal.map_associator (hom version).
    have hfr : μ[X] ≫ Δ[X]
        = (Δ[X] ▷ X) ≫ (α_ X X X).hom ≫ (X ◁ μ[X]) := (FrobeniusObj.frob_right).symm
    rw [Category.assoc, ← F.map_comp_assoc, hfr, F.map_comp, F.map_comp]
    simp only [Category.assoc]
    rw [← Functor.OplaxMonoidal.δ_natural_right,
        ← Functor.LaxMonoidal.μ_natural_left_assoc,
        Functor.Monoidal.map_associator,
        comp_whiskerRight, MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
  mul_comm := by
    conv_lhs => rw [← Category.assoc]
    rw [← Functor.LaxBraided.braided, Category.assoc, ← F.map_comp, CommFrobeniusObj.mul_comm]

end FunctorTransport


end GaiaPhysicsLean.A92dTqftFrobenius
