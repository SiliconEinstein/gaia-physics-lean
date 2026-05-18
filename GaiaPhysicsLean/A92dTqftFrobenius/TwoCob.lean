/- 2D TQFT ↔ commutative Frobenius algebra
   LKM source claim: gcn_c8351754bdb44e38 (Dumitrescu et al. 2015, has evidence chain)
   Tier: A
   See: /personal/lean_swarm/projects/a9_2d_tqft_frobenius/PROBLEM.md

   This file encodes the 2-cobordism category `2Cob` *abstractly* via its
   universal property — Kock (Theorem 3.3.2) shows that `2Cob` is the free
   symmetric monoidal category on a commutative Frobenius algebra. We do
   not construct cobordisms geometrically; instead we capture the data of
   such a universal symmetric monoidal category as a structure carrying a
   distinguished commutative Frobenius algebra object (the circle `S^1`).

   The full universal property — that any commutative Frobenius algebra in
   another symmetric monoidal category is hit by an essentially-unique
   strong-symmetric-monoidal functor — will be injected as a hypothesis
   structure in `Theorem.lean`, where it is used to state the classifying
   equivalence.

   gap_kind: mathlib_missing — Mathlib lacks a free-symmetric-monoidal-
   category construction; encoding the universal property as data on a
   structure (rather than building 2Cob explicitly) defers that gap. -/

import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import GaiaPhysicsLean.A92dTqftFrobenius.Defs

namespace GaiaPhysicsLean.A92dTqftFrobenius

open CategoryTheory MonoidalCategory

universe v u

/-- Witness data for a *universal* 2-cobordism category: a symmetric monoidal
category equipped with a distinguished commutative Frobenius algebra object
`circle` (representing `S¹`). Compare Kock, *Frobenius Algebras and 2D
Topological Quantum Field Theories* (LMS Student Texts 59), Theorem 3.3.2.

The full universal property — that for any symmetric monoidal category `V`
and any commutative Frobenius algebra `A` in `V` there is an essentially-
unique strong-symmetric-monoidal functor `carrier ⥤ V` sending `circle ↦ A`
— is *not* required as a field here. It is captured separately, as a
hypothesis structure attached to a `TwoCobUP` term in `Theorem.lean`,
because Mathlib does not yet provide a free-symmetric-monoidal-category
construction, and we want this stub to be lightweight. -/
structure TwoCobUP : Type (max (u+1) (v+1)) where
  /-- The underlying type of objects of the universal 2Cob category. -/
  carrier : Type u
  /-- Category structure on `carrier`. -/
  [cat : Category.{v} carrier]
  /-- Monoidal structure (disjoint union of 1-manifolds). -/
  [mon : MonoidalCategory.{v} carrier]
  /-- Symmetric structure (twist of components). -/
  [sym : SymmetricCategory.{v} carrier]
  /-- The distinguished circle object `S¹`. -/
  circle : carrier
  /-- The commutative Frobenius algebra structure on the circle. -/
  [frob : CommFrobeniusObj circle]

attribute [instance] TwoCobUP.cat TwoCobUP.mon TwoCobUP.sym TwoCobUP.frob

/-- Strengthened universal property: `TwoCobUP` plus an extension functor.
For any symmetric monoidal `V` and any `CommFrobeniusObj A` in `V`, there
exists a strong-symmetric-monoidal functor `carrier ⥤ V` sending `circle ↦ A`,
and this functor is unique up to unique monoidal natural isomorphism.

gap_kind: mathlib_missing — the existence of `extend` would follow from the
free-symmetric-monoidal-category construction (Kock §3.3) once Mathlib
provides it. We record it as data on the structure so that `TwoCobClassifies`
becomes derivable without a `sorry`. -/
structure TwoCobUP.WithExtend extends TwoCobUP.{v, u} where
  /-- The extension functor: given a commutative Frobenius algebra `A` in `V`,
  produce a strong-symmetric-monoidal functor `carrier ⥤ V` over `A`. -/
  extend : ∀ {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V]
             [SymmetricCategory.{v} V] (A : V) [CommFrobeniusObj A],
             carrier ⥤ V
  /-- The extension functor is strong monoidal. -/
  extend_monoidal : ∀ {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V]
                      [SymmetricCategory.{v} V] (A : V) [CommFrobeniusObj A],
                      (extend A).Monoidal
  /-- The extension functor is braided (hence symmetric monoidal). -/
  extend_braided : ∀ {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V]
                     [SymmetricCategory.{v} V] (A : V) [CommFrobeniusObj A],
                     (extend A).Braided
  /-- The extension functor sends `circle` to `A`. -/
  extend_circle : ∀ {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V]
                    [SymmetricCategory.{v} V] (A : V) [CommFrobeniusObj A],
                    (extend A).obj circle = A
  /-- The transported Frobenius structure on `(extend A).obj circle` agrees
  with the original Frobenius structure on `A`, modulo the carrier equality
  `extend_circle`. This is the on-the-nose strengthening required by the
  free-SMC universal property to obtain a strict `Equiv` (rather than only a
  categorical equivalence) between functors and Frobenius algebras.

  gap_kind: mathlib_missing — once Mathlib provides the explicit
  free-symmetric-monoidal-category construction (Kock §3.3), this field is
  derivable from the defining property of `extend`. -/
  extend_frob_circle : ∀ {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V]
                         [SymmetricCategory.{v} V] (A : V) [hA : CommFrobeniusObj A],
                         HEq (CommFrobeniusObj.map (extend A) circle) hA
  /-- Round-trip: applying `extend` to the image of a functor `F` recovers `F`
  up to a monoidal natural isomorphism (uniqueness clause). This is the
  honest categorical universal property — uniqueness up to unique iso,
  *not* on-the-nose equality. -/
  extend_unique : ∀ {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V]
                    [SymmetricCategory.{v} V] (F : carrier ⥤ V) [F.Braided],
                    extend (F.obj circle) ≅ F

end GaiaPhysicsLean.A92dTqftFrobenius
