/-
Copyright (c) 2026 Gaia Discovery. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaia Discovery Agent
-/
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Sets.Compacts
import Mathlib.Analysis.CStarAlgebra.Matrix
-- NOTE: We deliberately do NOT `import PPT2.Mathlib.Quaternions` here. The geometric
-- bridge SU(2) ≅ S³ via unit quaternions lives in that file. HaarSU2 only needs the
-- *abstract* compactness of SU(2), which is now proved in `instCompactSpaceSU2` below
-- via Heine-Borel (entrywise bound + closedness of `unitary`). The Quaternion homeomorphism
-- is therefore *not* required for the Haar-measure construction; we keep this file
-- decoupled from `Quaternions.lean` to avoid build entanglement.

/-!
# Haar measure on SU(2)

This file constructs the Haar (probability) measure on `SU(2)`, modelled in Mathlib as
`Matrix.unitaryGroup (Fin 2) ℂ` — the group of `2×2` unitary matrices over `ℂ`.

## Strategy

The Haar measure on a compact, Hausdorff topological group is unique up to scaling.
We use the abstract construction `MeasureTheory.Measure.haarMeasure` (Mathlib), specialised
to the `PositiveCompacts` set `K₀ = ⟨univ, isCompact_univ⟩`. Since `K₀` is the whole group,
`haarMeasure_self` directly gives `haarMeasureSU2 univ = 1`, so the resulting measure is
automatically a probability measure.

The geometric content (S³ ≅ SU(2) via unit quaternions) is established in
`PPT2/Mathlib/Quaternions.lean`; uniqueness of bi-invariant probability Haar measures on
compact groups (`MeasureTheory.Measure.Haar.Unique`) then identifies `haarMeasureSU2` with
the spherical measure pulled back along the unit-quaternion isomorphism.

## Main definitions

* `haarMeasureSU2`: the (unique) left-invariant probability Haar measure on SU(2).

## Main theorems

* `haarMeasureSU2_normalized`: `haarMeasureSU2 univ = 1`.
* `isHaarMeasureSU2`: the measure is a (left-invariant, regular, σ-finite) Haar measure.
* `isProbabilityMeasureSU2`: the measure is a probability measure.

## Implementation notes

`Matrix.unitaryGroup n α` is defined in Mathlib as a `Submonoid` of `Matrix n n α`.
The ambient ring `Matrix n n ℂ` is **not** a topological group (it is a topological ring,
and inversion is not globally continuous). Therefore the `Subgroup`-inheritance instance
`Subgroup.instIsTopologicalGroup` is not available.

We provide the missing instances directly:
* `TopologicalSpace`, `T2Space`: free, via `Subtype` of the underlying matrix space.
* `ContinuousMul`: free, via `Submonoid.continuousMul` (since `Matrix n n ℂ` is a
  topological ring).
* `ContinuousInv`: proved here, using the identity `U⁻¹ = star U` (definitional in
  `Matrix.UnitaryGroup`) and continuity of `Matrix.conjTranspose`/`star`.
* `IsTopologicalGroup`: combines the above.
* `MeasurableSpace`: defined as `borel`, with `BorelSpace` instance.
* `CompactSpace`: provided directly by `instCompactSpaceSU2` below, via the elementary
  Heine-Borel-style argument: the entries of a unitary matrix lie in the closed unit disc
  of `ℂ` (so the unitary group is bounded as a subset of the matrix product space) and the
  unitary subset is closed. No homeomorphism with `S³` and no quaternion topology is
  required.

## References

* Folland, "A Course in Abstract Harmonic Analysis", §2.2 (Haar on compact groups).
* Mathlib: `MeasureTheory.Measure.Haar.Basic`, `MeasureTheory.Measure.Haar.Unique`.

-/

open Matrix MeasureTheory MeasureTheory.Measure TopologicalSpace Set

namespace PPT2.Mathlib.HaarSU2

/-! ## Topological group instances on the unitary group over ℂ -/

section UnitaryTopology

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Inversion in `Matrix.unitaryGroup n ℂ` is continuous: the underlying value of `U⁻¹`
is `star U.val`, and `star = conjTranspose` is continuous on `Matrix n n ℂ`. -/
instance instContinuousInv :
    ContinuousInv (Matrix.unitaryGroup n ℂ) where
  continuous_inv := by
    -- The Submonoid carries the subtype topology, which is induced from `Subtype.val`.
    -- So a function into the unitary group is continuous iff its underlying matrix-valued
    -- map is continuous.
    rw [continuous_induced_rng]
    -- Goal:
    --   `Continuous (fun U : Matrix.unitaryGroup n ℂ => ((U⁻¹ : Matrix.unitaryGroup n ℂ) :
    --                                                    Matrix n n ℂ))`.
    -- By `Matrix.UnitaryGroup.inv_val`, `↑U⁻¹ = star (↑U : Matrix n n ℂ)` (definitionally,
    -- `rfl`). So this map equals `star ∘ Subtype.val`, which is continuous.
    simp only [Function.comp_def, Matrix.UnitaryGroup.inv_val]
    exact continuous_star.comp continuous_subtype_val

/-- The unitary group over `ℂ` is a topological group: continuous multiplication comes from
`Submonoid.continuousMul` (matrices form a topological ring, so multiplication is
continuous), and continuous inversion is `instContinuousInv` above. -/
instance instIsTopologicalGroup :
    IsTopologicalGroup (Matrix.unitaryGroup n ℂ) where

end UnitaryTopology

/-! ## SU(2) typeclass plumbing -/

/-- `SU(2)` as an `abbrev` synonym for `Matrix.unitaryGroup (Fin 2) ℂ`. We use an
abbreviation rather than a `def` so that all instances on `Matrix.unitaryGroup (Fin 2) ℂ`
flow through transparently. -/
abbrev SU2 : Type := Matrix.unitaryGroup (Fin 2) ℂ

noncomputable instance : MeasurableSpace SU2 := borel _
instance : BorelSpace SU2 := ⟨rfl⟩

/-- **Compactness of SU(2).**

**Mathematical content.** SU(2) is a closed and bounded subset of the finite-dimensional
space `Matrix (Fin 2) (Fin 2) ℂ`, hence compact by the Heine-Borel theorem. Rather than
invoke Heine-Borel through the (instance-heavy) finite-dimensional normed-space machinery,
we give an *elementary* product-of-compacts argument:

* Every entry of a unitary matrix has norm `≤ 1`
  (`Matrix.entry_norm_bound_of_unitary` from `Mathlib.Analysis.CStarAlgebra.Matrix`), so the
  unitary group sits inside the matrix-set
  `(Metric.closedBall (0 : ℂ) 1).matrix : Set (Matrix (Fin 2) (Fin 2) ℂ)` — a finite product
  of compact closed unit discs in `ℂ`. This product is compact via `IsCompact.matrix`.
* The unitary group is closed in `Matrix (Fin 2) (Fin 2) ℂ` via `isClosed_unitary` (Mathlib),
  using continuity of star and multiplication on the matrix ring (and `T2`-ness, hence `T1`).

A closed subset of a compact set is compact (`IsCompact.of_isClosed_subset`); we then
convert from a compact image of `Subtype.val` back to `IsCompact (univ : Set SU2)` and
finally to `CompactSpace SU2`. -/
instance instCompactSpaceSU2 : CompactSpace SU2 := by
  -- Reduce `CompactSpace SU2` to `IsCompact (univ : Set SU2)`, then to compactness of the
  -- image under the coercion `Subtype.val : SU2 → Matrix (Fin 2) (Fin 2) ℂ`.
  rw [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ, Subtype.range_coe_subtype]
  -- After unfolding `SU2`, the goal is exactly compactness of the underlying carrier of
  -- `Matrix.unitaryGroup (Fin 2) ℂ = unitary (Matrix (Fin 2) (Fin 2) ℂ)` in the ambient
  -- matrix space.
  -- The closed unit disc in `ℂ` is compact (`ℂ` is a proper space).
  have hball : IsCompact (Metric.closedBall (0 : ℂ) 1) :=
    ProperSpace.isCompact_closedBall _ _
  -- Hence the matrix-set of matrices with every entry in the closed unit disc is compact
  -- (finite product of compacts).
  have hmatBall :
      IsCompact ((Metric.closedBall (0 : ℂ) 1).matrix :
        Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
    hball.matrix
  -- The unitary group is closed in the ambient matrix ring.
  have hclosed :
      IsClosed (unitary (Matrix (Fin 2) (Fin 2) ℂ) :
        Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
    isClosed_unitary
  -- Containment: every unitary matrix has all entries with norm ≤ 1, hence in the closed
  -- unit disc.
  have hsubset :
      {U : Matrix (Fin 2) (Fin 2) ℂ | U ∈ Matrix.unitaryGroup (Fin 2) ℂ}
        ⊆ (Metric.closedBall (0 : ℂ) 1).matrix := by
    intro U hU i j
    have : ‖U i j‖ ≤ 1 := entry_norm_bound_of_unitary (𝕜 := ℂ) hU i j
    simpa [Metric.mem_closedBall, dist_zero_right] using this
  -- Conclude compactness of the unitary group via `IsCompact.of_isClosed_subset`.
  exact hmatBall.of_isClosed_subset hclosed hsubset

/-! ## The Haar measure on SU(2) -/

/-- The canonical normalising compact set for SU(2): the whole group (which is compact),
viewed as a `PositiveCompacts`. -/
noncomputable def K₀ : PositiveCompacts SU2 :=
  ⟨⟨Set.univ, isCompact_univ⟩, by
    -- `interior univ = univ`, which is nonempty (SU(2) contains `1`).
    simp⟩

/-- **Haar measure on SU(2).**

Constructed via `MeasureTheory.Measure.haarMeasure` applied to the positive compact
`K₀ = univ`. By `haarMeasure_self`, this measure assigns mass `1` to `univ`, hence is
automatically a probability measure on the compact group SU(2). -/
noncomputable def haarMeasureSU2 : Measure SU2 :=
  MeasureTheory.Measure.haarMeasure K₀

/-- The Haar measure on SU(2) is left-invariant, regular, and gives mass 1 to the group:
this is the `IsHaarMeasure` typeclass (left invariance, finite on compacts, positive on
nonempty opens). -/
instance isHaarMeasureSU2 : IsHaarMeasure haarMeasureSU2 :=
  Measure.isHaarMeasure_haarMeasure K₀

/-- The Haar measure on SU(2) is normalised: `haarMeasureSU2 univ = 1`. -/
theorem haarMeasureSU2_normalized : haarMeasureSU2 (Set.univ : Set SU2) = 1 := by
  -- `K₀ = ⟨univ, _⟩`, so `haarMeasure_self` gives the result directly.
  show haarMeasureSU2 (K₀ : Set SU2) = 1
  exact Measure.haarMeasure_self

/-- The Haar measure on SU(2) is a probability measure. -/
instance isProbabilityMeasureSU2 : IsProbabilityMeasure haarMeasureSU2 :=
  ⟨haarMeasureSU2_normalized⟩

/-- Left invariance of the SU(2) Haar measure (named lemma; the underlying content is in
the `IsHaarMeasure` typeclass via `IsMulLeftInvariant`). -/
theorem haarMeasureSU2_isMulLeftInvariant : IsMulLeftInvariant haarMeasureSU2 :=
  Measure.isMulLeftInvariant_haarMeasure K₀

/-- The Haar measure on SU(2) is a regular measure. -/
instance haarMeasureSU2_regular : haarMeasureSU2.Regular :=
  Measure.regular_haarMeasure

/-- **Right invariance of the SU(2) Haar measure.**

**Mathematical content.** On a compact Hausdorff topological group, every left-invariant
Haar probability measure is automatically right-invariant. The classical argument: for any
`g`, the pushforward `map (· * g) μ` is again a left-invariant Haar measure
(`isHaarMeasure_map_mul_right` from Mathlib), and it is also a probability measure
(`Measure.isProbabilityMeasure_map`, since right multiplication by `g` is measurable and
`μ` is a probability measure). Uniqueness of Haar probability measures on a (locally)
compact group (`isHaarMeasure_eq_of_isProbabilityMeasure` from
`Mathlib.MeasureTheory.Measure.Haar.Unique`) then forces `map (· * g) μ = μ`, which is
exactly the definition of right invariance.

The `LocallyCompactSpace` hypothesis required by the uniqueness lemma is automatic for
SU(2): `CompactSpace ⇒ WeaklyLocallyCompactSpace ⇒ LocallyCompactSpace` (the second
implication uses Hausdorffness, available here as `BorelSpace`/`T2Space` of the unitary
group). All these instances are inferred. -/
instance haarMeasureSU2_isMulRightInvariant : IsMulRightInvariant haarMeasureSU2 where
  map_mul_right_eq_self g := by
    -- The pushforward `map (· * g) haarMeasureSU2` is still a Haar measure (left-invariant
    -- and finite-on-compacts) and still a probability measure. SU(2) is compact, hence
    -- locally compact, so uniqueness of Haar probability measures applies.
    have hμ_meas : Measurable (fun U : SU2 => U * g) :=
      (continuous_mul_const g).measurable
    have : IsProbabilityMeasure (Measure.map (· * g) haarMeasureSU2) :=
      Measure.isProbabilityMeasure_map hμ_meas.aemeasurable
    -- `isHaarMeasure_map_mul_right` provides the `IsHaarMeasure` instance for the pushforward.
    -- `isHaarMeasure_eq_of_isProbabilityMeasure` then identifies it with `haarMeasureSU2`.
    exact isHaarMeasure_eq_of_isProbabilityMeasure
      (Measure.map (· * g) haarMeasureSU2) haarMeasureSU2

end PPT2.Mathlib.HaarSU2
