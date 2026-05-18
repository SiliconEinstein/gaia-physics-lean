# A9 — 2D TQFT ↔ commutative Frobenius algebra

> A symmetric monoidal functor $Z : 2\text{Cob} \to \mathrm{Vect}_K^{\mathrm{fd}}$
> is equivalent data to a commutative Frobenius algebra $A = Z(S^1)$.

Classical correspondence due to Atiyah–Segal (and elaborated in Kock,
*Frobenius Algebras and 2D Topological Quantum Field Theories*, §3.3.2;
Dumitrescu et al. 2015). LKM source claim: `gcn_c8351754bdb44e38`.

## Honest scope (read this before celebrating)

This formalization is **categorically honest**, not categorically naïve. The
target theorem

```lean
theorem two_cob_equiv_commutative_frobenius_exists
    (T : TwoCobUP.WithExtend.{v, u}) :
    (∀ (A : V) [hA : CommFrobeniusObj A],
        ∃ (F : T.carrier ⥤ V) (_hF : F.Braided),
          ∃ (_hCircle : F.obj T.circle = A),
            HEq (CommFrobeniusObj.map F T.circle) hA) ∧
    (∀ (F : T.carrier ⥤ V) [F.Braided],
        Nonempty (T.extend (F.obj T.circle) ≅ F))
```

states a *classifying equivalence of categories* (essential surjectivity on
data + essential uniqueness up to natural iso) — **not** a type-level `Equiv`
between `2Cob ⥤ V` and `CommFrob V`. That naïve form would require
categorical univalence or a free-SMC construction Mathlib doesn't yet have,
and rewriting it as an on-the-nose type-level equivalence makes the
hypothesis structure uninhabitable.

The *hard* mathematical content — constructing a concrete inhabitant of
`TwoCobUP.WithExtend` (i.e. the actual free-SMC construction of 2Cob and a
proof that it satisfies the universal property) — is **not in this proof**.
It is encoded as a `Type`-valued data bundle (`TwoCobUP.WithExtend`) passed
as a hypothesis. The proof is then 11 lines unpacking that structure.

Consequence:

* `#print axioms two_cob_equiv_commutative_frobenius_exists` lists only the
  standard three (`propext`, `Classical.choice`, `Quot.sound`) — the theorem
  is mechanically axiom-free.
* But this is a **conditional theorem**: it says "if you give me a witness
  of `TwoCobUP.WithExtend`, I will hand you back the classifying
  equivalence." It is **not** an unconditional construction of that
  equivalence from Mathlib.

We label this tier *conditional* in the top-level repository index.

## Proof outline

* **`Defs.lean`** — `CommFrobeniusObj` (commutative Frobenius algebra
  object in a braided monoidal category), the on-the-nose pushforward
  along a strong-monoidal functor, and the `Braided` typeclass for
  `2Cob ⥤ V` functors.
* **`TwoCob.lean`** — the universal-property *bundle*: `TwoCobUP` (a
  carrier category with a circle object and the right braided/monoidal
  structure) and `TwoCobUP.WithExtend` (carrier + the `extend` operation
  + its compatibility data).
* **`Theorem.lean`** — assemble essential surjectivity (`extend` hits every
  commutative Frobenius algebra on the circle) and uniqueness up to
  natural iso (`extend_unique`) into the conjunction stated above.

## What's *not* here

* No construction of `TwoCobUP.WithExtend`. Building one is the
  free-symmetric-monoidal-category-on-one-self-dual-object construction,
  a substantial unfinished Mathlib gap (∼1500 LOC, Kock §3.3 +
  combinatorics of decorated cobordisms).
* No on-the-nose type-level `Equiv (2Cob ⥤ V) (CommFrob V)`. That form
  is wrong by univalence and was explicitly rejected in iter 16–18 of
  the discovery loop (see `gaia-discovery` ledger for `a9_2d_tqft_frobenius`).

## Verify

```bash
lake build GaiaPhysicsLean.A92dTqftFrobenius.Theorem
lake env lean GaiaPhysicsLean/A92dTqftFrobenius/CheckAxioms.lean
```

Expected axiom list: `[propext, Classical.choice, Quot.sound]`.
