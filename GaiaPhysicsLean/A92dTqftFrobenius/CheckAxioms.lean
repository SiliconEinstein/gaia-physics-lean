import GaiaPhysicsLean.A92dTqftFrobenius.Theorem

/-! # Axiom audit for A9 (2D TQFT ↔ commutative Frobenius algebra)

Lean's `#print axioms` lists the *transitive* axiom closure of the term.
For a "fully formalized in Mathlib" theorem we expect only the three
standard Lean axioms `propext`, `Classical.choice`, `Quot.sound`.

Note the *categorical-honesty caveat* below: the existence of the
free-symmetric-monoidal-category extension is encoded as **data**
(a field of `TwoCobUP.WithExtend`), so the theorem is conditional
on inhabiting that structure. It is **not** axiom-padded, but the
hard mathematical content of constructing a concrete `WithExtend`
witness lives outside this proof. See `README.md` § "Honest scope".
-/

#print axioms GaiaPhysicsLean.A92dTqftFrobenius.two_cob_equiv_commutative_frobenius_exists
