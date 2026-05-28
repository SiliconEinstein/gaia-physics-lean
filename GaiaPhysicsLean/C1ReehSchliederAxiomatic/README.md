# C1 — Reeh–Schlieder theorem (axiomatic statement)

> In the Haag–Kastler framework, an irreducible vacuum representation of a
> local net of operator algebras has a vacuum vector that is simultaneously
> **cyclic** and **separating** for every local algebra whose causal complement
> is non-empty.

Reeh–Schlieder 1961; canonical reference Haag *Local Quantum Physics* §II.5.3.
LKM source claim: `gcn_687a62424c964753`.

## Honest scope — this is a *C-tier* deliverable

C-tier in `gaia-discovery` ≠ A-tier. The bar is intentionally different:

> **C-tier**: state the theorem precisely against axiomatized infrastructure
> + document the proof gap (paper ref + Mathlib PR plan + LOC estimate).
> The `sorry` on the main path is *the* deliverable, not a smell.

The Reeh–Schlieder proof requires **Tomita–Takesaki modular theory** (modular
operator Δ, modular conjugation J, KMS condition for the vacuum state on a
local algebra). Mathlib currently has **no** modular theory for von Neumann
algebras in standard form — closing this gap is estimated at 2000+ LOC of
operator-algebra infrastructure (modular flow, analytic continuation of
correlation functions, weak additivity → cyclicity argument).

So this file delivers exactly what a C-tier formalization promises: a precise
formal statement against an axiomatized substrate, with the proof labeled
`sorry` and tagged

```
gap_kind: open_modular_theory
mathlib_pr_plan: Tomita–Takesaki modular operator Δ + modular conjugation J
                 for von Neumann algebras in standard form
paper_ref: Reeh–Schlieder (1961) Nuovo Cimento 22:1051
           Haag, "Local Quantum Physics" (1996) §II.5.3
loc_estimate: 2000+
```

The single `sorry` in `Theorem.lean` is **the** documented one. There are no
hidden `sorry`s or undocumented axioms elsewhere in the module.

## What this file actually formalizes

* **`Defs.lean`** — the Haag–Kastler axiomatic substrate:
  * Opaque type: `MinkowskiSpace`.
  * Causal structure: `causalComplement : Set MinkowskiSpace → Set MinkowskiSpace`,
    `HasNonEmptyCausalComplement`.
  * Hilbert-space substrate: `H : Type` with Mathlib's
    `[NormedAddCommGroup H] [InnerProductSpace ℂ H]`.
  * Bounded operators: `BoundedOp H := H →L[ℂ] H` using Mathlib's
    `ContinuousLinearMap`.
  * `LocalNet` structure bundling isotony / locality / weak_additivity.
  * `VacuumRep` bundling a normalized vacuum vector and an irreducibility
    condition on closed invariant subspaces.
  * Predicates `IsCyclicVector`, `IsSeparatingVector` defined using Mathlib's
    `Dense` and bounded-operator application.

* **`Theorem.lean`** —

```lean
theorem reeh_schlieder_cyclic_and_separating
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (rep : VacuumRep H)
    (O : Set MinkowskiSpace)
    (hO : HasNonEmptyCausalComplement O) :
    IsCyclicVector H rep.vacuum (rep.net.alg O) ∧
    IsSeparatingVector H rep.vacuum (rep.net.alg O) := by
  sorry  -- gap_kind: open_modular_theory (see docstring)
```

## What this file is *not*

* **Not a proof.** Reeh–Schlieder requires modular theory; this is C-tier.
* **Not a Lorentzian-geometry formalization.** `MinkowskiSpace` and
  `causalComplement` remain opaque substrate axioms until Mathlib has the
  needed Minkowski causal-geometry layer.

## Verify

```bash
lake build GaiaPhysicsLean.C1ReehSchliederAxiomatic.Theorem
# ⚠ [N/N] Built GaiaPhysicsLean.C1ReehSchliederAxiomatic.Theorem (2.1s)
# warning: GaiaPhysicsLean/C1ReehSchliederAxiomatic/Theorem.lean:44:8: declaration uses `sorry`
# Build completed successfully.
```

The `sorry` warning is the documented one.

## Process note (iter4, 2026-05-27)

The C1 swarm reduced the substrate from 11 axioms to 2 by replacing the opaque
`HilbertSpace`, `BoundedOp`, operator operations, and cyclic/separating
predicates with Mathlib's `InnerProductSpace`, `ContinuousLinearMap`, normed
operator algebra operations, `Dense`, and explicit separating-vector
definitions. The only remaining substrate axioms are `MinkowskiSpace` and
`causalComplement`; the single theorem `sorry` remains the documented
Tomita–Takesaki modular-theory gap.
