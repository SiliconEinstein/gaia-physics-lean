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
  * Opaque types: `MinkowskiSpace`, `HilbertSpace`, `BoundedOp`.
  * Causal structure: `causalComplement : Set MinkowskiSpace → Set MinkowskiSpace`,
    `HasNonEmptyCausalComplement`.
  * Operator algebra ops: `opNorm`, `opSub`, `opMul`, `opApply`, `opZero`.
  * `LocalNet` structure bundling isotony / locality / weak_additivity.
  * `VacuumRep` bundling vacuum vector + irreducibility flag.
  * Predicates `IsCyclicVector`, `IsSeparatingVector` declared as axiomatized
    propositions.

* **`Theorem.lean`** —

```lean
theorem reeh_schlieder_cyclic_and_separating
    (rep : VacuumRep)
    (O : Set MinkowskiSpace)
    (hO : HasNonEmptyCausalComplement O) :
    IsCyclicVector rep.vacuum (rep.net.alg O) ∧
    IsSeparatingVector rep.vacuum (rep.net.alg O) := by
  sorry  -- gap_kind: open_modular_theory (see docstring)
```

## What this file is *not*

* **Not a proof.** Reeh–Schlieder requires modular theory; this is C-tier.
* **Not Hilbert-space-concrete.** `HilbertSpace` and `BoundedOp` are opaque
  axiomatized types — once Mathlib's modular-theory infrastructure exists,
  the natural follow-up project will be to instantiate these against
  Mathlib's `InnerProductSpace ℂ H` / `ContinuousLinearMap` substrate.

## Verify

```bash
lake build GaiaPhysicsLean.C1ReehSchliederAxiomatic.Theorem
# ⚠ [N/N] Built GaiaPhysicsLean.C1ReehSchliederAxiomatic.Theorem (2.1s)
# warning: GaiaPhysicsLean/C1ReehSchliederAxiomatic/Theorem.lean:44:8: declaration uses `sorry`
# Build completed successfully.
```

The `sorry` warning is the documented one.

## Process note (manual repair, 2026-05-19)

The agent's iter-4 run mis-diagnosed the module as "system overload preventing
lake build verification" — a false positive caused by `Defs.lean` shipping
**no imports** while using `Set MinkowskiSpace`, which made the elaborator
spin until lake's timeout fired (rc=124). The watchdog's `TERMINAL.success` →
`fake_success` downgrade caught the symptom. A 2-line manual fix —
`import Mathlib.Data.Set.Basic` in `Defs.lean` plus stripping a bogus
`{H : Type*} [NormedAddCommGroup H] ...` binder on the theorem signature
(`VacuumRep` is unparameterized in the agent's own `Defs.lean`) — made the
module compile cleanly with exactly the single documented `sorry`. The
upstream `lean_swarm` project ledger has been updated accordingly.
