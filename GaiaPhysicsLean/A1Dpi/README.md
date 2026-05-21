# A1 — Data Processing Inequality for quantum relative entropy (conditional)

> For every CPTP map $\Lambda : B(\mathcal{H}_K) \to B(\mathcal{H}_H)$ and any
> positive-semidefinite $\rho, \sigma \in \mathrm{Matrix}(\mathrm{Fin}\,d_K, \mathrm{Fin}\,d_K, \mathbb{C})$:
> $$ S(\Lambda(\rho) \,\|\, \Lambda(\sigma)) \;\le\; S(\rho \,\|\, \sigma). $$
>
> i.e. the quantum relative entropy is monotone under completely-positive
> trace-preserving maps.

Lindblad 1975 / Uhlmann 1977. The cornerstone "no-information-gain" theorem
of quantum information theory: classical post-processing cannot increase
distinguishability.

LKM source claim: `gcn_6a2c5b36819b448b` (Lindblad 1975 + Jin et al. 2022).

## Honest scope — *conditional* tier

This formalization satisfies the conditional-tier honesty contract:

* `lake build GaiaPhysicsLean.A1Dpi.Theorem` → **rc=0**
* `#print axioms quantum_relative_entropy_dpi` →
  `[propext, Classical.choice, Quot.sound]` (the standard three only)
* **Zero `sorry`, zero `axiom` across all 7 files** in this module
* …but the proof takes a `Prop`-valued **hypothesis bundle**
  `QRE_PartialTrace_Mono` as an explicit argument.

That hypothesis bundle is

```lean
abbrev QRE_PartialTrace_Mono : Prop :=
  ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (ρ σ : Matrix (m × n) (m × n) ℂ), ρ.PosSemidef → σ.PosSemidef →
    quantumRelativeEntropy (Matrix.partialTrace n ρ) (Matrix.partialTrace n σ) ≤
    quantumRelativeEntropy ρ σ
```

i.e. **DPI for the partial-trace channel** — the deep half of Lindblad's
monotonicity theorem. This is *the* operator-monotonicity statement that
Mathlib currently lacks the infrastructure for: it requires (any of) Lieb's
joint convexity (Lieb 1973), Klein's inequality, Petz's variational formula
for relative entropy, or operator-monotone function theory. None of those
are in Mathlib yet, and porting them is estimated at **300–500 LOC of
operator-concavity infrastructure** in `Mathlib.Analysis.Matrix.OperatorConcavity`.

What this file *does* provide (unconditionally):

1. **`KrausDecomposition.lean`** (267 LOC) — Choi-spectral-decomposition gives
   every CPTP map a finite Kraus representation $\Lambda(\rho) = \sum_i K_i \rho K_i^\dagger$
   with $\sum_i K_i^\dagger K_i = 1$. Uses Mathlib's
   `Matrix.PosSemidef.spectralTheorem` and the sibling A2 Choi theorem.
2. **`Stinespring.lean`** (200 LOC) — Stinespring isometric dilation:
   $\Lambda(\rho) = \mathrm{Tr}_E[V \rho V^\dagger]$ for some isometry
   $V : H \to H \otimes E$, built from the Kraus operators.
3. **`Theorem.lean`** (244 LOC) — main DPI proof. The two hard steps it
   reduces the conjecture to are:
   - **Isometric invariance**: $S(V\rho V^\dagger \| V\sigma V^\dagger) = S(\rho \| \sigma)$ — fully proved here via Mathlib's
     `NonUnitalStarAlgHomClass.map_cfcₙ`.
   - **Partial-trace monotonicity** $S(\mathrm{Tr}_E\,\rho \| \mathrm{Tr}_E\,\sigma) \le S(\rho \| \sigma)$ — this is the conditional hypothesis `hPTMono`.

The reduction itself is genuine work (~1100 LOC of formal Lean). The deferred
piece is exactly the "deep operator-monotonicity" half.

## What's *not* here

* No proof of `QRE_PartialTrace_Mono` itself. This is the Lindblad–Uhlmann
  monotonicity theorem, requiring `Lieb concavity` (or `Klein's inequality`)
  + `Petz variational formula`, none of which exist in current Mathlib.
* No use of `extendIsometryToUnitary` or other "Kraus → unitary" lifting.
  The proof uses the *isometric* Stinespring formulation, which is strictly
  weaker than the unitary one but sufficient for DPI.

## Proof outline

Main theorem `quantum_relative_entropy_dpi` follows the textbook
Lindblad–Stinespring reduction:

```
S(Λ(ρ) ‖ Λ(σ))
= S(Tr_E[V ρ V†] ‖ Tr_E[V σ V†])    -- Stinespring (this file, proved)
≤ S(V ρ V† ‖ V σ V†)                  -- DPI for partial trace (hypothesis hPTMono)
= S(ρ ‖ σ)                              -- isometric invariance (proved via cfcₙ)
```

The boundary cases `dK = 0` and `dH = 0` are dispatched separately.

## Verify

```bash
lake build GaiaPhysicsLean.A1Dpi.Theorem
lake env lean GaiaPhysicsLean/A1Dpi/CheckAxioms.lean
```

Expected output:
```
'GaiaPhysicsLean.A1Dpi.quantum_relative_entropy_dpi' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

## Process note (manual 2026-05-21 audit + refactor)

The upstream `a1_dpi` agent claimed `TERMINAL.success.axiomatized.iter20` with
6 axioms. Inspection showed 5/6 were dead scaffolding (declared but not in
the closure of the main theorem) and only 1 — `qre_partial_trace_mono_axiom`
— was live. This manual audit:
1. Deleted the 5 dead axioms and their cascading dead theorems (~250 LOC).
2. Refactored the one live axiom into the `QRE_PartialTrace_Mono`
   hypothesis bundle (mirroring A9's `TwoCobUP.WithExtend` data-bundle pattern).
3. Verified `#print axioms` is now mechanically clean.

The result is a legitimate conditional-tier formalization rather than a
soft-axiomatic claim, matching the honesty contract of `A92dTqftFrobenius`.
