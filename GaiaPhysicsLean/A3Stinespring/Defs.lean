/-
GaiaPhysicsLean.A3Stinespring.Defs

Core definitions for the (finite-dim) Stinespring dilation theorem.

Re-uses A2's `QChan`, `IsCP`, `Choi`, `Choi_apply`.

Adds:
  * `IsTP Φ`         — trace preservation `∀ X, (Φ X).trace = X.trace`.
  * `KrausForm`      — Kraus operators `K : Fin r → Matrix dH dK ℂ`
                       with TP identity `∑ k, (K k)ᴴ * K k = 1` and
                       channel identity `∀ X, Φ X = ∑ k, K k * X * (K k)ᴴ`.
  * `StinespringData`— ambient `Fin (dK * r)` space, canonical state index,
                       and a unitary `U` on `H_Q ⊗ H_E`.
  * `partialTraceR`  — partial trace over the right tensor factor.
  * `partialTraceR_apply` — pointwise unfolding lemma.

Used by sibling files in this directory (`Theorem.lean`, etc.).
-/
import GaiaPhysicsLean.A2ChoiTheorem.Defs

namespace GaiaPhysicsLean.A3Stinespring

open Matrix
open GaiaPhysicsLean.A2ChoiTheorem

/-- Trace preservation predicate for a (bare) finite-dim quantum channel:
    `∀ X, tr (Φ X) = tr X`. Combined with `IsCP` this gives CPTP. -/
def IsTP {dK dH : ℕ} (Φ : QChan dK dH) : Prop :=
  ∀ X : Matrix (Fin dK) (Fin dK) ℂ, (Φ X).trace = X.trace

/-- A Kraus form witness for a quantum channel `Φ : QChan dK dH` of rank `r`:
    a family `K : Fin r → Matrix dH dK ℂ` of Kraus operators satisfying
      * `∑ k, (K k)ᴴ * K k = 1` (trace-preservation), and
      * `Φ X = ∑ k, K k * X * (K k)ᴴ` for every input `X`.

    Note: `r` is typically the Choi rank obtained from the spectral
    decomposition of the Choi matrix (cf. A2's `Reverse.lean`). -/
structure KrausForm {dK dH : ℕ} (Φ : QChan dK dH) (r : ℕ) where
  /-- The Kraus operators. -/
  K : Fin r → Matrix (Fin dH) (Fin dK) ℂ
  /-- Trace-preservation: the Kraus operators form an isometric column block. -/
  tp : ∑ k, (K k).conjTranspose * (K k) = (1 : Matrix (Fin dK) (Fin dK) ℂ)
  /-- Channel identity: `Φ X = ∑ k, K k * X * (K k)ᴴ`. -/
  channel : ∀ X : Matrix (Fin dK) (Fin dK) ℂ,
    Φ X = ∑ k, (K k) * X * (K k).conjTranspose

/-- Stinespring dilation data of dimension `dK * r` for a channel acting on
    `Matrix (Fin dK) (Fin dK) ℂ` with environment dimension `r`.

    Records:
      * a unitary `U` on the composite space `Fin dK × Fin r` (encoded as
        `Fin (dK * r)` via the obvious product equivalence — but we phrase
        the matrix on the product type directly to avoid index shuffles);
      * a unitarity proof `Uᴴ * U = 1`;
      * the canonical environment state index `e0 : Fin r` (taken to be
        `⟨0, _⟩` whenever `r ≠ 0`).

    The pure-state |0⟩_E is recovered as the standard basis vector
    `e_{e0} : Fin r → ℂ`. The dilation theorem says: there exists such
    `StinespringData` with `Φ X = partialTraceR (U (X ⊗ |0⟩⟨0|) Uᴴ)`. -/
structure StinespringData (dK r : ℕ) where
  /-- Canonical environment state index (the |0⟩_E choice). -/
  e0 : Fin r
  /-- The dilation unitary `U` on `H_Q ⊗ H_E`. -/
  U : Matrix (Fin dK × Fin r) (Fin dK × Fin r) ℂ
  /-- Unitarity: `Uᴴ * U = 1`. -/
  unitary : U.conjTranspose * U = (1 : Matrix (Fin dK × Fin r) (Fin dK × Fin r) ℂ)

/-- Partial trace over the right (environment) factor:
    `(partialTraceR M) i j = ∑_e M (i, e) (j, e)`.

    This is the finite-dim specialisation of `Tr_E` on a bipartite matrix
    indexed by `Fin dQ × Fin dE`. -/
noncomputable def partialTraceR {dQ dE : ℕ}
    (M : Matrix (Fin dQ × Fin dE) (Fin dQ × Fin dE) ℂ) :
    Matrix (Fin dQ) (Fin dQ) ℂ :=
  fun i j => ∑ e : Fin dE, M (i, e) (j, e)

/-- Pointwise unfolding of `partialTraceR`. -/
@[simp] lemma partialTraceR_apply {dQ dE : ℕ}
    (M : Matrix (Fin dQ × Fin dE) (Fin dQ × Fin dE) ℂ) (i j : Fin dQ) :
    partialTraceR M i j = ∑ e : Fin dE, M (i, e) (j, e) := rfl

end GaiaPhysicsLean.A3Stinespring
