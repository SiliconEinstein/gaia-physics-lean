/- Basic definitions for FKG inequality
   - IsingMeasure: Gibbs measure on {±1}^Λ
   - Increasing: monotone functions on the componentwise partial order
-/

import Mathlib

namespace GaiaPhysicsLean.B6FkgInequality

/-- Configuration space: `{±1}^Λ`, represented as `Λ → Fin 2` where 0 ↔ -1, 1 ↔ +1. -/
def ConfigSpace (Λ : Type*) := Λ → Fin 2

/-- Componentwise partial order on configurations. -/
instance {Λ : Type*} : PartialOrder (ConfigSpace Λ) :=
  Pi.partialOrder

/-- Componentwise lattice on configurations, since `Fin 2` is a linear order. -/
instance {Λ : Type*} : Lattice (ConfigSpace Λ) :=
  Pi.instLattice

/-- `ConfigSpace Λ` is a finite type when `Λ` is. -/
instance {Λ : Type*} [Fintype Λ] [DecidableEq Λ] : Fintype (ConfigSpace Λ) :=
  inferInstanceAs (Fintype (Λ → Fin 2))

/-- `ConfigSpace Λ` has decidable equality when `Λ` does. -/
instance {Λ : Type*} [Fintype Λ] [DecidableEq Λ] : DecidableEq (ConfigSpace Λ) :=
  inferInstanceAs (DecidableEq (Λ → Fin 2))

/-- A function `f : ConfigSpace Λ → ℝ` is increasing if it preserves the partial order. -/
def Increasing {Λ : Type*} (f : ConfigSpace Λ → ℝ) : Prop :=
  ∀ σ τ : ConfigSpace Λ, σ ≤ τ → f σ ≤ f τ

/-- Spin values represented as integers: 0 ↦ -1, 1 ↦ +1. -/
def spinValue : Fin 2 → ℤ
  | 0 => -1
  | 1 => 1

/-- Ising Hamiltonian with coupling matrix `J`: `H(σ) = -∑ᵢⱼ Jᵢⱼ σᵢ σⱼ`. -/
def isingHamiltonian {Λ : Type*} [Fintype Λ] (J : Λ → Λ → ℝ) (σ : ConfigSpace Λ) : ℝ :=
  -∑ i : Λ, ∑ j : Λ, J i j * (spinValue (σ i) : ℝ) * (spinValue (σ j) : ℝ)

/-- Ferromagnetic condition: all couplings are non-negative. -/
def Ferromagnetic {Λ : Type*} (J : Λ → Λ → ℝ) : Prop :=
  ∀ i j : Λ, 0 ≤ J i j

/-- Ising Gibbs measure: a PMF proportional to `exp(-β H(σ))`.

This is a predicate on probability measures; the normalizing partition function is
recorded existentially. -/
def IsingMeasure {Λ : Type*} [Fintype Λ] (β : ℝ) (J : Λ → Λ → ℝ)
    (μ : PMF (ConfigSpace Λ)) : Prop :=
  Ferromagnetic J ∧
  ∃ Z : ℝ, Z > 0 ∧
    ∀ σ : ConfigSpace Λ,
      (μ σ).toReal = (Real.exp (-β * isingHamiltonian J σ)) / Z

/-- Pairwise supermodularity on `Fin 2` spins, proved by exhaustive case analysis. -/
lemma spinValue_pairwise_supermodular (a b c d : Fin 2) :
    spinValue a * spinValue b + spinValue c * spinValue d
      ≤ spinValue (a ⊔ c) * spinValue (b ⊔ d)
          + spinValue (a ⊓ c) * spinValue (b ⊓ d) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

/-- Real-valued version of pairwise supermodularity after casting to `ℝ`. -/
lemma spinValue_pairwise_supermodular_real (a b c d : Fin 2) :
    (spinValue a : ℝ) * (spinValue b : ℝ) + (spinValue c : ℝ) * (spinValue d : ℝ)
      ≤ (spinValue (a ⊔ c) : ℝ) * (spinValue (b ⊔ d) : ℝ)
          + (spinValue (a ⊓ c) : ℝ) * (spinValue (b ⊓ d) : ℝ) := by
  have h := spinValue_pairwise_supermodular a b c d
  exact_mod_cast h

/-- The Ising Hamiltonian is submodular under ferromagnetic couplings:
`H(σ ⊔ τ) + H(σ ⊓ τ) ≤ H(σ) + H(τ)`.

This is the algebraic ingredient behind the Holley lattice condition. -/
theorem isingHamiltonian_submodular {Λ : Type*} [Fintype Λ]
    {J : Λ → Λ → ℝ} (hJ : Ferromagnetic J) (σ τ : ConfigSpace Λ) :
    isingHamiltonian J (σ ⊔ τ) + isingHamiltonian J (σ ⊓ τ)
      ≤ isingHamiltonian J σ + isingHamiltonian J τ := by
  simp only [isingHamiltonian]
  have hpair : ∀ i j : Λ,
      J i j * (spinValue (σ i) : ℝ) * (spinValue (σ j) : ℝ)
        + J i j * (spinValue (τ i) : ℝ) * (spinValue (τ j) : ℝ)
      ≤ J i j * (spinValue ((σ ⊔ τ) i) : ℝ) * (spinValue ((σ ⊔ τ) j) : ℝ)
          + J i j * (spinValue ((σ ⊓ τ) i) : ℝ) * (spinValue ((σ ⊓ τ) j) : ℝ) := by
    intro i j
    have hsup : (σ ⊔ τ) i = σ i ⊔ τ i := rfl
    have hsup' : (σ ⊔ τ) j = σ j ⊔ τ j := rfl
    have hinf : (σ ⊓ τ) i = σ i ⊓ τ i := rfl
    have hinf' : (σ ⊓ τ) j = σ j ⊓ τ j := rfl
    rw [hsup, hsup', hinf, hinf']
    have hsm := spinValue_pairwise_supermodular_real (σ i) (σ j) (τ i) (τ j)
    have hJij : 0 ≤ J i j := hJ i j
    nlinarith [hsm, hJij]
  have hsum : ∑ i : Λ, ∑ j : Λ,
        (J i j * (spinValue (σ i) : ℝ) * (spinValue (σ j) : ℝ)
          + J i j * (spinValue (τ i) : ℝ) * (spinValue (τ j) : ℝ))
      ≤ ∑ i : Λ, ∑ j : Λ,
        (J i j * (spinValue ((σ ⊔ τ) i) : ℝ) * (spinValue ((σ ⊔ τ) j) : ℝ)
          + J i j * (spinValue ((σ ⊓ τ) i) : ℝ) * (spinValue ((σ ⊓ τ) j) : ℝ)) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact hpair i j
  have e1 : ∑ i : Λ, ∑ j : Λ,
        (J i j * (spinValue (σ i) : ℝ) * (spinValue (σ j) : ℝ)
          + J i j * (spinValue (τ i) : ℝ) * (spinValue (τ j) : ℝ))
      = (∑ i : Λ, ∑ j : Λ, J i j * (spinValue (σ i) : ℝ) * (spinValue (σ j) : ℝ))
        + (∑ i : Λ, ∑ j : Λ, J i j * (spinValue (τ i) : ℝ) * (spinValue (τ j) : ℝ)) := by
    simp [Finset.sum_add_distrib]
  have e2 : ∑ i : Λ, ∑ j : Λ,
        (J i j * (spinValue ((σ ⊔ τ) i) : ℝ) * (spinValue ((σ ⊔ τ) j) : ℝ)
          + J i j * (spinValue ((σ ⊓ τ) i) : ℝ) * (spinValue ((σ ⊓ τ) j) : ℝ))
      = (∑ i : Λ, ∑ j : Λ,
          J i j * (spinValue ((σ ⊔ τ) i) : ℝ) * (spinValue ((σ ⊔ τ) j) : ℝ))
        + (∑ i : Λ, ∑ j : Λ,
          J i j * (spinValue ((σ ⊓ τ) i) : ℝ) * (spinValue ((σ ⊓ τ) j) : ℝ)) := by
    simp [Finset.sum_add_distrib]
  rw [e1] at hsum
  rw [e2] at hsum
  linarith [hsum]

end GaiaPhysicsLean.B6FkgInequality
