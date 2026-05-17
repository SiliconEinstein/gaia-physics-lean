/- Kochen–Specker theorem (combinatorial, 18-vector set)
   LKM source claim: gcn_0b8cd733edc4459d
   Tier: A

   **Primary target**: `kochen_specker_18vec_no_valuation`

   Cabello-Estebaranz-García-Alcaine (CEGA) 18-vector set in ℝ^4.
   9 bases × 4 vectors = 36 slots; each vector appears in exactly 2 bases.
   Parity argument: sum of basisCounts = 2·(trueCount) is even, but 9·1 = 9 is odd.
-/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring

namespace GaiaPhysicsLean.A7KochenSpecker

def v : Fin 18 → Fin 4 → ℤ := fun i =>
  match i with
  |  ⟨0, _⟩  => ![ 0,  0,  1, -1]
  |  ⟨1, _⟩  => ![ 1, -1,  0,  0]
  |  ⟨2, _⟩  => ![ 1,  1, -1, -1]
  |  ⟨3, _⟩  => ![ 1,  1,  1,  1]
  |  ⟨4, _⟩  => ![ 1, -1,  1, -1]
  |  ⟨5, _⟩  => ![ 1,  1, -1,  1]
  |  ⟨6, _⟩  => ![ 1,  0, -1,  0]
  |  ⟨7, _⟩  => ![ 0,  1,  0, -1]
  |  ⟨8, _⟩  => ![ 1,  0,  1,  0]
  |  ⟨9, _⟩  => ![ 1,  1,  1, -1]
  |  ⟨10, _⟩ => ![-1,  1,  1,  1]
  |  ⟨11, _⟩ => ![ 1, -1,  1,  1]
  |  ⟨12, _⟩ => ![ 0,  0,  1,  1]
  |  ⟨13, _⟩ => ![ 1,  1,  0,  0]
  |  ⟨14, _⟩ => ![ 1,  0,  0,  1]
  |  ⟨15, _⟩ => ![ 0,  1, -1,  0]
  |  ⟨16, _⟩ => ![ 1,  0,  0, -1]
  |  ⟨17, _⟩ => ![ 0,  1,  1,  0]
  |  ⟨n + 18, h⟩ => absurd h (by omega)

def bases : Fin 9 → Fin 4 → Fin 18 := fun i =>
  match i with
  | ⟨0, _⟩ => ![(0 : Fin 18),  1,  2,  3]
  | ⟨1, _⟩ => ![(0 : Fin 18),  4,  5,  6]
  | ⟨2, _⟩ => ![(1 : Fin 18),  7,  8,  9]
  | ⟨3, _⟩ => ![(2 : Fin 18),  7, 10, 11]
  | ⟨4, _⟩ => ![(3 : Fin 18),  8, 12, 13]
  | ⟨5, _⟩ => ![(4 : Fin 18), 10, 14, 15]
  | ⟨6, _⟩ => ![(5 : Fin 18), 12, 14, 16]
  | ⟨7, _⟩ => ![(6 : Fin 18),  9, 11, 17]
  | ⟨8, _⟩ => ![(13 : Fin 18), 15, 16, 17]
  | ⟨n + 9, h⟩ => absurd h (by omega)

abbrev Valuation := Fin 18 → Bool

def basisCount (a : Valuation) (b : Fin 4 → Fin 18) : Nat :=
  (if a (b 0) then 1 else 0) + (if a (b 1) then 1 else 0) +
  (if a (b 2) then 1 else 0) + (if a (b 3) then 1 else 0)

def isKSValuation (a : Valuation) : Bool :=
  (decide (basisCount a (bases 0) = 1)) &&
  (decide (basisCount a (bases 1) = 1)) &&
  (decide (basisCount a (bases 2) = 1)) &&
  (decide (basisCount a (bases 3) = 1)) &&
  (decide (basisCount a (bases 4) = 1)) &&
  (decide (basisCount a (bases 5) = 1)) &&
  (decide (basisCount a (bases 6) = 1)) &&
  (decide (basisCount a (bases 7) = 1)) &&
  (decide (basisCount a (bases 8) = 1))

-- Helper: count how many bases contain a given vector
def vectorAppearanceCount (vec : Fin 18) : Nat :=
  (Finset.univ.filter (fun (b : Fin 9) =>
    (bases b 0 = vec) || (bases b 1 = vec) || (bases b 2 = vec) || (bases b 3 = vec))).card

-- Lemma: each vector appears in exactly 2 bases
theorem vector_appears_twice : ∀ i : Fin 18, vectorAppearanceCount i = 2 := by
  decide

-- Helper: count true assignments
-- Helper: count true assignments
def trueCount (a : Valuation) : Nat :=
  (Finset.univ.filter (fun i => a i = true)).card

-- Helper: indicator function for Bool
def boolToNat (b : Bool) : Nat := if b then 1 else 0

-- Lemma: sum of basisCount over all bases equals 2 * trueCount
-- Proof: Each of the 18 vectors appears in exactly 2 bases, so when we sum
-- the basisCount over all 9 bases, each vector's truth value is counted twice.
theorem sum_basisCount_eq_twice_trueCount (a : Valuation) :
    (Finset.univ.sum (fun b : Fin 9 => basisCount a (bases b))) = 2 * trueCount a := by
  -- Step 1: Convert trueCount to a sum of indicators.
  have hT : trueCount a = ∑ i : Fin 18, (if a i = true then 1 else 0 : ℕ) := by
    unfold trueCount
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hT, Finset.mul_sum]
  -- Step 2: Expand LHS sum over Fin 9 explicitly.
  rw [show (Finset.univ : Finset (Fin 9)) = {0,1,2,3,4,5,6,7,8} by decide]
  rw [show (Finset.univ : Finset (Fin 18)) =
      {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  -- Step 3: Reduce each `bases i j` and `basisCount` to its concrete vector index.
  -- We do this via a helper claim that `basisCount a (bases i)` equals the explicit sum.
  have b0 : basisCount a (bases 0) =
      (if a 0 then 1 else 0) + (if a 1 then 1 else 0) +
      (if a 2 then 1 else 0) + (if a 3 then 1 else 0) := rfl
  have b1 : basisCount a (bases 1) =
      (if a 0 then 1 else 0) + (if a 4 then 1 else 0) +
      (if a 5 then 1 else 0) + (if a 6 then 1 else 0) := rfl
  have b2 : basisCount a (bases 2) =
      (if a 1 then 1 else 0) + (if a 7 then 1 else 0) +
      (if a 8 then 1 else 0) + (if a 9 then 1 else 0) := rfl
  have b3 : basisCount a (bases 3) =
      (if a 2 then 1 else 0) + (if a 7 then 1 else 0) +
      (if a 10 then 1 else 0) + (if a 11 then 1 else 0) := rfl
  have b4 : basisCount a (bases 4) =
      (if a 3 then 1 else 0) + (if a 8 then 1 else 0) +
      (if a 12 then 1 else 0) + (if a 13 then 1 else 0) := rfl
  have b5 : basisCount a (bases 5) =
      (if a 4 then 1 else 0) + (if a 10 then 1 else 0) +
      (if a 14 then 1 else 0) + (if a 15 then 1 else 0) := rfl
  have b6 : basisCount a (bases 6) =
      (if a 5 then 1 else 0) + (if a 12 then 1 else 0) +
      (if a 14 then 1 else 0) + (if a 16 then 1 else 0) := rfl
  have b7 : basisCount a (bases 7) =
      (if a 6 then 1 else 0) + (if a 9 then 1 else 0) +
      (if a 11 then 1 else 0) + (if a 17 then 1 else 0) := rfl
  have b8 : basisCount a (bases 8) =
      (if a 13 then 1 else 0) + (if a 15 then 1 else 0) +
      (if a 16 then 1 else 0) + (if a 17 then 1 else 0) := rfl
  rw [b0, b1, b2, b3, b4, b5, b6, b7, b8]
  -- Step 4: Generalize each indicator and close with ring.
  generalize (if a 0 = true then 1 else 0 : ℕ) = x0
  generalize (if a 1 = true then 1 else 0 : ℕ) = x1
  generalize (if a 2 = true then 1 else 0 : ℕ) = x2
  generalize (if a 3 = true then 1 else 0 : ℕ) = x3
  generalize (if a 4 = true then 1 else 0 : ℕ) = x4
  generalize (if a 5 = true then 1 else 0 : ℕ) = x5
  generalize (if a 6 = true then 1 else 0 : ℕ) = x6
  generalize (if a 7 = true then 1 else 0 : ℕ) = x7
  generalize (if a 8 = true then 1 else 0 : ℕ) = x8
  generalize (if a 9 = true then 1 else 0 : ℕ) = x9
  generalize (if a 10 = true then 1 else 0 : ℕ) = x10
  generalize (if a 11 = true then 1 else 0 : ℕ) = x11
  generalize (if a 12 = true then 1 else 0 : ℕ) = x12
  generalize (if a 13 = true then 1 else 0 : ℕ) = x13
  generalize (if a 14 = true then 1 else 0 : ℕ) = x14
  generalize (if a 15 = true then 1 else 0 : ℕ) = x15
  generalize (if a 16 = true then 1 else 0 : ℕ) = x16
  generalize (if a 17 = true then 1 else 0 : ℕ) = x17
  ring

-- Lemma: if isKSValuation holds, sum equals 9
theorem ks_valuation_implies_sum_nine (a : Valuation) (h : isKSValuation a = true) :
    (Finset.univ.sum (fun b : Fin 9 => basisCount a (bases b))) = 9 := by
  unfold isKSValuation at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have h0 : basisCount a (bases 0) = 1 := h.1.1.1.1.1.1.1.1
  have h1 : basisCount a (bases 1) = 1 := h.1.1.1.1.1.1.1.2
  have h2 : basisCount a (bases 2) = 1 := h.1.1.1.1.1.1.2
  have h3 : basisCount a (bases 3) = 1 := h.1.1.1.1.1.2
  have h4 : basisCount a (bases 4) = 1 := h.1.1.1.1.2
  have h5 : basisCount a (bases 5) = 1 := h.1.1.1.2
  have h6 : basisCount a (bases 6) = 1 := h.1.1.2
  have h7 : basisCount a (bases 7) = 1 := h.1.2
  have h8 : basisCount a (bases 8) = 1 := h.2
  clear h
  rw [show (Finset.univ : Finset (Fin 9)) = {0,1,2,3,4,5,6,7,8} by decide]
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert,
      Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert,
      Finset.sum_singleton]
  · rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
    rfl
  all_goals decide

-- Parity contradiction helper
theorem nine_odd_two_k_even (k : Nat) : 9 ≠ 2 * k := by
  omega

-- Main theorem: structural proof via parity
theorem kochen_specker_18vec_no_valuation_structural :
    ∀ a : Valuation, isKSValuation a = false := by
  intro a
  by_contra h
  simp at h
  have sum_eq_nine := ks_valuation_implies_sum_nine a h
  have sum_eq_twice := sum_basisCount_eq_twice_trueCount a
  rw [sum_eq_twice] at sum_eq_nine
  exact nine_odd_two_k_even (trueCount a) sum_eq_nine.symm

theorem kochen_specker_18vec_no_valuation :
    ∀ a : Valuation, isKSValuation a = false :=
  kochen_specker_18vec_no_valuation_structural

end GaiaPhysicsLean.A7KochenSpecker
