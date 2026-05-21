/-
GaiaPhysicsLean.A1Dpi.IsometryExtension

Helper lemmas for extending an isometry to a unitary matrix.

Given V : Matrix (Fin n) (Fin k) ℂ with V† V = I_k (i.e., V has k orthonormal columns),
we want to extend V to a unitary matrix U : Matrix (Fin n) (Fin n) ℂ.

Strategy: Use the fact that V's columns form an orthonormal set in ℂ^n.
We need to find (n - k) additional orthonormal vectors orthogonal to V's columns.

gap_kind: mathlib_missing
paper_ref: Horn & Johnson, Matrix Analysis (2nd ed.), Theorem 2.3.2
loc_estimate: 150
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic

namespace GaiaPhysicsLean.A1Dpi

open Matrix Complex

variable {n k : ℕ}

/-- A matrix V with orthonormal columns satisfies V† V = I. -/
def HasOrthonormalColumns (V : Matrix (Fin n) (Fin k) ℂ) : Prop :=
  V.conjTranspose * V = 1

/-- The columns of V as vectors in ℂ^n. -/
def columnVec (V : Matrix (Fin n) (Fin k) ℂ) (j : Fin k) : Fin n → ℂ :=
  fun i => V i j

/-- Inner product on ℂ^n (standard Hermitian inner product). -/
noncomputable def innerProd (u v : Fin n → ℂ) : ℂ :=
  ∑ i : Fin n, starRingEnd ℂ (u i) * v i

end GaiaPhysicsLean.A1Dpi
