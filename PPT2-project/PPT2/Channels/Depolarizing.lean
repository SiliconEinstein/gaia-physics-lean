/-
PPT2.Channels.Depolarizing — definitions and entry-formula lemmas for the
depolarizing channel.  Extracted from Examples/Depolarizing so that
Cases/Dim2 can import these without creating an import cycle.
-/
import PPT2.Basic
import PPT2.Choi
import PPT2.EntanglementBreaking
import PPT2.PartialTranspose
import PPT2.Separable
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

namespace PPT2

open Matrix BigOperators
open scoped ComplexOrder Kronecker

/-- Φ is a d-dim depolarizing channel with mixing parameter p.
    Defined as: Φ_p(ρ) = p·ρ + ((1-p)/d) · Tr(ρ)·I. -/
def IsDepolarizing {d : Nat} (p : ℝ) (Φ : QChan d d) : Prop :=
  ∀ ρ : Matrix (Fin d) (Fin d) ℂ,
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) ρ =
      (p : ℂ) • ρ + (((1 : ℝ) - p) / (d : ℝ) : ℂ) • ((ρ.trace : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ))

/-- Trace of the matrix unit |a⟩⟨c|: Tr(|a⟩⟨c|) = δ_{a,c}. -/
lemma trace_single {d : ℕ} (a c : Fin d) :
    (Matrix.single a c (1 : ℂ)).trace = if a = c then (1 : ℂ) else 0 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.single_apply]
  by_cases h : a = c
  · subst h; simp
  · simp [h, Ne.symm h]

/-- Entry formula for the Choi matrix of a depolarizing channel. -/
lemma choi_depolarizing_entry {d : ℕ} (p : ℝ) (Φ : QChan d d) (h : IsDepolarizing p Φ)
    (a b c d_idx : Fin d) : (Choi Φ) (a, b) (c, d_idx) =
    (p : ℂ) * (if a = b ∧ c = d_idx then (1 : ℂ) else 0) +
    (((1 : ℝ) - p) / (d : ℝ) : ℂ) * (if a = c then (1 : ℂ) else 0) * (if b = d_idx then (1 : ℂ) else 0) := by
  rw [Choi_apply, h (Matrix.single a c (1 : ℂ))]
  have htrace : (Matrix.single a c (1 : ℂ)).trace = if a = c then (1 : ℂ) else 0 := trace_single a c
  rw [htrace]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, Matrix.one_apply, smul_eq_mul]
  ring

/-- Partial-transpose entry formula for the depolarizing Choi. -/
lemma choi_depolarizing_pt_entry {d : ℕ} (p : ℝ) (Φ : QChan d d) (h : IsDepolarizing p Φ)
    (a b c d_idx : Fin d) : (partialTranspose (Choi Φ)) (a, b) (c, d_idx) =
    (p : ℂ) * (if a = d_idx ∧ b = c then (1 : ℂ) else 0) +
    (((1 : ℝ) - p) / (d : ℝ) : ℂ) * (if a = c then (1 : ℂ) else 0) * (if b = d_idx then (1 : ℂ) else 0) := by
  unfold partialTranspose
  simp
  have h_entry := choi_depolarizing_entry p Φ h a d_idx c b
  simpa [eq_comm] using h_entry

/-- At p = 0, `Φ(ρ) = (1/d : ℂ) • (Tr ρ • I)`. -/
lemma depolarizing_p0_apply {d : Nat} (Φ : QChan d d) (h : IsDepolarizing 0 Φ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (Φ ρ) = (((1 : ℝ) / (d : ℝ) : ℂ)) • ((ρ.trace : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  have hh := h ρ
  rw [hh]
  simp

/-- Entry-wise identity: the partial transpose of a Kronecker product equals
    the Kronecker product with the right factor transposed. -/
lemma partialTranspose_kronecker {d : Nat}
    (A B : Matrix (Fin d) (Fin d) ℂ) :
    partialTranspose (A ⊗ₖ B) = A ⊗ₖ Bᵀ := by
  funext ⟨a, b⟩ ⟨c, e⟩
  simp [partialTranspose, Matrix.transpose_apply]

/-- Separable cone closed under partial transpose. -/
theorem Separable.partialTranspose {d : Nat}
    {X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hX : Separable X) : Separable (partialTranspose X) := by
  obtain ⟨k, p, A, B, hp, hA, hB, hXeq⟩ := hX
  refine ⟨k, p, A, fun i => (B i)ᵀ, hp, hA,
    fun i => (hB i).transpose, ?_⟩
  funext x y
  obtain ⟨a, b⟩ := x
  obtain ⟨c, e⟩ := y
  show X ⟨a, e⟩ ⟨c, b⟩ = _
  rw [hXeq]
  simp [Matrix.sum_apply, Matrix.transpose_apply]

/-- A PSD ⊗ PSD product is separable (single-summand witness). -/
theorem psd_kron_separable {d : Nat}
    (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Separable (Matrix.kronecker A B) := by
  refine ⟨1, fun _ => 1, fun _ => A, fun _ => B, ?_, ?_, ?_, ?_⟩
  · intro _; exact zero_le_one
  · intro _; exact hA
  · intro _; exact hB
  · simp

end PPT2
