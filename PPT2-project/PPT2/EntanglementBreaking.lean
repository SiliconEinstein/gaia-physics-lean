/-
PPT2.EntanglementBreaking — entanglement-breaking predicate via Choi+Separable
plus the EB ideal closure theorems (composition with CP maps stays in EB).
-/
import PPT2.Basic
import PPT2.Choi
import PPT2.Separable
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

namespace PPT2

open Matrix BigOperators
open scoped ComplexOrder

private lemma trace_mul_posSemidef_nonneg {d : ℕ}
    {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (0 : ℂ) ≤ (A * B).trace := by
  classical
  rw [hA.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
  set U := (hA.1.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  rw [show (star U : Matrix (Fin d) (Fin d) ℂ) = Uᴴ from Matrix.star_eq_conjTranspose _]
  rw [show U * diagonal (RCLike.ofReal ∘ hA.1.eigenvalues) * Uᴴ * B
        = (U * diagonal (RCLike.ofReal ∘ hA.1.eigenvalues)) * (Uᴴ * B) by
      simp [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm]
  rw [show Uᴴ * B * (U * diagonal (RCLike.ofReal ∘ hA.1.eigenvalues))
        = (Uᴴ * B * U) * diagonal (RCLike.ofReal ∘ hA.1.eigenvalues) by
      simp [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm]
  have key : (diagonal (RCLike.ofReal ∘ hA.1.eigenvalues) * (Uᴴ * B * U)).trace =
      ∑ i, (RCLike.ofReal (hA.1.eigenvalues i) : ℂ) * (Uᴴ * B * U) i i := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, diagonal_apply, Finset.mem_univ]
  rw [key]
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · exact RCLike.ofReal_nonneg.mpr (hA.eigenvalues_nonneg i)
  · exact (hB.conjTranspose_mul_mul_same U).diag_nonneg

/-- A quantum channel is **entanglement-breaking** iff its Choi matrix is
    separable. -/
def IsEB {d : Nat} (Φ : QChan d d) : Prop :=
  Separable (Choi Φ)

/-- Choi composition formula (left): if Choi(Ψ) is separable and Φ is
    PSD-preserving, then Choi(Φ ∘ Ψ) is separable. -/
theorem choi_comp_left_formula {d : Nat}
    (Φ Ψ : QChan d d)
    (hΨ : Separable (Choi Ψ))
    (hPSD : ∀ M : Matrix (Fin d) (Fin d) ℂ, M.PosSemidef → (Φ M).PosSemidef) :
    Separable (Choi (Φ.comp Ψ)) := by
  obtain ⟨k, p, A, B, hp, hA, hB, heq⟩ := hΨ
  refine ⟨k, p, A, fun l => Φ (B l), hp, hA, fun l => hPSD _ (hB l), ?_⟩
  ext ⟨a, b⟩ ⟨c, e⟩
  rw [choi_comp_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  have hPsiMat : Ψ (Matrix.single a c (1 : ℂ)) = ∑ l : Fin k, (p l * A l a c : ℂ) • B l := by
    ext b' e'
    have hentry := congr_fun (congr_fun heq (a, b')) (c, e')
    rw [Choi_apply] at hentry
    simp only [Matrix.sum_apply, Matrix.smul_apply] at hentry
    simp only [Matrix.sum_apply, Matrix.smul_apply]
    convert hentry using 1
    refine Finset.sum_congr rfl (fun l _ => ?_)
    unfold Matrix.kronecker Matrix.kroneckerMap; simp; ring
  rw [hPsiMat, map_sum]
  simp only [LinearMap.map_smul, Matrix.sum_apply, Matrix.smul_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  unfold Matrix.kronecker Matrix.kroneckerMap; simp; ring

/-- Choi composition formula (right): if Choi(Φ) is separable and Ψ is
    PSD-preserving and star-preserving, then Choi(Φ ∘ Ψ) is separable.

    Construction (mirror of `choi_comp_left_formula`):
    Write `Choi Φ = ∑ l, p l • (A l ⊗ B l)`.  For each `l`, define
      `C l a c := ∑ x y, A l x y * (Ψ E_{ac}) x y`.
    Then `C l` is PSD via the bilinear-form identity
      `⟨u, (C l) u⟩ = trace (A l * (Ψ N)ᵀ)`,
    where `N := vecMulVec (star u) u` is PSD (rank-1) and `Ψ N` is PSD by
    `hPSD`; transposing preserves PSD.  The Hermitian property of `C l`
    follows from `(A l)` Hermitian + `hStar` (using `single c a 1 = (single a c 1)ᴴ`).
    The entrywise equality `Choi(Φ ∘ Ψ) = ∑ l, p l • (C l ⊗ B l)` follows
    by linearity of `Φ` and the Choi-formula for `Φ`. -/
theorem choi_comp_right_formula {d : Nat}
    (Φ Ψ : QChan d d)
    (hΦ : Separable (Choi Φ))
    (hPSD : ∀ M : Matrix (Fin d) (Fin d) ℂ, M.PosSemidef → (Ψ M).PosSemidef)
    (hStar : ∀ M : Matrix (Fin d) (Fin d) ℂ, Ψ Mᴴ = (Ψ M)ᴴ) :
    Separable (Choi (Φ.comp Ψ)) := by
  classical
  obtain ⟨k, p, A, B, hp, hA, hB, heq⟩ := hΦ
  let C : Fin k → Matrix (Fin d) (Fin d) ℂ :=
    fun l => Matrix.of fun a c =>
      ∑ x : Fin d, ∑ y : Fin d, A l x y * (Ψ (Matrix.single a c (1 : ℂ))) x y
  have hSingleConj : ∀ a c : Fin d,
      (Matrix.single a c (1 : ℂ))ᴴ = Matrix.single c a (1 : ℂ) := by
    intro a c
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.single_apply, and_comm]
  refine ⟨k, p, C, B, hp, ?_, hB, ?_⟩
  · -- C l is PSD
    intro l
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?hHerm ?hDot
    case hHerm =>
      refine Matrix.IsHermitian.ext (fun a c => ?_)
      show star (∑ x : Fin d, ∑ y : Fin d, A l x y * (Ψ (Matrix.single c a (1 : ℂ))) x y)
            = ∑ x : Fin d, ∑ y : Fin d, A l x y * (Ψ (Matrix.single a c (1 : ℂ))) x y
      have hAH : ∀ x y, star (A l x y) = A l y x := fun x y => by
        have := congrArg (fun M => M y x) (hA l).1
        simpa [Matrix.conjTranspose_apply] using this
      have hPsiSwap : ∀ x y : Fin d,
          star ((Ψ (Matrix.single c a (1 : ℂ))) x y) =
          (Ψ (Matrix.single a c (1 : ℂ))) y x := by
        intro x y
        have hh := hStar (Matrix.single a c (1 : ℂ))
        rw [hSingleConj a c] at hh
        have heq2 : (Ψ (Matrix.single c a (1 : ℂ))) x y =
                    ((Ψ (Matrix.single a c (1 : ℂ)))ᴴ) x y := by rw [hh]
        rw [heq2, Matrix.conjTranspose_apply, star_star]
      rw [star_sum]
      have step : (∑ x : Fin d, star (∑ y : Fin d,
            A l x y * (Ψ (Matrix.single c a (1 : ℂ))) x y))
          = ∑ x : Fin d, ∑ y : Fin d,
              A l y x * (Ψ (Matrix.single a c (1 : ℂ))) y x := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [star_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [star_mul, hAH x y, hPsiSwap x y, mul_comm]
      rw [step, Finset.sum_comm]
    case hDot =>
      intro u
      have hVecDecomp : Matrix.vecMulVec (star u) u =
          ∑ a : Fin d, ∑ c : Fin d, (star (u a) * u c) • Matrix.single a c (1 : ℂ) := by
        ext a c
        simp only [Matrix.vecMulVec_apply, Pi.star_apply, Matrix.sum_apply,
                   Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
        rw [Finset.sum_eq_single a]
        · rw [Finset.sum_eq_single c]
          · simp
          · intro c' _ hc'; simp [hc']
          · intro h; exact absurd (Finset.mem_univ c) h
        · intro a' _ ha'
          apply Finset.sum_eq_zero
          intro c' _
          have hne : ¬ (a' = a ∧ c' = c) := fun h => ha' h.1
          simp [hne]
        · intro h; exact absurd (Finset.mem_univ a) h
      have hPsiVal : Ψ (Matrix.vecMulVec (star u) u) =
          ∑ a : Fin d, ∑ c : Fin d, (star (u a) * u c) • Ψ (Matrix.single a c (1 : ℂ)) := by
        rw [hVecDecomp, map_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [map_sum]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        exact LinearMap.map_smul _ _ _
      have hPsiPoint : ∀ x y : Fin d,
          (Ψ (Matrix.vecMulVec (star u) u)) x y =
          ∑ a : Fin d, ∑ c : Fin d,
            star (u a) * u c * (Ψ (Matrix.single a c (1 : ℂ))) x y := by
        intro x y
        rw [hPsiVal]
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      -- F: shared quadruple-sum kernel.
      let F : Fin d → Fin d → Fin d → Fin d → ℂ :=
        fun a c x y => star (u a) * u c * (A l x y * (Ψ (Matrix.single a c (1 : ℂ))) x y)
      have hLHS_eq : star u ⬝ᵥ (C l *ᵥ u) =
          ∑ a, ∑ c, ∑ x, ∑ y, F a c x y := by
        show ∑ a : Fin d, star (u a) * ((C l *ᵥ u) a) = _
        refine Finset.sum_congr rfl (fun a _ => ?_)
        show star (u a) * (∑ c : Fin d, (C l) a c * u c)
            = ∑ c, ∑ x, ∑ y, F a c x y
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        show star (u a) * ((∑ x : Fin d, ∑ y : Fin d,
                A l x y * (Ψ (Matrix.single a c (1 : ℂ))) x y) * u c)
            = ∑ x, ∑ y, F a c x y
        rw [show star (u a) * ((∑ x : Fin d, ∑ y : Fin d,
                A l x y * (Ψ (Matrix.single a c (1 : ℂ))) x y) * u c)
              = star (u a) * u c * (∑ x : Fin d, ∑ y : Fin d,
                A l x y * (Ψ (Matrix.single a c (1 : ℂ))) x y) from by ring]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.mul_sum]
      have hRHS_eq : (A l * (Ψ (Matrix.vecMulVec (star u) u))ᵀ).trace =
          ∑ x, ∑ y, ∑ a, ∑ c, F a c x y := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [hPsiPoint x y, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        show A l x y * (star (u a) * u c * (Ψ (Matrix.single a c (1 : ℂ))) x y)
            = star (u a) * u c * (A l x y * (Ψ (Matrix.single a c (1 : ℂ))) x y)
        ring
      have hkey : star u ⬝ᵥ (C l *ᵥ u) =
          (A l * (Ψ (Matrix.vecMulVec (star u) u))ᵀ).trace := by
        rw [hLHS_eq, hRHS_eq]
        calc ∑ a : Fin d, ∑ c : Fin d, ∑ x : Fin d, ∑ y : Fin d, F a c x y
            = ∑ a : Fin d, ∑ x : Fin d, ∑ c : Fin d, ∑ y : Fin d, F a c x y := by
                refine Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
          _ = ∑ x : Fin d, ∑ a : Fin d, ∑ c : Fin d, ∑ y : Fin d, F a c x y :=
                Finset.sum_comm
          _ = ∑ x : Fin d, ∑ a : Fin d, ∑ y : Fin d, ∑ c : Fin d, F a c x y := by
                refine Finset.sum_congr rfl (fun x _ => ?_)
                refine Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
          _ = ∑ x : Fin d, ∑ y : Fin d, ∑ a : Fin d, ∑ c : Fin d, F a c x y := by
                refine Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
      rw [hkey]
      apply trace_mul_posSemidef_nonneg (hA l)
      exact (hPSD _ (Matrix.posSemidef_vecMulVec_star_self u)).transpose
  · -- entry equality
    ext ⟨a, b⟩ ⟨c, e⟩
    rw [choi_comp_apply]
    set N : Matrix (Fin d) (Fin d) ℂ := Ψ (Matrix.single a c (1 : ℂ)) with hN_def
    have hPhiN : (Φ N) b e =
        ∑ x : Fin d, ∑ y : Fin d, N x y * (Φ (Matrix.single x y (1 : ℂ))) b e := by
      conv_lhs => rw [Matrix.eq_sum_single_smul N]
      rw [map_sum]
      simp only [Matrix.sum_apply]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [map_sum]
      simp only [Matrix.sum_apply]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [LinearMap.map_smul, Matrix.smul_apply, smul_eq_mul]
    have hPhiSingle : ∀ x y : Fin d,
        (Φ (Matrix.single x y (1 : ℂ))) b e =
        ∑ l : Fin k, (p l : ℂ) * A l x y * B l b e := by
      intro x y
      have hentry := congr_fun (congr_fun heq (x, b)) (y, e)
      rw [Choi_apply] at hentry
      simp only [Matrix.sum_apply, Matrix.smul_apply] at hentry
      convert hentry using 1
      refine Finset.sum_congr rfl (fun l _ => ?_)
      unfold Matrix.kronecker Matrix.kroneckerMap; simp; ring
    rw [hPhiN]
    simp_rw [hPhiSingle]
    have hKronEntry : ∀ l : Fin k,
        (Matrix.kronecker (C l) (B l)) (a, b) (c, e) = C l a c * B l b e := by
      intro l
      unfold Matrix.kronecker Matrix.kroneckerMap
      simp
    rw [show (∑ l : Fin k, (p l : ℂ) • Matrix.kronecker (C l) (B l)) (a, b) (c, e)
          = ∑ l : Fin k, (p l : ℂ) * (C l a c * B l b e) from by
            simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hKronEntry]]
    have hSwap : (∑ x : Fin d, ∑ y : Fin d,
                    N x y * ∑ l : Fin k, (p l : ℂ) * A l x y * B l b e)
        = ∑ l : Fin k, ∑ x : Fin d, ∑ y : Fin d,
            N x y * ((p l : ℂ) * A l x y * B l b e) := by
      calc (∑ x : Fin d, ∑ y : Fin d,
                  N x y * ∑ l : Fin k, (p l : ℂ) * A l x y * B l b e)
          = ∑ x : Fin d, ∑ y : Fin d, ∑ l : Fin k,
                N x y * ((p l : ℂ) * A l x y * B l b e) := by
              refine Finset.sum_congr rfl (fun x _ => ?_)
              refine Finset.sum_congr rfl (fun y _ => ?_)
              rw [Finset.mul_sum]
        _ = ∑ x : Fin d, ∑ l : Fin k, ∑ y : Fin d,
                N x y * ((p l : ℂ) * A l x y * B l b e) := by
              refine Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
        _ = ∑ l : Fin k, ∑ x : Fin d, ∑ y : Fin d,
                N x y * ((p l : ℂ) * A l x y * B l b e) := Finset.sum_comm
    rw [hSwap]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hClac : C l a c = ∑ x : Fin d, ∑ y : Fin d, A l x y * N x y := by
      simp only [C, Matrix.of_apply, hN_def]
    rw [hClac]
    rw [show ∑ x : Fin d, ∑ y : Fin d,
              N x y * ((p l : ℂ) * A l x y * B l b e)
          = ((p l : ℂ) * B l b e) * (∑ x : Fin d, ∑ y : Fin d, A l x y * N x y) from by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun x _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun y _ => ?_)
            ring]
    ring

/-- Separability preserved under left composition with a PSD-preserving map. -/
theorem separable_under_cp_left {d : Nat}
    (Φ Ψ : QChan d d)
    (hΨ : Separable (Choi Ψ))
    (hPSD : ∀ M : Matrix (Fin d) (Fin d) ℂ, M.PosSemidef → (Φ M).PosSemidef) :
    Separable (Choi (Φ.comp Ψ)) :=
  choi_comp_left_formula Φ Ψ hΨ hPSD

/-- Separability preserved under right composition (CP-on-first-factor). -/
theorem separable_under_cp_right {d : Nat}
    (Φ Ψ : QChan d d)
    (hΦ : Separable (Choi Φ))
    (hPSD : ∀ M : Matrix (Fin d) (Fin d) ℂ, M.PosSemidef → (Ψ M).PosSemidef)
    (hStar : ∀ M : Matrix (Fin d) (Fin d) ℂ, Ψ Mᴴ = (Ψ M)ᴴ) :
    Separable (Choi (Φ.comp Ψ)) :=
  choi_comp_right_formula Φ Ψ hΦ hPSD hStar

/-- EB ideal closure (left): composing a PSD-preserving map on the left with an EB
    channel yields an EB channel. -/
theorem EB_comp_left {d : Nat}
    (Φ Ψ : QChan d d)
    (hΨ : IsEB Ψ)
    (hPSD : ∀ M : Matrix (Fin d) (Fin d) ℂ, M.PosSemidef → (Φ M).PosSemidef) :
    IsEB (Φ.comp Ψ) := by
  unfold IsEB at hΨ ⊢
  exact separable_under_cp_left Φ Ψ hΨ hPSD

/-- EB ideal closure (right): composing an EB channel with a PSD-preserving
    star-preserving map on the right yields an EB channel. -/
theorem EB_comp_right {d : Nat}
    (Φ Ψ : QChan d d) (hΦ : IsEB Φ)
    (hPSD : ∀ M : Matrix (Fin d) (Fin d) ℂ, M.PosSemidef → (Ψ M).PosSemidef)
    (hStar : ∀ M : Matrix (Fin d) (Fin d) ℂ, Ψ Mᴴ = (Ψ M)ᴴ) :
    IsEB (Φ.comp Ψ) := by
  unfold IsEB at hΦ ⊢
  exact choi_comp_right_formula Φ Ψ hΦ hPSD hStar

end PPT2
