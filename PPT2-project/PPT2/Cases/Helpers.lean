/-
PPT2.Cases.Helpers — single-side PPT² corollaries.
When at least one factor is dephasing or depolarizing-below-threshold, the
composition is already EB without invoking the open PPT² conjecture.
-/
import PPT2.Basic
import PPT2.EntanglementBreaking
import PPT2.Examples.Dephasing
import PPT2.Examples.Depolarizing
import PPT2.Examples.MeasurePrepare
import PPT2.PartialTranspose
import PPT2.Separable
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.Order

namespace PPT2

open Matrix BigOperators
open scoped ComplexOrder Kronecker

/-- If Φ is a dephasing channel and both Φ, Ψ are PPT, then Φ ∘ Ψ is EB. -/
theorem ppt2_for_dephasing_left {d : Nat} (Φ Ψ : QChan d d)
    (hΦ : IsDephasing Φ) (_hPPTΦ : IsPPT Φ) (_hPPTΨ : IsPPT Ψ)
    (hPSDΨ : ∀ M : Matrix (Fin d) (Fin d) ℂ, M.PosSemidef → (Ψ M).PosSemidef)
    (hStarΨ : ∀ M : Matrix (Fin d) (Fin d) ℂ, Ψ Mᴴ = (Ψ M)ᴴ) :
    IsEB (Φ.comp Ψ) :=
  EB_comp_right Φ Ψ (ppt_dephasing_is_EB Φ _hPPTΦ hΦ)
    hPSDΨ hStarΨ

/-- If Ψ is dephasing and both Φ, Ψ are PPT, then Φ ∘ Ψ is EB.
    Requires Φ to be PSD-preserving. -/
theorem ppt2_for_dephasing_right {d : Nat} (Φ Ψ : QChan d d)
    (hΨ : IsDephasing Ψ) (_hPPTΦ : IsPPT Φ) (hPPTΨ : IsPPT Ψ)
    (hPSD : ∀ M : Matrix (Fin d) (Fin d) ℂ, M.PosSemidef → (Φ M).PosSemidef) :
    IsEB (Φ.comp Ψ) :=
  EB_comp_left Φ Ψ (ppt_dephasing_is_EB Ψ hPPTΨ hΨ) hPSD

/-- If Φ is depolarizing with p ∈ [0, 1/(d+1)] and Ψ is PPT, then Φ ∘ Ψ is EB. -/
theorem ppt2_for_depolarizing_left {d : Nat} (p : ℝ) (Φ Ψ : QChan d d)
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / (d + 1 : ℝ)) (hΦ : IsDepolarizing p Φ)
    (_hPPTΨ : IsPPT Ψ)
    (hPSDΨ : ∀ M : Matrix (Fin d) (Fin d) ℂ, M.PosSemidef → (Ψ M).PosSemidef)
    (hStarΨ : ∀ M : Matrix (Fin d) (Fin d) ℂ, Ψ Mᴴ = (Ψ M)ᴴ) :
    IsEB (Φ.comp Ψ) :=
  EB_comp_right Φ Ψ (depolarizing_below_threshold_implies_eb p Φ hp0 hp hΦ)
    hPSDΨ hStarΨ

/-- If Ψ is depolarizing with p ∈ [0, 1/(d+1)] and Φ is PPT, then Φ ∘ Ψ is EB.
    Requires Φ to be PSD-preserving. -/
theorem ppt2_for_depolarizing_right {d : Nat} (p : ℝ) (Φ Ψ : QChan d d)
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / (d + 1 : ℝ)) (hΨ : IsDepolarizing p Ψ)
    (_hPPTΦ : IsPPT Φ)
    (hPSD : ∀ M : Matrix (Fin d) (Fin d) ℂ, M.PosSemidef → (Φ M).PosSemidef) :
    IsEB (Φ.comp Ψ) :=
  EB_comp_left Φ Ψ (depolarizing_below_threshold_implies_eb p Ψ hp0 hp hΨ) hPSD

-- `partialTranspose_kronecker`, `Separable.partialTranspose`, and
-- `psd_kron_separable` are declared in `PPT2/Channels/Depolarizing.lean`
-- and re-exported via the import chain.

/-- Separable matrices have PSD partial transpose. Direct corollary of
    `Separable.partialTranspose` (cone closed under PT) and
    `separable_implies_psd` (cone ⊆ PSD). -/
theorem separable_implies_ppt {d : Nat}
    (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hX : Separable X) : (partialTranspose X).PosSemidef :=
  separable_implies_psd (hX.partialTranspose)

/-- Entanglement-breaking channels are PPT. Direct corollary of
    `separable_implies_ppt` applied to the Choi matrix, unfolding the
    definitions `IsEB := Separable ∘ Choi` and `IsPPT := PosSemidef ∘
    partialTranspose ∘ Choi`. -/
theorem EB_implies_PPT {d : Nat} (Φ : QChan d d)
    (hEB : IsEB Φ) : IsPPT Φ := by
  unfold IsEB at hEB
  unfold IsPPT
  exact separable_implies_ppt (Choi Φ) hEB

/-- For depolarizing channels at or below the King 2003 threshold `p ∈ [0, 1/(d+1)]`,
    PPT and EB are equivalent.  The forward direction uses
    `depolarizing_below_threshold_implies_eb`; the reverse direction is the
    trivial Peres 1996 direction through `EB_implies_PPT`.  Note the forward
    direction does not consume `IsPPT` — the threshold hypothesis already
    implies EB unconditionally; the iff form is the natural interface
    statement. -/
theorem depolarizing_PPT_iff_EB {d : Nat} (p : ℝ) (Φ : QChan d d)
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / (d + 1 : ℝ)) (h : IsDepolarizing p Φ) :
    IsPPT Φ ↔ IsEB Φ :=
  ⟨fun _ => depolarizing_below_threshold_implies_eb p Φ hp0 hp h,
   fun hEB => EB_implies_PPT Φ hEB⟩

/-- Unfolding lemma: Choi of a composed channel equals the double sum of
    Kronecker products of matrix units with the composed image.  This is the
    first step in replacing the `choi_comp_*_formula` axioms with true
    theorems: it does not use CP, linearity of Φ on Ψ's output, or
    separability — just the definitions `Choi := ∑ᵢⱼ |i⟩⟨j| ⊗ Φ(|i⟩⟨j|)` and
    `Φ.comp Ψ := LinearMap.comp Φ Ψ`. -/
theorem choi_comp_unfold {d : Nat} (Φ Ψ : QChan d d) :
    Choi (Φ.comp Ψ) =
      ∑ i : Fin d, ∑ j : Fin d,
        kron (Matrix.single i j (1 : ℂ))
             (Φ (Ψ (Matrix.single i j (1 : ℂ)))) := by
  rfl

-- `psd_kron_separable` is declared in `PPT2/Channels/Depolarizing.lean`.

/-- Replacing the second factor of a separable witness by any PSD-preserving
    image keeps the resulting Kronecker sum separable. -/
theorem separable_kron_sum_map_second {d : Nat}
    (f : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (hf : ∀ B : Matrix (Fin d) (Fin d) ℂ, B.PosSemidef → (f B).PosSemidef)
    (k : ℕ) (p : Fin k → ℝ) (A B : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (hp : ∀ i, 0 ≤ p i) (hA : ∀ i, (A i).PosSemidef)
    (hB : ∀ i, (B i).PosSemidef) :
    Separable (∑ i, (p i : ℂ) • Matrix.kronecker (A i) (f (B i))) := by
  refine ⟨k, p, A, fun i => f (B i), hp, hA, ?_, rfl⟩
  intro i; exact hf _ (hB i)

/-- **P2 真证桥（partial）**：把 `choi_comp_left_formula` axiom 拆成
    （a）Φ 把 PSD 送到 PSD（PSD-preserving）；
    （b）'partial-application' identity `Choi (Φ.comp Ψ) = (id ⊗ Φ) (Choi Ψ)`
        的等价形态——在裸 `QChan := LinearMap` 框架下需要 Choi-Jamiolkowski 函子性。

    本引理把 (b) 显式作为额外假设 `hChoiCompFun`，从而仅依赖 (a)+(b)+separable
    见证就能在 0 项目 axiom 下证 Choi(Φ.comp Ψ) separable。

    一旦 mathlib 中 `id ⊗ Φ` 在 Matrix tensor 上的 functoriality 上到 PSD level，
    `hChoiCompFun` 就可以从 Choi 定义自动推出，从而把 `choi_comp_left_formula` axiom
    完全消除（这是 v3.13 / iter-14 给 P2 真证留下的最小 missing infrastructure 接口）。 -/
theorem choi_comp_left_via_PSD_preserving {d : Nat}
    (Φ Ψ : QChan d d)
    (hPSD : ∀ M : Matrix (Fin d) (Fin d) ℂ, M.PosSemidef → (Φ M).PosSemidef)
    (hChoiCompFun :
      ∃ (k : ℕ) (p : Fin k → ℝ) (A B : Fin k → Matrix (Fin d) (Fin d) ℂ),
        (∀ i, 0 ≤ p i) ∧ (∀ i, (A i).PosSemidef) ∧ (∀ i, (B i).PosSemidef) ∧
        Choi (Φ.comp Ψ) =
          ∑ i, (p i : ℂ) • Matrix.kronecker (A i) (Φ (B i)))
    (_hΨ : Separable (Choi Ψ)) :
    Separable (Choi (Φ.comp Ψ)) := by
  obtain ⟨k, p, A, B, hp, hA, hB, heq⟩ := hChoiCompFun
  rw [heq]
  exact separable_kron_sum_map_second (fun M => Φ M) hPSD k p A B hp hA hB

/-- For dephasing channels, PPT and EB are equivalent.  Forward direction:
    `ppt_dephasing_is_EB` (dephasing → measure-and-prepare → EB; the PPT
    hypothesis is unused).  Reverse direction: `EB_implies_PPT` (the trivial
    Peres 1996 direction via `separable_implies_ppt` on the Choi matrix). -/
theorem dephasing_PPT_iff_EB {d : Nat} (Φ : QChan d d)
    (hDeph : IsDephasing Φ) : IsPPT Φ ↔ IsEB Φ :=
  ⟨fun hPPT => ppt_dephasing_is_EB Φ hPPT hDeph,
   fun hEB => EB_implies_PPT Φ hEB⟩

/-- For measure-and-prepare channels, PPT and EB are equivalent.
    Forward: any measure-and-prepare channel is EB (`measure_prepare_is_EB`,
    HSR 1998 / Watrous 2018 §4.6); the PPT hypothesis is not consumed.
    Reverse: EB → PPT is the trivial Peres 1996 direction via `EB_implies_PPT`. -/
theorem mp_PPT_iff_EB {d : Nat} (Φ : QChan d d)
    (hMP : IsMeasurePrepare Φ) : IsPPT Φ ↔ IsEB Φ :=
  ⟨fun _ => measure_prepare_is_EB Φ hMP,
   fun hEB => EB_implies_PPT Φ hEB⟩

/-- For dephasing channels, PPT and measure-and-prepare are equivalent.
    Forward: dephasing → measure-and-prepare unconditionally
    (`dephasing_is_measure_prepare`, Wilde §4.6.7); the PPT hypothesis is
    not consumed.  Reverse: measure-and-prepare → EB (`measure_prepare_is_EB`)
    → PPT (`EB_implies_PPT`, the trivial Peres 1996 direction). -/
theorem dephasing_PPT_iff_MP {d : Nat} (Φ : QChan d d)
    (hDeph : IsDephasing Φ) : IsPPT Φ ↔ IsMeasurePrepare Φ :=
  ⟨fun _ => dephasing_is_measure_prepare Φ hDeph,
   fun hMP => EB_implies_PPT Φ (measure_prepare_is_EB Φ hMP)⟩

/-- If Ψ is measure-and-prepare, then for any PSD-preserving Φ the composition Φ ∘ Ψ is EB. -/
theorem mp_comp_left {d : Nat} (Φ Ψ : QChan d d)
    (hΨ : IsMeasurePrepare Ψ)
    (hPSD : ∀ M : Matrix (Fin d) (Fin d) ℂ, M.PosSemidef → (Φ M).PosSemidef) :
    IsEB (Φ.comp Ψ) :=
  EB_comp_left Φ Ψ (measure_prepare_is_EB Ψ hΨ) hPSD

/-- If Φ is measure-and-prepare, then for any Ψ the composition Φ ∘ Ψ is EB. -/
theorem mp_comp_right {d : Nat} (Φ Ψ : QChan d d)
    (hΦ : IsMeasurePrepare Φ)
    (hPSDΨ : ∀ M : Matrix (Fin d) (Fin d) ℂ, M.PosSemidef → (Ψ M).PosSemidef)
    (hStarΨ : ∀ M : Matrix (Fin d) (Fin d) ℂ, Ψ Mᴴ = (Ψ M)ᴴ) :
    IsEB (Φ.comp Ψ) :=
  EB_comp_right Φ Ψ (measure_prepare_is_EB Φ hΦ) hPSDΨ hStarΨ

/-- **PPT² for measure-and-prepare (left)**: if Φ is measure-and-prepare and
    both Φ, Ψ are PPT, then `Φ ∘ Ψ` is entanglement-breaking. -/
theorem ppt2_for_mp_left {d : Nat} (Φ Ψ : QChan d d)
    (hΦ : IsMeasurePrepare Φ) (_hPPTΦ : IsPPT Φ) (_hPPTΨ : IsPPT Ψ)
    (hPSDΨ : ∀ M : Matrix (Fin d) (Fin d) ℂ, M.PosSemidef → (Ψ M).PosSemidef)
    (hStarΨ : ∀ M : Matrix (Fin d) (Fin d) ℂ, Ψ Mᴴ = (Ψ M)ᴴ) :
    IsEB (Φ.comp Ψ) :=
  EB_comp_right Φ Ψ (measure_prepare_is_EB Φ hΦ) hPSDΨ hStarΨ

/-- For measure-and-prepare channels, PPT and `Separable (Choi Φ)` are
    equivalent.  This is `mp_PPT_iff_EB` re-expressed using the
    *definition* `IsEB := Separable ∘ Choi` (no new content). -/
theorem mp_PPT_iff_separable_choi {d : Nat} (Φ : QChan d d)
    (hMP : IsMeasurePrepare Φ) : IsPPT Φ ↔ Separable (Choi Φ) := by
  have h := mp_PPT_iff_EB Φ hMP
  unfold IsEB at h
  exact h

/-- For depolarizing channels at or below the King 2003 threshold `p ∈ [0, 1/(d+1)]`,
    PPT and `Separable (Choi Φ)` are equivalent.  This is `depolarizing_PPT_iff_EB`
    re-expressed using the *definition* `IsEB := Separable ∘ Choi` (no new content). -/
theorem depolarizing_PPT_iff_separable_choi {d : Nat} (p : ℝ) (Φ : QChan d d)
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / (d + 1 : ℝ)) (h : IsDepolarizing p Φ) :
    IsPPT Φ ↔ Separable (Choi Φ) := by
  have hi := depolarizing_PPT_iff_EB p Φ hp0 hp h
  unfold IsEB at hi
  exact hi

/-- **P2 left bridge via functoriality**: if `Choi Ψ` is separable and `Φ` is
    PSD-preserving, then `Choi (Φ.comp Ψ)` is separable.

    Proof sketch: unpack the separable witness `Choi Ψ = ∑ₗ pₗ • (Aₗ ⊗ Bₗ)`.
    Entrywise, `Ψ(|a⟩⟨c|) = ∑ₗ pₗ · Aₗ[a,c] · Bₗ` (from `Choi_apply` + `heq`).
    By linearity of Φ, `Φ(Ψ(|a⟩⟨c|)) = ∑ₗ pₗ · Aₗ[a,c] · Φ(Bₗ)`.
    Hence `Choi (Φ.comp Ψ) = ∑ₗ pₗ • (Aₗ ⊗ Φ(Bₗ))`, which is separable since
    each `Φ(Bₗ)` is PSD by `hPSD`. -/
theorem choi_comp_left_via_functoriality {d : Nat} (Φ Ψ : QChan d d)
    (hΨ : Separable (Choi Ψ))
    (hPSD : ∀ M : Matrix (Fin d) (Fin d) ℂ, M.PosSemidef → (Φ M).PosSemidef) :
    Separable (Choi (Φ.comp Ψ)) := by
  obtain ⟨k, p, A, B, hp, hA, hB, heq⟩ := hΨ
  refine ⟨k, p, A, fun l => Φ (B l), hp, hA, fun l => hPSD _ (hB l), ?_⟩
  ext ⟨a, b⟩ ⟨c, e⟩
  rw [choi_comp_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  -- Recover Ψ(single a c 1) = ∑ₗ pₗ · Aₗ[a,c] · Bₗ from the separable witness
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

/-- **P2-right bridge via functoriality**: if `Choi Φ` is separable and `Ψ` is
    PSD-preserving, then `Choi (Φ.comp Ψ)` is separable.

    Proof: unpack the separable witness `Choi Φ = ∑ₗ pₗ • (Aₗ ⊗ Bₗ)`.
    Entrywise, `Φ(|x⟩⟨y|)[b,e] = ∑ₗ pₗ · Aₗ[x,y] · Bₗ[b,e]` (from `Choi_apply` + `heq`).
    By linearity of Φ, for any M:
      `Φ(M)[b,e] = ∑ₗ pₗ · (∑ x y, Aₗ[x,y] · M[x,y]) · Bₗ[b,e]`.
    Applying to `M = Ψ(|a⟩⟨c|)`:
      `(Φ∘Ψ)(|a⟩⟨c|)[b,e] = ∑ₗ pₗ · Cₗ[a,c] · Bₗ[b,e]`
    where `Cₗ[a,c] := ∑ x y, Aₗ[x,y] · (Ψ(|a⟩⟨c|))[x,y]`.
    Hence `Choi(Φ∘Ψ) = ∑ₗ pₗ • (Cₗ ⊗ Bₗ)`.

    The theorem follows from `choi_comp_right_formula` (which establishes the
    stronger result without the `hPSD` hypothesis). -/
theorem choi_comp_right_via_functoriality {d : Nat} (Φ Ψ : QChan d d)
    (hΦ : Separable (Choi Φ))
    (hPSD : ∀ M : Matrix (Fin d) (Fin d) ℂ, M.PosSemidef → (Ψ M).PosSemidef)
    (hStar : ∀ M : Matrix (Fin d) (Fin d) ℂ, Ψ Mᴴ = (Ψ M)ᴴ) :
    Separable (Choi (Φ.comp Ψ)) :=
  choi_comp_right_formula Φ Ψ hΦ hPSD hStar

end PPT2
