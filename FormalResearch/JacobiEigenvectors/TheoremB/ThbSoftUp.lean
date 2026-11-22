module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbSoftBlock
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbInputs

/-!
# Paper J, Theorem B, L3.5c, part 14: the upper soft block (`SoftBlockUp`)

Source: Paper J `app_thmB.tex`, proof of `prop:thb-inputs`, the soft block at the upper edge `X_s^+` (columns with `blockOf = none`, `J_hi < X`).

## Proved here

* **`softBlockUp_proved : SoftBlockUp CP TB spl`** (the frozen statement of `ThbInputs.lean`), for every chart pair `CP` and transfer bundle `TB`: from `soft_block_gen` (the soft block for a soft chart pair) applied to `CI0.softUpL, CI0.softUpR, CI1.softUpL, CI1.softUpR`
  (`mirror_up`, `soft_up_eq`, `TB.softUpL`, `TB.softUpR`), the entries of `compMatrix` on an upper soft column (`compMatrix_softUp_entry`), the host bound, and `stepZero` for the window `|X - bandHi| <= delta_0` of the columns (`cover`).

## Differences from the paper

The column set `|X - bandHi| <= delta_0` is derived from `cover` (`bandHi < J_hi + delta_0`) and `stepZero` (`X <= bandHi + C h^2`), and `h <= h_0` is replaced by `N >= N_0` outside this theorem.  **Not formalised**: nothing.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine FormalResearch.JB

open scoped Classical

section Up

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

theorem softBlockUp_proved (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (TB : TransferBundle CP) (spl : Fin CP.CI0.nb → ℝ) : SoftBlockUp CP TB spl := by
  intro hm hq ht0 hstd hhost
  obtain ⟨r, hr0⟩ := hstd
  obtain ⟨Ch, hH0, hCh0, hHpos, Hhost⟩ := hhost
  have hrq : StdAssump (frozenFamily F Kidx) (paramSet K t0) (q / 2) r := by
    have : q / 2 = Kidx := by omega
    rw [this]; exact hr0
  obtain ⟨hUc, hUδ, hUη, hUz, hUmu⟩ := CP.soft_up_eq
  obtain ⟨cs, Cε, cε, N0, h0, hCε, hcε, hh0, hh01, H⟩ := soft_block_gen CP.CI0.pc CP.CI0.softUpL CP.CI0.softUpR CP.CI1.softUpL CP.CI1.softUpR
    CP.CI0.mirror_up CP.CI1.mirror_up hUz hUmu hUc hUδ hUη hm r hrq TB.softUpL TB.softUpR Ch hCh0
  obtain ⟨Cs, hs0, hs0p, hsp⟩ := stepZero (frozenFamily F Kidx) (paramSet K t0) (q / 2) r hrq
  have hδpos : 0 < CP.CI0.softUpL.δ0 := CP.CI0.softUpL.consts_pos.1
  have hM : 0 < |Cs| + 1 := by positivity
  refine ⟨cs, Cε, cε, N0, min (min h0 hH0) (min t0 (min hs0 (CP.CI0.softUpL.δ0 / (|Cs| + 1)))), hCε, hcε,
    lt_min (lt_min hh0 hHpos) (lt_min ht0 (lt_min hs0p (div_pos hδpos hM))),
    (min_le_left _ _).trans ((min_le_left _ _).trans hh01), ?_⟩
  intro μ hμ N hN hst Xs Um hE cols hcols
  have hst1 : F.step N ≤ h0 := hst.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hst2 : F.step N ≤ hH0 := hst.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hst3 : F.step N ≤ t0 := hst.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hst4 : F.step N ≤ hs0 := hst.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hst5 : F.step N ≤ CP.CI0.softUpL.δ0 / (|Cs| + 1) :=
    hst.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hp := atStep_mem hμ N hst3
  have hE' := eig_frozen (Kidx := Kidx) hE
  have h1 : F.step N ≤ 1 := hst1.trans hh01
  have hsm : Cs * F.step N ^ 2 ≤ CP.CI0.softUpL.δ0 := by
    have e1 : Cs * F.step N ^ 2 ≤ |Cs| * F.step N := by
      calc Cs * F.step N ^ 2 ≤ |Cs| * F.step N ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
        _ ≤ |Cs| * F.step N := mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)
    have e2 : |Cs| * F.step N ≤ |Cs| * (CP.CI0.softUpL.δ0 / (|Cs| + 1)) := mul_le_mul_of_nonneg_left hst5 (abs_nonneg _)
    have e3 : |Cs| * (CP.CI0.softUpL.δ0 / (|Cs| + 1)) ≤ CP.CI0.softUpL.δ0 := by
      rw [← mul_div_assoc, div_le_iff₀ hM]
      nlinarith [mul_nonneg hδpos.le (abs_nonneg Cs)]
    linarith
  have hwin : ∀ k ∈ cols, |Xs k - (frozenFamily F Kidx).bandHi (atStep F μ N)| ≤ CP.CI0.softUpL.δ0 := by
    intro k hk
    obtain ⟨-, hJ⟩ := hcols k hk
    have hcov := CP.CI0.cover _ hp
    have hup : Xs k ≤ (frozenFamily F Kidx).bandHi (atStep F μ N) + Cs * F.step N ^ 2 := (hsp _ hp N hst4 Xs Um hE' k).2
    rw [abs_le]
    constructor <;> linarith [hcov.2.2.2.1]
  have hN0 := hN
  refine H _ hp N hN0 hst1 Xs Um hE' cols hwin (compMatrix CP.CI0 spl μ N Xs) (compMatrix CP.CI1 (CP.spl1 spl) μ N Xs) ?_ ?_ ?_ ?_
  · intro k hk i
    obtain ⟨hb, hJ⟩ := hcols k hk
    exact compMatrix_softUp_entry CP.CI0 spl μ N Xs k (fun ⟨ν, hν⟩ => blockOf_none CP.CI0 hb ν hν) hJ i
  · intro k hk i
    obtain ⟨hb, hJ⟩ := hcols k hk
    exact compMatrix_softUp_entry CP.CI1 (CP.spl1 spl) μ N Xs k
      (fun ⟨ν, h1, h2⟩ => blockOf_none CP.CI0 hb (Fin.cast CP.nb_eq ν) ⟨by rw [← CP.lo_eq]; exact h1, by rw [← CP.hi_eq]; exact h2⟩)
      (by rw [CP.J_eq.2]; exact hJ) i
  · intro j
    exact (Hhost μ hμ N hst2 hst3 Xs Um hE j).1
  · intro j
    exact (Hhost μ hμ N hst2 hst3 Xs Um hE j).2

end Up

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.softBlockUp_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.softBlockUp_proved

end FormalResearch.JacobiEigenvectors.TheoremB

end
