module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumAssemblyLower
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumAssemblySoft
public import FormalResearch.JacobiEigenvectors.Charts.ChartInputs

/-!
# Paper J: the window cover `WindowCover` from the chart cover fields (thm:A (i), item 3; finding F-S6-4)

Source: Paper J `thmA.tex`, proof of `thm:A (i)`: "the bulk blocks `[lo nu, hi nu]` and the two soft windows cover the band, with overlaps of positive length".

## Proved here (axiom-pinned)

* `windowCover_of_charts`: `WindowCover T K (Sum.elim lo aS) (Sum.elim hi bS) w` (the three fields `sub`, `cov`, `ovl`) from the chart fields `cover`, `cover_bulk`, `blocks_in_J`, `overlap_pos`
  of `ChartInputs`, for the bulk blocks and the two soft windows `[X_s^+ - w, X_s^+ + w]`, `[X_s^- - w, X_s^- + w]`.  No chart field was added.

## Differences from the paper

* The paper leaves the soft half-widths implicit.  Here both equal one `w` (`= delta` of `thmSmoSpec`), and three geometric relations are explicit premises: the soft windows reach into the bulk range
  (`X_s^+ - w < J_hi`, `J_lo < X_s^- + w`) and `w <= X_s^+ - X_s^-`; blocks have positive length.  They are satisfied for `w` small (the paper's "`delta` small"), and are premises of `thmAi_assembled`.

## Not formalised

A choice of `w` from the chart data (existence of small `w` meeting the relations): the callers supply it.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par]

/-- **`hcov` from the chart cover fields** (finding F-S6-4).  The bulk blocks `[lo nu, hi nu]` (cover `cover_bulk`, `blocks_in_J`, `cover`) and the two soft windows `[X_s^+ - w, X_s^+ + w]`,
`[X_s^- - w, X_s^- + w]` (`aS true, bS true`, `aS false, bS false`: the windows of `softUpWindow`, `softLoWindow` for `SoftPhaseInputs` of half-width `w`) cover `[X_s^- - w, X_s^+ + w]`, with positive-length overlaps
(`overlap_pos`) and window overlaps only inside the band.  Needed beyond the chart fields: both soft half-widths equal `w` (one `delta`), the soft windows reach into the bulk range
(`X_s^+ - w < J_hi`, `J_lo < X_s^- + w`), `w <= X_s^+ - X_s^-`, and positive-length blocks. -/
theorem windowCover_of_charts {T : SymbolFamily Par} {K : Set Par} {Kidx m : ℕ} {t0 : ℝ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    (CI : ChartInputs T K Kidx t0 m (2 * Kidx) U V cPC CPC) (ht0 : 0 ≤ t0) (w : ℝ) (hw : 0 < w)
    (aS bS : Bool → Par → ℝ) (haU : ∀ μ, aS true μ = T.bandHi μ - w) (hbU : ∀ μ, bS true μ = T.bandHi μ + w)
    (haL : ∀ μ, aS false μ = T.bandLo μ - w) (hbL : ∀ μ, bS false μ = T.bandLo μ + w)
    (hlt : ∀ ν, CI.lo ν < CI.hi ν)
    (hJhi : ∀ μ ∈ K, T.bandHi μ - w < CI.Jhi) (hJlo : ∀ μ ∈ K, CI.Jlo < T.bandLo μ + w)
    (hwb : ∀ μ ∈ K, w ≤ T.bandHi μ - T.bandLo μ) :
    WindowCover T K (Sum.elim (fun ν _ => CI.lo ν) aS) (Sum.elim (fun ν _ => CI.hi ν) bS) w := by
  have hcov : ∀ μ ∈ K, T.bandLo μ < CI.Jlo ∧ CI.Jlo ≤ CI.Jhi ∧ CI.Jhi < T.bandHi μ := by
    intro μ hμ
    have := CI.cover (μ, 0) ⟨hμ, ⟨by linarith, ht0⟩⟩
    rw [frozen_bandLo_zero, frozen_bandHi_zero] at this
    exact ⟨this.1, this.2.1, this.2.2.1⟩
  refine ⟨?_, ?_, ?_⟩
  · intro μ hμ i
    obtain ⟨h1, h2, h3⟩ := hcov μ hμ
    rcases i with ν | s
    · obtain ⟨b1, b2, b3⟩ := CI.blocks_in_J ν
      simp only [Sum.elim_inl]
      exact ⟨by linarith, hlt ν, by linarith⟩
    · cases s
      · simp only [Sum.elim_inr, haL, hbL]
        have := hwb μ hμ
        exact ⟨le_rfl, by linarith, by linarith⟩
      · simp only [Sum.elim_inr, haU, hbU]
        have := hwb μ hμ
        exact ⟨by linarith, by linarith, le_rfl⟩
  · intro μ hμ x hx
    obtain ⟨h1, h2, h3⟩ := hcov μ hμ
    have hJlo' := hJlo μ hμ
    have hJhi' := hJhi μ hμ
    by_cases hxl : x ≤ CI.Jlo
    · refine ⟨Sum.inr false, ?_⟩
      simp only [Sum.elim_inr, haL, hbL]
      exact ⟨hx.1, by linarith, Or.inr trivial, Or.inl (by linarith)⟩
    · by_cases hxh : CI.Jhi ≤ x
      · refine ⟨Sum.inr true, ?_⟩
        simp only [Sum.elim_inr, haU, hbU]
        exact ⟨by linarith, hx.2, Or.inl (by linarith), Or.inr trivial⟩
      · push Not at hxl hxh
        obtain ⟨ν, hν1, hν2, hν3, hν4⟩ := CI.cover_bulk x hxl.le hxh.le
        refine ⟨Sum.inl ν, ?_⟩
        simp only [Sum.elim_inl]
        refine ⟨hν1, hν2, Or.inl ?_, Or.inl ?_⟩
        · rcases hν3 with h | h
          · exact h
          · rw [h]; exact hxl
        · rcases hν4 with h | h
          · exact h
          · rw [h]; exact hxh
  · intro μ hμ i j hij x hxi hxj
    obtain ⟨h1, h2, h3⟩ := hcov μ hμ
    have hwb' := hwb μ hμ
    have hblock : ∀ ν, x ∈ Icc (CI.lo ν) (CI.hi ν) → x ∈ Icc (T.bandLo μ) (T.bandHi μ) := by
      intro ν hx
      obtain ⟨b1, b2, b3⟩ := CI.blocks_in_J ν
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rcases i with ν | s
    · exact hblock ν (by simpa using hxi)
    · rcases j with ν | s'
      · exact hblock ν (by simpa using hxj)
      · cases s <;> cases s'
        · exact absurd rfl hij
        · simp only [Sum.elim_inr, haL, hbL, haU, hbU, Set.mem_Icc] at hxi hxj
          exact ⟨by linarith [hxj.1], by linarith [hxi.2]⟩
        · simp only [Sum.elim_inr, haL, hbL, haU, hbU, Set.mem_Icc] at hxi hxj
          exact ⟨by linarith [hxi.1], by linarith [hxj.2]⟩
        · exact absurd rfl hij

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.windowCover_of_charts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.windowCover_of_charts

end FormalResearch.JacobiEigenvectors.TheoremA

end
