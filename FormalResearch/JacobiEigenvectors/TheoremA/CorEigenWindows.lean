module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.CorEigenBase
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumAssemblyBulk

/-!
# Paper J, Layer 2: the slope input of cor:eigen from the window data of the assembly (L2.E, F-BB-2)

Source: Paper J `app_thmA.tex`, proof of `thm:smo-spec`, paragraph "Density" ("`S_0^I` is `C^1` with `partial_X S_0^I <= -c < 0`"), used again in Step 3 of the proof of `cor:eigen` (`thmA.tex`).

`cor:eigen` needs `-S_0' >= 2 c_0` on the closed band (`BandSlope`).  The windows `WindowPhase` of the assembly (bulk blocks via `bulk_slope`, soft edges via `SoftPhaseInputs`) carry
the slope bound `partial_X Sigma_0(., 0) <= -c` on the open window and `Sigma_0(., 0) = S_0` on window and band, and the windows cover the band with the relative-interior property (`WindowCover`).

## Proved here (axiom-pinned)

* `bandSlope_of_windows`: for windows `W i` of a family `T` with cover `hcov` and any `S` that is `C^1` on the extended interval (`delta_1 > 0`) with `S_0 = actionS0 T` on the band: `BandSlope T K S`
  (every interior point of the band lies in the open interior of a window, where `S_0 = Sigma_0(., 0)` near it; the endpoints by continuity of `S_0'`).
* `BandSlope.of_trunc`: `BandSlope (truncSM G M) K S` gives `BandSlope G K S` (same band).
* `bandSlope_of_windows_trunc`: the form used with `thmSmoSpec_core`: windows of `truncSM G M`, `S` with `SmoothExt G K M S delta_1 Cn`, `ActionFormula G K S`.

## Differences from the paper

None; this is the paper's density-step slope for the glued function, restricted to the band.  The windows and the cover are the *premises* of `thmSmoSpec_core`
(`hlabels`, `WS`, `hcov`), which `layer4_windows` (`Assembly/ThmAi.lean`) now proves from the Layer-4 inputs; with them every `CorEigen*` theorem of `CorEigenCount.lean`, `CorEigenInverse.lean` follows (`corEigen_proved`, `Assembly/CorEigen.lean`).

## Not formalised

The explicit `S_0' = -int T^{-1/2}` (the slope is obtained from the chart data instead).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting

variable {Par : Type*} [TopologicalSpace Par]

theorem bandSlope_of_windows {ι : Type*} [Fintype ι] {T : SymbolFamily Par} {K : Set Par} {t0 : ℝ} {M : ℕ} {a b : ι → Par → ℝ} {δ : ℝ}
    (W : ∀ i, WindowPhase T K t0 M (a i) (b i)) (hδ : 0 < δ) (hcov : WindowCover T K a b δ) (hlt : ∀ μ ∈ K, T.bandLo μ < T.bandHi μ)
    {S : ℕ → Par → ℝ → ℝ} {δ1 : ℝ} (hδ1 : 0 < δ1)
    (hSm : ∀ μ ∈ K, ContDiffOn ℝ 1 (S 0 μ) (Icc (T.bandLo μ - δ1) (T.bandHi μ + δ1)))
    (hA : ∀ μ ∈ K, ∀ X ∈ Icc (T.bandLo μ) (T.bandHi μ), S 0 μ X = actionS0 T μ X) :
    BandSlope T K S := by
  choose c hc0 hcsl using fun i => (W i).slope
  obtain ⟨c0, hc0pos, hc0le⟩ := exists_pos_forall_le c hc0
  refine ⟨c0 / 2, by positivity, fun μ hμ X hX => ?_⟩
  have hlth := hlt μ hμ
  set lo := T.bandLo μ with hlo
  set hi := T.bandHi μ with hhi
  -- the bound on the open band
  have hopen : ∀ Y ∈ Ioo lo hi, deriv (S 0 μ) Y ≤ -c0 := by
    intro Y hY
    obtain ⟨i, h1, h2, h3, h4⟩ := hcov.cov μ hμ Y ⟨by linarith [hY.1], by linarith [hY.2]⟩
    have hai : a i μ < Y := by
      rcases h3 with h | h
      · exact h
      · rw [h]; linarith [hY.1]
    have hbi : Y < b i μ := by
      rcases h4 with h | h
      · exact h
      · rw [h]; linarith [hY.2]
    have hnh : Ioo (max (a i μ) lo) (min (b i μ) hi) ∈ nhds Y :=
      Ioo_mem_nhds (max_lt hai hY.1) (lt_min hbi hY.2)
    have hev : S 0 μ =ᶠ[nhds Y] fun X' => (W i).Sigma μ 0 X' 0 := by
      refine Filter.eventually_of_mem hnh (fun y hy => ?_)
      have hyb : y ∈ Icc lo hi := ⟨(le_max_right _ _).trans hy.1.le, hy.2.le.trans (min_le_right _ _)⟩
      have hyw : y ∈ Icc (a i μ) (b i μ) := ⟨(le_max_left _ _).trans hy.1.le, hy.2.le.trans (min_le_left _ _)⟩
      show S 0 μ y = (W i).Sigma μ 0 y 0
      rw [hA μ hμ y hyb, (W i).Sigma_zero μ hμ y hyw hyb]
    rw [hev.deriv_eq]
    exact (hcsl i μ hμ Y ⟨hai, hbi⟩).trans (neg_le_neg (hc0le i))
  -- closure
  have hAB : lo - δ1 < hi + δ1 := by linarith
  have hcont : ContinuousOn (deriv (S 0 μ)) (Ioo (lo - δ1) (hi + δ1)) :=
    ((hSm μ hμ).continuousOn_derivWithin (uniqueDiffOn_Icc hAB) le_rfl).mono Ioo_subset_Icc_self |>.congr
      (fun x hx => (derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)).symm)
  have hX' : X ∈ closure (Ioo lo hi) := by rw [closure_Ioo hlth.ne]; exact hX
  have key := ContinuousWithinAt.closure_le (f := deriv (S 0 μ)) (g := fun _ => -c0) (s := Ioo lo hi) hX'
    ((hcont X ⟨by linarith [hX.1], by linarith [hX.2]⟩).mono (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩))
    continuousWithinAt_const hopen
  linarith

/-- `BandSlope` depends on the family only through the band. -/
theorem BandSlope.of_band {F F' : SymbolFamily Par} {K : Set Par} {S : ℕ → Par → ℝ → ℝ}
    (hb : ∀ μ ∈ K, F.bandLo μ = F'.bandLo μ ∧ F.bandHi μ = F'.bandHi μ) (h : BandSlope F K S) : BandSlope F' K S := by
  obtain ⟨c0, hc0, h⟩ := h
  exact ⟨c0, hc0, fun μ hμ X hX => h μ hμ X (by rw [(hb μ hμ).1, (hb μ hμ).2]; exact hX)⟩

/-- **The slope input for the families of `thmSmoSpec_core`**: windows of `truncSM G M'` (any order `M'`), and any `S` that is `C^{M+1}` (any `M`) on a `delta_1`-neighbourhood of the band with `S_0 = actionS0 G` there. -/
theorem bandSlope_of_windows_trunc {ι : Type*} [Fintype ι] {G : SymbolFamily Par} {K : Set Par} {t0 : ℝ} {M' M : ℕ} {a b : ι → Par → ℝ} {δ : ℝ}
    (W : ∀ i, WindowPhase (truncSM G M') K t0 M' (a i) (b i)) (hδ : 0 < δ) (hcov : WindowCover (truncSM G M') K a b δ)
    (hlt : ∀ μ ∈ K, G.bandLo μ < G.bandHi μ) {S : ℕ → Par → ℝ → ℝ} {δ1 Cn : ℝ} (hδ1 : 0 < δ1)
    (hS : SmoothExt G K M S δ1 Cn) (hA : ActionFormula G K S) : BandSlope G K S := by
  have hb : ∀ μ ∈ K, (truncSM G M').bandLo μ = G.bandLo μ ∧ (truncSM G M').bandHi μ = G.bandHi μ :=
    fun μ _ => band_truncSM G M' μ
  have h := bandSlope_of_windows W hδ hcov (fun μ hμ => by rw [(hb μ hμ).1, (hb μ hμ).2]; exact hlt μ hμ) hδ1
    (S := S) (fun μ hμ => by
      rw [(hb μ hμ).1, (hb μ hμ).2]
      exact ((hS μ hμ 0 (Nat.zero_le _)).1.of_le (by exact_mod_cast Nat.succ_pos M)))
    (fun μ hμ X hX => by
      rw [(hb μ hμ).1, (hb μ hμ).2] at hX
      rw [hA μ hμ X hX, actionS0_truncSM])
  exact BandSlope.of_band (F := truncSM G M') (F' := G) hb h

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bandSlope_of_windows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bandSlope_of_windows

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bandSlope_of_windows_trunc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bandSlope_of_windows_trunc

end FormalResearch.JacobiEigenvectors.TheoremA
