module

public import FormalResearch.SignUncertainty.HankelLangerChartMain
public import FormalResearch.SignUncertainty.HankelLangerReal

/-!
# The analytic inverse of the Langer chart (`gt:7.7b` (iii)--(iv))

`chartYinv η y` is the unique `w` in `ball 0 (10⁻³)` with `y(w) = y` (choice; unique by `injOn_chartY`).  It is analytic
on `‖y‖ ≤ 4.94·10⁻⁴` (`analyticAt_chartYinv`) with derivative `1/y'(w)`, `‖w‖ ≤ 1.0019‖y‖`.  The disc `‖y‖ ≤ 4.94·10⁻⁴`
is the image of the paper's `|ũ| ≤ A_c²` (`w₀/2 = π² r₀/2 < 4.94·10⁻⁴` at `r₀ = 10⁻⁴`).
-/

@[expose] public section

open Complex Set Filter Topology Metric
open scoped Real

namespace FormalResearch.SignUncertainty

/-- An injective analytic map with nonvanishing derivative has an analytic inverse on its image
(for any choice function). -/
lemma analyticAt_choiceInverse {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ w ∈ U, AnalyticAt ℂ f w) (hinj : InjOn f U) (hne : ∀ w ∈ U, deriv f w ≠ 0)
    (hg : ∀ y ∈ f '' U, g y ∈ U ∧ f (g y) = y) {w0 : ℂ} (hw0 : w0 ∈ U) :
    AnalyticAt ℂ g (f w0) ∧ HasDerivAt g (deriv f w0)⁻¹ (f w0) := by
  have hfa := hf w0 hw0
  have hd := hfa.hasStrictDerivAt
  have hne0 := hne w0 hw0
  have hL := hfa.analyticAt_localInverse hne0
  have hLd := hd.to_localInverse hne0
  set L := hd.localInverse f (deriv f w0) w0 hne0 with hLdef
  have hLw : L (f w0) = w0 := HasStrictFDerivAt.localInverse_apply_image ..
  have hLU : ∀ᶠ y in 𝓝 (f w0), L y ∈ U := by
    have := hLd.hasDerivAt.continuousAt
    exact this.eventually (hU.mem_nhds (by rw [hLw]; exact hw0))
  have hR := HasStrictDerivAt.eventually_right_inverse hd hne0
  have heq : g =ᶠ[𝓝 (f w0)] L := by
    filter_upwards [hR, hLU] with y h1 h2
    have hy : y ∈ f '' U := ⟨L y, h2, h1⟩
    obtain ⟨hg1, hg2⟩ := hg y hy
    exact hinj hg1 h2 (hg2.trans h1.symm)
  exact ⟨hL.congr heq.symm, hLd.hasDerivAt.congr_of_eventuallyEq heq⟩

/-- The inverse of the Langer coordinate `y(w)` on `ball 0 (10⁻³)`. -/
noncomputable def chartYinv (η : ℕ → ℝ) (y : ℂ) : ℂ := by
  classical
  exact if h : ∃ w ∈ ball (0 : ℂ) 1e-3, chartY η w = y then h.choose else 0

lemma chartYinv_spec (η : ℕ → ℝ) {y : ℂ} (h : ∃ w ∈ ball (0 : ℂ) 1e-3, chartY η w = y) :
    chartYinv η y ∈ ball (0 : ℂ) 1e-3 ∧ chartY η (chartYinv η y) = y := by
  unfold chartYinv
  simp only [h, dite_true]
  exact h.choose_spec

lemma exists_chartY_small (h : LangerEta η) {y : ℂ} (hy : ‖y‖ ≤ 4.94e-4) :
    ∃ w ∈ ball (0 : ℂ) 1e-3, chartY η w = y := by
  obtain ⟨w, hw, hwy⟩ := exists_chartY_eq h (r := 9.9e-4) (by norm_num) le_rfl (y0 := y) (by linarith)
  exact ⟨w, by rw [mem_ball_zero_iff]; linarith [hw], hwy⟩

lemma norm_chartYinv_le (h : LangerEta η) {y : ℂ} (hy : ‖y‖ ≤ 4.94e-4) :
    ‖chartYinv η y‖ ≤ 5e-4 := by
  obtain ⟨hw, hwy⟩ := chartYinv_spec η (exists_chartY_small h hy)
  set w := chartYinv η y
  have hwn : ‖w‖ ≤ 1e-3 := (mem_ball_zero_iff.1 hw).le
  have := norm_chartY_add_le h hwn
  rw [hwy] at this
  have h2 : ‖w‖ ≤ ‖y‖ + ‖y + w‖ := by
    calc ‖w‖ = ‖-y + (y + w)‖ := by ring_nf
      _ ≤ ‖-y‖ + ‖y + w‖ := norm_add_le _ _
      _ = _ := by rw [norm_neg]
  linarith

theorem analyticAt_chartYinv (h : LangerEta η) {w0 : ℂ} (hw0 : ‖w0‖ < 1e-3) :
    AnalyticAt ℂ (chartYinv η) (chartY η w0) ∧
      HasDerivAt (chartYinv η) (chartYD η w0)⁻¹ (chartY η w0) := by
  have hU : IsOpen (ball (0 : ℂ) 1e-3) := isOpen_ball
  have hdiff : ∀ w ∈ ball (0 : ℂ) 1e-3, HasDerivAt (chartY η) (chartYD η w) w := fun w hw =>
    hasDerivAt_chartY h (mem_ball_zero_iff.1 hw).le
  have hf : ∀ w ∈ ball (0 : ℂ) 1e-3, AnalyticAt ℂ (chartY η) w := by
    intro w hw
    refine Complex.analyticAt_iff_eventually_differentiableAt.2 ?_
    filter_upwards [hU.mem_nhds hw] with z hz using (hdiff z hz).differentiableAt
  have hne : ∀ w ∈ ball (0 : ℂ) 1e-3, deriv (chartY η) w ≠ 0 := by
    intro w hw
    rw [(hdiff w hw).deriv]
    intro h0
    have := norm_chartYD_add_one_le h (mem_ball_zero_iff.1 hw).le
    rw [h0] at this; simp at this; norm_num at this
  have hinj : InjOn (chartY η) (ball (0 : ℂ) 1e-3) :=
    (injOn_chartY h).mono (ball_subset_closedBall)
  have key := analyticAt_choiceInverse (g := chartYinv η) hU hf hinj hne
    (fun y hy => chartYinv_spec η (by obtain ⟨w, hw, hwy⟩ := hy; exact ⟨w, hw, hwy⟩))
    (mem_ball_zero_iff.2 hw0)
  refine ⟨key.1, ?_⟩
  have := key.2
  rwa [(hdiff w0 (mem_ball_zero_iff.2 hw0)).deriv] at this

end FormalResearch.SignUncertainty
