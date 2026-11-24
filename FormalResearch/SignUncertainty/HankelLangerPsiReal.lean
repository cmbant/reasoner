module

public import FormalResearch.SignUncertainty.HankelLangerPsi
public import FormalResearch.SignUncertainty.HankelWtConj

/-!
# Analyticity and reality of the Langer-disc density `Ψ̃` (`gt:7.7c` (a))

`hankelPsi c f` is analytic on `closedBall 0 (c^{2/3} κ · 4.94·10⁻⁴)` (`analyticOnNhd_hankelPsi`) and real on the real
axis of that disc (`hankelPsi_real`; chart inverse conjugation symmetry, `hankelLocal_im_eq_zero`).
-/

@[expose] public section

open Complex Set Filter Topology Metric
open scoped Real

namespace FormalResearch.SignUncertainty

lemma exists_chartY_small' {η : ℕ → ℝ} (h : LangerEta η) {y : ℂ} (hy : ‖y‖ ≤ 9e-4) :
    ∃ w ∈ ball (0 : ℂ) 1e-3, chartY η w = y := by
  obtain ⟨w, hw, hwy⟩ := exists_chartY_eq h (r := 9.9e-4) (by norm_num) le_rfl (y0 := y) (by linarith)
  exact ⟨w, by rw [mem_ball_zero_iff]; linarith [hw], hwy⟩

lemma chartYinv_conj {η : ℕ → ℝ} (h : LangerEta η) {y : ℂ} (hy : ‖y‖ ≤ 9e-4) :
    chartYinv η (starRingEnd ℂ y) = starRingEnd ℂ (chartYinv η y) := by
  obtain ⟨hw, hY⟩ := chartYinv_spec η (exists_chartY_small' h hy)
  have hy' : ‖starRingEnd ℂ y‖ ≤ 9e-4 := by rw [Complex.norm_conj]; exact hy
  obtain ⟨hw', hY'⟩ := chartYinv_spec η (exists_chartY_small' h hy')
  have hcw : starRingEnd ℂ (chartYinv η y) ∈ ball (0 : ℂ) 1e-3 := by
    rw [mem_ball_zero_iff, Complex.norm_conj]; exact mem_ball_zero_iff.1 hw
  have hc : chartY η (starRingEnd ℂ (chartYinv η y)) = starRingEnd ℂ y := by
    rw [chartY_conj h (mem_ball_zero_iff.1 hw).le, hY]
  exact (injOn_chartY h).eq_iff (ball_subset_closedBall hw') (ball_subset_closedBall hcw) |>.1
    (hY'.trans hc.symm)

lemma deriv_chartYinv_real {y : ℝ} (hy : |y| ≤ 4.94e-4) :
    starRingEnd ℂ (deriv (chartYinv etaC) (y : ℂ)) = deriv (chartYinv etaC) (y : ℂ) := by
  have hyn : ‖(y : ℂ)‖ ≤ 4.94e-4 := by simpa using hy
  obtain ⟨hw, hY⟩ := chartYinv_spec etaC (exists_chartY_small langerEta_etaC hyn)
  have hd := (analyticAt_chartYinv langerEta_etaC (mem_ball_zero_iff.1 hw)).2
  rw [hY] at hd
  have hsym : chartYinv etaC =ᶠ[𝓝 (y : ℂ)] (starRingEnd ℂ) ∘ chartYinv etaC ∘ (starRingEnd ℂ) := by
    filter_upwards [ball_mem_nhds (y : ℂ) (by norm_num : (0 : ℝ) < 4e-4)] with z hz
    have hzn : ‖z‖ ≤ 9e-4 := by
      have := mem_ball_iff_norm.1 hz
      have h2 : ‖z‖ ≤ ‖z - y‖ + ‖(y : ℂ)‖ := by
        calc ‖z‖ = ‖(z - y) + y‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith
    have hz' := chartYinv_conj langerEta_etaC (y := starRingEnd ℂ z) (by rw [Complex.norm_conj]; exact hzn)
    rw [Complex.conj_conj] at hz'
    exact hz'
  have hd2 := hd.conj_conj
  have hy0 : starRingEnd ℂ (y : ℂ) = y := Complex.conj_ofReal y
  rw [hy0] at hd2
  have := hsym.deriv_eq
  have e : deriv (chartYinv etaC) (y : ℂ) = starRingEnd ℂ (chartYD etaC (chartYinv etaC ↑y))⁻¹ := by
    rw [this, hd2.deriv]
  rw [hd.deriv] at e ⊢
  exact e.symm

/-- `Ψ̃` is analytic on the closed Langer disc `‖u‖ ≤ c^{2/3} κ · 4.94·10⁻⁴` (across the cut). -/
theorem analyticOnNhd_hankelPsi {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    AnalyticOnNhd ℂ (hankelPsi c f) (closedBall (0 : ℂ) (c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4)) := by
  intro u hu
  set K : ℝ := c ^ (2 / 3 : ℝ) * langerKappa with hK
  have hK0 : 0 < K := mul_pos (Real.rpow_pos_of_pos hc _) langerKappa_pos
  have hyn : ‖u / (K : ℂ)‖ ≤ 4.94e-4 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK0, div_le_iff₀ hK0]
    have := mem_closedBall_zero_iff.1 hu
    linarith
  set y : ℂ := u / (K : ℂ) with hy
  obtain ⟨hw, hY⟩ := chartYinv_spec etaC (exists_chartY_small langerEta_etaC hyn)
  have hG : AnalyticAt ℂ (chartYinv etaC) y := by
    have := (analyticAt_chartYinv langerEta_etaC (mem_ball_zero_iff.1 hw)).1
    rwa [hY] at this
  have hwn := norm_chartYinv_le langerEta_etaC hyn
  have h1w : (1 + chartYinv etaC y) ∈ slitPlane :=
    one_add_mem_slitPlane_of_norm_lt (lt_of_le_of_lt hwn (by norm_num))
  have h1w0 : 1 + chartYinv etaC y ≠ 0 := Complex.slitPlane_ne_zero h1w
  have hD : AnalyticAt ℂ (deriv (chartYinv etaC)) y := hG.deriv
  have hlog : AnalyticAt ℂ (fun y => Complex.log (1 + chartYinv etaC y)) y :=
    (analyticAt_const.add hG).clog h1w
  have hloc : AnalyticAt ℂ (fun y => hankelLocal c f (Complex.log (1 + chartYinv etaC y))) y :=
    ((hankelLocal_differentiable hc hf).analyticAt _).comp hlog
  have hY' : AnalyticAt ℂ (hankelPsiY c f) y := by
    unfold hankelPsiY
    exact (((analyticAt_const.mul hD).div (analyticAt_const.add hG) h1w0)).mul hloc
  have hlin : AnalyticAt ℂ (fun u : ℂ => u / (K : ℂ)) u := by
    exact analyticAt_id.div analyticAt_const (by exact_mod_cast hK0.ne')
  exact AnalyticAt.comp (g := hankelPsiY c f) (f := fun u : ℂ => u / (K : ℂ)) hY' hlin

/-- `Ψ̃` is real on the real axis of the Langer disc. -/
theorem hankelPsi_real {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) {x : ℝ}
    (hx : |x| ≤ c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4) : (hankelPsi c f (x : ℂ)).im = 0 := by
  set K : ℝ := c ^ (2 / 3 : ℝ) * langerKappa with hK
  have hK0 : 0 < K := mul_pos (Real.rpow_pos_of_pos hc _) langerKappa_pos
  set yr : ℝ := x / K with hyr
  have hyr_le : |yr| ≤ 4.94e-4 := by
    rw [hyr, abs_div, abs_of_pos hK0, div_le_iff₀ hK0]; linarith
  have hyc : (x : ℂ) / (K : ℂ) = (yr : ℂ) := by rw [hyr]; push_cast; rfl
  have hyn : ‖(yr : ℂ)‖ ≤ 4.94e-4 := by simpa using hyr_le
  have hconjy : starRingEnd ℂ (yr : ℂ) = yr := Complex.conj_ofReal yr
  have hw := chartYinv_conj langerEta_etaC (y := (yr : ℂ)) (hyn.trans (by norm_num))
  rw [hconjy] at hw
  set w := chartYinv etaC (yr : ℂ) with hwdef
  have hwr : starRingEnd ℂ w = w := hw.symm
  have hwim : w.im = 0 := by
    have := congrArg Complex.im hwr
    simp at this; linarith
  have hwn := norm_chartYinv_le langerEta_etaC hyn
  have hwre : |w.re| ≤ 5e-4 := by
    have := Complex.abs_re_le_norm w
    linarith
  have h1pos : 0 < 1 + w.re := by linarith [abs_le.1 hwre]
  have hlogr : Complex.log (1 + w) = ((Real.log (1 + w.re) : ℝ) : ℂ) := by
    have : (1 + w) = ((1 + w.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hwim]
    rw [this, ← Complex.ofReal_log h1pos.le]
  have hL := hankelLocal_im_eq_zero (c := c) f (Real.log (1 + w.re))
  have hLc : starRingEnd ℂ (hankelLocal c f (Complex.log (1 + w))) =
      hankelLocal c f (Complex.log (1 + w)) := by
    rw [hlogr]; exact Complex.conj_eq_iff_im.2 hL
  have hDc := deriv_chartYinv_real hyr_le
  have h1c : starRingEnd ℂ (1 + w) = 1 + w := by rw [map_add, map_one, hwr]
  show (hankelPsiY c f ((x : ℂ) / (K : ℂ))).im = 0
  rw [hyc]
  rw [← Complex.conj_eq_iff_im]
  unfold hankelPsiY
  rw [map_mul, map_div₀, map_mul, map_neg, Complex.conj_ofReal, hDc, ← hwdef, h1c, hLc]

/-- info: 'FormalResearch.SignUncertainty.analyticOnNhd_hankelPsi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms analyticOnNhd_hankelPsi

/-- info: 'FormalResearch.SignUncertainty.hankelPsi_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelPsi_real

end FormalResearch.SignUncertainty
