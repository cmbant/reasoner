module

public import FormalResearch.Special.LatticeFourier

/-!
# The smooth-phase estimate for `∫ φ ({t₀} - ½)`

Combining the integration by parts (`ibp_identity`) with `integral_w_sawH_le`:
for `φ` holomorphic on `|Im s| ≤ y₀` with `|φ| ≤ C_φ e^{-κ|Re s|}`, and `Ψ = φ/τ₀'`,
`‖∫_{-X}^{X} φ ({t₀} - ½)‖ ≤ C_φ e^{-κX}/m + (1/12)(2C_w y₁ e^{-κX} + (2C_w/κ)e^{-2πmy₁})`
with `C_w = C_φ (e^{κr}/(rm) + K/m²)`, where `y₁ + r ≤ y₀` (`r` is the Cauchy radius for `φ'`).
This is the `J_k^±` part of the proof of `lem:latticesum` (i).
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex MeasureTheory intervalIntegral

/-- The constant `C_w = C_φ (e^{κr}/(rm) + K/m²)` bounding `|Ψ'|`. -/
noncomputable def smoothCw (Cφ κ r m K : ℝ) : ℝ := Cφ * (Real.exp (κ * r) / (r * m) + K / m ^ 2)

/-- Cauchy's estimate for `φ'` on the strip. -/
lemma norm_deriv_strip_le {φ : ℂ → ℂ} {Cφ κ r y0 : ℝ} (hr : 0 < r) (hκ : 0 ≤ κ) (hCφ : 0 ≤ Cφ)
    (hφd : DifferentiableOn ℂ φ {s | |s.im| ≤ y0})
    (hφb : ∀ s : ℂ, |s.im| ≤ y0 → ‖φ s‖ ≤ Cφ * Real.exp (-κ * |s.re|))
    {z : ℂ} (hz : |z.im| + r ≤ y0) :
    ‖deriv φ z‖ ≤ Cφ * Real.exp (κ * r) * Real.exp (-κ * |z.re|) / r := by
  have hsub : Metric.closedBall z r ⊆ {s : ℂ | |s.im| ≤ y0} := by
    intro ζ hζ
    have h1 : ‖ζ - z‖ ≤ r := by simpa [dist_eq_norm] using hζ
    have h2 : |(ζ - z).im| ≤ ‖ζ - z‖ := Complex.abs_im_le_norm _
    have h3 : |ζ.im| ≤ |z.im| + |(ζ - z).im| := by
      have : ζ.im = z.im + (ζ - z).im := by simp
      rw [this]; exact abs_add_le _ _
    show |ζ.im| ≤ y0
    linarith
  have hd : DiffContOnCl ℂ φ (Metric.ball z r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z hr.ne']
    exact hφd.mono hsub
  have hC : ∀ ζ ∈ Metric.sphere z r, ‖φ ζ‖ ≤ Cφ * Real.exp (κ * r) * Real.exp (-κ * |z.re|) := by
    intro ζ hζ
    have hζ' : ζ ∈ Metric.closedBall z r := Metric.sphere_subset_closedBall hζ
    have h1 : ‖ζ - z‖ = r := by simpa [dist_eq_norm] using hζ
    have h2 : |(ζ - z).re| ≤ ‖ζ - z‖ := Complex.abs_re_le_norm _
    have h3 : |z.re| ≤ |ζ.re| + |(ζ - z).re| := by
      have : z.re = ζ.re - (ζ - z).re := by simp
      rw [this]; exact abs_sub _ _
    refine (hφb ζ (hsub hζ')).trans ?_
    have hex : Real.exp (-κ * |ζ.re|) ≤ Real.exp (κ * r) * Real.exp (-κ * |z.re|) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
    calc Cφ * Real.exp (-κ * |ζ.re|) ≤ Cφ * (Real.exp (κ * r) * Real.exp (-κ * |z.re|)) :=
          mul_le_mul_of_nonneg_left hex hCφ
      _ = _ := by ring
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hd hC
  exact this

/-- `Ψ = φ/τ₀'`. -/
noncomputable def psiQuot (τ0 φ : ℂ → ℂ) (z : ℂ) : ℂ := φ z / deriv τ0 z

lemma strip_mem_nhds {y0 y1 r : ℝ} (hr : 0 < r) (hyr : y1 + r ≤ y0) {z : ℂ} (hz : |z.im| ≤ y1) :
    {s : ℂ | |s.im| ≤ y0} ∈ 𝓝 z := by
  have hU : IsOpen {s : ℂ | |s.im| < y0} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  refine Filter.mem_of_superset (hU.mem_nhds (by show |z.im| < y0; linarith)) ?_
  intro s hs; exact le_of_lt (show |s.im| < y0 from hs)

namespace CalPhase

variable {τ0 : ℂ → ℂ} {X y0 m M K : ℝ}

lemma ne_zero_deriv (h : CalPhase τ0 X y0 m M K) {z : ℂ} (hz : InWin X y0 z) : deriv τ0 z ≠ 0 := by
  intro h0
  have := h.ge z hz
  rw [h0] at this; simp at this; linarith [h.hm]

lemma analyticAt_psiQuot (h : CalPhase τ0 X y0 m M K) {φ : ℂ → ℂ} {y1 r : ℝ} (hr : 0 < r)
    (hyr : y1 + r ≤ y0) (hφd : DifferentiableOn ℂ φ {s | |s.im| ≤ y0})
    {z : ℂ} (hzr : |z.re| ≤ X + 1) (hzi : |z.im| ≤ y1) : AnalyticAt ℂ (psiQuot τ0 φ) z := by
  have hy : y1 ≤ y0 := by linarith
  have hw : InWin X y0 z := ⟨hzr, hzi.trans hy⟩
  have hφ : AnalyticAt ℂ φ z := hφd.analyticAt (strip_mem_nhds hr hyr hzi)
  exact hφ.div (h.ana_deriv hw) (h.ne_zero_deriv hw)

lemma norm_deriv_psiQuot_le (h : CalPhase τ0 X y0 m M K) {φ : ℂ → ℂ} {Cφ κ y1 r : ℝ}
    (hκ : 0 ≤ κ) (hCφ : 0 ≤ Cφ) (hr : 0 < r) (hyr : y1 + r ≤ y0)
    (hφd : DifferentiableOn ℂ φ {s | |s.im| ≤ y0})
    (hφb : ∀ s : ℂ, |s.im| ≤ y0 → ‖φ s‖ ≤ Cφ * Real.exp (-κ * |s.re|))
    {z : ℂ} (hzr : |z.re| ≤ X) (hzi : |z.im| ≤ y1) :
    ‖deriv (psiQuot τ0 φ) z‖ ≤ smoothCw Cφ κ r m K * Real.exp (-κ * |z.re|) := by
  have hy : y1 ≤ y0 := by linarith
  have hX := h.hX
  have hm := h.hm
  have hw : InWin X y0 z := ⟨hzr.trans (by linarith), hzi.trans hy⟩
  have hne := h.ne_zero_deriv hw
  have hφdiff : DifferentiableAt ℂ φ z := hφd.differentiableAt (strip_mem_nhds hr hyr hzi)
  have hτd : DifferentiableAt ℂ (deriv τ0) z := h.ddiff hw
  have hder := hφdiff.hasDerivAt.div hτd.hasDerivAt hne
  have hdz : deriv (psiQuot τ0 φ) z = (deriv φ z * deriv τ0 z - φ z * deriv (deriv τ0) z) /
      (deriv τ0 z) ^ 2 := hder.deriv
  rw [hdz]
  set a := deriv φ z
  set b := deriv τ0 z
  set c := φ z
  set d := deriv (deriv τ0) z
  have hb : m ≤ ‖b‖ := (h.ge z hw).trans (Complex.re_le_norm _)
  have hbpos : 0 < ‖b‖ := lt_of_lt_of_le hm hb
  have ha : ‖a‖ ≤ Cφ * Real.exp (κ * r) * Real.exp (-κ * |z.re|) / r :=
    norm_deriv_strip_le hr hκ hCφ hφd hφb (by linarith)
  have hc : ‖c‖ ≤ Cφ * Real.exp (-κ * |z.re|) := hφb z (hzi.trans hy)
  have hd' : ‖d‖ ≤ K := h.dd z hw
  have hK : 0 ≤ K := (norm_nonneg _).trans hd'
  set E := Real.exp (-κ * |z.re|) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hsplit : ‖(a * b - c * d) / b ^ 2‖ ≤ ‖a‖ / ‖b‖ + ‖c‖ * ‖d‖ / ‖b‖ ^ 2 := by
    rw [norm_div, norm_pow]
    have : ‖a * b - c * d‖ ≤ ‖a‖ * ‖b‖ + ‖c‖ * ‖d‖ := by
      calc _ ≤ ‖a * b‖ + ‖c * d‖ := norm_sub_le _ _
        _ = _ := by rw [norm_mul, norm_mul]
    calc ‖a * b - c * d‖ / ‖b‖ ^ 2 ≤ (‖a‖ * ‖b‖ + ‖c‖ * ‖d‖) / ‖b‖ ^ 2 :=
          div_le_div_of_nonneg_right this (by positivity)
      _ = ‖a‖ / ‖b‖ + ‖c‖ * ‖d‖ / ‖b‖ ^ 2 := by field_simp
  have t1 : ‖a‖ / ‖b‖ ≤ Cφ * Real.exp (κ * r) * E / r / m := by
    apply div_le_div₀ (by positivity) ha hm hb
  have t2 : ‖c‖ * ‖d‖ / ‖b‖ ^ 2 ≤ Cφ * E * K / m ^ 2 := by
    apply div_le_div₀ (by positivity) (mul_le_mul hc hd' (norm_nonneg _) (by positivity)) (by positivity)
    exact pow_le_pow_left₀ hm.le hb 2
  refine hsplit.trans ((add_le_add t1 t2).trans (le_of_eq ?_))
  unfold smoothCw
  field_simp

end CalPhase

end FormalResearch.Special.Lattice
