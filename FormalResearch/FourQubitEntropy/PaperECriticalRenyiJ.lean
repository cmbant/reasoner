import Mathlib

/-!
# The one-variable inequality behind the binary-grouping bound (`lem:fqe-renyi-grouping`)

Paper E, `renyi_cubic_bound.tex`. With `L = ln 2`, `q_b = 4L/(4L-1)`, `r_b = q_b - 1 = 1/(4L-1)`,
`w(a) = a²(3-2a)` and `h = binEntropy` (nats), the function
`J(a) = q_b (w ln a + (1-w) ln(1-a)) + h(w) + q_b a (1-a)` satisfies `J ≥ 0` on `[0,1]`.

Proof (as in the paper, but organised as a minimum principle): `J(1/2) = J(1) = 0`,
`J' = 6a(1-a) Φ(a)` with `Φ(a) = f(ln(a/(1-a)))`, `f(s) = (r_b - 1) s - ln(e^s + 3) + ln(3e^s + 1)`
strictly concave on `[0,∞)` with `f(0) = 0`; so at an interior negative minimum `c` we have
`Φ(c) = 0`, hence `Φ < 0` on `(c, 1)`, hence `J` is strictly decreasing on `[c,1]` and `J(1) < J(c) < 0`,
contradicting `J(1) = 0`.

Proved, axiom-free (`propext`, `Classical.choice`, `Quot.sound`).
-/

open Real

namespace FormalResearch.FourQubitEntropy.PaperECritical

/-- `ln 2`. -/
noncomputable def Lg : ℝ := Real.log 2
/-- The threshold order `q_b = 4 ln 2 / (4 ln 2 - 1)` (`eq:fqe-binary-threshold`). -/
noncomputable def qb : ℝ := 4 * Lg / (4 * Lg - 1)
/-- `r_b = q_b - 1 = 1/(4 ln 2 - 1)`. -/
noncomputable def rb : ℝ := 1 / (4 * Lg - 1)

theorem Lg_gt : 0.6931471803 < Lg := Real.log_two_gt_d9
theorem Lg_lt : Lg < 0.6931471808 := Real.log_two_lt_d9
theorem four_Lg_sub_one_pos : 0 < 4 * Lg - 1 := by have := Lg_gt; linarith
theorem qb_eq_rb_add_one : qb = rb + 1 := by
  have := four_Lg_sub_one_pos
  unfold qb rb; field_simp; ring

/-! ### The concave function `f` -/

/-- `f(s) = (r_b - 1) s - ln(e^s + 3) + ln(3 e^s + 1)`. -/
noncomputable def ff (s : ℝ) : ℝ := (rb - 1) * s - Real.log (Real.exp s + 3) + Real.log (3 * Real.exp s + 1)

theorem ff_zero : ff 0 = 0 := by
  simp only [ff, Real.exp_zero]; norm_num

/-- The derivative of `ff`. -/
noncomputable def ff' (s : ℝ) : ℝ :=
  (rb - 1) - Real.exp s / (Real.exp s + 3) + 3 * Real.exp s / (3 * Real.exp s + 1)

theorem hasDerivAt_ff (s : ℝ) : HasDerivAt ff (ff' s) s := by
  have h1 : HasDerivAt (fun s : ℝ => (rb - 1) * s) (rb - 1) s := by
    simpa using (hasDerivAt_id s).const_mul (rb - 1)
  have h2 : HasDerivAt (fun s => Real.log (Real.exp s + 3)) (Real.exp s / (Real.exp s + 3)) s :=
    ((Real.hasDerivAt_exp s).add_const 3).log (by positivity)
  have h3 : HasDerivAt (fun s => Real.log (3 * Real.exp s + 1)) (3 * Real.exp s / (3 * Real.exp s + 1)) s :=
    (((Real.hasDerivAt_exp s).const_mul 3).add_const 1).log (by positivity)
  exact (h1.sub h2).add h3

theorem ff_continuous : Continuous ff :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_ff s).continuousAt

theorem deriv_ff (s : ℝ) : deriv ff s = ff' s := (hasDerivAt_ff s).deriv

/-- `-t/(t+3) + 3t/(3t+1) = 8t/((t+3)(3t+1))`. -/
theorem ff'_eq (s : ℝ) : ff' s = (rb - 1) + 8 * Real.exp s / ((Real.exp s + 3) * (3 * Real.exp s + 1)) := by
  have h1 : 0 < Real.exp s := Real.exp_pos s
  unfold ff'
  field_simp
  ring

theorem kappa_anti {t t' : ℝ} (ht : 1 < t) (h : t < t') :
    8 * t' / ((t' + 3) * (3 * t' + 1)) < 8 * t / ((t + 3) * (3 * t + 1)) := by
  have h0 : 0 < t := by linarith
  have h1 : 0 < t' := by linarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos (sub_pos.mpr h) (sub_pos.mpr (show 1 < t * t' by nlinarith))]

theorem ff'_strictAnti : StrictAntiOn (deriv ff) (interior (Set.Ici (0 : ℝ))) := by
  rw [interior_Ici]
  intro x hx y hy hxy
  simp only [Set.mem_Ioi] at hx hy
  rw [deriv_ff, deriv_ff, ff'_eq, ff'_eq]
  have h1 : 1 < Real.exp x := by have := Real.exp_lt_exp.mpr hx; rwa [Real.exp_zero] at this
  have := kappa_anti h1 (Real.exp_lt_exp.mpr hxy)
  linarith

theorem ff_strictConcaveOn : StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) ff :=
  StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0) ff_continuous.continuousOn ff'_strictAnti

/-- If `f(s₀) ≤ 0` at some `s₀ > 0` then `f < 0` beyond `s₀` (strict concavity with `f(0) = 0`). -/
theorem ff_neg_beyond {s0 s : ℝ} (h0 : 0 < s0) (hf : ff s0 ≤ 0) (hs : s0 < s) : ff s < 0 := by
  have hs0 : 0 < s := by linarith
  have hp : 0 < s0 / s := div_pos h0 hs0
  have hc := ff_strictConcaveOn.2 (show (0 : ℝ) ∈ Set.Ici 0 from Set.mem_Ici.mpr le_rfl)
    (show s ∈ Set.Ici (0 : ℝ) from Set.mem_Ici.mpr hs0.le) (show (0 : ℝ) ≠ s by intro h; linarith)
    (show 0 < 1 - s0 / s by rw [sub_pos, div_lt_one hs0]; exact hs) hp (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, ff_zero] at hc
  have e : (1 - s0 / s) * 0 + s0 / s * s = s0 := by field_simp; ring
  have hc' : s0 / s * ff s < ff ((1 - s0 / s) * 0 + s0 / s * s) := by
    simpa [ff_zero] using hc
  rw [e] at hc'
  by_contra hneg
  push Not at hneg
  have := mul_nonneg hp.le hneg
  linarith


/-! ### The function `J` and its derivative -/

/-- `w(a) = a²(3 - 2a)`. -/
noncomputable def wf (a : ℝ) : ℝ := a ^ 2 * (3 - 2 * a)

/-- `J(a) = q_b (w ln a + (1-w) ln(1-a)) + h(w) + q_b a (1-a)`, `h` the binary entropy in nats. -/
noncomputable def Jf (a : ℝ) : ℝ :=
  qb * (wf a * Real.log a + (1 - wf a) * Real.log (1 - a)) + Real.binEntropy (wf a) + qb * a * (1 - a)

/-- `Φ(a) = q_b ln(a/(1-a)) - ln(w/(1-w))`, written without `w`. -/
noncomputable def Phi (a : ℝ) : ℝ :=
  (rb - 1) * (Real.log a - Real.log (1 - a)) - Real.log (3 - 2 * a) + Real.log (1 + 2 * a)

theorem Phi_eq_ff {a : ℝ} (h0 : 0 < a) (h1 : a < 1) : Phi a = ff (Real.log a - Real.log (1 - a)) := by
  have h1a : 0 < 1 - a := by linarith
  have h32 : 0 < 3 - 2 * a := by linarith
  have h12 : 0 < 1 + 2 * a := by linarith
  have he : Real.exp (Real.log a - Real.log (1 - a)) = a / (1 - a) := by
    rw [Real.exp_sub, Real.exp_log h0, Real.exp_log h1a]
  unfold ff Phi
  rw [he]
  have e1 : a / (1 - a) + 3 = (3 - 2 * a) / (1 - a) := by field_simp; ring
  have e2 : 3 * (a / (1 - a)) + 1 = (1 + 2 * a) / (1 - a) := by field_simp; ring
  rw [e1, e2, Real.log_div h32.ne' h1a.ne', Real.log_div h12.ne' h1a.ne']
  ring

theorem log_wf {a : ℝ} (h0 : 0 < a) (h1 : a < 1) : Real.log (wf a) = 2 * Real.log a + Real.log (3 - 2 * a) := by
  have h32 : 0 < 3 - 2 * a := by linarith
  unfold wf
  rw [Real.log_mul (by positivity) h32.ne', Real.log_pow]; push_cast; ring

theorem one_sub_wf (a : ℝ) : 1 - wf a = (1 - a) ^ 2 * (1 + 2 * a) := by unfold wf; ring

theorem log_one_sub_wf {a : ℝ} (h0 : 0 < a) (h1 : a < 1) :
    Real.log (1 - wf a) = 2 * Real.log (1 - a) + Real.log (1 + 2 * a) := by
  have h1a : 0 < 1 - a := by linarith
  have h12 : 0 < 1 + 2 * a := by linarith
  rw [one_sub_wf, Real.log_mul (by positivity) h12.ne', Real.log_pow]; push_cast; ring

theorem wf_pos {a : ℝ} (h0 : 0 < a) (h1 : a < 1) : 0 < wf a := by
  unfold wf; have : 0 < 3 - 2 * a := by linarith
  positivity

theorem wf_lt_one {a : ℝ} (h0 : 0 < a) (h1 : a < 1) : wf a < 1 := by
  have : 0 < 1 - wf a := by rw [one_sub_wf]; have : 0 < 1 - a := by linarith
                            have : 0 < 1 + 2 * a := by linarith
                            positivity
  linarith

theorem hasDerivAt_Jf {a : ℝ} (h0 : 0 < a) (h1 : a < 1) :
    HasDerivAt Jf (6 * a * (1 - a) * Phi a) a := by
  have h1a : 0 < 1 - a := by linarith
  have hw : HasDerivAt wf (6 * a * (1 - a)) a := by
    have h2 : HasDerivAt (fun a : ℝ => a ^ 2) (2 * a) a := by simpa using hasDerivAt_pow 2 a
    have h3 : HasDerivAt (fun a : ℝ => 3 - 2 * a) (-2) a := by
      simpa using ((hasDerivAt_id a).const_mul 2).const_sub 3
    exact (h2.mul h3).congr_deriv (by ring)
  have hl : HasDerivAt Real.log a⁻¹ a := Real.hasDerivAt_log h0.ne'
  have hl1 : HasDerivAt (fun a => Real.log (1 - a)) (-1 / (1 - a)) a := by
    simpa using (((hasDerivAt_id a).const_sub 1)).log h1a.ne'
  have hb : HasDerivAt (fun a => Real.binEntropy (wf a))
      ((Real.log (1 - wf a) - Real.log (wf a)) * (6 * a * (1 - a))) a :=
    ((Real.hasDerivAt_binEntropy (wf_pos h0 h1).ne' (wf_lt_one h0 h1).ne).comp a hw)
  have hq : HasDerivAt (fun a : ℝ => qb * a * (1 - a)) (qb * (1 - 2 * a)) a := by
    have := (((hasDerivAt_id a).const_mul qb).mul ((hasDerivAt_id a).const_sub 1))
    exact this.congr_deriv (by simp; ring)
  have hall := ((((hw.mul hl).add ((hw.const_sub 1).mul hl1)).const_mul qb).add hb).add hq
  refine hall.congr_deriv ?_
  rw [log_wf h0 h1, log_one_sub_wf h0 h1]
  unfold Phi wf
  rw [qb_eq_rb_add_one]
  have hne : a ≠ 0 := h0.ne'
  have hne2 : 1 - a ≠ 0 := h1a.ne'
  field_simp
  ring


theorem Jf_one : Jf 1 = 0 := by
  unfold Jf wf; norm_num

theorem Jf_zero : Jf 0 = 0 := by
  unfold Jf wf; simp

theorem Jf_half : Jf (1 / 2) = 0 := by
  have hw : wf (1 / 2) = 2⁻¹ := by unfold wf; norm_num
  have hlog : Real.log (1 / 2 : ℝ) = -Lg := by
    rw [one_div, Real.log_inv]; rfl
  have h1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have hq := four_Lg_sub_one_pos
  have hqL : qb * (4 * Lg - 1) = 4 * Lg := by unfold qb; field_simp
  unfold Jf
  rw [hw, h1, hlog]
  have : (1 : ℝ) - 2⁻¹ = 2⁻¹ := by norm_num
  rw [this, Real.binEntropy_two_inv]
  change qb * (2⁻¹ * -Lg + 2⁻¹ * -Lg) + Lg + qb * (1 / 2) * (1 / 2) = 0
  nlinarith

theorem Jf_symm (a : ℝ) : Jf (1 - a) = Jf a := by
  have hw : wf (1 - a) = 1 - wf a := by rw [one_sub_wf]; unfold wf; ring
  unfold Jf
  rw [hw, sub_sub_cancel, sub_sub_cancel, Real.binEntropy_one_sub]
  ring

theorem Jf_continuousOn : ContinuousOn Jf (Set.Ioc 0 1) := by
  have hfun : Jf = fun a => qb * (wf a * Real.log a + ((1 - a) * Real.log (1 - a)) * ((1 - a) * (1 + 2 * a)))
      + Real.binEntropy (wf a) + qb * a * (1 - a) := by
    funext a
    unfold Jf
    rw [one_sub_wf]; ring
  rw [hfun]
  have hw : Continuous wf := by unfold wf; fun_prop
  have hlog : ContinuousOn Real.log (Set.Ioc 0 1) :=
    Real.continuousOn_log.mono (fun x hx => ne_of_gt hx.1)
  have hml : Continuous fun x : ℝ => x * Real.log x := Real.continuous_mul_log
  have h2 : Continuous fun a : ℝ => ((1 - a) * Real.log (1 - a)) * ((1 - a) * (1 + 2 * a)) :=
    (hml.comp (continuous_const.sub continuous_id)).mul (by fun_prop)
  have hb : Continuous fun a => Real.binEntropy (wf a) := Real.binEntropy_continuous.comp hw
  refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.mul continuousOn_const ?_) hb.continuousOn)
    (by fun_prop)
  exact (hw.continuousOn.mul hlog).add h2.continuousOn

/-- **`J ≥ 0` on `[1/2, 1]`** (minimum principle). -/
theorem Jf_nonneg_right {a : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a ≤ 1) : 0 ≤ Jf a := by
  by_contra hneg
  push Not at hneg
  have hcont : ContinuousOn Jf (Set.Icc (1 / 2) 1) :=
    Jf_continuousOn.mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)
  obtain ⟨c, hc, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a, ⟨ha, ha1⟩⟩ hcont
  have hca : Jf c ≤ Jf a := hmin ⟨ha, ha1⟩
  have hcneg : Jf c < 0 := lt_of_le_of_lt hca hneg
  have hc2 : c ≠ 1 / 2 := fun h => by rw [h, Jf_half] at hcneg; exact lt_irrefl _ hcneg
  have hc1 : c ≠ 1 := fun h => by rw [h, Jf_one] at hcneg; exact lt_irrefl _ hcneg
  have hc2' : 1 / 2 < c := lt_of_le_of_ne hc.1 (Ne.symm hc2)
  have hc1' : c < 1 := lt_of_le_of_ne hc.2 hc1
  have hloc : IsLocalMin Jf c :=
    hmin.isLocalMin (Icc_mem_nhds hc2' hc1')
  have hder := hasDerivAt_Jf (show 0 < c by linarith) hc1'
  have hz := hloc.hasDerivAt_eq_zero hder
  have hPhi : Phi c = 0 := by
    have : 0 < 6 * c * (1 - c) := by
      have : 0 < 1 - c := by linarith
      positivity
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h this.ne'
    · exact h
  -- `J` is strictly decreasing on `[c, 1]`
  have hanti : StrictAntiOn Jf (Set.Icc c 1) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc c 1)
      (Jf_continuousOn.mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)) ?_
    intro x hx
    rw [interior_Icc] at hx
    obtain ⟨hxc, hx1⟩ := hx
    have hx0 : 0 < x := by linarith
    rw [(hasDerivAt_Jf hx0 hx1).deriv]
    have hs : 0 < Real.log c - Real.log (1 - c) := by
      rw [sub_pos]; exact Real.log_lt_log (by linarith) (by linarith)
    have hsx : Real.log c - Real.log (1 - c) < Real.log x - Real.log (1 - x) := by
      have h1 : Real.log c < Real.log x := Real.log_lt_log (by linarith) hxc
      have h2 : Real.log (1 - x) < Real.log (1 - c) := Real.log_lt_log (by linarith) (by linarith)
      linarith
    have hfc : ff (Real.log c - Real.log (1 - c)) ≤ 0 := by
      rw [← Phi_eq_ff (by linarith) hc1', hPhi]
    have := ff_neg_beyond hs hfc hsx
    rw [← Phi_eq_ff hx0 hx1] at this
    have : 0 < 6 * x * (1 - x) := by
      have : 0 < 1 - x := by linarith
      positivity
    nlinarith
  have := hanti ⟨le_refl c, hc1'.le⟩ ⟨hc1'.le, le_refl 1⟩ hc1'
  rw [Jf_one] at this
  linarith

/-- **`J ≥ 0` on `[0,1]`**: the analytic core of `lem:fqe-renyi-grouping` (`J(a) ≥ 0`). -/
theorem Jf_nonneg {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : 0 ≤ Jf a := by
  rcases le_total (1 / 2) a with h | h
  · exact Jf_nonneg_right h h1
  · rw [← Jf_symm]; exact Jf_nonneg_right (by linarith) (by linarith)

end FormalResearch.FourQubitEntropy.PaperECritical
