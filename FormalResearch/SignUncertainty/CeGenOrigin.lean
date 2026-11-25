module

public import FormalResearch.SignUncertainty.StripAdmissOrigin

/-!
# `cel:L3a` (2), the origin Mellin shift for the lift of an admissible strip multiplier (D1 / F2b leaf; `uct:gen-preedge` (2))

`ceOrigin_shift` is Lemma P.2 (2) of `ce_rate.tex` (`(cel:4.2)`, `(cel:4.5)`) in the single-strip form used by `uct:gen-preedge` (2) /
`(uct:gen-origin)` of `constant_terms_upper.tex`, for `J_c(z) = W̃(1 - z/c)` with `W̃` as in `uct:admiss`: with `G_c(iy) = 4^{-iy} Γ(iy)[E_c(iy) J_c(iy) - J_c(0)]`
(`ceOriginG`), `G_c ∈ L¹(ℝ)` and `f_W(Δ) - W̃(1) e^{-4Δ} = (2π)⁻¹ ∫ G_c(iy) Δ^{-iy} dy` for `Δ > 0`.  It is derived from `admiss_lift_eq_limit`
(shift with the pole `W̃(1)Γ(z)` removed, `StripAdmissOrigin`) and the new Mellin inversion
`integral_Gamma_mul_one_sub_four`: `(2π)⁻¹ ∫ Δ^{-iy} Γ(iy)(1 - 4^{-iy}) dy = e^{-Δ} - e^{-4Δ}`, proved from the Fubini representation
`mellin (e^{-t} - e^{-4t})(s) = Γ(s+1) ∫₁⁴ u^{-(s+1)} du` on `Re s > -1` (`mellin_expDiff`).

Class: proved, unconditional.  Not covered: the Dini modulus of the TeX (Hölder `|z|^α` only), multipliers `J_c` that are not of the form
`W̃(1 - z/c)` (the two-edge `W_S(c^{1/3} - c^{-2/3} z) + W_D(c^{-2/3} z)` of `PE3OriginData` and `thm:ce-post-edge`) and the symmetry `G_c(-iy) = conj G_c(iy)`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real


namespace FormalResearch.SignUncertainty

/-- `e^{-t} - e^{-4t}` as a complex-valued function. -/
noncomputable def expDiff (t : ℝ) : ℂ := ((Real.exp (-t) - Real.exp (-(4 * t)) : ℝ) : ℂ)

lemma expDiff_eq_integral {t : ℝ} :
    expDiff t = ∫ u in Icc (1 : ℝ) 4, ((t * Real.exp (-(u * t)) : ℝ) : ℂ) := by
  have h : ∫ u in Icc (1 : ℝ) 4, t * Real.exp (-(u * t)) = Real.exp (-t) - Real.exp (-(4 * t)) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 4)]
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u : ℝ => -Real.exp (-(u * t)))
      (f' := fun u : ℝ => t * Real.exp (-(u * t))) (a := 1) (b := 4) (fun u _ => by
        have h1 : HasDerivAt (fun u : ℝ => -(u * t)) (-t) u := by
          exact (((hasDerivAt_id' u).mul_const t).neg).congr_deriv (by ring)
        have := (h1.exp).neg
        convert this using 1; ring)
      (by
        apply Continuous.intervalIntegrable; fun_prop)
    rw [this]; simp; ring_nf
  rw [integral_complex_ofReal, h]; rfl


lemma cpow_ofReal_inv_pos {u : ℝ} (hu : 0 < u) (a : ℂ) : (1 / (u : ℂ)) ^ a = (u : ℂ) ^ (-a) := by
  rw [Complex.cpow_neg, one_div, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hu.le]; exact Real.pi_ne_zero.symm)]

/-- The integrand `t^s e^{-ut}` of the Fubini representation. -/
noncomputable def expDiffF (s : ℂ) (t u : ℝ) : ℂ := (t : ℂ) ^ s * ((Real.exp (-(u * t)) : ℝ) : ℂ)

lemma expDiffF_integrable {s : ℂ} (hs : -1 < s.re) :
    Integrable (Function.uncurry (expDiffF s)) ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Icc (1 : ℝ) 4))) := by
    have h1 : IntegrableOn (fun t : ℝ => t ^ s.re * Real.exp (-t)) (Ioi 0) := by
      have := Real.GammaIntegral_convergent (s := s.re + 1) (by linarith)
      refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp only [add_sub_cancel_right]; ring
    have h2 : Integrable (fun p : ℝ × ℝ => (p.1 ^ s.re * Real.exp (-p.1)) * (1 : ℝ))
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Icc (1 : ℝ) 4))) :=
      Integrable.mul_prod (f := fun t : ℝ => t ^ s.re * Real.exp (-t)) (g := fun _ : ℝ => (1 : ℝ)) h1
        (integrable_const (1 : ℝ))
    refine h2.mono' ?_ ?_
    · have hm : Measurable (Function.uncurry (expDiffF s)) := by
        refine Measurable.mul ?_ ?_
        · exact (Complex.measurable_ofReal.comp measurable_fst).pow_const s
        · exact Complex.measurable_ofReal.comp (Real.measurable_exp.comp ((measurable_snd.mul measurable_fst).neg))
      exact hm.aestronglyMeasurable
    · rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod (measurableSet_Icc (a := (1 : ℝ)) (b := 4)))] with p hp
      obtain ⟨hp1, hp2⟩ := hp
      have ht : 0 < p.1 := hp1
      simp only [Function.uncurry, expDiffF]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        Complex.norm_cpow_eq_rpow_re_of_pos ht, mul_one]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ht.le _)
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hp2.1]

lemma expDiff_mellin_integrand {s : ℂ} {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    (t : ℂ) ^ (s - 1) • expDiff t = ∫ u in Icc (1 : ℝ) 4, expDiffF s t u := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (mem_Ioi.mp ht).ne'
  have hcp : (t : ℂ) ^ s = (t : ℂ) ^ (s - 1) * t := by
    have := Complex.cpow_add (s - 1) 1 ht0
    rwa [sub_add_cancel, Complex.cpow_one] at this
  rw [expDiff_eq_integral, smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [expDiffF]
  rw [hcp]; push_cast; ring


/-- Mellin transform of `e^{-t} - e^{-4t}` on `Re s > -1`: `Γ(s+1) ∫₁⁴ u^{-(s+1)} du`. -/
lemma mellin_expDiff {s : ℂ} (hs : -1 < s.re) :
    mellin expDiff s = Complex.Gamma (s + 1) * ∫ u in Icc (1 : ℝ) 4, (u : ℂ) ^ (-(s + 1)) := by
  set F : ℝ → ℝ → ℂ := expDiffF s with hF
  have hstep : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • expDiff t = ∫ u in Icc (1 : ℝ) 4, F t u := fun t ht => expDiff_mellin_integrand ht
  have hint := expDiffF_integrable hs
  have hinner : ∀ u ∈ Icc (1 : ℝ) 4, ∫ t in Ioi (0 : ℝ), F t u = Complex.Gamma (s + 1) * (u : ℂ) ^ (-(s + 1)) := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := s + 1) (r := u) (by simp; linarith) hu0
    rw [add_sub_cancel_right] at this
    have e : ∀ t : ℝ, F t u = (t : ℂ) ^ s * Complex.exp (-((u : ℂ) * (t : ℂ))) := fun t => by
      simp only [hF, expDiffF]; push_cast; ring_nf
    simp_rw [e]
    rw [this, cpow_ofReal_inv_pos hu0, mul_comm]
  unfold mellin
  rw [setIntegral_congr_fun measurableSet_Ioi hstep, integral_integral_swap hint,
    setIntegral_congr_fun measurableSet_Icc hinner, integral_const_mul]


lemma mellinConvergent_expDiff {s : ℂ} (hs : -1 < s.re) : MellinConvergent expDiff s := by
  have h := (expDiffF_integrable hs).integral_prod_left
  refine h.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  simp only [Function.uncurry]
  exact (expDiff_mellin_integrand ht).symm

/-- `m(y) = Γ(1 + iy) ∫₁⁴ u^{-(1+iy)} du`, the Mellin transform of `e^{-t} - e^{-4t}` on the imaginary axis. -/
noncomputable def expDiffM (y : ℝ) : ℂ :=
  Complex.Gamma (1 + (y : ℂ) * Complex.I) * ∫ u in Icc (1 : ℝ) 4, (u : ℂ) ^ (-(1 + (y : ℂ) * Complex.I))

lemma expDiffM_eq (y : ℝ) : mellin expDiff (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I) = expDiffM y := by
  rw [mellin_expDiff (by simp)]
  have e : ((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I + 1 = 1 + (y : ℂ) * Complex.I := by push_cast; ring
  rw [e]; rfl

lemma expDiffM_eq_Gamma {y : ℝ} (hy : y ≠ 0) :
    expDiffM y = Complex.Gamma ((y : ℂ) * Complex.I) * (1 - (4 : ℂ) ^ (-((y : ℂ) * Complex.I))) := by
  set z : ℂ := (y : ℂ) * Complex.I with hz
  have hz0 : z ≠ 0 := by
    intro h; apply hy; have := congrArg Complex.im h; simpa [hz] using this
  have h1 : ∫ u in Icc (1 : ℝ) 4, (u : ℂ) ^ (-(1 + z)) = (1 - (4 : ℂ) ^ (-z)) / z := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 4)]
    have hr : -(1 + z) ≠ -1 := fun h => hz0 (by linear_combination -h)
    rw [integral_cpow (Or.inr ⟨hr, by
      rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 4)]; intro h; linarith [h.1]⟩)]
    have e : -(1 + z) + 1 = -z := by ring
    rw [e, Complex.ofReal_one, Complex.one_cpow]
    push_cast
    have : (-z) ≠ 0 := neg_ne_zero.mpr hz0
    field_simp
    ring
  have h2 : Complex.Gamma (1 + z) = z * Complex.Gamma z := by
    rw [add_comm, Complex.Gamma_add_one z hz0]
  simp only [expDiffM]
  rw [h1, h2]
  field_simp


lemma integrable_expDiffM : Integrable expDiffM := by
  obtain ⟨B, hB⟩ := Gamma_decay_strip (a := 1) (b := 1) one_pos le_rfl
  have hmeas : AEStronglyMeasurable expDiffM volume := by
    have h1 : Measurable fun y : ℝ => Complex.Gamma (1 + (y : ℂ) * Complex.I) := by
      have := continuous_Gamma_line 1 one_pos
      simpa using this.measurable
    have h2 : StronglyMeasurable fun y : ℝ => ∫ u in Icc (1 : ℝ) 4, (u : ℂ) ^ (-(1 + (y : ℂ) * Complex.I)) := by
      have hm : Measurable (fun p : ℝ × ℝ => (p.2 : ℂ) ^ (-(1 + (p.1 : ℂ) * Complex.I))) := by
        refine Measurable.pow (Complex.measurable_ofReal.comp measurable_snd) ?_
        exact ((measurable_const.add (Complex.measurable_ofReal.comp measurable_fst |>.mul measurable_const))).neg
      exact (hm.stronglyMeasurable).integral_prod_right' (ν := volume.restrict (Icc (1 : ℝ) 4))
    exact (h1.stronglyMeasurable.mul h2).aestronglyMeasurable
  refine (integrable_inv_one_add_sq.const_mul (4 * (|B| * 3))).mono' hmeas (Eventually.of_forall fun y => ?_)
  have hG := hB (1 + (y : ℂ) * Complex.I) (by simp) (by simp)
  simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at hG
  have hI : ‖∫ u in Icc (1 : ℝ) 4, (u : ℂ) ^ (-(1 + (y : ℂ) * Complex.I))‖ ≤ 3 := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (1 : ℝ) 4) (by simp)
      (f := fun u : ℝ => (u : ℂ) ^ (-(1 + (y : ℂ) * Complex.I))) (C := 1) (fun u hu => by
        have hu0 : 0 < u := by linarith [hu.1]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0]
        simp only [Complex.neg_re, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, neg_add_rev, neg_zero]
        exact Real.rpow_le_one_of_one_le_of_nonpos hu.1 (by norm_num))
    simpa [Measure.real, Real.volume_Icc] using this.trans (by norm_num)
  have hw : (1 + |y|) ^ (-(2 : ℝ)) ≤ (1 + y ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
    apply inv_anti₀ (by positivity)
    nlinarith [sq_abs y, abs_nonneg y]
  calc ‖expDiffM y‖ = ‖Complex.Gamma (1 + (y : ℂ) * Complex.I)‖ * ‖∫ u in Icc (1 : ℝ) 4, (u : ℂ) ^ (-(1 + (y : ℂ) * Complex.I))‖ :=
        norm_mul _ _
    _ ≤ (B * (1 + |y|) ^ (-(2 : ℝ))) * 3 :=
        mul_le_mul hG hI (norm_nonneg _) ((norm_nonneg _).trans hG)
    _ ≤ (|B| * (1 + y ^ 2)⁻¹) * 3 := by
        gcongr
        · exact le_abs_self B
    _ ≤ 4 * (|B| * 3) * (1 + y ^ 2)⁻¹ := by
        have : 0 ≤ |B| * 3 * (1 + y ^ 2)⁻¹ := by positivity
        nlinarith


/-- `y ↦ Γ(iy)(1 - 4^{-iy})` is integrable on `ℝ`. -/
theorem integrable_Gamma_mul_one_sub_four :
    Integrable fun y : ℝ => Complex.Gamma ((y : ℂ) * Complex.I) * (1 - (4 : ℂ) ^ (-((y : ℂ) * Complex.I))) := by
  refine integrable_expDiffM.congr ?_
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with y hy
  exact expDiffM_eq_Gamma hy

/-- **Mellin inversion of `Γ(z)(1 - 4^{-z})` on `Re z = 0`:**
`(2π)⁻¹ ∫ Δ^{-iy} Γ(iy)(1 - 4^{-iy}) dy = e^{-Δ} - e^{-4Δ}` for `Δ > 0`. -/
theorem integral_Gamma_mul_one_sub_four {Δ : ℝ} (hΔ : 0 < Δ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) *
        (Complex.Gamma ((y : ℂ) * Complex.I) * (1 - (4 : ℂ) ^ (-((y : ℂ) * Complex.I)))) =
      ((Real.exp (-Δ) - Real.exp (-(4 * Δ)) : ℝ) : ℂ) := by
  have hvert : Complex.VerticalIntegrable (mellin expDiff) 0 := by
    unfold Complex.VerticalIntegrable
    refine integrable_expDiffM.congr (Eventually.of_forall fun y => ?_)
    simp only
    rw [expDiffM_eq]
  have hcont : ContinuousAt expDiff Δ := by
    unfold expDiff; fun_prop
  have h := mellinInv_mellin_eq 0 expDiff hΔ (mellinConvergent_expDiff (by simp)) hvert hcont
  unfold mellinInv at h
  rw [Complex.real_smul] at h
  have e : ∫ y : ℝ, (Δ : ℂ) ^ (-(((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) • mellin expDiff (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
      ∫ y : ℝ, (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) *
        (Complex.Gamma ((y : ℂ) * Complex.I) * (1 - (4 : ℂ) ^ (-((y : ℂ) * Complex.I)))) := by
    refine integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with y hy
    rw [expDiffM_eq, expDiffM_eq_Gamma hy, smul_eq_mul]
    simp
  rw [e] at h
  exact h


/-! ### The origin shift for the lift of an admissible strip multiplier -/

open FormalResearch.CohnElkies

/-- `E_c(z) = exp(c ℋ(z/c) - z log(π/2))` (Lemma P.2, `cel:L3a`). -/
noncomputable def ceOriginE (c : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((c : ℂ) * stripH (z / (c : ℂ)) - z * ((Real.log (Real.pi / 2) : ℝ) : ℂ))

/-- `G_c(iy) = 4^{-iy} Γ(iy) [E_c(iy) J_c(iy) - J_c(0)]` with `J_c(z) = W̃(1 - z/c)` (`(cel:4.2)`). -/
noncomputable def ceOriginG (c : ℝ) (W : ℂ → ℂ) (y : ℝ) : ℂ :=
  (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) * Complex.Gamma ((y : ℂ) * Complex.I) *
    (ceOriginE c ((y : ℂ) * Complex.I) * W (1 - ((y : ℂ) * Complex.I) / (c : ℂ)) - W 1)

lemma four_cpow_mul_ceOriginE {c : ℝ} (hc : 0 < c) {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re < c) :
    (4 : ℂ) ^ (-z) * ceOriginE c z = admissEhat c z := by
  have hre0 : 0 ≤ (z / (c : ℂ)).re := by rw [Complex.div_ofReal_re]; positivity
  have hre1 : (z / (c : ℂ)).re < 1 := by rw [Complex.div_ofReal_re]; exact (div_lt_one hc).mpr hz1
  unfold ceOriginE admissEhat
  rw [← hInt_eq_stripH hre0 hre1]
  have h4 : (4 : ℂ) ^ (-z) = Complex.exp (-z * ((Real.log 4 : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num), show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num)]
    ring_nf
  have h2 : ((2 * Real.pi : ℝ) : ℂ) ^ (-z) = Complex.exp (-z * ((Real.log (2 * Real.pi) : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)),
      ← Complex.ofReal_log (by positivity)]
    ring_nf
  have hl : Real.log (2 * Real.pi) = Real.log 4 + Real.log (Real.pi / 2) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
  rw [h4, h2, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [hl]
  push_cast
  ring


section
variable {W : ℂ → ℂ}

/-- The pointwise limit `Γ(ε + iy) K(ε + iy) → Γ(iy) K(iy)` as `ε ↓ 0` (`y ≠ 0`). -/
lemma tendsto_Gamma_mul_admissK {c : ℝ} (hc : 0 < c) (hW : StripM1 W) {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun ε : ℝ => Complex.Gamma ((ε : ℂ) + (y : ℂ) * Complex.I) * admissK c W ((ε : ℂ) + (y : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 (Complex.Gamma ((y : ℂ) * Complex.I) * admissK c W ((y : ℂ) * Complex.I))) := by
  set z0 : ℂ := (y : ℂ) * Complex.I with hz0
  have hz0re : z0.re = 0 := by simp [hz0]
  have hz0ne : z0 ≠ 0 := by
    intro h; apply hy; have := congrArg Complex.im h; simpa [hz0] using this
  have hGc : ContinuousAt Complex.Gamma z0 := continuousAt_Gamma_of_re_nonneg hz0re.ge hz0ne
  have hKc := admissK_continuousOn hc hW z0 ⟨hz0re.ge, by rw [hz0re]; exact hc.le⟩
  have hcw : ContinuousWithinAt (fun z : ℂ => Complex.Gamma z * admissK c W z)
      {z : ℂ | 0 ≤ z.re ∧ z.re ≤ c} z0 := hGc.continuousWithinAt.mul hKc
  have hz : Tendsto (fun ε : ℝ => (ε : ℂ) + (y : ℂ) * Complex.I) (𝓝[>] (0 : ℝ))
      (𝓝[{z : ℂ | 0 ≤ z.re ∧ z.re ≤ c}] z0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun ε : ℝ => (ε : ℂ) + (y : ℂ) * Complex.I) (𝓝 (0 : ℝ)) (𝓝 (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) :=
        (by fun_prop : Continuous fun ε : ℝ => (ε : ℂ) + (y : ℂ) * Complex.I).continuousAt.tendsto
      simpa [hz0] using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT hc] with ε hε
      exact ⟨by simp; exact hε.1.le, by simp; exact hε.2.le⟩
  exact hcw.tendsto.comp hz

/-- `Γ(iy) K(iy)` is integrable. -/
theorem integrable_Gamma_mul_admissK {c α : ℝ} (hc : 2 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) (hW : StripM1 W)
    (hH : ∃ CH : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖1 - ζ‖ ≤ 1 / 2 → ‖W ζ - W 1‖ ≤ CH * ‖1 - ζ‖ ^ α) :
    Integrable fun y : ℝ => Complex.Gamma ((y : ℂ) * Complex.I) * admissK c W ((y : ℂ) * Complex.I) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨A, hA0, hA⟩ := admissRem_line_bound hc hα0 hα1 hW hH
  have hmeas : AEStronglyMeasurable (fun y : ℝ => Complex.Gamma ((y : ℂ) * Complex.I) * admissK c W ((y : ℂ) * Complex.I)) volume := by
    have hf : Continuous fun y : ℝ => (y : ℂ) * Complex.I := by fun_prop
    have hK : Continuous fun y : ℝ => admissK c W ((y : ℂ) * Complex.I) :=
      (admissK_continuousOn hc0 hW).comp_continuous hf (fun y => ⟨by simp, by simp; exact hc0.le⟩)
    have hcont : ContinuousOn (fun y : ℝ => Complex.Gamma ((y : ℂ) * Complex.I) * admissK c W ((y : ℂ) * Complex.I)) {y : ℝ | y ≠ 0} := by
      intro y hy
      have hz0ne : ((y : ℂ) * Complex.I) ≠ 0 := by
        intro h; apply hy; have := congrArg Complex.im h; simpa using this
      have hG : ContinuousAt Complex.Gamma ((y : ℂ) * Complex.I) := continuousAt_Gamma_of_re_nonneg (by simp) hz0ne
      exact ((hG.comp_of_eq hf.continuousAt rfl).mul hK.continuousAt).continuousWithinAt
    have := hcont.aestronglyMeasurable (μ := volume) (isOpen_compl_singleton.measurableSet)
    rwa [show {y : ℝ | y ≠ 0} = {(0 : ℝ)}ᶜ from rfl, restrict_compl_singleton] at this
  have hbd : ∀ y : ℝ, y ≠ 0 → ‖Complex.Gamma ((y : ℂ) * Complex.I) * admissK c W ((y : ℂ) * Complex.I)‖ ≤ A * originMajorant α y := by
    intro y hy
    have hlim := (tendsto_Gamma_mul_admissK hc0 hW hy).norm
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2), Ioo_mem_nhdsGT hc0] with ε hε hε'
    have hre0 : 0 < ((ε : ℂ) + (y : ℂ) * Complex.I).re := by simpa using hε.1
    have hre1 : ((ε : ℂ) + (y : ℂ) * Complex.I).re < c := by simpa using hε'.2
    rw [← admissRem_eq hc0 hre0 hre1]
    exact hA ε y hε.1 hε.2.le hy
  refine ((integrable_originMajorant hα0).const_mul A).mono' hmeas ?_
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with y hy
  exact hbd y hy


lemma integrable_cpow_mul {Δ : ℝ} (hΔ : 0 < Δ) {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable fun y : ℝ => (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) * g y := by
  have hc : Continuous fun y : ℝ => (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) :=
    Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hΔ.ne'))
  refine hg.norm.mono' (hc.aestronglyMeasurable.mul hg.1) (Eventually.of_forall fun y => ?_)
  rw [norm_mul]
  have : ‖(Δ : ℂ) ^ (-((y : ℂ) * Complex.I))‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hΔ]; simp
  rw [this, one_mul]

lemma ceOriginG_decomp {c : ℝ} (hc : 0 < c) (W : ℂ → ℂ) (y : ℝ) :
    ceOriginG c W y = Complex.Gamma ((y : ℂ) * Complex.I) * admissK c W ((y : ℂ) * Complex.I) +
      W 1 * (Complex.Gamma ((y : ℂ) * Complex.I) * (1 - (4 : ℂ) ^ (-((y : ℂ) * Complex.I)))) := by
  have h := four_cpow_mul_ceOriginE hc (z := (y : ℂ) * Complex.I) (by simp) (by simpa using hc)
  unfold ceOriginG admissK
  rw [← h]
  ring

/-- **`cel:L3a` (2) / `uct:gen-origin` for the lift of an admissible strip multiplier** (`(cel:4.2)`, `(cel:4.5)`, `(uct:gen-origin)`):
for `c ≥ 2`, `W̃` with the hypotheses `StripM1` and the Hölder bound `|W̃(ζ) - W̃(1)| ≤ C |1 - ζ|^α` at `ζ = 1` (this is `J_c(z) - J_c(0) = O(|z|^α)`,
`J_c(z) = W̃(1 - z/c)`; `α = 1/2` is the case used by `uct:gen-preedge` (2)), `G_c(iy) = 4^{-iy} Γ(iy)[E_c(iy) J_c(iy) - J_c(0)]` is integrable on `ℝ` and, for every `Δ > 0`,
`f_W(Δ) - W̃(1) e^{-4Δ} = (2π)⁻¹ ∫ G_c(iy) Δ^{-iy} dy`, where `f_W = admissLift c W` is the lift (`ĥ_c`).  Class: proved.  Not included: the more general Dini modulus
`ω_c` of the TeX, multipliers `J_c` that are not of the form `W̃(1 - z/c)` (e.g. the two-edge `W_S(c^{1/3} - c^{-2/3}z) + W_D(c^{-2/3}z)`), and `G_c(-iy) = conj G_c(iy)`. -/
theorem ceOrigin_shift {c α : ℝ} (hc : 2 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) {W : ℂ → ℂ} (hW : StripM1 W)
    (hH : ∃ CH : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖1 - ζ‖ ≤ 1 / 2 → ‖W ζ - W 1‖ ≤ CH * ‖1 - ζ‖ ^ α) :
    Integrable (ceOriginG c W) ∧ ∀ {Δ : ℝ}, 0 < Δ →
      ((admissLift c W Δ : ℝ) : ℂ) - W 1 * ((Real.exp (-(4 * Δ)) : ℝ) : ℂ) =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, ceOriginG c W y * (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) := by
  have hc0 : 0 < c := by linarith
  have hρ := integrable_Gamma_mul_admissK hc hα0 hα1 hW hH
  have hm := integrable_Gamma_mul_one_sub_four
  have hint : Integrable (ceOriginG c W) := by
    have := hρ.add (hm.const_mul (W 1))
    exact this.congr (Eventually.of_forall fun y => (ceOriginG_decomp hc0 W y).symm)
  refine ⟨hint, fun {Δ} hΔ => ?_⟩
  have h1 := admiss_lift_eq_limit hc hα0 hα1 hW hH hΔ
  have h2 := integral_Gamma_mul_one_sub_four hΔ
  have e : ∫ y : ℝ, ceOriginG c W y * (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) =
      (∫ y : ℝ, originLimit c W Δ y) + W 1 * ∫ y : ℝ, (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) *
        (Complex.Gamma ((y : ℂ) * Complex.I) * (1 - (4 : ℂ) ^ (-((y : ℂ) * Complex.I)))) := by
    rw [← integral_const_mul]
    have hs := integral_add (integrable_cpow_mul hΔ hρ) ((integrable_cpow_mul hΔ hm).const_mul (W 1))
    simp only [originLimit]
    rw [← hs]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [ceOriginG_decomp hc0 W y]
    ring
  rw [e, mul_add, ← mul_assoc, mul_comm ((1 / (2 * Real.pi) : ℝ) : ℂ) (W 1), mul_assoc, h2]
  rw [h1]
  push_cast
  ring_nf

end


/-- info: 'FormalResearch.SignUncertainty.integral_Gamma_mul_one_sub_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_Gamma_mul_one_sub_four

/-- info: 'FormalResearch.SignUncertainty.ceOrigin_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceOrigin_shift

end FormalResearch.SignUncertainty
