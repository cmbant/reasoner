module

public import Mathlib
public import FormalResearch.SignUncertainty.CtRoscPos

/-!
# `ct:dyadic` (4), `(ct:rosc)`: the exact algebra of `CtRoscBook` and the edge strip of `s₂` (piece `T6`)

`constant_terms_lower.tex`, `ct:dyadic` (4).  With `T(u) = w_R(|u|) = 1 - W₆(u)` on `[-R, R]` and `s₂^{lit} = ∫_0^R w_R(v) f_c(-v) sin((4/3)v^{3/2}) dv`
(the literal integral through the complex chart),

`budget + M_all + 2(s₁ - s₂^L) - ctRoscAiry = ∫_{-R}^R (1 - T) f_c - ε f(0) + M_all + 2(s₂^{lit} - s₂^L)`   (`ctRosc_alg`),

by the node sum (`ctBudget_nodes`, `T1`) and `ctW6(-v) = 1 - w_R(v)`.  The difference `s₂^{lit} - s₂^L` is the edge strip `v ∈ (0, -û(0⁻))`, `O((λM/R)^{12})` (`slit_edge`, `T6`).

All proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- The literal `s₂ = ∫_0^R w_R(v) f_c(-v) sin((4/3) v^{3/2}) dv` through the complex chart. -/
noncomputable def ctOscS2Lit (R ε c : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ v in Ioo 0 R, taperW R v * ((ctFcC ctChartC1 ε c f (-(v : ℂ))).re * Real.sin (4 / 3 * v ^ (3 / 2 : ℝ)))

/-- `W₆(x) = 1 - w_R(|x|)` for `|x| ≤ R`. -/
lemma ctW6_ofReal {R x : ℝ} (hR : 0 < R) (hx : |x| ≤ R) : ctW6 R (x : ℂ) = ((1 - taperW R |x| : ℝ) : ℂ) := by
  have h1 : max 0 (min |x| R) = |x| := by rw [min_eq_left hx, max_eq_right (abs_nonneg x)]
  have h2 : (|x| / R) ^ 12 = (x / R) ^ 12 := by
    have : |x| / R = |x / R| := by rw [abs_div, abs_of_pos hR]
    rw [this]
    exact Even.pow_abs ⟨6, by norm_num⟩ _
  unfold ctW6 taperW taperX
  rw [h1, h2]
  push_cast
  ring

lemma ctW6_neg_ofReal {R v : ℝ} (hR : 0 < R) (hv0 : 0 ≤ v) (hv : v ≤ R) :
    ctW6 R (-(v : ℂ)) = ((1 - taperW R v : ℝ) : ℂ) := by
  have h := ctW6_ofReal hR (x := -v) (by rw [abs_neg, abs_of_nonneg hv0]; exact hv)
  rw [abs_neg, abs_of_nonneg hv0] at h
  simpa using h

namespace CtRoscCtx

variable {ε c C ρ M R : ℝ} {f : ℝ → ℝ}

/-- `v ↦ Re f_c(-v)` is continuous on `[0, R]`. -/
lemma continuousOn_negF (X : CtRoscCtx ε c C ρ M f) (hRm : R ≤ ctRmax ctChartC1 c) (hR0 : 0 < R) :
    ContinuousOn (fun v : ℝ => (ctFcC ctChartC1 ε c f (-(v : ℂ))).re) (Icc 0 R) := by
  have h1 : ContinuousOn (fun v : ℝ => ctFcC ctChartC1 ε c f ((-v : ℝ) : ℂ)) (Icc 0 R) := by
    refine X.cont.comp continuous_neg.continuousOn (fun v hv => ?_)
    exact ⟨by linarith [hv.2, X.H.Rm_pos], by linarith [hv.1, X.H.Rm_pos]⟩
  exact (Complex.continuous_re.comp_continuousOn h1).congr (fun v _ => by simp)

/-- **The exact algebra of `CtRoscBook`**. -/
lemma ctRosc_alg (X : CtRoscCtx ε c C ρ M f) (hR1 : 1 < R) (hRm : R ≤ ctRmax ctChartC1 c) {N : ℕ}
    (hN : ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -FormalResearch.Special.airyZero n < R)) :
    ((ctBudget R ε c f + ctMall R ε c f + 2 * (ctOscS1 R ε c f - ctOscS2 R ε c f) : ℝ) : ℂ) -
        ctRoscAiry R ε c f N =
      (((∫ u in Ioo (-R) R, (1 - taperW R |u|) * ctFr ε c f u) - ε * f 0 + ctMall R ε c f +
        2 * (ctOscS2Lit R ε c f - ctOscS2 R ε c f) : ℝ) : ℂ) := by
  have hR0 : 0 < R := by linarith
  have hnodes := ctBudget_nodes (f := f) X.H X.W hRm hN
  -- the complex integral
  have hI : (∫ x in (-R)..R, ctW6 R (x : ℂ) * ctFcC ctChartC1 ε c f (x : ℂ)) =
      (((∫ u in Ioo (-R) R, (1 - taperW R |u|) * ctFr ε c f u : ℝ)) : ℂ) := by
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have hu' : |u| < R := abs_lt.2 ⟨hu.1, hu.2⟩
    rw [ctW6_ofReal hR0 hu'.le, X.H.ctFcC_ofReal (hu'.trans_le hRm)]
    push_cast; rfl
  -- the oscillatory integral
  have hJ : (∫ v in (0 : ℝ)..R, (ctW6 R (-(v : ℂ)) * ctFcC ctChartC1 ε c f (-(v : ℂ))).re *
        Real.sin (4 / 3 * v ^ (3 / 2 : ℝ))) = ctOscS1 R ε c f - ctOscS2Lit R ε c f := by
    have hsin : Continuous (fun v : ℝ => Real.sin (4 / 3 * v ^ (3 / 2 : ℝ))) :=
      Real.continuous_sin.comp (continuous_const.mul (Real.continuous_rpow_const (by norm_num)))
    have hF := X.continuousOn_negF hRm hR0
    have hFs : ContinuousOn (fun v : ℝ => (ctFcC ctChartC1 ε c f (-(v : ℂ))).re * Real.sin (4 / 3 * v ^ (3 / 2 : ℝ))) (Icc 0 R) :=
      hF.mul hsin.continuousOn
    have hT : Continuous (taperW R) := by unfold taperW taperX; fun_prop
    have hTs : ContinuousOn (fun v : ℝ => taperW R v *
        ((ctFcC ctChartC1 ε c f (-(v : ℂ))).re * Real.sin (4 / 3 * v ^ (3 / 2 : ℝ)))) (Icc 0 R) :=
      hT.continuousOn.mul hFs
    have i1 := (hFs.integrableOn_Icc (μ := volume)).mono_set (Ioo_subset_Icc_self : Ioo 0 R ⊆ Icc 0 R)
    have i2 := (hTs.integrableOn_Icc (μ := volume)).mono_set (Ioo_subset_Icc_self : Ioo 0 R ⊆ Icc 0 R)
    rw [intervalIntegral.integral_of_le hR0.le, integral_Ioc_eq_integral_Ioo]
    unfold ctOscS1 ctOscS2Lit
    rw [← integral_sub i1 i2]
    refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
    rw [ctW6_neg_ofReal hR0 hv.1.le hv.2.le, Complex.re_ofReal_mul]
    ring
  unfold ctRoscAiry
  rw [hI, hJ, ← hnodes]
  push_cast
  ring

/-- **The edge strip of `s₂`** (`T6`): `|s₂^{lit} - s₂^L| ≤ 2(λM/R)^{12}(1 + 2 A r_∞)`. -/
lemma slit_edge (X : CtRoscCtx ε c C ρ M f) (hR1 : 1 < R) (hRm : R ≤ ctRmax ctChartC1 c) :
    |ctOscS2Lit R ε c f - ctOscS2 R ε c f| ≤
      2 * (ctLam c * M / R) ^ 12 * (1 + 2 * langerRadius c * hankelRinf c) := by
  have hc0 := X.c_pos
  have hR0 : 0 < R := by linarith
  set δ := ctLam c * M with hδ
  have hδ0 : 0 ≤ δ := mul_nonneg (ctLam_pos hc0).le X.W.win.2.1
  set g : ℝ → ℝ := fun u => taperW R (-u) * (ctFr ε c f u * Real.sin (4 / 3 * (-u) ^ (3 / 2 : ℝ))) with hg
  have hT : Continuous (taperW R) := by unfold taperW taperX; fun_prop
  have hmeas : AEStronglyMeasurable (fun u : ℝ => taperW R (-u) * Real.sin (4 / 3 * (-u) ^ (3 / 2 : ℝ))) volume := by
    refine Measurable.aestronglyMeasurable ?_
    exact (hT.measurable.comp measurable_neg).mul
      (Real.measurable_sin.comp ((measurable_neg.pow_const _).const_mul _))
  have hint : IntegrableOn g (Ioo (-R) 0) := by
    have := (X.integrableOn_ctFr (a := -R) (b := 0) (by linarith) (by linarith [X.H.Rm_pos])).bdd_mul (c := 1)
      hmeas.restrict (Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (taperW_nonneg hR0 _)]
        calc taperW R (-u) * |Real.sin (4 / 3 * (-u) ^ (3 / 2 : ℝ))| ≤ 1 * 1 :=
              mul_le_mul (taperW_le_one hR0 _) (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1)
    refine Integrable.congr this (ae_restrict_of_forall_mem measurableSet_Ioo fun u _ => ?_)
    simp only [hg]; ring
  -- reflection `v = -u`
  have hrefl : ctOscS2Lit R ε c f = ∫ u in Ioo (-R) 0, g u := by
    calc ctOscS2Lit R ε c f = ∫ v in Ioo 0 R, g (-v) := by
          unfold ctOscS2Lit
          refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
          have hlt : |-v| < ctRmax ctChartC1 c := by
            rw [abs_neg, abs_of_pos hv.1]; linarith [hv.2]
          simp only [hg, neg_neg]
          have := X.H.ctFcC_re (f := f) hlt
          push_cast at this
          rw [this]
      _ = ∫ v in (0 : ℝ)..R, g (-v) := by
          rw [intervalIntegral.integral_of_le hR0.le, integral_Ioc_eq_integral_Ioo]
      _ = ∫ u in (-R)..(-0), g u := intervalIntegral.integral_comp_neg g
      _ = ∫ u in Ioo (-R) 0, g u := by
          rw [neg_zero, intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
  have e2 := X.neg_decomp hR1 hRm hint
  have hsub : ∫ x in Ioo (-ctRprime ε c R) 0, ctUhatD ε c x * g (ctUhat ε c x) = ctOscS2 R ε c f := by
    unfold ctOscS2
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    simp only [hg]
    rw [← ctFr_ctUhat X.H X.W f hR1 hRm hx]; ring
  have hstrip : ∫ u in Ioo (-δ) 0, |g u| ≤ 2 * (δ / R) ^ 12 * (1 + 2 * langerRadius c * hankelRinf c) := by
    refine X.strip_le hR1 hRm (by positivity) fun u hu => ?_
    simp only [hg]
    rw [abs_mul, abs_mul, abs_of_nonneg (taperW_nonneg hR0 _)]
    have hK : taperW R (-u) ≤ 2 * (δ / R) ^ 12 := by
      refine (taperW_le_pow hR0 (by linarith [hu.2] : 0 ≤ -u)).trans ?_
      have : (-u / R) ≤ δ / R := div_le_div_of_nonneg_right (by linarith [hu.1]) hR0.le
      have h0 : 0 ≤ -u / R := div_nonneg (by linarith [hu.2]) hR0.le
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 this 12) (by norm_num)
    calc taperW R (-u) * (|ctFr ε c f u| * |Real.sin (4 / 3 * (-u) ^ (3 / 2 : ℝ))|)
        ≤ (2 * (δ / R) ^ 12) * (|ctFr ε c f u| * 1) := by
          refine mul_le_mul hK ?_ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
      _ = 2 * (δ / R) ^ 12 * |ctFr ε c f u| := by ring
  rw [hrefl, ← hsub]
  exact e2.trans hstrip

end CtRoscCtx

end FormalResearch.SignUncertainty
