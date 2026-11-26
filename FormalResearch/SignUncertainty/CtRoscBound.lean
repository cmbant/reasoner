module

public import Mathlib
public import FormalResearch.SignUncertainty.CtRoscAlg
public import FormalResearch.SignUncertainty.CtRoscRates
public import FormalResearch.SignUncertainty.CtDyadicTaperBuild

/-!
# `ct:dyadic` (4), `(ct:rosc)`: the deterministic bound of `CtRoscBook` at one `c`

`constant_terms_lower.tex`, `ct:dyadic` (4).  Collects `ct_rosc_mass` (mass identity, `T2`-`T5`), `pos_lobe_le` (positive lobe, `T5`, cut `u₁ = R c^{-1/9}`) and `slit_edge` (edge strip, `T6`)
and absorbs the error terms into `10 c^{-4/3}` given the rate hypotheses `rosc_rates_hyp` (consequences of the `c → ∞` rates of `CtRoscRates`).

All proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- The `c`-dependent numerical hypotheses of `ctRosc_bound` (all hold for `c` large, `CtRoscRates`). -/
structure RoscRates (c₁ C M c : ℝ) : Prop where
  c1 : 1 ≤ c
  Ar : 3 * (langerRadius c * hankelRinf c) ≤ c ^ (-(4 / 3) : ℝ)
  Ar2 : 2 * langerRadius c * hankelRinf c ≤ 1
  exp_lin : 16 * Real.exp (-(1 / 25) * c) ≤ c ^ (-(4 / 3) : ℝ)
  exp_pow : 16 * Real.exp (-(5 * (langerLobeK * c₁ ^ 2 / 2) ^ (3 / 2 : ℝ)) * c ^ (5 / 6 : ℝ)) ≤ c ^ (-(4 / 3) : ℝ)
  strip : 8 * ((M / c₁ ^ 2) * c⁻¹) ^ 12 ≤ c ^ (-(4 / 3) : ℝ)
  lobe_one : 1 ≤ (langerLobeK * c₁ ^ 2 / 2) * c ^ (5 / 9 : ℝ)
  C_small : 2 * C * c ^ (-(1 / 3) : ℝ) ≤ c₁ ^ 2 * c ^ (5 / 9 : ℝ)

/-- **The bound of `CtRoscBook` at one `c`**: `|∫_{-R}^R W₆ f_c - ε f(0) + M_all + 2(s₂^{lit} - s₂^L)| ≤ 10 c^{-4/3}`. -/
lemma ctRosc_bound {ε c C ρ M R c₁ : ℝ} {f : ℝ → ℝ} (X : CtRoscCtx ε c C ρ M f) (hc₁ : 0 < c₁)
    (hrates : RoscRates c₁ C M c) (hR1 : 1 < R) (hRm : R ≤ ctRmax ctChartC1 c)
    (hRlow : c₁ ^ 2 * c ^ (2 / 3 : ℝ) ≤ R) :
    |(∫ u in Ioo (-R) R, (1 - taperW R |u|) * ctFr ε c f u) - ε * f 0 + ctMall R ε c f +
        2 * (ctOscS2Lit R ε c f - ctOscS2 R ε c f)| ≤ 10 * c ^ (-(4 / 3) : ℝ) := by
  have hc0 := X.c_pos
  have hR0 : 0 < R := by linarith
  set t : ℝ := c ^ (-(4 / 3) : ℝ) with ht
  have ht0 : 0 ≤ t := (Real.rpow_pos_of_pos hc0 _).le
  have hr0 : 0 ≤ hankelRinf c := hankelRinf_nonneg (by linarith [X.H.hc]) X.hf X.hε X.hM
  have hAlt : ctRmax ctChartC1 c < langerRadius c := by
    have := X.H.Rm_add_lt
    have : 0 ≤ C * c ^ (-(1 / 3 : ℝ)) := mul_nonneg X.H.C_nn (Real.rpow_nonneg hc0.le _)
    linarith
  have hRp := ctRprime_bounds X.H X.W hR1 hRm
  set u₁ : ℝ := R * c ^ (-(1 / 9) : ℝ) with hu₁
  have hc19 : c ^ (-(1 / 9) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hrates.c1 (by norm_num)
  have hc19p : 0 < c ^ (-(1 / 9) : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hu0 : 0 < u₁ := mul_pos hR0 hc19p
  have hu1 : u₁ ≤ R := by nlinarith
  have hu₁low : c₁ ^ 2 * c ^ (5 / 9 : ℝ) ≤ u₁ := by
    have : c ^ (2 / 3 : ℝ) * c ^ (-(1 / 9) : ℝ) = c ^ (5 / 9 : ℝ) := by
      rw [← Real.rpow_add hc0]; norm_num
    calc c₁ ^ 2 * c ^ (5 / 9 : ℝ) = c₁ ^ 2 * (c ^ (2 / 3 : ℝ) * c ^ (-(1 / 9) : ℝ)) := by rw [this]
      _ = (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) * c ^ (-(1 / 9) : ℝ) := by ring
      _ ≤ R * c ^ (-(1 / 9) : ℝ) := mul_le_mul_of_nonneg_right hRlow hc19p.le
  have hphi : u₁ / 2 ≤ ctPhiR ε c u₁ := by
    have h := (abs_le.1 (X.H.abs_ctPhiR_sub_le (u := u₁) (by rw [abs_of_pos hu0]; linarith))).1
    have := hrates.C_small
    linarith
  have hk₁ : 1 ≤ langerLobeK * ctPhiR ε c u₁ := by
    have h1 := hrates.lobe_one
    have : (langerLobeK * c₁ ^ 2 / 2) * c ^ (5 / 9 : ℝ) ≤ langerLobeK * ctPhiR ε c u₁ := by
      have : langerLobeK * (c₁ ^ 2 * c ^ (5 / 9 : ℝ) / 2) ≤ langerLobeK * ctPhiR ε c u₁ :=
        mul_le_mul_of_nonneg_left (by linarith) langerLobeK_pos.le
      calc _ = langerLobeK * (c₁ ^ 2 * c ^ (5 / 9 : ℝ) / 2) := by ring
        _ ≤ _ := this
    linarith
  have hmono : ctPhiR ε c u₁ ≤ ctPhiR ε c R :=
    X.H.ctPhiR_strictMonoOn.monotoneOn ⟨by linarith [X.H.Rm_pos], by linarith⟩ ⟨by linarith [X.H.Rm_pos], hRm⟩ hu1
  have hk : 1 ≤ langerLobeK * ctPhiR ε c R := by
    have := mul_le_mul_of_nonneg_left hmono langerLobeK_pos.le
    linarith
  have hmass := ct_rosc_mass X hR1 hRm hk
  have hpos := pos_lobe_le X hR0 hRm hu0 hu1 hk₁
  have hedge := X.slit_edge hR1 hRm
  -- the exponential terms
  have hB : 0 < 5 * (langerLobeK * c₁ ^ 2 / 2) ^ (3 / 2 : ℝ) := by
    have := langerLobeK_pos; positivity
  have hexpu : Real.exp (-5 * (langerLobeK * ctPhiR ε c u₁) ^ (3 / 2 : ℝ)) ≤
      Real.exp (-(5 * (langerLobeK * c₁ ^ 2 / 2) ^ (3 / 2 : ℝ)) * c ^ (5 / 6 : ℝ)) := by
    refine Real.exp_le_exp.2 ?_
    have h1 : (langerLobeK * c₁ ^ 2 / 2) * c ^ (5 / 9 : ℝ) ≤ langerLobeK * ctPhiR ε c u₁ := by
      have : langerLobeK * (c₁ ^ 2 * c ^ (5 / 9 : ℝ) / 2) ≤ langerLobeK * ctPhiR ε c u₁ :=
        mul_le_mul_of_nonneg_left (by linarith) langerLobeK_pos.le
      calc _ = langerLobeK * (c₁ ^ 2 * c ^ (5 / 9 : ℝ) / 2) := by ring
        _ ≤ _ := this
    have h2 : ((langerLobeK * c₁ ^ 2 / 2) * c ^ (5 / 9 : ℝ)) ^ (3 / 2 : ℝ) ≤
        (langerLobeK * ctPhiR ε c u₁) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (by have := langerLobeK_pos; positivity) h1 (by norm_num)
    have h3 : ((langerLobeK * c₁ ^ 2 / 2) * c ^ (5 / 9 : ℝ)) ^ (3 / 2 : ℝ) =
        (langerLobeK * c₁ ^ 2 / 2) ^ (3 / 2 : ℝ) * c ^ (5 / 6 : ℝ) := by
      rw [Real.mul_rpow (by have := langerLobeK_pos; positivity) (Real.rpow_nonneg hc0.le _),
        ← Real.rpow_mul hc0.le]; norm_num
    rw [h3] at h2
    nlinarith
  have hexpa : Real.exp (-5 * (langerLobeK * ctPhiR ε c R) ^ (3 / 2 : ℝ)) ≤
      Real.exp (-5 * (langerLobeK * ctPhiR ε c u₁) ^ (3 / 2 : ℝ)) := by
    refine Real.exp_le_exp.2 ?_
    have : (langerLobeK * ctPhiR ε c u₁) ^ (3 / 2 : ℝ) ≤ (langerLobeK * ctPhiR ε c R) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (mul_le_mul_of_nonneg_left hmono langerLobeK_pos.le) (by norm_num)
    linarith
  have hE1 := hrates.exp_pow
  have hE2 := hrates.exp_lin
  -- the strip
  have hδ : ctLam c * M / R ≤ (M / c₁ ^ 2) * c⁻¹ := by
    have hM0 := X.W.win.2.1
    have hl := ctLam_le hc0
    have h1 : ctLam c * M ≤ (c ^ (1 / 3 : ℝ))⁻¹ * M := mul_le_mul_of_nonneg_right hl hM0
    have hpow : c ^ (2 / 3 : ℝ) * c ^ (1 / 3 : ℝ) = c := by rw [← Real.rpow_add hc0]; norm_num
    have hc13 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    have hc23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    rw [div_le_iff₀ hR0]
    calc ctLam c * M ≤ (c ^ (1 / 3 : ℝ))⁻¹ * M := h1
      _ = (M / c₁ ^ 2) * c⁻¹ * (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) := by
        have hinv : c⁻¹ = (c ^ (2 / 3 : ℝ))⁻¹ * (c ^ (1 / 3 : ℝ))⁻¹ := by rw [← mul_inv, hpow]
        rw [hinv]; field_simp
      _ ≤ (M / c₁ ^ 2) * c⁻¹ * R := mul_le_mul_of_nonneg_left hRlow (by
        have := X.W.win.2.1; positivity)
  have hδ0 : 0 ≤ ctLam c * M / R := div_nonneg (mul_nonneg (ctLam_pos hc0).le X.W.win.2.1) hR0.le
  have hδ12 : (ctLam c * M / R) ^ 12 ≤ ((M / c₁ ^ 2) * c⁻¹) ^ 12 := pow_le_pow_left₀ hδ0 hδ 12
  have hst := hrates.strip
  have hAr := hrates.Ar
  have hAr2 := hrates.Ar2
  -- `(u₁/R)^12 = t`
  have hu₁R : (u₁ / R) ^ 12 = t := by
    rw [hu₁, mul_div_cancel_left₀ _ hR0.ne']
    have : (c ^ (-(1 / 9) : ℝ)) ^ 12 = c ^ (-(4 / 3) : ℝ) := by
      rw [← Real.rpow_mul_natCast hc0.le]; norm_num
    exact this
  have haA : ctPhiR ε c R ≤ langerRadius c := (abs_le.1 (X.H.abs_ctPhiR_lt (by rw [abs_of_pos hR0]; exact hRm)).le).2
  have hRpA : ctRprime ε c R ≤ langerRadius c := by linarith [hRp.2.1]
  have ha0 : 0 ≤ ctPhiR ε c u₁ := by linarith
  have hx1 : (ctPhiR ε c R + ctRprime ε c R) * hankelRinf c + ctRprime ε c R * hankelRinf c ≤ 3 * (langerRadius c * hankelRinf c) := by
    have h1 := mul_le_mul_of_nonneg_right haA hr0
    have h2 := mul_le_mul_of_nonneg_right hRpA hr0
    linarith
  have hx2 : (ctPhiR ε c R - ctPhiR ε c u₁) * hankelRinf c ≤ 2 * (langerRadius c * hankelRinf c) := by
    have h1 := mul_le_mul_of_nonneg_right haA hr0
    have h2 := mul_nonneg ha0 hr0
    have h3 := mul_nonneg (langerRadius_pos hc0).le hr0
    linarith
  have hS : 2 * (ctLam c * M / R) ^ 12 * (1 + 2 * langerRadius c * hankelRinf c) ≤ t / 2 := by
    have : 2 * (ctLam c * M / R) ^ 12 * (1 + 2 * langerRadius c * hankelRinf c) ≤ 2 * (ctLam c * M / R) ^ 12 * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith [pow_nonneg hδ0 12]
  have hP : 2 * (u₁ / R) ^ 12 * (1 + 2 * langerRadius c * hankelRinf c) ≤ 4 * t := by
    rw [hu₁R]; have := hrates.Ar2; nlinarith
  -- assemble
  have hY := hedge
  calc _ ≤ |(∫ u in Ioo (-R) R, (1 - taperW R |u|) * ctFr ε c f u) - ε * f 0 + ctMall R ε c f| +
        |2 * (ctOscS2Lit R ε c f - ctOscS2 R ε c f)| := abs_add_le _ _
    _ = |(∫ u in Ioo (-R) R, (1 - taperW R |u|) * ctFr ε c f u) - ε * f 0 + ctMall R ε c f| +
        2 * |ctOscS2Lit R ε c f - ctOscS2 R ε c f| := by rw [abs_mul]; norm_num
    _ ≤ 10 * t := by linarith [hmass, hpos, hY, hx1, hx2, hS, hP, hexpa, hexpu, hE1, hE2, hAr, hAr2, Real.exp_pos (-(1 / 25) * c)]

end FormalResearch.SignUncertainty
