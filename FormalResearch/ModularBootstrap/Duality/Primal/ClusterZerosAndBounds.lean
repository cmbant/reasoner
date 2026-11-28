module

public import FormalResearch.ModularBootstrap.Duality.Primal.ClusterCharts
public import FormalResearch.SignUncertainty.RadialRigidity

/-!
# Window Cardy ratios, extremal zero orders, and exponential chord bounds for PA2

Companion to `ClusterCharts.lean`:

* `cardyV_mul_jAiry_window_ratio`: uniform prefactor ratio `→ 1` and exact log-ratio bound
  `|log-exp| ≤ q_n |t - t₀|` on fixed `uAiry` windows;
* `airyProfile_orderNat_one`, `airyProfile_orderNat_node`, `airyProfile_zero_iff`;
* `hbExtremal_zero_im`, `hbProfile_orderNat_S`, `hbProfile_orderNat_offS`,
  `even_analyticOrderNatAt_of_nonneg`;
* `exp_sub_one_le_secant`, `exp_sub_one_le_quadratic`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal Polynomial

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.WeightAxioms FormalResearch.ModularBootstrap.ConcreteBootstrap
  FormalResearch.ModularBootstrap.FixedWeightTip FormalResearch.ModularBootstrap.Blowup
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Bessel
  FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.ArgPrinciple

/-! ### 1. Uniform Cardy-Jacobian ratio on fixed Airy windows -/

private noncomputable def cardyVPref (prob : FixedWeightProblem) (y : ℝ) : ℝ :=
  prob.nullPoly (Real.exp (-4 * Real.pi * y)) * (2 * y) ^ (prob.w - 1) * Real.sqrt y

private lemma cardyV_pref_continuousAt (prob : FixedWeightProblem) :
    ContinuousAt (cardyVPref prob) xiStar := by
  have hQ : Continuous (fun y : ℝ => prob.nullPoly (Real.exp (-4 * Real.pi * y))) := by
    have heq : (fun y : ℝ => prob.nullPoly (Real.exp (-4 * Real.pi * y))) =
        fun y : ℝ => (nullPolyExpC prob (Complex.ofReal y)).re := by
      ext y; exact congrArg Complex.re (nullPolyExpC_ofReal prob y).symm
    rw [heq]
    exact Complex.continuous_re.comp ((nullPolyExpC_entire prob).continuous.comp Complex.continuous_ofReal)
  exact ((hQ.continuousAt.mul (((continuous_const.mul continuous_id).pow _).continuousAt)).mul
    Real.continuous_sqrt.continuousAt)

private lemma cardyV_mul_jAiry_pt_band (prob : FixedWeightProblem)
    {C_V c y u η δ_f : ℝ}
    (hcm : max 1 (24 * prob.totalShift) ≤ c) (hcpos : 0 < c)
    (hV_as : ∀ {c' x : ℝ}, max 1 (24 * prob.totalShift) ≤ c' → xiStar / 2 ≤ x →
      |prob.cardyV (c' / 12) (c' * x ^ 2 / 3) /
          ((2 * x) ^ (prob.w - 1) * besselAs (c' * (2 * Real.pi * x / 3))) -
        prob.nullPoly (Real.exp (-4 * Real.pi * x))| ≤ C_V / c')
    (hq_bds : ∀ {x : ℝ}, xiStar / 2 ≤ x →
      prob.nullPoly (Real.exp (-4 * Real.pi * (xiStar / 2))) ≤
        prob.nullPoly (Real.exp (-4 * Real.pi * x)) ∧
      prob.nullPoly (Real.exp (-4 * Real.pi * x)) ≤ 1)
    (hCV : C_V / c ≤ prob.nullPoly (Real.exp (-4 * Real.pi * (xiStar / 2))) * η)
    (hη_pos : 0 < η) (hη_lt : η ≤ 1 / 4)
    (hδf : ∀ ⦃x : ℝ⦄, dist x xiStar < δ_f →
      dist (cardyVPref prob x) (cardyVPref prob xiStar) < η * cardyVPref prob xiStar)
    (hy : 0 < y) (hu_half : xiStar / 2 ≤ u) (hu_δ : |u - xiStar| < δ_f) (huy : u ^ 2 * c / 3 = y) :
    (1 - η) * (1 - η) * (2 * Real.sqrt 3 / (2 * Real.pi * Real.sqrt c * 3 * betaTip) *
      c ^ ((1 : ℝ) / 3) * cardyVPref prob xiStar * Real.exp (c * (2 * Real.pi * u / 3))) ≤
    prob.cardyV (c / 12) y * jAiry c y ∧
    prob.cardyV (c / 12) y * jAiry c y ≤
    (1 + η) * (1 + η) * (2 * Real.sqrt 3 / (2 * Real.pi * Real.sqrt c * 3 * betaTip) *
      c ^ ((1 : ℝ) / 3) * cardyVPref prob xiStar * Real.exp (c * (2 * Real.pi * u / 3))) := by
  have hu_pos : 0 < u := lt_of_lt_of_le (half_pos xiStar_pos) hu_half
  have hf_close : |cardyVPref prob u - cardyVPref prob xiStar| < η * cardyVPref prob xiStar := by
    simpa only [Real.dist_eq] using hδf hu_δ
  have hf_bounds : (1 - η) * cardyVPref prob xiStar ≤ cardyVPref prob u ∧
      cardyVPref prob u ≤ (1 + η) * cardyVPref prob xiStar := by
    have h := abs_lt.mp hf_close
    constructor <;> nlinarith
  have hV := hV_as hcm hu_half
  rw [show c * u ^ 2 / 3 = y by linarith] at hV
  have hq_u := (hq_bds hu_half).1
  have hV_rel : (1 - η) * prob.nullPoly (Real.exp (-4 * Real.pi * u)) ≤
      prob.cardyV (c / 12) y / ((2 * u) ^ (prob.w - 1) * besselAs (c * (2 * Real.pi * u / 3))) ∧
      prob.cardyV (c / 12) y / ((2 * u) ^ (prob.w - 1) * besselAs (c * (2 * Real.pi * u / 3))) ≤
      (1 + η) * prob.nullPoly (Real.exp (-4 * Real.pi * u)) := by
    have hCV' : C_V / c ≤ η * prob.nullPoly (Real.exp (-4 * Real.pi * u)) :=
      hCV.trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hq_u hη_pos.le)
    have hlo : -(C_V / c) ≤
        prob.cardyV (c / 12) y / ((2 * u) ^ (prob.w - 1) * besselAs (c * (2 * Real.pi * u / 3))) -
          prob.nullPoly (Real.exp (-4 * Real.pi * u)) := (abs_le.mp hV).1
    have hhi :
        prob.cardyV (c / 12) y / ((2 * u) ^ (prob.w - 1) * besselAs (c * (2 * Real.pi * u / 3))) -
          prob.nullPoly (Real.exp (-4 * Real.pi * u)) ≤ C_V / c := (abs_le.mp hV).2
    refine ⟨?_, ?_⟩
    · have h1 := (neg_le_neg hCV').trans hlo; linarith only [h1]
    · have h2 := hhi.trans hCV'; linarith only [h2]
  have hbessel : besselAs (c * (2 * Real.pi * u / 3)) =
      Real.sqrt 3 / (2 * Real.pi * Real.sqrt c * Real.sqrt u) * Real.exp (c * (2 * Real.pi * u / 3)) := by
    unfold besselAs
    have hsq : Real.sqrt (2 * Real.pi * (c * (2 * Real.pi * u / 3))) =
        2 * Real.pi * Real.sqrt c * Real.sqrt u / Real.sqrt 3 := by
      have e1 : 2 * Real.pi * (c * (2 * Real.pi * u / 3)) = (2 * Real.pi) ^ 2 * (c * u) / 3 := by ring
      have hdiv := Real.sqrt_div (mul_nonneg (sq_nonneg (2 * Real.pi)) (mul_nonneg hcpos.le hu_pos.le)) 3
      rw [e1, hdiv, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), Real.sqrt_mul hcpos.le]
      ring
    rw [hsq]; simp only [div_eq_mul_inv, mul_inv, inv_inv]; ring
  have hJ : jAiry c y = 2 * u * c ^ ((1 : ℝ) / 3) / (3 * betaTip) := by
    have hsq : Real.sqrt (3 * y / c) = u := by
      have h3y : 3 * y / c = u ^ 2 := by rw [← huy]; field_simp [hcpos.ne']
      rw [h3y, Real.sqrt_sq hu_pos.le]
    have hj : jAiry c y = 2 * Real.sqrt (3 * y / c) * c ^ ((1 : ℝ) / 3) / (3 * betaTip) := rfl
    rw [hj, hsq]
  have hden_pos : 0 < (2 * u) ^ (prob.w - 1) * besselAs (c * (2 * Real.pi * u / 3)) :=
    mul_pos (pow_pos (by positivity) _) (besselAs_pos (by positivity))
  have hV_eq : prob.cardyV (c / 12) y * jAiry c y =
      (prob.cardyV (c / 12) y / ((2 * u) ^ (prob.w - 1) * besselAs (c * (2 * Real.pi * u / 3)))) *
      ((2 * u) ^ (prob.w - 1) * besselAs (c * (2 * Real.pi * u / 3)) * jAiry c y) := by
    rw [← mul_assoc, div_mul_cancel₀ _ hden_pos.ne']
  have hfac_eq : (2 * u) ^ (prob.w - 1) * besselAs (c * (2 * Real.pi * u / 3)) * jAiry c y =
      2 * Real.sqrt 3 / (2 * Real.pi * Real.sqrt c * 3 * betaTip) *
        c ^ ((1 : ℝ) / 3) * ((2 * u) ^ (prob.w - 1) * Real.sqrt u) * Real.exp (c * (2 * Real.pi * u / 3)) := by
    rw [hbessel, hJ]
    have hsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu_pos.le
    have hu_div : u / Real.sqrt u = Real.sqrt u :=
      (div_eq_iff (Real.sqrt_pos.mpr hu_pos).ne').mpr hsq.symm
    calc (2 * u) ^ (prob.w - 1) *
          (Real.sqrt 3 / (2 * Real.pi * Real.sqrt c * Real.sqrt u) * Real.exp (c * (2 * Real.pi * u / 3))) *
          (2 * u * c ^ ((1 : ℝ) / 3) / (3 * betaTip))
        = (2 * Real.sqrt 3 / (2 * Real.pi * Real.sqrt c * 3 * betaTip) * c ^ ((1 : ℝ) / 3)) *
            ((2 * u) ^ (prob.w - 1) * (u / Real.sqrt u)) * Real.exp (c * (2 * Real.pi * u / 3)) := by ring
      _ = 2 * Real.sqrt 3 / (2 * Real.pi * Real.sqrt c * 3 * betaTip) *
            c ^ ((1 : ℝ) / 3) * ((2 * u) ^ (prob.w - 1) * Real.sqrt u) * Real.exp (c * (2 * Real.pi * u / 3)) := by
          rw [hu_div]
  have htail_nn : 0 ≤ 2 * Real.sqrt 3 / (2 * Real.pi * Real.sqrt c * 3 * betaTip) *
      c ^ ((1 : ℝ) / 3) * ((2 * u) ^ (prob.w - 1) * Real.sqrt u) * Real.exp (c * (2 * Real.pi * u / 3)) := by
    rw [← hfac_eq]; exact (mul_pos hden_pos (jAiry_pos hcpos hy)).le
  have hbase_nn : 0 ≤ 2 * Real.sqrt 3 / (2 * Real.pi * Real.sqrt c * 3 * betaTip) *
      c ^ ((1 : ℝ) / 3) * Real.exp (c * (2 * Real.pi * u / 3)) := by
    have := betaTip_pos
    exact mul_nonneg (mul_nonneg (div_nonneg (by positivity) (by positivity))
      (Real.rpow_nonneg hcpos.le _)) (Real.exp_pos _).le
  have hf_def : prob.nullPoly (Real.exp (-4 * Real.pi * u)) * (2 * u) ^ (prob.w - 1) * Real.sqrt u =
      cardyVPref prob u := rfl
  rw [hV_eq, hfac_eq]
  constructor
  · calc (1 - η) * (1 - η) * (2 * Real.sqrt 3 / (2 * Real.pi * Real.sqrt c * 3 * betaTip) *
            c ^ ((1 : ℝ) / 3) * cardyVPref prob xiStar * Real.exp (c * (2 * Real.pi * u / 3)))
        = 2 * Real.sqrt 3 / (2 * Real.pi * Real.sqrt c * 3 * betaTip) *
            c ^ ((1 : ℝ) / 3) * Real.exp (c * (2 * Real.pi * u / 3)) * ((1 - η) * ((1 - η) * cardyVPref prob xiStar)) := by ring
      _ ≤ 2 * Real.sqrt 3 / (2 * Real.pi * Real.sqrt c * 3 * betaTip) *
            c ^ ((1 : ℝ) / 3) * Real.exp (c * (2 * Real.pi * u / 3)) * ((1 - η) * cardyVPref prob u) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf_bounds.1 (by linarith)) hbase_nn
      _ = ((1 - η) * prob.nullPoly (Real.exp (-4 * Real.pi * u))) *
            (2 * Real.sqrt 3 / (2 * Real.pi * Real.sqrt c * 3 * betaTip) *
              c ^ ((1 : ℝ) / 3) * ((2 * u) ^ (prob.w - 1) * Real.sqrt u) * Real.exp (c * (2 * Real.pi * u / 3))) := by
          rw [← hf_def]; ring
      _ ≤ (prob.cardyV (c / 12) y / ((2 * u) ^ (prob.w - 1) * besselAs (c * (2 * Real.pi * u / 3)))) *
            (2 * Real.sqrt 3 / (2 * Real.pi * Real.sqrt c * 3 * betaTip) *
              c ^ ((1 : ℝ) / 3) * ((2 * u) ^ (prob.w - 1) * Real.sqrt u) * Real.exp (c * (2 * Real.pi * u / 3))) :=
          mul_le_mul_of_nonneg_right hV_rel.1 htail_nn
  · calc (prob.cardyV (c / 12) y / ((2 * u) ^ (prob.w - 1) * besselAs (c * (2 * Real.pi * u / 3)))) *
          (2 * Real.sqrt 3 / (2 * Real.pi * Real.sqrt c * 3 * betaTip) *
            c ^ ((1 : ℝ) / 3) * ((2 * u) ^ (prob.w - 1) * Real.sqrt u) * Real.exp (c * (2 * Real.pi * u / 3)))
        ≤ ((1 + η) * prob.nullPoly (Real.exp (-4 * Real.pi * u))) *
            (2 * Real.sqrt 3 / (2 * Real.pi * Real.sqrt c * 3 * betaTip) *
              c ^ ((1 : ℝ) / 3) * ((2 * u) ^ (prob.w - 1) * Real.sqrt u) * Real.exp (c * (2 * Real.pi * u / 3))) :=
          mul_le_mul_of_nonneg_right hV_rel.2 htail_nn
      _ = 2 * Real.sqrt 3 / (2 * Real.pi * Real.sqrt c * 3 * betaTip) *
            c ^ ((1 : ℝ) / 3) * Real.exp (c * (2 * Real.pi * u / 3)) * ((1 + η) * cardyVPref prob u) := by
          rw [← hf_def]; ring
      _ ≤ 2 * Real.sqrt 3 / (2 * Real.pi * Real.sqrt c * 3 * betaTip) *
            c ^ ((1 : ℝ) / 3) * Real.exp (c * (2 * Real.pi * u / 3)) * ((1 + η) * ((1 + η) * cardyVPref prob xiStar)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf_bounds.2 (by linarith)) hbase_nn
      _ = (1 + η) * (1 + η) * (2 * Real.sqrt 3 / (2 * Real.pi * Real.sqrt c * 3 * betaTip) *
            c ^ ((1 : ℝ) / 3) * cardyVPref prob xiStar * Real.exp (c * (2 * Real.pi * u / 3))) := by ring

/-- Uniform Cardy-Jacobian ratio on any bounded `uAiry` window `|uAiry c t| ≤ M`:
the non-exponential ratio tends uniformly to `1`, and the exponential factor
`exp(c * (2π / 3) * (√(3t/c) - √(3t₀/c)))` has log bounded by `q_n |t - t₀|` where
`q_n = π / √(3 * t_min / c) → π / ξ_*`. -/
theorem cardyV_mul_jAiry_window_ratio (prob : FixedWeightProblem) {M : ℝ} (_hM : 0 ≤ M) :
    ∀ ε > 0, ∃ c₀ : ℝ, max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ {c t t₀ : ℝ}, c₀ ≤ c → 0 < t → 0 < t₀ → |uAiry c t| ≤ M → |uAiry c t₀| ≤ M →
        let x := Real.sqrt (3 * t / c)
        let x₀ := Real.sqrt (3 * t₀ / c)
        let q := Real.pi / min x x₀
        xiStar / 2 ≤ x ∧ xiStar / 2 ≤ x₀ ∧
        |(prob.cardyV (c / 12) t * jAiry c t) / (prob.cardyV (c / 12) t₀ * jAiry c t₀) *
            Real.exp (-(c * (2 * Real.pi / 3) * (x - x₀))) - 1| ≤ ε ∧
        |c * (2 * Real.pi / 3) * (x - x₀)| ≤ q * |t - t₀| ∧
        |q - Real.pi / xiStar| ≤ ε := by
  intro ε hε
  obtain ⟨C_V, _, hV_as⟩ := cardyV_asymptotic_real prob (half_pos xiStar_pos)
  obtain ⟨hq0_pos, hq_bds⟩ := nullPoly_exp_bounds prob (half_pos xiStar_pos)
  let q₀ := prob.nullPoly (Real.exp (-4 * Real.pi * (xiStar / 2)))
  change 0 < q₀ at hq0_pos
  have hf_pos : 0 < cardyVPref prob xiStar := by
    have hq : q₀ ≤ prob.nullPoly (Real.exp (-4 * Real.pi * xiStar)) :=
      (hq_bds (by linarith [xiStar_pos])).1
    have hxi := xiStar_pos
    have hq_pos : 0 < prob.nullPoly (Real.exp (-4 * Real.pi * xiStar)) := hq0_pos.trans_le hq
    have hpow : 0 < (2 * xiStar) ^ (prob.w - 1) := pow_pos (by positivity) _
    have hrt : 0 < Real.sqrt xiStar := Real.sqrt_pos.mpr hxi
    dsimp [cardyVPref]; exact mul_pos (mul_pos hq_pos hpow) hrt
  -- Choose `δ₁` so that `|a / b - 1| ≤ ε` whenever `|a - 1| ≤ δ₁`, `|b - 1| ≤ δ₁`, and `|u - 1| ≤ δ₁`, `|v - 1| ≤ δ₁`.
  -- Specifically `(a * u) / (b * v) - 1`: if `1 - η ≤ a, u, b, v ≤ 1 + η` with `η < 1/4`,
  -- then `(1 - η)² / (1 + η)² ≤ (a*u)/(b*v) ≤ (1 + η)² / (1 - η)²`.
  -- Pick `η ∈ (0, 1/4]` with `max (1 - (1 - η)²/(1 + η)²) ((1 + η)²/(1 - η)² - 1) ≤ ε`.
  have hratio_cont : ContinuousAt (fun η : ℝ => ((1 + η) / (1 - η)) ^ 2 - 1) 0 := by
    have h1 : ContinuousAt (fun η : ℝ => (1 + η) / (1 - η)) 0 :=
      (continuousAt_const.add continuousAt_id).div (continuousAt_const.sub continuousAt_id) (by norm_num)
    exact ((h1.pow 2).sub continuousAt_const)
  have hratio_cont2 : ContinuousAt (fun η : ℝ => 1 - ((1 - η) / (1 + η)) ^ 2) 0 := by
    have h1 : ContinuousAt (fun η : ℝ => (1 - η) / (1 + η)) 0 :=
      (continuousAt_const.sub continuousAt_id).div (continuousAt_const.add continuousAt_id) (by norm_num)
    exact continuousAt_const.sub (h1.pow 2)
  obtain ⟨η, hη_pos, hη_lt, hη_up, hη_lo⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧
      ((1 + η) / (1 - η)) ^ 2 - 1 ≤ ε ∧ 1 - ((1 - η) / (1 + η)) ^ 2 ≤ ε := by
    have h1 := Metric.continuousAt_iff.mp hratio_cont ε hε
    have h2 := Metric.continuousAt_iff.mp hratio_cont2 ε hε
    obtain ⟨d₁, hd₁, hd₁p⟩ := h1
    obtain ⟨d₂, hd₂, hd₂p⟩ := h2
    let η := min (1 / 4) (min (d₁ / 2) (d₂ / 2))
    have hη_pos : 0 < η := by positivity
    refine ⟨η, hη_pos, min_le_left _ _, ?_, ?_⟩
    · have hh1 := hd₁p (show dist η 0 < d₁ by
        rw [Real.dist_eq, sub_zero, abs_of_pos hη_pos]
        exact (min_le_right _ _ |>.trans (min_le_left _ _)).trans_lt (by linarith))
      rw [Real.dist_eq] at hh1; simp at hh1; linarith [(abs_lt.mp hh1).2]
    · have hh2 := hd₂p (show dist η 0 < d₂ by
        rw [Real.dist_eq, sub_zero, abs_of_pos hη_pos]
        exact (min_le_right _ _ |>.trans (min_le_right _ _)).trans_lt (by linarith))
      rw [Real.dist_eq] at hh2; simp at hh2; linarith [(abs_lt.mp hh2).2]
  obtain ⟨δ_f, hδf_pos, hδf⟩ := Metric.continuousAt_iff.mp (cardyV_pref_continuousAt prob)
    (η * cardyVPref prob xiStar) (by positivity)
  have hx_tend : Tendsto (fun c : ℝ => M / (betaTip * c ^ ((2 : ℝ) / 3))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul (M / betaTip)).congr'
      (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc; rw [Real.rpow_neg hc.le]; ring)
  have h1 : ∀ᶠ c : ℝ in atTop, M / (betaTip * c ^ ((2 : ℝ) / 3)) < min (xiStar / 2) δ_f :=
    hx_tend.eventually (gt_mem_nhds (lt_min (half_pos xiStar_pos) hδf_pos))
  have h2 : ∀ᶠ c : ℝ in atTop, C_V / c ≤ q₀ * η :=
    ((tendsto_const_nhds (x := C_V)).div_atTop tendsto_id).eventually
      (ge_mem_nhds (mul_pos hq0_pos hη_pos))
  have h3 : ∀ᶠ c : ℝ in atTop,
      Real.pi / (xiStar - M / (betaTip * c ^ ((2 : ℝ) / 3))) - Real.pi / xiStar ≤ ε ∧
      Real.pi / xiStar - Real.pi / (xiStar + M / (betaTip * c ^ ((2 : ℝ) / 3))) ≤ ε := by
    have hlo : Tendsto (fun c : ℝ => Real.pi / (xiStar - M / (betaTip * c ^ ((2 : ℝ) / 3))) -
        Real.pi / xiStar) atTop (𝓝 0) := by
      have hd : Tendsto (fun c : ℝ => Real.pi / (xiStar - M / (betaTip * c ^ ((2 : ℝ) / 3))))
          atTop (𝓝 (Real.pi / xiStar)) :=
        tendsto_const_nhds.div (by simpa only [sub_zero] using tendsto_const_nhds.sub hx_tend)
          xiStar_pos.ne'
      simpa only [sub_self] using hd.sub_const (Real.pi / xiStar)
    have hhi : Tendsto (fun c : ℝ => Real.pi / xiStar -
        Real.pi / (xiStar + M / (betaTip * c ^ ((2 : ℝ) / 3)))) atTop (𝓝 0) := by
      have hd : Tendsto (fun c : ℝ => Real.pi / (xiStar + M / (betaTip * c ^ ((2 : ℝ) / 3))))
          atTop (𝓝 (Real.pi / xiStar)) :=
        tendsto_const_nhds.div (by simpa only [add_zero] using tendsto_const_nhds.add hx_tend)
          xiStar_pos.ne'
      simpa only [sub_self] using (tendsto_const_nhds (x := Real.pi / xiStar)).sub hd
    exact (hlo.eventually (ge_mem_nhds hε)).and (hhi.eventually (ge_mem_nhds hε))
  obtain ⟨c₁, hc₁⟩ := eventually_atTop.mp (h1.and (h2.and h3))
  refine ⟨max c₁ (max 1 (24 * prob.totalShift)), le_max_right _ _,
    fun {c t t₀} hc ht ht₀ hut hut₀ => ?_⟩
  have hcm : max 1 (24 * prob.totalShift) ≤ c := (le_max_right _ _).trans hc
  have hc1 : c₁ ≤ c := (le_max_left _ _).trans hc
  have hcpos : 0 < c := lt_of_lt_of_le (by linarith [le_max_left (1 : ℝ) (24 * prob.totalShift)]) hcm
  obtain ⟨hMx, hCV, hpi_lo, hpi_hi⟩ := hc₁ c hc1
  let x := Real.sqrt (3 * t / c)
  let x₀ := Real.sqrt (3 * t₀ / c)
  let q := Real.pi / min x x₀
  have hbd_x : ∀ {y u : ℝ}, u = Real.sqrt (3 * y / c) → |uAiry c y| ≤ M →
      |u - xiStar| ≤ M / (betaTip * c ^ ((2 : ℝ) / 3)) := fun {y u} hyu hy => by
    subst hyu
    have heq : Real.sqrt (3 * y / c) - xiStar = -uAiry c y / (betaTip * c ^ ((2 : ℝ) / 3)) := by
      unfold uAiry
      have hp : c ^ ((2 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hcpos _).ne'
      field_simp [betaTip_pos.ne', hp]
    rw [heq, abs_div, abs_neg, abs_of_pos (mul_pos betaTip_pos (Real.rpow_pos_of_pos hcpos _))]
    exact div_le_div_of_nonneg_right hy (mul_pos betaTip_pos (Real.rpow_pos_of_pos hcpos _)).le
  have hx_err := hbd_x rfl hut
  have hx₀_err := hbd_x rfl hut₀
  have hx_half : xiStar / 2 ≤ x := by linarith [(abs_le.mp hx_err).1, min_le_left (xiStar / 2) δ_f]
  have hx₀_half : xiStar / 2 ≤ x₀ := by linarith [(abs_le.mp hx₀_err).1, min_le_left (xiStar / 2) δ_f]
  have hx_pos : 0 < x := lt_of_lt_of_le (half_pos xiStar_pos) hx_half
  have hx₀_pos : 0 < x₀ := lt_of_lt_of_le (half_pos xiStar_pos) hx₀_half
  -- Bound `q - π/ξ_*`
  have hmin_lo : xiStar - M / (betaTip * c ^ ((2 : ℝ) / 3)) ≤ min x x₀ :=
    le_min (by linarith [(abs_le.mp hx_err).1]) (by linarith [(abs_le.mp hx₀_err).1])
  have hmin_hi : min x x₀ ≤ xiStar + M / (betaTip * c ^ ((2 : ℝ) / 3)) :=
    (min_le_left x x₀).trans (by linarith [(abs_le.mp hx_err).2])
  have hmin_pos : 0 < min x x₀ := lt_min hx_pos hx₀_pos
  have hsub_pos : 0 < xiStar - M / (betaTip * c ^ ((2 : ℝ) / 3)) := by
    linarith [min_le_left (xiStar / 2) δ_f, xiStar_pos]
  have hq_bd : |q - Real.pi / xiStar| ≤ ε := by
    rw [abs_le]
    have hup : q ≤ Real.pi / (xiStar - M / (betaTip * c ^ ((2 : ℝ) / 3))) :=
      div_le_div_of_nonneg_left Real.pi_pos.le hsub_pos hmin_lo
    have hlo : Real.pi / (xiStar + M / (betaTip * c ^ ((2 : ℝ) / 3))) ≤ q :=
      div_le_div_of_nonneg_left Real.pi_pos.le hmin_pos hmin_hi
    exact ⟨by linarith, by linarith⟩
  -- Exponential log-difference bound: `|c (2π/3) (x - x₀)| ≤ q |t - t₀|`
  have hexp_diff : |c * (2 * Real.pi / 3) * (x - x₀)| ≤ q * |t - t₀| := by
    have hmul : (x - x₀) * (x + x₀) = 3 * (t - t₀) / c := by
      have h1 : x ^ 2 = 3 * t / c := Real.sq_sqrt (by positivity)
      have h2 : x₀ ^ 2 = 3 * t₀ / c := Real.sq_sqrt (by positivity)
      calc (x - x₀) * (x + x₀) = x ^ 2 - x₀ ^ 2 := by ring
        _ = 3 * t / c - 3 * t₀ / c := by rw [h1, h2]
        _ = 3 * (t - t₀) / c := by ring
    have hsum_pos : 0 < x + x₀ := by linarith
    have heq : c * (2 * Real.pi / 3) * (x - x₀) = (2 * Real.pi / (x + x₀)) * (t - t₀) := by
      have := eq_div_of_mul_eq hsum_pos.ne' hmul
      rw [this]; field_simp [hcpos.ne', hsum_pos.ne']
    have h2pi : 2 * Real.pi / (x + x₀) ≤ q := by
      have hm : 2 * min x x₀ ≤ x + x₀ := by linarith [min_le_left x x₀, min_le_right x x₀]
      have hdiv := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * Real.pi)
        (by positivity : 0 < 2 * min x x₀) hm
      rwa [show 2 * Real.pi / (2 * min x x₀) = q by dsimp [q]; field_simp] at hdiv
    rw [heq, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi / (x + x₀))]
    exact mul_le_mul_of_nonneg_right h2pi (abs_nonneg _)
  -- Prefactor and asymptotic error control
  have h1 := cardyV_mul_jAiry_pt_band prob hcm hcpos hV_as hq_bds hCV hη_pos hη_lt hδf ht hx_half
    (hx_err.trans_lt (hMx.trans_le (min_le_right _ _)))
    (by rw [Real.sq_sqrt (by positivity)]; field_simp [hcpos.ne'])
  have h0 := cardyV_mul_jAiry_pt_band prob hcm hcpos hV_as hq_bds hCV hη_pos hη_lt hδf ht₀ hx₀_half
    (hx₀_err.trans_lt (hMx.trans_le (min_le_right _ _)))
    (by rw [Real.sq_sqrt (by positivity)]; field_simp [hcpos.ne'])
  let B := 2 * Real.sqrt 3 / (2 * Real.pi * Real.sqrt c * 3 * betaTip) *
    c ^ ((1 : ℝ) / 3) * cardyVPref prob xiStar
  have hB_pos : 0 < B := by have := betaTip_pos; positivity
  have hden_pos : 0 < prob.cardyV (c / 12) t₀ * jAiry c t₀ :=
    mul_pos (prob.cardyV_pos (by linarith [le_max_right (1 : ℝ) (24 * prob.totalShift)]) ht₀) (jAiry_pos hcpos ht₀)
  have hnum_pos : 0 < prob.cardyV (c / 12) t * jAiry c t :=
    mul_pos (prob.cardyV_pos (by linarith [le_max_right (1 : ℝ) (24 * prob.totalShift)]) ht) (jAiry_pos hcpos ht)
  have hlo_ratio : ((1 - η) / (1 + η)) ^ 2 ≤
      (prob.cardyV (c / 12) t * jAiry c t) / (prob.cardyV (c / 12) t₀ * jAiry c t₀) *
        Real.exp (-(c * (2 * Real.pi / 3) * (x - x₀))) := by
    have hnum_l : (1 - η) * (1 - η) * (B * Real.exp (c * (2 * Real.pi * x / 3))) ≤
        prob.cardyV (c / 12) t * jAiry c t := h1.1
    have hden_u : prob.cardyV (c / 12) t₀ * jAiry c t₀ ≤
        (1 + η) * (1 + η) * (B * Real.exp (c * (2 * Real.pi * x₀ / 3))) := h0.2
    have he1 : ((1 - η) / (1 + η)) ^ 2 =
        ((1 - η) * (1 - η) * (B * Real.exp (c * (2 * Real.pi * x / 3)))) /
        ((1 + η) * (1 + η) * (B * Real.exp (c * (2 * Real.pi * x₀ / 3)))) *
        Real.exp (-(c * (2 * Real.pi / 3) * (x - x₀))) := by
      have hexp : Real.exp (c * (2 * Real.pi * x / 3)) / Real.exp (c * (2 * Real.pi * x₀ / 3)) *
          Real.exp (-(c * (2 * Real.pi / 3) * (x - x₀))) = 1 := by
        rw [← Real.exp_sub, ← Real.exp_add,
          show c * (2 * Real.pi * x / 3) - c * (2 * Real.pi * x₀ / 3) + -(c * (2 * Real.pi / 3) * (x - x₀)) = 0 by ring,
          Real.exp_zero]
      calc ((1 - η) / (1 + η)) ^ 2
          = ((1 - η) / (1 + η)) ^ 2 *
              (Real.exp (c * (2 * Real.pi * x / 3)) / Real.exp (c * (2 * Real.pi * x₀ / 3)) *
                Real.exp (-(c * (2 * Real.pi / 3) * (x - x₀)))) := by rw [hexp, mul_one]
        _ = ((1 - η) * (1 - η) * (B * Real.exp (c * (2 * Real.pi * x / 3)))) /
              ((1 + η) * (1 + η) * (B * Real.exp (c * (2 * Real.pi * x₀ / 3)))) *
              Real.exp (-(c * (2 * Real.pi / 3) * (x - x₀))) := by
            field_simp [hB_pos.ne', (show 1 + η ≠ 0 by linarith)]
    rw [he1]
    exact mul_le_mul_of_nonneg_right
      (div_le_div₀ (by positivity) hnum_l hden_pos hden_u) (Real.exp_pos _).le
  have hup_ratio : (prob.cardyV (c / 12) t * jAiry c t) / (prob.cardyV (c / 12) t₀ * jAiry c t₀) *
      Real.exp (-(c * (2 * Real.pi / 3) * (x - x₀))) ≤ ((1 + η) / (1 - η)) ^ 2 := by
    have hnum_u : prob.cardyV (c / 12) t * jAiry c t ≤
        (1 + η) * (1 + η) * (B * Real.exp (c * (2 * Real.pi * x / 3))) := h1.2
    have hden_l : (1 - η) * (1 - η) * (B * Real.exp (c * (2 * Real.pi * x₀ / 3))) ≤
        prob.cardyV (c / 12) t₀ * jAiry c t₀ := h0.1
    have he1 : ((1 + η) / (1 - η)) ^ 2 =
        ((1 + η) * (1 + η) * (B * Real.exp (c * (2 * Real.pi * x / 3)))) /
        ((1 - η) * (1 - η) * (B * Real.exp (c * (2 * Real.pi * x₀ / 3)))) *
        Real.exp (-(c * (2 * Real.pi / 3) * (x - x₀))) := by
      have hexp : Real.exp (c * (2 * Real.pi * x / 3)) / Real.exp (c * (2 * Real.pi * x₀ / 3)) *
          Real.exp (-(c * (2 * Real.pi / 3) * (x - x₀))) = 1 := by
        rw [← Real.exp_sub, ← Real.exp_add,
          show c * (2 * Real.pi * x / 3) - c * (2 * Real.pi * x₀ / 3) + -(c * (2 * Real.pi / 3) * (x - x₀)) = 0 by ring,
          Real.exp_zero]
      calc ((1 + η) / (1 - η)) ^ 2
          = ((1 + η) / (1 - η)) ^ 2 *
              (Real.exp (c * (2 * Real.pi * x / 3)) / Real.exp (c * (2 * Real.pi * x₀ / 3)) *
                Real.exp (-(c * (2 * Real.pi / 3) * (x - x₀)))) := by rw [hexp, mul_one]
        _ = ((1 + η) * (1 + η) * (B * Real.exp (c * (2 * Real.pi * x / 3)))) /
              ((1 - η) * (1 - η) * (B * Real.exp (c * (2 * Real.pi * x₀ / 3)))) *
              Real.exp (-(c * (2 * Real.pi / 3) * (x - x₀))) := by
            field_simp [hB_pos.ne', (show 1 - η ≠ 0 by linarith)]
    rw [he1]
    have hden_pos' : 0 < (1 - η) * (1 - η) * (B * Real.exp (c * (2 * Real.pi * x₀ / 3))) :=
      mul_pos (mul_pos (by linarith) (by linarith)) (mul_pos hB_pos (Real.exp_pos _))
    exact mul_le_mul_of_nonneg_right
      (div_le_div₀ (by positivity) hnum_u hden_pos' hden_l) (Real.exp_pos _).le
  exact ⟨hx_half, hx₀_half, abs_le.mpr ⟨by linarith, by linarith⟩, hexp_diff, hq_bd⟩

/-! ### 2. Complex zeros & multiplicities of Airy and HB extremals -/

/-- Every complex zero of `airyExtremal` is `airyZero k` for some `k ≥ 1`. -/
lemma airyExtremal_eq_zero_iff (z : ℂ) :
    airyExtremal z = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ z = (airyZero k : ℂ) := by
  by_cases h1 : z = (airyZero 1 : ℂ)
  · subst h1
    refine ⟨fun _ => ⟨1, le_rfl, rfl⟩, fun _ => ?_⟩
    exact HermiteBiehlerData.airy.G_eq_zero_on_S _ HermiteBiehlerData.airy.tm_mem
  · have hne : z - (airyZero 1 : ℂ) ≠ 0 := sub_ne_zero.mpr h1
    rw [airyExtremal_eq h1, neg_eq_zero, div_eq_zero_iff, sq_eq_zero_iff]
    refine ⟨fun h => ?_, fun ⟨k, hk, hzk⟩ => ?_⟩
    · rcases h with hAi | hsub
      · exact (airyAiC_eq_zero_iff z).mp hAi
      · exact absurd hsub hne
    · left; exact (airyAiC_eq_zero_iff z).mpr ⟨k, hk, hzk⟩

lemma airyProfile_eq_zero_iff (z : ℂ) :
    airyProfile z = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ z = (airyZero k : ℂ) := by
  unfold airyProfile normProfile
  have hm : (((profileMass airyExtremal)⁻¹ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (inv_ne_zero airyExtremalProfile.mass_pos.ne')
  rw [mul_eq_zero, or_iff_right hm]
  exact airyExtremal_eq_zero_iff z

lemma airyProfile_orderNat_one :
    analyticOrderNatAt airyProfile (airyZero 1 : ℂ) = 1 := by
  have hm : (((profileMass airyExtremal)⁻¹ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (inv_ne_zero airyExtremalProfile.mass_pos.ne')
  have hc : AnalyticAt ℂ (fun _ : ℂ => (((profileMass airyExtremal)⁻¹ : ℝ) : ℂ)) (airyZero 1 : ℂ) :=
    analyticAt_const
  have ha := analyticOrderAt_mul hc (differentiable_airyExtremal.analyticAt _)
  have hord : analyticOrderAt (fun _ : ℂ => (((profileMass airyExtremal)⁻¹ : ℝ) : ℂ))
      (airyZero 1 : ℂ) = 0 := hc.analyticOrderAt_eq_zero.mpr hm
  have hext1 : analyticOrderAt airyExtremal (airyZero 1 : ℂ) = 1 :=
    (differentiable_airyExtremal.analyticAt _).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      (HermiteBiehlerData.airy.G_eq_zero_on_S _ HermiteBiehlerData.airy.tm_mem)
      (HermiteBiehlerData.airy.G_deriv_ne_zero _ HermiteBiehlerData.airy.tm_mem)
  have h1 : analyticOrderAt airyProfile (airyZero 1 : ℂ) = 1 := by
    have heq : airyProfile = (fun _ : ℂ => (((profileMass airyExtremal)⁻¹ : ℝ) : ℂ)) * airyExtremal := by
      ext z; unfold airyProfile normProfile; rfl
    rw [heq, ha, hord, zero_add, hext1]
  simp [analyticOrderNatAt, h1]

lemma airyProfile_orderNat_node {k : ℕ} (hk : 2 ≤ k) :
    analyticOrderNatAt airyProfile (airyZero k : ℂ) = 2 := by
  have hm : (((profileMass airyExtremal)⁻¹ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (inv_ne_zero airyExtremalProfile.mass_pos.ne')
  have hc : AnalyticAt ℂ (fun _ : ℂ => (((profileMass airyExtremal)⁻¹ : ℝ) : ℂ)) (airyZero k : ℂ) :=
    analyticAt_const
  have ha := analyticOrderAt_mul hc (differentiable_airyExtremal.analyticAt _)
  have hord : analyticOrderAt (fun _ : ℂ => (((profileMass airyExtremal)⁻¹ : ℝ) : ℂ))
      (airyZero k : ℂ) = 0 := hc.analyticOrderAt_eq_zero.mpr hm
  have hextk : analyticOrderAt airyExtremal (airyZero k : ℂ) = 2 := by
    have hne : (airyZero k : ℂ) ≠ (airyZero 1 : ℂ) := fun h => by
      have := airyZero_lt_of_lt (n := 1) (m := k) le_rfl (by omega)
      linarith [Complex.ofReal_injective h]
    have hnhds : airyExtremal =ᶠ[𝓝 (airyZero k : ℂ)]
        ((fun u : ℂ => -(u - (airyZero 1 : ℂ))⁻¹) * (airyAiC ^ 2)) := by
      filter_upwards [continuousAt_id.eventually_ne hne] with u hu
      dsimp only [id_eq] at hu
      change airyExtremal u = -(u - (airyZero 1 : ℂ))⁻¹ * airyAiC u ^ 2
      rw [airyExtremal_eq hu]; ring
    rw [analyticOrderAt_congr hnhds]
    have han_inv : AnalyticAt ℂ (fun u : ℂ => -(u - (airyZero 1 : ℂ))⁻¹) (airyZero k : ℂ) :=
      ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hne)).neg
    have han_Ai : AnalyticAt ℂ airyAiC (airyZero k : ℂ) := differentiable_airyAiC.analyticAt _
    have hAi1 : analyticOrderAt airyAiC (airyZero k : ℂ) = 1 :=
      han_Ai.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (airyAiC_airyZero k) (airyZero_deriv_ne_zero k)
    rw [analyticOrderAt_mul han_inv (han_Ai.pow 2),
      han_inv.analyticOrderAt_eq_zero.mpr (by simp [sub_ne_zero.mpr hne]), zero_add,
      analyticOrderAt_pow han_Ai, hAi1]
    norm_num
  have h2 : analyticOrderAt airyProfile (airyZero k : ℂ) = 2 := by
    have heq : airyProfile = (fun _ : ℂ => (((profileMass airyExtremal)⁻¹ : ℝ) : ℂ)) * airyExtremal := by
      ext z; unfold airyProfile normProfile; rfl
    rw [heq, ha, hord, zero_add, hextk]
  simp [analyticOrderNatAt, h2]

/-- Every complex zero of `hbExtremal hHB hQ` is real and is a zero of `airyPQN P Q`. -/
lemma hbExtremal_eq_zero_iff {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) (z : ℂ) :
    hbExtremal hHB hQ z = 0 ↔ airyPQN P Q z = 0 := by
  have hsp := hbExtremal_spec hHB hQ
  have hprod := hsp.2.1 z
  constructor
  · intro hz
    rw [hz, zero_mul] at hprod
    have he : (((-1 : ℝ) ^ (hbTopZeros hHB hQ).card : ℝ) : ℂ) ≠ 0 := by
      push_cast; exact pow_ne_zero _ (by norm_num)
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hprod.symm).resolve_left he)
  · intro hzN
    by_cases hzs : ∃ t ∈ hbTopZeros hHB hQ, z = (t : ℂ)
    · rcases hzs with ⟨t, ht, rfl⟩
      exact hsp.2.2.2.2.2.2.1 t ht
    · have hne : at47_pr (hbTopZeros hHB hQ) z ≠ 0 := by
        unfold at47_pr
        rw [Finset.prod_ne_zero_iff]
        intro t ht h0
        exact hzs ⟨t, ht, sub_eq_zero.mp h0⟩
      rw [hzN, zero_pow two_ne_zero, mul_zero] at hprod
      exact (mul_eq_zero.mp hprod).resolve_right hne

/-- Analytic order of `normProfile (hbExtremal hHB hQ)`: `1` on `S` and `2` on other real zeros. -/
lemma hbProfile_orderNat {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) {x : ℝ}
    (hx : airyPQN P Q (x : ℂ) = 0) :
    analyticOrderNatAt (normProfile (hbExtremal hHB hQ)) (x : ℂ) =
      if x ∈ hbTopZeros hHB hQ then 1 else 2 := by
  have hsp := hbExtremal_spec hHB hQ
  set G := hbExtremal hHB hQ
  set S := hbTopZeros hHB hQ
  have hmass_pos : 0 < profileMass G :=
    (hbExtremalProfile (HermiteBiehlerData.ofQNeZero hHB hQ)).mass_pos
  have hm : (((profileMass G)⁻¹ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (inv_ne_zero hmass_pos.ne')
  have hc_inv : AnalyticAt ℂ (fun _ : ℂ => (((profileMass G)⁻¹ : ℝ) : ℂ)) (x : ℂ) :=
    analyticAt_const
  have hnorm_ord : analyticOrderAt (normProfile G) (x : ℂ) = analyticOrderAt G (x : ℂ) := by
    have ha := analyticOrderAt_mul hc_inv (hsp.1.analyticAt _)
    have h0 := hc_inv.analyticOrderAt_eq_zero.mpr hm
    have heq : normProfile G = (fun _ : ℂ => (((profileMass G)⁻¹ : ℝ) : ℂ)) * G := by
      ext z; unfold normProfile; rfl
    rw [heq, ha, h0, zero_add]
  have hordG : analyticOrderAt G (x : ℂ) = if x ∈ S then (1 : ℕ∞) else 2 := by
    split_ifs with hS
    · have hx0 : G (x : ℂ) = 0 := hsp.2.2.2.2.2.2.1 x hS
      have hx' : deriv G (x : ℂ) ≠ 0 := (HermiteBiehlerData.ofQNeZero hHB hQ).G_deriv_ne_zero x hS
      exact (hsp.1.analyticAt _).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hx0 hx'
    · have hN_an : AnalyticAt ℂ (airyPQN P Q) (x : ℂ) := (differentiable_airyPQN P Q).analyticAt _
      have hN' : deriv (airyPQN P Q) (x : ℂ) ≠ 0 := by
        rw [deriv_airyPQN]; exact (airyPQ_zero_weight_pos hHB hQ hx).2
      have hN_ord1 : analyticOrderAt (airyPQN P Q) (x : ℂ) = 1 :=
        hN_an.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hx hN'
      have hpr_ne : at47_pr S (x : ℂ) ≠ 0 := by
        unfold at47_pr
        rw [Finset.prod_ne_zero_iff]
        intro t ht h0
        have htx : t = x := Complex.ofReal_injective (sub_eq_zero.mp h0).symm
        exact hS (htx ▸ ht)
      have hprod_fn : G * at47_pr S =
          (fun _ : ℂ => (((-1 : ℝ) ^ S.card : ℝ) : ℂ)) * (airyPQN P Q ^ 2) := funext hsp.2.1
      have hL := analyticOrderAt_mul (hsp.1.analyticAt (x : ℂ))
        ((at47_pr_differentiable S).analyticAt (x : ℂ))
      have hc_sign : AnalyticAt ℂ (fun _ : ℂ => (((-1 : ℝ) ^ S.card : ℝ) : ℂ)) (x : ℂ) :=
        analyticAt_const
      have hR := analyticOrderAt_mul hc_sign (hN_an.pow 2)
      have hpr_0 : analyticOrderAt (at47_pr S) (x : ℂ) = 0 :=
        ((at47_pr_differentiable S).analyticAt _).analyticOrderAt_eq_zero.mpr hpr_ne
      have he_ne : (((-1 : ℝ) ^ S.card : ℝ) : ℂ) ≠ 0 := by push_cast; exact pow_ne_zero _ (by norm_num)
      have he_0 : analyticOrderAt (fun _ => (((-1 : ℝ) ^ S.card : ℝ) : ℂ)) (x : ℂ) = 0 :=
        hc_sign.analyticOrderAt_eq_zero.mpr he_ne
      rw [← hprod_fn] at hR
      have hsq : analyticOrderAt (airyPQN P Q ^ 2) (x : ℂ) = 2 := by
        rw [analyticOrderAt_pow hN_an, hN_ord1]; norm_num
      have heq : analyticOrderAt G (x : ℂ) + 0 = 0 + 2 := by
        calc analyticOrderAt G (x : ℂ) + 0
            = analyticOrderAt G (x : ℂ) + analyticOrderAt (at47_pr S) (x : ℂ) := by rw [hpr_0]
          _ = analyticOrderAt (G * at47_pr S) (x : ℂ) := hL.symm
          _ = analyticOrderAt (fun _ => (((-1 : ℝ) ^ S.card : ℝ) : ℂ)) (x : ℂ) +
                analyticOrderAt (airyPQN P Q ^ 2) (x : ℂ) := hR
          _ = 0 + 2 := by rw [he_0, hsq]
      simpa using heq
  rw [show analyticOrderNatAt (normProfile G) (x : ℂ) = (analyticOrderAt (normProfile G) (x : ℂ)).toNat from rfl,
    hnorm_ord, hordG]
  split_ifs <;> rfl

/-- If `g` is holomorphic on `ball (x₀ : ℂ) R`, real and nonnegative on `(x₀ - δ, x₀ + δ)`, not
identically zero, and `g x₀ = 0`, then its analytic order at `x₀` is even and `≥ 2`. -/
lemma even_analyticOrderNatAt_of_nonneg {g : ℂ → ℂ} {x₀ R δ : ℝ}
    (hg : DifferentiableOn ℂ g (ball (x₀ : ℂ) R)) (hR : 0 < R) (hδ : 0 < δ)
    (hne : ∃ w ∈ ball (x₀ : ℂ) R, g w ≠ 0)
    (hreal : ∀ x : ℝ, |x - x₀| < δ → (g (x : ℂ)).im = 0)
    (hnn : ∀ x : ℝ, |x - x₀| < δ → 0 ≤ (g (x : ℂ)).re) (hz : g (x₀ : ℂ) = 0) :
    Even (analyticOrderNatAt g (x₀ : ℂ)) ∧ 2 ≤ analyticOrderNatAt g (x₀ : ℂ) := by
  have han := (hg.analyticOnNhd isOpen_ball) (x₀ : ℂ) (mem_ball_self hR)
  obtain ⟨w, hw, hgw⟩ := hne
  have hfin_ord := order_ne_top hg hw hgw (mem_ball_self hR)
  obtain ⟨h, hh_an, hh0, hgh⟩ := han.analyticOrderAt_ne_top.mp hfin_ord
  set m := analyticOrderNatAt g (x₀ : ℂ)
  have hm_pos : 1 ≤ m := by
    have hnz := han.analyticOrderAt_ne_zero.mpr hz
    have : m ≠ 0 := fun h0 => hnz ((ENat.toNat_eq_zero.mp h0).resolve_right hfin_ord)
    omega
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgh
  have hh_cont := hh_an.continuousAt
  let ρ := min δ ε
  have hρ : 0 < ρ := lt_min hδ hε
  have hh_re_pos : 0 ≤ (h (x₀ : ℂ)).re ∧ (h (x₀ : ℂ)).im = 0 := by
    have hseq : Tendsto (fun k : ℕ => x₀ + ρ / (k + 2 : ℝ)) atTop (𝓝 x₀) := by
      simpa using tendsto_const_nhds.add
        (tendsto_const_nhds.div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ)))))
    have hcomp := hh_cont.tendsto.comp (Complex.continuous_ofReal.tendsto x₀ |>.comp hseq)
    have hval : ∀ k : ℕ, 0 ≤ (h ((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ)).re ∧
        (h ((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ)).im = 0 := fun k => by
      have hk_pos : 0 < ρ / (k + 2 : ℝ) := div_pos hρ (by positivity)
      have hdist : |x₀ + ρ / (k + 2 : ℝ) - x₀| < ρ := by
        simpa [abs_of_pos hk_pos] using (div_lt_iff₀ (by positivity : (0 : ℝ) < k + 2)).mpr (by nlinarith)
      have hm1 : ((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ) ∈ ball (x₀ : ℂ) ε := by
        rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact hdist.trans_le (min_le_right _ _)
      have heq : g ((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ) =
          (((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ) - (x₀ : ℂ)) ^ m * h ((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ) := by
        simpa [smul_eq_mul] using hball hm1
      have hpow_pos : 0 < (ρ / (k + 2 : ℝ)) ^ m := pow_pos hk_pos m
      have hpow_c : (((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ) - (x₀ : ℂ)) ^ m =
          (((ρ / (k + 2 : ℝ)) ^ m : ℝ) : ℂ) := by push_cast; ring
      rw [hpow_c] at heq
      have hne_c : (((ρ / (k + 2 : ℝ)) ^ m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpow_pos.ne'
      have hdiv : h ((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ) =
          g ((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ) / (((ρ / (k + 2 : ℝ)) ^ m : ℝ) : ℂ) := by
        rw [heq]; field_simp
      rw [hdiv]
      have him : (g ((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ)).im = 0 :=
        hreal _ (hdist.trans_le (min_le_left _ _))
      have hgcast : g ((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ) =
          ((g ((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ)).re : ℂ) :=
        Complex.ext (by simp) (by simpa using him)
      rw [hgcast, ← Complex.ofReal_div, Complex.ofReal_re, Complex.ofReal_im]
      exact ⟨div_nonneg (hnn _ (hdist.trans_le (min_le_left _ _))) hpow_pos.le, rfl⟩
    exact ⟨ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp hcomp) (Eventually.of_forall fun k => (hval k).1),
      tendsto_nhds_unique (Complex.continuous_im.tendsto _ |>.comp hcomp)
        (tendsto_const_nhds.congr fun k => (hval k).2.symm)⟩
  have hh_re_strict : 0 < (h (x₀ : ℂ)).re :=
    lt_of_le_of_ne hh_re_pos.1 fun h0 => hh0 (Complex.ext h0.symm hh_re_pos.2)
  have heven : Even m := by
    by_contra hodd; rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨ε', hε', hball'⟩ := Metric.mem_nhds_iff.mp
      ((Complex.continuous_re.continuousAt.comp hh_cont).eventually (Ioi_mem_nhds hh_re_strict))
    let η := min (ρ / 2) (ε' / 2)
    have hη_pos : 0 < η := by positivity
    have hdist_ρ : |(x₀ - η) - x₀| < ρ := by
      rw [sub_sub_cancel_left, abs_neg, abs_of_pos hη_pos]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hdist_ε' : |(x₀ - η) - x₀| < ε' := by
      rw [sub_sub_cancel_left, abs_neg, abs_of_pos hη_pos]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have heq : g ((x₀ - η : ℝ) : ℂ) = (((x₀ - η : ℝ) : ℂ) - (x₀ : ℂ)) ^ m * h ((x₀ - η : ℝ) : ℂ) := by
      have heq0 := hball (by
        rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact hdist_ρ.trans_le (min_le_right _ _))
      change g ((x₀ - η : ℝ) : ℂ) = (((x₀ - η : ℝ) : ℂ) - (x₀ : ℂ)) ^ m • h ((x₀ - η : ℝ) : ℂ) at heq0
      rwa [smul_eq_mul] at heq0
    rw [show (((x₀ - η : ℝ) : ℂ) - (x₀ : ℂ)) ^ m = ((((-η) ^ m : ℝ)) : ℂ) by push_cast; ring] at heq
    have hre_g : (g ((x₀ - η : ℝ) : ℂ)).re = (-η) ^ m * (h ((x₀ - η : ℝ) : ℂ)).re := by
      rw [heq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hpow_neg : (-η) ^ m < 0 := hodd.pow_neg_iff.mpr (by linarith)
    have hhpos : 0 < (h ((x₀ - η : ℝ) : ℂ)).re := hball' (by
      rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hdist_ε')
    have hgnn := hnn _ (hdist_ρ.trans_le (min_le_left _ _))
    have hgre_neg : (g ((x₀ - η : ℝ) : ℂ)).re < 0 := by
      rw [hre_g]; exact mul_neg_of_neg_of_pos hpow_neg hhpos
    linarith
  obtain ⟨t, ht⟩ := heven; exact ⟨⟨t, ht⟩, by omega⟩

/-! ### 3. Exponential chord bounds for `dsl:hb-mass` -/

/-- Secant bound by convexity of `exp`: for `q ≥ 0`, `0 ≤ y ≤ D` (`D > 0`),
`exp (q * y) - 1 ≤ ((exp (q * D) - 1) / D) * y`. -/
lemma exp_sub_one_le_secant {q D y : ℝ} (hD : 0 < D) (hy0 : 0 ≤ y) (hyD : y ≤ D) :
    Real.exp (q * y) - 1 ≤ ((Real.exp (q * D) - 1) / D) * y := by
  let t : ℝ := y / D
  have ht0 : 0 ≤ t := div_nonneg hy0 hD.le
  have ht1 : t ≤ 1 := (div_le_one hD).mpr hyD
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hconv := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (q * D)) h1t ht0 (by ring)
  simp only [smul_eq_mul] at hconv
  rw [show (1 - t) * 0 + t * (q * D) = q * y by dsimp [t]; field_simp [hD.ne']; ring,
    Real.exp_zero, mul_one] at hconv
  have hr : ((Real.exp (q * D) - 1) / D) * y = t * (Real.exp (q * D) - 1) := by
    dsimp [t]; ring
  rw [hr]; linarith

/-- Quadratic Taylor bound: for `q ≥ 0`, `0 ≤ y ≤ D` (`D > 0`),
`exp (q * y) - 1 ≤ q * y + ((exp (q * D) - 1 - q * D) / D ^ 2) * y ^ 2`. -/
lemma exp_sub_one_le_quadratic {q D y : ℝ} (_hq : 0 ≤ q) (hD : 0 < D) (hy0 : 0 ≤ y) (hyD : y ≤ D) :
    Real.exp (q * y) - 1 ≤ q * y + ((Real.exp (q * D) - 1 - q * D) / D ^ 2) * y ^ 2 := by
  have ht0 : 0 ≤ y / D := div_nonneg hy0 hD.le
  have ht1 : y / D ≤ 1 := (div_le_one hD).mpr hyD
  have hs := (NormedSpace.expSeries_div_hasSum_exp (q * y)).summable
  have hsD := (NormedSpace.expSeries_div_hasSum_exp (q * D)).summable
  have hsub : Real.exp (q * y) - 1 - q * y = ∑' k : ℕ, (q * y) ^ (k + 2) / ((k + 2).factorial : ℝ) := by
    have h0 : Real.exp (q * y) = ∑' k : ℕ, (q * y) ^ k / (k.factorial : ℝ) := by
      rw [Real.exp_eq_exp_ℝ]; exact (NormedSpace.expSeries_div_hasSum_exp (q * y)).tsum_eq.symm
    have hs1 := (summable_nat_add_iff 1).2 hs
    rw [h0, hs.tsum_eq_zero_add, hs1.tsum_eq_zero_add]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add, pow_one,
      Nat.factorial_one, Nat.cast_one]
    ring
  have hsubD : Real.exp (q * D) - 1 - q * D = ∑' k : ℕ, (q * D) ^ (k + 2) / ((k + 2).factorial : ℝ) := by
    have h0 : Real.exp (q * D) = ∑' k : ℕ, (q * D) ^ k / (k.factorial : ℝ) := by
      rw [Real.exp_eq_exp_ℝ]; exact (NormedSpace.expSeries_div_hasSum_exp (q * D)).tsum_eq.symm
    have hs1 := (summable_nat_add_iff 1).2 hsD
    rw [h0, hsD.tsum_eq_zero_add, hs1.tsum_eq_zero_add]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add, pow_one,
      Nat.factorial_one, Nat.cast_one]
    ring
  have hterm : ∀ k : ℕ, (q * y) ^ (k + 2) / ((k + 2).factorial : ℝ) ≤
      ((y / D) ^ 2) * ((q * D) ^ (k + 2) / ((k + 2).factorial : ℝ)) := fun k => by
    have hpow : (y / D) ^ (k + 2) ≤ (y / D) ^ 2 := pow_le_pow_of_le_one ht0 ht1 (by omega)
    have hpos : 0 ≤ (q * D) ^ (k + 2) / ((k + 2).factorial : ℝ) := by positivity
    calc (q * y) ^ (k + 2) / ((k + 2).factorial : ℝ)
        = (y / D) ^ (k + 2) * ((q * D) ^ (k + 2) / ((k + 2).factorial : ℝ)) := by
            rw [mul_pow, div_pow, mul_pow]; field_simp [hD.ne']
      _ ≤ (y / D) ^ 2 * ((q * D) ^ (k + 2) / ((k + 2).factorial : ℝ)) :=
            mul_le_mul_of_nonneg_right hpow hpos
  have hs_y : Summable (fun k : ℕ => (q * y) ^ (k + 2) / ((k + 2).factorial : ℝ)) :=
    (summable_nat_add_iff 2).2 hs
  have hs_D : Summable (fun k : ℕ => (q * D) ^ (k + 2) / ((k + 2).factorial : ℝ)) :=
    (summable_nat_add_iff 2).2 hsD
  have hsum_le := hs_y.tsum_le_tsum hterm (hs_D.mul_left ((y / D) ^ 2))
  rw [tsum_mul_left, ← hsub, ← hsubD] at hsum_le
  have hrw : (y / D) ^ 2 * (Real.exp (q * D) - 1 - q * D) =
      ((Real.exp (q * D) - 1 - q * D) / D ^ 2) * y ^ 2 := by ring
  rw [hrw] at hsum_le
  linarith

end FormalResearch.ModularBootstrap.FixedWeight