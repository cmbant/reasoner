module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerBesselTwoTerm
public import FormalResearch.ModularBootstrap.FiveTerm.LowerEdgeHankel
public import FormalResearch.ModularBootstrap.Bessel.VAsymptotic
public import FormalResearch.ModularBootstrap.Bessel.VCorollaries

/-!
# `cts:edge-hankel` (2): two-term edge Hankel asymptotic (FIVE-L, Lemma C5(2))

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, Lemma C5 (`cts:edge-hankel`)(2):
uniformly for all `v ≥ 0`, with the principal square root `√(v + i/2)`:
`G(v + i/2) = -√2 π e^{iπ/4} / (v + i/2)^{1/2} ∫_{ξ_*/2}^∞ g(t(x)) V(t(x))`
`  * ((1 - e^{-4πx})^{-2} + a₁(x)/(c'(v + i/2)) + a₂(x)/c') e^{-i(4π/3)c'vx} (2c'x/3) dx`
`  + O(M[g] / (c'^2 √(1 + v)))`.

* `besselI0C_strip_decay`: `‖I₀(w)‖ ≤ 10 e^{Re w} ‖w‖^{-1/2}` for `0 ≤ Re w` and `16 ≤ ‖w‖`;
* `besselI0C_two_term_sharp`: `‖I₀(w) - besselTwoTerm w‖ ≤ 70 e^{Re w} ‖w‖^{-5/2} + 10 ‖w‖^{-1/2}`
  for `1 ≤ Re w` and `16 ≤ ‖w‖` (upgrading the `+ 2` cut error in `besselI0C_two_term` via one IBP
  on the circular arc of `laplaceA_rotate` and on `[π/2, π - ‖w‖^{-1/2}]`);
* `besselV_three_term`: uniform three-term asymptotic
  `V(c'x²/3) / besselAs(c' L(x)) = (1 - e^{-4πx})² + virasoroV1 x / c' + O(c'^{-2})`
  for `x ≥ ξ_*/2` and `c'` large;
* `edge_hankel_two_virasoro`: the full unrestricted (`∀ v ≥ 0`) statement of `cts:edge-hankel`(2).
-/

@[expose] public section

open MeasureTheory intervalIntegral Set Metric Filter Topology
open Complex hiding exp_re
open scoped Real
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.WeightAxioms
open FormalResearch.ModularBootstrap.FixedWeightTip FormalResearch.ModularBootstrap.PoissonJensen

namespace FormalResearch.ModularBootstrap.FiveTerm

noncomputable section

/-! ## Section 1: Decay of the cut error at `‖w‖ → ∞` -/

private lemma sin_ge_two_div_pi_min {θ : ℝ} (h0 : 0 ≤ θ) (hpi : θ ≤ π) :
    2 / π * min θ (π - θ) ≤ Real.sin θ := by
  rcases le_total θ (π / 2) with h | h
  · rw [min_eq_left (by linarith)]
    exact Real.mul_le_sin h0 h
  · rw [min_eq_right (by linarith), ← Real.sin_pi_sub]
    exact Real.mul_le_sin (by linarith) (by linarith)

private lemma sin_inv_sq_integral_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ π / 2) :
    ∫ θ in (π / 2)..(π - δ), (Real.sin θ)⁻¹ ^ 2 ≤ π ^ 2 / 4 * δ⁻¹ := by
  have h1 : ∀ θ ∈ Icc (π / 2) (π - δ), (Real.sin θ)⁻¹ ^ 2 ≤ (π ^ 2 / 4) * (π - θ)⁻¹ ^ 2 := by
    intro θ hθ
    have h0 : 0 ≤ θ := by linarith [hθ.1, Real.pi_pos]
    have hpi : θ ≤ π := by linarith [hθ.2]
    have hmin : min θ (π - θ) = π - θ := min_eq_right (by linarith [hθ.1])
    have hsin : 2 / π * (π - θ) ≤ Real.sin θ := by
      simpa [hmin] using sin_ge_two_div_pi_min h0 hpi
    have hpt : 0 < π - θ := by linarith [hθ.2]
    have h2pt : 0 < 2 / π * (π - θ) := by positivity
    have hinv : (Real.sin θ)⁻¹ ≤ (2 / π * (π - θ))⁻¹ := inv_anti₀ h2pt hsin
    have hsin_pos : 0 < Real.sin θ := lt_of_lt_of_le h2pt hsin
    have hsq : (Real.sin θ)⁻¹ ^ 2 ≤ (2 / π * (π - θ))⁻¹ ^ 2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hsin_pos.le) hinv 2
    refine hsq.trans_eq ?_
    field_simp [Real.pi_pos.ne']
    ring
  have hcont_l : ContinuousOn (fun θ : ℝ => (Real.sin θ)⁻¹ ^ 2) (uIcc (π / 2) (π - δ)) := by
    intro θ hθ
    rw [uIcc_of_le (by linarith)] at hθ
    have hsin : Real.sin θ ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos]) (by linarith [hθ.2])).ne'
    exact (((Real.continuous_sin.continuousAt.inv₀ hsin).pow 2).continuousWithinAt)
  have hcont_inv : ContinuousOn (fun θ : ℝ => (π - θ)⁻¹ ^ 2) (uIcc (π / 2) (π - δ)) :=
    (ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id) fun θ hθ => by
      rw [uIcc_of_le (by linarith)] at hθ
      change π - θ ≠ 0
      linarith [hθ.2]).pow 2
  have hcont_r : ContinuousOn (fun θ : ℝ => (π ^ 2 / 4) * (π - θ)⁻¹ ^ 2)
      (uIcc (π / 2) (π - δ)) :=
    continuousOn_const.mul hcont_inv
  have hmono := intervalIntegral.integral_mono_on (by linarith)
    hcont_l.intervalIntegrable hcont_r.intervalIntegrable h1
  have hftc : ∫ θ in (π / 2)..(π - δ), (π - θ)⁻¹ ^ 2 = δ⁻¹ - (π / 2)⁻¹ := by
    have hd : ∀ θ ∈ uIcc (π / 2) (π - δ),
        HasDerivAt (fun t : ℝ => (π - t)⁻¹) ((π - θ)⁻¹ ^ 2) θ := by
      intro θ hθ
      rw [uIcc_of_le (by linarith)] at hθ
      have hne : π - θ ≠ 0 := by linarith [hθ.2]
      have hlin : HasDerivAt (fun t : ℝ => π - t) (-1) θ := (hasDerivAt_id θ).const_sub π
      convert hlin.inv hne using 1
      ring
    have hres := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont_inv.intervalIntegrable
    simp only [sub_sub_cancel] at hres
    exact hres
  rw [intervalIntegral.integral_const_mul, hftc] at hmono
  refine hmono.trans ?_
  have hsub : δ⁻¹ - (π / 2)⁻¹ ≤ δ⁻¹ := sub_le_self _ (by positivity)
  nlinarith [sq_nonneg π]

/-- On `[0, π]`, for `0 ≤ w.re` and `16 ≤ ‖w‖`, `‖I₀(w)‖ ≤ 10 e^{Re w} ‖w‖^{-1/2}`. -/
theorem besselI0C_strip_decay {w : ℂ} (hw : 0 ≤ w.re) (hwn : 16 ≤ ‖w‖) :
    ‖Integration.besselI0C w‖ ≤ 10 * Real.exp w.re * ‖w‖ ^ (-(1 : ℝ) / 2) := by
  set δ : ℝ := ‖w‖ ^ (-(1 : ℝ) / 2) with hδdef
  have hw0 : 0 < ‖w‖ := by linarith
  have hwne : w ≠ 0 := norm_ne_zero_iff.mp hw0.ne'
  have hδpos : 0 < δ := Real.rpow_pos_of_pos hw0 _
  have hδ4 : δ ≤ 1 / 4 := by
    have h1 : (1 / 4 : ℝ) = (16 : ℝ) ^ (-(1 : ℝ) / 2) := by
      rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by ring, Real.rpow_neg (by norm_num),
        ← Real.sqrt_eq_rpow, show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      norm_num
    rw [hδdef, h1]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) hwn (by norm_num)
  have hpi3 : (3 : ℝ) < π := Real.pi_gt_three
  have hδpi2 : δ < π / 2 := by linarith
  have hinv_w : ‖w‖⁻¹ = δ ^ 2 := by
    rw [hδdef, ← Real.rpow_natCast, ← Real.rpow_mul hw0.le]
    norm_num [Real.rpow_neg_one]
  have hwn_eq : ‖w‖ = δ⁻¹ ^ 2 := by
    rw [← inv_inv ‖w‖, hinv_w, inv_pow]
  have hc_int : Continuous fun θ : ℝ => Complex.exp (w * (Real.cos θ : ℝ)) := by fun_prop
  have hsplit : ∫ θ in (0 : ℝ)..π, Complex.exp (w * (Real.cos θ : ℝ)) =
      (∫ θ in (0 : ℝ)..δ, Complex.exp (w * (Real.cos θ : ℝ))) +
      (∫ θ in δ..(π - δ), Complex.exp (w * (Real.cos θ : ℝ))) +
      (∫ θ in (π - δ)..π, Complex.exp (w * (Real.cos θ : ℝ))) := by
    have h12 := (intervalIntegral.integral_add_adjacent_intervals
      (μ := volume) (hc_int.intervalIntegrable 0 δ) (hc_int.intervalIntegrable δ (π - δ))).symm
    have h123 := (intervalIntegral.integral_add_adjacent_intervals
      (μ := volume) (hc_int.intervalIntegrable 0 (π - δ)) (hc_int.intervalIntegrable (π - δ) π)).symm
    rw [← h123, ← h12]
  have hpt : ∀ θ : ℝ, ‖Complex.exp (w * (Real.cos θ : ℝ))‖ ≤ Real.exp w.re := fun θ => by
    rw [Complex.norm_exp, mul_comm, Complex.re_ofReal_mul]
    exact Real.exp_le_exp.mpr (mul_le_of_le_one_left hw (Real.cos_le_one θ))
  have hhead : ‖∫ θ in (0 : ℝ)..δ, Complex.exp (w * (Real.cos θ : ℝ))‖ ≤
      δ * Real.exp w.re := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (fun θ _ => hpt θ)).trans_eq ?_
    rw [sub_zero, abs_of_pos hδpos]; ring
  have htail : ‖∫ θ in (π - δ)..π, Complex.exp (w * (Real.cos θ : ℝ))‖ ≤
      δ * Real.exp w.re := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (fun θ _ => hpt θ)).trans_eq ?_
    rw [show π - (π - δ) = δ by ring, abs_of_pos hδpos]; ring
  have hmid : ‖∫ θ in δ..(π - δ), Complex.exp (w * (Real.cos θ : ℝ))‖ ≤
      (2 * π + π ^ 2 / 2) * δ * Real.exp w.re := by
    let F : ℝ → ℂ := fun θ => Complex.exp (w * (Real.cos θ : ℝ)) / (-w * (Real.sin θ : ℝ))
    let G : ℝ → ℂ := fun θ =>
      Complex.exp (w * (Real.cos θ : ℝ)) * ((Real.cos θ : ℂ) / (w * (Real.sin θ : ℂ) ^ 2))
    have hF_deriv : ∀ θ ∈ uIcc δ (π - δ),
        HasDerivAt F (Complex.exp (w * (Real.cos θ : ℝ)) + G θ) θ := by
      intro θ hθ
      rw [uIcc_of_le (by linarith)] at hθ
      have hsin_pos : 0 < Real.sin θ :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
      have hsinC : (Real.sin θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsin_pos.ne'
      have hden_ne : (-w * (Real.sin θ : ℝ)) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hwne) hsinC
      have hu : HasDerivAt (fun t : ℝ => Complex.exp (w * (Real.cos t : ℝ)))
          (Complex.exp (w * (Real.cos θ : ℝ)) * (w * (-(Real.sin θ : ℝ)))) θ := by
        have hcos := (Real.hasDerivAt_cos θ).ofReal_comp
        simpa [mul_comm] using (hcos.const_mul w).cexp
      have hv : HasDerivAt (fun t : ℝ => -w * (Real.sin t : ℝ)) (-w * (Real.cos θ : ℝ)) θ :=
        ((Real.hasDerivAt_sin θ).ofReal_comp).const_mul (-w)
      refine (hu.div hv hden_ne).congr_deriv ?_
      dsimp [G]
      field_simp [hwne, hsinC]
      ring
    have hG_cont : ContinuousOn G (uIcc δ (π - δ)) := by
      intro θ hθ
      rw [uIcc_of_le (by linarith)] at hθ
      have hsin_pos : 0 < Real.sin θ :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
      have hden : w * (Real.sin θ : ℂ) ^ 2 ≠ 0 :=
        mul_ne_zero hwne (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hsin_pos.ne'))
      exact ContinuousAt.continuousWithinAt (by fun_prop (disch := exact hden))
    have hF_eq := intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv
      ((hc_int.continuousOn.add hG_cont).intervalIntegrable)
    have hsplit_eq : ∫ θ in δ..(π - δ), Complex.exp (w * (Real.cos θ : ℝ)) =
        (F (π - δ) - F δ) - ∫ θ in δ..(π - δ), G θ := by
      rw [intervalIntegral.integral_add (hc_int.intervalIntegrable _ _) hG_cont.intervalIntegrable]
        at hF_eq
      exact eq_sub_of_add_eq hF_eq
    have hsin_lb : ∀ θ ∈ uIcc δ (π - δ), 2 / π * δ ≤ Real.sin θ := by
      intro θ hθ
      rw [uIcc_of_le (by linarith)] at hθ
      have hmin : δ ≤ min θ (π - θ) := le_min hθ.1 (by linarith [hθ.2])
      calc 2 / π * δ ≤ 2 / π * min θ (π - θ) := by gcongr
        _ ≤ Real.sin θ := sin_ge_two_div_pi_min (by linarith [hθ.1]) (by linarith [hθ.2])
    have hF_bd : ∀ θ ∈ uIcc δ (π - δ), ‖F θ‖ ≤ (π / 2) * δ * Real.exp w.re := by
      intro θ hθ
      have hsin := hsin_lb θ hθ
      have hsin_pos : 0 < Real.sin θ := lt_of_lt_of_le (by positivity) hsin
      dsimp [F]
      rw [norm_div, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hsin_pos.le]
      calc ‖Complex.exp (w * (Real.cos θ : ℝ))‖ / (‖w‖ * Real.sin θ)
          ≤ Real.exp w.re / (‖w‖ * (2 / π * δ)) := by gcongr; exact hpt θ
        _ = (π / 2) * δ * Real.exp w.re := by
            rw [hwn_eq]; field_simp [hδpos.ne', Real.pi_pos.ne']
    have hG_bd : ‖∫ θ in δ..(π - δ), G θ‖ ≤ (π ^ 2 / 2) * δ * Real.exp w.re := by
      have hsin_int_split :
          (∫ θ in δ..(π - δ), (Real.sin θ)⁻¹ ^ 2) =
            (∫ θ in δ..(π / 2), (Real.sin θ)⁻¹ ^ 2) +
            (∫ θ in (π / 2)..(π - δ), (Real.sin θ)⁻¹ ^ 2) := by
        have hcont_s : ContinuousOn (fun θ : ℝ => (Real.sin θ)⁻¹ ^ 2) (uIcc δ (π - δ)) := by
          intro θ hθ
          have hs := lt_of_lt_of_le (by positivity) (hsin_lb θ hθ)
          exact (((Real.continuous_sin.continuousAt.inv₀ hs.ne').pow 2).continuousWithinAt)
        exact (intervalIntegral.integral_add_adjacent_intervals
          ((hcont_s.mono (uIcc_subset_uIcc (left_mem_uIcc)
            (mem_uIcc.mpr (Or.inl ⟨hδpi2.le, by linarith⟩)))).intervalIntegrable)
          ((hcont_s.mono (uIcc_subset_uIcc (mem_uIcc.mpr (Or.inl ⟨hδpi2.le, by linarith⟩))
            right_mem_uIcc)).intervalIntegrable)).symm
      have hleft_int : ∫ θ in δ..(π / 2), (Real.sin θ)⁻¹ ^ 2 ≤ π ^ 2 / 4 * δ⁻¹ := by
        have hsub : ∫ θ in δ..(π / 2), (Real.sin θ)⁻¹ ^ 2 =
            ∫ θ in (π / 2)..(π - δ), (Real.sin θ)⁻¹ ^ 2 := by
          have hcomp := intervalIntegral.integral_comp_sub_left (fun t => (Real.sin t)⁻¹ ^ 2) π
            (a := δ) (b := π / 2)
          have heq : (fun t : ℝ => (Real.sin (π - t))⁻¹ ^ 2) = fun t : ℝ => (Real.sin t)⁻¹ ^ 2 := by
            ext t; simp [Real.sin_pi_sub]
          rw [heq, show π - π / 2 = π / 2 by ring] at hcomp
          exact hcomp
        rw [hsub]
        exact sin_inv_sq_integral_le hδpos hδpi2.le
      have hright_int : ∫ θ in (π / 2)..(π - δ), (Real.sin θ)⁻¹ ^ 2 ≤ π ^ 2 / 4 * δ⁻¹ :=
        sin_inv_sq_integral_le hδpos hδpi2.le
      have hsin_norm : ‖∫ θ in δ..(π - δ), G θ‖ ≤
          Real.exp w.re / ‖w‖ * ∫ θ in δ..(π - δ), (Real.sin θ)⁻¹ ^ 2 := by
        have hG_int_r : IntervalIntegrable
            (fun θ : ℝ => Real.exp w.re / ‖w‖ * (Real.sin θ)⁻¹ ^ 2) volume δ (π - δ) := by
          have hcont_s : ContinuousOn (fun θ : ℝ => (Real.sin θ)⁻¹ ^ 2) (uIcc δ (π - δ)) := by
            intro θ hθ
            have hs := lt_of_lt_of_le (by positivity) (hsin_lb θ hθ)
            exact (((Real.continuous_sin.continuousAt.inv₀ hs.ne').pow 2).continuousWithinAt)
          exact (hcont_s.const_mul (Real.exp w.re / ‖w‖)).intervalIntegrable
        have hmono_norm : ‖∫ θ in δ..(π - δ), G θ‖ ≤
            ∫ θ in δ..(π - δ), (Real.exp w.re / ‖w‖ * (Real.sin θ)⁻¹ ^ 2) := by
          refine (intervalIntegral.norm_integral_le_integral_norm (by linarith : δ ≤ π - δ)).trans ?_
          refine intervalIntegral.integral_mono_on (by linarith) hG_cont.norm.intervalIntegrable hG_int_r ?_
          intro θ hθ
          have hθ' : θ ∈ uIcc δ (π - δ) := by
            rw [uIcc_of_le (by linarith)]; exact hθ
          have hsin_pos : 0 < Real.sin θ := lt_of_lt_of_le (by positivity) (hsin_lb θ hθ')
          dsimp [G]
          rw [norm_mul, norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg hsin_pos.le, Real.norm_eq_abs]
          have h1 : ‖Complex.exp (w * (Real.cos θ : ℝ))‖ ≤ Real.exp w.re := hpt θ
          have h2 : |Real.cos θ| ≤ 1 := abs_cos_le_one θ
          calc ‖Complex.exp (w * (Real.cos θ : ℝ))‖ * (|Real.cos θ| / (‖w‖ * Real.sin θ ^ 2))
              ≤ Real.exp w.re * (1 / (‖w‖ * Real.sin θ ^ 2)) := by gcongr
            _ = Real.exp w.re / ‖w‖ * (Real.sin θ)⁻¹ ^ 2 := by ring
        rw [intervalIntegral.integral_const_mul] at hmono_norm
        exact hmono_norm
      calc ‖∫ θ in δ..(π - δ), G θ‖
          ≤ Real.exp w.re / ‖w‖ * (π ^ 2 / 4 * δ⁻¹ + π ^ 2 / 4 * δ⁻¹) := by
            refine hsin_norm.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
            rw [hsin_int_split]; exact add_le_add hleft_int hright_int
        _ = (π ^ 2 / 2) * δ * Real.exp w.re := by
            rw [hwn_eq]; field_simp [hδpos.ne']; ring
    rw [hsplit_eq]
    calc ‖(F (π - δ) - F δ) - ∫ θ in δ..(π - δ), G θ‖
        ≤ ‖F (π - δ) - F δ‖ + ‖∫ θ in δ..(π - δ), G θ‖ := norm_sub_le _ _
      _ ≤ (‖F (π - δ)‖ + ‖F δ‖) + ‖∫ θ in δ..(π - δ), G θ‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ((π / 2) * δ * Real.exp w.re + (π / 2) * δ * Real.exp w.re) +
            (π ^ 2 / 2) * δ * Real.exp w.re := by
          gcongr
          · exact hF_bd (π - δ) right_mem_uIcc
          · exact hF_bd δ left_mem_uIcc
      _ = (π + π ^ 2 / 2) * δ * Real.exp w.re := by ring
      _ ≤ (2 * π + π ^ 2 / 2) * δ * Real.exp w.re := by
          have : 0 ≤ π * δ * Real.exp w.re := by positivity
          linarith
  unfold Integration.besselI0C
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, hsplit]
  have hsum : ‖(∫ θ in (0 : ℝ)..δ, Complex.exp (w * (Real.cos θ : ℝ))) +
      (∫ θ in δ..(π - δ), Complex.exp (w * (Real.cos θ : ℝ))) +
      (∫ θ in (π - δ)..π, Complex.exp (w * (Real.cos θ : ℝ)))‖ ≤
      (2 + 2 * π + π ^ 2 / 2) * δ * Real.exp w.re := by
    calc _ ≤ ‖(∫ θ in (0 : ℝ)..δ, Complex.exp (w * (Real.cos θ : ℝ))) +
          (∫ θ in δ..(π - δ), Complex.exp (w * (Real.cos θ : ℝ)))‖ +
          ‖∫ θ in (π - δ)..π, Complex.exp (w * (Real.cos θ : ℝ))‖ := norm_add_le _ _
      _ ≤ (‖∫ θ in (0 : ℝ)..δ, Complex.exp (w * (Real.cos θ : ℝ))‖ +
          ‖∫ θ in δ..(π - δ), Complex.exp (w * (Real.cos θ : ℝ))‖) +
          ‖∫ θ in (π - δ)..π, Complex.exp (w * (Real.cos θ : ℝ))‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (δ * Real.exp w.re + (2 * π + π ^ 2 / 2) * δ * Real.exp w.re) + δ * Real.exp w.re := by
          gcongr
      _ = (2 + 2 * π + π ^ 2 / 2) * δ * Real.exp w.re := by ring
  calc π⁻¹ * ‖_‖ ≤ π⁻¹ * ((2 + 2 * π + π ^ 2 / 2) * δ * Real.exp w.re) := by gcongr
    _ = (2 / π + 2 + π / 2) * Real.exp w.re * δ := by field_simp [Real.pi_pos.ne']
    _ ≤ 10 * Real.exp w.re * δ := by
        have hpi4 : π < 4 := Real.pi_lt_four
        have h2p : 2 / π ≤ 1 := by rw [div_le_one Real.pi_pos]; linarith
        have hnn : 0 ≤ Real.exp w.re * δ := by positivity
        nlinarith

private lemma chord_tail_decay {w : ℂ} (hw : 0 < w.re) (hwn : 16 ≤ ‖w‖) :
    ‖∫ θ in (π / 2)..π, Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ))‖ ≤
      8 * Real.exp (-w.re) * ‖w‖ ^ (-(1 : ℝ) / 2) := by
  set δ : ℝ := ‖w‖ ^ (-(1 : ℝ) / 2) with hδdef
  have hw0 : 0 < ‖w‖ := by linarith
  have hwne : w ≠ 0 := norm_ne_zero_iff.mp hw0.ne'
  have hδpos : 0 < δ := Real.rpow_pos_of_pos hw0 _
  have hδ4 : δ ≤ 1 / 4 := by
    have h1 : (1 / 4 : ℝ) = (16 : ℝ) ^ (-(1 : ℝ) / 2) := by
      rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by ring, Real.rpow_neg (by norm_num),
        ← Real.sqrt_eq_rpow, show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      norm_num
    rw [hδdef, h1]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) hwn (by norm_num)
  have hpi3 : (3 : ℝ) < π := Real.pi_gt_three
  have hδpi2 : δ < π / 2 := by linarith
  have hinv_w : ‖w‖⁻¹ = δ ^ 2 := by
    rw [hδdef, ← Real.rpow_natCast, ← Real.rpow_mul hw0.le]
    norm_num [Real.rpow_neg_one]
  have hwn_eq : ‖w‖ = δ⁻¹ ^ 2 := by
    rw [← inv_inv ‖w‖, hinv_w, inv_pow]
  have hc_int : Continuous fun θ : ℝ => Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ)) := by
    fun_prop
  have hsplit : ∫ θ in (π / 2)..π, Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ)) =
      (∫ θ in (π / 2)..(π - δ), Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ))) +
      (∫ θ in (π - δ)..π, Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ))) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hc_int.intervalIntegrable _ _) (hc_int.intervalIntegrable _ _)).symm
  have hpt : ∀ θ ∈ Icc (π / 2) π,
      ‖Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ))‖ ≤ Real.exp (-w.re) := by
    intro θ hθ
    rw [Complex.norm_exp, mul_comm, Complex.re_ofReal_mul, Complex.neg_re]
    apply Real.exp_le_exp.mpr
    have hcos : Real.cos θ ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 (by linarith [hθ.2, Real.pi_pos])
    nlinarith
  have htail : ‖∫ θ in (π - δ)..π, Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ))‖ ≤
      δ * Real.exp (-w.re) := by
    calc ‖∫ θ in (π - δ)..π, Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ))‖
        ≤ Real.exp (-w.re) * |π - (π - δ)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (C := Real.exp (-w.re)) fun θ hθ => by
            rw [uIoc_of_le (by linarith)] at hθ
            exact hpt θ ⟨by linarith [hθ.1], hθ.2⟩
      _ = δ * Real.exp (-w.re) := by rw [show π - (π - δ) = δ by ring, abs_of_pos hδpos]; ring
  let F : ℝ → ℂ := fun θ =>
    Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ)) / (-w * (Real.sin θ : ℝ))
  let G : ℝ → ℂ := fun θ =>
    Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ)) * ((Real.cos θ : ℂ) / (w * (Real.sin θ : ℂ) ^ 2))
  have hsin_lb : ∀ θ ∈ uIcc (π / 2) (π - δ), 2 / π * δ ≤ Real.sin θ := by
    intro θ hθ
    rw [uIcc_of_le (by linarith)] at hθ
    have hmin : min θ (π - θ) = π - θ := min_eq_right (by linarith [hθ.1])
    calc 2 / π * δ ≤ 2 / π * (π - θ) := by gcongr; linarith [hθ.2]
      _ = 2 / π * min θ (π - θ) := by rw [hmin]
      _ ≤ Real.sin θ := sin_ge_two_div_pi_min (by linarith [hθ.1]) (by linarith [hθ.2])
  have hF_deriv : ∀ θ ∈ uIcc (π / 2) (π - δ),
      HasDerivAt F (Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ)) + G θ) θ := by
    intro θ hθ
    have hsin_pos : 0 < Real.sin θ := lt_of_lt_of_le (by positivity) (hsin_lb θ hθ)
    have hsinC : (Real.sin θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsin_pos.ne'
    have hden_ne : (-w * (Real.sin θ : ℝ)) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hwne) hsinC
    have hu : HasDerivAt (fun t : ℝ => Complex.exp (-w * ((1 - Real.cos t : ℝ) : ℂ)))
        (Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ)) * (-w * (Real.sin θ : ℝ))) θ := by
      have hcos : HasDerivAt (fun t : ℝ => (1 : ℂ) - ((Real.cos t : ℝ) : ℂ))
          ((Real.sin θ : ℝ) : ℂ) θ := by
        have h1 := ((Real.hasDerivAt_cos θ).ofReal_comp).const_sub (1 : ℂ)
        exact h1.congr_deriv (by simp)
      have heq : (fun t : ℝ => Complex.exp (-w * ((1 - Real.cos t : ℝ) : ℂ))) =
          fun t : ℝ => Complex.exp (-w * ((1 : ℂ) - ((Real.cos t : ℝ) : ℂ))) := by
        ext t; push_cast; rfl
      rw [heq]
      convert (hcos.const_mul (-w)).cexp using 1
      push_cast; ring
    have hv : HasDerivAt (fun t : ℝ => -w * (Real.sin t : ℝ)) (-w * (Real.cos θ : ℝ)) θ :=
      ((Real.hasDerivAt_sin θ).ofReal_comp).const_mul (-w)
    refine (hu.div hv hden_ne).congr_deriv ?_
    dsimp [G]
    field_simp [hwne, hsinC]
    ring
  have hG_cont : ContinuousOn G (uIcc (π / 2) (π - δ)) := by
    intro θ hθ
    have hsin_pos : 0 < Real.sin θ := lt_of_lt_of_le (by positivity) (hsin_lb θ hθ)
    have hden : w * (Real.sin θ : ℂ) ^ 2 ≠ 0 :=
      mul_ne_zero hwne (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hsin_pos.ne'))
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := exact hden))
  have hF_eq := intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv
    ((hc_int.continuousOn.add hG_cont).intervalIntegrable)
  have hsplit_eq : ∫ θ in (π / 2)..(π - δ), Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ)) =
      (F (π - δ) - F (π / 2)) - ∫ θ in (π / 2)..(π - δ), G θ := by
    rw [intervalIntegral.integral_add (hc_int.intervalIntegrable _ _) hG_cont.intervalIntegrable]
      at hF_eq
    exact eq_sub_of_add_eq hF_eq
  have hF_bd : ∀ θ ∈ uIcc (π / 2) (π - δ), ‖F θ‖ ≤ (π / 2) * δ * Real.exp (-w.re) := by
    intro θ hθ
    have hsin := hsin_lb θ hθ
    have hsin_pos : 0 < Real.sin θ := lt_of_lt_of_le (by positivity) hsin
    rw [uIcc_of_le (by linarith)] at hθ
    have hmem : θ ∈ Icc (π / 2) π := ⟨hθ.1, by linarith [hθ.2]⟩
    dsimp [F]
    rw [norm_div, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hsin_pos.le]
    calc _ ≤ Real.exp (-w.re) / (‖w‖ * (2 / π * δ)) := by gcongr; exact hpt θ hmem
      _ = (π / 2) * δ * Real.exp (-w.re) := by
          rw [hwn_eq]; field_simp [hδpos.ne', Real.pi_pos.ne']
  have hG_bd : ‖∫ θ in (π / 2)..(π - δ), G θ‖ ≤ (π ^ 2 / 4) * δ * Real.exp (-w.re) := by
    have hG_int_r : IntervalIntegrable
        (fun θ : ℝ => Real.exp (-w.re) / ‖w‖ * (Real.sin θ)⁻¹ ^ 2) volume (π / 2) (π - δ) := by
      have hcont_s : ContinuousOn (fun θ : ℝ => (Real.sin θ)⁻¹ ^ 2) (uIcc (π / 2) (π - δ)) := by
        intro θ hθ
        have hs := lt_of_lt_of_le (by positivity) (hsin_lb θ hθ)
        exact (((Real.continuous_sin.continuousAt.inv₀ hs.ne').pow 2).continuousWithinAt)
      exact (hcont_s.const_mul (Real.exp (-w.re) / ‖w‖)).intervalIntegrable
    have hsin_norm : ‖∫ θ in (π / 2)..(π - δ), G θ‖ ≤
        Real.exp (-w.re) / ‖w‖ * ∫ θ in (π / 2)..(π - δ), (Real.sin θ)⁻¹ ^ 2 := by
      have hmono_norm : ‖∫ θ in (π / 2)..(π - δ), G θ‖ ≤
          ∫ θ in (π / 2)..(π - δ), (Real.exp (-w.re) / ‖w‖ * (Real.sin θ)⁻¹ ^ 2) := by
        refine (intervalIntegral.norm_integral_le_integral_norm (by linarith : π / 2 ≤ π - δ)).trans ?_
        refine intervalIntegral.integral_mono_on (by linarith) hG_cont.norm.intervalIntegrable hG_int_r ?_
        intro θ hθ
        have hθ' : θ ∈ uIcc (π / 2) (π - δ) := by
          rw [uIcc_of_le (by linarith)]; exact hθ
        have hmem : θ ∈ Icc (π / 2) π := ⟨hθ.1, by linarith [hθ.2]⟩
        have hsin_pos : 0 < Real.sin θ := lt_of_lt_of_le (by positivity) (hsin_lb θ hθ')
        dsimp [G]
        rw [norm_mul, norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg hsin_pos.le, Real.norm_eq_abs]
        calc _ ≤ Real.exp (-w.re) * (1 / (‖w‖ * Real.sin θ ^ 2)) := by
              gcongr; exact hpt θ hmem; exact abs_cos_le_one θ
          _ = Real.exp (-w.re) / ‖w‖ * (Real.sin θ)⁻¹ ^ 2 := by ring
      rw [intervalIntegral.integral_const_mul] at hmono_norm
      exact hmono_norm
    calc ‖∫ θ in (π / 2)..(π - δ), G θ‖
        ≤ Real.exp (-w.re) / ‖w‖ * (π ^ 2 / 4 * δ⁻¹) := by
          refine hsin_norm.trans (mul_le_mul_of_nonneg_left
            (sin_inv_sq_integral_le hδpos hδpi2.le) (by positivity))
      _ = (π ^ 2 / 4) * δ * Real.exp (-w.re) := by rw [hwn_eq]; field_simp [hδpos.ne']
  rw [hsplit, hsplit_eq]
  calc ‖((F (π - δ) - F (π / 2)) - ∫ θ in (π / 2)..(π - δ), G θ) +
        ∫ θ in (π - δ)..π, Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ))‖
      ≤ (‖F (π - δ)‖ + ‖F (π / 2)‖) + ‖∫ θ in (π / 2)..(π - δ), G θ‖ +
        ‖∫ θ in (π - δ)..π, Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ))‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ ((π / 2) * δ * Real.exp (-w.re) + (π / 2) * δ * Real.exp (-w.re)) +
          (π ^ 2 / 4) * δ * Real.exp (-w.re) + δ * Real.exp (-w.re) := by
        gcongr
        · exact hF_bd (π - δ) right_mem_uIcc
        · exact hF_bd (π / 2) left_mem_uIcc
    _ = (π + π ^ 2 / 4 + 1) * Real.exp (-w.re) * δ := by ring
    _ ≤ 8 * Real.exp (-w.re) * δ := by
        have hpi4 : π < 3.15 := Real.pi_lt_d2
        have hpi_sq : π ^ 2 / 4 < 2.6 := by nlinarith
        have hnn : 0 ≤ Real.exp (-w.re) * δ := by positivity
        nlinarith

private lemma laplaceA_rotate_decay {w : ℂ} (hw : 1 ≤ w.re) :
    ‖laplaceA w - Complex.exp (-((w.arg / 2 : ℝ) * I)) *
        ∫ s : ℝ in (0 : ℝ)..1, Complex.exp (-(‖w‖ : ℂ) * (s : ℂ) ^ 2) *
          psiC ((s : ℂ) * Complex.exp (-((w.arg / 2 : ℝ) * I)))‖ ≤
      4 * Real.exp (-w.re) / ‖w‖ := by
  set β : ℝ := w.arg / 2 with hβ
  have hw0 : 0 < w.re := by linarith
  have hwn0 : 0 < ‖w‖ := lt_of_lt_of_le hw0 (Complex.re_le_norm w)
  have hwne : w ≠ 0 := norm_ne_zero_iff.mp hwn0.ne'
  have harg : |w.arg| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hw0)
  have hβ' : |β| < π / 4 := by rw [hβ, abs_div]; simp; linarith
  have hwexp : w = (‖w‖ : ℂ) * Complex.exp ((2 * β : ℝ) * I) := by
    have := Complex.norm_mul_exp_arg_mul_I w
    rw [hβ]; push_cast; rw [show 2 * ((w.arg : ℂ) / 2) = (w.arg : ℂ) by ring]; exact this.symm
  have hf : DifferentiableOn ℂ (fun r : ℂ => Complex.exp (-w * r ^ 2) * psiC r) (ball 0 (√2)) :=
    (by fun_prop : Differentiable ℂ fun r : ℂ => Complex.exp (-w * r ^ 2)).differentiableOn.mul
      psiC_differentiableOn
  have hrot := rotate_ray hf one_pos sqrt_two_gt_one β
  have hA : laplaceA w = ∫ r : ℝ in (0 : ℝ)..1, Complex.exp (-w * (r : ℂ) ^ 2) * psiC (r : ℂ) := rfl
  have hray : ∀ s : ℝ, Complex.exp (-w * ((s : ℂ) * Complex.exp (-(β * I))) ^ 2) =
      Complex.exp (-(‖w‖ : ℂ) * (s : ℂ) ^ 2) := by
    intro s
    congr 1
    conv_lhs => rw [hwexp]
    rw [mul_pow, ← Complex.exp_nat_mul]
    have h2 : Complex.exp (((2 * β : ℝ) : ℂ) * I) * Complex.exp (-(((2 * β : ℝ) : ℂ) * I)) = 1 := by
      rw [← Complex.exp_add]; simp
    calc -((‖w‖ : ℂ) * Complex.exp (((2 * β : ℝ) : ℂ) * I)) *
          ((s : ℂ) ^ 2 * Complex.exp (((2 : ℕ) : ℂ) * -((β : ℂ) * I)))
        = -(‖w‖ : ℂ) * (s : ℂ) ^ 2 * (Complex.exp (((2 * β : ℝ) : ℂ) * I) *
            Complex.exp (-(((2 * β : ℝ) : ℂ) * I))) := by push_cast; ring
      _ = _ := by rw [h2]; ring
  have hint_eq : ∫ s : ℝ in (0 : ℝ)..1, Complex.exp (-w * ((s : ℂ) * Complex.exp (-(β * I))) ^ 2) *
      psiC ((s : ℂ) * Complex.exp (-(β * I))) =
      ∫ s : ℝ in (0 : ℝ)..1, Complex.exp (-(‖w‖ : ℂ) * (s : ℂ) ^ 2) *
        psiC ((s : ℂ) * Complex.exp (-(β * I))) :=
    intervalIntegral.integral_congr (fun s _ => by simp only [hray])
  rw [hint_eq] at hrot
  rw [hA, hrot]
  simp only [add_sub_cancel_left]
  let E : ℝ → ℂ := fun γ => Complex.exp (-w * Complex.exp (-((2 * γ : ℝ) : ℂ) * I))
  let ψd : ℂ → ℂ := fun u => psiC u * (u / 2) / (1 - u ^ 2 / 2)
  have hpsi_deriv : ∀ {u : ℂ}, ‖u‖ < √2 → HasDerivAt psiC (ψd u) u := by
    intro u hu
    have hre : 0 < (1 - u ^ 2 / 2).re := one_sub_re_pos hu
    have hlog : HasDerivAt (fun z : ℂ => Complex.log (1 - z ^ 2 / 2)) (-u / (1 - u ^ 2 / 2)) u := by
      have hg : HasDerivAt (fun z : ℂ => 1 - z ^ 2 / 2) (-u) u := by
        simpa using (((hasDerivAt_pow 2 u).div_const 2).const_sub (1 : ℂ)).congr_deriv (by ring)
      exact (Complex.hasDerivAt_clog (Or.inl hre)).comp u hg |>.congr_deriv (by ring)
    have hcexp := ((hlog.const_mul (-(1 / 2 : ℂ))).cexp)
    refine hcexp.congr_deriv ?_
    change Complex.exp (-(1 / 2 : ℂ) * Complex.log (1 - u ^ 2 / 2)) *
        (-(1 / 2 : ℂ) * (-u / (1 - u ^ 2 / 2))) = ψd u
    dsimp [psiC, ψd]
    ring
  let P : ℝ → ℂ := fun γ => -(1 / (2 * w)) * (E γ * (psiC (Complex.exp (-((γ : ℂ) * I))) *
    Complex.exp ((γ : ℂ) * I)))
  let Q : ℝ → ℂ := fun γ => -(1 / (2 * w)) * (E γ *
    (I * psiC (Complex.exp (-((γ : ℂ) * I))) * Complex.exp ((γ : ℂ) * I) -
     I * ψd (Complex.exp (-((γ : ℂ) * I)))))
  have hP_deriv : ∀ γ : ℝ, HasDerivAt P
      (E γ * psiC (Complex.exp (-((γ : ℂ) * I))) * (-I * Complex.exp (-((γ : ℂ) * I))) + Q γ) γ := by
    intro γ
    let uγ : ℂ := Complex.exp (-((γ : ℂ) * I))
    have huγ_norm : ‖uγ‖ = 1 := norm_exp_neg_I γ
    have huγ_lt : ‖uγ‖ < √2 := lt_of_eq_of_lt huγ_norm sqrt_two_gt_one
    have hE_d : HasDerivAt E (E γ * (2 * I * w * Complex.exp (-((2 * γ : ℝ) : ℂ) * I))) γ := by
      have harg_d : HasDerivAt (fun t : ℝ => -w * Complex.exp (-((2 : ℂ) * (t : ℂ) * I)))
          (-w * ((-((2 : ℂ) * I)) * Complex.exp (-((2 : ℂ) * (γ : ℂ) * I)))) γ := by
        have hlin : HasDerivAt (fun t : ℝ => -(2 : ℂ) * (t : ℂ) * I) (-(2 * I)) γ := by
          have := (((hasDerivAt_id γ).ofReal_comp).const_mul (-(2 : ℂ))).mul_const I
          exact this.congr_deriv (by ring)
        convert (hlin.cexp.const_mul (-w)) using 1
        ring
      have hE_eq : E = fun t : ℝ => Complex.exp (-w * Complex.exp (-((2 : ℂ) * (t : ℂ) * I))) := by
        ext t; dsimp [E]; push_cast; ring_nf
      rw [hE_eq]
      exact harg_d.cexp.congr_deriv (by push_cast; ring)
    have hu_d : HasDerivAt (fun t : ℝ => Complex.exp (-((t : ℂ) * I))) (-I * uγ) γ := by
      have hlin : HasDerivAt (fun t : ℝ => -((t : ℂ) * I)) (-I) γ := by
        have := (((hasDerivAt_id γ).ofReal_comp).mul_const I).neg
        exact this.congr_deriv (by simp)
      convert hlin.cexp using 1
      ring
    have hpsi_d : HasDerivAt (fun t : ℝ => psiC (Complex.exp (-((t : ℂ) * I))))
        (ψd uγ * (-I * uγ)) γ := (hpsi_deriv huγ_lt).comp γ (by convert hu_d using 1)
    have he_d : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * I)) (I * Complex.exp ((γ : ℂ) * I)) γ := by
      have hlin : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I γ := by
        have := (hasDerivAt_id γ).ofReal_comp.mul_const I
        exact this.congr_deriv (by simp)
      convert hlin.cexp using 1
      ring
    have hprod := (hE_d.mul (hpsi_d.mul he_d)).const_mul (-(1 / (2 * w)))
    refine hprod.congr_deriv ?_
    have he_mul : Complex.exp (-((2 * γ : ℝ) : ℂ) * I) * Complex.exp ((γ : ℂ) * I) =
        Complex.exp (-((γ : ℂ) * I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hu_mul : uγ * Complex.exp ((γ : ℂ) * I) = 1 := by
      dsimp [uγ]; rw [← Complex.exp_add]; simp
    change -(1 / (2 * w)) * (E γ * (2 * I * w * Complex.exp (-((2 * γ : ℝ) : ℂ) * I)) *
        (psiC uγ * Complex.exp ((γ : ℂ) * I)) +
      E γ * (ψd uγ * (-I * uγ) * Complex.exp ((γ : ℂ) * I) +
        psiC uγ * (I * Complex.exp ((γ : ℂ) * I)))) =
      E γ * psiC uγ * (-I * uγ) + Q γ
    dsimp [Q]
    calc -(1 / (2 * w)) * (E γ * (2 * I * w * Complex.exp (-((2 * γ : ℝ) : ℂ) * I)) *
          (psiC uγ * Complex.exp ((γ : ℂ) * I)) +
        E γ * (ψd uγ * (-I * uγ) * Complex.exp ((γ : ℂ) * I) +
          psiC uγ * (I * Complex.exp ((γ : ℂ) * I))))
        = E γ * psiC uγ * (-I * (Complex.exp (-((2 * γ : ℝ) : ℂ) * I) * Complex.exp ((γ : ℂ) * I))) *
            (w / w) -
          (1 / (2 * w)) * (E γ * (I * psiC uγ * Complex.exp ((γ : ℂ) * I) -
            I * ψd uγ * (uγ * Complex.exp ((γ : ℂ) * I)))) := by ring
      _ = E γ * psiC uγ * (-I * uγ) +
            -(1 / (2 * w)) * (E γ * (I * psiC uγ * Complex.exp ((γ : ℂ) * I) - I * ψd uγ)) := by
          rw [he_mul, hu_mul, div_self hwne]; ring
  have hQ_cont : Continuous Q := by
    have hpsi_c : Continuous fun γ : ℝ => psiC (Complex.exp (-((γ : ℂ) * I))) :=
      psiC_differentiableOn.continuousOn.comp_continuous (by fun_prop) fun γ => by
        rw [mem_ball_zero_iff, norm_exp_neg_I]; exact sqrt_two_gt_one
    have hden_c : Continuous fun γ : ℝ => (1 - (Complex.exp (-((γ : ℂ) * I))) ^ 2 / 2)⁻¹ :=
      Continuous.inv₀ (by fun_prop) fun γ => by
        have hre := one_sub_re_pos (lt_of_eq_of_lt (norm_exp_neg_I γ) sqrt_two_gt_one)
        intro h; rw [h] at hre; simp at hre
    have hψd_c : Continuous fun γ : ℝ => ψd (Complex.exp (-((γ : ℂ) * I))) := by
      dsimp [ψd]
      simp_rw [div_eq_mul_inv]
      exact (hpsi_c.mul (by fun_prop : Continuous fun γ : ℝ => Complex.exp (-((γ : ℂ) * I)) / 2)).mul hden_c
    dsimp [Q, E]
    exact continuous_const.mul
      ((by fun_prop : Continuous fun γ : ℝ => Complex.exp (-w * Complex.exp (-((2 * γ : ℝ) : ℂ) * I))).mul
        (((continuous_const.mul hpsi_c).mul (by fun_prop : Continuous fun γ : ℝ => Complex.exp ((γ : ℂ) * I))).sub
          (continuous_const.mul hψd_c)))
  have harc_cont : Continuous fun γ : ℝ =>
      E γ * psiC (Complex.exp (-((γ : ℂ) * I))) * (-I * Complex.exp (-((γ : ℂ) * I))) := by
    have hpsi_c : Continuous fun γ : ℝ => psiC (Complex.exp (-((γ : ℂ) * I))) :=
      psiC_differentiableOn.continuousOn.comp_continuous (by fun_prop) fun γ => by
        rw [mem_ball_zero_iff, norm_exp_neg_I]; exact sqrt_two_gt_one
    dsimp [E]
    exact (((by fun_prop : Continuous fun γ : ℝ =>
      Complex.exp (-w * Complex.exp (-((2 * γ : ℝ) : ℂ) * I))).mul hpsi_c).mul
      (by fun_prop : Continuous fun γ : ℝ => -I * Complex.exp (-((γ : ℂ) * I))))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun γ _ => hP_deriv γ)
    ((harc_cont.add hQ_cont).intervalIntegrable _ _)
  have hint_rew : ∫ γ in β..0,
      Complex.exp (-w * (((1 : ℝ) : ℂ) * Complex.exp (-((γ : ℂ) * I))) ^ 2) *
        psiC (((1 : ℝ) : ℂ) * Complex.exp (-((γ : ℂ) * I))) *
          (-I * ((1 : ℝ) : ℂ) * Complex.exp (-((γ : ℂ) * I))) =
      (P 0 - P β) - ∫ γ in β..0, Q γ := by
    have heq : (fun γ : ℝ =>
        Complex.exp (-w * (((1 : ℝ) : ℂ) * Complex.exp (-((γ : ℂ) * I))) ^ 2) *
          psiC (((1 : ℝ) : ℂ) * Complex.exp (-((γ : ℂ) * I))) *
            (-I * ((1 : ℝ) : ℂ) * Complex.exp (-((γ : ℂ) * I)))) =
        fun γ => E γ * psiC (Complex.exp (-((γ : ℂ) * I))) * (-I * Complex.exp (-((γ : ℂ) * I))) := by
      ext γ; dsimp [E]; simp only [Complex.ofReal_one, one_mul, mul_pow, ← Complex.exp_nat_mul]
      congr 2; congr 2; push_cast; ring
    rw [heq]
    rw [intervalIntegral.integral_add (harc_cont.intervalIntegrable _ _)
      (hQ_cont.intervalIntegrable _ _)] at hftc
    exact eq_sub_of_add_eq hftc
  have hE_bd : ∀ γ ∈ uIcc β 0, ‖E γ‖ ≤ Real.exp (-w.re) := by
    intro γ hγ
    have hγ' : |β - γ| ≤ |β| := by
      rw [uIcc] at hγ
      rcases le_total β 0 with h | h
      · rw [min_eq_left h, max_eq_right h] at hγ
        rw [abs_of_nonpos h, abs_le]; constructor <;> linarith [hγ.1, hγ.2]
      · rw [min_eq_right h, max_eq_left h] at hγ
        rw [abs_of_nonneg h, abs_le]; constructor <;> linarith [hγ.1, hγ.2]
    have hcos : Real.cos (2 * β) ≤ Real.cos (2 * (β - γ)) := by
      have h1 : |2 * (β - γ)| ≤ |2 * β| := by rw [abs_mul, abs_mul]; simp; linarith
      have h2 : |2 * β| ≤ π := by rw [abs_mul]; simp; linarith [Real.pi_pos]
      rw [← Real.cos_abs (2 * β), ← Real.cos_abs (2 * (β - γ))]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) h2 h1
    have hre : (w * Complex.exp (-((2 * γ : ℝ) : ℂ) * I)).re = ‖w‖ * Real.cos (2 * (β - γ)) := by
      conv_lhs => rw [hwexp]
      rw [show ((‖w‖ : ℂ) * Complex.exp (((2 * β : ℝ) : ℂ) * I)) *
            Complex.exp (-((2 * γ : ℝ) : ℂ) * I) =
          (‖w‖ : ℂ) * Complex.exp (((2 * (β - γ) : ℝ) : ℂ) * I) by
        rw [mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring]
      rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    have hRe : w.re = ‖w‖ * Real.cos (2 * β) := by
      conv_lhs => rw [hwexp]
      rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    dsimp [E]
    rw [Complex.norm_exp, neg_mul, Complex.neg_re, hre, hRe]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hcos (norm_nonneg w)])
  have hP_bd : ∀ γ ∈ uIcc β 0, ‖P γ‖ ≤ √2 * Real.exp (-w.re) / (2 * ‖w‖) := by
    intro γ hγ
    have hu : ‖Complex.exp (-((γ : ℂ) * I))‖ = 1 := norm_exp_neg_I γ
    have he : ‖Complex.exp ((γ : ℂ) * I)‖ = 1 := by simpa using norm_exp_neg_I (-γ)
    have hpsi : ‖psiC (Complex.exp (-((γ : ℂ) * I)))‖ ≤ √2 := psiC_norm_le hu.le
    dsimp [P]
    rw [norm_mul, norm_neg, norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      norm_mul, norm_mul, he, mul_one]
    calc (1 / (2 * ‖w‖)) * (‖E γ‖ * ‖psiC (Complex.exp (-((γ : ℂ) * I)))‖)
        ≤ (1 / (2 * ‖w‖)) * (Real.exp (-w.re) * √2) := by
          gcongr; exact hE_bd γ hγ
      _ = √2 * Real.exp (-w.re) / (2 * ‖w‖) := by ring
  have hQ_bd : ∀ γ ∈ uIcc β 0, ‖Q γ‖ ≤ (2 * √2) * Real.exp (-w.re) / (2 * ‖w‖) := by
    intro γ hγ
    have hu : ‖Complex.exp (-((γ : ℂ) * I))‖ = 1 := norm_exp_neg_I γ
    have he : ‖Complex.exp ((γ : ℂ) * I)‖ = 1 := by simpa using norm_exp_neg_I (-γ)
    have hpsi : ‖psiC (Complex.exp (-((γ : ℂ) * I)))‖ ≤ √2 := psiC_norm_le hu.le
    have hψd : ‖ψd (Complex.exp (-((γ : ℂ) * I)))‖ ≤ √2 := by
      dsimp [ψd]
      have hden := norm_sub_one_ge hu.le
      rw [norm_div, norm_mul, norm_div, hu, Complex.norm_ofNat]
      calc ‖psiC (Complex.exp (-((γ : ℂ) * I)))‖ * (1 / 2) /
            ‖1 - (Complex.exp (-((γ : ℂ) * I))) ^ 2 / 2‖
          ≤ √2 * (1 / 2) / (1 / 2) := by gcongr
        _ = √2 := by ring
    dsimp [Q]
    rw [norm_mul, norm_neg, norm_div, norm_one, norm_mul, Complex.norm_ofNat, norm_mul]
    have hmid : ‖I * psiC (Complex.exp (-((γ : ℂ) * I))) * Complex.exp ((γ : ℂ) * I) -
        I * ψd (Complex.exp (-((γ : ℂ) * I)))‖ ≤ 2 * √2 := by
      calc _ ≤ ‖I * psiC (Complex.exp (-((γ : ℂ) * I))) * Complex.exp ((γ : ℂ) * I)‖ +
            ‖I * ψd (Complex.exp (-((γ : ℂ) * I)))‖ := norm_sub_le _ _
        _ = ‖psiC (Complex.exp (-((γ : ℂ) * I)))‖ + ‖ψd (Complex.exp (-((γ : ℂ) * I)))‖ := by
            rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, he, one_mul, mul_one]
        _ ≤ √2 + √2 := add_le_add hpsi hψd
        _ = 2 * √2 := by ring
    calc 1 / (2 * ‖w‖) * (‖E γ‖ * ‖_‖)
        ≤ 1 / (2 * ‖w‖) * (Real.exp (-w.re) * (2 * √2)) := by
          gcongr; exact hE_bd γ hγ
      _ = (2 * √2) * Real.exp (-w.re) / (2 * ‖w‖) := by ring
  have hQ_int : ‖∫ γ in β..0, Q γ‖ ≤ (2 * √2) * Real.exp (-w.re) / (2 * ‖w‖) := by
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (fun γ hγ =>
      hQ_bd γ (uIoc_subset_uIcc hγ))
    have hβ1 : |0 - β| ≤ 1 := by
      rw [zero_sub, abs_neg]; linarith [Real.pi_lt_four]
    exact h1.trans (mul_le_of_le_one_right (by positivity) hβ1)
  rw [hint_rew]
  calc ‖(P 0 - P β) - ∫ γ in β..0, Q γ‖
      ≤ (‖P 0‖ + ‖P β‖) + ‖∫ γ in β..0, Q γ‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (√2 * Real.exp (-w.re) / (2 * ‖w‖) + √2 * Real.exp (-w.re) / (2 * ‖w‖)) +
          (2 * √2) * Real.exp (-w.re) / (2 * ‖w‖) := by
        gcongr
        · exact hP_bd 0 right_mem_uIcc
        · exact hP_bd β left_mem_uIcc
    _ = 2 * √2 * Real.exp (-w.re) / ‖w‖ := by ring
    _ ≤ 4 * Real.exp (-w.re) / ‖w‖ := by
        have hs2 : √2 ≤ 2 := by apply Real.sqrt_le_iff.mpr; constructor <;> norm_num
        gcongr

private lemma cos_half_change_eq (z : ℂ) :
    ∫ θ in (0 : ℝ)..(π / 2), Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) =
      ∫ t in (0 : ℝ)..1, Complex.exp (-z * (t : ℂ) ^ 2) *
        ((√2 / √(1 - t ^ 2 / 2) : ℝ) : ℂ) := by
  let f : ℝ → ℝ := fun θ => √2 * Real.sin (θ / 2)
  let f' : ℝ → ℝ := fun θ => (√2 / 2) * Real.cos (θ / 2)
  let g : ℝ → ℂ := fun t => Complex.exp (-z * (t : ℂ) ^ 2) * ((√2 / √(1 - t ^ 2 / 2) : ℝ) : ℂ)
  have hderiv : ∀ θ ∈ uIcc (0 : ℝ) (π / 2), HasDerivAt f (f' θ) θ := by
    intro θ _
    have h1 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) θ := (hasDerivAt_id θ).div_const 2
    have h2 : HasDerivAt (fun x : ℝ => Real.sin (x / 2)) (Real.cos (θ / 2) * (1 / 2)) θ :=
      h1.sin
    exact (h2.const_mul √2).congr_deriv (by dsimp [f']; ring)
  have hf'_cont : ContinuousOn f' (uIcc (0 : ℝ) (π / 2)) :=
    (by fun_prop : Continuous f').continuousOn
  have hg_cont : ContinuousOn g (f '' uIcc (0 : ℝ) (π / 2)) := by
    have himg : f '' uIcc (0 : ℝ) (π / 2) ⊆ Icc 0 1 := by
      rintro t ⟨θ, hθ, rfl⟩
      rw [uIcc_of_le (by positivity)] at hθ
      have hsin_nn : 0 ≤ Real.sin (θ / 2) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      have hsin_le : Real.sin (θ / 2) ≤ Real.sin (π / 4) :=
        Real.strictMonoOn_sin.monotoneOn
          ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
          ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
          (by linarith [hθ.2])
      rw [Real.sin_pi_div_four] at hsin_le
      refine ⟨mul_nonneg (Real.sqrt_nonneg _) hsin_nn, ?_⟩
      calc √2 * Real.sin (θ / 2) ≤ √2 * (√2 / 2) := by gcongr
        _ = 1 := by rw [← mul_div_assoc, Real.mul_self_sqrt zero_le_two]; norm_num
    refine ContinuousOn.mono ?_ himg
    intro t ht
    have hpos : 0 < 1 - t ^ 2 / 2 := by nlinarith [ht.1, ht.2]
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun s : ℝ => Complex.exp (-z * (s : ℂ) ^ 2)) t := by fun_prop
    have h2 : ContinuousAt (fun s : ℝ => ((√2 / √(1 - s ^ 2 / 2) : ℝ) : ℂ)) t :=
      Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_const.div ((Real.continuous_sqrt.continuousAt.comp
          (by fun_prop : Continuous fun s : ℝ => 1 - s ^ 2 / 2).continuousAt))
          (Real.sqrt_ne_zero'.mpr hpos))
    exact h1.mul h2
  have hcomp := intervalIntegral.integral_deriv_smul_comp' hderiv hf'_cont hg_cont
  have hf0 : f 0 = 0 := by simp [f]
  have hfpi : f (π / 2) = 1 := by
    dsimp [f]
    rw [show π / 2 / 2 = π / 4 by ring, Real.sin_pi_div_four, ← mul_div_assoc,
      Real.mul_self_sqrt zero_le_two]
    norm_num
  rw [hf0, hfpi] at hcomp
  rw [← hcomp]
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [uIcc_of_le (by positivity)] at hθ
  have hcos_pos : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hf_sq : f θ ^ 2 = 1 - Real.cos θ := by
    dsimp [f]
    rw [mul_pow, Real.sq_sqrt zero_le_two]
    have hcos_sq := Real.cos_sq (θ / 2)
    have hsin_sq := Real.sin_sq_add_cos_sq (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at hcos_sq
    linarith
  have hsqrt_eq : √(1 - f θ ^ 2 / 2) = Real.cos (θ / 2) := by
    rw [hf_sq, show 1 - (1 - Real.cos θ) / 2 = (1 + Real.cos θ) / 2 by ring]
    have hcos_half : Real.cos (θ / 2) ^ 2 = (1 + Real.cos θ) / 2 := by
      have := Real.cos_sq (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring] at this
      linarith
    rw [← hcos_half, Real.sqrt_sq hcos_pos.le]
  dsimp only [Function.comp_apply, g, f']
  rw [Complex.real_smul, hsqrt_eq, ← Complex.ofReal_pow, hf_sq]
  have hcos_ne : (Real.cos (θ / 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcos_pos.ne'
  have h2_sq : ((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two]; norm_num
  rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_div]
  calc Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ))
      = Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) * ((((√2 : ℂ) * (√2 : ℂ)) / 2) *
          ((Real.cos (θ / 2) : ℂ) / (Real.cos (θ / 2) : ℂ))) := by
        rw [h2_sq, div_self hcos_ne]; norm_num
    _ = ((√2 : ℂ) / 2 * (Real.cos (θ / 2) : ℂ)) *
          (Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) * ((√2 : ℂ) / (Real.cos (θ / 2) : ℂ))) := by
        ring

/-- **Sharpened two-term sector asymptotic of `I₀`** (removing the additive `2` of
`besselI0C_two_term` in favor of `10 ‖w‖^{-1/2}`).  For `1 ≤ Re w` and `16 ≤ ‖w‖`:
`‖I₀(w) - besselTwoTerm w‖ ≤ 70 e^{Re w} ‖w‖^{-5/2} + 10 ‖w‖^{-1/2}`. -/
theorem besselI0C_two_term_sharp {w : ℂ} (hw : 1 ≤ w.re) (hwn : 16 ≤ ‖w‖) :
    ‖Integration.besselI0C w - besselTwoTerm w‖ ≤
      70 * Real.exp w.re * ‖w‖ ^ (-(5 : ℝ) / 2) + 10 * ‖w‖ ^ (-(1 : ℝ) / 2) := by
  have hw0 : 0 < w.re := by linarith
  have hchord : ∫ θ in (0 : ℝ)..(π / 2), Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ)) =
      √2 * laplaceA w := by
    rw [cos_half_change_eq, laplaceA, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    rw [psiC_real ht.1 ht.2]
    push_cast; ring
  have hsplit : ∫ θ in (0 : ℝ)..π, Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ)) =
      (∫ θ in (0 : ℝ)..(π / 2), Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ))) +
        ∫ θ in (π / 2)..π, Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ)) := by
    have hc : Continuous fun θ : ℝ => Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ)) := by fun_prop
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm
  set R := ∫ θ in (π / 2)..π, Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ))
  have hmain : besselTwoTerm w = (Complex.exp w / (π : ℂ)) * (√2 * laplaceMain w) := by
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    have hs : ((√(2 * π) : ℝ) : ℂ) = (√2 : ℝ) * (√π : ℝ) := by
      rw [Real.sqrt_mul zero_le_two]; push_cast; ring
    have hsq : (((√2 : ℝ) : ℂ)) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt zero_le_two]; norm_num
    have hsp : (((√π : ℝ) : ℂ)) ^ 2 = (π : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
    have h20 : ((√2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
    have hp0 : ((√π : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
    rw [besselTwoTerm, laplaceMain, hs]; push_cast; field_simp; rw [← hsp, ← hsq]; ring
  rw [besselI0C_eq_chord, hsplit, hchord, hmain]
  have hdiff : (Complex.exp w / (π : ℂ)) * (√2 * laplaceA w + R) -
      (Complex.exp w / (π : ℂ)) * (√2 * laplaceMain w) =
      (Complex.exp w / (π : ℂ)) * (√2 * (laplaceA w - laplaceMain w) + R) := by ring
  rw [hdiff, norm_mul]
  have hexpn : ‖Complex.exp w / (π : ℂ)‖ = Real.exp w.re / π := by
    rw [norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [hexpn]
  have h1 := laplaceA_rotate_decay hw
  have h2 := ray_integral hw
  have hA_diff : ‖laplaceA w - laplaceMain w‖ ≤
      4 * Real.exp (-w.re) / ‖w‖ + 150 * ‖w‖ ^ (-(5 : ℝ) / 2) := by
    calc ‖laplaceA w - laplaceMain w‖
        ≤ ‖laplaceA w - _‖ + ‖_ - laplaceMain w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 4 * Real.exp (-w.re) / ‖w‖ + 150 * ‖w‖ ^ (-(5 : ℝ) / 2) := add_le_add h1 h2
  have hR := chord_tail_decay hw0 hwn
  have hwn_pos : 0 < ‖w‖ := by linarith
  have hinv_le_half : ‖w‖⁻¹ ≤ (1 / 4 : ℝ) * ‖w‖ ^ (-(1 : ℝ) / 2) := by
    have hr : ‖w‖⁻¹ = ‖w‖ ^ (-(1 : ℝ) / 2) * ‖w‖ ^ (-(1 : ℝ) / 2) := by
      rw [← Real.rpow_add hwn_pos]; norm_num [Real.rpow_neg_one]
    have hle : ‖w‖ ^ (-(1 : ℝ) / 2) ≤ 1 / 4 := by
      have h16 : (1 / 4 : ℝ) = (16 : ℝ) ^ (-(1 : ℝ) / 2) := by
        rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by ring, Real.rpow_neg (by norm_num),
          ← Real.sqrt_eq_rpow, show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        norm_num
      rw [h16]; exact Real.rpow_le_rpow_of_nonpos (by norm_num) hwn (by norm_num)
    rw [hr]
    calc ‖w‖ ^ (-(1 : ℝ) / 2) * ‖w‖ ^ (-(1 : ℝ) / 2) ≤ ‖w‖ ^ (-(1 : ℝ) / 2) * (1 / 4) := by gcongr
      _ = 1 / 4 * ‖w‖ ^ (-(1 : ℝ) / 2) := by ring
  have hs2 : √2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hsqrt2_norm : ‖(√2 : ℂ)‖ = √2 := by
    rw [show (√2 : ℂ) = ((√2 : ℝ) : ℂ) by simp, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hexpm : Real.exp w.re * Real.exp (-w.re) = 1 := by rw [← Real.exp_add]; simp
  calc Real.exp w.re / π * ‖(√2 : ℂ) * (laplaceA w - laplaceMain w) + R‖
      ≤ Real.exp w.re / π * (√2 * (4 * Real.exp (-w.re) / ‖w‖ + 150 * ‖w‖ ^ (-(5 : ℝ) / 2)) +
          8 * Real.exp (-w.re) * ‖w‖ ^ (-(1 : ℝ) / 2)) := by
        gcongr
        refine (norm_add_le _ _).trans (add_le_add ?_ hR)
        rw [norm_mul, hsqrt2_norm]; gcongr
    _ = ((4 * √2 / π) * ‖w‖⁻¹ + (8 / π) * ‖w‖ ^ (-(1 : ℝ) / 2)) * (Real.exp w.re * Real.exp (-w.re)) +
          150 * √2 / π * (Real.exp w.re * ‖w‖ ^ (-(5 : ℝ) / 2)) := by
        field_simp [Real.pi_pos.ne', hwn_pos.ne']; ring
    _ ≤ 70 * Real.exp w.re * ‖w‖ ^ (-(5 : ℝ) / 2) + 10 * ‖w‖ ^ (-(1 : ℝ) / 2) := by
        rw [hexpm, mul_one]
        have hpi3 := Real.pi_gt_three
        have a2 : 150 * √2 / π ≤ 70 := by
          have hs3 : √2 < 1.415 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
          rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_d2]
        have a1 : 4 * √2 / π * ‖w‖⁻¹ + 8 / π * ‖w‖ ^ (-(1 : ℝ) / 2) ≤ 10 * ‖w‖ ^ (-(1 : ℝ) / 2) := by
          calc 4 * √2 / π * ‖w‖⁻¹ + 8 / π * ‖w‖ ^ (-(1 : ℝ) / 2)
              ≤ (4 * (3 / 2) / 3) * (1 / 4 * ‖w‖ ^ (-(1 : ℝ) / 2)) +
                  (8 / 3) * ‖w‖ ^ (-(1 : ℝ) / 2) := by gcongr
            _ ≤ 10 * ‖w‖ ^ (-(1 : ℝ) / 2) := by
                nlinarith [Real.rpow_pos_of_pos hwn_pos (-(1 : ℝ) / 2)]
        have a3 : 0 ≤ Real.exp w.re * ‖w‖ ^ (-(5 : ℝ) / 2) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right a2 a3]

/-! ## Section 2: Three-term Virasoro `V(t(x))` expansion -/

/-- `V₁(x) := ∑_{j=0}^2 (-1)^j binom(2,j) e^{-4πjx} (3j - 12π j² x + 3/(16π x))`. -/
def virasoroV1 (x : ℝ) : ℝ :=
  3 / (16 * π * x) * (1 - Real.exp (-4 * π * x)) ^ 2 -
    2 * Real.exp (-4 * π * x) * (3 - 12 * π * x) +
    Real.exp (-8 * π * x) * (6 - 48 * π * x)

/-- Coefficient `a₁(x) := 3i / (32π x (1 - e^{-4πx})²)`. -/
def virasoroA1 (x : ℝ) : ℂ :=
  3 * I / (32 * (π : ℂ) * (x : ℂ) * ((1 - Real.exp (-4 * π * x)) ^ 2 : ℝ))

/-- Coefficient `a₂(x) := -V₁(x) / (1 - e^{-4πx})⁴`. -/
def virasoroA2 (x : ℝ) : ℝ :=
  -virasoroV1 x / (1 - Real.exp (-4 * π * x)) ^ 4

private lemma besselI0_two_term_real {w : ℝ} (hw : 1 ≤ w) :
    |Bessel.besselI0 w / Bessel.besselAs w - (1 + 1 / (8 * w))| ≤ 220 / w ^ 2 := by
  have hw0 : 0 < w := by linarith
  have hAs : 0 < Bessel.besselAs w := Bessel.besselAs_pos hw0
  have htwo := besselI0C_two_term (w := (w : ℂ)) (by simpa using hw)
  rw [Integration.besselI0C_ofReal] at htwo
  have htwoTerm : besselTwoTerm (w : ℂ) = ((Bessel.besselAs w * (1 + 1 / (8 * w)) : ℝ) : ℂ) := by
    unfold besselTwoTerm Bessel.besselAs
    have hlog : Complex.log (w : ℂ) = (Real.log w : ℂ) := (Complex.ofReal_log hw0.le).symm
    have hsqrt_inv : Complex.exp (-(1 / 2 : ℂ) * (Real.log w : ℂ)) = (((√w)⁻¹ : ℝ) : ℂ) := by
      rw [show -(1 / 2 : ℂ) * (Real.log w : ℂ) = ((-(1 / 2) * Real.log w : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_exp]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hw0.le, Real.rpow_def_of_pos hw0]
      congr 1; ring
    have hsq_eq : ((√(2 * π * w) : ℝ) : ℂ) = ((√(2 * π) : ℝ) : ℂ) * ((√w : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.sqrt_mul (by positivity)]
    have hsqrt_w_ne : ((√w : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hw0).ne'
    have h2pi_ne : ((√(2 * π) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
    rw [hlog, hsqrt_inv]
    push_cast
    rw [← Complex.ofReal_exp, hsq_eq]
    field_simp [hsqrt_w_ne, h2pi_ne, Complex.ofReal_ne_zero.mpr hw0.ne']
  rw [htwoTerm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at htwo
  simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg hw0.le] at htwo
  have hrpow : w ^ (-(5 : ℝ) / 2) = (w ^ 2 * √w)⁻¹ := by
    rw [show (-(5 : ℝ) / 2) = -((2 : ℝ) + 1 / 2) by ring, Real.rpow_neg hw0.le,
      Real.rpow_add hw0, Real.rpow_two, ← Real.sqrt_eq_rpow]
  have h2_le : 2 ≤ 12 * Real.exp w * w ^ (-(5 : ℝ) / 2) := by
    have hexp_ge : w ^ 3 / 6 ≤ Real.exp w := by
      have h := Real.sum_le_exp_of_nonneg hw0.le 4
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, Nat.factorial_one,
        Nat.factorial_two, Nat.cast_ofNat, pow_succ] at h
      have : 0 ≤ 1 + w + w ^ 2 / 2 := by positivity
      linarith [show w ^ 3 / (3 * 2 * 1 : ℝ) = w ^ 3 / 6 by ring]
    have hsqrt : √w ≤ w := Real.sqrt_le_iff.mpr ⟨hw0.le, by nlinarith⟩
    rw [hrpow]
    have hne : w ^ 2 * √w ≠ 0 := by positivity
    have hprod : 2 ≤ 12 * (w ^ 3 / 6) * (w ^ 2 * √w)⁻¹ := by
      have hw_le_w2 : w ^ 2 ≤ w ^ 3 := by nlinarith
      calc 2 = 2 * (w ^ 2 * √w) * (w ^ 2 * √w)⁻¹ := by field_simp [hne]
        _ ≤ 2 * (w ^ 2 * w) * (w ^ 2 * √w)⁻¹ := by gcongr
        _ = 12 * (w ^ 3 / 6) * (w ^ 2 * √w)⁻¹ := by ring
    exact hprod.trans (by gcongr)
  have hI_diff : |Bessel.besselI0 w - Bessel.besselAs w * (1 + 1 / (8 * w))| ≤
      82 * Real.exp w * w ^ (-(5 : ℝ) / 2) := by linarith
  have hdiv : |Bessel.besselI0 w / Bessel.besselAs w - (1 + 1 / (8 * w))| =
      |Bessel.besselI0 w - Bessel.besselAs w * (1 + 1 / (8 * w))| / Bessel.besselAs w := by
    rw [show Bessel.besselI0 w / Bessel.besselAs w - (1 + 1 / (8 * w)) =
        (Bessel.besselI0 w - Bessel.besselAs w * (1 + 1 / (8 * w))) / Bessel.besselAs w by
      field_simp [hAs.ne'], abs_div, abs_of_pos hAs]
  rw [hdiv]
  have h82 : 82 * Real.exp w * w ^ (-(5 : ℝ) / 2) / Bessel.besselAs w = 82 * √(2 * π) / w ^ 2 := by
    unfold Bessel.besselAs
    rw [hrpow, show 2 * π * w = (2 * π) * w by ring, Real.sqrt_mul (by positivity)]
    have hsqrt_w_ne : √w ≠ 0 := (Real.sqrt_pos.mpr hw0).ne'
    have h2pi_ne : √(2 * π) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp [hsqrt_w_ne, h2pi_ne, Real.exp_ne_zero w]
  refine (div_le_div_of_nonneg_right hI_diff hAs.le).trans (h82.le.trans ?_)
  have h2pi : √(2 * π) ≤ 2.6 := by
    rw [Real.sqrt_le_iff]; constructor <;> [norm_num; nlinarith [Real.pi_lt_d2]]
  gcongr; linarith

private lemma sqrt_one_sub_cubic_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 10) :
    1 - u / 2 - u ^ 2 / 8 - u ^ 3 / 4 ≤ √(1 - u) ∧ √(1 - u) ≤ 1 - u / 2 - u ^ 2 / 8 := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg u, pow_nonneg hu0 3, pow_nonneg hu0 4]
  · rw [Real.sqrt_le_left (by nlinarith)]
    nlinarith [sq_nonneg u, pow_nonneg hu0 3]

private lemma inv_sqrt_sqrt_one_sub_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 10) :
    |(√(1 - u))⁻¹ ^ (1 / 2 : ℝ) - (1 + u / 4)| ≤ 2 * u ^ 2 := by
  have hs_ge : 1 / 2 ≤ √(1 - u) := by apply Real.le_sqrt_of_sq_le; nlinarith
  have hs_le : √(1 - u) ≤ 1 := by rw [Real.sqrt_le_one]; linarith
  have hs_pos : 0 < √(1 - u) := by linarith
  set r : ℝ := (√(1 - u))⁻¹ ^ (1 / 2 : ℝ)
  have hr_pos : 0 < r := Real.rpow_pos_of_pos (inv_pos.mpr hs_pos) _
  have hr4 : r ^ 4 * (1 - u) = 1 := by
    have h2 : r ^ 2 = (√(1 - u))⁻¹ := by
      dsimp [r]; rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr hs_pos.le)]; norm_num
    have h4 : r ^ 4 = (r ^ 2) ^ 2 := by ring
    rw [h4, h2, inv_pow, Real.sq_sqrt (by linarith)]
    field_simp [show 1 - u ≠ 0 by linarith]
  have hlo : (1 + u / 4 - u ^ 2) ^ 4 * (1 - u) ≤ 1 := by
    nlinarith [sq_nonneg u, pow_nonneg hu0 3, pow_nonneg hu0 4, pow_nonneg hu0 5,
      pow_nonneg hu0 6, pow_nonneg hu0 7, pow_nonneg hu0 8]
  have hhi : 1 ≤ (1 + u / 4 + 2 * u ^ 2) ^ 4 * (1 - u) := by
    nlinarith [sq_nonneg u, pow_nonneg hu0 3, pow_nonneg hu0 4, pow_nonneg hu0 5,
      pow_nonneg hu0 6, pow_nonneg hu0 7, pow_nonneg hu0 8]
  have h1u : 0 < 1 - u := by linarith
  have hlo' : 1 + u / 4 - u ^ 2 ≤ r := by
    refine (pow_le_pow_iff_left₀ (by nlinarith [sq_nonneg u]) hr_pos.le (by norm_num : 4 ≠ 0)).1 ?_
    nlinarith
  have hhi' : r ≤ 1 + u / 4 + 2 * u ^ 2 := by
    refine (pow_le_pow_iff_left₀ hr_pos.le (by positivity) (by norm_num : 4 ≠ 0)).1 ?_
    nlinarith
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg u]

private lemma exp_nonpos_sub_one_add_abs_le {t : ℝ} (ht : t ≤ 0) :
    |Real.exp t - (1 + t)| ≤ t ^ 2 / 2 := by
  have h1 : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have h2 : Real.exp t ≤ 1 + t + t ^ 2 / 2 := by
    let f : ℝ → ℝ := fun s => 1 + s + s ^ 2 / 2 - Real.exp s
    have hf0 : f 0 = 0 := by simp [f]
    have hderiv : ∀ s ∈ Icc t 0, HasDerivAt f (1 + s - Real.exp s) s := by
      intro s _
      exact (((hasDerivAt_id s).const_add 1).add
        (((hasDerivAt_pow 2 s).div_const 2).congr_deriv (by ring))).sub (Real.hasDerivAt_exp s)
    have hanti : AntitoneOn f (Icc t 0) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc t 0)
        (by fun_prop : Continuous f).continuousOn
        (fun s hs => (hderiv s (interior_subset hs)).hasDerivWithinAt) fun s hs => ?_
      have hs1 := Real.add_one_le_exp s
      linarith
    have hle : f 0 ≤ f t := hanti ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
    dsimp [f] at hle hf0; linarith
  rw [abs_le]; constructor <;> linarith [sq_nonneg t]

private lemma term_j_virasoro {c' x : ℝ} (j : ℕ) (hj : j ≤ 2) (hc : 1000 ≤ c')
    (hx : xiStar / 2 ≤ x) :
    |Bessel.besselI0 (c' * Bessel.besselL x * √(1 - 12 * (j : ℝ) / c')) /
        Bessel.besselAs (c' * Bessel.besselL x) -
      Real.exp (-4 * π * (j : ℝ) * x) *
        (1 + (3 * (j : ℝ) - 12 * π * (j : ℝ) ^ 2 * x + 3 / (16 * π * x)) / c')| ≤
      96000 / c' ^ 2 := by
  have hc0 : 0 < c' := by linarith
  have hx5 : (1 / 10 : ℝ) ≤ x := by linarith [Bessel.one_fifth_le_xiStar]
  have hxpos : 0 < x := by linarith
  set z₀ : ℝ := c' * Bessel.besselL x with hz₀def
  have hz₀_lb : c' / 5 ≤ z₀ := by
    have hLx : 1 / 5 ≤ Bessel.besselL x := by
      rw [Bessel.besselL]; nlinarith [Real.pi_gt_three, hx5]
    rw [hz₀def]; nlinarith
  have hz₀_ge : 200 ≤ z₀ := by linarith
  set u : ℝ := 12 * (j : ℝ) / c' with hudef
  have hj2 : (j : ℝ) ≤ 2 := by exact_mod_cast hj
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 / 10 := by rw [hudef, div_le_iff₀ hc0]; linarith
  obtain ⟨hsl, hsr⟩ := sqrt_one_sub_cubic_bounds hu0 hu1
  set s : ℝ := √(1 - u) with hsdef
  have hs_lo : 1 / 2 ≤ s := by nlinarith
  have hs_hi : s ≤ 1 := by nlinarith
  have hz_ge : 100 ≤ z₀ * s := by nlinarith
  have htwo := besselI0_two_term_real (w := z₀ * s) (by linarith)
  set ε₀ : ℝ := Bessel.besselI0 (z₀ * s) / Bessel.besselAs (z₀ * s) - (1 + 1 / (8 * (z₀ * s)))
  have hε₀ : |ε₀| ≤ 220 / (z₀ * s) ^ 2 := htwo
  have hAs_ratio : Bessel.besselAs (z₀ * s) / Bessel.besselAs z₀ =
      Real.exp (-4 * π * (j : ℝ) * x) *
        (Real.exp (z₀ * (s - 1 + u / 2)) * (s⁻¹ ^ (1 / 2 : ℝ))) := by
    unfold Bessel.besselAs
    have hzu : z₀ * u / 2 = 4 * π * (j : ℝ) * x := by
      rw [hz₀def, hudef, Bessel.besselL]; field_simp [hc0.ne']; ring
    have hexp : Real.exp (z₀ * s) / Real.exp z₀ =
        Real.exp (-4 * π * (j : ℝ) * x) * Real.exp (z₀ * (s - 1 + u / 2)) := by
      rw [← Real.exp_sub, ← Real.exp_add]; congr 1; linarith
    have hsqrt : √(2 * π * z₀) / √(2 * π * (z₀ * s)) = s⁻¹ ^ (1 / 2 : ℝ) := by
      rw [show 2 * π * (z₀ * s) = (2 * π * z₀) * s by ring,
        Real.sqrt_mul (by positivity), ← div_div,
        div_self (Real.sqrt_pos.mpr (by positivity)).ne', one_div, Real.sqrt_eq_rpow,
        Real.inv_rpow (by linarith)]
    have hden1 : √(2 * π * z₀) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have hden2 : √(2 * π * (z₀ * s)) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have h1 : Real.exp (z₀ * s) / √(2 * π * (z₀ * s)) / (Real.exp z₀ / √(2 * π * z₀)) =
        (Real.exp (z₀ * s) / Real.exp z₀) * (√(2 * π * z₀) / √(2 * π * (z₀ * s))) := by
      field_simp [hden1, hden2, Real.exp_ne_zero z₀]
    rw [h1, hexp, hsqrt, mul_assoc]
  set q : ℝ := Real.exp (-4 * π * (j : ℝ) * x)
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.mpr (by have : 0 ≤ 4 * π * (j : ℝ) * x := by positivity; linarith)
  have hB_eq : Bessel.besselI0 (z₀ * s) / Bessel.besselAs z₀ =
      q * (Real.exp (z₀ * (s - 1 + u / 2)) * (s⁻¹ ^ (1 / 2 : ℝ)) *
        (1 + 1 / (8 * (z₀ * s)) + ε₀)) := by
    have hAs_s : 0 < Bessel.besselAs (z₀ * s) := Bessel.besselAs_pos (by linarith)
    have hAs_0 : 0 < Bessel.besselAs z₀ := Bessel.besselAs_pos (by linarith)
    have h1 : Bessel.besselI0 (z₀ * s) / Bessel.besselAs z₀ =
        (Bessel.besselAs (z₀ * s) / Bessel.besselAs z₀) *
          (Bessel.besselI0 (z₀ * s) / Bessel.besselAs (z₀ * s)) := by
      field_simp [hAs_s.ne', hAs_0.ne']
    rw [h1, hAs_ratio]
    have h2 : Bessel.besselI0 (z₀ * s) / Bessel.besselAs (z₀ * s) =
        1 + 1 / (8 * (z₀ * s)) + ε₀ := by dsimp [ε₀]; ring
    rw [h2]; ring
  rw [hB_eq, ← mul_sub, abs_mul, abs_of_pos hq0]
  have hxq1 : (j : ℝ) * x * q ≤ 1 / (4 * π) := by
    rcases eq_or_lt_of_le (Nat.zero_le j) with rfl | hjpos
    · simp; positivity
    · have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjpos
      have hex : (4 * π * (j : ℝ) * x) * q ≤ 1 := by
        have h := Real.add_one_le_exp (4 * π * (j : ℝ) * x)
        have hm : Real.exp (4 * π * (j : ℝ) * x) * q = 1 := by
          dsimp [q]; rw [← Real.exp_add]; simp
        nlinarith [Real.exp_pos (4 * π * (j : ℝ) * x)]
      calc (j : ℝ) * x * q = (4 * π * (j : ℝ) * x * q) / (4 * π) := by
            field_simp [Real.pi_pos.ne']
        _ ≤ 1 / (4 * π) := by gcongr
  have hxq2 : (12 * π * (j : ℝ) ^ 2 * x) * q ≤ 6 := by
    calc (12 * π * (j : ℝ) ^ 2 * x) * q = 12 * π * (j : ℝ) * ((j : ℝ) * x * q) := by ring
      _ ≤ 12 * π * 2 * (1 / (4 * π)) := by gcongr
      _ = 6 := by field_simp [Real.pi_pos.ne']; norm_num
  have hxq2_sq : (12 * π * (j : ℝ) ^ 2 * x) ^ 2 * q ≤ 144 := by
    rcases eq_or_lt_of_le (Nat.zero_le j) with rfl | hjpos
    · simp
    · have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjpos
      have h1 : (2 * π * (j : ℝ) * x) * Real.exp (-2 * π * (j : ℝ) * x) ≤ 1 := by
        have h := Real.add_one_le_exp (2 * π * (j : ℝ) * x)
        have hm : Real.exp (2 * π * (j : ℝ) * x) * Real.exp (-2 * π * (j : ℝ) * x) = 1 := by
          rw [← Real.exp_add]; simp
        nlinarith [Real.exp_pos (2 * π * (j : ℝ) * x)]
      have hq_sq : q = (Real.exp (-2 * π * (j : ℝ) * x)) ^ 2 := by
        dsimp [q]; rw [← Real.exp_nat_mul]; congr 1; ring
      rw [hq_sq]
      calc (12 * π * (j : ℝ) ^ 2 * x) ^ 2 * (Real.exp (-2 * π * (j : ℝ) * x)) ^ 2
          = (6 * (j : ℝ)) ^ 2 * ((2 * π * (j : ℝ) * x) * Real.exp (-2 * π * (j : ℝ) * x)) ^ 2 := by
            ring
        _ ≤ (6 * 2) ^ 2 * 1 ^ 2 := by gcongr
        _ = 144 := by norm_num
  set E_arg : ℝ := z₀ * (s - 1 + u / 2)
  set A : ℝ := Real.exp E_arg
  set α₁ : ℝ := 12 * π * (j : ℝ) ^ 2 * x
  set A₀ : ℝ := 1 - α₁ / c'
  set B : ℝ := s⁻¹ ^ (1 / 2 : ℝ)
  set α₂ : ℝ := 3 * (j : ℝ)
  set B₀ : ℝ := 1 + α₂ / c'
  set C : ℝ := 1 + 1 / (8 * (z₀ * s)) + ε₀
  set α₃ : ℝ := 3 / (16 * π * x)
  set C₀ : ℝ := 1 + α₃ / c'
  have hα₁_nn : 0 ≤ α₁ := by positivity
  have hα₂_bd : 0 ≤ α₂ ∧ α₂ ≤ 6 := ⟨by positivity, by linarith⟩
  have hα₃_bd : 0 ≤ α₃ ∧ α₃ ≤ 1 := by
    refine ⟨by positivity, ?_⟩
    dsimp [α₃]; rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  have hE_nonpos : E_arg ≤ 0 := by
    have : s - 1 + u / 2 ≤ 0 := by linarith [hsr, sq_nonneg u]
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) this
  have hzu2 : z₀ * (u ^ 2 / 8) = α₁ / c' := by
    rw [hz₀def, hudef, Bessel.besselL]; dsimp [α₁]; field_simp [hc0.ne']; ring
  have hE_diff : |E_arg - (-α₁ / c')| ≤ 288 * π * (j : ℝ) ^ 3 * x / c' ^ 2 := by
    have hdiff_s : E_arg - (-α₁ / c') = -z₀ * (1 - u / 2 - u ^ 2 / 8 - s) := by
      rw [neg_div, ← hzu2]; dsimp [E_arg]; ring
    rw [hdiff_s, neg_mul, abs_neg, abs_mul, abs_of_pos (by linarith),
      abs_of_nonneg (by linarith [hsr])]
    have hrem : 1 - u / 2 - u ^ 2 / 8 - s ≤ u ^ 3 / 4 := by linarith [hsl]
    have hzu3 : z₀ * (u ^ 3 / 4) = 288 * π * (j : ℝ) ^ 3 * x / c' ^ 2 := by
      rw [hz₀def, hudef, Bessel.besselL]; field_simp [hc0.ne']; ring
    calc z₀ * (1 - u / 2 - u ^ 2 / 8 - s) ≤ z₀ * (u ^ 3 / 4) := by gcongr
      _ = 288 * π * (j : ℝ) ^ 3 * x / c' ^ 2 := hzu3
  have hA_err : q * |A - A₀| ≤ 600 / c' ^ 2 := by
    have h1 : |A - (1 + E_arg)| ≤ E_arg ^ 2 / 2 := exp_nonpos_sub_one_add_abs_le hE_nonpos
    have hE_abs : |E_arg| ≤ 2 * (α₁ / c') := by
      have h3 : 288 * π * (j : ℝ) ^ 3 * x / c' ^ 2 ≤ α₁ / c' := by
        rcases eq_or_lt_of_le (Nat.zero_le j) with rfl | hjpos
        · simp [α₁]
        · have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjpos
          dsimp [α₁]
          rw [div_le_div_iff₀ (by positivity) hc0]
          have hpx : 0 < π * x := mul_pos Real.pi_pos hxpos
          have hj_le : 288 * (j : ℝ) ≤ 12 * c' := by linarith only [hj2, hc]
          calc (288 * π * (j : ℝ) ^ 3 * x) * c' = (π * x * (j : ℝ) ^ 2 * c') * (288 * (j : ℝ)) := by ring
            _ ≤ (π * x * (j : ℝ) ^ 2 * c') * (12 * c') := by gcongr
            _ = (12 * π * (j : ℝ) ^ 2 * x) * c' ^ 2 := by ring
      have h4 := abs_le.mp hE_diff
      have hnd : -α₁ / c' = -(α₁ / c') := neg_div α₁ c'
      have hαc : 0 ≤ α₁ / c' := by positivity
      rw [abs_le]; constructor <;> linarith only [h3, h4.1, h4.2, hnd, hαc]
    have hE_sq : E_arg ^ 2 ≤ 4 * (α₁ / c') ^ 2 := by
      have : E_arg ^ 2 = |E_arg| ^ 2 := (sq_abs _).symm
      rw [this]
      calc |E_arg| ^ 2 ≤ (2 * (α₁ / c')) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hE_abs 2
        _ = 4 * (α₁ / c') ^ 2 := by ring
    have htri : |A - A₀| ≤ E_arg ^ 2 / 2 + 288 * π * (j : ℝ) ^ 3 * x / c' ^ 2 := by
      have hsub : A - A₀ = (A - (1 + E_arg)) + (E_arg - (-α₁ / c')) := by dsimp [A₀]; ring
      rw [hsub]
      exact (abs_add_le _ _).trans (add_le_add h1 hE_diff)
    have hj_sq4 : (j : ℝ) ^ 2 ≤ 4 := by
      calc (j : ℝ) ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (by positivity) hj2 2
        _ = 4 := by norm_num
    calc q * |A - A₀| ≤ q * (2 * (α₁ / c') ^ 2 + 288 * π * (j : ℝ) ^ 3 * x / c' ^ 2) := by
          gcongr; linarith only [htri, hE_sq]
      _ = 2 * (α₁ ^ 2 * q) / c' ^ 2 + 288 * π * (j : ℝ) ^ 2 * ((j : ℝ) * x * q) / c' ^ 2 := by ring
      _ ≤ 2 * 144 / c' ^ 2 + 288 * π * 4 * (1 / (4 * π)) / c' ^ 2 := by
          gcongr
      _ = 576 / c' ^ 2 := by field_simp [Real.pi_pos.ne']; ring
      _ ≤ 600 / c' ^ 2 := by gcongr; norm_num
  have hB_err : |B - B₀| ≤ 1200 / c' ^ 2 := by
    have h1 := inv_sqrt_sqrt_one_sub_bounds hu0 hu1
    have hB0_eq : 1 + u / 4 = B₀ := by dsimp [B₀, α₂, u]; ring
    rw [hB0_eq] at h1
    have hj_sq4' : (j : ℝ) ^ 2 ≤ 4 := by
      calc (j : ℝ) ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (by positivity) hj2 2
        _ = 4 := by norm_num
    have hu2 : 2 * u ^ 2 ≤ 1200 / c' ^ 2 := by
      rw [hudef]; calc 2 * (12 * (j : ℝ) / c') ^ 2 = 288 * (j : ℝ) ^ 2 / c' ^ 2 := by ring
        _ ≤ 288 * 4 / c' ^ 2 := by gcongr
        _ ≤ 1200 / c' ^ 2 := by gcongr; norm_num
    exact h1.trans hu2
  have hB₀_bd : |B₀| ≤ 2 := by
    dsimp [B₀]; rw [abs_le]; constructor <;> [nlinarith; linarith]
  have hB_bd : |B| ≤ 2 := by
    have hdiff := abs_le.mp hB_err
    have hb0 := abs_le.mp hB₀_bd
    have h1 : 1200 / c' ^ 2 ≤ 1 / 100 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    rw [abs_le]; constructor <;> linarith [show 0 ≤ B from Real.rpow_nonneg (inv_nonneg.mpr (by linarith)) _]
  have hC_err : |C - C₀| ≤ 22100 / c' ^ 2 := by
    have h1 : 1 / (8 * z₀) = α₃ / c' := by
      rw [hz₀def, Bessel.besselL]; dsimp [α₃]; field_simp [hc0.ne', hxpos.ne', Real.pi_pos.ne']; ring
    have hdiff : C - C₀ = (1 - s) / (8 * z₀ * s) + ε₀ := by
      dsimp [C, C₀]; rw [← h1]; field_simp [hz₀_ge, hs_lo]; ring
    have h1ms : 1 - s ≤ u := by linarith
    have hterm1 : |(1 - s) / (8 * z₀ * s)| ≤ 30 / c' ^ 2 := by
      rw [abs_of_nonneg (div_nonneg (by linarith) (by positivity))]
      calc (1 - s) / (8 * z₀ * s) ≤ u / (8 * (c' / 5) * (1 / 2)) := by gcongr
        _ = (12 * (j : ℝ)) / (4 / 5 * c' ^ 2) := by rw [hudef]; field_simp [hc0.ne']; ring
        _ ≤ 24 / (4 / 5 * c' ^ 2) := by gcongr; linarith
        _ = 30 / c' ^ 2 := by ring
    have hterm2 : |ε₀| ≤ 22000 / c' ^ 2 := by
      refine hε₀.trans ?_
      have hzs : (c' / 10) ^ 2 ≤ (z₀ * s) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        calc c' / 10 = (c' / 5) * (1 / 2) := by ring
          _ ≤ z₀ * s := by gcongr
      calc 220 / (z₀ * s) ^ 2 ≤ 220 / (c' / 10) ^ 2 := by gcongr
        _ = 22000 / c' ^ 2 := by ring
    rw [hdiff]
    exact (abs_add_le _ _).trans (by linarith)
  have hC₀_bd : |C₀| ≤ 2 := by
    dsimp [C₀]; rw [abs_le]; constructor <;> [nlinarith; linarith]
  have hC_bd : |C| ≤ 2 := by
    have hdiff := abs_le.mp hC_err
    have hc0b := abs_le.mp hC₀_bd
    have h1 : 22100 / c' ^ 2 ≤ 1 / 10 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    rw [abs_le]; constructor <;> linarith
  have hqA₀ : q * |A₀| ≤ 2 := by
    have : |A₀| ≤ 1 + α₁ / c' := by
      dsimp [A₀]; exact (abs_sub _ _).trans_eq (by simp [abs_of_nonneg hα₁_nn])
    calc q * |A₀| ≤ q * (1 + α₁ / c') := by gcongr
      _ = q + (α₁ * q) / c' := by ring
      _ ≤ 1 + 6 / c' := by gcongr
      _ ≤ 2 := by linarith [show 6 / c' ≤ 1 by rw [div_le_one hc0]; linarith]
  have hpoly : q * |A₀ * B₀ * C₀ - (1 + (3 * (j : ℝ) - α₁ + α₃) / c')| ≤ 100 / c' ^ 2 := by
    have hid : A₀ * B₀ * C₀ - (1 + (3 * (j : ℝ) - α₁ + α₃) / c') =
        (-α₁ * α₂ - α₁ * α₃ + α₂ * α₃) / c' ^ 2 - (α₁ * α₂ * α₃) / c' ^ 3 := by
      dsimp [A₀, B₀, C₀, α₂]; ring
    rw [hid]
    have htri : |(-α₁ * α₂ - α₁ * α₃ + α₂ * α₃) / c' ^ 2 - (α₁ * α₂ * α₃) / c' ^ 3| ≤
        (α₁ * α₂ + α₁ * α₃ + α₂ * α₃) / c' ^ 2 + (α₁ * α₂ * α₃) / c' ^ 3 := by
      refine (abs_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_div, abs_of_pos (by positivity : 0 < c' ^ 2)]
        gcongr
        calc |-α₁ * α₂ - α₁ * α₃ + α₂ * α₃|
            ≤ |-α₁ * α₂ - α₁ * α₃| + |α₂ * α₃| := abs_add_le _ _
          _ ≤ (|-(α₁ * α₂)| + |α₁ * α₃|) + |α₂ * α₃| := by
              gcongr; simpa [neg_mul] using abs_sub_le (-(α₁ * α₂)) (α₁ * α₃)
          _ = α₁ * α₂ + α₁ * α₃ + α₂ * α₃ := by
              simp [abs_neg, abs_of_nonneg (mul_nonneg hα₁_nn hα₂_bd.1),
                abs_of_nonneg (mul_nonneg hα₁_nn hα₃_bd.1),
                abs_of_nonneg (mul_nonneg hα₂_bd.1 hα₃_bd.1)]
      · rw [abs_div, abs_of_pos (by positivity : 0 < c' ^ 3),
          abs_of_nonneg (by positivity)]
    calc q * |(-α₁ * α₂ - α₁ * α₃ + α₂ * α₃) / c' ^ 2 - (α₁ * α₂ * α₃) / c' ^ 3|
        ≤ q * ((α₁ * α₂ + α₁ * α₃ + α₂ * α₃) / c' ^ 2 + (α₁ * α₂ * α₃) / c' ^ 3) := by
          gcongr
      _ = ((α₁ * q) * α₂ + (α₁ * q) * α₃ + q * (α₂ * α₃) +
            ((α₁ * q) * α₂ * α₃) / c') / c' ^ 2 := by ring
      _ ≤ (6 * 6 + 6 * 1 + 1 * (6 * 1) + (6 * 6 * 1) / c') / c' ^ 2 := by gcongr
      _ ≤ (48 + 1) / c' ^ 2 := by
          gcongr; rw [div_le_one hc0]; linarith
      _ ≤ 100 / c' ^ 2 := by gcongr; norm_num
  have htel : A * B * C - (1 + (3 * (j : ℝ) - α₁ + α₃) / c') =
      (A - A₀) * (B * C) + A₀ * (B - B₀) * C + A₀ * B₀ * (C - C₀) +
        (A₀ * B₀ * C₀ - (1 + (3 * (j : ℝ) - α₁ + α₃) / c')) := by ring
  have hlin : (3 * (j : ℝ) - α₁ + α₃) / c' =
      (3 * (j : ℝ) - 12 * π * (j : ℝ) ^ 2 * x + 3 / (16 * π * x)) / c' := by
    dsimp [α₁, α₃]; ring
  rw [← hlin, htel]
  calc q * |((A - A₀) * (B * C) + A₀ * (B - B₀) * C + A₀ * B₀ * (C - C₀)) +
        (A₀ * B₀ * C₀ - (1 + (3 * (j : ℝ) - α₁ + α₃) / c'))|
      ≤ q * ((|A - A₀| * (|B| * |C|) + |A₀| * |B - B₀| * |C| + |A₀| * |B₀| * |C - C₀|) +
          |A₀ * B₀ * C₀ - (1 + (3 * (j : ℝ) - α₁ + α₃) / c')|) := by
        gcongr
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul, abs_mul]
          · rw [abs_mul, abs_mul]
        · rw [abs_mul, abs_mul]
    _ = (q * |A - A₀|) * (|B| * |C|) + (q * |A₀|) * |B - B₀| * |C| +
          (q * |A₀|) * |B₀| * |C - C₀| +
          q * |A₀ * B₀ * C₀ - (1 + (3 * (j : ℝ) - α₁ + α₃) / c')| := by ring
    _ ≤ (600 / c' ^ 2) * (2 * 2) + 2 * (1200 / c' ^ 2) * 2 +
          2 * 2 * (22100 / c' ^ 2) + 100 / c' ^ 2 := by gcongr
    _ = 95700 / c' ^ 2 := by ring
    _ ≤ 96000 / c' ^ 2 := by gcongr; norm_num

/-- **Uniform three-term asymptotic of `V(c'x²/3)`** on `x ≥ ξ_*/2` for `c' ≥ 10000`. -/
theorem besselV_three_term {c' x : ℝ} (hc : 10000 ≤ c') (hx : xiStar / 2 ≤ x) :
    |Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) / Bessel.besselAs (c' * Bessel.besselL x) -
      ((1 - Real.exp (-4 * π * x)) ^ 2 + virasoroV1 x / c')| ≤ 400000 / c' ^ 2 := by
  have hc0 : 0 < c' := by linarith
  have hx0 : 0 ≤ x := by linarith [Bessel.one_fifth_le_xiStar]
  have hV_eq : Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) =
      Bessel.besselK (c' / 12 - 0) (c' * x ^ 2 / 3) -
      2 * Bessel.besselK (c' / 12 - 1) (c' * x ^ 2 / 3) +
      Bessel.besselK (c' / 12 - 2) (c' * x ^ 2 / 3) := by
    unfold Bessel.besselV
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.cast_zero, sub_zero, Nat.cast_one, Nat.cast_ofNat, pow_zero, one_mul, pow_one,
      neg_one_pow_succ, neg_one_sq, Nat.choose_self, Nat.choose_zero_right, Nat.choose_one_right]
  rw [hV_eq, Bessel.besselK_shift hc0 hx0, Bessel.besselK_shift hc0 hx0,
    Bessel.besselK_shift hc0 hx0]
  have h0 := term_j_virasoro (c' := c') (x := x) 0 (by decide) (by linarith) hx
  have h1 := term_j_virasoro (c' := c') (x := x) 1 (by decide) (by linarith) hx
  have h2 := term_j_virasoro (c' := c') (x := x) 2 (by decide) (by linarith) hx
  simp only [Nat.cast_zero, mul_zero, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Real.exp_zero, one_mul, Nat.cast_one, mul_one, one_pow,
    Nat.cast_ofNat] at h0 h1 h2
  have hexp8 : Real.exp (-4 * π * 2 * x) = Real.exp (-8 * π * x) := by congr 1; ring
  have hexp_sq : Real.exp (-8 * π * x) = (Real.exp (-4 * π * x)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hmain : (1 - Real.exp (-4 * π * x)) ^ 2 + virasoroV1 x / c' =
      (1 + (3 / (16 * π * x)) / c') -
      2 * (Real.exp (-4 * π * x) * (1 + (3 - 12 * π * x + 3 / (16 * π * x)) / c')) +
      Real.exp (-4 * π * 2 * x) * (1 + (3 * 2 - 12 * π * 2 ^ 2 * x + 3 / (16 * π * x)) / c') := by
    rw [hexp8, virasoroV1, hexp_sq]
    ring
  rw [hmain]
  set A₀ := Bessel.besselAs (c' * Bessel.besselL x)
  have hsplit : (Bessel.besselI0 (c' * Bessel.besselL x * √(1 - 12 * 0 / c')) -
        2 * Bessel.besselI0 (c' * Bessel.besselL x * √(1 - 12 * 1 / c')) +
        Bessel.besselI0 (c' * Bessel.besselL x * √(1 - 12 * 2 / c'))) / A₀ =
      Bessel.besselI0 (c' * Bessel.besselL x * √(1 - 0 / c')) / A₀ -
      2 * (Bessel.besselI0 (c' * Bessel.besselL x * √(1 - 12 * 1 / c')) / A₀) +
      Bessel.besselI0 (c' * Bessel.besselL x * √(1 - 12 * 2 / c')) / A₀ := by
    simp only [mul_zero]; ring
  rw [hsplit]
  calc |(Bessel.besselI0 (c' * Bessel.besselL x * √(1 - 0 / c')) / A₀ -
          2 * (Bessel.besselI0 (c' * Bessel.besselL x * √(1 - 12 * 1 / c')) / A₀) +
          Bessel.besselI0 (c' * Bessel.besselL x * √(1 - 12 * 2 / c')) / A₀) -
        ((1 + 3 / (16 * π * x) / c') -
          2 * (Real.exp (-4 * π * x) * (1 + (3 - 12 * π * x + 3 / (16 * π * x)) / c')) +
          Real.exp (-4 * π * 2 * x) * (1 + (3 * 2 - 12 * π * 2 ^ 2 * x + 3 / (16 * π * x)) / c'))|
      = |(Bessel.besselI0 (c' * Bessel.besselL x * √(1 - 0 / c')) / A₀ -
            (1 + (0 + 3 / (16 * π * x)) / c')) -
          2 * (Bessel.besselI0 (c' * Bessel.besselL x * √(1 - 12 * 1 / c')) / A₀ -
            Real.exp (-4 * π * x) * (1 + (3 - 12 * π * x + 3 / (16 * π * x)) / c')) +
          (Bessel.besselI0 (c' * Bessel.besselL x * √(1 - 12 * 2 / c')) / A₀ -
            Real.exp (-4 * π * 2 * x) * (1 + (3 * 2 - 12 * π * 2 ^ 2 * x + 3 / (16 * π * x)) / c'))| := by
        congr 1; ring
    _ ≤ |Bessel.besselI0 (c' * Bessel.besselL x * √(1 - 0 / c')) / A₀ -
            (1 + (0 + 3 / (16 * π * x)) / c')| +
          2 * |Bessel.besselI0 (c' * Bessel.besselL x * √(1 - 12 * 1 / c')) / A₀ -
            Real.exp (-4 * π * x) * (1 + (3 - 12 * π * x + 3 / (16 * π * x)) / c')| +
          |Bessel.besselI0 (c' * Bessel.besselL x * √(1 - 12 * 2 / c')) / A₀ -
            Real.exp (-4 * π * 2 * x) * (1 + (3 * 2 - 12 * π * 2 ^ 2 * x + 3 / (16 * π * x)) / c')| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
        rw [abs_mul]; norm_num
    _ ≤ 96000 / c' ^ 2 + 2 * (96000 / c' ^ 2) + 96000 / c' ^ 2 := by
        have h1' : |Bessel.besselI0 (c' * Bessel.besselL x * √(1 - 12 * 1 / c')) / A₀ -
            Real.exp (-4 * π * x) * (1 + (3 - 12 * π * x + 3 / (16 * π * x)) / c')| ≤ 96000 / c' ^ 2 := by
          simpa [div_eq_mul_inv] using h1
        have h0' : |Bessel.besselI0 (c' * Bessel.besselL x * √(1 - 0 / c')) / A₀ -
            (1 + (0 + 3 / (16 * π * x)) / c')| ≤ 96000 / c' ^ 2 := by
          simpa [div_eq_mul_inv] using h0
        have h2' : |Bessel.besselI0 (c' * Bessel.besselL x * √(1 - 12 * 2 / c')) / A₀ -
            Real.exp (-4 * π * 2 * x) * (1 + (3 * 2 - 12 * π * 2 ^ 2 * x + 3 / (16 * π * x)) / c')| ≤ 96000 / c' ^ 2 := by
          simpa [div_eq_mul_inv] using h2
        linarith only [h0', h1', h2']
    _ = 384000 / c' ^ 2 := by ring
    _ ≤ 400000 / c' ^ 2 := by gcongr; norm_num

/-! ## Section 3: Complex kernel algebra and pointwise asymptotic on `x ≥ ξ_*/2` -/

theorem besselI0C_neg (w : ℂ) : Integration.besselI0C (-w) = Integration.besselI0C w := by
  unfold Integration.besselI0C
  congr 1
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => Complex.exp (w * (Real.cos θ : ℝ))) π (a := 0) (b := π)
  rw [sub_zero, sub_self] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [Real.cos_pi_sub]; push_cast; ring_nf

private lemma besselTwoTerm_neg_sqrt_identity {r v : ℝ} (hr : 0 < r) (hv : 0 ≤ v) :
    Complex.exp (-(1 / 2 : ℂ) * Complex.log ((r : ℂ) * (-I * ((v : ℂ) + I / 2)))) =
      Complex.exp (I * ((π : ℂ) / 4)) / ((√r : ℝ) : ℂ) *
        (((v : ℂ) + I / 2) ^ (1 / 2 : ℂ))⁻¹ := by
  set u : ℂ := (v : ℂ) + I / 2 with hudef
  set w : ℂ := (r : ℂ) * (-I * u) with hwdef
  have hw_re : 0 < w.re := by
    have : w = (r / 2 : ℂ) - I * (r * v : ℂ) := by
      dsimp [w, u]; ring_nf; rw [Complex.I_sq]; ring
    rw [this]; simp [hr]
  have hw_ne : w ≠ 0 := by
    intro h; rw [h] at hw_re; simp at hw_re
  have hu_im : 0 < u.im := by simp [u]
  have hu_ne : u ≠ 0 := by
    intro h; rw [h] at hu_im; simp at hu_im
  have hr_ne : ((√r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr).ne'
  set lhs : ℂ := Complex.exp (-(1 / 2 : ℂ) * Complex.log w)
  set rhs : ℂ := Complex.exp (I * ((π : ℂ) / 4)) / ((√r : ℝ) : ℂ) * (u ^ (1 / 2 : ℂ))⁻¹
  have hlhs_sq : lhs ^ 2 = w⁻¹ := by
    dsimp [lhs]
    rw [← Complex.exp_nat_mul]
    have h1 : (2 : ℕ) * (-(1 / 2 : ℂ) * Complex.log w) = -Complex.log w := by push_cast; ring
    rw [h1, Complex.exp_neg, Complex.exp_log hw_ne]
  have hrhs_sq : rhs ^ 2 = w⁻¹ := by
    dsimp [rhs]
    have hu_cpow : (u ^ (1 / 2 : ℂ)) ^ 2 = u := by
      rw [Complex.cpow_def_of_ne_zero hu_ne, ← Complex.exp_nat_mul]
      have h1 : ((2 : ℕ) : ℂ) * (Complex.log u * (1 / 2 : ℂ)) = Complex.log u := by push_cast; ring
      rw [h1, Complex.exp_log hu_ne]
    have hexp_sq : Complex.exp (I * ((π : ℂ) / 4)) ^ 2 = I := by
      rw [← Complex.exp_nat_mul]
      have h1 : ((2 : ℕ) : ℂ) * (I * ((π : ℂ) / 4)) = ((π / 2 : ℝ) : ℂ) * I := by push_cast; ring
      rw [h1, Complex.exp_mul_I]
      simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    have hsqrt_sq : ((√r : ℝ) : ℂ) ^ 2 = (r : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hr.le]
    rw [mul_pow, div_pow, inv_pow, hexp_sq, hsqrt_sq, hu_cpow]
    calc I / (r : ℂ) * u⁻¹ = ((r : ℂ) * (-I * u))⁻¹ := by
          field_simp [Complex.ofReal_ne_zero.mpr hr.ne', hu_ne]
      _ = w⁻¹ := rfl
  have hsq_eq : (lhs - rhs) * (lhs + rhs) = 0 := by
    calc (lhs - rhs) * (lhs + rhs) = lhs ^ 2 - rhs ^ 2 := by ring
      _ = w⁻¹ - w⁻¹ := by rw [hlhs_sq, hrhs_sq]
      _ = 0 := sub_self _
  have hlhs_re : 0 < lhs.re := by
    dsimp [lhs]
    rw [Complex.exp_re]
    refine mul_pos (Real.exp_pos _) ?_
    have him : (-(1 / 2 : ℂ) * Complex.log w).im = -(1 / 2) * w.arg := by
      simp [Complex.mul_im, Complex.log_im, Complex.log_re]
    rw [him]
    apply Real.cos_pos_of_mem_Ioo
    have harg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw_re))
    constructor <;> linarith [Real.pi_pos]
  have hrhs_re : 0 < rhs.re := by
    have hu_re : 0 ≤ u.re := by simpa [u] using hv
    have hu_arg : u.arg ∈ Icc 0 (π / 2) := by
      have h1 : |u.arg| ≤ π / 2 :=
        Complex.abs_arg_le_pi_div_two_iff.mpr (by simpa [u] using hv)
      have h2 : 0 ≤ u.arg := Complex.arg_nonneg_iff.mpr (by simp [u])
      exact ⟨h2, (abs_le.mp h1).2⟩
    have hrhs_eq : rhs = (((√r)⁻¹ : ℝ) : ℂ) * Complex.exp (I * ((π : ℂ) / 4) - (1 / 2 : ℂ) * Complex.log u) := by
      dsimp [rhs]
      rw [Complex.cpow_def_of_ne_zero hu_ne, ← Complex.exp_neg, div_eq_mul_inv, Complex.ofReal_inv]
      calc Complex.exp (I * ((π : ℂ) / 4)) * ((√r : ℂ))⁻¹ * Complex.exp (-(Complex.log u * (1 / 2 : ℂ)))
          = ((√r : ℂ))⁻¹ * (Complex.exp (I * ((π : ℂ) / 4)) * Complex.exp (-((1 / 2 : ℂ) * Complex.log u))) := by
            ring_nf
        _ = ((√r : ℂ))⁻¹ * Complex.exp (I * ((π : ℂ) / 4) - (1 / 2 : ℂ) * Complex.log u) := by
            rw [← Complex.exp_add, sub_eq_add_neg]
    rw [hrhs_eq, Complex.re_ofReal_mul]
    refine mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hr)) ?_
    rw [Complex.exp_re]
    refine mul_pos (Real.exp_pos _) ?_
    have him : (I * ((π : ℂ) / 4) - (1 / 2 : ℂ) * Complex.log u).im = π / 4 - u.arg / 2 := by
      simp [Complex.sub_im, Complex.mul_im, Complex.log_im, Complex.log_re]; ring
    rw [him]
    apply Real.cos_pos_of_mem_Ioo
    have hpi0 := Real.pi_pos
    constructor <;> linarith [hu_arg.1, hu_arg.2]
  rcases mul_eq_zero.mp hsq_eq with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hre : lhs.re + rhs.re = 0 := by
      have := congrArg Complex.re h
      simpa using this
    linarith

/-- Explicit algebra of `(-2π) * besselTwoTerm w` at `w = (4π/3 c' x)(-i(v + i/2))`. -/
lemma besselTwoTerm_edge {c' x v : ℝ} (hc : 0 < c') (hx : 0 < x) (hv : 0 ≤ v) :
    (-2 * (π : ℂ)) *
        besselTwoTerm ((4 * (π : ℂ) / 3 * (c' : ℂ) * (x : ℂ)) * (-I * ((v : ℂ) + I / 2))) =
      -(√2 * (π : ℂ) * Complex.exp (I * ((π : ℂ) / 4))) / ((v : ℂ) + I / 2) ^ (1 / 2 : ℂ) *
        ((Bessel.besselAs (c' * Bessel.besselL x) : ℂ) *
          (1 + 1 / (8 * ((4 * (π : ℂ) / 3 * (c' : ℂ) * (x : ℂ)) * (-I * ((v : ℂ) + I / 2))))) *
          Complex.exp (-I * ((4 * π / 3 * c' * v * x : ℝ) : ℂ))) := by
  set r : ℝ := 4 * π / 3 * c' * x with hrdef
  have hrpos : 0 < r := by positivity
  set u : ℂ := (v : ℂ) + I / 2
  set w : ℂ := (r : ℂ) * (-I * u)
  have hw_eq : w = (4 * (π : ℂ) / 3 * (c' : ℂ) * (x : ℂ)) * (-I * ((v : ℂ) + I / 2)) := by
    dsimp [w, r, u]; push_cast; ring
  have hw_split : w = ((c' * Bessel.besselL x : ℝ) : ℂ) + (-I * ((4 * π / 3 * c' * v * x : ℝ) : ℂ)) := by
    dsimp [w, r, u]; rw [Bessel.besselL]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hexp_w : Complex.exp w =
      ((Real.exp (c' * Bessel.besselL x) : ℝ) : ℂ) *
        Complex.exp (-I * ((4 * π / 3 * c' * v * x : ℝ) : ℂ)) := by
    rw [hw_split, Complex.exp_add, Complex.ofReal_exp]
  have hsqrt_rel : ((√(2 * π) : ℝ) : ℂ) * ((√r : ℝ) : ℂ) =
      ((√2 : ℝ) : ℂ) * ((√(2 * π * (c' * Bessel.besselL x)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul zero_le_two]
    congr 1
    rw [hrdef, Bessel.besselL]; ring
  have hlog_id := besselTwoTerm_neg_sqrt_identity hrpos hv
  have hden_ne : ((√(2 * π * (c' * Bessel.besselL x)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by unfold Bessel.besselL; positivity)).ne'
  rw [← hw_eq]
  unfold besselTwoTerm Bessel.besselAs
  rw [hlog_id, hexp_w]
  have hrw : (1 / (((√(2 * π) : ℝ) : ℂ) * ((√r : ℝ) : ℂ))) =
      1 / (((√2 : ℝ) : ℂ) * ((√(2 * π * (c' * Bessel.besselL x)) : ℝ) : ℂ)) := by
    rw [hsqrt_rel]
  have h2_sq : ((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two]; norm_num
  have hsq2_ne : ((√2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr zero_lt_two).ne'
  calc (-2 * (π : ℂ)) *
        (((((Real.exp (c' * Bessel.besselL x) : ℝ) : ℂ) *
              Complex.exp (-I * ((4 * π / 3 * c' * v * x : ℝ) : ℂ))) /
            ((√(2 * π) : ℝ) : ℂ)) *
          (Complex.exp (I * ((π : ℂ) / 4)) / ((√r : ℝ) : ℂ) * (u ^ (1 / 2 : ℂ))⁻¹) *
          (1 + 1 / (8 * w)))
      = -(((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) * (π : ℂ) * Complex.exp (I * ((π : ℂ) / 4))) *
          (u ^ (1 / 2 : ℂ))⁻¹ *
          ((((Real.exp (c' * Bessel.besselL x) : ℝ) : ℂ)) *
            (1 / (((√(2 * π) : ℝ) : ℂ) * ((√r : ℝ) : ℂ))) *
            (1 + 1 / (8 * w)) * Complex.exp (-I * ((4 * π / 3 * c' * v * x : ℝ) : ℂ))) := by
        rw [h2_sq]; ring
    _ = -(((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) * (π : ℂ) * Complex.exp (I * ((π : ℂ) / 4))) *
          (u ^ (1 / 2 : ℂ))⁻¹ *
          ((((Real.exp (c' * Bessel.besselL x) : ℝ) : ℂ)) *
            (1 / (((√2 : ℝ) : ℂ) * ((√(2 * π * (c' * Bessel.besselL x)) : ℝ) : ℂ))) *
            (1 + 1 / (8 * w)) * Complex.exp (-I * ((4 * π / 3 * c' * v * x : ℝ) : ℂ))) := by
        rw [hrw]
    _ = -(↑√2 * ↑π * Complex.exp (I * ↑π / 4)) / u ^ (1 / 2 : ℂ) *
          (↑(Real.exp (c' * Bessel.besselL x) / √(2 * π * (c' * Bessel.besselL x))) *
            (1 + 1 / (8 * w)) * Complex.exp (-I * ↑(4 * π / 3 * c' * v * x))) := by
        have huc_ne : u ^ (1 / 2 : ℂ) ≠ 0 :=
          Complex.cpow_ne_zero_iff.mpr (Or.inl (by
            intro h; have := congrArg Complex.im h; simp [u] at this))
        push_cast
        field_simp [hsq2_ne, hden_ne, huc_ne]
        ring

/-- The main integrand kernel of `cts:edge-asymp`. -/
def edgeMainKernel (c' v x : ℝ) : ℂ :=
  -(√2 * (π : ℂ) * Complex.exp (I * (π : ℂ) / 4)) / ((v : ℂ) + I / 2) ^ (1 / 2 : ℂ) *
    ((Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) : ℂ) *
      ((((1 - Real.exp (-4 * π * x)) ^ 2 : ℝ) : ℂ)⁻¹ +
        virasoroA1 x / ((c' : ℂ) * ((v : ℂ) + I / 2)) +
        ((virasoroA2 x / c' : ℝ) : ℂ)) *
      Complex.exp (-I * ((4 * π / 3 * c' * v * x : ℝ) : ℂ)))

private lemma virasoroV1_abs_le {x : ℝ} (hx : xiStar / 2 ≤ x) :
    |virasoroV1 x| ≤ 30 := by
  have hx5 : (1 / 10 : ℝ) ≤ x := by linarith [Bessel.one_fifth_le_xiStar]
  have hxpos : 0 < x := by linarith
  have hpi : 3 < π := Real.pi_gt_three
  have he1 : 0 < Real.exp (-4 * π * x) := Real.exp_pos _
  have he1_le : Real.exp (-4 * π * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have he2 : 0 < Real.exp (-8 * π * x) := Real.exp_pos _
  have he2_le : Real.exp (-8 * π * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have ht1 : 3 / (16 * π * x) * (1 - Real.exp (-4 * π * x)) ^ 2 ≤ 1 := by
    have ha : 3 / (16 * π * x) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    have hb : (1 - Real.exp (-4 * π * x)) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hxexp1 : 12 * π * x * Real.exp (-4 * π * x) ≤ 3 := by
    have h := Real.add_one_le_exp (4 * π * x)
    have hm : Real.exp (4 * π * x) * Real.exp (-4 * π * x) = 1 := by rw [← Real.exp_add]; simp
    have h4 : 4 * π * x * Real.exp (-4 * π * x) ≤ 1 := by nlinarith [Real.exp_pos (4 * π * x)]
    linarith
  have hxexp2 : 48 * π * x * Real.exp (-8 * π * x) ≤ 6 := by
    have h := Real.add_one_le_exp (8 * π * x)
    have hm : Real.exp (8 * π * x) * Real.exp (-8 * π * x) = 1 := by rw [← Real.exp_add]; simp
    have h8 : 8 * π * x * Real.exp (-8 * π * x) ≤ 1 := by nlinarith [Real.exp_pos (8 * π * x)]
    linarith
  dsimp [virasoroV1]
  have h1 : |3 / (16 * π * x) * (1 - Real.exp (-4 * π * x)) ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]; exact ht1
  have h2 : |2 * Real.exp (-4 * π * x) * (3 - 12 * π * x)| ≤ 12 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have hsub : |3 - 12 * π * x| ≤ 3 + 12 * π * x :=
      (abs_sub 3 (12 * π * x)).trans_eq (by simp [abs_of_pos (by positivity : 0 < 12 * π * x)])
    calc 2 * Real.exp (-4 * π * x) * |3 - 12 * π * x|
        ≤ 2 * Real.exp (-4 * π * x) * (3 + 12 * π * x) := by gcongr
      _ = 6 * Real.exp (-4 * π * x) + 2 * (12 * π * x * Real.exp (-4 * π * x)) := by ring
      _ ≤ 6 * 1 + 2 * 3 := by gcongr
      _ = 12 := by norm_num
  have h3 : |Real.exp (-8 * π * x) * (6 - 48 * π * x)| ≤ 12 := by
    rw [abs_mul, abs_of_nonneg he2.le]
    have hsub : |6 - 48 * π * x| ≤ 6 + 48 * π * x :=
      (abs_sub 6 (48 * π * x)).trans_eq (by simp [abs_of_pos (by positivity : 0 < 48 * π * x)])
    calc Real.exp (-8 * π * x) * |6 - 48 * π * x|
        ≤ Real.exp (-8 * π * x) * (6 + 48 * π * x) := by gcongr
      _ = 6 * Real.exp (-8 * π * x) + 48 * π * x * Real.exp (-8 * π * x) := by ring
      _ ≤ 6 * 1 + 6 := by gcongr
      _ = 12 := by norm_num
  calc |3 / (16 * π * x) * (1 - Real.exp (-4 * π * x)) ^ 2 -
        2 * Real.exp (-4 * π * x) * (3 - 12 * π * x) +
        Real.exp (-8 * π * x) * (6 - 48 * π * x)|
      ≤ (|3 / (16 * π * x) * (1 - Real.exp (-4 * π * x)) ^ 2| +
          |2 * Real.exp (-4 * π * x) * (3 - 12 * π * x)|) +
          |Real.exp (-8 * π * x) * (6 - 48 * π * x)| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ 1 + 12 + 12 := by linarith
    _ ≤ 30 := by norm_num

private lemma one_sub_exp_ge_half {x : ℝ} (hx : xiStar / 2 ≤ x) :
    1 / 2 ≤ 1 - Real.exp (-4 * π * x) := by
  have hx5 : (1 / 10 : ℝ) ≤ x := by linarith [Bessel.one_fifth_le_xiStar]
  have hpi := Real.pi_gt_three
  have h4px : 1 ≤ 4 * π * x := by nlinarith
  have hexp : Real.exp (-4 * π * x) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have hexp1 : Real.exp 1 > 2 := by linarith [Real.exp_one_gt_d9]
  have hinv : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]; linarith
  linarith

private lemma norm_u_cpow_half {v : ℝ} (hv : 0 ≤ v) :
    1 / 3 * (1 + v) ≤ ‖(v : ℂ) + I / 2‖ ∧ ‖(v : ℂ) + I / 2‖ ≤ 1 + v ∧
      ‖((v : ℂ) + I / 2) ^ (1 / 2 : ℂ)‖ = √‖(v : ℂ) + I / 2‖ := by
  set u : ℂ := (v : ℂ) + I / 2
  have hunorm_sq : ‖u‖ ^ 2 = v ^ 2 + 1 / 4 := by
    rw [Complex.sq_norm]; simp [Complex.normSq_apply, u]; ring
  have hlo : 1 / 3 * (1 + v) ≤ ‖u‖ := by
    rw [← Real.sqrt_sq (norm_nonneg u)]
    apply Real.le_sqrt_of_sq_le
    rw [hunorm_sq]; nlinarith [sq_nonneg (2 * v - 1 / 2)]
  have hhi : ‖u‖ ≤ 1 + v := by
    rw [← Real.sqrt_sq (norm_nonneg u), hunorm_sq]
    exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  refine ⟨hlo, hhi, ?_⟩
  have hu_ne : u ≠ 0 := by intro h; rw [h] at hlo; simp at hlo; linarith
  rw [Complex.cpow_def_of_ne_zero hu_ne, Complex.norm_exp]
  have hre : (Complex.log u * (1 / 2 : ℂ)).re = 1 / 2 * Real.log ‖u‖ := by
    simp [Complex.mul_re, Complex.log_re]; ring
  rw [hre, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (lt_of_lt_of_le (by positivity) hlo)]
  congr 1; ring

private lemma exp_le_V_of_ge {c' x : ℝ} (hc : 10000 ≤ c') (hx : xiStar / 2 ≤ x) :
    Real.exp (c' * Bessel.besselL x) ≤
      24 * √(c' * x) * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) := by
  have hc0 : 0 < c' := by linarith
  have hxpos : 0 < x := by linarith [Bessel.one_fifth_le_xiStar]
  have hV_pos : 0 < Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) := by
    have ha : 2 ≤ c' / 12 := by linarith
    have ht0 : 0 ≤ c' * x ^ 2 / 3 := by positivity
    rw [← Integration.virasoro_cardyV_eq_besselV ha ht0]
    have := Integration.virasoro_cardyV_ge ha ht0
    have : 0 < 8 * π ^ 4 * (c' * x ^ 2 / 3) ^ 2 := by positivity
    linarith
  have hV_cmp := (Bessel.besselV_comparison (c' := c') (x := x) hc hx).2
  have hsq_p : 0 < √(c' * x ^ 2 / 3) := Real.sqrt_pos.mpr (by positivity)
  rw [div_le_iff₀ hV_pos] at hV_cmp
  have hratio_V : √(c' * x ^ 2 / 3) / √x = √(c' * x / 3) := by
    rw [show c' * x ^ 2 / 3 = (c' * x / 3) * x by ring, Real.sqrt_mul (by positivity),
      mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr hxpos).ne']
  calc Real.exp (c' * Bessel.besselL x)
      = (1 / √(c' * x ^ 2 / 3) * Real.exp (c' * Bessel.besselL x)) * √(c' * x ^ 2 / 3) := by
        field_simp [hsq_p.ne']
    _ ≤ (6 * π / √x * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3)) * √(c' * x ^ 2 / 3) := by gcongr
    _ = 6 * π * (√(c' * x ^ 2 / 3) / √x) * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) := by ring
    _ = 6 * π * √(c' * x / 3) * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) := by rw [hratio_V]
    _ ≤ 6 * 4 * √(c' * x) * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) := by
        have hpi4 : π < 4 := Real.pi_lt_four
        have hsq3 : √(c' * x / 3) ≤ √(c' * x) := Real.sqrt_le_sqrt (by linarith [mul_pos hc0 hxpos])
        gcongr
    _ = 24 * √(c' * x) * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) := by ring

private lemma edge_kernel_pointwise_error :
    ∃ c₀ C : ℝ, 10000 ≤ c₀ ∧ 0 < C ∧ ∀ {c' v x : ℝ}, c₀ ≤ c' → 0 ≤ v → xiStar / 2 ≤ x →
      ‖(-2 * (π : ℂ)) *
          Integration.besselI0C (4 * (π : ℂ) * I * ((v : ℂ) + I / 2) *
            (Real.sqrt (c' * (c' * x ^ 2 / 3) / 3) : ℝ)) -
        edgeMainKernel c' v x‖ ≤
          C * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) / (c' ^ 2 * √(1 + v)) := by
  refine ⟨10000000, 10 ^ 9, by norm_num, by positivity, fun {c'} {v} {x} hc' hv hx => ?_⟩
  have hc0 : 0 < c' := by linarith
  have hc10k : 10000 ≤ c' := by linarith
  have hx5 : (1 / 10 : ℝ) ≤ x := by linarith [Bessel.one_fifth_le_xiStar]
  have hxpos : 0 < x := by linarith
  have hpi := Real.pi_gt_three
  have hsqrt_arg : Real.sqrt (c' * (c' * x ^ 2 / 3) / 3) = c' * x / 3 := by
    rw [show c' * (c' * x ^ 2 / 3) / 3 = (c' * x / 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hsqrt_arg]
  set u : ℂ := (v : ℂ) + I / 2
  set w : ℂ := (4 * (π : ℂ) / 3 * (c' : ℂ) * (x : ℂ)) * (-I * u)
  have hneg_arg : 4 * (π : ℂ) * I * u * ((c' * x / 3 : ℝ) : ℂ) = -w := by
    dsimp [w]; push_cast; ring
  rw [hneg_arg, besselI0C_neg]
  have hw_re : w.re = c' * Bessel.besselL x := by
    have h1 : w = ((c' * Bessel.besselL x : ℝ) : ℂ) + (-I * ((4 * π / 3 * c' * v * x : ℝ) : ℂ)) := by
      dsimp [w, u]; rw [Bessel.besselL]; push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [h1]; simp
  have hw_re_ge : 1 ≤ w.re := by
    rw [hw_re, Bessel.besselL]
    nlinarith [show 4 / 10 ≤ 4 * π / 3 * x by nlinarith]
  obtain ⟨hu_lo, hu_hi, hu_half⟩ := norm_u_cpow_half hv
  have hwn : ‖w‖ = (4 * π / 3 * c' * x) * ‖u‖ := by
    have hI : ‖-I * u‖ = ‖u‖ := by rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    dsimp [w]
    rw [show 4 * (π : ℂ) / 3 * (c' : ℂ) * (x : ℂ) = ((4 * π / 3 * c' * x : ℝ) : ℂ) by push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), hI]
  have hwn_lb : c' * x * (1 + v) ≤ ‖w‖ := by
    rw [hwn]
    calc c' * x * (1 + v) ≤ (4 * π / 3 * c' * x) * (1 / 3 * (1 + v)) := by
          nlinarith [mul_pos hc0 hxpos, show (0 : ℝ) ≤ 1 + v by linarith]
      _ ≤ (4 * π / 3 * c' * x) * ‖u‖ := by gcongr
  have hwn_ge16 : 16 ≤ ‖w‖ := by
    have hv1 : 1 ≤ 1 + v := by linarith
    nlinarith [mul_pos hc0 hxpos]
  have hI0_bd := besselI0C_two_term_sharp hw_re_ge hwn_ge16
  have hV_pos : 0 < Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) := by
    have ha : 2 ≤ c' / 12 := by linarith
    have ht0 : 0 ≤ c' * x ^ 2 / 3 := by positivity
    rw [← Integration.virasoro_cardyV_eq_besselV ha ht0]
    have := Integration.virasoro_cardyV_ge ha ht0
    have : 0 < 8 * π ^ 4 * (c' * x ^ 2 / 3) ^ 2 := by positivity
    linarith
  have hexp_V := exp_le_V_of_ge hc10k hx
  have hv1 : 1 ≤ 1 + v := by linarith
  have hcx_ge : c' / 10 ≤ c' * x := by nlinarith
  have hcx_pos : 0 < c' * x := by positivity
  have hPart1 : ‖(-2 * (π : ℂ)) * Integration.besselI0C w - (-2 * (π : ℂ)) * besselTwoTerm w‖ ≤
      10 ^ 7 * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) / (c' ^ 2 * √(1 + v)) := by
    rw [← mul_sub, norm_mul]
    have h2pi : ‖(-2 * (π : ℂ))‖ = 2 * π := by
      rw [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le]
    rw [hw_re] at hI0_bd
    rw [h2pi]
    have hvs : (1 + v) ^ (-(1 : ℝ) / 2) = (√(1 + v))⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity)]; congr 1; ring
    have hterm1 : 70 * Real.exp (c' * Bessel.besselL x) * ‖w‖ ^ (-(5 : ℝ) / 2) ≤
        10 ^ 6 * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) / (c' ^ 2 * √(1 + v)) := by
      have hw_rpow : ‖w‖ ^ (-(5 : ℝ) / 2) ≤ (c' * x * (1 + v)) ^ (-(5 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hwn_lb (by norm_num)
      have hrp_split : (c' * x * (1 + v)) ^ (-(5 : ℝ) / 2) ≤
          (c' * x) ^ (-(5 : ℝ) / 2) * (1 + v) ^ (-(1 : ℝ) / 2) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
        have hvp : (1 + v) ^ (-(5 : ℝ) / 2) ≤ (1 + v) ^ (-(1 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
        gcongr
      have hcx_comb : √(c' * x) * (c' * x) ^ (-(5 : ℝ) / 2) = ((c' * x) ^ 2)⁻¹ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hcx_pos]
        norm_num [Real.rpow_neg (by positivity : 0 ≤ c' * x)]
      have hcx2 : ((c' * x) ^ 2)⁻¹ ≤ 100 / c' ^ 2 := by
        rw [inv_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg x]
      calc 70 * Real.exp (c' * Bessel.besselL x) * ‖w‖ ^ (-(5 : ℝ) / 2)
          ≤ 70 * (24 * √(c' * x) * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3)) *
              ((c' * x) ^ (-(5 : ℝ) / 2) * (1 + v) ^ (-(1 : ℝ) / 2)) := by
            gcongr; exact hw_rpow.trans hrp_split
        _ = 1680 * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) *
              (√(c' * x) * (c' * x) ^ (-(5 : ℝ) / 2)) * (1 + v) ^ (-(1 : ℝ) / 2) := by ring
        _ ≤ 1680 * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) * (100 / c' ^ 2) * (√(1 + v))⁻¹ := by
            rw [hcx_comb, hvs]; gcongr
        _ = 168000 * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) / (c' ^ 2 * √(1 + v)) := by ring
        _ ≤ 10 ^ 6 * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) / (c' ^ 2 * √(1 + v)) := by
            gcongr; norm_num
    have hterm2 : 10 * ‖w‖ ^ (-(1 : ℝ) / 2) ≤
        2 * 10 ^ 4 * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) / (c' ^ 2 * √(1 + v)) := by
      have hw_rpow : ‖w‖ ^ (-(1 : ℝ) / 2) ≤ (c' * x * (1 + v)) ^ (-(1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hwn_lb (by norm_num)
      have hrp_split : (c' * x * (1 + v)) ^ (-(1 : ℝ) / 2) =
          (c' * x) ^ (-(1 : ℝ) / 2) * (1 + v) ^ (-(1 : ℝ) / 2) :=
        Real.mul_rpow (by positivity) (by positivity)
      have hcx_cancel : √(c' * x) * (c' * x) ^ (-(1 : ℝ) / 2) = 1 := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hcx_pos]
        simp
      have hexp_neg : Real.exp (-(c' * Bessel.besselL x)) ≤ 50 / c' ^ 2 := by
        have hL_lb : c' / 5 ≤ c' * Bessel.besselL x := by
          rw [Bessel.besselL]; nlinarith
        have h1 : (c' / 5) ^ 2 / 2 ≤ Real.exp (c' * Bessel.besselL x) := by
          have hsum := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ c' * Bessel.besselL x) 3
          simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
            pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one,
            Nat.factorial_two, Nat.cast_ofNat] at hsum
          have : 0 ≤ 1 + c' * Bessel.besselL x := by positivity
          have : (c' / 5) ^ 2 / 2 ≤ (c' * Bessel.besselL x) ^ 2 / 2 := by nlinarith
          linarith
        rw [Real.exp_neg, inv_le_div_iff₀ (Real.exp_pos _) (by positivity)]
        nlinarith [sq_nonneg c']
      have hone_eq : 1 = Real.exp (c' * Bessel.besselL x) * Real.exp (-(c' * Bessel.besselL x)) := by
        rw [← Real.exp_add]; simp
      calc 10 * ‖w‖ ^ (-(1 : ℝ) / 2)
          ≤ 10 * (1 * ((c' * x) ^ (-(1 : ℝ) / 2) * (1 + v) ^ (-(1 : ℝ) / 2))) := by
            rw [one_mul]; gcongr; exact hw_rpow.trans hrp_split.le
        _ = 10 * (Real.exp (c' * Bessel.besselL x) * Real.exp (-(c' * Bessel.besselL x))) *
              ((c' * x) ^ (-(1 : ℝ) / 2) * (1 + v) ^ (-(1 : ℝ) / 2)) := by rw [← hone_eq]
        _ ≤ 10 * ((24 * √(c' * x) * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3)) * (50 / c' ^ 2)) *
              ((c' * x) ^ (-(1 : ℝ) / 2) * (1 + v) ^ (-(1 : ℝ) / 2)) := by gcongr
        _ = 12000 * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) * (√(c' * x) * (c' * x) ^ (-(1 : ℝ) / 2)) *
              (1 + v) ^ (-(1 : ℝ) / 2) / c' ^ 2 := by ring
        _ = 12000 * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) / (c' ^ 2 * √(1 + v)) := by
            rw [hcx_cancel, hvs]; ring
        _ ≤ 2 * 10 ^ 4 * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) / (c' ^ 2 * √(1 + v)) := by
            gcongr; norm_num
    have hpi4 : π < 4 := Real.pi_lt_four
    calc 2 * π * ‖Integration.besselI0C w - besselTwoTerm w‖
        ≤ 8 * (70 * Real.exp (c' * Bessel.besselL x) * ‖w‖ ^ (-(5 : ℝ) / 2) +
            10 * ‖w‖ ^ (-(1 : ℝ) / 2)) := by
          gcongr
          · linarith
          · exact hI0_bd
      _ ≤ 8 * (10 ^ 6 * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) / (c' ^ 2 * √(1 + v)) +
            2 * 10 ^ 4 * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) / (c' ^ 2 * √(1 + v))) := by
          gcongr
      _ ≤ 10 ^ 7 * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) / (c' ^ 2 * √(1 + v)) := by
          have : 0 ≤ Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) / (c' ^ 2 * √(1 + v)) := by positivity
          linarith
  -- Step B: Compare `(-2π) * besselTwoTerm w` with `edgeMainKernel c' v x`
  have hPart2 : ‖(-2 * (π : ℂ)) * besselTwoTerm w - edgeMainKernel c' v x‖ ≤
      5 * 10 ^ 8 * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) / (c' ^ 2 * √(1 + v)) := by
    have hbt := besselTwoTerm_edge hc0 hxpos hv
    change (-2 * (π : ℂ)) * besselTwoTerm w = _ at hbt
    rw [hbt]
    set pref : ℂ := -(√2 * (π : ℂ) * Complex.exp (I * ((π : ℂ) / 4))) / (u ^ (1 / 2 : ℂ))
    have hpref_norm : ‖pref‖ ≤ 10 / √(1 + v) := by
      dsimp [pref]
      have hnum : ‖-(√2 * (π : ℂ) * Complex.exp (I * ((π : ℂ) / 4)))‖ = √2 * π := by
        rw [norm_neg, norm_mul, norm_mul]
        have hI : ‖Complex.exp (I * ((π : ℂ) / 4))‖ = 1 := by
          rw [show I * ((π : ℂ) / 4) = ((π / 4 : ℝ) : ℂ) * I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I]
        have hsq2 : ‖(√2 : ℂ)‖ = √2 := by
          rw [show (√2 : ℂ) = ((√2 : ℝ) : ℂ) by simp, Complex.norm_real,
            Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        rw [hsq2, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, hI, mul_one]
      have hden_lb : √(1 / 3 * (1 + v)) ≤ ‖u ^ (1 / 2 : ℂ)‖ := by
        rw [hu_half]; exact Real.sqrt_le_sqrt hu_lo
      have hden_eq : √(1 / 3 * (1 + v)) = √(1 + v) / √3 := by
        rw [show 1 / 3 * (1 + v) = (1 + v) / 3 by ring, Real.sqrt_div (by positivity)]
      rw [norm_div, hnum]
      calc √2 * π / ‖u ^ (1 / 2 : ℂ)‖ ≤ √2 * π / (√(1 + v) / √3) := by
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) (hden_eq ▸ hden_lb)
        _ = √6 * π / √(1 + v) := by
            rw [div_div_eq_mul_div, show √2 * π * √3 = (√2 * √3) * π by ring,
              ← Real.sqrt_mul zero_le_two, show (2 : ℝ) * 3 = 6 by norm_num]
        _ ≤ 10 / √(1 + v) := by
            have hsq6 : √6 ≤ 2.5 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
            gcongr; nlinarith [Real.pi_lt_four]
    have hexp_norm : ‖Complex.exp (-I * ((4 * π / 3 * c' * v * x : ℝ) : ℂ))‖ = 1 := by
      rw [show -I * ((4 * π / 3 * c' * v * x : ℝ) : ℂ) =
        ((- (4 * π / 3 * c' * v * x) : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    set A₀ : ℝ := Bessel.besselAs (c' * Bessel.besselL x)
    set V : ℝ := Bessel.besselV (c' / 12) (c' * x ^ 2 / 3)
    set d : ℝ := (1 - Real.exp (-4 * π * x)) ^ 2
    have hd_lb : 1 / 4 ≤ d := by
      have h1 := one_sub_exp_ge_half hx
      dsimp [d]; nlinarith
    have hd_le : d ≤ 1 := by
      have he0 : 0 ≤ Real.exp (-4 * π * x) := (Real.exp_pos _).le
      have he1 : Real.exp (-4 * π * x) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by have : 0 ≤ 4 * π * x := by positivity; linarith)
      dsimp [d]; nlinarith
    have hV3 := besselV_three_term hc10k hx
    change |V / A₀ - (d + virasoroV1 x / c')| ≤ 400000 / c' ^ 2 at hV3
    have hA₀_pos : 0 < A₀ := Bessel.besselAs_pos (by unfold Bessel.besselL; positivity)
    have hV_div_A₀ : 1 / 8 ≤ V / A₀ := by
      have h3 := (abs_le.mp hV3).1
      have hv1 := (abs_le.mp (virasoroV1_abs_le hx)).1
      have h1 : 30 / c' ≤ 1 / 32 := by rw [div_le_iff₀ hc0]; linarith
      have h2 : 400000 / c' ^ 2 ≤ 1 / 32 := by rw [div_le_iff₀ (by positivity)]; nlinarith
      have hv1' : -30 / c' ≤ virasoroV1 x / c' := div_le_div_of_nonneg_right hv1 hc0.le
      linarith only [h3, hv1', h1, h2, hd_lb]
    have ha₂_eq : virasoroA2 x = -virasoroV1 x / d ^ 2 := by dsimp [virasoroA2, d]; ring
    have ha₂_bd : |virasoroA2 x| ≤ 480 := by
      rw [ha₂_eq, abs_div, abs_neg, abs_of_pos (by positivity : 0 < d ^ 2)]
      calc |virasoroV1 x| / d ^ 2 ≤ 30 / (1 / 4) ^ 2 := by gcongr; exact virasoroV1_abs_le hx; nlinarith
        _ = 480 := by norm_num
    have hVA_main : |A₀ / V - (d⁻¹ + virasoroA2 x / c')| ≤ 20000000 / c' ^ 2 := by
      have hid : 1 - (V / A₀) * (d⁻¹ + virasoroA2 x / c') =
          (virasoroV1 x) ^ 2 / (d ^ 2 * c' ^ 2) -
            (V / A₀ - (d + virasoroV1 x / c')) * (d⁻¹ + virasoroA2 x / c') := by
        rw [ha₂_eq]; field_simp [show d ≠ 0 by linarith, hc0.ne']; ring
      have hnum_bd : |1 - (V / A₀) * (d⁻¹ + virasoroA2 x / c')| ≤ 2500000 / c' ^ 2 := by
        rw [hid]
        have hsq : (virasoroV1 x) ^ 2 / (d ^ 2 * c' ^ 2) ≤ 14400 / c' ^ 2 := by
          have hv1 := sq_le_sq' (abs_le.mp (virasoroV1_abs_le hx)).1 (abs_le.mp (virasoroV1_abs_le hx)).2
          calc (virasoroV1 x) ^ 2 / (d ^ 2 * c' ^ 2) ≤ 30 ^ 2 / ((1 / 4) ^ 2 * c' ^ 2) := by
                gcongr; nlinarith
            _ = 14400 / c' ^ 2 := by ring
        have hda : |d⁻¹ + virasoroA2 x / c'| ≤ 5 := by
          have hdinv : |d⁻¹| ≤ 4 := by
            rw [abs_of_pos (inv_pos.mpr (by linarith))]; rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
          have ha2c : |virasoroA2 x / c'| ≤ 1 := by
            rw [abs_div, abs_of_pos hc0]; rw [div_le_one hc0]; linarith [(abs_le.mp ha₂_bd).2]
          exact (abs_add_le _ _).trans (by linarith)
        calc |(virasoroV1 x) ^ 2 / (d ^ 2 * c' ^ 2) -
              (V / A₀ - (d + virasoroV1 x / c')) * (d⁻¹ + virasoroA2 x / c')|
            ≤ |(virasoroV1 x) ^ 2 / (d ^ 2 * c' ^ 2)| +
                |V / A₀ - (d + virasoroV1 x / c')| * |d⁻¹ + virasoroA2 x / c'| := by
              simpa [abs_mul] using abs_sub_le _ _
          _ ≤ 14400 / c' ^ 2 + (400000 / c' ^ 2) * 5 := by
              gcongr
              rw [abs_of_nonneg (by positivity)]; exact hsq
          _ ≤ 2500000 / c' ^ 2 := by
              have : (0 : ℝ) ≤ 1 / c' ^ 2 := by positivity
              nlinarith
      have hdiv_eq : A₀ / V - (d⁻¹ + virasoroA2 x / c') =
          (1 - (V / A₀) * (d⁻¹ + virasoroA2 x / c')) / (V / A₀) := by
        field_simp [hA₀_pos.ne', hV_pos.ne']
      rw [hdiv_eq, abs_div, abs_of_pos (by linarith)]
      calc |1 - (V / A₀) * (d⁻¹ + virasoroA2 x / c')| / (V / A₀)
          ≤ (2500000 / c' ^ 2) / (1 / 8) := by gcongr
        _ = 20000000 / c' ^ 2 := by ring
    have hw_inv : 1 / (8 * w) = (3 * I / (32 * (π : ℂ) * (x : ℂ))) / ((c' : ℂ) * u) := by
      dsimp [w]
      have hne : (4 * (π : ℂ) / 3 * (c' : ℂ) * (x : ℂ)) ≠ 0 := by
        have h1 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
        have h2 : (c' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc0.ne'
        have h3 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxpos.ne'
        positivity
      have hu_ne : u ≠ 0 := by intro h; rw [h] at hu_lo; simp at hu_lo; linarith
      field_simp [hne, hu_ne, Complex.I_ne_zero]
      ring
    have ha₁_rel : virasoroA1 x / ((c' : ℂ) * u) = ((d : ℝ) : ℂ)⁻¹ * (1 / (8 * w)) := by
      rw [hw_inv, virasoroA1]
      dsimp [d]
      have hd_ne : ((1 - Real.exp (-4 * π * x)) ^ 2 : ℂ) ≠ 0 := by
        exact_mod_cast (show (1 - Real.exp (-4 * π * x)) ^ 2 ≠ 0 by linarith)
      push_cast; ring
    have hdiff_kern : edgeMainKernel c' v x =
        pref * ((V : ℂ) * (((d : ℝ) : ℂ)⁻¹ + ((d : ℝ) : ℂ)⁻¹ * (1 / (8 * w)) +
          ((virasoroA2 x / c' : ℝ) : ℂ)) *
          Complex.exp (-I * ((4 * π / 3 * c' * v * x : ℝ) : ℂ))) := by
      dsimp [edgeMainKernel, pref, V, d]
      rw [← ha₁_rel]; push_cast; ring
    rw [hdiff_kern]
    have hsub_fact : pref * ((A₀ : ℂ) * (1 + 1 / (8 * w)) *
          Complex.exp (-I * ((4 * π / 3 * c' * v * x : ℝ) : ℂ))) -
        pref * ((V : ℂ) * (((d : ℝ) : ℂ)⁻¹ + ((d : ℝ) : ℂ)⁻¹ * (1 / (8 * w)) +
          ((virasoroA2 x / c' : ℝ) : ℂ)) *
          Complex.exp (-I * ((4 * π / 3 * c' * v * x : ℝ) : ℂ))) =
        pref * Complex.exp (-I * ((4 * π / 3 * c' * v * x : ℝ) : ℂ)) *
          (((A₀ - V * (d⁻¹ + virasoroA2 x / c') : ℝ) : ℂ) +
            (1 / (8 * w)) * ((A₀ - V * d⁻¹ : ℝ) : ℂ)) := by
      push_cast; ring
    rw [hsub_fact, norm_mul, norm_mul, hexp_norm, mul_one]
    have hw_inv_bd : ‖1 / (8 * w)‖ ≤ 1 / c' := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat]
      calc 1 / (8 * ‖w‖) ≤ 1 / (8 * (2 * c' * x * (1 + v))) := by gcongr
        _ ≤ 1 / (8 * (2 * c' * (1 / 10) * 1)) := by gcongr
        _ ≤ 1 / c' := by gcongr; nlinarith
    have hAV_bd1 : |A₀ - V * (d⁻¹ + virasoroA2 x / c')| ≤ 20000000 * V / c' ^ 2 := by
      have : A₀ - V * (d⁻¹ + virasoroA2 x / c') = V * (A₀ / V - (d⁻¹ + virasoroA2 x / c')) := by
        field_simp [hV_pos.ne']
      rw [this, abs_mul, abs_of_pos hV_pos]
      calc V * |A₀ / V - (d⁻¹ + virasoroA2 x / c')| ≤ V * (20000000 / c' ^ 2) := by gcongr
        _ = 20000000 * V / c' ^ 2 := by ring
    have hAV_bd2 : |A₀ - V * d⁻¹| ≤ 500 * V / c' := by
      have hid2 : A₀ - V * d⁻¹ = (A₀ - V * (d⁻¹ + virasoroA2 x / c')) + V * (virasoroA2 x / c') := by
        ring
      rw [hid2]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos hV_pos, abs_div, abs_of_pos hc0]
      calc |A₀ - V * (d⁻¹ + virasoroA2 x / c')| + V * (|virasoroA2 x| / c')
          ≤ 20000000 * V / c' ^ 2 + V * (480 / c') := by gcongr
        _ = (20000000 / c' + 480) * V / c' := by ring
        _ ≤ (2 + 480) * V / c' := by gcongr; rw [div_le_iff₀ hc0]; linarith
        _ ≤ 500 * V / c' := by gcongr; norm_num
    have hinner : ‖((A₀ - V * (d⁻¹ + virasoroA2 x / c') : ℝ) : ℂ) +
        (1 / (8 * w)) * ((A₀ - V * d⁻¹ : ℝ) : ℂ)‖ ≤ 20001000 * V / c' ^ 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |A₀ - V * (d⁻¹ + virasoroA2 x / c')| + ‖1 / (8 * w)‖ * |A₀ - V * d⁻¹|
          ≤ 20000000 * V / c' ^ 2 + (1 / c') * (500 * V / c') := by gcongr
        _ ≤ 20001000 * V / c' ^ 2 := by
            have : (0 : ℝ) ≤ V / c' ^ 2 := by positivity
            linarith [show (1 / c') * (500 * V / c') = 500 * (V / c' ^ 2) by ring]
    calc ‖pref‖ * ‖_‖ ≤ (10 / √(1 + v)) * (20001000 * V / c' ^ 2) := by gcongr
      _ ≤ 5 * 10 ^ 8 * V / (c' ^ 2 * √(1 + v)) := by
          have : (0 : ℝ) ≤ V / (c' ^ 2 * √(1 + v)) := by positivity
          calc (10 / √(1 + v)) * (20001000 * V / c' ^ 2)
              = 200010000 * (V / (c' ^ 2 * √(1 + v))) := by ring
            _ ≤ 5 * 10 ^ 8 * (V / (c' ^ 2 * √(1 + v))) := by gcongr; norm_num
            _ = _ := by ring
  calc ‖(-2 * (π : ℂ)) * Integration.besselI0C w - edgeMainKernel c' v x‖
      ≤ ‖(-2 * (π : ℂ)) * Integration.besselI0C w - (-2 * (π : ℂ)) * besselTwoTerm w‖ +
        ‖(-2 * (π : ℂ)) * besselTwoTerm w - edgeMainKernel c' v x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 10 ^ 7 * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) / (c' ^ 2 * √(1 + v)) +
          5 * 10 ^ 8 * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) / (c' ^ 2 * √(1 + v)) :=
        add_le_add hPart1 hPart2
    _ ≤ 10 ^ 9 * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) / (c' ^ 2 * √(1 + v)) := by
        have : (0 : ℝ) ≤ Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) / (c' ^ 2 * √(1 + v)) := by positivity
        linarith

/-! ## Section 4: Head decay and full integral asymptotic (`cts:edge-hankel` (2)) -/

private lemma head_pointwise_exp_bound :
    ∃ c₀ C κ : ℝ, 1 ≤ c₀ ∧ 0 < C ∧ 0 < κ ∧ ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {g : ℝ → ℝ},
      TestClass virasoroProblem (c' / 12) g → 0 < virasoroProblem.cardyNorm (c' / 12) g →
        ∀ {x : ℝ}, x ∈ Icc 0 (xiStar / 2) →
          |g (c' * x ^ 2 / 3)| * Real.exp (c' * (2 * π / 3) * x) ≤
            C * Real.exp (-κ * c') * virasoroProblem.cardyNorm (c' / 12) g := by
  have hξ := xiStar_pos
  obtain ⟨U⟩ := WeightAxioms.fixedWeightAxioms_of_problem virasoroProblem
  obtain ⟨c_Kw, C_Klo, hcKw8, hCKlo, hPJ_thm⟩ := stripPoissonJensen_general virasoroProblem
  set δ : ℝ := xiStar / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  let C_PJ : ℝ := pjConstOf U.C_e U.c_band C_Klo (slitL xiStar)
  let c_PJ : ℝ := max (max 1 U.c₀) c_Kw
  have hcPJ1 : 1 ≤ c_PJ := (le_max_left 1 U.c₀).trans (le_max_left _ _)
  obtain ⟨C_M1, C_M2, hCM1, hpropM⟩ := proposition_M_exp_general realSliceData
    (C_PJ := C_PJ) (p_e := U.p_e) hcPJ1 U.hp_e_nn
  let κ₀ : ℝ := 2.228 * δ ^ ((3 : ℝ) / 2)
  have hκ₀ : 0 < κ₀ := by positivity
  obtain ⟨C₄, hC₄, hC₄le⟩ := Integration.exists_rpow_le_mul_exp (p := C_M1 + 1) (κ := κ₀ / 2) (by positivity)
  have hC₄_pos : 0 < C₄ := by
    have h1 := hC₄le 1 le_rfl
    simp only [Real.one_rpow] at h1
    have hexp_pos : 0 < Real.exp (κ₀ / 2 * 1) := Real.exp_pos _
    nlinarith
  refine ⟨c_PJ, (1 / δ) * Real.exp C_M2 * C₄, κ₀ / 2, hcPJ1,
    by positivity, half_pos hκ₀, fun {c'} hc' {g} hg hMpos {x} hx => ?_⟩
  have hc₀' : max 1 U.c₀ ≤ c' := (le_max_left _ _).trans hc'
  have hcKw' : c_Kw ≤ c' := (le_max_right _ _).trans hc'
  have hc1 : 1 ≤ c' := hcPJ1.trans hc'
  have hc0 : 0 < c' := by linarith
  obtain ⟨P, hPCe, hPpe, hPcb, -, -⟩ : ∃ P : PropositionPAxioms virasoroProblem c',
      P.C_e = U.C_e ∧ P.p_e = U.p_e ∧ P.c_band = U.c_band ∧ P.C_up = U.C_up ∧ P.p_u = U.p_u := by
    have hc₀ : U.c₀ ≤ c' := (le_max_right _ _).trans hc₀'
    exact ⟨(U.axioms_at hc₀).toPropositionPAxioms, U.uniform_C_e hc₀, U.uniform_p_e hc₀,
      U.uniform_c_band hc₀, U.uniform_C_up hc₀, U.uniform_p_u hc₀⟩
  set M : ℝ := virasoroProblem.cardyNorm (c' / 12) g
  have hPJ_at : ∀ y ∈ Ico 0 xiStar, g (c' * y ^ 2 / 3) ≠ 0 →
      Real.log |g (c' * y ^ 2 / 3)| ≤ c' * majorantReal y + Real.log M -
        (1 / 2 : ℝ) * Real.log c' +
        (U.p_e + 1 / 2) * (1 - realSliceData.slitMassAt y) * Real.log c' +
        realSliceData.slitEntropyAt y + C_PJ := by
    intro y hy hy_ne
    have h := hPJ_thm P hcKw' hg hMpos y hy hy_ne
    rwa [hPCe, hPpe, hPcb] at h
  have hexp_bd := hpropM hc' hMpos hPJ_at
  have hx_mem : x ∈ Ico 0 xiStar := ⟨hx.1, hx.2.trans_lt (by linarith)⟩
  have hMexp := hexp_bd x hx_mem
  have hUdef : majorantReal x + (2 * π / 3) * x ≤ -slitDeficit (xiStar - x) :=
    majorantReal_g_deficit hx_mem
  have hx_pos_δ : δ ≤ xiStar - x := by dsimp [δ]; linarith [hx.2]
  have hslit_def := slitDeficit_ge (le_trans hδ0.le hx_pos_δ) (by linarith [hx.1] : xiStar - x ≤ xiStar)
  have hδ_rpow : δ ^ ((3 : ℝ) / 2) ≤ (xiStar - x) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow hδ0.le hx_pos_δ (by norm_num)
  have hU_le : majorantReal x + (2 * π / 3) * x ≤ -κ₀ := by
    calc majorantReal x + (2 * π / 3) * x
        ≤ -slitDeficit (xiStar - x) := hUdef
      _ ≤ -(2.228 * (xiStar - x) ^ ((3 : ℝ) / 2)) := neg_le_neg hslit_def
      _ ≤ -(2.228 * δ ^ ((3 : ℝ) / 2)) := neg_le_neg (mul_le_mul_of_nonneg_left hδ_rpow (by norm_num))
      _ = -κ₀ := rfl
  have hsqrt_le : Real.sqrt (xiStar - x) ≤ 1 := by
    calc Real.sqrt (xiStar - x) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith [hx.1, xiStar_lt_one])
      _ = 1 := Real.sqrt_one
  have hinv_le : (xiStar - x)⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ0 hx_pos_δ
  have hdx_pos : 0 < xiStar - x := lt_of_lt_of_le hδ0 hx_pos_δ
  have hexp_comb :
      Real.exp (c' * majorantReal x + C_M1 * Real.sqrt (xiStar - x) * Real.log c') *
        Real.exp (c' * (2 * π / 3) * x) ≤
        Real.exp (-κ₀ * c' + C_M1 * Real.log c') := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : c' * (majorantReal x + (2 * π / 3) * x) ≤ c' * (-κ₀) :=
      mul_le_mul_of_nonneg_left hU_le hc0.le
    have hlogc'_nn : 0 ≤ Real.log c' := Real.log_nonneg hc1
    have h2 : C_M1 * Real.sqrt (xiStar - x) * Real.log c' ≤ C_M1 * Real.log c' := by
      calc C_M1 * Real.sqrt (xiStar - x) * Real.log c' ≤ C_M1 * 1 * Real.log c' := by gcongr
        _ = C_M1 * Real.log c' := by ring
    linarith
  have hcm_eq : Real.exp (C_M1 * Real.log c') = c' ^ C_M1 := by
    rw [Real.rpow_def_of_pos hc0]; ring_nf
  have hpow_comb : c' ^ (-(1 / 2 : ℝ)) * Real.exp (-κ₀ * c' + C_M1 * Real.log c') ≤
      C₄ * Real.exp (-(κ₀ / 2) * c') := by
    have hcm1_nn : c' ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
    have hpow_tot : c' ^ (-(1 / 2 : ℝ)) * c' ^ C_M1 ≤ c' ^ (C_M1 + 1) := by
      have hc1le : c' ^ C_M1 ≤ c' ^ (C_M1 + 1) :=
        Real.rpow_le_rpow_of_exponent_le hc1 (by linarith)
      calc c' ^ (-(1 / 2 : ℝ)) * c' ^ C_M1 ≤ 1 * c' ^ C_M1 := by gcongr
        _ ≤ c' ^ (C_M1 + 1) := by linarith
    have hc4 := hC₄le c' hc1
    calc c' ^ (-(1 / 2 : ℝ)) * Real.exp (-κ₀ * c' + C_M1 * Real.log c')
        = (c' ^ (-(1 / 2 : ℝ)) * c' ^ C_M1) * Real.exp (-κ₀ * c') := by
          rw [Real.exp_add, hcm_eq]; ring
      _ ≤ (C₄ * Real.exp ((κ₀ / 2) * c')) * Real.exp (-κ₀ * c') :=
          mul_le_mul (hpow_tot.trans hc4) le_rfl (Real.exp_pos _).le (by positivity)
      _ = C₄ * Real.exp (-(κ₀ / 2) * c') := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  calc |g (c' * x ^ 2 / 3)| * Real.exp (c' * (2 * π / 3) * x)
      ≤ (Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * (xiStar - x)⁻¹ *
          Real.exp (c' * majorantReal x + C_M1 * Real.sqrt (xiStar - x) * Real.log c')) *
          Real.exp (c' * (2 * π / 3) * x) := by
        gcongr
    _ = Real.exp C_M2 * M * (xiStar - x)⁻¹ *
          (c' ^ (-(1 / 2 : ℝ)) *
            (Real.exp (c' * majorantReal x + C_M1 * Real.sqrt (xiStar - x) * Real.log c') *
              Real.exp (c' * (2 * π / 3) * x))) := by ring
    _ ≤ Real.exp C_M2 * M * δ⁻¹ * (C₄ * Real.exp (-(κ₀ / 2) * c')) := by
        have hexp_all := hpow_comb.trans' (mul_le_mul_of_nonneg_left hexp_comb (by positivity))
        have hM_nn : 0 ≤ M := virasoroProblem.cardyNorm_nonneg (by linarith : virasoroProblem.totalShift ≤ c' / 12) _
        exact mul_le_mul (mul_le_mul_of_nonneg_left hinv_le (by positivity)) hexp_all
          (by positivity) (by positivity)
    _ = ((1 / δ) * Real.exp C_M2 * C₄) * Real.exp (-(κ₀ / 2) * c') * M := by
        rw [one_div]; ring

private lemma edge_hankel_head_decay :
    ∃ c₀ C : ℝ, 10000 ≤ c₀ ∧ 0 < C ∧ ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {g : ℝ → ℝ},
      TestClass virasoroProblem (c' / 12) g → 0 < virasoroProblem.cardyNorm (c' / 12) g →
        ∀ {v : ℝ}, 0 ≤ v →
          ‖∫ t in Ioc 0 (c' * (xiStar / 2) ^ 2 / 3), (g t : ℂ) * (-2 * (π : ℂ)) *
              Integration.besselI0C (4 * (π : ℂ) * I * ((v : ℂ) + I / 2) *
                (Real.sqrt (c' * t / 3) : ℝ))‖ ≤
            C * virasoroProblem.cardyNorm (c' / 12) g / (c' ^ 2 * √(1 + v)) := by
  obtain ⟨c₁, C₁, κ, hc₁, hC₁, hκ, hhead⟩ := head_pointwise_exp_bound
  obtain ⟨C₂, hC₂, hC₂le⟩ := Integration.exists_rpow_le_mul_exp (p := (3 : ℝ)) (κ := κ / 2) (by positivity)
  have hC₂_pos : 0 < C₂ := by
    have := hC₂le 1 le_rfl; simp at this; nlinarith [Real.exp_pos (κ / 2)]
  refine ⟨max 10000 c₁, 200 * π * C₁ * C₂, le_max_left _ _, by positivity,
    fun {c'} hc' {g} hg hMpos {v} hv => ?_⟩
  have hc10k : 10000 ≤ c' := (le_max_left _ _).trans hc'
  have hc₁' : c₁ ≤ c' := (le_max_right _ _).trans hc'
  have hc0 : 0 < c' := by linarith
  have hc1 : 1 ≤ c' := by linarith
  set t₀ : ℝ := c' * (xiStar / 2) ^ 2 / 3 with ht₀
  have ht₀_pos : 0 < t₀ := by positivity [xiStar_pos]
  let φ : ℝ → ℝ := fun x => c' * x ^ 2 / 3
  let φ' : ℝ → ℝ := fun x => (2 * c' * x / 3 : ℝ)
  let F : ℝ → ℂ := fun t => (g t : ℂ) * (-2 * (π : ℂ)) *
    Integration.besselI0C (4 * (π : ℂ) * I * ((v : ℂ) + I / 2) * (Real.sqrt (c' * t / 3) : ℝ))
  have hb_strip : |((v : ℂ) + I / 2).im| ≤ 1 / 2 := by simp [abs_of_nonneg]
  have hint_F_Ioi : IntegrableOn F (Ioi 0) := by
    have hK_int := (Integration.lemmaB_d_integral (by linarith) hg).1
    have hmeas : AEStronglyMeasurable F (volume.restrict (Ioi 0)) := by
      have hg_m : AEStronglyMeasurable (fun t : ℝ => (g t : ℂ)) (volume.restrict (Ioi 0)) :=
        Complex.continuous_ofReal.comp_continuousOn hg.cont |>.mono Ioi_subset_Ici_self |>.aestronglyMeasurable measurableSet_Ioi
      have hI0_cont : Continuous Integration.besselI0C := by
        unfold Integration.besselI0C
        refine continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (by fun_prop) 0 π)
      have harg_cont : Continuous fun t : ℝ =>
          4 * (π : ℂ) * I * ((v : ℂ) + I / 2) * (Real.sqrt (c' * t / 3) : ℝ) := by fun_prop
      exact (hg_m.mul_const _).mul (hI0_cont.comp harg_cont).aestronglyMeasurable
    refine Integrable.mono' (hK_int.const_mul (2 * π)) hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp [F]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      show ‖(-2 * (π : ℂ))‖ = 2 * π by
        rw [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
          Real.norm_of_nonneg Real.pi_pos.le]]
    have hI_le := Integration.besselI0C_strip_le hc0 (mem_Ioi.mp ht).le hb_strip
    calc |g t| * (2 * π) * ‖Integration.besselI0C _‖
        ≤ |g t| * (2 * π) * kernelK 1 (c' / 12) t := by gcongr
      _ = 2 * π * (|g t| * kernelK 1 (c' / 12) t) := by ring
  have hI_Ioc : IntegrableOn F (Ioc 0 t₀) := hint_F_Ioi.mono_set Ioc_subset_Ioi_self
  rw [← intervalIntegral.integral_of_le ht₀_pos.le]
  -- Change variables `t = c' x^2 / 3` on `[0, xiStar/2]`
  have hsub : ∫ t in (0 : ℝ)..t₀, F t =
      ∫ x in (0 : ℝ)..(xiStar / 2), (φ' x : ℂ) • F (φ x) := by
    have hd : ∀ x ∈ uIcc (0 : ℝ) (xiStar / 2), HasDerivAt φ (φ' x) x := fun x _ => by
      dsimp [φ, φ']; exact ((hasDerivAt_pow 2 x).const_mul c' |>.div_const 3).congr_deriv (by ring)
    have hφ'_cont : ContinuousOn φ' (uIcc (0 : ℝ) (xiStar / 2)) := by dsimp [φ']; fun_prop
    have hF_cont : ContinuousOn F (φ '' uIcc 0 (xiStar / 2)) := by
      have himg : φ '' uIcc 0 (xiStar / 2) ⊆ Ici 0 := by
        rintro t ⟨x, _, rfl⟩; dsimp [φ]; positivity
      have hI0_cont : Continuous Integration.besselI0C := by
        unfold Integration.besselI0C
        refine continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (by fun_prop) 0 π)
      refine (((Complex.continuous_ofReal.comp_continuousOn hg.cont).mono himg).mul
        continuousOn_const).mul ((hI0_cont.comp (by fun_prop)).continuousOn)
    have hcomp := intervalIntegral.integral_deriv_smul_comp' hd hφ'_cont hF_cont
    have hsmul : ∫ x in (0 : ℝ)..(xiStar / 2), (φ' x : ℂ) • F (φ x) =
        ∫ x in (0 : ℝ)..(xiStar / 2), φ' x • F (φ x) :=
      intervalIntegral.integral_congr fun x _ => by simp [Complex.real_smul, smul_eq_mul]
    rw [hsmul]
    simpa [φ, ht₀] using hcomp.symm
  rw [hsub]
  -- Split at `x_cut := min (xiStar / 2) (12 / (c' * (1 + v)))`
  set M : ℝ := virasoroProblem.cardyNorm (c' / 12) g
  set x_cut : ℝ := min (xiStar / 2) (12 / (c' * (1 + v))) with hxcut
  have hxc_0 : 0 ≤ x_cut := le_min (by positivity [xiStar_pos]) (by positivity)
  have hxc_hi : x_cut ≤ xiStar / 2 := min_le_left _ _
  have hcont_sub : Continuous fun x : ℝ => (φ' x : ℂ) • F (φ x) := by
    have hI0_cont : Continuous Integration.besselI0C := by
      unfold Integration.besselI0C
      refine continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (by fun_prop) 0 π)
    have hcont_g : Continuous fun x : ℝ => g (φ x) :=
      hg.cont.comp_continuous (by dsimp [φ]; fun_prop) (fun x => by dsimp [φ]; positivity)
    dsimp [F, φ']
    exact (by fun_prop : Continuous fun x : ℝ => (2 * c' * x / 3 : ℝ)).smul
      (((Complex.continuous_ofReal.comp hcont_g).mul continuous_const).mul
        (hI0_cont.comp (by fun_prop)))
  have hsplit_x : ∫ x in (0 : ℝ)..(xiStar / 2), (φ' x : ℂ) • F (φ x) =
      (∫ x in (0 : ℝ)..x_cut, (φ' x : ℂ) • F (φ x)) +
      (∫ x in x_cut..(xiStar / 2), (φ' x : ℂ) • F (φ x)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont_sub.intervalIntegrable _ _) (hcont_sub.intervalIntegrable _ _)).symm
  rw [hsplit_x]
  have h2pi_norm : ‖(-2 * (π : ℂ))‖ = 2 * π := by
    rw [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hhead_exp_nn : 0 ≤ C₁ * Real.exp (-κ * c') * M := by positivity
  -- Piece A: `0..x_cut`
  have hA : ‖∫ x in (0 : ℝ)..x_cut, (φ' x : ℂ) • F (φ x)‖ ≤
      96 * π * C₁ * Real.exp (-κ * c') * M / (c' * √(1 + v)) := by
    have hpt_A : ∀ x ∈ Icc 0 x_cut,
        ‖(φ' x : ℂ) • F (φ x)‖ ≤ 2 * π * (C₁ * Real.exp (-κ * c') * M) * φ' x := by
      intro x hx
      have hx_mem : x ∈ Icc 0 (xiStar / 2) := ⟨hx.1, hx.2.trans hxc_hi⟩
      have hφ_nn : 0 ≤ φ x := by dsimp [φ]; positivity
      have hφ'_nn : 0 ≤ φ' x := by dsimp [φ']; positivity [hx.1]
      rw [Complex.coe_smul, norm_smul, Real.norm_of_nonneg hφ'_nn]
      dsimp [F]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, h2pi_norm]
      have hstrip := Integration.besselI0C_strip_le hc0 hφ_nn hb_strip
      have hK := kernelK_le_exp_slit hc0 hx.1
      have hPJ := hhead hc₁' hg hMpos hx_mem
      calc φ' x * (|g (φ x)| * (2 * π) * ‖Integration.besselI0C _‖)
          ≤ φ' x * (|g (φ x)| * (2 * π) * kernelK 1 (c' / 12) (φ x)) := by gcongr
        _ ≤ φ' x * (|g (φ x)| * (2 * π) * Real.exp (c' * (2 * π / 3) * x)) := by
            gcongr; exact hK
        _ = 2 * π * (|g (φ x)| * Real.exp (c' * (2 * π / 3) * x)) * φ' x := by ring
        _ ≤ 2 * π * (C₁ * Real.exp (-κ * c') * M) * φ' x := by gcongr
    have hmono := intervalIntegral.norm_integral_le_of_norm_le
      ((by fun_prop : Continuous fun x => 2 * π * (C₁ * Real.exp (-κ * c') * M) * φ' x).intervalIntegrable _ _)
      (by
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
        rw [uIoc_of_le hxc_0] at hx
        exact hpt_A x ⟨hx.1.le, hx.2⟩)
    have hint_φ' : ∫ x in (0 : ℝ)..x_cut, φ' x = c' * x_cut ^ 2 / 3 := by
      have hd : ∀ x ∈ uIcc (0 : ℝ) x_cut, HasDerivAt φ (φ' x) x := fun x _ => by
        dsimp [φ, φ']; exact ((hasDerivAt_pow 2 x).const_mul c' |>.div_const 3).congr_deriv (by ring)
      have hres := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        (by dsimp [φ']; fun_prop : Continuous φ').intervalIntegrable
      simpa [φ] using hres
    rw [intervalIntegral.integral_const_mul, hint_φ'] at hmono
    have hx_le2 : x_cut ≤ 12 / (c' * (1 + v)) := min_le_right _ _
    have hx_sq : c' * x_cut ^ 2 / 3 ≤ 48 / (c' * √(1 + v)) := by
      have hv1 : 1 ≤ 1 + v := by linarith
      have hsq_rt : √(1 + v) ≤ (1 + v) ^ 2 := by
        calc √(1 + v) ≤ 1 + v := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
          _ ≤ (1 + v) ^ 2 := by nlinarith
      calc c' * x_cut ^ 2 / 3 ≤ c' * (12 / (c' * (1 + v))) ^ 2 / 3 := by gcongr
        _ = 48 / (c' * (1 + v) ^ 2) := by field_simp [hc0.ne']; ring
        _ ≤ 48 / (c' * √(1 + v)) := by gcongr
    calc ‖∫ x in (0 : ℝ)..x_cut, (φ' x : ℂ) • F (φ x)‖
        ≤ 2 * π * (C₁ * Real.exp (-κ * c') * M) * (c' * x_cut ^ 2 / 3) := hmono
      _ ≤ 2 * π * (C₁ * Real.exp (-κ * c') * M) * (48 / (c' * √(1 + v))) := by gcongr
      _ = 96 * π * C₁ * Real.exp (-κ * c') * M / (c' * √(1 + v)) := by ring
  -- Piece B: `x_cut..(xiStar/2)`
  have hB : ‖∫ x in x_cut..(xiStar / 2), (φ' x : ℂ) • F (φ x)‖ ≤
      20 * π * C₁ * c' ^ (1 / 2 : ℝ) * Real.exp (-κ * c') * M / √(1 + v) := by
    rcases le_total (xiStar / 2) x_cut with htriv | hx_lt
    · have heq : x_cut = xiStar / 2 := le_antisymm hxc_hi htriv
      rw [heq, intervalIntegral.integral_same, norm_zero]
      positivity
    · have hxc_eq : x_cut = 12 / (c' * (1 + v)) := by
        rw [hxcut, min_eq_right]
        by_contra hcon
        push_neg at hcon
        rw [min_eq_left hcon.le] at hx_lt
        exact lt_irrefl _ hx_lt
      have hxc_pos : 0 < x_cut := by rw [hxc_eq]; positivity
      have hpt_B : ∀ x ∈ Icc x_cut (xiStar / 2),
          ‖(φ' x : ℂ) • F (φ x)‖ ≤ 20 * π * C₁ * c' ^ (1 / 2 : ℝ) * Real.exp (-κ * c') * M / √(1 + v) := by
        intro x hx
        have hx_pos : 0 < x := lt_of_lt_of_le hxc_pos hx.1
        have hx_mem : x ∈ Icc 0 (xiStar / 2) := ⟨hx_pos.le, hx.2⟩
        have hφ'_nn : 0 ≤ φ' x := by dsimp [φ']; positivity
        rw [Complex.coe_smul, norm_smul, Real.norm_of_nonneg hφ'_nn]
        dsimp [F]
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, h2pi_norm]
        have hsqrt_arg : Real.sqrt (c' * φ x / 3) = c' * x / 3 := by
          dsimp [φ]
          rw [show c' * (c' * x ^ 2 / 3) / 3 = (c' * x / 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
        rw [hsqrt_arg]
        set w : ℂ := (4 * (π : ℂ) / 3 * (c' : ℂ) * (x : ℂ)) * (-I * ((v : ℂ) + I / 2))
        have hneg_w : 4 * (π : ℂ) * I * ((v : ℂ) + I / 2) * ((c' * x / 3 : ℝ) : ℂ) = -w := by
          dsimp [w]; push_cast; ring
        rw [hneg_w, besselI0C_neg]
        have hw_re : w.re = c' * (2 * π / 3) * x := by
          have h1 : w = ((c' * (2 * π / 3) * x : ℝ) : ℂ) + (-I * ((4 * π / 3 * c' * v * x : ℝ) : ℂ)) := by
            dsimp [w]; push_cast; ring
          rw [h1]; simp
        obtain ⟨hu_lo, _, _⟩ := norm_u_cpow_half hv
        have hwn : ‖w‖ = (4 * π / 3 * c' * x) * ‖(v : ℂ) + I / 2‖ := by
          have hI : ‖-I * ((v : ℂ) + I / 2)‖ = ‖(v : ℂ) + I / 2‖ := by
            rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
          dsimp [w]
          rw [show 4 * (π : ℂ) / 3 * (c' : ℂ) * (x : ℂ) = ((4 * π / 3 * c' * x : ℝ) : ℂ) by push_cast; ring,
            norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), hI]
        have hwn_lb : 2 * c' * x * (1 + v) ≤ ‖w‖ := by
          rw [hwn]
          calc 2 * c' * x * (1 + v) = (4 * c' * x) * (1 / 2 * (1 + v)) := by ring
            _ ≤ (4 * π / 3 * c' * x) * ‖(v : ℂ) + I / 2‖ := by gcongr; linarith [Real.pi_gt_three]
        have hwn_ge16 : 16 ≤ ‖w‖ := by
          have h1 : 12 ≤ c' * (1 + v) * x := by
            rw [← div_le_iff₀ (by positivity : 0 < c' * (1 + v))]
            linarith [hxc_eq ▸ hx.1]
          nlinarith
        have hdec := besselI0C_strip_decay (by rw [hw_re]; positivity) hwn_ge16
        rw [hw_re] at hdec
        have hw_rpow : ‖w‖ ^ (-(1 : ℝ) / 2) ≤ (c' * x * (1 + v)) ^ (-(1 : ℝ) / 2) := by
          refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by norm_num)
          nlinarith [mul_pos (mul_pos hc0 hx_pos) (by positivity : 0 < 1 + v)]
        have hrp_split : (c' * x * (1 + v)) ^ (-(1 : ℝ) / 2) =
            (c' * x) ^ (-(1 : ℝ) / 2) * (√(1 + v))⁻¹ := by
          rw [Real.mul_rpow (by positivity) (by positivity), Real.sqrt_eq_rpow,
            ← Real.rpow_neg (by positivity)]; ring_nf
        have hcx_comb : (c' * x) ^ (-(1 : ℝ) / 2) * φ' x ≤ c' ^ (1 / 2 : ℝ) := by
          dsimp [φ']
          have hsqx : x ≤ 1 := by linarith [hx.2, xiStar_lt_one]
          have h1 : (c' * x) ^ (-(1 : ℝ) / 2) * x = c' ^ (-(1 : ℝ) / 2) * x ^ (1 / 2 : ℝ) := by
            rw [Real.mul_rpow hc0.le hx_pos.le, mul_assoc]
            congr 1
            have : x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
            conv_lhs => rhs; rw [this]
            rw [← Real.rpow_add hx_pos]; norm_num
          have hc_pow : c' ^ (-(1 : ℝ) / 2) * c' = c' ^ (1 / 2 : ℝ) := by
            conv_lhs => rhs; rw [← Real.rpow_one c']
            rw [← Real.rpow_add hc0]; norm_num
          have hxr : x ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hx_pos.le hsqx (by norm_num)
          calc (c' * x) ^ (-(1 : ℝ) / 2) * (2 * c' * x / 3)
              = (2 / 3 : ℝ) * c' * ((c' * x) ^ (-(1 : ℝ) / 2) * x) := by ring
            _ = (2 / 3 : ℝ) * (c' ^ (-(1 : ℝ) / 2) * c') * x ^ (1 / 2 : ℝ) := by rw [h1]; ring
            _ = (2 / 3 : ℝ) * c' ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by rw [hc_pow]
            _ ≤ 1 * c' ^ (1 / 2 : ℝ) * 1 := by gcongr; norm_num
            _ = c' ^ (1 / 2 : ℝ) := by ring
        have hPJ := hhead hc₁' hg hMpos hx_mem
        calc φ' x * (|g (φ x)| * (2 * π) * ‖Integration.besselI0C w‖)
            ≤ φ' x * (|g (φ x)| * (2 * π) * (10 * Real.exp (c' * (2 * π / 3) * x) * ‖w‖ ^ (-(1 : ℝ) / 2))) := by
              gcongr
          _ ≤ φ' x * (|g (φ x)| * (2 * π) * (10 * Real.exp (c' * (2 * π / 3) * x) *
                ((c' * x) ^ (-(1 : ℝ) / 2) * (√(1 + v))⁻¹))) := by
              gcongr; exact hw_rpow.trans_eq hrp_split
          _ = 20 * π * (|g (φ x)| * Real.exp (c' * (2 * π / 3) * x)) *
                ((c' * x) ^ (-(1 : ℝ) / 2) * φ' x) * (√(1 + v))⁻¹ := by ring
          _ ≤ 20 * π * (C₁ * Real.exp (-κ * c') * M) * c' ^ (1 / 2 : ℝ) * (√(1 + v))⁻¹ := by
              gcongr
          _ = 20 * π * C₁ * c' ^ (1 / 2 : ℝ) * Real.exp (-κ * c') * M / √(1 + v) := by ring
      have hlen : |xiStar / 2 - x_cut| ≤ 1 := by
        rw [abs_of_nonneg (by linarith [hx_lt])]
        linarith [xiStar_lt_one, hxc_pos]
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)).trans ?_
      · rw [uIoc_of_le hx_lt.le] at hx
        exact hpt_B x ⟨hx.1.le, hx.2⟩
      · exact mul_le_of_le_one_right (by positivity) hlen
  -- Combine Piece A + Piece B and absorb `c'^{1/2}` & `c'^2` into `C₂`
  have hc_abs : c' ^ 2 * (96 * π * C₁ * Real.exp (-κ * c') / c' +
      20 * π * C₁ * c' ^ (1 / 2 : ℝ) * Real.exp (-κ * c')) ≤ 200 * π * C₁ * C₂ := by
    have hpow2 : c' ^ 2 * Real.exp (-κ * c') ≤ C₂ * Real.exp (-(κ / 2) * c') := by
      have h1 : c' ^ (2 : ℝ) ≤ c' ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      rw [Real.rpow_two] at h1
      have h2 := hC₂le c' hc1
      have hexp_split : Real.exp (-κ * c') = Real.exp ((κ / 2) * c') * Real.exp (-(3 * κ / 2) * c') := by
        rw [← Real.exp_add]; congr 1; ring
      have hle_c2 : c' ^ 2 * Real.exp (-κ * c') ≤ (C₂ * Real.exp ((κ / 2) * c')) * Real.exp (-κ * c') := by
        gcongr; exact h1.trans h2
      refine hle_c2.trans ?_
      have heq : C₂ * Real.exp ((κ / 2) * c') * Real.exp (-κ * c') = C₂ * Real.exp (-(κ / 2) * c') := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      rw [heq]; exact le_rfl
    have hpow25 : c' ^ 2 * c' ^ (1 / 2 : ℝ) * Real.exp (-κ * c') ≤ C₂ := by
      have h1 : c' ^ 2 * c' ^ (1 / 2 : ℝ) ≤ c' ^ (3 : ℝ) := by
        have : c' ^ 2 = c' ^ (2 : ℝ) := (Real.rpow_two c').symm
        rw [this, ← Real.rpow_add hc0]
        exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      have h2 := hC₂le c' hc1
      have hexp_le : Real.exp ((κ / 2) * c') * Real.exp (-κ * c') ≤ 1 := by
        rw [← Real.exp_add, Real.exp_le_one_iff]; nlinarith
      calc c' ^ 2 * c' ^ (1 / 2 : ℝ) * Real.exp (-κ * c')
          ≤ (C₂ * Real.exp ((κ / 2) * c')) * Real.exp (-κ * c') := by gcongr; exact h1.trans h2
        _ = C₂ * (Real.exp ((κ / 2) * c') * Real.exp (-κ * c')) := by ring
        _ ≤ C₂ * 1 := by gcongr
        _ = C₂ := mul_one C₂
    have hpow1 : c' * Real.exp (-κ * c') ≤ C₂ := by
      have h1 : c' ≤ c' ^ (3 : ℝ) := by
        conv_lhs => rw [← Real.rpow_one c']
        exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      have h2 := hC₂le c' hc1
      have hexp_le : Real.exp ((κ / 2) * c') * Real.exp (-κ * c') ≤ 1 := by
        rw [← Real.exp_add, Real.exp_le_one_iff]; nlinarith
      calc c' * Real.exp (-κ * c') ≤ (C₂ * Real.exp ((κ / 2) * c')) * Real.exp (-κ * c') := by
            gcongr; exact h1.trans h2
        _ = C₂ * (Real.exp ((κ / 2) * c') * Real.exp (-κ * c')) := by ring
        _ ≤ C₂ * 1 := by gcongr
        _ = C₂ := mul_one C₂
    have he1 : Real.exp (-(κ / 2) * c') ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    calc c' ^ 2 * (96 * π * C₁ * Real.exp (-κ * c') / c' +
            20 * π * C₁ * c' ^ (1 / 2 : ℝ) * Real.exp (-κ * c'))
        = 96 * π * C₁ * (c' * (c' * Real.exp (-κ * c') / c')) +
            20 * π * C₁ * (c' ^ 2 * c' ^ (1 / 2 : ℝ) * Real.exp (-κ * c')) := by ring
      _ = 96 * π * C₁ * (c' * Real.exp (-κ * c')) +
            20 * π * C₁ * (c' ^ 2 * c' ^ (1 / 2 : ℝ) * Real.exp (-κ * c')) := by
          field_simp [hc0.ne']
      _ ≤ 96 * π * C₁ * C₂ + 20 * π * C₁ * C₂ := by gcongr
      _ ≤ 200 * π * C₁ * C₂ := by have : 0 ≤ π * C₁ * C₂ := by positivity; linarith
  calc ‖(∫ x in (0 : ℝ)..x_cut, (φ' x : ℂ) • F (φ x)) +
          ∫ x in x_cut..(xiStar / 2), (φ' x : ℂ) • F (φ x)‖
      ≤ ‖∫ x in (0 : ℝ)..x_cut, (φ' x : ℂ) • F (φ x)‖ +
          ‖∫ x in x_cut..(xiStar / 2), (φ' x : ℂ) • F (φ x)‖ := norm_add_le _ _
    _ ≤ 96 * π * C₁ * Real.exp (-κ * c') * M / (c' * √(1 + v)) +
          20 * π * C₁ * c' ^ (1 / 2 : ℝ) * Real.exp (-κ * c') * M / √(1 + v) := add_le_add hA hB
    _ = (c' ^ 2 * (96 * π * C₁ * Real.exp (-κ * c') / c' +
            20 * π * C₁ * c' ^ (1 / 2 : ℝ) * Real.exp (-κ * c'))) * M / (c' ^ 2 * √(1 + v)) := by
        field_simp [hc0.ne', (Real.sqrt_pos.mpr (by linarith : 0 < 1 + v)).ne']; ring
    _ ≤ (200 * π * C₁ * C₂) * M / (c' ^ 2 * √(1 + v)) := by gcongr

/-- **`cts:edge-hankel` (2) at spinless Virasoro (Lemma C5(2))**, unrestricted in `v ≥ 0`.
There exist `c₀, C > 0` such that for every `c' ≥ c₀`, every test `g` in
`TestClass virasoroProblem (c' / 12) g`, and every `v ≥ 0`:
`‖G(v + i/2) + (√2 π e^{iπ/4} / (v + i/2)^{1/2}) ∫_{ξ_*/2}^∞ g(t(x)) V(t(x))`
`  * ((1 - e^{-4πx})^{-2} + a₁(x)/(c'(v + i/2)) + a₂(x)/c') e^{-i(4π/3)c'vx} (2c'x/3) dx‖`
`  ≤ C * M[g] / (c' ^ 2 * √(1 + v))`,
where `G = Integration.hankelContinuation c' g` and `t(x) = c' x^2 / 3`. -/
theorem edge_hankel_two_virasoro :
    ∃ c₀ C : ℝ, 10000 ≤ c₀ ∧ 0 < C ∧ ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {g : ℝ → ℝ},
      TestClass virasoroProblem (c' / 12) g → ∀ {v : ℝ}, 0 ≤ v →
        ‖Integration.hankelContinuation c' g ((v : ℂ) + I / 2) -
            (-(√2 * (π : ℂ) * Complex.exp (I * (π : ℂ) / 4)) /
              ((v : ℂ) + I / 2) ^ (1 / 2 : ℂ)) *
              ∫ x in Ioi (xiStar / 2),
                ((g (c' * x ^ 2 / 3) * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) : ℝ) : ℂ) *
                  ((((1 - Real.exp (-4 * π * x)) ^ 2 : ℝ) : ℂ)⁻¹ +
                    virasoroA1 x / ((c' : ℂ) * ((v : ℂ) + I / 2)) +
                    ((virasoroA2 x / c' : ℝ) : ℂ)) *
                  Complex.exp (-I * ((4 * π / 3 * c' * v * x : ℝ) : ℂ)) *
                  ((2 * c' * x / 3 : ℝ) : ℂ)‖ ≤
          C * virasoroProblem.cardyNorm (c' / 12) g / (c' ^ 2 * √(1 + v)) := by
  obtain ⟨c₁, C₁, hc₁, hC₁, hkern⟩ := edge_kernel_pointwise_error
  obtain ⟨c₂, C₂, hc₂, hC₂, hhead⟩ := edge_hankel_head_decay
  refine ⟨max c₁ c₂, C₁ + C₂, hc₁.trans (le_max_left _ _), by positivity,
    fun {c'} hc' {g} hg {v} hv => ?_⟩
  have hc₁' : c₁ ≤ c' := (le_max_left _ _).trans hc'
  have hc₂' : c₂ ≤ c' := (le_max_right _ _).trans hc'
  have hc0 : 0 < c' := by linarith
  have hc10k : 10000 ≤ c' := by linarith
  have ha : 2 ≤ c' / 12 := by linarith
  have hshift : virasoroProblem.totalShift ≤ c' / 12 := by rw [virasoroProblem_totalShift]; exact ha
  set M : ℝ := virasoroProblem.cardyNorm (c' / 12) g
  have hMnn : 0 ≤ M := virasoroProblem.cardyNorm_nonneg hshift g
  let φ : ℝ → ℝ := fun x => c' * x ^ 2 / 3
  let φ' : ℝ → ℝ := fun x => (2 * c' * x / 3 : ℝ)
  set t₀ : ℝ := φ (xiStar / 2) with ht₀def
  have ht₀_pos : 0 < t₀ := by rw [ht₀def]; dsimp [φ]; positivity [xiStar_pos]
  let mainIntegrand : ℝ → ℂ := fun x =>
    ((g (φ x) * Bessel.besselV (c' / 12) (φ x) : ℝ) : ℂ) *
      ((((1 - Real.exp (-4 * π * x)) ^ 2 : ℝ) : ℂ)⁻¹ +
        virasoroA1 x / ((c' : ℂ) * ((v : ℂ) + I / 2)) +
        ((virasoroA2 x / c' : ℝ) : ℂ)) *
      Complex.exp (-I * ((4 * π / 3 * c' * v * x : ℝ) : ℂ)) * (φ' x : ℂ)
  let pref : ℂ := -(√2 * (π : ℂ) * Complex.exp (I * (π : ℂ) / 4)) / ((v : ℂ) + I / 2) ^ (1 / 2 : ℂ)
  have hmain_eq : ∀ x : ℝ, pref * mainIntegrand x = (g (φ x) : ℂ) * edgeMainKernel c' v x * (φ' x : ℂ) := by
    intro x
    dsimp [pref, mainIntegrand, edgeMainKernel]
    push_cast; ring
  have hV_int : IntegrableOn (fun t => |g t| * Bessel.besselV (c' / 12) t) (Ioi 0) := by
    refine hg.int_cardy.congr_fun (fun t ht => ?_) measurableSet_Ioi
    change |g t| * virasoroProblem.cardyV (c' / 12) t = _
    rw [Integration.virasoro_cardyV_eq_besselV ha (mem_Ioi.mp ht).le]
  -- Handle `M = 0` via `g =ᵐ 0` on `Ioi 0`
  rcases eq_or_lt_of_le hMnn with hM0 | hMpos
  · have hg_ae : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), g t = 0 := by
      have hint0 : ∫ t in Ioi (0 : ℝ), |g t| * virasoroProblem.cardyV (c' / 12) t = 0 := hM0.symm
      have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t => |g t| * virasoroProblem.cardyV (c' / 12) t :=
        ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
          mul_nonneg (abs_nonneg _) (virasoroProblem.cardyV_nonneg hshift (mem_Ioi.mp ht).le)
      have hae0 := (integral_eq_zero_iff_of_nonneg_ae hnn hg.int_cardy).mp hint0
      filter_upwards [hae0, ae_restrict_mem measurableSet_Ioi] with t ht h0
      have hVgt : 0 < virasoroProblem.cardyV (c' / 12) t := by
        have := Integration.virasoro_cardyV_ge ha (mem_Ioi.mp h0).le
        have : 0 < 8 * π ^ 4 * t ^ 2 := by positivity [mem_Ioi.mp h0]
        linarith
      rcases mul_eq_zero.mp ht with h | h
      · exact abs_eq_zero.mp h
      · exact absurd h hVgt.ne'
    have hL : Integration.hankelContinuation c' g ((v : ℂ) + I / 2) = 0 := by
      unfold Integration.hankelContinuation
      have hfun : (fun t => (g t : ℂ) *
          Integration.besselI0C (4 * (π : ℂ) * I * ((v : ℂ) + I / 2) * (Real.sqrt (c' * t / 3) : ℝ))) =ᵐ[
            volume.restrict (Ioi (0 : ℝ))] 0 := by
        filter_upwards [hg_ae] with t ht; simp [ht]
      rw [integral_congr_ae hfun]; simp
    have hg_cont0 : ∀ t ∈ Ioi (0 : ℝ), g t = 0 := by
      intro t ht
      by_contra hne
      have hU := ((hg.cont.continuousAt (Ici_mem_nhds ht)).eventually_ne hne).and (Ioi_mem_nhds ht)
      obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp hU
      have hm : volume (Ioo t (t + ε)) ≠ 0 := by simp [hεpos]
      have hbad_ae : ∀ᵐ s ∂(volume.restrict (Ioo t (t + ε))), g s = 0 :=
        ae_mono (Measure.restrict_mono (Ioo_subset_Ioi_self.trans (Ioi_subset_Ioi ht.le)) le_rfl) hg_ae
      have hne_ae : ∀ᵐ s ∂(volume.restrict (Ioo t (t + ε))), g s ≠ 0 :=
        ae_restrict_of_forall_mem measurableSet_Ioo fun s hs =>
          (hε (by rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]; linarith [hs.2])).1
      have hfalse : ∀ᵐ s ∂(volume.restrict (Ioo t (t + ε))), False := by
        filter_upwards [hbad_ae, hne_ae] with s hs1 hs2
        exact hs2 hs1
      have hnull : (volume.restrict (Ioo t (t + ε))) univ = 0 := by
        simpa [ae_iff] using hfalse
      rw [Measure.restrict_apply_univ] at hnull
      exact hm hnull
    have hR : ∫ x in Ioi (xiStar / 2), mainIntegrand x = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
      have hx0 : 0 < x := lt_trans (by positivity [xiStar_pos]) (mem_Ioi.mp hx)
      have hφ_pos : 0 < φ x := by dsimp [φ]; positivity
      simp [mainIntegrand, hg_cont0 (φ x) hφ_pos]
    rw [hL, hR, mul_zero, sub_zero, norm_zero]
    positivity
  -- Case `0 < M`
  let F : ℝ → ℂ := fun t => (g t : ℂ) * (-2 * (π : ℂ)) *
    Integration.besselI0C (4 * (π : ℂ) * I * ((v : ℂ) + I / 2) * (Real.sqrt (c' * t / 3) : ℝ))
  have hb_strip : |((v : ℂ) + I / 2).im| ≤ 1 / 2 := by simp [abs_of_nonneg]
  have hint_F_Ioi : IntegrableOn F (Ioi 0) := by
    have hK_int := (Integration.lemmaB_d_integral (by linarith) hg).1
    have hmeas : AEStronglyMeasurable F (volume.restrict (Ioi 0)) := by
      have hg_m : AEStronglyMeasurable (fun t : ℝ => (g t : ℂ)) (volume.restrict (Ioi 0)) :=
        Complex.continuous_ofReal.comp_continuousOn hg.cont |>.mono Ioi_subset_Ici_self |>.aestronglyMeasurable measurableSet_Ioi
      have hI0_cont : Continuous Integration.besselI0C := by
        unfold Integration.besselI0C
        refine continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (by fun_prop) 0 π)
      exact (hg_m.mul_const _).mul (hI0_cont.comp (by fun_prop)).aestronglyMeasurable
    refine Integrable.mono' (hK_int.const_mul (2 * π)) hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp [F]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      show ‖(-2 * (π : ℂ))‖ = 2 * π by
        rw [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
          Real.norm_of_nonneg Real.pi_pos.le]]
    have hI_le := Integration.besselI0C_strip_le hc0 (mem_Ioi.mp ht).le hb_strip
    calc |g t| * (2 * π) * ‖Integration.besselI0C _‖
        ≤ |g t| * (2 * π) * kernelK 1 (c' / 12) t := by gcongr
      _ = 2 * π * (|g t| * kernelK 1 (c' / 12) t) := by ring
  have hG_eq : Integration.hankelContinuation c' g ((v : ℂ) + I / 2) = ∫ t in Ioi 0, F t := by
    unfold Integration.hankelContinuation
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    dsimp [F]; ring
  have hsplit_Ioi : Ioi (0 : ℝ) = Ioc 0 t₀ ∪ Ioi t₀ := (Ioc_union_Ioi_eq_Ioi ht₀_pos.le).symm
  have hF_Ioc : IntegrableOn F (Ioc 0 t₀) := hint_F_Ioi.mono_set Ioc_subset_Ioi_self
  have hF_Ioi : IntegrableOn F (Ioi t₀) := hint_F_Ioi.mono_set (Ioi_subset_Ioi ht₀_pos.le)
  rw [hG_eq, hsplit_Ioi, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hF_Ioc hF_Ioi]
  have hV_cont : ContinuousOn (Bessel.besselV (c' / 12)) (Ici 0) :=
    (continuous_cardyV virasoroProblem (c' / 12)).continuousOn.congr fun t ht =>
      (Integration.virasoro_cardyV_eq_besselV ha (mem_Ici.mp ht)).symm
  have hφ_ge0 : ∀ x ∈ Ici (xiStar / 2), 0 ≤ φ x := fun x _ => by dsimp [φ]; positivity
  have hV_Ioi : IntegrableOn (fun t => |g t| * Bessel.besselV (c' / 12) t) (Ioi t₀) :=
    hV_int.mono_set (Ioi_subset_Ioi ht₀_pos.le)
  have hφ_mono : Tendsto φ atTop atTop := by
    dsimp [φ]
    exact (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).const_mul_atTop hc0 |>.atTop_div_const (by norm_num)
  have hV_tend : Tendsto (fun R : ℝ => ∫ t in t₀..(φ R), |g t| * Bessel.besselV (c' / 12) t) atTop
      (𝓝 (∫ t in Ioi t₀, |g t| * Bessel.besselV (c' / 12) t)) :=
    (intervalIntegral_tendsto_integral_Ioi t₀ hV_Ioi tendsto_id).comp hφ_mono
  have hcont_V_all : Continuous (fun x => |g (φ x)| * Bessel.besselV (c' / 12) (φ x) * φ' x) := by
    have hφ_all_nn : ∀ x : ℝ, 0 ≤ φ x := fun x => by dsimp [φ]; positivity
    exact ((hg.cont.abs.comp_continuous (by dsimp [φ]; fun_prop) hφ_all_nn).mul
      (hV_cont.comp_continuous (by dsimp [φ]; fun_prop) hφ_all_nn)).mul (by dsimp [φ']; fun_prop)
  have hV_phi_int : IntegrableOn (fun x => |g (φ x)| * Bessel.besselV (c' / 12) (φ x) * φ' x)
      (Ioi (xiStar / 2)) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
      (∫ t in Ioi t₀, |g t| * Bessel.besselV (c' / 12) t) (xiStar / 2)
      (fun R => (hcont_V_all.intervalIntegrable (xiStar / 2) R).1)
      (hcont_V_all.aestronglyMeasurable.mono_measure Measure.restrict_le_self) ?_
    refine eventually_atTop.mpr ⟨xiStar / 2, fun R hR => ?_⟩
    have hd : ∀ x ∈ uIcc (xiStar / 2) R, HasDerivAt φ (φ' x) x := fun x _ => by
      dsimp [φ, φ']; exact ((hasDerivAt_pow 2 x).const_mul c' |>.div_const 3).congr_deriv (by ring)
    have hφ'_c : ContinuousOn φ' (uIcc (xiStar / 2) R) := by dsimp [φ']; fun_prop
    have hcont_t : ContinuousOn (fun t => |g t| * Bessel.besselV (c' / 12) t)
        (φ '' uIcc (xiStar / 2) R) := by
      have himg : φ '' uIcc (xiStar / 2) R ⊆ Ici 0 := by rintro t ⟨x, _, rfl⟩; dsimp [φ]; positivity
      exact (hg.cont.abs.mul hV_cont).mono himg
    have hcov := intervalIntegral.integral_comp_mul_deriv' hd hφ'_c hcont_t
    have hcov' : ∫ x in (xiStar / 2)..R, |g (φ x)| * Bessel.besselV (c' / 12) (φ x) * φ' x =
        ∫ t in t₀..(φ R), |g t| * Bessel.besselV (c' / 12) t := by
      simpa [ht₀def] using hcov
    have hnn : 0 ≤ ∫ x in (xiStar / 2)..R, |g (φ x)| * Bessel.besselV (c' / 12) (φ x) * φ' x := by
      refine intervalIntegral.integral_nonneg hR fun x hx => ?_
      have hV0 : 0 ≤ Bessel.besselV (c' / 12) (φ x) := by
        rw [← Integration.virasoro_cardyV_eq_besselV ha (by dsimp [φ]; positivity)]
        exact virasoroProblem.cardyV_nonneg hshift (by dsimp [φ]; positivity)
      have hx0 : 0 ≤ x := by linarith [xiStar_pos, hx.1]
      have hφ'0 : 0 ≤ φ' x := by dsimp [φ']; positivity
      exact mul_nonneg (mul_nonneg (abs_nonneg _) hV0) hφ'0
    have ht₀_le : t₀ ≤ φ R := by
      dsimp [t₀, φ]; gcongr; linarith [xiStar_pos]
    rw [Real.norm_of_nonneg hnn, hcov', intervalIntegral.integral_of_le ht₀_le]
    refine setIntegral_mono_set hV_Ioi ?_ Ioc_subset_Ioi_self.eventuallySubset
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      mul_nonneg (abs_nonneg _) (by
        rw [← Integration.virasoro_cardyV_eq_besselV ha (mem_Ioi.mp ht).le]
        exact virasoroProblem.cardyV_nonneg hshift (mem_Ioi.mp ht).le)
  have hV_phi_le : ∫ x in Ioi (xiStar / 2), |g (φ x)| * Bessel.besselV (c' / 12) (φ x) * φ' x ≤ M := by
    have h1 := intervalIntegral_tendsto_integral_Ioi (xiStar / 2) hV_phi_int tendsto_id
    have heq : ∫ x in Ioi (xiStar / 2), |g (φ x)| * Bessel.besselV (c' / 12) (φ x) * φ' x =
        ∫ t in Ioi t₀, |g t| * Bessel.besselV (c' / 12) t := by
      refine tendsto_nhds_unique h1 ?_
      refine hV_tend.congr' (eventually_atTop.mpr ⟨xiStar / 2, fun R hR => ?_⟩)
      have hd : ∀ x ∈ uIcc (xiStar / 2) R, HasDerivAt φ (φ' x) x := fun x _ => by
        dsimp [φ, φ']; exact ((hasDerivAt_pow 2 x).const_mul c' |>.div_const 3).congr_deriv (by ring)
      have hcont_t : ContinuousOn (fun t => |g t| * Bessel.besselV (c' / 12) t)
          (φ '' uIcc (xiStar / 2) R) := by
        have himg : φ '' uIcc (xiStar / 2) R ⊆ Ici 0 := by
          rintro t ⟨x, _, rfl⟩; dsimp [φ]; exact div_nonneg (mul_nonneg hc0.le (sq_nonneg x)) (by norm_num)
        exact (hg.cont.abs.mul hV_cont).mono himg
      simpa [ht₀def] using (intervalIntegral.integral_comp_mul_deriv' hd (by dsimp [φ']; fun_prop) hcont_t).symm
    rw [heq]
    calc ∫ t in Ioi t₀, |g t| * Bessel.besselV (c' / 12) t
        ≤ ∫ t in Ioi (0 : ℝ), |g t| * Bessel.besselV (c' / 12) t := by
          refine setIntegral_mono_set hV_int ?_ (Ioi_subset_Ioi ht₀_pos.le).eventuallySubset
          exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
            mul_nonneg (abs_nonneg _) (by
              rw [← Integration.virasoro_cardyV_eq_besselV ha (mem_Ioi.mp ht).le]
              exact virasoroProblem.cardyV_nonneg hshift (mem_Ioi.mp ht).le)
      _ = M := by
          dsimp [M]; unfold FixedWeightProblem.cardyNorm
          refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
          rw [Integration.virasoro_cardyV_eq_besselV ha (mem_Ioi.mp ht).le]
  have hmain_cont : ContinuousOn mainIntegrand (Ici (xiStar / 2)) := by
    have hden_ne : ∀ x ∈ Ici (xiStar / 2), (1 - Real.exp (-4 * π * x)) ^ 2 ≠ 0 := fun x hx =>
      pow_ne_zero 2 (by linarith [one_sub_exp_ge_half hx])
    have hx_ne : ∀ x ∈ Ici (xiStar / 2), (x : ℂ) ≠ 0 := fun x hx =>
      Complex.ofReal_ne_zero.mpr (by linarith [xiStar_pos, mem_Ici.mp hx])
    have hV_c : ContinuousOn (fun x => ((g (φ x) * Bessel.besselV (c' / 12) (φ x) : ℝ) : ℂ))
        (Ici (xiStar / 2)) :=
      Complex.continuous_ofReal.comp_continuousOn
        ((hg.cont.comp (by dsimp [φ]; fun_prop) hφ_ge0).mul
          (hV_cont.comp (by dsimp [φ]; fun_prop) hφ_ge0))
    have ha1_c : ContinuousOn virasoroA1 (Ici (xiStar / 2)) := by
      intro x hx
      unfold virasoroA1
      have hne : 32 * (π : ℂ) * (x : ℂ) * ((1 - Real.exp (-4 * π * x)) ^ 2 : ℝ) ≠ 0 := by
        have h1 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
        have h2 := hx_ne x hx
        have h3 : (((1 - Real.exp (-4 * π * x)) ^ 2 : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (hden_ne x hx)
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h1) h2) h3
      exact ContinuousAt.continuousWithinAt (by fun_prop (disch := exact hne))
    have ha2_c : ContinuousOn virasoroA2 (Ici (xiStar / 2)) := by
      intro x hx
      unfold virasoroA2 virasoroV1
      have hne1 : 16 * π * x ≠ 0 := by
        have hxpos : 0 < x := lt_of_lt_of_le (by positivity [xiStar_pos]) (mem_Ici.mp hx)
        positivity
      have hne4 : (1 - Real.exp (-4 * π * x)) ^ 4 ≠ 0 :=
        pow_ne_zero 4 (by linarith [one_sub_exp_ge_half hx])
      exact ContinuousAt.continuousWithinAt (by fun_prop (disch := first | exact hne1 | exact hne4))
    have hinv_c : ContinuousOn (fun x => (((1 - Real.exp (-4 * π * x)) ^ 2 : ℝ) : ℂ)⁻¹) (Ici (xiStar / 2)) := by
      intro x hx
      have hne : (((1 - Real.exp (-4 * π * x)) ^ 2 : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (hden_ne x hx)
      exact ContinuousAt.continuousWithinAt (by fun_prop (disch := exact hne))
    exact (((hV_c.mul ((hinv_c.add (ha1_c.div_const _)).add
      (Complex.continuous_ofReal.comp_continuousOn (ha2_c.div_const c')))).mul
      (by fun_prop : Continuous fun x : ℝ => Complex.exp (-I * ((4 * π / 3 * c' * v * x : ℝ) : ℂ))).continuousOn).mul
      (by dsimp [φ']; fun_prop : Continuous fun x : ℝ => (φ' x : ℂ)).continuousOn)
  have hmain_int : IntegrableOn mainIntegrand (Ioi (xiStar / 2)) := by
    refine Integrable.mono' (hV_phi_int.const_mul 100)
      (hmain_cont.mono Ioi_subset_Ici_self |>.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : xiStar / 2 ≤ x := (mem_Ioi.mp hx).le
    have hxpos : 0 < x := lt_of_lt_of_le (by positivity [xiStar_pos]) hx'
    have hφ_nn : 0 ≤ φ x := by dsimp [φ]; positivity
    have hV_nn : 0 ≤ Bessel.besselV (c' / 12) (φ x) := by
      rw [← Integration.virasoro_cardyV_eq_besselV ha hφ_nn]
      exact virasoroProblem.cardyV_nonneg hshift hφ_nn
    have hφ'_nn : 0 ≤ φ' x := by dsimp [φ']; positivity
    have hd_lb := one_sub_exp_ge_half hx'
    have hinv_bd : ‖(((1 - Real.exp (-4 * π * x)) ^ 2 : ℝ) : ℂ)⁻¹‖ ≤ 4 := by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _),
        inv_le_comm₀ (by positivity) (by norm_num)]
      nlinarith
    have ha1_bd : ‖virasoroA1 x / ((c' : ℂ) * ((v : ℂ) + I / 2))‖ ≤ 1 := by
      dsimp [virasoroA1]
      have hx5 : (1 / 10 : ℝ) ≤ x := by linarith [Bessel.one_fifth_le_xiStar]
      obtain ⟨hu_lo, _, _⟩ := norm_u_cpow_half hv
      simp only [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_I,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, abs_of_pos hxpos,
        abs_of_pos (sq_pos_of_pos (by linarith : 0 < 1 - Real.exp (-4 * π * x))),
        abs_of_pos hc0, mul_one]
      have hden : 32 * π * x * (1 - Real.exp (-4 * π * x)) ^ 2 * (c' * ‖(v : ℂ) + I / 2‖) ≥ 3 := by
        have hpi := Real.pi_gt_three
        have : 1 / 3 ≤ ‖(v : ℂ) + I / 2‖ := by linarith
        nlinarith [show (1 / 4 : ℝ) ≤ (1 - Real.exp (-4 * π * x)) ^ 2 by nlinarith]
      exact div_le_one_of_le₀ (by linarith) (by positivity)
    have ha2_bd : ‖((virasoroA2 x / c' : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hc0]
      have ha2 : |virasoroA2 x| ≤ 480 := by
        dsimp [virasoroA2]
        rw [abs_div, abs_neg, abs_of_pos (pow_pos (by linarith [hd_lb]) 4)]
        calc |virasoroV1 x| / (1 - Real.exp (-4 * π * x)) ^ 4 ≤ 30 / (1 / 2) ^ 4 := by
              gcongr; exact virasoroV1_abs_le hx'; exact pow_le_pow_left₀ (by positivity) hd_lb 4
          _ = 480 := by norm_num
      rw [div_le_one hc0]; linarith
    have hexp_n : ‖Complex.exp (-I * ((4 * π / 3 * c' * v * x : ℝ) : ℂ))‖ = 1 := by
      rw [show -I * ((4 * π / 3 * c' * v * x : ℝ) : ℂ) =
        ((-(4 * π / 3 * c' * v * x) : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    dsimp [mainIntegrand]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, hexp_n, mul_one,
      Real.norm_of_nonneg hφ'_nn, Real.norm_eq_abs, abs_mul, abs_of_nonneg hV_nn]
    have hmid : ‖(((1 - Real.exp (-4 * π * x)) ^ 2 : ℝ) : ℂ)⁻¹ +
        virasoroA1 x / ((c' : ℂ) * ((v : ℂ) + I / 2)) + ((virasoroA2 x / c' : ℝ) : ℂ)‖ ≤ 100 := by
      calc _ ≤ ‖(((1 - Real.exp (-4 * π * x)) ^ 2 : ℝ) : ℂ)⁻¹‖ +
            ‖virasoroA1 x / ((c' : ℂ) * ((v : ℂ) + I / 2))‖ + ‖((virasoroA2 x / c' : ℝ) : ℂ)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ 4 + 1 + 1 := add_le_add (add_le_add hinv_bd ha1_bd) ha2_bd
        _ ≤ 100 := by norm_num
    calc |g (φ x)| * Bessel.besselV (c' / 12) (φ x) * ‖_‖ * φ' x
        ≤ |g (φ x)| * Bessel.besselV (c' / 12) (φ x) * 100 * φ' x := by gcongr
      _ = 100 * (|g (φ x)| * Bessel.besselV (c' / 12) (φ x) * φ' x) := by ring
  have hF_phi_int : IntegrableOn (fun x => (φ' x : ℂ) • F (φ x)) (Ioi (xiStar / 2)) := by
    have hF_cont_x : ContinuousOn (fun x => (φ' x : ℂ) • F (φ x)) (Ici (xiStar / 2)) := by
      have hI0_c : Continuous Integration.besselI0C := by
        unfold Integration.besselI0C
        refine continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (by fun_prop) 0 π)
      exact (by dsimp [φ']; fun_prop : Continuous fun x : ℝ => (φ' x : ℂ)).continuousOn.smul
        (((Complex.continuous_ofReal.comp_continuousOn (hg.cont.comp (by dsimp [φ]; fun_prop) hφ_ge0)).mul
          continuousOn_const).mul ((hI0_c.comp (by dsimp [φ]; fun_prop)).continuousOn))
    refine Integrable.mono' ((hV_phi_int.const_mul (C₁ / (c' ^ 2 * √(1 + v)))).add
      (hmain_int.norm.const_mul ‖pref‖))
      (hF_cont_x.mono Ioi_subset_Ici_self |>.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : xiStar / 2 ≤ x := (mem_Ioi.mp hx).le
    have hxpos : 0 < x := lt_of_lt_of_le (by positivity [xiStar_pos]) hx'
    have hφ'_nn : 0 ≤ φ' x := by dsimp [φ']; positivity
    have hV_nn : 0 ≤ Bessel.besselV (c' / 12) (φ x) := by
      rw [← Integration.virasoro_cardyV_eq_besselV ha (by dsimp [φ]; positivity)]
      exact virasoroProblem.cardyV_nonneg hshift (by dsimp [φ]; positivity)
    have hdiff_k := hkern hc₁' hv hx'
    have hdiff_rew : (φ' x : ℂ) • F (φ x) - pref * mainIntegrand x =
        (g (φ x) : ℂ) * ((-2 * (π : ℂ)) *
          Integration.besselI0C (4 * (π : ℂ) * I * ((v : ℂ) + I / 2) *
            (Real.sqrt (c' * φ x / 3) : ℝ)) - edgeMainKernel c' v x) * (φ' x : ℂ) := by
      rw [hmain_eq]; dsimp [F]; ring
    calc ‖(φ' x : ℂ) • F (φ x)‖
        = ‖((φ' x : ℂ) • F (φ x) - pref * mainIntegrand x) + pref * mainIntegrand x‖ := by
          congr 1; ring
      _ ≤ ‖(φ' x : ℂ) • F (φ x) - pref * mainIntegrand x‖ + ‖pref * mainIntegrand x‖ := norm_add_le _ _
      _ = |g (φ x)| * ‖(-2 * (π : ℂ)) * _ - edgeMainKernel c' v x‖ * φ' x + ‖pref‖ * ‖mainIntegrand x‖ := by
          rw [hdiff_rew, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_of_nonneg hφ'_nn]
      _ ≤ |g (φ x)| * (C₁ * Bessel.besselV (c' / 12) (φ x) / (c' ^ 2 * √(1 + v))) * φ' x +
            ‖pref‖ * ‖mainIntegrand x‖ := by gcongr
      _ = C₁ / (c' ^ 2 * √(1 + v)) * (|g (φ x)| * Bessel.besselV (c' / 12) (φ x) * φ' x) +
            ‖pref‖ * ‖mainIntegrand x‖ := by ring
  have hF_cov : ∫ t in Ioi t₀, F t = ∫ x in Ioi (xiStar / 2), (φ' x : ℂ) • F (φ x) := by
    have hL := (intervalIntegral_tendsto_integral_Ioi t₀ hF_Ioi tendsto_id).comp hφ_mono
    have hR := intervalIntegral_tendsto_integral_Ioi (xiStar / 2) hF_phi_int tendsto_id
    refine tendsto_nhds_unique hL (hR.congr' (eventually_atTop.mpr ⟨xiStar / 2, fun R hR => ?_⟩))
    rw [Function.comp_apply, id_eq]
    have hd : ∀ x ∈ uIcc (xiStar / 2) R, HasDerivAt φ (φ' x) x := fun x _ => by
      dsimp [φ, φ']; exact ((hasDerivAt_pow 2 x).const_mul c' |>.div_const 3).congr_deriv (by ring)
    have hF_c : ContinuousOn F (φ '' uIcc (xiStar / 2) R) := by
      have himg : φ '' uIcc (xiStar / 2) R ⊆ Ici 0 := by
        rintro t ⟨x, _, rfl⟩; dsimp [φ]; exact div_nonneg (mul_nonneg hc0.le (sq_nonneg x)) (by norm_num)
      have hI0_c : Continuous Integration.besselI0C := by
        unfold Integration.besselI0C
        refine continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (by fun_prop) 0 π)
      exact (((Complex.continuous_ofReal.comp_continuousOn hg.cont).mono himg).mul continuousOn_const).mul
        ((hI0_c.comp (by fun_prop)).continuousOn)
    have hcomp := intervalIntegral.integral_deriv_smul_comp' hd (by dsimp [φ']; fun_prop) hF_c
    have hsmul : ∫ x in (xiStar / 2)..R, (φ' x : ℂ) • F (φ x) =
        ∫ x in (xiStar / 2)..R, φ' x • F (φ x) :=
      intervalIntegral.integral_congr fun x _ => by simp [Complex.real_smul, smul_eq_mul]
    rw [hsmul]
    simpa [ht₀def] using hcomp
  rw [hF_cov]
  have hpref_main_eq : (∫ x in Ioi (xiStar / 2), (pref * mainIntegrand x)) =
      pref * ∫ x in Ioi (xiStar / 2), mainIntegrand x := MeasureTheory.integral_const_mul _ _
  have htail_diff : ‖∫ x in Ioi (xiStar / 2), (φ' x : ℂ) • F (φ x) -
        pref * ∫ x in Ioi (xiStar / 2), mainIntegrand x‖ ≤ C₁ * M / (c' ^ 2 * √(1 + v)) := by
    have hsub_int : (∫ x in Ioi (xiStar / 2), (φ' x : ℂ) • F (φ x)) -
          pref * ∫ x in Ioi (xiStar / 2), mainIntegrand x =
        ∫ x in Ioi (xiStar / 2), ((φ' x : ℂ) • F (φ x) - pref * mainIntegrand x) := by
      rw [← hpref_main_eq, ← MeasureTheory.integral_sub hF_phi_int (hmain_int.const_mul pref)]
    rw [hsub_int]
    have hint_bd : IntegrableOn
        (fun x => C₁ / (c' ^ 2 * √(1 + v)) * (|g (φ x)| * Bessel.besselV (c' / 12) (φ x) * φ' x))
        (Ioi (xiStar / 2)) := hV_phi_int.const_mul _
    have hnorm := norm_integral_le_of_norm_le hint_bd ?_
    · rw [integral_const_mul] at hnorm
      calc _ ≤ C₁ / (c' ^ 2 * √(1 + v)) *
              ∫ x in Ioi (xiStar / 2), |g (φ x)| * Bessel.besselV (c' / 12) (φ x) * φ' x := hnorm
        _ ≤ C₁ / (c' ^ 2 * √(1 + v)) * M := by gcongr
        _ = C₁ * M / (c' ^ 2 * √(1 + v)) := by ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx' : xiStar / 2 ≤ x := (mem_Ioi.mp hx).le
      have hxpos : 0 < x := lt_of_lt_of_le (by positivity [xiStar_pos]) hx'
      have hφ'_nn : 0 ≤ φ' x := by dsimp [φ']; positivity
      have hdiff_rew : (φ' x : ℂ) • F (φ x) - pref * mainIntegrand x =
          (g (φ x) : ℂ) * ((-2 * (π : ℂ)) *
            Integration.besselI0C (4 * (π : ℂ) * I * ((v : ℂ) + I / 2) *
              (Real.sqrt (c' * φ x / 3) : ℝ)) - edgeMainKernel c' v x) * (φ' x : ℂ) := by
        rw [hmain_eq]; dsimp [F]; ring
      rw [hdiff_rew, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_of_nonneg hφ'_nn]
      calc |g (φ x)| * ‖_‖ * φ' x
          ≤ |g (φ x)| * (C₁ * Bessel.besselV (c' / 12) (φ x) / (c' ^ 2 * √(1 + v))) * φ' x := by
            gcongr; exact hkern hc₁' hv hx'
        _ = C₁ / (c' ^ 2 * √(1 + v)) * (|g (φ x)| * Bessel.besselV (c' / 12) (φ x) * φ' x) := by
            ring
  have hhead_bd : ‖∫ t in Ioc 0 t₀, F t‖ ≤ C₂ * M / (c' ^ 2 * √(1 + v)) := hhead hc₂' hg hMpos hv
  change ‖((∫ t in Ioc 0 t₀, F t) + ∫ x in Ioi (xiStar / 2), (φ' x : ℂ) • F (φ x)) -
      pref * ∫ x in Ioi (xiStar / 2), mainIntegrand x‖ ≤ (C₁ + C₂) * M / (c' ^ 2 * √(1 + v))
  calc ‖((∫ t in Ioc 0 t₀, F t) + ∫ x in Ioi (xiStar / 2), (φ' x : ℂ) • F (φ x)) -
          pref * ∫ x in Ioi (xiStar / 2), mainIntegrand x‖
      = ‖(∫ t in Ioc 0 t₀, F t) +
          (∫ x in Ioi (xiStar / 2), (φ' x : ℂ) • F (φ x) - pref * ∫ x in Ioi (xiStar / 2), mainIntegrand x)‖ := by
        congr 1; ring
    _ ≤ ‖∫ t in Ioc 0 t₀, F t‖ +
          ‖∫ x in Ioi (xiStar / 2), (φ' x : ℂ) • F (φ x) - pref * ∫ x in Ioi (xiStar / 2), mainIntegrand x‖ :=
        norm_add_le _ _
    _ ≤ C₂ * M / (c' ^ 2 * √(1 + v)) + C₁ * M / (c' ^ 2 * √(1 + v)) :=
        add_le_add hhead_bd htail_diff
    _ = (C₁ + C₂) * M / (c' ^ 2 * √(1 + v)) := by ring

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.besselI0C_strip_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.besselI0C_strip_decay

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.besselI0C_two_term_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.besselI0C_two_term_sharp

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.besselV_three_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.besselV_three_term

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.edge_hankel_two_virasoro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.edge_hankel_two_virasoro


