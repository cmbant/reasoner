/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWg1Win
public import FormalResearch.SignUncertainty.UctMcSmall
public import FormalResearch.SignUncertainty.CtOuterTaylor
public import FormalResearch.SignUncertainty.FctPhysicalBudgetConcrete

/-!
# Intermediate-band expansion `(fct:hg1-mid)` for `ctWg1`

Proves `ctWg1_mid_bound`: for `ε = ±1`, `1 ≤ Sw`, `c ≥ c₀(Sw)`, `Sw ≤ hbS c ξ`, and `L = log(π² ξ) ≤ 3 * physDelta c`:

  `|normDensity (ctWg1 ε c) c ξ - (ceK / ceCs) * ceG1 (airyZero 1) (-ceBeta1 * hbS c ξ + ceBeta1 * (deriv (outerTheta ε) 0 / π²) * liftEps c)| ≤ C * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ))`.

Proof: rescale `τ = ς u` (`ς = c^{-1/3}`) in `wg1PartA_normDensity`, compare directly against `airy_reference_identity`
on `Re w = 0` (`liftSymbol_zero_order`), split at `V₀ = max (5 √(12 S)) (c^{1/12})` and `V₁ = c^{1/6}`:
* `|u| ≥ V₁`: tail decay `wg1YA u = O((1 + |u|)^{-9/2})` gives `O(c^{-7/12})`.
* `|u| ≤ V₀`: phase difference `O(c^{-2/3} (|u|³ + |u|⁵))` (`ceHth_le_of_le_one`, `outerTheta_taylor`) and amplitude
  difference `O(c^{-2/3} (|u| + u²))` (`mc_small`) integrate against `(1 + |u|)^{-9/2}` to `O(c^{-13/24} + c^{-1/6} L^{3/4})`.
* `V₀ ≤ |u| ≤ V₁`: finite-interval 1-step IBP on exact and reference separately using `hankelEdgeM_ge_sq_tenth` and
  `wg1YA_cuspProfile` gives `O(V₀^{-13/2} + ς V₀^{-11/2}) = O(c^{-13/24})`.
Finally `wg1PartB` is `O(c^{-2/3})` by `ctWg1_partB_bound`.

Class: proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter FormalResearch.SignUncertainty.FctSym
open FormalResearch.SignUncertainty.FctCuspEdge FormalResearch.Asymptotics

namespace FormalResearch.SignUncertainty

/-! ### Helper bounds for `wg1YA`, `ceHth`, `exp(i x)`, and finite-interval IBP -/

private lemma ctTg1_eq_seedT_sub {w : ℂ} (hw : 0 ≤ w.re) :
    ctTg1 w = seedT 0 w - seedT 1 w := by
  rw [seedT_eq_text 0 hw, seedT_eq_text 1 hw]
  unfold seedText ctTg1
  rw [uctG1Ext_eq hw]
  simp

private lemma wg1YA_continuous : Continuous wg1YA := by
  have hy : wg1YA = fun u : ℝ => seedT 0 (((ceCs * u : ℝ) : ℂ) * Complex.I) -
      seedT 1 (((ceCs * u : ℝ) : ℂ) * Complex.I) := by
    funext u
    unfold wg1YA
    exact ctTg1_eq_seedT_sub (by simp)
  rw [hy]
  have hline : Continuous (fun u : ℝ => ((ceCs * u : ℝ) : ℂ) * Complex.I) := by fun_prop
  have hmem : ∀ u : ℝ, ((ceCs * u : ℝ) : ℂ) * Complex.I ∈ {w : ℂ | 0 ≤ w.re} := fun u => by simp
  exact ((seedT_continuousOn 0).comp_continuous hline hmem).sub
    ((seedT_continuousOn 1).comp_continuous hline hmem)

private lemma wg1YA_unif_and_deriv :
    ∃ C_Y : ℝ, 0 < C_Y ∧
      (∀ u : ℝ, ‖wg1YA u‖ ≤ C_Y * (1 + |u|) ^ (-(9 / 2 : ℝ))) ∧
      (∀ u : ℝ, 1 ≤ |u| → ‖deriv wg1YA u‖ ≤ C_Y * |u| ^ (-(11 / 2 : ℝ))) ∧
      (∀ u : ℝ, u ≠ 0 → HasDerivAt wg1YA (deriv wg1YA u) u) ∧
      ContinuousOn (deriv wg1YA) ({0}ᶜ) := by
  obtain ⟨CY, hCY0, hYA⟩ := wg1YA_cuspProfile
  obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (wg1YA_continuous.continuousOn : ContinuousOn wg1YA (Icc (-1) 1))
  have hM0_pos : 0 ≤ max M0 0 := le_max_right _ _
  refine ⟨max (CY + 1) (max M0 0) * 32, by positivity, ?_, ?_, ?_, ?_⟩
  · intro u
    have h2 : (2 : ℝ) ^ (9 / 2 : ℝ) ≤ 32 := by
      have h1 : (2 : ℝ) ^ (9 / 2 : ℝ) ≤ (2 : ℝ) ^ (5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      exact h1.trans (by norm_num)
    have h2n : (2 : ℝ) ^ (9 / 2 : ℝ) * (2 : ℝ) ^ (-(9 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; norm_num
    by_cases hu : 1 ≤ |u|
    · have hfar := hYA.far_bound 0 (by norm_num) u hu
      simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero, show -(2 * (3 / 2 : ℝ) + 3 / 2) = -(9 / 2 : ℝ) by norm_num] at hfar
      have h1u : 1 + |u| ≤ 2 * |u| := by linarith
      have hrp : |u| ^ (-(9 / 2 : ℝ)) ≤ 32 * (1 + |u|) ^ (-(9 / 2 : ℝ)) := by
        have hpos : 0 < |u| := by linarith
        have hinv : (2 * |u|) ^ (-(9 / 2 : ℝ)) ≤ (1 + |u|) ^ (-(9 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h1u (by norm_num)
        rw [Real.mul_rpow (by positivity) hpos.le] at hinv
        calc |u| ^ (-(9 / 2 : ℝ))
            = (2 : ℝ) ^ (9 / 2 : ℝ) * ((2 : ℝ) ^ (-(9 / 2 : ℝ)) * |u| ^ (-(9 / 2 : ℝ))) := by
                rw [← mul_assoc, h2n, one_mul]
          _ ≤ 32 * (1 + |u|) ^ (-(9 / 2 : ℝ)) :=
                mul_le_mul h2 hinv (by positivity) (by norm_num)
      calc ‖wg1YA u‖ ≤ CY * |u| ^ (-(9 / 2 : ℝ)) := hfar
        _ ≤ max (CY + 1) (max M0 0) * (32 * (1 + |u|) ^ (-(9 / 2 : ℝ))) :=
              mul_le_mul (le_max_of_le_left (by linarith)) hrp (by positivity) (by positivity)
        _ = _ := by ring
    · push Not at hu
      have humem : u ∈ Icc (-1 : ℝ) 1 := abs_le.mp hu.le
      have hbd : ‖wg1YA u‖ ≤ max M0 0 := (hM0 u humem).trans (le_max_left _ _)
      have h1u : 1 + |u| ≤ 2 := by linarith
      have hrp : (1 : ℝ) ≤ 32 * (1 + |u|) ^ (-(9 / 2 : ℝ)) := by
        have hinv : (2 : ℝ) ^ (-(9 / 2 : ℝ)) ≤ (1 + |u|) ^ (-(9 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h1u (by norm_num)
        calc (1 : ℝ) = (2 : ℝ) ^ (9 / 2 : ℝ) * (2 : ℝ) ^ (-(9 / 2 : ℝ)) := h2n.symm
          _ ≤ 32 * (1 + |u|) ^ (-(9 / 2 : ℝ)) :=
                mul_le_mul h2 hinv (by positivity) (by norm_num)
      calc ‖wg1YA u‖ ≤ max M0 0 * 1 := by linarith
        _ ≤ max (CY + 1) (max M0 0) * (32 * (1 + |u|) ^ (-(9 / 2 : ℝ))) :=
              mul_le_mul (le_max_right _ _) hrp (by positivity) (by positivity)
        _ = _ := by ring
  · intro u hu
    have hfar := hYA.far_bound 1 (by norm_num) u hu
    rw [iteratedDeriv_one] at hfar
    have hexp : -(2 * (3 / 2 : ℝ) + 3 / 2) - ((1 : ℕ) : ℝ) = -(11 / 2 : ℝ) := by norm_num
    rw [hexp] at hfar
    refine hfar.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hcy : CY ≤ max (CY + 1) (max M0 0) := le_max_of_le_left (by linarith)
    nlinarith
  · intro u hu
    have hcd : ContDiffOn ℝ 3 wg1YA ({0}ᶜ) := hYA.contDiffOn_Y
    exact ((hcd.differentiableOn (by norm_num)).differentiableAt (isOpen_ne.mem_nhds hu)).hasDerivAt
  · have hcd : ContDiffOn ℝ 3 wg1YA ({0}ᶜ) := hYA.contDiffOn_Y
    exact (hcd.continuousOn_derivWithin isOpen_ne.uniqueDiffOn (by norm_num)).congr
      fun u hu => (derivWithin_of_isOpen isOpen_ne hu).symm

private lemma norm_cexp_I_sub_le (x y : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ))‖ ≤ |x - y| := by
  let f : ℝ → ℂ := fun t => Complex.exp (Complex.I * (t : ℂ))
  have hderiv : ∀ t : ℝ, HasDerivAt f (Complex.I * f t) t := fun t => by
    have hlin : HasDerivAt (fun s : ℝ => Complex.I * (s : ℂ)) Complex.I t := by
      simpa using Complex.ofRealCLM.hasDerivAt (x := t) |>.const_mul Complex.I
    simpa [f, mul_comm] using hlin.cexp
  have hbound : ∀ t ∈ (univ : Set ℝ), ‖deriv f t‖ ≤ 1 := fun t _ => by
    rw [(hderiv t).deriv, norm_mul, Complex.norm_I, one_mul,
      show f t = Complex.exp ((t : ℂ) * Complex.I) by dsimp only [f]; ring_nf,
      Complex.norm_exp_ofReal_mul_I]
  have hmvt := convex_univ.norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (hderiv t).differentiableAt) hbound (mem_univ y) (mem_univ x)
  simpa [f, Real.norm_eq_abs] using hmvt

private lemma ceHth_even (x : ℝ) : ceHth (-x) = ceHth x := by
  unfold ceHth
  rw [Real.tanh_neg, neg_div_neg_eq, neg_sq]

private lemma c_edgePhi_sub_cubic_bound {c L ς u : ℝ} (hc0 : 0 < c) (hς0 : 0 < ς)
    (hcube : c * ς ^ 3 = 1) (hς_eq : ς ^ 2 = c ^ (-(2 / 3 : ℝ)))
    (hS : L = Real.pi ^ 2 * ς ^ 2 * S) (hV : |ς * u| ≤ 1 / 2) :
    |c * edgePhi L (ς * u) - (Real.pi ^ 2 * S * u - Real.pi ^ 2 / 36 * u ^ 3)| ≤
      (Real.pi ^ 4 / 600) * c ^ (-(2 / 3 : ℝ)) * |u| ^ 5 := by
  rw [edgePhi_eq_cubic_add_ceHth]
  have hlin : c * (L * (ς * u) - Real.pi ^ 2 / 36 * (ς * u) ^ 3) = Real.pi ^ 2 * S * u - Real.pi ^ 2 / 36 * u ^ 3 := by
    rw [hS]
    calc c * (Real.pi ^ 2 * ς ^ 2 * S * (ς * u) - Real.pi ^ 2 / 36 * (ς * u) ^ 3)
        = (c * ς ^ 3) * (Real.pi ^ 2 * S * u - Real.pi ^ 2 / 36 * u ^ 3) := by ring
      _ = Real.pi ^ 2 * S * u - Real.pi ^ 2 / 36 * u ^ 3 := by rw [hcube, one_mul]
  have heq : c * (L * (ς * u) - Real.pi ^ 2 / 36 * (ς * u) ^ 3 + ∫ t in (0 : ℝ)..(ς * u), ceHth (Real.pi * t / 2)) -
      (Real.pi ^ 2 * S * u - Real.pi ^ 2 / 36 * u ^ 3) =
      c * ∫ t in (0 : ℝ)..(ς * u), ceHth (Real.pi * t / 2) := by rw [mul_add, hlin]; ring
  rw [heq, abs_mul, abs_of_pos hc0]
  have hpi2 : Real.pi / 2 ≤ 2 := by linarith [Real.pi_lt_four]
  have hint : |∫ t in (0 : ℝ)..(ς * u), ceHth (Real.pi * t / 2)| ≤ (Real.pi ^ 4 / 600) * |ς * u| ^ 5 := by
    have hpt : ∀ t ∈ uIcc (0 : ℝ) (ς * u), |ceHth (Real.pi * t / 2)| ≤ (Real.pi ^ 4 / 120) * |t| ^ 4 := by
      intro t ht
      have ht_le : |t| ≤ |ς * u| := by
        rcases le_or_gt 0 (ς * u) with h0 | h0
        · rw [uIcc_of_le h0] at ht
          rw [abs_of_nonneg ht.1, abs_of_nonneg h0]; exact ht.2
        · rw [uIcc_of_ge h0.le] at ht
          rw [abs_of_nonpos ht.2, abs_of_neg h0]; linarith [ht.1]
      have hx_le : Real.pi * |t| / 2 ≤ 1 := by
        calc Real.pi * |t| / 2 ≤ Real.pi * |ς * u| / 2 := by gcongr
          _ ≤ Real.pi * (1 / 2) / 2 := by gcongr
          _ ≤ 1 := by linarith [Real.pi_lt_four]
      by_cases ht0 : t = 0
      · subst ht0; unfold ceHth; simp
      · have hx0 : 0 < Real.pi * |t| / 2 := mul_pos (div_pos (mul_pos Real.pi_pos (abs_pos.mpr ht0)) two_pos) one_pos |>.trans_eq (by ring)
        have hpos : 0 < ceHth (Real.pi * |t| / 2) := ceHth_pos hx0
        have hle := ceHth_le_of_le_one hx0 hx_le
        have habs : ceHth (Real.pi * t / 2) = ceHth (Real.pi * |t| / 2) := by
          rcases le_or_gt 0 t with h | h
          · rw [abs_of_nonneg h]
          · rw [abs_of_neg h, show Real.pi * -t / 2 = -(Real.pi * t / 2) by ring, ceHth_even]
        rw [habs, abs_of_pos hpos]
        exact hle.trans_eq (by ring)
    have hpow4 : ∫ t in (0 : ℝ)..|ς * u|, (Real.pi ^ 4 / 120) * t ^ 4 = (Real.pi ^ 4 / 600) * |ς * u| ^ 5 := by
      rw [intervalIntegral.integral_const_mul, integral_pow]; ring
    have hi_g : IntervalIntegrable (fun t : ℝ => (Real.pi ^ 4 / 120) * t ^ 4) volume 0 |ς * u| :=
      ((continuous_const.mul (continuous_pow 4)).intervalIntegrable 0 |ς * u|)
    rcases le_or_gt 0 (ς * u) with h0 | h0
    · have hi_g0 : IntervalIntegrable (fun t : ℝ => (Real.pi ^ 4 / 120) * t ^ 4) volume 0 (ς * u) :=
        ((continuous_const.mul (continuous_pow 4)).intervalIntegrable 0 (ς * u))
      have h1 := intervalIntegral.norm_integral_le_of_norm_le h0
        (ae_of_all _ fun t ht => by
          have ht' := hpt t (by rw [uIcc_of_le h0]; exact ⟨ht.1.le, ht.2⟩)
          rw [abs_of_nonneg ht.1.le] at ht'
          exact (Real.norm_eq_abs _).le.trans ht')
        hi_g0
      have hcalc : ∫ t in (0 : ℝ)..(ς * u), (Real.pi ^ 4 / 120) * t ^ 4 = (Real.pi ^ 4 / 600) * |ς * u| ^ 5 := by
        rw [intervalIntegral.integral_const_mul, integral_pow, abs_of_nonneg h0]; ring
      rw [Real.norm_eq_abs] at h1
      exact h1.trans_eq hcalc
    · rw [intervalIntegral.integral_symm, abs_neg]
      have hneg : 0 ≤ -(ς * u) := by linarith
      have hi_g' : IntervalIntegrable (fun t : ℝ => (Real.pi ^ 4 / 120) * t ^ 4) volume (ς * u) 0 :=
        ((continuous_const.mul (continuous_pow 4)).intervalIntegrable (ς * u) 0)
      have h1 := intervalIntegral.norm_integral_le_of_norm_le h0.le
        (ae_of_all _ fun t ht => by
          have ht' := hpt t (by rw [uIcc_of_ge h0.le]; exact ⟨ht.1.le, ht.2⟩)
          have h4 : |t| ^ 4 = t ^ 4 := by
            calc |t| ^ 4 = (|t| ^ 2) ^ 2 := by ring
              _ = (t ^ 2) ^ 2 := by rw [sq_abs]
              _ = t ^ 4 := by ring
          exact (Real.norm_eq_abs _).le.trans (ht'.trans_eq (by rw [h4])))
        hi_g'
      have hcalc : ∫ t in (ς * u)..(0 : ℝ), (Real.pi ^ 4 / 120) * t ^ 4 = (Real.pi ^ 4 / 600) * |ς * u| ^ 5 := by
        rw [intervalIntegral.integral_const_mul, integral_pow, abs_of_neg h0]; ring
      rw [Real.norm_eq_abs, hcalc] at h1
      exact h1
  calc c * |∫ t in (0 : ℝ)..(ς * u), ceHth (Real.pi * t / 2)|
      ≤ c * ((Real.pi ^ 4 / 600) * |ς * u| ^ 5) := mul_le_mul_of_nonneg_left hint hc0.le
    _ = (Real.pi ^ 4 / 600) * (c * ς ^ 3) * ς ^ 2 * |u| ^ 5 := by
        rw [abs_mul, abs_of_pos hς0, mul_pow]; ring
    _ = (Real.pi ^ 4 / 600) * c ^ (-(2 / 3 : ℝ)) * |u| ^ 5 := by
        rw [hcube, mul_one, hς_eq]

private lemma ibp_osc_interval {a b κ K₂ G₀ G₁ G₂ ς : ℝ} (ha1 : 1 ≤ a) (hab : a ≤ b)
    (hκ : 0 < κ) (hK₂ : 0 ≤ K₂) (hG₀ : 0 ≤ G₀) (hG₁ : 0 ≤ G₁) (hG₂ : 0 ≤ G₂) (hς : 0 ≤ ς)
    {φ φ' φ'' : ℝ → ℝ} {g g' : ℝ → ℂ}
    (hφ : ∀ u ∈ Icc a b, HasDerivAt φ (φ' u) u)
    (hφ' : ∀ u ∈ Icc a b, HasDerivAt φ' (φ'' u) u)
    (hφ'_cont : ContinuousOn φ' (Icc a b))
    (hφ''_cont : ContinuousOn φ'' (Icc a b))
    (hφ'_lb : ∀ u ∈ Icc a b, κ * u ^ 2 ≤ |φ' u|)
    (hφ''_ub : ∀ u ∈ Icc a b, |φ'' u| ≤ K₂ * u)
    (hg : ∀ u ∈ Icc a b, HasDerivAt g (g' u) u)
    (hg'_cont : ContinuousOn g' (Icc a b))
    (hg_ub : ∀ u ∈ Icc a b, ‖g u‖ ≤ G₀ * u ^ (-(9 / 2 : ℝ)))
    (hg'_ub : ∀ u ∈ Icc a b, ‖g' u‖ ≤ G₁ * u ^ (-(11 / 2 : ℝ)) + G₂ * ς * u ^ (-(9 / 2 : ℝ))) :
    ‖∫ u in a..b, Complex.exp (Complex.I * (φ u : ℂ)) * g u‖ ≤
      (2 * G₀ / κ + (2 / 13) * (G₁ / κ + G₀ * K₂ / κ ^ 2)) * a ^ (-(13 / 2 : ℝ)) +
      (2 / 11) * (G₂ / κ) * ς * a ^ (-(11 / 2 : ℝ)) := by
  let H : ℝ → ℂ := fun u => Complex.exp (Complex.I * (φ u : ℂ))
  let H' : ℝ → ℂ := fun u => Complex.I * (φ' u : ℂ) * H u
  let Q : ℝ → ℂ := fun u => g u / (Complex.I * (φ' u : ℂ))
  let Q' : ℝ → ℂ := fun u =>
    g' u / (Complex.I * (φ' u : ℂ)) - g u * (φ'' u : ℂ) / (Complex.I * (φ' u : ℂ) ^ 2)
  have hφ'_ne : ∀ u ∈ Icc a b, φ' u ≠ 0 := fun u hu => by
    have hlb := hφ'_lb u hu
    have hu0 : 0 < u := by linarith [ha1, hu.1]
    exact abs_pos.mp (lt_of_lt_of_le (by positivity) hlb)
  have hH_deriv : ∀ u ∈ uIcc a b, HasDerivAt H (H' u) u := fun u hu => by
    rw [uIcc_of_le hab] at hu
    have h1 := ((hφ u hu).ofReal_comp.const_mul Complex.I).cexp
    simpa [H, H', mul_comm (H u)] using h1
  have hQ_deriv : ∀ u ∈ uIcc a b, HasDerivAt Q (Q' u) u := fun u hu => by
    rw [uIcc_of_le hab] at hu
    have hden : Complex.I * (φ' u : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (hφ'_ne u hu))
    have hd1 := hg u hu
    have hd2 := (hφ' u hu).ofReal_comp.const_mul Complex.I
    refine (hd1.div hd2 hden).congr_deriv ?_
    dsimp only [Q']
    field_simp [hden, Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr (hφ'_ne u hu)]
  have hH'_cont : ContinuousOn H' (uIcc a b) := by
    rw [uIcc_of_le hab]
    have hφc : ContinuousOn φ (Icc a b) := fun u hu => (hφ u hu).continuousAt.continuousWithinAt
    exact (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφ'_cont)).mul
      (Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφc)))
  have hQ'_cont : ContinuousOn Q' (uIcc a b) := by
    rw [uIcc_of_le hab]
    have hg_cont : ContinuousOn g (Icc a b) := fun u hu => (hg u hu).continuousAt.continuousWithinAt
    have h1 : ContinuousOn (fun u => g' u / (Complex.I * (φ' u : ℂ))) (Icc a b) :=
      hg'_cont.div (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφ'_cont))
        fun u hu => mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (hφ'_ne u hu))
    have h2 : ContinuousOn (fun u => g u * (φ'' u : ℂ) / (Complex.I * (φ' u : ℂ) ^ 2)) (Icc a b) :=
      (hg_cont.mul (Complex.continuous_ofReal.comp_continuousOn hφ''_cont)).div
        (continuousOn_const.mul ((Complex.continuous_ofReal.comp_continuousOn hφ'_cont).pow 2))
        fun u hu => mul_ne_zero Complex.I_ne_zero (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (hφ'_ne u hu)))
    exact h1.sub h2
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hH_deriv hQ_deriv
    (hH'_cont.intervalIntegrable) (hQ'_cont.intervalIntegrable)
  have hprod : ∫ u in a..b, H u * g u = ∫ u in a..b, H' u * Q u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hab] at hu
    have hden : Complex.I * (φ' u : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (hφ'_ne u hu))
    dsimp only [H', Q]
    rw [show Complex.I * (φ' u : ℂ) * H u * (g u / (Complex.I * (φ' u : ℂ))) =
        H u * g u * ((Complex.I * (φ' u : ℂ)) / (Complex.I * (φ' u : ℂ))) by ring,
      div_self hden, mul_one]
  have hibp' : ∫ u in a..b, H' u * Q u = H b * Q b - H a * Q a - ∫ u in a..b, H u * Q' u :=
    eq_sub_of_add_eq' (eq_sub_iff_add_eq.mp hibp)
  rw [hprod, hibp']
  have hnorm_H : ∀ u : ℝ, ‖H u‖ = 1 := fun u => by simp [H, Complex.norm_exp]
  have hnorm_Q : ∀ u ∈ Icc a b, ‖Q u‖ ≤ (G₀ / κ) * a ^ (-(13 / 2 : ℝ)) := fun u hu => by
    have hu0 : 0 < u := by linarith [ha1, hu.1]
    have hlb : κ * u ^ 2 ≤ |φ' u| := hφ'_lb u hu
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hnum := hg_ub u hu
    have hrp : u ^ (-(9 / 2 : ℝ)) / u ^ 2 = u ^ (-(13 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_natCast u 2, ← Real.rpow_neg hu0.le, ← Real.rpow_add hu0]; norm_num
    have hdiv : G₀ * u ^ (-(9 / 2 : ℝ)) / (κ * u ^ 2) = (G₀ / κ) * u ^ (-(13 / 2 : ℝ)) := by
      calc G₀ * u ^ (-(9 / 2 : ℝ)) / (κ * u ^ 2) = (G₀ / κ) * (u ^ (-(9 / 2 : ℝ)) / u ^ 2) := by ring
        _ = (G₀ / κ) * u ^ (-(13 / 2 : ℝ)) := by rw [hrp]
    calc ‖g u‖ / |φ' u| ≤ (G₀ * u ^ (-(9 / 2 : ℝ))) / (κ * u ^ 2) := by gcongr
      _ = (G₀ / κ) * u ^ (-(13 / 2 : ℝ)) := hdiv
      _ ≤ (G₀ / κ) * a ^ (-(13 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by linarith) hu.1 (by norm_num)) (div_nonneg hG₀ hκ.le)
  have hQ'_bound : ∀ u ∈ Icc a b, ‖Q' u‖ ≤
      (G₁ / κ + G₀ * K₂ / κ ^ 2) * u ^ (-(15 / 2 : ℝ)) + (G₂ / κ) * ς * u ^ (-(13 / 2 : ℝ)) := fun u hu => by
    have hu0 : 0 < u := by linarith [ha1, hu.1]
    have hlb : κ * u ^ 2 ≤ |φ' u| := hφ'_lb u hu
    have h1 : ‖g' u / (Complex.I * (φ' u : ℂ))‖ ≤
        (G₁ / κ) * u ^ (-(15 / 2 : ℝ)) + (G₂ / κ) * ς * u ^ (-(13 / 2 : ℝ)) := by
      rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have hnum := hg'_ub u hu
      have hd1 : u ^ (-(11 / 2 : ℝ)) / u ^ 2 = u ^ (-(15 / 2 : ℝ)) := by
        rw [div_eq_mul_inv, ← Real.rpow_natCast u 2, ← Real.rpow_neg hu0.le, ← Real.rpow_add hu0]; norm_num
      have hd2 : u ^ (-(9 / 2 : ℝ)) / u ^ 2 = u ^ (-(13 / 2 : ℝ)) := by
        rw [div_eq_mul_inv, ← Real.rpow_natCast u 2, ← Real.rpow_neg hu0.le, ← Real.rpow_add hu0]; norm_num
      calc ‖g' u‖ / |φ' u| ≤ (G₁ * u ^ (-(11 / 2 : ℝ)) + G₂ * ς * u ^ (-(9 / 2 : ℝ))) / (κ * u ^ 2) := by gcongr
        _ = (G₁ / κ) * (u ^ (-(11 / 2 : ℝ)) / u ^ 2) + (G₂ / κ) * ς * (u ^ (-(9 / 2 : ℝ)) / u ^ 2) := by ring
        _ = _ := by rw [hd1, hd2]
    have h2 : ‖g u * (φ'' u : ℂ) / (Complex.I * (φ' u : ℂ) ^ 2)‖ ≤ (G₀ * K₂ / κ ^ 2) * u ^ (-(15 / 2 : ℝ)) := by
      rw [norm_div, norm_mul, norm_mul, Complex.norm_I, one_mul, norm_pow, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      have hsq : (κ * u ^ 2) ^ 2 ≤ |φ' u| ^ 2 := pow_le_pow_left₀ (by positivity) hlb 2
      have hnum := mul_le_mul (hg_ub u hu) (hφ''_ub u hu) (abs_nonneg _) (by positivity)
      have hd : u ^ (-(9 / 2 : ℝ)) * u / (u ^ 2) ^ 2 = u ^ (-(15 / 2 : ℝ)) := by
        have hu4 : (u ^ (4 : ℕ) : ℝ)⁻¹ = u ^ (-(4 : ℝ)) :=
          calc (u ^ (4 : ℕ) : ℝ)⁻¹ = (u ^ ((4 : ℕ) : ℝ))⁻¹ := by rw [Real.rpow_natCast]
            _ = u ^ (-((4 : ℕ) : ℝ)) := (Real.rpow_neg hu0.le 4).symm
            _ = u ^ (-(4 : ℝ)) := by norm_num
        calc u ^ (-(9 / 2 : ℝ)) * u / (u ^ 2) ^ 2
            = u ^ (-(9 / 2 : ℝ)) * u ^ (1 : ℝ) * ((u ^ (4 : ℕ)) : ℝ)⁻¹ := by
                rw [Real.rpow_one]; ring
          _ = u ^ (-(9 / 2 : ℝ)) * u ^ (1 : ℝ) * u ^ (-(4 : ℝ)) := by rw [hu4]
          _ = u ^ (-(15 / 2 : ℝ)) := by
                rw [← Real.rpow_add hu0, ← Real.rpow_add hu0]; norm_num
      calc ‖g u‖ * |φ'' u| / |φ' u| ^ 2
          ≤ (G₀ * u ^ (-(9 / 2 : ℝ)) * (K₂ * u)) / (κ * u ^ 2) ^ 2 := by gcongr
        _ = (G₀ * K₂ / κ ^ 2) * (u ^ (-(9 / 2 : ℝ)) * u / (u ^ 2) ^ 2) := by ring
        _ = _ := by rw [hd]
    calc ‖Q' u‖ ≤ ‖g' u / (Complex.I * (φ' u : ℂ))‖ + ‖g u * (φ'' u : ℂ) / (Complex.I * (φ' u : ℂ) ^ 2)‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hi_bound : ‖∫ u in a..b, H u * Q' u‖ ≤
      ((2 / 13) * (G₁ / κ + G₀ * K₂ / κ ^ 2)) * a ^ (-(13 / 2 : ℝ)) +
      (2 / 11) * (G₂ / κ) * ς * a ^ (-(11 / 2 : ℝ)) := by
    let F : ℝ → ℝ := fun u => (G₁ / κ + G₀ * K₂ / κ ^ 2) * u ^ (-(15 / 2 : ℝ)) + (G₂ / κ) * ς * u ^ (-(13 / 2 : ℝ))
    have hpt : ∀ u ∈ Ioc a b, ‖H u * Q' u‖ ≤ F u := fun u hu => by
      rw [norm_mul, hnorm_H, one_mul]
      exact hQ'_bound u ⟨hu.1.le, hu.2⟩
    have ha0 : (0 : ℝ) ∉ uIcc a b := by rw [uIcc_of_le hab]; exact fun h => by linarith [h.1]
    have hiF1 : IntervalIntegrable (fun u : ℝ => u ^ (-(15 / 2 : ℝ))) volume a b :=
      intervalIntegral.intervalIntegrable_rpow (by right; exact ha0)
    have hiF2 : IntervalIntegrable (fun u : ℝ => u ^ (-(13 / 2 : ℝ))) volume a b :=
      intervalIntegral.intervalIntegrable_rpow (by right; exact ha0)
    have hiF : IntervalIntegrable F volume a b := (hiF1.const_mul _).add (hiF2.const_mul _)
    have hle := intervalIntegral.norm_integral_le_of_norm_le hab (ae_of_all _ hpt) hiF
    have hr1 : ∫ u in a..b, u ^ (-(15 / 2 : ℝ)) ≤ (2 / 13 : ℝ) * a ^ (-(13 / 2 : ℝ)) := by
      rw [integral_rpow (by right; exact ⟨by norm_num, ha0⟩)]
      have hp1 : -(15 / 2 : ℝ) + 1 = -(13 / 2 : ℝ) := by norm_num
      rw [hp1]
      have hb0 : 0 ≤ b ^ (-(13 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
      linarith
    have hr2 : ∫ u in a..b, u ^ (-(13 / 2 : ℝ)) ≤ (2 / 11 : ℝ) * a ^ (-(11 / 2 : ℝ)) := by
      rw [integral_rpow (by right; exact ⟨by norm_num, ha0⟩)]
      have hp1 : -(13 / 2 : ℝ) + 1 = -(11 / 2 : ℝ) := by norm_num
      rw [hp1]
      have hb0 : 0 ≤ b ^ (-(11 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
      linarith
    calc ‖∫ u in a..b, H u * Q' u‖ ≤ ∫ u in a..b, F u := hle
      _ = (G₁ / κ + G₀ * K₂ / κ ^ 2) * (∫ u in a..b, u ^ (-(15 / 2 : ℝ))) +
            (G₂ / κ) * ς * (∫ u in a..b, u ^ (-(13 / 2 : ℝ))) := by
          dsimp only [F]
          rw [intervalIntegral.integral_add (hiF1.const_mul _) (hiF2.const_mul _),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ ≤ (G₁ / κ + G₀ * K₂ / κ ^ 2) * ((2 / 13 : ℝ) * a ^ (-(13 / 2 : ℝ))) +
            (G₂ / κ) * ς * ((2 / 11 : ℝ) * a ^ (-(11 / 2 : ℝ))) := by gcongr
      _ = _ := by ring
  have hb_term := hnorm_Q b ⟨hab, le_rfl⟩
  have ha_term := hnorm_Q a ⟨le_rfl, hab⟩
  have hHb : ‖H b * Q b‖ ≤ (G₀ / κ) * a ^ (-(13 / 2 : ℝ)) := by
    rw [norm_mul, hnorm_H, one_mul]; exact hb_term
  have hHa : ‖H a * Q a‖ ≤ (G₀ / κ) * a ^ (-(13 / 2 : ℝ)) := by
    rw [norm_mul, hnorm_H, one_mul]; exact ha_term
  calc ‖H b * Q b - H a * Q a - ∫ u in a..b, H u * Q' u‖
      ≤ ‖H b * Q b - H a * Q a‖ + ‖∫ u in a..b, H u * Q' u‖ := norm_sub_le _ _
    _ ≤ ‖H b * Q b‖ + ‖H a * Q a‖ + ‖∫ u in a..b, H u * Q' u‖ := add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ (G₀ / κ) * a ^ (-(13 / 2 : ℝ)) + (G₀ / κ) * a ^ (-(13 / 2 : ℝ)) +
          (((2 / 13) * (G₁ / κ + G₀ * K₂ / κ ^ 2)) * a ^ (-(13 / 2 : ℝ)) +
            (2 / 11) * (G₂ / κ) * ς * a ^ (-(11 / 2 : ℝ))) := add_le_add (add_le_add hHb hHa) hi_bound
    _ = _ := by ring

private lemma intervalIntegral_one_add_abs_neg_three_half (V : ℝ) (hV : 0 ≤ V) :
    ∫ u in (-V)..V, (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ 4 := by
  have hi : IntervalIntegrable (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) volume (-V) V :=
    ((continuous_const.add continuous_abs).rpow continuous_const fun u =>
      Or.inl (add_pos_of_pos_of_nonneg one_pos (abs_nonneg u)).ne').intervalIntegrable (-V) V
  have hi1 : IntervalIntegrable (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) volume (-V) 0 :=
    hi.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]; intro u hu; exact ⟨hu.1, hu.2.trans hV⟩)
  have hi2 : IntervalIntegrable (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) volume 0 V :=
    hi.mono_set (by rw [uIcc_of_le hV, uIcc_of_le (by linarith)]; intro u hu; exact ⟨by linarith [hu.1], hu.2⟩)
  have heven : ∫ u in (-V)..V, (1 + |u|) ^ (-(3 / 2 : ℝ)) = 2 * ∫ u in (0 : ℝ)..V, (1 + u) ^ (-(3 / 2 : ℝ)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    have hneg : ∫ u in (-V)..(0 : ℝ), (1 + |u|) ^ (-(3 / 2 : ℝ)) = ∫ u in (0 : ℝ)..V, (1 + u) ^ (-(3 / 2 : ℝ)) := by
      have := intervalIntegral.integral_comp_neg (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) (a := (0 : ℝ)) (b := V)
      simp only [neg_zero] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le hV] at hu
      rw [abs_neg, abs_of_nonneg hu.1]
    have hpos : ∫ u in (0 : ℝ)..V, (1 + |u|) ^ (-(3 / 2 : ℝ)) = ∫ u in (0 : ℝ)..V, (1 + u) ^ (-(3 / 2 : ℝ)) := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le hV] at hu
      rw [abs_of_nonneg hu.1]
    rw [hneg, hpos]; ring
  have h0V : ∫ u in (0 : ℝ)..V, (1 + u) ^ (-(3 / 2 : ℝ)) ≤ 2 := by
    have htr := intervalIntegral.integral_comp_add_right (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) (a := (0 : ℝ)) (b := V) 1
    simp only [zero_add] at htr
    have heq : ∫ u in (0 : ℝ)..V, (1 + u) ^ (-(3 / 2 : ℝ)) = ∫ t in (1 : ℝ)..(V + 1), t ^ (-(3 / 2 : ℝ)) := by
      rw [← htr]; refine intervalIntegral.integral_congr fun u _ => by ring
    rw [heq, integral_rpow (by right; exact ⟨by norm_num, by rw [uIcc_of_le (by linarith)]; exact fun h => by linarith [h.1]⟩)]
    rw [show -(3 / 2 : ℝ) + 1 = -(1 / 2 : ℝ) by norm_num, Real.one_rpow]
    have hnn : 0 ≤ (V + 1) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
    linarith
  linarith

private lemma intervalIntegral_abs_half (V : ℝ) (hV : 0 ≤ V) :
    ∫ u in (-V)..V, |u| ^ (1 / 2 : ℝ) = (4 / 3 : ℝ) * V ^ (3 / 2 : ℝ) := by
  have hi : IntervalIntegrable (fun u : ℝ => |u| ^ (1 / 2 : ℝ)) volume (-V) V :=
    (continuous_abs.rpow continuous_const fun _ => Or.inr (by norm_num)).intervalIntegrable (-V) V
  have hi1 : IntervalIntegrable (fun u : ℝ => |u| ^ (1 / 2 : ℝ)) volume (-V) 0 :=
    hi.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]; intro u hu; exact ⟨hu.1, hu.2.trans hV⟩)
  have hi2 : IntervalIntegrable (fun u : ℝ => |u| ^ (1 / 2 : ℝ)) volume 0 V :=
    hi.mono_set (by rw [uIcc_of_le hV, uIcc_of_le (by linarith)]; intro u hu; exact ⟨by linarith [hu.1], hu.2⟩)
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hneg : ∫ u in (-V)..(0 : ℝ), |u| ^ (1 / 2 : ℝ) = ∫ u in (0 : ℝ)..V, u ^ (1 / 2 : ℝ) := by
    have := intervalIntegral.integral_comp_neg (fun u : ℝ => |u| ^ (1 / 2 : ℝ)) (a := (0 : ℝ)) (b := V)
    simp only [neg_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hV] at hu
    rw [abs_neg, abs_of_nonneg hu.1]
  have hpos : ∫ u in (0 : ℝ)..V, |u| ^ (1 / 2 : ℝ) = ∫ u in (0 : ℝ)..V, u ^ (1 / 2 : ℝ) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hV] at hu
    rw [abs_of_nonneg hu.1]
  rw [hneg, hpos, integral_rpow (by left; norm_num), Real.zero_rpow (by norm_num)]
  norm_num; ring

private lemma mid_tail_bd {CA CY V₁ C_tail c : ℝ} (hV₁0 : 0 < V₁)
    (hV₁_pow : V₁ ^ (-(7 / 2 : ℝ)) = c ^ (-(7 / 12 : ℝ)))
    (hC_tail : C_tail = 2 * (CA + 1) * CY * (2 / 7))
    {D : ℝ → ℂ} (hiD : Integrable D)
    (hD_far : ∀ u : ℝ, V₁ ≤ |u| → ‖D u‖ ≤ (CA + 1) * CY * |u| ^ (-(9 / 2 : ℝ))) :
    ‖∫ u in (Ioc (-V₁) V₁)ᶜ, D u‖ ≤ C_tail * c ^ (-(7 / 12 : ℝ)) := by
  have hS₁c : (Ioc (-V₁) V₁)ᶜ = Iic (-V₁) ∪ Ioi V₁ := by
    ext u; simp only [mem_compl_iff, mem_Ioc, not_and, not_le, mem_union, mem_Iic, mem_Ioi]
    constructor
    · intro h; rcases le_or_gt u (-V₁) with hu | hu; exact Or.inl hu; exact Or.inr (h hu)
    · rintro (hu | hu) h1; linarith only [hu, h1]; exact hu
  have hi_Ioi : IntegrableOn (fun u : ℝ => u ^ (-(9 / 2 : ℝ))) (Ioi V₁) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hV₁0
  have hval_Ioi : ∫ u in Ioi V₁, u ^ (-(9 / 2 : ℝ)) = (2 / 7 : ℝ) * V₁ ^ (-(7 / 2 : ℝ)) := by
    have hi1 := integral_Ioi_rpow_of_lt (by norm_num : -(9 / 2 : ℝ) < -1) hV₁0
    rw [hi1, show -(9 / 2 : ℝ) + 1 = -(7 / 2 : ℝ) by norm_num]; ring
  have hdisj : Disjoint (Iic (-V₁)) (Ioi V₁) :=
    Set.disjoint_iff.mpr fun u hu => by linarith only [mem_Iic.mp hu.1, mem_Ioi.mp hu.2, hV₁0]
  have h1' : IntegrableOn (fun u : ℝ => (CA + 1) * CY * |u| ^ (-(9 / 2 : ℝ))) (Ioi V₁) := by
    have h1m : IntegrableOn (fun u : ℝ => (CA + 1) * CY * u ^ (-(9 / 2 : ℝ))) (Ioi V₁) :=
      hi_Ioi.const_mul ((CA + 1) * CY)
    refine h1m.congr_fun ?_ measurableSet_Ioi
    intro u hu; dsimp only; rw [abs_of_pos (by linarith only [mem_Ioi.mp hu, hV₁0])]
  have h2' : IntegrableOn (fun u : ℝ => (CA + 1) * CY * |u| ^ (-(9 / 2 : ℝ))) (Iic (-V₁)) := by
    have hIci : IntegrableOn (fun u : ℝ => u ^ (-(9 / 2 : ℝ))) (Ici V₁) :=
      hi_Ioi.congr_set_ae Ioi_ae_eq_Ici.symm
    have h2 : IntegrableOn (fun u : ℝ => (-u) ^ (-(9 / 2 : ℝ))) (Iic (-V₁)) := by
      have heq_m : (Iic (-V₁)).indicator (fun u : ℝ => (-u) ^ (-(9 / 2 : ℝ))) =
          fun u => (Ici V₁).indicator (fun s => s ^ (-(9 / 2 : ℝ))) (-u) := by
        ext u; by_cases h : u ≤ -V₁
        · simp [h, show V₁ ≤ -u by linarith only [h]]
        · simp [h, show ¬ (V₁ ≤ -u) by linarith only [h]]
      rw [← integrable_indicator_iff measurableSet_Iic, heq_m]
      exact (integrable_indicator_iff measurableSet_Ici).mpr hIci |>.comp_neg
    have h2m : IntegrableOn (fun u : ℝ => (CA + 1) * CY * (-u) ^ (-(9 / 2 : ℝ))) (Iic (-V₁)) :=
      h2.const_mul ((CA + 1) * CY)
    refine h2m.congr_fun ?_ measurableSet_Iic
    intro u hu; dsimp only; rw [abs_of_neg (by linarith only [mem_Iic.mp hu, hV₁0])]
  have hi_tail : IntegrableOn (fun u : ℝ => (CA + 1) * CY * |u| ^ (-(9 / 2 : ℝ))) (Ioc (-V₁) V₁)ᶜ := by
    rw [hS₁c]; exact h2'.union h1'
  have hnorm_set : ‖∫ u in (Ioc (-V₁) V₁)ᶜ, D u‖ ≤ ∫ u in (Ioc (-V₁) V₁)ᶜ, (CA + 1) * CY * |u| ^ (-(9 / 2 : ℝ)) := by
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
    refine MeasureTheory.setIntegral_mono_on hiD.norm.integrableOn hi_tail measurableSet_Ioc.compl fun u hu => ?_
    apply hD_far
    rw [hS₁c] at hu
    rcases hu with hu | hu
    · rw [abs_of_neg (by linarith [mem_Iic.mp hu])]; linarith [mem_Iic.mp hu]
    · rw [abs_of_pos (by linarith [mem_Ioi.mp hu])]; linarith [mem_Ioi.mp hu]
  have hval_c : ∫ u in (Ioc (-V₁) V₁)ᶜ, (CA + 1) * CY * |u| ^ (-(9 / 2 : ℝ)) = C_tail * V₁ ^ (-(7 / 2 : ℝ)) := by
    rw [hS₁c, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi h2' h1']
    have hi_c1 : ∫ u in Ioi V₁, (CA + 1) * CY * |u| ^ (-(9 / 2 : ℝ)) =
        (CA + 1) * CY * ((2 / 7 : ℝ) * V₁ ^ (-(7 / 2 : ℝ))) := by
      rw [← hval_Ioi, ← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
      rw [abs_of_pos (by linarith [mem_Ioi.mp hu])]
    have hi_c2 : ∫ u in Iic (-V₁), (CA + 1) * CY * |u| ^ (-(9 / 2 : ℝ)) =
        (CA + 1) * CY * ((2 / 7 : ℝ) * V₁ ^ (-(7 / 2 : ℝ))) := by
      have hIci_val : ∫ u in Ici V₁, u ^ (-(9 / 2 : ℝ)) = (2 / 7 : ℝ) * V₁ ^ (-(7 / 2 : ℝ)) := by
        rw [MeasureTheory.integral_Ici_eq_integral_Ioi]; exact hval_Ioi
      have hneg : ∫ u in Iic (-V₁), |u| ^ (-(9 / 2 : ℝ)) = ∫ u in Ici V₁, u ^ (-(9 / 2 : ℝ)) := by
        rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Ici,
          ← MeasureTheory.integral_neg_eq_self (fun u => (Ici V₁).indicator (fun s : ℝ => s ^ (-(9 / 2 : ℝ))) u)]
        congr 1; ext u; by_cases h : u ≤ -V₁
        · simp [h, show V₁ ≤ -u by linarith, abs_of_neg (by linarith : u < 0)]
        · simp [h, show ¬ (V₁ ≤ -u) by linarith]
      rw [MeasureTheory.integral_const_mul, hneg, hIci_val]
    rw [hi_c1, hi_c2, hC_tail]; ring
  rw [hval_c, hV₁_pow] at hnorm_set
  exact hnorm_set

private lemma mid_inner_bd {ε c S L ς θ θ3 Cθ Cθ1 Kmc CY V₀ V₁ C_inner : ℝ}
    (hc0 : 0 < c) (hc1 : 1 ≤ c) (hς : 0 < ς) (hς1 : ς ≤ 1) (hcube : c * ς ^ 3 = 1)
    (hς2_eq : ς ^ 2 = c ^ (-(2 / 3 : ℝ))) (hς3_eq : ς ^ 3 = c⁻¹)
    (hL0 : 0 < L) (hL_eq : L = Real.pi ^ 2 * ς ^ 2 * S)
    (hV₀_eq : V₀ = max (5 * Real.sqrt (12 * S)) (c ^ (1 / 12 : ℝ)))
    (hV₀_ge10 : 10 ≤ V₀) (_hV₀_ge_cut : 5 * Real.sqrt (12 * S) ≤ V₀)
    (_hV₀_ge_c112 : c ^ (1 / 12 : ℝ) ≤ V₀) (hV₀_le_V₁ : V₀ ≤ V₁) (hςV₁ : ς * V₁ ≤ 1 / 100)
    (hKmc0 : 0 ≤ Kmc)
    (hMc : ∀ τ : ℝ, |τ| ≤ 1 / 5 → ‖uctMc c 0 τ - 1‖ ≤ Kmc * (c ^ (-(2 / 3 : ℝ)) * |τ| + τ ^ 2))
    (hθ : ∀ τ : ℝ, |τ| ≤ 1 → |outerTheta ε τ - θ * τ - θ3 * τ ^ 3| ≤ Cθ * |τ| ^ 5)
    (hCθ1 : Cθ1 = |θ3| + |Cθ| + 1)
    (hCY0 : 0 < CY) (hYA_unif : ∀ u : ℝ, ‖wg1YA u‖ ≤ CY * (1 + |u|) ^ (-(9 / 2 : ℝ)))
    (hC_inner : C_inner = CY * (4 * (Kmc * 2 + Real.pi ^ 4 / 600 + Cθ1) + (Real.pi ^ 4 / 600) * 43) + 1) :
    ‖∫ u in (-V₀)..V₀,
      (Complex.exp (Complex.I * ((c * edgePhi L (ς * u) : ℝ) : ℂ)) * wg1AmpA ε c (ς * u) * wg1YA u -
       Complex.exp (Complex.I * (((Real.pi ^ 2 * S - θ * ς) * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ)) * wg1YA u)‖ ≤
      C_inner * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ)) := by
  let D : ℝ → ℂ := fun u =>
    Complex.exp (Complex.I * ((c * edgePhi L (ς * u) : ℝ) : ℂ)) * wg1AmpA ε c (ς * u) * wg1YA u -
    Complex.exp (Complex.I * (((Real.pi ^ 2 * S - θ * ς) * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ)) * wg1YA u
  have hV₀0 : 0 ≤ V₀ := by linarith only [hV₀_ge10]
  have hpt : ∀ u ∈ Ioc (-V₀) V₀, ‖D u‖ ≤
      CY * (Kmc * 2 + Real.pi ^ 4 / 600 + Cθ1) * c ^ (-(2 / 3 : ℝ)) * (1 + |u|) ^ (-(3 / 2 : ℝ)) +
      CY * (Real.pi ^ 4 / 600) * c ^ (-(2 / 3 : ℝ)) * |u| ^ (1 / 2 : ℝ) := fun u hu => by
    have hu_V₀ : |u| ≤ V₀ := abs_le.mpr ⟨hu.1.le, hu.2⟩
    have hu_V₁ : |u| ≤ V₁ := hu_V₀.trans hV₀_le_V₁
    have hςu : |ς * u| ≤ 1 / 5 := by
      calc |ς * u| = ς * |u| := by rw [abs_mul, abs_of_pos hς]
        _ ≤ ς * V₁ := by gcongr
        _ ≤ 1 / 100 := hςV₁
        _ ≤ 1 / 5 := by norm_num
    have hmc_u : ‖uctMc c 0 (ς * u) - 1‖ ≤ (Kmc * 2) * c ^ (-(2 / 3 : ℝ)) * (1 + |u|) ^ 3 := by
      have hm := hMc (ς * u) hςu
      have h1 : c ^ (-(2 / 3 : ℝ)) * |ς * u| + (ς * u) ^ 2 ≤ c ^ (-(2 / 3 : ℝ)) * (|u| + u ^ 2) := by
        have h1a : |ς * u| ≤ |u| := by
          rw [abs_mul, abs_of_pos hς]; exact mul_le_of_le_one_left (abs_nonneg u) hς1
        have h1b : (ς * u) ^ 2 = c ^ (-(2 / 3 : ℝ)) * u ^ 2 := by rw [mul_pow, hς2_eq]
        nlinarith only [h1a, h1b, Real.rpow_nonneg hc0.le (-(2 / 3 : ℝ))]
      have h2 : |u| + u ^ 2 ≤ 2 * (1 + |u|) ^ 3 := by
        have hsq : |u| ^ 2 = u ^ 2 := sq_abs u
        nlinarith only [hsq, abs_nonneg u, sq_nonneg |u|]
      have hc23_nn : 0 ≤ c ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg hc0.le (-(2 / 3 : ℝ))
      calc ‖uctMc c 0 (ς * u) - 1‖ ≤ Kmc * (c ^ (-(2 / 3 : ℝ)) * |ς * u| + (ς * u) ^ 2) := hm
        _ ≤ Kmc * (c ^ (-(2 / 3 : ℝ)) * (|u| + u ^ 2)) := mul_le_mul_of_nonneg_left h1 hKmc0
        _ ≤ Kmc * (c ^ (-(2 / 3 : ℝ)) * (2 * (1 + |u|) ^ 3)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hc23_nn) hKmc0
        _ = (Kmc * 2) * c ^ (-(2 / 3 : ℝ)) * (1 + |u|) ^ 3 := by ring
    have hph_u : |c * edgePhi L (ς * u) - outerTheta ε (ς * u) -
        ((Real.pi ^ 2 * S - θ * ς) * u - Real.pi ^ 2 / 36 * u ^ 3)| ≤
        (Real.pi ^ 4 / 600) * c ^ (-(2 / 3 : ℝ)) * |u| ^ 5 + Cθ1 * c ^ (-(2 / 3 : ℝ)) * (1 + |u|) ^ 3 := by
      have h1 := c_edgePhi_sub_cubic_bound (S := S) (u := u) hc0 hς hcube hς2_eq hL_eq (by linarith only [hςu])
      have hθ_u : |outerTheta ε (ς * u) - θ * (ς * u)| ≤ Cθ1 * c ^ (-(2 / 3 : ℝ)) * (1 + |u|) ^ 3 := by
        have hτ1 : |ς * u| ≤ 1 := by linarith only [hςu]
        have ht := hθ (ς * u) hτ1
        have h53 : |ς * u| ^ 5 ≤ |ς * u| ^ 3 :=
          pow_le_pow_of_le_one (abs_nonneg _) hτ1 (by norm_num)
        have h3_eq : |ς * u| ^ 3 ≤ c ^ (-(2 / 3 : ℝ)) * (1 + |u|) ^ 3 := by
          rw [abs_mul, abs_of_pos hς, mul_pow, hς3_eq]
          have hc_m : c⁻¹ ≤ c ^ (-(2 / 3 : ℝ)) := by
            rw [← Real.rpow_neg_one c]
            exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
          have hu3 : |u| ^ 3 ≤ (1 + |u|) ^ 3 := pow_le_pow_left₀ (abs_nonneg u) (by linarith only [abs_nonneg u]) 3
          exact mul_le_mul hc_m hu3 (by positivity) (by positivity)
        have hlin : outerTheta ε (ς * u) - θ * (ς * u) =
            (outerTheta ε (ς * u) - θ * (ς * u) - θ3 * (ς * u) ^ 3) + θ3 * (ς * u) ^ 3 := by ring
        calc |outerTheta ε (ς * u) - θ * (ς * u)|
            = |(outerTheta ε (ς * u) - θ * (ς * u) - θ3 * (ς * u) ^ 3) + θ3 * (ς * u) ^ 3| := congrArg abs hlin
          _ ≤ |outerTheta ε (ς * u) - θ * (ς * u) - θ3 * (ς * u) ^ 3| + |θ3 * (ς * u) ^ 3| := abs_add_le _ _
          _ ≤ Cθ * |ς * u| ^ 5 + |θ3| * |ς * u| ^ 3 := by
              rw [abs_mul, show |(ς * u) ^ 3| = |ς * u| ^ 3 by exact abs_pow _ 3]
              gcongr
          _ ≤ |Cθ| * |ς * u| ^ 3 + |θ3| * |ς * u| ^ 3 := by
              have hC5 : Cθ * |ς * u| ^ 5 ≤ |Cθ| * |ς * u| ^ 3 :=
                calc Cθ * |ς * u| ^ 5 ≤ |Cθ| * |ς * u| ^ 5 := mul_le_mul_of_nonneg_right (le_abs_self Cθ) (by positivity)
                  _ ≤ |Cθ| * |ς * u| ^ 3 := mul_le_mul_of_nonneg_left h53 (abs_nonneg _)
              gcongr
          _ = (|Cθ| + |θ3|) * |ς * u| ^ 3 := by ring
          _ ≤ Cθ1 * (c ^ (-(2 / 3 : ℝ)) * (1 + |u|) ^ 3) := by
              refine mul_le_mul (by rw [hCθ1]; linarith only [abs_nonneg θ3, abs_nonneg Cθ]) h3_eq
                (by positivity) (by rw [hCθ1]; positivity)
          _ = _ := by ring
      have htri : c * edgePhi L (ς * u) - outerTheta ε (ς * u) -
          ((Real.pi ^ 2 * S - θ * ς) * u - Real.pi ^ 2 / 36 * u ^ 3) =
          (c * edgePhi L (ς * u) - (Real.pi ^ 2 * S * u - Real.pi ^ 2 / 36 * u ^ 3)) -
          (outerTheta ε (ς * u) - θ * (ς * u)) := by ring
      rw [htri]
      exact (abs_sub _ _).trans (add_le_add h1 hθ_u) |>.trans_eq (by ring)
    have hDu : D u = wg1YA u *
        (Complex.exp (Complex.I * ((c * edgePhi L (ς * u) - outerTheta ε (ς * u) : ℝ) : ℂ)) * (uctMc c 0 (ς * u) - 1) +
          (Complex.exp (Complex.I * ((c * edgePhi L (ς * u) - outerTheta ε (ς * u) : ℝ) : ℂ)) -
            Complex.exp (Complex.I * (((Real.pi ^ 2 * S - θ * ς) * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ)))) := by
      dsimp only [D]; unfold wg1AmpA
      have hexp_mul : Complex.exp (Complex.I * ((c * edgePhi L (ς * u) : ℝ) : ℂ)) *
          Complex.exp (-(Complex.I * (outerTheta ε (ς * u) : ℂ))) =
          Complex.exp (Complex.I * ((c * edgePhi L (ς * u) - outerTheta ε (ς * u) : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      linear_combination (wg1YA u * uctMc c 0 (ς * u)) * hexp_mul
    have hbr : ‖Complex.exp (Complex.I * ((c * edgePhi L (ς * u) - outerTheta ε (ς * u) : ℝ) : ℂ)) * (uctMc c 0 (ς * u) - 1) +
          (Complex.exp (Complex.I * ((c * edgePhi L (ς * u) - outerTheta ε (ς * u) : ℝ) : ℂ)) -
            Complex.exp (Complex.I * (((Real.pi ^ 2 * S - θ * ς) * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ)))‖ ≤
        (Kmc * 2 + Real.pi ^ 4 / 600 + Cθ1) * c ^ (-(2 / 3 : ℝ)) * (1 + |u|) ^ 3 +
        (Real.pi ^ 4 / 600) * c ^ (-(2 / 3 : ℝ)) * |u| ^ 5 := by
      have he1 : ‖Complex.exp (Complex.I * ((c * edgePhi L (ς * u) - outerTheta ε (ς * u) : ℝ) : ℂ))‖ = 1 := by
        rw [show Complex.I * ((c * edgePhi L (ς * u) - outerTheta ε (ς * u) : ℝ) : ℂ) =
          (((c * edgePhi L (ς * u) - outerTheta ε (ς * u) : ℝ) : ℂ) * Complex.I) by ring]
        exact Complex.norm_exp_ofReal_mul_I _
      have hd1 : ‖Complex.exp (Complex.I * ((c * edgePhi L (ς * u) - outerTheta ε (ς * u) : ℝ) : ℂ)) * (uctMc c 0 (ς * u) - 1)‖ ≤
          (Kmc * 2) * c ^ (-(2 / 3 : ℝ)) * (1 + |u|) ^ 3 := by
        rw [norm_mul, he1, one_mul]; exact hmc_u
      have hd2 := (norm_cexp_I_sub_le _ _).trans hph_u
      have hnn1 : 0 ≤ c ^ (-(2 / 3 : ℝ)) * (1 + |u|) ^ 3 := by positivity
      calc ‖_‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
        _ ≤ (Kmc * 2) * c ^ (-(2 / 3 : ℝ)) * (1 + |u|) ^ 3 +
            ((Real.pi ^ 4 / 600) * c ^ (-(2 / 3 : ℝ)) * |u| ^ 5 + Cθ1 * c ^ (-(2 / 3 : ℝ)) * (1 + |u|) ^ 3) := add_le_add hd1 hd2
        _ = (Kmc * 2 + Cθ1) * (c ^ (-(2 / 3 : ℝ)) * (1 + |u|) ^ 3) +
            (Real.pi ^ 4 / 600) * c ^ (-(2 / 3 : ℝ)) * |u| ^ 5 := by ring
        _ ≤ (Kmc * 2 + Real.pi ^ 4 / 600 + Cθ1) * (c ^ (-(2 / 3 : ℝ)) * (1 + |u|) ^ 3) +
            (Real.pi ^ 4 / 600) * c ^ (-(2 / 3 : ℝ)) * |u| ^ 5 := by
              have hk : Kmc * 2 + Cθ1 ≤ Kmc * 2 + Real.pi ^ 4 / 600 + Cθ1 := by
                linarith only [show (0 : ℝ) ≤ Real.pi ^ 4 / 600 by positivity]
              gcongr
        _ = _ := by ring
    have hYA_pow3 : (1 + |u|) ^ (-(9 / 2 : ℝ)) * (1 + |u|) ^ 3 = (1 + |u|) ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast (1 + |u|) 3, ← Real.rpow_add (by positivity)]; norm_num
    have hYA_pow5 : (1 + |u|) ^ (-(9 / 2 : ℝ)) * |u| ^ 5 ≤ |u| ^ (1 / 2 : ℝ) := by
      by_cases hu0 : u = 0
      · subst hu0; simp
      · have hu_pos : 0 < |u| := abs_pos.mpr hu0
        have h1 : (1 + |u|) ^ (-(9 / 2 : ℝ)) ≤ |u| ^ (-(9 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hu_pos (by linarith only) (by norm_num)
        calc (1 + |u|) ^ (-(9 / 2 : ℝ)) * |u| ^ (5 : ℕ)
            ≤ |u| ^ (-(9 / 2 : ℝ)) * |u| ^ (5 : ℕ) := mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = |u| ^ (-(9 / 2 : ℝ)) * |u| ^ (5 : ℝ) := by rw [← Real.rpow_natCast |u| 5]; norm_num
          _ = |u| ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hu_pos]; norm_num
    rw [hDu, norm_mul]
    have hCY_nn : 0 ≤ CY * (1 + |u|) ^ (-(9 / 2 : ℝ)) := mul_nonneg hCY0.le (by positivity)
    calc ‖wg1YA u‖ * ‖_‖
        ≤ (CY * (1 + |u|) ^ (-(9 / 2 : ℝ))) *
            ((Kmc * 2 + Real.pi ^ 4 / 600 + Cθ1) * c ^ (-(2 / 3 : ℝ)) * (1 + |u|) ^ 3 +
              (Real.pi ^ 4 / 600) * c ^ (-(2 / 3 : ℝ)) * |u| ^ 5) :=
          mul_le_mul (hYA_unif u) hbr (norm_nonneg _) hCY_nn
      _ = CY * (Kmc * 2 + Real.pi ^ 4 / 600 + Cθ1) * c ^ (-(2 / 3 : ℝ)) * ((1 + |u|) ^ (-(9 / 2 : ℝ)) * (1 + |u|) ^ 3) +
            CY * (Real.pi ^ 4 / 600) * c ^ (-(2 / 3 : ℝ)) * ((1 + |u|) ^ (-(9 / 2 : ℝ)) * |u| ^ 5) := by ring
      _ ≤ CY * (Kmc * 2 + Real.pi ^ 4 / 600 + Cθ1) * c ^ (-(2 / 3 : ℝ)) * (1 + |u|) ^ (-(3 / 2 : ℝ)) +
            CY * (Real.pi ^ 4 / 600) * c ^ (-(2 / 3 : ℝ)) * |u| ^ (1 / 2 : ℝ) := by
          rw [hYA_pow3]; gcongr
  have hi1 : IntervalIntegrable (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) volume (-V₀) V₀ :=
    ((continuous_const.add continuous_abs).rpow continuous_const fun u =>
      Or.inl (add_pos_of_pos_of_nonneg one_pos (abs_nonneg u)).ne').intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun u : ℝ => |u| ^ (1 / 2 : ℝ)) volume (-V₀) V₀ :=
    (continuous_abs.rpow continuous_const fun _ => Or.inr (by norm_num)).intervalIntegrable _ _
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le (by linarith only [hV₀0]) (ae_of_all _ hpt)
    ((hi1.const_mul _).add (hi2.const_mul _))
  have hint1 := intervalIntegral_one_add_abs_neg_three_half V₀ hV₀0
  have hint2 := intervalIntegral_abs_half V₀ hV₀0
  have hV₀_half : V₀ ^ (3 / 2 : ℝ) ≤ (5 * Real.sqrt (12 * S)) ^ (3 / 2 : ℝ) + (c ^ (1 / 12 : ℝ)) ^ (3 / 2 : ℝ) := by
    rcases le_total (5 * Real.sqrt (12 * S)) (c ^ (1 / 12 : ℝ)) with hle | hle
    · rw [hV₀_eq, max_eq_right hle]
      exact le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
    · rw [hV₀_eq, max_eq_left hle]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)
  have hS34 : (5 * Real.sqrt (12 * S)) ^ (3 / 2 : ℝ) ≤ 32 * c ^ (1 / 2 : ℝ) * L ^ (3 / 4 : ℝ) := by
    have hS_L : 12 * S = (12 / Real.pi ^ 2) * (c ^ (2 / 3 : ℝ) * L) := by
      rw [hL_eq, hς2_eq]
      have hmul : c ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) = 1 := by rw [← Real.rpow_add hc0]; norm_num
      have hpi0 : Real.pi ^ 2 ≠ 0 := (sq_pos_of_pos Real.pi_pos).ne'
      calc 12 * S = (12 / Real.pi ^ 2) * (c ^ (2 / 3 : ℝ) * (Real.pi ^ 2 * c ^ (-(2 / 3 : ℝ)) * S)) := by
            rw [show c ^ (2 / 3 : ℝ) * (Real.pi ^ 2 * c ^ (-(2 / 3 : ℝ)) * S) =
              Real.pi ^ 2 * S * (c ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ))) by ring, hmul, mul_one]
            field_simp [hpi0]
        _ = _ := by ring
    have h12_lt : 12 / Real.pi ^ 2 ≤ 4 / 3 := by
      have hpi9 : 9 ≤ Real.pi ^ 2 := by nlinarith only [Real.pi_gt_three]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith only [hpi9]
    have hsq : 5 * Real.sqrt (12 * S) ≤ 10 * (c ^ (2 / 3 : ℝ) * L) ^ (1 / 2 : ℝ) := by
      rw [hS_L, Real.sqrt_eq_rpow]
      have h1 : ((12 / Real.pi ^ 2) * (c ^ (2 / 3 : ℝ) * L)) ^ (1 / 2 : ℝ) ≤
          (4 / 3 : ℝ) ^ (1 / 2 : ℝ) * (c ^ (2 / 3 : ℝ) * L) ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
        gcongr
      have h2 : (4 / 3 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by norm_num)]; norm_num
      have hr_nn : 0 ≤ (c ^ (2 / 3 : ℝ) * L) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
      calc 5 * ((12 / Real.pi ^ 2) * (c ^ (2 / 3 : ℝ) * L)) ^ (1 / 2 : ℝ)
          ≤ 5 * ((4 / 3 : ℝ) ^ (1 / 2 : ℝ) * (c ^ (2 / 3 : ℝ) * L) ^ (1 / 2 : ℝ)) := by gcongr
        _ ≤ 5 * (2 * (c ^ (2 / 3 : ℝ) * L) ^ (1 / 2 : ℝ)) := by gcongr
        _ = 10 * (c ^ (2 / 3 : ℝ) * L) ^ (1 / 2 : ℝ) := by ring
    have h32 : (5 * Real.sqrt (12 * S)) ^ (3 / 2 : ℝ) ≤ (10 * (c ^ (2 / 3 : ℝ) * L) ^ (1 / 2 : ℝ)) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hsq (by norm_num)
    have h10_lt : (10 : ℝ) ^ (3 / 2 : ℝ) ≤ 32 := by
      have hsq1 : (10 : ℝ) ^ 3 ≤ 32 ^ 2 := by norm_num
      have hr : (10 : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt ((10 : ℝ) ^ 3) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (10 : ℝ) 3, ← Real.rpow_mul (by norm_num)]; norm_num
      rw [hr, Real.sqrt_le_left (by norm_num)]
      exact hsq1
    calc (5 * Real.sqrt (12 * S)) ^ (3 / 2 : ℝ)
        ≤ (10 * (c ^ (2 / 3 : ℝ) * L) ^ (1 / 2 : ℝ)) ^ (3 / 2 : ℝ) := h32
      _ = (10 : ℝ) ^ (3 / 2 : ℝ) * ((c ^ (2 / 3 : ℝ) * L) ^ (1 / 2 : ℝ)) ^ (3 / 2 : ℝ) :=
          Real.mul_rpow (by positivity) (by positivity)
      _ = (10 : ℝ) ^ (3 / 2 : ℝ) * (c ^ (1 / 2 : ℝ) * L ^ (3 / 4 : ℝ)) := by
          rw [← Real.rpow_mul (by positivity), show (1 / 2 : ℝ) * (3 / 2 : ℝ) = 3 / 4 by norm_num,
            Real.mul_rpow (by positivity) hL0.le, ← Real.rpow_mul hc0.le]; norm_num
      _ ≤ 32 * (c ^ (1 / 2 : ℝ) * L ^ (3 / 4 : ℝ)) := by gcongr
      _ = 32 * c ^ (1 / 2 : ℝ) * L ^ (3 / 4 : ℝ) := by ring
  have hc18 : (c ^ (1 / 12 : ℝ)) ^ (3 / 2 : ℝ) = c ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_mul hc0.le]; norm_num
  have hc23_le : c ^ (-(2 / 3 : ℝ)) ≤ c ^ (-(13 / 24 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hc23_18 : c ^ (-(2 / 3 : ℝ)) * c ^ (1 / 8 : ℝ) = c ^ (-(13 / 24 : ℝ)) := by
    rw [← Real.rpow_add hc0]; norm_num
  have hc23_12 : c ^ (-(2 / 3 : ℝ)) * (c ^ (1 / 2 : ℝ) * L ^ (3 / 4 : ℝ)) = c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ) := by
    rw [← mul_assoc, ← Real.rpow_add hc0]; norm_num
  have hV₀_mul : c ^ (-(2 / 3 : ℝ)) * ((4 / 3 : ℝ) * V₀ ^ (3 / 2 : ℝ)) ≤
      43 * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ)) := by
    have hc23_nn : 0 ≤ c ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
    have h1 : V₀ ^ (3 / 2 : ℝ) ≤ 32 * c ^ (1 / 2 : ℝ) * L ^ (3 / 4 : ℝ) + c ^ (1 / 8 : ℝ) := by
      linarith only [hV₀_half, hS34, hc18]
    have hnn1 : 0 ≤ c ^ (1 / 2 : ℝ) * L ^ (3 / 4 : ℝ) := by positivity
    have hnn2 : 0 ≤ c ^ (1 / 8 : ℝ) := by positivity
    calc c ^ (-(2 / 3 : ℝ)) * ((4 / 3 : ℝ) * V₀ ^ (3 / 2 : ℝ))
        ≤ c ^ (-(2 / 3 : ℝ)) * ((4 / 3 : ℝ) * (32 * c ^ (1 / 2 : ℝ) * L ^ (3 / 4 : ℝ) + c ^ (1 / 8 : ℝ))) := by
            gcongr
      _ ≤ c ^ (-(2 / 3 : ℝ)) * (43 * (c ^ (1 / 2 : ℝ) * L ^ (3 / 4 : ℝ)) + 2 * c ^ (1 / 8 : ℝ)) :=
            mul_le_mul_of_nonneg_left (by linarith only [hnn1, hnn2]) hc23_nn
      _ = 43 * (c ^ (-(2 / 3 : ℝ)) * (c ^ (1 / 2 : ℝ) * L ^ (3 / 4 : ℝ))) +
            2 * (c ^ (-(2 / 3 : ℝ)) * c ^ (1 / 8 : ℝ)) := by ring
      _ = 43 * (c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ)) + 2 * c ^ (-(13 / 24 : ℝ)) := by
            rw [hc23_12, hc23_18]
      _ ≤ 43 * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ)) := by
            have hc_nn : 0 ≤ c ^ (-(13 / 24 : ℝ)) := by positivity
            linarith only [hc_nn, hnn1, show (0 : ℝ) ≤ c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ) by positivity]
  have hint_comb : ∫ u in (-V₀)..V₀,
        (CY * (Kmc * 2 + Real.pi ^ 4 / 600 + Cθ1) * c ^ (-(2 / 3 : ℝ)) * (1 + |u|) ^ (-(3 / 2 : ℝ)) +
          CY * (Real.pi ^ 4 / 600) * c ^ (-(2 / 3 : ℝ)) * |u| ^ (1 / 2 : ℝ))
      = CY * (Kmc * 2 + Real.pi ^ 4 / 600 + Cθ1) * c ^ (-(2 / 3 : ℝ)) * (∫ u in (-V₀)..V₀, (1 + |u|) ^ (-(3 / 2 : ℝ))) +
        CY * (Real.pi ^ 4 / 600) * c ^ (-(2 / 3 : ℝ)) * (∫ u in (-V₀)..V₀, |u| ^ (1 / 2 : ℝ)) := by
    rw [intervalIntegral.integral_add (hi1.const_mul _) (hi2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hA_nonneg : 0 ≤ CY * (Kmc * 2 + Real.pi ^ 4 / 600 + Cθ1) := by rw [hCθ1]; positivity
  have hB_nonneg : 0 ≤ CY * (Real.pi ^ 4 / 600) := by positivity
  have hL_nn : 0 ≤ c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ) := by positivity
  have hsum_nn : 0 ≤ c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ) := by positivity
  have hP0 : ‖∫ u in (-V₀)..V₀, D u‖ ≤
      CY * (Kmc * 2 + Real.pi ^ 4 / 600 + Cθ1) * c ^ (-(2 / 3 : ℝ)) * 4 +
        CY * (Real.pi ^ 4 / 600) * (c ^ (-(2 / 3 : ℝ)) * ((4 / 3 : ℝ) * V₀ ^ (3 / 2 : ℝ))) := by
    rw [hint_comb] at hnorm
    have h1' : CY * (Kmc * 2 + Real.pi ^ 4 / 600 + Cθ1) * c ^ (-(2 / 3 : ℝ)) *
        (∫ u in (-V₀)..V₀, (1 + |u|) ^ (-(3 / 2 : ℝ))) ≤
        CY * (Kmc * 2 + Real.pi ^ 4 / 600 + Cθ1) * c ^ (-(2 / 3 : ℝ)) * 4 :=
      mul_le_mul_of_nonneg_left hint1 (mul_nonneg hA_nonneg (Real.rpow_nonneg hc0.le _))
    have h2' : CY * (Real.pi ^ 4 / 600) * c ^ (-(2 / 3 : ℝ)) * (∫ u in (-V₀)..V₀, |u| ^ (1 / 2 : ℝ)) =
        CY * (Real.pi ^ 4 / 600) * (c ^ (-(2 / 3 : ℝ)) * ((4 / 3 : ℝ) * V₀ ^ (3 / 2 : ℝ))) := by
      rw [hint2]; ring
    linarith only [hnorm, h1', h2']
  have hP1 : CY * (Kmc * 2 + Real.pi ^ 4 / 600 + Cθ1) * c ^ (-(2 / 3 : ℝ)) * 4 ≤
      CY * (Kmc * 2 + Real.pi ^ 4 / 600 + Cθ1) * (4 * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ))) := by
    have h1c : c ^ (-(2 / 3 : ℝ)) * 4 ≤ 4 * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ)) := by
      linarith only [hc23_le, hL_nn]
    rw [mul_assoc (CY * (Kmc * 2 + Real.pi ^ 4 / 600 + Cθ1)) (c ^ (-(2 / 3 : ℝ))) 4]
    exact mul_le_mul_of_nonneg_left h1c hA_nonneg
  have hP2 : CY * (Real.pi ^ 4 / 600) * (c ^ (-(2 / 3 : ℝ)) * ((4 / 3 : ℝ) * V₀ ^ (3 / 2 : ℝ))) ≤
      CY * (Real.pi ^ 4 / 600) * (43 * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ))) :=
    mul_le_mul_of_nonneg_left hV₀_mul hB_nonneg
  have heq_ci : CY * (Kmc * 2 + Real.pi ^ 4 / 600 + Cθ1) * 4 + CY * (Real.pi ^ 4 / 600) * 43 ≤ C_inner := by
    rw [hC_inner]; linarith only
  calc ‖∫ u in (-V₀)..V₀, D u‖
      ≤ CY * (Kmc * 2 + Real.pi ^ 4 / 600 + Cθ1) * (4 * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ))) +
          CY * (Real.pi ^ 4 / 600) * (43 * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ))) :=
        hP0.trans (add_le_add hP1 hP2)
    _ = (CY * (Kmc * 2 + Real.pi ^ 4 / 600 + Cθ1) * 4 + CY * (Real.pi ^ 4 / 600) * 43) *
          (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ)) := by ring
    _ ≤ C_inner * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right heq_ci hsum_nn

private lemma mid_ibp_side {ε c S L ς θ CA CY V₀ V₁ κ_ex κ_ref K2 C_ibp_ex C_ibp_ref s : ℝ}
    (hs : s = 1 ∨ s = -1) (hc0 : 0 < c) (hc1 : 1 ≤ c) (hς : 0 < ς) (hcube : c * ς ^ 3 = 1)
    (hς_eq : ς = c ^ (-(1 / 3 : ℝ))) (hS0 : 0 < S) (hL_eq : L = Real.pi ^ 2 * ς ^ 2 * S)
    (hV₀_ge10 : 10 ≤ V₀) (hV₀_ge_cut : 5 * Real.sqrt (12 * S) ≤ V₀)
    (hV₀_ge_c112 : c ^ (1 / 12 : ℝ) ≤ V₀) (hV₀_le_V₁ : V₀ ≤ V₁) (hςV₁ : ς * V₁ ≤ 1 / 100)
    (hθς : |θ * ς| ≤ 1) (hCA0 : 0 ≤ CA) (hCY0 : 0 < CY)
    (hYA_unif : ∀ u : ℝ, ‖wg1YA u‖ ≤ CY * (1 + |u|) ^ (-(9 / 2 : ℝ)))
    (hYA_deriv : ∀ u : ℝ, 1 ≤ |u| → ‖deriv wg1YA u‖ ≤ CY * |u| ^ (-(11 / 2 : ℝ)))
    (hYA_hasDeriv : ∀ u : ℝ, u ≠ 0 → HasDerivAt wg1YA (deriv wg1YA u) u)
    (hYA_deriv_cont : ContinuousOn (deriv wg1YA) ({0}ᶜ))
    (hAmp_c : CuspAmplitude (Real.pi / 8) CA (wg1AmpA ε c))
    (hAmp0 : ∀ τ : ℝ, ‖wg1AmpA ε c τ‖ ≤ CA)
    (hAmp1 : ∀ τ : ℝ, ‖deriv (wg1AmpA ε c) τ‖ ≤ CA)
    (h_ex_cont : Continuous (fun u : ℝ => Complex.exp (Complex.I * ((c * edgePhi L (ς * u) : ℝ) : ℂ)) * wg1AmpA ε c (ς * u) * wg1YA u))
    (h_ref_cont : Continuous (fun u : ℝ => Complex.exp (Complex.I * (((Real.pi ^ 2 * S - θ * ς) * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ)) * wg1YA u))
    (hK2 : K2 = 2) (hκex : κ_ex = 1 / 15) (hκref : κ_ref = 1 / 2)
    (hCex : C_ibp_ex = 2 * ((CA + 1) * CY) / κ_ex + (2 / 13) * ((CA + 1) * CY / κ_ex + (CA + 1) * CY * K2 / κ_ex ^ 2) + (2 / 11) * ((CA + 1) * CY / κ_ex))
    (hCref : C_ibp_ref = 2 * CY / κ_ref + (2 / 13) * (CY / κ_ref + CY * K2 / κ_ref ^ 2)) :
    ‖∫ u in V₀..V₁,
      (Complex.exp (Complex.I * ((c * edgePhi L (ς * (s * u)) : ℝ) : ℂ)) * wg1AmpA ε c (ς * (s * u)) * wg1YA (s * u) -
       Complex.exp (Complex.I * (((Real.pi ^ 2 * S - θ * ς) * (s * u) - Real.pi ^ 2 / 36 * (s * u) ^ 3 : ℝ) : ℂ)) * wg1YA (s * u))‖ ≤
      (C_ibp_ex + C_ibp_ref) * c ^ (-(13 / 24 : ℝ)) := by
  let exactInt : ℝ → ℂ := fun u =>
    Complex.exp (Complex.I * ((c * edgePhi L (ς * u) : ℝ) : ℂ)) * wg1AmpA ε c (ς * u) * wg1YA u
  let refInt : ℝ → ℂ := fun u =>
    Complex.exp (Complex.I * (((Real.pi ^ 2 * S - θ * ς) * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ)) * wg1YA u
  have hD_eq : ∫ u in V₀..V₁, (exactInt (s * u) - refInt (s * u)) =
      (∫ u in V₀..V₁, exactInt (s * u)) - (∫ u in V₀..V₁, refInt (s * u)) := by
    have hi1 : IntervalIntegrable (fun u => exactInt (s * u)) volume V₀ V₁ :=
      (h_ex_cont.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun u => refInt (s * u)) volume V₀ V₁ :=
      (h_ref_cont.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
    exact intervalIntegral.integral_sub hi1 hi2
  have hV₀_lb : 300 * S ≤ V₀ ^ 2 := by
    calc 300 * S = (5 * Real.sqrt (12 * S)) ^ 2 := by rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
      _ ≤ V₀ ^ 2 := pow_le_pow_left₀ (by positivity) hV₀_ge_cut 2
  have hV₀_rpow : V₀ ^ (-(13 / 2 : ℝ)) ≤ c ^ (-(13 / 24 : ℝ)) := by
    calc V₀ ^ (-(13 / 2 : ℝ)) ≤ (c ^ (1 / 12 : ℝ)) ^ (-(13 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hV₀_ge_c112 (by norm_num)
      _ = c ^ (-(13 / 24 : ℝ)) := by rw [← Real.rpow_mul hc0.le]; norm_num
  have hς_V₀_rpow : ς * V₀ ^ (-(11 / 2 : ℝ)) ≤ c ^ (-(13 / 24 : ℝ)) := by
    have h1 : ς * V₀ ^ (-(11 / 2 : ℝ)) ≤ c ^ (-(1 / 3 : ℝ)) * (c ^ (1 / 12 : ℝ)) ^ (-(11 / 2 : ℝ)) := by
      rw [hς_eq]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity) hV₀_ge_c112 (by norm_num)) (by positivity)
    have h2 : c ^ (-(1 / 3 : ℝ)) * (c ^ (1 / 12 : ℝ)) ^ (-(11 / 2 : ℝ)) = c ^ (-(19 / 24 : ℝ)) := by
      rw [← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; norm_num
    have h3 : c ^ (-(19 / 24 : ℝ)) ≤ c ^ (-(13 / 24 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    linarith only [h1, h2, h3]
  have hV₀_ge1 : (1 : ℝ) ≤ V₀ := by linarith only [hV₀_ge10]
  have hex_bound : ‖∫ u in V₀..V₁, exactInt (s * u)‖ ≤ C_ibp_ex * c ^ (-(13 / 24 : ℝ)) := by
    let φe : ℝ → ℝ := fun u => s * (c * edgePhi L (ς * u))
    let φe' : ℝ → ℝ := fun u => s * (c * ς * (L - hankelEdgeM (ς * u)))
    let φe'' : ℝ → ℝ := fun u => -(s * (c * ς ^ 2 * hankelEdgeM' (ς * u)))
    let ge : ℝ → ℂ := fun u => wg1AmpA ε c (ς * (s * u)) * wg1YA (s * u)
    let ge' : ℝ → ℂ := fun u =>
      ((ς * s : ℝ) : ℂ) * deriv (wg1AmpA ε c) (ς * (s * u)) * wg1YA (s * u) +
        wg1AmpA ε c (ς * (s * u)) * (((s : ℝ) : ℂ) * deriv wg1YA (s * u))
    have hint_eq : ∫ u in V₀..V₁, exactInt (s * u) =
        ∫ u in V₀..V₁, Complex.exp (Complex.I * (φe u : ℂ)) * ge u := by
      refine intervalIntegral.integral_congr fun u _ => ?_
      dsimp only [exactInt, φe, ge]
      have hodd : edgePhi L (ς * (s * u)) = s * edgePhi L (ς * u) := by
        rcases hs with rfl | rfl
        · simp
        · rw [show ς * (-1 * u) = -(ς * u) by ring, hankelEdgePhi_odd]; ring
      rw [hodd, show c * (s * edgePhi L (ς * u)) = s * (c * edgePhi L (ς * u)) by ring]
      ring
    have hφe : ∀ u ∈ Icc V₀ V₁, HasDerivAt φe (φe' u) u := fun u hu => by
      have hu0 : 0 < ς * u := mul_pos hς (by linarith only [hV₀_ge10, hu.1])
      have hids : HasDerivAt (fun x : ℝ => ς * x) ς u := by
        simpa only [id_eq, mul_one] using (hasDerivAt_id u).const_mul ς
      have hd1 := (((hankelEdgePhi_hasDerivAt L hu0).comp u hids).const_mul c).const_mul s
      refine hd1.congr_deriv ?_
      dsimp only [φe']; ring
    have hφe' : ∀ u ∈ Icc V₀ V₁, HasDerivAt φe' (φe'' u) u := fun u hu => by
      have hu0 : 0 < ς * u := mul_pos hς (by linarith only [hV₀_ge10, hu.1])
      have hids : HasDerivAt (fun x : ℝ => ς * x) ς u := by
        simpa only [id_eq, mul_one] using (hasDerivAt_id u).const_mul ς
      have hd1 := (hankelEdgeM_hasDerivAt hu0).comp u hids
      have hd2 := ((hd1.const_sub L).const_mul (c * ς)).const_mul s
      refine hd2.congr_deriv ?_
      dsimp only [φe'']; ring
    have hφe'_cont : ContinuousOn φe' (Icc V₀ V₁) := fun u hu => (hφe' u hu).continuousAt.continuousWithinAt
    have hφe''_cont : ContinuousOn φe'' (Icc V₀ V₁) := by
      have hcd := CtMDeriv.contDiffOn_mPrime
      have hm'_cont : ContinuousOn hankelEdgeM' (Ioi 0) :=
        hcd.continuousOn.congr fun t ht => (CtOuter.mPrime_eq_hankelEdgeM' ht).symm
      have hm'_sub : ContinuousOn (fun u => hankelEdgeM' (ς * u)) (Icc V₀ V₁) :=
        hm'_cont.comp (continuous_const.mul continuous_id).continuousOn fun u hu =>
          mul_pos hς (by linarith only [hV₀_ge10, hu.1])
      exact (continuousOn_const.mul (continuousOn_const.mul hm'_sub)).neg
    have hφe'_lb : ∀ u ∈ Icc V₀ V₁, κ_ex * u ^ 2 ≤ |φe' u| := fun u hu => by
      have hu0 : 0 < u := by linarith only [hV₀_ge10, hu.1]
      have hm_lb : (ς * u) ^ 2 / 10 ≤ hankelEdgeM (ς * u) := hankelEdgeM_ge_sq_tenth (mul_nonneg hς.le hu0.le)
        (by calc ς * u ≤ ς * V₁ := mul_le_mul_of_nonneg_left hu.2 hς.le
            _ ≤ 1 / 100 := hςV₁
            _ ≤ 2 := by norm_num)
      have hcς_m : u ^ 2 / 10 ≤ c * ς * hankelEdgeM (ς * u) := by
        calc u ^ 2 / 10 = (c * ς ^ 3) * (u ^ 2 / 10) := by rw [hcube, one_mul]
          _ = c * ς * ((ς * u) ^ 2 / 10) := by ring
          _ ≤ c * ς * hankelEdgeM (ς * u) := mul_le_mul_of_nonneg_left hm_lb (by positivity)
      have hcς_L : c * ς * L = Real.pi ^ 2 * S := by
        rw [hL_eq]; calc c * ς * (Real.pi ^ 2 * ς ^ 2 * S) = (c * ς ^ 3) * (Real.pi ^ 2 * S) := by ring
          _ = Real.pi ^ 2 * S := by rw [hcube, one_mul]
      have hu2 : V₀ ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by linarith only [hV₀_ge10]) hu.1 2
      have hpi2S : Real.pi ^ 2 * S ≤ u ^ 2 / 30 := by
        have hpi10 : Real.pi ^ 2 ≤ 10 := by nlinarith only [Real.pi_lt_d2, Real.pi_pos]
        calc Real.pi ^ 2 * S ≤ 10 * S := mul_le_mul_of_nonneg_right hpi10 hS0.le
          _ ≤ (10 / 300 : ℝ) * V₀ ^ 2 := by linarith only [hV₀_lb]
          _ ≤ u ^ 2 / 30 := by linarith only [hu2]
      have hdiff : κ_ex * u ^ 2 ≤ c * ς * hankelEdgeM (ς * u) - c * ς * L := by
        rw [hκex]; linarith only [hcς_m, hcς_L, hpi2S]
      have habs_s : |s| = 1 := by rcases hs with rfl | rfl <;> simp
      calc κ_ex * u ^ 2 ≤ c * ς * hankelEdgeM (ς * u) - c * ς * L := hdiff
        _ = -(c * ς * (L - hankelEdgeM (ς * u))) := by ring
        _ ≤ |c * ς * (L - hankelEdgeM (ς * u))| := neg_le_abs _
        _ = |φe' u| := by conv_rhs => dsimp only [φe']; rw [abs_mul, habs_s, one_mul]
    have hφe''_ub : ∀ u ∈ Icc V₀ V₁, |φe'' u| ≤ K2 * u := fun u hu => by
      have hu0 : 0 < u := by linarith only [hV₀_ge10, hu.1]
      have hm'_ub := hankelEdgeM'_bounds (mul_pos hς hu0)
      have hm'_pos : 0 < hankelEdgeM' (ς * u) := lt_of_lt_of_le (by positivity) hm'_ub.1
      have habs_s : |s| = 1 := by rcases hs with rfl | rfl <;> simp
      have hpiK : Real.pi ^ 2 / 6 ≤ K2 := by rw [hK2]; nlinarith only [Real.pi_lt_d2, Real.pi_pos]
      calc |φe'' u| = |s| * (c * ς ^ 2 * |hankelEdgeM' (ς * u)|) := by
              dsimp only [φe'']; rw [abs_neg, abs_mul, abs_mul]; congr 1; rw [abs_of_pos (by positivity)]
        _ = c * ς ^ 2 * hankelEdgeM' (ς * u) := by rw [habs_s, abs_of_pos hm'_pos, one_mul]
        _ ≤ c * ς ^ 2 * (Real.pi ^ 2 / 6 * (ς * u)) := mul_le_mul_of_nonneg_left hm'_ub.2.1 (by positivity)
        _ = Real.pi ^ 2 / 6 * (c * ς ^ 3) * u := by ring
        _ = Real.pi ^ 2 / 6 * u := by rw [hcube, mul_one]
        _ ≤ K2 * u := mul_le_mul_of_nonneg_right hpiK hu0.le
    have hge_deriv : ∀ u ∈ Icc V₀ V₁, HasDerivAt ge (ge' u) u := fun u hu => by
      have hu0 : 0 < u := by linarith only [hV₀_ge10, hu.1]
      have hsu0 : s * u ≠ 0 := mul_ne_zero (by rcases hs with rfl | rfl <;> norm_num) hu0.ne'
      have hidςs : HasDerivAt (fun x : ℝ => ς * (s * x)) (ς * s) u := by
        have h1 : HasDerivAt (fun x : ℝ => (ς * s) * x) (ς * s) u := by
          simpa only [id_eq, mul_one] using (hasDerivAt_id u).const_mul (ς * s)
        exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by ring)
      have hdA := ((hAmp_c.contDiff.differentiable (by norm_num)).differentiableAt.hasDerivAt).scomp u hidςs
      have hdA' : HasDerivAt (fun x => wg1AmpA ε c (ς * (s * x)))
          (((ς * s : ℝ) : ℂ) * deriv (wg1AmpA ε c) (ς * (s * u))) u := by
        refine hdA.congr_deriv ?_; simp only [Complex.real_smul]
      have hids : HasDerivAt (fun x : ℝ => s * x) s u := by
        simpa only [id_eq, mul_one] using (hasDerivAt_id u).const_mul s
      have hdY := (hYA_hasDeriv (s * u) hsu0).scomp u hids
      have hdY' : HasDerivAt (fun x => wg1YA (s * x)) (((s : ℝ) : ℂ) * deriv wg1YA (s * u)) u := by
        refine hdY.congr_deriv ?_; simp only [Complex.real_smul]
      exact (hdA'.mul hdY').congr_deriv (by dsimp only [ge'])
    have hge'_cont : ContinuousOn ge' (Icc V₀ V₁) := by
      have hcA' : Continuous (deriv (wg1AmpA ε c)) := hAmp_c.contDiff.continuous_deriv (by norm_num)
      have h1 : ContinuousOn (fun u => ((ς * s : ℝ) : ℂ) * deriv (wg1AmpA ε c) (ς * (s * u)) * wg1YA (s * u)) (Icc V₀ V₁) :=
        ((continuousOn_const.mul (hcA'.comp (continuous_const.mul (continuous_const.mul continuous_id))).continuousOn).mul
          (wg1YA_continuous.comp (continuous_const.mul continuous_id)).continuousOn)
      have hY'c : ContinuousOn (fun u => deriv wg1YA (s * u)) (Icc V₀ V₁) :=
        hYA_deriv_cont.comp (continuous_const.mul continuous_id).continuousOn fun u hu =>
          mul_ne_zero (by rcases hs with rfl | rfl <;> norm_num) (by linarith only [hV₀_ge10, hu.1])
      have h2 : ContinuousOn (fun u => wg1AmpA ε c (ς * (s * u)) * (((s : ℝ) : ℂ) * deriv wg1YA (s * u))) (Icc V₀ V₁) :=
        ((hAmp_c.contDiff.continuous.comp (continuous_const.mul (continuous_const.mul continuous_id))).continuousOn.mul
          (continuousOn_const.mul hY'c))
      exact h1.add h2
    have hge_ub : ∀ u ∈ Icc V₀ V₁, ‖ge u‖ ≤ (CA + 1) * CY * u ^ (-(9 / 2 : ℝ)) := fun u hu => by
      have hu0 : 0 < u := by linarith only [hV₀_ge10, hu.1]
      have habs_su : |s * u| = u := by
        rw [abs_mul, show |s| = 1 by rcases hs with rfl | rfl <;> simp, one_mul, abs_of_pos hu0]
      have hu_le : (1 + |s * u|) ^ (-(9 / 2 : ℝ)) ≤ u ^ (-(9 / 2 : ℝ)) := by
        rw [habs_su]; exact Real.rpow_le_rpow_of_nonpos hu0 (by linarith only) (by norm_num)
      have hCYu : 0 ≤ CY * u ^ (-(9 / 2 : ℝ)) := by positivity
      dsimp only [ge]; rw [norm_mul]
      calc ‖wg1AmpA ε c (ς * (s * u))‖ * ‖wg1YA (s * u)‖
          ≤ CA * (CY * (1 + |s * u|) ^ (-(9 / 2 : ℝ))) := mul_le_mul (hAmp0 _) (hYA_unif _) (norm_nonneg _) hCA0
        _ ≤ CA * (CY * u ^ (-(9 / 2 : ℝ))) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu_le hCY0.le) hCA0
        _ ≤ (CA + 1) * (CY * u ^ (-(9 / 2 : ℝ))) := mul_le_mul_of_nonneg_right (by linarith only) hCYu
        _ = (CA + 1) * CY * u ^ (-(9 / 2 : ℝ)) := by ring
    have hge'_ub : ∀ u ∈ Icc V₀ V₁,
        ‖ge' u‖ ≤ (CA + 1) * CY * u ^ (-(11 / 2 : ℝ)) + (CA + 1) * CY * ς * u ^ (-(9 / 2 : ℝ)) := fun u hu => by
      have hu0 : 0 < u := by linarith only [hV₀_ge10, hu.1]
      have habs_su : |s * u| = u := by
        rw [abs_mul, show |s| = 1 by rcases hs with rfl | rfl <;> simp, one_mul, abs_of_pos hu0]
      have h1su : 1 ≤ |s * u| := by rw [habs_su]; linarith only [hV₀_ge10, hu.1]
      have habs_s : |s| = 1 := by rcases hs with rfl | rfl <;> simp
      have hnorm_ςs : ‖((ς * s : ℝ) : ℂ)‖ = ς := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hς, habs_s, mul_one]
      have hnorm_s : ‖((s : ℝ) : ℂ)‖ = 1 := by rw [Complex.norm_real, Real.norm_eq_abs, habs_s]
      have ht1 : ‖((ς * s : ℝ) : ℂ) * deriv (wg1AmpA ε c) (ς * (s * u)) * wg1YA (s * u)‖ ≤
          (CA + 1) * CY * ς * u ^ (-(9 / 2 : ℝ)) := by
        rw [norm_mul, norm_mul, hnorm_ςs]
        have hu_le : (1 + |s * u|) ^ (-(9 / 2 : ℝ)) ≤ u ^ (-(9 / 2 : ℝ)) := by
          rw [habs_su]; exact Real.rpow_le_rpow_of_nonpos hu0 (by linarith only) (by norm_num)
        have hnn : 0 ≤ CY * ς * u ^ (-(9 / 2 : ℝ)) := by positivity
        calc ς * ‖deriv (wg1AmpA ε c) (ς * (s * u))‖ * ‖wg1YA (s * u)‖
            ≤ ς * CA * (CY * (1 + |s * u|) ^ (-(9 / 2 : ℝ))) :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hAmp1 _) hς.le) (hYA_unif _) (norm_nonneg _)
                (mul_nonneg hς.le hCA0)
          _ ≤ ς * CA * (CY * u ^ (-(9 / 2 : ℝ))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu_le hCY0.le) (mul_nonneg hς.le hCA0)
          _ = CA * (CY * ς * u ^ (-(9 / 2 : ℝ))) := by ring
          _ ≤ (CA + 1) * (CY * ς * u ^ (-(9 / 2 : ℝ))) := mul_le_mul_of_nonneg_right (by linarith only) hnn
          _ = (CA + 1) * CY * ς * u ^ (-(9 / 2 : ℝ)) := by ring
      have ht2 : ‖wg1AmpA ε c (ς * (s * u)) * (((s : ℝ) : ℂ) * deriv wg1YA (s * u))‖ ≤
          (CA + 1) * CY * u ^ (-(11 / 2 : ℝ)) := by
        rw [norm_mul, norm_mul, hnorm_s, one_mul]
        have hY' := hYA_deriv (s * u) h1su; rw [habs_su] at hY'
        have hnn : 0 ≤ CY * u ^ (-(11 / 2 : ℝ)) := by positivity
        calc ‖wg1AmpA ε c (ς * (s * u))‖ * ‖deriv wg1YA (s * u)‖
            ≤ CA * (CY * u ^ (-(11 / 2 : ℝ))) := mul_le_mul (hAmp0 _) hY' (norm_nonneg _) hCA0
          _ ≤ (CA + 1) * (CY * u ^ (-(11 / 2 : ℝ))) := mul_le_mul_of_nonneg_right (by linarith only) hnn
          _ = (CA + 1) * CY * u ^ (-(11 / 2 : ℝ)) := by ring
      rw [add_comm]
      exact (norm_add_le _ _).trans (add_le_add ht1 ht2)
    have hibp := ibp_osc_interval hV₀_ge1 hV₀_le_V₁ (by rw [hκex]; norm_num : 0 < κ_ex)
      (by rw [hK2]; norm_num : 0 ≤ K2) (by positivity) (by positivity) (by positivity) hς.le
      hφe hφe' hφe'_cont hφe''_cont hφe'_lb hφe''_ub hge_deriv hge'_cont hge_ub hge'_ub
    rw [hint_eq]
    calc ‖∫ u in V₀..V₁, Complex.exp (Complex.I * (φe u : ℂ)) * ge u‖
        ≤ (2 * ((CA + 1) * CY) / κ_ex + (2 / 13) * ((CA + 1) * CY / κ_ex + (CA + 1) * CY * K2 / κ_ex ^ 2)) *
              V₀ ^ (-(13 / 2 : ℝ)) +
            (2 / 11) * ((CA + 1) * CY / κ_ex) * ς * V₀ ^ (-(11 / 2 : ℝ)) := hibp
      _ ≤ (2 * ((CA + 1) * CY) / κ_ex + (2 / 13) * ((CA + 1) * CY / κ_ex + (CA + 1) * CY * K2 / κ_ex ^ 2)) *
              c ^ (-(13 / 24 : ℝ)) +
            (2 / 11) * ((CA + 1) * CY / κ_ex) * c ^ (-(13 / 24 : ℝ)) := by
            rw [mul_assoc ((2 / 11) * ((CA + 1) * CY / κ_ex)) ς _]
            have hA : 0 ≤ 2 * ((CA + 1) * CY) / κ_ex + (2 / 13) * ((CA + 1) * CY / κ_ex + (CA + 1) * CY * K2 / κ_ex ^ 2) := by
              rw [hκex, hK2]; positivity
            have hB : 0 ≤ (2 / 11 : ℝ) * ((CA + 1) * CY / κ_ex) := by rw [hκex]; positivity
            exact add_le_add (mul_le_mul_of_nonneg_left hV₀_rpow hA) (mul_le_mul_of_nonneg_left hς_V₀_rpow hB)
      _ = C_ibp_ex * c ^ (-(13 / 24 : ℝ)) := by rw [hCex]; ring
  have href_bound : ‖∫ u in V₀..V₁, refInt (s * u)‖ ≤ C_ibp_ref * c ^ (-(13 / 24 : ℝ)) := by
    let φr : ℝ → ℝ := fun u => s * ((Real.pi ^ 2 * S - θ * ς) * u - Real.pi ^ 2 / 36 * u ^ 3)
    let φr' : ℝ → ℝ := fun u => s * ((Real.pi ^ 2 * S - θ * ς) - Real.pi ^ 2 / 12 * u ^ 2)
    let φr'' : ℝ → ℝ := fun u => -(s * (Real.pi ^ 2 / 6 * u))
    let gr : ℝ → ℂ := fun u => wg1YA (s * u)
    let gr' : ℝ → ℂ := fun u => ((s : ℝ) : ℂ) * deriv wg1YA (s * u)
    have hint_eq : ∫ u in V₀..V₁, refInt (s * u) =
        ∫ u in V₀..V₁, Complex.exp (Complex.I * (φr u : ℂ)) * gr u := by
      refine intervalIntegral.integral_congr fun u _ => ?_
      dsimp only [refInt, φr, gr]
      have hs3 : (s * u) ^ 3 = s * u ^ 3 := by rcases hs with rfl | rfl <;> ring
      rw [show (Real.pi ^ 2 * S - θ * ς) * (s * u) - Real.pi ^ 2 / 36 * (s * u) ^ 3 =
        s * ((Real.pi ^ 2 * S - θ * ς) * u - Real.pi ^ 2 / 36 * u ^ 3) by rw [hs3]; ring]
    have hφr : ∀ u ∈ Icc V₀ V₁, HasDerivAt φr (φr' u) u := fun u _ => by
      dsimp only [φr, φr']
      have := (((hasDerivAt_id u).const_mul (Real.pi ^ 2 * S - θ * ς)).sub
        (((hasDerivAt_pow 3 u).const_mul (Real.pi ^ 2 / 36)))).const_mul s
      refine this.congr_deriv ?_; ring
    have hφr' : ∀ u ∈ Icc V₀ V₁, HasDerivAt φr' (φr'' u) u := fun u _ => by
      dsimp only [φr', φr'']
      have := ((hasDerivAt_const u (Real.pi ^ 2 * S - θ * ς)).sub
        ((hasDerivAt_pow 2 u).const_mul (Real.pi ^ 2 / 12))).const_mul s
      refine this.congr_deriv ?_; ring
    have hφr'_cont : ContinuousOn φr' (Icc V₀ V₁) := by fun_prop
    have hφr''_cont : ContinuousOn φr'' (Icc V₀ V₁) := by fun_prop
    have hφr'_lb : ∀ u ∈ Icc V₀ V₁, κ_ref * u ^ 2 ≤ |φr' u| := fun u hu => by
      have hu2 : V₀ ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by linarith only [hV₀_ge10]) hu.1 2
      have h100u : 100 ≤ u ^ 2 := by nlinarith only [hV₀_ge10, hu.1]
      have hpi9 : 9 ≤ Real.pi ^ 2 := by nlinarith only [Real.pi_gt_three]
      have hS_u : 300 * S ≤ u ^ 2 := hV₀_lb.trans hu2
      have h1 : Real.pi ^ 2 / 12 * u ^ 2 - Real.pi ^ 2 * S ≥ (24 / 300 : ℝ) * Real.pi ^ 2 * u ^ 2 := by
        nlinarith only [hS_u, sq_pos_of_pos Real.pi_pos]
      have h2 : (24 / 300 : ℝ) * Real.pi ^ 2 * u ^ 2 ≥ (72 / 100 : ℝ) * u ^ 2 := by
        nlinarith only [hpi9, sq_nonneg u]
      have hθ_lb : -((1 / 100 : ℝ) * u ^ 2) ≤ θ * ς := by
        have hth1 := (abs_le.mp hθς).1
        linarith only [hth1, h100u]
      have hneg_lb : κ_ref * u ^ 2 ≤ Real.pi ^ 2 / 12 * u ^ 2 - (Real.pi ^ 2 * S - θ * ς) := by
        rw [hκref]; linarith only [h1, h2, hθ_lb, sq_nonneg u]
      have habs_s : |s| = 1 := by rcases hs with rfl | rfl <;> simp
      calc κ_ref * u ^ 2 ≤ -((Real.pi ^ 2 * S - θ * ς) - Real.pi ^ 2 / 12 * u ^ 2) := by linarith only [hneg_lb]
        _ ≤ |(Real.pi ^ 2 * S - θ * ς) - Real.pi ^ 2 / 12 * u ^ 2| := by rw [← abs_neg]; exact le_abs_self _
        _ = |φr' u| := by dsimp only [φr']; rw [abs_mul, habs_s, one_mul]
    have hφr''_ub : ∀ u ∈ Icc V₀ V₁, |φr'' u| ≤ K2 * u := fun u hu => by
      have hu0 : 0 < u := by linarith only [hV₀_ge10, hu.1]
      have habs_s : |s| = 1 := by rcases hs with rfl | rfl <;> simp
      dsimp only [φr'']
      rw [abs_neg, abs_mul, habs_s, one_mul, abs_of_pos (by positivity)]
      have hpiK : Real.pi ^ 2 / 6 ≤ K2 := by rw [hK2]; nlinarith only [Real.pi_lt_d2, Real.pi_pos]
      exact mul_le_mul_of_nonneg_right hpiK hu0.le
    have hgr_deriv : ∀ u ∈ Icc V₀ V₁, HasDerivAt gr (gr' u) u := fun u hu => by
      have hu0 : 0 < u := by linarith only [hV₀_ge10, hu.1]
      have hsu0 : s * u ≠ 0 := mul_ne_zero (by rcases hs with rfl | rfl <;> norm_num) hu0.ne'
      have hids : HasDerivAt (fun x : ℝ => s * x) s u := by
        simpa only [id_eq, mul_one] using (hasDerivAt_id u).const_mul s
      have hdY := (hYA_hasDeriv (s * u) hsu0).scomp u hids
      refine hdY.congr_deriv ?_; dsimp only [gr']; simp only [Complex.real_smul]
    have hgr'_cont : ContinuousOn gr' (Icc V₀ V₁) := by
      have hY'c : ContinuousOn (fun u => deriv wg1YA (s * u)) (Icc V₀ V₁) :=
        hYA_deriv_cont.comp (continuous_const.mul continuous_id).continuousOn fun u hu =>
          mul_ne_zero (by rcases hs with rfl | rfl <;> norm_num) (by linarith only [hV₀_ge10, hu.1])
      exact continuousOn_const.mul hY'c
    have hgr_ub : ∀ u ∈ Icc V₀ V₁, ‖gr u‖ ≤ CY * u ^ (-(9 / 2 : ℝ)) := fun u hu => by
      have hu0 : 0 < u := by linarith only [hV₀_ge10, hu.1]
      have habs_su : |s * u| = u := by
        rw [abs_mul, show |s| = 1 by rcases hs with rfl | rfl <;> simp, one_mul, abs_of_pos hu0]
      have hu_le : (1 + |s * u|) ^ (-(9 / 2 : ℝ)) ≤ u ^ (-(9 / 2 : ℝ)) := by
        rw [habs_su]; exact Real.rpow_le_rpow_of_nonpos hu0 (by linarith only) (by norm_num)
      exact (hYA_unif (s * u)).trans (mul_le_mul_of_nonneg_left hu_le hCY0.le)
    have hgr'_ub : ∀ u ∈ Icc V₀ V₁, ‖gr' u‖ ≤ CY * u ^ (-(11 / 2 : ℝ)) + 0 * ς * u ^ (-(9 / 2 : ℝ)) := fun u hu => by
      have hu0 : 0 < u := by linarith only [hV₀_ge10, hu.1]
      have habs_su : |s * u| = u := by
        rw [abs_mul, show |s| = 1 by rcases hs with rfl | rfl <;> simp, one_mul, abs_of_pos hu0]
      have h1su : 1 ≤ |s * u| := by rw [habs_su]; linarith only [hV₀_ge10, hu.1]
      have hnorm_s : ‖((s : ℝ) : ℂ)‖ = 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]; rcases hs with rfl | rfl <;> simp
      dsimp only [gr']; rw [norm_mul, hnorm_s, one_mul, zero_mul, zero_mul, add_zero]
      have hY' := hYA_deriv (s * u) h1su; rwa [habs_su] at hY'
    have hibp := ibp_osc_interval hV₀_ge1 hV₀_le_V₁ (by rw [hκref]; norm_num : 0 < κ_ref)
      (by rw [hK2]; norm_num : 0 ≤ K2) hCY0.le hCY0.le le_rfl hς.le
      hφr hφr' hφr'_cont hφr''_cont hφr'_lb hφr''_ub hgr_deriv hgr'_cont hgr_ub hgr'_ub
    rw [hint_eq]
    have hCref_nn : 0 ≤ 2 * CY / κ_ref + (2 / 13) * (CY / κ_ref + CY * K2 / κ_ref ^ 2) := by
      rw [hκref, hK2]; positivity
    calc ‖∫ u in V₀..V₁, Complex.exp (Complex.I * (φr u : ℂ)) * gr u‖
        ≤ (2 * CY / κ_ref + (2 / 13) * (CY / κ_ref + CY * K2 / κ_ref ^ 2)) * V₀ ^ (-(13 / 2 : ℝ)) +
            (2 / 11) * (0 / κ_ref) * ς * V₀ ^ (-(11 / 2 : ℝ)) := hibp
      _ = (2 * CY / κ_ref + (2 / 13) * (CY / κ_ref + CY * K2 / κ_ref ^ 2)) * V₀ ^ (-(13 / 2 : ℝ)) := by ring
      _ ≤ (2 * CY / κ_ref + (2 / 13) * (CY / κ_ref + CY * K2 / κ_ref ^ 2)) * c ^ (-(13 / 24 : ℝ)) :=
            mul_le_mul_of_nonneg_left hV₀_rpow hCref_nn
      _ = C_ibp_ref * c ^ (-(13 / 24 : ℝ)) := by rw [hCref]
  rw [hD_eq]
  exact (norm_sub_le _ _).trans ((add_le_add hex_bound href_bound).trans_eq (by ring))

private lemma ctWg1_mid_single {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (Sw : ℝ) (hSw : 1 ≤ Sw) :
    ∃ c₀ C : ℝ, 64 ≤ c₀ ∧ 0 < C ∧ ∀ {c ξ : ℝ}, c₀ ≤ c → 0 < ξ →
      Sw ≤ hbS c ξ → Real.log (Real.pi ^ 2 * ξ) ≤ 3 * physDelta c →
      |normDensity (wg1PartA ε c) c ξ -
          ceK / ceCs * ceG1 (Special.airyZero 1)
            (-(ceBeta1 * hbS c ξ) + ceBeta1 * (deriv (outerTheta ε) 0 / Real.pi ^ 2) * liftEps c)| ≤
        C * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * Real.log (Real.pi ^ 2 * ξ) ^ (3 / 4 : ℝ)) := by
  obtain ⟨CY, hCY0, hYA_unif, hYA_deriv, hYA_hasDeriv, hYA_deriv_cont⟩ := wg1YA_unif_and_deriv
  obtain ⟨cA, CA, hcA64, hCA0, hAmp⟩ := wg1AmpA_cuspAmplitude
  obtain ⟨cmc, Kmc, hKmc0, hMc⟩ := mc_small
  obtain ⟨Cθ, hθ⟩ := outerTheta_taylor ε
  set θ : ℝ := deriv (outerTheta ε) 0
  set θ3 : ℝ := iteratedDeriv 3 (outerTheta ε) 0 / 6
  set Cθ1 : ℝ := |θ3| + |Cθ| + 1
  set c0 : ℝ := max (max cA cmc) (max (10 ^ 12 : ℝ) ((|θ| + 1) ^ 3 + 1))
  have hc064 : 64 ≤ c0 := le_max_of_le_left (le_max_of_le_left hcA64)
  let C_tail : ℝ := 2 * (CA + 1) * CY * (2 / 7)
  let C_inner : ℝ := CY * (4 * (Kmc * 2 + Real.pi ^ 4 / 600 + Cθ1) + (Real.pi ^ 4 / 600) * 43) + 1
  let K2 : ℝ := 2
  let κ_ex : ℝ := 1 / 15
  let κ_ref : ℝ := 1 / 2
  let C_ibp_ex : ℝ := (2 * ((CA + 1) * CY) / κ_ex + (2 / 13) * ((CA + 1) * CY / κ_ex + (CA + 1) * CY * K2 / κ_ex ^ 2)) +
    (2 / 11) * ((CA + 1) * CY / κ_ex)
  let C_ibp_ref : ℝ := 2 * CY / κ_ref + (2 / 13) * (CY / κ_ref + CY * K2 / κ_ref ^ 2)
  let Ctot : ℝ := (C_tail + C_inner + 2 * C_ibp_ex + 2 * C_ibp_ref) / (2 * Real.pi) + 1
  refine ⟨c0, Ctot, hc064, by positivity, fun {c ξ} hc hξ hS hL_ub => ?_⟩
  have hccA : cA ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hccmc : cmc ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hc1012 : (10 ^ 12 : ℝ) ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hcθ : (|θ| + 1) ^ 3 + 1 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  have hc64 : 64 ≤ c := hc064.trans hc
  have hc0 : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  set ς : ℝ := liftEps c
  have hς : 0 < ς := liftEps_pos hc0
  have hcube : c * ς ^ 3 = 1 := by have := liftEps_cube_mul hc0; linarith
  have hς2_eq : ς ^ 2 = c ^ (-(2 / 3 : ℝ)) := by
    dsimp only [ς, liftEps]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hς3_eq : ς ^ 3 = c⁻¹ := by
    have : ς ^ 3 * c = 1 := liftEps_cube_mul hc0
    field_simp [hc0.ne']; linarith
  have hς1 : ς ≤ 1 := by
    have : c ^ (-(1 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
    exact this
  set S : ℝ := hbS c ξ
  set L : ℝ := Real.log (Real.pi ^ 2 * ξ)
  have hS1 : 1 ≤ S := hSw.trans hS
  have hS0 : 0 < S := by linarith
  have hL_eq : L = Real.pi ^ 2 * ς ^ 2 * S := hb_L_eq hc0
  have hL0 : 0 < L := by rw [hL_eq]; positivity
  -- Bounds on `V₀` and `V₁`
  have hδ_ub : physDelta c ≤ Real.pi ^ 2 / 12 * c ^ (-(1 / 2 : ℝ)) := by
    have hτ1 : 0 ≤ c ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hc0.le _
    have hm : physDelta c = hankelEdgeM (c ^ (-(1 / 4 : ℝ))) := rfl
    rw [hm]
    refine (hankelEdgeM_le_sq hτ1).trans_eq ?_
    rw [← Real.rpow_natCast (c ^ (-(1 / 4 : ℝ))) 2, ← Real.rpow_mul hc0.le]; norm_num
  have hS_ub : S ≤ (1 / 4 : ℝ) * c ^ (1 / 6 : ℝ) := by
    have hL2 : Real.pi ^ 2 * c ^ (-(2 / 3 : ℝ)) * S ≤ (Real.pi ^ 2 / 4 : ℝ) * c ^ (-(1 / 2 : ℝ)) := by
      calc Real.pi ^ 2 * c ^ (-(2 / 3 : ℝ)) * S = L := by rw [hL_eq, hς2_eq]
        _ ≤ 3 * physDelta c := hL_ub
        _ ≤ 3 * (Real.pi ^ 2 / 12 * c ^ (-(1 / 2 : ℝ))) := by gcongr
        _ = (Real.pi ^ 2 / 4 : ℝ) * c ^ (-(1 / 2 : ℝ)) := by ring
    have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    have h1 : c ^ (-(2 / 3 : ℝ)) * S ≤ (1 / 4 : ℝ) * c ^ (-(1 / 2 : ℝ)) := by nlinarith
    have h2 : S ≤ (1 / 4 : ℝ) * c ^ (-(1 / 2 : ℝ)) * c ^ (2 / 3 : ℝ) := by
      have hc23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
      have := mul_le_mul_of_nonneg_right h1 hc23.le
      have hmul : c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) = 1 := by
        rw [← Real.rpow_add hc0]; norm_num
      linarith [show c ^ (-(2 / 3 : ℝ)) * S * c ^ (2 / 3 : ℝ) = S * (c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) by ring,
        show S * (c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) = S by rw [hmul, mul_one]]
    refine h2.trans_eq ?_
    rw [mul_assoc, ← Real.rpow_add hc0]; norm_num
  set V₀ : ℝ := max (5 * Real.sqrt (12 * S)) (c ^ (1 / 12 : ℝ))
  set V₁ : ℝ := c ^ (1 / 6 : ℝ)
  have hc112_ge10 : 10 ≤ c ^ (1 / 12 : ℝ) := by
    have h10 : (10 : ℝ) = ((10 ^ 12 : ℝ) ^ (1 / 12 : ℝ)) := by
      rw [← Real.rpow_natCast (10 : ℝ) 12, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [h10]
    exact Real.rpow_le_rpow (by norm_num) hc1012 (by norm_num)
  have hV₀_ge_c112 : c ^ (1 / 12 : ℝ) ≤ V₀ := le_max_right _ _
  have hV₀_ge10 : 10 ≤ V₀ := hc112_ge10.trans hV₀_ge_c112
  have hV₀_ge_cut : 5 * Real.sqrt (12 * S) ≤ V₀ := le_max_left _ _
  have hV₀_le_V₁ : V₀ ≤ V₁ := by
    have hc16 : c ^ (1 / 12 : ℝ) * c ^ (1 / 12 : ℝ) = V₁ := by
      dsimp only [V₁]; rw [← Real.rpow_add hc0]; norm_num
    have h1 : c ^ (1 / 12 : ℝ) ≤ V₁ := by nlinarith
    have hsqrt3 : Real.sqrt 3 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have hsqrt_c : Real.sqrt (c ^ (1 / 6 : ℝ)) = c ^ (1 / 12 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hc0.le]; norm_num
    have h2 : 5 * Real.sqrt (12 * S) ≤ V₁ := by
      have h12S : 12 * S ≤ 3 * c ^ (1 / 6 : ℝ) := by linarith [hS_ub]
      calc 5 * Real.sqrt (12 * S) ≤ 5 * Real.sqrt (3 * c ^ (1 / 6 : ℝ)) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h12S) (by norm_num)
        _ = 5 * (Real.sqrt 3 * Real.sqrt (c ^ (1 / 6 : ℝ))) := by rw [Real.sqrt_mul (by norm_num)]
        _ ≤ 5 * (2 * c ^ (1 / 12 : ℝ)) := by rw [hsqrt_c]; gcongr
        _ = 10 * c ^ (1 / 12 : ℝ) := by ring
        _ ≤ c ^ (1 / 12 : ℝ) * c ^ (1 / 12 : ℝ) := by gcongr
        _ = V₁ := hc16
    exact max_le h2 h1
  have hV₁_ge10 : 10 ≤ V₁ := hV₀_ge10.trans hV₀_le_V₁
  have hςV₁ : ς * V₁ ≤ 1 / 100 := by
    have hςV : ς * V₁ = c ^ (-(1 / 6 : ℝ)) := by
      dsimp only [ς, liftEps, V₁]; rw [← Real.rpow_add hc0]; norm_num
    have h100 : (c ^ (-(1 / 6 : ℝ))) ≤ (10 ^ 12 : ℝ) ^ (-(1 / 6 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hc1012 (by norm_num)
    have h100_eq : ((10 ^ 12 : ℝ) ^ (-(1 / 6 : ℝ))) = 1 / 100 := by
      rw [← Real.rpow_natCast (10 : ℝ) 12, ← Real.rpow_mul (by norm_num)]; norm_num
    linarith
  have hθς : |θ * ς| ≤ 1 := by
    have h1 : c ^ (1 / 3 : ℝ) ≥ |θ| + 1 := by
      have : (|θ| + 1) ^ 3 ≤ c := by linarith
      have hroot : |θ| + 1 = ((|θ| + 1) ^ 3 : ℝ) ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_natCast (|θ| + 1) 3, ← Real.rpow_mul (by positivity)]; norm_num
      rw [hroot]
      exact Real.rpow_le_rpow (by positivity) this (by norm_num)
    have h2 : |θ| * ς ≤ 1 := by
      have : ς = (c ^ (1 / 3 : ℝ))⁻¹ := by dsimp only [ς, liftEps]; rw [Real.rpow_neg hc0.le]
      rw [this]
      calc |θ| * (c ^ (1 / 3 : ℝ))⁻¹ ≤ (|θ| + 1) * (c ^ (1 / 3 : ℝ))⁻¹ := by gcongr; linarith
        _ ≤ c ^ (1 / 3 : ℝ) * (c ^ (1 / 3 : ℝ))⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ (Real.rpow_pos_of_pos hc0 _).ne'
    simpa [abs_mul, abs_of_pos hς] using h2
  -- Define exact & reference integrands
  let exactInt : ℝ → ℂ := fun u =>
    Complex.exp (Complex.I * ((c * edgePhi L (ς * u) : ℝ) : ℂ)) * wg1AmpA ε c (ς * u) * wg1YA u
  let refInt : ℝ → ℂ := fun u =>
    Complex.exp (Complex.I * (((Real.pi ^ 2 * S - θ * ς) * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ)) * wg1YA u
  have hAmp_c := hAmp hε hccA
  have hAmp0 : ∀ τ : ℝ, ‖wg1AmpA ε c τ‖ ≤ CA := fun τ => by
    have h := hAmp_c.deriv_bound 0 (by norm_num) τ
    simp only [iteratedDeriv_zero] at h
    exact h.trans (mul_le_of_le_one_right hCA0 (Real.exp_le_one_iff.mpr (by rw [neg_mul]; exact neg_nonpos.mpr (by positivity))))
  have hAmp1 : ∀ τ : ℝ, ‖deriv (wg1AmpA ε c) τ‖ ≤ CA := fun τ => by
    have h := hAmp_c.deriv_bound 1 (by norm_num) τ
    rw [iteratedDeriv_one] at h
    exact h.trans (mul_le_of_le_one_right hCA0 (Real.exp_le_one_iff.mpr (by rw [neg_mul]; exact neg_nonpos.mpr (by positivity))))
  have h_ex_cont : Continuous exactInt := by
    have hφc : Continuous (fun u : ℝ => edgePhi L (ς * u)) :=
      (continuous_iff_continuousAt.mpr fun u => (hasDerivAt_edgePhi L u).continuousAt).comp
        (continuous_const.mul continuous_id)
    exact ((Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_const.mul hφc)))).mul ((hAmp_c.contDiff.continuous).comp (continuous_const.mul continuous_id))).mul wg1YA_continuous
  have h_ref_cont : Continuous refInt :=
    (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (by fun_prop)))).mul wg1YA_continuous
  have hrp9_5 : ∀ u : ℝ, (1 + |u|) ^ (-(9 / 2 : ℝ)) ≤ (1 + |u|) ^ (-(5 / 2 : ℝ)) := fun u =>
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg u]) (by norm_num)
  have hi_ex : Integrable exactInt := (integrable_weight ((CA + 1) * CY)).mono' h_ex_cont.aestronglyMeasurable
    (ae_of_all _ fun u => by
      dsimp only [exactInt]
      rw [norm_mul, norm_mul,
        show Complex.I * ((c * edgePhi L (ς * u) : ℝ) : ℂ) = (((c * edgePhi L (ς * u) : ℝ) : ℂ) * Complex.I) by ring,
        Complex.norm_exp_ofReal_mul_I, one_mul]
      calc ‖wg1AmpA ε c (ς * u)‖ * ‖wg1YA u‖ ≤ CA * (CY * (1 + |u|) ^ (-(9 / 2 : ℝ))) :=
            mul_le_mul (hAmp0 _) (hYA_unif u) (norm_nonneg _) hCA0
        _ ≤ CA * (CY * (1 + |u|) ^ (-(5 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hrp9_5 u) hCY0.le) hCA0
        _ ≤ (CA + 1) * CY * (1 + |u|) ^ (-(5 / 2 : ℝ)) := by
            have : 0 ≤ CY * (1 + |u|) ^ (-(5 / 2 : ℝ)) := by positivity
            linarith)
  have hi_ref : Integrable refInt := (integrable_weight CY).mono' h_ref_cont.aestronglyMeasurable
    (ae_of_all _ fun u => by
      dsimp only [refInt]
      rw [norm_mul,
        show Complex.I * (((Real.pi ^ 2 * S - θ * ς) * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ) =
          ((((Real.pi ^ 2 * S - θ * ς) * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ) * Complex.I) by ring,
        Complex.norm_exp_ofReal_mul_I, one_mul]
      exact (hYA_unif u).trans (mul_le_mul_of_nonneg_left (hrp9_5 u) hCY0.le))
  -- Identify `normDensity (wg1PartA)` and reference integral
  have hnd_eq : normDensity (wg1PartA ε c) c ξ =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ u : ℝ, exactInt u).re := by
    rw [wg1PartA_normDensity hε hc0 hξ]
    unfold cuspEdgeJ
    set f : ℝ → ℂ := fun τ =>
      Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * wg1AmpA ε c τ * wg1YA (c ^ (1 / 3 : ℝ) * τ)
    have h1 := MeasureTheory.Measure.integral_comp_mul_left f ς
    have hf : ∀ u : ℝ, f (ς * u) = exactInt u := fun u => by
      dsimp only [f, exactInt]
      have hcς : c ^ (1 / 3 : ℝ) * (ς * u) = u := by
        have : c ^ (1 / 3 : ℝ) * ς = 1 := by
          dsimp only [ς, liftEps]; rw [← Real.rpow_add hc0]; norm_num
        calc c ^ (1 / 3 : ℝ) * (ς * u) = (c ^ (1 / 3 : ℝ) * ς) * u := by ring
          _ = u := by rw [this, one_mul]
      rw [hcς]
    have hsc : |ς⁻¹| = c ^ (1 / 3 : ℝ) := by
      rw [abs_of_pos (inv_pos.mpr hς)]
      dsimp only [ς, liftEps]; rw [Real.rpow_neg hc0.le, inv_inv]
    have heq_int : ((c ^ (1 / 3 : ℝ) / (2 * Real.pi) : ℝ) : ℂ) * ∫ τ : ℝ, f τ =
        ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ u : ℝ, exactInt u := by
      have heq_f : ∫ u : ℝ, f (ς * u) = ∫ u : ℝ, exactInt u := integral_congr_ae (ae_of_all _ hf)
      rw [← heq_f, h1, Complex.real_smul, hsc]
      push_cast; ring
    rw [heq_int]
  have href_id := airy_reference_identity hasU2_ceG1 (continuous_ceG1 _) (le_refl (0 : ℝ)) 0 hξ
    (Real.pi ^ 2 * S - θ * ς)
  have href_val : ((ceK / ceCs * ceG1 (Special.airyZero 1)
      (-(ceBeta1 * S) + ceBeta1 * (θ / Real.pi ^ 2) * ς) : ℝ) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ u : ℝ, refInt u := by
    have h1 := congrArg (fun z : ℂ => (ξ : ℂ) * z) href_id
    have hξ0 : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ.ne'
    have hwindow0 : windowSmooth 0 0 (ceG1 (Special.airyZero 1)) = ceG1 (Special.airyZero 1) := by
      funext x; simp [windowSmooth]
    have harg : -((Real.pi ^ 2 * S - θ * ς) / ceCs) = -(ceBeta1 * S) + ceBeta1 * (θ / Real.pi ^ 2) * ς := by
      have hcm := ceCs_mul_ceBeta1
      rw [← hcm]; field_simp [ceCs_pos.ne', ceBeta1_pos.ne']; ring
    rw [hwindow0, harg] at h1
    have hR_eq : ∫ u : ℝ, refInt u = ∫ v : ℝ, liftSymbol (ceG1 (Special.airyZero 1)) 0 0 ((v : ℂ) * Complex.I) *
        Complex.exp (Complex.I * (((Real.pi ^ 2 * S - θ * ς) * v - Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) := by
      refine integral_congr_ae (ae_of_all _ fun u => ?_)
      dsimp only [refInt]
      rw [liftSymbol_zero_order]; unfold wg1YA ctTg1; push_cast; ring
    rw [hR_eq]
    have h2pi : ((2 * Real.pi : ℝ) : ℂ)⁻¹ = (ξ : ℂ) * ((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ := by
      push_cast; field_simp [hξ0]
    symm
    calc ((2 * Real.pi : ℝ) : ℂ)⁻¹ * _
        = (ξ : ℂ) * (((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * _) := by rw [h2pi, mul_assoc]
      _ = (ξ : ℂ) * ((ceK : ℂ) / ((ceCs : ℂ) * (ξ : ℂ)) *
            ((ceG1 (Special.airyZero 1) (-(ceBeta1 * S) + ceBeta1 * (θ / Real.pi ^ 2) * ς) : ℝ) : ℂ)) := h1
      _ = _ := by push_cast; field_simp [hξ0]
  have hdiff_le : |normDensity (wg1PartA ε c) c ξ -
      ceK / ceCs * ceG1 (Special.airyZero 1) (-(ceBeta1 * S) + ceBeta1 * (θ / Real.pi ^ 2) * ς)| ≤
      (2 * Real.pi)⁻¹ * ‖∫ u : ℝ, (exactInt u - refInt u)‖ := by
    rw [hnd_eq, ← Complex.ofReal_re (ceK / ceCs * ceG1 _ _), href_val, ← Complex.sub_re, ← mul_sub,
      ← integral_sub hi_ex hi_ref]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  -- Split `∫ u, (exactInt u - refInt u)` into `S₁ᶜ`, `(-V₁)..(-V₀)`, `(-V₀)..V₀`, and `V₀..V₁`
  let D : ℝ → ℂ := fun u => exactInt u - refInt u
  have hiD : Integrable D := hi_ex.sub hi_ref
  let S₁ : Set ℝ := Ioc (-V₁) V₁
  have hsplit_main : ∫ u : ℝ, D u =
      (∫ u in S₁ᶜ, D u) + ((∫ u in (-V₁)..(-V₀), D u) + (∫ u in (-V₀)..V₀, D u) + (∫ u in V₀..V₁, D u)) := by
    have h1 := (MeasureTheory.integral_add_compl (measurableSet_Ioc : MeasurableSet S₁) hiD).symm
    have h2 : ∫ u in S₁, D u = ∫ u in (-V₁)..V₁, D u := (intervalIntegral.integral_of_le (by linarith)).symm
    have hi_int : ∀ x y : ℝ, IntervalIntegrable D volume x y := fun x y => hiD.intervalIntegrable
    have h3 : ∫ u in (-V₁)..V₁, D u = (∫ u in (-V₁)..(-V₀), D u) + (∫ u in (-V₀)..V₀, D u) + (∫ u in V₀..V₁, D u) := by
      have hA := intervalIntegral.integral_add_adjacent_intervals (hi_int (-V₁) (-V₀)) (hi_int (-V₀) V₀)
      have hB := intervalIntegral.integral_add_adjacent_intervals (hi_int (-V₁) V₀) (hi_int V₀ V₁)
      rw [← hB, ← hA]
    rw [h1, h2, h3]; ring
  -- 1. Tail `|u| ≥ V₁`
  have htail_bd : ‖∫ u in S₁ᶜ, D u‖ ≤ C_tail * c ^ (-(7 / 12 : ℝ)) := by
    have hD_far : ∀ u : ℝ, V₁ ≤ |u| → ‖D u‖ ≤ (CA + 1) * CY * |u| ^ (-(9 / 2 : ℝ)) := fun u hu => by
      have hu_pos : 0 < |u| := by linarith only [hV₁_ge10, hu]
      have hu_ne : (1 + |u|) ^ (-(9 / 2 : ℝ)) ≤ |u| ^ (-(9 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hu_pos (by linarith only [abs_nonneg u]) (by norm_num)
      have h_ex_u : ‖exactInt u‖ ≤ CA * CY * |u| ^ (-(9 / 2 : ℝ)) := by
        dsimp only [exactInt]
        rw [norm_mul, norm_mul,
          show Complex.I * ((c * edgePhi L (ς * u) : ℝ) : ℂ) = (((c * edgePhi L (ς * u) : ℝ) : ℂ) * Complex.I) by ring,
          Complex.norm_exp_ofReal_mul_I, one_mul]
        calc ‖wg1AmpA ε c (ς * u)‖ * ‖wg1YA u‖ ≤ CA * (CY * (1 + |u|) ^ (-(9 / 2 : ℝ))) :=
              mul_le_mul (hAmp0 _) (hYA_unif u) (norm_nonneg _) hCA0
          _ ≤ CA * (CY * |u| ^ (-(9 / 2 : ℝ))) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu_ne hCY0.le) hCA0
          _ = _ := by ring
      have h_ref_u : ‖refInt u‖ ≤ 1 * CY * |u| ^ (-(9 / 2 : ℝ)) := by
        dsimp only [refInt]
        rw [norm_mul,
          show Complex.I * (((Real.pi ^ 2 * S - θ * ς) * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ) =
            ((((Real.pi ^ 2 * S - θ * ς) * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ) * Complex.I) by ring,
          Complex.norm_exp_ofReal_mul_I, one_mul, one_mul]
        exact (hYA_unif u).trans (mul_le_mul_of_nonneg_left hu_ne hCY0.le)
      calc ‖exactInt u - refInt u‖ ≤ ‖exactInt u‖ + ‖refInt u‖ := norm_sub_le _ _
        _ ≤ _ := by linarith only [h_ex_u, h_ref_u]
    have hV₁_pow : V₁ ^ (-(7 / 2 : ℝ)) = c ^ (-(7 / 12 : ℝ)) := by
      dsimp only [V₁]; rw [← Real.rpow_mul hc0.le]; norm_num
    exact mid_tail_bd (by linarith only [hV₁_ge10]) hV₁_pow rfl hiD hD_far
  -- 2. Inner piece `(-V₀)..V₀`
  have hinner_bd : ‖∫ u in (-V₀)..V₀, D u‖ ≤
      C_inner * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ)) :=
    mid_inner_bd hc0 hc1 hς hς1 hcube hς2_eq hς3_eq hL0 hL_eq rfl hV₀_ge10 hV₀_ge_cut hV₀_ge_c112
      hV₀_le_V₁ hςV₁ hKmc0 (fun τ hτ => ((hMc c 0 hccmc le_rfl zero_le_one).2 τ hτ).1) hθ rfl hCY0 hYA_unif rfl
  -- 3. IBP bands `V₀..V₁` and `(-V₁)..(-V₀)`
  have hibp_pos : ‖∫ u in V₀..V₁, D u‖ ≤ (C_ibp_ex + C_ibp_ref) * c ^ (-(13 / 24 : ℝ)) := by
    have := mid_ibp_side (Or.inl rfl) hc0 hc1 hς hcube rfl hS0 hL_eq hV₀_ge10 hV₀_ge_cut hV₀_ge_c112
      hV₀_le_V₁ hςV₁ hθς hCA0 hCY0 hYA_unif hYA_deriv hYA_hasDeriv hYA_deriv_cont hAmp_c hAmp0 hAmp1
      h_ex_cont h_ref_cont rfl rfl rfl rfl rfl
    simpa only [one_mul] using this
  have hibp_neg : ‖∫ u in (-V₁)..(-V₀), D u‖ ≤ (C_ibp_ex + C_ibp_ref) * c ^ (-(13 / 24 : ℝ)) := by
    have hcomp := intervalIntegral.integral_comp_neg D (a := V₀) (b := V₁)
    rw [← hcomp]
    have := mid_ibp_side (Or.inr rfl) hc0 hc1 hς hcube rfl hS0 hL_eq hV₀_ge10 hV₀_ge_cut hV₀_ge_c112
      hV₀_le_V₁ hςV₁ hθς hCA0 hCY0 hYA_unif hYA_deriv hYA_hasDeriv hYA_deriv_cont hAmp_c hAmp0 hAmp1
      h_ex_cont h_ref_cont rfl rfl rfl rfl rfl
    simpa only [neg_one_mul] using this
  -- 4. Combine all four pieces
  have hint_tot : ‖∫ u : ℝ, D u‖ ≤
      (C_tail + C_inner + 2 * C_ibp_ex + 2 * C_ibp_ref) *
        (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ)) := by
    have hc712 : c ^ (-(7 / 12 : ℝ)) ≤ c ^ (-(13 / 24 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have hL_nn : 0 ≤ c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ) := by positivity
    have hsum_nn : 0 ≤ c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ) := by positivity
    have h1 : ‖∫ u in S₁ᶜ, D u‖ ≤ C_tail * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ)) := by
      have hc00 : c ^ (-(7 / 12 : ℝ)) ≤ c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ) := by
        linarith only [hc712, hL_nn]
      exact htail_bd.trans (mul_le_mul_of_nonneg_left hc00 (by dsimp only [C_tail]; positivity))
    have h2 : ‖∫ u in (-V₁)..(-V₀), D u‖ ≤
        (C_ibp_ex + C_ibp_ref) * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ)) :=
      hibp_neg.trans (mul_le_mul_of_nonneg_left (by linarith only [hL_nn]) (by positivity))
    have h3 : ‖∫ u in V₀..V₁, D u‖ ≤
        (C_ibp_ex + C_ibp_ref) * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ)) :=
      hibp_pos.trans (mul_le_mul_of_nonneg_left (by linarith only [hL_nn]) (by positivity))
    rw [hsplit_main]
    calc ‖(∫ u in S₁ᶜ, D u) + ((∫ u in (-V₁)..(-V₀), D u) + (∫ u in (-V₀)..V₀, D u) + (∫ u in V₀..V₁, D u))‖
        ≤ ‖∫ u in S₁ᶜ, D u‖ + ‖(∫ u in (-V₁)..(-V₀), D u) + (∫ u in (-V₀)..V₀, D u) + (∫ u in V₀..V₁, D u)‖ :=
            norm_add_le _ _
      _ ≤ ‖∫ u in S₁ᶜ, D u‖ + (‖∫ u in (-V₁)..(-V₀), D u‖ + ‖∫ u in (-V₀)..V₀, D u‖ + ‖∫ u in V₀..V₁, D u‖) := by
            gcongr; exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := by linarith only [h1, h2, h3, hinner_bd]
  refine hdiff_le.trans ?_
  calc (2 * Real.pi)⁻¹ * ‖∫ u : ℝ, (exactInt u - refInt u)‖
      ≤ (2 * Real.pi)⁻¹ * ((C_tail + C_inner + 2 * C_ibp_ex + 2 * C_ibp_ref) *
          (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ))) := by
            gcongr
    _ ≤ Ctot * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ)) := by
            have hsum_nn : 0 ≤ c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ) := by positivity
            have hC : (2 * Real.pi)⁻¹ * (C_tail + C_inner + 2 * C_ibp_ex + 2 * C_ibp_ref) ≤ Ctot := by
              dsimp only [Ctot]; rw [div_eq_mul_inv]; linarith only
            calc (2 * Real.pi)⁻¹ * ((C_tail + C_inner + 2 * C_ibp_ex + 2 * C_ibp_ref) *
                    (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ)))
                = ((2 * Real.pi)⁻¹ * (C_tail + C_inner + 2 * C_ibp_ex + 2 * C_ibp_ref)) *
                    (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ)) := by ring
              _ ≤ Ctot * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * L ^ (3 / 4 : ℝ)) := by gcongr

/-- **`(fct:hg1-mid)`**: intermediate-band Airy expansion of `normDensity (ctWg1 ε c) c ξ` on
`Sw ≤ hbS c ξ` and `log(π² ξ) ≤ 3 * physDelta c`. -/
theorem ctWg1_mid_bound (Sw : ℝ) (hSw : 1 ≤ Sw) :
    ∃ c₀ C : ℝ, 64 ≤ c₀ ∧ 0 < C ∧ ∀ {ε c ξ : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
      Sw ≤ hbS c ξ → Real.log (Real.pi ^ 2 * ξ) ≤ 3 * physDelta c →
      |normDensity (ctWg1 ε c) c ξ -
          ceK / ceCs * ceG1 (Special.airyZero 1)
            (-(ceBeta1 * hbS c ξ) + ceBeta1 * (deriv (outerTheta ε) 0 / Real.pi ^ 2) * liftEps c)| ≤
        C * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * Real.log (Real.pi ^ 2 * ξ) ^ (3 / 4 : ℝ)) := by
  obtain ⟨c1, C1, hc1, hC1, h1⟩ := ctWg1_mid_single (Or.inl rfl) Sw hSw
  obtain ⟨c2, C2, hc2, hC2, h2⟩ := ctWg1_mid_single (Or.inr rfl) Sw hSw
  obtain ⟨cS, hcS, hsp⟩ := ctWg1_normDensity_split
  obtain ⟨cB, CB, hcB, hCB0, hB⟩ := ctWg1_partB_bound
  refine ⟨max (max c1 c2) (max cS cB), max C1 C2 + CB, le_max_of_le_left (le_max_of_le_left hc1),
    by positivity, fun {ε c ξ} hε hc hξ hS hL_ub => ?_⟩
  have hc64 : 64 ≤ c := (le_max_of_le_left (le_max_of_le_left hc1)).trans hc
  have hc1' : 1 ≤ c := by linarith only [hc64]
  have hc0 : 0 < c := by linarith only [hc64]
  have hL0 : 0 ≤ Real.log (Real.pi ^ 2 * ξ) := by
    have h1S : 0 < hbS c ξ := by linarith only [hSw, hS]
    have hL_eq : Real.log (Real.pi ^ 2 * ξ) = Real.pi ^ 2 * (liftEps c) ^ 2 * hbS c ξ := hb_L_eq hc0
    rw [hL_eq]; positivity
  rw [hsp hε ((le_max_left cS cB).trans ((le_max_right _ _).trans hc)) hξ]
  have hA_bd : |normDensity (wg1PartA ε c) c ξ - ceK / ceCs * ceG1 (Special.airyZero 1)
      (-(ceBeta1 * hbS c ξ) + ceBeta1 * (deriv (outerTheta ε) 0 / Real.pi ^ 2) * liftEps c)| ≤
      max C1 C2 * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * Real.log (Real.pi ^ 2 * ξ) ^ (3 / 4 : ℝ)) := by
    have hsum_nn : 0 ≤ c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * Real.log (Real.pi ^ 2 * ξ) ^ (3 / 4 : ℝ) := by positivity
    rcases hε with rfl | rfl
    · exact (h1 ((le_max_left c1 c2).trans ((le_max_left _ _).trans hc)) hξ hS hL_ub).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hsum_nn)
    · exact (h2 ((le_max_right c1 c2).trans ((le_max_left _ _).trans hc)) hξ hS hL_ub).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hsum_nn)
  have hB_bd := (hB hε ((le_max_right cS cB).trans ((le_max_right _ _).trans hc)) hξ).1
  have hB_le : |normDensity (wg1PartB ε c) c ξ| ≤
      CB * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * Real.log (Real.pi ^ 2 * ξ) ^ (3 / 4 : ℝ)) := by
    have hc23 : c ^ (-(2 / 3 : ℝ)) ≤ c ^ (-(13 / 24 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hc1' (by norm_num)
    have hL_nn : 0 ≤ c ^ (-(1 / 6 : ℝ)) * Real.log (Real.pi ^ 2 * ξ) ^ (3 / 4 : ℝ) := by positivity
    exact hB_bd.trans (mul_le_mul_of_nonneg_left (by linarith only [hc23, hL_nn]) hCB0)
  have htri : normDensity (wg1PartA ε c) c ξ + normDensity (wg1PartB ε c) c ξ -
      ceK / ceCs * ceG1 (Special.airyZero 1)
        (-(ceBeta1 * hbS c ξ) + ceBeta1 * (deriv (outerTheta ε) 0 / Real.pi ^ 2) * liftEps c) =
      (normDensity (wg1PartA ε c) c ξ - ceK / ceCs * ceG1 (Special.airyZero 1)
        (-(ceBeta1 * hbS c ξ) + ceBeta1 * (deriv (outerTheta ε) 0 / Real.pi ^ 2) * liftEps c)) +
      normDensity (wg1PartB ε c) c ξ := by ring
  rw [htri]
  calc |_ + _| ≤ |_| + |_| := abs_add_le _ _
    _ ≤ max C1 C2 * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * Real.log (Real.pi ^ 2 * ξ) ^ (3 / 4 : ℝ)) +
        CB * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * Real.log (Real.pi ^ 2 * ξ) ^ (3 / 4 : ℝ)) :=
          add_le_add hA_bd hB_le
    _ = (max C1 C2 + CB) * (c ^ (-(13 / 24 : ℝ)) + c ^ (-(1 / 6 : ℝ)) * Real.log (Real.pi ^ 2 * ξ) ^ (3 / 4 : ℝ)) := by
          ring

/-- info: 'FormalResearch.SignUncertainty.ctWg1_mid_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctWg1_mid_bound

end FormalResearch.SignUncertainty

