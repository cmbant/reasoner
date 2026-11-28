/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_4_2

/-!
# Section 4.3 Helpers (`s4:4.3`): Calibrated Positivity, Negative-Mass Box, and Error Comparison

Supporting lemmas for `SpinS4_4_3` (`Spin/SpinS4_4_3.lean`):
1. `spinGcal_re_nonneg_of_ge`, `spinHbCalReal_pos_lower_near_tip`: exterior positivity and uniform
   near-tip kernel positivity.
2. `integrable_spinCalInt_integrand`, `integrable_spinCalNorm_integrand`,
   `spinFProfile_le_spinCalNorm`: `L¹` comparison between `∫_{aJ}^{bJ} spinFProfile` and `spinCalNorm`.
3. `spin_neg_mass_ge_third`, `spinWc_mul_le_exp_s4`, `spinWc_mul_ge_cFc`: negative weighted mass
   lower bound and Cardy weight comparisons near `ξ_*`.
4. `spinHProfile_ofReal_eq`, `spin_neg_mass_box_lower`, `spinHProfile_err_integral_le`: real-axis
   profile formula, box concentration of `(G)_-`, and `s4:4.1` error bound on compact `u`-intervals.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Spin

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal

/-! ### Section 1: Calibrated positivity and `spinFProfile ≤ spinCalNorm` -/

lemma spinGcal_re_nonneg_of_ge {a x₁ b : ℝ} (ha : 0 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) (hx₁ : 0 ≤ x₁)
    (hgap : ∀ ξ d : ℝ, x₁ ^ 2 ≤ ξ ^ 2 + d ^ 2 → 0 ≤ spinG a Φ (ξ + d) (ξ - d))
    (hb : x₁ ≤ b) :
    0 ≤ (spinGcal a Φ (b : ℂ)).re := by
  rw [spinGcal_re_ofReal ha hΦ b]
  refine mul_nonneg (by positivity) (integral_nonneg fun d => ?_)
  refine mul_nonneg (spinHbCalReal_nonneg b d) (hgap b d ?_)
  have hb2 : x₁ ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hx₁ hb 2
  linarith [sq_nonneg d]

lemma spinHbCalReal_pos_lower_near_tip :
    ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ b ∈ Icc (xiStar / 2) (2 * xiStar),
        ∀ d ∈ Icc (-(xiStar / 4)) (xiStar / 4), h₀ ≤ spinHbCalReal b d := by
  let K : Set (ℝ × ℝ) := Icc (xiStar / 2) (2 * xiStar) ×ˢ Icc (-(xiStar / 4)) (xiStar / 4)
  have hK_comp : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hK_ne : K.Nonempty :=
    ⟨(xiStar, 0), ⟨by linarith [xiStar_pos], by linarith [xiStar_pos]⟩,
      ⟨by linarith [xiStar_pos], by linarith [xiStar_pos]⟩⟩
  have hcont : ContinuousOn (fun p : ℝ × ℝ => spinHbCalReal p.1 p.2) K := by
    have hth : Continuous Real.tanh := by
      have heq : Real.tanh = fun x => Real.sinh x / Real.cosh x := funext Real.tanh_eq_sinh_div_cosh
      rw [heq]
      exact Real.continuous_sinh.div Real.continuous_cosh fun x => (Real.cosh_pos x).ne'
    have hfull : Continuous (fun p : ℝ × ℝ => spinHbCalReal p.1 p.2) := by
      unfold spinHbCalReal spinCalFac
      refine Continuous.mul (Continuous.mul (Continuous.div_const (Continuous.mul ?_ ?_) _) ?_) ?_
      · exact continuous_const.div (continuous_const.add (continuous_fst.pow 2)) fun p =>
          (add_pos_of_pos_of_nonneg one_pos (sq_nonneg p.1)).ne'
      · exact ((hth.comp ((continuous_fst.add continuous_snd).div_const 2)).pow 2).mul
          ((hth.comp ((continuous_fst.sub continuous_snd).div_const 2)).pow 2)
      · exact Real.continuous_exp.comp ((continuous_snd.pow 2).div_const _).neg
      · exact Real.continuous_exp.comp
          (((continuous_const.mul ((continuous_fst.pow 2).sub continuous_const)).div_const _).sub
            (((continuous_fst.pow 2).sub continuous_const).pow 2))
    exact hfull.continuousOn
  obtain ⟨⟨b₀, d₀⟩, hbd₀, hmin⟩ := hK_comp.exists_isMinOn hK_ne hcont
  have hpos : 0 < spinHbCalReal b₀ d₀ := by
    have hb₀ : xiStar / 2 ≤ b₀ ∧ b₀ ≤ 2 * xiStar := hbd₀.1
    have hd₀ : -(xiStar / 4) ≤ d₀ ∧ d₀ ≤ xiStar / 4 := hbd₀.2
    have hbp : 0 < (b₀ + d₀) / 2 := by linarith only [hb₀.1, hd₀.1, xiStar_pos]
    have hbm : 0 < (b₀ - d₀) / 2 := by linarith only [hb₀.1, hd₀.2, xiStar_pos]
    have hxs : 0 < Real.tanh (xiStar / 2) := spinTanh_pos (half_pos xiStar_pos)
    have htp : 0 < Real.tanh ((b₀ + d₀) / 2) := spinTanh_pos hbp
    have htm : 0 < Real.tanh ((b₀ - d₀) / 2) := spinTanh_pos hbm
    unfold spinHbCalReal spinCalFac
    exact mul_pos (mul_pos (div_pos (mul_pos (div_pos (add_pos_of_pos_of_nonneg one_pos (sq_nonneg xiStar))
      (add_pos_of_pos_of_nonneg one_pos (sq_nonneg b₀)))
      (mul_pos (pow_pos htp 2) (pow_pos htm 2))) (pow_pos hxs 4))
      (Real.exp_pos _)) (Real.exp_pos _)
  exact ⟨spinHbCalReal b₀ d₀, hpos, fun b hb d hd => isMinOn_iff.mp hmin (b, d) ⟨hb, hd⟩⟩

lemma integrable_spinCalInt_integrand {c : ℝ} (hc : 40 ≤ c) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass ((c - 1) / 12) Φ) :
    let n := c - 1
    let a := n / 12
    Integrable (fun b : ℝ => a * Real.exp (n * spinL b) * (spinGcal a Φ (b : ℂ)).re) := by
  intro n a
  have ha0 : 0 ≤ a := by dsimp [a, n]; linarith
  have hG_meas : Measurable (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) := by
    unfold spinG
    exact (hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk
      (continuous_const.mul continuous_snd))).measurable
  have hadj := spinCal_adjoint_identity hc hΦ hG_meas (fun _ => le_rfl)
    (fun x y => spinG_d4_neg_left hΦ x y) (fun x y => spinG_d4_neg_right hΦ x y)
    (φ := fun _ : ℝ => (1 : ℝ)) measurable_const zero_le_one (fun _ => by norm_num)
  have hprod_int : Integrable (fun p : ℝ × ℝ =>
      a * Real.exp (n * spinL p.1) *
        (4 * spinCalF xiStar ^ 2 * spinHbCalReal p.1 p.2 * spinG a Φ (p.1 + p.2) (p.1 - p.2)))
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hadj.1.congr (Eventually.of_forall fun p => by dsimp only; ring)
  have hleft := hprod_int.integral_prod_left
  refine hleft.congr (Eventually.of_forall fun b => ?_)
  dsimp only
  rw [spinGcal_re_ofReal ha0 hΦ b, ← mul_assoc, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun d => ?_)
  ring

lemma integrable_spinCalNorm_integrand {c : ℝ} (hc : 40 ≤ c) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass ((c - 1) / 12) Φ) :
    let n := c - 1
    let a := n / 12
    Integrable (fun b : ℝ => a * Real.exp (n * spinL b) * |(spinGcal a Φ (b : ℂ)).re|) := by
  intro n a
  have ha0 : 0 ≤ a := by dsimp [a, n]; linarith
  refine (integrable_spinCalInt_integrand hc hΦ).abs.congr (Eventually.of_forall fun b => ?_)
  dsimp only
  have hcoef : 0 ≤ a * Real.exp (n * spinL b) := mul_nonneg ha0 (Real.exp_pos _).le
  rw [abs_mul, abs_of_nonneg hcoef]

lemma spinFProfile_le_spinCalNorm {c aJ bJ : ℝ} (hc : 49 ≤ c) (_hab : aJ < bJ)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass ((c - 1) / 12) Φ) :
    ∫ u in Icc aJ bJ, spinFProfile c Φ u ≤ spinCalNorm c Φ := by
  let n := c - 1
  let a := n / 12
  let ε := n ^ (-(2 / 3 : ℝ))
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have ha_nn : 0 ≤ a := by dsimp [a]; linarith
  have hε_pos : 0 < ε := Real.rpow_pos_of_pos hn_pos _
  let Fb : ℝ → ℝ := fun b => a * Real.exp (n * spinL b) * (spinGcal a Φ (b : ℂ)).re
  let FbAbs : ℝ → ℝ := fun b => a * Real.exp (n * spinL b) * |(spinGcal a Φ (b : ℂ)).re|
  let e : ℝ ≃ᵐ ℝ :=
    (MeasurableEquiv.mulLeft₀ ε hε_pos.ne').trans (MeasurableEquiv.addLeft xiStar)
  have he_apply : ∀ u : ℝ, e u = xiStar + ε * u := fun u => by simp [e]
  have he_pre : e ⁻¹' Icc (xiStar + ε * aJ) (xiStar + ε * bJ) = Icc aJ bJ := by
    ext u
    rw [Set.mem_preimage, he_apply, Set.mem_Icc, Set.mem_Icc]
    constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> nlinarith
  let e1 : ℝ ≃ᵐ ℝ := MeasurableEquiv.mulLeft₀ ε hε_pos.ne'
  let e2 : ℝ ≃ᵐ ℝ := MeasurableEquiv.addLeft xiStar
  have he1 : Measure.map e1 (volume : Measure ℝ) = ENNReal.ofReal ε⁻¹ • (volume : Measure ℝ) := by
    have h := Real.map_volume_mul_left hε_pos.ne'
    rwa [abs_of_pos (inv_pos.mpr hε_pos)] at h
  have he2 : Measure.map e2 (volume : Measure ℝ) = (volume : Measure ℝ) :=
    (MeasureTheory.measurePreserving_add_left volume xiStar).map_eq
  have hcov : ∫ u in Icc aJ bJ, spinFProfile c Φ u =
      ∫ b in Icc (xiStar + ε * aJ) (xiStar + ε * bJ), Fb b := by
    rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc]
    let g_ind : ℝ → ℝ := (Icc (xiStar + ε * aJ) (xiStar + ε * bJ)).indicator (fun b => ε * Fb b)
    have hlhs : ∫ u : ℝ, (Icc aJ bJ).indicator (spinFProfile c Φ) u =
        ∫ u : ℝ, g_ind (e2 (e1 u)) := by
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      dsimp only
      have hee : e2 (e1 u) = e u := rfl
      rw [hee]
      by_cases hu : u ∈ Icc aJ bJ
      · have heu : e u ∈ Icc (xiStar + ε * aJ) (xiStar + ε * bJ) := by rwa [← he_pre] at hu
        dsimp [g_ind]
        rw [Set.indicator_of_mem hu, Set.indicator_of_mem heu, he_apply]
        unfold spinFProfile; dsimp only [Fb, n, a, ε]; ring
      · have heu : e u ∉ Icc (xiStar + ε * aJ) (xiStar + ε * bJ) := by rwa [← he_pre] at hu
        dsimp [g_ind]
        rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem heu]
    have hmap1 : ∫ u : ℝ, g_ind (e2 (e1 u)) = ∫ x : ℝ, g_ind (e2 x) ∂(Measure.map e1 volume) :=
      (integral_map_equiv e1 (fun x => g_ind (e2 x))).symm
    have hmap2 : ∫ x : ℝ, g_ind (e2 x) = ∫ b : ℝ, g_ind b := by
      simpa [e2] using integral_add_left_eq_self g_ind xiStar
    rw [hlhs, hmap1, he1, integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.mpr hε_pos).le,
      smul_eq_mul, hmap2, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun b => ?_)
    dsimp only [g_ind]
    by_cases hb : b ∈ Icc (xiStar + ε * aJ) (xiStar + ε * bJ)
    · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb]
      field_simp [hε_pos.ne']
    · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb, mul_zero]
  have hc40 : 40 ≤ c := by linarith
  have hFb_int : Integrable Fb := integrable_spinCalInt_integrand hc40 hΦ
  have hFbAbs_int : Integrable FbAbs := integrable_spinCalNorm_integrand hc40 hΦ
  have hpt : ∀ b : ℝ, Fb b ≤ FbAbs b := fun b =>
    mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg ha_nn (Real.exp_pos _).le)
  have hmono1 : ∫ b in Icc (xiStar + ε * aJ) (xiStar + ε * bJ), Fb b ≤
      ∫ b in Icc (xiStar + ε * aJ) (xiStar + ε * bJ), FbAbs b :=
    setIntegral_mono hFb_int.integrableOn hFbAbs_int.integrableOn hpt
  have hmono2 : ∫ b in Icc (xiStar + ε * aJ) (xiStar + ε * bJ), FbAbs b ≤ ∫ b : ℝ, FbAbs b :=
    setIntegral_le_integral hFbAbs_int (Eventually.of_forall fun b =>
      mul_nonneg (mul_nonneg ha_nn (Real.exp_pos _).le) (abs_nonneg _))
  rw [hcov]
  exact hmono1.trans (hmono2.trans_eq rfl)

/-! ### Section 2: Negative weighted mass and Cardy weights near `ξ_*` -/

lemma spin_neg_mass_ge_third {c x₁ : ℝ} (hc : 49 ≤ c) {Φ : ℝ × ℝ → ℝ}
    (hS : SpinSlackHyp c x₁ Φ) :
    let n := c - 1
    let a := n / 12
    1 / 3 ≤ ∫ p : ℝ × ℝ, max (-spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2 := by
  intro n a
  rcases hS with ⟨_, hΦ, hM2, hvac, _⟩
  have hn_ge : 48 ≤ n := by dsimp [n]; linarith
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have ha0 : 0 < a := by linarith
  have h_abs_int : Integrable (fun p : ℝ × ℝ => |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) :=
    integrable_spinG_wc ha0 hΦ
  have h_g_int : Integrable (fun p : ℝ × ℝ => spinG a Φ p.1 p.2 * spinWc a p.1 * spinWc a p.2) := by
    refine h_abs_int.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hWc : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
      have hGc : Continuous (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) := by
        unfold spinG; exact hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk
          (continuous_const.mul continuous_snd))
      exact ((hGc.mul (hWc.comp continuous_fst)).mul (hWc.comp continuous_snd)).aestronglyMeasurable
    · have hw1 := spinWc_nonneg ha2.le p.1
      have hw2 := spinWc_nonneg ha2.le p.2
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw1, abs_of_nonneg hw2]
  have hsplit : (fun p : ℝ × ℝ => max (-spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2) =
      fun p : ℝ × ℝ => (1 / 2 : ℝ) * (|spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 -
        spinG a Φ p.1 p.2 * spinWc a p.1 * spinWc a p.2) := by
    ext p
    have hmax : max (-spinG a Φ p.1 p.2) 0 = (|spinG a Φ p.1 p.2| - spinG a Φ p.1 p.2) / 2 := by
      rcases le_total (spinG a Φ p.1 p.2) 0 with h | h
      · rw [max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h]; ring
      · rw [max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h]; ring
    rw [hmax]; ring
  rw [hsplit, integral_const_mul, integral_sub h_abs_int h_g_int,
    ← spinM2_eq_spinWc ha0 Φ, hM2]
  have hvac' := hvac
  rw [spinPhiVac_eq_spinWc ha0 Φ] at hvac'
  have hn_inv : n⁻¹ ≤ (48 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hn_ge
  change -(n⁻¹) ≤ _ at hvac'
  linarith

lemma spinWc_mul_le_exp_s4 {a ξ d : ℝ} (ha : 2 < a) (hp : 0 < ξ + d) (hm : 0 < ξ - d) :
    spinWc a (ξ + d) * spinWc a (ξ - d) ≤ a * Real.exp ((12 * a) * (2 * π / 3) * ξ) := by
  have ha0 : 0 < a := by linarith
  have hfc_le1 : ∀ x : ℝ, 0 < x → spinCalFc a x ≤ 1 := fun x hx => by
    unfold spinCalFc
    have hg0 : 0 < spinGamma a := spinGamma_pos ha
    have hg1 : spinGamma a < 1 := spinGamma_lt_one ha
    have hgm : 0 ≤ 1 - spinGamma a := by linarith
    have he1 : 0 ≤ Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3) := (Real.exp_pos _).le
    have he2 : 0 ≤ Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3) := (Real.exp_pos _).le
    have hl1 : Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hpos : 0 ≤ π * (12 * a) * (1 + spinGamma a) * x / 3 := by positivity
      linarith
    have hl2 : Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hpos : 0 ≤ π * (12 * a) * (1 - spinGamma a) * x / 3 := by positivity
      linarith
    nlinarith
  have hfc_nn : ∀ x : ℝ, 0 < x → 0 ≤ spinCalFc a x := fun x hx => (spinCalFc_pos_of_pos ha hx).le
  rw [spinWc_factorization ha.le (ξ + d), spinWc_factorization ha.le (ξ - d),
    abs_of_pos hp, abs_of_pos hm]
  have hexp : (Real.sqrt a * Real.exp (4 * π * a * (ξ + d)) * spinCalFc a (ξ + d)) *
      (Real.sqrt a * Real.exp (4 * π * a * (ξ - d)) * spinCalFc a (ξ - d)) =
      (a * Real.exp ((12 * a) * (2 * π / 3) * ξ)) * (spinCalFc a (ξ + d) * spinCalFc a (ξ - d)) := by
    have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0.le
    have hex : Real.exp (4 * π * a * (ξ + d)) * Real.exp (4 * π * a * (ξ - d)) =
        Real.exp ((12 * a) * (2 * π / 3) * ξ) := by
      rw [← Real.exp_add]; congr 1; ring
    calc (Real.sqrt a * Real.exp (4 * π * a * (ξ + d)) * spinCalFc a (ξ + d)) *
          (Real.sqrt a * Real.exp (4 * π * a * (ξ - d)) * spinCalFc a (ξ - d))
        = (Real.sqrt a * Real.sqrt a) *
            (Real.exp (4 * π * a * (ξ + d)) * Real.exp (4 * π * a * (ξ - d))) *
            (spinCalFc a (ξ + d) * spinCalFc a (ξ - d)) := by ring
      _ = _ := by rw [hsq, hex]
  rw [hexp]
  have hprod_le1 : spinCalFc a (ξ + d) * spinCalFc a (ξ - d) ≤ 1 :=
    (mul_le_mul (hfc_le1 _ hp) (hfc_le1 _ hm) (hfc_nn _ hm) zero_le_one).trans_eq (one_mul 1)
  exact mul_le_of_le_one_right (mul_nonneg ha0.le (Real.exp_pos _).le) hprod_le1

lemma spinWc_mul_ge_cFc {a ξ d : ℝ} (ha : 2 < a) (hp : xiStar / 4 ≤ ξ + d) (hm : xiStar / 4 ≤ ξ - d) :
    (1 - Real.exp (-π * xiStar)) ^ 4 * (a * Real.exp ((12 * a) * (2 * π / 3) * ξ)) ≤
      spinWc a (ξ + d) * spinWc a (ξ - d) := by
  have ha0 : 0 < a := by linarith
  have hp_pos : 0 < ξ + d := by linarith [xiStar_pos]
  have hm_pos : 0 < ξ - d := by linarith [xiStar_pos]
  have hfc_lb : ∀ x : ℝ, xiStar / 4 ≤ x → (1 - Real.exp (-π * xiStar)) ^ 2 ≤ spinCalFc a x := fun x hx => by
    unfold spinCalFc
    have hg0 : 0 < spinGamma a := spinGamma_pos ha
    have hg1 : spinGamma a < 1 := spinGamma_lt_one ha
    have hgm_ge : (12 * a) * (1 - spinGamma a) ≥ 12 := by
      have hsq : (1 - spinGamma a) * (1 + spinGamma a) = 2 / a := by
        rw [show (1 - spinGamma a) * (1 + spinGamma a) = 1 - spinGamma a ^ 2 by ring,
          spinGamma_sq ha.le]; ring
      have h1 : 12 * a * (1 - spinGamma a) * (1 + spinGamma a) = 24 := by
        rw [mul_assoc, hsq]; field_simp [ha0.ne']; norm_num
      nlinarith
    have hgp_ge : (12 * a) * (1 + spinGamma a) ≥ 12 := by nlinarith
    have hx_pos : 0 < x := by linarith [xiStar_pos]
    have harg1 : π * xiStar ≤ π * (12 * a) * (1 + spinGamma a) * x / 3 := by
      have h1 : π * (12 * a) * (1 + spinGamma a) * x / 3 =
          π * x * ((12 * a) * (1 + spinGamma a)) / 3 := by ring
      rw [h1]
      have h2 : π * x * 12 / 3 ≤ π * x * ((12 * a) * (1 + spinGamma a)) / 3 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hgp_ge
          (mul_nonneg Real.pi_pos.le hx_pos.le)) (by norm_num)
      linarith [show π * xiStar ≤ π * x * 12 / 3 by nlinarith [Real.pi_pos]]
    have harg2 : π * xiStar ≤ π * (12 * a) * (1 - spinGamma a) * x / 3 := by
      have h1 : π * (12 * a) * (1 - spinGamma a) * x / 3 =
          π * x * ((12 * a) * (1 - spinGamma a)) / 3 := by ring
      rw [h1]
      have h2 : π * x * 12 / 3 ≤ π * x * ((12 * a) * (1 - spinGamma a)) / 3 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hgm_ge
          (mul_nonneg Real.pi_pos.le hx_pos.le)) (by norm_num)
      linarith [show π * xiStar ≤ π * x * 12 / 3 by nlinarith [Real.pi_pos]]
    have he1 : 1 - Real.exp (-π * xiStar) ≤
        1 - Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3) := by
      have h := Real.exp_le_exp.mpr (show -π * (12 * a) * (1 + spinGamma a) * x / 3 ≤ -π * xiStar by linarith)
      linarith
    have he2 : 1 - Real.exp (-π * xiStar) ≤
        1 - Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3) := by
      have h := Real.exp_le_exp.mpr (show -π * (12 * a) * (1 - spinGamma a) * x / 3 ≤ -π * xiStar by linarith)
      linarith
    have hc_nn : 0 ≤ 1 - Real.exp (-π * xiStar) := by
      rw [sub_nonneg, Real.exp_le_one_iff]; nlinarith [Real.pi_pos, xiStar_pos]
    rw [sq]
    exact mul_le_mul he1 he2 hc_nn (hc_nn.trans he1)
  rw [spinWc_factorization ha.le (ξ + d), spinWc_factorization ha.le (ξ - d),
    abs_of_pos hp_pos, abs_of_pos hm_pos]
  have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0.le
  have hex : Real.exp (4 * π * a * (ξ + d)) * Real.exp (4 * π * a * (ξ - d)) =
      Real.exp ((12 * a) * (2 * π / 3) * ξ) := by
    rw [← Real.exp_add]; congr 1; ring
  have hexp : (Real.sqrt a * Real.exp (4 * π * a * (ξ + d)) * spinCalFc a (ξ + d)) *
      (Real.sqrt a * Real.exp (4 * π * a * (ξ - d)) * spinCalFc a (ξ - d)) =
      (spinCalFc a (ξ + d) * spinCalFc a (ξ - d)) * (a * Real.exp ((12 * a) * (2 * π / 3) * ξ)) := by
    calc (Real.sqrt a * Real.exp (4 * π * a * (ξ + d)) * spinCalFc a (ξ + d)) *
          (Real.sqrt a * Real.exp (4 * π * a * (ξ - d)) * spinCalFc a (ξ - d))
        = (spinCalFc a (ξ + d) * spinCalFc a (ξ - d)) *
            ((Real.sqrt a * Real.sqrt a) *
              (Real.exp (4 * π * a * (ξ + d)) * Real.exp (4 * π * a * (ξ - d)))) := by ring
      _ = _ := by rw [hsq, hex]
  rw [hexp]
  have h1 := hfc_lb _ hp
  have h2 := hfc_lb _ hm
  have hc_sq_nn : 0 ≤ (1 - Real.exp (-π * xiStar)) ^ 2 := sq_nonneg _
  have hc4_le : (1 - Real.exp (-π * xiStar)) ^ 4 ≤ spinCalFc a (ξ + d) * spinCalFc a (ξ - d) := by
    rw [show (1 - Real.exp (-π * xiStar)) ^ 4 =
      (1 - Real.exp (-π * xiStar)) ^ 2 * (1 - Real.exp (-π * xiStar)) ^ 2 by ring]
    exact mul_le_mul h1 h2 hc_sq_nn (hc_sq_nn.trans h1)
  exact mul_le_mul_of_nonneg_right hc4_le (mul_nonneg ha0.le (Real.exp_pos _).le)

/-! ### Section 3: Real-axis profile representation and box change of variables -/

lemma continuous_spinTruncInv_s4_3 {a : ℝ} {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ)
    (N : ℕ) : Continuous (fun p : ℝ × ℝ => spinTruncInv a N Φ p.1 p.2) := by
  have hG_cont : Continuous (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) := by
    unfold spinG
    exact hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
  have hsc : ∀ c1 c2 : ℝ, Continuous (fun p : ℝ × ℝ => spinG a Φ (c1 * p.1) (c2 * p.2)) := fun c1 c2 =>
    hG_cont.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
  have hsum : ∀ (M : ℕ) (f : ℕ → ℝ × ℝ → ℝ),
      (∀ k, Continuous (f k)) → Continuous (fun x => ∑ k ∈ Finset.range M, f k x) := by
    intro M f hf
    induction M with
    | zero => simp; exact continuous_const
    | succ k ih => simp_rw [Finset.sum_range_succ]; exact ih.add (hf k)
  unfold spinTruncInv
  refine hsum N _ fun j => hsum N _ fun ℓ => ?_
  simp only [spinDeltaA, spinDa, ← mul_assoc]
  exact (((hsc _ _).sub (hsc _ _)).sub (hsc _ _)).add (hsc _ _)

lemma spinTruncInvC_ofReal_s4_3 {a : ℝ} (ha : 2 ≤ a) (N : ℕ) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) (xL xR : ℝ) :
    spinTruncInvC a N Φ (xL : ℂ) (xR : ℂ) = (spinTruncInv a N Φ xL xR : ℂ) := by
  unfold spinTruncInvC spinTruncInv spinDeltaAC spinDeltaA
  simp only [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ℓ _ => ?_
  have h1 : (spinLambda a : ℂ) * ((spinLambda a ^ j : ℝ) : ℂ) * (xL : ℂ) =
      (((spinLambda a * (spinLambda a ^ j * xL) : ℝ)) : ℂ) := by push_cast; ring
  have h2 : (spinLambda a : ℂ) * ((spinLambda a ^ ℓ : ℝ) : ℂ) * (xR : ℂ) =
      (((spinLambda a * (spinLambda a ^ ℓ * xR) : ℝ)) : ℂ) := by push_cast; ring
  rw [← mul_assoc, ← mul_assoc, h1, h2]
  exact spinDaC_eq_spinDa ha hΦ _ _

lemma spinHProfile_ofReal_eq {c V : ℝ} (hc : 49 ≤ c) (hV : 0 < V) (N : ℕ)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass ((c - 1) / 12) Φ) {χ : ℝ → ℝ}
    (hχ_meas : Measurable χ) (hχ_bd : ∀ v : ℝ, 0 ≤ χ v ∧ χ v ≤ 1)
    (hχ_supp : ∀ v : ℝ, V < |v| → χ v = 0) (u : ℝ) :
    let n := c - 1
    let a := n / 12
    let ε := n ^ (-(2 / 3 : ℝ))
    Integrable (fun d : ℝ =>
      χ (d / Real.sqrt ε) * spinTruncInv a N Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d)) ∧
    (spinHProfile c N Φ χ (u : ℂ)).im = 0 ∧
    (spinHProfile c N Φ χ (u : ℂ)).re =
      ε * a * Real.exp (n * (2 * π / 3) * (xiStar + ε * u)) *
        ∫ d : ℝ, χ (d / Real.sqrt ε) *
          spinTruncInv a N Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d) := by
  intro n a ε
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have hε_pos : 0 < ε := Real.rpow_pos_of_pos hn_pos _
  let W : ℝ := V * Real.sqrt ε
  let g_real : ℝ → ℝ := fun d =>
    χ (d / Real.sqrt ε) * spinTruncInv a N Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d)
  have hpair : Continuous (fun d : ℝ => ((xiStar + ε * u) + d, (xiStar + ε * u) - d)) :=
    (continuous_const.add continuous_id).prodMk (continuous_const.sub continuous_id)
  have hcont_tr : Continuous (fun d : ℝ => spinTruncInv a N Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d)) := by
    change Continuous ((fun p : ℝ × ℝ => spinTruncInv a N Φ p.1 p.2) ∘
      fun d : ℝ => ((xiStar + ε * u) + d, (xiStar + ε * u) - d))
    exact (continuous_spinTruncInv_s4_3 hΦ N).comp hpair
  have hg_int : Integrable g_real := by
    have hcomp : IntegrableOn (fun d : ℝ => spinTruncInv a N Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d)) (Icc (-W) W) :=
      hcont_tr.continuousOn.integrableOn_Icc
    have hW_nn : 0 ≤ W := mul_nonneg hV.le (Real.sqrt_nonneg _)
    have hm : AEStronglyMeasurable g_real volume :=
      ((hχ_meas.comp (measurable_id.div_const _)).mul hcont_tr.measurable).aestronglyMeasurable
    refine (hcomp.integrable_indicator measurableSet_Icc).mono hm (Eventually.of_forall fun d => ?_)
    dsimp only [g_real]
    by_cases hd : d ∈ Icc (-W) W
    · rw [Set.indicator_of_mem hd, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      have hχ1 : |χ (d / Real.sqrt ε)| ≤ 1 := by
        have h := hχ_bd (d / Real.sqrt ε); exact abs_le.mpr ⟨by linarith, h.2⟩
      exact mul_le_of_le_one_left (abs_nonneg _) hχ1
    · have hnot : V < |d / Real.sqrt ε| := by
        have hsq_pos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε_pos
        rw [abs_div, abs_of_pos hsq_pos, lt_div_iff₀ hsq_pos]
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hd
        rcases hd with h1 | h2
        · rw [abs_of_neg (by linarith only [h1, hW_nn])]; linarith only [h1]
        · rw [abs_of_nonneg (by linarith only [h2, hW_nn])]; linarith only [h2]
      rw [Set.indicator_of_notMem hd, hχ_supp _ hnot, zero_mul, norm_zero]
  have hofReal_int : ∀ d : ℝ,
      (χ (d / Real.sqrt ε) : ℂ) * spinTruncInvC a N Φ
        (((xiStar + ε * u : ℝ) : ℂ) + (d : ℂ)) (((xiStar + ε * u : ℝ) : ℂ) - (d : ℂ)) =
        ((g_real d : ℝ) : ℂ) := fun d => by
    have hp : ((xiStar + ε * u : ℝ) : ℂ) + (d : ℂ) = (((xiStar + ε * u) + d : ℝ) : ℂ) := by push_cast; rfl
    have hm : ((xiStar + ε * u : ℝ) : ℂ) - (d : ℂ) = (((xiStar + ε * u) - d : ℝ) : ℂ) := by push_cast; rfl
    rw [hp, hm, spinTruncInvC_ofReal_s4_3 ha2.le N hΦ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d)]
    dsimp only [g_real]; push_cast; rfl
  have hQ_eq : spinQSlice c N Φ χ ((xiStar + ε * u : ℝ) : ℂ) = ((∫ d : ℝ, g_real d : ℝ) : ℂ) := by
    unfold spinQSlice
    dsimp only
    rw [integral_congr_ae (Eventually.of_forall hofReal_int)]
    exact Complex.ofRealCLM.integral_comp_comm hg_int
  let I_val : ℝ := ∫ d : ℝ, g_real d
  have hH_eq : spinHProfile c N Φ χ (u : ℂ) =
      ((ε * a * Real.exp (n * (2 * π / 3) * (xiStar + ε * u)) * I_val : ℝ) : ℂ) := by
    unfold spinHProfile
    dsimp only
    have hb_eq : (xiStar : ℂ) + (ε : ℂ) * (u : ℂ) = ((xiStar + ε * u : ℝ) : ℂ) := by push_cast; rfl
    rw [hb_eq, hQ_eq]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
    change _ = ((ε * a * Real.exp (n * (2 * π / 3) * (xiStar + ε * u)) * I_val : ℝ) : ℂ)
    rw [← Complex.ofReal_mul]
  exact ⟨hg_int, by rw [hH_eq, Complex.ofReal_im], by rw [hH_eq, Complex.ofReal_re]⟩


lemma lt_div_sqrt_of_notMem_Icc {d V ε : ℝ} (hV : 0 ≤ V) (hε : 0 < ε)
    (hd : d ∉ Icc (-(V * Real.sqrt ε)) (V * Real.sqrt ε)) :
    V < |d / Real.sqrt ε| := by
  have hsq_pos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hW_nn : 0 ≤ V * Real.sqrt ε := mul_nonneg hV hsq_pos.le
  rw [abs_div, abs_of_pos hsq_pos, lt_div_iff₀ hsq_pos]
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hd
  rcases hd with h1 | h2
  · rw [abs_of_neg (by linarith only [h1, hW_nn])]; linarith only [h1]
  · rw [abs_of_nonneg (by linarith only [h2, hW_nn])]; linarith only [h2]

lemma exp_decay_ceil_log_tendsto {α : ℝ} (hα : 0 < α) :
    Tendsto (fun c : ℝ => ((Nat.ceil (Real.log (c - 1)) : ℝ) + 1) *
      Real.exp (-α * (Nat.ceil (Real.log (c - 1)) : ℝ))) atTop (𝓝 0) := by
  let g : ℝ → ℝ := fun c => (2 / α + 1) * (c - 1) ^ (-(α / 2))
  have hg : Tendsto g atTop (𝓝 0) := by
    have hsub : Tendsto (fun c : ℝ => c - 1) atTop atTop :=
      Filter.Tendsto.atTop_add tendsto_id tendsto_const_nhds
    have ht : Tendsto (fun c : ℝ => (c - 1) ^ (-(α / 2))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (half_pos hα)).comp hsub
    simpa [g] using ht.const_mul (2 / α + 1)
  have hbd : ∀ᶠ c : ℝ in atTop,
      ((Nat.ceil (Real.log (c - 1)) : ℝ) + 1) *
        Real.exp (-α * (Nat.ceil (Real.log (c - 1)) : ℝ)) ∈ Icc 0 (g c) := by
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with c hc
    have hlog_pos : 0 < Real.log (c - 1) := Real.log_pos (by linarith)
    let N : ℕ := Nat.ceil (Real.log (c - 1))
    have hN_ge : Real.log (c - 1) ≤ (N : ℝ) := Nat.le_ceil _
    have hc_pos : 0 < c - 1 := by linarith
    have hnonneg : 0 ≤ ((N : ℝ) + 1) * Real.exp (-α * (N : ℝ)) := by positivity
    have h1 : (N : ℝ) * (α / 2) + 1 ≤ Real.exp ((α / 2) * (N : ℝ)) := by
      simpa [mul_comm] using Real.add_one_le_exp ((α / 2) * (N : ℝ))
    have h2 : ((N : ℝ) + 1) * Real.exp (-(α / 2) * (N : ℝ)) ≤ 2 / α + 1 := by
      have hdiv : ((N : ℝ) + 1) ≤ (2 / α + 1) * ((N : ℝ) * (α / 2) + 1) := by
        have hN_nn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
        have h1' : (N : ℝ) * 1 ≤ (N : ℝ) * ((2 / α) * (α / 2)) + 1 + (2 / α) * (N : ℝ) * (α / 2) := by
          have hne : α ≠ 0 := hα.ne'
          field_simp [hne]
          nlinarith [mul_nonneg hN_nn hα.le]
        have hmul : (2 / α + 1) * ((N : ℝ) * (α / 2) + 1) =
            (N : ℝ) + (2 / α) + 1 + (N : ℝ) * (α / 2) := by
          field_simp [hα.ne']; ring
        rw [hmul]
        nlinarith [div_pos two_pos hα, mul_nonneg hN_nn hα.le]
      have hexp_pos : 0 < Real.exp ((α / 2) * (N : ℝ)) := Real.exp_pos _
      calc ((N : ℝ) + 1) * Real.exp (-(α / 2) * (N : ℝ))
          = ((N : ℝ) + 1) * (Real.exp ((α / 2) * (N : ℝ)))⁻¹ := by
              rw [show -(α / 2) * (N : ℝ) = -((α / 2) * (N : ℝ)) by ring, Real.exp_neg]
        _ ≤ (2 / α + 1) * Real.exp ((α / 2) * (N : ℝ)) * (Real.exp ((α / 2) * (N : ℝ)))⁻¹ := by
              have ha := hdiv.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
              exact mul_le_mul_of_nonneg_right ha (inv_pos.mpr hexp_pos).le
        _ = 2 / α + 1 := by
              rw [mul_assoc, mul_inv_cancel₀ hexp_pos.ne', mul_one]
    have h3 : Real.exp (-(α / 2) * (N : ℝ)) ≤ (c - 1) ^ (-(α / 2)) := by
      rw [Real.rpow_def_of_pos hc_pos, Real.exp_le_exp]
      nlinarith
    have hsplit : ((N : ℝ) + 1) * Real.exp (-α * (N : ℝ)) =
        (((N : ℝ) + 1) * Real.exp (-(α / 2) * (N : ℝ))) * Real.exp (-(α / 2) * (N : ℝ)) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    refine ⟨hnonneg, ?_⟩
    rw [hsplit]
    exact mul_le_mul h2 h3 (Real.exp_pos _).le (by positivity)
  exact squeeze_zero' (hbd.mono fun _ h => h.1) (hbd.mono fun _ h => h.2) hg

lemma adaptive_chi_H_lower {c V u : ℝ} (hc : 49 ≤ c) (hV : 0 < V)
    (N : ℕ) {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass ((c - 1) / 12) Φ) (ξ : ℝ) :
    let n := c - 1
    let a := n / 12
    let ε := n ^ (-(2 / 3 : ℝ))
    let χ : ℝ → ℝ := (Icc (-V) V).indicator fun v =>
      if spinG a Φ (ξ + Real.sqrt ε * v) (ξ - Real.sqrt ε * v) < 0 then 1 else 0
    Measurable χ ∧ (∀ v, 0 ≤ χ v ∧ χ v ≤ 1) ∧ (∀ v, V < |v| → χ v = 0) ∧
    (ξ = xiStar + ε * u →
      (spinHProfile c N Φ χ (u : ℂ)).re ≤
        -(ε * a * Real.exp (n * (2 * π / 3) * (xiStar + ε * u)) *
          ∫ d in Icc (-(V * Real.sqrt ε)) (V * Real.sqrt ε),
            max (-spinG a Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d)) 0) +
        (ε * a * Real.exp (n * (2 * π / 3) * (xiStar + ε * u)) *
          ∫ d in Icc (-(V * Real.sqrt ε)) (V * Real.sqrt ε),
            |spinG a Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d) -
              spinTruncInv a N Φ ((xiStar + ε * u) + d) ((xiStar + ε * u) - d)|)) := by
  intro n a ε χ
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have ha0 : 0 < a := by linarith
  have hε_pos : 0 < ε := Real.rpow_pos_of_pos hn_pos _
  have hsq_pos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε_pos
  have hGc : Continuous (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) := by
    unfold spinG; exact hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk
      (continuous_const.mul continuous_snd))
  have hmeas : Measurable χ := by
    have hcont : Continuous (fun v : ℝ => spinG a Φ (ξ + Real.sqrt ε * v) (ξ - Real.sqrt ε * v)) :=
      hGc.comp ((continuous_const.add (continuous_const.mul continuous_id)).prodMk
        (continuous_const.sub (continuous_const.mul continuous_id)))
    let S_neg : Set ℝ := {v : ℝ | spinG a Φ (ξ + Real.sqrt ε * v) (ξ - Real.sqrt ε * v) < 0}
    have hS : MeasurableSet S_neg := (isOpen_lt hcont continuous_const).measurableSet
    have hfun : (fun v : ℝ => if spinG a Φ (ξ + Real.sqrt ε * v) (ξ - Real.sqrt ε * v) < 0 then
        (1 : ℝ) else 0) = S_neg.indicator 1 := by
      ext v; by_cases hv : spinG a Φ (ξ + Real.sqrt ε * v) (ξ - Real.sqrt ε * v) < 0 <;> simp [S_neg, hv]
    dsimp [χ]; rw [hfun]; exact (measurable_one.indicator hS).indicator measurableSet_Icc
  have hbd : ∀ v, 0 ≤ χ v ∧ χ v ≤ 1 := fun v => by
    dsimp [χ]
    by_cases hv : v ∈ Icc (-V) V
    · rw [Set.indicator_of_mem hv]; split_ifs <;> norm_num
    · rw [Set.indicator_of_notMem hv]; norm_num
  have hsupp : ∀ v, V < |v| → χ v = 0 := fun v hv => by
    dsimp [χ]
    have hnot : v ∉ Icc (-V) V := fun h => by
      have : |v| ≤ V := abs_le.mpr h; linarith
    exact Set.indicator_of_notMem hnot _
  refine ⟨hmeas, hbd, hsupp, fun hξ => ?_⟩
  obtain ⟨_, _, hH_re⟩ := spinHProfile_ofReal_eq hc hV N hΦ hmeas hbd hsupp u
  change (spinHProfile c N Φ χ (u : ℂ)).re = _ at hH_re
  let b : ℝ := xiStar + ε * u
  let W : ℝ := V * Real.sqrt ε
  have hW_nn : 0 ≤ W := mul_nonneg hV.le hsq_pos.le
  have hG_int : IntegrableOn (fun d : ℝ => max (-spinG a Φ (b + d) (b - d)) 0) (Icc (-W) W) :=
    ((hGc.comp ((continuous_const.add continuous_id).prodMk
      (continuous_const.sub continuous_id))).neg.max continuous_const).continuousOn.integrableOn_Icc
  have hpair_b : Continuous (fun d : ℝ => (b + d, b - d)) :=
    (continuous_const.add continuous_id).prodMk (continuous_const.sub continuous_id)
  have hcont_tr_b : Continuous (fun d : ℝ => spinTruncInv a N Φ (b + d) (b - d)) := by
    change Continuous ((fun p : ℝ × ℝ => spinTruncInv a N Φ p.1 p.2) ∘ fun d : ℝ => (b + d, b - d))
    exact (continuous_spinTruncInv_s4_3 hΦ N).comp hpair_b
  have herr_int : IntegrableOn (fun d : ℝ => |spinG a Φ (b + d) (b - d) -
      spinTruncInv a N Φ (b + d) (b - d)|) (Icc (-W) W) :=
    ((hGc.comp hpair_b).sub hcont_tr_b).abs.continuousOn.integrableOn_Icc
  let tr_fn : ℝ → ℝ := fun d => χ (d / Real.sqrt ε) * spinTruncInv a N Φ (b + d) (b - d)
  let g_fn : ℝ → ℝ := fun d => χ (d / Real.sqrt ε) * spinG a Φ (b + d) (b - d)
  have hg_eq_neg : ∀ d : ℝ, g_fn d =
      -(Icc (-W) W).indicator (fun d => max (-spinG a Φ (b + d) (b - d)) 0) d := fun d => by
    dsimp [g_fn]
    by_cases hd : d ∈ Icc (-W) W
    · have hdv : d / Real.sqrt ε ∈ Icc (-V) V := by
        rw [Set.mem_Icc] at hd ⊢; constructor
        · rw [le_div_iff₀ hsq_pos]; linarith
        · rw [div_le_iff₀ hsq_pos]; linarith
      have harg_p : ξ + Real.sqrt ε * (d / Real.sqrt ε) = b + d := by
        dsimp [b]; rw [hξ, mul_div_cancel₀ _ hsq_pos.ne']
      have harg_m : ξ - Real.sqrt ε * (d / Real.sqrt ε) = b - d := by
        dsimp [b]; rw [hξ, mul_div_cancel₀ _ hsq_pos.ne']
      dsimp [χ]
      rw [Set.indicator_of_mem hdv, Set.indicator_of_mem hd, harg_p, harg_m]
      split_ifs with hlt
      · rw [one_mul, max_eq_left (neg_nonneg.mpr hlt.le), neg_neg]
      · have hge : 0 ≤ spinG a Φ (b + d) (b - d) := not_lt.mp hlt
        rw [zero_mul, max_eq_right (neg_nonpos.mpr hge), neg_zero]
    · have hnotv := lt_div_sqrt_of_notMem_Icc hV.le hε_pos hd
      rw [hsupp _ hnotv, Set.indicator_of_notMem hd, zero_mul, neg_zero]
  have hg_full_int : Integrable g_fn := by
    have heq : g_fn = fun d => -(Icc (-W) W).indicator (fun d => max (-spinG a Φ (b + d) (b - d)) 0) d :=
      funext hg_eq_neg
    rw [heq]
    exact (hG_int.integrable_indicator measurableSet_Icc).neg
  have htr_full_int : Integrable tr_fn := by
    have := (spinHProfile_ofReal_eq hc hV N hΦ hmeas hbd hsupp u).1
    exact this
  have hdiff_le : ∫ d : ℝ, (tr_fn d - g_fn d) ≤
      ∫ d in Icc (-W) W, |spinG a Φ (b + d) (b - d) - spinTruncInv a N Φ (b + d) (b - d)| := by
    have hpt : ∀ d : ℝ, tr_fn d - g_fn d ≤
        (Icc (-W) W).indicator (fun d => |spinG a Φ (b + d) (b - d) - spinTruncInv a N Φ (b + d) (b - d)|) d := by
      intro d
      dsimp [tr_fn, g_fn]
      by_cases hd : d ∈ Icc (-W) W
      · rw [Set.indicator_of_mem hd, ← mul_sub]
        have hχ := hbd (d / Real.sqrt ε)
        calc χ (d / Real.sqrt ε) * (spinTruncInv a N Φ (b + d) (b - d) - spinG a Φ (b + d) (b - d))
            ≤ χ (d / Real.sqrt ε) * |spinTruncInv a N Φ (b + d) (b - d) - spinG a Φ (b + d) (b - d)| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) hχ.1
          _ ≤ 1 * |spinTruncInv a N Φ (b + d) (b - d) - spinG a Φ (b + d) (b - d)| :=
              mul_le_mul_of_nonneg_right hχ.2 (abs_nonneg _)
          _ = |spinG a Φ (b + d) (b - d) - spinTruncInv a N Φ (b + d) (b - d)| := by
              rw [one_mul, abs_sub_comm]
      · have hnotv := lt_div_sqrt_of_notMem_Icc hV.le hε_pos hd
        rw [hsupp _ hnotv, Set.indicator_of_notMem hd]; norm_num
    rw [← integral_indicator measurableSet_Icc]
    exact integral_mono (htr_full_int.sub hg_full_int) (herr_int.integrable_indicator measurableSet_Icc) hpt
  have hg_int_val : ∫ d : ℝ, g_fn d =
      -(∫ d in Icc (-W) W, max (-spinG a Φ (b + d) (b - d)) 0) := by
    have heq : g_fn = fun d => -(Icc (-W) W).indicator (fun d => max (-spinG a Φ (b + d) (b - d)) 0) d :=
      funext hg_eq_neg
    rw [heq, integral_neg, integral_indicator measurableSet_Icc]
  have htr_le : ∫ d : ℝ, tr_fn d ≤
      -(∫ d in Icc (-W) W, max (-spinG a Φ (b + d) (b - d)) 0) +
        ∫ d in Icc (-W) W, |spinG a Φ (b + d) (b - d) - spinTruncInv a N Φ (b + d) (b - d)| := by
    have hsub := integral_sub htr_full_int hg_full_int
    linarith [hdiff_le, hg_int_val, hsub]
  have hcoef : 0 ≤ ε * a * Real.exp (n * (2 * π / 3) * (xiStar + ε * u)) :=
    mul_nonneg (mul_nonneg hε_pos.le ha0.le) (Real.exp_pos _).le
  rw [hH_re]
  calc ε * a * Real.exp (n * (2 * π / 3) * (xiStar + ε * u)) * ∫ d : ℝ, tr_fn d
      ≤ ε * a * Real.exp (n * (2 * π / 3) * (xiStar + ε * u)) *
          (-(∫ d in Icc (-W) W, max (-spinG a Φ (b + d) (b - d)) 0) +
            ∫ d in Icc (-W) W, |spinG a Φ (b + d) (b - d) - spinTruncInv a N Φ (b + d) (b - d)|) :=
        mul_le_mul_of_nonneg_left htr_le hcoef
    _ = _ := by ring

end FormalResearch.ModularBootstrap.Spin
