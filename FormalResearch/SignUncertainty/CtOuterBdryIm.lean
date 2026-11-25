module

public import FormalResearch.SignUncertainty.CtOuterU2
public import FormalResearch.SignUncertainty.CtOuterPhase
public import FormalResearch.SignUncertainty.CtOuterBoundary

/-!
# Boundary values of the imaginary part of a strip integral

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:outer` (3) (the boundary identity
`Im h̃(iτ) = p.v. ∫ ũ(t)/sinh(π(t-τ)) dt`).  **Proved.**

For an amplitude `a` of at most logarithmic growth that is Lipschitz near `τ`,
`Im ∫ a(t)/sin(π(σ + iτ - it)) dt → ∫ (a(t) - a(τ))/sinh(π(t-τ)) dt` as `σ ↓ 0`
(the imaginary part of the kernel is odd in `τ - t`, so the constant `a(τ)` can be subtracted; dominated convergence).
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- Poisson-type kernel: `Im 1/sin(π(σ + i s)) = -cos(πσ) sinh(πs)/(sin²(πσ) + sinh²(πs))`. -/
noncomputable def pker (σ s : ℝ) : ℝ :=
  -Real.cos (π * σ) * Real.sinh (π * s) / (Real.sin (π * σ) ^ 2 + Real.sinh (π * s) ^ 2)

lemma im_kern0 (σ τ t : ℝ) : (kern0 ((σ : ℂ) + Complex.I * τ) t).im = pker σ (τ - t) := by
  have hre : (↑π * ((σ : ℂ) + Complex.I * τ - Complex.I * t)).re = π * σ := by
    simp [Complex.mul_re]
  have him : (↑π * ((σ : ℂ) + Complex.I * τ - Complex.I * t)).im = π * (τ - t) := by
    simp [Complex.mul_im]
  have hsi : (Complex.sin (↑π * ((σ : ℂ) + Complex.I * τ - Complex.I * t))).im =
      Real.cos (π * σ) * Real.sinh (π * (τ - t)) := by
    rw [sin_eq_re_im]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, mul_zero, mul_one, zero_mul, add_zero, zero_add]
    have h2 : ((σ : ℂ) + Complex.I * τ - Complex.I * t).im = τ - t := by simp
    rw [h2, hre]
  unfold kern0 pker
  rw [one_div, Complex.inv_im, Complex.normSq_eq_norm_sq, norm_sin_sq, hsi, hre, him]
  ring

lemma pker_neg (σ s : ℝ) : pker σ (-s) = -pker σ s := by
  unfold pker
  simp only [mul_neg, Real.sinh_neg, neg_sq]
  ring

lemma abs_pker_le (σ s : ℝ) : |pker σ s| ≤ 1 / |Real.sinh (π * s)| := by
  by_cases hs : Real.sinh (π * s) = 0
  · unfold pker; simp [hs]
  have hpos : 0 < Real.sinh (π * s) ^ 2 := by positivity
  have hsin : 0 ≤ Real.sin (π * σ) ^ 2 := sq_nonneg _
  unfold pker
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < Real.sin (π * σ) ^ 2 + Real.sinh (π * s) ^ 2),
    abs_mul, abs_neg, div_le_div_iff₀ (by positivity) (abs_pos.mpr hs)]
  have h1 : |Real.cos (π * σ)| ≤ 1 := Real.abs_cos_le_one _
  have h2 : |Real.sinh (π * s)| * |Real.sinh (π * s)| = Real.sinh (π * s) ^ 2 := by
    rw [← sq, sq_abs]
  calc |Real.cos (π * σ)| * |Real.sinh (π * s)| * |Real.sinh (π * s)| ≤ 1 * Real.sinh (π * s) ^ 2 := by
        rw [mul_assoc, h2]; exact mul_le_mul_of_nonneg_right h1 hpos.le
    _ ≤ 1 * (Real.sin (π * σ) ^ 2 + Real.sinh (π * s) ^ 2) := by linarith only [hsin]

lemma tendsto_pker {s : ℝ} (hs : s ≠ 0) :
    Tendsto (fun σ : ℝ => pker σ s) (𝓝 0) (𝓝 (-(1 / Real.sinh (π * s)))) := by
  have hsh : Real.sinh (π * s) ≠ 0 := Real.sinh_eq_zero.not.mpr (mul_ne_zero Real.pi_pos.ne' hs)
  have hc : ContinuousAt (fun σ : ℝ => pker σ s) 0 := by
    unfold pker
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    simp [hsh]
  have := hc.tendsto
  have e : pker 0 s = -(1 / Real.sinh (π * s)) := by
    unfold pker
    simp
    field_simp
  rwa [e] at this

/-! ### Logarithmic weight -/

/-- Weight `1 + |log|t|| + |t|` of the amplitudes with logarithmic growth. -/
noncomputable def wlog (t : ℝ) : ℝ := 1 + |Real.log (|t|)| + |t|

lemma measurable_wlog : Measurable wlog := by
  unfold wlog
  have : Measurable fun t : ℝ => Real.log |t| := Real.measurable_log.comp measurable_abs
  fun_prop

lemma integrable_abs_exp {c : ℝ} (hc : 0 < c) : Integrable fun t : ℝ => |t| * Real.exp (-c * |t|) := by
  have hint := (integrable_exp_neg_abs' (c := c / 2) (by positivity)).const_mul (2 / c)
  refine Integrable.mono' hint ?_ (Eventually.of_forall fun t => ?_)
  · exact (by fun_prop : Continuous fun t : ℝ => |t| * Real.exp (-c * |t|)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    have h1 : (c / 2) * |t| ≤ Real.exp ((c / 2) * |t|) := by
      linarith only [Real.add_one_le_exp ((c / 2) * |t|)]
    have h2 : |t| ≤ 2 / c * Real.exp ((c / 2) * |t|) := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 / c)
      have e : 2 / c * ((c / 2) * |t|) = |t| := by field_simp
      linarith only [this, e]
    calc |t| * Real.exp (-c * |t|) ≤ 2 / c * Real.exp ((c / 2) * |t|) * Real.exp (-c * |t|) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = 2 / c * Real.exp (-(c / 2) * |t|) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf

lemma integrable_log_abs_exp {c : ℝ} (hc : 0 < c) :
    Integrable fun t : ℝ => |Real.log (|t|)| * Real.exp (-c * |t|) := by
  have hI : IntegrableOn (fun t : ℝ => |Real.log (|t|)|) (Icc (-1 : ℝ) 1) := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := (-1 : ℝ)) (b := 1)).norm
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)] at h
    refine h.congr_fun (fun t _ => ?_) measurableSet_Icc
    simp [Real.log_abs]
  have h1 := hI.integrable_indicator measurableSet_Icc
  have h2 := integrable_abs_exp hc
  refine Integrable.mono' (h1.add h2) ?_ (Eventually.of_forall fun t => ?_)
  · have : Measurable fun t : ℝ => |Real.log (|t|)| * Real.exp (-c * |t|) := by
      have : Measurable fun t : ℝ => Real.log |t| := Real.measurable_log.comp measurable_abs
      fun_prop
    exact this.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    by_cases ht : |t| ≤ 1
    · have hmem : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [(abs_le.mp ht).1], (abs_le.mp ht).2⟩
      have : Real.exp (-c * |t|) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [hc, abs_nonneg t])
      simp only [Pi.add_apply, indicator_of_mem hmem]
      have h3 : 0 ≤ |t| * Real.exp (-c * |t|) := by positivity
      calc |Real.log (|t|)| * Real.exp (-c * |t|) ≤ |Real.log (|t|)| * 1 :=
            mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ ≤ |Real.log (|t|)| + |t| * Real.exp (-c * |t|) := by linarith only [h3]
    · have hlog : |Real.log (|t|)| ≤ |t| := by
        have h1' : 1 < |t| := not_le.mp ht
        rw [abs_of_nonneg (Real.log_nonneg h1'.le)]
        exact Real.log_le_self (abs_nonneg t)
      have hmem : t ∉ Icc (-1 : ℝ) 1 := fun h => ht (abs_le.mpr ⟨h.1, h.2⟩)
      simp only [Pi.add_apply, indicator_of_notMem hmem, zero_add]
      exact mul_le_mul_of_nonneg_right hlog (Real.exp_pos _).le

lemma integrable_wlog_exp {c : ℝ} (hc : 0 < c) :
    Integrable fun t : ℝ => wlog t * Real.exp (-c * |t|) := by
  have h := ((integrable_exp_neg_abs' hc).add (integrable_log_abs_exp hc)).add (integrable_abs_exp hc)
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, wlog]
  ring


/-- The boundary functional `F_a(τ) = ∫ (a(t) - a(τ)) / sinh(π(t - τ)) dt`. -/
noncomputable def bdryF (a : ℝ → ℝ) (τ : ℝ) : ℝ := ∫ t : ℝ, (a t - a τ) / Real.sinh (π * (t - τ))

lemma integrable_amp_mul_k {a : ℝ → ℝ} (hm : Measurable a) {M : ℝ} (hM : ∀ t, |a t| ≤ M * wlog t)
    {k : ℝ → ℂ} (hk : AEStronglyMeasurable k volume) {C c : ℝ} (hc : 0 < c)
    (hC : ∀ t, ‖k t‖ ≤ C * Real.exp (-c * |t|)) : Integrable fun t : ℝ => (a t : ℂ) * k t := by
  have hw0 : 1 ≤ wlog 0 := by simp [wlog]
  have hM0 : 0 ≤ M := by
    have := (abs_nonneg (a 0)).trans (hM 0)
    have hw : 0 < wlog 0 := by linarith
    exact nonneg_of_mul_nonneg_left (by simpa using this) hw
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg (k 0)).trans (hC 0)
    simpa using this
  have h := (integrable_wlog_exp hc).const_mul (M * C)
  refine Integrable.mono' h ((Complex.measurable_ofReal.comp hm).aestronglyMeasurable.mul hk)
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |a t| * ‖k t‖ ≤ (M * wlog t) * (C * Real.exp (-c * |t|)) :=
        mul_le_mul (hM t) (hC t) (norm_nonneg _) (by
          have : 0 ≤ wlog t := by unfold wlog; positivity
          positivity)
    _ = M * C * (wlog t * Real.exp (-c * |t|)) := by ring

lemma norm_kern0_le_exp {σ τ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (t : ℝ) :
    ‖kern0 ((σ : ℂ) + Complex.I * τ) t‖ ≤
      (2 / Real.sin (π * σ) * Real.exp (π * |τ|)) * Real.exp (-π * |t|) := by
  have hsin : 0 < Real.sin (π * σ) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have h := norm_kern0_le (ζ := (σ : ℂ) + Complex.I * τ) t hsin (Real.sin_le_one _) (by simp)
  have him : ((σ : ℂ) + Complex.I * τ).im = τ := by simp
  rw [him] at h
  have hexp : Real.exp (-(π * |τ - t|)) ≤ Real.exp (π * |τ|) * Real.exp (-π * |t|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : |t| ≤ |τ - t| + |τ| := by
      calc |t| = |τ - (τ - t)| := by ring_nf
        _ ≤ |τ| + |τ - t| := abs_sub _ _
        _ = _ := by ring
    nlinarith only [this, Real.pi_pos]
  calc _ ≤ 2 / Real.sin (π * σ) * Real.exp (-(π * |τ - t|)) := h
    _ ≤ 2 / Real.sin (π * σ) * (Real.exp (π * |τ|) * Real.exp (-π * |t|)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

lemma integral_pker_zero {σ τ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) : ∫ t : ℝ, pker σ (τ - t) = 0 := by
  have hint : Integrable fun t : ℝ => pker σ (τ - t) := by
    have h := (integrable_exp_neg_abs' (c := π) Real.pi_pos).const_mul
      (2 / Real.sin (π * σ) * Real.exp (π * |τ|))
    refine Integrable.mono' h ?_ (Eventually.of_forall fun t => ?_)
    · have : Continuous fun t : ℝ => pker σ (τ - t) := by
        unfold pker
        refine Continuous.div (by fun_prop) (by fun_prop) (fun t => ?_)
        have hsin : 0 < Real.sin (π * σ) :=
          Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
        positivity
      exact this.aestronglyMeasurable
    · rw [Real.norm_eq_abs, ← im_kern0 σ τ t]
      exact (Complex.abs_im_le_norm _).trans (norm_kern0_le_exp hσ hσ1 t)
  have h1 : ∫ t : ℝ, pker σ (τ - t) = ∫ s : ℝ, pker σ s := integral_sub_left_eq_self (fun s => pker σ s) volume τ
  rw [h1]
  have h2 : ∫ s : ℝ, pker σ s = ∫ s : ℝ, pker σ (-s) := (integral_neg_eq_self (fun s => pker σ s) volume).symm
  have h3 : ∫ s : ℝ, pker σ (-s) = -∫ s : ℝ, pker σ s := by
    simp_rw [pker_neg]; rw [integral_neg]
  linarith only [h2, h3]


lemma abs_sinh_pi (s : ℝ) : |Real.sinh (π * s)| = Real.sinh (π * |s|) := by
  rcases le_total 0 s with h0 | h0
  · rw [abs_of_nonneg h0, abs_of_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg Real.pi_pos.le h0))]
  · rw [abs_of_nonpos h0, abs_of_nonpos (Real.sinh_nonpos_iff.mpr (mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le h0)),
      mul_neg, Real.sinh_neg]

lemma sinh_abs_lower {δ s : ℝ} (_hδ : 0 < δ) (hs : δ ≤ |s|) :
    (1 - Real.exp (-(2 * π * δ))) / 2 * Real.exp (π * |s|) ≤ |Real.sinh (π * s)| := by
  rw [abs_sinh_pi]; exact sinh_pi_lower (m := δ) (s := |s|) hs

/-- The majorant `|a(t) - a(τ)| / |sinh(π(t-τ))|` is integrable. -/
lemma integrable_bdry_major {a : ℝ → ℝ} (hm : Measurable a) {M : ℝ} (hM : ∀ t, |a t| ≤ M * wlog t)
    {τ δ L : ℝ} (hδ : 0 < δ) (hL : ∀ t, |t - τ| ≤ δ → |a t - a τ| ≤ L * |t - τ|) :
    Integrable fun t : ℝ => |a t - a τ| / |Real.sinh (π * (t - τ))| := by
  set q : ℝ := Real.exp (-(2 * π * δ)) with hq
  have hq1 : 0 < 1 - q := by
    have : q < 1 := Real.exp_lt_one_iff.mpr (by have := Real.pi_pos; nlinarith)
    linarith
  have hM0 : 0 ≤ M := by
    have := (abs_nonneg (a 0)).trans (hM 0)
    have hw : 1 ≤ wlog 0 := by simp [wlog]
    exact nonneg_of_mul_nonneg_left (by simpa using this) (by linarith)
  have hL0 : 0 ≤ L := by
    have := hL (τ + δ) (by simp [abs_of_pos hδ])
    have h2 : 0 ≤ |a (τ + δ) - a τ| := abs_nonneg _
    have : 0 ≤ L * |τ + δ - τ| := h2.trans this
    have h3 : 0 < |τ + δ - τ| := by simp [abs_of_pos hδ]; exact hδ
    exact nonneg_of_mul_nonneg_left this h3
  have h1 : Integrable fun t : ℝ => (L / π) * (Icc (τ - δ) (τ + δ)).indicator (fun _ => (1 : ℝ)) t := by
    have : Integrable ((Icc (τ - δ) (τ + δ)).indicator (fun _ => (1 : ℝ))) :=
      (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
    exact this.const_mul _
  have h2 : Integrable fun t : ℝ => (2 / (1 - q) * (M + |a τ|) * Real.exp (π * |τ|)) *
      (wlog t * Real.exp (-π * |t|)) := by
    have := (integrable_wlog_exp Real.pi_pos).const_mul (2 / (1 - q) * (M + |a τ|) * Real.exp (π * |τ|))
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [neg_mul]
  refine Integrable.mono' (h1.add h2) ?_ (Eventually.of_forall fun t => ?_)
  · have : Measurable fun t : ℝ => |a t - a τ| / |Real.sinh (π * (t - τ))| := by
      have : Measurable fun t : ℝ => Real.sinh (π * (t - τ)) := by fun_prop
      exact ((hm.sub measurable_const).abs).div this.abs
    exact this.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    by_cases ht : |t - τ| ≤ δ
    · have hmem : t ∈ Icc (τ - δ) (τ + δ) := ⟨by linarith [(abs_le.mp ht).1], by linarith [(abs_le.mp ht).2]⟩
      simp only [Pi.add_apply, indicator_of_mem hmem, mul_one]
      by_cases h0 : t = τ
      · subst h0
        have hw0 : 0 ≤ wlog t := by unfold wlog; positivity
        simp
        positivity
      have hs0 : t - τ ≠ 0 := sub_ne_zero.mpr h0
      have hsh : π * |t - τ| ≤ |Real.sinh (π * (t - τ))| := by
        rw [abs_sinh_pi]; exact Real.self_le_sinh_iff.mpr (by positivity)
      have hpos : 0 < |t - τ| := abs_pos.mpr hs0
      calc |a t - a τ| / |Real.sinh (π * (t - τ))| ≤ (L * |t - τ|) / (π * |t - τ|) := by
            apply div_le_div₀ (by positivity) (hL t ht) (by positivity) hsh
        _ = L / π := by field_simp
        _ ≤ L / π + _ := by
            have : 0 ≤ 2 / (1 - q) * (M + |a τ|) * Real.exp (π * |τ|) * (wlog t * Real.exp (-π * |t|)) := by
              have : 0 ≤ wlog t := by unfold wlog; positivity
              positivity
            linarith only [this]
    · have hgt : δ ≤ |t - τ| := (not_le.mp ht).le
      have hmem : t ∉ Icc (τ - δ) (τ + δ) := fun h => ht (abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩)
      simp only [Pi.add_apply, indicator_of_notMem hmem, mul_zero, zero_add]
      have hlow := sinh_abs_lower hδ hgt
      rw [← hq] at hlow
      have hpos : 0 < (1 - q) / 2 * Real.exp (π * |t - τ|) := by positivity
      have hnum : |a t - a τ| ≤ (M + |a τ|) * wlog t := by
        have hw : 1 ≤ wlog t := by unfold wlog; linarith [abs_nonneg (Real.log (|t|)), abs_nonneg t]
        calc |a t - a τ| ≤ |a t| + |a τ| := abs_sub _ _
          _ ≤ M * wlog t + |a τ| * wlog t := by
              have := hM t
              nlinarith only [this, hw, abs_nonneg (a τ)]
          _ = (M + |a τ|) * wlog t := by ring
      have hw0 : 0 ≤ wlog t := by unfold wlog; positivity
      have hexp : Real.exp (-π * |t - τ|) ≤ Real.exp (π * |τ|) * Real.exp (-π * |t|) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have : |t| ≤ |t - τ| + |τ| := by
          calc |t| = |(t - τ) + τ| := by ring_nf
            _ ≤ _ := abs_add_le _ _
        nlinarith only [this, Real.pi_pos]
      calc |a t - a τ| / |Real.sinh (π * (t - τ))|
          ≤ ((M + |a τ|) * wlog t) / ((1 - q) / 2 * Real.exp (π * |t - τ|)) := by
            apply div_le_div₀ (by positivity) hnum hpos hlow
        _ = 2 / (1 - q) * (M + |a τ|) * wlog t * Real.exp (-π * |t - τ|) := by
            rw [neg_mul, Real.exp_neg]; field_simp
        _ ≤ 2 / (1 - q) * (M + |a τ|) * wlog t * (Real.exp (π * |τ|) * Real.exp (-π * |t|)) := by
            have : 0 ≤ 2 / (1 - q) * (M + |a τ|) * wlog t := by
              have : 0 ≤ wlog t := by unfold wlog; positivity
              positivity
            exact mul_le_mul_of_nonneg_left hexp this
        _ = 2 / (1 - q) * (M + |a τ|) * Real.exp (π * |τ|) * (wlog t * Real.exp (-π * |t|)) := by ring
        _ = _ := by ring


lemma integrable_amp_kern0_im {a : ℝ → ℝ} (hm : Measurable a) {M : ℝ} (hM : ∀ t, |a t| ≤ M * wlog t)
    {σ τ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    Integrable fun t : ℝ => (a t : ℂ) * kern0 ((σ : ℂ) + Complex.I * τ) t := by
  have hs : ((σ : ℂ) + Complex.I * τ) ∈ strip := ⟨by simpa using hσ, by simpa using hσ1⟩
  exact integrable_amp_mul_k hm hM (continuous_kern0 hs).aestronglyMeasurable Real.pi_pos
    (fun t => by simpa using norm_kern0_le_exp hσ hσ1 t)

lemma im_genH_eq {a : ℝ → ℝ} (hm : Measurable a) {M : ℝ} (hM : ∀ t, |a t| ≤ M * wlog t)
    {σ τ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    (genH a ((σ : ℂ) + Complex.I * τ)).im = ∫ t : ℝ, a t * pker σ (τ - t) := by
  have hint := integrable_amp_kern0_im hm hM (τ := τ) hσ hσ1
  unfold genH
  rw [← RCLike.im_to_complex, ← integral_im hint]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  change ((a t : ℂ) * kern0 ((σ : ℂ) + Complex.I * τ) t).im = _
  rw [Complex.im_ofReal_mul, im_kern0]

lemma integrable_amp_pker {a : ℝ → ℝ} (hm : Measurable a) {M : ℝ} (hM : ∀ t, |a t| ≤ M * wlog t)
    {σ τ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    Integrable fun t : ℝ => a t * pker σ (τ - t) := by
  have hint := (integrable_amp_kern0_im hm hM (τ := τ) hσ hσ1).im
  refine hint.congr (Eventually.of_forall fun t => ?_)
  change ((a t : ℂ) * kern0 ((σ : ℂ) + Complex.I * τ) t).im = _
  rw [Complex.im_ofReal_mul, im_kern0]

/-- **Boundary value of the imaginary part of a strip integral.** -/
theorem tendsto_im_genH {a : ℝ → ℝ} (hm : Measurable a) {M : ℝ} (hM : ∀ t, |a t| ≤ M * wlog t)
    {τ δ L : ℝ} (hδ : 0 < δ) (hL : ∀ t, |t - τ| ≤ δ → |a t - a τ| ≤ L * |t - τ|) :
    Tendsto (fun σ : ℝ => (genH a ((σ : ℂ) + Complex.I * τ)).im) (𝓝[>] 0) (𝓝 (bdryF a τ)) := by
  have hmaj := integrable_bdry_major hm hM hδ hL
  -- rewrite the functional
  have hrew : ∀ σ : ℝ, 0 < σ → σ < 1 → (genH a ((σ : ℂ) + Complex.I * τ)).im =
      ∫ t : ℝ, (a t - a τ) * pker σ (τ - t) := by
    intro σ hσ hσ1
    rw [im_genH_eq hm hM hσ hσ1]
    have h1 := integrable_amp_pker hm hM (τ := τ) hσ hσ1
    have h2 : Integrable fun t : ℝ => pker σ (τ - t) := by
      have := integrable_amp_pker (a := fun _ => (1 : ℝ)) measurable_const (M := 1)
        (fun t => by simp [wlog]; linarith [abs_nonneg (Real.log t), abs_nonneg t]) (τ := τ) hσ hσ1
      simpa using this
    have e : ∀ t : ℝ, (a t - a τ) * pker σ (τ - t) = a t * pker σ (τ - t) - a τ * pker σ (τ - t) := fun t => by ring
    simp_rw [e]
    rw [integral_sub h1 (h2.const_mul _), integral_const_mul, integral_pker_zero hσ hσ1]
    ring
  have hlim : Tendsto (fun σ : ℝ => ∫ t : ℝ, (a t - a τ) * pker σ (τ - t)) (𝓝[>] 0)
      (𝓝 (bdryF a τ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => |a t - a τ| / |Real.sinh (π * (t - τ))|) ?_ ?_ hmaj ?_
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with σ hσ
      have hc : Continuous fun t : ℝ => pker σ (τ - t) := by
        unfold pker
        refine Continuous.div (by fun_prop) (by fun_prop) (fun t => ?_)
        have hsin : 0 < Real.sin (π * σ) :=
          Real.sin_pos_of_pos_of_lt_pi (by have := hσ.1; positivity) (by nlinarith [Real.pi_pos, hσ.2])
        positivity
      exact ((hm.sub measurable_const).mul hc.measurable).aestronglyMeasurable
    · refine Eventually.of_forall fun σ => Eventually.of_forall fun t => ?_
      rw [Real.norm_eq_abs, abs_mul]
      have h := abs_pker_le σ (τ - t)
      have e : |Real.sinh (π * (τ - t))| = |Real.sinh (π * (t - τ))| := by
        rw [abs_sinh_pi, abs_sinh_pi, abs_sub_comm]
      rw [e] at h
      calc |a t - a τ| * |pker σ (τ - t)| ≤ |a t - a τ| * (1 / |Real.sinh (π * (t - τ))|) :=
            mul_le_mul_of_nonneg_left h (abs_nonneg _)
        _ = |a t - a τ| / |Real.sinh (π * (t - τ))| := by rw [mul_one_div]
    · refine Eventually.of_forall fun t => ?_
      by_cases ht : t = τ
      · subst ht; simp
      have hs : τ - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
      have := ((tendsto_pker hs).const_mul (a t - a τ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      have e : (a t - a τ) * -(1 / Real.sinh (π * (τ - t))) = (a t - a τ) / Real.sinh (π * (t - τ)) := by
        rw [show π * (t - τ) = -(π * (τ - t)) by ring, Real.sinh_neg]
        ring
      rwa [e] at this
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with σ hσ
  exact (hrew σ hσ.1 hσ.2).symm


/-- Lipschitz bound for `u_r` on `[τ - 1, τ + 1]`. -/
lemma uR_lipschitz (τ : ℝ) : ∃ L : ℝ, ∀ t : ℝ, |t - τ| ≤ 1 → |uR t - uR τ| ≤ L * |t - τ| := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := τ - 1) (b := τ + 1)).exists_bound_of_continuousOn
    continuous_uR1.continuousOn
  refine ⟨B, fun t ht => ?_⟩
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => uR (τ + s)) (uR1 (τ + s)) s := fun s =>
    ((hasDerivAt_uR (τ + s)).comp s ((hasDerivAt_id s).const_add τ)).congr_deriv (by simp)
  have := abs_sub_le_of_deriv hd (r := 1) (K := B) (x := t - τ) (fun y hy => by
    have := hB (τ + y) ⟨by linarith [hy.1], by linarith [hy.2]⟩
    rwa [Real.norm_eq_abs] at this) (by simpa using ht)
  simpa using this

lemma uR_wlog : ∃ M : ℝ, ∀ t : ℝ, |uR t| ≤ M * wlog t := by
  refine ⟨2 + 2 * C0, fun t => ?_⟩
  have h1 := abs_uR_le' t
  have h2 := log_one_add_sq_le t
  have h3 : 1 ≤ wlog t := by unfold wlog; linarith [abs_nonneg (Real.log (|t|)), abs_nonneg t]
  have h4 : |t| ≤ wlog t := by unfold wlog; linarith [abs_nonneg (Real.log (|t|))]
  have h5 := mul_le_mul_of_nonneg_left h3 C0_nonneg
  linarith only [h1, h2, h4, h5, C0_nonneg]

/-- **`Im h̄(iτ) = ∫ (u_r(t) - u_r(τ))/sinh(π(t-τ)) dt`.** -/
theorem im_outerHbar (τ : ℝ) : (outerHbar (Complex.I * (τ : ℂ))).im = bdryF uR τ := by
  obtain ⟨M, hM⟩ := uR_wlog
  obtain ⟨L, hL⟩ := uR_lipschitz τ
  have h1 := tendsto_im_genH continuous_uR.measurable hM one_pos hL
  have hmem : Complex.I * (τ : ℂ) ∈ closedStrip := ⟨by simp, by simp⟩
  have h2 := outerHbar_tendsto hmem
  have hpath : Tendsto (fun σ : ℝ => (σ : ℂ) + Complex.I * τ) (𝓝[>] 0) (𝓝[strip] (Complex.I * (τ : ℂ))) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun σ : ℝ => (σ : ℂ) + Complex.I * τ) (𝓝 0) (𝓝 ((0 : ℝ) + Complex.I * τ)) :=
        (Complex.continuous_ofReal.add continuous_const).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with σ hσ
      exact ⟨by simpa using hσ.1, by simpa using hσ.2⟩
  have h3 := (Complex.continuous_im.tendsto _).comp (h2.comp hpath)
  have h4 : (fun σ : ℝ => (genH uR ((σ : ℂ) + Complex.I * τ)).im) =
      (Complex.im ∘ outerH ∘ fun σ : ℝ => (σ : ℂ) + Complex.I * τ) := by
    funext σ; simp [outerH_eq_genH]
  rw [h4] at h1
  exact tendsto_nhds_unique h3 h1

/-- **`θ_-(τ) = ∫ (u_r(t) - u_r(τ))/sinh(π(t-τ)) dt - arctan τ`.** -/
theorem outerTheta_neg_eq (τ : ℝ) : outerTheta (-1) τ = bdryF uR τ - Real.arctan τ := by
  unfold outerTheta
  rw [im_outerHbar]
  norm_num

/-- info: 'FormalResearch.SignUncertainty.CtOuter.tendsto_im_genH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_im_genH

/-- info: 'FormalResearch.SignUncertainty.CtOuter.im_outerHbar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms im_outerHbar

/-- info: 'FormalResearch.SignUncertainty.CtOuter.outerTheta_neg_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outerTheta_neg_eq

end FormalResearch.SignUncertainty.CtOuter
