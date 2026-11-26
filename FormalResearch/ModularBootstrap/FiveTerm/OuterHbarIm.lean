module

public import FormalResearch.ModularBootstrap.FiveTerm.CombData
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroAmpDeriv
public import FormalResearch.SignUncertainty.CtOuterBdryIm

/-!
# `Im h̄_a(iτ) = F_a(τ)` for a locally Lipschitz amplitude of log-linear growth (FIVE-S, step 1)

For an admissible amplitude `a` (`StripOuter.Amp`) with `|a(t)| ≤ M (1 + |log |t|| + |t|)` and `a` locally
Lipschitz, the boundary value of `Im` of the strip Schwarz integral on the left edge is the conjugate-function
functional of Paper I: `Im h̄_a(iτ) = ∫ (a(t) - a(τ))/sinh(π(t-τ)) dt` (`bdryF`).  Applied to `aAmp`.
All proved unconditionally.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

/-- **`Im h̄_a(iτ) = F_a(τ)`** (Paper I's `tendsto_im_genH` transported to the boundary extension). -/
theorem im_hbarA_eq_bdryF {a : ℝ → ℝ} (ha : Amp a) {M : ℝ} (hM : ∀ t, |a t| ≤ M * wlog t)
    (hL : ∀ τ : ℝ, ∃ δ L : ℝ, 0 < δ ∧ ∀ t, |t - τ| ≤ δ → |a t - a τ| ≤ L * |t - τ|) (τ : ℝ) :
    (hbarA a (Complex.I * (τ : ℂ))).im = bdryF a τ := by
  obtain ⟨δ, L, hδ, hL'⟩ := hL τ
  have h1 := tendsto_im_genH ha.cont.measurable hM hδ hL'
  have hmem : Complex.I * (τ : ℂ) ∈ closedStrip := ⟨by simp, by simp⟩
  have h2 := hbarA_tendsto ha hmem
  have hpath : Tendsto (fun σ : ℝ => (σ : ℂ) + Complex.I * τ) (𝓝[>] 0)
      (𝓝[strip] (Complex.I * (τ : ℂ))) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun σ : ℝ => (σ : ℂ) + Complex.I * τ) (𝓝 0) (𝓝 ((0 : ℝ) + Complex.I * τ)) :=
        (Complex.continuous_ofReal.add continuous_const).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with σ hσ
      exact ⟨by simpa using hσ.1, by simpa using hσ.2⟩
  have h3 := (Complex.continuous_im.tendsto _).comp (h2.comp hpath)
  exact tendsto_nhds_unique h3 h1

/-- A `C¹` function with continuous derivative is locally Lipschitz in the form needed above. -/
lemma localLip_of_deriv {a a' : ℝ → ℝ} (hd : ∀ t, HasDerivAt a (a' t) t) (hc : Continuous a') (τ : ℝ) :
    ∃ δ L : ℝ, 0 < δ ∧ ∀ t, |t - τ| ≤ δ → |a t - a τ| ≤ L * |t - τ| := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := τ - 1) (b := τ + 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨1, B, one_pos, fun t ht => ?_⟩
  have hmem : ∀ x ∈ Icc (τ - 1) (τ + 1), ‖a' x‖ ≤ B := hB
  have hconv : Convex ℝ (Icc (τ - 1) (τ + 1)) := convex_Icc _ _
  have htm : t ∈ Icc (τ - 1) (τ + 1) := by
    rw [abs_le] at ht; constructor <;> linarith [ht.1, ht.2]
  have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hd x).hasDerivWithinAt) hmem (show τ ∈ Icc (τ - 1) (τ + 1) from ⟨by linarith, by linarith⟩) htm
  simpa [Real.norm_eq_abs] using h

/-- `m ≤ a ≤ α|t| + β` gives the log-linear bound `|a| ≤ (|m| + α + |β|) wlog`. -/
lemma abs_le_wlog_of_bounds {a : ℝ → ℝ} {m α β : ℝ} (hα : 0 ≤ α) (hm : ∀ t, m ≤ a t)
    (hb : ∀ t, a t ≤ α * |t| + β) : ∃ M : ℝ, ∀ t, |a t| ≤ M * wlog t := by
  refine ⟨|m| + α + |β|, fun t => ?_⟩
  have h1 : 1 ≤ wlog t := by unfold wlog; linarith [abs_nonneg (Real.log (|t|)), abs_nonneg t]
  have h2 : |t| ≤ wlog t := by unfold wlog; linarith [abs_nonneg (Real.log (|t|))]
  have h3 := mul_le_mul_of_nonneg_left h2 hα
  have h4 : |m| * 1 ≤ |m| * wlog t := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have h5 : |β| * 1 ≤ |β| * wlog t := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  rw [abs_le]
  constructor
  · have hw0 : 0 ≤ wlog t := by linarith
    nlinarith [neg_abs_le m, mul_nonneg hα hw0, mul_nonneg (abs_nonneg β) hw0, hm t]
  · have hw0 : 0 ≤ wlog t := by linarith
    nlinarith [le_abs_self β, mul_nonneg (abs_nonneg m) hw0, hb t]

lemma continuous_aD : Continuous aD := by
  unfold aD
  have hx := continuous_xT
  have hv := continuous_vT
  have hb := continuous_bT
  have hl := continuous_lamT
  have hc : ∀ c : ℝ, Continuous fun t : ℝ => Real.cosh (π * t / c) :=
    fun c => Real.continuous_cosh.comp (by fun_prop)
  have hs : ∀ c : ℝ, Continuous fun t : ℝ => Real.sinh (π * t / c) :=
    fun c => Real.continuous_sinh.comp (by fun_prop)
  have hxD : Continuous xD := by
    unfold xD
    refine (Real.continuous_sinh.comp (by fun_prop)).div ?_ (fun t => ?_)
    · exact continuous_const.mul ((Real.continuous_sqrt.comp (Real.continuous_cosh.comp (by fun_prop))).mul
        (Real.continuous_sqrt.comp (continuous_const.add (Real.continuous_cosh.comp (by fun_prop)))))
    · have h1 : 0 < √(Real.cosh (π * t)) := Real.sqrt_pos.mpr (Real.cosh_pos _)
      have h2 : 0 < √(1 + Real.cosh (π * t)) := Real.sqrt_pos.mpr (by linarith [Real.cosh_pos (π * t)])
      positivity
  have hvD : Continuous vD := by
    unfold vD
    refine (continuous_const.mul (hc 2)).div ?_ (fun t => ?_)
    · exact continuous_const.mul (Real.continuous_sqrt.comp (Real.continuous_cosh.comp (by fun_prop)))
    · have h1 : 0 < √(Real.cosh (π * t)) := Real.sqrt_pos.mpr (Real.cosh_pos _)
      positivity
  have hlD : Continuous lD := by
    unfold lD
    exact ((Real.continuous_exp.comp (continuous_const.mul hx |>.neg)).mul (continuous_const.mul hxD)).div_const _
  refine (((((continuous_const.mul (hxD.div hx (fun t => (xT_pos t).ne'))).add
    (continuous_const.mul (((hv.mul hvD).div hb (fun t => (bT_pos t).ne')).div hb (fun t => (bT_pos t).ne')))).add
    (continuous_const.mul (hlD.div hl (fun t => (lamT_pos t).ne')))).add
    (continuous_const.mul (((hs 4).mul continuous_const).div (hc 4) (fun t => (Real.cosh_pos _).ne')))).add
    (continuous_const.mul (((hs 2).mul continuous_const).div (hc 2) (fun t => (Real.cosh_pos _).ne')))).sub
    (continuous_const.mul (((Real.continuous_sinh.comp (by fun_prop : Continuous fun t : ℝ => π * t)).mul
      continuous_const).div (Real.continuous_cosh.comp (by fun_prop : Continuous fun t : ℝ => π * t))
      (fun t => (Real.cosh_pos _).ne')))

/-- **`Im h̄_a(iτ) = F_a(τ)` for `a = aAmp`.** -/
theorem im_hbarA_aAmp (τ : ℝ) : (hbarA aAmp (Complex.I * (τ : ℂ))).im = bdryF aAmp τ := by
  obtain ⟨⟨m, hm⟩, ⟨β, hβ⟩⟩ := exists_aAmp_bounds
  obtain ⟨M, hM⟩ := abs_le_wlog_of_bounds (by positivity : (0 : ℝ) ≤ 5 * π / 8) hm hβ
  exact im_hbarA_eq_bdryF amp_aAmp hM (fun τ => localLip_of_deriv hasDerivAt_aAmp continuous_aD τ) τ

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
