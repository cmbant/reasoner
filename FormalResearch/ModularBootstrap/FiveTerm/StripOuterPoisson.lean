module

public import FormalResearch.ModularBootstrap.FiveTerm.StripOuterBoundary
public import FormalResearch.SignUncertainty.CtOuterPoisson

/-!
# Poisson representation and growth bounds for `genH a` (FIVE-0 slice 1; `cts:involution` (1))

For `Amp a` and `ζ` in the open strip, `Re genH a ζ = ∫ a(t) P_{Re ζ}(Im ζ - t) dt` (`re_genH`) with the strip Poisson
kernel `poissonK` of Paper I.  Consequences (`re_genH_ge`, `re_genH_le`, `re_hbarA_ge`, `re_hbarA_le`):

* if `a ≥ m` then `Re hbarA a ≥ m` on the closed strip;
* if `a(t) ≤ α|t| + β` (`α ≥ 0`) then `Re hbarA a (σ + iτ) ≤ α|τ| + β + α κ` on the closed strip, with `κ` an absolute
  constant (the first moment of the kernel).

All proved unconditionally.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.ModularBootstrap.FiveTerm.StripOuter

section

variable {a : ℝ → ℝ}

lemma re_genH (ha : Amp a) {ζ : ℂ} (hζ : ζ ∈ strip) :
    (genH a ζ).re = ∫ t : ℝ, a t * poissonK ζ.re (ζ.im - t) := by
  rw [genH_eq_integral]
  refine (integral_re (integrable_integrandA ha hζ)).symm.trans ?_
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [RCLike.re_to_complex]
  rw [div_eq_mul_inv, ← one_div, Complex.re_ofReal_mul, re_inv_sin_arg hζ]

lemma integrable_re_genH (ha : Amp a) {ζ : ℂ} (hζ : ζ ∈ strip) :
    Integrable fun t : ℝ => a t * poissonK ζ.re (ζ.im - t) := by
  have := (integrable_integrandA ha hζ).re
  refine this.congr (Eventually.of_forall fun t => ?_)
  simp only [RCLike.re_to_complex]
  rw [div_eq_mul_inv, ← one_div, Complex.re_ofReal_mul, re_inv_sin_arg hζ]

lemma integrable_poissonK_comp {ζ : ℂ} (hζ : ζ ∈ strip) :
    Integrable fun t : ℝ => poissonK ζ.re (ζ.im - t) := by
  have := (integrable_poissonK hζ.1 hζ.2).comp_sub_left ζ.im
  simpa using this

lemma integral_poissonK_comp {ζ : ℂ} (hζ : ζ ∈ strip) :
    ∫ t : ℝ, poissonK ζ.re (ζ.im - t) = 1 := by
  have h := integral_sub_left_eq_self (fun s : ℝ => poissonK ζ.re s) volume ζ.im
  rw [h]; exact integral_poissonK hζ.1 hζ.2

/-- Lower bound: `a ≥ m` implies `Re genH a ≥ m`. -/
lemma re_genH_ge (ha : Amp a) {m : ℝ} (hm : ∀ t, m ≤ a t) {ζ : ℂ} (hζ : ζ ∈ strip) :
    m ≤ (genH a ζ).re := by
  rw [re_genH ha hζ]
  have h1 : ∫ t : ℝ, m * poissonK ζ.re (ζ.im - t) = m := by
    rw [integral_const_mul, integral_poissonK_comp hζ]; ring
  rw [← h1]
  refine integral_mono (integrable_poissonK_comp hζ |>.const_mul m) (integrable_re_genH ha hζ) (fun t => ?_)
  exact mul_le_mul_of_nonneg_right (hm t) (poissonK_pos hζ.1 hζ.2 _).le

/-- The first moment of the strip Poisson kernel is bounded uniformly. -/
lemma poissonK_moment : ∃ κ : ℝ, 0 ≤ κ ∧ ∀ x : ℝ, 0 < x → x < 1 →
    Integrable (fun s : ℝ => |s| * poissonK x s) ∧ ∫ s : ℝ, |s| * poissonK x s ≤ κ := by
  have hπ1 : 0 < π - 1 := by linarith [Real.pi_gt_three]
  have hint : Integrable (fun s : ℝ => 8 * Real.exp (-(π - 1) * |s|)) :=
    (integrable_exp_neg_abs' hπ1).const_mul 8
  refine ⟨1 + ∫ s : ℝ, 8 * Real.exp (-(π - 1) * |s|), ?_, fun x h0 h1 => ?_⟩
  · have : 0 ≤ ∫ s : ℝ, 8 * Real.exp (-(π - 1) * |s|) :=
      integral_nonneg (fun s => by positivity)
    linarith
  have hK := integrable_poissonK h0 h1
  have hbound : ∀ s : ℝ, |s| * poissonK x s ≤ poissonK x s + 8 * Real.exp (-(π - 1) * |s|) := by
    intro s
    have hKp := (poissonK_pos h0 h1 s).le
    by_cases hs : 1 ≤ |s|
    · have h8 := poissonK_le h0 h1 hs
      have hts : |s| * Real.exp (-(π * |s|)) ≤ Real.exp (-(π - 1) * |s|) := by
        have : |s| * Real.exp (-|s|) ≤ 1 := by
          have h2 := Real.add_one_le_exp |s|
          have h3 : |s| ≤ Real.exp |s| := by linarith
          rw [Real.exp_neg]; rw [mul_inv_le_iff₀ (Real.exp_pos _)]; linarith
        calc |s| * Real.exp (-(π * |s|)) = (|s| * Real.exp (-|s|)) * Real.exp (-(π - 1) * |s|) := by
              rw [mul_assoc, ← Real.exp_add]; congr 2; ring
          _ ≤ 1 * Real.exp (-(π - 1) * |s|) := by gcongr
          _ = _ := one_mul _
      calc |s| * poissonK x s ≤ |s| * (8 * Real.exp (-(π * |s|))) := by gcongr
        _ = 8 * (|s| * Real.exp (-(π * |s|))) := by ring
        _ ≤ 8 * Real.exp (-(π - 1) * |s|) := by gcongr
        _ ≤ _ := by linarith
    · push Not at hs
      have : |s| * poissonK x s ≤ poissonK x s := by
        calc |s| * poissonK x s ≤ 1 * poissonK x s := by gcongr
          _ = _ := one_mul _
      have : 0 ≤ 8 * Real.exp (-(π - 1) * |s|) := by positivity
      linarith
  have hmeas : AEStronglyMeasurable (fun s : ℝ => |s| * poissonK x s) volume :=
    (continuous_abs.aestronglyMeasurable).mul hK.aestronglyMeasurable
  have hI : Integrable (fun s : ℝ => |s| * poissonK x s) :=
    Integrable.mono' (hK.add hint) hmeas (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity [poissonK_pos h0 h1 s])]
      exact hbound s)
  refine ⟨hI, ?_⟩
  calc ∫ s : ℝ, |s| * poissonK x s ≤ ∫ s : ℝ, (poissonK x s + 8 * Real.exp (-(π - 1) * |s|)) :=
        integral_mono hI (hK.add hint) hbound
    _ = 1 + ∫ s : ℝ, 8 * Real.exp (-(π - 1) * |s|) := by
        rw [integral_add hK hint, integral_poissonK h0 h1]

/-- Upper bound: `a(t) ≤ α|t| + β` implies `Re genH a ζ ≤ α|Im ζ| + β + α κ`. -/
lemma re_genH_le (ha : Amp a) {α β : ℝ} (hα : 0 ≤ α) (hb : ∀ t, a t ≤ α * |t| + β) :
    ∃ κ : ℝ, ∀ ζ ∈ strip, (genH a ζ).re ≤ α * |ζ.im| + β + α * κ := by
  obtain ⟨κ, hκ0, hκ⟩ := poissonK_moment
  refine ⟨κ, fun ζ hζ => ?_⟩
  rw [re_genH ha hζ]
  obtain ⟨hI, hIκ⟩ := hκ ζ.re hζ.1 hζ.2
  have hI' : Integrable fun t : ℝ => |ζ.im - t| * poissonK ζ.re (ζ.im - t) := by
    have := hI.comp_sub_left ζ.im
    simpa using this
  have hmom : ∫ t : ℝ, |ζ.im - t| * poissonK ζ.re (ζ.im - t) ≤ κ := by
    have h := integral_sub_left_eq_self (fun s : ℝ => |s| * poissonK ζ.re s) volume ζ.im
    rw [h]; exact hIκ
  have hpt : ∀ t : ℝ, a t * poissonK ζ.re (ζ.im - t) ≤
      (α * |ζ.im| + β) * poissonK ζ.re (ζ.im - t) + α * (|ζ.im - t| * poissonK ζ.re (ζ.im - t)) := by
    intro t
    have hKp := (poissonK_pos hζ.1 hζ.2 (ζ.im - t)).le
    have h1 : |t| ≤ |ζ.im| + |ζ.im - t| := by
      calc |t| = |ζ.im - (ζ.im - t)| := by ring_nf
        _ ≤ |ζ.im| + |ζ.im - t| := abs_sub _ _
    have h2 := hb t
    calc a t * poissonK ζ.re (ζ.im - t) ≤ (α * |t| + β) * poissonK ζ.re (ζ.im - t) :=
          mul_le_mul_of_nonneg_right h2 hKp
      _ ≤ (α * (|ζ.im| + |ζ.im - t|) + β) * poissonK ζ.re (ζ.im - t) := by
          gcongr
      _ = _ := by ring
  calc ∫ t : ℝ, a t * poissonK ζ.re (ζ.im - t)
      ≤ ∫ t : ℝ, ((α * |ζ.im| + β) * poissonK ζ.re (ζ.im - t) +
          α * (|ζ.im - t| * poissonK ζ.re (ζ.im - t))) :=
        integral_mono (integrable_re_genH ha hζ)
          (((integrable_poissonK_comp hζ).const_mul _).add (hI'.const_mul α)) hpt
    _ = (α * |ζ.im| + β) + α * ∫ t : ℝ, |ζ.im - t| * poissonK ζ.re (ζ.im - t) := by
        rw [integral_add ((integrable_poissonK_comp hζ).const_mul _) (hI'.const_mul α),
          integral_const_mul, integral_const_mul, integral_poissonK_comp hζ]; ring
    _ ≤ α * |ζ.im| + β + α * κ := by
        have := mul_le_mul_of_nonneg_left hmom hα
        linarith

/-- Closed-strip lower bound for the boundary extension. -/
lemma re_hbarA_ge (ha : Amp a) {m : ℝ} (hm : ∀ t, m ≤ a t) {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    m ≤ (hbarA a ζ).re := by
  have := neBot_nhdsWithin_strip hζ
  have hf : Tendsto (fun ξ => (genH a ξ).re) (𝓝[strip] ζ) (𝓝 (hbarA a ζ).re) :=
    (Complex.continuous_re.tendsto _).comp (hbarA_tendsto ha hζ)
  exact ge_of_tendsto hf (by filter_upwards [self_mem_nhdsWithin] with ξ hξ using re_genH_ge ha hm hξ)

/-- Closed-strip upper bound for the boundary extension. -/
lemma re_hbarA_le (ha : Amp a) {α β : ℝ} (hα : 0 ≤ α) (hb : ∀ t, a t ≤ α * |t| + β) :
    ∃ κ : ℝ, ∀ ζ ∈ closedStrip, (hbarA a ζ).re ≤ α * |ζ.im| + β + α * κ := by
  obtain ⟨κ, hκ⟩ := re_genH_le ha hα hb
  refine ⟨κ, fun ζ hζ => ?_⟩
  have := neBot_nhdsWithin_strip hζ
  have hf : Tendsto (fun ξ => (genH a ξ).re) (𝓝[strip] ζ) (𝓝 (hbarA a ζ).re) :=
    (Complex.continuous_re.tendsto _).comp (hbarA_tendsto ha hζ)
  have hg : Tendsto (fun ξ : ℂ => α * |ξ.im| + β + α * κ) (𝓝[strip] ζ) (𝓝 (α * |ζ.im| + β + α * κ)) := by
    have : Continuous fun ξ : ℂ => α * |ξ.im| + β + α * κ := by fun_prop
    exact (this.tendsto ζ).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto hf hg (by filter_upwards [self_mem_nhdsWithin] with ξ hξ using hκ ξ hξ)

end

end FormalResearch.ModularBootstrap.FiveTerm.StripOuter
