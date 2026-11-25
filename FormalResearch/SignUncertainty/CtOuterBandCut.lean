module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Topology.Algebra.Support

/-!
# Smooth cutoffs with scale-invariant derivative bounds

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 4 (smooth partition of unity
`1 = χ_loc + χ_0 + χ_∞` with `|χ^{(k)}| ≤ C_k τ_0^{-k}`).  **Proved.**

`exists_step`: a smooth step `X` from `0` (for `τ ≤ a`) to `1` (for `τ ≥ b`) with `|X'| ≤ K₁/(b-a)`, `|X''| ≤ K₂/(b-a)²`
(absolute `K₁, K₂`), obtained from `Real.smoothTransition`.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.CtOsc

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma deriv_smoothTransition_zero_of_nonpos {x : ℝ} (hx : x < 0) : deriv Real.smoothTransition x = 0 := by
  have : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hx] with y hy using Real.smoothTransition.zero_of_nonpos hy.le
  rw [this.deriv_eq]; simp

lemma deriv_smoothTransition_zero_of_one_lt {x : ℝ} (hx : 1 < x) : deriv Real.smoothTransition x = 0 := by
  have : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy using Real.smoothTransition.one_of_one_le hy.le
  rw [this.deriv_eq]; simp

lemma contDiff_deriv_zeta : ContDiff ℝ ∞' (deriv Real.smoothTransition) :=
  (contDiff_infty_iff_deriv.mp (Real.smoothTransition.contDiff (n := ⊤))).2

lemma contDiff_deriv_deriv_zeta : ContDiff ℝ ∞' (deriv (deriv Real.smoothTransition)) :=
  (contDiff_infty_iff_deriv.mp contDiff_deriv_zeta).2

lemma bdd_deriv_zeta : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |deriv Real.smoothTransition x| ≤ K := by
  have hc : Continuous (deriv Real.smoothTransition) := contDiff_deriv_zeta.continuous
  have hs : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun x hx => ?_
    rcases lt_or_ge x 0 with h | h
    · exact deriv_smoothTransition_zero_of_nonpos h
    · exact deriv_smoothTransition_zero_of_one_lt (by
        by_contra h1; exact hx ⟨h, not_lt.mp h1⟩)
  obtain ⟨K, hK⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨max K 0, le_max_right _ _, fun x => by
    have := (hK x).trans (le_max_left K 0)
    rwa [Real.norm_eq_abs] at this⟩

lemma bdd_deriv_deriv_zeta : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ K := by
  have hc : Continuous (deriv (deriv Real.smoothTransition)) := contDiff_deriv_deriv_zeta.continuous
  have hs : HasCompactSupport (deriv (deriv Real.smoothTransition)) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun x hx => ?_
    rcases lt_or_ge x 0 with h | h
    · have : deriv Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds h] with y hy using deriv_smoothTransition_zero_of_nonpos hy
      rw [this.deriv_eq]; simp
    · have h1 : 1 < x := by by_contra h1; exact hx ⟨h, not_lt.mp h1⟩
      have : deriv Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [Ioi_mem_nhds h1] with y hy using deriv_smoothTransition_zero_of_one_lt hy
      rw [this.deriv_eq]; simp
  obtain ⟨K, hK⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨max K 0, le_max_right _ _, fun x => by
    have := (hK x).trans (le_max_left K 0)
    rwa [Real.norm_eq_abs] at this⟩

lemma deriv2_zeta_zero_of_neg {x : ℝ} (hx : x < 0) : deriv (deriv Real.smoothTransition) x = 0 := by
  have : deriv Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hx] with y hy using deriv_smoothTransition_zero_of_nonpos hy
  rw [this.deriv_eq]; simp

lemma deriv2_zeta_zero_of_one_lt {x : ℝ} (hx : 1 < x) : deriv (deriv Real.smoothTransition) x = 0 := by
  have : deriv Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy using deriv_smoothTransition_zero_of_one_lt hy
  rw [this.deriv_eq]; simp

/-- A smooth step from `0` (`τ ≤ a`) to `1` (`τ ≥ b`), with scale-invariant derivative bounds. -/
lemma exists_step : ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧ ∀ a b : ℝ, a < b → ∃ X X1 X2 : ℝ → ℝ,
    (∀ τ, HasDerivAt X (X1 τ) τ) ∧ (∀ τ, HasDerivAt X1 (X2 τ) τ) ∧ Continuous X2 ∧
    (∀ τ, 0 ≤ X τ ∧ X τ ≤ 1) ∧ (∀ τ, τ ≤ a → X τ = 0) ∧ (∀ τ, b ≤ τ → X τ = 1) ∧
    (∀ τ, τ < a → X1 τ = 0 ∧ X2 τ = 0) ∧ (∀ τ, b < τ → X1 τ = 0 ∧ X2 τ = 0) ∧
    (∀ τ, |X1 τ| ≤ K1 / (b - a)) ∧ (∀ τ, |X2 τ| ≤ K2 / (b - a) ^ 2) := by
  obtain ⟨K1, hK1, hb1⟩ := bdd_deriv_zeta
  obtain ⟨K2, hK2, hb2⟩ := bdd_deriv_deriv_zeta
  refine ⟨K1, K2, hK1, hK2, fun a b hab => ?_⟩
  have hw : 0 < b - a := sub_pos.mpr hab
  set w := b - a with hwdef
  have hu : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => (τ - a) / w) (1 / w) τ := fun τ => by
    simpa using ((hasDerivAt_id τ).sub_const a).div_const w
  have hζ : Differentiable ℝ Real.smoothTransition := (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
  have hζ1 : Differentiable ℝ (deriv Real.smoothTransition) := contDiff_deriv_zeta.differentiable (by norm_num)
  refine ⟨fun τ => Real.smoothTransition ((τ - a) / w), fun τ => deriv Real.smoothTransition ((τ - a) / w) / w,
    fun τ => deriv (deriv Real.smoothTransition) ((τ - a) / w) / w ^ 2, fun τ => ?_, fun τ => ?_, ?_, fun τ => ?_,
    fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_, fun τ => ?_, fun τ => ?_⟩
  · have := (hζ ((τ - a) / w)).hasDerivAt.comp τ (hu τ)
    exact this.congr_deriv (by ring)
  · have := (hζ1 ((τ - a) / w)).hasDerivAt.comp τ (hu τ)
    have e : deriv (deriv Real.smoothTransition) ((τ - a) / w) * (1 / w) / w =
        deriv (deriv Real.smoothTransition) ((τ - a) / w) / w ^ 2 := by field_simp
    have := this.div_const w
    refine this.congr_deriv ?_
    field_simp
  · have hc : Continuous (deriv (deriv Real.smoothTransition)) := contDiff_deriv_deriv_zeta.continuous
    exact (hc.comp ((continuous_id.sub continuous_const).div_const w)).div_const _
  · exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le)
  · exact Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hw]; linarith)
  · have : (τ - a) / w < 0 := div_neg_of_neg_of_pos (by linarith) hw
    simp [deriv_smoothTransition_zero_of_nonpos this, deriv2_zeta_zero_of_neg this]
  · have : 1 < (τ - a) / w := by rw [lt_div_iff₀ hw]; linarith
    simp [deriv_smoothTransition_zero_of_one_lt this, deriv2_zeta_zero_of_one_lt this]
  · rw [abs_div, abs_of_pos hw]
    exact div_le_div_of_nonneg_right (hb1 _) hw.le
  · rw [abs_div, abs_of_pos (by positivity : 0 < w ^ 2)]
    exact div_le_div_of_nonneg_right (hb2 _) (by positivity)

end FormalResearch.SignUncertainty.CtOsc
