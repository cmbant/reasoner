module

public import FormalResearch.SignUncertainty.CtOuterBdryDecay
public import FormalResearch.SignUncertainty.CtOuterTilde

/-!
# The cutoff splitting `ũ = ũ₀ + ũ₁`

**Proved.**  `χ(t) = smoothTransition(3 - t²)` is smooth, `1` on `|t| ≤ 1` and `0` on `|t| ≥ 2`.  `ũ₀ = χ ũ` is
integrable and supported in `[-2, 2]`; `ũ₁ = (1 - χ) ũ` is `C^∞` with `|ũ₁^{(n)}(t)| ≤ A_n (1+|t|) e^{-π|t|}`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- Smooth cutoff, `1` on `|t| ≤ 1`, `0` on `|t| ≥ 2`. -/
noncomputable def chi (t : ℝ) : ℝ := Real.smoothTransition (3 - t ^ 2)

lemma chi_nonneg (t : ℝ) : 0 ≤ chi t := Real.smoothTransition.nonneg _
lemma chi_le_one (t : ℝ) : chi t ≤ 1 := Real.smoothTransition.le_one _
lemma chi_eq_one {t : ℝ} (ht : |t| ≤ 1) : chi t = 1 := by
  unfold chi
  apply Real.smoothTransition.one_of_one_le
  have : t ^ 2 ≤ 1 := by nlinarith only [abs_nonneg t, ht, sq_abs t]
  linarith
lemma chi_eq_zero {t : ℝ} (ht : 2 ≤ |t|) : chi t = 0 := by
  unfold chi
  apply Real.smoothTransition.zero_of_nonpos
  have : 4 ≤ t ^ 2 := by nlinarith only [ht, sq_abs t]
  linarith
lemma contDiff_chi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) chi :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_const.sub (contDiff_id.pow 2))

lemma chi_neg (t : ℝ) : chi (-t) = chi t := by unfold chi; rw [neg_sq]

lemma wpl_neg (t : ℝ) : wpl (-t) = wpl t := by unfold wpl; rw [abs_neg, neg_sq]

lemma utl_neg (t : ℝ) : utl (-t) = utl t := by unfold utl; rw [uR_neg, wpl_neg]

lemma utl_wlog : ∃ M : ℝ, ∀ t : ℝ, |utl t| ≤ M * wlog t := by
  obtain ⟨M, hM⟩ := uR_wlog
  refine ⟨M + (3 + |cLog|), fun t => ?_⟩
  have hw : 0 ≤ wlog t := by unfold wlog; positivity
  calc |utl t| ≤ |uR t| + |wpl t| := abs_add_le _ _
    _ ≤ M * wlog t + (3 + |cLog|) * wlog t := add_le_add (hM t) (wpl_bound t)
    _ = _ := by ring

lemma measurable_utl : Measurable utl := continuous_uR.measurable.add measurable_wpl

lemma contDiffAt_utl {t : ℝ} (ht : t ≠ 0) : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) utl t := by
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) uR t := contDiff_uR_inf.contDiffAt
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) wpl t := by
    have e : wpl = fun s : ℝ => Real.log s + (1 / 2) * Real.log (1 + s ^ 2) + cLog := by
      funext s; unfold wpl; rw [Real.log_abs]
    rw [e]
    have hl : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Real.log t := Real.contDiffAt_log.2 ht
    have hq : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => Real.log (1 + s ^ 2)) t := by
      have hne : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
      exact (Real.contDiffAt_log.2 hne).comp t (contDiffAt_const.add (contDiffAt_id.pow 2))
    exact (hl.add (contDiffAt_const.mul hq)).add contDiffAt_const
  exact h1.add h2

/-- `ũ₀ = χ ũ` (supported in `[-2,2]`). -/
noncomputable def utl0 (t : ℝ) : ℝ := chi t * utl t
/-- `ũ₁ = (1 - χ) ũ` (smooth). -/
noncomputable def utl1 (t : ℝ) : ℝ := (1 - chi t) * utl t

lemma utl0_add_utl1 (t : ℝ) : utl0 t + utl1 t = utl t := by unfold utl0 utl1; ring

lemma utl0_eq_zero {t : ℝ} (ht : 2 ≤ |t|) : utl0 t = 0 := by unfold utl0; rw [chi_eq_zero ht, zero_mul]
lemma utl1_eq {t : ℝ} (ht : 2 ≤ |t|) : utl1 t = utl t := by unfold utl1; rw [chi_eq_zero ht]; ring
lemma utl1_eq_zero {t : ℝ} (ht : |t| ≤ 1) : utl1 t = 0 := by unfold utl1; rw [chi_eq_one ht]; ring

lemma utl1_neg (t : ℝ) : utl1 (-t) = utl1 t := by unfold utl1; rw [chi_neg, utl_neg]

lemma measurable_utl0 : Measurable utl0 := contDiff_chi.continuous.measurable.mul measurable_utl
lemma measurable_utl1 : Measurable utl1 :=
  (measurable_const.sub contDiff_chi.continuous.measurable).mul measurable_utl

lemma abs_utl0_le : ∃ M : ℝ, ∀ t, |utl0 t| ≤ M * wlog t := by
  obtain ⟨M, hM⟩ := utl_wlog
  refine ⟨M, fun t => ?_⟩
  unfold utl0
  rw [abs_mul, abs_of_nonneg (chi_nonneg t)]
  calc chi t * |utl t| ≤ 1 * |utl t| := mul_le_mul_of_nonneg_right (chi_le_one t) (abs_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hM t

lemma abs_utl1_le : ∃ M : ℝ, ∀ t, |utl1 t| ≤ M * wlog t := by
  obtain ⟨M, hM⟩ := utl_wlog
  refine ⟨M, fun t => ?_⟩
  unfold utl1
  have : |1 - chi t| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [chi_nonneg t, chi_le_one t]
  rw [abs_mul]
  calc |1 - chi t| * |utl t| ≤ 1 * |utl t| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hM t

lemma integrable_utl0 : Integrable utl0 := by
  obtain ⟨M0, hM0⟩ := abs_utl0_le
  have hM : ∀ t, |utl0 t| ≤ |M0| * wlog t := fun t =>
    (hM0 t).trans (mul_le_mul_of_nonneg_right (le_abs_self M0) (by unfold wlog; positivity))
  have h := (integrable_wlog_exp (c := π) Real.pi_pos).const_mul (|M0| * Real.exp (2 * π))
  refine Integrable.mono' h measurable_utl0.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs]
  have hw : 0 ≤ wlog t := by unfold wlog; positivity
  by_cases ht : 2 ≤ |t|
  · rw [utl0_eq_zero ht]; simp only [abs_zero]
    positivity
  · have he : 1 ≤ Real.exp (2 * π) * Real.exp (-π * |t|) := by
      rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith only [Real.pi_pos, not_le.mp ht]
    have h0 : 0 ≤ |M0| * wlog t := by positivity
    calc |utl0 t| ≤ |M0| * wlog t := hM t
      _ ≤ |M0| * wlog t * (Real.exp (2 * π) * Real.exp (-π * |t|)) := by nlinarith only [h0, he]
      _ = |M0| * Real.exp (2 * π) * (wlog t * Real.exp (-π * |t|)) := by ring

/-- `ũ₁` is `C^∞`. -/
lemma contDiff_utl1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) utl1 := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t = 0
  · subst ht
    have hev : utl1 =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℝ) := by
      have : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), |s| < 1 := by
        have := (continuous_abs (G := ℝ)).continuousAt (x := (0 : ℝ))
        exact this.eventually (Iio_mem_nhds (by simp))
      filter_upwards [this] with s hs using utl1_eq_zero hs.le
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact ((contDiffAt_const.sub contDiff_chi.contDiffAt).mul (contDiffAt_utl ht))

/-- Iterated derivatives of an even/odd function have the same absolute value at `t` and `-t`. -/
lemma abs_iteratedDeriv_neg {f : ℝ → ℝ} {c : ℝ} (hc : |c| = 1) (hf : ∀ x, f (-x) = c * f x)
    (hd : ∀ n : ℕ, ContDiff ℝ n f) (n : ℕ) (t : ℝ) :
    |iteratedDeriv n f (-t)| = |iteratedDeriv n f t| := by
  have h1 := iteratedDeriv_comp_neg n f t
  have e : (fun x => f (-x)) = fun x => c * f x := funext hf
  rw [e, iteratedDeriv_const_mul c (hd n).contDiffAt] at h1
  have h2 := congrArg abs h1
  rw [abs_mul, hc, one_mul, smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at h2
  exact h2.symm

/-- **Derivative bounds for `ũ₁`**: `|ũ₁^{(n)}(t)| ≤ A_n (1+|t|) e^{-π|t|}`. -/
theorem utl1_deriv_bound (n : ℕ) :
    ∃ A : ℝ, ∀ t : ℝ, |iteratedDeriv n utl1 t| ≤ A * ((1 + |t|) * Real.exp (-π * |t|)) := by
  obtain ⟨K, hK⟩ := utl_deriv_bound n
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) utl1 := contDiff_utl1
  have hcont : Continuous (iteratedDeriv n utl1) := hc.continuous_iteratedDeriv n (by exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := iteratedDeriv n utl1) (s := Icc (-5 : ℝ) 5)
    hcont.continuousOn
  have hdn : ∀ m : ℕ, ContDiff ℝ m utl1 := fun m => hc.of_le (by exact_mod_cast le_top)
  refine ⟨|K| + |B| * Real.exp (5 * π), fun t => ?_⟩
  have hq : 0 ≤ (1 + |t|) * Real.exp (-π * |t|) := by positivity
  have far : ∀ u : ℝ, 5 ≤ u → |iteratedDeriv n utl1 u| ≤ (|K| + |B| * Real.exp (5 * π)) * ((1 + |u|) * Real.exp (-π * |u|)) := by
    intro u hu
    have hev : utl1 =ᶠ[𝓝 u] utl := by
      have : ∀ᶠ s : ℝ in 𝓝 u, 5 / 2 < s := lt_mem_nhds (by linarith)
      filter_upwards [this] with s hs
      exact utl1_eq (by rw [abs_of_pos (by linarith)]; linarith)
    rw [hev.iteratedDeriv_eq n, abs_of_nonneg (by linarith : (0 : ℝ) ≤ u)]
    have := hK u hu
    calc _ ≤ K * ((u + 1) * Real.exp (-π * u)) := this
      _ ≤ |K| * ((1 + u) * Real.exp (-π * u)) := by
          rw [add_comm u 1]; exact mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
      _ ≤ _ := by
          rw [add_mul]; have : 0 ≤ |B| * Real.exp (5 * π) * ((1 + u) * Real.exp (-π * u)) := by positivity
          linarith only [this]
  by_cases h5 : 5 ≤ |t|
  · rcases le_abs'.mp h5 with h | h
    · -- t ≤ -5
      have hn := abs_iteratedDeriv_neg (f := utl1) (c := 1) (by simp) (fun x => by rw [utl1_neg, one_mul]) hdn n (-t)
      rw [neg_neg] at hn
      rw [hn]
      have := far (-t) (by linarith)
      rwa [abs_neg] at this
    · exact far t h
  · have ht : t ∈ Icc (-5 : ℝ) 5 := ⟨by linarith [abs_le.mp (not_le.mp h5).le |>.1], by linarith [abs_le.mp (not_le.mp h5).le |>.2]⟩
    have h1 := hB t ht
    rw [Real.norm_eq_abs] at h1
    have h2 : Real.exp (-(5 * π)) ≤ (1 + |t|) * Real.exp (-π * |t|) := by
      have : Real.exp (-(5 * π)) ≤ Real.exp (-π * |t|) := by
        apply Real.exp_le_exp.mpr; nlinarith only [Real.pi_pos, not_le.mp h5]
      have h3 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
      nlinarith only [this, h3, Real.exp_pos (-π * |t|)]
    have hex : Real.exp (5 * π) * Real.exp (-(5 * π)) = 1 := by rw [← Real.exp_add]; simp
    calc |iteratedDeriv n utl1 t| ≤ B := h1
      _ ≤ |B| := le_abs_self B
      _ = |B| * Real.exp (5 * π) * Real.exp (-(5 * π)) := by rw [mul_assoc, hex, mul_one]
      _ ≤ |B| * Real.exp (5 * π) * ((1 + |t|) * Real.exp (-π * |t|)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ _ := by
          have : 0 ≤ |K| * ((1 + |t|) * Real.exp (-π * |t|)) := by positivity
          nlinarith only [this]

/-- info: 'FormalResearch.SignUncertainty.CtOuter.utl1_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms utl1_deriv_bound

end FormalResearch.SignUncertainty.CtOuter
