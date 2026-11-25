module

public import FormalResearch.SignUncertainty.CtOuterU2
public import FormalResearch.SignUncertainty.CtOuterBdryIm
public import FormalResearch.SignUncertainty.CtOuterLogId

/-!
# Differentiating the boundary functional

**Proved.**  For a `C²` amplitude `b` with `b, b', b''` bounded, `F_b(τ) = ∫ (b(τ+s) - b(τ))/sinh(πs) ds` is differentiable with
`F_b' = F_{b'}`; hence for smooth `b` with all derivatives bounded, `d^n/dτ^n F_b = F_{b^{(n)}}`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- `F_b(τ) = ∫ (b(τ+s) - b(τ)) / sinh(πs) ds` (the same as `bdryF`, in the variable `s = t - τ`). -/
lemma bdryF_eq_shift (b : ℝ → ℝ) (τ : ℝ) :
    bdryF b τ = ∫ s : ℝ, (b (τ + s) - b τ) / Real.sinh (π * s) := by
  unfold bdryF
  rw [← integral_add_left_eq_self (fun t : ℝ => (b t - b τ) / Real.sinh (π * (t - τ))) τ]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [add_sub_cancel_left]

lemma abs_inv_sinh_le_far {s : ℝ} (hs : 1 ≤ |s|) : 1 / |Real.sinh (π * s)| ≤ 4 * Real.exp (-π * |s|) := by
  have h := exp_div_four_le_sinh (t := π * |s|) (by nlinarith [Real.pi_gt_three])
  rw [abs_sinh_pi]
  have hpos : 0 < Real.exp (π * |s|) / 4 := by positivity
  rw [div_le_iff₀ (by exact lt_of_lt_of_le hpos h)]
  calc (1 : ℝ) = 4 * Real.exp (-π * |s|) * (Real.exp (π * |s|) / 4) := by
        rw [neg_mul, Real.exp_neg]; field_simp
    _ ≤ 4 * Real.exp (-π * |s|) * Real.sinh (π * |s|) := by
        apply mul_le_mul_of_nonneg_left h (by positivity)

lemma abs_div_sinh_le_near {s : ℝ} (hs : s ≠ 0) : |s| / |Real.sinh (π * s)| ≤ 1 / π := by
  have hsh : π * |s| ≤ |Real.sinh (π * s)| := by
    rw [abs_sinh_pi]; exact Real.self_le_sinh_iff.mpr (by positivity)
  have hpos : 0 < |s| := abs_pos.mpr hs
  rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
  nlinarith [mul_comm π |s|]


/-- Majorant `c 1_{[-1,1]} + d e^{-π|s|}`. -/
noncomputable def majS (c d : ℝ) (s : ℝ) : ℝ :=
  c * (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) s + d * Real.exp (-π * |s|)

lemma integrable_majS (c d : ℝ) : Integrable (majS c d) := by
  have h1 : Integrable fun s : ℝ => c * (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) s :=
    (((integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))).const_mul c)
  exact h1.add ((integrable_exp_neg_abs' Real.pi_pos).const_mul d)

lemma majS_nonneg {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (s : ℝ) : 0 ≤ majS c d s := by
  unfold majS
  have : 0 ≤ (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) s := indicator_nonneg (fun _ _ => zero_le_one) s
  positivity

/-- MVT: `|f(τ+s) - f(τ)| ≤ B |s|` if `|f'| ≤ B`. -/
lemma abs_shift_sub_le {f g : ℝ → ℝ} (hd : ∀ t, HasDerivAt f (g t) t) {B : ℝ} (hB : ∀ t, |g t| ≤ B)
    (τ s : ℝ) : |f (τ + s) - f τ| ≤ B * |s| := by
  have hd' : ∀ x : ℝ, HasDerivAt (fun x : ℝ => f (τ + x)) (g (τ + x)) x := fun x =>
    ((hd (τ + x)).comp x ((hasDerivAt_id x).const_add τ)).congr_deriv (by simp)
  have := abs_sub_le_of_deriv hd' (r := |s|) (K := B) (x := s) (fun y _ => hB (τ + y)) le_rfl
  simpa using this

/-- Pointwise bound for the integrand of `F_b`: `|(h(τ+s) - h(τ))/sinh(πs)| ≤ majS(B1/π, 8 B0)`. -/
lemma shift_integrand_le {h h' : ℝ → ℝ} (hd : ∀ t, HasDerivAt h (h' t) t) {B0 B1 : ℝ}
    (hB0 : ∀ t, |h t| ≤ B0) (hB1 : ∀ t, |h' t| ≤ B1) (τ s : ℝ) :
    |(h (τ + s) - h τ) / Real.sinh (π * s)| ≤ majS (B1 / π) (8 * B0) s := by
  have hB10 : 0 ≤ B1 := (abs_nonneg _).trans (hB1 0)
  have hB00 : 0 ≤ B0 := (abs_nonneg _).trans (hB0 0)
  rw [abs_div]
  by_cases hs : |s| ≤ 1
  · have hmem : s ∈ Icc (-1 : ℝ) 1 := abs_le.mp hs
    unfold majS
    rw [indicator_of_mem hmem]
    by_cases h0 : s = 0
    · subst h0; simp
      positivity
    have := abs_shift_sub_le hd hB1 τ s
    have h2 := abs_div_sinh_le_near h0
    have hpos : 0 < |Real.sinh (π * s)| := by
      rw [abs_sinh_pi]; exact Real.sinh_pos_iff.mpr (by have := abs_pos.mpr h0; positivity)
    calc |h (τ + s) - h τ| / |Real.sinh (π * s)| ≤ (B1 * |s|) / |Real.sinh (π * s)| :=
          div_le_div_of_nonneg_right this hpos.le
      _ = B1 * (|s| / |Real.sinh (π * s)|) := by ring
      _ ≤ B1 * (1 / π) := mul_le_mul_of_nonneg_left h2 hB10
      _ ≤ B1 / π * 1 + 8 * B0 * Real.exp (-π * |s|) := by
          have : 0 ≤ 8 * B0 * Real.exp (-π * |s|) := by positivity
          linarith [show B1 * (1 / π) = B1 / π * 1 by ring]
  · have hfar := abs_inv_sinh_le_far (not_le.mp hs).le
    have hmem : s ∉ Icc (-1 : ℝ) 1 := fun h => hs (abs_le.mpr ⟨h.1, h.2⟩)
    unfold majS
    rw [indicator_of_notMem hmem, mul_zero, zero_add]
    have hnum : |h (τ + s) - h τ| ≤ 2 * B0 := by
      calc _ ≤ |h (τ + s)| + |h τ| := abs_sub _ _
        _ ≤ B0 + B0 := add_le_add (hB0 _) (hB0 _)
        _ = 2 * B0 := by ring
    calc |h (τ + s) - h τ| / |Real.sinh (π * s)| = |h (τ + s) - h τ| * (1 / |Real.sinh (π * s)|) := by ring
      _ ≤ (2 * B0) * (4 * Real.exp (-π * |s|)) :=
          mul_le_mul hnum hfar (by positivity) (by positivity)
      _ = 8 * B0 * Real.exp (-π * |s|) := by ring

/-- **`d/dτ F_b = F_{b'}`.** -/
theorem hasDerivAt_bdryF {b b' b'' : ℝ → ℝ} (hb : ∀ t, HasDerivAt b (b' t) t)
    (hb' : ∀ t, HasDerivAt b' (b'' t) t) {B0 B1 B2 : ℝ} (h0 : ∀ t, |b t| ≤ B0) (h1 : ∀ t, |b' t| ≤ B1)
    (h2 : ∀ t, |b'' t| ≤ B2) (τ : ℝ) : HasDerivAt (bdryF b) (bdryF b' τ) τ := by
  have hB00 : 0 ≤ B0 := (abs_nonneg _).trans (h0 0)
  have hB10 : 0 ≤ B1 := (abs_nonneg _).trans (h1 0)
  have hB20 : 0 ≤ B2 := (abs_nonneg _).trans (h2 0)
  have hfun : bdryF b = fun x : ℝ => ∫ s : ℝ, (b (x + s) - b x) / Real.sinh (π * s) := funext (bdryF_eq_shift b)
  rw [hfun, bdryF_eq_shift b']
  have hsm : ∀ x : ℝ, Measurable fun s : ℝ => (b (x + s) - b x) / Real.sinh (π * s) := by
    intro x
    have hc : Continuous b := continuous_iff_continuousAt.2 fun t => (hb t).continuousAt
    exact ((hc.comp (continuous_const.add continuous_id)).measurable.sub measurable_const).div
      (by fun_prop)
  have hsm' : ∀ x : ℝ, Measurable fun s : ℝ => (b' (x + s) - b' x) / Real.sinh (π * s) := by
    intro x
    have hc : Continuous b' := continuous_iff_continuousAt.2 fun t => (hb' t).continuousAt
    exact ((hc.comp (continuous_const.add continuous_id)).measurable.sub measurable_const).div
      (by fun_prop)
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (s := univ) (x₀ := τ)
    (F := fun x s => (b (x + s) - b x) / Real.sinh (π * s))
    (F' := fun x s => (b' (x + s) - b' x) / Real.sinh (π * s))
    (bound := majS (B2 / π) (8 * B1)) Filter.univ_mem
    (Eventually.of_forall fun x => (hsm x).aestronglyMeasurable)
    (by
      refine Integrable.mono' (integrable_majS (B1 / π) (8 * B0)) (hsm τ).aestronglyMeasurable
        (Eventually.of_forall fun s => ?_)
      rw [Real.norm_eq_abs]; exact shift_integrand_le hb h0 h1 τ s)
    (hsm' τ).aestronglyMeasurable
    (Eventually.of_forall fun s x _ => by
      rw [Real.norm_eq_abs]; exact shift_integrand_le hb' h1 h2 x s)
    (integrable_majS _ _)
    (Eventually.of_forall fun s x _ => by
      have h3 : HasDerivAt (fun y : ℝ => b (y + s) - b y) (b' (x + s) - b' x) x := by
        have := ((hb (x + s)).comp x ((hasDerivAt_id x).add_const s)).sub (hb x)
        exact this.congr_deriv (by simp)
      have := h3.div_const (Real.sinh (π * s))
      simpa [add_comm] using this)
  exact this.2


/-- **`d^n/dτ^n F_b = F_{b^{(n)}}`** for smooth `b` all of whose derivatives are bounded. -/
theorem iteratedDeriv_bdryF {b : ℝ → ℝ} (hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b)
    (hbd : ∀ n : ℕ, ∃ B : ℝ, ∀ t : ℝ, |iteratedDeriv n b t| ≤ B) :
    ∀ n : ℕ, iteratedDeriv n (bdryF b) = bdryF (iteratedDeriv n b) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext τ
    have hd : ∀ m : ℕ, ∀ t : ℝ, HasDerivAt (iteratedDeriv m b) (iteratedDeriv (m + 1) b t) t := by
      intro m t
      have := (hb.differentiable_iteratedDeriv m (by exact_mod_cast WithTop.coe_lt_top _)) t
      have h := this.hasDerivAt
      rwa [← iteratedDeriv_succ] at h
    obtain ⟨B0, hB0⟩ := hbd n
    obtain ⟨B1, hB1⟩ := hbd (n + 1)
    obtain ⟨B2, hB2⟩ := hbd (n + 2)
    exact (hasDerivAt_bdryF (hd n) (hd (n + 1)) hB0 hB1 hB2 τ).deriv

/-- info: 'FormalResearch.SignUncertainty.CtOuter.hasDerivAt_bdryF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_bdryF

/-- info: 'FormalResearch.SignUncertainty.CtOuter.iteratedDeriv_bdryF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms iteratedDeriv_bdryF

end FormalResearch.SignUncertainty.CtOuter
