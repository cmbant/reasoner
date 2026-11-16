module

public import Mathlib

/-!
# Hadamard's lemma in `C^k` via the parametric integral `∫₀¹ w(t) K(c + t(q - c)) dt`

Mathlib has the analytic version (`dslope` of an analytic function is analytic) but no `C^k` version.  Here:

* `hadInt w K c q = ∫₀¹ w(t) K(c + t(q-c)) dt`; `continuousOn_hadInt`, `hasDerivAt_hadInt` (derivative
  `hadInt (t·w) K'`, by dominated differentiation under the integral) and by induction `contDiffOn_hadInt`
  (`K ∈ C^m` on a ball `⇒ hadInt w K c ∈ C^m` on that ball, for continuous `w`);
* `dslope_eq_hadInt`: `(F q - F c)/(q - c) = ∫₀¹ F'(c + t(q-c)) dt`;
* `contDiffAt_dslope`: `F ∈ C^{m+1}` at `c` `⇒` `dslope F c ∈ C^m` at `c`.
-/

@[expose] public section

open Filter Topology Set MeasureTheory Metric

namespace FormalResearch.Special

/-- The Hadamard integral `q ↦ ∫₀¹ w(t) K(c + t (q - c)) dt`. -/
noncomputable def hadInt (w K : ℝ → ℝ) (c q : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, w t * K (c + t * (q - c))

lemma hadInt_mem_ball {c ρ q t : ℝ} (hq : q ∈ ball c ρ) (ht : t ∈ Icc (0 : ℝ) 1) :
    c + t * (q - c) ∈ ball c ρ := by
  rw [mem_ball, Real.dist_eq] at hq ⊢
  have : |c + t * (q - c) - c| = t * |q - c| := by
    rw [add_sub_cancel_left, abs_mul, abs_of_nonneg ht.1]
  rw [this]
  calc t * |q - c| ≤ 1 * |q - c| := by gcongr; exact ht.2
    _ = |q - c| := one_mul _
    _ < ρ := hq

lemma hadInt_cont_t {w K : ℝ → ℝ} {c ρ q : ℝ} (hw : Continuous w)
    (hK : ContinuousOn K (ball c ρ)) (hq : q ∈ ball c ρ) :
    ContinuousOn (fun t => w t * K (c + t * (q - c))) (Icc 0 1) := by
  refine hw.continuousOn.mul ?_
  refine hK.comp (by fun_prop) fun t ht => hadInt_mem_ball hq ht

lemma hadInt_integrand_bound {c : ℝ} {r ρ : ℝ} (hr : r < ρ) {K : ℝ → ℝ}
    (hK : ContinuousOn K (ball c ρ)) (w : ℝ → ℝ) (hw : Continuous w) :
    ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall c r,
      ‖w t * K (c + t * (x - c))‖ ≤ B := by
  obtain ⟨B1, hB1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hw.continuousOn
  obtain ⟨B2, hB2⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn
    (hK.mono (closedBall_subset_ball hr))
  refine ⟨B1 * B2, fun t ht x hx => ?_⟩
  rw [norm_mul]
  refine mul_le_mul (hB1 t ht) (hB2 _ ?_) (norm_nonneg _) ((norm_nonneg _).trans (hB1 t ht))
  rw [mem_closedBall, Real.dist_eq] at hx ⊢
  have : |c + t * (x - c) - c| = t * |x - c| := by
    rw [add_sub_cancel_left, abs_mul, abs_of_nonneg ht.1]
  rw [this]
  calc t * |x - c| ≤ 1 * |x - c| := by gcongr; exact ht.2
    _ = |x - c| := one_mul _
    _ ≤ r := hx

lemma continuousOn_hadInt {w K : ℝ → ℝ} {c ρ : ℝ} (hw : Continuous w)
    (hK : ContinuousOn K (ball c ρ)) : ContinuousOn (hadInt w K c) (ball c ρ) := by
  intro q hq
  apply ContinuousAt.continuousWithinAt
  obtain ⟨r, hqr, hrρ⟩ : ∃ r, dist q c < r ∧ r < ρ := exists_between (mem_ball.1 hq)
  obtain ⟨B, hB⟩ := hadInt_integrand_bound hrρ hK w hw
  have hs : ball c r ∈ 𝓝 q := isOpen_ball.mem_nhds (mem_ball.2 hqr)
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => B) ?_ ?_ ?_ ?_
  · filter_upwards [hs] with x hx
    exact ((hadInt_cont_t hw hK (ball_subset_ball hrρ.le hx)).mono
      (by simpa using Ioc_subset_Icc_self)).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [hs] with x hx
    refine Eventually.of_forall fun t ht => hB t (Ioc_subset_Icc_self (by simpa using ht)) x
      (ball_subset_closedBall hx)
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun t ht => ?_
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self (by simpa using ht)
    refine ContinuousAt.mul continuousAt_const ?_
    have hKc : ContinuousAt K (c + t * (q - c)) :=
      hK.continuousAt (isOpen_ball.mem_nhds (hadInt_mem_ball hq ht'))
    exact hKc.comp (f := fun x => c + t * (x - c)) (by fun_prop)


lemma hasDerivAt_hadInt {w K : ℝ → ℝ} {c ρ q : ℝ} (hw : Continuous w)
    (hK : ContDiffOn ℝ 1 K (ball c ρ)) (hq : q ∈ ball c ρ) :
    HasDerivAt (hadInt w K c) (hadInt (fun t => t * w t) (deriv K) c q) q := by
  have hKc : ContinuousOn K (ball c ρ) := hK.continuousOn
  have hK' : ContinuousOn (deriv K) (ball c ρ) :=
    hK.continuousOn_deriv_of_isOpen isOpen_ball le_rfl
  have hwt : Continuous (fun t => t * w t) := continuous_id.mul hw
  obtain ⟨r, hqr, hrρ⟩ : ∃ r, dist q c < r ∧ r < ρ := exists_between (mem_ball.1 hq)
  obtain ⟨B, hB⟩ := hadInt_integrand_bound hrρ hK' (fun t => t * w t) hwt
  have hs : ball c r ∈ 𝓝 q := isOpen_ball.mem_nhds (mem_ball.2 hqr)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 1)
    (F := fun x t => w t * K (c + t * (x - c)))
    (F' := fun x t => (t * w t) * deriv K (c + t * (x - c))) (x₀ := q) (s := ball c r)
    (bound := fun _ => B) hs ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · exact key.2
  · filter_upwards [hs] with x hx
    exact ((hadInt_cont_t hw hKc (ball_subset_ball hrρ.le hx)).mono
      (by simpa using Ioc_subset_Icc_self)).aestronglyMeasurable measurableSet_Ioc
  · exact (hadInt_cont_t hw hKc hq).intervalIntegrable_of_Icc zero_le_one
  · exact ((hadInt_cont_t hwt hK' hq).mono
      (by simpa using Ioc_subset_Icc_self)).aestronglyMeasurable measurableSet_Ioc
  · refine Eventually.of_forall fun t ht x hx => hB t (Ioc_subset_Icc_self (by simpa using ht)) x
      (ball_subset_closedBall hx)
  · refine Eventually.of_forall fun t ht x hx => ?_
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self (by simpa using ht)
    have hxρ : x ∈ ball c ρ := ball_subset_ball hrρ.le hx
    have hKd : DifferentiableAt ℝ K (c + t * (x - c)) :=
      (hK.differentiableOn one_ne_zero).differentiableAt
        (isOpen_ball.mem_nhds (hadInt_mem_ball hxρ ht'))
    have h1 : HasDerivAt (fun x : ℝ => c + t * (x - c)) t x := by
      simpa using (((hasDerivAt_id x).sub_const c).const_mul t).const_add c
    have := (hKd.hasDerivAt.comp x h1).const_mul (w t)
    convert this using 1
    simp only [Function.comp_apply]
    ring

lemma contDiffOn_hadInt {c ρ : ℝ} (m : ℕ) : ∀ (w K : ℝ → ℝ), Continuous w →
    ContDiffOn ℝ m K (ball c ρ) → ContDiffOn ℝ m (hadInt w K c) (ball c ρ) := by
  induction m with
  | zero =>
    intro w K hw hK
    rw [Nat.cast_zero, contDiffOn_zero] at hK ⊢
    exact continuousOn_hadInt hw hK
  | succ m ih =>
    intro w K hw hK
    have hK1 : ContDiffOn ℝ 1 K (ball c ρ) :=
      hK.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m))
    have hdK : ContDiffOn ℝ m (deriv K) (ball c ρ) :=
      hK.deriv_of_isOpen isOpen_ball (by simp)
    have hwt : Continuous (fun t => t * w t) := continuous_id.mul hw
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_ball]
    refine ⟨fun q hq => (hasDerivAt_hadInt hw hK1 hq).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    exact (ih _ _ hwt hdK).congr fun q hq => (hasDerivAt_hadInt hw hK1 hq).deriv


lemma exists_ball_contDiffOn {F : ℝ → ℝ} {c : ℝ} {n : ℕ} (h : ContDiffAt ℝ n F c) :
    ∃ ρ > 0, ContDiffOn ℝ n F (ball c ρ) := by
  have h1 : ∀ᶠ y in 𝓝 c, ContDiffAt ℝ n F y := h.eventually (by simp)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 h1
  exact ⟨ρ, hρ, fun y hy => (hball y hy).contDiffWithinAt⟩

/-- Hadamard's lemma in integral form: `(F q - F c)/(q - c) = ∫₀¹ F'(c + t (q - c)) dt`. -/
lemma dslope_eq_hadInt {F : ℝ → ℝ} {c ρ q : ℝ} (hF : ContDiffOn ℝ 1 F (ball c ρ))
    (hq : q ∈ ball c ρ) : dslope F c q = hadInt (fun _ => 1) (deriv F) c q := by
  have hK' : ContinuousOn (deriv F) (ball c ρ) :=
    hF.continuousOn_deriv_of_isOpen isOpen_ball le_rfl
  by_cases hqc : q = c
  · subst hqc
    simp [hadInt, dslope_same]
  · rw [dslope_of_ne _ hqc, slope_def_field]
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => F (c + t * (q - c))) ((q - c) * deriv F (c + t * (q - c))) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hFd : DifferentiableAt ℝ F (c + t * (q - c)) :=
        (hF.differentiableOn one_ne_zero).differentiableAt
          (isOpen_ball.mem_nhds (hadInt_mem_ball hq ht))
      have h1 : HasDerivAt (fun t : ℝ => c + t * (q - c)) (q - c) t := by
        simpa using ((hasDerivAt_id t).mul_const (q - c)).const_add c
      exact (hFd.hasDerivAt.comp t h1).congr_deriv (mul_comm _ _)
    have hcont : ContinuousOn (fun t : ℝ => (q - c) * deriv F (c + t * (q - c))) (Icc 0 1) := by
      refine continuousOn_const.mul ?_
      exact hK'.comp (by fun_prop) fun t ht => hadInt_mem_ball hq ht
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable_of_Icc zero_le_one)
    rw [intervalIntegral.integral_const_mul] at hint
    have e1 : c + 1 * (q - c) = q := by ring
    have e0 : c + 0 * (q - c) = c := by ring
    rw [e1, e0] at hint
    simp only [hadInt, one_mul]
    have hne : q - c ≠ 0 := sub_ne_zero.2 hqc
    rw [div_eq_iff hne]
    linarith

lemma contDiffOn_dslope {F : ℝ → ℝ} {c ρ : ℝ} (m : ℕ) (hF : ContDiffOn ℝ (m + 1 : ℕ) F (ball c ρ)) :
    ContDiffOn ℝ m (dslope F c) (ball c ρ) := by
  have hF1 : ContDiffOn ℝ 1 F (ball c ρ) :=
    hF.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m))
  have hdK : ContDiffOn ℝ m (deriv F) (ball c ρ) := hF.deriv_of_isOpen isOpen_ball (by simp)
  exact (contDiffOn_hadInt m _ _ continuous_const hdK).congr fun q hq => dslope_eq_hadInt hF1 hq


/-- Hadamard's lemma: if `F ∈ C^{m+1}` at `c` then `dslope F c` (the difference quotient with its
value `F'(c)` at `c`) is `C^m` at `c`. -/
theorem contDiffAt_dslope {F : ℝ → ℝ} {c : ℝ} (m : ℕ)
    (hF : ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) F c) : ContDiffAt ℝ m (dslope F c) c := by
  obtain ⟨ρ, hρ, hFb⟩ := exists_ball_contDiffOn hF
  exact (contDiffOn_dslope m hFb).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hρ))

/-- info: 'FormalResearch.Special.contDiffOn_hadInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.contDiffOn_hadInt

/-- info: 'FormalResearch.Special.contDiffAt_dslope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.contDiffAt_dslope

end FormalResearch.Special
