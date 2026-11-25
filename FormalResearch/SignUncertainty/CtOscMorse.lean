module

public import FormalResearch.SignUncertainty.CtMorseExpansion
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Stationary phase with a variable phase (Morse chart)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 4, Piece 1 (stationary-phase core).  **Proved.**

Averages `avg w G t = ∫₀¹ w(r) G(rt) dr` and their derivatives (Hadamard quotients of a phase).
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real Interval

namespace FormalResearch.SignUncertainty.CtOsc

/-- `avg w G t = ∫₀¹ w(r) G(r t) dr`. -/
noncomputable def avg (w G : ℝ → ℝ) (t : ℝ) : ℝ := ∫ r in (0 : ℝ)..1, w r * G (r * t)

lemma abs_avg_le {w G : ℝ → ℝ} {R M W : ℝ} (hw : ∀ r ∈ Icc (0 : ℝ) 1, |w r| ≤ W) (hG : ∀ y ∈ Ioo (-R) R, |G y| ≤ M)
    {t : ℝ} (ht : t ∈ Ioo (-R) R) : |avg w G t| ≤ W * M := by
  unfold avg
  have hW : 0 ≤ W := (abs_nonneg _).trans (hw 0 ⟨le_rfl, zero_le_one⟩)
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := W * M)
    (f := fun r => w r * G (r * t)) (fun r hr => by
      rw [uIoc_of_le zero_le_one] at hr
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := hw r ⟨hr.1.le, hr.2⟩
      have hrt : r * t ∈ Ioo (-R) R := by
        have h2 : |r * t| ≤ |t| := by
          rw [abs_mul, abs_of_nonneg hr.1.le]; exact mul_le_of_le_one_left (abs_nonneg _) hr.2
        have : |t| < R := abs_lt.mpr ht
        exact abs_lt.mp (by linarith)
      exact mul_le_mul h1 (hG _ hrt) (abs_nonneg _) hW)
  simpa [Real.norm_eq_abs] using this

lemma mem_Ioo_of_mul {R r t : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Ioo (-R) R) : r * t ∈ Ioo (-R) R := by
  have h2 : |r * t| ≤ |t| := by
    rw [abs_mul, abs_of_nonneg hr.1]; exact mul_le_of_le_one_left (abs_nonneg _) hr.2
  have : |t| < R := abs_lt.mpr ht
  exact abs_lt.mp (by linarith)

/-- Differentiation of an average under the integral sign. -/
lemma hasDerivAt_avg {G G1 : ℝ → ℝ} {R : ℝ} (hG : ∀ y ∈ Ioo (-R) R, HasDerivAt G (G1 y) y)
    (hG1 : ContinuousOn G1 (Ioo (-R) R)) {w : ℝ → ℝ} (hw : Continuous w) {t : ℝ} (ht : t ∈ Ioo (-R) R) :
    HasDerivAt (avg w G) (avg (fun r => w r * r) G1 t) t := by
  have hRt : |t| < R := abs_lt.mpr ht
  set R' : ℝ := (|t| + R) / 2 with hR'
  have hR'1 : |t| < R' := by rw [hR']; linarith
  have hR'2 : R' < R := by rw [hR']; linarith
  have hGc : ContinuousOn G (Ioo (-R) R) := fun y hy => (hG y hy).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R') (b := R')).exists_bound_of_continuousOn
    (hG1.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩))
  obtain ⟨W, hW⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hw.continuousOn
  have hmemR' : ∀ r ∈ Icc (0 : ℝ) 1, ∀ x ∈ Ioo (-R') R', r * x ∈ Ioo (-R) R := fun r hr x hx =>
    mem_Ioo_of_mul (R := R) hr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hs : Ioo (-R') R' ∈ 𝓝 t := Ioo_mem_nhds (by linarith [abs_nonneg t, neg_abs_le t]) (by linarith [le_abs_self t])
  have hFc : ∀ x ∈ Ioo (-R') R', ContinuousOn (fun r : ℝ => w r * G (r * x)) (Icc 0 1) := fun x hx =>
    hw.continuousOn.mul (hGc.comp (continuous_id.mul continuous_const).continuousOn
      (fun r hr => hmemR' r hr x hx))
  have hF'c : ∀ x ∈ Ioo (-R') R', ContinuousOn (fun r : ℝ => w r * (r * G1 (r * x))) (Icc 0 1) := fun x hx =>
    hw.continuousOn.mul (continuous_id.continuousOn.mul (hG1.comp (continuous_id.mul continuous_const).continuousOn
      (fun r hr => hmemR' r hr x hx)))
  have htR' : t ∈ Ioo (-R') R' := ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have hfin := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := (0 : ℝ)) (b := 1)
    (F := fun x r => w r * G (r * x)) (F' := fun x r => w r * (r * G1 (r * x)))
    (x₀ := t) (s := Ioo (-R') R') (bound := fun _ => W * M) hs
    (by
      filter_upwards [hs] with x hx
      rw [uIoc_of_le zero_le_one]
      exact ((hFc x hx).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    (((hFc t htR').intervalIntegrable_of_Icc zero_le_one))
    (by
      rw [uIoc_of_le zero_le_one]
      exact ((hF'c t htR').mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    (Eventually.of_forall fun r hr x hx => by
      rw [uIoc_of_le zero_le_one] at hr
      have hr' : r ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hr
      have hrx : r * x ∈ Icc (-R') R' := by
        have := mem_Ioo_of_mul (R := R') hr' hx
        exact ⟨this.1.le, this.2.le⟩
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have hbw : |w r| ≤ W := by simpa using hW r hr'
      have hbG : |G1 (r * x)| ≤ M := by simpa using hM _ hrx
      have hr1 : |r| ≤ 1 := by rw [abs_of_nonneg hr'.1]; exact hr'.2
      calc |w r| * (|r| * |G1 (r * x)|) ≤ W * (1 * M) :=
            mul_le_mul hbw (mul_le_mul hr1 hbG (abs_nonneg _) zero_le_one) (by positivity) ((abs_nonneg _).trans hbw)
        _ = W * M := by ring)
    intervalIntegrable_const
    (Eventually.of_forall fun r hr x hx => by
      rw [uIoc_of_le zero_le_one] at hr
      have hr' : r ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hr
      have hrx : r * x ∈ Ioo (-R) R := hmemR' r hr' x hx
      have h1 : HasDerivAt (fun y : ℝ => r * y) r x := by simpa using (hasDerivAt_id' x).const_mul r
      have h2 := (hG _ hrx).scomp x h1
      have h3 := h2.const_mul (w r)
      refine h3.congr_deriv ?_
      simp [mul_comm, mul_left_comm])
  have := hfin.2
  unfold avg
  convert this using 1
  refine intervalIntegral.integral_congr fun r _ => ?_
  show (fun r => w r * r) r * G1 (r * t) = w r * (r * G1 (r * t))
  ring

/-- Continuity of an average of a continuous function. -/
lemma continuousOn_avg {G : ℝ → ℝ} {R : ℝ} (hG : ContinuousOn G (Ioo (-R) R)) {w : ℝ → ℝ} (hw : Continuous w) :
    ContinuousOn (avg w G) (Ioo (-R) R) := by
  intro t ht
  refine ContinuousAt.continuousWithinAt ?_
  have hRt : |t| < R := abs_lt.mpr ht
  set R' : ℝ := (|t| + R) / 2 with hR'
  have hR'1 : |t| < R' := by rw [hR']; linarith
  have hR'2 : R' < R := by rw [hR']; linarith
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R') (b := R')).exists_bound_of_continuousOn
    (hG.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩))
  obtain ⟨W, hW⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hw.continuousOn
  have hmemR' : ∀ r ∈ Icc (0 : ℝ) 1, ∀ x ∈ Ioo (-R') R', r * x ∈ Ioo (-R) R := fun r hr x hx =>
    mem_Ioo_of_mul (R := R) hr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hs : Ioo (-R') R' ∈ 𝓝 t := Ioo_mem_nhds (by linarith [abs_nonneg t, neg_abs_le t]) (by linarith [le_abs_self t])
  have hFc : ∀ x ∈ Ioo (-R') R', ContinuousOn (fun r : ℝ => w r * G (r * x)) (Icc 0 1) := fun x hx =>
    hw.continuousOn.mul (hG.comp (continuous_id.mul continuous_const).continuousOn
      (fun r hr => hmemR' r hr x hx))
  unfold avg
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => W * M) ?_ ?_
    intervalIntegrable_const ?_
  · filter_upwards [hs] with x hx
    rw [uIoc_of_le zero_le_one]
    exact ((hFc x hx).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [hs] with x hx
    refine Eventually.of_forall fun r hr => ?_
    rw [uIoc_of_le zero_le_one] at hr
    have hr' : r ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hr
    have hrx : r * x ∈ Icc (-R') R' := by
      have := mem_Ioo_of_mul (R := R') hr' hx
      exact ⟨this.1.le, this.2.le⟩
    rw [Real.norm_eq_abs, abs_mul]
    have hbw : |w r| ≤ W := by simpa using hW r hr'
    have hbG : |G (r * x)| ≤ M := by simpa using hM _ hrx
    exact mul_le_mul hbw hbG (abs_nonneg _) ((abs_nonneg _).trans hbw)
  · refine Eventually.of_forall fun r hr => ?_
    rw [uIoc_of_le zero_le_one] at hr
    have hr' : r ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hr
    have hrt : r * t ∈ Ioo (-R) R := mem_Ioo_of_mul hr' ht
    have h1 : ContinuousAt (fun x : ℝ => r * x) t := (continuous_const.mul continuous_id).continuousAt
    exact continuousAt_const.mul ((hG.continuousAt (Ioo_mem_nhds hrt.1 hrt.2)).comp h1)

lemma avg_ge {w G : ℝ → ℝ} {R m : ℝ} (hw : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ w r) (hwc : Continuous w)
    (hG : ∀ y ∈ Ioo (-R) R, m ≤ G y) (hGc : ContinuousOn G (Ioo (-R) R)) {t : ℝ} (ht : t ∈ Ioo (-R) R) :
    m * ∫ r in (0 : ℝ)..1, w r ≤ avg w G t := by
  unfold avg
  have hc : ContinuousOn (fun r : ℝ => w r * G (r * t)) (Icc 0 1) :=
    hwc.continuousOn.mul (hGc.comp (continuous_id.mul continuous_const).continuousOn
      (fun r hr => mem_Ioo_of_mul hr ht))
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on zero_le_one
    ((hwc.continuousOn.intervalIntegrable_of_Icc zero_le_one).const_mul m)
    (hc.intervalIntegrable_of_Icc zero_le_one) fun r hr => ?_
  rw [mul_comm m]
  exact mul_le_mul_of_nonneg_left (hG _ (mem_Ioo_of_mul hr ht)) (hw r hr)

/-- Data of a phase `φ` on `(-1,1)` with `φ(0) = φ'(0) = 0`, `φ'' = f ≥ c₁`, and `|f|, |f'|, |f''| ≤ C`;
`φ1 = φ'`, `f1 = f'`, `f2 = f''`. -/
structure Phase (c1 C : ℝ) (φ φ1 f f1 f2 : ℝ → ℝ) : Prop where
  d0 : ∀ y ∈ Ioo (-1 : ℝ) 1, HasDerivAt φ (φ1 y) y
  d1 : ∀ y ∈ Ioo (-1 : ℝ) 1, HasDerivAt φ1 (f y) y
  d2 : ∀ y ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 y) y
  d3 : ∀ y ∈ Ioo (-1 : ℝ) 1, HasDerivAt f1 (f2 y) y
  c2 : ContinuousOn f2 (Ioo (-1 : ℝ) 1)
  z0 : φ 0 = 0
  z1 : φ1 0 = 0
  lo : ∀ y ∈ Ioo (-1 : ℝ) 1, c1 ≤ f y
  b0 : ∀ y ∈ Ioo (-1 : ℝ) 1, |f y| ≤ C
  b1 : ∀ y ∈ Ioo (-1 : ℝ) 1, |f1 y| ≤ C
  b2 : ∀ y ∈ Ioo (-1 : ℝ) 1, |f2 y| ≤ C

/-- Hadamard quotients: `φ' = t ρ`, `φ = t² q / 2`. -/
noncomputable def rho (f : ℝ → ℝ) : ℝ → ℝ := avg (fun _ => 1) f
noncomputable def rho1 (f1 : ℝ → ℝ) : ℝ → ℝ := avg (fun r => r) f1
noncomputable def rho2 (f2 : ℝ → ℝ) : ℝ → ℝ := avg (fun r => r * r) f2
noncomputable def qf (f : ℝ → ℝ) : ℝ → ℝ := avg (fun r => 2 * r) (rho f)
noncomputable def q1f (f1 : ℝ → ℝ) : ℝ → ℝ := avg (fun r => 2 * r * r) (rho1 f1)
noncomputable def q2f (f2 : ℝ → ℝ) : ℝ → ℝ := avg (fun r => 2 * r * r * r) (rho2 f2)

section
variable {c1 C : ℝ} {φ φ1 f f1 f2 : ℝ → ℝ}

lemma Phase.cont0 (h : Phase c1 C φ φ1 f f1 f2) : ContinuousOn f (Ioo (-1 : ℝ) 1) :=
  fun y hy => (h.d2 y hy).continuousAt.continuousWithinAt
lemma Phase.cont1 (h : Phase c1 C φ φ1 f f1 f2) : ContinuousOn f1 (Ioo (-1 : ℝ) 1) :=
  fun y hy => (h.d3 y hy).continuousAt.continuousWithinAt

lemma Phase.hasDerivAt_rho (h : Phase c1 C φ φ1 f f1 f2) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (rho f) (rho1 f1 t) t := by
  have := hasDerivAt_avg (w := fun _ => (1 : ℝ)) h.d2 h.cont1 continuous_const ht
  have e : (fun r : ℝ => (fun _ : ℝ => (1 : ℝ)) r * r) = fun r => r := by funext r; simp
  rw [e] at this
  exact this

lemma Phase.hasDerivAt_rho1 (h : Phase c1 C φ φ1 f f1 f2) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (rho1 f1) (rho2 f2 t) t := by
  have := hasDerivAt_avg (w := fun r => r) h.d3 h.c2 continuous_id ht
  simpa only [rho1, rho2] using this

lemma Phase.cont_rho2 (h : Phase c1 C φ φ1 f f1 f2) : ContinuousOn (rho2 f2) (Ioo (-1 : ℝ) 1) :=
  continuousOn_avg h.c2 (continuous_id.mul continuous_id)

lemma Phase.cont_rho1 (h : Phase c1 C φ φ1 f f1 f2) : ContinuousOn (rho1 f1) (Ioo (-1 : ℝ) 1) :=
  fun y hy => (h.hasDerivAt_rho1 hy).continuousAt.continuousWithinAt

lemma Phase.cont_rho (h : Phase c1 C φ φ1 f f1 f2) : ContinuousOn (rho f) (Ioo (-1 : ℝ) 1) :=
  fun y hy => (h.hasDerivAt_rho hy).continuousAt.continuousWithinAt

lemma Phase.hasDerivAt_q (h : Phase c1 C φ φ1 f f1 f2) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (qf f) (q1f f1 t) t := by
  have := hasDerivAt_avg (w := fun r => 2 * r) (fun y hy => h.hasDerivAt_rho hy) h.cont_rho1
    (continuous_const.mul continuous_id) ht
  simpa only [qf, q1f] using this

lemma Phase.hasDerivAt_q1 (h : Phase c1 C φ φ1 f f1 f2) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (q1f f1) (q2f f2 t) t := by
  have := hasDerivAt_avg (w := fun r => 2 * r * r) (fun y hy => h.hasDerivAt_rho1 hy) h.cont_rho2
    ((continuous_const.mul continuous_id).mul continuous_id) ht
  simpa only [q1f, q2f] using this

lemma Phase.cont_q2 (h : Phase c1 C φ φ1 f f1 f2) : ContinuousOn (q2f f2) (Ioo (-1 : ℝ) 1) :=
  continuousOn_avg h.cont_rho2 (((continuous_const.mul continuous_id).mul continuous_id).mul continuous_id)

lemma Phase.cont_q1 (h : Phase c1 C φ φ1 f f1 f2) : ContinuousOn (q1f f1) (Ioo (-1 : ℝ) 1) :=
  fun y hy => (h.hasDerivAt_q1 hy).continuousAt.continuousWithinAt

lemma w1_le : ∀ r ∈ Icc (0 : ℝ) 1, |(fun _ : ℝ => (1 : ℝ)) r| ≤ 1 := fun r _ => by simp
lemma wr_le : ∀ r ∈ Icc (0 : ℝ) 1, |(fun r : ℝ => r) r| ≤ 1 := fun r hr => by
  simp only; rw [abs_of_nonneg hr.1]; exact hr.2
lemma wrr_le : ∀ r ∈ Icc (0 : ℝ) 1, |(fun r : ℝ => r * r) r| ≤ 1 := fun r hr => by
  simp only; rw [abs_of_nonneg (mul_nonneg hr.1 hr.1)]; nlinarith [hr.1, hr.2]
lemma w2r_le : ∀ r ∈ Icc (0 : ℝ) 1, |(fun r : ℝ => 2 * r) r| ≤ 2 := fun r hr => by
  simp only; rw [abs_of_nonneg (by linarith [hr.1])]; linarith [hr.2]
lemma w2rr_le : ∀ r ∈ Icc (0 : ℝ) 1, |(fun r : ℝ => 2 * r * r) r| ≤ 2 := fun r hr => by
  simp only; rw [abs_of_nonneg (by have := hr.1; positivity)]; nlinarith [hr.1, hr.2]
lemma w2rrr_le : ∀ r ∈ Icc (0 : ℝ) 1, |(fun r : ℝ => 2 * r * r * r) r| ≤ 2 := fun r hr => by
  simp only; rw [abs_of_nonneg (by have := hr.1; positivity)]
  have h1 := hr.1; have h2 := hr.2
  have : r * r ≤ 1 := by nlinarith
  have : r * r * r ≤ 1 := by nlinarith
  linarith

lemma Phase.abs_rho (h : Phase c1 C φ φ1 f f1 f2) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : |rho f t| ≤ 1 * C := abs_avg_le w1_le h.b0 ht
lemma Phase.abs_rho1 (h : Phase c1 C φ φ1 f f1 f2) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : |rho1 f1 t| ≤ 1 * C := abs_avg_le wr_le h.b1 ht
lemma Phase.abs_rho2 (h : Phase c1 C φ φ1 f f1 f2) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : |rho2 f2 t| ≤ 1 * C := abs_avg_le wrr_le h.b2 ht

lemma Phase.abs_q (h : Phase c1 C φ φ1 f f1 f2) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : |qf f t| ≤ 2 * (1 * C) :=
  abs_avg_le w2r_le (fun y hy => h.abs_rho hy) ht
lemma Phase.abs_q1 (h : Phase c1 C φ φ1 f f1 f2) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : |q1f f1 t| ≤ 2 * (1 * C) :=
  abs_avg_le w2rr_le (fun y hy => h.abs_rho1 hy) ht
lemma Phase.abs_q2 (h : Phase c1 C φ φ1 f f1 f2) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : |q2f f2 t| ≤ 2 * (1 * C) :=
  abs_avg_le w2rrr_le (fun y hy => h.abs_rho2 hy) ht

lemma int_one : ∫ r in (0 : ℝ)..1, (fun _ : ℝ => (1 : ℝ)) r = 1 := by simp
lemma int_two_r : ∫ r in (0 : ℝ)..1, (fun r : ℝ => 2 * r) r = 1 := by
  simp only []
  rw [intervalIntegral.integral_const_mul, integral_id]; norm_num

lemma Phase.rho_ge (h : Phase c1 C φ φ1 f f1 f2) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : c1 ≤ rho f t := by
  have := avg_ge (w := fun _ => (1 : ℝ)) (fun r _ => zero_le_one) continuous_const h.lo h.cont0 ht
  rwa [int_one, mul_one] at this

lemma Phase.q_ge (h : Phase c1 C φ φ1 f f1 f2) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : c1 ≤ qf f t := by
  have := avg_ge (w := fun r => 2 * r) (fun r hr => by have := hr.1; positivity)
    (continuous_const.mul continuous_id) (fun y hy => h.rho_ge hy) h.cont_rho ht
  rwa [int_two_r, mul_one] at this

lemma mem_Ioo_of_uIcc {t x : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (hx : x ∈ Set.uIcc 0 t) : x ∈ Ioo (-1 : ℝ) 1 :=
  (Set.ordConnected_Ioo (a := (-1 : ℝ)) (b := 1)).uIcc_subset (by norm_num : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1) ht hx

lemma Phase.phi1_eq (h : Phase c1 C φ φ1 f f1 f2) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : φ1 t = t * rho f t := by
  have h1 : ∫ x in (0 : ℝ)..t, f x = φ1 t - φ1 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => h.d1 x (mem_Ioo_of_uIcc ht hx))
      ((h.cont0.mono (fun x hx => mem_Ioo_of_uIcc ht hx)).intervalIntegrable)
  have h2 := intervalIntegral.smul_integral_comp_mul_right (a := (0 : ℝ)) (b := 1) (f := f) t
  rw [zero_mul, one_mul] at h2
  rw [h.z1, sub_zero] at h1
  rw [← h1, ← h2]
  simp only [rho, avg, one_mul, smul_eq_mul]

lemma Phase.cont_phi1 (h : Phase c1 C φ φ1 f f1 f2) : ContinuousOn φ1 (Ioo (-1 : ℝ) 1) :=
  fun y hy => (h.d1 y hy).continuousAt.continuousWithinAt

lemma Phase.phi_eq (h : Phase c1 C φ φ1 f f1 f2) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : φ t = t ^ 2 * qf f t / 2 := by
  have h1 : ∫ x in (0 : ℝ)..t, φ1 x = φ t - φ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => h.d0 x (mem_Ioo_of_uIcc ht hx))
      ((h.cont_phi1.mono (fun x hx => mem_Ioo_of_uIcc ht hx)).intervalIntegrable)
  rw [h.z0, sub_zero] at h1
  have h3 : ∫ x in (0 : ℝ)..t, φ1 x = ∫ x in (0 : ℝ)..t, x * rho f x :=
    intervalIntegral.integral_congr fun x hx => h.phi1_eq (mem_Ioo_of_uIcc ht (by simpa using hx))
  have h2 := intervalIntegral.smul_integral_comp_mul_right (a := (0 : ℝ)) (b := 1) (f := fun y => y * rho f y) t
  rw [zero_mul, one_mul] at h2
  have e1 : ∫ x in (0 : ℝ)..1, (x * t) * rho f (x * t) = t * ∫ x in (0 : ℝ)..1, x * rho f (x * t) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by first | ring | (simp only; ring)
  have e2 : qf f t = 2 * ∫ x in (0 : ℝ)..1, x * rho f (x * t) := by
    unfold qf avg
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by first | ring | (simp only; ring)
  rw [← h1, h3, ← h2, smul_eq_mul, e1, e2]
  ring

lemma Phase.q_zero (h : Phase c1 C φ φ1 f f1 f2) : qf f 0 = rho f 0 := by
  unfold qf avg
  simp only [mul_zero]
  rw [intervalIntegral.integral_mul_const]
  have := int_two_r
  simp only at this
  rw [this, one_mul]

/-- `q + t q'/2 = ρ` (so that `s = t √q` has `s' = ρ/√q`). -/
lemma Phase.q_id (h : Phase c1 C φ φ1 f f1 f2) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    qf f t + t * q1f f1 t / 2 = rho f t := by
  by_cases h0 : t = 0
  · subst h0; simp [h.q_zero]
  have hd : HasDerivAt (fun y => y ^ 2 * qf f y / 2) (t * qf f t + t ^ 2 * q1f f1 t / 2) t := by
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
    have := ((h1.mul (h.hasDerivAt_q ht)).div_const 2)
    convert this using 1; ring
  have heq : φ =ᶠ[𝓝 t] fun y => y ^ 2 * qf f y / 2 := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with y hy using h.phi_eq hy
  have h1 := (h.d0 t ht).congr_of_eventuallyEq heq.symm
  have := hd.unique h1
  rw [h.phi1_eq ht] at this
  have h2 : t * (qf f t + t * q1f f1 t / 2) = t * rho f t := by linarith
  exact mul_left_cancel₀ h0 h2

end

end FormalResearch.SignUncertainty.CtOsc
