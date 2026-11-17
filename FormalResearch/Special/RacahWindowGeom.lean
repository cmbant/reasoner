module

public import FormalResearch.Special.BulkKappaAmp
public import FormalResearch.Special.DiscreteAiryLimitChains2Racah

/-!
# Racah window, part 1: the phase of a centred Racah chain with `τ = +1`

For the centred Racah data `(P, Q, τ, x, q_*)` with `P, Q ≥ 0`, `0 < q_*`, `0 < 1 - P q_*²`, `0 < 1 - Q q_*²`, the turn `Φ(P, Q, 1, x, q_*²) = 0` and `|x| < 1`
(`RwGeo`), the function `u = hrU P Q 1 x` satisfies `0 < u < 1` on `[0, q_*)` (`u(q_*) = 1`): `Φ` is convex with `Φ(0) = x - 1 < 0`, and `x - β₀ σ ≥ x - β₀ q_*² = ẽ(q_*²) > 0`.
Consequences, the Racah counterparts of `BulkIndexSteps` and `BulkWindowChart.bwn_phase_bounds` (there `u = x/√(1-t²)`):

* `rwg_u_bounds`: on `[0, b]`, `b < q_*`, `lo ≤ u ≤ hi` with `0 < lo`, `hi < 1` (compactness);
* `rwg_phase_step`: for `0 ≤ q ≤ q' ≤ b`: `arccos(hi) (q' - q) ≤ Φ(q) - Φ(q') ≤ arccos(lo) (q' - q)`, with `arccos(hi) > 0`, `arccos(lo) < π/2`;
* `rwg_phase_bounds`: `0 ≤ Φ(q) ≤ (π/2)(q_* - q)` on `[0, q_*]`; `rwg_phase_pos`, `rwg_phase_ge`.

**Claim class: proved.**  **Not formalised:** `τ = -1` (there `u` can be negative and `arccos u` exceeds `π/2`).
-/

@[expose] public section

open Finset Set FormalResearch.Racah.P3
open scoped Real

namespace FormalResearch.Special

/-- The geometric hypotheses of the centred Racah chain with `τ = +1`. -/
structure RwGeo (P Q x qs : ℝ) : Prop where
  hP : 0 ≤ P
  hQ : 0 ≤ Q
  hqs : 0 < qs
  hα : 0 < 1 - P * qs ^ 2
  hβ : 0 < 1 - Q * qs ^ 2
  hturn : Phi P Q 1 x (qs ^ 2) = 0
  hx : -1 < x ∧ x < 1

namespace RwGeo

variable {P Q x qs : ℝ}

lemma hint (G : RwGeo P Q x qs) {t : ℝ} (ht : t ≤ qs) (ht0 : 0 ≤ t) : 0 < (1 - P * t ^ 2) * (1 - Q * t ^ 2) := by
  have h2 : t ^ 2 ≤ qs ^ 2 := pow_le_pow_left₀ ht0 ht 2
  have a1 : 0 < 1 - P * t ^ 2 := by nlinarith [G.hα, G.hP, sq_nonneg t]
  have a2 : 0 < 1 - Q * t ^ 2 := by nlinarith [G.hβ, G.hQ, sq_nonneg t]
  exact mul_pos a1 a2

lemma etilde_pos (G : RwGeo P Q x qs) {t : ℝ} (ht : t ≤ qs) (ht0 : 0 ≤ t) : 0 < etilde P Q (t ^ 2) := by
  unfold etilde; exact Real.sqrt_pos.2 (G.hint ht ht0)

lemma dom (G : RwGeo P Q x qs) {t : ℝ} (ht : t ≤ qs) (ht0 : 0 ≤ t) : t ^ 2 ∈ Dom P Q := by
  have a1 := G.hint ht ht0
  have h2 : t ^ 2 ≤ qs ^ 2 := pow_le_pow_left₀ ht0 ht 2
  refine ⟨sq_nonneg t, ?_, ?_⟩
  · nlinarith [G.hα, G.hP, sq_nonneg t]
  · nlinarith [G.hβ, G.hQ, sq_nonneg t]

lemma x_turn (G : RwGeo P Q x qs) : Real.sqrt (P * Q) * qs ^ 2 < x := by
  have h := G.hturn
  unfold Phi at h
  have := G.etilde_pos le_rfl G.hqs.le
  linarith

/-- `0 < u(t) < 1` on `[0, q_*)`, `u(q_*) = 1`, `0 < u` on `[0, q_*]`. -/
lemma u_pos (G : RwGeo P Q x qs) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ qs) : 0 < hrU P Q 1 x t := by
  unfold hrU
  have h1 := G.x_turn
  have h2 : Real.sqrt (P * Q) * t ^ 2 ≤ Real.sqrt (P * Q) * qs ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 ht 2) (Real.sqrt_nonneg _)
  have := G.etilde_pos ht ht0
  apply div_pos _ this
  linarith

lemma u_lt_one (G : RwGeo P Q x qs) {t : ℝ} (ht0 : 0 ≤ t) (ht : t < qs) : hrU P Q 1 x t < 1 := by
  have hep := G.etilde_pos ht.le ht0
  unfold hrU
  rw [div_lt_one hep]
  have hconv := Phi_convexOn (p := P) (q := Q) 1 x
  have hs0 : (0 : ℝ) < qs ^ 2 := by have := G.hqs; positivity
  have hd : (0 : ℝ) ∈ Dom P Q := Dom_zero
  have hdq : qs ^ 2 ∈ Dom P Q := G.dom le_rfl G.hqs.le
  set a : ℝ := 1 - t ^ 2 / qs ^ 2 with ha
  set b : ℝ := t ^ 2 / qs ^ 2 with hb
  have hb0 : 0 ≤ b := by positivity
  have ha0 : 0 < a := by
    rw [ha, sub_pos, div_lt_one hs0]
    exact pow_lt_pow_left₀ ht ht0 two_ne_zero
  have hab : a + b = 1 := by rw [ha, hb]; ring
  have key := hconv.2 hd hdq ha0.le hb0 hab
  simp only [smul_eq_mul, mul_zero, zero_add] at key
  have hqne : qs ≠ 0 := G.hqs.ne'
  have e : b * qs ^ 2 = t ^ 2 := by rw [hb]; field_simp
  rw [e, G.hturn] at key
  have h0 : Phi P Q 1 x 0 = x - 1 := by simp [Phi, etilde_zero]
  rw [h0] at key
  have hlt : a * (x - 1) < 0 := mul_neg_of_pos_of_neg ha0 (by linarith [G.hx.2])
  unfold Phi at key
  linarith

lemma contOn (G : RwGeo P Q x qs) : ContinuousOn (hrU P Q 1 x) (Set.Icc 0 qs) := by
  unfold hrU
  apply ContinuousOn.div
  · fun_prop
  · unfold etilde
    fun_prop
  · intro t ht
    exact (G.etilde_pos ht.2 ht.1).ne'

lemma acos_contOn (G : RwGeo P Q x qs) :
    ContinuousOn (fun t => Real.arccos (hrU P Q 1 x t)) (Set.Icc 0 qs) :=
  Real.continuous_arccos.comp_continuousOn G.contOn

/-- Uniform bounds of `u` on `[0, b]`, `b < q_*`. -/
lemma u_bounds (G : RwGeo P Q x qs) {b : ℝ} (hb0 : 0 ≤ b) (hb : b < qs) :
    ∃ lo hi : ℝ, 0 < lo ∧ hi < 1 ∧ ∀ t ∈ Set.Icc (0 : ℝ) b, lo ≤ hrU P Q 1 x t ∧ hrU P Q 1 x t ≤ hi := by
  have hc : ContinuousOn (hrU P Q 1 x) (Set.Icc 0 b) := G.contOn.mono (Set.Icc_subset_Icc le_rfl hb.le)
  have hne : (Set.Icc (0 : ℝ) b).Nonempty := ⟨0, le_rfl, hb0⟩
  obtain ⟨t1, ht1, hmin⟩ := isCompact_Icc.exists_isMinOn hne hc
  obtain ⟨t2, ht2, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hc
  refine ⟨hrU P Q 1 x t1, hrU P Q 1 x t2, G.u_pos ht1.1 (ht1.2.trans hb.le), G.u_lt_one ht2.1 (lt_of_le_of_lt ht2.2 hb), ?_⟩
  intro t ht
  exact ⟨hmin ht, hmax ht⟩

lemma acos_integrable (G : RwGeo P Q x qs) {c d : ℝ} (hc : 0 ≤ c) (hc' : c ≤ qs) (hd : 0 ≤ d) (hd' : d ≤ qs) :
    IntervalIntegrable (fun t => Real.arccos (hrU P Q 1 x t)) MeasureTheory.volume c d := by
  apply ContinuousOn.intervalIntegrable
  apply G.acos_contOn.mono
  intro t ht
  rw [Set.mem_uIcc] at ht
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Phase step.** -/
theorem phase_step (G : RwGeo P Q x qs) {lo hi b q q' : ℝ}
    (hlohi : ∀ t ∈ Set.Icc (0 : ℝ) b, lo ≤ hrU P Q 1 x t ∧ hrU P Q 1 x t ≤ hi) (hb : b ≤ qs)
    (hq : 0 ≤ q) (hqq : q ≤ q') (hq' : q' ≤ b) :
    Real.arccos hi * (q' - q) ≤ bkPhase P Q 1 x qs q - bkPhase P Q 1 x qs q' ∧
    bkPhase P Q 1 x qs q - bkPhase P Q 1 x qs q' ≤ Real.arccos lo * (q' - q) := by
  have e : bkPhase P Q 1 x qs q - bkPhase P Q 1 x qs q' = ∫ t in q..q', Real.arccos (hrU P Q 1 x t) := by
    unfold bkPhase
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (G.acos_integrable hq (by linarith) (by linarith) (by linarith))
      (G.acos_integrable (c := q') (d := qs) (by linarith) (by linarith) G.hqs.le le_rfl)]
    ring
  rw [e]
  have hI := G.acos_integrable hq (by linarith) (by linarith) (by linarith : q' ≤ qs)
  constructor
  · have := intervalIntegral.integral_mono_on hqq (intervalIntegrable_const (c := Real.arccos hi)) hI
      (fun t ht => Real.arccos_le_arccos (hlohi t ⟨hq.trans ht.1, ht.2.trans hq'⟩).2)
    simpa [mul_comm] using this
  · have := intervalIntegral.integral_mono_on hqq hI (intervalIntegrable_const (c := Real.arccos lo))
      (fun t ht => Real.arccos_le_arccos (hlohi t ⟨hq.trans ht.1, ht.2.trans hq'⟩).1)
    simpa [mul_comm] using this

/-- `0 ≤ Φ(q) ≤ (π/2)(q_* - q)` for `0 ≤ q ≤ q_*`. -/
theorem phase_bounds (G : RwGeo P Q x qs) {q : ℝ} (hq : 0 ≤ q) (hqs : q ≤ qs) :
    0 ≤ bkPhase P Q 1 x qs q ∧ bkPhase P Q 1 x qs q ≤ π / 2 * (qs - q) := by
  have hb : ∀ t ∈ Set.Icc q qs, 0 ≤ Real.arccos (hrU P Q 1 x t) ∧ Real.arccos (hrU P Q 1 x t) ≤ π / 2 := by
    intro t ht
    exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.2 (G.u_pos (hq.trans ht.1) ht.2).le⟩
  have hI := G.acos_integrable hq hqs G.hqs.le le_rfl
  unfold bkPhase
  constructor
  · exact intervalIntegral.integral_nonneg hqs (fun t ht => (hb t ht).1)
  · have := intervalIntegral.integral_mono_on hqs hI (intervalIntegrable_const (c := π / 2)) (fun t ht => (hb t ht).2)
    simp at this; linarith

/-- `Φ(b₀) > 0` for `0 ≤ b₀ < q_*`. -/
theorem phase_pos (G : RwGeo P Q x qs) {b0 : ℝ} (hb0 : 0 ≤ b0) (hb : b0 < qs) : 0 < bkPhase P Q 1 x qs b0 := by
  set b' := (b0 + qs) / 2 with hb'
  have hb'1 : b0 < b' := by rw [hb']; linarith
  have hb'2 : b' < qs := by rw [hb']; linarith
  obtain ⟨lo, hi, hlo, hhi, H⟩ := G.u_bounds (b := b') (hb0.trans hb'1.le) hb'2
  have h1 := (G.phase_step H hb'2.le hb0 hb'1.le le_rfl).1
  have h2 := (G.phase_bounds (hb0.trans hb'1.le) hb'2.le).1
  have hδ : 0 < Real.arccos hi := Real.arccos_pos.2 hhi
  have : 0 < Real.arccos hi * (b' - b0) := mul_pos hδ (by linarith)
  linarith

theorem phase_ge (G : RwGeo P Q x qs) {b0 q : ℝ} (hq : 0 ≤ q) (hqb : q ≤ b0) (hb : b0 < qs) :
    bkPhase P Q 1 x qs b0 ≤ bkPhase P Q 1 x qs q := by
  obtain ⟨lo, hi, hlo, hhi, H⟩ := G.u_bounds (b := b0) (hq.trans hqb) hb
  have h1 := (G.phase_step H hb.le hq hqb le_rfl).1
  have hδ : 0 ≤ Real.arccos hi := Real.arccos_nonneg _
  have : 0 ≤ Real.arccos hi * (b0 - q) := mul_nonneg hδ (by linarith)
  linarith

end RwGeo

end FormalResearch.Special
