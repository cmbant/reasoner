module

public import FormalResearch.Special.BulkKappaAmp
public import FormalResearch.Special.DiscreteAiryLimitChains2Racah

/-!
# Racah window, part 1: the phase of a centred Racah chain, `τ = ±1`

For the centred Racah data `(P, Q, τ, x, q_*)` with `P, Q ≥ 0`, `τ² = 1`, `|x| < 1`, `0 < q_*`, `0 < 1 - P q_*²`, `0 < 1 - Q q_*²` and the turn `Φ(P, Q, τ, x, q_*²) = 0`
(`RwGeo`; `Φ(σ) = τ(x - β₀σ) - ẽ(σ)`), the function `u = hrU P Q τ x` satisfies `-1 < u < 1` on `[0, q_*)` and `u(q_*) = 1`: `Φ` is convex with `Φ(0) = τx - 1 < 0`
(so `u < 1`), and the same for `Φ` with `τ → -τ`, `x` fixed: `-τ(x - β₀σ) - ẽ(σ)` is convex, `= -τx - 1 < 0` at `0` and `= -2ẽ(q_*²) < 0` at `q_*²` (so `u > -1`).
For `τ = +1` also `u > 0` (`x - β₀σ ≥ ẽ(q_*²) > 0`), for `τ = -1` only `u > 0` near the turn.  Consequences, the Racah counterparts of `BulkIndexSteps` and `BulkWindowChart.bwn_phase_bounds`
(there `u = x/√(1-t²)`):

* `RwGeo.u_bounds`: on `[0, b]`, `b < q_*`, `lo ≤ u ≤ hi` with `-1 < lo`, `hi < 1` (compactness);
* `RwGeo.phase_step`: for `0 ≤ q ≤ q' ≤ b`: `arccos(hi) (q' - q) ≤ Φ(q) - Φ(q') ≤ arccos(lo) (q' - q)`, with `arccos(hi) > 0`, `arccos(lo) < π`;
* `RwGeo.phase_bounds`, `phase_pos`, `phase_ge`: `Φ ≥ 0`, `Φ(b₀) > 0`, `Φ` decreasing; `RwGeo.near_turn`: `u > 0` and `Φ(q) ≤ (π/2)(q_* - q)` on `[q_* - ρ_u, q_*]`.

**Claim class: proved.**
-/

@[expose] public section

open Finset Set FormalResearch.Racah.P3
open scoped Real

namespace FormalResearch.Special

/-- The geometric hypotheses of the centred Racah chain with `τ = ±1`. -/
structure RwGeo (P Q τ x qs : ℝ) : Prop where
  hP : 0 ≤ P
  hQ : 0 ≤ Q
  hτ : τ ^ 2 = 1
  hqs : 0 < qs
  hα : 0 < 1 - P * qs ^ 2
  hβ : 0 < 1 - Q * qs ^ 2
  hturn : Phi P Q τ x (qs ^ 2) = 0
  hx : -1 < x ∧ x < 1

namespace RwGeo

variable {P Q τ x qs : ℝ}

lemma hint (G : RwGeo P Q τ x qs) {t : ℝ} (ht : t ≤ qs) (ht0 : 0 ≤ t) : 0 < (1 - P * t ^ 2) * (1 - Q * t ^ 2) := by
  have h2 : t ^ 2 ≤ qs ^ 2 := pow_le_pow_left₀ ht0 ht 2
  have a1 : 0 < 1 - P * t ^ 2 := by nlinarith [G.hα, G.hP, sq_nonneg t]
  have a2 : 0 < 1 - Q * t ^ 2 := by nlinarith [G.hβ, G.hQ, sq_nonneg t]
  exact mul_pos a1 a2

lemma etilde_pos (G : RwGeo P Q τ x qs) {t : ℝ} (ht : t ≤ qs) (ht0 : 0 ≤ t) : 0 < etilde P Q (t ^ 2) := by
  unfold etilde; exact Real.sqrt_pos.2 (G.hint ht ht0)

lemma dom (G : RwGeo P Q τ x qs) {t : ℝ} (ht : t ≤ qs) (ht0 : 0 ≤ t) : t ^ 2 ∈ Dom P Q := by
  have h2 : t ^ 2 ≤ qs ^ 2 := pow_le_pow_left₀ ht0 ht 2
  refine ⟨sq_nonneg t, ?_, ?_⟩
  · nlinarith [G.hα, G.hP, sq_nonneg t]
  · nlinarith [G.hβ, G.hQ, sq_nonneg t]

lemma turn_pos (G : RwGeo P Q τ x qs) : 0 < τ * (x - Real.sqrt (P * Q) * qs ^ 2) := by
  have h := G.hturn
  unfold Phi at h
  have := G.etilde_pos le_rfl G.hqs.le
  linarith

lemma tau_cases (G : RwGeo P Q τ x qs) : τ = 1 ∨ τ = -1 := by
  have h : (τ - 1) * (τ + 1) = 0 := by linear_combination G.hτ
  rcases mul_eq_zero.1 h with h | h
  · left; linarith
  · right; linarith

lemma phi_zero (τ' x : ℝ) : Phi P Q τ' x 0 = τ' * x - 1 := by simp [Phi, etilde_zero]

/-- `u < 1` on `[0, q_*)`. -/
lemma u_lt_one (G : RwGeo P Q τ x qs) {t : ℝ} (ht0 : 0 ≤ t) (ht : t < qs) : hrU P Q τ x t < 1 := by
  have hep := G.etilde_pos ht.le ht0
  unfold hrU
  rw [div_lt_one hep]
  have hconv := Phi_convexOn (p := P) (q := Q) τ x
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
  rw [e, G.hturn, phi_zero] at key
  have hκ : τ * x - 1 < 0 := by
    rcases G.tau_cases with h | h <;> rw [h] <;> linarith [G.hx.1, G.hx.2]
  have hlt : a * (τ * x - 1) < 0 := mul_neg_of_pos_of_neg ha0 hκ
  unfold Phi at key
  linarith

/-- `u > -1` on `[0, q_*]`. -/
lemma u_gt_neg_one (G : RwGeo P Q τ x qs) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ qs) : -1 < hrU P Q τ x t := by
  have hep := G.etilde_pos ht ht0
  unfold hrU
  rw [lt_div_iff₀ hep]
  have hconv := Phi_convexOn (p := P) (q := Q) (-τ) x
  have hs0 : (0 : ℝ) < qs ^ 2 := by have := G.hqs; positivity
  have hd : (0 : ℝ) ∈ Dom P Q := Dom_zero
  have hdq : qs ^ 2 ∈ Dom P Q := G.dom le_rfl G.hqs.le
  set a : ℝ := 1 - t ^ 2 / qs ^ 2 with ha
  set b : ℝ := t ^ 2 / qs ^ 2 with hb
  have hb0 : 0 ≤ b := by positivity
  have ha0 : 0 ≤ a := by
    rw [ha, sub_nonneg, div_le_one hs0]
    exact pow_le_pow_left₀ ht0 ht 2
  have hab : a + b = 1 := by rw [ha, hb]; ring
  have key := hconv.2 hd hdq ha0 hb0 hab
  simp only [smul_eq_mul, mul_zero, zero_add] at key
  have hqne : qs ≠ 0 := G.hqs.ne'
  have e : b * qs ^ 2 = t ^ 2 := by rw [hb]; field_simp
  rw [e, phi_zero] at key
  have h0 : -τ * x - 1 < 0 := by
    rcases G.tau_cases with h | h <;> rw [h] <;> linarith [G.hx.1, G.hx.2]
  have hq : Phi P Q (-τ) x (qs ^ 2) < 0 := by
    have h1 := G.turn_pos
    have h2 := G.etilde_pos le_rfl G.hqs.le
    have h3 := G.hturn
    unfold Phi at h3 ⊢
    nlinarith
  have hlt : a * (-τ * x - 1) + b * Phi P Q (-τ) x (qs ^ 2) < 0 := by
    rcases ha0.lt_or_eq with ha1 | ha1
    · have := mul_neg_of_pos_of_neg ha1 h0
      have : b * Phi P Q (-τ) x (qs ^ 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb0 hq.le
      linarith
    · have hb1 : b = 1 := by linarith
      rw [← ha1, hb1]; simpa using hq
  unfold Phi at key hlt
  nlinarith

lemma contOn (G : RwGeo P Q τ x qs) : ContinuousOn (hrU P Q τ x) (Set.Icc 0 qs) := by
  unfold hrU
  apply ContinuousOn.div
  · fun_prop
  · unfold etilde
    fun_prop
  · intro t ht
    exact (G.etilde_pos ht.2 ht.1).ne'

lemma acos_contOn (G : RwGeo P Q τ x qs) :
    ContinuousOn (fun t => Real.arccos (hrU P Q τ x t)) (Set.Icc 0 qs) :=
  Real.continuous_arccos.comp_continuousOn G.contOn

/-- Uniform bounds of `u` on `[0, b]`, `b < q_*`. -/
lemma u_bounds (G : RwGeo P Q τ x qs) {b : ℝ} (hb0 : 0 ≤ b) (hb : b < qs) :
    ∃ lo hi : ℝ, -1 < lo ∧ hi < 1 ∧ ∀ t ∈ Set.Icc (0 : ℝ) b, lo ≤ hrU P Q τ x t ∧ hrU P Q τ x t ≤ hi := by
  have hc : ContinuousOn (hrU P Q τ x) (Set.Icc 0 b) := G.contOn.mono (Set.Icc_subset_Icc le_rfl hb.le)
  have hne : (Set.Icc (0 : ℝ) b).Nonempty := ⟨0, le_rfl, hb0⟩
  obtain ⟨t1, ht1, hmin⟩ := isCompact_Icc.exists_isMinOn hne hc
  obtain ⟨t2, ht2, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hc
  refine ⟨hrU P Q τ x t1, hrU P Q τ x t2, G.u_gt_neg_one ht1.1 (ht1.2.trans hb.le),
    G.u_lt_one ht2.1 (lt_of_le_of_lt ht2.2 hb), ?_⟩
  intro t ht
  exact ⟨hmin ht, hmax ht⟩

/-- Uniform bounds of `u` on `[c, d]`, `0 ≤ c ≤ d < q_*`, with the lower bound attained. -/
lemma u_bounds_Icc (G : RwGeo P Q τ x qs) {c d : ℝ} (hc0 : 0 ≤ c) (hcd : c ≤ d) (hd : d < qs) :
    ∃ lo hi : ℝ, (∃ t ∈ Set.Icc c d, lo = hrU P Q τ x t) ∧ hi < 1 ∧
      ∀ t ∈ Set.Icc c d, lo ≤ hrU P Q τ x t ∧ hrU P Q τ x t ≤ hi := by
  have hc : ContinuousOn (hrU P Q τ x) (Set.Icc c d) := G.contOn.mono (Set.Icc_subset_Icc hc0 hd.le)
  have hne : (Set.Icc c d).Nonempty := ⟨c, le_rfl, hcd⟩
  obtain ⟨t1, ht1, hmin⟩ := isCompact_Icc.exists_isMinOn hne hc
  obtain ⟨t2, ht2, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hc
  refine ⟨hrU P Q τ x t1, hrU P Q τ x t2, ⟨t1, ht1, rfl⟩, G.u_lt_one (hc0.trans ht2.1) (lt_of_le_of_lt ht2.2 hd), ?_⟩
  intro t ht
  exact ⟨hmin ht, hmax ht⟩

/-- Near the turn `u > 0`. -/
theorem near_turn_pos (G : RwGeo P Q τ x qs) :
    ∃ ρu : ℝ, 0 < ρu ∧ ρu ≤ qs ∧ ∀ q : ℝ, qs - ρu ≤ q → q ≤ qs → 0 < hrU P Q τ x q := by
  have h1 : hrU P Q τ x qs = 1 := hrU_turn (G.hint le_rfl G.hqs.le) G.hturn
  have hc : ContinuousWithinAt (hrU P Q τ x) (Set.Icc 0 qs) qs := G.contOn.continuousWithinAt ⟨G.hqs.le, le_rfl⟩
  obtain ⟨δ, hδ, hδb⟩ := Metric.continuousWithinAt_iff.1 hc (1 / 2) (by norm_num)
  refine ⟨min (δ / 2) qs, lt_min (by linarith) G.hqs, min_le_right _ _, ?_⟩
  intro q hq1 hq2
  have hρδ : min (δ / 2) qs ≤ δ / 2 := min_le_left _ _
  have hρq : min (δ / 2) qs ≤ qs := min_le_right _ _
  have hq0 : 0 ≤ q := by linarith
  have hd : dist q qs < δ := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  have := hδb (x := q) ⟨hq0, hq2⟩ hd
  rw [Real.dist_eq, h1, abs_lt] at this
  linarith [this.1]

lemma acos_integrable (G : RwGeo P Q τ x qs) {c d : ℝ} (hc : 0 ≤ c) (hc' : c ≤ qs) (hd : 0 ≤ d) (hd' : d ≤ qs) :
    IntervalIntegrable (fun t => Real.arccos (hrU P Q τ x t)) MeasureTheory.volume c d := by
  apply ContinuousOn.intervalIntegrable
  apply G.acos_contOn.mono
  intro t ht
  rw [Set.mem_uIcc] at ht
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Phase step.** -/
theorem phase_step (G : RwGeo P Q τ x qs) {lo hi q q' : ℝ}
    (hlohi : ∀ t ∈ Set.Icc q q', lo ≤ hrU P Q τ x t ∧ hrU P Q τ x t ≤ hi)
    (hq : 0 ≤ q) (hqq : q ≤ q') (hq' : q' ≤ qs) :
    Real.arccos hi * (q' - q) ≤ bkPhase P Q τ x qs q - bkPhase P Q τ x qs q' ∧
    bkPhase P Q τ x qs q - bkPhase P Q τ x qs q' ≤ Real.arccos lo * (q' - q) := by
  have e : bkPhase P Q τ x qs q - bkPhase P Q τ x qs q' = ∫ t in q..q', Real.arccos (hrU P Q τ x t) := by
    unfold bkPhase
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (G.acos_integrable hq (by linarith) (by linarith) (by linarith))
      (G.acos_integrable (c := q') (d := qs) (by linarith) (by linarith) G.hqs.le le_rfl)]
    ring
  rw [e]
  have hI := G.acos_integrable hq (by linarith) (by linarith) hq'
  constructor
  · have := intervalIntegral.integral_mono_on hqq (intervalIntegrable_const (c := Real.arccos hi)) hI
      (fun t ht => Real.arccos_le_arccos (hlohi t ht).2)
    simpa [mul_comm] using this
  · have := intervalIntegral.integral_mono_on hqq hI (intervalIntegrable_const (c := Real.arccos lo))
      (fun t ht => Real.arccos_le_arccos (hlohi t ht).1)
    simpa [mul_comm] using this

/-- `Φ(q) ≥ 0` for `0 ≤ q ≤ q_*`. -/
theorem phase_nonneg (G : RwGeo P Q τ x qs) {q : ℝ} (hq : 0 ≤ q) (hqs : q ≤ qs) : 0 ≤ bkPhase P Q τ x qs q := by
  unfold bkPhase
  exact intervalIntegral.integral_nonneg hqs (fun t _ => Real.arccos_nonneg _)

/-- `Φ(b₀) > 0` for `0 ≤ b₀ < q_*`. -/
theorem phase_pos (G : RwGeo P Q τ x qs) {b0 : ℝ} (hb0 : 0 ≤ b0) (hb : b0 < qs) : 0 < bkPhase P Q τ x qs b0 := by
  set b' := (b0 + qs) / 2 with hb'
  have hb'1 : b0 < b' := by rw [hb']; linarith
  have hb'2 : b' < qs := by rw [hb']; linarith
  obtain ⟨lo, hi, hlo, hhi, H⟩ := G.u_bounds (b := b') (hb0.trans hb'1.le) hb'2
  have h1 := (G.phase_step (fun t ht => H t ⟨ht.1.trans' hb0, ht.2⟩) hb0 hb'1.le hb'2.le).1
  have h2 := G.phase_nonneg (hb0.trans hb'1.le) hb'2.le
  have hδ : 0 < Real.arccos hi := Real.arccos_pos.2 hhi
  have : 0 < Real.arccos hi * (b' - b0) := mul_pos hδ (by linarith)
  linarith

theorem phase_ge (G : RwGeo P Q τ x qs) {b0 q : ℝ} (hq : 0 ≤ q) (hqb : q ≤ b0) (hb : b0 < qs) :
    bkPhase P Q τ x qs b0 ≤ bkPhase P Q τ x qs q := by
  obtain ⟨lo, hi, hlo, hhi, H⟩ := G.u_bounds (b := b0) (hq.trans hqb) hb
  have h1 := (G.phase_step (fun t ht => H t ⟨hq.trans ht.1, ht.2⟩) hq hqb hb.le).1
  have hδ : 0 ≤ Real.arccos hi := Real.arccos_nonneg _
  have : 0 ≤ Real.arccos hi * (b0 - q) := mul_nonneg hδ (by linarith)
  linarith

/-- Near the turn `u > 0`, hence `Φ(q) ≤ (π/2)(q_* - q)`. -/
theorem near_turn (G : RwGeo P Q τ x qs) :
    ∃ ρu : ℝ, 0 < ρu ∧ ρu ≤ qs ∧ ∀ q : ℝ, qs - ρu ≤ q → q ≤ qs → bkPhase P Q τ x qs q ≤ π / 2 * (qs - q) := by
  have h1 : hrU P Q τ x qs = 1 := hrU_turn (G.hint le_rfl G.hqs.le) G.hturn
  have hc : ContinuousWithinAt (hrU P Q τ x) (Set.Icc 0 qs) qs := G.contOn.continuousWithinAt ⟨G.hqs.le, le_rfl⟩
  obtain ⟨δ, hδ, hδb⟩ := Metric.continuousWithinAt_iff.1 hc (1 / 2) (by norm_num)
  refine ⟨min (δ / 2) qs, lt_min (by linarith) G.hqs, min_le_right _ _, ?_⟩
  intro q hq1 hq2
  have hρδ : min (δ / 2) qs ≤ δ / 2 := min_le_left _ _
  have hρq : min (δ / 2) qs ≤ qs := min_le_right _ _
  have hq0 : 0 ≤ q := by linarith
  have hpos : ∀ t ∈ Set.Icc q qs, 0 ≤ hrU P Q τ x t := by
    intro t ht
    have hd : dist t qs < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]
    have := hδb (x := t) ⟨hq0.trans ht.1, ht.2⟩ hd
    rw [Real.dist_eq, h1, abs_lt] at this
    linarith [this.1]
  have hb : ∀ t ∈ Set.Icc q qs, 0 ≤ Real.arccos (hrU P Q τ x t) ∧ Real.arccos (hrU P Q τ x t) ≤ π / 2 :=
    fun t ht => ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.2 (hpos t ht)⟩
  have hI := G.acos_integrable hq0 hq2 G.hqs.le le_rfl
  unfold bkPhase
  have := intervalIntegral.integral_mono_on hq2 hI (intervalIntegrable_const (c := π / 2)) (fun t ht => (hb t ht).2)
  simp at this; linarith

end RwGeo

end FormalResearch.Special
