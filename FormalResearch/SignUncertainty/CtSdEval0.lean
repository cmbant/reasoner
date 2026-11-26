module

public import FormalResearch.SignUncertainty.CtSdChain

/-!
# Integrability and phase-weighted bounds along polygonal chains (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3 (`ct:sd-moments` applied to the
integrand terms).  **Proved.**  Along a `Chain3` an amplitude `h` which is continuous away from the start of each piece and
bounded by a three-term power `Σ K_i |w|^{α_i}` (`α_i ≥ -1/2`) has `h e^{iPh_U}` interval integrable on every piece, its chain
integral is linear in `h`, and `|∫_Γ h e^{iPh_U}| ≤ Σ K_i · mom_{α_i}(Γ)` with `mom` the phase-weighted moments of `CtSdChain`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real

namespace FormalResearch.SignUncertainty.CtSd

/-- The point `z₀ + t d` of a piece. -/
def Piece.pt (q : Piece) (t : ℝ) : ℂ := q.z0 + (t : ℂ) * q.d

lemma norm_pt_lt {R₀ : ℝ} {q : Piece} (hq : q.Ok R₀) {t : ℝ} (ht : t ∈ Icc q.a q.b) : ‖q.pt t‖ < R₀ := by
  have := (hq.2.1 t ht).1
  rwa [mem_ball_zero_iff] at this

/-- The dominating function `|w|^α e^{-Im Ph_U(w)} |d|` is interval integrable on a valid piece when `α > -1`. -/
lemma piece_dom_integrable {R₀ : ℝ} {q : Piece} (hq : q.Ok R₀) (U α : ℝ) (hα : -1 < α) :
    IntervalIntegrable (fun t : ℝ => ‖q.pt t‖ ^ α * Real.exp (-(PhU U (q.pt t)).im) * ‖q.d‖) volume q.a q.b := by
  have hcg : Continuous fun t : ℝ => Real.exp (-(PhU U (q.pt t)).im) * ‖q.d‖ := by
    unfold PhU Piece.pt; fun_prop
  obtain ⟨hab, -, hne⟩ := hq
  by_cases h0 : q.pt q.a = 0
  · have hz0 : q.z0 = -(q.a : ℂ) * q.d := by
      have := h0
      unfold Piece.pt at this
      linear_combination this
    have hpt : ∀ t, q.pt t = ((t - q.a : ℝ) : ℂ) * q.d := by
      intro t; unfold Piece.pt; rw [hz0]; push_cast; ring
    have hrw : ∀ t ∈ Ioc q.a q.b, ‖q.pt t‖ ^ α * Real.exp (-(PhU U (q.pt t)).im) * ‖q.d‖ =
        (t - q.a) ^ α * (‖q.d‖ ^ α * (Real.exp (-(PhU U (q.pt t)).im) * ‖q.d‖)) := by
      intro t ht
      have h1 : 0 ≤ t - q.a := by linarith [ht.1]
      rw [hpt, norm_mul, Complex.norm_real, Real.norm_of_nonneg h1, Real.mul_rpow h1 (norm_nonneg _)]
      ring
    have h1 : IntervalIntegrable (fun t : ℝ => (t - q.a) ^ α) volume q.a q.b := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := q.b - q.a) hα).comp_sub_right q.a
      simpa using this
    have h2 : IntervalIntegrable (fun t : ℝ => (t - q.a) ^ α * (‖q.d‖ ^ α * (Real.exp (-(PhU U (q.pt t)).im) * ‖q.d‖)))
        volume q.a q.b :=
      h1.mul_continuousOn (hcg.const_smul (‖q.d‖ ^ α)).continuousOn
    exact h2.congr (fun t ht => (hrw t (by rwa [uIoc_of_le hab] at ht)).symm)
  · have hne' : ∀ t ∈ Icc q.a q.b, q.pt t ≠ 0 := by
      intro t ht
      rcases ht.1.eq_or_lt with h | h
      · rw [← h]; exact h0
      · exact hne t ⟨h, ht.2⟩
    have hc : ContinuousOn (fun t : ℝ => ‖q.pt t‖ ^ α) (Icc q.a q.b) := by
      intro t ht
      have hcp : ContinuousAt (fun t : ℝ => ‖q.pt t‖) t := by
        unfold Piece.pt; fun_prop
      exact (hcp.rpow_const (Or.inl (norm_ne_zero_iff.mpr (hne' t ht)))).continuousWithinAt
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    have := hc.mul hcg.continuousOn
    convert this using 1
    ext t
    simp [mul_assoc]

/-- Integrability of `h e^{iPh_U} d` from a crude bound `K |w|^{-1/2}`. -/
lemma piece_int_of_crude {R₀ : ℝ} {q : Piece} (hq : q.Ok R₀) {h : ℂ → ℂ} {K : ℝ} (U : ℝ)
    (hc : ContinuousOn (fun t : ℝ => h (q.pt t)) (Ioc q.a q.b))
    (hb : ∀ t ∈ Ioc q.a q.b, ‖h (q.pt t)‖ ≤ K * ‖q.pt t‖ ^ (-(1 / 2 : ℝ))) :
    IntervalIntegrable (fun t : ℝ => h (q.pt t) * Complex.exp (Complex.I * PhU U (q.pt t)) * q.d) volume q.a q.b := by
  have hab := hq.1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hd := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
    (piece_dom_integrable hq U (-(1 / 2)) (by norm_num))).const_mul K
  refine hd.mono' ?_ ?_
  · have hce : Continuous fun t : ℝ => Complex.exp (Complex.I * PhU U (q.pt t)) * q.d := by
      unfold PhU Piece.pt; fun_prop
    exact (hc.mul hce.continuousOn).aestronglyMeasurable measurableSet_Ioc |>.congr
      (ae_of_all _ fun t => by simp [mul_assoc])
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_mul, norm_mul, norm_exp_I_mul]
    have := hb t ht
    have he : 0 ≤ Real.exp (-(PhU U (q.pt t)).im) := (Real.exp_pos _).le
    calc ‖h (q.pt t)‖ * Real.exp (-(PhU U (q.pt t)).im) * ‖q.d‖
        ≤ K * ‖q.pt t‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-(PhU U (q.pt t)).im) * ‖q.d‖ := by gcongr
      _ = K * (‖q.pt t‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-(PhU U (q.pt t)).im) * ‖q.d‖) := by ring

/-- A three-term power amplitude bound on a piece. -/
def PieceBd (h : ℂ → ℂ) (q : Piece) (K1 α1 K2 α2 K3 α3 : ℝ) : Prop :=
  ContinuousOn (fun t : ℝ => h (q.pt t)) (Ioc q.a q.b) ∧
    ∀ t ∈ Ioc q.a q.b, ‖h (q.pt t)‖ ≤ K1 * ‖q.pt t‖ ^ α1 + K2 * ‖q.pt t‖ ^ α2 + K3 * ‖q.pt t‖ ^ α3

lemma rpow_le_crude {x R₀ α : ℝ} (hx : 0 < x) (hxR : x ≤ R₀) (hα : -(1 / 2 : ℝ) ≤ α) :
    x ^ α ≤ R₀ ^ (α + 1 / 2) * x ^ (-(1 / 2 : ℝ)) := by
  have h1 : x ^ α = x ^ (α + 1 / 2) * x ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  rw [h1]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx.le hxR (by linarith)) (by positivity)

lemma PieceBd.integrable {R₀ : ℝ} {q : Piece} (hq : q.Ok R₀) {h : ℂ → ℂ} {K1 α1 K2 α2 K3 α3 : ℝ}
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3)
    (h1 : -(1 / 2 : ℝ) ≤ α1) (h2 : -(1 / 2 : ℝ) ≤ α2) (h3 : -(1 / 2 : ℝ) ≤ α3) (U : ℝ)
    (hb : PieceBd h q K1 α1 K2 α2 K3 α3) :
    IntervalIntegrable (fun t : ℝ => h (q.pt t) * Complex.exp (Complex.I * PhU U (q.pt t)) * q.d) volume q.a q.b := by
  refine piece_int_of_crude hq (K := K1 * R₀ ^ (α1 + 1 / 2) + K2 * R₀ ^ (α2 + 1 / 2) + K3 * R₀ ^ (α3 + 1 / 2)) U hb.1 ?_
  intro t ht
  have hx : 0 < ‖q.pt t‖ := norm_pos_iff.mpr (hq.2.2 t ht)
  have hxR : ‖q.pt t‖ ≤ R₀ := (norm_pt_lt hq ⟨ht.1.le, ht.2⟩).le
  have e1 := mul_le_mul_of_nonneg_left (rpow_le_crude hx hxR h1) hK1
  have e2 := mul_le_mul_of_nonneg_left (rpow_le_crude hx hxR h2) hK2
  have e3 := mul_le_mul_of_nonneg_left (rpow_le_crude hx hxR h3) hK3
  have := hb.2 t ht
  linarith only [this, e1, e2, e3]

/-- Three-term phase-weighted bound on a segment. -/
theorem lineInt_phase_le3 {U : ℝ} {z₀ d : ℂ} {a b : ℝ} (hab : a ≤ b) {h : ℂ → ℂ} {K1 K2 K3 α1 α2 α3 : ℝ}
    (hh : ∀ t ∈ Ioc a b, ‖h (z₀ + (t : ℂ) * d)‖ ≤ K1 * ‖z₀ + (t : ℂ) * d‖ ^ α1 + K2 * ‖z₀ + (t : ℂ) * d‖ ^ α2 +
      K3 * ‖z₀ + (t : ℂ) * d‖ ^ α3)
    (hi1 : IntervalIntegrable (fun t : ℝ => ‖z₀ + (t : ℂ) * d‖ ^ α1 *
      Real.exp (-(PhU U (z₀ + (t : ℂ) * d)).im) * ‖d‖) volume a b)
    (hi2 : IntervalIntegrable (fun t : ℝ => ‖z₀ + (t : ℂ) * d‖ ^ α2 *
      Real.exp (-(PhU U (z₀ + (t : ℂ) * d)).im) * ‖d‖) volume a b)
    (hi3 : IntervalIntegrable (fun t : ℝ => ‖z₀ + (t : ℂ) * d‖ ^ α3 *
      Real.exp (-(PhU U (z₀ + (t : ℂ) * d)).im) * ‖d‖) volume a b) :
    ‖lineInt z₀ d a b (fun w => h w * Complex.exp (Complex.I * PhU U w))‖ ≤
      K1 * (∫ t in a..b, ‖z₀ + (t : ℂ) * d‖ ^ α1 * Real.exp (-(PhU U (z₀ + (t : ℂ) * d)).im) * ‖d‖) +
      K2 * (∫ t in a..b, ‖z₀ + (t : ℂ) * d‖ ^ α2 * Real.exp (-(PhU U (z₀ + (t : ℂ) * d)).im) * ‖d‖) +
      K3 * (∫ t in a..b, ‖z₀ + (t : ℂ) * d‖ ^ α3 * Real.exp (-(PhU U (z₀ + (t : ℂ) * d)).im) * ‖d‖) := by
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (hi1.const_mul K1) (hi2.const_mul K2),
    ← intervalIntegral.integral_add ((hi1.const_mul K1).add (hi2.const_mul K2)) (hi3.const_mul K3)]
  unfold lineInt
  refine intervalIntegral.norm_integral_le_of_norm_le hab (ae_of_all _ fun t ht => ?_)
    (((hi1.const_mul K1).add (hi2.const_mul K2)).add (hi3.const_mul K3))
  rw [norm_mul, norm_mul, norm_exp_I_mul]
  have := hh t ht
  have hd : 0 ≤ ‖d‖ := norm_nonneg d
  have he : 0 ≤ Real.exp (-(PhU U (z₀ + (t : ℂ) * d)).im) := (Real.exp_pos _).le
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this he) hd
  linarith only [this]

/-- The chain integral of `h e^{iPh_U}`. -/
noncomputable def Chain3.intE {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) (U : ℝ) (h : ℂ → ℂ) : ℂ :=
  ch.int (fun w => h w * Complex.exp (Complex.I * PhU U w))

/-- Three-term amplitude bound along all pieces. -/
def Chain3.Bd {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) (h : ℂ → ℂ) (K1 α1 K2 α2 K3 α3 : ℝ) : Prop :=
  PieceBd h ch.q1 K1 α1 K2 α2 K3 α3 ∧ PieceBd h ch.q2 K1 α1 K2 α2 K3 α3 ∧ PieceBd h ch.q3 K1 α1 K2 α2 K3 α3

/-- **Phase-weighted bound along a chain**: `|∫_Γ h e^{iPh}| ≤ Σ K_i mom_{α_i}`. -/
theorem Chain3.norm_intE_le {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) {U : ℝ} {h : ℂ → ℂ} {K1 α1 K2 α2 K3 α3 : ℝ}
    (h1 : -(1 / 2 : ℝ) ≤ α1) (h2 : -(1 / 2 : ℝ) ≤ α2) (h3 : -(1 / 2 : ℝ) ≤ α3)
    (hb : ch.Bd h K1 α1 K2 α2 K3 α3) :
    ‖ch.intE U h‖ ≤ K1 * ch.mom U α1 + K2 * ch.mom U α2 + K3 * ch.mom U α3 := by
  have piece : ∀ q : Piece, q.Ok R₀ → PieceBd h q K1 α1 K2 α2 K3 α3 →
      ‖lineInt q.z0 q.d q.a q.b (fun w => h w * Complex.exp (Complex.I * PhU U w))‖ ≤
        K1 * (∫ t in q.a..q.b, ‖q.z0 + (t : ℂ) * q.d‖ ^ α1 * Real.exp (-(PhU U (q.z0 + (t : ℂ) * q.d)).im) * ‖q.d‖) +
        K2 * (∫ t in q.a..q.b, ‖q.z0 + (t : ℂ) * q.d‖ ^ α2 * Real.exp (-(PhU U (q.z0 + (t : ℂ) * q.d)).im) * ‖q.d‖) +
        K3 * (∫ t in q.a..q.b, ‖q.z0 + (t : ℂ) * q.d‖ ^ α3 * Real.exp (-(PhU U (q.z0 + (t : ℂ) * q.d)).im) * ‖q.d‖) := by
    intro q hq hbq
    exact lineInt_phase_le3 hq.1 hbq.2 (piece_dom_integrable hq U α1 (by linarith))
      (piece_dom_integrable hq U α2 (by linarith)) (piece_dom_integrable hq U α3 (by linarith))
  have e1 := piece ch.q1 ch.ok1 hb.1
  have e2 := piece ch.q2 ch.ok2 hb.2.1
  have e3 := piece ch.q3 ch.ok3 hb.2.2
  unfold Chain3.intE Chain3.int
  unfold Chain3.mom
  refine (norm_add₃_le).trans ?_
  linarith only [e1, e2, e3]

/-- Chain integrals of two integrable amplitudes add. -/
theorem Chain3.intE_add {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) {U : ℝ} {h g : ℂ → ℂ}
    {K1 α1 K2 α2 K3 α3 L1 β1 L2 β2 L3 β3 : ℝ}
    (hK : 0 ≤ K1 ∧ 0 ≤ K2 ∧ 0 ≤ K3) (hL : 0 ≤ L1 ∧ 0 ≤ L2 ∧ 0 ≤ L3)
    (h1 : -(1 / 2 : ℝ) ≤ α1) (h2 : -(1 / 2 : ℝ) ≤ α2) (h3 : -(1 / 2 : ℝ) ≤ α3)
    (g1 : -(1 / 2 : ℝ) ≤ β1) (g2 : -(1 / 2 : ℝ) ≤ β2) (g3 : -(1 / 2 : ℝ) ≤ β3)
    (hb : ch.Bd h K1 α1 K2 α2 K3 α3) (gb : ch.Bd g L1 β1 L2 β2 L3 β3) :
    ch.intE U (fun w => h w + g w) = ch.intE U h + ch.intE U g := by
  have piece : ∀ q : Piece, q.Ok R₀ → PieceBd h q K1 α1 K2 α2 K3 α3 → PieceBd g q L1 β1 L2 β2 L3 β3 →
      lineInt q.z0 q.d q.a q.b (fun w => (h w + g w) * Complex.exp (Complex.I * PhU U w)) =
        lineInt q.z0 q.d q.a q.b (fun w => h w * Complex.exp (Complex.I * PhU U w)) +
        lineInt q.z0 q.d q.a q.b (fun w => g w * Complex.exp (Complex.I * PhU U w)) := by
    intro q hq hbq gbq
    have i1 := PieceBd.integrable hq hK.1 hK.2.1 hK.2.2 h1 h2 h3 U hbq
    have i2 := PieceBd.integrable hq hL.1 hL.2.1 hL.2.2 g1 g2 g3 U gbq
    unfold lineInt
    calc _ = ∫ t in q.a..q.b, (h (q.pt t) * Complex.exp (Complex.I * PhU U (q.pt t)) * q.d +
          g (q.pt t) * Complex.exp (Complex.I * PhU U (q.pt t)) * q.d) :=
          intervalIntegral.integral_congr (fun t _ => by simp only [Piece.pt, add_mul])
      _ = _ := intervalIntegral.integral_add i1 i2
  unfold Chain3.intE Chain3.int
  rw [piece ch.q1 ch.ok1 hb.1 gb.1, piece ch.q2 ch.ok2 hb.2.1 gb.2.1, piece ch.q3 ch.ok3 hb.2.2 gb.2.2]
  ring

/-- Chain integrals commute with a constant factor. -/
theorem Chain3.intE_const_mul {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) (U : ℝ) (k : ℂ) (h : ℂ → ℂ) :
    ch.intE U (fun w => k * h w) = k * ch.intE U h := by
  have piece : ∀ q : Piece, lineInt q.z0 q.d q.a q.b (fun w => (k * h w) * Complex.exp (Complex.I * PhU U w)) =
      k * lineInt q.z0 q.d q.a q.b (fun w => h w * Complex.exp (Complex.I * PhU U w)) := by
    intro q
    unfold lineInt
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only [mul_assoc]
  unfold Chain3.intE Chain3.int
  rw [piece ch.q1, piece ch.q2, piece ch.q3]
  ring

/-- Path independence for `csr · g` over all chains with a common endpoint. -/
theorem Chain3.int_csr_uniform {R₀ : ℝ} (hR : 0 < R₀) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 R₀)) :
    ∃ Φ : ℂ → ℂ, ∀ {p : ℂ} (ch : Chain3 R₀ p), ch.int (fun z => csr z * g z) = Φ p - Φ 0 := by
  obtain ⟨Φ, hΦ⟩ := lineInt_csr hR hg
  refine ⟨Φ, fun {p} ch => ?_⟩
  have e1 := hΦ ch.q1.z0 ch.q1.d ch.q1.a ch.q1.b ch.ok1.1 ch.ok1.2.1 ch.ok1.2.2
  have e2 := hΦ ch.q2.z0 ch.q2.d ch.q2.a ch.q2.b ch.ok2.1 ch.ok2.2.1 ch.ok2.2.2
  have e3 := hΦ ch.q3.z0 ch.q3.d ch.q3.a ch.q3.b ch.ok3.1 ch.ok3.2.1 ch.ok3.2.2
  unfold Chain3.int
  rw [e1, e2, e3]
  have h0 : ch.q1.z0 + (ch.q1.a : ℂ) * ch.q1.d = 0 := ch.h0
  have h12 : ch.q1.z0 + (ch.q1.b : ℂ) * ch.q1.d = ch.q2.z0 + (ch.q2.a : ℂ) * ch.q2.d := ch.h12
  have h23 : ch.q2.z0 + (ch.q2.b : ℂ) * ch.q2.d = ch.q3.z0 + (ch.q3.a : ℂ) * ch.q3.d := ch.h23
  have h3 : ch.q3.z0 + (ch.q3.b : ℂ) * ch.q3.d = p := ch.h3
  rw [h0, h12, h23, h3]
  ring

end FormalResearch.SignUncertainty.CtSd
