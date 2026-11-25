module

public import FormalResearch.SignUncertainty.CtOscMorse
public import FormalResearch.SignUncertainty.CtOscD2

/-!
# The Morse coordinate `s = t √q(t)` and bounds on `s' = ρ/√q`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 4, Piece 1 ("The real Morse coordinate
`s = t (2∫₀¹(1-r) φ̃''(rt) dr)^{1/2}` has `s'(0) = 1`, with `s'` bounded above and away from zero").  **Proved.**

For a `Phase` datum, `s(t) = t √(q(t))` satisfies `s² = 2 φ`, `s' = ρ/√q`, and `s'` is `D2` with explicit constants
depending only on `(c₁, C)`.
-/

@[expose] public section

open Set Filter Topology

namespace FormalResearch.SignUncertainty.CtOsc

noncomputable def Kq' (C : ℝ) : ℝ := 2 * (1 * C)
noncomputable def Ku (c1 C : ℝ) : ℝ := (Kq' C + 1) + Kq' C * (Real.sqrt c1)⁻¹ + Kq' C ^ 2 * (Real.sqrt c1)⁻¹ ^ 3
noncomputable def Kw (c1 C : ℝ) : ℝ :=
  (Real.sqrt c1)⁻¹ + Ku c1 C * (Real.sqrt c1)⁻¹ ^ 2 + 2 * (Ku c1 C ^ 2 * (Real.sqrt c1)⁻¹ ^ 3)
/-- Bound for `s'` and its first two derivatives. -/
noncomputable def Ksd (c1 C : ℝ) : ℝ := 4 * (C * Kw c1 C)

section
variable {c1 C : ℝ} {φ φ1 f f1 f2 : ℝ → ℝ}

lemma Phase.C0 (h : Phase c1 C φ φ1 f f1 f2) : 0 ≤ C :=
  (abs_nonneg _).trans (h.b0 0 (by norm_num))

lemma Phase.D2_rho (h : Phase c1 C φ φ1 f f1 f2) : D2 (Ioo (-1 : ℝ) 1) (rho f) (rho1 f1) (rho2 f2) C where
  d1 _ hy := h.hasDerivAt_rho hy
  d2 _ hy := h.hasDerivAt_rho1 hy
  c2 := h.cont_rho2
  K0 := h.C0
  b0 y hy := by simpa [Real.norm_eq_abs] using h.abs_rho hy
  b1 y hy := by simpa [Real.norm_eq_abs] using h.abs_rho1 hy
  b2 y hy := by simpa [Real.norm_eq_abs] using h.abs_rho2 hy

lemma Phase.D2_q (h : Phase c1 C φ φ1 f f1 f2) : D2 (Ioo (-1 : ℝ) 1) (qf f) (q1f f1) (q2f f2) (Kq' C) where
  d1 _ hy := h.hasDerivAt_q hy
  d2 _ hy := h.hasDerivAt_q1 hy
  c2 := h.cont_q2
  K0 := by have := h.C0; unfold Kq'; positivity
  b0 y hy := by simpa [Real.norm_eq_abs, Kq'] using h.abs_q hy
  b1 y hy := by simpa [Real.norm_eq_abs, Kq'] using h.abs_q1 hy
  b2 y hy := by simpa [Real.norm_eq_abs, Kq'] using h.abs_q2 hy

lemma Phase.D2_sqrt (h : Phase c1 C φ φ1 f f1 f2) (hc : 0 < c1) :
    D2 (Ioo (-1 : ℝ) 1) (fun y => Real.sqrt (qf f y)) (fun y => q1f f1 y / (2 * Real.sqrt (qf f y)))
      (fun y => q2f f2 y / (2 * Real.sqrt (qf f y)) - (q1f f1 y) ^ 2 / (4 * Real.sqrt (qf f y) ^ 3)) (Ku c1 C) :=
  h.D2_q.sqrt hc (fun y hy => h.q_ge hy)

lemma Phase.D2_w (h : Phase c1 C φ φ1 f f1 f2) (hc : 0 < c1) :
    D2 (Ioo (-1 : ℝ) 1) (fun y => (Real.sqrt (qf f y))⁻¹)
      (fun y => -(q1f f1 y / (2 * Real.sqrt (qf f y))) * ((Real.sqrt (qf f y))⁻¹) ^ 2)
      (fun y => -(q2f f2 y / (2 * Real.sqrt (qf f y)) - (q1f f1 y) ^ 2 / (4 * Real.sqrt (qf f y) ^ 3)) *
          ((Real.sqrt (qf f y))⁻¹) ^ 2 + 2 * (q1f f1 y / (2 * Real.sqrt (qf f y))) ^ 2 * ((Real.sqrt (qf f y))⁻¹) ^ 3)
      (Kw c1 C) :=
  (h.D2_sqrt hc).inv (Real.sqrt_pos.mpr hc) (fun y hy => Real.sqrt_le_sqrt (h.q_ge hy))

/-- `s' = ρ / √q` is `D2` with an explicit constant. -/
lemma Phase.D2_sd (h : Phase c1 C φ φ1 f f1 f2) (hc : 0 < c1) :
    ∃ sd sd1 sd2 : ℝ → ℝ, D2 (Ioo (-1 : ℝ) 1) sd sd1 sd2 (Ksd c1 C) ∧
      ∀ y, sd y = rho f y / Real.sqrt (qf f y) := by
  refine ⟨_, _, _, (h.D2_rho.smul (h.D2_w hc)), fun y => ?_⟩
  simp [div_eq_mul_inv]

/-- The Morse coordinate `s(t) = t √q(t)`. -/
noncomputable def sfun (f : ℝ → ℝ) (t : ℝ) : ℝ := t * Real.sqrt (qf f t)

lemma Phase.hasDerivAt_s (h : Phase c1 C φ φ1 f f1 f2) (hc : 0 < c1) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (sfun f) (rho f t / Real.sqrt (qf f t)) t := by
  have hq : 0 < qf f t := lt_of_lt_of_le hc (h.q_ge ht)
  have hu : 0 < Real.sqrt (qf f t) := Real.sqrt_pos.mpr hq
  have hd := (hasDerivAt_id t).mul ((h.D2_sqrt hc).d1 t ht)
  refine hd.congr_deriv ?_
  rw [← h.q_id ht]
  have hsq : Real.sqrt (qf f t) ^ 2 = qf f t := Real.sq_sqrt hq.le
  field_simp
  rw [hsq]
  simp only [id_eq]
  ring

lemma Phase.s_sq (h : Phase c1 C φ φ1 f f1 f2) (hc : 0 < c1) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    sfun f t ^ 2 / 2 = φ t := by
  have hq : 0 < qf f t := lt_of_lt_of_le hc (h.q_ge ht)
  unfold sfun
  rw [mul_pow, Real.sq_sqrt hq.le, h.phi_eq ht]

lemma Phase.s_zero (f : ℝ → ℝ) : sfun f 0 = 0 := by simp [sfun]

lemma Phase.rho_zero (h : Phase c1 C φ φ1 f f1 f2) : rho f 0 = f 0 := by
  unfold rho avg
  simp only [mul_zero, one_mul]
  simp

lemma Phase.sd_zero (h : Phase c1 C φ φ1 f f1 f2) (hc : 0 < c1) :
    rho f 0 / Real.sqrt (qf f 0) = Real.sqrt (f 0) := by
  have h0 : 0 < f 0 := lt_of_lt_of_le hc (h.lo 0 (by norm_num))
  rw [h.q_zero, h.rho_zero]
  have := Real.sq_sqrt h0.le
  have hs : 0 < Real.sqrt (f 0) := Real.sqrt_pos.mpr h0
  field_simp
  nlinarith

/-- Lower bound `s' ≥ c₁ / √(2C)`. -/
lemma Phase.sd_ge (h : Phase c1 C φ φ1 f f1 f2) (hc : 0 < c1) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    c1 / Real.sqrt (Kq' C) ≤ rho f t / Real.sqrt (qf f t) := by
  have hq : 0 < qf f t := lt_of_lt_of_le hc (h.q_ge ht)
  have hu : 0 < Real.sqrt (qf f t) := Real.sqrt_pos.mpr hq
  have hqle : qf f t ≤ Kq' C := (le_abs_self _).trans (by simpa [Kq'] using h.abs_q ht)
  have hsq : Real.sqrt (qf f t) ≤ Real.sqrt (Kq' C) := Real.sqrt_le_sqrt hqle
  calc c1 / Real.sqrt (Kq' C) ≤ c1 / Real.sqrt (qf f t) := div_le_div_of_nonneg_left hc.le hu hsq
    _ ≤ rho f t / Real.sqrt (qf f t) := div_le_div_of_nonneg_right (h.rho_ge ht) hu.le

end

end FormalResearch.SignUncertainty.CtOsc
