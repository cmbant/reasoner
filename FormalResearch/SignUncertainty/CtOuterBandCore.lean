module

public import FormalResearch.SignUncertainty.CtOuterBandLeft
public import FormalResearch.SignUncertainty.CtOscStat

/-!
# The stationary-phase core of the outer band (Piece 1): phase data

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 4, Piece 1: with `τ = τ₀(1+t/2)`,
`φ̃(t) = (ϕ(τ) - ϕ(τ₀))/(¼τ₀² m'(τ₀))` satisfies `φ̃(0) = φ̃'(0) = 0`, `φ̃'' = m'(τ)/m'(τ₀) ∈ [c₁, C₁]` and
`|φ̃^{(k)}| ≤ C` (`k = 3, 4`).  **Proved.**
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOsc

/-- `τ(t) = τ₀(1+t/2)`. -/
noncomputable def tt (τ0 t : ℝ) : ℝ := τ0 * (1 + t / 2)

lemma hasDerivAt_tt (τ0 y : ℝ) : HasDerivAt (tt τ0) (τ0 / 2) y := by
  unfold tt
  have := ((hasDerivAt_id y).div_const 2).const_add 1 |>.const_mul τ0
  simpa [mul_comm, div_eq_mul_inv, mul_assoc] using this

lemma tt_ge {τ0 t : ℝ} (hτ0 : 0 < τ0) (ht : t ∈ Ioo (-1 : ℝ) 1) : τ0 / 2 ≤ tt τ0 t := by
  unfold tt; nlinarith [ht.1]

lemma tt_le {τ0 t : ℝ} (hτ0 : 0 < τ0) (ht : t ∈ Ioo (-1 : ℝ) 1) : tt τ0 t ≤ 3 * τ0 / 2 := by
  unfold tt; nlinarith [ht.2]

lemma tt_pos {τ0 t : ℝ} (hτ0 : 0 < τ0) (ht : t ∈ Ioo (-1 : ℝ) 1) : 0 < tt τ0 t :=
  lt_of_lt_of_le (by positivity) (tt_ge hτ0 ht)

lemma ratio_lo {τ0 τ : ℝ} (hτ0 : 0 < τ0) (h1 : τ0 / 2 ≤ τ) (h2 : τ ≤ 3 * τ0 / 2) :
    2 / 9 * (τ0 / (1 + τ0 ^ 2)) ≤ τ / (1 + τ ^ 2) := by
  have hτ : 0 < τ := lt_of_lt_of_le (by positivity) h1
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hτ0.le (sq_nonneg τ0), mul_nonneg hτ0.le (sub_nonneg.2 h2), mul_nonneg hτ.le (sq_nonneg τ0),
    mul_nonneg (sub_nonneg.2 h1) (sq_nonneg τ0), mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2), mul_pos hτ hτ0]

lemma ratio_hi {τ0 τ : ℝ} (hτ0 : 0 < τ0) (h1 : τ0 / 2 ≤ τ) (h2 : τ ≤ 3 * τ0 / 2) :
    τ / (1 + τ ^ 2) ≤ 6 * (τ0 / (1 + τ0 ^ 2)) := by
  have hτ : 0 < τ := lt_of_lt_of_le (by positivity) h1
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hτ0.le (sq_nonneg τ0), mul_nonneg hτ0.le (sub_nonneg.2 h2), mul_nonneg hτ.le (sq_nonneg τ0),
    mul_nonneg (sub_nonneg.2 h1) (sq_nonneg τ0), mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2), mul_pos hτ hτ0,
    mul_nonneg hτ.le (sq_nonneg (τ - τ0))]

section
variable {C0 : ℝ} {m m1 m2 m3 : ℝ → ℝ}

lemma MData.C0_ge (h : MData C0 m m1 m2 m3) : 1 ≤ C0 := by
  have a := h.lo 1 one_pos
  have b := h.hi 1 one_pos
  norm_num at a b
  linarith

lemma one_add_ge {τ0 τ : ℝ} (hτ0 : 0 < τ0) (h1 : τ0 / 2 ≤ τ) : (1 + τ0) / 2 ≤ 1 + τ := by linarith

/-- The rescaled phase satisfies the hypotheses of `stat_phase`. -/
theorem phase_data (hM : MData C0 m m1 m2 m3) {τ0 : ℝ} (hτ0 : 0 < τ0) {ϕ : ℝ → ℝ}
    (hϕ : ∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - m τ0) τ) :
    Phase (2 / (9 * C0)) (6 * C0) (fun t => (ϕ (tt τ0 t) - ϕ τ0) / (τ0 ^ 2 * m1 τ0 / 4))
      (fun t => (τ0 / 2) * (m (tt τ0 t) - m τ0) / (τ0 ^ 2 * m1 τ0 / 4))
      (fun t => m1 (tt τ0 t) / m1 τ0) (fun t => (τ0 / 2) * m2 (tt τ0 t) / m1 τ0)
      (fun t => (τ0 / 2) ^ 2 * m3 (tt τ0 t) / m1 τ0) := by
  have hC0 := hM.C0_ge
  have hC0p : 0 < C0 := by linarith
  have hm1 := hM.m1_pos hτ0
  have hD : 0 < τ0 ^ 2 * m1 τ0 / 4 := by positivity
  have hm1lo := hM.lo τ0 hτ0
  have hm1hi := hM.hi τ0 hτ0
  have hν : 0 < τ0 / (1 + τ0 ^ 2) := by positivity
  refine
    { d0 := fun y hy => ?_, d1 := fun y hy => ?_, d2 := fun y hy => ?_, d3 := fun y hy => ?_, c2 := ?_,
      z0 := ?_, z1 := ?_, lo := fun y hy => ?_, b0 := fun y hy => ?_, b1 := fun y hy => ?_, b2 := fun y hy => ?_ }
  · have hτ := tt_pos hτ0 hy
    have := ((hϕ _ hτ).comp y (hasDerivAt_tt τ0 y)).sub_const (ϕ τ0) |>.div_const (τ0 ^ 2 * m1 τ0 / 4)
    refine this.congr_deriv ?_
    try simp only [smul_eq_mul]
    ring
  · have hτ := tt_pos hτ0 hy
    have h1 := (hM.d0 _ hτ).comp y (hasDerivAt_tt τ0 y)
    have := ((h1.sub_const (m τ0)).const_mul (τ0 / 2)).div_const (τ0 ^ 2 * m1 τ0 / 4)
    refine this.congr_deriv ?_
    try simp only [smul_eq_mul]
    field_simp
    ring
  · have hτ := tt_pos hτ0 hy
    have h1 := (hM.d1 _ hτ).comp y (hasDerivAt_tt τ0 y)
    have := h1.div_const (m1 τ0)
    refine this.congr_deriv ?_
    try simp only [smul_eq_mul]
    ring
  · have hτ := tt_pos hτ0 hy
    have h1 := (hM.d2 _ hτ).comp y (hasDerivAt_tt τ0 y)
    have := (h1.const_mul ((τ0 / 2))).div_const (m1 τ0)
    refine this.congr_deriv ?_
    try simp only [smul_eq_mul]
    ring
  · have hc3 : ContinuousOn m3 (Ioi 0) := hM.c3
    have hcomp : ContinuousOn (fun t => m3 (tt τ0 t)) (Ioo (-1 : ℝ) 1) :=
      hc3.comp (fun t _ => (hasDerivAt_tt τ0 t).continuousAt.continuousWithinAt)
        (fun t ht => tt_pos hτ0 ht)
    exact (continuousOn_const.mul hcomp).div_const _
  · simp [tt]
  · have : tt τ0 0 = τ0 := by simp [tt]
    simp [this]
  · have hτ := tt_pos hτ0 hy
    have a1 := ratio_lo hτ0 (tt_ge hτ0 hy) (tt_le hτ0 hy)
    have a2 := hM.lo _ hτ
    have a3 : 2 / 9 * (τ0 / (1 + τ0 ^ 2)) ≤ m1 (tt τ0 y) := a1.trans a2
    rw [le_div_iff₀ hm1]
    calc 2 / (9 * C0) * m1 τ0 ≤ 2 / (9 * C0) * (C0 * (τ0 / (1 + τ0 ^ 2))) :=
          mul_le_mul_of_nonneg_left hm1hi (by positivity)
      _ = 2 / 9 * (τ0 / (1 + τ0 ^ 2)) := by field_simp
      _ ≤ _ := a3
  · have hτ := tt_pos hτ0 hy
    have a1 := ratio_hi hτ0 (tt_ge hτ0 hy) (tt_le hτ0 hy)
    have a2 := hM.hi _ hτ
    have hp := hM.m1_pos hτ
    rw [abs_of_pos (div_pos hp hm1), div_le_iff₀ hm1]
    calc m1 (tt τ0 y) ≤ C0 * (tt τ0 y / (1 + tt τ0 y ^ 2)) := a2
      _ ≤ C0 * (6 * (τ0 / (1 + τ0 ^ 2))) := mul_le_mul_of_nonneg_left a1 hC0p.le
      _ ≤ 6 * C0 * m1 τ0 := by nlinarith [mul_le_mul_of_nonneg_left hm1lo (by positivity : (0 : ℝ) ≤ 6 * C0)]
  · have hτ := tt_pos hτ0 hy
    have hu := one_add_ge hτ0 (tt_ge hτ0 hy)
    set u := 1 + tt τ0 y with hu_def
    have hu0 : 0 < u := by rw [hu_def]; linarith
    have hb := hM.b2 _ hτ
    have e : (1 + tt τ0 y) = u := rfl
    rw [e] at hb
    rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < τ0 / 2), abs_of_pos hm1, div_le_iff₀ hm1]
    have h1 : τ0 / 2 * |m2 (tt τ0 y)| ≤ τ0 / 2 * (C0 / u ^ 2) := mul_le_mul_of_nonneg_left hb (by positivity)
    have h2 : τ0 / 2 * (C0 / u ^ 2) ≤ 6 * C0 * (τ0 / (1 + τ0 ^ 2)) := by
      have : (1 + τ0 ^ 2) ≤ 12 * u ^ 2 := by nlinarith [sq_nonneg τ0, sq_nonneg (u - (1 + τ0) / 2)]
      rw [show τ0 / 2 * (C0 / u ^ 2) = C0 * τ0 / (2 * u ^ 2) by ring, show 6 * C0 * (τ0 / (1 + τ0 ^ 2)) =
        6 * C0 * τ0 / (1 + τ0 ^ 2) by ring, div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ C0 * τ0 := by positivity
      nlinarith [mul_nonneg this (sub_nonneg.2 ‹1 + τ0 ^ 2 ≤ 12 * u ^ 2›)]
    have h3 : 6 * C0 * (τ0 / (1 + τ0 ^ 2)) ≤ 6 * C0 * m1 τ0 := mul_le_mul_of_nonneg_left hm1lo (by positivity)
    linarith
  · have hτ := tt_pos hτ0 hy
    have hu := one_add_ge hτ0 (tt_ge hτ0 hy)
    set u := 1 + tt τ0 y with hu_def
    have hu0 : 0 < u := by rw [hu_def]; linarith
    have hb := hM.b3 _ hτ
    have e : (1 + tt τ0 y) = u := rfl
    rw [e] at hb
    rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < (τ0 / 2) ^ 2), abs_of_pos hm1, div_le_iff₀ hm1]
    have h1 : (τ0 / 2) ^ 2 * |m3 (tt τ0 y)| ≤ (τ0 / 2) ^ 2 * (C0 / u ^ 3) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    have h2 : (τ0 / 2) ^ 2 * (C0 / u ^ 3) ≤ 6 * C0 * (τ0 / (1 + τ0 ^ 2)) := by
      have h8 : (1 + τ0) ^ 3 ≤ 8 * u ^ 3 := by
        have : 1 + τ0 ≤ 2 * u := by linarith
        calc (1 + τ0) ^ 3 ≤ (2 * u) ^ 3 := pow_le_pow_left₀ (by positivity) this 3
          _ = 8 * u ^ 3 := by ring
      have h9 : τ0 * (1 + τ0 ^ 2) ≤ 24 * u ^ 3 := by nlinarith [pow_pos hτ0 3, sq_nonneg τ0]
      rw [show (τ0 / 2) ^ 2 * (C0 / u ^ 3) = C0 * τ0 ^ 2 / (4 * u ^ 3) by ring, show 6 * C0 * (τ0 / (1 + τ0 ^ 2)) =
        6 * C0 * τ0 / (1 + τ0 ^ 2) by ring, div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ C0 * τ0 := by positivity
      nlinarith [mul_nonneg this (sub_nonneg.2 h9)]
    have h3 : 6 * C0 * (τ0 / (1 + τ0 ^ 2)) ≤ 6 * C0 * m1 τ0 := mul_le_mul_of_nonneg_left hm1lo (by positivity)
    linarith

/-- Normalisation `N = τ₀^{1/2}/(1+τ₀)`. -/
noncomputable def Nn (τ0 : ℝ) : ℝ := τ0 ^ (1 / 2 : ℝ) / (1 + τ0)

lemma Nn_pos {τ0 : ℝ} (hτ0 : 0 < τ0) : 0 < Nn τ0 := by unfold Nn; positivity

/-- Scaling of the amplitude weights on `τ ∈ [τ₀/2, 3τ₀/2]`. -/
lemma amp_scale {τ0 τ KB : ℝ} (hτ0 : 0 < τ0) (h1 : τ0 / 2 ≤ τ) (h2 : τ ≤ 3 * τ0 / 2) (hKB : 0 ≤ KB) :
    KB * τ ^ (1 / 2 : ℝ) / (1 + τ) ≤ 4 * KB * Nn τ0 ∧
    τ0 / 2 * (KB * τ ^ (-1 / 2 : ℝ) / (1 + τ)) ≤ 2 * KB * Nn τ0 ∧
    (τ0 / 2) ^ 2 * (KB * τ ^ (-3 / 2 : ℝ) / (1 + τ)) ≤ 2 * KB * Nn τ0 := by
  have hτ : 0 < τ := lt_of_lt_of_le (by positivity) h1
  set s := Real.sqrt τ0 with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hτ0
  have hss : s * s = τ0 := Real.mul_self_sqrt hτ0.le
  have hNn : Nn τ0 = s / (1 + τ0) := by
    unfold Nn; rw [← Real.sqrt_eq_rpow]
  have hr : τ ^ (1 / 2 : ℝ) = Real.sqrt τ := by rw [Real.sqrt_eq_rpow]
  have hr2 : τ ^ (-1 / 2 : ℝ) = (Real.sqrt τ)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hτ.le]; norm_num
  have hr3 : τ ^ (-3 / 2 : ℝ) = (Real.sqrt τ)⁻¹ * τ⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hτ.le, ← Real.rpow_neg_one, ← Real.rpow_add hτ]; norm_num
  have hq0 : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hqq : Real.sqrt τ * Real.sqrt τ = τ := Real.mul_self_sqrt hτ.le
  -- √τ ≤ 2 s and √τ ≥ s/2
  have hup : Real.sqrt τ ≤ 2 * s := by
    refine le_of_sq_le_sq (by nlinarith) (by positivity)
  have hlo : s / 2 ≤ Real.sqrt τ := by
    refine le_of_sq_le_sq ?_ hq0.le
    nlinarith
  have hinv : (Real.sqrt τ)⁻¹ ≤ 2 / s := by
    rw [inv_le_comm₀ hq0 (by positivity), inv_div]; exact hlo
  have hτinv : τ⁻¹ ≤ 2 / τ0 := by
    rw [inv_le_comm₀ hτ (by positivity), inv_div]; exact h1
  have hden : (1 + τ)⁻¹ ≤ 2 / (1 + τ0) := by
    rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]; linarith
  have e1 : KB * τ ^ (1 / 2 : ℝ) / (1 + τ) = KB * Real.sqrt τ * (1 + τ)⁻¹ := by rw [hr]; ring
  have e2 : τ0 / 2 * (KB * τ ^ (-1 / 2 : ℝ) / (1 + τ)) = τ0 / 2 * KB * (Real.sqrt τ)⁻¹ * (1 + τ)⁻¹ := by
    rw [hr2]; ring
  have e3 : (τ0 / 2) ^ 2 * (KB * τ ^ (-3 / 2 : ℝ) / (1 + τ)) =
      (τ0 / 2) ^ 2 * KB * ((Real.sqrt τ)⁻¹ * τ⁻¹) * (1 + τ)⁻¹ := by rw [hr3]; ring
  rw [hNn]
  have hKs : 0 ≤ KB * s := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]
    calc KB * Real.sqrt τ * (1 + τ)⁻¹ ≤ KB * (2 * s) * (2 / (1 + τ0)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hup hKB) hden (by positivity) (by positivity)
      _ = 4 * KB * (s / (1 + τ0)) := by ring
  · rw [e2]
    calc τ0 / 2 * KB * (Real.sqrt τ)⁻¹ * (1 + τ)⁻¹ ≤ τ0 / 2 * KB * (2 / s) * (2 / (1 + τ0)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hinv (by positivity)) hden (by positivity) (by positivity)
      _ = 2 * KB * (s / (1 + τ0)) := by
          rw [← hss]; field_simp
  · rw [e3]
    have hprod : (Real.sqrt τ)⁻¹ * τ⁻¹ ≤ 2 / s * (2 / τ0) :=
      mul_le_mul hinv hτinv (by positivity) (by positivity)
    calc (τ0 / 2) ^ 2 * KB * ((Real.sqrt τ)⁻¹ * τ⁻¹) * (1 + τ)⁻¹ ≤
        (τ0 / 2) ^ 2 * KB * (2 / s * (2 / τ0)) * (2 / (1 + τ0)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hprod (by positivity)) hden (by positivity) (by positivity)
      _ = 2 * KB * (s / (1 + τ0)) := by
          rw [← hss]; field_simp

/-- The rescaled, normalised amplitude is `D2` on `(-1,1)` with a uniform constant. -/
lemma amp_D2 {τ0 KB : ℝ} (hτ0 : 0 < τ0) (hKB : 0 ≤ KB) {B B1 B2 : ℝ → ℂ}
    (hB : ∀ τ : ℝ, 0 < τ → HasDerivAt B (B1 τ) τ) (hB1 : ∀ τ : ℝ, 0 < τ → HasDerivAt B1 (B2 τ) τ)
    (hc2 : ContinuousOn B2 (Ioi 0))
    (hbB : ∀ τ : ℝ, 0 < τ → ‖B τ‖ ≤ KB * τ ^ (1 / 2 : ℝ) / (1 + τ))
    (hbB1 : ∀ τ : ℝ, 0 < τ → ‖B1 τ‖ ≤ KB * τ ^ (-1 / 2 : ℝ) / (1 + τ))
    (hbB2 : ∀ τ : ℝ, 0 < τ → ‖B2 τ‖ ≤ KB * τ ^ (-3 / 2 : ℝ) / (1 + τ)) :
    D2 (Ioo (-1 : ℝ) 1) (fun t => (Nn τ0)⁻¹ • B (tt τ0 t))
      (fun t => ((τ0 / 2) * (Nn τ0)⁻¹) • B1 (tt τ0 t))
      (fun t => ((τ0 / 2) ^ 2 * (Nn τ0)⁻¹) • B2 (tt τ0 t)) (4 * KB) := by
  have hN := Nn_pos hτ0
  refine
    { d1 := fun y hy => ?_, d2 := fun y hy => ?_, c2 := ?_, K0 := by positivity, b0 := fun y hy => ?_,
      b1 := fun y hy => ?_, b2 := fun y hy => ?_ }
  · have hτ := tt_pos hτ0 hy
    have := ((hB _ hτ).scomp y (hasDerivAt_tt τ0 y)).const_smul (Nn τ0)⁻¹
    refine this.congr_deriv ?_
    rw [smul_smul]; congr 1; ring
  · have hτ := tt_pos hτ0 hy
    have := ((hB1 _ hτ).scomp y (hasDerivAt_tt τ0 y)).const_smul ((τ0 / 2) * (Nn τ0)⁻¹)
    refine this.congr_deriv ?_
    rw [smul_smul]; congr 1; ring
  · have hcomp : ContinuousOn (fun t => B2 (tt τ0 t)) (Ioo (-1 : ℝ) 1) :=
      hc2.comp (fun t _ => (hasDerivAt_tt τ0 t).continuousAt.continuousWithinAt) (fun t ht => tt_pos hτ0 ht)
    exact (continuousOn_const (c := ((τ0 / 2) ^ 2 * (Nn τ0)⁻¹))).smul hcomp
  · have hτ := tt_pos hτ0 hy
    obtain ⟨a1, -, -⟩ := amp_scale hτ0 (tt_ge hτ0 hy) (tt_le hτ0 hy) hKB
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hN)]
    calc (Nn τ0)⁻¹ * ‖B (tt τ0 y)‖ ≤ (Nn τ0)⁻¹ * (4 * KB * Nn τ0) :=
          mul_le_mul_of_nonneg_left ((hbB _ hτ).trans a1) (by positivity)
      _ = 4 * KB := by field_simp
  · have hτ := tt_pos hτ0 hy
    obtain ⟨-, a2, -⟩ := amp_scale hτ0 (tt_ge hτ0 hy) (tt_le hτ0 hy) hKB
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < τ0 / 2 * (Nn τ0)⁻¹)]
    have h5 : τ0 / 2 * (Nn τ0)⁻¹ * ‖B1 (tt τ0 y)‖ ≤
        τ0 / 2 * (Nn τ0)⁻¹ * (KB * (tt τ0 y) ^ (-1 / 2 : ℝ) / (1 + tt τ0 y)) :=
      mul_le_mul_of_nonneg_left (hbB1 _ hτ) (by positivity)
    calc τ0 / 2 * (Nn τ0)⁻¹ * ‖B1 (tt τ0 y)‖ ≤
        (Nn τ0)⁻¹ * (τ0 / 2 * (KB * (tt τ0 y) ^ (-1 / 2 : ℝ) / (1 + tt τ0 y))) := by
          refine h5.trans (le_of_eq ?_); ring
      _ ≤ (Nn τ0)⁻¹ * (2 * KB * Nn τ0) := mul_le_mul_of_nonneg_left a2 (by positivity)
      _ = 2 * KB := by field_simp
      _ ≤ 4 * KB := by linarith
  · have hτ := tt_pos hτ0 hy
    obtain ⟨-, -, a3⟩ := amp_scale hτ0 (tt_ge hτ0 hy) (tt_le hτ0 hy) hKB
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (τ0 / 2) ^ 2 * (Nn τ0)⁻¹)]
    have h5 : (τ0 / 2) ^ 2 * (Nn τ0)⁻¹ * ‖B2 (tt τ0 y)‖ ≤
        (τ0 / 2) ^ 2 * (Nn τ0)⁻¹ * (KB * (tt τ0 y) ^ (-3 / 2 : ℝ) / (1 + tt τ0 y)) :=
      mul_le_mul_of_nonneg_left (hbB2 _ hτ) (by positivity)
    calc (τ0 / 2) ^ 2 * (Nn τ0)⁻¹ * ‖B2 (tt τ0 y)‖ ≤
        (Nn τ0)⁻¹ * ((τ0 / 2) ^ 2 * (KB * (tt τ0 y) ^ (-3 / 2 : ℝ) / (1 + tt τ0 y))) := by
          refine h5.trans (le_of_eq ?_); ring
      _ ≤ (Nn τ0)⁻¹ * (2 * KB * Nn τ0) := mul_le_mul_of_nonneg_left a3 (by positivity)
      _ = 2 * KB := by field_simp
      _ ≤ 4 * KB := by linarith

lemma integral_tt {τ0 : ℝ} (hτ0 : 0 < τ0) (F : ℝ → ℂ) :
    ∫ τ, F τ = ((τ0 / 2 : ℝ) : ℂ) * ∫ t, F (tt τ0 t) := by
  have h1 : ∫ t, F (tt τ0 t) = ∫ t, (fun s => F (τ0 + s)) ((τ0 / 2) * t) := by
    congr 1; funext t; unfold tt; congr 1; ring
  rw [h1, Measure.integral_comp_mul_left (fun s => F (τ0 + s)) (τ0 / 2),
    integral_add_left_eq_self (fun s => F s) τ0]
  rw [Complex.real_smul, abs_of_pos (inv_pos.mpr (by positivity : 0 < τ0 / 2))]
  push_cast
  have : (τ0 : ℂ) ≠ 0 := by exact_mod_cast hτ0.ne'
  field_simp

lemma sqrt_scale {τ0 c m1v : ℝ} (hτ0 : 0 < τ0) (hc : 0 < c) (hm : 0 < m1v) :
    τ0 / 2 * Real.sqrt (2 * π / (c * (τ0 ^ 2 * m1v / 4))) = Real.sqrt (2 * π / (c * m1v)) := by
  have hpi := Real.pi_pos
  have e : (τ0 / 2) ^ 2 * (2 * π / (c * (τ0 ^ 2 * m1v / 4))) = 2 * π / (c * m1v) := by
    field_simp; ring
  rw [← e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- **Piece 1** (stationary-phase core): `∫₀^T B e^{icϕ} = e^{iπ/4} √(2π/(c m'(τ₀))) B(τ₀) e^{icϕ(τ₀)} + O(...)`. -/
theorem piece1 (C0 : ℝ) (hC0 : 0 < C0) :
    ∃ θ K : ℝ, 0 < θ ∧ θ < 1 ∧ 0 ≤ K ∧
      ∀ {m m1 m2 m3 : ℝ → ℝ} {τ0 c T KB : ℝ} {ϕ : ℝ → ℝ} {B B1 B2 : ℝ → ℂ},
        MData C0 m m1 m2 m3 → 0 < τ0 → 0 < c → 0 < T → 0 ≤ KB →
        1 ≤ c * (τ0 ^ 2 * m1 τ0 / 4) →
        (∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - m τ0) τ) →
        (∀ τ : ℝ, 0 < τ → HasDerivAt B (B1 τ) τ) → (∀ τ : ℝ, 0 < τ → HasDerivAt B1 (B2 τ) τ) →
        ContinuousOn B2 (Ioi 0) →
        (∀ τ : ℝ, 0 < τ → ‖B τ‖ ≤ KB * τ ^ (1 / 2 : ℝ) / (1 + τ)) →
        (∀ τ : ℝ, 0 < τ → ‖B1 τ‖ ≤ KB * τ ^ (-1 / 2 : ℝ) / (1 + τ)) →
        (∀ τ : ℝ, 0 < τ → ‖B2 τ‖ ≤ KB * τ ^ (-3 / 2 : ℝ) / (1 + τ)) →
        (∀ t : ℝ, θ ≤ |t| → B (tt τ0 t) = 0) → (∀ τ : ℝ, τ ≤ 0 ∨ T ≤ τ → B τ = 0) →
        ‖(∫ τ in (0 : ℝ)..T, B τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) -
            Complex.exp ((π : ℂ) / 4 * Complex.I) * ((Real.sqrt (2 * π / (c * m1 τ0)) : ℝ) : ℂ) * B τ0 *
              Complex.exp (Complex.I * c * (ϕ τ0 : ℂ))‖ ≤
          τ0 / 2 * Nn τ0 * K * (4 * KB) / ((c * (τ0 ^ 2 * m1 τ0 / 4)) * Real.sqrt (c * (τ0 ^ 2 * m1 τ0 / 4))) := by
  have hc1 : 0 < 2 / (9 * C0) := by positivity
  obtain ⟨θ, K, hθ0, hθ1, hK0, H⟩ := stat_phase (2 / (9 * C0)) (6 * C0) hc1
  refine ⟨θ, K, hθ0, hθ1, hK0, ?_⟩
  intro m m1 m2 m3 τ0 c T KB ϕ B B1 B2 hM hτ0 hc hT hKB hlam hϕ hB hB1 hc2 hbB hbB1 hbB2 hsupp hB0
  have hN := Nn_pos hτ0
  have hm1 := hM.m1_pos hτ0
  set D := τ0 ^ 2 * m1 τ0 / 4 with hD
  have hD0 : 0 < D := by positivity
  set lam := c * D with hlam_def
  have hlam0 : 0 < lam := by positivity
  have hph := phase_data hM hτ0 hϕ
  have hA := amp_D2 hτ0 hKB hB hB1 hc2 hbB hbB1 hbB2
  have hsupp' : ∀ t : ℝ, θ ≤ |t| → (Nn τ0)⁻¹ • B (tt τ0 t) = 0 := fun t ht => by rw [hsupp t ht, smul_zero]
  have key := H hph hA hsupp' hlam
  set E0 : ℂ := Complex.exp (Complex.I * c * (ϕ τ0 : ℂ)) with hE0
  set F : ℝ → ℂ := fun τ => B τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ)) with hF
  have h1 : ∫ τ in (0 : ℝ)..T, F τ = ∫ τ, F τ := by
    rw [intervalIntegral.integral_of_le hT.le]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun τ hτ => ?_
    have : τ ≤ 0 ∨ T ≤ τ := by
      by_contra hcon
      push_neg at hcon
      exact hτ ⟨hcon.1, hcon.2.le⟩
    simp [hF, hB0 τ this]
  have hexp : ∀ t : ℝ, F (tt τ0 t) = ((Nn τ0 : ℝ) : ℂ) * E0 *
      ((Nn τ0)⁻¹ • B (tt τ0 t) * Complex.exp (Complex.I * (lam : ℂ) *
        (((ϕ (tt τ0 t) - ϕ τ0) / (τ0 ^ 2 * m1 τ0 / 4) : ℝ) : ℂ))) := by
    intro t
    have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD0.ne'
    have hNc : ((Nn τ0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have hexp2 : Complex.exp (Complex.I * c * (ϕ (tt τ0 t) : ℂ)) = E0 * Complex.exp (Complex.I * (lam : ℂ) *
        (((ϕ (tt τ0 t) - ϕ τ0) / (τ0 ^ 2 * m1 τ0 / 4) : ℝ) : ℂ)) := by
      rw [hE0, ← Complex.exp_add]
      congr 1
      rw [hlam_def]
      push_cast
      have : ((τ0 : ℂ) ^ 2 * (m1 τ0 : ℂ) / 4) = (D : ℂ) := by rw [hD]; push_cast; ring
      rw [this]
      field_simp
      ring
    simp only [hF]
    rw [hexp2, Complex.real_smul]
    push_cast
    field_simp
  have h2 : ∫ τ, F τ = ((τ0 / 2 : ℝ) : ℂ) * (((Nn τ0 : ℝ) : ℂ) * E0 * ∫ t : ℝ, ((Nn τ0)⁻¹ • B (tt τ0 t) *
      Complex.exp (Complex.I * (lam : ℂ) * (((ϕ (tt τ0 t) - ϕ τ0) / (τ0 ^ 2 * m1 τ0 / 4) : ℝ) : ℂ)))) := by
    rw [integral_tt hτ0 F]
    congr 1
    rw [← integral_const_mul]
    congr 1; funext t
    exact hexp t
  have hf0 : m1 (tt τ0 0) / m1 τ0 = 1 := by
    have : tt τ0 0 = τ0 := by simp [tt]
    rw [this]; exact div_self hm1.ne'
  have hlead : Complex.exp ((π : ℂ) / 4 * Complex.I) * ((Real.sqrt (2 * π / (c * m1 τ0)) : ℝ) : ℂ) * B τ0 * E0 =
      ((τ0 / 2 : ℝ) : ℂ) * (((Nn τ0 : ℝ) : ℂ) * E0 * (Complex.exp ((π : ℂ) / 4 * Complex.I) *
        ((Real.sqrt (2 * π / (lam * (m1 (tt τ0 0) / m1 τ0))) : ℝ) : ℂ) * ((Nn τ0)⁻¹ • B (tt τ0 0)))) := by
    rw [hf0, mul_one, ← sqrt_scale hτ0 hc hm1]
    have : tt τ0 0 = τ0 := by simp [tt]
    rw [this, Complex.real_smul]
    have hNc : ((Nn τ0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [hlam_def, hD]
    push_cast
    field_simp
  rw [h1, h2, hlead, ← mul_sub, ← mul_sub, norm_mul, norm_mul, norm_mul]
  have hE0n : ‖E0‖ = 1 := norm_cexp_phase _ _
  rw [hE0n, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < τ0 / 2), abs_of_pos hN]
  have := key
  calc τ0 / 2 * (Nn τ0 * ‖_‖) ≤ τ0 / 2 * (Nn τ0 * (K * (4 * KB) / (lam * Real.sqrt lam))) := by
        gcongr
    _ = _ := by ring

end

end FormalResearch.SignUncertainty.CtOsc
