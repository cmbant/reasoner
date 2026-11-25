module

public import FormalResearch.SignUncertainty.CtOuterBandConcrete

/-!
# Derivative bounds for the modulus `√(6 m'/π²)` of the outer amplitude

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 4 (`ct:A-derivs`: `|A^{(k)}| ≤ C_k
min(τ^{1/2-k}, τ^{-1/2-k})`), the factor `√(6 m'(τ)/π²)`.  **Proved.**
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.SignUncertainty.CtOsc

/-- `f = √(6 m'/π²)`. -/
noncomputable def sqf (m1 : ℝ → ℝ) (τ : ℝ) : ℝ := Real.sqrt (6 / π ^ 2 * m1 τ)
noncomputable def sqf1 (m1 m2 : ℝ → ℝ) (τ : ℝ) : ℝ := 6 / π ^ 2 * m2 τ / (2 * sqf m1 τ)
noncomputable def sqf2 (m1 m2 m3 : ℝ → ℝ) (τ : ℝ) : ℝ :=
  6 / π ^ 2 * m3 τ / (2 * sqf m1 τ) - 6 / π ^ 2 * m2 τ * sqf1 m1 m2 τ / (2 * sqf m1 τ ^ 2)

section
variable {C0 : ℝ} {m m1 m2 m3 : ℝ → ℝ}

lemma sqf_pos (hM : MData C0 m m1 m2 m3) {τ : ℝ} (hτ : 0 < τ) : 0 < sqf m1 τ := by
  unfold sqf; exact Real.sqrt_pos.mpr (by have := hM.m1_pos hτ; positivity)

lemma hasDerivAt_sqf (hM : MData C0 m m1 m2 m3) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (sqf m1) (sqf1 m1 m2 τ) τ := by
  have h1 := ((hM.d1 τ hτ).const_mul (6 / π ^ 2)).sqrt (by have := hM.m1_pos hτ; positivity)
  exact h1.congr_deriv (by unfold sqf1 sqf; ring)

lemma hasDerivAt_sqf1 (hM : MData C0 m m1 m2 m3) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (sqf1 m1 m2) (sqf2 m1 m2 m3 τ) τ := by
  have hf := hasDerivAt_sqf hM hτ
  have hfp := sqf_pos hM hτ
  have h1 := ((hM.d2 τ hτ).const_mul (6 / π ^ 2)).div (hf.const_mul 2) (by positivity)
  refine h1.congr_deriv ?_
  unfold sqf2
  have : sqf m1 τ ≠ 0 := hfp.ne'
  field_simp

lemma continuousOn_sqf2 (hM : MData C0 m m1 m2 m3) : ContinuousOn (sqf2 m1 m2 m3) (Ioi 0) := by
  intro τ hτ
  have hτ' : 0 < τ := hτ
  have hc : ∀ x ∈ Ioi (0 : ℝ), ContinuousAt (sqf m1) x := fun x hx => (hasDerivAt_sqf hM hx).continuousAt
  have hf : ContinuousAt (sqf m1) τ := hc τ hτ
  have hf1 : ContinuousAt (sqf1 m1 m2) τ := (hasDerivAt_sqf1 hM hτ').continuousAt
  have hm2 : ContinuousAt m2 τ := (hM.d2 τ hτ').continuousAt
  have hm3 : ContinuousAt m3 τ := hM.c3.continuousAt (Ioi_mem_nhds hτ')
  have hfp := sqf_pos hM hτ'
  unfold sqf2
  refine ContinuousAt.continuousWithinAt (ContinuousAt.sub ?_ ?_)
  · exact (continuousAt_const.mul hm3).div (continuousAt_const.mul hf) (by positivity)
  · exact ((continuousAt_const.mul hm2).mul hf1).div (continuousAt_const.mul (hf.pow 2)) (by positivity)

theorem sqf_bounds (hM : MData C0 m m1 m2 m3) : ∃ KF : ℝ, 0 ≤ KF ∧ ∀ τ : ℝ, 0 < τ →
    |sqf m1 τ| ≤ KF * τ ^ (1 / 2 : ℝ) / (1 + τ) ∧ |sqf1 m1 m2 τ| ≤ KF * τ ^ (-1 / 2 : ℝ) / (1 + τ) ∧
      |sqf2 m1 m2 m3 τ| ≤ KF * τ ^ (-3 / 2 : ℝ) / (1 + τ) := by
  have hC0 := hM.C0nn
  have hpi := Real.pi_pos
  set a : ℝ := 6 / π ^ 2 with ha
  have ha0 : 0 < a := by positivity
  set sa := Real.sqrt a with hsa
  have hsa0 : 0 < sa := Real.sqrt_pos.mpr ha0
  have hsasq : sa ^ 2 = a := Real.sq_sqrt ha0.le
  set K1 := Real.sqrt (2 * a * C0) with hK1
  have hK10 : 0 ≤ K1 := Real.sqrt_nonneg _
  have hK1sq : K1 ^ 2 = 2 * a * C0 := Real.sq_sqrt (by positivity)
  set K2 := sa * C0 / 2 with hK2
  set K3 := sa * C0 / 2 + sa * C0 ^ 2 / 4 with hK3
  refine ⟨K1 + K2 + K3, by positivity, fun τ hτ => ?_⟩
  set S := Real.sqrt τ with hS
  have hS0 : 0 < S := Real.sqrt_pos.mpr hτ
  have hSS : S ^ 2 = τ := Real.sq_sqrt hτ.le
  set D := 1 + τ with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  have hr : τ ^ (1 / 2 : ℝ) = S := by rw [hS, Real.sqrt_eq_rpow]
  have hr2 : τ ^ (-1 / 2 : ℝ) = S⁻¹ := by
    rw [hS, Real.sqrt_eq_rpow, ← Real.rpow_neg hτ.le]; norm_num
  have hr3 : τ ^ (-3 / 2 : ℝ) = (S ^ 3)⁻¹ := rpow_neg_three_half hτ
  rw [hr, hr2, hr3]
  have hm1p := hM.m1_pos hτ
  have hm1lo := hM.lo τ hτ
  have hm1hi := hM.hi τ hτ
  have m2b := hM.b2 τ hτ
  have m3b := hM.b3 τ hτ
  set f := sqf m1 τ with hf
  have hfp : 0 < f := sqf_pos hM hτ
  have hfsq : f ^ 2 = a * m1 τ := Real.sq_sqrt (by positivity)
  have hν : τ / (1 + τ ^ 2) ≤ m1 τ := hm1lo
  have hD2 : 1 + τ ^ 2 ≤ D ^ 2 := by rw [hD]; nlinarith
  have hD2' : D ^ 2 ≤ 2 * (1 + τ ^ 2) := by rw [hD]; nlinarith [sq_nonneg (τ - 1)]
  have hlo : sa * S ≤ f * D := by
    have hb : τ / D ^ 2 ≤ m1 τ := (div_le_div_of_nonneg_left hτ.le (by positivity) hD2).trans hν
    have h1 : (sa * S / D) ^ 2 ≤ f ^ 2 := by
      rw [hfsq, div_pow, mul_pow, hsasq, hSS]
      calc a * τ / D ^ 2 = a * (τ / D ^ 2) := by ring
        _ ≤ a * m1 τ := mul_le_mul_of_nonneg_left hb ha0.le
    have := le_of_sq_le_sq h1 hfp.le
    rwa [div_le_iff₀ hD0] at this
  have hhi : f ≤ K1 * S / D := by
    refine le_of_sq_le_sq ?_ (by positivity)
    have h2 : τ / (1 + τ ^ 2) ≤ 2 * τ / D ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hD2' hτ.le
      linarith
    have h3 : m1 τ ≤ C0 * (2 * τ / D ^ 2) :=
      hm1hi.trans (mul_le_mul_of_nonneg_left h2 hC0)
    rw [hfsq, div_pow, mul_pow, hK1sq, hSS]
    calc a * m1 τ ≤ a * (C0 * (2 * τ / D ^ 2)) := mul_le_mul_of_nonneg_left h3 ha0.le
      _ = 2 * a * C0 * τ / D ^ 2 := by ring
  have hinv : 1 / f ≤ D / (sa * S) := by
    rw [div_le_div_iff₀ hfp (by positivity)]; linarith
  have hK1le : K1 ≤ K1 + K2 + K3 := by
    have : 0 ≤ K2 := by positivity
    have : 0 ≤ K3 := by positivity
    linarith
  have hinv0 : 0 ≤ 1 / f := by positivity
  have hDsa : 0 ≤ D / (sa * S) := by positivity
  have e1 : |sqf1 m1 m2 τ| = a * |m2 τ| * (1 / f) / 2 := by
    unfold sqf1
    rw [abs_div, abs_mul, abs_of_pos ha0, abs_of_pos (by positivity : 0 < 2 * f)]
    field_simp
  have b1 : |sqf1 m1 m2 τ| ≤ K2 * S⁻¹ / D := by
    rw [e1]
    have h1 : a * |m2 τ| * (1 / f) ≤ a * (C0 / D ^ 2) * (D / (sa * S)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left m2b ha0.le) hinv hinv0 (by positivity)
    calc a * |m2 τ| * (1 / f) / 2 ≤ a * (C0 / D ^ 2) * (D / (sa * S)) / 2 :=
          div_le_div_of_nonneg_right h1 (by norm_num)
      _ = K2 * S⁻¹ / D := by rw [hK2, ← hsasq]; field_simp
  have u1 : |a * m3 τ / (2 * f)| = a * |m3 τ| * (1 / f) / 2 := by
    rw [abs_div, abs_mul, abs_of_pos ha0, abs_of_pos (by positivity : 0 < 2 * f)]; field_simp
  have u2 : |a * m2 τ * sqf1 m1 m2 τ / (2 * f ^ 2)| = a * |m2 τ| * |sqf1 m1 m2 τ| * (1 / f) ^ 2 / 2 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos ha0, abs_of_pos (by positivity : 0 < 2 * f ^ 2)]; field_simp
  have hf2 : |sqf2 m1 m2 m3 τ| ≤ a * |m3 τ| * (1 / f) / 2 + a * |m2 τ| * |sqf1 m1 m2 τ| * (1 / f) ^ 2 / 2 := by
    have e : sqf2 m1 m2 m3 τ = a * m3 τ / (2 * f) - a * m2 τ * sqf1 m1 m2 τ / (2 * f ^ 2) := rfl
    rw [e]
    exact (abs_sub _ _).trans (le_of_eq (by rw [u1, u2]))
  have t1 : a * |m3 τ| * (1 / f) / 2 ≤ K2 / (D * S ^ 3) := by
    have h1 : a * |m3 τ| * (1 / f) ≤ a * (C0 / D ^ 3) * (D / (sa * S)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left m3b ha0.le) hinv hinv0 (by positivity)
    calc a * |m3 τ| * (1 / f) / 2 ≤ a * (C0 / D ^ 3) * (D / (sa * S)) / 2 :=
          div_le_div_of_nonneg_right h1 (by norm_num)
      _ = K2 / (D ^ 2 * S) := by rw [hK2, ← hsasq]; field_simp
      _ ≤ K2 / (D * S ^ 3) := by
        refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        have : S ^ 2 ≤ D := by rw [hSS, hD]; linarith
        have hDS : 0 < D * S := by positivity
        have := mul_le_mul_of_nonneg_left this hDS.le
        calc D * S ^ 3 = D * S * S ^ 2 := by ring
          _ ≤ D * S * D := this
          _ = D ^ 2 * S := by ring
  have t2 : a * |m2 τ| * |sqf1 m1 m2 τ| * (1 / f) ^ 2 / 2 ≤ (sa * C0 ^ 2 / 4) / (D * S ^ 3) := by
    have hx2 : (1 / f) ^ 2 ≤ (D / (sa * S)) ^ 2 := pow_le_pow_left₀ hinv0 hinv 2
    have h1 : a * |m2 τ| * |sqf1 m1 m2 τ| * (1 / f) ^ 2 ≤
        a * (C0 / D ^ 2) * (K2 * S⁻¹ / D) * (D / (sa * S)) ^ 2 :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left m2b ha0.le) b1 (abs_nonneg _) (by positivity)) hx2
        (by positivity) (by positivity)
    calc a * |m2 τ| * |sqf1 m1 m2 τ| * (1 / f) ^ 2 / 2 ≤
        a * (C0 / D ^ 2) * (K2 * S⁻¹ / D) * (D / (sa * S)) ^ 2 / 2 := div_le_div_of_nonneg_right h1 (by norm_num)
      _ = (sa * C0 ^ 2 / 4) / (D * S ^ 3) := by rw [hK2, ← hsasq]; field_simp; ring
  have hK3le : K3 ≤ K1 + K2 + K3 := by
    have : 0 ≤ K2 := by positivity
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_of_pos hfp]
    calc f ≤ K1 * S / D := hhi
      _ ≤ (K1 + K2 + K3) * S / D := by gcongr
  · refine b1.trans ?_
    have : 0 ≤ K3 := by positivity
    have hw : 0 ≤ S⁻¹ / D := by positivity
    calc K2 * S⁻¹ / D = K2 * (S⁻¹ / D) := by ring
      _ ≤ (K1 + K2 + K3) * (S⁻¹ / D) := mul_le_mul_of_nonneg_right (by linarith) hw
      _ = _ := by ring
  · have hs : K2 / (D * S ^ 3) + (sa * C0 ^ 2 / 4) / (D * S ^ 3) = K3 * (S ^ 3)⁻¹ / D := by
      rw [hK3, hK2]; field_simp
    have hw : 0 ≤ (S ^ 3)⁻¹ / D := by positivity
    have h5 : K3 * (S ^ 3)⁻¹ / D ≤ (K1 + K2 + K3) * (S ^ 3)⁻¹ / D := by
      calc K3 * (S ^ 3)⁻¹ / D = K3 * ((S ^ 3)⁻¹ / D) := by ring
        _ ≤ (K1 + K2 + K3) * ((S ^ 3)⁻¹ / D) := mul_le_mul_of_nonneg_right hK3le hw
        _ = _ := by ring
    exact hf2.trans ((add_le_add t1 t2).trans (hs.le.trans h5))

end

end FormalResearch.SignUncertainty.CtOsc
