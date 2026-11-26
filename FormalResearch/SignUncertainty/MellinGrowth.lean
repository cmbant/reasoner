module

public import FormalResearch.SignUncertainty.MellinStripAnalytic
public import FormalResearch.Special.ComplexStirlingStrip

/-!
# Crude growth bounds in the Mellin strip (`gt:7.4(2)`, growth hypothesis)

The Phragmén–Lindelöf step of `gt:7.4(2)` needs only that `M̃_f(z) e^{-cℋ(ζ)}` has at most
double-exponential growth `exp(B exp(a |Im ζ|))`, `a < π`, in the strip. This module proves the
inputs, with non-sharp constants:

* `exists_norm_inv_Gamma_le`: `1/|Γ(z)| ≤ K e^{K |Im z|}` on `a ≤ Re z ≤ b` (`a ≥ 1/2`), from
  `norm_Gamma_strip_abs` for `|Im z| ≥ 1` and compactness otherwise.
* `exists_norm_mellinStrip_le`: for `c > 3/2`, `f ∈ 𝒜_c^ε`: `|M̃_f(z)| ≤ K e^{K|Im z|}` on `0 < Re z < c`,
  using the reflection `M̃_f(c-z) = ε M̃_f(z)` for `Re z < c/2`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special.ComplexStirling

/-- Lower bound for `|Γ|` in a vertical strip, in the form `1/|Γ(z)| ≤ K e^{K |Im z|}`. -/
theorem exists_norm_inv_Gamma_le {a b : ℝ} (ha : 1 / 2 ≤ a) (hab : a ≤ b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖Complex.Gamma z‖⁻¹ ≤ K * Real.exp (K * |z.im|) := by
  -- compact part `|Im z| ≤ 1`
  set C0 : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
      (Icc a b ×ˢ Icc (-1 : ℝ) 1) with hC0
  have hC0c : IsCompact C0 :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hC0re : ∀ z ∈ C0, 0 < z.re := by
    rintro z ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one, sub_self]
    linarith [hx.1]
  have hcont : ContinuousOn (fun z : ℂ => ‖Complex.Gamma z‖⁻¹) C0 := by
    intro z hz
    have hz0 : 0 < z.re := hC0re z hz
    have hne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz0
    have hd : DifferentiableAt ℂ Complex.Gamma z := by
      apply Complex.differentiableAt_Gamma
      intro m hm
      have := congrArg Complex.re hm
      simp at this
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact ((hd.continuousAt.norm).inv₀ (norm_ne_zero_iff.mpr hne)).continuousWithinAt
  obtain ⟨K0, hK0⟩ := hC0c.exists_bound_of_continuousOn hcont
  -- far part
  set Kb : ℝ := (b + 1 / 2) * b ^ 2 / 2 + b ^ 3 / 3 with hKb
  refine ⟨max (max K0 (Real.exp (Kb + 2))) 2, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro z hza hzb
  set K : ℝ := max (max K0 (Real.exp (Kb + 2))) 2 with hK
  have hK2 : 2 ≤ K := le_max_right _ _
  have hKK0 : K0 ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hKe : Real.exp (Kb + 2) ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have hx0 : 0 < z.re := by linarith
  by_cases hy : |z.im| ≤ 1
  · have hzC : z ∈ C0 := ⟨(z.re, z.im), ⟨⟨hza, hzb⟩, abs_le.mp hy⟩, by simp⟩
    have h1 := hK0 z hzC
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
    calc ‖Complex.Gamma z‖⁻¹ ≤ K0 := h1
      _ ≤ K := hKK0
      _ ≤ K * Real.exp (K * |z.im|) := by
        have : 1 ≤ Real.exp (K * |z.im|) :=
          Real.one_le_exp (mul_nonneg (by linarith) (abs_nonneg _))
        nlinarith [this, (by linarith : (0 : ℝ) ≤ K)]
  · replace hy := lt_of_not_ge hy
    have hy0 : z.im ≠ 0 := by intro h; rw [h] at hy; simp at hy; linarith
    have hzeq : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by simp
    have hG := norm_Gamma_strip_abs hx0 hy0
    rw [← hzeq] at hG
    have hyp : 0 < |z.im| := by linarith
    have hδ := abs_stripDelta_le hx0 hyp
    have hconst : stripConst z.re ≤ Kb := by
      unfold stripConst
      have h1 : |z.re - 1 / 2| ≤ b + 1 / 2 := by
        rw [abs_le]; constructor <;> linarith
      have h2 : z.re ^ 2 ≤ b ^ 2 := by nlinarith
      have h3 : z.re ^ 3 ≤ b ^ 3 := by nlinarith [sq_nonneg z.re, sq_nonneg b, sq_nonneg (z.re - b)]
      have : |z.re - 1 / 2| * z.re ^ 2 ≤ (b + 1 / 2) * b ^ 2 :=
        mul_le_mul h1 h2 (by positivity) (by linarith)
      linarith
    have hc0 : 0 ≤ stripConst z.re := by unfold stripConst; positivity
    have hδ2 : abs (stripDelta z.re |z.im|) ≤ Kb + 2 := by
      refine hδ.trans ?_
      have hy1 : 1 ≤ |z.im| := hy.le
      have e1 : stripConst z.re / |z.im| ^ 2 ≤ stripConst z.re := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (|z.im|), mul_nonneg hc0 (sub_nonneg.2 (one_le_pow₀ hy1 : (1 : ℝ) ≤ |z.im| ^ 2))]
      have e2 : 2 / |z.im| ≤ 2 := by
        rw [div_le_iff₀ hyp]; nlinarith
      linarith
    have hge : Real.exp (-(Kb + 2)) ≤ Real.exp (stripDelta z.re |z.im|) :=
      Real.exp_le_exp.mpr (by linarith [(abs_le.mp hδ2).1])
    have hpow : (1 : ℝ) ≤ |z.im| ^ (z.re - 1 / 2) :=
      Real.one_le_rpow hy.le (by linarith)
    have hsq : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
      rw [Real.one_le_sqrt]; nlinarith [Real.pi_gt_three]
    have hlow : Real.exp (-(Real.pi * |z.im| / 2)) * Real.exp (-(Kb + 2)) ≤ ‖Complex.Gamma z‖ := by
      rw [hG]
      have hp1 : 0 < Real.exp (-(Real.pi * |z.im| / 2)) := Real.exp_pos _
      have hp2 : 0 < Real.exp (-(Kb + 2)) := Real.exp_pos _
      calc Real.exp (-(Real.pi * |z.im| / 2)) * Real.exp (-(Kb + 2))
          = 1 * 1 * Real.exp (-(Real.pi * |z.im| / 2)) * Real.exp (-(Kb + 2)) := by ring
        _ ≤ Real.sqrt (2 * Real.pi) * |z.im| ^ (z.re - 1 / 2) *
              Real.exp (-(Real.pi * |z.im| / 2)) * Real.exp (stripDelta z.re |z.im|) := by
          gcongr
    have hpos : 0 < Real.exp (-(Real.pi * |z.im| / 2)) * Real.exp (-(Kb + 2)) := by positivity
    have hinv : ‖Complex.Gamma z‖⁻¹ ≤ Real.exp (Kb + 2) * Real.exp (Real.pi * |z.im| / 2) := by
      calc ‖Complex.Gamma z‖⁻¹ ≤ (Real.exp (-(Real.pi * |z.im| / 2)) * Real.exp (-(Kb + 2)))⁻¹ :=
            inv_anti₀ hpos hlow
        _ = Real.exp (Kb + 2) * Real.exp (Real.pi * |z.im| / 2) := by
          rw [← Real.exp_add, ← Real.exp_neg, ← Real.exp_add]; congr 1; ring
    calc ‖Complex.Gamma z‖⁻¹ ≤ Real.exp (Kb + 2) * Real.exp (Real.pi * |z.im| / 2) := hinv
      _ ≤ K * Real.exp (K * |z.im|) := by
        refine mul_le_mul hKe (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by linarith)
        have : Real.pi / 2 ≤ 2 := by linarith [Real.pi_lt_four]
        nlinarith [abs_nonneg z.im]

/-- Crude exponential bound for `M̃_f` on the right half of the strip `c/2 ≤ Re z < c`. -/
theorem exists_norm_mellinStrip_le_right {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ}
    (hf : IsHankelEigenfn c ε f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, c / 2 ≤ z.re → z.re ≤ c →
      ‖mellinStrip f z‖ ≤ K * Real.exp (K * |z.im|) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨K1, hK1, hG⟩ := exists_norm_inv_Gamma_le (a := c / 2) (b := c) (by linarith) (by linarith)
  have hi1 := integrableOn_abs_mul_rpow_eigen hc0 hf (x := c / 2) (by linarith) (by linarith)
  have hi2 := integrableOn_abs_mul_rpow_eigen hc0 hf (x := c) hc0 le_rfl
  set J : ℝ := ∫ Δ in Ioi (0 : ℝ), (|f Δ| * Δ ^ (c / 2 - 1) + |f Δ| * Δ ^ (c - 1)) with hJ
  have hJ0 : 0 ≤ J := by
    refine setIntegral_nonneg measurableSet_Ioi fun Δ hΔ => ?_
    have : 0 < Δ := hΔ
    positivity
  have h2pi : (1 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
  refine ⟨K1 * (2 * Real.pi) ^ c * J + K1, by positivity, ?_⟩
  intro z hza hzb
  have hx0 : 0 < z.re := by linarith
  have hraw : ‖mellinRaw f z‖ ≤ J := by
    unfold mellinRaw
    refine (norm_integral_le_integral_norm _).trans ?_
    refine setIntegral_mono_on ((integrableOn_mellin_integrand hc0 hf hx0 hzb).norm)
      (hi1.add hi2) measurableSet_Ioi fun Δ hΔ => ?_
    have hΔ0 : 0 < Δ := hΔ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hΔ0]
    simp only [Complex.sub_re, Complex.one_re]
    have hfa := abs_nonneg (f Δ)
    rcases le_or_gt 1 Δ with h1 | h1
    · have : Δ ^ (z.re - 1) ≤ Δ ^ (c - 1) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
      have h0 : 0 ≤ |f Δ| * Δ ^ (c / 2 - 1) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this hfa]
    · have : Δ ^ (z.re - 1) ≤ Δ ^ (c / 2 - 1) :=
        Real.rpow_le_rpow_of_exponent_ge hΔ0 h1.le (by linarith)
      have h0 : 0 ≤ |f Δ| * Δ ^ (c - 1) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this hfa]
  have hpow : ‖((2 * Real.pi : ℝ) : ℂ) ^ z‖ ≤ (2 * Real.pi) ^ c := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le h2pi.le hzb
  have hGz := hG z hza hzb
  unfold mellinStrip
  rw [norm_mul, norm_div]
  have hexp : 1 ≤ Real.exp ((K1 * (2 * Real.pi) ^ c * J + K1) * |z.im|) := Real.one_le_exp
    (mul_nonneg (by positivity) (abs_nonneg _))
  have hP0 : 0 ≤ (2 * Real.pi) ^ c := Real.rpow_nonneg (by positivity) c
  have hKJ : 0 ≤ K1 * (2 * Real.pi) ^ c * J := mul_nonneg (mul_nonneg hK1 hP0) hJ0
  have hexp2 : Real.exp (K1 * |z.im|) ≤ Real.exp ((K1 * (2 * Real.pi) ^ c * J + K1) * |z.im|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
  have hnorm : ‖((2 * Real.pi : ℝ) : ℂ) ^ z‖ / ‖Complex.Gamma z‖ * ‖mellinRaw f z‖ ≤
      (2 * Real.pi) ^ c * (K1 * Real.exp (K1 * |z.im|)) * J := by
    rw [div_eq_mul_inv]
    have e1 : ‖((2 * Real.pi : ℝ) : ℂ) ^ z‖ * ‖Complex.Gamma z‖⁻¹ ≤
        (2 * Real.pi) ^ c * (K1 * Real.exp (K1 * |z.im|)) :=
      mul_le_mul hpow hGz (by positivity) hP0
    exact mul_le_mul e1 hraw (norm_nonneg _) (by positivity)
  refine hnorm.trans ?_
  calc (2 * Real.pi) ^ c * (K1 * Real.exp (K1 * |z.im|)) * J
      = (K1 * (2 * Real.pi) ^ c * J) * Real.exp (K1 * |z.im|) := by ring
    _ ≤ (K1 * (2 * Real.pi) ^ c * J + K1) * Real.exp ((K1 * (2 * Real.pi) ^ c * J + K1) * |z.im|) := by
      exact mul_le_mul (by linarith) hexp2 (Real.exp_pos _).le (by linarith)

/-- Crude exponential bound for `M̃_f` on the whole strip `0 < Re z < c` (`ε = ±1`). -/
theorem exists_norm_mellinStrip_le {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ}
    (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, 0 < z.re → z.re < c →
      ‖mellinStrip f z‖ ≤ K * Real.exp (K * |z.im|) := by
  obtain ⟨K, hK, hb⟩ := exists_norm_mellinStrip_le_right hc hf
  refine ⟨K, hK, fun z hz0 hzc => ?_⟩
  by_cases hz : c / 2 ≤ z.re
  · exact hb z hz hzc.le
  · have hz' : z.re < c / 2 := lt_of_not_ge hz
    have hrefl := mellinStrip_reflection hc hf (z := z) hz0 hzc
    have hnorm : ‖mellinStrip f z‖ = ‖mellinStrip f ((c : ℂ) - z)‖ := by
      have hε1 : ‖(ε : ℂ)‖ = 1 := by
        rcases hε with h | h <;> simp [h]
      have hrefl' := mellinStrip_reflection hc hf (z := (c : ℂ) - z) (by simp; linarith)
        (by simp; linarith)
      rw [sub_sub_cancel] at hrefl'
      rw [hrefl', norm_mul, hε1, one_mul]
    rw [hnorm]
    have hre : ((c : ℂ) - z).re = c - z.re := by simp
    have him : |((c : ℂ) - z).im| = |z.im| := by simp
    have := hb ((c : ℂ) - z) (by rw [hre]; linarith) (by rw [hre]; linarith)
    rwa [him] at this

/-- info: 'FormalResearch.SignUncertainty.exists_norm_inv_Gamma_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_norm_inv_Gamma_le

/-- info: 'FormalResearch.SignUncertainty.exists_norm_mellinStrip_le_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_norm_mellinStrip_le_right

/-- info: 'FormalResearch.SignUncertainty.exists_norm_mellinStrip_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_norm_mellinStrip_le

end FormalResearch.SignUncertainty
