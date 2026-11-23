module

public import FormalResearch.SignUncertainty.MellinGrowth

/-!
# Decay of the raw Mellin transform on the left of the strip (`lem:radial-compactness`, Step 1)

For `c > 3/2`, `f ∈ 𝒜_c^ε`, `ε = ±1` and `0 < x₁`, `2 x₁ < c`: `|mellinRaw f (x₁ + i y)| ≤ C (1 + |y|)^{-(c - 2 x₁)}`.
The reflection `M̃_f(c - z) = ε M̃_f(z)` and the trivial bound `|mellinRaw f| ≤ J` on `x₁ ≤ Re z ≤ c` give
`|mellinRaw f z| ≲ |Γ(z)| / |Γ(c - z)|`, and `norm_Gamma_strip_abs` gives the ratio `|y|^{2x₁ - c}`.
This is the left-edge bound of the three-lines argument of `MellinInversion`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special.ComplexStirling

/-- `|mellinRaw f z| ≤ J` on `x₀ ≤ Re z ≤ c`. -/
theorem exists_norm_mellinRaw_le {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    {x0 : ℝ} (hx0 : 0 < x0) (hx0c : x0 ≤ c) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ z : ℂ, x0 ≤ z.re → z.re ≤ c → ‖mellinRaw f z‖ ≤ J := by
  have hi1 := integrableOn_abs_mul_rpow_eigen hc hf hx0 hx0c
  have hi2 := integrableOn_abs_mul_rpow_eigen hc hf hc le_rfl
  set J : ℝ := ∫ Δ in Ioi (0 : ℝ), (|f Δ| * Δ ^ (x0 - 1) + |f Δ| * Δ ^ (c - 1)) with hJ
  have hJ0 : 0 ≤ J := by
    refine setIntegral_nonneg measurableSet_Ioi fun Δ hΔ => ?_
    have : 0 < Δ := hΔ
    positivity
  refine ⟨J, hJ0, fun z hza hzb => ?_⟩
  have hz0 : 0 < z.re := by linarith
  unfold mellinRaw
  refine (norm_integral_le_integral_norm _).trans ?_
  refine setIntegral_mono_on ((integrableOn_mellin_integrand hc hf hz0 hzb).norm)
    (hi1.add hi2) measurableSet_Ioi fun Δ hΔ => ?_
  have hΔ0 : 0 < Δ := hΔ
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hΔ0]
  simp only [Complex.sub_re, Complex.one_re]
  have hfa := abs_nonneg (f Δ)
  rcases le_or_gt 1 Δ with h1 | h1
  · have : Δ ^ (z.re - 1) ≤ Δ ^ (c - 1) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    have h0 : 0 ≤ |f Δ| * Δ ^ (x0 - 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hfa]
  · have : Δ ^ (z.re - 1) ≤ Δ ^ (x0 - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hΔ0 h1.le (by linarith)
    have h0 : 0 ≤ |f Δ| * Δ ^ (c - 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hfa]

/-- Uniform bound for the Stirling remainder `δ(x, y)` on `0 < x ≤ b`, `y ≥ 1`. -/
lemma abs_stripDelta_le_const {x y b : ℝ} (hx : 0 < x) (hxb : x ≤ b) (hy : 1 ≤ y) :
    abs (stripDelta x y) ≤ (b + 1 / 2) * b ^ 2 / 2 + b ^ 3 / 3 + 2 := by
  have hy0 : 0 < y := by linarith
  have hδ := abs_stripDelta_le hx hy0
  have hconst : stripConst x ≤ (b + 1 / 2) * b ^ 2 / 2 + b ^ 3 / 3 := by
    unfold stripConst
    have h1 : |x - 1 / 2| ≤ b + 1 / 2 := by
      rw [abs_le]; constructor <;> linarith
    have h2 : x ^ 2 ≤ b ^ 2 := by nlinarith
    have h3 : x ^ 3 ≤ b ^ 3 := by nlinarith [sq_nonneg x, sq_nonneg b, sq_nonneg (x - b)]
    have : |x - 1 / 2| * x ^ 2 ≤ (b + 1 / 2) * b ^ 2 :=
      mul_le_mul h1 h2 (by positivity) (by linarith)
    linarith
  have hc0 : 0 ≤ stripConst x := by unfold stripConst; positivity
  refine hδ.trans ?_
  have e1 : stripConst x / y ^ 2 ≤ stripConst x := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hc0 (sub_nonneg.2 (one_le_pow₀ hy : (1 : ℝ) ≤ y ^ 2))]
  have e2 : 2 / y ≤ 2 := by
    rw [div_le_iff₀ hy0]; nlinarith
  linarith

/-- The Gamma ratio `|Γ(x₁ + iy)| / |Γ(c - x₁ - iy)| ≤ e^{2D} |y|^{2x₁ - c}` for `|y| ≥ 1`. -/
lemma norm_Gamma_ratio_le {c x1 y : ℝ} (hx1 : 0 < x1) (hx1c : 2 * x1 < c) (hy : 1 ≤ |y|) :
    ‖Complex.Gamma ((x1 : ℂ) + (y : ℂ) * Complex.I)‖ /
        ‖Complex.Gamma (((c - x1 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I)‖ ≤
      Real.exp (2 * ((c + 1 / 2) * c ^ 2 / 2 + c ^ 3 / 3 + 2)) * |y| ^ (2 * x1 - c) := by
  have hy0 : y ≠ 0 := by intro h; rw [h] at hy; simp at hy; linarith
  have hx2 : 0 < c - x1 := by linarith
  have hay : 0 < |y| := by linarith
  have h1 := norm_Gamma_strip_abs hx1 hy0
  have h2 := norm_Gamma_strip_abs hx2 (neg_ne_zero.mpr hy0)
  rw [abs_neg] at h2
  rw [h1, h2]
  set D : ℝ := (c + 1 / 2) * c ^ 2 / 2 + c ^ 3 / 3 + 2 with hD
  have d1 : abs (stripDelta x1 |y|) ≤ D := abs_stripDelta_le_const hx1 (by linarith) hy
  have d2 : abs (stripDelta (c - x1) |y|) ≤ D := abs_stripDelta_le_const hx2 (by linarith) hy
  have hS : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hq : 0 < |y| ^ (c - x1 - 1 / 2) := Real.rpow_pos_of_pos hay _
  have hE : 0 < Real.exp (-(Real.pi * |y| / 2)) := Real.exp_pos _
  have hpq : |y| ^ (x1 - 1 / 2) = |y| ^ (c - x1 - 1 / 2) * |y| ^ (2 * x1 - c) := by
    rw [← Real.rpow_add hay]; congr 1; ring
  rw [hpq]
  have hden : 0 < Real.sqrt (2 * Real.pi) * |y| ^ (c - x1 - 1 / 2) *
      Real.exp (-(Real.pi * |y| / 2)) * Real.exp (stripDelta (c - x1) |y|) := by positivity
  rw [div_le_iff₀ hden, show Real.sqrt (2 * Real.pi) * (|y| ^ (c - x1 - 1 / 2) * |y| ^ (2 * x1 - c)) *
    Real.exp (-(Real.pi * |y| / 2)) * Real.exp (stripDelta x1 |y|) = (Real.sqrt (2 * Real.pi) *
    |y| ^ (c - x1 - 1 / 2) * Real.exp (-(Real.pi * |y| / 2))) * |y| ^ (2 * x1 - c) *
    Real.exp (stripDelta x1 |y|) by ring]
  have e1 : Real.exp (stripDelta x1 |y|) ≤ Real.exp D := Real.exp_le_exp.mpr (le_trans (le_abs_self _) d1)
  have e2 : Real.exp (-D) ≤ Real.exp (stripDelta (c - x1) |y|) :=
    Real.exp_le_exp.mpr (by linarith [(abs_le.mp d2).1])
  have e3 : Real.exp D = Real.exp (2 * D) * Real.exp (-D) := by rw [← Real.exp_add]; congr 1; ring
  have hpw : 0 < |y| ^ (2 * x1 - c) := Real.rpow_pos_of_pos hay _
  set A := Real.sqrt (2 * Real.pi) * |y| ^ (c - x1 - 1 / 2) * Real.exp (-(Real.pi * |y| / 2)) with hA
  have hA0 : 0 < A := by positivity
  calc A * |y| ^ (2 * x1 - c) * Real.exp (stripDelta x1 |y|)
      ≤ A * |y| ^ (2 * x1 - c) * Real.exp D := by gcongr
    _ = Real.exp (2 * D) * |y| ^ (2 * x1 - c) * (A * Real.exp (-D)) := by rw [e3]; ring
    _ ≤ Real.exp (2 * D) * |y| ^ (2 * x1 - c) * (A * Real.exp (stripDelta (c - x1) |y|)) := by
        gcongr
    _ = _ := by ring

/-- Left-edge decay: `|mellinRaw f (x₁ + iy)| ≤ C (1 + |y|)^{-(c - 2x₁)}`. -/
theorem exists_norm_mellinRaw_left {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ}
    (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1) {x1 : ℝ} (hx1 : 0 < x1)
    (hx1c : 2 * x1 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ,
      ‖mellinRaw f ((x1 : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C * (1 + |y|) ^ (-(c - 2 * x1)) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨J, hJ0, hJ⟩ := exists_norm_mellinRaw_le hc0 hf hx1 (by linarith)
  set a : ℝ := c - 2 * x1 with ha
  have ha0 : 0 < a := by linarith
  set P : ℝ := (2 * Real.pi) ^ (c - x1) / (2 * Real.pi) ^ x1 with hP
  have hP0 : 0 ≤ P := by positivity
  set R : ℝ := Real.exp (2 * ((c + 1 / 2) * c ^ 2 / 2 + c ^ 3 / 3 + 2)) with hR
  -- pointwise reflection bound
  have key : ∀ y : ℝ, ‖mellinRaw f ((x1 : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      P * J * (‖Complex.Gamma ((x1 : ℂ) + (y : ℂ) * Complex.I)‖ /
        ‖Complex.Gamma (((c - x1 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I)‖) := by
    intro y
    set z : ℂ := (x1 : ℂ) + (y : ℂ) * Complex.I with hz
    have hzre : z.re = x1 := by simp [hz]
    have hz0 : 0 < z.re := by rw [hzre]; exact hx1
    have hzc : z.re < c := by rw [hzre]; linarith
    set z' : ℂ := ((c - x1 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I with hz'
    have hz'eq : (c : ℂ) - z = z' := by rw [hz, hz']; push_cast; ring
    have hz're : z'.re = c - x1 := by simp [hz']
    have hz'0 : 0 < z'.re := by rw [hz're]; linarith
    have hGz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz0
    have hGz' : Complex.Gamma z' ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz'0
    have hpz : (((2 * Real.pi : ℝ) : ℂ)) ^ z ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))
    have hraw : mellinRaw f z = mellinStrip f z * (Complex.Gamma z / ((2 * Real.pi : ℝ) : ℂ) ^ z) := by
      unfold mellinStrip; field_simp
    have hnormM : ‖mellinStrip f z‖ = ‖mellinStrip f z'‖ := by
      have h1 := mellinStrip_reflection hc hf (z := z) hz0 hzc
      have hε1 : ‖(ε : ℂ)‖ = 1 := by rcases hε with h | h <;> simp [h]
      rw [hz'eq] at h1
      rw [h1, norm_mul, hε1, one_mul]
    have hM' : ‖mellinStrip f z'‖ ≤ (2 * Real.pi) ^ (c - x1) * J / ‖Complex.Gamma z'‖ := by
      unfold mellinStrip
      rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), hz're]
      have := hJ z' (by rw [hz're]; linarith) (by rw [hz're]; linarith)
      have hg : 0 < ‖Complex.Gamma z'‖ := norm_pos_iff.mpr hGz'
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hg]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    rw [hraw, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), hzre, hnormM]
    have hgp : 0 < ‖Complex.Gamma z'‖ := norm_pos_iff.mpr hGz'
    have hpp : 0 < (2 * Real.pi) ^ x1 := by positivity
    calc ‖mellinStrip f z'‖ * (‖Complex.Gamma z‖ / (2 * Real.pi) ^ x1)
        ≤ ((2 * Real.pi) ^ (c - x1) * J / ‖Complex.Gamma z'‖) *
          (‖Complex.Gamma z‖ / (2 * Real.pi) ^ x1) := by gcongr
      _ = P * J * (‖Complex.Gamma z‖ / ‖Complex.Gamma z'‖) := by
          rw [hP]; field_simp
  refine ⟨max (P * J * R * 2 ^ a) (J * 2 ^ a), by positivity, fun y => ?_⟩
  have hpos : 0 < (1 + |y|) ^ (-a) := Real.rpow_pos_of_pos (by positivity) _
  rcases le_or_gt 1 |y| with hy | hy
  · have hrat := norm_Gamma_ratio_le hx1 hx1c hy
    have hk := key y
    have hy2 : |y| ^ (-a) ≤ 2 ^ a * (1 + |y|) ^ (-a) := by
      have hay : 0 < |y| := by linarith
      have : (1 + |y|) ≤ 2 * |y| := by linarith
      have h3 : (2 * |y|) ^ (-a) ≤ (1 + |y|) ^ (-a) := Real.rpow_le_rpow_of_nonpos (by positivity) this (by linarith)
      have h4 : (2 * |y|) ^ (-a) = 2 ^ (-a) * |y| ^ (-a) := Real.mul_rpow (by norm_num) hay.le
      have h5 : (2 : ℝ) ^ (-a) * 2 ^ a = 1 := by rw [← Real.rpow_add (by norm_num)]; simp
      have h6 : 0 < (2 : ℝ) ^ a := by positivity
      nlinarith [h3, h4, h5, h6, Real.rpow_nonneg hay.le (-a)]
    have hpw : |y| ^ (2 * x1 - c) = |y| ^ (-a) := by congr 1; rw [ha]; ring
    rw [hpw] at hrat
    calc ‖mellinRaw f ((x1 : ℂ) + (y : ℂ) * Complex.I)‖ ≤ P * J * (R * |y| ^ (-a)) :=
          hk.trans (mul_le_mul_of_nonneg_left hrat (by positivity))
      _ ≤ P * J * (R * (2 ^ a * (1 + |y|) ^ (-a))) := by gcongr
      _ = (P * J * R * 2 ^ a) * (1 + |y|) ^ (-a) := by ring
      _ ≤ max (P * J * R * 2 ^ a) (J * 2 ^ a) * (1 + |y|) ^ (-a) := by gcongr; exact le_max_left _ _
  · have hJy := hJ ((x1 : ℂ) + (y : ℂ) * Complex.I) (by simp) (by simp; linarith)
    have h2 : (1 + |y|) ^ (-a) ≥ (2 : ℝ) ^ (-a) := by
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [abs_nonneg y]) (by linarith)
    have h5 : (2 : ℝ) ^ (-a) * 2 ^ a = 1 := by rw [← Real.rpow_add (by norm_num)]; simp
    have h6 : 0 < (2 : ℝ) ^ a := by positivity
    calc ‖mellinRaw f ((x1 : ℂ) + (y : ℂ) * Complex.I)‖ ≤ J := hJy
      _ = (J * 2 ^ a) * 2 ^ (-a) := by rw [mul_assoc, mul_comm ((2:ℝ)^a), h5, mul_one]
      _ ≤ (J * 2 ^ a) * (1 + |y|) ^ (-a) := by gcongr
      _ ≤ max (P * J * R * 2 ^ a) (J * 2 ^ a) * (1 + |y|) ^ (-a) := by gcongr; exact le_max_right _ _

/-- info: 'FormalResearch.SignUncertainty.exists_norm_mellinRaw_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_norm_mellinRaw_le

/-- info: 'FormalResearch.SignUncertainty.exists_norm_mellinRaw_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_norm_mellinRaw_left

end FormalResearch.SignUncertainty
