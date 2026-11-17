module

public import FormalResearch.Special.ComplexStirlingLine

/-!
# `|Γ(x + iy)|` in vertical strips, with explicit remainder

For `x > 0` and `y > 0` (and by `Γ(z̄) = conj Γ(z)` for `y < 0` with `|y|`):

`|Γ(x+iy)| = √(2π) · y^{x-1/2} · e^{-πy/2} · e^{δ}`, `|δ| ≤ K(x)/y² + 2/y`, where
`K(x) = |x-1/2| x²/2 + x³/3`  (`norm_Gamma_strip`).

In particular on `0 < x ≤ b`, `y ≥ 1`: `|δ| ≤ (K_b + 2)/y` with `K_b = (b+1/2) b²/2 + b³/3`, and for
`y ≥ K_b + 2`
`| |Γ(x+iy)| / (√(2π) y^{x-1/2} e^{-πy/2}) - 1 | ≤ 2 (K_b+2)/y`
(`norm_Gamma_strip_ratio`), i.e. `|Γ(x+iy)| = √(2π) |y|^{x-1/2} e^{-π|y|/2} (1 + O(1/|y|))`
uniformly for `x` in compact subsets of `(0,∞)`, with the explicit constants above.

Proof: `|Γ z| = exp(Re binetLogGamma z)`, `Re[(z-1/2) log z] = (x-1/2) log|z| - y arg z`,
`arg z = π/2 - arctan(x/y)`, `|z|² = y²(1 + x²/y²)`, `arctan u ≥ u - u³/3`, and
`|Re binetB z| ≤ 2/|z| ≤ 2/y`.

Numerics (mpmath, 30 digits, `x ∈ {0.05,0.1,0.5,1,2,3}`, `y ∈ {1,2,5,20,100,1000}`): the inequality
`|δ| ≤ K(x)/y² + 2/y` holds in all cases, with `max y|δ| ≈ 1.15` (the constants are crude, not sharp).

Not formalised: sharper constants, the corresponding statement for `arg Γ(x+iy)`, `x ≤ 0`.
-/

@[expose] public section

namespace FormalResearch.Special.ComplexStirling

open MeasureTheory Set Filter Topology Complex

/-- `arctan u ≥ u - u³/3` for `u ≥ 0`. -/
lemma arctan_ge_sub_cube {u : ℝ} (hu : 0 ≤ u) : u - u ^ 3 / 3 ≤ Real.arctan u := by
  have hd : ∀ v : ℝ, HasDerivAt (fun v => Real.arctan v - v + v ^ 3 / 3) (v ^ 4 / (1 + v ^ 2)) v := by
    intro v
    have h := (((Real.hasDerivAt_arctan v).sub (hasDerivAt_id v)).add
      ((hasDerivAt_pow 3 v).div_const 3))
    refine h.congr_deriv ?_
    field_simp
    ring
  have hmono : MonotoneOn (fun v => Real.arctan v - v + v ^ 3 / 3) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [(hd x).deriv]; positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hu) hu
  simp at this
  linarith

/-- For `x, y > 0`: `arg (x + iy) = π/2 - arctan (x/y)`. -/
lemma arg_eq_pi_div_two_sub_arctan {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Complex.arg ((x : ℂ) + (y : ℂ) * I) = Real.pi / 2 - Real.arctan (x / y) := by
  set z : ℂ := (x : ℂ) + (y : ℂ) * I with hz
  have hre : z.re = x := by simp [hz]
  have him : z.im = y := by simp [hz]
  have htan := Complex.tan_arg z
  rw [hre, him] at htan
  have hb : |Complex.arg z| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (by rw [hre]; exact hx))
  rw [abs_lt] at hb
  have h1 : Complex.arg z = Real.arctan (y / x) := by
    rw [← htan, Real.arctan_tan hb.1 hb.2]
  have h2 := Real.arctan_inv_of_pos (div_pos hy hx)
  rw [inv_div] at h2
  rw [h1]; linarith

/-- The explicit constant `K(x) = |x - 1/2| x²/2 + x³/3`. -/
noncomputable def stripConst (x : ℝ) : ℝ := |x - 1 / 2| * x ^ 2 / 2 + x ^ 3 / 3

/-- The remainder in the logarithm of the modulus. -/
noncomputable def stripDelta (x y : ℝ) : ℝ :=
  (x - 1 / 2) * (Real.log (1 + (x / y) ^ 2) / 2) + (y * Real.arctan (x / y) - x) +
    (binetB ((x : ℂ) + (y : ℂ) * I)).re

lemma norm_strip_ge {x y : ℝ} (_hx : 0 < x) (hy : 0 < y) :
    y ≤ ‖(x : ℂ) + (y : ℂ) * I‖ := by
  have := Complex.abs_im_le_norm ((x : ℂ) + (y : ℂ) * I)
  simpa [abs_of_pos hy] using this

lemma log_norm_strip {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log ‖(x : ℂ) + (y : ℂ) * I‖ = Real.log y + Real.log (1 + (x / y) ^ 2) / 2 := by
  have hn : 0 < ‖(x : ℂ) + (y : ℂ) * I‖ := lt_of_lt_of_le hy (norm_strip_ge hx hy)
  have hsq : ‖(x : ℂ) + (y : ℂ) * I‖ ^ 2 = y ^ 2 * (1 + (x / y) ^ 2) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    field_simp
    ring
  have h1 : Real.log (‖(x : ℂ) + (y : ℂ) * I‖ ^ 2) = 2 * Real.log ‖(x : ℂ) + (y : ℂ) * I‖ := by
    rw [Real.log_pow]; norm_num
  rw [hsq, Real.log_mul (by positivity) (by positivity), Real.log_pow] at h1
  push_cast at h1
  linarith

lemma re_binetLogGamma_strip {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (binetLogGamma ((x : ℂ) + (y : ℂ) * I)).re =
      Real.log (2 * Real.pi) / 2 + (x - 1 / 2) * Real.log y - Real.pi * y / 2 + stripDelta x y := by
  set z : ℂ := (x : ℂ) + (y : ℂ) * I with hz
  have hre : z.re = x := by simp [hz]
  have him : z.im = y := by simp [hz]
  have h1 : (z - 1 / 2).re = x - 1 / 2 := by simp [hre]
  have h2 : (z - 1 / 2).im = y := by simp [him]
  have key : binetLogGamma z = (z - 1 / 2) * Complex.log z - z +
      ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) + binetB z := rfl
  rw [key, Complex.add_re, Complex.add_re, Complex.sub_re, Complex.mul_re, h1, h2, Complex.log_re,
    Complex.log_im, Complex.ofReal_re, hre, log_norm_strip hx hy,
    arg_eq_pi_div_two_sub_arctan hx hy]
  unfold stripDelta
  ring

lemma abs_stripDelta_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |stripDelta x y| ≤ stripConst x / y ^ 2 + 2 / y := by
  have hu : 0 ≤ x / y := by positivity
  have hL0 : 0 ≤ Real.log (1 + (x / y) ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg (x / y)])
  have hL1 : Real.log (1 + (x / y) ^ 2) ≤ (x / y) ^ 2 := by
    have := Real.log_le_sub_one_of_pos (x := 1 + (x / y) ^ 2) (by positivity)
    linarith
  have ht1 : |(x - 1 / 2) * (Real.log (1 + (x / y) ^ 2) / 2)| ≤ |x - 1 / 2| * x ^ 2 / 2 / y ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.log (1 + (x / y) ^ 2) / 2)]
    have : |x - 1 / 2| * (Real.log (1 + (x / y) ^ 2) / 2) ≤ |x - 1 / 2| * ((x / y) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    refine this.trans (le_of_eq ?_)
    field_simp
  have hA1 : Real.arctan (x / y) ≤ x / y := Real.arctan_le_self hu
  have hA2 := arctan_ge_sub_cube hu
  have ht2 : |y * Real.arctan (x / y) - x| ≤ x ^ 3 / 3 / y ^ 2 := by
    rw [abs_le]
    constructor
    · have : y * (x / y - (x / y) ^ 3 / 3) ≤ y * Real.arctan (x / y) :=
        mul_le_mul_of_nonneg_left hA2 hy.le
      have e : y * (x / y - (x / y) ^ 3 / 3) = x - x ^ 3 / 3 / y ^ 2 := by field_simp
      linarith
    · have : y * Real.arctan (x / y) ≤ y * (x / y) := mul_le_mul_of_nonneg_left hA1 hy.le
      have e : y * (x / y) = x := by field_simp
      have : 0 ≤ x ^ 3 / 3 / y ^ 2 := by positivity
      linarith
  have ht3 : |(binetB ((x : ℂ) + (y : ℂ) * I)).re| ≤ 2 / y := by
    refine (Complex.abs_re_le_norm _).trans ((norm_binetB_le_div (by simpa using hx)).trans ?_)
    exact div_le_div_of_nonneg_left (by norm_num) hy (norm_strip_ge hx hy)
  unfold stripDelta
  refine (abs_add_three _ _ _).trans ?_
  have e : stripConst x / y ^ 2 + 2 / y =
      |x - 1 / 2| * x ^ 2 / 2 / y ^ 2 + x ^ 3 / 3 / y ^ 2 + 2 / y := by
    unfold stripConst; ring
  rw [e]
  exact add_le_add (add_le_add ht1 ht2) ht3

/-- `|Γ(x+iy)| = √(2π) y^{x-1/2} e^{-πy/2} e^{δ}` with `|δ| ≤ K(x)/y² + 2/y`, `x, y > 0`. -/
theorem norm_Gamma_strip {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ‖Complex.Gamma ((x : ℂ) + (y : ℂ) * I)‖ =
      Real.sqrt (2 * Real.pi) * y ^ (x - 1 / 2) * Real.exp (-(Real.pi * y / 2)) *
        Real.exp (stripDelta x y) := by
  have hxr : 0 < ((x : ℂ) + (y : ℂ) * I).re := by simpa using hx
  rw [← exp_binetLogGamma hxr, Complex.norm_exp, re_binetLogGamma_strip hx hy]
  have h2pi : 0 < 2 * Real.pi := by positivity
  have e1 : Real.exp (Real.log (2 * Real.pi) / 2) = Real.sqrt (2 * Real.pi) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos h2pi]; ring_nf
  have e2 : Real.exp ((x - 1 / 2) * Real.log y) = y ^ (x - 1 / 2) := by
    rw [Real.rpow_def_of_pos hy]; ring_nf
  rw [show Real.log (2 * Real.pi) / 2 + (x - 1 / 2) * Real.log y - Real.pi * y / 2 +
      stripDelta x y = Real.log (2 * Real.pi) / 2 + (x - 1 / 2) * Real.log y +
      (-(Real.pi * y / 2)) + stripDelta x y by ring, Real.exp_add, Real.exp_add, Real.exp_add, e1, e2]

/-- The same for any real `y ≠ 0` (with `|y|`), by `Γ(z̄) = conj Γ(z)`. -/
theorem norm_Gamma_strip_abs {x y : ℝ} (hx : 0 < x) (hy : y ≠ 0) :
    ‖Complex.Gamma ((x : ℂ) + (y : ℂ) * I)‖ =
      Real.sqrt (2 * Real.pi) * |y| ^ (x - 1 / 2) * Real.exp (-(Real.pi * |y| / 2)) *
        Real.exp (stripDelta x |y|) := by
  rcases lt_or_gt_of_ne hy with h | h
  · have h' : 0 < -y := by linarith
    have hc : (x : ℂ) + (y : ℂ) * I = (starRingEnd ℂ) ((x : ℂ) + ((-y : ℝ) : ℂ) * I) := by
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    rw [hc, Complex.Gamma_conj, Complex.norm_conj, norm_Gamma_strip hx h', abs_of_neg h]
  · rw [norm_Gamma_strip hx h, abs_of_pos h]

/-- Uniform relative error on `0 < x ≤ b`: with `K_b = (b+1/2) b²/2 + b³/3`, for
`y ≥ max 1 (K_b + 2)`,
`| |Γ(x+iy)| / (√(2π) y^{x-1/2} e^{-πy/2}) - 1 | ≤ 2 (K_b + 2) / y`. -/
theorem norm_Gamma_strip_ratio {x y b : ℝ} (hx : 0 < x) (hxb : x ≤ b) (hy : 1 ≤ y)
    (hyK : (b + 1 / 2) * b ^ 2 / 2 + b ^ 3 / 3 + 2 ≤ y) :
    |‖Complex.Gamma ((x : ℂ) + (y : ℂ) * I)‖ /
        (Real.sqrt (2 * Real.pi) * y ^ (x - 1 / 2) * Real.exp (-(Real.pi * y / 2))) - 1| ≤
      2 * ((b + 1 / 2) * b ^ 2 / 2 + b ^ 3 / 3 + 2) / y := by
  have hy0 : 0 < y := by linarith
  set Kb : ℝ := (b + 1 / 2) * b ^ 2 / 2 + b ^ 3 / 3 with hKb
  have hden : 0 < Real.sqrt (2 * Real.pi) * y ^ (x - 1 / 2) * Real.exp (-(Real.pi * y / 2)) := by
    positivity
  rw [norm_Gamma_strip hx hy0, mul_div_cancel_left₀ _ hden.ne']
  have hK : stripConst x ≤ Kb := by
    unfold stripConst
    have h1 : |x - 1 / 2| ≤ b + 1 / 2 := by
      rw [abs_le]; constructor <;> linarith
    have h2 : x ^ 2 ≤ b ^ 2 := by nlinarith
    have h3 : x ^ 3 ≤ b ^ 3 := by nlinarith [sq_nonneg x, sq_nonneg b, sq_nonneg (x - b)]
    have : |x - 1 / 2| * x ^ 2 ≤ (b + 1 / 2) * b ^ 2 :=
      mul_le_mul h1 h2 (by positivity) (by linarith)
    linarith
  have hδ : |stripDelta x y| ≤ (Kb + 2) / y := by
    refine (abs_stripDelta_le hx hy0).trans ?_
    have h1 : stripConst x / y ^ 2 ≤ Kb / y := by
      rw [div_le_div_iff₀ (by positivity) hy0]
      have h0 : 0 ≤ stripConst x := by unfold stripConst; positivity
      have hKb0 : 0 ≤ Kb := h0.trans hK
      nlinarith [mul_le_mul_of_nonneg_right hK hy0.le,
        mul_nonneg (mul_nonneg hKb0 hy0.le) (sub_nonneg.2 hy)]
    have : (Kb + 2) / y = Kb / y + 2 / y := by ring
    linarith
  have hle1 : |stripDelta x y| ≤ 1 := by
    refine hδ.trans ?_
    rw [div_le_one hy0]; exact hyK
  have := Real.abs_exp_sub_one_le hle1
  refine this.trans ?_
  calc 2 * |stripDelta x y| ≤ 2 * ((Kb + 2) / y) := by linarith
    _ = 2 * (Kb + 2) / y := by ring

/-- info: 'FormalResearch.Special.ComplexStirling.norm_Gamma_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ComplexStirling.norm_Gamma_strip

/-- info: 'FormalResearch.Special.ComplexStirling.norm_Gamma_strip_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ComplexStirling.norm_Gamma_strip_abs

/-- info: 'FormalResearch.Special.ComplexStirling.norm_Gamma_strip_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ComplexStirling.norm_Gamma_strip_ratio

end FormalResearch.Special.ComplexStirling
