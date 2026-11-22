module

public import FormalResearch.ModularBootstrap.Bessel.VCorollaries

/-!
# Lemma B (d), pure Bessel part: `K_a ≤ C c'² V`

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Lemma B (`vlo:Bessel`), part (d), proof
paragraph "For (d), take `a - 2 ≥ c'/24`": the pointwise comparison of the kernel `K_a` with
`V = K_a - 2K_{a-1} + K_{a-2}` that feeds `∫|g| K_a ≤ C c'² M[g]` (the integral bound itself needs the
test class and is not part of this file).

* `besselK_le_of_le_inv`: `K_a(t) ≤ I₀(4π/√12)` for `t ≤ 1/c'`, `a = c'/12`;
* `besselK_le_mul_besselV`: `K_a(t) ≤ C c'² V(t)` for `t ≥ 1/c'`, `c' ≥ c₀`, with the explicit
  `c₀ = 1000`, `C = e^{92}` (not optimised; the paper's `C` is unspecified).  The three paper steps:
  `V ≥ 4π²t/(a-2) · I₂(z₂)` (`besselV_ge_besselI2`), `I₂ ≥ I₀/(8e⁴)` for `z ≥ 1`
  (`besselI0_le_mul_besselI2`, from `I₂ ≥ z²/8`, `I₀ ≤ e^z` and `I₂ ≥ I₀/2` for `z ≥ 4`),
  `(log I₀)' ≤ 1` (`besselI0_le_mul_exp`) on `1/c' ≤ t ≤ c'`, and the `I₀` asymptotic
  (`besselV_asymptotic`) for `t ≥ c'`.
-/

@[expose] public section

open Real

namespace FormalResearch.ModularBootstrap.Bessel

/-- `I₀(z) ≤ 8 e⁴ I₂(z)` for `z ≥ 1`. -/
lemma besselI0_le_mul_besselI2 {z : ℝ} (hz : 1 ≤ z) : besselI0 z ≤ 8 * exp 4 * besselI 2 z := by
  have hz0 : 0 ≤ z := by linarith
  have hI2 := besselI2_ge z
  have he4 : 0 < exp 4 := exp_pos 4
  have he41 : 1 ≤ exp 4 := one_le_exp (by norm_num)
  rcases le_total z 4 with h | h
  · have h1 : besselI0 z ≤ exp z := besselI0_le_exp hz0
    have h2 : exp z ≤ exp 4 := exp_le_exp.mpr h
    have h3 : (1 : ℝ) / 8 ≤ besselI 2 z := by nlinarith
    nlinarith
  · have := besselI2_ge_half h
    have h0 : 0 ≤ besselI 2 z := besselI_nonneg 2 hz0
    nlinarith

/-- `K_a(t) ≤ I₀(4π/√12)` for `t ≤ 1/c'`, where `a = c'/12`. -/
theorem besselK_le_of_le_inv {c' t : ℝ} (hc : 0 < c') (ht' : t ≤ 1 / c') :
    besselK (c' / 12) t ≤ besselI0 (4 * π / √12) := by
  unfold besselK
  apply besselI0_mono (by positivity)
  have h : c' / 12 * t ≤ 1 / 12 := by
    have : c' * t ≤ 1 := by rwa [le_div_iff₀ hc, mul_comm] at ht'
    linarith
  have h2 : √(c' / 12 * t) ≤ √(1 / 12) := Real.sqrt_le_sqrt h
  have h3 : √(1 / 12 : ℝ) = 1 / √12 := by rw [Real.sqrt_div (by norm_num), Real.sqrt_one]
  rw [h3] at h2
  have : 4 * π / √12 = 4 * π * (1 / √12) := by ring
  rw [this]
  gcongr

/-- Middle range `1/c' ≤ t ≤ c'`. -/
lemma besselK_le_mul_besselV_mid {c' t : ℝ} (hc : 48 ≤ c') (ht1 : 1 / c' ≤ t) (ht2 : t ≤ c') :
    besselK (c' / 12) t ≤ exp 92 * c' ^ 2 * besselV (c' / 12) t := by
  have hc0 : 0 < c' := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  set a := c' / 12 with ha
  have ha4 : 4 ≤ a := by rw [ha]; linarith
  have ha2 : 0 < a - 2 := by linarith
  have ha2' : c' / 24 ≤ a - 2 := by rw [ha]; linarith
  set z2 := 4 * π * √((a - 2) * t) with hz2
  set z0 := 4 * π * √(a * t) with hz0
  -- z2 ≥ 1
  have hz2_ge : 1 ≤ z2 := by
    have h1 : 1 / 24 ≤ (a - 2) * t := by
      have : c' / 24 * (1 / c') ≤ (a - 2) * t := by gcongr
      calc (1 : ℝ) / 24 = c' / 24 * (1 / c') := by field_simp
        _ ≤ _ := this
    have h2 : √(1 / 24) ≤ √((a - 2) * t) := Real.sqrt_le_sqrt h1
    have h3 : (1 : ℝ) / 5 ≤ √(1 / 24) := by
      apply Real.le_sqrt_of_sq_le; norm_num
    rw [hz2]
    have := Real.pi_gt_three
    nlinarith
  have hz2_le : z2 ≤ z0 := by
    rw [hz2, hz0]
    gcongr
    linarith
  -- difference bound
  have hdiff : z0 - z2 ≤ 88 := by
    set p := √a with hp
    set r := √(a - 2) with hr
    set s := √t with hs
    have hp0 : 0 < p := Real.sqrt_pos.mpr (by linarith)
    have hr0 : 0 < r := Real.sqrt_pos.mpr ha2
    have hs0 : 0 < s := Real.sqrt_pos.mpr ht0
    have hp2 : p ^ 2 = a := Real.sq_sqrt (by linarith)
    have hr2 : r ^ 2 = a - 2 := Real.sq_sqrt ha2.le
    have hs2 : s ^ 2 = t := Real.sq_sqrt ht0.le
    have hrp : r ≤ p := Real.sqrt_le_sqrt (by linarith)
    have hz0' : z0 = 4 * π * (p * s) := by rw [hz0, Real.sqrt_mul (by linarith)]
    have hz2' : z2 = 4 * π * (r * s) := by rw [hz2, Real.sqrt_mul ha2.le]
    have h12 : s ≤ 3.47 * p := by
      have : s ^ 2 ≤ (3.47 * p) ^ 2 := by
        rw [hs2, mul_pow, hp2]
        have : t ≤ c' := ht2
        rw [ha] at *
        nlinarith
      exact abs_le_of_sq_le_sq' this (by positivity) |>.2
    have hpr : (p - r) * p ≤ 2 := by
      have : (p - r) * (p + r) = 2 := by nlinarith
      nlinarith
    have : (p - r) * s ≤ 2 * 3.47 := by
      have h1 : (p - r) * s * p ≤ 2 * 3.47 * p := by
        nlinarith [mul_le_mul_of_nonneg_left h12 (sub_nonneg.2 hrp)]
      exact le_of_mul_le_mul_right h1 hp0
    have hπ := Real.pi_lt_d2
    rw [hz0', hz2']
    nlinarith [mul_nonneg (sub_nonneg.2 hrp) hs0.le, pi_pos]
  -- the chain
  have hK : besselK a t = besselI0 z0 := rfl
  have h1 : besselI0 z0 ≤ exp (z0 - z2) * besselI0 z2 := besselI0_le_mul_exp hz2_le
  have h2 : exp (z0 - z2) ≤ exp 88 := exp_le_exp.mpr hdiff
  have h3 : besselI0 z2 ≤ 8 * exp 4 * besselI 2 z2 := besselI0_le_mul_besselI2 hz2_ge
  have hV : 4 * π ^ 2 * t / (a - 2) * besselI 2 z2 ≤ besselV a t := by
    have := besselV_ge_besselI2 (a := a) (t := t) (by linarith) ht0.le
    exact this
  have hI2pos : 0 ≤ besselI 2 z2 := besselI_nonneg 2 (by linarith)
  have hI0pos : 0 ≤ besselI0 z2 := besselI_nonneg 0 (by linarith)
  have hcoef : (a - 2) / (4 * π ^ 2 * t) ≤ c' ^ 2 / 400 := by
    have hpi2 : 9 < π ^ 2 := by nlinarith [Real.pi_gt_three]
    have h1 : 1 ≤ t * c' := by rwa [div_le_iff₀ hc0] at ht1
    rw [div_le_iff₀ (by positivity)]
    have h2 : c' ^ 2 / 400 * (4 * π ^ 2 * t) = (c' * π ^ 2 / 100) * (t * c') := by ring
    rw [h2]
    have h3 : (c' * π ^ 2 / 100) * 1 ≤ (c' * π ^ 2 / 100) * (t * c') :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have : c' * 9 ≤ c' * π ^ 2 := by gcongr
    rw [ha]; nlinarith
  have hI2 : besselI 2 z2 ≤ besselV a t * ((a - 2) / (4 * π ^ 2 * t)) := by
    have hpos : 0 < 4 * π ^ 2 * t / (a - 2) := by positivity
    have := hV
    rw [← le_div_iff₀' hpos] at this
    calc besselI 2 z2 ≤ besselV a t / (4 * π ^ 2 * t / (a - 2)) := this
      _ = besselV a t * ((a - 2) / (4 * π ^ 2 * t)) := by field_simp
  have hV0 : 0 ≤ besselV a t := le_trans (by positivity) hV
  rw [hK]
  calc besselI0 z0 ≤ exp (z0 - z2) * besselI0 z2 := h1
    _ ≤ exp 88 * besselI0 z2 := by gcongr
    _ ≤ exp 88 * (8 * exp 4 * besselI 2 z2) := by gcongr
    _ ≤ exp 88 * (8 * exp 4 * (besselV a t * ((a - 2) / (4 * π ^ 2 * t)))) := by gcongr
    _ ≤ exp 88 * (8 * exp 4 * (besselV a t * (c' ^ 2 / 400))) := by gcongr
    _ = (exp 88 * exp 4) * (8 / 400) * c' ^ 2 * besselV a t := by ring
    _ ≤ exp 92 * c' ^ 2 * besselV a t := by
        have e : exp 88 * exp 4 = exp 92 := by rw [← exp_add]; norm_num
        rw [e]
        have : 0 ≤ exp 92 * c' ^ 2 * besselV a t := by positivity
        nlinarith

/-- Large range `t ≥ c'`. -/
lemma besselK_le_mul_besselV_large {c' t : ℝ} (hc : 1000 ≤ c') (ht : c' ≤ t) :
    besselK (c' / 12) t ≤ 7 * besselV (c' / 12) t := by
  have hc0 : 0 < c' := by linarith
  have ht0 : 0 < t := by linarith
  set x := √(3 * t / c') with hx
  have hx2 : x ^ 2 = 3 * t / c' := Real.sq_sqrt (by positivity)
  have hx1 : (1 : ℝ) ≤ x := by
    rw [hx]; apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hc0]; nlinarith
  have hx0 : 0 < x := by linarith
  have htx : c' * x ^ 2 / 3 = t := by rw [hx2]; field_simp
  have hasym := besselV_asymptotic (x₀ := 1) one_pos (c' := c') (x := x) (by norm_num; linarith) hx1
  rw [htx] at hasym
  set z0 := c' * besselL x with hz0
  have hz4 : 4 ≤ z0 := by
    rw [hz0]; unfold besselL
    have := Real.pi_gt_three
    nlinarith [mul_le_mul_of_nonneg_left hx1 hc0.le]
  have hz00 : 0 < z0 := by linarith
  have hA := besselAs_pos hz00
  have hKK : besselK (c' / 12) t = besselI0 z0 := by
    have := besselK_shift (c' := c') (x := x) (j := 0) hc0 hx0.le
    rw [htx] at this
    simpa using this
  have hu := besselI0_upper hz4
  set q := exp (-(4 * π * x)) with hq
  have hq0 : 0 < q := exp_pos _
  have hq1 : q ≤ 1 / 13 := by
    have h1 : (12 : ℝ) ≤ 4 * π * x := by nlinarith [Real.pi_gt_three]
    have h5 : 4 * π * x + 1 ≤ exp (4 * π * x) := Real.add_one_le_exp _
    have h6 : q * exp (4 * π * x) = 1 := by rw [hq, ← exp_add]; simp
    nlinarith [exp_pos (4 * π * x)]
  set B := besselV (c' / 12) t / besselAs z0 with hB
  have herr : (96 + 60 / (1 : ℝ)) / c' ≤ 1 / 5 := by
    rw [div_le_iff₀ hc0]; norm_num; linarith
  have hBlo : 1 / 2 ≤ B := by
    have := (abs_le.mp hasym).1
    have h1 : 1 / 2 ≤ (1 - q) ^ 2 - 1 / 5 := by nlinarith
    linarith
  have hV : besselV (c' / 12) t = B * besselAs z0 := by rw [hB]; field_simp
  rw [hKK]
  calc besselI0 z0 ≤ (1 + 10 / z0) * besselAs z0 := hu
    _ ≤ (7 / 2) * besselAs z0 := by
        have : 10 / z0 ≤ 10 / 4 := by gcongr
        gcongr; linarith
    _ ≤ 7 * (B * besselAs z0) := by nlinarith
    _ = 7 * besselV (c' / 12) t := by rw [hV]

/-- **Lemma B (d), pure Bessel part** (`vlo:Bessel`): the form needed by Lemma G.  For `c' ≥ 1000`
(`c₀ = 1000`) and `t ≥ 1/c'`, with `a = c'/12` (so `a - 2 ≥ c'/24`),
`K_a(t) ≤ e^{92} c'² V(t)`.  The constant `C = e^{92}` is explicit but not optimised (the paper's
`C` is unspecified).  The complementary range `t ≤ 1/c'` is `besselK_le_of_le_inv`. -/
theorem besselK_le_mul_besselV {c' t : ℝ} (hc : 1000 ≤ c') (ht : 1 / c' ≤ t) :
    besselK (c' / 12) t ≤ exp 92 * c' ^ 2 * besselV (c' / 12) t := by
  have hc0 : 0 < c' := by linarith
  rcases le_total t c' with h | h
  · exact besselK_le_mul_besselV_mid (by linarith) ht h
  · have h1 := besselK_le_mul_besselV_large hc h
    have ht0 : 0 ≤ t := by linarith
    have hV : 8 * π ^ 4 * t ^ 2 ≤ besselV (c' / 12) t := besselV_ge (by linarith) ht0
    have hV0 : 0 ≤ besselV (c' / 12) t := le_trans (by positivity) hV
    have he : (93 : ℝ) ≤ exp 92 := by
      have := Real.add_one_le_exp (92 : ℝ); linarith
    have hc2 : (1 : ℝ) ≤ c' ^ 2 := by nlinarith
    have : (7 : ℝ) ≤ exp 92 * c' ^ 2 := by nlinarith
    calc besselK (c' / 12) t ≤ 7 * besselV (c' / 12) t := h1
      _ ≤ exp 92 * c' ^ 2 * besselV (c' / 12) t := by gcongr

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselK_le_of_le_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselK_le_of_le_inv

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselK_le_mul_besselV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselK_le_mul_besselV

end FormalResearch.ModularBootstrap.Bessel
