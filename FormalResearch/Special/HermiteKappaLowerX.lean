module

public import FormalResearch.Special.HermiteKappaEnvelope
public import FormalResearch.Special.HermiteKappaOde

/-!
# Lower bound for the bulk amplitude of a Weber-type solution (the mass is `1/2` on the half line)

For `f` with `WeberData (q⁶)`, `q ≥ 20`, whose mass `V(x) = ∫_0^x f²` tends to `1/2` (parity + `∫ f² = 1`),
the WKB amplitude `T = w f² + f'²/w` satisfies `T ≥ 9/50` on the whole bulk `[0, x_b]` (`weber_T_lower`; numerically `T ≈ 2/π ≈ 0.64`).

Proof: `T ≥ 0.99 A` with `A = max T` (`weber_bulk_A`); the tail mass `∫_{x_b}^∞ f² ≤ E(x_b)/(2x_b) ≤ 50/q²` since
`E(x) = f'² + (q⁶ - x²) f² = ∫_x^∞ 2t f²` (monotone `G = E + 2x_b V`, no improper integral), so `V(x_b) ≥ 1/2 - 50/q²`; and
`V(x_b) ≤ A arcsin(x_b/q³) ≤ 1.6 A`.  Hence `A ≥ 0.23`.

`hermite_V_tendsto`: the Hermite instance (`∫_0^∞ φ_n² = 1/2`).  **Claim class: proved.**
-/

@[expose] public section

open Real Filter Topology MeasureTheory

namespace FormalResearch.Special

section abstract

variable {q : ℝ} {f g V : ℝ → ℝ}

/-- Tail mass: `V(b) - V(x_b) ≤ 50/q²` for all `b ≥ x_b`. -/
lemma tail_mass (hq : 4 ≤ q) (h : WeberData (q ^ 6) f g V) {b : ℝ} (hb : bxb q ≤ b) :
    V b - V (bxb q) ≤ 50 / q ^ 2 := by
  have hq0 : 0 < q := by linarith
  obtain ⟨-, hE0⟩ := xb_data hq h
  have hxb0 := bxb_nonneg q
  have hxbq := bxb_ge hq
  set xb := bxb q with hxb
  set G : ℝ → ℝ := fun y => WeberData.E (q ^ 6) f g y + 2 * xb * V y with hG
  have hanti : AntitoneOn G (Set.Ici xb) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici xb) ?_ ?_ ?_
    · intro y _
      exact ((h.hasDerivAt_E y).add ((h.hV y).const_mul (2 * xb))).continuousAt.continuousWithinAt
    · intro y _
      exact ((h.hasDerivAt_E y).add ((h.hV y).const_mul (2 * xb))).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy' : xb < y := hy
      have hdG : HasDerivAt G (-2 * y * f y ^ 2 + 2 * xb * f y ^ 2) y := by
        have := (h.hasDerivAt_E y).add ((h.hV y).const_mul (2 * xb))
        exact this
      rw [hdG.deriv]
      nlinarith [sq_nonneg (f y)]
  have h1 := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hb) hb
  have hEb := h.E_nonneg (hxb0.trans hb)
  simp only [hG] at h1
  have h2 : 2 * xb * (V b - V xb) ≤ 50 * q := by nlinarith
  have h3 : q ^ 3 ≤ 2 * xb := by linarith
  rw [div_eq_mul_inv]
  have hq3 : 0 < q ^ 3 := by positivity
  have : V b - V xb ≤ 50 * q / (2 * xb) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  calc V b - V xb ≤ 50 * q / (2 * xb) := this
    _ ≤ 50 * q / q ^ 3 := div_le_div_of_nonneg_left (by positivity) hq3 h3
    _ = 50 * (q ^ 2)⁻¹ := by field_simp

/-- Upper bound for the mass of the bulk: `V(x_b) ≤ A arcsin(x_b/q³)` when `f² ≤ A/w` on the bulk. -/
lemma bulk_mass_le (hq : 4 ≤ q) (h : WeberData (q ^ 6) f g V) {A : ℝ}
    (hA : ∀ y ∈ Set.Icc 0 (bxb q), f y ^ 2 ≤ A / bw q y) :
    V (bxb q) ≤ A * Real.arcsin (bxb q / q ^ 3) := by
  have hq0 : 0 < q := by linarith
  have hxb0 := bxb_nonneg q
  have hdF : ∀ y ∈ Set.Icc (0 : ℝ) (bxb q), HasDerivAt (fun y => A * Real.arcsin (y / q ^ 3) - V y)
      (A / bw q y - f y ^ 2) y := by
    intro y hy
    obtain ⟨hy0, hyq, h10, hwq, hw2⟩ := bulk_point hq hy
    have hwp : 0 < bw q y := by linarith
    have hne1 : y / q ^ 3 ≠ -1 := by
      have : 0 ≤ y / q ^ 3 := by positivity
      linarith
    have hne2 : y / q ^ 3 ≠ 1 := by
      intro hc
      have : y = q ^ 3 := by field_simp at hc; exact hc
      have h4 := hw2
      rw [this] at h4
      have : (0 : ℝ) < bw q y ^ 2 := by positivity
      nlinarith
    have hin : HasDerivAt (fun y : ℝ => y / q ^ 3) (1 / q ^ 3) y := by
      simpa using (hasDerivAt_id y).div_const (q ^ 3)
    have h1 := (Real.hasDerivAt_arcsin hne1 hne2).comp y hin
    have h2 := (h1.const_mul A).sub (h.hV y)
    refine h2.congr_deriv ?_
    have hq3 : 0 < q ^ 3 := by positivity
    have e : √(1 - (y / q ^ 3) ^ 2) = bw q y / q ^ 3 := by
      have : 1 - (y / q ^ 3) ^ 2 = (bw q y / q ^ 3) ^ 2 := by
        field_simp; nlinarith [hw2]
      rw [this]; exact Real.sqrt_sq (by positivity)
    simp only [e]
    field_simp
  have hmono := mono_of_hd (F := fun y => A * Real.arcsin (y / q ^ 3) - V y)
    (F' := fun y => A / bw q y - f y ^ 2) hxb0 hdF (fun y hy => by
      have := hA y hy
      linarith)
  simp only [zero_div, Real.arcsin_zero, mul_zero, h.V0, sub_zero] at hmono
  linarith

/-- **Lower bound for the bulk amplitude**: `T ≥ 9/50` on `[0, x_b]`, for `q ≥ 20` and mass `V → 1/2`. -/
theorem weber_T_lower (hq : 20 ≤ q) (h : WeberData (q ^ 6) f g V) (hV : Tendsto V atTop (𝓝 (1 / 2))) :
    ∀ y ∈ Set.Icc 0 (bxb q), 9 / 50 ≤ invT (bw q) f g y := by
  have hq4 : 4 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  obtain ⟨A, hA0, hA5, hA⟩ := weber_bulk_A hq4 h
  have hxbI : bxb q ∈ Set.Icc (0 : ℝ) (bxb q) := ⟨bxb_nonneg q, le_refl _⟩
  -- the tail
  have htail : 1 / 2 - 50 / q ^ 2 ≤ V (bxb q) := by
    have hle : (1 / 2 : ℝ) ≤ V (bxb q) + 50 / q ^ 2 := by
      refine le_of_tendsto hV ?_
      filter_upwards [eventually_ge_atTop (bxb q)] with b hb
      have := tail_mass hq4 h hb
      linarith
    linarith
  -- the bulk
  have hf2 : ∀ y ∈ Set.Icc (0 : ℝ) (bxb q), f y ^ 2 ≤ A / bw q y := by
    intro y hy
    have hwp := bw_pos hq4 hy
    exact (f_sq_le_T hwp).trans (div_le_div_of_nonneg_right (hA y hy).2 hwp.le)
  have hup := bulk_mass_le hq4 h hf2
  have hasin : Real.arcsin (bxb q / q ^ 3) ≤ 8 / 5 := by
    have := Real.arcsin_le_pi_div_two (bxb q / q ^ 3)
    have := Real.pi_lt_d2
    linarith
  have hq2 : 400 ≤ q ^ 2 := by nlinarith
  have h50 : 50 / q ^ 2 ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hAlow : 3 / 16 ≤ A := by
    have := mul_le_mul_of_nonneg_left hasin hA0
    nlinarith
  intro y hy
  have := (hA y hy).1
  linarith

/-- info: 'FormalResearch.Special.weber_T_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.weber_T_lower

end abstract

/-- `∫_0^∞ φ_n² = 1/2`: the mass function of `φ_n` tends to `1/2`. -/
theorem hermite_V_tendsto (n : ℕ) :
    Tendsto (fun x => ∫ t in (0 : ℝ)..x, hermitePhi n t ^ 2) atTop (𝓝 (1 / 2)) := by
  have hint : Integrable (fun t => hermitePhi n t ^ 2) := by
    simpa [sq] using integrable_hermitePhi_mul n n
  have hT := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hint.integrableOn tendsto_id
  have hval : ∫ t in Set.Ioi (0 : ℝ), hermitePhi n t ^ 2 = 1 / 2 := by
    have h1 := integral_comp_abs (f := fun t => hermitePhi n t ^ 2)
    have e : (fun x : ℝ => hermitePhi n |x| ^ 2) = fun x => hermitePhi n x ^ 2 := by
      funext x
      rcases abs_choice x with h | h
      · rw [h]
      · rw [h, ← sq_abs, abs_hermitePhi_neg, sq_abs]
    rw [e, integral_hermitePhi_sq] at h1
    linarith
  rw [hval] at hT
  simpa using hT

end FormalResearch.Special
