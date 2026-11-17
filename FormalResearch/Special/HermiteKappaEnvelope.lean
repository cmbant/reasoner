module

public import FormalResearch.Special.HermiteKappaBulk

/-!
# The uniform envelope of a Weber-type solution

For `f` with `WeberData (q⁶)` (`q ≥ 4`), the three regions give, for all `x ≥ 0`,
`f(x)² √(|q⁶ - x²| + q²) ≤ C` (`weber_envelope`), `C = 3·10⁷` (explicit, not optimised):

* **bulk** `0 ≤ x ≤ x_b` (`q⁶ - x² ≥ 100 q²`): `f² ≤ T/w ≤ 5/√(q⁶ - x²)` (`weber_bulk_T`);
* **turning window** `x_b ≤ x ≤ s = q³`: the energy `E = f'² + (q⁶ - x²) f²` is nonincreasing, `E(x_b) = w T ≤ 50 q`, so
  `|f'| ≤ √(50 q)` on the window, whose length is `≤ 100/q`; hence `f² ≤ (10⁶ + 1)/q` (`window_bound`);
* **forbidden region** `x ≥ s`: `f² ≤ f(s)² exp(-(4/3)√(2s)(x - s)^{3/2})` (`WeberData.sq_exp_decay`), which beats the
  polynomial factor (`forbidden_bound`).

**Claim class: proved.**
-/

@[expose] public section

open Real

namespace FormalResearch.Special

section window

variable {q : ℝ} {f g V : ℝ → ℝ}

lemma bw_xb (hq : 4 ≤ q) : bw q (bxb q) = 10 * q := by
  have hq0 : 0 < q := by linarith
  unfold bw
  rw [bxb_sq hq]
  rw [show q ^ 6 - (q ^ 6 - 100 * q ^ 2) = (10 * q) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

/-- At the end of the bulk: `f² ≤ 1/(2q)` and `E ≤ 50 q`. -/
lemma xb_data (hq : 4 ≤ q) (h : WeberData (q ^ 6) f g V) :
    f (bxb q) ^ 2 ≤ 1 / (2 * q) ∧ WeberData.E (q ^ 6) f g (bxb q) ≤ 50 * q := by
  have hq0 : 0 < q := by linarith
  have hxbI : bxb q ∈ Set.Icc (0 : ℝ) (bxb q) := ⟨bxb_nonneg q, le_refl _⟩
  have hT := weber_bulk_T hq h (bxb q) hxbI
  have hw := bw_xb hq
  have hwp : (0 : ℝ) < bw q (bxb q) := by rw [hw]; positivity
  have h1 := f_sq_le_T (f := f (bxb q)) (g := g (bxb q)) hwp
  have e : invT (bw q) f g (bxb q) = bw q (bxb q) * f (bxb q) ^ 2 + g (bxb q) ^ 2 / bw q (bxb q) := rfl
  rw [← e] at h1
  refine ⟨?_, ?_⟩
  · rw [hw] at h1
    have : invT (bw q) f g (bxb q) / (10 * q) ≤ 5 / (10 * q) :=
      div_le_div_of_nonneg_right hT (by positivity)
    have e2 : (5 : ℝ) / (10 * q) = 1 / (2 * q) := by field_simp; norm_num
    rw [hw] at *
    linarith
  · have hE : WeberData.E (q ^ 6) f g (bxb q) = bw q (bxb q) * invT (bw q) f g (bxb q) := by
      have hw2 : bw q (bxb q) ^ 2 = q ^ 6 - bxb q ^ 2 := Real.sq_sqrt (by rw [bxb_sq hq]; nlinarith [pow_pos hq0 2, q4_ge hq])
      simp only [WeberData.E, invT]
      field_simp
      rw [← hw2]; ring
    rw [hE, hw]
    have : (0 : ℝ) ≤ 10 * q := by positivity
    nlinarith

/-- **Turning window**: `f² ≤ (10⁶ + 1)/q` on `[x_b, q³]`. -/
theorem window_bound (hq : 4 ≤ q) (h : WeberData (q ^ 6) f g V) {x : ℝ}
    (hx1 : bxb q ≤ x) (hx2 : x ≤ q ^ 3) : f x ^ 2 ≤ 1000001 / q := by
  have hq0 : 0 < q := by linarith
  obtain ⟨hf0, hE0⟩ := xb_data hq h
  have hxb0 := bxb_nonneg q
  -- derivative bound on the window
  have hg : ∀ y ∈ Set.Icc (bxb q) x, |g y| ≤ √(50 * q) := by
    intro y hy
    have h1 : WeberData.E (q ^ 6) f g y ≤ WeberData.E (q ^ 6) f g (bxb q) :=
      h.E_antitoneOn hxb0 (hxb0.trans hy.1) hy.1
    have hy3 : y ≤ q ^ 3 := hy.2.trans hx2
    have h2 : 0 ≤ (q ^ 6 - y ^ 2) * f y ^ 2 := by
      have : 0 ≤ q ^ 6 - y ^ 2 := by nlinarith [hxb0.trans hy.1, pow_pos hq0 3]
      positivity
    have h3 : g y ^ 2 ≤ 50 * q := by
      simp only [WeberData.E] at h1 hE0 ⊢
      nlinarith
    exact Real.abs_le_sqrt h3
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Set.Icc (bxb q) x) (C := √(50 * q))
    (fun y _ => (h.hf y).differentiableAt)
    (fun y hy => by rw [(h.hf y).deriv]; exact hg y hy)
    (convex_Icc _ _) (Set.left_mem_Icc.2 hx1) (Set.right_mem_Icc.2 hx1)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hx1)] at hmv
  have hlen : x - bxb q ≤ 100 / q := by
    have hsq := bxb_sq hq
    have : (q ^ 3 - bxb q) * (q ^ 3 + bxb q) = 100 * q ^ 2 := by nlinarith
    have h3 : x - bxb q ≤ q ^ 3 - bxb q := by linarith
    have h4 : q ^ 3 - bxb q ≤ 100 / q := by
      rw [le_div_iff₀ hq0]
      nlinarith [pow_pos hq0 3, pow_pos hq0 2]
    linarith
  have hB : 0 ≤ √(50 * q) := Real.sqrt_nonneg _
  have hmv2 : |f x - f (bxb q)| ≤ √(50 * q) * (100 / q) :=
    hmv.trans (mul_le_mul_of_nonneg_left hlen hB)
  have hsq : (f x - f (bxb q)) ^ 2 ≤ (√(50 * q) * (100 / q)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hmv2 2
  have hs50 : √(50 * q) ^ 2 = 50 * q := Real.sq_sqrt (by positivity)
  have e : (√(50 * q) * (100 / q)) ^ 2 = 500000 / q := by
    rw [mul_pow, hs50]; field_simp; ring
  have : f x ^ 2 ≤ 2 * f (bxb q) ^ 2 + 2 * (f x - f (bxb q)) ^ 2 := by
    nlinarith [sq_nonneg (f x - 2 * f (bxb q))]
  have e2 : 2 * (1 / (2 * q)) = 1 / q := by field_simp
  rw [e] at hsq
  have e3 : (1000001 : ℝ) / q = 1 / q + 2 * (500000 / q) := by ring
  rw [e3]
  nlinarith

lemma one_add_sq_le_exp_cube {z : ℝ} (hz : 0 ≤ z) : 1 + z ^ 2 ≤ 2 * Real.exp (z ^ 3) := by
  have h1 : z ^ 2 ≤ 1 + z ^ 3 := by
    rcases le_total z 1 with h | h
    · nlinarith [sq_nonneg z, pow_nonneg hz 3]
    · nlinarith [sq_nonneg z]
  have h2 := Real.add_one_le_exp (z ^ 3)
  nlinarith [pow_nonneg hz 3]

/-- **Forbidden region**: from `f(q³)² ≤ K/q`, `f² √(|q⁶ - x²| + q²) ≤ 2K` for `x ≥ q³`. -/
theorem forbidden_bound (hq : 1 ≤ q) (h : WeberData (q ^ 6) f g V) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : f (q ^ 3) ^ 2 ≤ K / q) {x : ℝ} (hx : q ^ 3 ≤ x) :
    f x ^ 2 * √(|q ^ 6 - x ^ 2| + q ^ 2) ≤ 2 * K := by
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < q ^ 3 := by positivity
  have hs : (q ^ 3) ^ 2 = q ^ 6 := by ring
  have hdec := h.sq_exp_decay hs0 hs hx
  set a : ℝ := √q with ha
  set b : ℝ := √(x - q ^ 3) with hb
  have ha0 : 0 < a := Real.sqrt_pos.2 hq0
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = q := Real.sq_sqrt hq0.le
  have hb2 : b ^ 2 = x - q ^ 3 := Real.sq_sqrt (sub_nonneg.2 hx)
  have ha1 : 1 ≤ a := by nlinarith
  set z : ℝ := a * b with hz
  have hz0 : 0 ≤ z := by positivity
  -- exponent
  have hs2 : √(2 * q ^ 3) = √2 * a ^ 3 := by
    rw [Real.sqrt_mul (by norm_num)]
    congr 1
    rw [show q ^ 3 = (a ^ 3) ^ 2 by rw [← ha2]; ring]
    exact Real.sqrt_sq (by positivity)
  have hexp : z ^ 3 ≤ (4 / 3) * √(2 * q ^ 3) * b ^ 3 := by
    rw [hs2, hz]
    have h2 : (1 : ℝ) ≤ √2 := by
      rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
    have : 0 ≤ (a * b) ^ 3 := by positivity
    nlinarith [mul_pow a b 3]
  have hdec' : f x ^ 2 * Real.exp (z ^ 3) ≤ f (q ^ 3) ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) (sq_nonneg _)) hdec
  have hfx : f x ^ 2 ≤ K / q * Real.exp (-(z ^ 3)) := by
    have h1 : f x ^ 2 ≤ f (q ^ 3) ^ 2 * Real.exp (-(z ^ 3)) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]; exact hdec'
    exact h1.trans (mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le)
  -- the polynomial factor
  have hd : |q ^ 6 - x ^ 2| + q ^ 2 ≤ (q * (1 + z ^ 2)) ^ 2 := by
    have hx2 : q ^ 6 ≤ x ^ 2 := by nlinarith [pow_pos hq0 3]
    rw [abs_of_nonpos (by linarith)]
    have hxe : x = q ^ 3 + b ^ 2 := by linarith
    have hzq : z ^ 2 = q * b ^ 2 := by rw [hz, mul_pow, ha2]
    have e : (q * (1 + z ^ 2)) ^ 2 = q ^ 2 + 2 * q ^ 2 * z ^ 2 + q ^ 2 * z ^ 4 := by ring
    rw [e, hzq, hxe]
    have : 1 ≤ q := hq
    have hb4 : 0 ≤ b ^ 4 := by positivity
    nlinarith [mul_nonneg hb4 (sub_nonneg.2 (show 1 ≤ q ^ 4 from one_le_pow₀ hq)),
      pow_pos hq0 2, mul_nonneg (pow_nonneg hq0.le 2) (sq_nonneg b)]
  have hsqrt : √(|q ^ 6 - x ^ 2| + q ^ 2) ≤ q * (1 + z ^ 2) := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, hd⟩
  have hmain : f x ^ 2 * √(|q ^ 6 - x ^ 2| + q ^ 2) ≤ K / q * Real.exp (-(z ^ 3)) * (q * (1 + z ^ 2)) :=
    mul_le_mul hfx hsqrt (Real.sqrt_nonneg _) (by positivity)
  have e : K / q * Real.exp (-(z ^ 3)) * (q * (1 + z ^ 2)) = K * ((1 + z ^ 2) * Real.exp (-(z ^ 3))) := by
    field_simp
  rw [e] at hmain
  have hz3 := one_add_sq_le_exp_cube hz0
  have h5 : (1 + z ^ 2) * Real.exp (-(z ^ 3)) ≤ 2 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    linarith
  have := mul_le_mul_of_nonneg_left h5 hK0
  linarith

/-- **Uniform envelope** for `q ≥ 4`: `f² √(|q⁶ - x²| + q²) ≤ 12·10⁶` for all `x ≥ 0`. -/
theorem weber_envelope (hq : 4 ≤ q) (h : WeberData (q ^ 6) f g V) {x : ℝ} (hx : 0 ≤ x) :
    f x ^ 2 * √(|q ^ 6 - x ^ 2| + q ^ 2) ≤ 12000000 := by
  have hq0 : 0 < q := by linarith
  have hxb0 := bxb_nonneg q
  have hxbq : bxb q ≤ q ^ 3 := by
    unfold bxb
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    nlinarith [pow_pos hq0 2]
  rcases le_total x (bxb q) with hx1 | hx1
  · -- bulk
    have hI : x ∈ Set.Icc (0 : ℝ) (bxb q) := ⟨hx, hx1⟩
    obtain ⟨-, -, h10, -, hw2⟩ := bulk_point hq hI
    have hwp := bw_pos hq hI
    have hT := weber_bulk_T hq h x hI
    have hf := f_sq_le_T (f := f x) (g := g x) hwp
    have e : invT (bw q) f g x = bw q x * f x ^ 2 + g x ^ 2 / bw q x := rfl
    rw [← e] at hf
    have h1 : f x ^ 2 ≤ 5 / bw q x := hf.trans (div_le_div_of_nonneg_right hT hwp.le)
    have hd : |q ^ 6 - x ^ 2| + q ^ 2 ≤ (11 / 10 * bw q x) ^ 2 := by
      rw [abs_of_nonneg (by nlinarith [hw2, sq_nonneg (bw q x)] : (0 : ℝ) ≤ q ^ 6 - x ^ 2)]
      nlinarith [sq_nonneg q]
    have hs : √(|q ^ 6 - x ^ 2| + q ^ 2) ≤ 11 / 10 * bw q x := Real.sqrt_le_iff.2 ⟨by positivity, hd⟩
    calc f x ^ 2 * √(|q ^ 6 - x ^ 2| + q ^ 2) ≤ 5 / bw q x * (11 / 10 * bw q x) :=
          mul_le_mul h1 hs (Real.sqrt_nonneg _) (by positivity)
      _ = 11 / 2 := by field_simp; norm_num
      _ ≤ 12000000 := by norm_num
  · rcases le_total x (q ^ 3) with hx2 | hx2
    · -- window
      have hw := window_bound hq h hx1 hx2
      have hd : |q ^ 6 - x ^ 2| + q ^ 2 ≤ (11 * q) ^ 2 := by
        have hsq := bxb_sq hq
        have : 0 ≤ q ^ 6 - x ^ 2 := by nlinarith [pow_pos hq0 3]
        rw [abs_of_nonneg this]
        nlinarith [mul_self_nonneg x, pow_pos hq0 2]
      have hs : √(|q ^ 6 - x ^ 2| + q ^ 2) ≤ 11 * q := Real.sqrt_le_iff.2 ⟨by positivity, hd⟩
      calc f x ^ 2 * √(|q ^ 6 - x ^ 2| + q ^ 2) ≤ 1000001 / q * (11 * q) :=
            mul_le_mul hw hs (Real.sqrt_nonneg _) (by positivity)
        _ = 11000011 := by field_simp; norm_num
        _ ≤ 12000000 := by norm_num
    · have hK := window_bound hq h hxbq le_rfl
      have := forbidden_bound (by linarith) h (K := 1000001) (by norm_num) hK hx2
      linarith

end window

end FormalResearch.Special
