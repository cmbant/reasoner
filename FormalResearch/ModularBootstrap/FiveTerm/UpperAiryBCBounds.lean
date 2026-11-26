module

public import FormalResearch.ModularBootstrap.FiveTerm.UpperAiryBC

/-!
# `cts:BC-bnds`, step 3: the bound on the right side of `cts:BC-id`

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, Lemma `cts:tip-shared` (c), label `cts:BC-id`
and its bound, with `h = X^{-1/2}/2`.  For `X ≥ 1` and `0 < h ≤ 1/2`, the right side of `cts:BC-id`,

  `∫_0^h w Ai(·-X) - w(h) B(h-X) + w'(h) C(h-X) + ∫_h^∞ w'' C(·-X)`,

is bounded by `40 (X^{-1/4} ∫_0^h |w| + X^{-3/4} |w(h)| + X^{-5/4} |w'(h)| + ∫_h^∞ |w''| |C(·-X)|)`.  The constant
`40` is explicit and independent of `w`, `X`, `h`; the four terms come from
`|Ai(x)| ≤ 3(1+|x|)^{-1/4}` on `x ≤ 0` (`abs_airyAi_le_of_nonpos`), `|B(t)| ≤ 16|t|^{-3/4}`, `|C(t)| ≤ 16|t|^{-5/4}`
for `t ≤ -1/2` (`Bneg_decay` for `t ≤ -1`, and `|B|, |C| ≤ 16` on `[-1,-1/2]`), and `|X - h| ≥ X/2`.  Integrability
of `|w''| |C(·-X)|` on `(h,∞)` is `airyBC_integrableOn_abs`.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.Special.AiryPrimNeg

/-- `|B(t)| ≤ 16 (-t)^{-3/4}` and `|C(t)| ≤ 16 (-t)^{-5/4}` for `t ≤ -1/2`. -/
private lemma primB_primC_neg_bound {t : ℝ} (ht : t ≤ -1 / 2) :
    |airyPrimB t| ≤ 16 * (-t) ^ (-(3 / 4) : ℝ) ∧ |airyPrimC t| ≤ 16 * (-t) ^ (-(5 / 4) : ℝ) := by
  have hBeq : airyPrimB t = Bneg t := airyPrimB_eq (by linarith)
  have hCeq : airyPrimC t = t * Bneg t - airyAi' t := by
    unfold airyPrimC
    rw [hBeq]
  rcases le_total t (-1) with h1 | h1
  · have hB := Bneg_decay h1
    exact ⟨by rw [hBeq]; exact hB.1, by rw [hCeq]; exact hB.2⟩
  · have hpos : 0 < -t := by linarith
    have hle1 : -t ≤ 1 := by linarith
    have hr1 : 1 ≤ (-t) ^ (-(3 / 4) : ℝ) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos hle1 (by norm_num)
    have hr2 : 1 ≤ (-t) ^ (-(5 / 4) : ℝ) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos hle1 (by norm_num)
    have hI : |∫ x in t..0, airyAi x| ≤ 3 * |0 - t| := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := 0) (C := 3)
        (f := airyAi) (fun x _ => by rw [Real.norm_eq_abs]; exact abs_airyAi_le_three x)
      simpa [Real.norm_eq_abs] using this
    have habs0 : |0 - t| = -t := by rw [zero_sub, abs_of_pos hpos]
    have hBbd : |Bneg t| ≤ 11 / 3 := by
      unfold Bneg
      have h := abs_sub (2 / 3 : ℝ) (∫ x in t..0, airyAi x)
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)] at h
      linarith
    have habst : |t| = -t := abs_of_neg (by linarith)
    have hAi' := abs_airyAi'_le_of_nonpos (x := t) (by linarith)
    rw [habst] at hAi'
    have h14 : (1 + -t) ^ (1 / 4 : ℝ) ≤ 2 := by
      calc (1 + -t) ^ (1 / 4 : ℝ) ≤ (1 + -t) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = 1 + -t := Real.rpow_one _
        _ ≤ 2 := by linarith
    have hBabs : |airyPrimB t| ≤ 11 / 3 := by rw [hBeq]; exact hBbd
    have hCbd : |airyPrimC t| ≤ 16 := by
      rw [hCeq]
      have h1' := abs_sub (t * Bneg t) (airyAi' t)
      rw [abs_mul, habst] at h1'
      have h2 : -t * |Bneg t| ≤ 1 * (11 / 3) := mul_le_mul (by linarith) hBbd (abs_nonneg _) (by norm_num)
      linarith
    exact ⟨by linarith, by linarith⟩

/-- `(X/2)^{-z} = 2^z X^{-z}` for `X > 0`. -/
private lemma rpow_div_two (X : ℝ) (hX : 0 < X) (z : ℝ) : (X / 2) ^ (-z) = 2 ^ z * X ^ (-z) := by
  rw [Real.div_rpow hX.le (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    div_inv_eq_mul, mul_comm]

/-- `2^{1/4} ≤ 5/4`, hence `2^{3/4}, 2^{5/4} ≤ 5/2`. -/
private lemma two_rpow_quarter_le : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 5 / 4 := by
  have hu0 : 0 ≤ (2 : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hu4 : ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  nlinarith [sq_nonneg ((2 : ℝ) ^ (1 / 4 : ℝ) - 5 / 4), sq_nonneg ((2 : ℝ) ^ (1 / 4 : ℝ)),
    mul_nonneg hu0 hu0]

private lemma two_rpow_five_quarter_le : (2 : ℝ) ^ (5 / 4 : ℝ) ≤ 5 / 2 := by
  have h : (2 : ℝ) ^ (5 / 4 : ℝ) = 2 * (2 : ℝ) ^ (1 / 4 : ℝ) := by
    rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one]
  rw [h]
  linarith [two_rpow_quarter_le]

private lemma two_rpow_three_quarter_le : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 5 / 2 :=
  (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num : (3 / 4 : ℝ) ≤ 5 / 4)).trans
    two_rpow_five_quarter_le

/-- **`cts:BC-bnds` step 3**: the right side of `cts:BC-id` is bounded by `40 (X^{-1/4} ∫_0^h|w| + X^{-3/4}|w(h)| +
X^{-5/4}|w'(h)| + ∫_h^∞|w''||C(·-X)|)`, for `X ≥ 1`, `0 < h ≤ 1/2`.  The integrability of the last integrand on
`(h,∞)` is part of the conclusion. -/
theorem airyBC_rhs_bound {X h : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hh2 : h ≤ 1 / 2) {w w1 w2 : ℝ → ℝ}
    (hwint : IntervalIntegrable w volume 0 h) (hw2 : ContinuousOn w2 (Ioi 0))
    (hpoly2 : ∃ (K : ℝ) (N : ℕ), ∀ s, h ≤ s → |w2 s| ≤ K * (1 + s) ^ N) :
    IntegrableOn (fun s => |w2 s| * |airyPrimC (s - X)|) (Ioi h) ∧
      |(∫ s in (0 : ℝ)..h, w s * airyAi (s - X)) - w h * airyPrimB (h - X) +
          w1 h * airyPrimC (h - X) + ∫ s in Ioi h, w2 s * airyPrimC (s - X)| ≤
        40 * (X ^ (-(1 / 4) : ℝ) * (∫ s in (0 : ℝ)..h, |w s|) + X ^ (-(3 / 4) : ℝ) * |w h| +
          X ^ (-(5 / 4) : ℝ) * |w1 h| + ∫ s in Ioi h, |w2 s| * |airyPrimC (s - X)|) := by
  obtain ⟨K, N, hK⟩ := hpoly2
  have hXpos : 0 < X := by linarith
  have hhX : h < X := by linarith
  have hint := airyBC_integrableOn_abs hh hhX hw2 hK
  refine ⟨hint, ?_⟩
  -- nonnegativity of the integrals and of the powers
  have hJ0 : 0 ≤ ∫ s in (0 : ℝ)..h, |w s| := intervalIntegral.integral_nonneg hh.le (fun s _ => abs_nonneg _)
  have hJ2 : 0 ≤ ∫ s in Ioi h, |w2 s| * |airyPrimC (s - X)| :=
    setIntegral_nonneg measurableSet_Ioi (fun s _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hpX1 : 0 ≤ X ^ (-(1 / 4) : ℝ) := Real.rpow_nonneg hXpos.le _
  have hpX3 : 0 ≤ X ^ (-(3 / 4) : ℝ) := Real.rpow_nonneg hXpos.le _
  have hpX5 : 0 ≤ X ^ (-(5 / 4) : ℝ) := Real.rpow_nonneg hXpos.le _
  -- (a) the Airy integral on `[0,h]`
  have hI0 : |∫ s in (0 : ℝ)..h, w s * airyAi (s - X)| ≤
      40 * (X ^ (-(1 / 4) : ℝ) * ∫ s in (0 : ℝ)..h, |w s|) := by
    have hg : IntervalIntegrable (fun s => (3 * (2 ^ (1 / 4 : ℝ) * X ^ (-(1 / 4) : ℝ))) * |w s|)
        volume 0 h :=
      (hwint.abs).const_mul _
    have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioc 0 h →
        ‖w s * airyAi (s - X)‖ ≤ (3 * (2 ^ (1 / 4 : ℝ) * X ^ (-(1 / 4) : ℝ))) * |w s| := by
      refine Eventually.of_forall fun s hs => ?_
      have hs0 : 0 < s := hs.1
      have hsX : s - X ≤ 0 := by linarith [hs.2]
      have hA := abs_airyAi_le_of_nonpos (x := s - X) hsX
      have habsX : |s - X| = X - s := by
        rw [abs_of_nonpos hsX]
        ring
      have hXs : X / 2 ≤ 1 + |s - X| := by
        rw [habsX]
        linarith [hs.2]
      have hpow : (1 + |s - X|) ^ (-(1 / 4) : ℝ) ≤ (X / 2) ^ (-(1 / 4) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hXs (by norm_num)
      rw [rpow_div_two X hXpos (1 / 4)] at hpow
      rw [Real.norm_eq_abs, abs_mul]
      calc |w s| * |airyAi (s - X)| ≤ |w s| * (3 * (2 ^ (1 / 4 : ℝ) * X ^ (-(1 / 4) : ℝ))) :=
            mul_le_mul_of_nonneg_left (hA.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))) (abs_nonneg _)
        _ = (3 * (2 ^ (1 / 4 : ℝ) * X ^ (-(1 / 4) : ℝ))) * |w s| := by ring
    have hmain := intervalIntegral.norm_integral_le_of_norm_le hh.le hae hg
    rw [intervalIntegral.integral_const_mul, Real.norm_eq_abs] at hmain
    have hc : 3 * (2 ^ (1 / 4 : ℝ) * X ^ (-(1 / 4) : ℝ)) * (∫ s in (0 : ℝ)..h, |w s|) ≤
        40 * (X ^ (-(1 / 4) : ℝ) * ∫ s in (0 : ℝ)..h, |w s|) := by
      have h3 : 3 * (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 40 := by linarith [two_rpow_quarter_le]
      have h4 : 0 ≤ X ^ (-(1 / 4) : ℝ) * ∫ s in (0 : ℝ)..h, |w s| := mul_nonneg hpX1 hJ0
      have e : 3 * (2 ^ (1 / 4 : ℝ) * X ^ (-(1 / 4) : ℝ)) * (∫ s in (0 : ℝ)..h, |w s|) =
          (3 * 2 ^ (1 / 4 : ℝ)) * (X ^ (-(1 / 4) : ℝ) * ∫ s in (0 : ℝ)..h, |w s|) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right h3 h4
    linarith
  -- (b) the boundary term at `h`: `|B(h-X)| ≤ 40 X^{-3/4}`
  have hBw : |w h * airyPrimB (h - X)| ≤ 40 * (X ^ (-(3 / 4) : ℝ) * |w h|) := by
    have hB := (primB_primC_neg_bound (t := h - X) (by linarith)).1
    have hdist : (-(h - X)) ^ (-(3 / 4) : ℝ) ≤ (X / 2) ^ (-(3 / 4) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
    rw [rpow_div_two X hXpos (3 / 4)] at hdist
    have h16 : 16 * (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 40 := by linarith [two_rpow_three_quarter_le]
    have hB2 : |airyPrimB (h - X)| ≤ 40 * X ^ (-(3 / 4) : ℝ) := by
      calc |airyPrimB (h - X)| ≤ 16 * (-(h - X)) ^ (-(3 / 4) : ℝ) := hB
        _ ≤ 16 * (2 ^ (3 / 4 : ℝ) * X ^ (-(3 / 4) : ℝ)) := mul_le_mul_of_nonneg_left hdist (by norm_num)
        _ = (16 * 2 ^ (3 / 4 : ℝ)) * X ^ (-(3 / 4) : ℝ) := by ring
        _ ≤ 40 * X ^ (-(3 / 4) : ℝ) := mul_le_mul_of_nonneg_right h16 hpX3
    rw [abs_mul]
    calc |w h| * |airyPrimB (h - X)| ≤ |w h| * (40 * X ^ (-(3 / 4) : ℝ)) :=
          mul_le_mul_of_nonneg_left hB2 (abs_nonneg _)
      _ = 40 * (X ^ (-(3 / 4) : ℝ) * |w h|) := by ring
  -- (c) the derivative term at `h`: `|C(h-X)| ≤ 40 X^{-5/4}`
  have hCw : |w1 h * airyPrimC (h - X)| ≤ 40 * (X ^ (-(5 / 4) : ℝ) * |w1 h|) := by
    have hC := (primB_primC_neg_bound (t := h - X) (by linarith)).2
    have hdist : (-(h - X)) ^ (-(5 / 4) : ℝ) ≤ (X / 2) ^ (-(5 / 4) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
    rw [rpow_div_two X hXpos (5 / 4)] at hdist
    have h16 : 16 * (2 : ℝ) ^ (5 / 4 : ℝ) ≤ 40 := by linarith [two_rpow_five_quarter_le]
    have hC2 : |airyPrimC (h - X)| ≤ 40 * X ^ (-(5 / 4) : ℝ) := by
      calc |airyPrimC (h - X)| ≤ 16 * (-(h - X)) ^ (-(5 / 4) : ℝ) := hC
        _ ≤ 16 * (2 ^ (5 / 4 : ℝ) * X ^ (-(5 / 4) : ℝ)) := mul_le_mul_of_nonneg_left hdist (by norm_num)
        _ = (16 * 2 ^ (5 / 4 : ℝ)) * X ^ (-(5 / 4) : ℝ) := by ring
        _ ≤ 40 * X ^ (-(5 / 4) : ℝ) := mul_le_mul_of_nonneg_right h16 hpX5
    rw [abs_mul]
    calc |w1 h| * |airyPrimC (h - X)| ≤ |w1 h| * (40 * X ^ (-(5 / 4) : ℝ)) :=
          mul_le_mul_of_nonneg_left hC2 (abs_nonneg _)
      _ = 40 * (X ^ (-(5 / 4) : ℝ) * |w1 h|) := by ring
  -- (d) the tail integral: `|∫_h^∞ w2 C| ≤ ∫_h^∞ |w2| |C|`
  have hI2 : |∫ s in Ioi h, w2 s * airyPrimC (s - X)| ≤ ∫ s in Ioi h, |w2 s| * |airyPrimC (s - X)| := by
    have := norm_integral_le_integral_norm (μ := volume.restrict (Ioi h))
      (fun s => w2 s * airyPrimC (s - X))
    simpa only [Real.norm_eq_abs, abs_mul] using this
  -- the triangle inequality on the four terms
  have a1 := abs_add_le ((∫ s in (0 : ℝ)..h, w s * airyAi (s - X)) - w h * airyPrimB (h - X) +
    w1 h * airyPrimC (h - X)) (∫ s in Ioi h, w2 s * airyPrimC (s - X))
  have a2 := abs_add_le ((∫ s in (0 : ℝ)..h, w s * airyAi (s - X)) - w h * airyPrimB (h - X))
    (w1 h * airyPrimC (h - X))
  have a3 := abs_sub (∫ s in (0 : ℝ)..h, w s * airyAi (s - X)) (w h * airyPrimB (h - X))
  linarith [a1, a2, a3, hI0, hBw, hCw, hI2, hJ2]

/-- The step-3 bound with the paper's split point `h = X^{-1/2}/2` (`X ≥ 1`). -/
theorem airyBC_rhs_bound_paper {X h : ℝ} (hX : 1 ≤ X) (hh : h = X ^ (-(1 / 2) : ℝ) / 2)
    {w w1 w2 : ℝ → ℝ} (hwint : IntervalIntegrable w volume 0 h) (hw2 : ContinuousOn w2 (Ioi 0))
    (hpoly2 : ∃ (K : ℝ) (N : ℕ), ∀ s, h ≤ s → |w2 s| ≤ K * (1 + s) ^ N) :
    IntegrableOn (fun s => |w2 s| * |airyPrimC (s - X)|) (Ioi h) ∧
      |(∫ s in (0 : ℝ)..h, w s * airyAi (s - X)) - w h * airyPrimB (h - X) +
          w1 h * airyPrimC (h - X) + ∫ s in Ioi h, w2 s * airyPrimC (s - X)| ≤
        40 * (X ^ (-(1 / 4) : ℝ) * (∫ s in (0 : ℝ)..h, |w s|) + X ^ (-(3 / 4) : ℝ) * |w h| +
          X ^ (-(5 / 4) : ℝ) * |w1 h| + ∫ s in Ioi h, |w2 s| * |airyPrimC (s - X)|) := by
  have hpos : 0 < h := by
    rw [hh]
    exact div_pos (Real.rpow_pos_of_pos (by linarith) _) (by norm_num)
  have hle : h ≤ 1 / 2 := by
    rw [hh]
    have : X ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX (by norm_num)
    linarith
  exact airyBC_rhs_bound hX hpos hle hwint hw2 hpoly2

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.airyBC_rhs_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyBC_rhs_bound

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.airyBC_rhs_bound_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyBC_rhs_bound_paper

/-! ### Step 4: the three bounds `cts:BC-bnds` -/

/-- `|C(t)| ≤ 16` on `[-1,0]`. -/
private lemma primC_small {t : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 0) : |airyPrimC t| ≤ 16 := by
  have hBeq : airyPrimB t = Bneg t := airyPrimB_eq h2
  have hCeq : airyPrimC t = t * Bneg t - airyAi' t := by
    unfold airyPrimC
    rw [hBeq]
  have hI : |∫ x in t..0, airyAi x| ≤ 3 * |0 - t| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := 0) (C := 3)
      (f := airyAi) (fun x _ => by rw [Real.norm_eq_abs]; exact abs_airyAi_le_three x)
    simpa [Real.norm_eq_abs] using this
  have habs1 : |0 - t| ≤ 1 := by
    rw [zero_sub, abs_le]
    constructor <;> linarith
  have hBbd : |Bneg t| ≤ 11 / 3 := by
    unfold Bneg
    have h := abs_sub (2 / 3 : ℝ) (∫ x in t..0, airyAi x)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)] at h
    linarith
  have habst : |t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hAi' := abs_airyAi'_le_of_nonpos (x := t) h2
  have h14 : (1 + |t|) ^ (1 / 4 : ℝ) ≤ 2 := by
    calc (1 + |t|) ^ (1 / 4 : ℝ) ≤ (1 + |t|) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (by norm_num)
      _ = 1 + |t| := Real.rpow_one _
      _ ≤ 2 := by linarith
  rw [hCeq]
  have h1' := abs_sub (t * Bneg t) (airyAi' t)
  rw [abs_mul] at h1'
  have h2' : |t| * |Bneg t| ≤ 1 * (11 / 3) := mul_le_mul habst hBbd (abs_nonneg _) (by norm_num)
  linarith

/-- `r^{-5/4} ≤ 2^{5/4} (1+r)^{-5/4}` for `r ≥ 1`. -/
private lemma rpow_neg_five_quarter_le {r : ℝ} (hr : 1 ≤ r) :
    r ^ (-(5 / 4) : ℝ) ≤ 2 ^ (5 / 4 : ℝ) * (1 + r) ^ (-(5 / 4) : ℝ) := by
  have h1 : (2 * r) ^ (-(5 / 4) : ℝ) ≤ (1 + r) ^ (-(5 / 4) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
  rw [Real.mul_rpow (by norm_num) (by linarith)] at h1
  have h2 : (2 : ℝ) ^ (5 / 4 : ℝ) * (2 : ℝ) ^ (-(5 / 4) : ℝ) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  calc r ^ (-(5 / 4) : ℝ) = 2 ^ (5 / 4 : ℝ) * ((2 : ℝ) ^ (-(5 / 4) : ℝ) * r ^ (-(5 / 4) : ℝ)) := by
        rw [← mul_assoc, h2, one_mul]
    _ ≤ 2 ^ (5 / 4 : ℝ) * (1 + r) ^ (-(5 / 4) : ℝ) := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- The global kernel bound: `|C(t)| ≤ M (1+|t|)^{-5/4}` for all `t`. -/
theorem airyBC_primC_dom :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |airyPrimC t| ≤ M * (1 + |t|) ^ (-(5 / 4) : ℝ) := by
  obtain ⟨K0, hK0, hdec⟩ := airyBC_primDecay_pos
  refine ⟨16 * 2 ^ (5 / 4 : ℝ) + K0 * Real.exp (2 / 3) * (81 / 4), by positivity, fun t => ?_⟩
  have hz0 : 0 ≤ (1 + |t|) ^ (-(5 / 4) : ℝ) := Real.rpow_nonneg (by positivity) _
  have hM2 : 0 ≤ K0 * Real.exp (2 / 3) * (81 / 4) := by positivity
  have h2pos : (0 : ℝ) ≤ 2 ^ (5 / 4 : ℝ) := by positivity
  rcases le_total t (-1) with ht | ht
  · -- `t ≤ -1`: Bneg decay
    have hb := (Bneg_decay ht).2
    have hC : airyPrimC t = t * Bneg t - airyAi' t := by
      unfold airyPrimC
      rw [airyPrimB_eq (by linarith)]
    have habs : |t| = -t := abs_of_neg (by linarith)
    have hr : 1 ≤ -t := by linarith
    have hpow := rpow_neg_five_quarter_le hr
    rw [habs, hC]
    have hfinal : 16 * (-t) ^ (-(5 / 4) : ℝ) ≤ (16 * 2 ^ (5 / 4 : ℝ)) * (1 + -t) ^ (-(5 / 4) : ℝ) := by
      have := mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 16)
      linarith
    have hpos2 : 0 ≤ K0 * Real.exp (2 / 3) * (81 / 4) * (1 + -t) ^ (-(5 / 4) : ℝ) :=
      mul_nonneg hM2 (Real.rpow_nonneg (by linarith) _)
    calc |t * Bneg t - airyAi' t| ≤ 16 * (-t) ^ (-(5 / 4) : ℝ) := hb
      _ ≤ (16 * 2 ^ (5 / 4 : ℝ)) * (1 + -t) ^ (-(5 / 4) : ℝ) := hfinal
      _ ≤ (16 * 2 ^ (5 / 4 : ℝ) + K0 * Real.exp (2 / 3) * (81 / 4)) * (1 + -t) ^ (-(5 / 4) : ℝ) := by
          nlinarith
  · rcases le_or_gt t 0 with ht0 | ht0
    · -- `-1 ≤ t ≤ 0`: bounded
      have hsmall := primC_small ht ht0
      have hle : (2 : ℝ) ≤ 1 + |t| + 1 := by linarith [abs_nonneg t]
      have hA : (2 : ℝ) ^ (-(5 / 4) : ℝ) ≤ (1 + |t|) ^ (-(5 / 4) : ℝ) := by
        apply Real.rpow_le_rpow_of_nonpos (by positivity)
        · rw [abs_of_nonpos ht0]
          linarith
        · norm_num
      have h1 : (1 : ℝ) = 2 ^ (5 / 4 : ℝ) * (2 : ℝ) ^ (-(5 / 4) : ℝ) := by
        rw [← Real.rpow_add (by norm_num)]
        norm_num
      have h16 : (16 : ℝ) ≤ (16 * 2 ^ (5 / 4 : ℝ)) * (1 + |t|) ^ (-(5 / 4) : ℝ) := by
        have := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 2 ^ (5 / 4 : ℝ))
        nlinarith
      have hpos2 : 0 ≤ K0 * Real.exp (2 / 3) * (81 / 4) * (1 + |t|) ^ (-(5 / 4) : ℝ) :=
        mul_nonneg hM2 hz0
      calc |airyPrimC t| ≤ 16 := hsmall
        _ ≤ (16 * 2 ^ (5 / 4 : ℝ)) * (1 + |t|) ^ (-(5 / 4) : ℝ) := h16
        _ ≤ _ := by nlinarith
    · -- `t > 0`: exponential decay, `(1+t) e^{-2t/3} ≤ e^{2/3} (81/4) (1+t)^{-5/4}`
      have ht' : 0 < t := ht0
      rw [abs_of_pos ht']
      have hd := (hdec t ht').2
      have hx1 : 1 ≤ 1 + t := by linarith
      have hzt : 0 ≤ (1 + t) ^ (-(5 / 4) : ℝ) := Real.rpow_nonneg (by linarith) _
      have hexp1 : Real.exp (-(2 / 3) * t) = Real.exp (2 / 3) * Real.exp (-((2 / 3) * (1 + t))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hy0 : 0 ≤ (2 / 3) * (1 + t) := mul_nonneg (by norm_num) (by linarith)
      have hcube : (1 + t) ^ 3 ≤ (81 / 4) * Real.exp ((2 / 3) * (1 + t)) := by
        have h3 := Real.pow_div_factorial_le_exp _ hy0 3
        have e1 : ((2 / 3) * (1 + t)) ^ 3 = (8 / 27) * (1 + t) ^ 3 := by ring
        rw [e1] at h3
        norm_num [Nat.factorial] at h3
        linarith
      have hexpneg : (1 + t) ^ 3 * Real.exp (-((2 / 3) * (1 + t))) ≤ 81 / 4 := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
        linarith
      have hp1 : (1 + t) ^ (9 / 4 : ℝ) ≤ (1 + t) ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hp1
      have hsplit : (1 + t) ^ (-(5 / 4) : ℝ) * (1 + t) ^ (9 / 4 : ℝ) = 1 + t := by
        rw [← Real.rpow_add (by linarith), show (-(5 / 4) : ℝ) + 9 / 4 = 1 by norm_num, Real.rpow_one]
      have hE : 0 ≤ Real.exp (-(2 / 3) * t) := (Real.exp_pos _).le
      have hK0z : 0 ≤ K0 * (1 + t) ^ (-(5 / 4) : ℝ) := mul_nonneg hK0 hzt
      calc |airyPrimC t| ≤ K0 * (1 + t) * Real.exp (-(2 / 3) * t) := hd
        _ = K0 * ((1 + t) ^ (-(5 / 4) : ℝ) * (1 + t) ^ (9 / 4 : ℝ)) * Real.exp (-(2 / 3) * t) := by
            rw [hsplit]
        _ = K0 * (1 + t) ^ (-(5 / 4) : ℝ) * ((1 + t) ^ (9 / 4 : ℝ) * Real.exp (-(2 / 3) * t)) := by
            ring
        _ ≤ K0 * (1 + t) ^ (-(5 / 4) : ℝ) * ((1 + t) ^ 3 * Real.exp (-(2 / 3) * t)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp1 hE) hK0z
        _ = K0 * (1 + t) ^ (-(5 / 4) : ℝ) * (Real.exp (2 / 3) * ((1 + t) ^ 3 *
              Real.exp (-((2 / 3) * (1 + t))))) := by
            rw [hexp1]
            ring
        _ ≤ K0 * (1 + t) ^ (-(5 / 4) : ℝ) * (Real.exp (2 / 3) * (81 / 4)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexpneg (Real.exp_pos _).le) hK0z
        _ = (K0 * Real.exp (2 / 3) * (81 / 4)) * (1 + t) ^ (-(5 / 4) : ℝ) := by ring
        _ ≤ _ := by nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 16 * 2 ^ (5 / 4 : ℝ)) hzt]

/-- The integrable dominating function `(1+|t|)^{-5/4}` on `ℝ`. -/
private lemma integrable_japanese_five_quarter :
    Integrable (fun t : ℝ => (1 + |t|) ^ (-(5 / 4) : ℝ)) := by
  have h0 := integrable_one_add_norm (μ := volume) (E := ℝ) (r := 5 / 4) (by norm_num)
  simpa [Real.norm_eq_abs] using h0

/-- **Tail estimate.** For `0 < h ≤ X/2` and `p > 1`, with the kernel bound `|C(t)| ≤ M(1+|t|)^{-5/4}`:
`∫_{(h,∞)} s^{-p}|C(s-X)| ds ≤ M (X/2)^{-5/4} ∫_{(h,∞)} s^{-p} ds + (X/2)^{-p} M ∫_ℝ (1+|t|)^{-5/4} dt`. -/
theorem airyBC_tail_rpow {X h p M : ℝ} (hp : 1 < p) (hh : 0 < h) (hhX : h ≤ X / 2)
    (hM : 0 ≤ M) (hC : ∀ t : ℝ, |airyPrimC t| ≤ M * (1 + |t|) ^ (-(5 / 4) : ℝ)) :
    ∫ s in Ioi h, s ^ (-p) * |airyPrimC (s - X)| ≤
      M * (X / 2) ^ (-(5 / 4) : ℝ) * (∫ s in Ioi h, s ^ (-p)) +
        (X / 2) ^ (-p) * M * (∫ t : ℝ, (1 + |t|) ^ (-(5 / 4) : ℝ)) := by
  have hX2 : 0 < X / 2 := by linarith
  have hG2 : Integrable (fun s : ℝ => (X / 2) ^ (-p) * M * (1 + |s - X|) ^ (-(5 / 4) : ℝ)) :=
    (integrable_japanese_five_quarter.comp_sub_right X).const_mul _
  have hG1 : IntegrableOn (fun s : ℝ => M * (X / 2) ^ (-(5 / 4) : ℝ) * s ^ (-p)) (Ioi h) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1) hh).const_mul _
  have hpt : ∀ s ∈ Ioi h, s ^ (-p) * |airyPrimC (s - X)| ≤
      M * (X / 2) ^ (-(5 / 4) : ℝ) * s ^ (-p) + (X / 2) ^ (-p) * M * (1 + |s - X|) ^ (-(5 / 4) : ℝ) := by
    intro s hs
    have hs0 : 0 < s := hh.trans hs
    have hsp : 0 ≤ s ^ (-p) := Real.rpow_nonneg hs0.le _
    have hA : 0 ≤ (1 + |s - X|) ^ (-(5 / 4) : ℝ) := Real.rpow_nonneg (by positivity) _
    have hF : s ^ (-p) * |airyPrimC (s - X)| ≤ s ^ (-p) * (M * (1 + |s - X|) ^ (-(5 / 4) : ℝ)) :=
      mul_le_mul_of_nonneg_left (hC (s - X)) hsp
    have hB : 0 ≤ (X / 2) ^ (-p) * M * (1 + |s - X|) ^ (-(5 / 4) : ℝ) :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hX2.le _) hM) hA
    rcases le_total s (X / 2) with hsX | hsX
    · have hle : (1 + |s - X|) ^ (-(5 / 4) : ℝ) ≤ (X / 2) ^ (-(5 / 4) : ℝ) := by
        apply Real.rpow_le_rpow_of_nonpos hX2
        · rw [abs_of_nonpos (by linarith)]
          linarith
        · norm_num
      calc s ^ (-p) * |airyPrimC (s - X)| ≤ s ^ (-p) * (M * (1 + |s - X|) ^ (-(5 / 4) : ℝ)) := hF
        _ ≤ s ^ (-p) * (M * (X / 2) ^ (-(5 / 4) : ℝ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hM) hsp
        _ = M * (X / 2) ^ (-(5 / 4) : ℝ) * s ^ (-p) := by ring
        _ ≤ _ := by linarith
    · have hle2 : s ^ (-p) ≤ (X / 2) ^ (-p) :=
        Real.rpow_le_rpow_of_nonpos hX2 hsX (by linarith)
      calc s ^ (-p) * |airyPrimC (s - X)| ≤ s ^ (-p) * (M * (1 + |s - X|) ^ (-(5 / 4) : ℝ)) := hF
        _ ≤ (X / 2) ^ (-p) * (M * (1 + |s - X|) ^ (-(5 / 4) : ℝ)) :=
            mul_le_mul_of_nonneg_right hle2 (mul_nonneg hM hA)
        _ = (X / 2) ^ (-p) * M * (1 + |s - X|) ^ (-(5 / 4) : ℝ) := by ring
        _ ≤ _ := by
            have : 0 ≤ M * (X / 2) ^ (-(5 / 4) : ℝ) * s ^ (-p) :=
              mul_nonneg (mul_nonneg hM (Real.rpow_nonneg hX2.le _)) hsp
            linarith
  have hsplit : ∫ s in Ioi h, s ^ (-p) * |airyPrimC (s - X)| ≤
      ∫ s in Ioi h, (M * (X / 2) ^ (-(5 / 4) : ℝ) * s ^ (-p) +
        (X / 2) ^ (-p) * M * (1 + |s - X|) ^ (-(5 / 4) : ℝ)) := by
    refine integral_mono_of_nonneg ?_ (hG1.add hG2.integrableOn) ?_
    · exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => by
        have hs0 : 0 < s := hh.trans hs
        exact mul_nonneg (Real.rpow_nonneg hs0.le _) (abs_nonneg _))
    · exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => hpt s hs)
  rw [integral_add hG1 hG2.integrableOn, MeasureTheory.integral_const_mul] at hsplit
  have htail : ∫ s in Ioi h, (X / 2) ^ (-p) * M * (1 + |s - X|) ^ (-(5 / 4) : ℝ) ≤
      (X / 2) ^ (-p) * M * (∫ t : ℝ, (1 + |t|) ^ (-(5 / 4) : ℝ)) := by
    have h1 : ∫ s in Ioi h, (X / 2) ^ (-p) * M * (1 + |s - X|) ^ (-(5 / 4) : ℝ) ≤
        ∫ s : ℝ, (X / 2) ^ (-p) * M * (1 + |s - X|) ^ (-(5 / 4) : ℝ) :=
      setIntegral_le_integral hG2 (Eventually.of_forall fun s => by
        exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hX2.le _) hM) (Real.rpow_nonneg (by positivity) _))
    have h2 : ∫ s : ℝ, (X / 2) ^ (-p) * M * (1 + |s - X|) ^ (-(5 / 4) : ℝ) =
        (X / 2) ^ (-p) * M * (∫ t : ℝ, (1 + |t|) ^ (-(5 / 4) : ℝ)) := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      exact integral_sub_right_eq_self (fun t : ℝ => (1 + |t|) ^ (-(5 / 4) : ℝ)) X
    linarith
  have hI : M * (X / 2) ^ (-(5 / 4) : ℝ) * (∫ s in Ioi h, s ^ (-p)) =
      ∫ s in Ioi h, M * (X / 2) ^ (-(5 / 4) : ℝ) * s ^ (-p) := by
    rw [MeasureTheory.integral_const_mul]
  linarith

/-! #### The families `w_0 = s^{-1/2}(1-e^{-τs})`, `w_2 = s^{1/2}e^{-τs}` and their derivatives

Writing `q = s^{-1/2}`, `ι = s⁻¹`, `E = e^{-τs}`, `u = s^{1/2}` (so `q = u ι`), the derivatives close as polynomials
in `(q, ι, E)` and `(u, ι, E)`, using `q' = -(1/2) q ι`, `u' = (1/2) u ι`, `ι' = -ι²`, `E' = -τE`. -/

/-- `w_0(s) = s^{-1/2}(1 - e^{-τs})` (the paper's `w_0`). -/
noncomputable def stepW0 (τ s : ℝ) : ℝ := s ^ (-(1 / 2) : ℝ) * (1 - Real.exp (-(τ * s)))

/-- `w_1 = w_0'`. -/
noncomputable def stepW1 (τ s : ℝ) : ℝ :=
  s ^ (-(1 / 2) : ℝ) * (-(1 / 2) * s⁻¹ + ((1 / 2) * s⁻¹ + τ) * Real.exp (-(τ * s)))

/-- `w_2 = w_0''`. -/
noncomputable def stepW2 (τ s : ℝ) : ℝ :=
  s ^ (-(1 / 2) : ℝ) * ((3 / 4) * (s⁻¹ * s⁻¹) +
    (-(3 / 4) * (s⁻¹ * s⁻¹) - τ * s⁻¹ - τ ^ 2) * Real.exp (-(τ * s)))

/-- `w_3 = w_0'''`. -/
noncomputable def stepW3 (τ s : ℝ) : ℝ :=
  s ^ (-(1 / 2) : ℝ) * (-(15 / 8) * (s⁻¹ * s⁻¹ * s⁻¹) +
    ((15 / 8) * (s⁻¹ * s⁻¹ * s⁻¹) + (9 / 4) * τ * (s⁻¹ * s⁻¹) + (3 / 2) * τ ^ 2 * s⁻¹ + τ ^ 3) *
      Real.exp (-(τ * s)))

/-- `w_2(s) = s^{1/2} e^{-τs}` (the paper's `w_2`). -/
noncomputable def stepV0 (τ s : ℝ) : ℝ := s ^ (1 / 2 : ℝ) * Real.exp (-(τ * s))

/-- `w_2' ` for the family `stepV0`. -/
noncomputable def stepV1 (τ s : ℝ) : ℝ := s ^ (1 / 2 : ℝ) * Real.exp (-(τ * s)) * (s⁻¹ / 2 - τ)

/-- `w_2''` for the family `stepV0`. -/
noncomputable def stepV2 (τ s : ℝ) : ℝ :=
  s ^ (1 / 2 : ℝ) * Real.exp (-(τ * s)) * (-(s⁻¹ * s⁻¹) / 4 - τ * s⁻¹ + τ ^ 2)

private lemma hasDerivAt_rpow_neg_half {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) (-(1 / 2) * (s ^ (-(1 / 2) : ℝ) / s)) s := by
  have h := Real.hasDerivAt_rpow_const (x := s) (p := -(1 / 2)) (Or.inl hs.ne')
  rwa [Real.rpow_sub_one hs.ne'] at h

private lemma hasDerivAt_rpow_half {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun x : ℝ => x ^ (1 / 2 : ℝ)) ((1 / 2) * (s ^ (1 / 2 : ℝ) / s)) s := by
  have h := Real.hasDerivAt_rpow_const (x := s) (p := 1 / 2) (Or.inl hs.ne')
  rwa [Real.rpow_sub_one hs.ne'] at h

private lemma hasDerivAt_expT (τ s : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-(τ * x))) (Real.exp (-(τ * s)) * (-τ)) s := by
  have h := (((hasDerivAt_id' s).const_mul τ).neg).exp
  convert h using 1
  simp only [Pi.neg_apply]
  ring

private lemma hasDerivAt_invS {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun x : ℝ => x⁻¹) (-(s⁻¹ * s⁻¹)) s := by
  have h := hasDerivAt_inv hs.ne'
  convert h using 1
  ring

private lemma hasDerivAt_stepW0 {τ s : ℝ} (hs : 0 < s) :
    HasDerivAt (stepW0 τ) (stepW1 τ s) s := by
  have h := (hasDerivAt_rpow_neg_half hs).mul
    ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_expT τ s))
  unfold stepW0 stepW1
  convert h using 1
  simp only [Pi.sub_apply]
  ring

private lemma hasDerivAt_stepW1 {τ s : ℝ} (hs : 0 < s) :
    HasDerivAt (stepW1 τ) (stepW2 τ s) s := by
  have hin := ((hasDerivAt_invS hs).const_mul (-(1 / 2))).add
    ((((hasDerivAt_invS hs).const_mul (1 / 2)).add_const τ).mul (hasDerivAt_expT τ s))
  have h := (hasDerivAt_rpow_neg_half hs).mul hin
  unfold stepW1 stepW2
  convert h using 1
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

private lemma hasDerivAt_stepW2 {τ s : ℝ} (hs : 0 < s) :
    HasDerivAt (stepW2 τ) (stepW3 τ s) s := by
  have hI2 := (hasDerivAt_invS hs).mul (hasDerivAt_invS hs)
  have hI3 := hI2.mul (hasDerivAt_invS hs)
  have hin := (((hI2.const_mul (3 / 4)).add
    ((((hI2.const_mul (-(3 / 4))).sub ((hasDerivAt_invS hs).const_mul τ)).sub_const (τ ^ 2)).mul
      (hasDerivAt_expT τ s))))
  have h := (hasDerivAt_rpow_neg_half hs).mul hin
  unfold stepW2 stepW3
  convert h using 1
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  ring

private lemma hasDerivAt_stepV0 {τ s : ℝ} (hs : 0 < s) :
    HasDerivAt (stepV0 τ) (stepV1 τ s) s := by
  have h := (hasDerivAt_rpow_half hs).mul (hasDerivAt_expT τ s)
  unfold stepV0 stepV1
  convert h using 1
  ring

private lemma hasDerivAt_stepV1 {τ s : ℝ} (hs : 0 < s) :
    HasDerivAt (stepV1 τ) (stepV2 τ s) s := by
  have hin := (((hasDerivAt_invS hs).div_const 2).sub_const τ)
  have h := ((hasDerivAt_rpow_half hs).mul (hasDerivAt_expT τ s)).mul hin
  unfold stepV1 stepV2
  convert h using 1
  simp only [Pi.mul_apply]
  ring

/-! #### Pointwise bounds -/

/-- The exponential facts: for `τ, s ≥ 0` and `E = e^{-τs}`. -/
private lemma expFacts {τ s : ℝ} (hτ : 0 ≤ τ) (hs : 0 ≤ s) :
    0 ≤ Real.exp (-(τ * s)) ∧ Real.exp (-(τ * s)) ≤ 1 ∧ 1 - Real.exp (-(τ * s)) ≤ τ * s ∧
      τ * s * Real.exp (-(τ * s)) ≤ 1 ∧ (τ * s) ^ 2 * Real.exp (-(τ * s)) ≤ 2 := by
  have hy : 0 ≤ τ * s := mul_nonneg hτ hs
  have hpos : 0 < Real.exp (-(τ * s)) := Real.exp_pos _
  refine ⟨hpos.le, ?_, ?_, ?_, ?_⟩
  · exact Real.exp_le_one_iff.2 (by linarith)
  · linarith [Real.add_one_le_exp (-(τ * s))]
  · rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    linarith [Real.add_one_le_exp (τ * s)]
  · have hq := Real.quadratic_le_exp_of_nonneg hy
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    nlinarith [hq]

/-- Algebra for `w_0`: `|q(1-E)| ≤ τ s q`. -/
private lemma alg_W0 {q s τ E : ℝ} (hq : 0 ≤ q) (hE1 : E ≤ 1) (hE3 : 1 - E ≤ τ * s) :
    |q * (1 - E)| ≤ τ * s * q := by
  rw [abs_of_nonneg (mul_nonneg hq (by linarith))]
  calc q * (1 - E) ≤ q * (τ * s) := mul_le_mul_of_nonneg_left hE3 hq
    _ = τ * s * q := by ring

/-- Algebra for `w_1`: `|q(-(1/2)ι + ((1/2)ι + τ)E)| ≤ τ q`. -/
private lemma alg_W1 {q s ι τ E : ℝ} (hq : 0 ≤ q) (hι : 0 ≤ ι) (hτ : 0 ≤ τ) (hιs : s * ι = 1)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1) (hE3 : 1 - E ≤ τ * s) :
    |q * (-(1 / 2) * ι + ((1 / 2) * ι + τ) * E)| ≤ τ * q := by
  have hιτs : ι * (τ * s) = τ := by linear_combination τ * hιs
  have hA : ι * (1 - E) ≤ τ := by
    calc ι * (1 - E) ≤ ι * (τ * s) := mul_le_mul_of_nonneg_left hE3 hι
      _ = τ := hιτs
  have hA0 : 0 ≤ ι * (1 - E) := mul_nonneg hι (by linarith)
  have hB : τ * E ≤ τ := mul_le_of_le_one_right hτ hE1
  have hB0 : 0 ≤ τ * E := mul_nonneg hτ hE0
  have hP : -(1 / 2) * ι + ((1 / 2) * ι + τ) * E = -((1 / 2) * (ι * (1 - E))) + τ * E := by ring
  have hPabs : |-(1 / 2) * ι + ((1 / 2) * ι + τ) * E| ≤ τ := by
    rw [hP, abs_le]
    constructor <;> linarith
  rw [abs_mul, abs_of_nonneg hq]
  calc q * |-(1 / 2) * ι + ((1 / 2) * ι + τ) * E| ≤ q * τ := mul_le_mul_of_nonneg_left hPabs hq
    _ = τ * q := by ring

/-- Algebra for `w_2`: `|q((3/4)ι² + (-(3/4)ι² - τι - τ²)E)| ≤ 3 τ q ι`. -/
private lemma alg_W2 {q s ι τ E : ℝ} (hq : 0 ≤ q) (hι : 0 ≤ ι) (hτ : 0 ≤ τ) (hιs : s * ι = 1)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1) (hE3 : 1 - E ≤ τ * s) (hE4 : τ * s * E ≤ 1) :
    |q * ((3 / 4) * (ι * ι) + (-(3 / 4) * (ι * ι) - τ * ι - τ ^ 2) * E)| ≤ 3 * τ * q * ι := by
  have hτι : 0 ≤ τ * ι := mul_nonneg hτ hι
  have f1 : ι * ι * (1 - E) ≤ τ * ι := by
    have h1 : ι * ι * (1 - E) ≤ ι * ι * (τ * s) := mul_le_mul_of_nonneg_left hE3 (mul_nonneg hι hι)
    have e : ι * ι * (τ * s) = τ * ι := by linear_combination (τ * ι) * hιs
    linarith
  have f0 : 0 ≤ ι * ι * (1 - E) := mul_nonneg (mul_nonneg hι hι) (by linarith)
  have hB : τ * ι * E ≤ τ * ι := mul_le_of_le_one_right hτι hE1
  have hB0 : 0 ≤ τ * ι * E := mul_nonneg hτι hE0
  have hC : τ ^ 2 * E ≤ τ * ι := by
    have e : τ ^ 2 * E = ι * τ * (τ * s * E) := by linear_combination (-(τ ^ 2 * E)) * hιs
    have h1 : ι * τ * (τ * s * E) ≤ ι * τ * 1 := mul_le_mul_of_nonneg_left hE4 (mul_nonneg hι hτ)
    linarith
  have hC0 : 0 ≤ τ ^ 2 * E := mul_nonneg (sq_nonneg τ) hE0
  have hP : (3 / 4) * (ι * ι) + (-(3 / 4) * (ι * ι) - τ * ι - τ ^ 2) * E =
      (3 / 4) * (ι * ι * (1 - E)) - (τ * ι * E + τ ^ 2 * E) := by ring
  have hPabs : |(3 / 4) * (ι * ι) + (-(3 / 4) * (ι * ι) - τ * ι - τ ^ 2) * E| ≤ 3 * (τ * ι) := by
    rw [hP, abs_le]
    constructor <;> linarith
  rw [abs_mul, abs_of_nonneg hq]
  calc q * |(3 / 4) * (ι * ι) + (-(3 / 4) * (ι * ι) - τ * ι - τ ^ 2) * E|
      ≤ q * (3 * (τ * ι)) := mul_le_mul_of_nonneg_left hPabs hq
    _ = 3 * τ * q * ι := by ring

/-- Algebra for `w_3`: `|q(-(15/8)ι³ + ((15/8)ι³ + (9/4)τι² + (3/2)τ²ι + τ³)E)| ≤ 6 τ q ι²`. -/
private lemma alg_W3 {q s ι τ E : ℝ} (hq : 0 ≤ q) (hι : 0 ≤ ι) (hτ : 0 ≤ τ) (hιs : s * ι = 1)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1) (hE3 : 1 - E ≤ τ * s) (hE4 : τ * s * E ≤ 1)
    (hE5 : (τ * s) ^ 2 * E ≤ 2) :
    |q * (-(15 / 8) * (ι * ι * ι) + ((15 / 8) * (ι * ι * ι) + (9 / 4) * τ * (ι * ι) +
      (3 / 2) * τ ^ 2 * ι + τ ^ 3) * E)| ≤ 6 * τ * q * (ι * ι) := by
  have hτii : 0 ≤ τ * (ι * ι) := mul_nonneg hτ (mul_nonneg hι hι)
  have g1 : ι * ι * ι * (1 - E) ≤ τ * (ι * ι) := by
    have h1 : ι * ι * ι * (1 - E) ≤ ι * ι * ι * (τ * s) :=
      mul_le_mul_of_nonneg_left hE3 (mul_nonneg (mul_nonneg hι hι) hι)
    have e : ι * ι * ι * (τ * s) = τ * (ι * ι) := by linear_combination (τ * (ι * ι)) * hιs
    linarith
  have g0 : 0 ≤ ι * ι * ι * (1 - E) :=
    mul_nonneg (mul_nonneg (mul_nonneg hι hι) hι) (by linarith)
  have g2 : τ * (ι * ι) * E ≤ τ * (ι * ι) := mul_le_of_le_one_right hτii hE1
  have g3 : τ ^ 2 * ι * E ≤ τ * (ι * ι) := by
    have e : τ ^ 2 * ι * E = τ * (ι * ι) * (τ * s * E) := by
      linear_combination (-(τ ^ 2 * ι * E)) * hιs
    have h1 : τ * (ι * ι) * (τ * s * E) ≤ τ * (ι * ι) * 1 := mul_le_mul_of_nonneg_left hE4 hτii
    linarith
  have g4 : τ ^ 3 * E ≤ 2 * (τ * (ι * ι)) := by
    have e : τ ^ 3 * E = τ * (ι * ι) * ((τ * s) ^ 2 * E) := by
      linear_combination (-(τ ^ 3 * E) * (s * ι + 1)) * hιs
    have h1 : τ * (ι * ι) * ((τ * s) ^ 2 * E) ≤ τ * (ι * ι) * 2 :=
      mul_le_mul_of_nonneg_left hE5 hτii
    linarith
  have hY0 : 0 ≤ (9 / 4) * τ * (ι * ι) * E + (3 / 2) * τ ^ 2 * ι * E + τ ^ 3 * E := by
    have a1 : 0 ≤ (9 / 4) * τ * (ι * ι) * E :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hτ) (mul_nonneg hι hι)) hE0
    have a2 : 0 ≤ (3 / 2) * τ ^ 2 * ι * E :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg τ)) hι) hE0
    have a3 : 0 ≤ τ ^ 3 * E := mul_nonneg (pow_nonneg hτ 3) hE0
    linarith
  have hP : -(15 / 8) * (ι * ι * ι) + ((15 / 8) * (ι * ι * ι) + (9 / 4) * τ * (ι * ι) +
      (3 / 2) * τ ^ 2 * ι + τ ^ 3) * E =
      -((15 / 8) * (ι * ι * ι * (1 - E))) +
        ((9 / 4) * τ * (ι * ι) * E + (3 / 2) * τ ^ 2 * ι * E + τ ^ 3 * E) := by ring
  have hPabs : |-(15 / 8) * (ι * ι * ι) + ((15 / 8) * (ι * ι * ι) + (9 / 4) * τ * (ι * ι) +
      (3 / 2) * τ ^ 2 * ι + τ ^ 3) * E| ≤ 6 * (τ * (ι * ι)) := by
    rw [hP, abs_le]
    constructor <;> linarith
  rw [abs_mul, abs_of_nonneg hq]
  calc q * |-(15 / 8) * (ι * ι * ι) + ((15 / 8) * (ι * ι * ι) + (9 / 4) * τ * (ι * ι) +
        (3 / 2) * τ ^ 2 * ι + τ ^ 3) * E|
      ≤ q * (6 * (τ * (ι * ι))) := mul_le_mul_of_nonneg_left hPabs hq
    _ = 6 * τ * q * (ι * ι) := by ring

/-- Algebra for `w_2` family: `|u E| ≤ u`. -/
private lemma alg_V0 {u E : ℝ} (hu : 0 ≤ u) (hE0 : 0 ≤ E) (hE1 : E ≤ 1) : |u * E| ≤ u := by
  rw [abs_mul, abs_of_nonneg hu, abs_of_nonneg hE0]
  exact mul_le_of_le_one_right hu hE1

/-- Algebra for `w_2'`: `|uE(ι/2 - τ)| ≤ 2 u ι`. -/
private lemma alg_V1 {u s ι τ E : ℝ} (hu : 0 ≤ u) (hι : 0 ≤ ι) (hτ : 0 ≤ τ) (hιs : s * ι = 1)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1) (hE4 : τ * s * E ≤ 1) :
    |u * E * (ι / 2 - τ)| ≤ 2 * (u * ι) := by
  have hab : |ι / 2 - τ| ≤ ι / 2 + τ := abs_le.2 ⟨by linarith, by linarith⟩
  have hE' : 0 ≤ u * E := mul_nonneg hu hE0
  have hui : 0 ≤ u * ι := mul_nonneg hu hι
  rw [abs_mul, abs_of_nonneg hE']
  have h1 : u * E * |ι / 2 - τ| ≤ u * E * (ι / 2 + τ) := mul_le_mul_of_nonneg_left hab hE'
  have e2 : u * τ * E = u * ι * (τ * s * E) := by linear_combination (-(u * τ * E)) * hιs
  have hA : u * ι * (τ * s * E) ≤ u * ι := mul_le_of_le_one_right hui hE4
  have hB : u * ι * E ≤ u * ι := mul_le_of_le_one_right hui hE1
  have e3 : u * E * (ι / 2 + τ) = (1 / 2) * (u * ι * E) + u * τ * E := by ring
  linarith [h1, e2, e3, hA, hB, hui]

/-- Algebra for `w_2''`: `|uE(-(ι²)/4 - τι + τ²)| ≤ 4 u ι²`. -/
private lemma alg_V2 {u s ι τ E : ℝ} (hu : 0 ≤ u) (hι : 0 ≤ ι) (hτ : 0 ≤ τ) (hιs : s * ι = 1)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1) (hE4 : τ * s * E ≤ 1) (hE5 : (τ * s) ^ 2 * E ≤ 2) :
    |u * E * (-(ι * ι) / 4 - τ * ι + τ ^ 2)| ≤ 4 * (u * (ι * ι)) := by
  have hιι : 0 ≤ ι * ι := mul_nonneg hι hι
  have hτι : 0 ≤ τ * ι := mul_nonneg hτ hι
  have hP : |-(ι * ι) / 4 - τ * ι + τ ^ 2| ≤ (ι * ι) / 4 + τ * ι + τ ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg τ]
  have hE' : 0 ≤ u * E := mul_nonneg hu hE0
  rw [abs_mul, abs_of_nonneg hE']
  have h1 : u * E * |-(ι * ι) / 4 - τ * ι + τ ^ 2| ≤ u * E * ((ι * ι) / 4 + τ * ι + τ ^ 2) :=
    mul_le_mul_of_nonneg_left hP hE'
  have e1 : u * E * ((ι * ι) / 4 + τ * ι + τ ^ 2) =
      (1 / 4) * (u * (ι * ι) * E) + u * (τ * ι * E) + u * (τ ^ 2 * E) := by ring
  have k1 : u * (ι * ι) * E ≤ u * (ι * ι) := mul_le_of_le_one_right (mul_nonneg hu hιι) hE1
  have k2 : u * (τ * ι * E) ≤ u * (ι * ι) := by
    have e : τ * ι * E = (ι * ι) * (τ * s * E) := by linear_combination (-(τ * ι * E)) * hιs
    have h2 : (ι * ι) * (τ * s * E) ≤ (ι * ι) * 1 := mul_le_mul_of_nonneg_left hE4 hιι
    calc u * (τ * ι * E) = u * ((ι * ι) * (τ * s * E)) := by rw [e]
      _ ≤ u * ((ι * ι) * 1) := mul_le_mul_of_nonneg_left h2 hu
      _ = u * (ι * ι) := by ring
  have k3 : u * (τ ^ 2 * E) ≤ 2 * (u * (ι * ι)) := by
    have e : τ ^ 2 * E = (ι * ι) * ((τ * s) ^ 2 * E) := by
      linear_combination (-(τ ^ 2 * E) * (s * ι + 1)) * hιs
    have h2 : (ι * ι) * ((τ * s) ^ 2 * E) ≤ (ι * ι) * 2 := mul_le_mul_of_nonneg_left hE5 hιι
    calc u * (τ ^ 2 * E) = u * ((ι * ι) * ((τ * s) ^ 2 * E)) := by rw [e]
      _ ≤ u * ((ι * ι) * 2) := mul_le_mul_of_nonneg_left h2 hu
      _ = 2 * (u * (ι * ι)) := by ring
  have k0 : 0 ≤ u * (ι * ι) := mul_nonneg hu hιι
  linarith [h1, e1, k1, k2, k3, k0]

/-! #### The rpow identities and the pointwise bounds of the families -/

private lemma rpow_neg_half_mul_s {s : ℝ} (hs : 0 < s) :
    s ^ (-(1 / 2) : ℝ) * s = s ^ (1 / 2 : ℝ) := by
  rw [← Real.rpow_add_one hs.ne']
  norm_num

private lemma rpow_half_mul_inv {s : ℝ} (hs : 0 < s) :
    s ^ (1 / 2 : ℝ) * s⁻¹ = s ^ (-(1 / 2) : ℝ) := by
  rw [← div_eq_mul_inv, ← Real.rpow_sub_one hs.ne']
  norm_num

private lemma rpow_neg_half_mul_inv {s : ℝ} (hs : 0 < s) :
    s ^ (-(1 / 2) : ℝ) * s⁻¹ = s ^ (-(3 / 2) : ℝ) := by
  rw [← div_eq_mul_inv, ← Real.rpow_sub_one hs.ne']
  norm_num

private lemma rpow_neg_three_half_mul_inv {s : ℝ} (hs : 0 < s) :
    s ^ (-(3 / 2) : ℝ) * s⁻¹ = s ^ (-(5 / 2) : ℝ) := by
  rw [← div_eq_mul_inv, ← Real.rpow_sub_one hs.ne']
  norm_num

/-- `|w_0(s)| ≤ τ s^{1/2}` for `τ ≥ 0`. -/
theorem stepW0_bound {τ s : ℝ} (hτ : 0 ≤ τ) (hs : 0 < s) :
    |stepW0 τ s| ≤ τ * s ^ (1 / 2 : ℝ) := by
  obtain ⟨-, hE1, hE3, -, -⟩ := expFacts hτ hs.le
  have hq : 0 ≤ s ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hs.le _
  have h := alg_W0 hq hE1 hE3
  unfold stepW0
  calc |s ^ (-(1 / 2) : ℝ) * (1 - Real.exp (-(τ * s)))| ≤ τ * s * s ^ (-(1 / 2) : ℝ) := h
    _ = τ * (s ^ (-(1 / 2) : ℝ) * s) := by ring
    _ = τ * s ^ (1 / 2 : ℝ) := by rw [rpow_neg_half_mul_s hs]

/-- `|w_1(s)| ≤ τ s^{-1/2}` for `0 ≤ τ`. -/
theorem stepW1_bound {τ s : ℝ} (hτ : 0 ≤ τ) (hs : 0 < s) :
    |stepW1 τ s| ≤ τ * s ^ (-(1 / 2) : ℝ) := by
  obtain ⟨hE0, hE1, hE3, -, -⟩ := expFacts hτ hs.le
  have hq : 0 ≤ s ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hs.le _
  have hι : 0 ≤ s⁻¹ := inv_nonneg.2 hs.le
  have hιs : s * s⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  unfold stepW1
  exact alg_W1 hq hι hτ hιs hE0 hE1 hE3

/-- `(X^{-1/2}/2)^a = 2^{-a} X^{-a/2}` for `X > 0`. -/
private lemma rpow_h_eq {X : ℝ} (hX : 0 < X) (a : ℝ) :
    (X ^ (-(1 / 2) : ℝ) / 2) ^ a = 2 ^ (-a) * X ^ (-(a / 2)) := by
  have e : (-(1 / 2) : ℝ) * a = -(a / 2) := by ring
  rw [Real.div_rpow (Real.rpow_nonneg hX.le _) (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_mul hX.le, e,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) a]
  ring

/-- `(X/2)^a = 2^{-a} X^a` for `X > 0`. -/
private lemma rpow_half_div {X : ℝ} (hX : 0 < X) (a : ℝ) : (X / 2) ^ a = 2 ^ (-a) * X ^ a := by
  rw [Real.div_rpow hX.le (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) a]
  ring

/-- The two tail constants at the paper's split `h = X^{-1/2}/2`, for `X ≥ 1`:
`∫_h^∞ s^{-3/2}|C(s-X)| ≤ K₃ X^{-1}` and `∫_h^∞ s^{-5/2}|C(s-X)| ≤ K₅ X^{-1/2}`. -/
private lemma tail_consts :
    ∃ K3 K5 : ℝ, 0 ≤ K3 ∧ 0 ≤ K5 ∧ ∀ X : ℝ, 1 ≤ X →
      (∫ s in Ioi (X ^ (-(1 / 2) : ℝ) / 2), s ^ (-(3 / 2) : ℝ) * |airyPrimC (s - X)|) ≤
        K3 * X ^ (-1 : ℝ) ∧
      (∫ s in Ioi (X ^ (-(1 / 2) : ℝ) / 2), s ^ (-(5 / 2) : ℝ) * |airyPrimC (s - X)|) ≤
        K5 * X ^ (-(1 / 2) : ℝ) := by
  obtain ⟨M, hM, hC⟩ := airyBC_primC_dom
  have hG0 : 0 ≤ |∫ t : ℝ, (1 + |t|) ^ (-(5 / 4) : ℝ)| := abs_nonneg _
  refine ⟨M * (2 ^ (5 / 4 : ℝ) * 2 * 2 ^ (1 / 2 : ℝ)) + 2 ^ (3 / 2 : ℝ) * (M * |∫ t : ℝ, (1 + |t|) ^ (-(5 / 4) : ℝ)|),
    M * (2 ^ (5 / 4 : ℝ) * ((2 / 3) * 2 ^ (3 / 2 : ℝ))) +
      2 ^ (5 / 2 : ℝ) * (M * |∫ t : ℝ, (1 + |t|) ^ (-(5 / 4) : ℝ)|), ?_, ?_, fun X hX1 => ?_⟩
  · exact add_nonneg (mul_nonneg hM (by positivity)) (mul_nonneg (by positivity) (mul_nonneg hM hG0))
  · exact add_nonneg (mul_nonneg hM (by positivity)) (mul_nonneg (by positivity) (mul_nonneg hM hG0))
  have hX0 : 0 < X := by linarith
  have hsmall : X ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX1 (by norm_num)
  have hpos : 0 < X ^ (-(1 / 2) : ℝ) / 2 := div_pos (Real.rpow_pos_of_pos hX0 _) (by norm_num)
  have hle : X ^ (-(1 / 2) : ℝ) / 2 ≤ X / 2 := by linarith
  have hT32 := airyBC_tail_rpow (p := 3 / 2) (by norm_num) hpos hle hM hC
  have hT52 := airyBC_tail_rpow (p := 5 / 2) (by norm_num) hpos hle hM hC
  have hI32 : ∫ s in Ioi (X ^ (-(1 / 2) : ℝ) / 2), s ^ (-(3 / 2) : ℝ) =
      2 * (X ^ (-(1 / 2) : ℝ) / 2) ^ (-(1 / 2) : ℝ) := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) hpos]
    have e : (-(3 / 2) : ℝ) + 1 = -(1 / 2) := by norm_num
    rw [e]
    ring
  have hI52 : ∫ s in Ioi (X ^ (-(1 / 2) : ℝ) / 2), s ^ (-(5 / 2) : ℝ) =
      (2 / 3) * (X ^ (-(1 / 2) : ℝ) / 2) ^ (-(3 / 2) : ℝ) := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) hpos]
    have e : (-(5 / 2) : ℝ) + 1 = -(3 / 2) := by norm_num
    rw [e]
    ring
  have hh12 : (X ^ (-(1 / 2) : ℝ) / 2) ^ (-(1 / 2) : ℝ) = 2 ^ (1 / 2 : ℝ) * X ^ (1 / 4 : ℝ) := by
    rw [rpow_h_eq hX0]
    norm_num
  have hh32 : (X ^ (-(1 / 2) : ℝ) / 2) ^ (-(3 / 2) : ℝ) = 2 ^ (3 / 2 : ℝ) * X ^ (3 / 4 : ℝ) := by
    rw [rpow_h_eq hX0]
    norm_num
  have hx54 : (X / 2) ^ (-(5 / 4) : ℝ) = 2 ^ (5 / 4 : ℝ) * X ^ (-(5 / 4) : ℝ) := by
    rw [rpow_half_div hX0]
    norm_num
  have hx32 : (X / 2) ^ (-(3 / 2) : ℝ) = 2 ^ (3 / 2 : ℝ) * X ^ (-(3 / 2) : ℝ) := by
    rw [rpow_half_div hX0]
    norm_num
  have hx52 : (X / 2) ^ (-(5 / 2) : ℝ) = 2 ^ (5 / 2 : ℝ) * X ^ (-(5 / 2) : ℝ) := by
    rw [rpow_half_div hX0]
    norm_num
  have hXe1 : X ^ (-(5 / 4) : ℝ) * X ^ (1 / 4 : ℝ) = X ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hX0]
    norm_num
  have hXe2 : X ^ (-(5 / 4) : ℝ) * X ^ (3 / 4 : ℝ) = X ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_add hX0]
    norm_num
  have hXe3 : X ^ (-(3 / 2) : ℝ) ≤ X ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have hXe4 : X ^ (-(5 / 2) : ℝ) ≤ X ^ (-(1 / 2) : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have hXp3 : 0 ≤ X ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg hX0.le _
  have hXp5 : 0 ≤ X ^ (-(5 / 2) : ℝ) := Real.rpow_nonneg hX0.le _
  have hMG : M * (∫ t : ℝ, (1 + |t|) ^ (-(5 / 4) : ℝ)) ≤ M * |∫ t : ℝ, (1 + |t|) ^ (-(5 / 4) : ℝ)| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) hM
  constructor
  · have key1 : M * (2 ^ (5 / 4 : ℝ) * X ^ (-(5 / 4) : ℝ)) * (2 * (2 ^ (1 / 2 : ℝ) * X ^ (1 / 4 : ℝ))) =
        (M * (2 ^ (5 / 4 : ℝ) * 2 * 2 ^ (1 / 2 : ℝ))) * X ^ (-1 : ℝ) := by
      rw [← hXe1]
      ring
    have key2 : 2 ^ (3 / 2 : ℝ) * X ^ (-(3 / 2) : ℝ) * M * (∫ t : ℝ, (1 + |t|) ^ (-(5 / 4) : ℝ)) ≤
        (2 ^ (3 / 2 : ℝ) * (M * |∫ t : ℝ, (1 + |t|) ^ (-(5 / 4) : ℝ)|)) * X ^ (-1 : ℝ) := by
      calc 2 ^ (3 / 2 : ℝ) * X ^ (-(3 / 2) : ℝ) * M * (∫ t : ℝ, (1 + |t|) ^ (-(5 / 4) : ℝ))
          = (2 ^ (3 / 2 : ℝ) * X ^ (-(3 / 2) : ℝ)) * (M * ∫ t : ℝ, (1 + |t|) ^ (-(5 / 4) : ℝ)) := by
            ring
        _ ≤ (2 ^ (3 / 2 : ℝ) * X ^ (-(3 / 2) : ℝ)) * (M * |∫ t : ℝ, (1 + |t|) ^ (-(5 / 4) : ℝ)|) :=
            mul_le_mul_of_nonneg_left hMG (mul_nonneg (by positivity) hXp3)
        _ ≤ (2 ^ (3 / 2 : ℝ) * X ^ (-1 : ℝ)) * (M * |∫ t : ℝ, (1 + |t|) ^ (-(5 / 4) : ℝ)|) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXe3 (by positivity))
              (mul_nonneg hM hG0)
        _ = (2 ^ (3 / 2 : ℝ) * (M * |∫ t : ℝ, (1 + |t|) ^ (-(5 / 4) : ℝ)|)) * X ^ (-1 : ℝ) := by
            ring
    calc ∫ s in Ioi (X ^ (-(1 / 2) : ℝ) / 2), s ^ (-(3 / 2) : ℝ) * |airyPrimC (s - X)|
        ≤ M * (X / 2) ^ (-(5 / 4) : ℝ) * (∫ s in Ioi (X ^ (-(1 / 2) : ℝ) / 2), s ^ (-(3 / 2) : ℝ)) +
          (X / 2) ^ (-(3 / 2) : ℝ) * M * (∫ t : ℝ, (1 + |t|) ^ (-(5 / 4) : ℝ)) := hT32
      _ = M * (2 ^ (5 / 4 : ℝ) * X ^ (-(5 / 4) : ℝ)) * (2 * (2 ^ (1 / 2 : ℝ) * X ^ (1 / 4 : ℝ))) +
          2 ^ (3 / 2 : ℝ) * X ^ (-(3 / 2) : ℝ) * M * (∫ t : ℝ, (1 + |t|) ^ (-(5 / 4) : ℝ)) := by
          rw [hI32, hh12, hx54, hx32]
          ring
      _ ≤ K3 * X ^ (-1 : ℝ) := by
          rw [key1]
          nlinarith [key2]
  · sorry

end FormalResearch.ModularBootstrap.FiveTerm

/-- Continuity of `w_3` on `(0,∞)`. -/
theorem stepW3_continuousOn (τ : ℝ) : ContinuousOn (stepW3 τ) (Ioi 0) := by
  intro s hs
  have hs0 : s ≠ 0 := (Set.mem_Ioi.1 hs).ne'
  have hi : ContinuousAt (fun x : ℝ => x⁻¹) s := continuousAt_inv₀ hs0
  have hq : ContinuousAt (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) s :=
    Real.continuousAt_rpow_const s _ (Or.inl hs0)
  have he : ContinuousAt (fun x : ℝ => Real.exp (-(τ * x))) s :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousAt
  have hc : ContinuousAt (stepW3 τ) s := by
    unfold stepW3
    fun_prop
  exact hc.continuousWithinAt

/-- Continuity of `w_2''` on `(0,∞)`. -/
theorem stepV2_continuousOn (τ : ℝ) : ContinuousOn (stepV2 τ) (Ioi 0) := by
  intro s hs
  have hs0 : s ≠ 0 := (Set.mem_Ioi.1 hs).ne'
  have hi : ContinuousAt (fun x : ℝ => x⁻¹) s := continuousAt_inv₀ hs0
  have hu : ContinuousAt (fun x : ℝ => x ^ (1 / 2 : ℝ)) s :=
    Real.continuousAt_rpow_const s _ (Or.inl hs0)
  have he : ContinuousAt (fun x : ℝ => Real.exp (-(τ * x))) s :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousAt
  have hc : ContinuousAt (stepV2 τ) s := by
    unfold stepV2
    fun_prop
  exact hc.continuousWithinAt

/-- `|w_2(s)| ≤ 3 τ s^{-3/2}` for `0 ≤ τ`. -/
theorem stepW2_bound {τ s : ℝ} (hτ : 0 ≤ τ) (hs : 0 < s) :
    |stepW2 τ s| ≤ 3 * τ * s ^ (-(3 / 2) : ℝ) := by
  obtain ⟨hE0, hE1, hE3, hE4, -⟩ := expFacts hτ hs.le
  have hq : 0 ≤ s ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hs.le _
  have hι : 0 ≤ s⁻¹ := inv_nonneg.2 hs.le
  have hιs : s * s⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  have h := alg_W2 hq hι hτ hιs hE0 hE1 hE3 hE4
  unfold stepW2
  calc _ ≤ 3 * τ * s ^ (-(1 / 2) : ℝ) * s⁻¹ := h
    _ = 3 * τ * (s ^ (-(1 / 2) : ℝ) * s⁻¹) := by ring
    _ = 3 * τ * s ^ (-(3 / 2) : ℝ) := by rw [rpow_neg_half_mul_inv hs]

/-- `|w_3(s)| ≤ 6 τ s^{-5/2}` for `0 ≤ τ`. -/
theorem stepW3_bound {τ s : ℝ} (hτ : 0 ≤ τ) (hs : 0 < s) :
    |stepW3 τ s| ≤ 6 * τ * s ^ (-(5 / 2) : ℝ) := by
  obtain ⟨hE0, hE1, hE3, hE4, hE5⟩ := expFacts hτ hs.le
  have hq : 0 ≤ s ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hs.le _
  have hι : 0 ≤ s⁻¹ := inv_nonneg.2 hs.le
  have hιs : s * s⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  have h := alg_W3 hq hι hτ hιs hE0 hE1 hE3 hE4 hE5
  unfold stepW3
  calc _ ≤ 6 * τ * s ^ (-(1 / 2) : ℝ) * (s⁻¹ * s⁻¹) := h
    _ = 6 * τ * ((s ^ (-(1 / 2) : ℝ) * s⁻¹) * s⁻¹) := by ring
    _ = 6 * τ * (s ^ (-(3 / 2) : ℝ) * s⁻¹) := by rw [rpow_neg_half_mul_inv hs]
    _ = 6 * τ * s ^ (-(5 / 2) : ℝ) := by rw [rpow_neg_three_half_mul_inv hs]

/-- `|w_2-family, value| ≤ s^{1/2}`. -/
theorem stepV0_bound {τ s : ℝ} (hτ : 0 ≤ τ) (hs : 0 < s) :
    |stepV0 τ s| ≤ s ^ (1 / 2 : ℝ) := by
  obtain ⟨hE0, hE1, -, -, -⟩ := expFacts hτ hs.le
  unfold stepV0
  exact alg_V0 (Real.rpow_nonneg hs.le _) hE0 hE1

/-- `|(w_2)'| ≤ 2 s^{-1/2}`. -/
theorem stepV1_bound {τ s : ℝ} (hτ : 0 ≤ τ) (hs : 0 < s) :
    |stepV1 τ s| ≤ 2 * s ^ (-(1 / 2) : ℝ) := by
  obtain ⟨hE0, hE1, -, hE4, -⟩ := expFacts hτ hs.le
  have hu : 0 ≤ s ^ (1 / 2 : ℝ) := Real.rpow_nonneg hs.le _
  have hι : 0 ≤ s⁻¹ := inv_nonneg.2 hs.le
  have hιs : s * s⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  have h := alg_V1 hu hι hτ hιs hE0 hE1 hE4
  unfold stepV1
  calc _ ≤ 2 * (s ^ (1 / 2 : ℝ) * s⁻¹) := h
    _ = 2 * s ^ (-(1 / 2) : ℝ) := by rw [rpow_half_mul_inv hs]

/-- `|(w_2)''| ≤ 4 s^{-3/2}`. -/
theorem stepV2_bound {τ s : ℝ} (hτ : 0 ≤ τ) (hs : 0 < s) :
    |stepV2 τ s| ≤ 4 * s ^ (-(3 / 2) : ℝ) := by
  obtain ⟨hE0, hE1, -, hE4, hE5⟩ := expFacts hτ hs.le
  have hu : 0 ≤ s ^ (1 / 2 : ℝ) := Real.rpow_nonneg hs.le _
  have hι : 0 ≤ s⁻¹ := inv_nonneg.2 hs.le
  have hιs : s * s⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  have h := alg_V2 hu hι hτ hιs hE0 hE1 hE4 hE5
  unfold stepV2
  calc _ ≤ 4 * (s ^ (1 / 2 : ℝ) * (s⁻¹ * s⁻¹)) := h
    _ = 4 * ((s ^ (1 / 2 : ℝ) * s⁻¹) * s⁻¹) := by ring
    _ = 4 * (s ^ (-(1 / 2) : ℝ) * s⁻¹) := by rw [rpow_half_mul_inv hs]
    _ = 4 * s ^ (-(3 / 2) : ℝ) := by rw [rpow_neg_half_mul_inv hs]

end FormalResearch.ModularBootstrap.FiveTerm
