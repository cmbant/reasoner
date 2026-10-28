import FormalResearch.FourQubitEntropy.SevenQubitConseqEnvelope

/-!
# Monotonicity and convexity of the envelope `g₈`

`g₈` is antitone on `[1/8, 1]` and convex on `[1/8, 107/289]` (the second half of
`lem:seven-fixed-purity-envelope`).

With `s = √(7(8p-1))` (so `t = (1+s)/8`) and `L(s) = ln(7(1+s)/(7-s))` one has
`g₈'(p) = -(7/2) L(s)/s`, and `g₈'` is nondecreasing as long as `L(s)/s` is nonincreasing, i.e.
`s L'(s) ≤ L(s)` with `L' = 8/((1+s)(7-s))`.  With `y = 4s/(7+3s)` one has
`7(1+s)/(7-s) = (1+y)/(1-y)`, and the series bound `ln((1+y)/(1-y)) ≥ 2y + 2y³/3` reduces
`s L' ≤ L` to the polynomial `147 + (343/3)s + 17 s² - (43/3)s³ ≥ 0`, true for `s ≤ 63/17`
(`p = 107/289`, the paper's `r = 10`).
-/

open Real Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitConseq

noncomputable def sOf (p : ℝ) : ℝ := Real.sqrt (7 * (8 * p - 1))

noncomputable def Lg (s : ℝ) : ℝ := log 7 + log (1 + s) - log (7 - s)

noncomputable def Hs (s : ℝ) : ℝ := Gsp ((1 + s) / 8)

theorem g8_eq_Hs (p : ℝ) : g8 p = Hs (sOf p) := rfl

theorem hasDerivAt_Gsp {a : ℝ} (h0 : 0 < a) (h1 : a < 1) :
    HasDerivAt Gsp (log ((1 - a) / 7) - log a) a := by
  have hb : 0 < (1 - a) / 7 := by linarith
  have d1 := Real.hasDerivAt_negMulLog h0.ne'
  have d2 : HasDerivAt (fun x => (1 - x) / 7) (-1 / 7) a := by
    have := ((hasDerivAt_id a).const_sub 1).div_const 7
    simpa using this
  have d3 := (Real.hasDerivAt_negMulLog hb.ne').comp a d2
  have := d1.add (d3.const_mul 7)
  refine this.congr_deriv ?_
  ring

theorem hasDerivAt_Hs {s : ℝ} (h0 : -1 < s) (h1 : s < 7) : HasDerivAt Hs (-Lg s / 8) s := by
  have ha0 : 0 < (1 + s) / 8 := by linarith
  have ha1 : (1 + s) / 8 < 1 := by linarith
  have d1 : HasDerivAt (fun x => (1 + x) / 8) (1 / 8) s := by
    have := ((hasDerivAt_id s).const_add 1).div_const 8
    simpa using this
  have := (hasDerivAt_Gsp ha0 ha1).comp s d1
  refine this.congr_deriv ?_
  unfold Lg
  have e1 : log ((1 - (1 + s) / 8) / 7) = log (7 - s) - log 56 := by
    rw [← Real.log_div (by linarith) (by norm_num)]; congr 1; field_simp; ring
  have e2 : log ((1 + s) / 8) = log (1 + s) - log 8 := by
    rw [Real.log_div (by linarith) (by norm_num)]
  have e3 : log 56 = log 7 + log 8 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e1, e2, e3]
  ring

theorem hasDerivAt_sOf {p : ℝ} (hp : 1 / 8 < p) : HasDerivAt sOf (28 / sOf p) p := by
  have hu : 0 < 7 * (8 * p - 1) := by linarith
  have d1 : HasDerivAt (fun p => 7 * (8 * p - 1)) 56 p := by
    have := (((hasDerivAt_id p).const_mul 8).sub_const 1).const_mul 7
    refine this.congr_deriv ?_
    norm_num
  have := (Real.hasDerivAt_sqrt hu.ne').comp p d1
  unfold sOf
  refine this.congr_deriv ?_
  have : 0 < Real.sqrt (7 * (8 * p - 1)) := Real.sqrt_pos.2 hu
  field_simp
  ring

theorem sOf_pos {p : ℝ} (hp : 1 / 8 < p) : 0 < sOf p := Real.sqrt_pos.2 (by linarith)

theorem sOf_lt_seven {p : ℝ} (hp : p < 1) : sOf p < 7 := by
  unfold sOf
  rw [Real.sqrt_lt' (by norm_num)]; linarith

theorem hasDerivAt_g8 {p : ℝ} (h0 : 1 / 8 < p) (h1 : p < 1) :
    HasDerivAt g8 (-Lg (sOf p) / 8 * (28 / sOf p)) p := by
  have hs0 := sOf_pos h0
  have hs7 := sOf_lt_seven h1
  exact (hasDerivAt_Hs (by linarith) hs7).comp p (hasDerivAt_sOf h0)

theorem Lg_nonneg {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 7) : 0 ≤ Lg s := by
  unfold Lg
  have : log (7 - s) ≤ log 7 + log (1 + s) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) (by nlinarith)
  linarith

theorem g8_continuousOn : Continuous g8 := by
  unfold g8 Gsp tOf
  have := Real.continuous_negMulLog
  fun_prop

/-- `g₈` is antitone on `[1/8, 1]`. -/
theorem g8_antitoneOn : AntitoneOn g8 (Set.Icc (1 / 8) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) g8_continuousOn.continuousOn
  · intro p hp
    rw [interior_Icc] at hp
    exact (hasDerivAt_g8 hp.1 hp.2).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    rw [(hasDerivAt_g8 hp.1 hp.2).deriv]
    have hs0 := sOf_pos hp.1
    have hL := Lg_nonneg hs0.le (sOf_lt_seven hp.2)
    have : 0 ≤ Lg (sOf p) / 8 * (28 / sOf p) := by positivity
    have e : -Lg (sOf p) / 8 * (28 / sOf p) = -(Lg (sOf p) / 8 * (28 / sOf p)) := by ring
    linarith

/-! ### Convexity -/

theorem hasDerivAt_Lg {s : ℝ} (h0 : -1 < s) (h1 : s < 7) :
    HasDerivAt Lg (1 / (1 + s) + 1 / (7 - s)) s := by
  have d1 : HasDerivAt (fun x => 1 + x) 1 s := by simpa using (hasDerivAt_id s).const_add 1
  have d2 : HasDerivAt (fun x => 7 - x) (-1) s := by simpa using (hasDerivAt_id s).const_sub 7
  have h1' := (Real.hasDerivAt_log (by linarith : (1 + s) ≠ 0))
  have h2' := (Real.hasDerivAt_log (by linarith : (7 - s) ≠ 0))
  have := (((h1'.comp s d1).const_add (log 7))).sub (h2'.comp s d2)
  unfold Lg
  refine this.congr_deriv ?_
  field_simp
  ring

/-- The key log inequality `s L'(s) ≤ L(s)` on `(0, 63/17]`. -/
theorem Lg_ge {s : ℝ} (h0 : 0 < s) (h1 : s ≤ 63 / 17) :
    s * (1 / (1 + s) + 1 / (7 - s)) ≤ Lg s := by
  set y : ℝ := 4 * s / (7 + 3 * s) with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y < 1 := by
    rw [hy, div_lt_one (by positivity)]; linarith
  have hlog := Real.sum_range_le_log_div hy0 hy1 2
  have hr : (1 + y) / (1 - y) = 7 * (1 + s) / (7 - s) := by
    rw [hy]
    have h7 : (7 + 3 * s) ≠ 0 := by positivity
    have h8 : (7 - s) ≠ 0 := by linarith
    have e1 : 1 + 4 * s / (7 + 3 * s) = 7 * (1 + s) / (7 + 3 * s) := by field_simp; ring
    have e2 : 1 - 4 * s / (7 + 3 * s) = (7 - s) / (7 + 3 * s) := by field_simp; ring
    rw [e1, e2, div_div_div_cancel_right₀ h7]
  rw [hr] at hlog
  have hL : Lg s = log (7 * (1 + s) / (7 - s)) := by
    unfold Lg
    rw [Real.log_div (by positivity) (by linarith), Real.log_mul (by norm_num) (by linarith)]
  rw [hL]
  simp [Finset.sum_range_succ] at hlog
  have hpoly : s * (1 / (1 + s) + 1 / (7 - s)) ≤ 2 * (y + y ^ 3 / 3) := by
    rw [hy]
    have h7 : 0 < 7 + 3 * s := by positivity
    have h8 : 0 < 7 - s := by linarith
    have h9 : 0 < 1 + s := by linarith
    rw [div_add_div _ _ h9.ne' h8.ne', ← mul_div_assoc, div_le_iff₀ (by positivity)]
    have e : 2 * (4 * s / (7 + 3 * s) + (4 * s / (7 + 3 * s)) ^ 3 / 3) =
        2 * (4 * s * (3 * (7 + 3 * s) ^ 2 + 16 * s ^ 2)) / (3 * (7 + 3 * s) ^ 3) := by
      field_simp
      ring
    rw [e, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [mul_pos h0 h0, mul_pos (mul_pos h0 h0) h0, pow_pos h0 4,
      mul_nonneg h0.le (sub_nonneg.2 h1), mul_nonneg (mul_nonneg h0.le h0.le) (sub_nonneg.2 h1),
      mul_nonneg (mul_nonneg (mul_nonneg h0.le h0.le) h0.le) (sub_nonneg.2 h1)]
  linarith

theorem Phi_antitone : AntitoneOn (fun s => Lg s / s) (Set.Ioo 0 (63 / 17)) := by
  have hd : ∀ s ∈ Set.Ioo (0 : ℝ) (63 / 17), HasDerivAt (fun s => Lg s / s)
      (((1 / (1 + s) + 1 / (7 - s)) * s - Lg s * 1) / s ^ 2) s := by
    intro s hs
    have h0 := hs.1
    have h1 : s < 7 := by linarith [hs.2]
    exact (hasDerivAt_Lg (by linarith) h1).div (hasDerivAt_id s) h0.ne'
  apply antitoneOn_of_deriv_nonpos (convex_Ioo _ _)
  · intro s hs
    exact (hd s hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioo] at hs
    exact (hd s hs).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ioo] at hs
    rw [(hd s hs).deriv]
    have := Lg_ge hs.1 hs.2.le
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    nlinarith

/-- **`lem:seven-fixed-purity-envelope` (convexity).** `g₈` is convex on `[1/8, 107/289]`. -/
theorem g8_convexOn : ConvexOn ℝ (Set.Icc (1 / 8) (107 / 289)) g8 := by
  apply MonotoneOn.convexOn_of_deriv (convex_Icc _ _) g8_continuousOn.continuousOn
  · intro p hp
    rw [interior_Icc] at hp
    exact (hasDerivAt_g8 hp.1 (by linarith [hp.2])).differentiableAt.differentiableWithinAt
  · intro p hp q hq hpq
    rw [interior_Icc] at hp hq
    have hp1 : p < 1 := by linarith [hp.2]
    have hq1 : q < 1 := by linarith [hq.2]
    rw [(hasDerivAt_g8 hp.1 hp1).deriv, (hasDerivAt_g8 hq.1 hq1).deriv]
    have hsp := sOf_pos hp.1
    have hsq := sOf_pos hq.1
    have hlt : sOf p ≤ sOf q := Real.sqrt_le_sqrt (by linarith)
    have hq63 : sOf q < 63 / 17 := by
      unfold sOf
      rw [Real.sqrt_lt' (by norm_num)]
      linarith [hq.2]
    have hanti := Phi_antitone (a := sOf p) (b := sOf q) ⟨hsp, by linarith⟩ ⟨hsq, hq63⟩ hlt
    simp only at hanti
    have e : ∀ s : ℝ, -Lg s / 8 * (28 / s) = -(7 / 2) * (Lg s / s) := fun s => by ring
    rw [e, e]
    nlinarith

end FormalResearch.FourQubitEntropy.SevenQubitConseq
