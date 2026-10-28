import FormalResearch.FourQubitEntropy.SevenQubitConseqCeiling

/-!
# `lem:seven-entropy-linear-purity`: the universal dimension-eight entropy-purity slope

For every probability vector `λ` on eight points,
`3 - S(λ) ≥ (2/5)(8 ∑ λ² - 1)` (bits), i.e. in nats
`(2/5) ln 2 (8 ∑ λ² - 1) ≤ 3 ln 2 - ∑ -λ ln λ`.

Proof (`seven_qubit_entropy_compatibility.tex`, SP7-5).  `entropy_le_g8` reduces to the one-spike
spectrum `((1+7r)/8, ((1-r)/8)^7)`, where the claim is `F(r) ≥ C r²`, `F(r) = (1+7r)ln(1+7r) +
7(1-r)ln(1-r)`, `C = (112/5) ln 2`.  This file proves `F(r) ≥ C r²` on `[0,1]` by a route that
differs from the paper's 14-interval grid and needs only `ln 2, ln 3, ln 5, ln 7`:

* on `[0, 1/3]`, `(F - C r²)' ≥ 0` (a two-term `arctanh` bound), and `F - C r²` vanishes at `0`;
* on `[1/3, 1]`, four tangent lines of `F` (the elementary `x ln x` tangent inequality) at
  `τ = 3/7, 4/7, 5/7, 6/7`, where `1+7τ` and `1-τ` are products of `2,3,5,7`, each on a subinterval
  with endpoints `1/3 < 11/20 < 7/10 < 4/5 < 1`; `F - C r²` minus the tangent is a concave quadratic,
  so positivity of the tangent minus `C r²` at the two endpoints suffices (the checks are linear in
  `ln 2, ln 3, ln 5, ln 7`, which are enclosed by the `arctanh` series).

Everything is proved (no hypotheses, no `native_decide`).
-/

open Real Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitConseq

open FormalResearch.FourQubitEntropy.SevenQubitIco

namespace LinPur

/-! ### Rational enclosures of logarithms (arctanh series) -/

/-- Four-term lower `arctanh` series bound for `log x`, `x ≥ 1`. -/
theorem log_ge_lo {x : ℝ} (hx : 1 ≤ x) :
    2 * (((x - 1) / (x + 1)) + ((x - 1) / (x + 1)) ^ 3 / 3 + ((x - 1) / (x + 1)) ^ 5 / 5 +
      ((x - 1) / (x + 1)) ^ 7 / 7) ≤ log x := by
  set y := (x - 1) / (x + 1) with hy
  have hy0 : 0 ≤ y := div_nonneg (by linarith) (by linarith)
  have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
  have := Real.sum_range_le_log_div hy0 hy1 4
  have hr : (1 + y) / (1 - y) = x := by rw [hy]; field_simp; ring
  rw [hr] at this
  simp [Finset.sum_range_succ] at this
  linarith

/-- Four-term upper `arctanh` series bound for `log x`, `x ≥ 1`. -/
theorem log_ge_hi {x : ℝ} (hx : 1 ≤ x) :
    log x ≤ 2 * (((x - 1) / (x + 1)) + ((x - 1) / (x + 1)) ^ 3 / 3 + ((x - 1) / (x + 1)) ^ 5 / 5 +
      ((x - 1) / (x + 1)) ^ 7 / 7) + 2 * (((x - 1) / (x + 1)) ^ 9 / (1 - ((x - 1) / (x + 1)) ^ 2)) := by
  set y := (x - 1) / (x + 1) with hy
  have hy0 : 0 ≤ y := div_nonneg (by linarith) (by linarith)
  have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
  have := Real.log_div_le_sum_range_add hy0 hy1 4
  have hr : (1 + y) / (1 - y) = x := by rw [hy]; field_simp; ring
  rw [hr] at this
  simp [Finset.sum_range_succ] at this
  linarith

theorem log2_lo : (6931471803 / 10000000000 : ℝ) < log 2 := by
  have := Real.log_two_gt_d9; norm_num at this ⊢; linarith

theorem log2_hi : log 2 < (6931471808 / 10000000000 : ℝ) := by
  have := Real.log_two_lt_d9; norm_num at this ⊢; linarith

/-- `log 3 = log 2 + log (3/2)`. -/
theorem log3_eq : log 3 = log 2 + log (3 / 2) := by
  rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num

theorem log5_eq : log 5 = 2 * log 2 + log (5 / 4) := by
  have : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [← this, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num

theorem log7_eq : log 7 = 3 * log 2 - log (8 / 7) := by
  have h8 : log 8 = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  rw [Real.log_div (by norm_num) (by norm_num), h8]; ring

theorem log3_lo : (10986120 / 10000000 : ℝ) < log 3 := by
  have h := log_ge_lo (x := 3 / 2) (by norm_num)
  have := log2_lo
  rw [log3_eq]; norm_num at h ⊢; linarith

theorem log3_hi : log 3 < (10986140 / 10000000 : ℝ) := by
  have h := log_ge_hi (x := 3 / 2) (by norm_num)
  have := log2_hi
  rw [log3_eq]; norm_num at h ⊢; linarith

theorem log5_lo : (16094378 / 10000000 : ℝ) < log 5 := by
  have h := log_ge_lo (x := 5 / 4) (by norm_num)
  have := log2_lo
  rw [log5_eq]; norm_num at h ⊢; linarith

theorem log5_hi : log 5 < (16094380 / 10000000 : ℝ) := by
  have h := log_ge_hi (x := 5 / 4) (by norm_num)
  have := log2_hi
  rw [log5_eq]; norm_num at h ⊢; linarith

theorem log7_lo : (19459100 / 10000000 : ℝ) < log 7 := by
  have h := log_ge_hi (x := 8 / 7) (by norm_num)
  have := log2_lo
  rw [log7_eq]; norm_num at h ⊢; linarith

theorem log7_hi : log 7 < (19459102 / 10000000 : ℝ) := by
  have h := log_ge_lo (x := 8 / 7) (by norm_num)
  have := log2_hi
  rw [log7_eq]; norm_num at h ⊢; linarith

/-! ### The tangent inequality for `x ln x` and the function `F` -/

/-- `x ln x` lies above its tangent at `y > 0` (valid also at `x = 0`). -/
theorem xlogx_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    y * log y + (log y + 1) * (x - y) ≤ x * log x := by
  rcases hx.eq_or_lt with h | h
  · subst h; simp; linarith
  · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos h hy)
    rw [Real.log_div h.ne' hy.ne', inv_div] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 h.le
    have e : x * (1 - y / x) = x - y := by field_simp
    nlinarith

/-- `F(r) = (1+7r) ln(1+7r) + 7(1-r) ln(1-r)`. -/
noncomputable def Fsp (r : ℝ) : ℝ := (1 + 7 * r) * log (1 + 7 * r) + 7 * (1 - r) * log (1 - r)

theorem Fsp_tangent {a r : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Fsp a + 7 * (log (1 + 7 * a) - log (1 - a)) * (r - a) ≤ Fsp r := by
  have h1 := xlogx_tangent (x := 1 + 7 * r) (y := 1 + 7 * a) (by linarith) (by linarith)
  have h2 := xlogx_tangent (x := 1 - r) (y := 1 - a) (by linarith) (by linarith)
  unfold Fsp
  nlinarith [h1, h2]

/-- A concave quadratic (linear minus `C r²`) that is nonnegative at both endpoints is nonnegative. -/
theorem concave_nonneg {α β C l u r : ℝ} (hC : 0 ≤ C) (hl : l ≤ r) (hu : r ≤ u)
    (h1 : 0 ≤ α + β * l - C * l ^ 2) (h2 : 0 ≤ α + β * u - C * u ^ 2) :
    0 ≤ α + β * r - C * r ^ 2 := by
  by_cases hlu : l < u
  · have key : (u - l) * (α + β * r - C * r ^ 2) =
        (u - r) * (α + β * l - C * l ^ 2) + (r - l) * (α + β * u - C * u ^ 2) +
          C * ((u - l) * (r - l) * (u - r)) := by ring
    have hR : 0 ≤ (u - r) * (α + β * l - C * l ^ 2) + (r - l) * (α + β * u - C * u ^ 2) +
        C * ((u - l) * (r - l) * (u - r)) :=
      add_nonneg (add_nonneg (mul_nonneg (sub_nonneg.2 hu) h1) (mul_nonneg (sub_nonneg.2 hl) h2))
        (mul_nonneg hC (mul_nonneg (mul_nonneg (sub_nonneg.2 hlu.le) (sub_nonneg.2 hl))
          (sub_nonneg.2 hu)))
    rw [← key] at hR
    exact (mul_nonneg_iff_of_pos_left (sub_pos.2 hlu)).1 hR
  · have : r = l := le_antisymm (by linarith [not_lt.1 hlu]) hl
    subst this; exact h1

/-- One tangent piece: the tangent at `τ` minus `C r²` is nonnegative at both endpoints of `[l,u]`. -/
theorem piece {τ l u r C : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hl0 : 0 ≤ l) (hu1 : u ≤ 1)
    (hC : 0 ≤ C) (hl : l ≤ r) (hu : r ≤ u)
    (h1 : 0 ≤ Fsp τ + 7 * (log (1 + 7 * τ) - log (1 - τ)) * (l - τ) - C * l ^ 2)
    (h2 : 0 ≤ Fsp τ + 7 * (log (1 + 7 * τ) - log (1 - τ)) * (u - τ) - C * u ^ 2) :
    C * r ^ 2 ≤ Fsp r := by
  have hq := concave_nonneg (α := Fsp τ - 7 * (log (1 + 7 * τ) - log (1 - τ)) * τ)
    (β := 7 * (log (1 + 7 * τ) - log (1 - τ))) (C := C) (l := l) (u := u) (r := r) hC hl hu
    (by linarith) (by linarith)
  have ht := Fsp_tangent hτ0 hτ1 (hl0.trans hl) (hu.trans hu1)
  nlinarith [hq, ht]

/-! ### Values of `F` and `F'` at `τ = j/7` -/

theorem lg4 : log 4 = 2 * log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num

theorem lg6 : log 6 = log 2 + log 3 := by
  rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num

theorem Fsp_3_7 : Fsp (3 / 7) = 16 * log 2 - 4 * log 7 ∧
    log (1 + 7 * (3 / 7)) - log (1 - 3 / 7) = log 7 := by
  have e1 : (1 + 7 * (3 / 7) : ℝ) = 4 := by norm_num
  have e2 : (1 - 3 / 7 : ℝ) = 4 / 7 := by norm_num
  have e3 : log (4 / 7) = 2 * log 2 - log 7 := by
    rw [Real.log_div (by norm_num) (by norm_num), lg4]
  unfold Fsp
  rw [e1, e2, e3, lg4]
  constructor <;> ring

theorem Fsp_4_7 : Fsp (4 / 7) = 5 * log 5 + 3 * log 3 - 3 * log 7 ∧
    log (1 + 7 * (4 / 7)) - log (1 - 4 / 7) = log 5 - log 3 + log 7 := by
  have e1 : (1 + 7 * (4 / 7) : ℝ) = 5 := by norm_num
  have e2 : (1 - 4 / 7 : ℝ) = 3 / 7 := by norm_num
  have e3 : log (3 / 7) = log 3 - log 7 := Real.log_div (by norm_num) (by norm_num)
  unfold Fsp
  rw [e1, e2, e3]
  constructor <;> ring

theorem Fsp_5_7 : Fsp (5 / 7) = 6 * log 2 + 6 * log 3 + 2 * log 2 - 2 * log 7 ∧
    log (1 + 7 * (5 / 7)) - log (1 - 5 / 7) = log 3 + log 7 := by
  have e1 : (1 + 7 * (5 / 7) : ℝ) = 6 := by norm_num
  have e2 : (1 - 5 / 7 : ℝ) = 2 / 7 := by norm_num
  have e3 : log (2 / 7) = log 2 - log 7 := Real.log_div (by norm_num) (by norm_num)
  unfold Fsp
  rw [e1, e2, e3, lg6]
  constructor <;> ring

theorem Fsp_6_7 : Fsp (6 / 7) = 6 * log 7 ∧
    log (1 + 7 * (6 / 7)) - log (1 - 6 / 7) = 2 * log 7 := by
  have e1 : (1 + 7 * (6 / 7) : ℝ) = 7 := by norm_num
  have e2 : (1 - 6 / 7 : ℝ) = 7⁻¹ := by norm_num
  unfold Fsp
  rw [e1, e2, Real.log_inv]
  constructor <;> ring

/-! ### `F ≥ C r²` on `[1/3, 1]` -/

theorem Fsp_ge_upper {r : ℝ} (h0 : 1 / 3 ≤ r) (h1 : r ≤ 1) :
    (112 / 5) * log 2 * r ^ 2 ≤ Fsp r := by
  have hC : 0 ≤ (112 / 5) * log 2 := by have := log2_lo; positivity
  have l2 := log2_lo; have l2' := log2_hi
  have l3 := log3_lo; have l3' := log3_hi
  have l5 := log5_lo; have l5' := log5_hi
  have l7 := log7_lo; have l7' := log7_hi
  rcases le_total r (11 / 20) with ha | ha
  · obtain ⟨hF, hB⟩ := Fsp_3_7
    refine piece (τ := 3 / 7) (l := 1 / 3) (u := 11 / 20) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hC h0 ha ?_ ?_ <;> rw [hF, hB] <;> nlinarith
  rcases le_total r (7 / 10) with hb | hb
  · obtain ⟨hF, hB⟩ := Fsp_4_7
    refine piece (τ := 4 / 7) (l := 11 / 20) (u := 7 / 10) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hC ha hb ?_ ?_ <;> rw [hF, hB] <;> nlinarith
  rcases le_total r (4 / 5) with hc | hc
  · obtain ⟨hF, hB⟩ := Fsp_5_7
    refine piece (τ := 5 / 7) (l := 7 / 10) (u := 4 / 5) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hC hb hc ?_ ?_ <;> rw [hF, hB] <;> nlinarith
  · obtain ⟨hF, hB⟩ := Fsp_6_7
    refine piece (τ := 6 / 7) (l := 4 / 5) (u := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hC hc h1 ?_ ?_ <;> rw [hF, hB] <;> nlinarith

/-! ### `F ≥ C r²` on `[0, 1/3]` -/

theorem Fsp_hasDerivAt {r : ℝ} (h0 : -(1 : ℝ) / 7 < r) (h1 : r < 1) :
    HasDerivAt Fsp (7 * (log (1 + 7 * r) - log (1 - r))) r := by
  have p1 : 0 < 1 + 7 * r := by linarith
  have p2 : 0 < 1 - r := by linarith
  have a : HasDerivAt (fun r : ℝ => 1 + 7 * r) 7 r := by
    simpa using ((hasDerivAt_id r).const_mul (7 : ℝ)).const_add 1
  have b : HasDerivAt (fun r : ℝ => 1 - r) (-1) r := by
    simpa using (hasDerivAt_id r).const_sub 1
  have la := a.log p1.ne'
  have lb := b.log p2.ne'
  have h := (a.mul la).add ((b.const_mul 7).mul lb)
  have e : (7 * log (1 + 7 * r) + (1 + 7 * r) * (7 / (1 + 7 * r))) +
      (7 * -1 * log (1 - r) + 7 * (1 - r) * (-1 / (1 - r))) =
      7 * (log (1 + 7 * r) - log (1 - r)) := by
    field_simp; ring
  rw [e] at h
  exact h

theorem fprime_nonneg {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1 / 3) :
    (112 / 5) * log 2 * (2 * r) ≤ 7 * (log (1 + 7 * r) - log (1 - r)) := by
  have hs : 0 < 1 + 3 * r := by linarith
  set y := 4 * r / (1 + 3 * r) with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one hs]; linarith
  have hlog := Real.sum_range_le_log_div hy0 hy1 2
  have hr : (1 + y) / (1 - y) = (1 + 7 * r) / (1 - r) := by
    rw [hy]; field_simp; ring
  rw [hr, Real.log_div (by linarith) (by linarith)] at hlog
  simp [Finset.sum_range_succ] at hlog
  have hpoly : 4437 / 1000 * r ≤ 2 * (y + y ^ 3 / 3) := by
    have e : 2 * (y + y ^ 3 / 3) - 4437 / 1000 * r =
        r * (8 * (1 + 3 * r) ^ 2 + 128 / 3 * r ^ 2 - 4437 / 1000 * (1 + 3 * r) ^ 3) /
          (1 + 3 * r) ^ 3 := by
      rw [hy]; field_simp; ring
    have hnum : 0 ≤ 8 * (1 + 3 * r) ^ 2 + 128 / 3 * r ^ 2 - 4437 / 1000 * (1 + 3 * r) ^ 3 := by
      nlinarith [mul_nonneg h0.le (sub_nonneg.2 h1), mul_nonneg (mul_nonneg h0.le h0.le) (sub_nonneg.2 h1)]
    have : 0 ≤ 2 * (y + y ^ 3 / 3) - 4437 / 1000 * r := by
      rw [e]; positivity
    linarith
  have l2 := mul_le_mul_of_nonneg_right log2_hi.le h0.le
  nlinarith

theorem Fsp_ge_lower {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 3) :
    (112 / 5) * log 2 * r ^ 2 ≤ Fsp r := by
  have hd : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 3),
      HasDerivAt (fun r => Fsp r - (112 / 5) * log 2 * r ^ 2)
        (7 * (log (1 + 7 * x) - log (1 - x)) - (112 / 5) * log 2 * (2 * x)) x := by
    intro x hx
    have h2 : HasDerivAt (fun r : ℝ => (112 / 5) * log 2 * r ^ 2) ((112 / 5) * log 2 * (2 * x)) x :=
      ((hasDerivAt_pow 2 x).const_mul ((112 / 5) * log 2)).congr_deriv (by simp)
    exact (Fsp_hasDerivAt (r := x) (by linarith [hx.1]) (by linarith [hx.2])).sub h2
  have hmono : MonotoneOn (fun r => Fsp r - (112 / 5) * log 2 * r ^ 2) (Set.Icc 0 (1 / 3)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x ⟨hx.1.le, hx.2.le⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x ⟨hx.1.le, hx.2.le⟩).deriv]
      have := fprime_nonneg hx.1 hx.2.le
      linarith
  have := hmono ⟨le_rfl, by norm_num⟩ ⟨h0, h1⟩ h0
  have e0 : Fsp 0 = 0 := by simp [Fsp]
  simp only [e0] at this
  norm_num at this
  linarith

/-- **`F(r) ≥ (112/5) ln 2 · r²` on `[0,1]`** (`F(r) = (1+7r) ln(1+7r) + 7(1-r) ln(1-r)`). -/
theorem Fsp_ge {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : (112 / 5) * log 2 * r ^ 2 ≤ Fsp r := by
  rcases le_total r (1 / 3) with h | h
  · exact Fsp_ge_lower h0 h
  · exact Fsp_ge_upper h h1

/-! ### The spike entropy in terms of `F` -/

theorem Gsp_spike {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    Gsp ((1 + 7 * r) / 8) = 3 * log 2 - Fsp r / 8 := by
  have h8 : log 8 = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have e : (1 - (1 + 7 * r) / 8) / 7 = (1 - r) / 8 := by ring
  have hA : log ((1 + 7 * r) / 8) = log (1 + 7 * r) - 3 * log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), h8]
  unfold Gsp Fsp
  rw [e]
  simp only [negMulLog]
  rcases h1.eq_or_lt with h | h
  · subst h; norm_num [hA]; rw [h8]; ring
  · have hB : log ((1 - r) / 8) = log (1 - r) - 3 * log 2 := by
      rw [Real.log_div (by linarith) (by norm_num), h8]
    rw [hA, hB]; ring

/-! ### The lemma -/

/-- **`lem:seven-entropy-linear-purity`, in nats.**  For every probability vector on an eight-point
set, `(2/5) ln 2 (8 ∑ λ² - 1) ≤ 3 ln 2 - ∑ -λ ln λ`.  (Proved; no hypotheses.) -/
theorem entropy_linear_purity_nats {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = 8)
    (lam : ι → ℝ) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) :
    (2 / 5) * log 2 * (8 * ∑ i, lam i ^ 2 - 1) ≤ 3 * log 2 - ∑ i, negMulLog (lam i) := by
  set p := ∑ i, lam i ^ 2 with hp
  have hp1 : 1 / 8 ≤ p := sum_sq_ge hcard lam h1
  have hp2 : p ≤ 1 := sum_sq_le lam h0 h1
  have hS := entropy_le_g8 hcard lam h0 h1
  rw [← hp] at hS
  set s := Real.sqrt (7 * (8 * p - 1)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 7 * (8 * p - 1) := Real.sq_sqrt (by linarith)
  have hs7 : s ≤ 7 := by nlinarith
  have hr0 : 0 ≤ s / 7 := by positivity
  have hr1 : s / 7 ≤ 1 := by linarith
  have hg : g8 p = 3 * log 2 - Fsp (s / 7) / 8 := by
    unfold g8 tOf
    rw [← hs]
    have : (1 + s) / 8 = (1 + 7 * (s / 7)) / 8 := by ring
    rw [this]
    exact Gsp_spike hr0 hr1
  have hF := Fsp_ge hr0 hr1
  have l2 : 0 < log 2 := Real.log_pos (by norm_num)
  have e : 8 * p - 1 = 7 * (s / 7) ^ 2 := by nlinarith
  rw [e]
  nlinarith [hS, hg, hF]

/-- **`lem:seven-entropy-linear-purity`, in bits.**  `3 - S(λ) ≥ (2/5)(8 ∑ λ² - 1)` for every
probability vector on an eight-point set, with `S(λ) = (∑ -λ ln λ)/ln 2`. -/
theorem entropy_linear_purity_bits {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = 8)
    (lam : ι → ℝ) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) :
    (2 / 5) * (8 * ∑ i, lam i ^ 2 - 1) ≤ 3 - (∑ i, negMulLog (lam i)) / log 2 := by
  have l2 : 0 < log 2 := Real.log_pos (by norm_num)
  have h := entropy_linear_purity_nats hcard lam h0 h1
  have h' : (∑ i, negMulLog (lam i)) / log 2 ≤ 3 - (2 / 5) * (8 * ∑ i, lam i ^ 2 - 1) := by
    rw [div_le_iff₀ l2]; nlinarith [h]
  linarith

/-- The same for the reduced state of a `3|4` cut of a unit vector (entropy in nats, `cutEntropy`). -/
theorem cutEntropy_linear_purity (c : Cut 3 4) (ψ : BitString → ℂ)
    (hc : Function.Bijective c) (hψ : UnitVec ψ) :
    (2 / 5) * log 2 * (8 * cutPurity c ψ - 1) ≤ 3 * log 2 - cutEntropy c ψ := by
  have := entropy_linear_purity_nats card_triple _ (spec_nonneg c ψ) (spec_sum c hc ψ hψ)
  rw [spec_sq] at this
  exact this

end LinPur

end FormalResearch.FourQubitEntropy.SevenQubitConseq
