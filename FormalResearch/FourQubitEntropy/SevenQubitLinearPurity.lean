import FormalResearch.FourQubitEntropy.SevenQubitConseqSpectrum
import FormalResearch.FourQubitEntropy.SevenQubitConseqEnvelope

/-!
# `lem:seven-entropy-linear-purity`: the universal dimension-eight entropy-purity slope

For every probability vector `λ` on eight points (entropy `S` in bits),
`3 - S(λ) ≥ (7 log₂ 7 / 48)(8 ∑ λ² - 1) ≥ (49/120)(8 ∑ λ² - 1) ≥ (2/5)(8 ∑ λ² - 1)`, i.e. in nats
`(7/48) ln 7 (8 ∑ λ² - 1) ≤ 3 ln 2 - ∑ -λ ln λ`.

Proof (`seven_qubit_entropy_compatibility.tex`, SP7-5).  `entropy_le_g8` reduces to the one-spike
spectrum `((1+7r)/8, ((1-r)/8)^7)`, where `8 ∑ λ² - 1 = 7 r²` and `3 ln 2 - S = F(r)/8` with
`F(r) = (1+7r)ln(1+7r) + 7(1-r)ln(1-r)`.  The sharp first inequality is `F(r) ≥ (49/6) ln 7 · r²`
(`Fsp_ge_sharp`), proved as in the paper: `(F/r²)' = N/r³` with `N = r F' - 2F`, `N'' = r F'''`,
`N(0) = N'(0) = 0` and `N(6/7) = 0`, so `N < 0` on `(0, 6/7)` and `N > 0` on `(6/7, 1)`, and `F/r²` has its
minimum `(49/6) ln 7` at `r = 6/7`.  The comparisons `7 log₂ 7/48 ≥ 49/120 ≥ 2/5` use `7⁵ > 2¹⁴`.
The equality cases (spectra `(7/8, (1/56)^7)` and uniform) are not formalized.

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

theorem log7_eq : log 7 = 3 * log 2 - log (8 / 7) := by
  have h8 : log 8 = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  rw [Real.log_div (by norm_num) (by norm_num), h8]; ring


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


theorem Fsp_6_7 : Fsp (6 / 7) = 6 * log 7 ∧
    log (1 + 7 * (6 / 7)) - log (1 - 6 / 7) = 2 * log 7 := by
  have e1 : (1 + 7 * (6 / 7) : ℝ) = 7 := by norm_num
  have e2 : (1 - 6 / 7 : ℝ) = 7⁻¹ := by norm_num
  unfold Fsp
  rw [e1, e2, Real.log_inv]
  constructor <;> ring


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


/-! ### The sharp constant: `F(r) ≥ (49/6) ln 7 · r²` on `[0,1]`

`F(r)/r²` has derivative `N(r)/r³` with `N = r F' - 2F`.  Writing `F' = F1`, `F'' = F2`, `F''' = F3`,
one has `N' = r F2 - F1` and `N'' = r F3`, with `F3` negative on `(-1/7, 3/7)` and positive on `(3/7, 1)`.
Since `N(0) = N'(0) = 0`, `N` is negative on `(0, 3/7]`; on `[3/7, 1)` it is convex and `N(6/7) = 0`.
Hence `N < 0` on `(0, 6/7)` and `N > 0` on `(6/7, 1)`: `F(r)/r²` decreases to `r = 6/7` and then increases,
with minimum `F(6/7)/(6/7)² = (49/6) ln 7`. -/

/-- `F'(r)`. -/
noncomputable def F1sp (r : ℝ) : ℝ := 7 * (log (1 + 7 * r) - log (1 - r))

/-- `F''(r)`. -/
noncomputable def F2sp (r : ℝ) : ℝ := 56 / ((1 + 7 * r) * (1 - r))

/-- `F'''(r)`. -/
noncomputable def F3sp (r : ℝ) : ℝ := 112 * (7 * r - 3) / ((1 + 7 * r) * (1 - r)) ^ 2

/-- `N(r) = r F'(r) - 2 F(r)`. -/
noncomputable def Nsp (r : ℝ) : ℝ := r * F1sp r - 2 * Fsp r

/-- `N'(r) = r F''(r) - F'(r)`. -/
noncomputable def N1sp (r : ℝ) : ℝ := r * F2sp r - F1sp r

theorem F1sp_hasDerivAt {r : ℝ} (h0 : -(1 : ℝ) / 7 < r) (h1 : r < 1) :
    HasDerivAt F1sp (F2sp r) r := by
  have p1 : 0 < 1 + 7 * r := by linarith
  have p2 : 0 < 1 - r := by linarith
  have a : HasDerivAt (fun r : ℝ => 1 + 7 * r) 7 r := by
    simpa using ((hasDerivAt_id r).const_mul (7 : ℝ)).const_add 1
  have b : HasDerivAt (fun r : ℝ => 1 - r) (-1) r := by
    simpa using (hasDerivAt_id r).const_sub 1
  have h := ((a.log p1.ne').sub (b.log p2.ne')).const_mul 7
  have e : 7 * (7 / (1 + 7 * r) - -1 / (1 - r)) = F2sp r := by
    unfold F2sp; field_simp; ring
  rw [e] at h
  exact h

theorem F2sp_hasDerivAt {r : ℝ} (h0 : -(1 : ℝ) / 7 < r) (h1 : r < 1) :
    HasDerivAt F2sp (F3sp r) r := by
  have p1 : 0 < 1 + 7 * r := by linarith
  have p2 : 0 < 1 - r := by linarith
  have a : HasDerivAt (fun r : ℝ => 1 + 7 * r) 7 r := by
    simpa using ((hasDerivAt_id r).const_mul (7 : ℝ)).const_add 1
  have b : HasDerivAt (fun r : ℝ => 1 - r) (-1) r := by
    simpa using (hasDerivAt_id r).const_sub 1
  have hd := a.mul b
  have hc : HasDerivAt (fun _ : ℝ => (56 : ℝ)) 0 r := hasDerivAt_const r 56
  have h := hc.div hd (by show (1 + 7 * r) * (1 - r) ≠ 0; positivity)
  have hF : F2sp = (fun _ : ℝ => (56 : ℝ)) / ((fun r : ℝ => 1 + 7 * r) * fun r : ℝ => 1 - r) := by
    funext x; simp [F2sp]
  rw [hF]
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  unfold F3sp; field_simp; ring

theorem Nsp_hasDerivAt {r : ℝ} (h0 : -(1 : ℝ) / 7 < r) (h1 : r < 1) :
    HasDerivAt Nsp (N1sp r) r := by
  have h := ((hasDerivAt_id r).mul (F1sp_hasDerivAt h0 h1)).sub
    ((Fsp_hasDerivAt h0 h1).const_mul 2)
  have e : 1 * F1sp r + id r * F2sp r - 2 * (7 * (log (1 + 7 * r) - log (1 - r))) = N1sp r := by
    unfold N1sp F1sp; simp only [id]; ring
  rw [e] at h
  exact h

theorem N1sp_hasDerivAt {r : ℝ} (h0 : -(1 : ℝ) / 7 < r) (h1 : r < 1) :
    HasDerivAt N1sp (r * F3sp r) r := by
  have h := ((hasDerivAt_id r).mul (F2sp_hasDerivAt h0 h1)).sub (F1sp_hasDerivAt h0 h1)
  have e : 1 * F2sp r + id r * F3sp r - F2sp r = r * F3sp r := by
    simp only [id]; ring
  rw [e] at h
  exact h

theorem F3sp_neg {r : ℝ} (h0 : -(1 : ℝ) / 7 < r) (h1 : r < 3 / 7) : F3sp r < 0 := by
  unfold F3sp
  have p1 : 0 < 1 + 7 * r := by linarith
  have p2 : 0 < 1 - r := by linarith
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

theorem F3sp_nonneg {r : ℝ} (h0 : 3 / 7 ≤ r) (h1 : r < 1) : 0 ≤ F3sp r := by
  unfold F3sp
  have p1 : 0 < 1 + 7 * r := by linarith
  have p2 : 0 < 1 - r := by linarith
  exact div_nonneg (by linarith) (by positivity)

/-- `N < 0` on `(0, 3/7]`. -/
theorem Nsp_neg_low {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 3 / 7) : Nsp r < 0 := by
  have hN1 : StrictAntiOn N1sp (Set.Icc (0 : ℝ) (3 / 7)) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
    · intro x hx
      exact (N1sp_hasDerivAt (by linarith [hx.1]) (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(N1sp_hasDerivAt (by linarith [hx.1]) (by linarith [hx.2])).deriv]
      exact mul_neg_of_pos_of_neg hx.1 (F3sp_neg (by linarith [hx.1]) hx.2)
  have e0 : N1sp 0 = 0 := by simp [N1sp, F2sp, F1sp]
  have hneg : ∀ x ∈ Set.Ioc (0 : ℝ) (3 / 7), N1sp x < 0 := by
    intro x hx
    have := hN1 (a := 0) (b := x) ⟨le_rfl, by norm_num⟩ ⟨hx.1.le, hx.2⟩ hx.1
    rwa [e0] at this
  have hN : StrictAntiOn Nsp (Set.Icc (0 : ℝ) (3 / 7)) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
    · intro x hx
      exact (Nsp_hasDerivAt (by linarith [hx.1]) (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(Nsp_hasDerivAt (by linarith [hx.1]) (by linarith [hx.2])).deriv]
      exact hneg x ⟨hx.1, hx.2.le⟩
  have e1 : Nsp 0 = 0 := by simp [Nsp, F1sp, Fsp]
  have := hN (a := 0) (b := r) ⟨le_rfl, by norm_num⟩ ⟨h0.le, h1⟩ h0
  rwa [e1] at this

/-- `N` is convex on `[3/7, 1)`. -/
theorem Nsp_convexOn : ConvexOn ℝ (Set.Ico (3 / 7 : ℝ) 1) Nsp := by
  have hmono : MonotoneOn N1sp (Set.Ioo (3 / 7 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioo _ _) ?_ ?_ ?_
    · intro x hx
      exact (N1sp_hasDerivAt (by linarith [hx.1]) hx.2).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      exact (N1sp_hasDerivAt (by linarith [hx.1]) hx.2).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      rw [(N1sp_hasDerivAt (by linarith [hx.1]) hx.2).deriv]
      exact mul_nonneg (by linarith [hx.1]) (F3sp_nonneg hx.1.le hx.2)
  refine MonotoneOn.convexOn_of_deriv (convex_Ico _ _) ?_ ?_ ?_
  · intro x hx
    exact (Nsp_hasDerivAt (by linarith [hx.1]) hx.2).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ico] at hx
    exact (Nsp_hasDerivAt (by linarith [hx.1]) hx.2).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    rw [interior_Ico] at hx hy
    rw [(Nsp_hasDerivAt (by linarith [hx.1]) hx.2).deriv,
      (Nsp_hasDerivAt (by linarith [hy.1]) hy.2).deriv]
    exact hmono hx hy hxy

theorem Nsp_6_7 : Nsp (6 / 7) = 0 := by
  obtain ⟨hF, hB⟩ := Fsp_6_7
  have : F1sp (6 / 7) = 7 * (2 * log 7) := by unfold F1sp; rw [hB]
  unfold Nsp; rw [this, hF]; ring

/-- `N < 0` on `(0, 6/7)`. -/
theorem Nsp_neg {r : ℝ} (h0 : 0 < r) (h1 : r < 6 / 7) : Nsp r < 0 := by
  rcases le_total r (3 / 7) with h | h
  · exact Nsp_neg_low h0 h
  · have ha := Nsp_neg_low (r := 3 / 7) (by norm_num) le_rfl
    have hx : (3 / 7 : ℝ) ∈ Set.Ico (3 / 7 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
    have hy : (6 / 7 : ℝ) ∈ Set.Ico (3 / 7 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have hA : 0 ≤ (6 / 7 - r) / (3 / 7) := div_nonneg (by linarith) (by norm_num)
    have hB : 0 ≤ (r - 3 / 7) / (3 / 7) := div_nonneg (by linarith) (by norm_num)
    have hab : (6 / 7 - r) / (3 / 7) + (r - 3 / 7) / (3 / 7) = 1 := by field_simp; ring
    have hc := Nsp_convexOn.2 hx hy hA hB hab
    have e : ((6 / 7 - r) / (3 / 7)) • (3 / 7 : ℝ) + ((r - 3 / 7) / (3 / 7)) • (6 / 7 : ℝ) = r := by
      simp only [smul_eq_mul]; field_simp; ring
    rw [e, smul_eq_mul, smul_eq_mul, Nsp_6_7, mul_zero, add_zero] at hc
    have hp : 0 < (6 / 7 - r) / (3 / 7) := div_pos (by linarith) (by norm_num)
    exact lt_of_le_of_lt hc (mul_neg_of_pos_of_neg hp ha)

/-- `N > 0` on `(6/7, 1)`. -/
theorem Nsp_pos {r : ℝ} (h0 : 6 / 7 < r) (h1 : r < 1) : 0 < Nsp r := by
  have ha := Nsp_neg_low (r := 3 / 7) (by norm_num) le_rfl
  have hr : 0 < r - 3 / 7 := by linarith
  have hx : (3 / 7 : ℝ) ∈ Set.Ico (3 / 7 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hy : r ∈ Set.Ico (3 / 7 : ℝ) 1 := ⟨by linarith, h1⟩
  have hA : 0 ≤ (r - 6 / 7) / (r - 3 / 7) := div_nonneg (by linarith) hr.le
  have hB : 0 ≤ (3 / 7) / (r - 3 / 7) := div_nonneg (by norm_num) hr.le
  have hne : r - 3 / 7 ≠ 0 := hr.ne'
  have hab : (r - 6 / 7) / (r - 3 / 7) + (3 / 7) / (r - 3 / 7) = 1 := by
    rw [← add_div, div_eq_one_iff_eq hne]; ring
  have hc := Nsp_convexOn.2 hx hy hA hB hab
  have e : ((r - 6 / 7) / (r - 3 / 7)) • (3 / 7 : ℝ) + ((3 / 7) / (r - 3 / 7)) • r = 6 / 7 := by
    simp only [smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hne]; ring
  rw [e, smul_eq_mul, smul_eq_mul, Nsp_6_7] at hc
  have hp : 0 < (r - 6 / 7) / (r - 3 / 7) := div_pos (by linarith) hr
  have hq : 0 < (3 / 7) / (r - 3 / 7) := div_pos (by norm_num) hr
  by_contra hneg
  have h3 := mul_nonpos_of_nonneg_of_nonpos hq.le (not_lt.1 hneg)
  have h4 : 0 < (r - 6 / 7) / (r - 3 / 7) * (-Nsp (3 / 7)) := mul_pos hp (by linarith)
  nlinarith

/-- `F(r)/r²`. -/
noncomputable def phiSp (r : ℝ) : ℝ := Fsp r / r ^ 2

theorem phiSp_hasDerivAt {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    HasDerivAt phiSp (Nsp r / r ^ 3) r := by
  have h := (Fsp_hasDerivAt (by linarith) h1).div (hasDerivAt_pow 2 r) (by positivity)
  have hF : phiSp = Fsp / fun x : ℝ => x ^ 2 := by funext x; simp [phiSp]
  rw [hF]
  refine h.congr_deriv ?_
  unfold Nsp F1sp; push_cast; field_simp

theorem phiSp_6_7 : phiSp (6 / 7) = (49 / 6) * log 7 := by
  obtain ⟨hF, -⟩ := Fsp_6_7
  unfold phiSp; rw [hF]; ring

/-- **Sharp bound**: `F(r) ≥ (49/6) ln 7 · r²` on `[0,1]`, with equality at `r = 0` and `r = 6/7`. -/
theorem Fsp_ge_sharp {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : (49 / 6) * log 7 * r ^ 2 ≤ Fsp r := by
  have l7 := log7_hi
  have l2 := log2_lo
  rcases h0.eq_or_lt with hr | hr
  · subst hr; simp [Fsp]
  rcases h1.eq_or_lt with hr1 | hr1
  · subst hr1
    have e : Fsp 1 = 24 * log 2 := by
      have h8 : log 8 = 3 * log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
      simp only [Fsp]; norm_num [h8]; ring
    rw [e]; nlinarith
  have hanti : AntitoneOn phiSp (Set.Ioc (0 : ℝ) (6 / 7)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioc _ _) ?_ ?_ ?_
    · intro x hx
      exact (phiSp_hasDerivAt hx.1 (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      exact (phiSp_hasDerivAt hx.1 (by linarith [hx.2])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(phiSp_hasDerivAt hx.1 (by linarith [hx.2])).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (Nsp_neg hx.1 hx.2).le (by have := hx.1; positivity)
  have hmono : MonotoneOn phiSp (Set.Ico (6 / 7 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico _ _) ?_ ?_ ?_
    · intro x hx
      exact (phiSp_hasDerivAt (by linarith [hx.1]) hx.2).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      exact (phiSp_hasDerivAt (by linarith [hx.1]) hx.2).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      rw [(phiSp_hasDerivAt (by linarith [hx.1]) hx.2).deriv]
      exact div_nonneg (Nsp_pos hx.1 hx.2).le (by have : 0 < x := by linarith [hx.1]
                                                  positivity)
  have hphi : (49 / 6) * log 7 ≤ phiSp r := by
    rcases le_total r (6 / 7) with h | h
    · have := hanti ⟨hr, h⟩ ⟨by norm_num, le_rfl⟩ h
      rwa [phiSp_6_7] at this
    · have := hmono ⟨le_rfl, by norm_num⟩ ⟨h, hr1⟩ h
      rwa [phiSp_6_7] at this
  unfold phiSp at hphi
  rw [le_div_iff₀ (by positivity)] at hphi
  exact hphi


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

/-- `7⁵ = 16807 > 16384 = 2¹⁴`, i.e. `ln 7 > (14/5) ln 2`. -/
theorem log7_gt : (14 / 5) * log 2 < log 7 := by
  have h : (2 : ℝ) ^ 14 < 7 ^ 5 := by norm_num
  have := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at this
  push_cast at this
  linarith

/-- **`lem:seven-entropy-linear-purity`, sharp first inequality, in nats.**  For every probability
vector on an eight-point set, `(7/48) ln 7 · (8 ∑ λ² - 1) ≤ 3 ln 2 - ∑ -λ ln λ`; in bits the slope is
`7 log₂ 7 / 48`.  (Proved; no hypotheses.  The equality cases are not formalized.) -/
theorem entropy_linear_purity_sharp_nats {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = 8)
    (lam : ι → ℝ) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) :
    (7 / 48) * log 7 * (8 * ∑ i, lam i ^ 2 - 1) ≤ 3 * log 2 - ∑ i, negMulLog (lam i) := by
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
  have hF := Fsp_ge_sharp hr0 hr1
  have e : 8 * p - 1 = 7 * (s / 7) ^ 2 := by nlinarith
  rw [e]
  nlinarith [hS, hg, hF]

/-- **`lem:seven-entropy-linear-purity`, rational slope `49/120`, in nats.** -/
theorem entropy_linear_purity_rat_nats {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = 8)
    (lam : ι → ℝ) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) :
    (49 / 120) * log 2 * (8 * ∑ i, lam i ^ 2 - 1) ≤ 3 * log 2 - ∑ i, negMulLog (lam i) := by
  have hp1 : 1 / 8 ≤ ∑ i, lam i ^ 2 := sum_sq_ge hcard lam h1
  have h := entropy_linear_purity_sharp_nats hcard lam h0 h1
  have hl := log7_gt
  have hq : 0 ≤ 8 * ∑ i, lam i ^ 2 - 1 := by linarith
  nlinarith [mul_nonneg hq (sub_nonneg.2 hl.le)]

/-- **`lem:seven-entropy-linear-purity`, in nats.**  For every probability vector on an eight-point
set, `(2/5) ln 2 (8 ∑ λ² - 1) ≤ 3 ln 2 - ∑ -λ ln λ`.  (Proved; no hypotheses.)  This is the weakest
of the three slopes `7 log₂ 7/48 ≥ 49/120 ≥ 2/5` of the lemma and the one the competitor band uses. -/
theorem entropy_linear_purity_nats {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = 8)
    (lam : ι → ℝ) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) :
    (2 / 5) * log 2 * (8 * ∑ i, lam i ^ 2 - 1) ≤ 3 * log 2 - ∑ i, negMulLog (lam i) := by
  have hp1 : 1 / 8 ≤ ∑ i, lam i ^ 2 := sum_sq_ge hcard lam h1
  have h := entropy_linear_purity_rat_nats hcard lam h0 h1
  have l2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hq : 0 ≤ 8 * ∑ i, lam i ^ 2 - 1 := by linarith
  nlinarith [mul_nonneg l2.le hq]

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

/-- **`lem:seven-entropy-linear-purity`, sharp slope in bits.**
`3 - S(λ) ≥ (7 log₂ 7 / 48)(8 ∑ λ² - 1) ≥ (49/120)(8 ∑ λ² - 1)`. -/
theorem entropy_linear_purity_sharp_bits {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = 8)
    (lam : ι → ℝ) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) :
    (7 * (log 7 / log 2) / 48) * (8 * ∑ i, lam i ^ 2 - 1) ≤ 3 - (∑ i, negMulLog (lam i)) / log 2 ∧
    (49 / 120) * (8 * ∑ i, lam i ^ 2 - 1) ≤ (7 * (log 7 / log 2) / 48) * (8 * ∑ i, lam i ^ 2 - 1) := by
  have l2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hp1 : 1 / 8 ≤ ∑ i, lam i ^ 2 := sum_sq_ge hcard lam h1
  have hq : 0 ≤ 8 * ∑ i, lam i ^ 2 - 1 := by linarith
  constructor
  · have h := entropy_linear_purity_sharp_nats hcard lam h0 h1
    have e3 : 3 - (∑ i, negMulLog (lam i)) / log 2 =
        (3 * log 2 - ∑ i, negMulLog (lam i)) / log 2 := by field_simp
    rw [e3, le_div_iff₀ l2]
    have e : 7 * (log 7 / log 2) / 48 * (8 * ∑ i, lam i ^ 2 - 1) * log 2 =
        (7 / 48) * log 7 * (8 * ∑ i, lam i ^ 2 - 1) := by field_simp
    rw [e]; exact h
  · have hr : 14 / 5 ≤ log 7 / log 2 := by rw [le_div_iff₀ l2]; linarith [log7_gt]
    nlinarith [mul_nonneg hq (sub_nonneg.2 hr)]

/-- The same for the reduced state of a `3|4` cut of a unit vector (entropy in nats, `cutEntropy`). -/
theorem cutEntropy_linear_purity (c : Cut 3 4) (ψ : BitString → ℂ)
    (hc : Function.Bijective c) (hψ : UnitVec ψ) :
    (2 / 5) * log 2 * (8 * cutPurity c ψ - 1) ≤ 3 * log 2 - cutEntropy c ψ := by
  have := entropy_linear_purity_nats card_triple _ (spec_nonneg c ψ) (spec_sum c hc ψ hψ)
  rw [spec_sq] at this
  exact this

/-- The sharp slope for the reduced state of a `3|4` cut (nats). -/
theorem cutEntropy_linear_purity_sharp (c : Cut 3 4) (ψ : BitString → ℂ)
    (hc : Function.Bijective c) (hψ : UnitVec ψ) :
    (7 / 48) * log 7 * (8 * cutPurity c ψ - 1) ≤ 3 * log 2 - cutEntropy c ψ := by
  have := entropy_linear_purity_sharp_nats card_triple _ (spec_nonneg c ψ) (spec_sum c hc ψ hψ)
  rw [spec_sq] at this
  exact this

end LinPur

end FormalResearch.FourQubitEntropy.SevenQubitConseq
