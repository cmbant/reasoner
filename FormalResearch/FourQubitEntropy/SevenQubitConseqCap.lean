import FormalResearch.FourQubitEntropy.SevenQubitConseqCeiling

/-!
# `prop:seven-entropy-spectral-spike` (conditional on `SevenPurityBound`)

If every eigenvalue of every three-qubit marginal of a pure seven-qubit state is at most `99/500`, then
`E₃(ψ) < 59307/20000 = 2.96535` bits.

The paper's proof (SC-2) uses the scalar quadratic majorant `f ≤ f(b) + f'(b)(t-b) - c(t-b)²` on
`[0, m]` and the four-copy purity bound `π₃ ≥ 211/1600`.  Here the majorant is
`SevenQubitConseqMajorant.majorant` with `b = 11327/100000`, `m = 99/500` (so `c = -hc m b`), and the
purity input is the sharp `π₃ ≥ 121/917` (`SevenPurityBound`); the same `b` then gives
`E₃ ≤ 2.96495` bits, so the four-copy bound is not needed.  The second half of the paper's proposition,
`E₃(ψ_{7/100}) > 59307/20000`, concerns the icosahedral family and is not formalized here.
-/

open Real Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitConseq

open FormalResearch.FourQubitEntropy.SevenQubitIco

/-- Entropy bound for a spectrum with all entries at most `m`, via the Hermite majorant at `b`. -/
theorem cap_entropy_bound {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = 8) (lam : ι → ℝ)
    (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) {b m : ℝ} (hb : 0 < b) (hbm : b ≤ m)
    (hle : ∀ i, lam i ≤ m) :
    ∑ i, negMulLog (lam i) ≤
      (-log b - 1 + 8 * b) + hc m b * (∑ i, lam i ^ 2 - 2 * b + 8 * b ^ 2) := by
  have hmaj : ∀ i, negMulLog (lam i) ≤
      (negMulLog b + (-log b - 1) * (-b) + hc m b * b ^ 2) +
      ((-log b - 1) - 2 * hc m b * b) * lam i + hc m b * lam i ^ 2 := by
    intro i
    have := majorant hb hbm (h0 i) (hle i)
    simp only [tang] at this
    nlinarith [this]
  calc ∑ i, negMulLog (lam i)
      ≤ ∑ i, ((negMulLog b + (-log b - 1) * (-b) + hc m b * b ^ 2) +
        ((-log b - 1) - 2 * hc m b * b) * lam i + hc m b * lam i ^ 2) :=
        Finset.sum_le_sum fun i _ => hmaj i
    _ = (-log b - 1 + 8 * b) + hc m b * (∑ i, lam i ^ 2 - 2 * b + 8 * b ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1]
        simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
        simp only [negMulLog]
        push_cast
        ring

theorem hc_nonpos {m b : ℝ} (hb : 0 < b) (hbm : b ≤ m) : hc m b ≤ 0 := by
  unfold hc
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  have hm : 0 < m := hb.trans_le hbm
  have := Real.one_sub_inv_le_log_of_pos (div_pos hm hb)
  rw [Real.log_div hm.ne' hb.ne', inv_div] at this
  unfold rem tang negMulLog
  have e : m * (1 - b / m) = m - b := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left this hm.le]

/-- Mean-entropy bound under a uniform eigenvalue cap. -/
theorem meanEntropy3_cap_le (ψ : BitString → ℂ) (hψ : UnitVec ψ) {b m : ℝ} (hb : 0 < b)
    (hbm : b ≤ m)
    (hcap : ∀ mk ∈ tripleMasks, ∀ i, (redMatPsi_isHermitian (maskCut 3 4 mk) ψ).eigenvalues i ≤ m) :
    meanEntropy3 ψ ≤ (-log b - 1 + 8 * b) + hc m b * (meanPurity3 ψ - 2 * b + 8 * b ^ 2) := by
  have hmem : ∀ mk ∈ tripleMasks, weight mk = 3 := fun mk hm => (Finset.mem_filter.1 hm).2
  have hterm : ∀ mk ∈ tripleMasks, cutEntropy (maskCut 3 4 mk) ψ ≤
      (-log b - 1 + 8 * b) +
        hc m b * (cutPurity (maskCut 3 4 mk) ψ - 2 * b + 8 * b ^ 2) := by
    intro mk hm
    have hbj := maskCut_bijective_three mk (hmem mk hm)
    have := cap_entropy_bound card_triple _ (spec_nonneg (maskCut 3 4 mk) ψ)
      (spec_sum (maskCut 3 4 mk) hbj ψ hψ) hb hbm (hcap mk hm)
    rw [spec_sq] at this
    exact this
  have hsum := Finset.sum_le_sum hterm
  have hexp : ∑ mk ∈ tripleMasks, ((-log b - 1 + 8 * b) +
        hc m b * (cutPurity (maskCut 3 4 mk) ψ - 2 * b + 8 * b ^ 2)) =
      35 * (-log b - 1 + 8 * b) + hc m b * (∑ mk ∈ tripleMasks, cutPurity (maskCut 3 4 mk) ψ
        - 35 * (2 * b) + 35 * (8 * b ^ 2)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum,
      tripleMasks_card, nsmul_eq_mul]
    push_cast
    ring
  rw [hexp] at hsum
  unfold meanEntropy3 meanPurity3
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 35)]
  nlinarith [hsum]

/-- A series lower bound for `log x`, `x ≥ 1` (three terms). -/
theorem log_ge_three {x : ℝ} (hx : 1 ≤ x) :
    2 * (((x - 1) / (x + 1)) + ((x - 1) / (x + 1)) ^ 3 / 3 + ((x - 1) / (x + 1)) ^ 5 / 5) ≤ log x := by
  set y := (x - 1) / (x + 1) with hy
  have hy0 : 0 ≤ y := div_nonneg (by linarith) (by linarith)
  have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
  have := Real.sum_range_le_log_div hy0 hy1 3
  have hr : (1 + y) / (1 - y) = x := by rw [hy]; field_simp; ring
  rw [hr] at this
  simp [Finset.sum_range_succ] at this
  linarith

theorem cap_numeric :
    (-log (11327 / 100000 : ℝ) - 1 + 8 * (11327 / 100000)) +
      hc (99 / 500) (11327 / 100000) * (121 / 917 - 2 * (11327 / 100000) + 8 * (11327 / 100000) ^ 2)
      < 59307 / 20000 * log 2 := by
  set b : ℝ := 11327 / 100000 with hb
  set m : ℝ := 99 / 500 with hm
  have hlb : (0 : ℝ) < b := by norm_num [hb]
  have e8 : log b = log (8 * b) - 3 * log 2 := by
    have : log (8 * b) = log 8 + log b := Real.log_mul (by norm_num) hlb.ne'
    have h8 : log 8 = 3 * log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    linarith
  have l1 := Lb_le_log (x := 8 * b) (by norm_num [hb])
  have l2 := log_ge_three (x := m / b) (by norm_num [hb, hm])
  have lm : log (m / b) = log m - log b := Real.log_div (by norm_num [hm]) hlb.ne'
  have hrem : rem b m = -(m * log (m / b)) + (m - b) := by
    unfold rem tang negMulLog
    rw [lm]
    ring
  have hden : 0 < (m - b) ^ 2 := by norm_num [hb, hm]
  have hw : 0 < (121 / 917 : ℝ) - 2 * b + 8 * b ^ 2 := by norm_num [hb]
  have hcdef : hc m b * (m - b) ^ 2 = rem b m := hc_mul
  set y : ℝ := ((m / b) - 1) / ((m / b) + 1) with hy
  set K : ℝ := m * (2 * (y + y ^ 3 / 3 + y ^ 5 / 5)) - (m - b) with hK
  have hcle : hc m b ≤ -K / (m - b) ^ 2 := by
    rw [le_div_iff₀ hden, hcdef, hrem]
    have := mul_le_mul_of_nonneg_left l2 (by norm_num [hm] : (0 : ℝ) ≤ m)
    rw [hK]
    nlinarith [this]
  have hstep := mul_le_mul_of_nonneg_right hcle hw.le
  have l2' := Real.log_two_lt_d9
  have l2'' := Real.log_two_gt_d9
  rw [e8]
  have hy' : y = ((99 / 500) / (11327 / 100000) - 1) / ((99 / 500) / (11327 / 100000) + 1) := by
    rw [hy, hm, hb]
  have hKv : K = (99 / 500) * (2 * (y + y ^ 3 / 3 + y ^ 5 / 5)) - (99 / 500 - 11327 / 100000) := by
    rw [hK, hm, hb]
  rw [hKv, hy'] at hstep
  unfold Lb at l1
  norm_num [hb, hm] at l1 hstep ⊢
  nlinarith [hstep, l1, l2', l2'']

/-- **`prop:seven-entropy-spectral-spike`** (conditional on the sharp purity bound).  If every
eigenvalue of every three-qubit marginal of the unit vector `ψ` is at most `99/500`, then
`E₃(ψ) < 2.96535` bits. -/
theorem entropy_cap_exclusion (h : SevenPurityBound) (ψ : BitString → ℂ) (hψ : UnitVec ψ)
    (hcap : ∀ mk ∈ tripleMasks, ∀ i,
      (redMatPsi_isHermitian (maskCut 3 4 mk) ψ).eigenvalues i ≤ 99 / 500) :
    meanEntropy3 ψ < 59307 / 20000 * Real.log 2 := by
  have hb : (0 : ℝ) < 11327 / 100000 := by norm_num
  have hbm : (11327 / 100000 : ℝ) ≤ 99 / 500 := by norm_num
  have h1 := meanEntropy3_cap_le ψ hψ hb hbm hcap
  have hc0 := hc_nonpos hb hbm
  have hpi := h ψ hψ
  have hw : (0 : ℝ) ≤ 121 / 917 - 2 * (11327 / 100000) + 8 * (11327 / 100000) ^ 2 := by norm_num
  have h2 : hc (99 / 500) (11327 / 100000) * (meanPurity3 ψ - 2 * (11327 / 100000) +
      8 * (11327 / 100000) ^ 2) ≤ hc (99 / 500) (11327 / 100000) *
      (121 / 917 - 2 * (11327 / 100000) + 8 * (11327 / 100000) ^ 2) :=
    mul_le_mul_of_nonpos_left (by linarith) hc0
  have := cap_numeric
  linarith

end FormalResearch.FourQubitEntropy.SevenQubitConseq
