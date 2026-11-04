module

public import FormalResearch.FourQubitEntropy.SevenQubitConseqSpectrum
public import FormalResearch.FourQubitEntropy.SevenQubitConseqEnvelope
public import FormalResearch.NQubit.Entropy.PuritySlope

/-!
# `lem:seven-entropy-linear-purity`: the universal dimension-eight entropy-purity slope

For every probability vector `λ` on eight points (entropy `S` in bits),
`3 - S(λ) ≥ (7 log₂ 7 / 48)(8 ∑ λ² - 1) ≥ (49/120)(8 ∑ λ² - 1) ≥ (2/5)(8 ∑ λ² - 1)`, i.e. in nats
`(7/48) ln 7 (8 ∑ λ² - 1) ≤ 3 ln 2 - ∑ -λ ln λ`.

Proof (`seven_qubit_entropy_compatibility.tex`, SP7-5).  The sharp first inequality is the case
`d = 8` of the all-dimension slope `NQubit.Entropy.entropy_purity_slope_nats` (`NQubit/Entropy/PuritySlope.lean`,
`c_d = (d-1) log₂(d-1)/(d(d-2))`, `c_8 = 7 log₂ 7/48`), whose equality case
`NQubit.Entropy.entropy_purity_slope_eq_iff` (uniform, or `(7/8, (1/56)^7)`) is proved there.
`Fsp_ge_sharp` and `Gsp_spike` are the `m = 7` cases of `NQubit.Entropy.spikeDeficit_ge_sharp` and `NQubit.Entropy.spikeEnt_eq`.
The comparisons `7 log₂ 7/48 ≥ 49/120 ≥ 2/5` use `7⁵ > 2¹⁴`.

Everything is proved (no hypotheses, no `native_decide`).
-/

@[expose] public section


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

/-- The four-term `arctanh` upper bound for `log x` used in `log_ge_hi`, as a function. -/
noncomputable def arctanhHi (x : ℝ) : ℝ :=
  2 * (((x - 1) / (x + 1)) + ((x - 1) / (x + 1)) ^ 3 / 3 + ((x - 1) / (x + 1)) ^ 5 / 5 +
    ((x - 1) / (x + 1)) ^ 7 / 7) + 2 * (((x - 1) / (x + 1)) ^ 9 / (1 - ((x - 1) / (x + 1)) ^ 2))

theorem log_le_arctanhHi {x : ℝ} (hx : 1 ≤ x) : log x ≤ arctanhHi x := log_ge_hi hx

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

theorem Fsp_eq_spikeDeficit (r : ℝ) : Fsp r = NQubit.Entropy.spikeDeficit 7 r := by
  unfold Fsp NQubit.Entropy.spikeDeficit; simp only [negMulLog]; ring

/-- **Sharp bound**: `F(r) ≥ (49/6) ln 7 · r²` on `[0,1]`, with equality at `r = 0` and `r = 6/7`
(the case `m = 7` of `NQubit.Entropy.spikeDeficit_ge_sharp` / `spikeDeficit_eq_iff`). -/
theorem Fsp_ge_sharp {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : (49 / 6) * log 7 * r ^ 2 ≤ Fsp r := by
  have h := NQubit.Entropy.spikeDeficit_ge_sharp (m := 7) (by norm_num) h0 h1
  rw [Fsp_eq_spikeDeficit]; norm_num at h ⊢; linarith


/-! ### The spike entropy in terms of `F` -/

theorem Gsp_spike {r : ℝ} (_h0 : 0 ≤ r) (_h1 : r ≤ 1) :
    Gsp ((1 + 7 * r) / 8) = 3 * log 2 - Fsp r / 8 := by
  have h8 : log 8 = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h := NQubit.Entropy.spikeEnt_eq (d := 8) (r := r) (by norm_num)
  rw [Gsp_eq_spikeEnt, Fsp_eq_spikeDeficit, ← h8]
  norm_num at h ⊢; exact h


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
  have h := NQubit.Entropy.entropy_purity_slope_nats (d := 8) (by norm_num) hcard lam h0 h1
  have h8 : log 8 = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  norm_num [h8] at h
  linarith

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
