module

public import FormalResearch.Special.BesselNormalized
public import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# The Bessel series `T_c(z) = ∑ z^k / (k! Γ(c+k))` and its differentiation

For real `c > 0`, `besselSeries c z = ∑_k z^k / (k! Γ(c+k))` (the regularised `₀F₁(; c; z)`), an entire
function of `z` with `besselNorm ν x = Γ(ν+1) · besselSeries (ν+1) (-(x/2)²)`.

* `hasDerivAt_besselSeries`: `T_c' = T_{c+1}`;
* `besselSeries_recurrence`: `T_c = c T_{c+1} + z T_{c+2}`;
* `hasDerivAt_besselNorm`: `(besselNorm ν)'(x) = -(x / (2(ν+1))) besselNorm (ν+1) x` for `ν > -1`;
* `besselNorm_recurrence`: `besselNorm ν x = besselNorm (ν+1) x - x² / (4(ν+1)(ν+2)) besselNorm (ν+2) x`.
-/

@[expose] public section

open Set Filter Topology
open scoped Nat

namespace FormalResearch.Special

/-- The coefficient `1 / (k! Γ(c+k))`. -/
noncomputable def besselSeriesCoeff (c : ℝ) (k : ℕ) : ℝ :=
  1 / ((k ! : ℝ) * Real.Gamma (c + k))

/-- `T_c(z) = ∑_k z^k / (k! Γ(c+k))`. -/
noncomputable def besselSeries (c z : ℝ) : ℝ :=
  ∑' k : ℕ, z ^ k * besselSeriesCoeff c k

lemma besselSeriesCoeff_pos {c : ℝ} (hc : 0 < c) (k : ℕ) : 0 < besselSeriesCoeff c k := by
  unfold besselSeriesCoeff
  have : 0 < Real.Gamma (c + k) := Real.Gamma_pos_of_pos (by positivity)
  positivity

lemma besselSeriesCoeff_succ {c : ℝ} (k : ℕ) :
    ((k : ℝ) + 1) * besselSeriesCoeff c (k + 1) = besselSeriesCoeff (c + 1) k := by
  unfold besselSeriesCoeff
  rw [Nat.factorial_succ, show c + 1 + (k : ℝ) = c + ((k + 1 : ℕ) : ℝ) by push_cast; ring]
  push_cast
  have : (k ! : ℝ) ≠ 0 := by positivity
  have : ((k : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- Relation with `besselNorm`. -/
theorem besselNorm_eq_besselSeries (ν x : ℝ) :
    besselNorm ν x = Real.Gamma (ν + 1) * besselSeries (ν + 1) (-(x / 2) ^ 2) := by
  unfold besselNorm besselSeries
  congr 1
  refine tsum_congr fun k => ?_
  rw [show (-(x / 2) ^ 2) ^ k = (-1) ^ k * (x / 2) ^ (2 * k) by rw [neg_pow ((x / 2) ^ 2) k, ← pow_mul],
    besselNormCoeff, besselSeriesCoeff, show ν + 1 + (k : ℝ) = ν + k + 1 by ring]

theorem summable_besselSeries_abs {c : ℝ} (hc : 0 < c) (r : ℝ) :
    Summable fun k : ℕ => |r| ^ k * besselSeriesCoeff c k := by
  have h := (besselNorm_summable (c - 1) (2 * √|r|)).abs
  refine h.congr fun k => ?_
  have hco : 0 < besselNormCoeff (c - 1) k := by
    unfold besselNormCoeff
    have : 0 < Real.Gamma (c - 1 + k + 1) := Real.Gamma_pos_of_pos (by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    positivity
  have e : (2 * √|r| / 2) ^ (2 * k) = |r| ^ k := by
    rw [show 2 * √|r| / 2 = √|r| by ring, pow_mul, Real.sq_sqrt (abs_nonneg r)]
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, e, abs_of_nonneg
    (by positivity : (0 : ℝ) ≤ |r| ^ k), abs_of_pos hco]
  unfold besselNormCoeff besselSeriesCoeff
  rw [show c + (k : ℝ) = c - 1 + k + 1 by ring]

theorem summable_besselSeries {c : ℝ} (hc : 0 < c) (z : ℝ) :
    Summable fun k : ℕ => z ^ k * besselSeriesCoeff c k := by
  refine Summable.of_norm_bounded (summable_besselSeries_abs hc z) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (besselSeriesCoeff_pos hc k)]

/-- `T_c' = T_{c+1}`. -/
theorem hasDerivAt_besselSeries {c : ℝ} (hc : 0 < c) (z : ℝ) :
    HasDerivAt (besselSeries c) (besselSeries (c + 1) z) z := by
  set r : ℝ := |z| + 1 with hr
  have hr0 : 0 < r := by positivity
  have hu : Summable fun n : ℕ => (n : ℝ) * r ^ (n - 1) * besselSeriesCoeff c n := by
    rw [← summable_nat_add_iff 1]
    refine (summable_besselSeries_abs (by linarith : 0 < c + 1) r).congr fun n => ?_
    rw [abs_of_pos hr0, ← besselSeriesCoeff_succ]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring
  have hd := hasDerivAt_tsum_of_isPreconnected (u := fun n : ℕ => (n : ℝ) * r ^ (n - 1) *
      besselSeriesCoeff c n) (g := fun (n : ℕ) (y : ℝ) => y ^ n * besselSeriesCoeff c n)
    (g' := fun (n : ℕ) (y : ℝ) => (n : ℝ) * y ^ (n - 1) * besselSeriesCoeff c n)
    (t := Ioo (-r) r) hu isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => by simpa using (hasDerivAt_pow n y).mul_const (besselSeriesCoeff c n))
    (fun n y hy => by
      have hy' : |y| ≤ r := (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (besselSeriesCoeff_pos hc n),
        abs_pow, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) hy' _) (Nat.cast_nonneg n))
        (besselSeriesCoeff_pos hc n).le)
    (y₀ := 0) ⟨by linarith, hr0⟩ (summable_besselSeries hc 0)
    (y := z) ⟨by linarith [neg_abs_le z, abs_nonneg z], by linarith [le_abs_self z]⟩
  refine hd.congr_deriv ?_
  have hs : Summable fun n : ℕ => (n : ℝ) * z ^ (n - 1) * besselSeriesCoeff c n := by
    rw [← summable_nat_add_iff 1]
    refine (summable_besselSeries (by linarith : 0 < c + 1) z).congr fun n => ?_
    rw [← besselSeriesCoeff_succ]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  unfold besselSeries
  refine tsum_congr fun n => ?_
  rw [← besselSeriesCoeff_succ]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  ring


lemma besselSeriesCoeff_rec {c : ℝ} (hc : 0 < c) (k : ℕ) :
    besselSeriesCoeff c (k + 1) =
      c * besselSeriesCoeff (c + 1) (k + 1) + besselSeriesCoeff (c + 2) k := by
  unfold besselSeriesCoeff
  have hk : (0 : ℝ) < c + k + 1 := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hG : 0 < Real.Gamma (c + k + 1) := Real.Gamma_pos_of_pos hk
  have e1 : c + ((k + 1 : ℕ) : ℝ) = c + k + 1 := by push_cast; ring
  have e2 : c + 1 + ((k + 1 : ℕ) : ℝ) = (c + k + 1) + 1 := by push_cast; ring
  have e3 : c + 2 + (k : ℝ) = (c + k + 1) + 1 := by ring
  rw [e1, e2, e3, Real.Gamma_add_one hk.ne', Nat.factorial_succ]
  push_cast
  have : (k ! : ℝ) ≠ 0 := by positivity
  have : ((k : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

lemma besselSeriesCoeff_zero_rec {c : ℝ} (hc : 0 < c) :
    besselSeriesCoeff c 0 = c * besselSeriesCoeff (c + 1) 0 := by
  unfold besselSeriesCoeff
  simp only [Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, add_zero, one_mul]
  rw [Real.Gamma_add_one hc.ne']
  have : Real.Gamma c ≠ 0 := (Real.Gamma_pos_of_pos hc).ne'
  field_simp

/-- `T_c = c T_{c+1} + z T_{c+2}`. -/
theorem besselSeries_recurrence {c : ℝ} (hc : 0 < c) (z : ℝ) :
    besselSeries c z = c * besselSeries (c + 1) z + z * besselSeries (c + 2) z := by
  unfold besselSeries
  have h0 := summable_besselSeries hc z
  have h1 := summable_besselSeries (by linarith : 0 < c + 1) z
  have h2 := summable_besselSeries (by linarith : 0 < c + 2) z
  have h1' : Summable fun k : ℕ => z ^ (k + 1) * besselSeriesCoeff (c + 1) (k + 1) :=
    (summable_nat_add_iff 1).mpr h1
  have hA : ∑' k : ℕ, z ^ (k + 1) * besselSeriesCoeff c (k + 1) =
      c * ∑' k : ℕ, z ^ (k + 1) * besselSeriesCoeff (c + 1) (k + 1) +
        ∑' k : ℕ, z * (z ^ k * besselSeriesCoeff (c + 2) k) := by
    rw [← tsum_mul_left, ← (h1'.mul_left c).tsum_add (h2.mul_left z)]
    refine tsum_congr fun k => ?_
    rw [besselSeriesCoeff_rec hc k]
    ring
  rw [h0.tsum_eq_zero_add, h1.tsum_eq_zero_add, hA, tsum_mul_left (a := z), besselSeriesCoeff_zero_rec hc]
  simp only [pow_zero, one_mul]
  ring


/-- `(besselNorm ν)'(x) = -(x / (2(ν+1))) besselNorm (ν+1) x` for `ν > -1`
(DLMF 10.6.2 in the normalisation `besselNorm`). -/
theorem hasDerivAt_besselNorm {ν : ℝ} (hν : -1 < ν) (x : ℝ) :
    HasDerivAt (besselNorm ν) (-(x / (2 * (ν + 1))) * besselNorm (ν + 1) x) x := by
  have hc : 0 < ν + 1 := by linarith
  have hin : HasDerivAt (fun x : ℝ => -(x / 2) ^ 2) (-(x / 2)) x := by
    have := (((hasDerivAt_id x).div_const 2).pow 2).neg
    refine this.congr_deriv ?_
    simp; ring
  have h := ((hasDerivAt_besselSeries hc (-(x / 2) ^ 2)).comp x hin).const_mul (Real.Gamma (ν + 1))
  have hfun : besselNorm ν = fun x => Real.Gamma (ν + 1) * besselSeries (ν + 1) (-(x / 2) ^ 2) :=
    funext fun x => besselNorm_eq_besselSeries ν x
  rw [hfun]
  refine h.congr_deriv ?_
  rw [besselNorm_eq_besselSeries (ν + 1), show ν + 1 + 1 = ν + 1 + 1 from rfl,
    show Real.Gamma (ν + 1 + 1) = (ν + 1) * Real.Gamma (ν + 1) from Real.Gamma_add_one hc.ne']
  have : (ν + 1) ≠ 0 := hc.ne'
  field_simp

/-- `besselNorm ν x = besselNorm (ν+1) x - x² / (4(ν+1)(ν+2)) besselNorm (ν+2) x`, `ν > -1`. -/
theorem besselNorm_recurrence {ν : ℝ} (hν : -1 < ν) (x : ℝ) :
    besselNorm ν x = besselNorm (ν + 1) x -
      x ^ 2 / (4 * (ν + 1) * (ν + 2)) * besselNorm (ν + 2) x := by
  have hc : 0 < ν + 1 := by linarith
  have h := besselSeries_recurrence hc (-(x / 2) ^ 2)
  rw [show ν + 1 + 2 = ν + 2 + 1 by ring] at h
  rw [besselNorm_eq_besselSeries ν, besselNorm_eq_besselSeries (ν + 1),
    besselNorm_eq_besselSeries (ν + 2), h]
  have e1 : Real.Gamma (ν + 1 + 1) = (ν + 1) * Real.Gamma (ν + 1) := Real.Gamma_add_one hc.ne'
  have e2 : Real.Gamma (ν + 2 + 1) = (ν + 2) * ((ν + 1) * Real.Gamma (ν + 1)) := by
    rw [Real.Gamma_add_one (by linarith), show ν + 2 = ν + 1 + 1 by ring, e1]
  rw [e1, e2]
  have h1 : (ν + 1) ≠ 0 := hc.ne'
  have h2 : (ν + 2) ≠ 0 := by linarith
  have h3 : Real.Gamma (ν + 1) ≠ 0 := (Real.Gamma_pos_of_pos hc).ne'
  have e3 : ν + 1 + 1 = ν + 1 + 1 := rfl
  generalize besselSeries (ν + 1 + 1) (-(x / 2) ^ 2) = A
  generalize besselSeries (ν + 2 + 1) (-(x / 2) ^ 2) = B
  generalize Real.Gamma (ν + 1) = G at *
  field_simp
  ring

/-- info: 'FormalResearch.Special.hasDerivAt_besselNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_besselNorm

/-- info: 'FormalResearch.Special.besselNorm_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselNorm_recurrence

end FormalResearch.Special
