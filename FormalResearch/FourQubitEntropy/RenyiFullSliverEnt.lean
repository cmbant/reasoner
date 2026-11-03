module

public import FormalResearch.FourQubitEntropy.RenyiFullRpow
public import FormalResearch.FourQubitEntropy.RenyiFullDefs
public import FormalResearch.FourQubitEntropy.RenyiFullDual

/-!
# Entropy estimates for the cluster sliver (`lem:fqe-cluster-sliver`)

Paper E, `sup_renyi.tex`, proof of `lem:fqe-cluster-sliver`, paragraph *Entropy estimates*, at the order
`q_s = 1587/1000`, `r = q_s - 1`, `L = ln 2`:

* `binary_ent` (SE): `-ln((1-u)^q + u^q) ≤ r L (K u - c_s u^{8/5} + (12/5) u²)` for `0 ≤ u ≤ 1/16`,
  `K = 7801/2000`, `c_s = 5/2`;
* `entS`, `entB` (SH): head/tail estimates for the two charts
  `((1-u+δ)/2, (1-u-δ)/2, u/2, u/2)` and `((1-u)/2, (1-u)/2, (u+δ)/2, (u-δ)/2)`.
-/

@[expose] public section


set_option exponentiation.threshold 5000

namespace FormalResearch.FourQubitEntropy.RenyiFull

open Finset

theorem qS_lt_two' : qS < 2 := by unfold qS; norm_num

theorem qS_gt_one : 1 < qS := by unfold qS; norm_num

/-! ### Taylor consequences for `(1+x)^q` -/

theorem cf_two (q : ℝ) : cf q 2 = q * (q - 1) / 2 := by
  simp [cf, ff, Nat.factorial]

theorem cf_three (q : ℝ) : cf q 3 = q * (q - 1) * (q - 2) / 6 := by
  simp [cf, ff, Nat.factorial]

theorem cf_four (q : ℝ) : cf q 4 = q * (q - 1) * (q - 2) * (q - 3) / 24 := by
  simp [cf, ff, Nat.factorial]

theorem cf_five (q : ℝ) : cf q 5 = q * (q - 1) * (q - 2) * (q - 3) * (q - 4) / 120 := by
  simp [cf, ff, Nat.factorial]

theorem taylor_sum (q x : ℝ) : ∑ k ∈ range 6, cf q k * x ^ k =
    1 + q * x + q * (q - 1) / 2 * x ^ 2 + q * (q - 1) * (q - 2) / 6 * x ^ 3 +
      q * (q - 1) * (q - 2) * (q - 3) / 24 * x ^ 4 +
      q * (q - 1) * (q - 2) * (q - 3) * (q - 4) / 120 * x ^ 5 := by
  simp only [sum_range_succ, sum_range_zero]
  rw [cf_two, cf_three, cf_four, cf_five]
  simp [cf, ff]

/-- `(1 - u)^q ≥ 1 - q u + q(q-1)u²/2` for `1 < q < 2`, `0 ≤ u ≤ 1`. -/
theorem one_sub_rpow_ge {q : ℝ} (h1 : 1 < q) (h2 : q < 2) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    1 - q * u + q * (q - 1) / 2 * u ^ 2 ≤ (1 - u) ^ q := by
  have h := taylor_rpow h1 h2 (u := -u) (by linarith)
  rw [taylor_sum] at h
  have e : (1 + -u) = 1 - u := by ring
  rw [e] at h
  have a1 : 0 < q := by linarith
  have a2 : 0 < q - 1 := by linarith
  have a3 : q - 2 < 0 := by linarith
  have a4 : q - 3 < 0 := by linarith
  have a5 : q - 4 < 0 := by linarith
  have t3 : 0 ≤ q * (q - 1) * (q - 2) / 6 * u ^ 3 * (-1) := by
    have : q * (q - 1) * (q - 2) ≤ 0 := by
      have := mul_pos a1 a2
      nlinarith
    have h3 := pow_nonneg hu0 3
    nlinarith
  have t4 : 0 ≤ q * (q - 1) * (q - 2) * (q - 3) / 24 * u ^ 4 := by
    have : 0 ≤ q * (q - 1) * (q - 2) * (q - 3) := by
      have := mul_pos (mul_pos a1 a2) (mul_pos_of_neg_of_neg a3 a4)
      linarith
    have := pow_nonneg hu0 4
    positivity
  have t5 : 0 ≤ q * (q - 1) * (q - 2) * (q - 3) * (q - 4) / 120 * u ^ 5 * (-1) := by
    have : q * (q - 1) * (q - 2) * (q - 3) * (q - 4) ≤ 0 := by
      have := mul_pos (mul_pos a1 a2) (mul_pos_of_neg_of_neg a3 a4)
      nlinarith
    have h5 := pow_nonneg hu0 5
    nlinarith
  nlinarith [h, t3, t4, t5]

/-- Symmetric second-order lower bound: `(a+δ)^q + (a-δ)^q ≥ 2a^q + q(q-1)a^{q-2}δ²`
for `1 < q < 2`, `0 < a`, `0 ≤ δ ≤ a`. -/
theorem sym_taylor {q : ℝ} (h1 : 1 < q) (h2 : q < 2) {a δ : ℝ} (ha : 0 < a) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ a) :
    2 * a ^ q + q * (q - 1) * a ^ (q - 2) * δ ^ 2 ≤ (a + δ) ^ q + (a - δ) ^ q := by
  obtain ⟨w, hw0, hw1, rfl⟩ : ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ δ = a * w :=
    ⟨δ / a, div_nonneg hδ0 ha.le, (div_le_one ha).2 hδ, by field_simp⟩
  have tp := taylor_rpow h1 h2 (u := w) (by linarith)
  have tm := taylor_rpow h1 h2 (u := -w) (by linarith)
  rw [taylor_sum] at tp tm
  have e1 : (1 + -w) = 1 - w := by ring
  rw [e1] at tm
  have a1 : 0 < q := by linarith
  have a2 : 0 < q - 1 := by linarith
  have a3 : q - 2 < 0 := by linarith
  have a4 : q - 3 < 0 := by linarith
  have c4 : 0 ≤ q * (q - 1) * (q - 2) * (q - 3) / 24 * w ^ 4 := by
    have : 0 ≤ q * (q - 1) * (q - 2) * (q - 3) := by
      have := mul_pos (mul_pos a1 a2) (mul_pos_of_neg_of_neg a3 a4)
      linarith
    have := pow_nonneg hw0 4
    positivity
  have hs : 2 + q * (q - 1) * w ^ 2 ≤ (1 + w) ^ q + (1 - w) ^ q := by
    nlinarith [tp, tm, c4]
  have m1 : (a + a * w) ^ q = a ^ q * (1 + w) ^ q := by
    rw [show a + a * w = a * (1 + w) by ring, Real.mul_rpow ha.le (by linarith)]
  have m2 : (a - a * w) ^ q = a ^ q * (1 - w) ^ q := by
    rw [show a - a * w = a * (1 - w) by ring, Real.mul_rpow ha.le (by linarith)]
  have m3 : a ^ q = a ^ (q - 2) * a ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ha]; norm_num
  rw [m1, m2]
  have hq0 : 0 < a ^ q := Real.rpow_pos_of_pos ha _
  have : a ^ q * (2 + q * (q - 1) * w ^ 2) ≤ a ^ q * ((1 + w) ^ q + (1 - w) ^ q) :=
    mul_le_mul_of_nonneg_left hs hq0.le
  calc 2 * a ^ q + q * (q - 1) * a ^ (q - 2) * (a * w) ^ 2
      = a ^ q * (2 + q * (q - 1) * w ^ 2) := by rw [m3]; ring
    _ ≤ _ := by rw [mul_add]; linarith

/-! ### Numerical rpow comparisons at `q_s` -/

theorem u_pow_small {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16) : u ^ ((13 : ℝ) / 1000) ≤ 50 / 51 := by
  have h1 : u ^ ((13 : ℝ) / 1000) ≤ (1 / 16 : ℝ) ^ ((13 : ℝ) / 1000) :=
    Real.rpow_le_rpow hu0 hu1 (by norm_num)
  have h2 := rpow_le_of_le_pow (x := (1 / 16 : ℝ)) (b := 50 / 51) (m := 13) (n := 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 : ((13 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) = (13 : ℝ) / 1000 := by norm_num
  rw [h3] at h2
  linarith

theorem u_pow_q_ge {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16) :
    51 / 50 * u ^ (8 / 5 : ℝ) ≤ u ^ qS := by
  rcases hu0.eq_or_lt with h | h
  · subst h
    rw [Real.zero_rpow (by norm_num), Real.zero_rpow (by unfold qS; norm_num)]; norm_num
  · have e : qS = 8 / 5 + -((13 : ℝ) / 1000) := by unfold qS; norm_num
    rw [e, Real.rpow_add h, Real.rpow_neg h.le]
    have hs := u_pow_small hu0 hu1
    have hp : 0 < u ^ ((13 : ℝ) / 1000) := Real.rpow_pos_of_pos h _
    have : (51 / 50 : ℝ) ≤ (u ^ ((13 : ℝ) / 1000))⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hp]
      calc u ^ ((13 : ℝ) / 1000) ≤ 50 / 51 := hs
        _ = (51 / 50 : ℝ)⁻¹ := by norm_num
    have hy : 0 ≤ u ^ (8 / 5 : ℝ) := Real.rpow_nonneg h.le _
    nlinarith

theorem u_pow_r_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16) : u ^ ((587 : ℝ) / 1000) ≤ 2 / 9 := by
  have h1 : u ^ ((587 : ℝ) / 1000) ≤ (1 / 16 : ℝ) ^ ((587 : ℝ) / 1000) :=
    Real.rpow_le_rpow hu0 hu1 (by norm_num)
  have h2 := rpow_le_of_le_pow (x := (1 / 16 : ℝ)) (b := 2 / 9) (m := 587) (n := 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 : ((587 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) = (587 : ℝ) / 1000 := by norm_num
  rw [h3] at h2
  linarith

theorem u_pow_q_le_u {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : u ^ qS ≤ u :=
  Real.rpow_le_self_of_le_one hu0 hu1 qS_gt_one.le

theorem u_pow_q_le_ninth {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16) : u ^ qS ≤ 2 / 9 * u := by
  have e : qS = 1 + (587 : ℝ) / 1000 := by unfold qS; norm_num
  rw [e, Real.rpow_add' hu0 (by norm_num), Real.rpow_one]
  have := u_pow_r_le hu0 hu1
  nlinarith

/-- The two bounds for `ln 2` used throughout. -/
theorem log2_bounds : 693147 / 1000000 < Real.log 2 ∧ Real.log 2 < 693148 / 1000000 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

/-! ### The binary entropy (SE) -/

theorem binary_ent {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16) :
    -Real.log ((1 - u) ^ qS + u ^ qS) ≤
      (qS - 1) * Real.log 2 * (39005 / 10000 * u - 5 / 2 * u ^ (8 / 5 : ℝ) + 12 / 5 * u ^ 2) := by
  obtain ⟨hL1, hL2⟩ := log2_bounds
  have hq1 := qS_gt_one
  have hq2 := qS_lt_two'
  have hT := one_sub_rpow_ge hq1 hq2 hu0 (by linarith : u ≤ 1)
  have hqle : u ^ qS ≤ u := u_pow_q_le_u hu0 (by linarith)
  have hq0 : 0 ≤ u ^ qS := Real.rpow_nonneg hu0 _
  have hq1' : (1 - u) ^ qS ≤ 1 - u :=
    Real.rpow_le_self_of_le_one (by linarith) (by linarith) hq1.le
  have hy := u_pow_q_ge hu0 hu1
  have hy0 : 0 ≤ u ^ (8 / 5 : ℝ) := Real.rpow_nonneg hu0 _
  set M := (1 - u) ^ qS + u ^ qS with hM
  set z := qS * u - qS * (qS - 1) / 2 * u ^ 2 - u ^ qS with hz
  have qv : qS = 1587 / 1000 := rfl
  have hMz : 1 - z ≤ M := by rw [hM, hz]; linarith
  have hM1 : M ≤ 1 := by rw [hM]; linarith
  have hz0 : 0 ≤ z := by linarith
  have hzq : z ≤ qS * u := by
    have : 0 ≤ qS * (qS - 1) / 2 * u ^ 2 := by positivity
    rw [hz]; linarith
  have hqu : qS * u ≤ qS / 16 := by nlinarith
  have hz1 : z < 1 := by rw [qv] at hqu hzq; linarith
  have hlog : Real.log (1 - z) ≤ Real.log M := Real.log_le_log (by linarith) hMz
  have hlz := neg_log_one_sub_le hz0 hz1
  have hden : 2 * (1 - qS / 16) ≤ 2 * (1 - z) := by linarith
  have hfrac : z ^ 2 / (2 * (1 - z)) ≤ qS ^ 2 * u ^ 2 / (2 * (1 - qS / 16)) := by
    have hnum : z ^ 2 ≤ qS ^ 2 * u ^ 2 := by
      have : z ^ 2 ≤ (qS * u) ^ 2 := pow_le_pow_left₀ hz0 hzq 2
      nlinarith
    have hp : 0 < 2 * (1 - qS / 16) := by rw [qv]; norm_num
    calc z ^ 2 / (2 * (1 - z)) ≤ qS ^ 2 * u ^ 2 / (2 * (1 - z)) :=
          div_le_div_of_nonneg_right hnum (by linarith)
      _ ≤ qS ^ 2 * u ^ 2 / (2 * (1 - qS / 16)) :=
          div_le_div_of_nonneg_left (by positivity) hp hden
  have hTh : qS ^ 2 * u ^ 2 / (2 * (1 - qS / 16)) ≤ 1398 / 1000 * u ^ 2 := by
    rw [div_le_iff₀ (by rw [qv]; norm_num), qv]
    nlinarith [sq_nonneg u]
  have hC2 : qS * (qS - 1) / 2 = 931569 / 2000000 := by rw [qv]; norm_num
  have hL : 0 < Real.log 2 := by linarith
  have ha : qS ≤ (qS - 1) * Real.log 2 * (39005 / 10000) := by rw [qv]; nlinarith
  have hb : (qS - 1) * Real.log 2 * (5 / 2) ≤ 51 / 50 := by rw [qv]; nlinarith
  have hc : 1398 / 1000 - 931569 / 2000000 ≤ (qS - 1) * Real.log 2 * (12 / 5) := by
    rw [qv]; nlinarith
  have h1 := mul_le_mul_of_nonneg_right ha hu0
  have h2 := mul_le_mul_of_nonneg_right hb hy0
  have h3 := mul_le_mul_of_nonneg_right hc (sq_nonneg u)
  have hneg : -Real.log M ≤ -Real.log (1 - z) := by linarith
  have hfin : -Real.log M ≤ z + 1398 / 1000 * u ^ 2 := by linarith
  rw [hC2] at hz
  linarith [h1, h2, h3, hfin, hy, hz]

/-! ### Head estimate, chart `S` -/

/-- Final numerical step of the head estimate (chart `S`). -/
theorem head_numeric {u v ζ Lg : ℝ} (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hL1 : 693147 / 1000000 < Lg)
    (hL2 : Lg < 693148 / 1000000) (hlo : 931569 / 2000000 * (1 + 3 / 2 * u) * v ≤ ζ) (hζ0 : 0 ≤ ζ)
    (hup : ζ ≤ 27 / 50 * v) :
    (qS - 1) * Lg * (113 / 100 * v + 3 / 2 * u * v - 3 / 8 * v ^ 2) ≤ ζ - ζ ^ 2 / 2 := by
  have qv : qS = 1587 / 1000 := rfl
  have hz2 : ζ ^ 2 ≤ (27 / 50 * v) ^ 2 := pow_le_pow_left₀ hζ0 hup 2
  have hc : (qS - 1) * Lg * (113 / 100) ≤ 931569 / 2000000 := by rw [qv]; linarith
  have hc' : (qS - 1) * Lg ≤ 931569 / 2000000 := by rw [qv]; linarith
  have hc'' : (27 / 50) ^ 2 / 2 ≤ (qS - 1) * Lg * (3 / 8) := by rw [qv]; linarith
  have k1 := mul_le_mul_of_nonneg_right hc hv0
  have k2 := mul_le_mul_of_nonneg_right hc' (mul_nonneg hu0 hv0)
  have k3 := mul_le_mul_of_nonneg_right hc'' (sq_nonneg v)
  nlinarith [k1, k2, k3, hz2, hlo]


/-- Pure algebra for the head factor: `(1 + 3u/2) M ≤ X` for `M = X(1-u)² + w`, `0 ≤ w ≤ 2u/9`. -/
theorem head_alg_lo {u X w : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16) (hX : 1 ≤ X) (hw : w ≤ 2 / 9 * u) :
    (1 + 3 / 2 * u) * (X * (1 - u) ^ 2 + w) ≤ X := by
  have e1 : 0 ≤ 1 / 2 * u + 2 * u ^ 2 - 3 / 2 * u ^ 3 := by nlinarith [sq_nonneg u, mul_nonneg hu0 hu0]
  have e2 : (1 / 2 * u + 2 * u ^ 2 - 3 / 2 * u ^ 3) ≤ X * (1 / 2 * u + 2 * u ^ 2 - 3 / 2 * u ^ 3) := by
    nlinarith
  have e3 : (1 + 3 / 2 * u) * w ≤ (1 + 3 / 2 * u) * (2 / 9 * u) :=
    mul_le_mul_of_nonneg_left hw (by linarith)
  nlinarith


theorem head_S {u δ v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16) (hδ0 : 0 ≤ δ) (hvδ : v = δ ^ 2)
    (hv : v ≤ 1 / 20) :
    (qS - 1) * Real.log 2 * (113 / 100 * v + 3 / 2 * u * v - 3 / 8 * v ^ 2) ≤
      Real.log (((1 - u + δ) ^ qS + (1 - u - δ) ^ qS) / 2 + u ^ qS) -
        Real.log ((1 - u) ^ qS + u ^ qS) := by
  obtain ⟨hL1, hL2⟩ := log2_bounds
  have hq1 := qS_gt_one
  have hq2 := qS_lt_two'
  have qv : qS = 1587 / 1000 := rfl
  have hA1 : 0 < 1 - u := by linarith
  have hA15 : 15 / 16 ≤ 1 - u := by linarith
  have hδle : δ ≤ 1 - u := by nlinarith [sq_nonneg (δ - 1 / 4)]
  have hv0 : 0 ≤ v := by rw [hvδ]; positivity
  have hsym := sym_taylor hq1 hq2 hA1 hδ0 hδle
  set X := (1 - u) ^ (qS - 2) with hX
  have hXpos : 0 < X := Real.rpow_pos_of_pos hA1 _
  have hX1 : 1 ≤ X := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hA1 (by linarith) (by linarith)
  have hAq : (1 - u) ^ qS = X * (1 - u) ^ 2 := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_add hA1]; norm_num
  have huq0 : 0 ≤ u ^ qS := Real.rpow_nonneg hu0 _
  have huq := u_pow_q_le_ninth hu0 hu1
  set M := (1 - u) ^ qS + u ^ qS with hM
  have hMpos : 0 < M := by
    have : 0 < (1 - u) ^ qS := Real.rpow_pos_of_pos hA1 _
    rw [hM]; linarith
  set N := ((1 - u + δ) ^ qS + (1 - u - δ) ^ qS) / 2 + u ^ qS with hN
  have hc1 : qS * (qS - 1) / 2 = 931569 / 2000000 := by rw [qv]; norm_num
  have hNM : M + 931569 / 2000000 * X * v ≤ N := by
    have : qS * (qS - 1) * X * δ ^ 2 = 2 * (931569 / 2000000) * X * v := by
      rw [hvδ, ← hc1]; ring
    rw [hN, hM]
    nlinarith [hsym, this]
  set ζ := 931569 / 2000000 * X * v / M with hζ
  have hζ0 : 0 ≤ ζ := by positivity
  have hN1 : 1 + ζ ≤ N / M := by
    rw [le_div_iff₀ hMpos, hζ]
    have : (1 + 931569 / 2000000 * X * v / M) * M = M + 931569 / 2000000 * X * v := by
      field_simp
    rw [this]; exact hNM
  have hup : ζ ≤ 27 / 50 * v := by
    rw [hζ, div_le_iff₀ hMpos]
    have hMX : X * (1 - u) ^ 2 ≤ M := by rw [hM, ← hAq]; linarith
    have h1 : X * (225 / 256) ≤ X * (1 - u) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hXpos.le
      nlinarith
    have h2 : 931569 / 2000000 * X ≤ 27 / 50 * M := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h2 hv0]
  have hlo : 931569 / 2000000 * (1 + 3 / 2 * u) * v ≤ ζ := by
    rw [hζ, le_div_iff₀ hMpos]
    have hMu : M ≤ X * (1 - u) ^ 2 + 2 / 9 * u := by rw [hM, hAq]; linarith
    have h1 : (1 + 3 / 2 * u) * M ≤ X := by
      have := head_alg_lo (w := u ^ qS) hu0 hu1 hX1 huq
      calc (1 + 3 / 2 * u) * M = (1 + 3 / 2 * u) * (X * (1 - u) ^ 2 + u ^ qS) := by rw [hM, hAq]
        _ ≤ X := this
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 931569 / 2000000 * v)
    nlinarith [h2]
  have hNpos : 0 < N := by
    have : 0 ≤ 931569 / 2000000 * X * v := by positivity
    linarith
  have hlogN : Real.log (1 + ζ) ≤ Real.log (N / M) := Real.log_le_log (by linarith) hN1
  have hζ1 : ζ ≤ 1 := by linarith
  have hl2 := log_ge_taylor2 hζ0 hζ1
  rw [Real.log_div hNpos.ne' hMpos.ne'] at hlogN
  have := head_numeric hu0 hv0 hL1 hL2 hlo hζ0 hup
  linarith

/-! ### Tail estimate, chart `B` -/

theorem u_pow_neg_ge {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1 / 30) : 3 ≤ u ^ (qS - 2) := by
  have e : qS - 2 = -((413 : ℝ) / 1000) := by unfold qS; norm_num
  rw [e, Real.rpow_neg hu0.le]
  have h1 : u ^ ((413 : ℝ) / 1000) ≤ (1 / 30 : ℝ) ^ ((413 : ℝ) / 1000) :=
    Real.rpow_le_rpow hu0.le hu1 (by norm_num)
  have h2 := rpow_le_of_le_pow (x := (1 / 30 : ℝ)) (b := 1 / 3) (m := 413) (n := 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 : ((413 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) = (413 : ℝ) / 1000 := by norm_num
  rw [h3] at h2
  have hp : 0 < u ^ ((413 : ℝ) / 1000) := Real.rpow_pos_of_pos hu0 _
  rw [le_inv_comm₀ (by norm_num) hp]
  calc u ^ ((413 : ℝ) / 1000) ≤ 1 / 3 := by linarith
    _ = (3 : ℝ)⁻¹ := by norm_num

/-- Final numerical step of the tail estimate (chart `B`). -/
theorem tail_numeric {v ζ Lg : ℝ} (hv0 : 0 ≤ v) (hL2 : Lg < 693148 / 1000000)
    (hlo : 3 * (931569 / 2000000) * v ≤ ζ) (hup : ζ ≤ 1 / 50) :
    (qS - 1) * Lg * (3 * v) ≤ ζ - ζ ^ 2 / 2 := by
  have qv : qS = 1587 / 1000 := rfl
  have hζ0 : 0 ≤ ζ := le_trans (by positivity) hlo
  have h1 : ζ ^ 2 ≤ 1 / 50 * ζ := by nlinarith
  have hc : (qS - 1) * Lg * 3 ≤ 3 * (931569 / 2000000) * (99 / 100) := by rw [qv]; nlinarith
  have k := mul_le_mul_of_nonneg_right hc hv0
  nlinarith [k, h1, hlo]

theorem head_B {u δ v : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1 / 30) (hδ0 : 0 ≤ δ) (hδu : δ ≤ u)
    (hvδ : v = δ ^ 2) :
    (qS - 1) * Real.log 2 * (3 * v) ≤
      Real.log ((1 - u) ^ qS + ((u + δ) ^ qS + (u - δ) ^ qS) / 2) -
        Real.log ((1 - u) ^ qS + u ^ qS) := by
  obtain ⟨hL1, hL2⟩ := log2_bounds
  have hq1 := qS_gt_one
  have hq2 := qS_lt_two'
  have qv : qS = 1587 / 1000 := rfl
  have hA1 : 0 < 1 - u := by linarith
  have hv0 : 0 ≤ v := by rw [hvδ]; positivity
  have hsym := sym_taylor hq1 hq2 hu0 hδ0 hδu
  set Y := u ^ (qS - 2) with hY
  have hY3 : 3 ≤ Y := u_pow_neg_ge hu0 hu1
  have hYq : u ^ qS = Y * u ^ 2 := by
    rw [hY, ← Real.rpow_natCast, ← Real.rpow_add hu0]; norm_num
  have huq0 : 0 ≤ u ^ qS := Real.rpow_nonneg hu0.le _
  have huq := u_pow_q_le_u hu0.le (by linarith)
  have hT := one_sub_rpow_ge hq1 hq2 hu0.le (by linarith : u ≤ 1)
  have hq1' : (1 - u) ^ qS ≤ 1 - u :=
    Real.rpow_le_self_of_le_one (by linarith) (by linarith) hq1.le
  set M := (1 - u) ^ qS + u ^ qS with hM
  have hM1 : M ≤ 1 := by rw [hM]; linarith
  have hM9 : 9 / 10 ≤ M := by
    have h0 : 0 ≤ qS * (qS - 1) / 2 * u ^ 2 := by positivity
    have hqu : qS * u ≤ 1587 / 1000 * (1 / 30) := by
      rw [qv]; exact mul_le_mul_of_nonneg_left hu1 (by norm_num)
    rw [hM]; linarith
  have hMpos : 0 < M := by linarith
  set N := (1 - u) ^ qS + ((u + δ) ^ qS + (u - δ) ^ qS) / 2 with hN
  have hc1 : qS * (qS - 1) / 2 = 931569 / 2000000 := by rw [qv]; norm_num
  have hNM : M + 931569 / 2000000 * Y * v ≤ N := by
    have : qS * (qS - 1) * Y * δ ^ 2 = 2 * (931569 / 2000000) * Y * v := by
      rw [hvδ, ← hc1]; ring
    rw [hN, hM]
    nlinarith [hsym, this]
  set ζ := 931569 / 2000000 * Y * v / M with hζ
  have hζ0 : 0 ≤ ζ := by positivity
  have hN1 : 1 + ζ ≤ N / M := by
    rw [le_div_iff₀ hMpos, hζ]
    have : (1 + 931569 / 2000000 * Y * v / M) * M = M + 931569 / 2000000 * Y * v := by
      field_simp
    rw [this]; exact hNM
  have hlo : 3 * (931569 / 2000000) * v ≤ ζ := by
    rw [hζ, le_div_iff₀ hMpos]
    have h1 : 3 * (931569 / 2000000) * v * M ≤ 3 * (931569 / 2000000) * v := by
      have : 0 ≤ 3 * (931569 / 2000000) * v := by positivity
      nlinarith
    have h2 : 3 * (931569 / 2000000) * v ≤ 931569 / 2000000 * Y * v := by
      have := mul_le_mul_of_nonneg_right hY3 (by positivity : (0 : ℝ) ≤ 931569 / 2000000 * v)
      nlinarith
    linarith
  have hup : ζ ≤ 1 / 50 := by
    rw [hζ, div_le_iff₀ hMpos]
    have hvu : v ≤ u ^ 2 := by
      rw [hvδ]; exact pow_le_pow_left₀ hδ0 hδu 2
    have h1 : Y * v ≤ u := by
      have := mul_le_mul_of_nonneg_left hvu (by linarith : 0 ≤ Y)
      rw [← hYq] at this; linarith
    have h2 : 931569 / 2000000 * Y * v ≤ 931569 / 2000000 * (1 / 30) := by
      have : 931569 / 2000000 * (Y * v) ≤ 931569 / 2000000 * (1 / 30) :=
        mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
      linarith
    nlinarith
  have hNpos : 0 < N := by
    have : 0 ≤ 931569 / 2000000 * Y * v := by positivity
    linarith
  have hlogN : Real.log (1 + ζ) ≤ Real.log (N / M) := Real.log_le_log (by linarith) hN1
  have hl2 := log_ge_taylor2 hζ0 (by linarith)
  rw [Real.log_div hNpos.ne' hMpos.ne'] at hlogN
  have := tail_numeric hv0 hL2 hlo hup
  linarith

/-! ### Assembly: the entropy of the two charts -/

/-- `renyiSpec` from `ln N`, for a four-point sum `Σ μᵢ^q = 2N/2^q`. -/
theorem renyiSpec_of_sum {μ : Fin 4 → ℝ} {N R : ℝ} (hN : 0 < N)
    (hsum : ∑ i, μ i ^ qS = 2 * N / (2 : ℝ) ^ qS)
    (hR : -Real.log N ≤ (qS - 1) * Real.log 2 * R) : renyiSpec qS μ ≤ 1 + R := by
  have hq1 := qS_gt_one
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr : 0 < (qS - 1) * Real.log 2 := mul_pos (by linarith) hL
  rw [renyiSpec_eq_neg hq1, hsum, div_le_iff₀ hr]
  have hT : (0 : ℝ) < (2 : ℝ) ^ qS := Real.rpow_pos_of_pos (by norm_num) _
  have hl : Real.log (2 * N / (2 : ℝ) ^ qS) = Real.log 2 + Real.log N - qS * Real.log 2 := by
    rw [Real.log_div (by positivity) hT.ne', Real.log_mul (by norm_num) hN.ne',
      Real.log_rpow (by norm_num)]
  rw [hl]
  nlinarith [hR]

theorem entS {u δ v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16) (hδ0 : 0 ≤ δ) (hvδ : v = δ ^ 2)
    (hv : v ≤ 1 / 20) :
    renyiSpec qS ![(1 - u + δ) / 2, (1 - u - δ) / 2, u / 2, u / 2] ≤
      1 + 39005 / 10000 * u - 5 / 2 * u ^ (8 / 5 : ℝ) + 12 / 5 * u ^ 2 -
        (113 / 100 * v + 3 / 2 * u * v - 3 / 8 * v ^ 2) := by
  have hδle : δ ≤ 1 - u := by nlinarith [sq_nonneg (δ - 1 / 4)]
  have hA1 : 0 < 1 - u := by linarith
  have hM : 0 < (1 - u) ^ qS + u ^ qS :=
    add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos hA1 _) (Real.rpow_nonneg hu0 _)
  have hh := head_S hu0 hu1 hδ0 hvδ hv
  have hb := binary_ent hu0 hu1
  set N := ((1 - u + δ) ^ qS + (1 - u - δ) ^ qS) / 2 + u ^ qS with hN
  have hpos : 0 < (1 - u) ^ qS + u ^ qS := hM
  have hNpos : 0 < N := by
    have h1 : 0 ≤ (1 - u + δ) ^ qS := Real.rpow_nonneg (by linarith) _
    have h2 : 0 ≤ (1 - u - δ) ^ qS := Real.rpow_nonneg (by linarith) _
    have h3 : 0 < u ^ qS ∨ u ^ qS = 0 := by
      rcases (Real.rpow_nonneg hu0 qS).eq_or_lt with h | h
      · exact Or.inr h.symm
      · exact Or.inl h
    have h4 : 0 < (1 - u + δ) ^ qS := Real.rpow_pos_of_pos (by linarith) _
    have := Real.rpow_nonneg hu0 qS
    rw [hN]; linarith
  have hsum : ∑ i, (![(1 - u + δ) / 2, (1 - u - δ) / 2, u / 2, u / 2] : Fin 4 → ℝ) i ^ qS =
      2 * N / (2 : ℝ) ^ qS := by
    simp only [Fin.sum_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [Real.div_rpow (by linarith) (by norm_num), Real.div_rpow (by linarith) (by norm_num),
      Real.div_rpow hu0 (by norm_num), hN]
    ring
  have := renyiSpec_of_sum (R := 39005 / 10000 * u - 5 / 2 * u ^ (8 / 5 : ℝ) + 12 / 5 * u ^ 2 -
    (113 / 100 * v + 3 / 2 * u * v - 3 / 8 * v ^ 2)) hNpos hsum (by nlinarith [hh, hb])
  linarith

theorem entB {u δ v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 30) (hδ0 : 0 ≤ δ) (hδu : δ ≤ u)
    (hvδ : v = δ ^ 2) :
    renyiSpec qS ![(1 - u) / 2, (1 - u) / 2, (u + δ) / 2, (u - δ) / 2] ≤
      1 + 39005 / 10000 * u - 5 / 2 * u ^ (8 / 5 : ℝ) + 12 / 5 * u ^ 2 - 3 * v := by
  rcases hu0.eq_or_lt with h | h
  · subst h
    have hd : δ = 0 := le_antisymm hδu hδ0
    subst hd
    have hv0 : v = 0 := by rw [hvδ]; norm_num
    subst hv0
    have : (![(1 - 0) / 2, (1 - 0) / 2, (0 + 0) / 2, (0 - 0) / 2] : Fin 4 → ℝ) = c1 := by
      funext i; fin_cases i <;> simp [c1]
    rw [this, renyiSpec_c1 (by linarith [qS_gt_one]) (ne_of_gt qS_gt_one)]
    rw [Real.zero_rpow (by norm_num)]
    norm_num
  · have hA1 : 0 < 1 - u := by linarith
    have hM : 0 < (1 - u) ^ qS + u ^ qS :=
      add_pos (Real.rpow_pos_of_pos hA1 _) (Real.rpow_pos_of_pos h _)
    have hh := head_B h hu1 hδ0 hδu hvδ
    have hb := binary_ent hu0 (by linarith)
    set N := (1 - u) ^ qS + ((u + δ) ^ qS + (u - δ) ^ qS) / 2 with hN
    have hNpos : 0 < N := by
      have h1 : 0 ≤ (u + δ) ^ qS := Real.rpow_nonneg (by linarith) _
      have h2 : 0 ≤ (u - δ) ^ qS := Real.rpow_nonneg (by linarith) _
      have h4 : 0 < (1 - u) ^ qS := Real.rpow_pos_of_pos hA1 _
      rw [hN]; linarith
    have hsum : ∑ i, (![(1 - u) / 2, (1 - u) / 2, (u + δ) / 2, (u - δ) / 2] : Fin 4 → ℝ) i ^ qS =
        2 * N / (2 : ℝ) ^ qS := by
      simp only [Fin.sum_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      rw [Real.div_rpow (by linarith) (by norm_num), Real.div_rpow (by linarith) (by norm_num),
        Real.div_rpow (by linarith) (by norm_num), hN]
      ring
    have := renyiSpec_of_sum (R := 39005 / 10000 * u - 5 / 2 * u ^ (8 / 5 : ℝ) + 12 / 5 * u ^ 2 - 3 * v)
      hNpos hsum (by nlinarith [hh, hb])
    linarith

end FormalResearch.FourQubitEntropy.RenyiFull
