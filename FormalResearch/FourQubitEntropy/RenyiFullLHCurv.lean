module

public import FormalResearch.FourQubitEntropy.RenyiFullLHCurvCells
public import FormalResearch.FourQubitEntropy.RenyiFullSliverEnt

/-!
# Large-head curvature: the bound on `h_aaaa` and the sign of `f_aaaa`

Paper E, `lem:fqe-large-head-curvature`.  For `1/2 ≤ a ≤ 4/5` and `K` in a range, `h_aaaa(a, K)` is bounded using the
quasi-convexity of `J(·)` in `y` (`lhJ_quasi`) between two rational envelopes of `y(a,K)`; the
envelopes come from the elementary estimates `ρ² ≤ ρ^q ≤ ρ (1+ρ)/2`, `ρ = (1-a)/a ∈ [1/4, 1]`
(a real-variable replacement of the paper's endpoint bounds by Cauchy's formula).
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.RenyiFull

open Set

theorem lhY_eq_rho {q K a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    lhY q K a = (1 - K * ((1 - a) / a) ^ q) / (1 + K * ((1 - a) / a) ^ q) := by
  have hq : 0 < a ^ q := Real.rpow_pos_of_pos ha q
  unfold lhY lhZ
  rw [Real.div_rpow (by linarith) ha.le]
  field_simp

theorem ydecr {w W : ℝ} (hw : 0 ≤ w) (hwW : w ≤ W) : (1 - W) / (1 + W) ≤ (1 - w) / (1 + w) := by
  have h1 : 0 < 1 + w := by linarith
  have h2 : 0 < 1 + W := by linarith
  rw [div_le_div_iff₀ h2 h1]
  nlinarith

theorem rho_rpow_le {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) : ρ ^ qS ≤ ρ := by
  have := Real.rpow_le_rpow_of_exponent_ge h0 h1 (show (1 : ℝ) ≤ qS by unfold qS; norm_num)
  simpa using this

theorem rho_sq_le_rpow {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) : ρ ^ 2 ≤ ρ ^ qS := by
  have := Real.rpow_le_rpow_of_exponent_ge h0 h1 (show qS ≤ (2 : ℝ) by unfold qS; norm_num)
  simpa using this

theorem rho_rpow_le_sqrt {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) : ρ ^ qS ≤ ρ * (1 + ρ) / 2 := by
  have h32 : ρ ^ qS ≤ ρ ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_ge h0 h1 (show (3 : ℝ) / 2 ≤ qS by unfold qS; norm_num)
  have e : ρ ^ ((3 : ℝ) / 2) = ρ * Real.sqrt ρ := by
    rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add h0, Real.rpow_one, Real.sqrt_eq_rpow]
  have hs := Real.sq_sqrt h0.le
  have : Real.sqrt ρ ≤ (1 + ρ) / 2 := by nlinarith [sq_nonneg (Real.sqrt ρ - 1)]
  have := mul_le_mul_of_nonneg_left this h0.le
  nlinarith


noncomputable def lhBd (M x : ℝ) : ℝ :=
  M * (587 / 1000 : ℝ) * (693147 / 1000000 : ℝ) * (1 - x ^ 2) ^ 4 / (16 * qS)

theorem lhdJ_at_x_nonpos {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 3 / 5) : lhdJ qS x x ≤ 0 := by
  have e : lhdJ qS x x = 8 * x * (qS - 1) * (3 * (qS - 1) ^ 2 * x ^ 2 - 2 * qS ^ 2 + qS + 3) := by
    unfold lhdJ; ring
  rw [e]
  have hq : qS = 1587 / 1000 := rfl
  have h2 : 3 * (qS - 1) ^ 2 * x ^ 2 - 2 * qS ^ 2 + qS + 3 ≤ 0 := by
    rw [hq]; nlinarith
  have h3 : 0 ≤ 8 * x * (qS - 1) := by rw [hq]; positivity
  exact mul_nonpos_of_nonneg_of_nonpos h3 h2

theorem lhJ_le_of_ends {x y1 y y2 B : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 3 / 5) (hy1 : x ≤ y1) (h12 : y1 ≤ y)
    (h2 : y ≤ y2) (e1 : lhJ qS x y1 ≤ B) (e2 : lhJ qS x y2 ≤ B) : lhJ qS x y ≤ B :=
  (lhJ_quasi (by unfold qS; norm_num) h0 (lhdJ_at_x_nonpos h0 h1) hy1 h12 h2).trans (max_le e1 e2)

/-- Common setting: `ρ = (1-a)/a`, `x = 2a-1`, `ρ = (1-x)/(1+x)`. -/
theorem rho_eq {a : ℝ} (ha : 0 < a) : (1 - a) / a = (1 - (2 * a - 1)) / (1 + (2 * a - 1)) := by
  field_simp
  ring

theorem lhY_ge_of_le {K a W : ℝ} (ha : 0 < a) (ha1 : a < 1) (hK : 0 ≤ K)
    (hw : K * ((1 - a) / a) ^ qS ≤ W) : (1 - W) / (1 + W) ≤ lhY qS K a := by
  rw [lhY_eq_rho ha ha1]
  have : 0 ≤ ((1 - a) / a) ^ qS := Real.rpow_nonneg (by apply div_nonneg <;> linarith) _
  exact ydecr (by positivity) hw

theorem lhY_le_of_ge {K a w0 : ℝ} (ha : 0 < a) (ha1 : a < 1) (hw0 : 0 ≤ w0)
    (hw : w0 ≤ K * ((1 - a) / a) ^ qS) : lhY qS K a ≤ (1 - w0) / (1 + w0) := by
  rw [lhY_eq_rho ha ha1]
  exact ydecr hw0 hw

/-- The upper envelope `y_h(x)` for `K ≥ 1/2`. -/
theorem lhY_le_yh {K a : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a < 1) (hK : 1 / 2 ≤ K) :
    lhY qS K a ≤
      ((1 + (2 * a - 1)) ^ 2 - (1 - (2 * a - 1)) ^ 2 / 2) /
        ((1 + (2 * a - 1)) ^ 2 + (1 - (2 * a - 1)) ^ 2 / 2) := by
  have ha0 : 0 < a := by linarith
  have hρ0 : 0 < (1 - a) / a := div_pos (by linarith) ha0
  have hρ1 : (1 - a) / a ≤ 1 := (div_le_one ha0).2 (by linarith)
  have h2 := rho_sq_le_rpow hρ0 hρ1
  have := lhY_le_of_ge (K := K) ha0 ha1 (w0 := 1 / 2 * ((1 - a) / a) ^ 2) (by positivity)
    (by nlinarith [sq_nonneg ((1 - a) / a), Real.rpow_nonneg hρ0.le qS])
  refine this.trans (le_of_eq ?_)
  rw [rho_eq ha0]
  have : 0 < 1 + (2 * a - 1) := by linarith
  field_simp


/-- Lower envelope `y_l^A(x)` for `K ≤ 61/80`. -/
theorem lhY_ge_ylA {K a : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a < 1) (hK0 : 0 ≤ K) (hK : K ≤ 61 / 80) :
    ((1 + (2 * a - 1)) - 61 / 80 * (1 - (2 * a - 1))) /
        ((1 + (2 * a - 1)) + 61 / 80 * (1 - (2 * a - 1))) ≤ lhY qS K a := by
  have ha0 : 0 < a := by linarith
  have hρ0 : 0 < (1 - a) / a := div_pos (by linarith) ha0
  have hρ1 : (1 - a) / a ≤ 1 := (div_le_one ha0).2 (by linarith)
  have h1 := rho_rpow_le hρ0 hρ1
  have := lhY_ge_of_le (K := K) (W := 61 / 80 * ((1 - a) / a)) ha0 ha1 hK0
    (by nlinarith [Real.rpow_nonneg hρ0.le qS])
  refine le_trans (le_of_eq ?_) this
  rw [rho_eq ha0]
  have : 0 < 1 + (2 * a - 1) := by linarith
  field_simp

theorem yB_alg {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 - (1 - x) / (1 + x) * (1 + (1 - x) / (1 + x)) / 2) / (1 + (1 - x) / (1 + x) * (1 + (1 - x) / (1 + x)) / 2) =
      ((1 + x) ^ 2 - (1 - x)) / ((1 + x) ^ 2 + (1 - x)) := by
  have h1 : 0 < 1 + x := by linarith
  have hW : (1 - x) / (1 + x) * (1 + (1 - x) / (1 + x)) / 2 = (1 - x) / (1 + x) ^ 2 := by
    field_simp
    ring
  rw [hW]
  have hD : (1 + x) ^ 2 + (1 - x) ≠ 0 := by nlinarith
  have hD2 : (1 + x) ^ 2 ≠ 0 := by positivity
  have hnn : 0 ≤ (1 - x) / (1 + x) ^ 2 := div_nonneg (by linarith) (by positivity)
  have hden : 1 + (1 - x) / (1 + x) ^ 2 ≠ 0 := by linarith
  rw [div_eq_div_iff hden hD]
  field_simp

/-- Lower envelope `y_l^B(x)` for `K ≤ 1`. -/
theorem lhY_ge_ylB {K a : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a < 1) (hK0 : 0 ≤ K) (hK : K ≤ 1) :
    ((1 + (2 * a - 1)) ^ 2 - (1 - (2 * a - 1))) /
        ((1 + (2 * a - 1)) ^ 2 + (1 - (2 * a - 1))) ≤ lhY qS K a := by
  have ha0 : 0 < a := by linarith
  have hρ0 : 0 < (1 - a) / a := div_pos (by linarith) ha0
  have hρ1 : (1 - a) / a ≤ 1 := (div_le_one ha0).2 (by linarith)
  have h1 := rho_rpow_le_sqrt hρ0 hρ1
  have hp := Real.rpow_nonneg hρ0.le qS
  have := lhY_ge_of_le (K := K) (W := ((1 - a) / a) * (1 + (1 - a) / a) / 2) ha0 ha1 hK0
    (by nlinarith)
  refine le_trans (le_of_eq ?_) this
  rw [rho_eq ha0]
  exact (yB_alg (x := 2 * a - 1) (by linarith) (by linarith)).symm

theorem x_le_ylA {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 3 / 5) :
    x ≤ ((1 + x) - 61 / 80 * (1 - x)) / ((1 + x) + 61 / 80 * (1 - x)) := by
  have hD : 0 < (1 + x) + 61 / 80 * (1 - x) := by nlinarith
  rw [le_div_iff₀ hD]
  nlinarith

theorem x_le_ylB {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 3 / 5) :
    x ≤ ((1 + x) ^ 2 - (1 - x)) / ((1 + x) ^ 2 + (1 - x)) := by
  have hD : 0 < (1 + x) ^ 2 + (1 - x) := by nlinarith
  rw [le_div_iff₀ hD]
  nlinarith [mul_nonneg (mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 1 - x)) (by linarith : (0 : ℝ) ≤ 1 + x)]

theorem yh_le_one {x : ℝ} (h0 : 0 ≤ x) (_h1 : x ≤ 3 / 5) :
    ((1 + x) ^ 2 - (1 - x) ^ 2 / 2) / ((1 + x) ^ 2 + (1 - x) ^ 2 / 2) ≤ 1 := by
  have hD : 0 < (1 + x) ^ 2 + (1 - x) ^ 2 / 2 := by nlinarith
  rw [div_le_one hD]
  nlinarith [sq_nonneg (1 - x)]

theorem lhBd_mono {M M' x : ℝ} (h : M ≤ M') : lhBd M x ≤ lhBd M' x := by
  unfold lhBd
  have : 0 ≤ (1 - x ^ 2) ^ 4 := by positivity
  have hq : 0 < 16 * qS := by unfold qS; norm_num
  apply div_le_div_of_nonneg_right _ hq.le
  nlinarith

/-- **`h_aaaa` numerator bound, case A**: `K ∈ [1/2, 61/80]`. -/
theorem lhJ_bound_A {K a : ℝ} (ha : 1 / 2 ≤ a) (ha' : a ≤ 4 / 5) (hK : 1 / 2 ≤ K) (hK' : K ≤ 61 / 80) :
    lhJ qS (2 * a - 1) (lhY qS K a) ≤ lhBd (1696 / 25) (2 * a - 1) := by
  have h0 : 0 ≤ 2 * a - 1 := by linarith
  have h1 : 2 * a - 1 ≤ 3 / 5 := by linarith
  have ha1 : a < 1 := by linarith
  refine lhJ_le_of_ends h0 h1 (x_le_ylA h0 h1) (lhY_ge_ylA ha ha1 (by linarith) hK') (lhY_le_yh ha ha1 hK)
    ?_ ?_
  · exact lh_poly_A h0 h1
  · exact lh_poly_H h0 h1

/-- **`h_aaaa` numerator bound, case B**: `K ∈ [1/2, 1]`. -/
theorem lhJ_bound_B {K a : ℝ} (ha : 1 / 2 ≤ a) (ha' : a ≤ 4 / 5) (hK : 1 / 2 ≤ K) (hK' : K ≤ 1) :
    lhJ qS (2 * a - 1) (lhY qS K a) ≤ lhBd (4293 / 50) (2 * a - 1) := by
  have h0 : 0 ≤ 2 * a - 1 := by linarith
  have h1 : 2 * a - 1 ≤ 3 / 5 := by linarith
  have ha1 : a < 1 := by linarith
  refine lhJ_le_of_ends h0 h1 (x_le_ylB h0 h1) (lhY_ge_ylB ha ha1 (by linarith) hK') (lhY_le_yh ha ha1 hK)
    ?_ ?_
  · exact lh_poly_B h0 h1
  · have h2 : lhBd (1696 / 25) (2 * a - 1) ≤ lhBd (4293 / 50) (2 * a - 1) := lhBd_mono (by norm_num)
    exact (lh_poly_H h0 h1).trans h2


/-- `h_aaaa < M` from the bound on `J`. -/
theorem hd4_lt_of_J {K a M : ℝ} (ha : 1 / 2 ≤ a) (ha' : a ≤ 4 / 5) (_hK : 0 < K)
    (hJ : lhJ qS (2 * a - 1) (lhY qS K a) ≤ lhBd M (2 * a - 1)) (hM : 0 < M) : hd4 qS K a < M := by
  have h0 : 0 ≤ 2 * a - 1 := by linarith
  have h1 : 2 * a - 1 ≤ 3 / 5 := by linarith
  have hx4 : 0 < (1 - (2 * a - 1) ^ 2) ^ 4 := by
    have : 0 < 1 - (2 * a - 1) ^ 2 := by nlinarith
    positivity
  have hq : qS = 1587 / 1000 := rfl
  have hL := log2_bounds
  have hr : 0 < qS - 1 := by rw [hq]; norm_num
  have hc : 0 < (qS - 1) * Real.log 2 := mul_pos hr (by linarith [hL.1])
  have e : hd4 qS K a = 16 * qS * lhJ qS (2 * a - 1) (lhY qS K a) /
      ((1 - (2 * a - 1) ^ 2) ^ 4 * ((qS - 1) * Real.log 2)) := by
    have hx4' := hx4.ne'
    have hc' := hc.ne'
    unfold hd4 lhm4
    field_simp
  rw [e, div_lt_iff₀ (mul_pos hx4 hc)]
  unfold lhBd at hJ
  rw [le_div_iff₀ (by rw [hq]; norm_num)] at hJ
  have hr' : qS - 1 = 587 / 1000 := by rw [hq]; norm_num
  rw [hr']
  rw [hr'] at hc
  nlinarith [mul_pos (mul_pos hM hx4) (sub_pos.2 hL.1)]

theorem f4_neg_A {K a B : ℝ} (ha : 1 / 2 ≤ a) (ha' : a ≤ 4 / 5) (hK : 1 / 2 ≤ K) (hK' : K ≤ 61 / 80)
    (hB : 1 / 3 ≤ B) : hd4 qS K a + Pg4 gL B < 0 := by
  have := hd4_lt_of_J ha ha' (by linarith) (lhJ_bound_A ha ha' hK hK') (by norm_num)
  unfold Pg4 gL
  nlinarith

theorem f4_neg_B {K a B : ℝ} (ha : 1 / 2 ≤ a) (ha' : a ≤ 4 / 5) (hK : 1 / 2 ≤ K) (hK' : K ≤ 1)
    (hB : 1 / 2 ≤ B) : hd4 qS K a + Pg4 gL B < 0 := by
  have := hd4_lt_of_J ha ha' (by linarith) (lhJ_bound_B ha ha' hK hK') (by norm_num)
  unfold Pg4 gL
  nlinarith

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.lhJ_bound_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lhJ_bound_A

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.lhJ_bound_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lhJ_bound_B

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.f4_neg_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms f4_neg_A

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.f4_neg_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms f4_neg_B

end FormalResearch.FourQubitEntropy.RenyiFull
