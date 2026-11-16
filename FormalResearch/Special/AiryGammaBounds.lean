module

public import FormalResearch.Special.AiryValues

/-!
# Rational enclosures of `Γ(1/3)`, `Γ(2/3)`, `Ai(0)` and `Ai'(0)`

The Taylor evaluation of `Ai` on the negative axis (`AiryZeroTaylor`) needs two-sided rational bounds on
`Ai(0) = 3^{-2/3}/Γ(2/3)` and `Ai'(0) = -3^{-1/3}/Γ(1/3)` (`airyAi_zero`, `airyAi'_zero`).  Only about
`1.5 %` accuracy is needed there, and a log-convexity argument gives it without any Stirling-type machinery:

* from the log-convexity of `Γ` (Mathlib `Real.BohrMollerup.f_add_nat_le/ge`, applied to `log ∘ Γ`), for
  `0 < x ≤ 1` and an integer `n ≥ 2`:
  `(n-1)! (n-1)^x ≤ Γ(n+x) ≤ (n-1)! n^x`  (`airyGamma_nat_add_le`, `airyGamma_nat_add_ge`);
* `Γ(x + n) = Γ(x) ∏_{j<n} (x + j)` (`airyGamma_add_nat`);
* with `n = 27` and `x = 1/3, 2/3` the powers `27^x ∈ {3, 9}` are integers; applying the upper bound at `n = 27`
  and the lower bound at `n = 28` gives
  `Γ(1/3) ∈ [2.6572…, 2.6900…]`, `Γ(2/3) ∈ [1.3269…, 1.3597…]` (true values `2.678938…`, `1.354117…`);
* `airyGamma_third_bounds`, `airyGamma_two_thirds_bounds`: the rounded enclosures
  `2.657 < Γ(1/3) < 2.691` and `1.326 < Γ(2/3) < 1.360`;
* `airyAi_zero_bounds`, `airyAi'_zero_bounds`: `0.3533 < Ai(0) < 0.3628` and
  `-0.2611 < Ai'(0) < -0.2576` (true values `0.355028…`, `-0.258819…`), using `3^{1/3} ∈ (1.442, 1.4423)`.

Numerically checked with mpmath (30 digits): `Γ(1/3) = 2.678938534707747…`, `Γ(2/3) = 1.354117939426400…`,
`Ai(0) = 0.355028053887817…`, `Ai'(0) = -0.258819403792806…`, and the exact rational endpoints of the
`n = 27` enclosure (`2.6572029…, 2.6900079…` and `1.3269265…, 1.3596901…`).  Not formalised: sharper bounds
(any accuracy is reachable by taking `n` a cube; the constants here are not optimal).
-/

@[expose] public section

open Real
open scoped Nat

namespace FormalResearch.Special

/-- `Γ(x + n) = Γ(x) ∏_{j<n}(x + j)` for `x > 0`. -/
lemma airyGamma_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.Gamma (x + n) = Real.Gamma x * ∏ j ∈ Finset.range n, (x + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpos : 0 < x + n := by positivity
    rw [show x + ((n + 1 : ℕ) : ℝ) = (x + n) + 1 by push_cast; ring,
      Real.Gamma_add_one hpos.ne', ih, Finset.prod_range_succ]
    ring

private lemma airyGamma_logconvex :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (Real.log ∘ Real.Gamma) := Real.convexOn_log_Gamma

private lemma airyGamma_feq {y : ℝ} (hy : 0 < y) :
    (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
  simp only [Function.comp_apply]
  rw [Real.Gamma_add_one hy.ne', Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
  ring

/-- Log-convexity upper bound: `Γ(n + x) ≤ (n-1)! n^x` for `0 < x ≤ 1`, `n ≥ 1`. -/
lemma airyGamma_nat_add_le {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) {n : ℕ} (hn : n ≠ 0) :
    Real.Gamma (n + x) ≤ ((n - 1)! : ℝ) * (n : ℝ) ^ x := by
  have h := Real.BohrMollerup.f_add_nat_le airyGamma_logconvex (fun {y} hy => airyGamma_feq hy) hn hx hx1
  simp only [Function.comp_apply] at h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hGn : Real.Gamma (n : ℝ) = ((n - 1)! : ℝ) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simpa using Real.Gamma_nat_eq_factorial m
  have hpos : 0 < Real.Gamma (n + x) := Real.Gamma_pos_of_pos (by positivity)
  have hGpos : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos hn0
  calc Real.Gamma (n + x) = Real.exp (Real.log (Real.Gamma (n + x))) := (Real.exp_log hpos).symm
    _ ≤ Real.exp (Real.log (Real.Gamma n) + x * Real.log n) := Real.exp_le_exp.mpr h
    _ = Real.Gamma n * (n : ℝ) ^ x := by
      rw [Real.exp_add, Real.exp_log hGpos, Real.rpow_def_of_pos hn0, mul_comm x]
    _ = _ := by rw [hGn]

/-- Log-convexity lower bound: `(n-1)! (n-1)^x ≤ Γ(n + x)` for `x > 0`, `n ≥ 2`. -/
lemma airyGamma_nat_add_ge {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 2 ≤ n) :
    ((n - 1)! : ℝ) * ((n : ℝ) - 1) ^ x ≤ Real.Gamma (n + x) := by
  have h := Real.BohrMollerup.f_add_nat_ge airyGamma_logconvex (fun {y} hy => airyGamma_feq hy) hn hx
  simp only [Function.comp_apply] at h
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hGn : Real.Gamma (n : ℝ) = ((n - 1)! : ℝ) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : n ≠ 0)
    simpa using Real.Gamma_nat_eq_factorial m
  have hGpos : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos (by linarith)
  have hpos : 0 < Real.Gamma (n + x) := Real.Gamma_pos_of_pos (by positivity)
  calc ((n - 1)! : ℝ) * ((n : ℝ) - 1) ^ x = Real.exp (Real.log (Real.Gamma n) + x * Real.log ((n : ℝ) - 1)) := by
        rw [Real.exp_add, Real.exp_log hGpos, Real.rpow_def_of_pos hn0, mul_comm x, hGn]
    _ ≤ Real.exp (Real.log (Real.Gamma (n + x))) := Real.exp_le_exp.mpr h
    _ = _ := Real.exp_log hpos

lemma airyGamma_rpow_third : (27 : ℝ) ^ (1 / 3 : ℝ) = 3 := by
  rw [show (27 : ℝ) = 3 ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

lemma airyGamma_rpow_two_thirds : (27 : ℝ) ^ (2 / 3 : ℝ) = 9 := by
  rw [show (27 : ℝ) = 3 ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `Γ(x)` from the `n = 27` enclosure: `27! 27^x/((27 + x) Π) ≤ Γ(x) ≤ 26! 27^x/Π`,
`Π = ∏_{j<27}(x + j)`, for `x` with `27^x = c`. -/
lemma airyGamma_enclosure {x c : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hc : (27 : ℝ) ^ x = c) :
    (27 ! : ℝ) * c / ((27 + x) * ∏ j ∈ Finset.range 27, (x + j)) ≤ Real.Gamma x ∧
      Real.Gamma x ≤ (26 ! : ℝ) * c / ∏ j ∈ Finset.range 27, (x + j) := by
  have hP : 0 < ∏ j ∈ Finset.range 27, (x + (j : ℝ)) :=
    Finset.prod_pos fun j _ => by positivity
  have hup := airyGamma_nat_add_le hx hx1 (n := 27) (by norm_num)
  have hlo := airyGamma_nat_add_ge hx (n := 28) (by norm_num)
  rw [add_comm, airyGamma_add_nat hx] at hup
  have e27 : ((27 : ℕ) : ℝ) = 27 := by norm_num
  have e28 : ((28 : ℕ) : ℝ) - 1 = 27 := by norm_num
  rw [e27, hc] at hup
  rw [e28, hc] at hlo
  have h28 : Real.Gamma (x + ((28 : ℕ) : ℝ)) = (x + 27) * Real.Gamma (x + 27) := by
    rw [show (x + ((28 : ℕ) : ℝ)) = (x + 27) + 1 by norm_num; ring,
      Real.Gamma_add_one (by positivity)]
  have h27 : Real.Gamma (x + 27) = Real.Gamma x * ∏ j ∈ Finset.range 27, (x + j) := by
    have := airyGamma_add_nat hx 27
    simpa using this
  rw [add_comm, h28, h27] at hlo
  have f28 : (((28 - 1 : ℕ)! : ℕ) : ℝ) = (27 ! : ℝ) := by norm_num
  have f26 : (((27 - 1 : ℕ)! : ℕ) : ℝ) = (26 ! : ℝ) := by norm_num
  rw [f28] at hlo
  rw [f26] at hup
  constructor
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [hlo]
  · rw [le_div_iff₀ hP]
    nlinarith [hup]

/-- `2.657 < Γ(1/3) < 2.691`. -/
theorem airyGamma_third_bounds : 2.657 < Real.Gamma (1 / 3) ∧ Real.Gamma (1 / 3) < 2.691 := by
  obtain ⟨h1, h2⟩ := airyGamma_enclosure (x := 1 / 3) (c := 3) (by norm_num) (by norm_num)
    airyGamma_rpow_third
  constructor
  · refine lt_of_lt_of_le ?_ h1
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    norm_num [Nat.factorial]
  · refine lt_of_le_of_lt h2 ?_
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    norm_num [Nat.factorial]

/-- `1.326 < Γ(2/3) < 1.360`. -/
theorem airyGamma_two_thirds_bounds : 1.326 < Real.Gamma (2 / 3) ∧ Real.Gamma (2 / 3) < 1.360 := by
  obtain ⟨h1, h2⟩ := airyGamma_enclosure (x := 2 / 3) (c := 9) (by norm_num) (by norm_num)
    airyGamma_rpow_two_thirds
  constructor
  · refine lt_of_lt_of_le ?_ h1
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    norm_num [Nat.factorial]
  · refine lt_of_le_of_lt h2 ?_
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    norm_num [Nat.factorial]

/-- `3^{1/3} ∈ (1.442, 1.4423)`. -/
lemma airyGamma_cbrt_three_bounds :
    1.442 < (3 : ℝ) ^ (1 / 3 : ℝ) ∧ (3 : ℝ) ^ (1 / 3 : ℝ) < 1.4423 := by
  have hc : ((3 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hpos : 0 < (3 : ℝ) ^ (1 / 3 : ℝ) := by positivity
  set c := (3 : ℝ) ^ (1 / 3 : ℝ)
  constructor
  · by_contra h
    push Not at h
    have := pow_le_pow_left₀ hpos.le h 3
    norm_num at this; linarith
  · by_contra h
    push Not at h
    have := pow_le_pow_left₀ (by norm_num) h 3
    norm_num at this; linarith

/-- `3^{-1/3} ∈ (0.6933, 0.6935)` and `3^{-2/3} ∈ (0.4806, 0.4810)`. -/
lemma airyGamma_three_neg_pow :
    0.6933 < (3 : ℝ) ^ (-(1 / 3) : ℝ) ∧ (3 : ℝ) ^ (-(1 / 3) : ℝ) < 0.6935 ∧
      0.4806 < (3 : ℝ) ^ (-(2 / 3) : ℝ) ∧ (3 : ℝ) ^ (-(2 / 3) : ℝ) < 0.4810 := by
  obtain ⟨h1, h2⟩ := airyGamma_cbrt_three_bounds
  have e1 : (3 : ℝ) ^ (-(1 / 3) : ℝ) = 1 / (3 : ℝ) ^ (1 / 3 : ℝ) := by
    rw [Real.rpow_neg (by norm_num)]; exact (one_div _).symm
  have e2 : (3 : ℝ) ^ (-(2 / 3) : ℝ) = 1 / ((3 : ℝ) ^ (1 / 3 : ℝ)) ^ 2 := by
    rw [Real.rpow_neg (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), one_div]
    norm_num
  set c := (3 : ℝ) ^ (1 / 3 : ℝ)
  have hc : 0 < c := by positivity
  rw [e1, e2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hc]; nlinarith
  · rw [div_lt_iff₀ hc]; nlinarith
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- `0.3533 < Ai(0) < 0.3628` (true value `0.355028…`). -/
theorem airyAi_zero_bounds : 0.3533 < airyAi 0 ∧ airyAi 0 < 0.3628 := by
  obtain ⟨-, -, h3, h4⟩ := airyGamma_three_neg_pow
  obtain ⟨h5, h6⟩ := airyGamma_two_thirds_bounds
  rw [airyAi_zero]
  have hg : 0 < Real.Gamma (2 / 3) := by linarith
  constructor
  · rw [lt_div_iff₀ hg]; nlinarith
  · rw [div_lt_iff₀ hg]; nlinarith

/-- `-0.2611 < Ai'(0) < -0.2576` (true value `-0.258819…`). -/
theorem airyAi'_zero_bounds : -0.2611 < airyAi' 0 ∧ airyAi' 0 < -0.2576 := by
  obtain ⟨h1, h2, -, -⟩ := airyGamma_three_neg_pow
  obtain ⟨h5, h6⟩ := airyGamma_third_bounds
  rw [airyAi'_zero]
  have hg : 0 < Real.Gamma (1 / 3) := by linarith
  constructor
  · have : (3 : ℝ) ^ (-(1 / 3) : ℝ) / Real.Gamma (1 / 3) < 0.2611 := by
      rw [div_lt_iff₀ hg]; nlinarith
    linarith
  · have : 0.2576 < (3 : ℝ) ^ (-(1 / 3) : ℝ) / Real.Gamma (1 / 3) := by
      rw [lt_div_iff₀ hg]; nlinarith
    linarith

/-- info: 'FormalResearch.Special.airyAi_zero_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_zero_bounds

/-- info: 'FormalResearch.Special.airyAi'_zero_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi'_zero_bounds

end FormalResearch.Special
