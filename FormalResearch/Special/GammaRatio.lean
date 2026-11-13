module

public import Interval.EulerMaclaurin.Gamma
public import Mathlib
public import FormalResearch.Racah.P2AnalyticCore

/-!
# Large-`x` asymptotics of `Γ(x+a)/Γ(x+b)`

Asymptotic expansion of the Gamma ratio as `x → ∞` with `a b` fixed (DLMF 5.11.13,
Tricomi-Erdélyi), derived from the Stirling series with remainder for `log Γ`
(`log_gamma_em` in the vendored `Interval.EulerMaclaurin.Gamma`, girving/interval,
`ThirdParty/interval/NOTICE.md`).  All statements are in terms of `t = 1/x` written `x⁻¹`.

* `gammaRatioCoeff k a b = (-1)^{k+1} (B_{k+1}(a) - B_{k+1}(b)) / (k (k+1))`, `B_n = bernoulliFun n`.
* `logGamma_sub_expansion` : `log Γ(x+a) - log Γ(x+b) = (a-b) log x + ∑_{k=1}^K c_k(a,b) x^{-k}
  + O(x^{-(K+1)})` as `x → ∞` (`IsBigO` along `atTop`, for every `K`); `logGamma_sub_expansion_bound`
  is the `∃ C x₀` form (the constants are not explicit).
* `gamma_ratio_isEquivalent` : `Γ(x+a)/Γ(x+b) ∼ x^{a-b}` (`Asymptotics.IsEquivalent`).
* `gamma_ratio_two_term` : `Γ(x+a)/Γ(x+b) = x^{a-b} (1 + (a-b)(a+b-1)/(2x)) + O(x^{a-b-2})`.
* `Ct_log_expansion` : for the central products `Ct` of `FormalResearch/Racah/P2AnalyticCt.lean`,
  `log Ct r S (1/N²) = r log S + ∑_{k=1}^K c_k((r+1)/2, (1-r)/2) (N S)^{-k} + O(N^{-(K+1)})`
  (an instance, through `Ct_Gamma`); `Ct_log_expansion_two` : only even `k` survive and
  `c_2 = -r(r²-1)/24`, so `log Ct = r log S - r(r²-1)/24 (NS)^{-2} + O(N^{-4})`.

Method.  `Asy f F K` (`f = ∑_{k ≤ K} F_k x^{-k} + O(x^{-K-1})`, `F` a formal power series) is closed
under `+`, `-`, scalar multiples, finite sums and products (`asy_mul`, by truncated Cauchy products).
`log(1+a/x)`, `x log(1+a/x)`, `(x+a)⁻¹` and its powers have explicit series (`logSeries`,
`logSeries'`, `geoSeries`); `log_gamma_em` at `x+a` then gives `Asy` of
`E_a(x) = log Γ(x+a) - ((x+a-1/2) log x - x + (1/2) log 2π)` with the series `stirSeries`, and the
coefficient identity `coeff_stirSeries` (`[x^{-k}] E_a = (-1)^{k+1} B_{k+1}(a)/(k(k+1))`) is the
termwise binomial identity `coeff_term` together with `B_n(a) = ∑ C(n,i) B_i a^{n-i}`.

Mathlib has no Gamma-ratio asymptotics (checked: no `IsEquivalent`/`atTop` statement about `Gamma`).
-/

@[expose] public section

namespace FormalResearch.Special.GammaRatio

open Filter Topology Asymptotics PowerSeries Finset

/-! ### Asymptotic expansions in `t = 1/x` with formal power series coefficients -/

/-- `Asy f F K`: `f x = ∑_{k ≤ K} F_k x^{-k} + O(x^{-K-1})` as `x → ∞`. -/
def Asy (f : ℝ → ℝ) (F : PowerSeries ℝ) (K : ℕ) : Prop :=
  (fun x : ℝ => f x - ∑ k ∈ range (K + 1), coeff k F * x⁻¹ ^ k) =O[atTop] fun x => x⁻¹ ^ (K + 1)

theorem asy_congr {f g : ℝ → ℝ} {F : PowerSeries ℝ} {K : ℕ} (h : Asy f F K)
    (hfg : f =ᶠ[atTop] g) : Asy g F K := by
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [hfg] with x hx using by simp [hx]

theorem asy_add {f g : ℝ → ℝ} {F G : PowerSeries ℝ} {K : ℕ} (hf : Asy f F K) (hg : Asy g G K) :
    Asy (fun x => f x + g x) (F + G) K := by
  have := hf.add hg
  refine this.congr_left fun x => ?_
  simp [map_add, add_mul, sum_add_distrib]
  ring

theorem asy_sub {f g : ℝ → ℝ} {F G : PowerSeries ℝ} {K : ℕ} (hf : Asy f F K) (hg : Asy g G K) :
    Asy (fun x => f x - g x) (F - G) K := by
  have := hf.sub hg
  refine this.congr_left fun x => ?_
  simp [map_sub, sub_mul, sum_sub_distrib]
  ring

theorem asy_smul (c : ℝ) {f : ℝ → ℝ} {F : PowerSeries ℝ} {K : ℕ} (hf : Asy f F K) :
    Asy (fun x => c * f x) (c • F) K := by
  have := hf.const_mul_left c
  refine this.congr_left fun x => ?_
  simp [mul_sum, mul_sub, mul_assoc]

theorem asy_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {F : ι → PowerSeries ℝ} {K : ℕ}
    (h : ∀ i ∈ s, Asy (f i) (F i) K) :
    Asy (fun x => ∑ i ∈ s, f i x) (∑ i ∈ s, F i) K := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa [Asy] using (isBigO_zero (fun x : ℝ => x⁻¹ ^ (K + 1)) atTop)
  | insert j s hj ih =>
    simp only [sum_insert hj]
    exact asy_add (h j (mem_insert_self _ _)) (ih fun i hi => h i (mem_insert_of_mem hi))

theorem asy_of_isBigO {f : ℝ → ℝ} {K : ℕ} (h : f =O[atTop] fun x : ℝ => x⁻¹ ^ (K + 1)) :
    Asy f 0 K := by
  simpa [Asy] using h

theorem asy_const (c : ℝ) (K : ℕ) : Asy (fun _ => c) (C c) K := by
  have : (fun x : ℝ => c - ∑ k ∈ range (K + 1), coeff k (C c : PowerSeries ℝ) * x⁻¹ ^ k) = 0 := by
    ext x
    simp [coeff_C]
  rw [Asy, this]
  exact isBigO_zero _ _

theorem eval_trunc_eq (F : PowerSeries ℝ) (K : ℕ) (t : ℝ) :
    (PowerSeries.trunc (K + 1) F).eval t = ∑ k ∈ range (K + 1), coeff k F * t ^ k := by
  rw [Polynomial.eval_eq_sum_range' (n := K + 1) (PowerSeries.natDegree_trunc_lt F K)]
  refine sum_congr rfl fun k hk => ?_
  simp [PowerSeries.coeff_trunc, mem_range.mp hk]

/-- A polynomial in `t = x⁻¹` is bounded as `x → ∞`. -/
theorem isBigO_one_poly (P : Polynomial ℝ) :
    (fun x : ℝ => P.eval x⁻¹) =O[atTop] fun _ => (1 : ℝ) := by
  refine Tendsto.isBigO_one ℝ (c := P.eval 0) ?_
  exact (P.continuous.tendsto 0).comp tendsto_inv_atTop_zero

theorem isBigO_one_sum (F : PowerSeries ℝ) (K : ℕ) :
    (fun x : ℝ => ∑ k ∈ range (K + 1), coeff k F * x⁻¹ ^ k) =O[atTop] fun _ => (1 : ℝ) := by
  refine (isBigO_one_poly (PowerSeries.trunc (K + 1) F)).congr_left fun x => ?_
  rw [eval_trunc_eq]

theorem inv_pow_isBigO_one (n : ℕ) :
    (fun x : ℝ => x⁻¹ ^ n) =O[atTop] fun _ => (1 : ℝ) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have h0 : 0 < x := by linarith
  have : x⁻¹ ^ n ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hx)
  simpa [abs_of_nonneg, h0.le] using this

theorem isBigO_one_asy {f : ℝ → ℝ} {F : PowerSeries ℝ} {K : ℕ} (h : Asy f F K) :
    f =O[atTop] fun _ => (1 : ℝ) := by
  have h1 := h.trans (inv_pow_isBigO_one (K + 1))
  have := h1.add (isBigO_one_sum F K)
  simpa using this

theorem asy_mul {f g : ℝ → ℝ} {F G : PowerSeries ℝ} {K : ℕ} (hf : Asy f F K) (hg : Asy g G K) :
    Asy (fun x => f x * g x) (F * G) K := by
  set P := PowerSeries.trunc (K + 1) F with hP
  set Q := PowerSeries.trunc (K + 1) G with hQ
  set U := P * Q - PowerSeries.trunc (K + 1) (F * G) with hU
  have hdvd : (Polynomial.X : Polynomial ℝ) ^ (K + 1) ∣ U := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    have h1 := PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc F G hd
    rw [hU, Polynomial.coeff_sub, PowerSeries.coeff_trunc]
    simp only [hd, ↓reduceIte]
    rw [h1, ← hP, ← hQ, ← Polynomial.coe_mul, Polynomial.coeff_coe, sub_self]
  obtain ⟨R, hR⟩ := hdvd
  have hRO := isBigO_one_poly R
  -- decomposition
  have key : ∀ x : ℝ,
      f x * g x - ∑ k ∈ range (K + 1), coeff k (F * G) * x⁻¹ ^ k =
      (f x - ∑ k ∈ range (K + 1), coeff k F * x⁻¹ ^ k) * g x +
      (∑ k ∈ range (K + 1), coeff k F * x⁻¹ ^ k) *
        (g x - ∑ k ∈ range (K + 1), coeff k G * x⁻¹ ^ k) +
      x⁻¹ ^ (K + 1) * R.eval x⁻¹ := by
    intro x
    have h2 := congrArg (Polynomial.eval x⁻¹) hU
    rw [hR] at h2
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, hP, hQ, eval_trunc_eq] at h2
    linear_combination (-1 : ℝ) * h2
  have t1 : (fun x : ℝ => (f x - ∑ k ∈ range (K + 1), coeff k F * x⁻¹ ^ k) * g x) =O[atTop]
      fun x : ℝ => x⁻¹ ^ (K + 1) := by
    simpa using hf.mul (isBigO_one_asy hg)
  have t2 : (fun x : ℝ => (∑ k ∈ range (K + 1), coeff k F * x⁻¹ ^ k) *
      (g x - ∑ k ∈ range (K + 1), coeff k G * x⁻¹ ^ k)) =O[atTop]
      fun x : ℝ => x⁻¹ ^ (K + 1) := by
    simpa using (isBigO_one_sum F K).mul hg
  have t3 : (fun x : ℝ => x⁻¹ ^ (K + 1) * R.eval x⁻¹) =O[atTop]
      fun x : ℝ => x⁻¹ ^ (K + 1) := by
    simpa using (isBigO_refl (fun x : ℝ => x⁻¹ ^ (K + 1)) atTop).mul hRO
  unfold Asy
  simp only [key]
  exact (t1.add t2).add t3


/-! ### Basic expansions: `log (1 + a/x)` and `(x+a)⁻¹` -/

/-- Series of `log (1 + a t)`. -/
noncomputable def logSeries (a : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun k => if k = 0 then 0 else (-1) ^ (k + 1) * a ^ k / k

/-- Series of `log (1 + a t) / t`. -/
noncomputable def logSeries' (a : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun k => (-1) ^ k * a ^ (k + 1) / (k + 1)

/-- Series of `1 / (1 + a t)`. -/
noncomputable def geoSeries (a : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun j => (-a) ^ j

theorem logSeries_eq (a : ℝ) : logSeries a = X * logSeries' a := by
  ext k
  rcases k with _ | k
  · simp [logSeries]
  · simp only [logSeries, logSeries', coeff_mk, coeff_succ_X_mul]
    push_cast
    simp [pow_succ]

theorem eventually_small (a : ℝ) :
    ∀ᶠ x : ℝ in atTop, 0 < x ∧ |a| * x⁻¹ ≤ 1 / 2 := by
  filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop (2 * |a|)] with x hx0 hx
  refine ⟨hx0, ?_⟩
  rw [← div_eq_mul_inv, div_le_iff₀ hx0]
  linarith

theorem asy_log (a : ℝ) (K : ℕ) : Asy (fun x => Real.log (1 + a / x)) (logSeries a) K := by
  refine IsBigO.of_bound (2 * |a| ^ (K + 1)) ?_
  filter_upwards [eventually_small a] with x ⟨hx0, hx⟩
  have hu : |(-a) * x⁻¹| < 1 := by
    rw [abs_mul, abs_neg, abs_inv, abs_of_pos hx0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hu K
  have hsum : ∑ k ∈ range (K + 1), coeff k (logSeries a) * x⁻¹ ^ k =
      -∑ i ∈ range K, ((-a) * x⁻¹) ^ (i + 1) / (i + 1) := by
    rw [sum_range_succ', ← sum_neg_distrib, show coeff 0 (logSeries a) = 0 by simp [logSeries]]
    simp only [zero_mul, add_zero]
    refine sum_congr rfl fun i _ => ?_
    simp only [logSeries, coeff_mk, Nat.succ_ne_zero, ite_false]
    push_cast
    ring
  have hlog : 1 - (-a) * x⁻¹ = 1 + a / x := by ring
  rw [hlog] at h
  have : Real.log (1 + a / x) - ∑ k ∈ range (K + 1), coeff k (logSeries a) * x⁻¹ ^ k =
      (∑ i ∈ range K, ((-a) * x⁻¹) ^ (i + 1) / (i + 1)) + Real.log (1 + a / x) := by
    rw [hsum]; ring
  rw [this]
  refine h.trans ?_
  have hu' : |(-a) * x⁻¹| = |a| * x⁻¹ := by
    rw [abs_mul, abs_neg, abs_inv, abs_of_pos hx0]
  rw [hu', Real.norm_eq_abs, abs_pow, abs_of_pos (inv_pos.mpr hx0)]
  have h1 : 0 < 1 - |a| * x⁻¹ := by linarith
  rw [div_le_iff₀ h1, mul_pow]
  have h2 : 0 ≤ |a| ^ (K + 1) * x⁻¹ ^ (K + 1) := by positivity
  nlinarith [h2]


theorem asy_shift {f : ℝ → ℝ} {F : PowerSeries ℝ} {K : ℕ} (h : Asy f (X * F) (K + 1)) :
    Asy (fun x => x * f x) F K := by
  have h1 := (isBigO_refl (fun x : ℝ => x) atTop).mul h
  have h2 : (fun x : ℝ => x * x⁻¹ ^ (K + 1 + 1)) =ᶠ[atTop] fun x : ℝ => x⁻¹ ^ (K + 1) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [pow_succ _ (K + 1), ← mul_assoc, mul_comm x, mul_assoc, mul_inv_cancel₀ hx.ne', mul_one]
  refine (h1.congr' EventuallyEq.rfl h2).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [mul_sub]
  congr 1
  rw [sum_range_succ', mul_add]
  simp only [coeff_zero_X_mul, zero_mul, mul_zero, add_zero, coeff_succ_X_mul, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [pow_succ]
  calc x * (coeff k F * (x⁻¹ ^ k * x⁻¹)) = coeff k F * x⁻¹ ^ k * (x * x⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hx.ne', mul_one]

theorem asy_xlog (a : ℝ) (K : ℕ) :
    Asy (fun x => x * Real.log (1 + a / x) - a) (logSeries' a - C a) K := by
  have h := asy_log a (K + 1)
  rw [logSeries_eq] at h
  exact asy_sub (asy_shift h) (asy_const a K)

theorem asy_inv_add (a : ℝ) (K : ℕ) : Asy (fun x => (x + a)⁻¹) (X * geoSeries a) K := by
  refine IsBigO.of_bound (2 * |a| ^ K) ?_
  filter_upwards [eventually_small a] with x ⟨hx0, hx⟩
  set r : ℝ := -a * x⁻¹ with hr
  have hr1 : |r| ≤ 1 / 2 := by
    rw [hr, abs_mul, abs_neg, abs_inv, abs_of_pos hx0]; exact hx
  have hpos : 0 < 1 - r := by
    have := le_abs_self r
    linarith
  have hsum : ∑ k ∈ range (K + 1), coeff k (X * geoSeries a) * x⁻¹ ^ k =
      x⁻¹ * ∑ j ∈ range K, r ^ j := by
    rw [sum_range_succ', mul_sum]
    simp only [coeff_zero_X_mul, zero_mul, add_zero, coeff_succ_X_mul, geoSeries, coeff_mk]
    refine sum_congr rfl fun j _ => ?_
    rw [hr, mul_pow, neg_pow a, pow_succ]
    ring
  have hg := geom_sum_mul_neg r K
  have hxa : x + a ≠ 0 := by
    intro h0
    have : |a| * x⁻¹ ≤ 1 / 2 := hx
    have ha : a = -x := by linarith
    rw [ha, abs_neg, abs_of_pos hx0, mul_inv_cancel₀ hx0.ne'] at this
    norm_num at this
  have e1 : (x + a)⁻¹ = x⁻¹ / (1 - r) := by
    rw [hr]; field_simp
    rw [sub_neg_eq_add, div_self hxa]
  have e2 : (x + a)⁻¹ - ∑ k ∈ range (K + 1), coeff k (X * geoSeries a) * x⁻¹ ^ k =
      x⁻¹ * r ^ K / (1 - r) := by
    rw [hsum, e1]
    have : ∑ j ∈ range K, r ^ j = (1 - r ^ K) / (1 - r) := by
      rw [eq_div_iff hpos.ne']; exact hg
    rw [this]; field_simp; ring
  rw [e2, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_pow,
    abs_of_pos hpos, abs_of_pos (inv_pos.mpr hx0), div_le_iff₀ hpos]
  have hrK : |r| ^ K = |a| ^ K * x⁻¹ ^ K := by
    rw [hr, abs_mul, abs_neg, abs_inv, abs_of_pos hx0, mul_pow]
  rw [hrK, pow_succ x⁻¹ K]
  have h0 : 0 ≤ |a| ^ K * x⁻¹ ^ K * x⁻¹ := by positivity
  have h1 : 1 / 2 ≤ 1 - r := by have := le_abs_self r; linarith
  nlinarith [h0]


theorem asy_inv_pow (a : ℝ) (K n : ℕ) :
    Asy (fun x => ((x + a)⁻¹) ^ n) ((X * geoSeries a) ^ n) K := by
  induction n with
  | zero => simpa using asy_const 1 K
  | succ n ih =>
    simpa [pow_succ] using asy_mul ih (asy_inv_add a K)

/-! ### Coefficients -/

theorem geoSeries_eq (a : ℝ) : geoSeries a = rescale (-a) (mk 1 : PowerSeries ℝ) := by
  ext j
  simp [geoSeries, coeff_rescale]

theorem coeff_geoSeries_pow (a : ℝ) (m j : ℕ) :
    coeff j (geoSeries a ^ (m + 1)) = (-a) ^ j * (Nat.choose (m + j) m : ℝ) := by
  rw [geoSeries_eq, ← map_pow, mk_one_pow_eq_mk_choose_add, coeff_rescale, coeff_mk]

theorem coeff_Xgeo_pow (a : ℝ) (m k : ℕ) :
    coeff k ((X * geoSeries a) ^ (m + 1)) =
      if m + 1 ≤ k then (-a) ^ (k - (m + 1)) * (Nat.choose (k - 1) m : ℝ) else 0 := by
  rw [mul_pow, coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_geoSeries_pow]
    congr 3
    omega
  · rfl

theorem bernoulliFun_eq_sum (n : ℕ) (a : ℝ) :
    bernoulliFun n a =
      ∑ i ∈ range (n + 1), (bernoulli i : ℝ) * (Nat.choose n i : ℝ) * a ^ (n - i) := by
  simp [bernoulliFun, Polynomial.bernoulli, Polynomial.eval_map, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_monomial]


theorem choose_identity (n m : ℕ) :
    (n + 2) * (n + 1) * Nat.choose n m = Nat.choose (n + 2) (m + 2) * ((m + 1) * (m + 2)) := by
  have h1 := Nat.add_one_mul_choose_eq n m
  have h2 := Nat.add_one_mul_choose_eq (n + 1) (m + 1)
  calc (n + 2) * (n + 1) * Nat.choose n m = (n + 2) * ((n + 1) * Nat.choose n m) := by ring
    _ = (n + 2) * (Nat.choose (n + 1) (m + 1) * (m + 1)) := by rw [h1]
    _ = ((n + 1 + 1) * Nat.choose (n + 1) (m + 1)) * (m + 1) := by ring
    _ = _ := by rw [h2]; ring

/-- The `m`-th summand of the coefficient identity. -/
theorem coeff_term (n m : ℕ) (hm : m < n + 1) (a : ℝ) :
    ((bernoulli (m + 2) : ℝ) / ((m + 1) * (m + 2))) * ((-a) ^ (n - m) * (Nat.choose n m : ℝ)) =
      (-1) ^ (n + 2) / ((n + 1) * (n + 2)) *
        ((bernoulli (m + 2) : ℝ) * (Nat.choose (n + 2) (m + 2) : ℝ) * a ^ (n + 2 - (m + 2))) := by
  rcases Nat.even_or_odd m with he | ho
  · have e1 : n + 2 - (m + 2) = n - m := by omega
    have e2 : (-1 : ℝ) ^ (n - m) = (-1) ^ (n + 2) := by
      have : (-1 : ℝ) ^ n = (-1) ^ (n - m) * (-1) ^ m := by
        rw [← pow_add]; congr 1; omega
      rw [he.neg_one_pow, mul_one] at this
      rw [← this]; ring
    have hc := choose_identity n m
    have hc' : ((n : ℝ) + 2) * ((n : ℝ) + 1) * (Nat.choose n m : ℝ) =
        (Nat.choose (n + 2) (m + 2) : ℝ) * (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
      exact_mod_cast hc
    have hC : (Nat.choose n m : ℝ) = (Nat.choose (n + 2) (m + 2) : ℝ) * (((m : ℝ) + 1) * ((m : ℝ) + 2)) /
        (((n : ℝ) + 2) * ((n : ℝ) + 1)) := by
      rw [eq_div_iff (by positivity)]; linarith
    rw [e1, neg_pow a, e2, hC]
    field_simp
  · have : bernoulli (m + 2) = 0 := bernoulli_eq_zero_of_odd (by exact ho.add_even even_two) (by omega)
    simp [this]


/-- `B_{m+2} / ((m+1)(m+2))`: the Stirling series coefficients. -/
noncomputable def betaCoef (m : ℕ) : ℝ := (bernoulli (m + 2) : ℝ) / ((m + 1) * (m + 2))

/-- The coefficient `c_k(a) = (-1)^{k+1} B_{k+1}(a) / (k (k+1))` of `x^{-k}` in
`log Γ(x+a) - ((x+a-1/2) log x - x + (1/2) log 2π)`. -/
noncomputable def gammaCoeff (k : ℕ) (a : ℝ) : ℝ :=
  (-1) ^ (k + 1) * bernoulliFun (k + 1) a / (k * (k + 1))

/-- Formal series of `E_a(x) = log Γ(x+a) - ((x+a-1/2) log x - x + (1/2) log 2π)` (truncated Stirling
series, `M` terms). -/
noncomputable def stirSeries (a : ℝ) (M : ℕ) : PowerSeries ℝ :=
  logSeries' a - C a + (a - 1 / 2) • logSeries a +
    ∑ m ∈ range M, betaCoef m • (X * geoSeries a) ^ (m + 1)

theorem bernoulliFun_split (n : ℕ) (a : ℝ) :
    bernoulliFun (n + 1 + 1) a =
      ∑ m ∈ range (n + 1), (bernoulli (m + 2) : ℝ) * (Nat.choose (n + 2) (m + 2) : ℝ) *
        a ^ (n + 2 - (m + 2)) - (n + 2) / 2 * a ^ (n + 1) + a ^ (n + 2) := by
  rw [bernoulliFun_eq_sum, sum_range_succ' _ (n + 1 + 1), sum_range_succ' _ (n + 1)]
  simp only [bernoulli_zero, Nat.choose_zero_right]
  push_cast
  simp
  ring

theorem coeff_stirSeries_zero (a : ℝ) (M : ℕ) : coeff 0 (stirSeries a M) = 0 := by
  have h : ∀ m ∈ range M, coeff 0 (betaCoef m • (X * geoSeries a) ^ (m + 1)) = 0 := by
    intro m _
    simp [pow_succ]
  simp [stirSeries, map_sum, logSeries, logSeries']

theorem coeff_stirSeries (a : ℝ) (n M : ℕ) (hM : n + 1 ≤ M) :
    coeff (n + 1) (stirSeries a M) = gammaCoeff (n + 1) a := by
  have hsum : ∑ m ∈ range M, betaCoef m * coeff (n + 1) ((X * geoSeries a) ^ (m + 1)) =
      ∑ m ∈ range (n + 1), betaCoef m * ((-a) ^ (n - m) * (Nat.choose n m : ℝ)) := by
    have : ∀ m ∈ range M, betaCoef m * coeff (n + 1) ((X * geoSeries a) ^ (m + 1)) =
        if m < n + 1 then betaCoef m * ((-a) ^ (n - m) * (Nat.choose n m : ℝ)) else 0 := by
      intro m _
      rw [coeff_Xgeo_pow]
      by_cases h : m < n + 1
      · have h' : m + 1 ≤ n + 1 := h
        simp only [h', h, ↓reduceIte]
        congr 3
        all_goals omega
      · have h' : ¬ m + 1 ≤ n + 1 := by omega
        simp only [h', h, ↓reduceIte, mul_zero]
    rw [sum_congr rfl this, ← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext m
    simp only [mem_filter, mem_range]
    omega
  simp only [stirSeries, map_add, map_sub, map_sum, coeff_smul, smul_eq_mul, coeff_C,
    Nat.succ_ne_zero, ite_false, sub_zero, logSeries', logSeries, coeff_mk, hsum]
  simp only [betaCoef]
  rw [sum_congr rfl (fun m hm => coeff_term n m (mem_range.mp hm) a), ← mul_sum]
  unfold gammaCoeff
  rw [bernoulliFun_split]
  push_cast
  field_simp
  ring


/-! ### Stirling series, shifted -/

theorem inv_add_isBigO (a : ℝ) :
    (fun x : ℝ => (x + a)⁻¹) =O[atTop] fun x : ℝ => x⁻¹ := by
  have h := asy_inv_add a 0
  unfold Asy at h
  simpa [coeff_zero_X_mul] using h

theorem inv_pow_isBigO_inv_pow {m n : ℕ} (h : n ≤ m) :
    (fun x : ℝ => x⁻¹ ^ m) =O[atTop] fun x : ℝ => x⁻¹ ^ n := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have h0 : 0 < x := by linarith
  have : x⁻¹ ^ m ≤ x⁻¹ ^ n :=
    pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hx) h
  simpa [abs_of_nonneg, h0.le] using this

theorem rem_isBigO (a : ℝ) (K : ℕ) :
    (fun x : ℝ => _root_.rem (x + a) (2 * K)) =O[atTop] fun x : ℝ => x⁻¹ ^ (K + 1) := by
  have h1 : (fun x : ℝ => _root_.rem (x + a) (2 * K)) =O[atTop]
      fun x : ℝ => ((x + a)⁻¹) ^ (2 * K + 1) := by
    refine IsBigO.of_bound |betaCoef (2 * K)| ?_
    filter_upwards [eventually_gt_atTop (-a), eventually_gt_atTop 0] with x hxa hx0
    have hy : 0 < x + a := by linarith
    have := abs_rem_le' (x + a) (2 * K) (by simp) hy
    refine this.trans (le_of_eq ?_)
    simp only [term, betaCoef, Real.norm_eq_abs]
    push_cast
    rw [div_eq_mul_inv _ ((x + a) ^ (2 * K + 1)), abs_mul, abs_inv, abs_pow, abs_of_pos hy,
      inv_pow, abs_of_pos (inv_pos.mpr (pow_pos hy _))]
  have h2 := (inv_add_isBigO a).pow (2 * K + 1)
  exact (h1.trans h2).trans (inv_pow_isBigO_inv_pow (by omega))


theorem term_eq_betaCoef (y : ℝ) (m : ℕ) : term y m = betaCoef m * y⁻¹ ^ (m + 1) := by
  simp only [term, betaCoef, inv_pow, div_eq_mul_inv]

theorem logGamma_shift_eq (a : ℝ) (K : ℕ) {x : ℝ} (hx : 0 < x) (hy : 0 < x + a) :
    Real.log (Real.Gamma (x + a)) - ((x + a - 1 / 2) * Real.log x - x + Real.log (2 * Real.pi) / 2) =
      (x * Real.log (1 + a / x) - a + (a - 1 / 2) * Real.log (1 + a / x) +
        ∑ m ∈ range (2 * K + 1), betaCoef m * ((x + a)⁻¹) ^ (m + 1)) - _root_.rem (x + a) (2 * K) := by
  have h1 : Real.log (x + a) = Real.log x + Real.log (1 + a / x) := by
    have h2 : 0 < 1 + a / x := by
      have : 1 + a / x = (x + a) / x := by field_simp
      rw [this]; positivity
    rw [← Real.log_mul hx.ne' h2.ne']
    congr 1
    field_simp
  rw [log_gamma_em (x + a) (2 * K) hy, const_eq, h1]
  have h3 : _root_.sum (x + a) (2 * K) = ∑ m ∈ range (2 * K + 1), betaCoef m * ((x + a)⁻¹) ^ (m + 1) := by
    simp only [_root_.sum, term_eq_betaCoef]
  rw [h3]
  ring

theorem logGamma_asy (a : ℝ) (K : ℕ) :
    Asy (fun x => Real.log (Real.Gamma (x + a)) -
      ((x + a - 1 / 2) * Real.log x - x + Real.log (2 * Real.pi) / 2)) (stirSeries a (2 * K + 1)) K := by
  have h1 := asy_xlog a K
  have h2 := asy_smul (a - 1 / 2) (asy_log a K)
  have h3 := asy_sum (range (2 * K + 1))
    (fun m _ => asy_smul (betaCoef m) (asy_inv_pow a K (m + 1)))
  have h4 := asy_of_isBigO (rem_isBigO a K)
  have h5 := asy_sub (asy_add (asy_add h1 h2) h3) h4
  rw [sub_zero] at h5
  refine asy_congr h5 ?_
  filter_upwards [eventually_gt_atTop 0, eventually_gt_atTop (-a)] with x hx hxa
  exact (logGamma_shift_eq a K hx (by linarith)).symm


/-! ### The expansion of `log Γ(x+a) - log Γ(x+b)` -/

/-- The coefficient `c_k(a,b) = (-1)^{k+1} (B_{k+1}(a) - B_{k+1}(b)) / (k (k+1))` of `x^{-k}` in the
expansion of `log Γ(x+a) - log Γ(x+b) - (a-b) log x` (DLMF 5.11.13, Tricomi-Erdélyi). -/
noncomputable def gammaRatioCoeff (k : ℕ) (a b : ℝ) : ℝ :=
  (-1) ^ (k + 1) * (bernoulliFun (k + 1) a - bernoulliFun (k + 1) b) / (k * (k + 1))

theorem gammaRatioCoeff_eq (k : ℕ) (a b : ℝ) :
    gammaRatioCoeff k a b = gammaCoeff k a - gammaCoeff k b := by
  simp only [gammaRatioCoeff, gammaCoeff]
  ring

theorem sum_Icc_eq_sum_range (K : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Icc 1 K, f k = ∑ k ∈ range K, f (k + 1) := by
  have : Icc 1 K = Ico 1 (K + 1) := by ext; simp
  rw [this, Finset.sum_Ico_eq_sum_range]
  simp [add_comm]

/-- **Expansion of the log Gamma ratio.** For fixed `a b : ℝ` and `K : ℕ`, as `x → ∞`,
`log Γ(x+a) - log Γ(x+b) = (a-b) log x + ∑_{k=1}^{K} c_k(a,b) x^{-k} + O(x^{-(K+1)})`
with `c_k(a,b) = (-1)^{k+1} (B_{k+1}(a) - B_{k+1}(b)) / (k (k+1))`. -/
theorem logGamma_sub_expansion (a b : ℝ) (K : ℕ) :
    (fun x : ℝ => Real.log (Real.Gamma (x + a)) - Real.log (Real.Gamma (x + b)) -
      ((a - b) * Real.log x + ∑ k ∈ Icc 1 K, gammaRatioCoeff k a b * x⁻¹ ^ k))
      =O[atTop] fun x : ℝ => x⁻¹ ^ (K + 1) := by
  have h := asy_sub (logGamma_asy a K) (logGamma_asy b K)
  unfold Asy at h
  refine h.congr_left fun x => ?_
  have hs : ∑ k ∈ range (K + 1), coeff k (stirSeries a (2 * K + 1) - stirSeries b (2 * K + 1)) *
      x⁻¹ ^ k = ∑ k ∈ Icc 1 K, gammaRatioCoeff k a b * x⁻¹ ^ k := by
    rw [sum_Icc_eq_sum_range, sum_range_succ']
    simp only [map_sub, coeff_stirSeries_zero, sub_self, zero_mul, add_zero]
    refine sum_congr rfl fun n hn => ?_
    rw [coeff_stirSeries a n _ (by have := mem_range.mp hn; omega),
      coeff_stirSeries b n _ (by have := mem_range.mp hn; omega), gammaRatioCoeff_eq]
  rw [hs]
  ring


/-- Existential form of `logGamma_sub_expansion`: an explicit-shape bound with some constants. -/
theorem logGamma_sub_expansion_bound (a b : ℝ) (K : ℕ) :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      |Real.log (Real.Gamma (x + a)) - Real.log (Real.Gamma (x + b)) -
        ((a - b) * Real.log x + ∑ k ∈ Icc 1 K, gammaRatioCoeff k a b * x⁻¹ ^ k)| ≤
        C * |x⁻¹| ^ (K + 1) := by
  obtain ⟨C, hC⟩ := (logGamma_sub_expansion a b K).bound
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hC
  refine ⟨max C 1, x₀, by positivity, fun x hx => ?_⟩
  have := hx₀ x hx
  simp only [Real.norm_eq_abs, abs_pow] at this
  refine this.trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-! ### Small cases of the coefficients -/

theorem bernoulliFun_two (y : ℝ) : bernoulliFun 2 y = y ^ 2 - y + 1 / 6 := by
  rw [bernoulliFun_eq_sum]
  simp [sum_range_succ, bernoulli_two]
  ring

theorem bernoulliFun_three (y : ℝ) : bernoulliFun 3 y = y ^ 3 - 3 / 2 * y ^ 2 + y / 2 := by
  rw [bernoulliFun_eq_sum]
  have h3 : bernoulli 3 = 0 := bernoulli_eq_zero_of_odd (by decide) (by norm_num)
  simp [sum_range_succ, bernoulli_two, bernoulli_one, bernoulli_zero, h3]
  ring

theorem gammaRatioCoeff_one (a b : ℝ) : gammaRatioCoeff 1 a b = (a - b) * (a + b - 1) / 2 := by
  unfold gammaRatioCoeff
  rw [show (1 : ℕ) + 1 = 2 from rfl, bernoulliFun_two, bernoulliFun_two]
  push_cast
  ring

theorem gammaRatioCoeff_two (a b : ℝ) :
    gammaRatioCoeff 2 a b = -((a ^ 3 - 3 / 2 * a ^ 2 + a / 2) - (b ^ 3 - 3 / 2 * b ^ 2 + b / 2)) / 6 := by
  unfold gammaRatioCoeff
  rw [show (2 : ℕ) + 1 = 3 from rfl, bernoulliFun_three, bernoulliFun_three]
  push_cast
  ring

/-- For the symmetric pair `b = 1 - a`, all odd coefficients vanish. -/
theorem gammaRatioCoeff_symm_odd {k : ℕ} (hk : Odd k) (a : ℝ) :
    gammaRatioCoeff k a (1 - a) = 0 := by
  have h : bernoulliFun (k + 1) (1 - a) = bernoulliFun (k + 1) a := by
    rw [bernoulliFun_eval_one_sub, (hk.add_one).neg_one_pow, one_mul]
  simp [gammaRatioCoeff, h]


/-! ### The ratio `Γ(x+a)/Γ(x+b)` -/

/-- The log-ratio defect `u(x) = log Γ(x+a) - log Γ(x+b) - (a-b) log x`. -/
noncomputable def ratioDefect (a b x : ℝ) : ℝ :=
  Real.log (Real.Gamma (x + a)) - Real.log (Real.Gamma (x + b)) - (a - b) * Real.log x

theorem ratio_eq_rpow_mul_exp (a b : ℝ) {x : ℝ} (hx : 0 < x) (ha : 0 < x + a) (hb : 0 < x + b) :
    Real.Gamma (x + a) / Real.Gamma (x + b) = x ^ (a - b) * Real.exp (ratioDefect a b x) := by
  have h1 := Real.Gamma_pos_of_pos ha
  have h2 := Real.Gamma_pos_of_pos hb
  rw [ratioDefect, Real.rpow_def_of_pos hx, ← Real.exp_add, mul_comm (Real.log x),
    show (a - b) * Real.log x + (Real.log (Real.Gamma (x + a)) - Real.log (Real.Gamma (x + b)) -
      (a - b) * Real.log x) = Real.log (Real.Gamma (x + a)) - Real.log (Real.Gamma (x + b)) by ring,
    Real.exp_sub, Real.exp_log h1, Real.exp_log h2]

theorem ratioDefect_isBigO (a b : ℝ) :
    (fun x => ratioDefect a b x) =O[atTop] fun x : ℝ => x⁻¹ := by
  have h := logGamma_sub_expansion a b 0
  simpa [ratioDefect] using h

theorem ratioDefect_tendsto (a b : ℝ) : Tendsto (fun x => ratioDefect a b x) atTop (𝓝 0) :=
  (ratioDefect_isBigO a b).trans_tendsto tendsto_inv_atTop_zero

theorem eventually_ratio_eq (a b : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      Real.Gamma (x + a) / Real.Gamma (x + b) = x ^ (a - b) * Real.exp (ratioDefect a b x) := by
  filter_upwards [eventually_gt_atTop 0, eventually_gt_atTop (-a), eventually_gt_atTop (-b)]
    with x hx ha hb
  exact ratio_eq_rpow_mul_exp a b hx (by linarith) (by linarith)

/-- **Leading order.** `Γ(x+a)/Γ(x+b) ∼ x^{a-b}` as `x → ∞` (not in Mathlib; follows from the
`K = 0` case of `logGamma_sub_expansion`). -/
theorem gamma_ratio_isEquivalent (a b : ℝ) :
    (fun x : ℝ => Real.Gamma (x + a) / Real.Gamma (x + b)) ~[atTop] fun x : ℝ => x ^ (a - b) := by
  apply isEquivalent_of_tendsto_one
  have h1 : Tendsto (fun x => Real.exp (ratioDefect a b x)) atTop (𝓝 1) := by
    have := (Real.continuous_exp.tendsto 0).comp (ratioDefect_tendsto a b)
    rw [Real.exp_zero] at this
    exact this
  refine h1.congr' ?_
  filter_upwards [eventually_ratio_eq a b, eventually_gt_atTop 0] with x hx hx0
  have : 0 < x ^ (a - b) := Real.rpow_pos_of_pos hx0 _
  simp only [Pi.div_apply]
  rw [hx]
  field_simp

/-- **Two-term form.**
`Γ(x+a)/Γ(x+b) = x^{a-b} (1 + (a-b)(a+b-1)/(2x) + O(x^{-2}))`, i.e. the error is
`O(x^{a-b-2})`. -/
theorem gamma_ratio_two_term (a b : ℝ) :
    (fun x : ℝ => Real.Gamma (x + a) / Real.Gamma (x + b) -
      x ^ (a - b) * (1 + (a - b) * (a + b - 1) / 2 * x⁻¹))
      =O[atTop] fun x : ℝ => x ^ (a - b) * x⁻¹ ^ 2 := by
  have hexp : (fun x => Real.exp (ratioDefect a b x) - 1 - ratioDefect a b x) =O[atTop]
      fun x => ratioDefect a b x ^ 2 := by
    refine IsBigO.of_bound 1 ?_
    have : ∀ᶠ x : ℝ in atTop, |ratioDefect a b x| ≤ 1 :=
      (ratioDefect_tendsto a b).eventually (Metric.closedBall_mem_nhds 0 one_pos)
        |>.mono fun x hx => by simpa using hx
    filter_upwards [this] with x hx
    have := Real.abs_exp_sub_one_sub_id_le hx
    simpa [Real.norm_eq_abs, abs_sq] using this
  have hu2 : (fun x => ratioDefect a b x ^ 2) =O[atTop] fun x : ℝ => x⁻¹ ^ 2 :=
    (ratioDefect_isBigO a b).pow 2
  have h1 := logGamma_sub_expansion a b 1
  simp only [Icc_self, sum_singleton, gammaRatioCoeff_one, pow_one] at h1
  have hmain : (fun x => Real.exp (ratioDefect a b x) - 1 - (a - b) * (a + b - 1) / 2 * x⁻¹)
      =O[atTop] fun x : ℝ => x⁻¹ ^ 2 := by
    have := (hexp.trans hu2).add h1
    refine this.congr_left fun x => ?_
    simp only [ratioDefect]
    ring
  have h3 := (isBigO_refl (fun x : ℝ => x ^ (a - b)) atTop).mul hmain
  refine h3.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ratio_eq a b] with x hx
  rw [hx]
  ring


/-! ### Link to the central products `Ct` -/

/-- **`Ct` is an instance of the Gamma-ratio expansion.** For fixed `r : ℕ`, `S > 0` and `K`, as `N → ∞`
`log Ct r S (1/N²) = r log S + ∑_{k=1}^{K} c_k((r+1)/2, (1-r)/2) (N S)^{-k} + O(N^{-(K+1)})`,
because `Ct r S (1/N²) N^r = Γ(NS+(r+1)/2)/Γ(NS-(r-1)/2)` (`FormalResearch.Racah.Ct_Gamma`). -/
theorem Ct_log_expansion (r : ℕ) {S : ℝ} (hS : 0 < S) (K : ℕ) :
    (fun N : ℝ => Real.log (FormalResearch.Racah.Ct r S (1 / N ^ 2)) -
      (r * Real.log S + ∑ k ∈ Icc 1 K,
        gammaRatioCoeff k (((r : ℝ) + 1) / 2) ((1 - (r : ℝ)) / 2) * (N * S)⁻¹ ^ k))
      =O[atTop] fun N : ℝ => N⁻¹ ^ (K + 1) := by
  set a : ℝ := ((r : ℝ) + 1) / 2 with ha
  set b : ℝ := (1 - (r : ℝ)) / 2 with hb
  have hk : Tendsto (fun N : ℝ => N * S) atTop atTop :=
    tendsto_id.atTop_mul_const hS
  have h1 := (logGamma_sub_expansion a b K).comp_tendsto hk
  have h2 : ((fun x : ℝ => x⁻¹ ^ (K + 1)) ∘ fun N : ℝ => N * S) =O[atTop]
      fun N : ℝ => N⁻¹ ^ (K + 1) := by
    refine (isBigO_const_mul_self ((S⁻¹) ^ (K + 1)) (fun N : ℝ => N⁻¹ ^ (K + 1)) atTop).congr_left
      fun N => ?_
    simp only [Function.comp, mul_inv, mul_pow]
    ring
  refine (h1.trans h2).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0,
    (hk.eventually_gt_atTop (((r : ℝ) - 1) / 2))] with N hN hpos
  have hpos' : 0 < N * S - ((r : ℝ) - 1) / 2 := by linarith
  have hG := FormalResearch.Racah.Ct_Gamma r hN hpos'
  have hb' : N * S - ((r : ℝ) - 1) / 2 = N * S + b := by rw [hb]; ring
  rw [hb'] at hG
  have hGa : 0 < Real.Gamma (N * S + a) := Real.Gamma_pos_of_pos (by rw [ha]; positivity)
  have hGb : 0 < Real.Gamma (N * S + b) := Real.Gamma_pos_of_pos (by linarith)
  have hNr : 0 < N ^ r := pow_pos hN r
  have hCt : 0 < FormalResearch.Racah.Ct r S (1 / N ^ 2) := by
    have : 0 < FormalResearch.Racah.Ct r S (1 / N ^ 2) * N ^ r := by
      rw [hG]; positivity
    exact pos_of_mul_pos_left this hNr.le
  have hlog : Real.log (FormalResearch.Racah.Ct r S (1 / N ^ 2)) + r * Real.log N =
      Real.log (Real.Gamma (N * S + a)) - Real.log (Real.Gamma (N * S + b)) := by
    rw [← Real.log_pow, ← Real.log_mul hCt.ne' hNr.ne', hG, Real.log_div hGa.ne' hGb.ne']
  have hab : a - b = r := by rw [ha, hb]; ring
  have hlogNS : Real.log (N * S) = Real.log N + Real.log S := Real.log_mul hN.ne' hS.ne'
  simp only [Function.comp]
  rw [hab, hlogNS]
  linear_combination (-1 : ℝ) * hlog


theorem gammaRatioCoeff_Ct_two (r : ℕ) :
    gammaRatioCoeff 2 (((r : ℝ) + 1) / 2) ((1 - (r : ℝ)) / 2) = -((r : ℝ) * ((r : ℝ) ^ 2 - 1)) / 24 := by
  rw [gammaRatioCoeff_two]
  ring

theorem gammaRatioCoeff_Ct_odd {k : ℕ} (hk : Odd k) (r : ℕ) :
    gammaRatioCoeff k (((r : ℝ) + 1) / 2) ((1 - (r : ℝ)) / 2) = 0 := by
  rw [show (1 - (r : ℝ)) / 2 = 1 - ((r : ℝ) + 1) / 2 by ring]
  exact gammaRatioCoeff_symm_odd hk _

/-- **The first correction of `Ct`.**  `log Ct r S (1/N²) = r log S - r(r²-1)/24 · (NS)^{-2} +
O(N^{-4})` as `N → ∞` (the `O(N⁻³)` term vanishes by the symmetry `b = 1 - a`).  This is the
qualitative content of `FormalResearch.Racah.abs_log_Ct_sub_le`, whose main term it recovers. -/
theorem Ct_log_expansion_two (r : ℕ) {S : ℝ} (hS : 0 < S) :
    (fun N : ℝ => Real.log (FormalResearch.Racah.Ct r S (1 / N ^ 2)) -
      (r * Real.log S - (r : ℝ) * ((r : ℝ) ^ 2 - 1) / 24 * (N * S)⁻¹ ^ 2))
      =O[atTop] fun N : ℝ => N⁻¹ ^ 4 := by
  have h := Ct_log_expansion r hS 3
  have e : Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  refine h.congr_left fun N => ?_
  have h1 := gammaRatioCoeff_Ct_odd (by decide : Odd 1) r
  have h3 := gammaRatioCoeff_Ct_odd (by decide : Odd 3) r
  have h2 := gammaRatioCoeff_Ct_two r
  rw [e, sum_insert (by decide), sum_insert (by decide), sum_singleton, h1, h2, h3]
  ring


/-! ### Axiom pins -/

/-- info: 'FormalResearch.Special.GammaRatio.coeff_stirSeries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coeff_stirSeries

/-- info: 'FormalResearch.Special.GammaRatio.logGamma_sub_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms logGamma_sub_expansion

/-- info: 'FormalResearch.Special.GammaRatio.logGamma_sub_expansion_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms logGamma_sub_expansion_bound

/-- info: 'FormalResearch.Special.GammaRatio.gamma_ratio_isEquivalent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gamma_ratio_isEquivalent

/-- info: 'FormalResearch.Special.GammaRatio.gamma_ratio_two_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gamma_ratio_two_term

/-- info: 'FormalResearch.Special.GammaRatio.Ct_log_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ct_log_expansion

/-- info: 'FormalResearch.Special.GammaRatio.Ct_log_expansion_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ct_log_expansion_two

end FormalResearch.Special.GammaRatio
