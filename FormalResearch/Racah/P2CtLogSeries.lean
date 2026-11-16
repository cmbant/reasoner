module

public import FormalResearch.Racah.P2AnalyticCt
public import FormalResearch.Asymptotics.CenteredPowerSum
public import FormalResearch.Asymptotics.LogSeries

/-!
# The logarithm of the central factorial product as a convergent series (Weyl P2)

For the central products `Ct r u t = ∏_{q=-(r-1)/2}^{(r-1)/2} (u + q√t)`
(`FormalResearch/Racah/P2AnalyticCt.lean`; `t = h²`) we prove

* `Ct_sq_eq_prod`: `Ct r u t ^ 2 = ∏_{k<r} (u² - (k-(r-1)/2)² t)` (a polynomial identity: pairing
  `q` with `-q`);
* `Ct_pos_le`: `Ct r u t > 0` for `u > 0`, `t ≥ 0`, `r² t ≤ 4u²`;
* `Ct_log_hasSum`: under the same hypotheses
  `log Ct r u t - r log u = - ∑_{n ≥ 1} S_{2n}(r) (t/u²)^n / (2n)`,
  a convergent series, where `S_{2n}(r) = centeredPowerSum r (2n)`
  (`= 2 B_{2n+1}((r+1)/2)/(2n+1)` by `FormalResearch.Asymptotics.centeredPowerSum_even_eq_bernoulliFun`).

The hypothesis `r² t ≤ 4 u²` implies `|q| √t < u` for all `|q| ≤ (r-1)/2`, i.e. every factor
`u + q√t` is positive; on the physical `3j` lattice it holds automatically
(`P2SeedLogAllOrderPhys`).  This is the Mercator series of the finite product, exact (not
asymptotic); it is a different route to the coefficients of `Ct_log_expansion`
(`FormalResearch/Special/GammaRatio.lean`), which is a large-`N` statement through the Gamma
function.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Asymptotics Finset

/-- `𝔠_r(u,h)² = ∏_{k<r} (u² - (k-(r-1)/2)² h²)`, as a polynomial identity in `u, t = h²`. -/
theorem Ct_sq_eq_prod (r : ℕ) (u t : ℝ) :
    Ct r u t ^ 2 = ∏ k ∈ range r, (u ^ 2 - ((k : ℝ) - ((r : ℝ) - 1) / 2) ^ 2 * t) := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ => simp [Ct_zero]
    | 1, _ => simp [Ct_one]
    | r + 2, ih =>
      rw [Ct_succ_succ, mul_pow, ih r (by omega), prod_range_succ', prod_range_succ]
      have e : ∀ k ∈ range r, (u ^ 2 - (((k + 1 : ℕ) : ℝ) - (((r + 2 : ℕ) : ℝ) - 1) / 2) ^ 2 * t) =
          (u ^ 2 - ((k : ℝ) - ((r : ℝ) - 1) / 2) ^ 2 * t) := by
        intro k _; push_cast; ring
      rw [prod_congr rfl e]
      push_cast
      ring

private lemma sq_t_lt {r k : ℕ} {u t : ℝ} (hu : 0 < u) (ht : 0 ≤ t) (h : (r : ℝ) ^ 2 * t ≤ 4 * u ^ 2)
    (hk : k < r) : ((k : ℝ) - ((r : ℝ) - 1) / 2) ^ 2 * t < u ^ 2 := by
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
  have hk1 : (k : ℝ) + 1 ≤ r := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : ((k : ℝ) - ((r : ℝ) - 1) / 2) ^ 2 < (r : ℝ) ^ 2 / 4 := by
    have := sq_le_sq' (a := (k : ℝ) - ((r : ℝ) - 1) / 2) (b := ((r : ℝ) - 1) / 2)
      (by linarith) (by linarith)
    nlinarith
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0]; simpa using pow_pos hu 2
  · calc _ < (r : ℝ) ^ 2 / 4 * t := mul_lt_mul_of_pos_right h1 hpos
      _ ≤ u ^ 2 := by nlinarith

/-- `𝔠_r(u,h) > 0` when `u > 0` and `(r h)² ≤ 4u²` (every factor `u + qh` is positive). -/
theorem Ct_pos_le (r : ℕ) {u t : ℝ} (hu : 0 < u) (ht : 0 ≤ t) (h : (r : ℝ) ^ 2 * t ≤ 4 * u ^ 2) :
    0 < Ct r u t := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ => simp [Ct_zero]
    | 1, _ => simpa [Ct_one] using hu
    | r + 2, ih =>
      rw [Ct_succ_succ]
      refine mul_pos ?_ (ih r (by omega) (by
        have : (r : ℝ) ^ 2 ≤ ((r + 2 : ℕ) : ℝ) ^ 2 := by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) r]
        nlinarith))
      have := sq_t_lt (r := r + 2) (k := 0) hu ht h (by omega)
      push_cast at this
      nlinarith

/-- **`log 𝔠_r(u,h)` as a convergent series.**  For `u > 0`, `t = h² ≥ 0`, `r² t ≤ 4u²`:
`log Ct r u t - r log u = ∑_{n≥1} (-1/2) S_{2n}(r) (t/u²)^n / n`. -/
theorem Ct_log_hasSum (r : ℕ) {u t : ℝ} (hu : 0 < u) (ht : 0 ≤ t)
    (h : (r : ℝ) ^ 2 * t ≤ 4 * u ^ 2) :
    HasSum (fun n : ℕ => -(1 / 2) *
        (centeredPowerSum r (2 * (n + 1)) * (t / u ^ 2) ^ (n + 1) / ((n : ℝ) + 1)))
      (Real.log (Ct r u t) - r * Real.log u) := by
  set y : ℕ → ℝ := fun k => ((k : ℝ) - ((r : ℝ) - 1) / 2) ^ 2 * (t / u ^ 2) with hy
  have hylt : ∀ k ∈ range r, |y k| < 1 := by
    intro k hk
    have := sq_t_lt hu ht h (mem_range.1 hk)
    have hy0 : 0 ≤ y k := mul_nonneg (sq_nonneg _) (div_nonneg ht (sq_nonneg u))
    rw [abs_of_nonneg hy0, hy]
    simp only
    rw [← mul_div_assoc, div_lt_one (by positivity)]
    exact this
  have hM := (hasSum_log_one_sub_finset (range r) y hylt).mul_left (1 / 2)
  have hpos := Ct_pos_le r hu ht h
  have hfac : ∀ k ∈ range r, (1 - y k) ≠ 0 := fun k hk => (sub_pos.2 (by
    have := hylt k hk; exact (abs_lt.1 this).2)).ne'
  have hsq : Ct r u t ^ 2 = u ^ (2 * r) * ∏ k ∈ range r, (1 - y k) := by
    rw [Ct_sq_eq_prod]
    have : ∀ k ∈ range r, (u ^ 2 - ((k : ℝ) - ((r : ℝ) - 1) / 2) ^ 2 * t) = u ^ 2 * (1 - y k) := by
      intro k _; rw [hy]; simp only; field_simp
    rw [prod_congr rfl this, prod_mul_distrib, prod_const, card_range, ← pow_mul]
  have hlog : Real.log (Ct r u t) - r * Real.log u = 1 / 2 * ∑ k ∈ range r, Real.log (1 - y k) := by
    have h2 : 2 * Real.log (Ct r u t) = (2 * r) * Real.log u + ∑ k ∈ range r, Real.log (1 - y k) := by
      have := congrArg Real.log hsq
      rw [Real.log_pow, Real.log_mul (by positivity) (prod_ne_zero_iff.2 hfac),
        Real.log_pow, Real.log_prod hfac] at this
      push_cast at this
      linarith
    linarith
  rw [hlog]
  convert hM using 1
  funext n
  have : ∑ k ∈ range r, y k ^ (n + 1) = centeredPowerSum r (2 * (n + 1)) * (t / u ^ 2) ^ (n + 1) := by
    unfold centeredPowerSum
    rw [sum_mul]
    refine sum_congr rfl fun k _ => ?_
    rw [hy]; simp only; rw [mul_pow, ← pow_mul]
  rw [this]; ring

/-- info: 'FormalResearch.Racah.Ct_log_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ct_log_hasSum

end FormalResearch.Racah
