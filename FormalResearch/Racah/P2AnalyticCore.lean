module

public import Mathlib
public import FormalResearch.Racah.P2AnalyticCt

/-!
# Generic analytic lemmas for the analytic half of Weyl P2 (WP1: T1.1, T1.2, T1.4)

Paper labels: `lem:centeredshift` (T1.1), `thm:analytic-recurrence` and
`lem:physicalinterpolation` (scalar content, T1.2), `lem:momentpolynomial` /
the central-binomial convolution `∑_{i+j=r} C(2i,i) C(2j,j) = 4^r` (T1.4).

## T1.1: the central products `Ct r u t` (polynomials in `u`, `t = h²`)

* `CtPoly r`, `eval_CtPoly`: `Ct r u t` is the evaluation of an explicit `MvPolynomial (Fin 2) ℝ`.
* `analyticAt_Ct_comp`, `analyticAt_Ct`, `contDiff_Ct`: analytic / smooth everywhere.
* `Ct_zero_t` (in `P2AnalyticCt`): `Ct r u 0 = u ^ r`.
* `Ct_pos`: `0 < Ct r u t` for `u > 0`, `t ≥ 0`, `r² t < 4u²`.
* `abs_log_Ct_sub_le`, `abs_log_Ct_sub_le_of_le`: the log estimate
  `|log (Ct r S t) - (r log S - r(r²-1)/24 · t/S²)| ≤ (r⁵/8)(t/S²)²` (explicit constant,
  valid for `r² t/S² ≤ 1/2`; the second form gives `C t²` with `C = r⁵/(8 S₀⁴)` for `S ≥ S₀`).
* `Ct_Gamma`: `Ct r S (1/N²) · N^r = Γ(NS+(r+1)/2)/Γ(NS-(r-1)/2)` when `NS - (r-1)/2 > 0`.

## T1.2: scalar analytic propagation

* `analyticAt_recurrence_two` / `analyticAt_recurrence_one`: a three-term recurrence
  `a k · y (k+1) = b k · y k - c k · y (k-1)` with coefficients analytic at `p₀`,
  `a k p₀ ≠ 0`, and analytic start data has every `y k` analytic at `p₀`.  (Here `p₀` lives in any
  real normed space `X`; in the application `X = E × ℝ` and `p₀ = (z₀, 0)`.)
* `analyticAt_sqrt_comp`: square root of a positive analytic function is analytic.

## T1.4: the central binomial convolution `sum_centralBinom_mul`.
-/

@[expose] public section

namespace FormalResearch.Racah

open Filter Topology
open scoped ContDiff

/-! ### T1.1: `Ct` is a polynomial / analytic -/

/-- Explicit polynomial in `(u,t) = (X 0, X 1)` representing `Ct r u t`. -/
noncomputable def CtPoly : ℕ → MvPolynomial (Fin 2) ℝ
  | 0 => 1
  | 1 => MvPolynomial.X 0
  | r + 2 => (MvPolynomial.X 0 ^ 2 - MvPolynomial.C (((r : ℝ) + 1) ^ 2 / 4) * MvPolynomial.X 1) *
      CtPoly r

/-- `Ct r u t` is the value of the explicit polynomial `CtPoly r` at `(u,t)`. -/
theorem eval_CtPoly (r : ℕ) (u t : ℝ) :
    MvPolynomial.eval ![u, t] (CtPoly r) = Ct r u t := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ => simp [CtPoly, Ct_zero]
    | 1, _ => simp [CtPoly, Ct_one]
    | r + 2, ih =>
      simp only [CtPoly, Ct_succ_succ, map_mul, map_sub, map_pow, MvPolynomial.eval_X,
        MvPolynomial.eval_C]
      rw [ih r (by omega)]
      simp

/-- `Ct r (u x) (t x)` is analytic at `x` when `u` and `t` are. -/
theorem analyticAt_Ct_comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (r : ℕ)
    {u t : X → ℝ} {x : X} (hu : AnalyticAt ℝ u x) (ht : AnalyticAt ℝ t x) :
    AnalyticAt ℝ (fun y => Ct r (u y) (t y)) x := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ => simpa [Ct_zero] using analyticAt_const
    | 1, _ => simpa [Ct_one] using hu
    | r + 2, ih =>
      simp only [Ct_succ_succ]
      exact ((hu.pow 2).sub (analyticAt_const.mul ht)).mul (ih r (by omega))

/-- `(u,t) ↦ Ct r u t` is analytic at every point of `ℝ × ℝ`. -/
theorem analyticAt_Ct (r : ℕ) (p : ℝ × ℝ) :
    AnalyticAt ℝ (fun q : ℝ × ℝ => Ct r q.1 q.2) p :=
  analyticAt_Ct_comp r (analyticAt_fst) (analyticAt_snd)

/-- `(u,t) ↦ Ct r u t` is `C^∞`. -/
theorem contDiff_Ct (r : ℕ) : ContDiff ℝ ∞ (fun q : ℝ × ℝ => Ct r q.1 q.2) :=
  contDiff_iff_contDiffAt.mpr fun p => (analyticAt_Ct r p).contDiffAt
/-- Positivity of the central product in the small-`t` range `r² t < 4u²`. -/
theorem Ct_pos (r : ℕ) {u t : ℝ} (hu : 0 < u) (ht : 0 ≤ t)
    (hr : (r : ℝ) ^ 2 * t < 4 * u ^ 2) : 0 < Ct r u t := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ => simp [Ct_zero]
    | 1, _ => simpa [Ct_one] using hu
    | r + 2, ih =>
      rw [Ct_succ_succ]
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have h1 : ((r : ℝ) + 1) ^ 2 * t ≤ ((r : ℝ) + 2) ^ 2 * t :=
        mul_le_mul_of_nonneg_right (by nlinarith) ht
      have h2 : (r : ℝ) ^ 2 * t ≤ ((r : ℝ) + 2) ^ 2 * t :=
        mul_le_mul_of_nonneg_right (by nlinarith) ht
      have hr' : (((r + 2 : ℕ) : ℝ)) = (r : ℝ) + 2 := by push_cast; ring
      rw [hr'] at hr
      refine mul_pos (by nlinarith) (ih r (by omega) (by nlinarith))

/-! ### The logarithmic estimate -/

theorem abs_log_one_sub_add_le {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) :
    |y + Real.log (1 - y)| ≤ 2 * y ^ 2 := by
  have hy1 : |y| < 1 := by rw [abs_of_nonneg hy0]; linarith
  have := Real.abs_log_sub_add_sum_range_le hy1 1
  simp only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, div_one] at this
  rw [abs_of_nonneg hy0] at this
  refine this.trans ?_
  rw [div_le_iff₀ (by linarith)]
  have h2 : y ^ (1 + 1) = y ^ 2 := by norm_num
  rw [h2]
  nlinarith [mul_nonneg (sq_nonneg y) (by linarith : 0 ≤ 1 - 2 * y)]

/-- **Log estimate for the central products** (`lem:centeredshift`).  For `S > 0`, `t ≥ 0` and
`r² · (t/S²) ≤ 1/2`:
`|log Ct r S t - (r log S - r(r²-1)/24 · t/S²)| ≤ (r⁵/8) (t/S²)²`. -/
theorem abs_log_Ct_sub_le (r : ℕ) {S t : ℝ} (hS : 0 < S) (ht : 0 ≤ t)
    (hx : (r : ℝ) ^ 2 * (t / S ^ 2) ≤ 1 / 2) :
    |Real.log (Ct r S t) - ((r : ℝ) * Real.log S - (r : ℝ) * ((r : ℝ) ^ 2 - 1) / 24 * (t / S ^ 2))|
      ≤ (r : ℝ) ^ 5 / 8 * (t / S ^ 2) ^ 2 := by
  have hS2 : 0 < S ^ 2 := by positivity
  set x : ℝ := t / S ^ 2 with hxdef
  have hx0 : 0 ≤ x := by positivity
  have htx : t = x * S ^ 2 := by rw [hxdef]; field_simp
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ => simp [Ct_zero]
    | 1, _ => simp [Ct_one]; positivity
    | r + 2, ih =>
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have hr' : (((r + 2 : ℕ) : ℝ)) = (r : ℝ) + 2 := by push_cast; ring
      rw [hr'] at hx ⊢
      have hxr : (r : ℝ) ^ 2 * x ≤ 1 / 2 := by nlinarith
      have hrec := ih r (by omega) (by simpa using hxr)
      set a : ℝ := ((r : ℝ) + 1) ^ 2 / 4 with ha
      have ha0 : 0 ≤ a := by positivity
      have hax : a * x ≤ 1 / 2 := by rw [ha]; nlinarith
      have hpos : 0 < Ct r S t := by
        refine Ct_pos r hS ht ?_
        have : (r : ℝ) ^ 2 * t ≤ S ^ 2 / 2 := by rw [htx]; nlinarith
        nlinarith
      have hfac : 0 < 1 - a * x := by linarith
      have hlog : Real.log (Ct (r + 2) S t) =
          Real.log (Ct r S t) + (2 * Real.log S + Real.log (1 - a * x)) := by
        rw [Ct_succ_succ]
        have e : S ^ 2 - ((r : ℝ) + 1) ^ 2 / 4 * t = S ^ 2 * (1 - a * x) := by
          rw [htx, ha]; ring
        rw [e, Real.log_mul (mul_pos hS2 hfac).ne' hpos.ne', Real.log_mul hS2.ne' hfac.ne',
          Real.log_pow]
        push_cast; ring
      have hstep := abs_log_one_sub_add_le (y := a * x) (by positivity) hax
      rw [hlog]
      have key : Real.log (Ct r S t) + (2 * Real.log S + Real.log (1 - a * x)) -
          (((r : ℝ) + 2) * Real.log S - ((r : ℝ) + 2) * (((r : ℝ) + 2) ^ 2 - 1) / 24 * x) =
          (Real.log (Ct r S t) - ((r : ℝ) * Real.log S - (r : ℝ) * ((r : ℝ) ^ 2 - 1) / 24 * x)) +
          (a * x + Real.log (1 - a * x)) := by
        rw [ha]; ring
      rw [key]
      refine (abs_add_le _ _).trans ?_
      have hb : 2 * (a * x) ^ 2 ≤ ((r : ℝ) + 2) ^ 5 / 8 * x ^ 2 - (r : ℝ) ^ 5 / 8 * x ^ 2 := by
        have : 2 * (a * x) ^ 2 = ((r : ℝ) + 1) ^ 4 / 8 * x ^ 2 := by rw [ha]; ring
        rw [this]
        have hp : ((r : ℝ) + 1) ^ 4 ≤ ((r : ℝ) + 2) ^ 5 - (r : ℝ) ^ 5 := by
          nlinarith [pow_nonneg hr0 2, pow_nonneg hr0 3, pow_nonneg hr0 4]
        nlinarith [sq_nonneg x]
      linarith

/-- The `C t²` form of the log estimate on a compact range `S ≥ S₀ > 0`, `r² t ≤ S₀²/2`:
the constant is `r⁵/(8 S₀⁴)`. -/
theorem abs_log_Ct_sub_le_of_le (r : ℕ) {S₀ S t : ℝ} (hS₀ : 0 < S₀) (hS : S₀ ≤ S)
    (ht : 0 ≤ t) (hr : (r : ℝ) ^ 2 * t ≤ S₀ ^ 2 / 2) :
    |Real.log (Ct r S t) - ((r : ℝ) * Real.log S - (r : ℝ) * ((r : ℝ) ^ 2 - 1) / 24 * (t / S ^ 2))|
      ≤ (r : ℝ) ^ 5 / (8 * S₀ ^ 4) * t ^ 2 := by
  have hSpos : 0 < S := hS₀.trans_le hS
  have hS2 : S₀ ^ 2 ≤ S ^ 2 := by nlinarith
  have hx : (r : ℝ) ^ 2 * (t / S ^ 2) ≤ 1 / 2 := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    have : (r : ℝ) ^ 2 * t ≤ S ^ 2 / 2 := hr.trans (by linarith)
    linarith
  refine (abs_log_Ct_sub_le r hSpos ht hx).trans ?_
  have h4 : S₀ ^ 4 ≤ S ^ 4 := by
    calc S₀ ^ 4 = (S₀ ^ 2) ^ 2 := by ring
      _ ≤ (S ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hS2 2
      _ = S ^ 4 := by ring
  have : (r : ℝ) ^ 5 / 8 * (t / S ^ 2) ^ 2 = (r : ℝ) ^ 5 / (8 * S ^ 4) * t ^ 2 := by
    field_simp
  rw [this]
  have h5 : (r : ℝ) ^ 5 / (8 * S ^ 4) ≤ (r : ℝ) ^ 5 / (8 * S₀ ^ 4) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  exact mul_le_mul_of_nonneg_right h5 (by positivity)

/-! ### The Gamma form -/

/-- **Gamma form** (`lem:centeredshift`, consecutive case):
`Ct r S (1/N²) · N^r = Γ(NS + (r+1)/2) / Γ(NS - (r-1)/2)` whenever `N > 0` and
`NS - (r-1)/2 > 0`. -/
theorem Ct_Gamma (r : ℕ) {N S : ℝ} (hN : 0 < N)
    (hpos : 0 < N * S - ((r : ℝ) - 1) / 2) :
    Ct r S (1 / N ^ 2) * N ^ r =
      Real.Gamma (N * S + ((r : ℝ) + 1) / 2) / Real.Gamma (N * S - ((r : ℝ) - 1) / 2) := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ =>
      simp only [Ct_zero, pow_zero, mul_one, Nat.cast_zero] at hpos ⊢
      rw [show N * S + (0 + 1) / 2 = N * S - (0 - 1) / 2 by ring]
      exact (div_self (Real.Gamma_pos_of_pos hpos).ne').symm
    | 1, _ =>
      simp only [Ct_one, pow_one, Nat.cast_one] at hpos ⊢
      have hNS : 0 < N * S := by linarith
      have h1 : N * S + (1 + 1) / 2 = N * S + 1 := by ring
      have h2 : N * S - (1 - 1) / 2 = N * S := by ring
      rw [h1, h2, Real.Gamma_add_one hNS.ne', mul_div_assoc,
        div_self (Real.Gamma_pos_of_pos hNS).ne', mul_one]
      ring
    | r + 2, ih =>
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have hr' : (((r + 2 : ℕ) : ℝ)) = (r : ℝ) + 2 := by push_cast; ring
      rw [hr'] at hpos ⊢
      have hpos' : 0 < N * S - ((r : ℝ) - 1) / 2 := by linarith
      have hih := ih r (by omega) hpos'
      have hA : 0 < N * S - ((r : ℝ) + 1) / 2 := by linarith
      have hB : 0 < N * S + ((r : ℝ) + 1) / 2 := by linarith
      have e1 : N * S + ((r : ℝ) + 2 + 1) / 2 = (N * S + ((r : ℝ) + 1) / 2) + 1 := by ring
      have e2 : N * S - ((r : ℝ) + 2 - 1) / 2 = N * S - ((r : ℝ) + 1) / 2 := by ring
      have e3 : N * S - ((r : ℝ) - 1) / 2 = (N * S - ((r : ℝ) + 1) / 2) + 1 := by ring
      rw [e1, e2, Real.Gamma_add_one hB.ne']
      rw [e3, Real.Gamma_add_one hA.ne'] at hih
      have hGA := (Real.Gamma_pos_of_pos hA).ne'
      have hGB := (Real.Gamma_pos_of_pos hB).ne'
      have hfac : Ct (r + 2) S (1 / N ^ 2) * N ^ (r + 2) =
          ((N * S + ((r : ℝ) + 1) / 2) * (N * S - ((r : ℝ) + 1) / 2)) *
            (Ct r S (1 / N ^ 2) * N ^ r) := by
        rw [Ct_succ_succ]; field_simp; ring
      rw [hfac, hih]
      have hA0 := hA.ne'
      rw [mul_div_assoc', mul_comm (N * S + ((r : ℝ) + 1) / 2) _, mul_assoc,
        mul_div_mul_left _ _ hA0]

/-! ### T1.2: analytic propagation of a scalar three-term recurrence -/

section Propagation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Analytic propagation, two analytic starts** (scalar `thm:analytic-recurrence`).
Let `a b c : ℕ → X → ℝ` be analytic at `p₀` with `a k p₀ ≠ 0`, and let `y : ℕ → X → ℝ` satisfy
`a (k+1) · y (k+2) = b (k+1) · y (k+1) - c (k+1) · y k` near `p₀` for every `k`.  If `y 0`, `y 1`
are analytic at `p₀`, so is every `y k`.  (In the application `X = E × ℝ` and `p₀ = (z₀, 0)`.) -/
theorem analyticAt_recurrence_two {a b c y : ℕ → X → ℝ} {p₀ : X}
    (ha : ∀ k, AnalyticAt ℝ (a k) p₀) (hb : ∀ k, AnalyticAt ℝ (b k) p₀)
    (hc : ∀ k, AnalyticAt ℝ (c k) p₀) (ha0 : ∀ k, a k p₀ ≠ 0)
    (hrec : ∀ k, ∀ᶠ p in 𝓝 p₀, a (k + 1) p * y (k + 2) p =
      b (k + 1) p * y (k + 1) p - c (k + 1) p * y k p)
    (hy0 : AnalyticAt ℝ (y 0) p₀) (hy1 : AnalyticAt ℝ (y 1) p₀) :
    ∀ k, AnalyticAt ℝ (y k) p₀ := by
  have key : ∀ k, AnalyticAt ℝ (y k) p₀ ∧ AnalyticAt ℝ (y (k + 1)) p₀ := by
    intro k
    induction k with
    | zero => exact ⟨hy0, hy1⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hne : ∀ᶠ p in 𝓝 p₀, a (k + 1) p ≠ 0 :=
        (ha (k + 1)).continuousAt.eventually_ne (ha0 (k + 1))
      have hq : AnalyticAt ℝ (fun p => (b (k + 1) p * y (k + 1) p - c (k + 1) p * y k p) /
          a (k + 1) p) p₀ :=
        (((hb (k + 1)).mul ih.2).sub ((hc (k + 1)).mul ih.1)).div (ha (k + 1)) (ha0 (k + 1))
      refine hq.congr ?_
      filter_upwards [hrec k, hne] with p hp hn
      rw [← hp]
      field_simp
  exact fun k => (key k).1

/-- **Analytic propagation, one analytic start.**  With the convention `y (k-1) = y 0` at `k = 0`
(natural subtraction), i.e. `a 0 · y 1 = (b 0 - c 0) · y 0`: relations
`a k · y (k+1) = b k · y k - c k · y (k-1)` near `p₀` for all `k` and an analytic `y 0` make
every `y k` analytic at `p₀`.  (When `c 0 = 0` this is the "single analytic start" case.) -/
theorem analyticAt_recurrence_one {a b c y : ℕ → X → ℝ} {p₀ : X}
    (ha : ∀ k, AnalyticAt ℝ (a k) p₀) (hb : ∀ k, AnalyticAt ℝ (b k) p₀)
    (hc : ∀ k, AnalyticAt ℝ (c k) p₀) (ha0 : ∀ k, a k p₀ ≠ 0)
    (hrec : ∀ k, ∀ᶠ p in 𝓝 p₀, a k p * y (k + 1) p = b k p * y k p - c k p * y (k - 1) p)
    (hy0 : AnalyticAt ℝ (y 0) p₀) : ∀ k, AnalyticAt ℝ (y k) p₀ := by
  have hy1 : AnalyticAt ℝ (y 1) p₀ := by
    have hne : ∀ᶠ p in 𝓝 p₀, a 0 p ≠ 0 := (ha 0).continuousAt.eventually_ne (ha0 0)
    have hq : AnalyticAt ℝ (fun p => (b 0 p - c 0 p) * y 0 p / a 0 p) p₀ :=
      (((hb 0).sub (hc 0)).mul hy0).div (ha 0) (ha0 0)
    refine hq.congr ?_
    filter_upwards [hrec 0, hne] with p hp hn
    have : a 0 p * y 1 p = (b 0 p - c 0 p) * y 0 p := by simpa [sub_mul] using hp
    rw [← this]
    field_simp
  refine analyticAt_recurrence_two ha hb hc ha0 (fun k => ?_) hy0 hy1
  filter_upwards [hrec (k + 1)] with p hp
  simpa using hp

/-- The square root of a positive analytic function is analytic (`lem:physicalinterpolation`,
branch of the square root). -/
theorem analyticAt_sqrt_comp {g : X → ℝ} {p₀ : X} (hg : AnalyticAt ℝ g p₀) (h0 : 0 < g p₀) :
    AnalyticAt ℝ (fun p => Real.sqrt (g p)) p₀ := by
  have hlog : AnalyticAt ℝ (fun p => Real.log (g p)) p₀ :=
    (analyticAt_log h0).comp_of_eq hg rfl
  have h1 : AnalyticAt ℝ (fun p => Real.exp (Real.log (g p) / 2)) p₀ :=
    analyticAt_rexp.comp_of_eq hlog.div_const rfl
  refine h1.congr ?_
  filter_upwards [hg.continuousAt.eventually (lt_mem_nhds h0)] with p hp
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp]
  ring_nf

/-- One-variable version: `Real.sqrt` is analytic at positive points. -/
theorem analyticAt_real_sqrt {x : ℝ} (hx : 0 < x) : AnalyticAt ℝ Real.sqrt x :=
  analyticAt_sqrt_comp (g := id) analyticAt_id hx

end Propagation

/-! ### T1.4: the central binomial convolution -/

section CentralBinom

open scoped PowerSeries

private lemma coeff_X_mul_derivative' (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X * d⁄dX f) = n * PowerSeries.coeff n f := by
  cases n with
  | zero => simp
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    push_cast; ring

private lemma coeff_four_mul (φ : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n ((4 : PowerSeries ℚ) * φ) = 4 * PowerSeries.coeff n φ := by
  rw [← map_ofNat (PowerSeries.C (R := ℚ)) 4, PowerSeries.coeff_C_mul]

private lemma coeff_two_mul (φ : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n ((2 : PowerSeries ℚ) * φ) = 2 * PowerSeries.coeff n φ := by
  rw [← map_ofNat (PowerSeries.C (R := ℚ)) 2, PowerSeries.coeff_C_mul]

/-- `∑_{i+j=r} C(2i,i) C(2j,j) = 4^r`. -/
theorem sum_centralBinom_mul (r : ℕ) :
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal r,
      Nat.centralBinom ij.1 * Nat.centralBinom ij.2 = 4 ^ r := by
  let f : PowerSeries ℚ := PowerSeries.mk fun n => (Nat.centralBinom n : ℚ)
  have hf : d⁄dX f = 4 * (PowerSeries.X * d⁄dX f) + 2 * f := by
    ext n
    rw [PowerSeries.coeff_derivative, map_add, coeff_four_mul, coeff_two_mul,
      coeff_X_mul_derivative']
    simp only [f, PowerSeries.coeff_mk]
    have := Nat.succ_mul_centralBinom_succ n
    have h' : ((n + 1 : ℕ) : ℚ) * (Nat.centralBinom (n + 1) : ℚ) =
        2 * (2 * (n : ℚ) + 1) * (Nat.centralBinom n : ℚ) := by exact_mod_cast this
    push_cast at h'
    linear_combination h'
  set g : PowerSeries ℚ := f * f with hg
  have hdg : d⁄dX g = 4 * (PowerSeries.X * d⁄dX g) + 4 * g := by
    have h1 : d⁄dX g = 2 * f * d⁄dX f := by
      rw [hg, Derivation.leibniz]; simp only [smul_eq_mul]; ring
    rw [h1]
    linear_combination (2 * f) * hf
  have hrec : ∀ n, PowerSeries.coeff (n + 1) g = 4 * PowerSeries.coeff n g := by
    intro n
    have := congrArg (PowerSeries.coeff n) hdg
    rw [PowerSeries.coeff_derivative, map_add, coeff_four_mul, coeff_four_mul,
      coeff_X_mul_derivative'] at this
    have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
    have h2 : ((n : ℚ) + 1) * PowerSeries.coeff (n + 1) g =
        ((n : ℚ) + 1) * (4 * PowerSeries.coeff n g) := by
      linear_combination this
    exact mul_left_cancel₀ hn h2
  have hg0 : PowerSeries.coeff 0 g = 1 := by simp [hg, f, Nat.centralBinom_zero]
  have hgn : ∀ n, PowerSeries.coeff n g = 4 ^ n := by
    intro n
    induction n with
    | zero => simpa using hg0
    | succ n ih => rw [hrec, ih]; ring
  have := hgn r
  rw [hg, PowerSeries.coeff_mul] at this
  simp only [f, PowerSeries.coeff_mk] at this
  exact_mod_cast this

/-- Power-series form: `(∑ C(2r,r) 4^{-r} Xʳ)² (1 - X) = 1` over `ℚ`. -/
theorem centralBinom_series_sq :
    (PowerSeries.mk fun r => (Nat.centralBinom r : ℚ) / 4 ^ r) ^ 2 * (1 - PowerSeries.X) = 1 := by
  set h : PowerSeries ℚ := PowerSeries.mk fun r => (Nat.centralBinom r : ℚ) / 4 ^ r with hh
  have hsq : ∀ n, PowerSeries.coeff n (h ^ 2) = 1 := by
    intro n
    rw [sq, PowerSeries.coeff_mul]
    have := sum_centralBinom_mul n
    have hq : ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        (Nat.centralBinom ij.1 : ℚ) * Nat.centralBinom ij.2 = 4 ^ n := by exact_mod_cast this
    simp only [hh, PowerSeries.coeff_mk]
    have h4 : (0 : ℚ) < 4 ^ n := by positivity
    refine mul_left_cancel₀ h4.ne' ?_
    have hterm : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        (4 : ℚ) ^ n * ((Nat.centralBinom ij.1 : ℚ) / 4 ^ ij.1 * ((Nat.centralBinom ij.2 : ℚ) / 4 ^ ij.2))
          = (Nat.centralBinom ij.1 : ℚ) * Nat.centralBinom ij.2 := by
      intro ij hij
      have hs : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      rw [← hs, pow_add]
      field_simp
    rw [Finset.mul_sum, Finset.sum_congr rfl hterm, hq, mul_one]
  have hser : h ^ 2 = PowerSeries.mk fun _ => (1 : ℚ) := by
    ext n; rw [hsq, PowerSeries.coeff_mk]
  rw [hser]
  ext n
  rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mk]
  cases n with
  | zero => simp
  | succ n =>
    rw [mul_comm, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
    simp

end CentralBinom

/-- info: 'FormalResearch.Racah.abs_log_Ct_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abs_log_Ct_sub_le

/-- info: 'FormalResearch.Racah.Ct_Gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ct_Gamma

/-- info: 'FormalResearch.Racah.analyticAt_recurrence_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms analyticAt_recurrence_two

/-- info: 'FormalResearch.Racah.analyticAt_sqrt_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms analyticAt_sqrt_comp

/-- info: 'FormalResearch.Racah.sum_centralBinom_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sum_centralBinom_mul

/-- info: 'FormalResearch.Racah.centralBinom_series_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms centralBinom_series_sq

/-- info: 'FormalResearch.Racah.contDiff_Ct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiff_Ct

/-- info: 'FormalResearch.Racah.Ct_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ct_pos

/-- info: 'FormalResearch.Racah.eval_CtPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_CtPoly

end FormalResearch.Racah
