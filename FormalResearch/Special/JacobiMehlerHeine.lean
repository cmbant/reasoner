module

public import FormalResearch.Special.JacobiDef
public import FormalResearch.Special.GammaRatio
public import FormalResearch.Asymptotics.DominatedSeries

/-!
# Mehler–Heine formula for Jacobi polynomials

For real `α > -1` and real `β`, uniformly for `z` in a bounded subset of `ℂ` (hence uniformly on
compact sets),

  `n^{-α} P_n^{(α,β)}(cos(z/n)) ⟶ ∑_{ℓ≥0} (-1)^ℓ (z/2)^{2ℓ} / (ℓ! Γ(α+ℓ+1)) = (z/2)^{-α} J_α(z)`

(Szegő, Theorem 8.1.1; DLMF 18.11.1).  The limit function is `mhLimit α`, an entire function; its
identification with Mathlib's `Complex.besselJ` is in `FormalResearch/Special/JacobiBessel.lean`.

## Method

The explicit sum `jacobi` (DLMF 18.5.7) is rewritten, with `cos w - 1 = -2 sin²(w/2)`, as
`n^{-α} P_n(cos(z/n)) = ∑_{ℓ≤n} (-1)^ℓ mhCoeff α β n ℓ · (n sin(z/(2n)))^{2ℓ}` (`mh_aeval`), with the
real coefficients `mhCoeff = n^{-α-2ℓ} (n+α+β+1)_ℓ (α+ℓ+1)_{n-ℓ} / (ℓ! (n-ℓ)!)`.

* termwise limit `mhCoeff → 1/(ℓ! Γ(α+ℓ+1))` (`tendsto_mhCoeff`): `(n+γ)_ℓ/n^ℓ → 1` and the Gamma
  ratio `Γ(n+α+1)/Γ(n-ℓ+1) ∼ n^{α+ℓ}` (`GammaRatio.gamma_ratio_isEquivalent`);
* explicit summable majorant `|mhCoeff α β n ℓ| ≤ e^α (e (2+|α+β+1|))^ℓ/ℓ!` for `1 ≤ ℓ ≤ n`
  (`abs_mhCoeff_le`), from `(a+1)_m/m! ≤ exp(a H_m)` and `|(x)_ℓ| ≤ (|x|+ℓ)^ℓ`;
* `|sin w - w| ≤ |w|²` for `|w| ≤ 1` (so `n sin(z/(2n)) → z/2` uniformly on bounded sets and
  `|n sin(z/(2n))| ≤ |z|`);
* the generic uniform Tannery theorem `FormalResearch.Asymptotics.tendstoUniformlyOn_sum_of_dominated`
  (`FormalResearch/Asymptotics/DominatedSeries.lean`).

## Scope

* `α > -1` (so that every `Γ(α+ℓ+1)` is positive); `β` is arbitrary.  Not formalised: `α ≤ -1`
  (where `1/Γ` has zeros and the leading behaviour changes), a rate `O(1/n)`, and the Mehler–Heine
  formula for other families (Laguerre, Gegenbauer, Hermite).
* The statement is for the explicit-sum polynomial `jacobi` evaluated at the complex point
  `cos(z/n)` through `Polynomial.aeval`; the real-line form is in `JacobiBessel.lean`.
-/

@[expose] public section

open Polynomial Filter Topology Asymptotics

namespace FormalResearch.Special

/-- `Γ(z+m) = (z)_m Γ(z)` for real `z > 0`. -/
lemma gamma_add_nat_eq (z : ℝ) (hz : 0 < z) (m : ℕ) :
    Real.Gamma (z + m) = (ascPochhammer ℝ m).eval z * Real.Gamma z := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h0 : z + m ≠ 0 := by positivity
    rw [ascPochhammer_succ_eval, show z + ((m + 1 : ℕ) : ℝ) = (z + m) + 1 by push_cast; ring,
      Real.Gamma_add_one h0, ih]
    ring

/-- `(n+γ)_ℓ / n^ℓ → 1`. -/
lemma tendsto_poch_div_pow (γ : ℝ) (ℓ : ℕ) :
    Tendsto (fun n : ℕ => (ascPochhammer ℝ ℓ).eval ((n : ℝ) + γ) / (n : ℝ) ^ ℓ) atTop (𝓝 1) := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    have h2 : Tendsto (fun n : ℕ => 1 + (γ + ℓ) * ((n : ℝ))⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (γ + ℓ)
        |>.const_add 1
    have := ih.mul h2
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    rw [ascPochhammer_succ_eval]
    field_simp
    ring

/-- The ratio `(a+1)_m / m!` for `a = α + ℓ > -1` as a Gamma ratio, and its limit. -/
lemma tendsto_poch_div_fact (α : ℝ) (ℓ : ℕ) (hα : -1 < α) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-(α + ℓ)) *
      ((ascPochhammer ℝ (n - ℓ)).eval (α + ℓ + 1) / ((n - ℓ).factorial : ℝ)))
      atTop (𝓝 (1 / Real.Gamma (α + ℓ + 1))) := by
  have hapos : 0 < α + ℓ + 1 := by
    have : (0:ℝ) ≤ ℓ := Nat.cast_nonneg _
    linarith
  have hG := Real.Gamma_pos_of_pos hapos
  have hequiv := GammaRatio.gamma_ratio_isEquivalent (α + 1) (1 - ℓ)
  have hv : ∀ᶠ x : ℝ in atTop, x ^ (α + 1 - (1 - ℓ)) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact (Real.rpow_pos_of_pos hx _).ne'
  have h1 := (isEquivalent_iff_tendsto_one hv).1 hequiv
  have h2 : Tendsto (fun n : ℕ => (Real.Gamma ((n : ℝ) + (α + 1)) / Real.Gamma ((n : ℝ) + (1 - ℓ))) /
      (n : ℝ) ^ (α + 1 - (1 - ℓ))) atTop (𝓝 1) :=
    h1.comp tendsto_natCast_atTop_atTop
  have h3 := h2.mul_const (1 / Real.Gamma (α + ℓ + 1))
  rw [one_mul] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop ℓ, eventually_gt_atTop 0] with n hn hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have key := gamma_add_nat_eq (α + ℓ + 1) hapos (n - ℓ)
  have e1 : α + ℓ + 1 + ((n - ℓ : ℕ) : ℝ) = (n : ℝ) + (α + 1) := by
    rw [Nat.cast_sub hn]; ring
  have e2 : ((n - ℓ : ℕ) : ℝ) + 1 = (n : ℝ) + (1 - ℓ) := by
    rw [Nat.cast_sub hn]; ring
  have hf : Real.Gamma (((n - ℓ : ℕ) : ℝ) + 1) = ((n - ℓ).factorial : ℝ) :=
    Real.Gamma_nat_eq_factorial _
  rw [e1] at key
  rw [e2] at hf
  rw [key, hf, show -(α + ℓ) = -(α + 1 - (1 - ℓ)) by ring, Real.rpow_neg hnpos.le]
  have hfpos : (0 : ℝ) < Real.Gamma ((n : ℝ) + (1 - ℓ)) := by
    rw [hf]; exact_mod_cast Nat.factorial_pos _
  have hnp : (0:ℝ) < (n : ℝ) ^ (α + 1 - (1 - ℓ)) := Real.rpow_pos_of_pos hnpos _
  field_simp

/-- The rescaled coefficient `n^{-α} n^{-2ℓ} (n+α+β+1)_ℓ (α+ℓ+1)_{n-ℓ} / (ℓ! (n-ℓ)!)`: the `ℓ`-th term
of `n^{-α} P_n^{(α,β)}(cos(z/n))` is `(-1)^ℓ mhCoeff α β n ℓ · (n sin(z/(2n)))^{2ℓ}`. -/
noncomputable def mhCoeff (α β : ℝ) (n ℓ : ℕ) : ℝ :=
  (n : ℝ) ^ (-α) / (n : ℝ) ^ (2 * ℓ) *
    ((ascPochhammer ℝ ℓ).eval ((n : ℝ) + (α + β + 1)) *
      ((ascPochhammer ℝ (n - ℓ)).eval (α + ℓ + 1) / ((n - ℓ).factorial : ℝ)) /
        (ℓ.factorial : ℝ))

/-- Termwise limit of the rescaled coefficients: `mhCoeff α β n ℓ → 1/(ℓ! Γ(α+ℓ+1))`. -/
lemma tendsto_mhCoeff (α β : ℝ) (hα : -1 < α) (ℓ : ℕ) :
    Tendsto (fun n : ℕ => mhCoeff α β n ℓ) atTop
      (𝓝 (1 / ((ℓ.factorial : ℝ) * Real.Gamma (α + ℓ + 1)))) := by
  have h1 := (tendsto_poch_div_pow (α + β + 1) ℓ).mul (tendsto_poch_div_fact α ℓ hα)
  have h2 := h1.div_const (ℓ.factorial : ℝ)
  have hf : (ℓ.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero ℓ
  rw [one_mul] at h2
  have e : 1 / Real.Gamma (α + ℓ + 1) / (ℓ.factorial : ℝ) =
      1 / ((ℓ.factorial : ℝ) * Real.Gamma (α + ℓ + 1)) := by
    rw [div_div, mul_comm]
  rw [e] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [mhCoeff]
  rw [Real.rpow_neg hnpos.le, Real.rpow_neg hnpos.le, Real.rpow_add hnpos, Real.rpow_natCast,
    pow_mul']
  have : (0:ℝ) < (n : ℝ) ^ α := Real.rpow_pos_of_pos hnpos _
  field_simp

/-- `0 ≤ (a+1)_m / m! ≤ exp(a H_m)` for `a ≥ 0`, `H_m` the harmonic number. -/
lemma poch_ratio_le (a : ℝ) (ha : 0 ≤ a) (m : ℕ) :
    0 ≤ (ascPochhammer ℝ m).eval (a + 1) / (m.factorial : ℝ) ∧
      (ascPochhammer ℝ m).eval (a + 1) / (m.factorial : ℝ) ≤ Real.exp (a * (harmonic m : ℝ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨h0, h1⟩ := ih
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have e1 : (ascPochhammer ℝ (m + 1)).eval (a + 1) / ((m + 1).factorial : ℝ) =
        ((ascPochhammer ℝ m).eval (a + 1) / (m.factorial : ℝ)) * (1 + a / ((m : ℝ) + 1)) := by
      rw [ascPochhammer_succ_eval, Nat.factorial_succ]
      push_cast
      have : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
      field_simp
      ring
    have e2 : Real.exp (a * (harmonic (m + 1) : ℝ)) =
        Real.exp (a * (harmonic m : ℝ)) * Real.exp (a / ((m : ℝ) + 1)) := by
      rw [← Real.exp_add, harmonic_succ]
      push_cast
      congr 1
      ring
    rw [e1, e2]
    have hpos : 0 ≤ 1 + a / ((m : ℝ) + 1) := by positivity
    refine ⟨mul_nonneg h0 hpos, ?_⟩
    have := Real.add_one_le_exp (a / ((m : ℝ) + 1))
    exact mul_le_mul h1 (by linarith) hpos (Real.exp_pos _).le

/-- `|(x)_ℓ| ≤ (|x| + ℓ)^ℓ`. -/
lemma abs_poch_le (x : ℝ) (ℓ : ℕ) : |(ascPochhammer ℝ ℓ).eval x| ≤ (|x| + ℓ) ^ ℓ := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    rw [ascPochhammer_succ_eval, abs_mul]
    have h1 : |x + ℓ| ≤ |x| + ℓ := by
      refine (abs_add_le _ _).trans ?_
      simp
    have h2 : (|x| + ℓ) ^ ℓ * (|x| + ℓ) ≤ (|x| + ((ℓ + 1 : ℕ) : ℝ)) ^ (ℓ + 1) := by
      rw [← pow_succ]
      exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) _
    exact (mul_le_mul ih h1 (abs_nonneg _) (by positivity)).trans h2

/-- Uniform bound on the rescaled coefficients for `1 ≤ ℓ ≤ n`:
`|mhCoeff α β n ℓ| ≤ e^α (e (2 + |α+β+1|))^ℓ / ℓ!` (a summable majorant in `ℓ`). -/
lemma abs_mhCoeff_le (α β : ℝ) (hα : -1 < α) {n ℓ : ℕ} (hn : 1 ≤ n) (hℓ1 : 1 ≤ ℓ)
    (hℓn : ℓ ≤ n) :
    |mhCoeff α β n ℓ| ≤
      Real.exp α * (Real.exp 1 * (2 + |α + β + 1|)) ^ ℓ / (ℓ.factorial : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
  set γ := α + β + 1 with hγ
  set a := α + ℓ with ha
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  -- bound on the Pochhammer factor
  have hE : |(ascPochhammer ℝ ℓ).eval ((n : ℝ) + γ)| ≤ ((n : ℝ) * (2 + |γ|)) ^ ℓ := by
    refine (abs_poch_le _ ℓ).trans ?_
    gcongr
    have h1 : |(n : ℝ) + γ| ≤ n + |γ| := by
      refine (abs_add_le _ _).trans ?_
      simp
    have h2 : (ℓ : ℝ) ≤ n := by exact_mod_cast hℓn
    nlinarith [abs_nonneg γ]
  -- bound on the ratio
  obtain ⟨hR0, hR1⟩ := poch_ratio_le a ha0 (n - ℓ)
  have hH : (harmonic (n - ℓ) : ℝ) ≤ 1 + Real.log n := by
    refine (harmonic_le_one_add_log _).trans ?_
    have : Real.log ((n - ℓ : ℕ) : ℝ) ≤ Real.log n := by
      rcases Nat.eq_zero_or_pos (n - ℓ) with h | h
      · rw [h]; simpa using Real.log_nonneg hn1
      · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast Nat.sub_le n ℓ)
    linarith
  have hR : (ascPochhammer ℝ (n - ℓ)).eval (a + 1) / ((n - ℓ).factorial : ℝ) ≤
      Real.exp a * (n : ℝ) ^ a := by
    refine hR1.trans ?_
    rw [Real.rpow_def_of_pos hnpos, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : a * (harmonic (n - ℓ) : ℝ) ≤ a * (1 + Real.log n) := mul_le_mul_of_nonneg_left hH ha0
    nlinarith
  have hf : (0 : ℝ) < (ℓ.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos ℓ
  have hn2 : (0 : ℝ) < (n : ℝ) ^ (2 * ℓ) := by positivity
  have hpow : (n : ℝ) ^ (-α) * (n : ℝ) ^ a = (n : ℝ) ^ ℓ := by
    rw [← Real.rpow_add hnpos, show -α + a = (ℓ : ℝ) by rw [ha]; ring, Real.rpow_natCast]
  have hexp : Real.exp a = Real.exp α * Real.exp 1 ^ ℓ := by
    rw [ha, Real.exp_add, ← Real.exp_nat_mul, mul_one]
  simp only [mhCoeff]
  rw [show α + (ℓ : ℝ) + 1 = a + 1 by rw [ha]]
  set E := (ascPochhammer ℝ ℓ).eval ((n : ℝ) + γ) with hEdef
  set R := (ascPochhammer ℝ (n - ℓ)).eval (a + 1) / ((n - ℓ).factorial : ℝ) with hRdef
  have hnα : 0 < (n : ℝ) ^ (-α) := Real.rpow_pos_of_pos hnpos _
  rw [abs_mul, abs_div, abs_div, abs_mul, abs_of_pos hnα, abs_of_pos hn2, abs_of_pos hf,
    abs_of_nonneg hR0]
  calc (n : ℝ) ^ (-α) / (n : ℝ) ^ (2 * ℓ) * (|E| * R / ℓ.factorial)
      ≤ (n : ℝ) ^ (-α) / (n : ℝ) ^ (2 * ℓ) *
          (((n : ℝ) * (2 + |γ|)) ^ ℓ * (Real.exp a * (n : ℝ) ^ a) / ℓ.factorial) := by
        gcongr
    _ = Real.exp α * (Real.exp 1 * (2 + |γ|)) ^ ℓ / (ℓ.factorial : ℝ) := by
        rw [hexp, mul_pow, pow_mul, mul_pow]
        have : (n : ℝ) ^ (-α) * (n : ℝ) ^ a = (n : ℝ) ^ ℓ := hpow
        have hnl : (0:ℝ) < (n : ℝ) ^ ℓ := by positivity
        field_simp
        calc _ = (n : ℝ) ^ ℓ * ((n : ℝ) ^ (-α) * (n : ℝ) ^ a) := by ring
          _ = (n : ℝ) ^ ℓ * (n : ℝ) ^ ℓ := by rw [this]
          _ = ((n : ℝ) ^ 2) ^ ℓ := by rw [← pow_mul, two_mul, pow_add]

/-! ### The complex argument `cos(z/n)` -/

lemma norm_sin_sub_le {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖Complex.sin w - w‖ ≤ ‖w‖ ^ 2 := by
  have hA := Complex.norm_exp_sub_one_sub_id_le (x := w * Complex.I) (by simpa using hw)
  have hB := Complex.norm_exp_sub_one_sub_id_le (x := -(w * Complex.I)) (by simpa using hw)
  simp only [norm_neg, norm_mul, Complex.norm_I, mul_one] at hA hB
  have e : Complex.sin w - w = Complex.I / 2 *
      ((Complex.exp (-(w * Complex.I)) - 1 - -(w * Complex.I)) -
        (Complex.exp (w * Complex.I) - 1 - w * Complex.I)) := by
    rw [Complex.sin, neg_mul]
    linear_combination (-w) * Complex.I_sq
  rw [e, norm_mul, norm_div, Complex.norm_I, Complex.norm_ofNat]
  have := norm_sub_le (Complex.exp (-(w * Complex.I)) - 1 - -(w * Complex.I))
    (Complex.exp (w * Complex.I) - 1 - w * Complex.I)
  nlinarith [norm_nonneg w, sq_nonneg ‖w‖]

lemma norm_sin_le {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖Complex.sin w‖ ≤ 2 * ‖w‖ := by
  have h := norm_sin_sub_le hw
  have : ‖Complex.sin w‖ ≤ ‖Complex.sin w - w‖ + ‖w‖ := by
    simpa using norm_add_le (Complex.sin w - w) w
  nlinarith [norm_nonneg w]

/-- The `ℓ`-th term of `n^{-α} P_n^{(α,β)}(cos(z/n))` in terms of `u = n sin(z/(2n))`. -/
lemma mh_term (α β : ℝ) {n : ℕ} (hn : 1 ≤ n) (ℓ : ℕ) (z : ℂ) :
    (((n : ℝ) ^ (-α) : ℝ) : ℂ) * ((jacobiCoeff α β n ℓ : ℝ) : ℂ) *
        (Complex.cos (z / n) - 1) ^ ℓ =
      (-1) ^ ℓ * ((mhCoeff α β n ℓ : ℝ) : ℂ) *
        ((n : ℂ) * Complex.sin (z / (2 * n))) ^ (2 * ℓ) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : Complex.cos (z / n) - 1 = -2 * Complex.sin (z / (2 * n)) ^ 2 := by
    have : z / n = 2 * (z / (2 * n)) := by field_simp
    rw [this, Complex.cos_two_mul, Complex.cos_sq']
    ring
  have hreal : (n : ℝ) ^ (-α) * jacobiCoeff α β n ℓ * (-2) ^ ℓ =
      (-1) ^ ℓ * mhCoeff α β n ℓ * (n : ℝ) ^ (2 * ℓ) := by
    simp only [jacobiCoeff, mhCoeff]
    rw [show (n : ℝ) + α + β + 1 = (n : ℝ) + (α + β + 1) by ring, neg_pow (2 : ℝ)]
    have h1 : (0 : ℝ) < (n : ℝ) ^ (2 * ℓ) := by positivity
    have h2 : (ℓ.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero ℓ
    have h3 : ((n - ℓ).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp
  have hreal' : (((n : ℝ) ^ (-α) : ℝ) : ℂ) * (jacobiCoeff α β n ℓ : ℂ) * (-2) ^ ℓ =
      (-1) ^ ℓ * (mhCoeff α β n ℓ : ℂ) * ((n : ℝ) : ℂ) ^ (2 * ℓ) := by
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hreal
  rw [hc, mul_pow, ← pow_mul, mul_pow (n : ℂ)]
  push_cast at hreal' ⊢
  linear_combination Complex.sin (z / (2 * n)) ^ (2 * ℓ) * hreal'

/-- `n^{-α} P_n^{(α,β)}(cos(z/n))` as a finite sum of explicit terms. -/
lemma mh_aeval (α β : ℝ) {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    (((n : ℝ) ^ (-α) : ℝ) : ℂ) * Polynomial.aeval (Complex.cos (z / n)) (jacobi α β n) =
      ∑ ℓ ∈ Finset.range (n + 1), (-1) ^ ℓ * ((mhCoeff α β n ℓ : ℝ) : ℂ) *
        ((n : ℂ) * Complex.sin (z / (2 * n))) ^ (2 * ℓ) := by
  simp only [jacobi, map_sum, map_mul, aeval_C, map_pow, map_sub, aeval_X, map_one,
    Finset.mul_sum, Complex.coe_algebraMap]
  exact Finset.sum_congr rfl fun ℓ _ => by rw [← mh_term α β hn ℓ z, mul_assoc]

/-- The Taylor coefficients `1/(ℓ! Γ(α+ℓ+1))` of the Mehler–Heine limit function. -/
noncomputable def mhLimitCoeff (α : ℝ) (ℓ : ℕ) : ℝ :=
  1 / ((ℓ.factorial : ℝ) * Real.Gamma (α + ℓ + 1))

/-- The Mehler–Heine limit function
`∑_ℓ (-1)^ℓ (z/2)^{2ℓ} / (ℓ! Γ(α+ℓ+1)) = (z/2)^{-α} J_α(z)`, an entire function of `z`. -/
noncomputable def mhLimit (α : ℝ) (z : ℂ) : ℂ :=
  ∑' ℓ : ℕ, (-1) ^ ℓ * ((mhLimitCoeff α ℓ : ℝ) : ℂ) * (z / 2) ^ (2 * ℓ)

/-- **Mehler–Heine formula, uniform form.** For real `α > -1`, real `β` and `R ≥ 0`,
`n^{-α} P_n^{(α,β)}(cos(z/n)) → ∑_ℓ (-1)^ℓ (z/2)^{2ℓ}/(ℓ! Γ(α+ℓ+1))` as `n → ∞`, uniformly for
`‖z‖ ≤ R` in `ℂ`. -/
theorem mehlerHeine_uniform (α β : ℝ) (hα : -1 < α) {R : ℝ} (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun (n : ℕ) (z : ℂ) => (((n : ℝ) ^ (-α) : ℝ) : ℂ) *
      Polynomial.aeval (Complex.cos (z / n)) (jacobi α β n)) (mhLimit α) atTop
      (Metric.closedBall 0 R) := by
  set S : ℝ := max R 1 with hS
  have hS1 : 1 ≤ S := le_max_right _ _
  have hRS : R ≤ S := le_max_left _ _
  have hS0 : 0 < S := by linarith
  set γ : ℝ := α + β + 1 with hγ
  -- the sin bounds
  have hw : ∀ n : ℕ, (R + 1 ≤ n) → ∀ z : ℂ, ‖z‖ ≤ R → ‖z / (2 * n)‖ ≤ 1 / 2 := by
    intro n hn z hz
    have hn1 : (1 : ℝ) ≤ n := by linarith
    rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_natCast, div_le_div_iff₀ (by positivity)
      (by norm_num)]
    nlinarith
  have hu : ∀ n : ℕ, (R + 1 ≤ n) → ∀ z : ℂ, ‖z‖ ≤ R →
      ‖(n : ℂ) * Complex.sin (z / (2 * n))‖ ≤ R := by
    intro n hn z hz
    have hn1 : (1 : ℝ) ≤ n := by linarith
    have h1 := norm_sin_le (w := z / (2 * n)) (by linarith [hw n hn z hz])
    rw [norm_mul, Complex.norm_natCast]
    refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans ?_
    rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_natCast]
    field_simp
    linarith
  have hu2 : ∀ n : ℕ, (R + 1 ≤ n) → ∀ z : ℂ, ‖z‖ ≤ R →
      ‖(n : ℂ) * Complex.sin (z / (2 * n)) - z / 2‖ ≤ S ^ 2 / n := by
    intro n hn z hz
    have hn1 : (1 : ℝ) ≤ n := by linarith
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by exact_mod_cast hn1.trans_lt' zero_lt_one |>.ne')
    have h1 := norm_sin_sub_le (w := z / (2 * n)) (by linarith [hw n hn z hz])
    have e : (n : ℂ) * Complex.sin (z / (2 * n)) - z / 2 =
        (n : ℂ) * (Complex.sin (z / (2 * n)) - z / (2 * n)) := by field_simp
    rw [e, norm_mul, Complex.norm_natCast]
    have h2 : ‖z / (2 * n)‖ ^ 2 ≤ S ^ 2 / (n : ℝ) ^ 2 := by
      have : ‖z / (2 * n)‖ ≤ S / n := by
        rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_natCast,
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      rw [← div_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    calc (n : ℝ) * ‖Complex.sin (z / (2 * n)) - z / (2 * n)‖
        ≤ (n : ℝ) * (S ^ 2 / (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      _ = S ^ 2 / n := by field_simp
  have hmhA : ∀ ℓ : ℕ, 0 ≤ mhLimitCoeff α ℓ := by
    intro ℓ
    have : 0 < Real.Gamma (α + ℓ + 1) :=
      Real.Gamma_pos_of_pos (by have : (0:ℝ) ≤ ℓ := Nat.cast_nonneg _; linarith)
    unfold mhLimitCoeff
    positivity
  -- termwise uniform convergence
  have hlim : ∀ ℓ : ℕ, TendstoUniformlyOn
      (fun (n : ℕ) (z : ℂ) => (-1 : ℂ) ^ ℓ * ((mhCoeff α β n ℓ : ℝ) : ℂ) *
        ((n : ℂ) * Complex.sin (z / (2 * n))) ^ (2 * ℓ))
      (fun z => (-1 : ℂ) ^ ℓ * ((mhLimitCoeff α ℓ : ℝ) : ℂ) * (z / 2) ^ (2 * ℓ)) atTop
      (Metric.closedBall 0 R) := by
    intro ℓ
    have hm := tendsto_mhCoeff α β hα ℓ
    set A := mhLimitCoeff α ℓ with hA
    have hm' : Tendsto (fun n : ℕ => |mhCoeff α β n ℓ - A|) atTop (𝓝 0) := by
      have := (hm.sub_const A)
      simpa [hA, mhLimitCoeff] using this.abs
    have hc : Tendsto (fun n : ℕ => |mhCoeff α β n ℓ - A| * S ^ (2 * ℓ) +
        |A| * (2 * ℓ) * S ^ (2 * ℓ) * (S ^ 2 / n)) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ => S ^ 2 / (n : ℝ)) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat _
      simpa using (hm'.mul_const (S ^ (2 * ℓ))).add (h2.const_mul (|A| * (2 * ℓ) * S ^ (2 * ℓ)))
    refine FormalResearch.Asymptotics.tendstoUniformlyOn_of_norm_le hc ?_
    filter_upwards [eventually_ge_atTop ⌈R + 1⌉₊] with n hn z hz
    have hn' : R + 1 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have hz' : ‖z‖ ≤ R := by simpa using hz
    set u : ℂ := (n : ℂ) * Complex.sin (z / (2 * n)) with hudef
    have hu' : ‖u‖ ≤ S := (hu n hn' z hz').trans hRS
    have hzS : ‖z / 2‖ ≤ S := by
      rw [norm_div, Complex.norm_ofNat]; linarith [norm_nonneg z]
    have key := FormalResearch.Asymptotics.norm_pow_sub_pow_le' hu' hzS hS1 (2 * ℓ)
    have e : (-1 : ℂ) ^ ℓ * (mhCoeff α β n ℓ : ℂ) * u ^ (2 * ℓ) -
        (-1 : ℂ) ^ ℓ * (A : ℂ) * (z / 2) ^ (2 * ℓ) =
        (-1 : ℂ) ^ ℓ * (((mhCoeff α β n ℓ - A : ℝ) : ℂ) * u ^ (2 * ℓ) +
          (A : ℂ) * (u ^ (2 * ℓ) - (z / 2) ^ (2 * ℓ))) := by
      push_cast; ring
    rw [e, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu' _) (abs_nonneg _)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h3 := hu2 n hn' z hz'
      have h4 : ((2 * ℓ : ℕ) : ℝ) * S ^ (2 * ℓ) * ‖u - z / 2‖ ≤
          (2 * (ℓ : ℝ)) * S ^ (2 * ℓ) * (S ^ 2 / n) := by
        push_cast
        gcongr
      calc |A| * ‖u ^ (2 * ℓ) - (z / 2) ^ (2 * ℓ)‖
          ≤ |A| * ((2 * (ℓ : ℝ)) * S ^ (2 * ℓ) * (S ^ 2 / n)) :=
            mul_le_mul_of_nonneg_left (key.trans h4) (abs_nonneg _)
        _ = |A| * (2 * ℓ) * S ^ (2 * ℓ) * (S ^ 2 / n) := by ring
  -- domination
  set c : ℝ := Real.exp 1 * (2 + |γ|) * S ^ 2 with hcdef
  set M : ℕ → ℝ := fun ℓ => Real.exp α * (c ^ ℓ / (ℓ.factorial : ℝ)) with hMdef
  have hM : Summable M := (Real.summable_pow_div_factorial c).mul_left _
  have hM0 : ∀ ℓ, 0 ≤ M ℓ := fun ℓ => by
    have : 0 ≤ c := by positivity
    simp only [hMdef]; positivity
  have hdom : ∀ᶠ n : ℕ in atTop, ∀ ℓ ∈ Finset.range (n + 1), 1 ≤ ℓ → ∀ z ∈ Metric.closedBall (0 : ℂ) R,
      ‖(-1 : ℂ) ^ ℓ * ((mhCoeff α β n ℓ : ℝ) : ℂ) *
        ((n : ℂ) * Complex.sin (z / (2 * n))) ^ (2 * ℓ)‖ ≤ M ℓ := by
    filter_upwards [eventually_ge_atTop ⌈R + 1⌉₊] with n hn ℓ hℓ hℓ1 z hz
    have hn' : R + 1 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have hn1 : 1 ≤ n := by
      have : (1 : ℝ) ≤ n := by linarith
      exact_mod_cast this
    have hz' : ‖z‖ ≤ R := by simpa using hz
    have hℓn : ℓ ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ)
    have hu' := (hu n hn' z hz').trans hRS
    have hb := abs_mhCoeff_le α β hα hn1 hℓ1 hℓn
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
      Real.norm_eq_abs, norm_pow]
    have hf : (0 : ℝ) < (ℓ.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos ℓ
    calc |mhCoeff α β n ℓ| * ‖(n : ℂ) * Complex.sin (z / (2 * n))‖ ^ (2 * ℓ)
        ≤ (Real.exp α * (Real.exp 1 * (2 + |γ|)) ^ ℓ / (ℓ.factorial : ℝ)) * S ^ (2 * ℓ) :=
          mul_le_mul hb (pow_le_pow_left₀ (norm_nonneg _) hu' _) (by positivity)
            (by positivity)
      _ = M ℓ := by
          simp only [hMdef, hcdef]
          rw [pow_mul, mul_pow (Real.exp 1 * (2 + |γ|))]
          ring
  have hmain := FormalResearch.Asymptotics.tendstoUniformlyOn_sum_of_dominated
    (l := atTop) (s := fun n : ℕ => Finset.range (n + 1))
    (fun L => by
      filter_upwards [eventually_ge_atTop L] with n hn
      exact Finset.range_subset_range.2 (by omega))
    (Fn := fun (n : ℕ) (ℓ : ℕ) (z : ℂ) => (-1 : ℂ) ^ ℓ * ((mhCoeff α β n ℓ : ℝ) : ℂ) *
        ((n : ℂ) * Complex.sin (z / (2 * n))) ^ (2 * ℓ))
    (G := fun ℓ z => (-1 : ℂ) ^ ℓ * ((mhLimitCoeff α ℓ : ℝ) : ℂ) * (z / 2) ^ (2 * ℓ))
    (K := Metric.closedBall 0 R) hM hM0 1 hlim hdom
  refine hmain.congr ?_
  filter_upwards [eventually_ge_atTop 1] with n hn z _
  exact (mh_aeval α β hn z).symm

/-! ### Axiom check -/

/-- info: 'FormalResearch.Special.mehlerHeine_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.mehlerHeine_uniform

/-- info: 'FormalResearch.Special.tendsto_mhCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.tendsto_mhCoeff

/-- info: 'FormalResearch.Special.abs_mhCoeff_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.abs_mhCoeff_le

end FormalResearch.Special
