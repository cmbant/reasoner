module

public import FormalResearch.Racah.P2AnalyticCarrier3jRec

/-!
# The `3j` square-root-free carrier (Weyl P2, `lem:sqrtfreecarrier`): summary and consequences

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `lem:sqrtfreecarrier` (`eq:sqrtfreecarrier`,
`eq:3jrankpoly`), Appendix G.  Modules: `P2AnalyticCarrier3jDef` (definitions, polynomiality),
`P2AnalyticCarrier3jSeed` (the starts in every chamber), `P2AnalyticCarrier3jRec` (the induction,
`Phi3j_carrier`); this file collects the results and adds the closed-form germ `Gc3`, the
`t = 0` carrier `dZero3`, the rank recurrence of `ptilde3` and its leading coefficient.

## Results

* `Phi3j_carrier` (`Rec`): `Φ_{L₀+k}^{M,σ} = √(𝔠_α(τ,h)𝔠_β(1-τ,h)) / √(Ct(2L+1,1,h²)) · P̃_{L₀+k}(τ;h²)`
  at every admissible physical point, every chamber, every rank `L ≤ N-1`.
* `Phi3j_eq_Gc3`: the same as `Φ = G(x, h²)` with the explicit closed-form germ
  `Gc3 M σ k x t` (all `Ct`), the interface for the analytic half.
* `ptilde3_rank_poly`, `ptilde3_rank_poly_row0`: `eq:3jrankpoly` for `ptilde3` itself.
* `ptilde3_polynomial`, `natDegree_ptilde3Poly_le` (`Def`), `ptilde3Poly_coeff_top`: polynomiality in
  `τ` of degree `≤ k` with polynomial coefficients in `t`, leading coefficient the constant
  `lead3 M σ k`.
* `dZero3`: the `t = 0` carrier `√(τ^{p_+}(1-τ)^{p_-}) · P̃(τ;0)`, `Gc3_zero`, `dZero3_zero`,
  `dZero3_rank_rec` (the classical three-term rank recurrence of the would-be Wigner `d`).
  It is *not* identified with the Wigner `d` here.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner Polynomial

/-- The closed-form carrier germ `G(x,t) = √(Ct p_+ ((1-x)/2) t · Ct p_- ((1+x)/2) t) /
√(Ct (2L+1) 1 t) · P̃_{L₀+k}((1-x)/2; t)` (`2L+1 = p_+ + p_- + 2k + 1`), with `t = h²`. -/
noncomputable def Gc3 (M σ : ℚ) (k : ℕ) (x t : ℝ) : ℝ :=
  Real.sqrt (Ct (pPlus3 M σ) ((1 - x) / 2) t * Ct (pMinus3 M σ) ((1 + x) / 2) t) /
    Real.sqrt (Ct (pPlus3 M σ + pMinus3 M σ + 2 * k + 1) 1 t) *
    ptilde3 M σ k ((1 - x) / 2) t

/-- **`eq:sqrtfreecarrier` (3j) in germ form**: `Φ_{L₀+k}^{M,σ} = G(2μ/N, 1/N²)` on the physical
lattice, with `G = Gc3` explicit. -/
theorem Phi3j_eq_Gc3 (M σ N μ : ℚ) (α β : ℕ) (hα : |M - σ| = α) (hβ : |M + σ| = β)
    (hA : SpecAdm M σ N) (hN : 0 < N) (hlat : Lat4 M σ N μ) (k : ℕ)
    (hk : max |M| |σ| + k + 1 ≤ N) :
    Phi3j (max |M| |σ| + k) M σ N μ = Gc3 M σ k (2 * (μ : ℝ) / N) (1 / (N : ℝ) ^ 2) := by
  have h1 : pPlus3 M σ = α := by unfold pPlus3; rw [hα]; exact Nat.floor_natCast α
  have h2 : pMinus3 M σ = β := by unfold pMinus3; rw [hβ]; exact Nat.floor_natCast β
  rw [Phi3j_carrier M σ N μ α β hα hβ hA hN hlat k hk, Gc3, h1, h2,
    Cprod_eq_Ct', Cprod_eq_Ct']

/-- The `t = 0` carrier: `dZero3 M σ k x = √(((1-x)/2)^{p_+} ((1+x)/2)^{p_-}) · P̃_{L₀+k}((1-x)/2; 0)`
(the would-be Wigner `d^{L₀+k}_{Mσ}(arccos x)`; not identified with it here). -/
noncomputable def dZero3 (M σ : ℚ) (k : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (((1 - x) / 2) ^ pPlus3 M σ * ((1 + x) / 2) ^ pMinus3 M σ) *
    ptilde3 M σ k ((1 - x) / 2) 0

/-- At `t = 0` the germ is `dZero3`. -/
theorem Gc3_zero (M σ : ℚ) (k : ℕ) (x : ℝ) : Gc3 M σ k x 0 = dZero3 M σ k x := by
  unfold Gc3 dZero3
  simp [Ct_zero_t]

/-- The start of `dZero3` (extremal rank): `d^{L₀}_{Mσ} = ε √((2L₀)!/(α!β!)) √(τ^α (1-τ)^β)`. -/
theorem dZero3_zero (M σ : ℚ) (x : ℝ) :
    dZero3 M σ 0 x = seed3 M σ * Real.sqrt (((1 - x) / 2) ^ pPlus3 M σ * ((1 + x) / 2) ^ pMinus3 M σ) := by
  unfold dZero3
  rw [ptilde3_zero, mul_comm]

/-- The second scalar start: `dZero3 0 0 1 x = x` (`d^1_{00} = cos θ`). -/
theorem dZero3_one_zero (x : ℝ) : dZero3 0 0 1 x = x := by
  unfold dZero3
  rw [ptilde3_one_of_eq _ _ _ _ (by simp)]
  simp [pPlus3, pMinus3]
  ring

/-- `eq:3jrankpoly` for `ptilde3`, rows `L = L₀ + k + 1` (all rows above the first when `L₀ = 0`):
`(2L+1)[L(L+1)(1-2τ) - Mσ] P̃_L = (L+1) R_L (1-L²t) P̃_{L-1} + L R_{L+1} P̃_{L+1}`. -/
theorem ptilde3_rank_poly (M σ : ℚ) (k : ℕ) (τ t : ℝ) :
    (2 * ((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) + 1) *
        (((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) *
            (((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) + 1) * (1 - 2 * τ) - (M : ℝ) * σ) *
          ptilde3 M σ (k + 1) τ t =
      (((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) + 1) *
          Rk M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ)) *
          (1 - (((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ)) ^ 2 * t) * ptilde3 M σ k τ t +
        (((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ)) *
          Rk M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ) + 1) * ptilde3 M σ (k + 2) τ t := by
  have hL : (0 : ℚ) < max |M| |σ| + ((k + 1 : ℕ) : ℚ) := by
    have := le_trans (abs_nonneg M) (le_max_left |M| |σ|)
    have : (0 : ℚ) < ((k + 1 : ℕ) : ℚ) := by positivity
    linarith
  have hLr : ((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hR : Rk M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ) + 1) ≠ 0 := by
    apply (Rk_pos M σ _ _).ne'
    have : (0 : ℚ) ≤ ((k + 1 : ℕ) : ℚ) := Nat.cast_nonneg _
    linarith
  rw [ptilde3_succ_succ]
  unfold step3
  field_simp
  ring

/-- `eq:3jrankpoly`, first row `L = L₀ > 0` (where `R_{L₀} = 0`):
`(2L₀+1)[L₀(L₀+1)(1-2τ) - Mσ] P̃_{L₀} = L₀ R_{L₀+1} P̃_{L₀+1}`. -/
theorem ptilde3_rank_poly_row0 (M σ : ℚ) (τ t : ℝ) (h0 : max |M| |σ| ≠ 0) :
    (2 * ((max |M| |σ| : ℚ) : ℝ) + 1) *
        (((max |M| |σ| : ℚ) : ℝ) * (((max |M| |σ| : ℚ) : ℝ) + 1) * (1 - 2 * τ) - (M : ℝ) * σ) *
          ptilde3 M σ 0 τ t =
      ((max |M| |σ| : ℚ) : ℝ) * Rk M σ (max |M| |σ| + 1) * ptilde3 M σ 1 τ t := by
  have hL : (0 : ℚ) < max |M| |σ| := lt_of_le_of_ne (le_trans (abs_nonneg M) (le_max_left |M| |σ|))
    (Ne.symm h0)
  have hLr : ((max |M| |σ| : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hR : Rk M σ (max |M| |σ| + 1) ≠ 0 := (Rk_pos M σ _ (by linarith)).ne'
  rw [ptilde3_one_of_ne _ _ _ _ h0, ptilde3_zero]
  unfold step3
  field_simp
  ring

/-- **Rank recurrence of the would-be Wigner `d`** (`t = 0` of `eq:3jrankpoly`): for `L = L₀+k+1`,
`(2L+1)(L(L+1)x - Mσ) d_L = (L+1) R_L d_{L-1} + L R_{L+1} d_{L+1}` with `d_L = dZero3 M σ (L-L₀) x`. -/
theorem dZero3_rank_rec (M σ : ℚ) (k : ℕ) (x : ℝ) :
    (2 * ((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) + 1) *
        (((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) *
            (((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) + 1) * x - (M : ℝ) * σ) *
          dZero3 M σ (k + 1) x =
      (((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) + 1) *
          Rk M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ)) * dZero3 M σ k x +
        (((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ)) *
          Rk M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ) + 1) * dZero3 M σ (k + 2) x := by
  have h := ptilde3_rank_poly M σ k ((1 - x) / 2) 0
  have e : (1 : ℝ) - 2 * ((1 - x) / 2) = x := by ring
  rw [e] at h
  unfold dZero3
  simp only [mul_zero, sub_zero, mul_one] at h
  linear_combination
    (Real.sqrt (((1 - x) / 2) ^ pPlus3 M σ * ((1 + x) / 2) ^ pMinus3 M σ)) * h

/-! ### Leading coefficient -/

lemma coeff_step3P_top (M σ L : ℚ) (hL : (L : ℝ) ≠ 0) (hR : Rk M σ (L + 1) ≠ 0) (a b : Polynomial (Polynomial ℝ)) (n : ℕ)
    (ha : a.natDegree ≤ n) (hb : b.natDegree ≤ n) :
    (step3P M σ L a b).coeff (n + 1) =
      C (-2 * (2 * (L : ℝ) + 1) * ((L : ℝ) + 1) / Rk M σ (L + 1)) * a.coeff n := by
  unfold step3P
  have hY : ((C (C ((L : ℝ) * ((L : ℝ) + 1))) * (1 - C (C 2) * X) -
      C (C ((M : ℝ) * σ))) : Polynomial (Polynomial ℝ)).natDegree ≤ 1 := by
    have hX : (C (C 2) * X : Polynomial (Polynomial ℝ)).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans natDegree_X_le
    have h1X : ((1 : Polynomial (Polynomial ℝ)) - C (C 2) * X).natDegree ≤ 1 :=
      (natDegree_sub_le _ _).trans (max_le (by simp) hX)
    exact (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans h1X)
      (by rw [natDegree_C]; omega))
  have hZ : ((1 : Polynomial (Polynomial ℝ)) - C (C ((L : ℝ) ^ 2) * X)).natDegree ≤ 0 :=
    (natDegree_sub_le _ _).trans (max_le (by simp) (by rw [natDegree_C]))
  have hZb : (C (C (((L : ℝ) + 1) * Rk M σ L)) * (1 - C (C ((L : ℝ) ^ 2) * X)) * b :
      Polynomial (Polynomial ℝ)).natDegree ≤ n := by
    have e1 := natDegree_mul_le (p := (C (C (((L : ℝ) + 1) * Rk M σ L)) : Polynomial (Polynomial ℝ)) *
      (1 - C (C ((L : ℝ) ^ 2) * X))) (q := b)
    have e2 := natDegree_C_mul_le (C (((L : ℝ) + 1) * Rk M σ L) : Polynomial ℝ)
      (1 - C (C ((L : ℝ) ^ 2) * X))
    omega
  rw [coeff_C_mul, coeff_sub, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hZb (Nat.lt_succ_self n)),
    sub_zero, mul_assoc, coeff_C_mul, add_comm n 1,
    coeff_mul_add_eq_of_natDegree_le hY ha]
  simp only [coeff_sub, coeff_C_mul, coeff_one, coeff_X_one, coeff_C]
  simp only [one_ne_zero, ite_false, mul_one, zero_sub, sub_zero]
  have key : (C (1 / ((L : ℝ) * Rk M σ (L + 1))) * (C (2 * (L : ℝ) + 1) *
      (C ((L : ℝ) * ((L : ℝ) + 1)) * -C 2)) : Polynomial ℝ) =
      C (-2 * (2 * (L : ℝ) + 1) * ((L : ℝ) + 1) / Rk M σ (L + 1)) := by
    rw [← C_neg, ← C_mul, ← C_mul, ← C_mul]
    congr 1
    field_simp
  calc _ = (C (1 / ((L : ℝ) * Rk M σ (L + 1))) * (C (2 * (L : ℝ) + 1) *
      (C ((L : ℝ) * ((L : ℝ) + 1)) * -C 2))) * a.coeff n := by ring
    _ = _ := by rw [key]

/-- The `τ^k` coefficient of `P̃_{L₀+k}`: a constant (independent of `t`), by the recursion
`lead_{k+1} = -2(2L+1)(L+1)/R_{L+1} · lead_k`, `L = L₀+k`, `lead_0 = seed3 M σ`. -/
noncomputable def lead3 (M σ : ℚ) : ℕ → ℝ
  | 0 => seed3 M σ
  | k + 1 =>
      -2 * (2 * ((max |M| |σ| + (k : ℚ) : ℚ) : ℝ) + 1) * (((max |M| |σ| + (k : ℚ) : ℚ) : ℝ) + 1) /
        Rk M σ (max |M| |σ| + (k : ℚ) + 1) * lead3 M σ k

/-- **Leading coefficient** (`lem:sqrtfreecarrier`): `P̃_{L₀+k}` has degree `≤ k` in `τ` and its
`τ^k` coefficient is the `t`-independent constant `lead3 M σ k`. -/
theorem ptilde3Poly_coeff_top (M σ : ℚ) (k : ℕ) :
    (ptilde3Poly M σ k).coeff k = C (lead3 M σ k) := by
  have hL0 : (0 : ℚ) ≤ max |M| |σ| := le_trans (abs_nonneg M) (le_max_left _ _)
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [ptilde3Poly, lead3]
    | 1, _ =>
      by_cases h0 : max |M| |σ| = 0
      · have hM : M = 0 := abs_nonpos_iff.mp (h0 ▸ le_max_left _ _)
        have hs : σ = 0 := abs_nonpos_iff.mp (h0 ▸ le_max_right _ _)
        subst hM hs
        simp [ptilde3Poly, lead3, Rk, seed3, pPlus3, pMinus3, coeff_one]
      · have hL : (0 : ℚ) < max |M| |σ| := lt_of_le_of_ne hL0 (Ne.symm h0)
        have hLr : ((max |M| |σ| : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
        have hR : Rk M σ (max |M| |σ| + 1) ≠ 0 := (Rk_pos M σ _ (by linarith)).ne'
        simp only [ptilde3Poly, h0, ite_false]
        rw [coeff_step3P_top M σ _ hLr hR _ _ 0 (by simp) (by simp)]
        simp [lead3]
    | k + 2, ih =>
      have hL : (0 : ℚ) < max |M| |σ| + ((k + 1 : ℕ) : ℚ) := by
        have : (0 : ℚ) < ((k + 1 : ℕ) : ℚ) := by positivity
        linarith
      have hLr : ((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
      have hR : Rk M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ) + 1) ≠ 0 := by
        apply (Rk_pos M σ _ _).ne'
        have : (0 : ℚ) ≤ ((k + 1 : ℕ) : ℚ) := Nat.cast_nonneg _
        linarith
      rw [ptilde3Poly]
      rw [coeff_step3P_top M σ _ hLr hR _ _ (k + 1) (natDegree_ptilde3Poly_le M σ (k + 1))
        ((natDegree_ptilde3Poly_le M σ k).trans (by omega)), ih (k + 1) (by omega)]
      simp only [← C_mul, lead3]

/-- `lem:sqrtfreecarrier`, polynomiality with leading coefficient, in `∃` form: `P̃_{L₀+k}` is
`evalP P` for a `P : Polynomial (Polynomial ℝ)` (outer variable `τ`, inner `t`) of `τ`-degree `≤ k`
whose `τ^k`-coefficient is the constant polynomial `lead3 M σ k`. -/
theorem ptilde3_polynomial_lead (M σ : ℚ) (k : ℕ) :
    ∃ P : Polynomial (Polynomial ℝ), P.natDegree ≤ k ∧ P.coeff k = C (lead3 M σ k) ∧
      ∀ τ t : ℝ, ptilde3 M σ k τ t = evalP P τ t :=
  ⟨ptilde3Poly M σ k, natDegree_ptilde3Poly_le M σ k, ptilde3Poly_coeff_top M σ k,
    fun τ t => ptilde3_eq_evalP M σ k τ t⟩

/-- info: 'FormalResearch.Racah.Phi3j_eq_Gc3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_eq_Gc3

/-- info: 'FormalResearch.Racah.Gc3_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Gc3_zero

/-- info: 'FormalResearch.Racah.ptilde3_rank_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ptilde3_rank_poly

/-- info: 'FormalResearch.Racah.ptilde3_rank_poly_row0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ptilde3_rank_poly_row0

/-- info: 'FormalResearch.Racah.dZero3_rank_rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dZero3_rank_rec

/-- info: 'FormalResearch.Racah.ptilde3Poly_coeff_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ptilde3Poly_coeff_top

/-- info: 'FormalResearch.Racah.ptilde3_polynomial_lead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ptilde3_polynomial_lead

end FormalResearch.Racah
