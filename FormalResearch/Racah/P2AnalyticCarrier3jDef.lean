module

public import FormalResearch.Racah.P2AnalyticCt
public import FormalResearch.Racah.P2ThreeJRec

/-!
# The square-root-free `3j` carrier: definitions and polynomiality (Weyl P2, `lem:sqrtfreecarrier`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `lem:sqrtfreecarrier`
(`eq:sqrtfreecarrier`, `eq:3jrankpoly`), Appendix G.

## Conventions

* `M σ : ℚ` with `α = |M-σ|` and `β = |M+σ|` natural numbers (`pPlus3 M σ`, `pMinus3 M σ`; the
  paper's `p_+ = |M-σ|`, `p_- = |M+σ|`); the minimal rank is `L₀ = max(|M|,|σ|)` and
  `α + β = 2 L₀` (`hahn_alpha_add_beta`).  The rank is written `L = L₀ + k`.
* `τ = (1-x)/2` and `t = h²` are two independent real variables (the paper's `t` of
  `lem:sqrtfreecarrier` is our `τ`; our `t = h² = N⁻²` is the paper's `h²`).
* `ptilde3 M σ k τ t` is `P̃_{L₀+k}` of `lem:sqrtfreecarrier`, defined by the square-root-free
  rank recurrence `eq:3jrankpoly`
  `(2L+1)[L(L+1)(1-2τ) - Mσ] P̃_L = (L+1) R_L (1-L²t) P̃_{L-1} + L R_{L+1} P̃_{L+1}`
  (`R_k = Rk M σ k`), solved forwards for `P̃_{L+1}` (`step3`), with the starts
  * `P̃_{L₀} = seed3 M σ = ε(M,σ) √((2L₀)!/(α! β!))`, `ε = (-1)^α` for `σ ≤ M` and `1` for `σ > M`
    (the chamber signs of `eq:HahnAllChamberPhase`; this is the paper's
    `(-1)^{L₀-σ} √((2L₀)!/((L₀+σ)!(L₀-σ)!))` in the extremal chamber `M = L₀`);
  * for `L₀ > 0` the row `L = L₀` has no backward term (`R_{L₀} = 0`), so `P̃_{L₀+1}` is given
    by the recurrence from `P̃_{L₀}` alone; for `L₀ = 0` (`M = σ = 0`) the recurrence is degenerate
    (`L R_{L+1} = 0`) and the start is `P̃_1 = 1 - 2τ` (the paper's second scalar start).

## Results

* `ptilde3_*`: the defining equations.
* `ptilde3Poly`, `ptilde3_eq_evalP`: `P̃_{L₀+k}` is `evalP` of an explicit polynomial in `τ` with
  coefficients polynomial in `t` (an element of `Polynomial (Polynomial ℝ)`, outer variable `τ`,
  inner variable `t`); `natDegree_ptilde3Poly_le`: degree `≤ k` in `τ`.
* `Ct_zero_t`: `Ct r u 0 = u ^ r`.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner Polynomial

/-- `p_+ = |M - σ|` as a natural number. -/
def pPlus3 (M σ : ℚ) : ℕ := ⌊|M - σ|⌋₊

/-- `p_- = |M + σ|` as a natural number. -/
def pMinus3 (M σ : ℚ) : ℕ := ⌊|M + σ|⌋₊

/-- The start `P̃_{L₀}` of the carrier in every chamber:
`ε(M,σ) √((2L₀)!/(α!β!))`, `ε = (-1)^α` if `σ ≤ M` and `1` if `σ > M`
(`α = |M-σ|`, `β = |M+σ|`, `α + β = 2 L₀`). -/
noncomputable def seed3 (M σ : ℚ) : ℝ :=
  (if σ ≤ M then (-1 : ℝ) ^ pPlus3 M σ else 1) *
    Real.sqrt (((pPlus3 M σ + pMinus3 M σ).factorial : ℝ) /
      (((pPlus3 M σ).factorial : ℝ) * ((pMinus3 M σ).factorial : ℝ)))

/-- One forward step of the square-root-free rank recurrence `eq:3jrankpoly`: from `a = P̃_L`
and `b = P̃_{L-1}` to `P̃_{L+1}`,
`((2L+1)[L(L+1)(1-2τ) - Mσ] a - (L+1) R_L (1-L²t) b) / (L R_{L+1})`. -/
noncomputable def step3 (M σ L : ℚ) (τ t a b : ℝ) : ℝ :=
  ((2 * (L : ℝ) + 1) * ((L : ℝ) * ((L : ℝ) + 1) * (1 - 2 * τ) - (M : ℝ) * σ) * a -
      ((L : ℝ) + 1) * Rk M σ L * (1 - (L : ℝ) ^ 2 * t) * b) /
    ((L : ℝ) * Rk M σ (L + 1))

/-- **`P̃_{L₀+k}(τ; t)` of `lem:sqrtfreecarrier`** (`τ = (1-x)/2`, `t = h²`), defined by the
square-root-free rank recurrence `eq:3jrankpoly` with the starts described in the module
docstring. -/
noncomputable def ptilde3 (M σ : ℚ) : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => seed3 M σ
  | 1, τ, t =>
      if max |M| |σ| = 0 then 1 - 2 * τ else step3 M σ (max |M| |σ|) τ t (seed3 M σ) 0
  | k + 2, τ, t =>
      step3 M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ)) τ t (ptilde3 M σ (k + 1) τ t)
        (ptilde3 M σ k τ t)

lemma ptilde3_zero (M σ : ℚ) (τ t : ℝ) : ptilde3 M σ 0 τ t = seed3 M σ := rfl

lemma ptilde3_one_of_ne (M σ : ℚ) (τ t : ℝ) (h : max |M| |σ| ≠ 0) :
    ptilde3 M σ 1 τ t = step3 M σ (max |M| |σ|) τ t (seed3 M σ) 0 := by
  simp [ptilde3, h]

lemma ptilde3_one_of_eq (M σ : ℚ) (τ t : ℝ) (h : max |M| |σ| = 0) :
    ptilde3 M σ 1 τ t = 1 - 2 * τ := by
  simp [ptilde3, h]

lemma ptilde3_succ_succ (M σ : ℚ) (k : ℕ) (τ t : ℝ) :
    ptilde3 M σ (k + 2) τ t =
      step3 M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ)) τ t (ptilde3 M σ (k + 1) τ t)
        (ptilde3 M σ k τ t) := rfl

/-! ### `Ct` at `t = 0` -/

/-- At zero scale the central product is the power: `𝔠_r(u,0) = u^r`. -/
theorem Ct_zero_t (r : ℕ) (u : ℝ) : Ct r u 0 = u ^ r := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ => simp [Ct_zero]
    | 1, _ => simp [Ct_one]
    | r + 2, ih =>
      rw [Ct_succ_succ, ih r (by omega)]
      ring

/-! ### Polynomiality -/

/-- Evaluation `Polynomial (Polynomial ℝ) → ℝ`, `P ↦ P(τ; t)`: the outer variable is `τ`, the inner
(coefficient) variable is `t`. -/
noncomputable def evP (τ t : ℝ) : Polynomial (Polynomial ℝ) →+* ℝ :=
  (Polynomial.evalRingHom τ).comp (Polynomial.mapRingHom (Polynomial.evalRingHom t))

/-- `P(τ; t)` for `P : Polynomial (Polynomial ℝ)`. -/
noncomputable def evalP (P : Polynomial (Polynomial ℝ)) (τ t : ℝ) : ℝ := evP τ t P

@[simp] lemma evalP_C_C (r τ t : ℝ) : evalP (C (C r)) τ t = r := by simp [evalP, evP]
@[simp] lemma evalP_X (τ t : ℝ) : evalP X τ t = τ := by simp [evalP, evP]
@[simp] lemma evalP_C_X (τ t : ℝ) : evalP (C X) τ t = t := by simp [evalP, evP]
@[simp] lemma evalP_add (P Q : Polynomial (Polynomial ℝ)) (τ t : ℝ) :
    evalP (P + Q) τ t = evalP P τ t + evalP Q τ t := map_add _ _ _
@[simp] lemma evalP_sub (P Q : Polynomial (Polynomial ℝ)) (τ t : ℝ) :
    evalP (P - Q) τ t = evalP P τ t - evalP Q τ t := map_sub _ _ _
@[simp] lemma evalP_mul (P Q : Polynomial (Polynomial ℝ)) (τ t : ℝ) :
    evalP (P * Q) τ t = evalP P τ t * evalP Q τ t := map_mul _ _ _
@[simp] lemma evalP_one (τ t : ℝ) : evalP 1 τ t = 1 := map_one _
@[simp] lemma evalP_zero (τ t : ℝ) : evalP 0 τ t = 0 := map_zero _

/-- The polynomial form of `step3` in `Polynomial (Polynomial ℝ)`. -/
noncomputable def step3P (M σ L : ℚ) (a b : Polynomial (Polynomial ℝ)) :
    Polynomial (Polynomial ℝ) :=
  C (C (1 / ((L : ℝ) * Rk M σ (L + 1)))) *
    (C (C (2 * (L : ℝ) + 1)) *
        (C (C ((L : ℝ) * ((L : ℝ) + 1))) * (1 - C (C 2) * X) - C (C ((M : ℝ) * σ))) * a -
      C (C (((L : ℝ) + 1) * Rk M σ L)) * (1 - C (C ((L : ℝ) ^ 2) * X)) * b)

@[simp] lemma evalP_pow (P : Polynomial (Polynomial ℝ)) (n : ℕ) (τ t : ℝ) :
    evalP (P ^ n) τ t = evalP P τ t ^ n := map_pow _ _ _

lemma evalP_step3P (M σ L : ℚ) (a b : Polynomial (Polynomial ℝ)) (τ t : ℝ) :
    evalP (step3P M σ L a b) τ t = step3 M σ L τ t (evalP a τ t) (evalP b τ t) := by
  unfold step3P step3
  simp
  ring

/-- The polynomial family `P̃_{L₀+k}` in `Polynomial (Polynomial ℝ)` (outer variable `τ`,
inner variable `t`). -/
noncomputable def ptilde3Poly (M σ : ℚ) : ℕ → Polynomial (Polynomial ℝ)
  | 0 => C (C (seed3 M σ))
  | 1 =>
      if max |M| |σ| = 0 then 1 - C (C 2) * X
      else step3P M σ (max |M| |σ|) (C (C (seed3 M σ))) 0
  | k + 2 =>
      step3P M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ)) (ptilde3Poly M σ (k + 1)) (ptilde3Poly M σ k)

/-- `ptilde3` is the evaluation of the polynomial family `ptilde3Poly`. -/
theorem ptilde3_eq_evalP (M σ : ℚ) (k : ℕ) (τ t : ℝ) :
    ptilde3 M σ k τ t = evalP (ptilde3Poly M σ k) τ t := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [ptilde3, ptilde3Poly]
    | 1, _ =>
      by_cases h : max |M| |σ| = 0
      · simp [ptilde3, ptilde3Poly, h]
      · simp only [ptilde3, ptilde3Poly, h, ite_false]
        rw [evalP_step3P]
        simp
    | k + 2, ih =>
      rw [ptilde3_succ_succ, ptilde3Poly, evalP_step3P, ih (k + 1) (by omega), ih k (by omega)]

lemma natDegree_step3P_le (M σ L : ℚ) (a b : Polynomial (Polynomial ℝ)) (n : ℕ)
    (ha : a.natDegree ≤ n) (hb : b.natDegree ≤ n + 1) :
    (step3P M σ L a b).natDegree ≤ n + 1 := by
  unfold step3P
  have hX : (C (C 2) * X : Polynomial (Polynomial ℝ)).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans natDegree_X_le
  have h1X : ((1 : Polynomial (Polynomial ℝ)) - C (C 2) * X).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (max_le (by simp) hX)
  have hY : ((C (C ((L : ℝ) * ((L : ℝ) + 1))) * (1 - C (C 2) * X) -
      C (C ((M : ℝ) * σ))) : Polynomial (Polynomial ℝ)).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans h1X)
      (by rw [natDegree_C]; omega))
  have hZ : ((1 : Polynomial (Polynomial ℝ)) - C (C ((L : ℝ) ^ 2) * X)).natDegree ≤ 0 :=
    (natDegree_sub_le _ _).trans (max_le (by simp) (by rw [natDegree_C]))
  have h1 : ((C (C (2 * (L : ℝ) + 1)) *
        (C (C ((L : ℝ) * ((L : ℝ) + 1))) * (1 - C (C 2) * X) - C (C ((M : ℝ) * σ))) * a :
        Polynomial (Polynomial ℝ))).natDegree ≤ n + 1 := by
    have e1 := natDegree_mul_le (p := (C (C (2 * (L : ℝ) + 1)) : Polynomial (Polynomial ℝ)) *
      (C (C ((L : ℝ) * ((L : ℝ) + 1))) * (1 - C (C 2) * X) - C (C ((M : ℝ) * σ)))) (q := a)
    have e2 := natDegree_C_mul_le (C (2 * (L : ℝ) + 1) : Polynomial ℝ)
      (C (C ((L : ℝ) * ((L : ℝ) + 1))) * (1 - C (C 2) * X) - C (C ((M : ℝ) * σ)))
    omega
  have h2 : ((C (C (((L : ℝ) + 1) * Rk M σ L)) * (1 - C (C ((L : ℝ) ^ 2) * X)) * b :
      Polynomial (Polynomial ℝ))).natDegree ≤ n + 1 := by
    have e1 := natDegree_mul_le (p := (C (C (((L : ℝ) + 1) * Rk M σ L)) : Polynomial (Polynomial ℝ)) *
      (1 - C (C ((L : ℝ) ^ 2) * X))) (q := b)
    have e2 := natDegree_C_mul_le (C (((L : ℝ) + 1) * Rk M σ L) : Polynomial ℝ)
      (1 - C (C ((L : ℝ) ^ 2) * X))
    omega
  exact (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans (max_le h1 h2))

/-- **Polynomiality** (`lem:sqrtfreecarrier`): `P̃_{L₀+k}` has degree `≤ k` in `τ`, and its
coefficients are polynomials in `t`. -/
theorem natDegree_ptilde3Poly_le (M σ : ℚ) (k : ℕ) : (ptilde3Poly M σ k).natDegree ≤ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [ptilde3Poly]
    | 1, _ =>
      by_cases h : max |M| |σ| = 0
      · simp only [ptilde3Poly, h, ite_true]
        refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
        refine natDegree_mul_le.trans ?_
        simp
      · simp only [ptilde3Poly, h, ite_false]
        exact natDegree_step3P_le _ _ _ _ _ 0 (by simp) (by simp)
    | k + 2, ih =>
      rw [ptilde3Poly]
      exact natDegree_step3P_le _ _ _ _ _ (k + 1) (ih (k + 1) (by omega))
        ((ih k (by omega)).trans (by omega))

/-- **`lem:sqrtfreecarrier` polynomiality, in the form `∃ P`**: for every `k` there is
`P : Polynomial (Polynomial ℝ)` of `τ`-degree `≤ k` (coefficients polynomials in `t`) with
`P̃_{L₀+k}(τ;t) = P(τ;t)` for all `τ, t`. -/
theorem ptilde3_polynomial (M σ : ℚ) (k : ℕ) :
    ∃ P : Polynomial (Polynomial ℝ), P.natDegree ≤ k ∧
      ∀ τ t : ℝ, ptilde3 M σ k τ t = evalP P τ t :=
  ⟨ptilde3Poly M σ k, natDegree_ptilde3Poly_le M σ k, fun τ t => ptilde3_eq_evalP M σ k τ t⟩

/-- info: 'FormalResearch.Racah.ptilde3_eq_evalP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ptilde3_eq_evalP

/-- info: 'FormalResearch.Racah.ptilde3_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ptilde3_polynomial

/-- info: 'FormalResearch.Racah.Ct_zero_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ct_zero_t

end FormalResearch.Racah
