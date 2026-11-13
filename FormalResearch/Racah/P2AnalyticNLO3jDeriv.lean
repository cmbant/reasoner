module

public import FormalResearch.Racah.P2AnalyticBulk3j

/-!
# Next-to-leading squeezed `3j` formula: the `t`-derivative of the carrier (Weyl P2, `thm:3jNLO`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `thm:3jNLO` (proof: seed derivative
`eq:3jf2seednorm` and the `t`-derivative of the rank recurrence `eq:3jrank`).

For `x ∈ (-1,1)`, `τ = (1-x)/2`, `τ' = (1+x)/2`, `α = p_+`, `β = p_-`, `n = α+β+2k+1 = 2L+1`:

* `hasDerivAt_Ct`: `∂_t 𝔠_r(u; t)|_{t=0} = -c_r u^{r-2}`, `c_r = r(r²-1)/24`.
* `qt3 M σ k τ = ∂_t P̃_{L₀+k}(τ;t)|_{t=0}`; `qt3_zero`, `qt3_one` (both `0`: the seed and the
  second start do not depend on `t`), `qt3_rank` (the rank recurrence differentiated in `t`).
* `f3even_one_eq`: `f_2 = ∂_t G(x,t)|_{t=0} = (c_n/2 - μ) d + √(τ^α τ'^β) · qt3`, with
  `μ = (c_α/τ² + c_β/τ'²)/2` and `d = dZero3 M σ k x` (the seed derivative, `eq:3jf2seednorm`).
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner Set

/-- `c_r = r(r²-1)/24`: `𝔠_r(u;t) = u^r - c_r u^{r-2} t + O(t²)`. -/
noncomputable def cc (r : ℕ) : ℝ := (r : ℝ) * ((r : ℝ) ^ 2 - 1) / 24

lemma cc_add_two (r : ℕ) : cc (r + 2) = cc r + ((r : ℝ) + 1) ^ 2 / 4 := by
  unfold cc; push_cast; ring

/-- **`∂_t 𝔠_r(u;t)` at `t = 0`**: `-c_r u^r / u²`. -/
lemma hasDerivAt_Ct (r : ℕ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun t => Ct r u t) (-(cc r) * u ^ r / u ^ 2) 0 := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ =>
      have : (fun t => Ct 0 u t) = fun _ => (1 : ℝ) := by funext t; rfl
      rw [this]; simpa [cc] using hasDerivAt_const (0 : ℝ) (1 : ℝ)
    | 1, _ =>
      have : (fun t => Ct 1 u t) = fun _ => u := by funext t; rfl
      rw [this]; simpa [cc] using hasDerivAt_const (0 : ℝ) u
    | r + 2, ih =>
      have h0 := ih r (by omega)
      have h1 : HasDerivAt (fun t : ℝ => u ^ 2 - ((r : ℝ) + 1) ^ 2 / 4 * t)
          (-(((r : ℝ) + 1) ^ 2 / 4)) 0 := by
        have := ((hasDerivAt_id (0 : ℝ)).const_mul (((r : ℝ) + 1) ^ 2 / 4)).const_sub (u ^ 2)
        simpa using this
      have h2 := h1.mul h0
      have e : (fun t => Ct (r + 2) u t) =
          (fun t : ℝ => u ^ 2 - ((r : ℝ) + 1) ^ 2 / 4 * t) * fun t => Ct r u t := by
        funext t; rfl
      rw [e]
      refine h2.congr_deriv ?_
      rw [Ct_zero_t, cc_add_two]
      simp only [mul_zero, sub_zero]
      field_simp
      ring

/-! ### `t`-derivative of the carrier polynomials -/

lemma differentiableAt_ptilde3_t (M σ : ℚ) (k : ℕ) (τ : ℝ) :
    DifferentiableAt ℝ (fun t => ptilde3 M σ k τ t) 0 := by
  have h := (analyticAt_ptilde3 M σ k (τ, 0)).differentiableAt.comp (0 : ℝ)
    ((differentiableAt_const τ).prodMk differentiableAt_id)
  exact h

/-- `q_k(τ) = ∂_t P̃_{L₀+k}(τ;t)|_{t=0}`. -/
noncomputable def qt3 (M σ : ℚ) (k : ℕ) (τ : ℝ) : ℝ := deriv (fun t => ptilde3 M σ k τ t) 0

lemma hasDerivAt_ptilde3_t (M σ : ℚ) (k : ℕ) (τ : ℝ) :
    HasDerivAt (fun t => ptilde3 M σ k τ t) (qt3 M σ k τ) 0 :=
  (differentiableAt_ptilde3_t M σ k τ).hasDerivAt

/-- The extremal start does not depend on `t`. -/
lemma qt3_zero (M σ : ℚ) (τ : ℝ) : qt3 M σ 0 τ = 0 := by
  unfold qt3
  have : (fun t => ptilde3 M σ 0 τ t) = fun _ => seed3 M σ := by funext t; rfl
  rw [this]; simp

/-- The second start does not depend on `t` (`b = 0` in the first `step3`). -/
lemma qt3_one (M σ : ℚ) (τ : ℝ) : qt3 M σ 1 τ = 0 := by
  unfold qt3
  have : (fun t => ptilde3 M σ 1 τ t) = fun _ => ptilde3 M σ 1 τ 0 := by
    funext t
    by_cases h : max |M| |σ| = 0
    · rw [ptilde3_one_of_eq _ _ _ _ h, ptilde3_one_of_eq _ _ _ _ h]
    · rw [ptilde3_one_of_ne _ _ _ _ h, ptilde3_one_of_ne _ _ _ _ h]
      simp [step3]
  rw [this]; simp

/-- **The rank recurrence `eq:3jrankpoly` differentiated in `t` at `t = 0`**, rows
`L = L₀ + k + 1`:
`(2L+1)[L(L+1)(1-2τ) - Mσ] q_{k+1} = (L+1) R_L (q_k - L² P̃_k(τ;0)) + L R_{L+1} q_{k+2}`. -/
theorem qt3_rank (M σ : ℚ) (k : ℕ) (τ : ℝ) :
    (2 * ((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) + 1) *
        (((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) *
            (((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) + 1) * (1 - 2 * τ) - (M : ℝ) * σ) *
          qt3 M σ (k + 1) τ =
      (((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) + 1) *
          Rk M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ)) *
          (qt3 M σ k τ - (((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ)) ^ 2 * ptilde3 M σ k τ 0) +
        (((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ)) *
          Rk M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ) + 1) * qt3 M σ (k + 2) τ := by
  set L : ℝ := (((max |M| |σ| + ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ)) with hL
  set R1 : ℝ := Rk M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ)) with hR1
  set R2 : ℝ := Rk M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ) + 1) with hR2
  have hfun : (fun t => (2 * L + 1) * (L * (L + 1) * (1 - 2 * τ) - (M : ℝ) * σ) *
        ptilde3 M σ (k + 1) τ t) =
      fun t => (L + 1) * R1 * (1 - L ^ 2 * t) * ptilde3 M σ k τ t +
        L * R2 * ptilde3 M σ (k + 2) τ t := by
    funext t
    exact ptilde3_rank_poly M σ k τ t
  have hA := (hasDerivAt_ptilde3_t M σ (k + 1) τ).const_mul
    ((2 * L + 1) * (L * (L + 1) * (1 - 2 * τ) - (M : ℝ) * σ))
  have hB1 : HasDerivAt (fun t : ℝ => (L + 1) * R1 * (1 - L ^ 2 * t))
      ((L + 1) * R1 * (-L ^ 2)) 0 := by
    have := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub ((hasDerivAt_id (0 : ℝ)).const_mul (L ^ 2))).const_mul
      ((L + 1) * R1)
    simpa using this
  have hB := (hB1.mul (hasDerivAt_ptilde3_t M σ k τ)).add
    ((hasDerivAt_ptilde3_t M σ (k + 2) τ).const_mul (L * R2))
  rw [hfun] at hA
  have := hA.unique hB
  simp only [mul_zero, sub_zero, mul_one] at this
  linear_combination this

/-! ### `t`-derivative of the germ -/

/-- `μ = (c_α/τ² + c_β/τ'²)/2`, the `L`-independent part of the seed derivative. -/
noncomputable def nloMu (α β : ℕ) (x : ℝ) : ℝ :=
  (cc α / ((1 - x) / 2) ^ 2 + cc β / ((1 + x) / 2) ^ 2) / 2

/-- **The seed derivative** (`eq:3jf2seednorm`): for `x ∈ (-1,1)`,
`∂_t G(x,t)|_{t=0} = (c_n/2 - μ) · dZero3 + √(τ^α τ'^β) · q_k(τ)`, `n = α+β+2k+1`. -/
theorem hasDerivAt_Gc3_t (M σ : ℚ) (k : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => Gc3 M σ k x t)
      ((cc (pPlus3 M σ + pMinus3 M σ + 2 * k + 1) / 2 - nloMu (pPlus3 M σ) (pMinus3 M σ) x) *
          dZero3 M σ k x +
        Real.sqrt (((1 - x) / 2) ^ pPlus3 M σ * ((1 + x) / 2) ^ pMinus3 M σ) *
          qt3 M σ k ((1 - x) / 2)) 0 := by
  have hτ : 0 < (1 - x) / 2 := by linarith [hx.2]
  have hτ' : 0 < (1 + x) / 2 := by linarith [hx.1]
  set a := pPlus3 M σ
  set b := pMinus3 M σ
  set u : ℝ := (1 - x) / 2 with hu
  set v : ℝ := (1 + x) / 2 with hv
  set n := a + b + 2 * k + 1
  have hP0 : 0 < u ^ a * v ^ b := by positivity
  have hP := (hasDerivAt_Ct a hτ.ne').mul (hasDerivAt_Ct b hτ'.ne')
  have hT := hasDerivAt_Ct n (one_ne_zero (α := ℝ))
  have hsP := hP.sqrt (by
    show Ct a u 0 * Ct b v 0 ≠ 0
    rw [Ct_zero_t, Ct_zero_t]; exact hP0.ne')
  have hsT := hT.sqrt (by show Ct n 1 0 ≠ 0; simp [Ct_zero_t])
  have hdiv := hsP.div hsT (by show Real.sqrt (Ct n 1 0) ≠ 0; simp [Ct_zero_t])
  have hfin := hdiv.mul (hasDerivAt_ptilde3_t M σ k u)
  unfold Gc3
  refine hfin.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.div_apply, Ct_zero_t, one_pow, Real.sqrt_one, div_one]
  unfold dZero3 nloMu
  rw [← hu, ← hv]
  have hs : 0 < Real.sqrt (u ^ a * v ^ b) := Real.sqrt_pos.mpr hP0
  have hs2 : Real.sqrt (u ^ a * v ^ b) ^ 2 = u ^ a * v ^ b := Real.sq_sqrt hP0.le
  rw [qt3]
  generalize Real.sqrt (u ^ a * v ^ b) = s at *
  generalize ptilde3 M σ k u 0 = p
  generalize deriv (fun t => ptilde3 M σ k u t) 0 = q
  have hu0 : u ≠ 0 := hτ.ne'
  have hv0 : v ≠ 0 := hτ'.ne'
  have hsP : u ^ a * v ^ b = s ^ 2 := hs2.symm
  field_simp
  rw [hsP]
  ring

/-- **`f_2` through the seed derivative and `q_k`**: for `x ∈ (-1,1)`,
`f_2 = (c_n/2 - μ) · dZero3 + √(τ^α τ'^β) · q_k(τ)`. -/
theorem f3even_one_eq (M σ : ℚ) (k : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    f3even M σ k 1 x =
      (cc (pPlus3 M σ + pMinus3 M σ + 2 * k + 1) / 2 - nloMu (pPlus3 M σ) (pMinus3 M σ) x) *
          dZero3 M σ k x +
        Real.sqrt (((1 - x) / 2) ^ pPlus3 M σ * ((1 + x) / 2) ^ pMinus3 M σ) *
          qt3 M σ k ((1 - x) / 2) := by
  unfold f3even taylorCoeff
  rw [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, div_one]
  exact (hasDerivAt_Gc3_t M σ k hx).deriv

/-- info: 'FormalResearch.Racah.hasDerivAt_Ct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_Ct

/-- info: 'FormalResearch.Racah.qt3_rank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qt3_rank

/-- info: 'FormalResearch.Racah.hasDerivAt_Gc3_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_Gc3_t

/-- info: 'FormalResearch.Racah.f3even_one_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms f3even_one_eq

end FormalResearch.Racah
