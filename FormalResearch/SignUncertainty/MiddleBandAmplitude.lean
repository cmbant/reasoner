module

public import FormalResearch.SignUncertainty.MiddleBandNormalForm
public import FormalResearch.CohnElkies.OuterWeightedBound
public import FormalResearch.CohnElkies.PieceCUniform

/-!
# GT.2a `(e7)`: the amplitude `P(θ) = k_c(τ(θ)) τ'(θ)` against `e^{iθ/2}`

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `cegt:GT2a`, inner difference.

On the real axis put `k_c(x) = (1 - ix)^{-1/2} e^{B_c(ix)}` (`outerK`), `t(θ) = Re τ(θ)`, `P(θ) = k_c(t(θ)) t'(θ)` and
`q(θ) = P(θ) - e^{iθ/2}`.  Then for `|θ| ≤ 0.18`, `1/c ≤ L ≤ 0.002`:
`|q(θ)| ≤ M (L + θ²)`, `|q'(θ)| ≤ M (L + |θ|)`, `|q''(θ)| ≤ M`.

* `outerK_zero`, `outerK_deriv_zero`: `k_c(0) = 1` and `|k_c'(0) - i/2| ≤ 1/(12c)`.
* `amp_q_bounds`: the three bounds above, with an absolute constant `M`.
* `innerDiff_local`: `(e8)` at one point for an arbitrary local symbol size `ρ`; `innerDiff_bounds`: `(e8)`, `|𝒟^{(r)}(u)| ≤ C (L + ε²u²) |u|^{-5/2-r}` (`r ≤ 2`, `|u| ≥ 1`, `ε|u| ≤ 0.18`) for `𝒟(u) = P(u) W̃(w₁(u)) - e^{iεu/2} W̃(u)`,
  from `symbol_diff_local` and the bounds above; `C` depends only on the symbol constant.

Status: proved, unconditional given `O4NormalForm L τ` (itself conditional on `O4QuotientBound L`).  Not formalised here: the change of
variables `τ = τ(εu)` in `I_main` and the region estimates (`G4`-`G8`).
-/

@[expose] public section

open Metric Set Filter Topology Complex Function
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Asymptotics

lemma outerK_zero (c : ℝ) : outerK c 0 = 1 := by
  simp [outerK, binetDiff]

/-- `k_c'(0) = i/2 + i B_c'(0)`, hence `|k_c'(0) - i/2| ≤ 1/(12c)`. -/
lemma outerK_deriv_zero {c : ℝ} (hc : 0 < c) : ‖deriv (outerK c) 0 - Complex.I / 2‖ ≤ 1 / (12 * c) := by
  have hBd : DifferentiableAt ℂ (binetDiff c) (Complex.I * (0 : ℂ)) := by
    refine (binetDiff_differentiableOn hc).differentiableAt (isOpen_lt Complex.continuous_re continuous_const |>.mem_nhds ?_)
    simp
  set b' : ℂ := deriv (binetDiff c) (Complex.I * (0 : ℂ)) with hb'
  have hA : HasDerivAt (fun z : ℂ => (1 - Complex.I * z) ^ (-((1 / 2 : ℝ) : ℂ))) (Complex.I / 2) 0 := by
    have hf : HasDerivAt (fun z : ℂ => 1 - Complex.I * z) (-Complex.I) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul Complex.I).const_sub (1 : ℂ)
    have := hf.cpow_const (c := -((1 / 2 : ℝ) : ℂ)) (by simp)
    convert this using 1
    simp
    ring
  have hB : HasDerivAt (fun z : ℂ => binetDiff c (Complex.I * z)) (b' * Complex.I) 0 := by
    have := hBd.hasDerivAt.comp (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).const_mul Complex.I)
    convert this using 1
    · rfl
    · rw [hb']; ring
  have hK := hA.mul (hB.cexp)
  have hK' : HasDerivAt (outerK c) (Complex.I / 2 + b' * Complex.I) 0 := by
    have := hK.comp_ofReal (z := (0 : ℝ))
    refine (this.congr_deriv ?_).congr_of_eventuallyEq ?_ |>.congr_deriv rfl
    · simp [binetDiff]
    · exact Filter.Eventually.of_forall fun x => by simp [outerK]
  rw [hK'.deriv]
  have h1 : ‖b'‖ ≤ 1 / (12 * c) := by
    have := binetDiff_iteratedDeriv_norm_le hc (ζ := Complex.I * 0) (by simp) (r := 1) le_rfl
    simpa [hb', iteratedDeriv_one] using this
  calc ‖Complex.I / 2 + b' * Complex.I - Complex.I / 2‖ = ‖b'‖ := by
        rw [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one]
    _ ≤ _ := h1

section

variable {L : ℝ} {τ : ℂ → ℂ}

/-- The real part `t(θ) = Re τ(θ)` and its first three derivatives along the real axis. -/
noncomputable def trF (τ : ℂ → ℂ) (n : ℕ) (θ : ℝ) : ℝ := (iteratedDeriv n τ (θ : ℂ)).re

lemma trF_hasDerivAt (h : O4NormalForm L τ) (n : ℕ) {θ : ℝ} (hθ : |θ| < 0.22) :
    HasDerivAt (trF τ n) (trF τ (n + 1) θ) θ := by
  have hd : DifferentiableOn ℂ (iteratedDeriv n τ) (ball 0 0.22) := by
    induction n with
    | zero => simpa using h.differentiableOn
    | succ k ih =>
      have := differentiableOn_deriv_ball ih
      simpa [iteratedDeriv_succ] using this
  have hm : (θ : ℂ) ∈ ball (0 : ℂ) 0.22 := by simpa [Complex.norm_real] using hθ
  have := ((hd.differentiableAt (isOpen_ball.mem_nhds hm)).hasDerivAt).real_of_complex
  show HasDerivAt (fun x : ℝ => (iteratedDeriv n τ (x : ℂ)).re) ((iteratedDeriv (n + 1) τ (θ : ℂ)).re) θ
  rw [iteratedDeriv_succ]
  exact this

lemma trF_one_eq : ∀ θ : ℝ, trF τ 1 θ = (deriv τ (θ : ℂ)).re := fun θ => by
  simp [trF, iteratedDeriv_one]

end

section

variable {L : ℝ} {τ : ℂ → ℂ}

/-- `q(θ) = k_c(t(θ)) t'(θ) - e^{iθ/2}`. -/
noncomputable def ampQ0 (c : ℝ) (τ : ℂ → ℂ) (θ : ℝ) : ℂ :=
  outerK c (trF τ 0 θ) * (trF τ 1 θ : ℂ) - Complex.exp (Complex.I * (θ : ℂ) / 2)

/-- `q'(θ)`. -/
noncomputable def ampQ1 (c : ℝ) (τ : ℂ → ℂ) (θ : ℝ) : ℂ :=
  (deriv (outerK c) (trF τ 0 θ) * (trF τ 1 θ : ℂ) ^ 2 + outerK c (trF τ 0 θ) * (trF τ 2 θ : ℂ)) -
    (Complex.I / 2) * Complex.exp (Complex.I * (θ : ℂ) / 2)

/-- `q''(θ)`. -/
noncomputable def ampQ2 (c : ℝ) (τ : ℂ → ℂ) (θ : ℝ) : ℂ :=
  (deriv (deriv (outerK c)) (trF τ 0 θ) * (trF τ 1 θ : ℂ) ^ 3 +
      3 * deriv (outerK c) (trF τ 0 θ) * (trF τ 1 θ : ℂ) * (trF τ 2 θ : ℂ) +
      outerK c (trF τ 0 θ) * (trF τ 3 θ : ℂ)) + (1 / 4) * Complex.exp (Complex.I * (θ : ℂ) / 2)

lemma hasDerivAt_expHalf (θ : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (Complex.I * (y : ℂ) / 2)) ((Complex.I / 2) * Complex.exp (Complex.I * (θ : ℂ) / 2)) θ := by
  have h1 : HasDerivAt (fun z : ℂ => Complex.exp (Complex.I * z / 2)) ((Complex.I / 2) * Complex.exp (Complex.I * (θ : ℂ) / 2)) (θ : ℂ) := by
    have := ((hasDerivAt_id' (θ : ℂ)).const_mul Complex.I).div_const 2 |>.cexp
    convert this using 1
    ring
  exact h1.comp_ofReal

lemma ampQ_hasDerivAt (h : O4NormalForm L τ) {c : ℝ} (hc : 2 ≤ c) {θ : ℝ} (hθ : |θ| < 0.22) :
    HasDerivAt (ampQ0 c τ) (ampQ1 c τ θ) θ ∧ HasDerivAt (ampQ1 c τ) (ampQ2 c τ θ) θ := by
  obtain ⟨CK, hCK, hKb⟩ := outerK_bounds
  have hk := (hKb hc).1
  have hk1 : ∀ x : ℝ, HasDerivAt (outerK c) (deriv (outerK c) x) x := fun x => (hk.differentiable (by norm_num) x).hasDerivAt
  have hk2 : ∀ x : ℝ, HasDerivAt (deriv (outerK c)) (deriv (deriv (outerK c)) x) x := by
    have hd : Differentiable ℝ (iteratedDeriv 1 (outerK c)) := hk.differentiable_iteratedDeriv 1 (by norm_num)
    rw [iteratedDeriv_one] at hd
    exact fun x => (hd x).hasDerivAt
  have t0 := trF_hasDerivAt h 0 hθ
  have t1 := trF_hasDerivAt h 1 hθ
  have t2 := trF_hasDerivAt h 2 hθ
  have c0 : HasDerivAt (fun y => outerK c (trF τ 0 y)) (↑(trF τ 1 θ) * deriv (outerK c) (trF τ 0 θ)) θ := by
    have := (hk1 (trF τ 0 θ)).scomp θ t0
    exact this.congr_deriv (by simp [Complex.real_smul])
  have c1 : HasDerivAt (fun y => deriv (outerK c) (trF τ 0 y)) (↑(trF τ 1 θ) * deriv (deriv (outerK c)) (trF τ 0 θ)) θ := by
    have := (hk2 (trF τ 0 θ)).scomp θ t0
    exact this.congr_deriv (by simp [Complex.real_smul])
  have r1 : HasDerivAt (fun y => ((trF τ 1 y : ℝ) : ℂ)) ((trF τ 2 θ : ℝ) : ℂ) θ := t1.ofReal_comp
  have r2 : HasDerivAt (fun y => ((trF τ 2 y : ℝ) : ℂ)) ((trF τ 3 θ : ℝ) : ℂ) θ := t2.ofReal_comp
  have e0 := hasDerivAt_expHalf θ
  have e1 : HasDerivAt (fun y : ℝ => (Complex.I / 2) * Complex.exp (Complex.I * (y : ℂ) / 2))
      ((Complex.I / 2) * ((Complex.I / 2) * Complex.exp (Complex.I * (θ : ℂ) / 2))) θ := e0.const_mul _
  have r2' : HasDerivAt (fun y => ((trF τ 2 y : ℝ) : ℂ)) ((trF τ 3 θ : ℝ) : ℂ) θ := r2
  constructor
  · exact ((c0.mul r1).sub e0).congr_deriv (by simp only [ampQ1]; ring)
  · have hp := (c1.mul (r1.pow 2)).add (c0.mul r2')
    refine (hp.sub e1).congr_deriv ?_
    simp only [ampQ2, Pi.pow_apply]
    push_cast
    linear_combination (-(1 / 4 : ℂ)) * Complex.exp (Complex.I * (θ : ℂ) / 2) * (Complex.I_sq + 1 - 1)


/-- **`(e7)` in the variable `θ`**: for `|θ| ≤ 0.18`, `1/c ≤ L ≤ 0.002`, `c ≥ 2`,
`|q| ≤ M(L + θ²)`, `|q'| ≤ M(L + |θ|)`, `|q''| ≤ M`, with `M` depending only on the constant of `outerK_bounds`. -/
theorem amp_q_bounds : ∃ M : ℝ, 1 ≤ M ∧ ∀ {L : ℝ} {τ : ℂ → ℂ}, O4NormalForm L τ → 0 < L → L ≤ 0.002 →
    ∀ {c : ℝ}, 2 ≤ c → 1 / c ≤ L → ∀ {θ : ℝ}, |θ| ≤ 0.18 →
    ‖ampQ0 c τ θ‖ ≤ M * (L + θ ^ 2) ∧ ‖ampQ1 c τ θ‖ ≤ M * (L + |θ|) ∧ ‖ampQ2 c τ θ‖ ≤ M := by
  obtain ⟨CK, hCK, hKb⟩ := outerK_bounds
  refine ⟨(CK + 1) * 10 ^ 10, by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 10) 10], ?_⟩
  intro L τ h hL0 hL2 c hc hcL θ hθ
  set M : ℝ := (CK + 1) * 10 ^ 10 with hM
  have hM1 : 1 ≤ M := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 10) 10]
  have hc0 : 0 < c := by linarith
  obtain ⟨hk, hkb⟩ := hKb hc
  have hkb0 : ∀ x : ℝ, ‖outerK c x‖ ≤ CK := fun x => by
    have := hkb 0 (by norm_num) x
    simp only [iteratedDeriv_zero] at this
    refine this.trans ?_
    have : (1 + x ^ 2) ^ (-(1 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg x]) (by norm_num)
    nlinarith
  have hkb1 : ∀ x : ℝ, ‖deriv (outerK c) x‖ ≤ CK := fun x => by
    have := hkb 1 (by norm_num) x
    simp only [iteratedDeriv_one] at this
    refine this.trans ?_
    have : (1 + x ^ 2) ^ (-(1 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg x]) (by norm_num)
    nlinarith
  have hkb2 : ∀ x : ℝ, ‖deriv (deriv (outerK c)) x‖ ≤ CK := fun x => by
    have := hkb 2 (by norm_num) x
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    refine this.trans ?_
    have : (1 + x ^ 2) ^ (-(1 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg x]) (by norm_num)
    nlinarith
  have hκ := edgeKappa0_bounds hL0 hL2
  have hκ1 : edgeKappa0 L ≤ 1.0005 := by linarith [hκ.2]
  -- bounds on `t', t'', t'''`
  have T : ∀ x : ℝ, |x| ≤ 0.18 → |trF τ 1 x| ≤ 2000 ∧ |trF τ 2 x| ≤ 9000 ∧ |trF τ 3 x| ≤ 50000 := by
    intro x hx
    obtain ⟨-, t1, t2⟩ := tau_taylor_bounds h hx
    have t3 := tau_third_deriv_bound h x hx
    have hx2 : x ^ 2 ≤ 0.0324 := by nlinarith [sq_abs x, abs_nonneg x]
    refine ⟨?_, ?_, ?_⟩
    · have e1 : |trF τ 1 x - edgeKappa0 L| ≤ 50000 * x ^ 2 := by
        have := Complex.abs_re_le_norm (deriv τ (x : ℂ) - (edgeKappa0 L : ℂ))
        simp only [Complex.sub_re, Complex.ofReal_re] at this
        rw [trF_one_eq]; exact this.trans t1
      have := abs_le.mp e1
      rw [abs_le]; constructor <;> nlinarith [hκ.1]
    · have := (Complex.abs_re_le_norm (deriv (deriv τ) (x : ℂ)))
      have e : trF τ 2 x = (deriv (deriv τ) (x : ℂ)).re := by simp [trF, iteratedDeriv_succ]
      rw [e]; refine this.trans (t2.trans ?_); nlinarith [abs_nonneg x]
    · have := (Complex.abs_re_le_norm (deriv (deriv (deriv τ)) (x : ℂ)))
      have e : trF τ 3 x = (deriv (deriv (deriv τ)) (x : ℂ)).re := by simp [trF, iteratedDeriv_succ]
      rw [e]; exact this.trans t3
  -- the second derivative bound
  have hQ2 : ∀ x : ℝ, |x| ≤ 0.18 → ‖ampQ2 c τ x‖ ≤ M := by
    intro x hx
    obtain ⟨a1, a2, a3⟩ := T x hx
    have n1 : ‖(trF τ 1 x : ℂ)‖ ≤ 2000 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact a1
    have n2 : ‖(trF τ 2 x : ℂ)‖ ≤ 9000 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact a2
    have n3 : ‖(trF τ 3 x : ℂ)‖ ≤ 50000 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact a3
    have he : ‖Complex.exp (Complex.I * (x : ℂ) / 2)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    simp only [ampQ2]
    calc _ ≤ ‖deriv (deriv (outerK c)) (trF τ 0 x) * (trF τ 1 x : ℂ) ^ 3 +
          3 * deriv (outerK c) (trF τ 0 x) * (trF τ 1 x : ℂ) * (trF τ 2 x : ℂ) + outerK c (trF τ 0 x) * (trF τ 3 x : ℂ)‖ +
        ‖(1 / 4 : ℂ) * Complex.exp (Complex.I * (x : ℂ) / 2)‖ := norm_add_le _ _
      _ ≤ (CK * 2000 ^ 3 + 3 * CK * 2000 * 9000 + CK * 50000) + 1 / 4 := by
        refine add_le_add ?_ ?_
        · refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
          · rw [norm_mul, norm_pow]; gcongr; exact hkb2 _
          · rw [norm_mul, norm_mul, norm_mul]
            have : ‖(3 : ℂ)‖ = 3 := by simp
            rw [this]; gcongr; exact hkb1 _
          · rw [norm_mul]; gcongr; exact hkb0 _
        · rw [norm_mul, he]; norm_num
      _ ≤ M := by rw [hM]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 10) 10]
  -- values at the origin
  have hz1 : deriv τ 0 = (edgeKappa0 L : ℂ) := h.hasDerivAt_zero.deriv
  have hz2 : deriv (deriv τ) 0 = 0 := deriv_deriv_zero_of_odd (by norm_num) h.differentiableOn h.odd
  have t00 : trF τ 0 0 = 0 := by simp [trF, h.zero]
  have t10 : trF τ 1 0 = edgeKappa0 L := by simp [trF, hz1]
  have t20 : trF τ 2 0 = 0 := by simp [trF, iteratedDeriv_succ, hz2]
  have q00 : ampQ0 c τ 0 = ((edgeKappa0 L - 1 : ℝ) : ℂ) := by
    simp [ampQ0, t00, t10, outerK_zero]
  have q10 : ‖ampQ1 c τ 0‖ ≤ L := by
    have e : ampQ1 c τ 0 = (deriv (outerK c) 0 - Complex.I / 2) * ((edgeKappa0 L ^ 2 : ℝ) : ℂ) +
        (Complex.I / 2) * (((edgeKappa0 L ^ 2 - 1 : ℝ)) : ℂ) := by
      simp only [ampQ1, t00, t10, t20, outerK_zero]
      push_cast; simp; ring
    rw [e]
    have h1 := outerK_deriv_zero hc0
    have hk2 : 0 ≤ edgeKappa0 L ^ 2 := sq_nonneg _
    have hk3 : 0 ≤ edgeKappa0 L ^ 2 - 1 := by nlinarith [hκ.1]
    calc _ ≤ ‖(deriv (outerK c) 0 - Complex.I / 2) * ((edgeKappa0 L ^ 2 : ℝ) : ℂ)‖ +
          ‖(Complex.I / 2) * (((edgeKappa0 L ^ 2 - 1 : ℝ)) : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 / (12 * c) * edgeKappa0 L ^ 2 + (1 / 2) * (edgeKappa0 L ^ 2 - 1) := by
        refine add_le_add ?_ ?_
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk2]; gcongr
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk3]
          simp
      _ ≤ L := by
        have hc' : 1 / (12 * c) ≤ L / 12 := by
          rw [show 1 / (12 * c) = (1 / c) / 12 by field_simp]; exact div_le_div_of_nonneg_right hcL (by norm_num)
        have ha : edgeKappa0 L - 1 ≤ L / 4 := by linarith [hκ.2]
        have hb : edgeKappa0 L + 1 ≤ 2.0005 := by linarith
        have hkk : edgeKappa0 L ^ 2 - 1 ≤ L / 4 * 2.0005 := by
          have := mul_le_mul ha hb (by linarith) (by linarith)
          nlinarith
        have hk2' : edgeKappa0 L ^ 2 ≤ 1.0011 := by nlinarith [hκ.1, hκ.2]
        have hm := mul_le_mul hc' hk2' (by positivity) (by positivity)
        nlinarith
  have q00n : ‖ampQ0 c τ 0‖ ≤ L / 4 := by
    rw [q00, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hκ.1])]
    linarith [hκ.2]
  -- first derivative
  have hq1 : ∀ x : ℝ, |x| ≤ 0.18 → ‖ampQ1 c τ x‖ ≤ L + M * |x| := by
    intro x hx
    have hxs : ∀ s ∈ uIcc 0 x, |s| ≤ |x| := fun s hs => by
      rw [mem_uIcc] at hs
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
      · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith
    have := mvt_from_origin (f := ampQ1 c τ) (f' := ampQ2 c τ) (θ := x) (B := M)
      (fun s hs => (ampQ_hasDerivAt h hc (by have := hxs s hs; linarith)).2) (fun s hs => hQ2 s ((hxs s hs).trans hx))
    calc _ = ‖ampQ1 c τ 0 + (ampQ1 c τ x - ampQ1 c τ 0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖ampQ1 c τ 0‖ + ‖ampQ1 c τ x - ampQ1 c τ 0‖ := norm_add_le _ _
      _ ≤ L + M * |x| := add_le_add q10 this
  have hq0 : ∀ x : ℝ, |x| ≤ 0.18 → ‖ampQ0 c τ x‖ ≤ L / 4 + L * |x| + M * x ^ 2 := by
    intro x hx
    have hxs : ∀ s ∈ uIcc 0 x, |s| ≤ |x| := fun s hs => by
      rw [mem_uIcc] at hs
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
      · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith
    have := mvt_from_origin (f := fun y : ℝ => ampQ0 c τ y - ampQ1 c τ 0 * (y : ℂ))
      (f' := fun y => ampQ1 c τ y - ampQ1 c τ 0) (θ := x) (B := M * |x|)
      (fun s hs => by
        have h1 := (ampQ_hasDerivAt h hc (θ := s) (by have := hxs s hs; linarith)).1
        have h2 : HasDerivAt (fun y : ℝ => ampQ1 c τ 0 * (y : ℂ)) (ampQ1 c τ 0) s := by
          simpa using ((hasDerivAt_id' s).ofReal_comp).const_mul (ampQ1 c τ 0)
        exact h1.sub h2)
      (fun s hs => by
        have hsx := (hxs s hs)
        have := mvt_from_origin (f := ampQ1 c τ) (f' := ampQ2 c τ) (θ := s) (B := M)
          (fun r hr => by
            have hrs : |r| ≤ |s| := by
              rw [mem_uIcc] at hr
              rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
              · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith
            exact (ampQ_hasDerivAt h hc (by linarith)).2)
          (fun r hr => by
            have hrs : |r| ≤ |s| := by
              rw [mem_uIcc] at hr
              rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
              · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith
            exact hQ2 r (by linarith))
        calc _ ≤ M * |s| := this
          _ ≤ M * |x| := by gcongr)
    calc _ = ‖ampQ0 c τ 0 + ((ampQ0 c τ x - ampQ1 c τ 0 * (x : ℂ)) - (ampQ0 c τ 0 - ampQ1 c τ 0 * ((0 : ℝ) : ℂ))) +
          ampQ1 c τ 0 * (x : ℂ)‖ := by simp
      _ ≤ ‖ampQ0 c τ 0‖ + ‖(ampQ0 c τ x - ampQ1 c τ 0 * (x : ℂ)) - (ampQ0 c τ 0 - ampQ1 c τ 0 * ((0 : ℝ) : ℂ))‖ +
          ‖ampQ1 c τ 0 * (x : ℂ)‖ := norm_add₃_le
      _ ≤ L / 4 + M * |x| * |x| + L * |x| := by
        refine add_le_add (add_le_add q00n this) ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; gcongr
      _ = L / 4 + L * |x| + M * x ^ 2 := by rw [mul_assoc, abs_mul_abs_self]; ring
  refine ⟨?_, ?_, hQ2 θ hθ⟩
  · refine (hq0 θ hθ).trans ?_
    have : |θ| ≤ 1 := by linarith
    nlinarith [abs_nonneg θ, mul_le_mul_of_nonneg_left this hL0.le]
  · refine (hq1 θ hθ).trans ?_
    nlinarith [abs_nonneg θ]



/-- Chain rule for the dilation `s ↦ ε s`. -/
lemma hasDerivAt_dilate {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : ℝ → F} {g' : F} {ε x : ℝ}
    (h : HasDerivAt g g' (ε * x)) : HasDerivAt (fun s => g (ε * s)) (ε • g') x := by
  have := h.scomp x ((hasDerivAt_id' x).const_mul ε)
  exact this.congr_deriv (by simp)

/-- The inner difference `𝒟(u) = P(u) W̃(w₁(u)) - e^{iεu/2} W̃(u)` with `P(u) = k_c(t(εu)) t'(εu)`, `w₁(u) = t(εu)/ε`. -/
noncomputable def innerDiff (c ε : ℝ) (τ : ℂ → ℂ) (W : ℝ → ℂ) (u : ℝ) : ℂ :=
  outerK c (trF τ 0 (ε * u)) * (trF τ 1 (ε * u) : ℂ) * W (trF τ 0 (ε * u) / ε) -
    Complex.exp (Complex.I * ((ε * u : ℝ) : ℂ) / 2) * W u

set_option maxHeartbeats 1600000 in
/-- **`(e8)` at a point, local form.**  For `u ≠ 0` with `ε|u| ≤ 0.18` and a symbol `W` with `‖W^{(j)}(x)‖ ≤ A_W ρ |u|^{-j}` for `x`
between `|u|/2` and `|u| + |w(u)|` (`w(u) = t(εu)/ε`), the inner difference satisfies `‖𝒟^{(r)}(u)‖ ≤ C (L + ε²u²) ρ |u|^{-r}`
(`r ≤ 2`); `C` depends only on `A_W`.  Used with `ρ = |u|^{-5/2}` (`|u| ≥ 1`, `innerDiff_bounds`) and, for `W - W(0)`, `ρ = |u|^{1/2}`
(near zero). -/
theorem innerDiff_local (AW : ℝ) (hAW : 1 ≤ AW) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {L : ℝ} {τ : ℂ → ℂ}, O4NormalForm L τ → 0 < L → L ≤ 0.002 → ∀ {c ε : ℝ}, 2 ≤ c → 0 < ε → 1 / c ≤ L →
    ∀ {W W1 W2 W3 : ℝ → ℂ},
      (∀ s, s ≠ 0 → HasDerivAt W (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s) →
    ∀ {u ρ : ℝ}, 0 < |u| → ε * |u| ≤ 0.18 → 0 < ρ →
      (∀ x, |u| / 2 ≤ |x| → |x| ≤ |u| + |trF τ 0 (ε * u) / ε| → ‖W x‖ ≤ AW * ρ ∧ ‖W1 x‖ ≤ AW * (ρ * |u|⁻¹) ∧
        ‖W2 x‖ ≤ AW * (ρ * (|u|⁻¹) ^ 2) ∧ ‖W3 x‖ ≤ AW * (ρ * (|u|⁻¹) ^ 3)) →
      ‖innerDiff c ε τ W u‖ ≤ C * (L + ε ^ 2 * u ^ 2) * ρ ∧
      ‖deriv (innerDiff c ε τ W) u‖ ≤ C * (L + ε ^ 2 * u ^ 2) * (ρ * |u|⁻¹) ∧
      ‖deriv (deriv (innerDiff c ε τ W)) u‖ ≤ C * (L + ε ^ 2 * u ^ 2) * (ρ * (|u|⁻¹) ^ 2) := by
  obtain ⟨M, hM1, hMb⟩ := amp_q_bounds
  set A : ℝ := M + 50000 + AW with hA
  have hA1 : 1 ≤ A := by linarith
  refine ⟨4096 * A ^ 4, by positivity, ?_⟩
  intro L τ h hL0 hL2 c ε hc hε hcL W W1 W2 W3 hWd u ρ hu1 hu18 hρ hSl
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hu1
  set θ : ℝ := ε * u with hθdef
  have hθabs : |θ| = ε * |u| := by rw [hθdef, abs_mul, abs_of_pos hε]
  have hθ18 : |θ| ≤ 0.18 := by rw [hθabs]; exact hu18
  have hθ0 : θ ≠ 0 := mul_ne_zero hε.ne' hu0
  have hθ1 : |θ| ≤ 1 := by linarith
  have hθ2 : θ ^ 2 ≤ 0.0324 := by nlinarith [sq_abs θ, abs_nonneg θ]
  have hθu : ε ^ 2 * u ^ 2 = θ ^ 2 := by rw [hθdef]; ring
  have hMA : M ≤ A := by linarith
  have h5A : (50000 : ℝ) ≤ A := by linarith
  have hAWA : AW ≤ A := by linarith
  have hκ := edgeKappa0_bounds hL0 hL2
  have hUo : IsOpen {s : ℝ | |ε * s| < 0.22} := isOpen_lt (continuous_abs.comp (continuous_const.mul continuous_id)) continuous_const
  have huU : u ∈ {s : ℝ | |ε * s| < 0.22} := by show |ε * u| < 0.22; rw [← hθdef]; linarith
  -- derivative data on `U`
  have hmemU : ∀ s ∈ {s : ℝ | |ε * s| < 0.22}, |ε * s| < 0.22 := fun s hs => hs
  set wF : ℝ → ℝ := fun s => trF τ 0 (ε * s) / ε with hwF
  set w1F : ℝ → ℝ := fun s => trF τ 1 (ε * s) with hw1F
  set w2F : ℝ → ℝ := fun s => ε * trF τ 2 (ε * s) with hw2F
  have hwd : ∀ s ∈ {s : ℝ | |ε * s| < 0.22}, HasDerivAt wF (w1F s) s ∧ HasDerivAt w1F (w2F s) s := by
    intro s hs
    have h0 := hasDerivAt_dilate (trF_hasDerivAt h 0 (hmemU s hs))
    have h1 := hasDerivAt_dilate (trF_hasDerivAt h 1 (hmemU s hs))
    refine ⟨?_, ?_⟩
    · have := h0.div_const ε
      refine this.congr_deriv ?_
      simp only [hw1F, smul_eq_mul]; field_simp
    · exact h1.congr_deriv (by simp only [hw2F, smul_eq_mul])
  set QF : ℝ → ℂ := fun s => ampQ0 c τ (ε * s) with hQF
  set Q1F : ℝ → ℂ := fun s => (ε : ℂ) * ampQ1 c τ (ε * s) with hQ1F
  set Q2F : ℝ → ℂ := fun s => ((ε : ℂ) ^ 2) * ampQ2 c τ (ε * s) with hQ2F
  have hQd : ∀ s ∈ {s : ℝ | |ε * s| < 0.22}, HasDerivAt QF (Q1F s) s ∧ HasDerivAt Q1F (Q2F s) s := by
    intro s hs
    obtain ⟨a0, a1⟩ := ampQ_hasDerivAt h hc (hmemU s hs)
    have b0 := hasDerivAt_dilate a0
    have b1 := (hasDerivAt_dilate a1).const_mul (ε : ℂ)
    refine ⟨b0.congr_deriv ?_, b1.congr_deriv ?_⟩
    · simp [hQ1F, Complex.real_smul]
    · simp [hQ2F, Complex.real_smul]; ring
  set EF : ℝ → ℂ := fun s => Complex.exp (Complex.I * ((ε * s : ℝ) : ℂ) / 2) with hEF
  set E1F : ℝ → ℂ := fun s => ((Complex.I * (ε : ℂ) / 2)) * EF s with hE1F
  set E2F : ℝ → ℂ := fun s => ((Complex.I * (ε : ℂ) / 2)) ^ 2 * EF s with hE2F
  have hEd : ∀ s ∈ {s : ℝ | |ε * s| < 0.22}, HasDerivAt EF (E1F s) s ∧ HasDerivAt E1F (E2F s) s := by
    intro s hs
    have e0 := hasDerivAt_dilate (hasDerivAt_expHalf (ε * s))
    have e0' : HasDerivAt EF (E1F s) s := by
      refine e0.congr_deriv ?_
      simp only [hE1F, hEF, Complex.real_smul]; push_cast; ring
    refine ⟨e0', ?_⟩
    have := e0'.const_mul (Complex.I * (ε : ℂ) / 2)
    refine this.congr_deriv ?_
    simp only [hE2F]; ring
  -- pointwise hypotheses
  have hnorm_u : |u| = |θ| / ε := by rw [hθabs]; field_simp
  have hq : 1 / |u| = ε / |θ| := by rw [hnorm_u]; field_simp
  have hδ0 : 0 ≤ L + ε ^ 2 * u ^ 2 := by positivity
  have hδ1 : L + ε ^ 2 * u ^ 2 ≤ 1 := by rw [hθu]; linarith
  have hδ : L + ε ^ 2 * u ^ 2 = L + θ ^ 2 := by rw [hθu]
  have hratio := h.ratio hL0 hL2 hθ0 (by linarith : |θ| < 0.22)
  have htrθ : trF τ 0 θ = (τ (θ : ℂ)).re := by simp [trF]
  have hsg : 0 < wF u * u := by
    show 0 < trF τ 0 (ε * u) / ε * u
    rw [← hθdef, htrθ]
    have hpos : 0 < (τ (θ : ℂ)).re * θ := by
      have := hratio.1
      have h2 : 0 < (τ (θ : ℂ)).re / θ := by linarith
      have h3 : (τ (θ : ℂ)).re * θ = ((τ (θ : ℂ)).re / θ) * θ ^ 2 := by field_simp
      rw [h3]; exact mul_pos h2 (by positivity)
    have : (τ (θ : ℂ)).re / ε * u = ((τ (θ : ℂ)).re * θ) / ε ^ 2 := by rw [hθdef]; field_simp
    rw [this]; positivity
  have habs_tr : 0.989 * |θ| ≤ |trF τ 0 θ| := by
    rw [htrθ]
    have h1 := hratio.1
    have : |(τ (θ : ℂ)).re / θ| = |(τ (θ : ℂ)).re| / |θ| := abs_div _ _
    have h2 : 0.989 < |(τ (θ : ℂ)).re| / |θ| := by
      rw [← this, abs_of_pos (by linarith)]; exact h1
    rw [lt_div_iff₀ (abs_pos.mpr hθ0)] at h2
    linarith
  have hw0 : |u| / 2 ≤ |wF u| := by
    show |u| / 2 ≤ |trF τ 0 (ε * u) / ε|
    rw [← hθdef, abs_div, abs_of_pos hε, hnorm_u]
    have : |θ| / ε / 2 ≤ |trF τ 0 θ| / ε := by
      rw [div_div, div_le_div_iff₀ (by positivity) hε]; nlinarith [abs_nonneg θ, abs_nonneg (trF τ 0 θ)]
    exact this
  obtain ⟨tt0, tt1, tt2⟩ := tau_taylor_bounds h hθ18
  have e_tr0 : |trF τ 0 θ - edgeKappa0 L * θ| ≤ 50000 * |θ| ^ 3 := by
    have := Complex.abs_re_le_norm (τ (θ : ℂ) - (edgeKappa0 L : ℂ) * θ)
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at this
    rw [htrθ]; exact this.trans tt0
  have e_tr1 : |trF τ 1 θ - edgeKappa0 L| ≤ 50000 * θ ^ 2 := by
    have := Complex.abs_re_le_norm (deriv τ (θ : ℂ) - (edgeKappa0 L : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    rw [trF_one_eq]; exact this.trans tt1
  have e_tr2 : |trF τ 2 θ| ≤ 50000 * |θ| := by
    have := Complex.abs_re_le_norm (deriv (deriv τ) (θ : ℂ))
    have e : trF τ 2 θ = (deriv (deriv τ) (θ : ℂ)).re := by simp [trF, iteratedDeriv_succ]
    rw [e]; exact this.trans tt2
  have hk1 : 0 ≤ edgeKappa0 L - 1 := by linarith [hκ.1]
  have hk2 : edgeKappa0 L - 1 ≤ L / 4 := by linarith [hκ.2]
  have hδθ : 0 ≤ L + θ ^ 2 := by positivity
  have hw_u : |wF u - u| ≤ A * (L + ε ^ 2 * u ^ 2) * |u| := by
    show |trF τ 0 (ε * u) / ε - u| ≤ _
    rw [← hθdef, hδ]
    have : trF τ 0 θ / ε - u = (trF τ 0 θ - θ) / ε := by rw [hθdef]; field_simp
    rw [this, abs_div, abs_of_pos hε, div_le_iff₀ hε]
    have h1 : |trF τ 0 θ - θ| ≤ 50000 * |θ| ^ 3 + (L / 4) * |θ| := by
      have : trF τ 0 θ - θ = (trF τ 0 θ - edgeKappa0 L * θ) + (edgeKappa0 L - 1) * θ := by ring
      rw [this]
      refine (abs_add_le _ _).trans (add_le_add e_tr0 ?_)
      rw [abs_mul, abs_of_nonneg hk1]; gcongr
    have h2 : |θ| ^ 3 = θ ^ 2 * |θ| := by rw [← sq_abs θ]; ring
    have h3 : A * (L + θ ^ 2) * |u| * ε = A * (L + θ ^ 2) * |θ| := by rw [hθabs]; ring
    rw [h3]
    nlinarith [abs_nonneg θ, mul_nonneg hδθ (abs_nonneg θ), sq_nonneg θ, mul_nonneg hL0.le (abs_nonneg θ)]
  have hu_pos : 0 < |u| := hu1
  have hA0 : 0 ≤ A := by linarith
  have hAθ2 : 50000 * θ ^ 2 ≤ A * θ ^ 2 := mul_le_mul_of_nonneg_right h5A (sq_nonneg θ)
  have hMθ2 : M * θ ^ 2 ≤ A * θ ^ 2 := mul_le_mul_of_nonneg_right hMA (sq_nonneg θ)
  have hAL : L ≤ A * L := le_mul_of_one_le_left hL0.le hA1
  have hML : M * L ≤ A * L := mul_le_mul_of_nonneg_right hMA hL0.le
  have hAdist : A * (L + θ ^ 2) = A * L + A * θ ^ 2 := mul_add A L (θ ^ 2)
  have hεu : ε * |u| = |θ| := hθabs.symm
  have hw1_u : |w1F u - 1| ≤ A * (L + ε ^ 2 * u ^ 2) := by
    show |trF τ 1 (ε * u) - 1| ≤ _
    rw [← hθdef, hδ]
    have : trF τ 1 θ - 1 = (trF τ 1 θ - edgeKappa0 L) + (edgeKappa0 L - 1) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg hk1]
    linarith
  have hw2_u : |w2F u| ≤ A * (L + ε ^ 2 * u ^ 2) / |u| := by
    rw [le_div_iff₀ hu_pos]
    show |ε * trF τ 2 (ε * u)| * |u| ≤ _
    rw [← hθdef, hδ, abs_mul, abs_of_pos hε]
    calc ε * |trF τ 2 θ| * |u| ≤ ε * (50000 * |θ|) * |u| := by gcongr
      _ = 50000 * |θ| * (ε * |u|) := by ring
      _ = 50000 * θ ^ 2 := by rw [hεu, mul_assoc, abs_mul_abs_self]; ring
      _ ≤ A * (L + θ ^ 2) := by linarith [mul_nonneg hA0 hL0.le]
  have hQ0_u : ‖QF u‖ ≤ A * (L + ε ^ 2 * u ^ 2) := by
    obtain ⟨b0, -, -⟩ := hMb h hL0 hL2 hc hcL hθ18
    show ‖ampQ0 c τ (ε * u)‖ ≤ _
    rw [← hθdef, hδ]
    exact b0.trans (mul_le_mul_of_nonneg_right hMA hδθ)
  have hQ1_u : ‖Q1F u‖ ≤ A * (L + ε ^ 2 * u ^ 2) / |u| := by
    obtain ⟨-, b1, -⟩ := hMb h hL0 hL2 hc hcL hθ18
    rw [le_div_iff₀ hu_pos]
    show ‖(ε : ℂ) * ampQ1 c τ (ε * u)‖ * |u| ≤ _
    rw [← hθdef, hδ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    calc ε * ‖ampQ1 c τ θ‖ * |u| = ‖ampQ1 c τ θ‖ * (ε * |u|) := by ring
      _ = ‖ampQ1 c τ θ‖ * |θ| := by rw [hεu]
      _ ≤ M * (L + |θ|) * |θ| := by gcongr
      _ = M * (L * |θ|) + M * θ ^ 2 := by rw [← sq_abs θ]; ring
      _ ≤ A * (L + θ ^ 2) := by
        have h1 : L * |θ| ≤ L := mul_le_of_le_one_right hL0.le hθ1
        have h2 : M * (L * |θ|) ≤ M * L := mul_le_mul_of_nonneg_left h1 (by linarith)
        linarith
  have hQ2_u : ‖Q2F u‖ ≤ A * (L + ε ^ 2 * u ^ 2) / |u| ^ 2 := by
    obtain ⟨-, -, b2⟩ := hMb h hL0 hL2 hc hcL hθ18
    rw [le_div_iff₀ (by positivity)]
    show ‖((ε : ℂ) ^ 2) * ampQ2 c τ (ε * u)‖ * |u| ^ 2 ≤ _
    rw [← hθdef, hδ, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    calc ε ^ 2 * ‖ampQ2 c τ θ‖ * |u| ^ 2 = ‖ampQ2 c τ θ‖ * (ε * |u|) ^ 2 := by ring
      _ = ‖ampQ2 c τ θ‖ * θ ^ 2 := by rw [hεu, sq_abs]
      _ ≤ M * θ ^ 2 := by gcongr
      _ ≤ A * (L + θ ^ 2) := by linarith [mul_nonneg hA0 hL0.le]
  have hEn : ∀ s : ℝ, ‖EF s‖ = 1 := fun s => by simp [hEF, Complex.norm_exp]
  have hE0_u : ‖EF u‖ ≤ A := by rw [hEn]; linarith
  have hE1n : ‖E1F u‖ = ε / 2 := by
    simp only [hE1F, norm_mul, hEn, mul_one, Complex.norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hε, Complex.norm_ofNat, one_mul]
  have hE2n : ‖E2F u‖ = ε ^ 2 / 4 := by
    simp only [hE2F, norm_mul, hEn, mul_one, norm_pow, Complex.norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hε, Complex.norm_ofNat, one_mul]
    ring
  have hE1_u : ‖E1F u‖ ≤ A / |u| := by
    rw [le_div_iff₀ hu_pos, hE1n]
    have : ε / 2 * |u| = |θ| / 2 := by rw [← hεu]; ring
    rw [this]; linarith [abs_nonneg θ]
  have hE2_u : ‖E2F u‖ ≤ A / |u| ^ 2 := by
    rw [le_div_iff₀ (by positivity), hE2n]
    have : ε ^ 2 / 4 * |u| ^ 2 = θ ^ 2 / 4 := by rw [← sq_abs θ, ← hεu]; ring
    rw [this]; linarith [sq_nonneg θ]
  have hSl' : ∀ x, |u| / 2 ≤ |x| → |x| ≤ |u| + |wF u| → ‖W x‖ ≤ 64 * A * ρ ∧ ‖W1 x‖ ≤ 64 * A * (ρ * |u|⁻¹) ∧
      ‖W2 x‖ ≤ 64 * A * (ρ * (|u|⁻¹) ^ 2) ∧ ‖W3 x‖ ≤ 64 * A * (ρ * (|u|⁻¹) ^ 3) := by
    intro x hx hxR
    obtain ⟨a0, a1, a2, a3⟩ := hSl x hx hxR
    have hq0 : 0 ≤ |u|⁻¹ := inv_nonneg.mpr hu_pos.le
    have hAW64 : AW ≤ 64 * A := by linarith
    refine ⟨a0.trans ?_, a1.trans ?_, a2.trans ?_, a3.trans ?_⟩ <;> gcongr
  have key := symbol_diff_local A hA1 hUo (W := W) (w := wF) (w1 := w1F) (w2 := w2F) (Q := QF) (Q1 := Q1F) (Q2 := Q2F)
    (E := EF) (E1 := E1F) (E2 := E2F) (δ := L + ε ^ 2 * u ^ 2) (u := u) (ρ := ρ) (R := |u| + |wF u|) huU hu1 hδ0 hδ1 hρ
    (by linarith [abs_nonneg (wF u)]) (by linarith [abs_nonneg u]) hWd hSl' hwd hQd hEd
    hsg hw0 hw_u hw1_u hw2_u hQ0_u hQ1_u hQ2_u hE0_u hE1_u hE2_u
  have hD : innerDiff c ε τ W = fun s => QF s * W (wF s) + EF s * (W (wF s) - W s) := by
    funext s
    simp only [innerDiff, hQF, ampQ0, hEF, hwF]
    ring
  rw [hD]
  obtain ⟨k0, k1, k2⟩ := key
  exact ⟨by simpa [mul_assoc] using k0, by simpa [mul_assoc] using k1, by simpa [mul_assoc] using k2⟩

/-- The decay hypotheses `‖W^{(j)}(s)‖ ≤ A|s|^{-5/2-j}` give the local form with `ρ = |u|^{-5/2}` and constant `64A`. -/
lemma symbol_local_of_decay {AW : ℝ} {W W1 W2 W3 : ℝ → ℂ} {u : ℝ} (hu : 1 ≤ |u|)
    (hWb : ∀ s, 1 / 2 ≤ |s| → ‖W s‖ ≤ AW * |s| ^ (-(5 / 2 : ℝ)) ∧ ‖W1 s‖ ≤ AW * |s| ^ (-(7 / 2 : ℝ)) ∧
      ‖W2 s‖ ≤ AW * |s| ^ (-(9 / 2 : ℝ)) ∧ ‖W3 s‖ ≤ AW * |s| ^ (-(11 / 2 : ℝ))) (hA : 0 ≤ AW) :
    ∀ x, |u| / 2 ≤ |x| → ‖W x‖ ≤ (64 * AW) * |u| ^ (-(5 / 2 : ℝ)) ∧
      ‖W1 x‖ ≤ (64 * AW) * (|u| ^ (-(5 / 2 : ℝ)) * |u|⁻¹) ∧
      ‖W2 x‖ ≤ (64 * AW) * (|u| ^ (-(5 / 2 : ℝ)) * (|u|⁻¹) ^ 2) ∧
      ‖W3 x‖ ≤ (64 * AW) * (|u| ^ (-(5 / 2 : ℝ)) * (|u|⁻¹) ^ 3) := by
  intro x hx
  have hm0 : 0 < |u| := by linarith
  have hx' : 1 / 2 ≤ |x| := by linarith
  obtain ⟨b0, b1, b2, b3⟩ := hWb x hx'
  have r0 := mbd_rpow_le hm0 hx (by norm_num : (0 : ℝ) < 5 / 2) (by norm_num)
  have r1 := mbd_rpow_le hm0 hx (by norm_num : (0 : ℝ) < 7 / 2) (by norm_num)
  have r2 := mbd_rpow_le hm0 hx (by norm_num : (0 : ℝ) < 9 / 2) (by norm_num)
  have r3 := mbd_rpow_le hm0 hx (by norm_num : (0 : ℝ) < 11 / 2) (by norm_num)
  have e7 : |u| ^ (-(7 / 2 : ℝ)) = |u| ^ (-(5 / 2 : ℝ)) * |u|⁻¹ := by
    rw [show (-(7 / 2 : ℝ)) = -(5 / 2 : ℝ) + (-1 : ℝ) by norm_num, Real.rpow_add hm0, Real.rpow_neg_one]
  have e9 : |u| ^ (-(9 / 2 : ℝ)) = |u| ^ (-(5 / 2 : ℝ)) * (|u|⁻¹) ^ 2 := by
    rw [show (-(9 / 2 : ℝ)) = -(5 / 2 : ℝ) + (-2 : ℝ) by norm_num, Real.rpow_add hm0]
    rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; simp [zpow_neg]
  have e11 : |u| ^ (-(11 / 2 : ℝ)) = |u| ^ (-(5 / 2 : ℝ)) * (|u|⁻¹) ^ 3 := by
    rw [show (-(11 / 2 : ℝ)) = -(5 / 2 : ℝ) + (-3 : ℝ) by norm_num, Real.rpow_add hm0]
    rw [show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; simp [zpow_neg]
  rw [e7] at r1; rw [e9] at r2; rw [e11] at r3
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc ‖W x‖ ≤ AW * |x| ^ (-(5 / 2 : ℝ)) := b0
      _ ≤ AW * (64 * |u| ^ (-(5 / 2 : ℝ))) := by gcongr
      _ = _ := by ring
  · calc ‖W1 x‖ ≤ AW * |x| ^ (-(7 / 2 : ℝ)) := b1
      _ ≤ AW * (64 * (|u| ^ (-(5 / 2 : ℝ)) * |u|⁻¹)) := by gcongr
      _ = _ := by ring
  · calc ‖W2 x‖ ≤ AW * |x| ^ (-(9 / 2 : ℝ)) := b2
      _ ≤ AW * (64 * (|u| ^ (-(5 / 2 : ℝ)) * (|u|⁻¹) ^ 2)) := by gcongr
      _ = _ := by ring
  · calc ‖W3 x‖ ≤ AW * |x| ^ (-(11 / 2 : ℝ)) := b3
      _ ≤ AW * (64 * (|u| ^ (-(5 / 2 : ℝ)) * (|u|⁻¹) ^ 3)) := by gcongr
      _ = _ := by ring

/-- **`(e8)`**: `|𝒟^{(r)}(u)| ≤ C (L + ε²u²) |u|^{-5/2-r}` (`r ≤ 2`, `|u| ≥ 1`, `ε|u| ≤ 0.18`), for symbols `W̃` with
`|W̃^{(j)}(s)| ≤ A_W |s|^{-5/2-j}` (`|s| ≥ 1/2`, `j ≤ 3`); `C` depends only on `A_W`. -/
theorem innerDiff_bounds (AW : ℝ) (hAW : 1 ≤ AW) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {L : ℝ} {τ : ℂ → ℂ}, O4NormalForm L τ → 0 < L → L ≤ 0.002 → ∀ {c ε : ℝ}, 2 ≤ c → 0 < ε → 1 / c ≤ L →
    ∀ {W W1 W2 W3 : ℝ → ℂ},
      (∀ s, s ≠ 0 → HasDerivAt W (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s) →
      (∀ s, 1 / 2 ≤ |s| → ‖W s‖ ≤ AW * |s| ^ (-(5 / 2 : ℝ)) ∧ ‖W1 s‖ ≤ AW * |s| ^ (-(7 / 2 : ℝ)) ∧
        ‖W2 s‖ ≤ AW * |s| ^ (-(9 / 2 : ℝ)) ∧ ‖W3 s‖ ≤ AW * |s| ^ (-(11 / 2 : ℝ))) →
    ∀ {u : ℝ}, 1 ≤ |u| → ε * |u| ≤ 0.18 →
      ‖innerDiff c ε τ W u‖ ≤ C * (L + ε ^ 2 * u ^ 2) * |u| ^ (-(5 / 2 : ℝ)) ∧
      ‖deriv (innerDiff c ε τ W) u‖ ≤ C * (L + ε ^ 2 * u ^ 2) * |u| ^ (-(7 / 2 : ℝ)) ∧
      ‖deriv (deriv (innerDiff c ε τ W)) u‖ ≤ C * (L + ε ^ 2 * u ^ 2) * |u| ^ (-(9 / 2 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := innerDiff_local (64 * AW) (by linarith)
  refine ⟨C, hC0, ?_⟩
  intro L τ h hL0 hL2 c ε hc hε hcL W W1 W2 W3 hWd hWb u hu1 hu18
  have hm0 : 0 < |u| := by linarith
  have hS := symbol_local_of_decay hu1 hWb (by linarith)
  obtain ⟨k0, k1, k2⟩ := hC h hL0 hL2 hc hε hcL hWd hm0 hu18 (Real.rpow_pos_of_pos hm0 _)
    (fun x hx _ => hS x hx)
  have e7 : |u| ^ (-(7 / 2 : ℝ)) = |u| ^ (-(5 / 2 : ℝ)) * |u|⁻¹ := by
    rw [show (-(7 / 2 : ℝ)) = -(5 / 2 : ℝ) + (-1 : ℝ) by norm_num, Real.rpow_add hm0, Real.rpow_neg_one]
  have e9 : |u| ^ (-(9 / 2 : ℝ)) = |u| ^ (-(5 / 2 : ℝ)) * (|u|⁻¹) ^ 2 := by
    rw [show (-(9 / 2 : ℝ)) = -(5 / 2 : ℝ) + (-2 : ℝ) by norm_num, Real.rpow_add hm0]
    rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; simp [zpow_neg]
  rw [e7, e9]
  exact ⟨k0, k1, k2⟩

end

/-- info: 'FormalResearch.SignUncertainty.outerK_deriv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.outerK_deriv_zero

/-- info: 'FormalResearch.SignUncertainty.ampQ_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.ampQ_hasDerivAt

/-- info: 'FormalResearch.SignUncertainty.amp_q_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.amp_q_bounds

/-- info: 'FormalResearch.SignUncertainty.innerDiff_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.innerDiff_local

/-- info: 'FormalResearch.SignUncertainty.innerDiff_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.innerDiff_bounds

end FormalResearch.SignUncertainty
