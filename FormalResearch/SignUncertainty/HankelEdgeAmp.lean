module

public import FormalResearch.Asymptotics.BinetRemainder

/-!
# Edge amplitude of the Hankel edge expansion

The edge amplitude `a₀(τ) = (1 - i τ)^{1/2} exp(-B_c(i τ))`, where `B_c` is the shifted
Binet difference `FormalResearch.Asymptotics.binetDiff`.

## Main definitions
* `hankelEdgeAmpB c τ`: the Binet difference `B_c(i τ)`.
* `hankelEdgeAmp c τ`: the edge amplitude `a₀(τ)`.
* `hankelEdgeAmp' c τ`: its real derivative in `τ`.

## Main results (all for `0 < c`)
* `hankelEdgeAmp_binetDiff_differentiableAt`: `B_c` is complex differentiable on `Re ζ < 1`.
* `hankelEdgeAmp_hasDerivAt`: `a₀` has real derivative `hankelEdgeAmp' c τ` at every `τ`.
* `hankelEdgeAmp_norm_eq`, `hankelEdgeAmp_norm_le`: the exact modulus of `a₀`, and its bound
  `‖a₀ τ‖ ≤ (1 + τ²)^{1/4} exp(1 / (6 c))`.
* `hankelEdgeAmp_bound`: for `c ≥ 1`, `‖a₀ τ‖ + ‖a₀' τ‖ ≤ 4 (1 + |τ|)^{1/2}`.
* `hankelEdgeAmp_continuous`: `a₀` is continuous in `τ`.

All statements are proved in standard classical mathematics; no numerical evidence is used.
-/

@[expose] public section

open Set
open scoped Topology

namespace FormalResearch.SignUncertainty

/-- The Binet difference `B_c(i τ)` on the imaginary axis. -/
noncomputable def hankelEdgeAmpB (c τ : ℝ) : ℂ :=
  FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)

/-- The edge amplitude `a₀(τ) = (1 - i τ)^{1/2} exp(-B_c(i τ))`. -/
noncomputable def hankelEdgeAmp (c τ : ℝ) : ℂ :=
  (1 - (τ : ℂ) * Complex.I) ^ (1 / 2 : ℂ) * Complex.exp (-(hankelEdgeAmpB c τ))

/-- The real derivative `d/dτ a₀(τ)`. -/
noncomputable def hankelEdgeAmp' (c τ : ℝ) : ℂ :=
  ((-Complex.I / 2) * (1 - (τ : ℂ) * Complex.I) ^ (-(1 / 2) : ℂ)
     - (1 - (τ : ℂ) * Complex.I) ^ (1 / 2 : ℂ) *
        (Complex.I * deriv (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I)))
    * Complex.exp (-(hankelEdgeAmpB c τ))

/-! ### Differentiability of `B_c` -/

/-- `B_c` is complex differentiable at every `ζ` with `Re ζ < 1` (`c > 0`). -/
theorem hankelEdgeAmp_binetDiff_differentiableAt {c : ℝ} (hc : 0 < c) {ζ : ℂ}
    (hζ : ζ.re < 1) :
    DifferentiableAt ℂ (FormalResearch.Asymptotics.binetDiff c) ζ := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hw : (c : ℂ) * (1 - ζ) ∈ {w : ℂ | 0 < w.re} := by
    show 0 < ((c : ℂ) * (1 - ζ)).re
    have hre : ((c : ℂ) * (1 - ζ)).re = c * (1 - ζ.re) := by
      simp [Complex.mul_re]
    rw [hre]
    exact mul_pos hc (by linarith)
  have hf : DifferentiableAt ℂ (fun z : ℂ => (c : ℂ) * (1 - z)) ζ := by fun_prop
  have hg : DifferentiableAt ℂ FormalResearch.Asymptotics.binetRem ((c : ℂ) * (1 - ζ)) :=
    (FormalResearch.Asymptotics.binetRem_differentiableOn.differentiableAt
      (hopen.mem_nhds hw))
  have h1 : DifferentiableAt ℂ
      (FormalResearch.Asymptotics.binetRem ∘ fun z : ℂ => (c : ℂ) * (1 - z)) ζ :=
    DifferentiableAt.comp ζ hg hf
  have h2 : DifferentiableAt ℂ
      (fun _ : ℂ => FormalResearch.Asymptotics.binetRem (c : ℂ)) ζ :=
    differentiableAt_const _
  unfold FormalResearch.Asymptotics.binetDiff
  exact h1.sub h2

/-! ### Modulus of the base `1 - i τ` -/

/-- `‖1 - i τ‖ = (1 + τ²)^{1/2}`. -/
theorem hankelEdgeAmp_norm_base (τ : ℝ) :
    ‖(1 : ℂ) - (τ : ℂ) * Complex.I‖ = (1 + τ ^ 2) ^ (1 / 2 : ℝ) := by
  rw [Complex.norm_def, Complex.normSq_apply, Real.sqrt_eq_rpow]
  congr 1
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, sub_zero, Complex.sub_im,
    Complex.one_im, Complex.mul_im, mul_one]
  ring

/-- For a real exponent `s`, `‖(1 - i τ)^s‖ = (1 + τ²)^{s/2}`. -/
theorem hankelEdgeAmp_norm_cpow_real (τ s : ℝ) :
    ‖(1 - (τ : ℂ) * Complex.I) ^ (s : ℂ)‖ = (1 + τ ^ 2) ^ (s / 2) := by
  rw [Complex.norm_cpow_real, hankelEdgeAmp_norm_base, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- The modulus of `a₀(τ)`: `‖a₀(τ)‖ = (1 + τ²)^{1/4} exp(-Re B_c(i τ))`. -/
theorem hankelEdgeAmp_norm_eq (c τ : ℝ) :
    ‖hankelEdgeAmp c τ‖ = (1 + τ ^ 2) ^ (1 / 4 : ℝ) *
      Real.exp (-(hankelEdgeAmpB c τ).re) := by
  have hpow : ‖(1 - (τ : ℂ) * Complex.I) ^ (1 / 2 : ℂ)‖ = (1 + τ ^ 2) ^ (1 / 4 : ℝ) := by
    have h := hankelEdgeAmp_norm_cpow_real τ (1 / 2 : ℝ)
    push_cast at h
    rw [h]
    norm_num
  rw [hankelEdgeAmp, norm_mul, hpow, Complex.norm_exp, Complex.neg_re]

/-- `‖exp(-B_c(i τ))‖ ≤ exp(1 / (6 c))` (`0 < c`). -/
theorem hankelEdgeAmp_exp_norm_le {c : ℝ} (hc : 0 < c) (τ : ℝ) :
    ‖Complex.exp (-(hankelEdgeAmpB c τ))‖ ≤ Real.exp (1 / (6 * c)) := by
  rw [Complex.norm_exp, Complex.neg_re]
  have hB : ‖hankelEdgeAmpB c τ‖ ≤ 1 / (6 * c) :=
    FormalResearch.Asymptotics.binetDiff_norm_le_left hc (by simp)
  have hneg : -(hankelEdgeAmpB c τ).re ≤ 1 / (6 * c) :=
    (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hB)
  exact Real.exp_le_exp.mpr hneg

/-- Bound `‖a₀(τ)‖ ≤ (1 + τ²)^{1/4} exp(1 / (6 c))` (`0 < c`). -/
theorem hankelEdgeAmp_norm_le {c : ℝ} (hc : 0 < c) (τ : ℝ) :
    ‖hankelEdgeAmp c τ‖ ≤ (1 + τ ^ 2) ^ (1 / 4 : ℝ) * Real.exp (1 / (6 * c)) := by
  have hE := hankelEdgeAmp_exp_norm_le hc τ
  rw [Complex.norm_exp, Complex.neg_re] at hE
  rw [hankelEdgeAmp_norm_eq]
  exact mul_le_mul_of_nonneg_left hE (by positivity)

/-! ### Derivative -/

/-- `a₀` has real derivative `hankelEdgeAmp' c τ` at every `τ` (`c > 0`). -/
theorem hankelEdgeAmp_hasDerivAt {c : ℝ} (hc : 0 < c) (τ : ℝ) :
    HasDerivAt (hankelEdgeAmp c) (hankelEdgeAmp' c τ) τ := by
  have hslit : (1 : ℂ) - (τ : ℂ) * Complex.I ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    simp
  have hlin : HasDerivAt (fun u : ℂ => (1 : ℂ) - u * Complex.I) (-Complex.I) (τ : ℂ) := by
    have h := ((hasDerivAt_id' (τ : ℂ)).mul_const Complex.I).const_sub (1 : ℂ)
    simpa using h
  have hpow : HasDerivAt (fun u : ℂ => (1 - u * Complex.I) ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * (1 - (τ : ℂ) * Complex.I) ^ ((1 / 2 : ℂ) - 1) * (-Complex.I))
      (τ : ℂ) :=
    hlin.cpow_const hslit
  have hBd : HasDerivAt (FormalResearch.Asymptotics.binetDiff c)
      (deriv (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I))
      ((τ : ℂ) * Complex.I) :=
    (hankelEdgeAmp_binetDiff_differentiableAt hc (by simp)).hasDerivAt
  have hinner : HasDerivAt (fun u : ℂ => u * Complex.I) Complex.I (τ : ℂ) := by
    simpa using (hasDerivAt_id' (τ : ℂ)).mul_const Complex.I
  have hcomp : HasDerivAt (FormalResearch.Asymptotics.binetDiff c ∘ fun u : ℂ => u * Complex.I)
      (deriv (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I) * Complex.I)
      (τ : ℂ) :=
    HasDerivAt.comp (τ : ℂ) hBd hinner
  have hB : HasDerivAt (fun u : ℂ => FormalResearch.Asymptotics.binetDiff c (u * Complex.I))
      (deriv (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I) * Complex.I)
      (τ : ℂ) := hcomp
  have hexp : HasDerivAt
      (fun u : ℂ => Complex.exp (-(FormalResearch.Asymptotics.binetDiff c (u * Complex.I))))
      (Complex.exp (-(FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I))) *
        (-(deriv (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I) * Complex.I)))
      (τ : ℂ) :=
    hB.neg.cexp
  have hmain := hpow.mul hexp
  have hreal := hmain.comp_ofReal
  have hexp_eq : (1 / 2 : ℂ) - 1 = -(1 / 2) := by ring
  refine hreal.congr_deriv ?_
  rw [hexp_eq]
  unfold hankelEdgeAmp' hankelEdgeAmpB
  ring

/-! ### Continuity and the uniform bound -/

/-- `a₀` is continuous in `τ` (`c > 0`). -/
theorem hankelEdgeAmp_continuous {c : ℝ} (hc : 0 < c) : Continuous (hankelEdgeAmp c) :=
  continuous_iff_continuousAt.2 fun τ => (hankelEdgeAmp_hasDerivAt hc τ).continuousAt

/-- Pointwise bound `‖a₀(τ)‖ + ‖a₀'(τ)‖ ≤ 4 (1 + |τ|)^{1/2}` for `c ≥ 1`. -/
theorem hankelEdgeAmp_bound {c : ℝ} (hc : 1 ≤ c) (τ : ℝ) :
    ‖hankelEdgeAmp c τ‖ + ‖hankelEdgeAmp' c τ‖ ≤ 4 * (1 + |τ|) ^ (1 / 2 : ℝ) := by
  have hc0 : 0 < c := by linarith
  set P : ℝ := (1 + τ ^ 2) ^ (1 / 4 : ℝ) with hP
  set E : ℝ := Real.exp (1 / (6 * c)) with hE
  set Q : ℝ := (1 + |τ|) ^ (1 / 2 : ℝ) with hQ
  have hP0 : 0 ≤ P := by positivity
  have hE0 : 0 ≤ E := by positivity
  have hQ1 : 1 ≤ Q := Real.one_le_rpow (by linarith [abs_nonneg τ]) (by norm_num)
  -- `P ≤ Q`
  have hPQ : P ≤ Q := by
    have h1 : 1 + τ ^ 2 ≤ (1 + |τ|) ^ 2 := by
      nlinarith [abs_nonneg τ, sq_abs τ]
    have h2 : ((1 + |τ|) ^ 2 : ℝ) ^ (1 / 4 : ℝ) = Q := by
      rw [hQ, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hP, ← h2]
    exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  -- `E ≤ 6/5`
  have hE_le : E ≤ 6 / 5 := by
    have hx : 1 / (6 * c) ≤ 1 / 6 := by
      apply one_div_le_one_div_of_le (by norm_num)
      linarith
    have hexp6 : Real.exp (1 / 6) ≤ 6 / 5 := by
      have h1 := Real.add_one_le_exp (-(1 / 6 : ℝ))
      have h2 : Real.exp (1 / 6) * Real.exp (-(1 / 6)) = 1 := by
        rw [← Real.exp_add]; simp
      have h3 := Real.exp_pos (1 / 6 : ℝ)
      nlinarith
    calc E ≤ Real.exp (1 / 6) := Real.exp_le_exp.mpr hx
      _ ≤ 6 / 5 := hexp6
  -- norm of the amplitude
  have hA : ‖hankelEdgeAmp c τ‖ ≤ P * E := hankelEdgeAmp_norm_le hc0 τ
  -- norm of the derivative
  have hX : ‖(1 - (τ : ℂ) * Complex.I) ^ (-(1 / 2) : ℂ)‖ ≤ 1 := by
    have h := hankelEdgeAmp_norm_cpow_real τ (-(1 / 2) : ℝ)
    push_cast at h
    rw [h]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg τ])
    linarith
  have hY : ‖(1 - (τ : ℂ) * Complex.I) ^ (1 / 2 : ℂ)‖ = P := by
    have h := hankelEdgeAmp_norm_cpow_real τ (1 / 2 : ℝ)
    push_cast at h
    rw [h, hP]
    norm_num
  have hD : ‖deriv (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I)‖ ≤ 1 / 12 := by
    have h := FormalResearch.Asymptotics.binetDiff_iteratedDeriv_norm_le hc0
      (ζ := (τ : ℂ) * Complex.I) (r := 1) (by simp) le_rfl
    rw [iteratedDeriv_one] at h
    have h' : ‖deriv (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I)‖ ≤
        (Nat.factorial 1 : ℝ) / (12 * c) := h
    refine h'.trans ?_
    rw [Nat.factorial_one, Nat.cast_one, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hExp := hankelEdgeAmp_exp_norm_le hc0 τ
  have hM : ‖hankelEdgeAmp' c τ‖ ≤ (1 / 2 + P / 12) * E := by
    unfold hankelEdgeAmp'
    rw [norm_mul]
    refine mul_le_mul ?_ hExp (norm_nonneg _) (by positivity)
    have hI : ‖-Complex.I / 2‖ = 1 / 2 := by norm_num [norm_div]
    have h1 : ‖(-Complex.I / 2) * (1 - (τ : ℂ) * Complex.I) ^ (-(1 / 2) : ℂ)‖ ≤ 1 / 2 := by
      rw [norm_mul, hI]
      nlinarith [norm_nonneg ((1 - (τ : ℂ) * Complex.I) ^ (-(1 / 2) : ℂ))]
    have h2 : ‖(1 - (τ : ℂ) * Complex.I) ^ (1 / 2 : ℂ) *
        (Complex.I * deriv (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I))‖
        ≤ P / 12 := by
      rw [norm_mul, norm_mul, hY, Complex.norm_I, one_mul]
      calc P * ‖deriv (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I)‖
          ≤ P * (1 / 12) := mul_le_mul_of_nonneg_left hD hP0
        _ = P / 12 := by ring
    calc ‖(-Complex.I / 2) * (1 - (τ : ℂ) * Complex.I) ^ (-(1 / 2) : ℂ) -
          (1 - (τ : ℂ) * Complex.I) ^ (1 / 2 : ℂ) *
            (Complex.I * deriv (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I))‖
        ≤ ‖(-Complex.I / 2) * (1 - (τ : ℂ) * Complex.I) ^ (-(1 / 2) : ℂ)‖ +
          ‖(1 - (τ : ℂ) * Complex.I) ^ (1 / 2 : ℂ) *
            (Complex.I * deriv (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I))‖ :=
          norm_sub_le _ _
      _ ≤ 1 / 2 + P / 12 := add_le_add h1 h2
  have hsum : ‖hankelEdgeAmp c τ‖ + ‖hankelEdgeAmp' c τ‖ ≤ P * E + (1 / 2 + P / 12) * E :=
    add_le_add hA hM
  have hbr : 0 ≤ 1 / 2 + 13 / 12 * P := by positivity
  have hfac : P * E + (1 / 2 + P / 12) * E = E * (1 / 2 + 13 / 12 * P) := by ring
  calc ‖hankelEdgeAmp c τ‖ + ‖hankelEdgeAmp' c τ‖
      ≤ E * (1 / 2 + 13 / 12 * P) := by linarith
    _ ≤ 6 / 5 * (1 / 2 + 13 / 12 * Q) :=
        mul_le_mul hE_le (by linarith) hbr (by norm_num)
    _ ≤ 4 * Q := by linarith

/-! ### Axiom checks -/

/-- info: 'FormalResearch.SignUncertainty.hankelEdgeAmp_binetDiff_differentiableAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.hankelEdgeAmp_binetDiff_differentiableAt

/-- info: 'FormalResearch.SignUncertainty.hankelEdgeAmp_norm_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.hankelEdgeAmp_norm_base

/-- info: 'FormalResearch.SignUncertainty.hankelEdgeAmp_norm_cpow_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.hankelEdgeAmp_norm_cpow_real

/-- info: 'FormalResearch.SignUncertainty.hankelEdgeAmp_norm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.hankelEdgeAmp_norm_eq

/-- info: 'FormalResearch.SignUncertainty.hankelEdgeAmp_exp_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.hankelEdgeAmp_exp_norm_le

/-- info: 'FormalResearch.SignUncertainty.hankelEdgeAmp_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.hankelEdgeAmp_norm_le

/-- info: 'FormalResearch.SignUncertainty.hankelEdgeAmp_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.hankelEdgeAmp_hasDerivAt

/-- info: 'FormalResearch.SignUncertainty.hankelEdgeAmp_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.hankelEdgeAmp_continuous

/-- info: 'FormalResearch.SignUncertainty.hankelEdgeAmp_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.hankelEdgeAmp_bound

end FormalResearch.SignUncertainty
