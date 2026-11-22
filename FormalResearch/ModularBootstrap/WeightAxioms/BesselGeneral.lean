module

public import FormalResearch.ModularBootstrap.Crossing.SumRule
public import FormalResearch.ModularBootstrap.ComplexBessel.BesselI0Sector
public import FormalResearch.Special.AiryHypergeometric

/-!
# General Integer-Order Modified Bessel Functions `I_n` (`n : ℕ`) and Complex Asymptotics

Extends `Bessel` and `ComplexBessel.BesselI0Sector` from `I₀` to `I_n` for all `n : ℕ` (used for
general chiral weight `w ≥ 1` with `n = w - 1`):

* `besselSC n y := Complex.regularizedHGFun 0 {(n + 1 : ℂ)} y` and
  `besselIC n z := (z / 2)^n * besselSC n (z^2 / 4)` (entire, agreeing with `Bessel.besselI n` on `ℝ`
  and with `besselI0C` at `n = 0`).
* `besselIC_eq_integral`: `I_n(z) = π⁻¹ ∫₀^π exp(z cos θ) cos(n θ) dθ` for all `z : ℂ`.
* `sinEvenIntegral`, `besselSC_eq_sin_integral`: the positive-weight integral representation
  `besselSC n (z^2 / 4) = ((n! * ∫₀^π sin^{2n} θ dθ)⁻¹) * ∫₀^π exp(z cos θ) sin^{2n} θ dθ`
  (`n1_super_virasoro.tex`, Lemma 4(a) proof), giving `‖besselSC n (z^2 / 4)‖ ≤ besselS n (z.re ^ 2 / 4)`
  and derivative/scaling bounds for the strip continuation.
* `besselIC_sector_asymptotic_of_re_pos`, `besselIC_sector_asymptotic`: uniform complex sector
  asymptotic `‖I_n(z) - asC z‖ ≤ (C / ‖z‖) * ‖asC z‖` on `|arg z| ≤ π/2 - ε` (`0 < z.re`,
  `κ * ‖z‖ ≤ z.re`), proved by reducing `I_n - I_0` via `1 - cos(n θ) ≤ n^2 π^2 t^2 / 4` and
  reusing `ComplexBessel.besselI0C_sector_asymptotic_of_re_pos`.
* `besselI_asymptotic_real`: real corollary `|I_n(x) / as(x) - 1| ≤ C_n / x` for `x > 0`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set intervalIntegral
open scoped Real Nat Interval

namespace FormalResearch.ModularBootstrap.WeightAxioms

open Crossing Bessel ComplexBessel

/-! ### Section 1: Complex `besselSC` and `besselIC` -/

/-- Entire regularized Bessel power series `S_n(y) = ∑_{k ≥ 0} y^k / (k! (k + n)!)`. -/
noncomputable def besselSC (n : ℕ) (y : ℂ) : ℂ :=
  Complex.regularizedHGFun 0 {((n + 1 : ℕ) : ℂ)} y

/-- Entire modified Bessel function of integer order `n : ℕ`:
`I_n(z) = (z / 2)^n S_n(z^2 / 4)`. -/
noncomputable def besselIC (n : ℕ) (z : ℂ) : ℂ :=
  (z / 2) ^ n * besselSC n (z ^ 2 / 4)

lemma besselSC_eq_tsum (n : ℕ) (y : ℂ) :
    besselSC n y = ∑' k : ℕ, y ^ k / ((k ! : ℂ) * ((k + n)! : ℂ)) := by
  unfold besselSC
  rw [FormalResearch.Special.regularizedHGFun_zero_singleton]
  refine tsum_congr fun k => ?_
  have hgam : Complex.Gamma (((n + 1 : ℕ) : ℂ) + (k : ℂ)) = ((k + n)! : ℂ) := by
    rw [show ((n + 1 : ℕ) : ℂ) + (k : ℂ) = ((k + n : ℕ) : ℂ) + 1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial]
  rw [hgam]
  ring

lemma besselSC_zero_order (y : ℂ) :
    besselSC 0 y = Complex.regularizedHGFun 0 {(1 : ℂ)} y := by
  simp [besselSC]

lemma besselIC_zero_eq (z : ℂ) : besselIC 0 z = besselI0C z := by
  unfold besselIC
  rw [pow_zero, one_mul, besselSC_zero_order, besselI0C_eq_hgfun]

lemma besselSC_entire (n : ℕ) : Differentiable ℂ (besselSC n) := fun y =>
  (Complex.analyticAt_regularizedHGFun_zero y).differentiableAt

lemma besselIC_entire (n : ℕ) : Differentiable ℂ (besselIC n) := by
  unfold besselIC
  have h1 : Differentiable ℂ (fun z : ℂ => (z / 2) ^ n) :=
    (differentiable_id.div_const 2).pow n
  have h2 : Differentiable ℂ (fun z : ℂ => besselSC n (z ^ 2 / 4)) :=
    (besselSC_entire n).comp ((differentiable_id.pow 2).div_const 4)
  exact h1.mul h2

lemma besselSC_ofReal (n : ℕ) (y : ℝ) : besselSC n (y : ℂ) = (besselS n y : ℂ) := by
  rw [besselSC_eq_tsum, besselS]
  have hs : Summable fun k : ℕ => besselTerm n y k := by
    have hexp : Summable fun k : ℕ => |y| ^ k / (k ! : ℝ) := Real.summable_pow_div_factorial |y|
    refine hexp.of_norm_bounded fun k => ?_
    unfold besselTerm
    have hk1 : (0 : ℝ) < (k ! : ℝ) := by positivity
    have hk2 : (1 : ℝ) ≤ ((k + n)! : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (by positivity : 0 < (k ! : ℝ) * ((k + n)! : ℝ))]
    exact div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg _) k) hk1 (by nlinarith)
  have hsum := Complex.ofRealCLM.hasSum hs.hasSum
  have hsum_eq : (∑' k : ℕ, ((besselTerm n y k : ℝ) : ℂ)) = ((∑' k : ℕ, besselTerm n y k : ℝ) : ℂ) :=
    hsum.tsum_eq
  rw [← hsum_eq]
  refine tsum_congr fun k => ?_
  unfold besselTerm
  push_cast
  rfl

lemma besselIC_ofReal (n : ℕ) (x : ℝ) : besselIC n (x : ℂ) = (besselI n x : ℂ) := by
  unfold besselIC besselI
  rw [show ((x : ℂ) ^ 2 / 4) = ((x ^ 2 / 4 : ℝ) : ℂ) by push_cast; ring, besselSC_ofReal]
  push_cast
  rfl

/-! ### Section 2: Integral representation `I_n(z) = π⁻¹ ∫₀^π exp(z cos θ) cos(n θ) dθ` -/

private lemma besselIC_integral_differentiable (n : ℕ) :
    Differentiable ℂ (fun z : ℂ =>
      (π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..π, Complex.exp (z * (Real.cos θ : ℝ)) * (Real.cos (n * θ) : ℝ)) := by
  intro z₀
  let F : ℂ → ℝ → ℂ := fun z θ => Complex.exp (z * (Real.cos θ : ℝ)) * (Real.cos (n * θ) : ℝ)
  let F' : ℂ → ℝ → ℂ := fun z θ =>
    (Real.cos θ : ℂ) * Complex.exp (z * (Real.cos θ : ℝ)) * (Real.cos (n * θ) : ℝ)
  have hF_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) (volume.restrict (Ι (0 : ℝ) π)) :=
    Eventually.of_forall fun z => (by fun_prop : Continuous (F z)).aestronglyMeasurable
  have hF_int : IntervalIntegrable (F z₀) volume 0 π :=
    (by fun_prop : Continuous (F z₀)).intervalIntegrable 0 π
  have hF'_meas : AEStronglyMeasurable (F' z₀) (volume.restrict (Ι (0 : ℝ) π)) :=
    (by fun_prop : Continuous (F' z₀)).aestronglyMeasurable
  have hbound : ∀ᵐ θ : ℝ, θ ∈ Ι (0 : ℝ) π → ∀ z ∈ ball z₀ 1,
      ‖F' z θ‖ ≤ Real.exp (‖z₀‖ + 1) := by
    refine Eventually.of_forall fun θ _ z hz => ?_
    have hcos : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
    have hcosn : |Real.cos (n * θ)| ≤ 1 := Real.abs_cos_le_one (n * θ)
    have hz_norm : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have hlt : ‖z - z₀‖ < 1 := by simpa [Complex.dist_eq] using mem_ball.mp hz
      linarith [show ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ by simpa using norm_add_le (z - z₀) z₀]
    have hre : (z * (Real.cos θ : ℝ)).re ≤ ‖z₀‖ + 1 := by
      calc (z * (Real.cos θ : ℝ)).re ≤ ‖z * (Real.cos θ : ℝ)‖ := Complex.re_le_norm _
        _ = ‖z‖ * |Real.cos θ| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ (‖z₀‖ + 1) * 1 := mul_le_mul hz_norm hcos (abs_nonneg _) (by positivity)
        _ = ‖z₀‖ + 1 := mul_one _
    calc ‖F' z θ‖ = |Real.cos θ| * Real.exp ((z * (Real.cos θ : ℝ)).re) * |Real.cos (n * θ)| := by
          dsimp [F']
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
            Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 1 * Real.exp (‖z₀‖ + 1) * 1 := by gcongr
      _ = Real.exp (‖z₀‖ + 1) := by ring
  have hdiff : ∀ᵐ θ : ℝ, θ ∈ Ι (0 : ℝ) π →
      ∀ z ∈ ball z₀ 1, HasDerivAt (F · θ) (F' z θ) z := by
    refine Eventually.of_forall fun θ _ z _ => ?_
    have hd : HasDerivAt (fun w : ℂ => w * (Real.cos θ : ℂ)) (Real.cos θ : ℂ) z := by
      simpa using (hasDerivAt_id z).mul_const (Real.cos θ : ℂ)
    exact ((hd.cexp).mul_const ((Real.cos (n * θ) : ℝ) : ℂ)).congr_deriv (by
      dsimp [F']; ring)
  have key := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds z₀ one_pos) hF_meas hF_int hF'_meas hbound
    intervalIntegrable_const hdiff).2
  exact (key.const_mul (π : ℂ)⁻¹).differentiableAt

/-- Integral representation of `besselIC n z` on all of `ℂ`:
`I_n(z) = π⁻¹ ∫₀^π exp(z cos θ) cos(n θ) dθ`. -/
theorem besselIC_eq_integral (n : ℕ) (z : ℂ) :
    besselIC n z =
      (π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..π, Complex.exp (z * (Real.cos θ : ℝ)) * (Real.cos (n * θ) : ℝ) := by
  let g : ℂ → ℂ := fun w =>
    (π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..π, Complex.exp (w * (Real.cos θ : ℝ)) * (Real.cos (n * θ) : ℝ)
  have han1 : AnalyticOnNhd ℂ (besselIC n) univ :=
    (besselIC_entire n).differentiableOn.analyticOnNhd isOpen_univ
  have han2 : AnalyticOnNhd ℂ g univ :=
    (besselIC_integral_differentiable n).differentiableOn.analyticOnNhd isOpen_univ
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), besselIC n w = g w := by
    rw [frequently_nhdsWithin_iff, Filter.frequently_iff]
    intro U hU
    obtain ⟨r, hr_pos, hrU⟩ := Metric.mem_nhds_iff.mp hU
    refine ⟨((r / 2 : ℝ) : ℂ), hrU ?_, ?_, ?_⟩
    · simp only [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hr_pos)]
      linarith
    · rw [besselIC_ofReal, Crossing.besselI_eq_integral]
      dsimp [g]
      have hfn : (fun θ : ℝ => Complex.exp (((r / 2 : ℝ) : ℂ) * (Real.cos θ : ℝ)) *
            (Real.cos (n * θ) : ℝ)) =
          fun θ : ℝ => ((Real.exp ((r / 2) * Real.cos θ) * Real.cos (n * θ) : ℝ) : ℂ) := by
        ext θ; rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
      rw [one_div, ← Complex.ofReal_inv, hfn, intervalIntegral.integral_ofReal]
      push_cast; ring
    · exact Complex.ofReal_ne_zero.mpr (half_pos hr_pos).ne'
  exact congrFun (han1.eq_of_frequently_eq han2 hfreq) z

/-! ### Section 3: Positive-measure integral representation of `besselSC n (z^2 / 4)` -/

/-- Normalised sine integral `∫₀^π sin^{2n} θ dθ`. -/
noncomputable def sinEvenIntegral (n : ℕ) : ℝ :=
  ∫ θ in (0 : ℝ)..π, Real.sin θ ^ (2 * n)

lemma sinEvenIntegral_zero : sinEvenIntegral 0 = π := by
  simp [sinEvenIntegral]

lemma sinEvenIntegral_succ (n : ℕ) :
    sinEvenIntegral (n + 1) = (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) * sinEvenIntegral n := by
  unfold sinEvenIntegral
  rw [show 2 * (n + 1) = 2 * n + 2 by ring, integral_sin_pow]
  simp only [Real.sin_zero, Real.sin_pi, zero_pow (Nat.succ_ne_zero _), zero_mul, sub_self,
    zero_div, zero_add]
  push_cast; ring

lemma sinEvenIntegral_pos (n : ℕ) : 0 < sinEvenIntegral n := by
  induction n with
  | zero => rw [sinEvenIntegral_zero]; exact Real.pi_pos
  | succ n ih => rw [sinEvenIntegral_succ]; positivity

lemma sinEvenIntegral_eq (n : ℕ) :
    sinEvenIntegral n = π * ((2 * n)! : ℝ) / (4 ^ n * ((n ! : ℝ) ^ 2)) := by
  induction n with
  | zero => simp [sinEvenIntegral_zero]
  | succ n ih =>
    rw [sinEvenIntegral_succ, ih]
    have h1 : ((2 * (n + 1))! : ℝ) = (2 * n + 2) * (2 * n + 1) * ((2 * n)! : ℝ) := by
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    rw [h1, Nat.factorial_succ n]
    push_cast
    have hn_ne : (n ! : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-- Mixed moment `∫₀^π cos^m θ sin^{2n} θ dθ`. -/
noncomputable def cosSinMoment (m n : ℕ) : ℝ :=
  ∫ θ in (0 : ℝ)..π, Real.cos θ ^ m * Real.sin θ ^ (2 * n)

lemma cosSinMoment_odd (k n : ℕ) : cosSinMoment (2 * k + 1) n = 0 := by
  unfold cosSinMoment
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => Real.cos θ ^ (2 * k + 1) * Real.sin θ ^ (2 * n)) π (a := 0) (b := π)
  simp only [sub_zero, sub_self] at hsub
  have hneg : ∫ θ in (0 : ℝ)..π, Real.cos (π - θ) ^ (2 * k + 1) * Real.sin (π - θ) ^ (2 * n) =
      -∫ θ in (0 : ℝ)..π, Real.cos θ ^ (2 * k + 1) * Real.sin θ ^ (2 * n) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [Real.cos_pi_sub, Real.sin_pi_sub, Odd.neg_pow ⟨k, rfl⟩]
    ring
  linarith

lemma cosSinMoment_zero (n : ℕ) : cosSinMoment 0 n = sinEvenIntegral n := by
  simp [cosSinMoment, sinEvenIntegral]

lemma cosSinMoment_add_two (m n : ℕ) :
    cosSinMoment (m + 2) n = ((m : ℝ) + 1) / ((m : ℝ) + 2 + 2 * (n : ℝ)) * cosSinMoment m n := by
  unfold cosSinMoment
  let F : ℝ → ℝ := fun θ => Real.cos θ ^ (m + 1) * Real.sin θ ^ (2 * n + 1)
  have hderiv : ∀ θ ∈ uIcc (0 : ℝ) π,
      HasDerivAt F
        (-((m : ℝ) + 1) * Real.cos θ ^ m * Real.sin θ ^ (2 * n + 2) +
          (2 * (n : ℝ) + 1) * Real.cos θ ^ (m + 2) * Real.sin θ ^ (2 * n)) θ := by
    intro θ _
    have hc : HasDerivAt (fun x => Real.cos x ^ (m + 1))
        (((m : ℝ) + 1) * Real.cos θ ^ m * (-Real.sin θ)) θ := by
      have h := (Real.hasDerivAt_cos θ).pow (m + 1)
      simpa [Pi.pow_def, Nat.cast_add, Nat.cast_one] using h.congr_deriv (by simp)
    have hs : HasDerivAt (fun x => Real.sin x ^ (2 * n + 1))
        ((2 * (n : ℝ) + 1) * Real.sin θ ^ (2 * n) * Real.cos θ) θ := by
      have h := (Real.hasDerivAt_sin θ).pow (2 * n + 1)
      simpa [Pi.pow_def, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using h.congr_deriv (by simp)
    refine (hc.mul hs).congr_deriv ?_
    rw [show 2 * n + 2 = 2 * n + 1 + 1 by ring, show m + 2 = m + 1 + 1 by ring,
      pow_succ (Real.sin θ) (2 * n + 1), pow_succ (Real.cos θ) (m + 1)]
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun θ : ℝ =>
      -((m : ℝ) + 1) * Real.cos θ ^ m * Real.sin θ ^ (2 * n + 2) +
        (2 * (n : ℝ) + 1) * Real.cos θ ^ (m + 2) * Real.sin θ ^ (2 * n)).intervalIntegrable 0 π)
  have hF0 : F 0 = 0 := by simp [F]
  have hFpi : F π = 0 := by simp [F]
  rw [hF0, hFpi, sub_self] at hint
  have hrew : ∀ θ : ℝ,
      -((m : ℝ) + 1) * Real.cos θ ^ m * Real.sin θ ^ (2 * n + 2) +
        (2 * (n : ℝ) + 1) * Real.cos θ ^ (m + 2) * Real.sin θ ^ (2 * n) =
      ((m : ℝ) + 2 + 2 * (n : ℝ)) * (Real.cos θ ^ (m + 2) * Real.sin θ ^ (2 * n)) -
        ((m : ℝ) + 1) * (Real.cos θ ^ m * Real.sin θ ^ (2 * n)) := by
    intro θ
    have hsq : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := Real.sin_sq θ
    rw [show 2 * n + 2 = 2 * n + 2 by rfl, pow_add, hsq, pow_add (Real.cos θ) m 2]
    ring
  have h1 : IntervalIntegrable (fun θ : ℝ =>
      ((m : ℝ) + 2 + 2 * (n : ℝ)) * (Real.cos θ ^ (m + 2) * Real.sin θ ^ (2 * n))) volume 0 π :=
    Continuous.intervalIntegrable (by fun_prop) 0 π
  have h2 : IntervalIntegrable (fun θ : ℝ =>
      ((m : ℝ) + 1) * (Real.cos θ ^ m * Real.sin θ ^ (2 * n))) volume 0 π :=
    Continuous.intervalIntegrable (by fun_prop) 0 π
  rw [intervalIntegral.integral_congr (fun θ _ => hrew θ), intervalIntegral.integral_sub h1 h2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint
  have hden : (m : ℝ) + 2 + 2 * (n : ℝ) ≠ 0 := by positivity
  field_simp [hden]
  linarith

lemma cosSinMoment_even (k n : ℕ) :
    cosSinMoment (2 * k) n =
      ((2 * k)! : ℝ) * (n ! : ℝ) / (4 ^ k * (k ! : ℝ) * ((k + n)! : ℝ)) * sinEvenIntegral n := by
  induction k with
  | zero =>
    have hn_ne : (n ! : ℝ) ≠ 0 := by positivity
    simp [cosSinMoment_zero]; field_simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, cosSinMoment_add_two, ih]
    have h1 : ((2 * (k + 1))! : ℝ) = (2 * k + 2) * (2 * k + 1) * ((2 * k)! : ℝ) := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    rw [show 2 * k + 2 = 2 * (k + 1) by ring, h1, Nat.factorial_succ k, Nat.succ_add,
      Nat.factorial_succ (k + n)]
    push_cast
    have hk_ne : (k ! : ℝ) ≠ 0 := by positivity
    have hkn_ne : ((k + n)! : ℝ) ≠ 0 := by positivity
    have hden_ne : 2 * (k : ℝ) + 2 + 2 * (n : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-- Positive-weight integral representation of `besselSC n (z^2 / 4)` for all `n : ℕ` and `z : ℂ`:
`besselSC n (z^2 / 4) = ((n! * sinEvenIntegral n) : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..π, exp(z cos θ) sin^{2n} θ dθ`. -/
theorem besselSC_eq_sin_integral (n : ℕ) (z : ℂ) :
    besselSC n (z ^ 2 / 4) =
      (((n ! : ℝ) * sinEvenIntegral n : ℝ) : ℂ)⁻¹ *
        ∫ θ in (0 : ℝ)..π, Complex.exp (z * (Real.cos θ : ℝ)) * ((Real.sin θ ^ (2 * n) : ℝ) : ℂ) := by
  have hc_pos : 0 < (n ! : ℝ) * sinEvenIntegral n := mul_pos (by positivity) (sinEvenIntegral_pos n)
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := π)
    (F := fun (m : ℕ) (θ : ℝ) => (z * (Real.cos θ : ℝ)) ^ m / (m ! : ℂ) * ((Real.sin θ ^ (2 * n) : ℝ) : ℂ))
    (f := fun θ : ℝ => Complex.exp (z * (Real.cos θ : ℝ)) * ((Real.sin θ ^ (2 * n) : ℝ) : ℂ))
    (fun m _ => ‖z‖ ^ m / (m ! : ℝ))
    (fun m => by fun_prop)
    (fun m => Filter.Eventually.of_forall fun θ _ => by
      have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
      have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
      rw [norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_pow]
      have h1 : |Real.cos θ| ^ m ≤ 1 := pow_le_one₀ (abs_nonneg _) hc
      have h2 : |Real.sin θ| ^ (2 * n) ≤ 1 := pow_le_one₀ (abs_nonneg _) hs
      have h3 : (‖z‖ * |Real.cos θ|) ^ m / (m ! : ℝ) ≤ ‖z‖ ^ m / (m ! : ℝ) := by
        gcongr
        calc ‖z‖ * |Real.cos θ| ≤ ‖z‖ * 1 := by gcongr
          _ = ‖z‖ := mul_one _
      calc (‖z‖ * |Real.cos θ|) ^ m / (m ! : ℝ) * |Real.sin θ| ^ (2 * n)
          ≤ (‖z‖ ^ m / (m ! : ℝ)) * 1 := mul_le_mul h3 h2 (by positivity) (by positivity)
        _ = ‖z‖ ^ m / (m ! : ℝ) := mul_one _)
    (Filter.Eventually.of_forall fun _ _ => Real.summable_pow_div_factorial ‖z‖)
    (by simp)
    (Filter.Eventually.of_forall fun θ _ => by
      have hexp := (NormedSpace.expSeries_div_hasSum_exp (z * (Real.cos θ : ℝ))).mul_right
        ((Real.sin θ ^ (2 * n) : ℝ) : ℂ)
      rw [← Complex.exp_eq_exp_ℂ] at hexp
      exact hexp)
  have hterm : ∀ m : ℕ,
      ∫ θ in (0 : ℝ)..π,
        (z * (Real.cos θ : ℝ)) ^ m / (m ! : ℂ) * ((Real.sin θ ^ (2 * n) : ℝ) : ℂ) =
      z ^ m / (m ! : ℂ) * (cosSinMoment m n : ℂ) := fun m => by
    have hfn : (fun θ : ℝ =>
        (z * (Real.cos θ : ℝ)) ^ m / (m ! : ℂ) * ((Real.sin θ ^ (2 * n) : ℝ) : ℂ)) =
        fun θ : ℝ => (z ^ m / (m ! : ℂ)) * ((Real.cos θ ^ m * Real.sin θ ^ (2 * n) : ℝ) : ℂ) := by
      ext θ; rw [mul_pow]; push_cast; ring
    rw [hfn, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
    rfl
  have hsum2 : HasSum (fun m : ℕ => z ^ m / (m ! : ℂ) * (cosSinMoment m n : ℂ))
      (∫ θ in (0 : ℝ)..π, Complex.exp (z * (Real.cos θ : ℝ)) * ((Real.sin θ ^ (2 * n) : ℝ) : ℂ)) := by
    convert hsum using 1
    ext m
    exact (hterm m).symm
  have heven : HasSum (fun k : ℕ => z ^ (2 * k) / ((2 * k)! : ℂ) * (cosSinMoment (2 * k) n : ℂ))
      (∫ θ in (0 : ℝ)..π, Complex.exp (z * (Real.cos θ : ℝ)) * ((Real.sin θ ^ (2 * n) : ℝ) : ℂ)) := by
    have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by dsimp at h; omega
    show HasSum ((fun m => z ^ m / (m ! : ℂ) * (cosSinMoment m n : ℂ)) ∘ fun k => 2 * k) _
    rw [hinj.hasSum_iff]
    · exact hsum2
    · intro m hm
      have : m % 2 = 1 := by
        by_contra h2
        exact hm ⟨m / 2, by dsimp; omega⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
      simp [cosSinMoment_odd]
  have hmul := heven.mul_left ((((n ! : ℝ) * sinEvenIntegral n : ℝ) : ℂ)⁻¹)
  have hcoeff : ∀ k : ℕ,
      ((((n ! : ℝ) * sinEvenIntegral n : ℝ) : ℂ)⁻¹) *
        (z ^ (2 * k) / ((2 * k)! : ℂ) * (cosSinMoment (2 * k) n : ℂ)) =
      (z ^ 2 / 4) ^ k / ((k ! : ℂ) * ((k + n)! : ℂ)) := fun k => by
    rw [cosSinMoment_even]
    push_cast
    have hs_ne : (sinEvenIntegral n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sinEvenIntegral_pos n).ne'
    have hn_ne : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hk_ne : (k ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have h2k_ne : ((2 * k)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * k)
    have hkn_ne : ((k + n)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k + n)
    rw [div_pow, pow_mul, show (4 : ℂ) ^ k = ((2 : ℂ) ^ 2) ^ k by norm_num, ← pow_mul]
    field_simp
  simp_rw [hcoeff] at hmul
  rw [besselSC_eq_tsum]
  exact hmul.tsum_eq

/-- Strip domination of `besselSC`: `‖besselSC n (z^2 / 4)‖ ≤ besselS n (z.re ^ 2 / 4)`. -/
theorem norm_besselSC_sq_div_four_le (n : ℕ) (z : ℂ) :
    ‖besselSC n (z ^ 2 / 4)‖ ≤ besselS n (z.re ^ 2 / 4) := by
  have hs_pos := sinEvenIntegral_pos n
  rw [besselSC_eq_sin_integral, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (mul_pos (by positivity) hs_pos).le]
  have hreal : (besselS n (z.re ^ 2 / 4) : ℂ) = besselSC n ((z.re : ℂ) ^ 2 / 4) := by
    rw [show ((z.re : ℂ) ^ 2 / 4) = ((z.re ^ 2 / 4 : ℝ) : ℂ) by push_cast; ring, besselSC_ofReal]
  have hreal_eq : besselS n (z.re ^ 2 / 4) =
      ((n ! : ℝ) * sinEvenIntegral n)⁻¹ *
        ∫ θ in (0 : ℝ)..π, Real.exp (z.re * Real.cos θ) * Real.sin θ ^ (2 * n) := by
    have h1 := besselSC_eq_sin_integral n (z.re : ℂ)
    rw [← hreal] at h1
    have hfn : (fun θ : ℝ => Complex.exp ((z.re : ℂ) * (Real.cos θ : ℝ)) *
          ((Real.sin θ ^ (2 * n) : ℝ) : ℂ)) =
        fun θ : ℝ => ((Real.exp (z.re * Real.cos θ) * Real.sin θ ^ (2 * n) : ℝ) : ℂ) := by
      ext θ; rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
    rw [hfn, intervalIntegral.integral_ofReal] at h1
    exact Complex.ofReal_injective (by simpa [Complex.ofReal_mul, Complex.ofReal_inv] using h1)
  rw [hreal_eq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (intervalIntegral.norm_integral_le_integral_norm Real.pi_pos.le).trans ?_
  refine le_of_eq (intervalIntegral.integral_congr fun θ hθ => ?_)
  rw [uIcc_of_le Real.pi_pos.le] at hθ
  have hsin_nn : 0 ≤ Real.sin θ ^ (2 * n) := pow_nonneg (Real.sin_nonneg_of_mem_Icc hθ) _
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg hsin_nn]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- Derivative of `z ↦ besselSC n (z^2 / 4)` as a sine-weighted integral. -/
noncomputable def besselSCSqDeriv (n : ℕ) (z : ℂ) : ℂ :=
  (((n ! : ℝ) * sinEvenIntegral n : ℝ) : ℂ)⁻¹ *
    ∫ θ in (0 : ℝ)..π, (Real.cos θ : ℂ) * Complex.exp (z * (Real.cos θ : ℝ)) *
      ((Real.sin θ ^ (2 * n) : ℝ) : ℂ)

lemma hasDerivAt_besselSC_sq_div_four (n : ℕ) (z₀ : ℂ) :
    HasDerivAt (fun z : ℂ => besselSC n (z ^ 2 / 4)) (besselSCSqDeriv n z₀) z₀ := by
  let F : ℂ → ℝ → ℂ := fun z θ =>
    Complex.exp (z * (Real.cos θ : ℝ)) * ((Real.sin θ ^ (2 * n) : ℝ) : ℂ)
  let F' : ℂ → ℝ → ℂ := fun z θ =>
    (Real.cos θ : ℂ) * Complex.exp (z * (Real.cos θ : ℝ)) * ((Real.sin θ ^ (2 * n) : ℝ) : ℂ)
  have hint := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℂ) (F := F) (F' := F') (x₀ := z₀) (s := Metric.ball z₀ 1)
    (a := 0) (b := π) (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => (by fun_prop : Continuous (F z)).aestronglyMeasurable)
    ((by fun_prop : Continuous (F z₀)).intervalIntegrable 0 π)
    (by fun_prop : Continuous (F' z₀)).aestronglyMeasurable
    (Eventually.of_forall fun θ _ z hz => by
      dsimp [F']
      have hcos : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
      have hsin : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
      have hz1 : ‖z‖ ≤ ‖z₀‖ + 1 := by
        calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
          _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
          _ ≤ 1 + ‖z₀‖ := by linarith [(dist_eq_norm z z₀ ▸ Metric.mem_ball.mp hz).le]
          _ = ‖z₀‖ + 1 := by ring
      have hre : (z * (Real.cos θ : ℝ)).re ≤ ‖z₀‖ + 1 := by
        calc (z * (Real.cos θ : ℝ)).re ≤ ‖z * (Real.cos θ : ℝ)‖ := Complex.re_le_norm _
          _ = ‖z‖ * |Real.cos θ| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ ‖z₀‖ + 1 := by nlinarith [norm_nonneg z]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
        Complex.norm_real, Real.norm_eq_abs, abs_pow]
      have hs1 : |Real.sin θ| ^ (2 * n) ≤ 1 := pow_le_one₀ (abs_nonneg _) hsin
      calc |Real.cos θ| * Real.exp (z * (Real.cos θ : ℝ)).re * |Real.sin θ| ^ (2 * n)
          ≤ 1 * Real.exp (‖z₀‖ + 1) * 1 := by gcongr
        _ = Real.exp (‖z₀‖ + 1) := by ring)
    (intervalIntegrable_const (μ := volume))
    (Eventually.of_forall fun θ _ z _ => by
      dsimp [F, F']
      have hd := (((hasDerivAt_id z).mul_const (Real.cos θ : ℂ)).cexp.mul_const
        ((Real.sin θ ^ (2 * n) : ℝ) : ℂ))
      refine hd.congr_deriv ?_
      dsimp only [id_eq]; ring)
  have hconst := hint.2.const_mul ((((n ! : ℝ) * sinEvenIntegral n : ℝ) : ℂ)⁻¹)
  refine hconst.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
  exact besselSC_eq_sin_integral n z

lemma besselSCSqDeriv_norm_le (n : ℕ) (z : ℂ) :
    ‖besselSCSqDeriv n z‖ ≤ besselS n (z.re ^ 2 / 4) := by
  have hs_pos := sinEvenIntegral_pos n
  unfold besselSCSqDeriv
  rw [norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (mul_pos (by positivity) hs_pos).le]
  have hreal_eq : besselS n (z.re ^ 2 / 4) =
      ((n ! : ℝ) * sinEvenIntegral n)⁻¹ *
        ∫ θ in (0 : ℝ)..π, Real.exp (z.re * Real.cos θ) * Real.sin θ ^ (2 * n) := by
    have h1 := besselSC_eq_sin_integral n (z.re : ℂ)
    have hreal : (besselS n (z.re ^ 2 / 4) : ℂ) = besselSC n ((z.re : ℂ) ^ 2 / 4) := by
      rw [show ((z.re : ℂ) ^ 2 / 4) = ((z.re ^ 2 / 4 : ℝ) : ℂ) by push_cast; ring, besselSC_ofReal]
    rw [← hreal] at h1
    have hfn : (fun θ : ℝ => Complex.exp ((z.re : ℂ) * (Real.cos θ : ℝ)) *
          ((Real.sin θ ^ (2 * n) : ℝ) : ℂ)) =
        fun θ : ℝ => ((Real.exp (z.re * Real.cos θ) * Real.sin θ ^ (2 * n) : ℝ) : ℂ) := by
      ext θ; rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
    rw [hfn, intervalIntegral.integral_ofReal] at h1
    exact Complex.ofReal_injective (by simpa [Complex.ofReal_mul, Complex.ofReal_inv] using h1)
  rw [hreal_eq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (intervalIntegral.norm_integral_le_integral_norm Real.pi_pos.le).trans ?_
  refine intervalIntegral.integral_mono_on Real.pi_pos.le
    (Continuous.intervalIntegrable (by fun_prop) 0 π)
    (Continuous.intervalIntegrable (by fun_prop) 0 π)
    fun θ hθ => ?_
  have hsin_nn : 0 ≤ Real.sin θ ^ (2 * n) := pow_nonneg (Real.sin_nonneg_of_mem_Icc hθ) _
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
    Complex.norm_real, Real.norm_of_nonneg hsin_nn]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hcos : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  calc |Real.cos θ| * Real.exp (z.re * Real.cos θ) * Real.sin θ ^ (2 * n)
      ≤ 1 * Real.exp (z.re * Real.cos θ) * Real.sin θ ^ (2 * n) := by gcongr
    _ = Real.exp (z.re * Real.cos θ) * Real.sin θ ^ (2 * n) := by ring

lemma besselS_sq_div_four_le_exp (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    besselS n (u ^ 2 / 4) ≤ Real.exp u / (n ! : ℝ) := by
  have hs_pos := sinEvenIntegral_pos n
  have hreal_eq : besselS n (u ^ 2 / 4) =
      ((n ! : ℝ) * sinEvenIntegral n)⁻¹ *
        ∫ θ in (0 : ℝ)..π, Real.exp (u * Real.cos θ) * Real.sin θ ^ (2 * n) := by
    have h1 := besselSC_eq_sin_integral n (u : ℂ)
    have hreal : (besselS n (u ^ 2 / 4) : ℂ) = besselSC n ((u : ℂ) ^ 2 / 4) := by
      rw [show ((u : ℂ) ^ 2 / 4) = ((u ^ 2 / 4 : ℝ) : ℂ) by push_cast; ring, besselSC_ofReal]
    rw [← hreal] at h1
    have hfn : (fun θ : ℝ => Complex.exp ((u : ℂ) * (Real.cos θ : ℝ)) *
          ((Real.sin θ ^ (2 * n) : ℝ) : ℂ)) =
        fun θ : ℝ => ((Real.exp (u * Real.cos θ) * Real.sin θ ^ (2 * n) : ℝ) : ℂ) := by
      ext θ; rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
    rw [hfn, intervalIntegral.integral_ofReal] at h1
    exact Complex.ofReal_injective (by simpa [Complex.ofReal_mul, Complex.ofReal_inv] using h1)
  rw [hreal_eq]
  have hle : ∫ θ in (0 : ℝ)..π, Real.exp (u * Real.cos θ) * Real.sin θ ^ (2 * n) ≤
      Real.exp u * sinEvenIntegral n := by
    unfold sinEvenIntegral
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on Real.pi_pos.le
      (Continuous.intervalIntegrable (by fun_prop) 0 π)
      (Continuous.intervalIntegrable (by fun_prop) 0 π) fun θ hθ => ?_
    have hsin_nn : 0 ≤ Real.sin θ ^ (2 * n) := pow_nonneg (Real.sin_nonneg_of_mem_Icc hθ) _
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [Real.cos_le_one θ])) hsin_nn
  have hs_ne : sinEvenIntegral n ≠ 0 := hs_pos.ne'
  calc ((n ! : ℝ) * sinEvenIntegral n)⁻¹ *
        ∫ θ in (0 : ℝ)..π, Real.exp (u * Real.cos θ) * Real.sin θ ^ (2 * n)
      ≤ ((n ! : ℝ) * sinEvenIntegral n)⁻¹ * (Real.exp u * sinEvenIntegral n) := by
        refine mul_le_mul_of_nonneg_left hle (by positivity)
    _ = Real.exp u / (n ! : ℝ) := by field_simp

lemma besselS_sq_div_four_ge_pos (n : ℕ) {u : ℝ} (_hu : 0 < u) :
    ∃ c z₀ : ℝ, 0 < c ∧ 1 ≤ z₀ ∧ ∀ v : ℝ, z₀ ≤ v →
      c * Real.exp v / v ^ ((n : ℝ) + 1 / 2) ≤ besselS n (v ^ 2 / 4) := by
  obtain ⟨c₀, z₀, hc₀, hz₀, hbd⟩ := Crossing.besselI_ge_exp_div_sqrt n
  refine ⟨c₀ * 2 ^ n, z₀, by positivity, hz₀, fun v hv => ?_⟩
  have hv_pos : 0 < v := lt_of_lt_of_le (by linarith) hv
  have h1 := hbd v hv
  have hI : besselI n v = (v / 2) ^ n * besselS n (v ^ 2 / 4) := rfl
  rw [hI] at h1
  have hpow_pos : 0 < (v / 2) ^ n := by positivity
  have h2 : c₀ * Real.exp v / Real.sqrt v / (v / 2) ^ n ≤ besselS n (v ^ 2 / 4) := by
    rw [div_le_iff₀ hpow_pos]
    linarith
  refine le_trans ?_ h2
  have hrpow : Real.sqrt v * v ^ n = v ^ ((n : ℝ) + 1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast v n, ← Real.rpow_add hv_pos]
    congr 1; ring
  have h2n : (v / 2) ^ n = v ^ n / 2 ^ n := div_pow v 2 n
  rw [h2n]
  have heq : c₀ * Real.exp v / Real.sqrt v / (v ^ n / 2 ^ n) =
      c₀ * 2 ^ n * Real.exp v / (Real.sqrt v * v ^ n) := by
    have hvn : v ^ n ≠ 0 := by positivity
    have hsv : Real.sqrt v ≠ 0 := by positivity
    field_simp
  rw [heq, hrpow]

/-- Scaling domination for `besselS`: for `0 ≤ r < 1`, `u * S_n((r u)^2 / 4) ≤ C * S_n(u^2 / 4)`
for all `u ≥ 0` (used for differentiating `hankelContinuationW` under the integral sign). -/
theorem mul_besselS_scaled_le (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u →
      u * besselS n ((r * u) ^ 2 / 4) ≤ C * besselS n (u ^ 2 / 4) := by
  obtain ⟨c₀, z₀, hc₀, hz₀, hbd⟩ := besselS_sq_div_four_ge_pos n (u := 1) zero_lt_one
  set δ : ℝ := 1 - r with hδ_def
  have hδ : 0 < δ := sub_pos.mpr hr1
  have hexp_poly : ∃ C_p : ℝ, 0 < C_p ∧ ∀ u : ℝ, 0 ≤ u →
      u ^ (n + 2) ≤ C_p * Real.exp (δ * u) := by
    refine ⟨((n + 2)! : ℝ) / δ ^ (n + 2), by positivity, fun u hu => ?_⟩
    have hterm : (δ * u) ^ (n + 2) / ((n + 2)! : ℝ) ≤ Real.exp (δ * u) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      exact (Real.summable_pow_div_factorial (δ * u)).le_tsum (n + 2)
        fun k _ => div_nonneg (pow_nonneg (by positivity) k) (by positivity)
    rw [mul_pow] at hterm
    have h1 : u ^ (n + 2) ≤ ((n + 2)! : ℝ) / δ ^ (n + 2) * Real.exp (δ * u) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at hterm
      nlinarith
    exact h1
  obtain ⟨C_p, hCp_pos, hCp⟩ := hexp_poly
  let C_small : ℝ := z₀ * (n ! : ℝ) * Real.exp z₀ / (n ! : ℝ)
  let C_head : ℝ := z₀ * Real.exp z₀
  let C_tail : ℝ := C_p / (c₀ * (n ! : ℝ))
  let C : ℝ := max C_head C_tail
  refine ⟨C, le_trans (by positivity) (le_max_left _ _), fun u hu => ?_⟩
  rcases le_or_gt u z₀ with hu_le | hu_gt
  · have hSn_lo : (n ! : ℝ)⁻¹ ≤ besselS n (u ^ 2 / 4) := by
      have h0 := besselS_mono n le_rfl (show (0 : ℝ) ≤ u ^ 2 / 4 by positivity)
      rwa [besselS_zero_arg, one_div] at h0
    have hSn_hi : besselS n ((r * u) ^ 2 / 4) ≤ Real.exp z₀ / (n ! : ℝ) := by
      refine (besselS_sq_div_four_le_exp n (mul_nonneg hr0 hu)).trans ?_
      exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
    have hnn : 0 ≤ besselS n ((r * u) ^ 2 / 4) := besselS_nonneg n (by positivity)
    have hS_nn : 0 ≤ besselS n (u ^ 2 / 4) := besselS_nonneg n (by positivity)
    calc u * besselS n ((r * u) ^ 2 / 4)
        ≤ z₀ * (Real.exp z₀ / (n ! : ℝ)) := mul_le_mul hu_le hSn_hi hnn (by linarith)
      _ = C_head * (n ! : ℝ)⁻¹ := by dsimp [C_head]; ring
      _ ≤ C_head * besselS n (u ^ 2 / 4) := mul_le_mul_of_nonneg_left hSn_lo (by dsimp [C_head]; positivity)
      _ ≤ C * besselS n (u ^ 2 / 4) := mul_le_mul_of_nonneg_right (le_max_left _ _) hS_nn
  · have hu_ge1 : 1 ≤ u := hz₀.trans hu_gt.le
    have hu_pos : 0 < u := by linarith
    have hlo := hbd u hu_gt.le
    have hhi : besselS n ((r * u) ^ 2 / 4) ≤ Real.exp (r * u) / (n ! : ℝ) :=
      besselS_sq_div_four_le_exp n (mul_nonneg hr0 hu)
    have hrpow_le : u * u ^ ((n : ℝ) + 1 / 2) ≤ u ^ (n + 2) := by
      have h1 : u ^ (1 / 2 : ℝ) ≤ u ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hu_ge1 (by norm_num)
      rw [Real.rpow_one] at h1
      have h2 : u ^ ((n : ℝ) + 1 / 2) = u ^ (n : ℝ) * u ^ (1 / 2 : ℝ) :=
        Real.rpow_add hu_pos n (1 / 2)
      rw [h2, Real.rpow_natCast]
      calc u * (u ^ n * u ^ (1 / 2 : ℝ)) ≤ u * (u ^ n * u) := by gcongr
        _ = u ^ (n + 2) := by ring
    have hpoly : u * u ^ ((n : ℝ) + 1 / 2) ≤ C_p * Real.exp (δ * u) :=
      hrpow_le.trans (hCp u hu)
    have hmain : u * (Real.exp (r * u) / (n ! : ℝ)) ≤
        C_tail * (c₀ * Real.exp u / u ^ ((n : ℝ) + 1 / 2)) := by
      have hden_pos : 0 < u ^ ((n : ℝ) + 1 / 2) := Real.rpow_pos_of_pos hu_pos _
      have hexp_eq : Real.exp (δ * u) * Real.exp (r * u) = Real.exp u := by
        rw [← Real.exp_add]; congr 1; dsimp [δ]; ring
      rw [div_mul_div_comm, mul_div_mul_comm]
      have hc₀_ne : c₀ ≠ 0 := hc₀.ne'
      have hn_ne : (n ! : ℝ) ≠ 0 := by positivity
      calc u * (Real.exp (r * u) / (n ! : ℝ))
          = (u * u ^ ((n : ℝ) + 1 / 2)) * Real.exp (r * u) / ((n ! : ℝ) * u ^ ((n : ℝ) + 1 / 2)) := by
            field_simp [hden_pos.ne']
        _ ≤ (C_p * Real.exp (δ * u)) * Real.exp (r * u) / ((n ! : ℝ) * u ^ ((n : ℝ) + 1 / 2)) := by
            gcongr
        _ = C_p * (Real.exp (δ * u) * Real.exp (r * u)) / ((n ! : ℝ) * u ^ ((n : ℝ) + 1 / 2)) := by
            ring
        _ = C_p * Real.exp u / ((n ! : ℝ) * u ^ ((n : ℝ) + 1 / 2)) := by rw [hexp_eq]
        _ = (C_p / (c₀ * (n ! : ℝ))) * (c₀ * Real.exp u / u ^ ((n : ℝ) + 1 / 2)) := by
            field_simp [hc₀_ne, hn_ne]
    have hS_nn : 0 ≤ besselS n (u ^ 2 / 4) := besselS_nonneg n (by positivity)
    calc u * besselS n ((r * u) ^ 2 / 4)
        ≤ u * (Real.exp (r * u) / (n ! : ℝ)) := by gcongr
      _ ≤ C_tail * (c₀ * Real.exp u / u ^ ((n : ℝ) + 1 / 2)) := hmain
      _ ≤ C_tail * besselS n (u ^ 2 / 4) := mul_le_mul_of_nonneg_left hlo (by dsimp [C_tail]; positivity)
      _ ≤ C * besselS n (u ^ 2 / 4) := mul_le_mul_of_nonneg_right (le_max_right _ _) hS_nn

/-! ### Section 4: Complex sector asymptotic for `besselIC n z` -/

private lemma one_sub_cos_nat_mul_le (n : ℕ) {θ : ℝ} (h0 : 0 ≤ θ) (hpi : θ ≤ Real.pi / 2) :
    |Real.cos (n * θ) - 1| ≤ (n : ℝ) ^ 2 * Real.pi ^ 2 / 4 * (√2 * Real.sin (θ / 2)) ^ 2 := by
  have h1 : 1 - Real.cos (n * θ) = 2 * Real.sin ((n : ℝ) * θ / 2) ^ 2 := by
    have hcos : Real.cos (n * θ) = Real.cos (2 * ((n : ℝ) * θ / 2)) := by ring_nf
    rw [hcos, Real.cos_two_mul]
    have := Real.cos_sq_add_sin_sq ((n : ℝ) * θ / 2)
    linarith
  have hsin_le : |Real.sin ((n : ℝ) * θ / 2)| ≤ (n : ℝ) * θ / 2 :=
    (Real.abs_sin_le_abs).trans_eq (abs_of_nonneg (by positivity))
  have hcos_le : |Real.cos (n * θ) - 1| ≤ (n : ℝ) ^ 2 * θ ^ 2 / 2 := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [Real.cos_le_one (n * θ)]), h1]
    have hsq : Real.sin ((n : ℝ) * θ / 2) ^ 2 ≤ ((n : ℝ) * θ / 2) ^ 2 := by
      rw [← sq_abs (Real.sin ((n : ℝ) * θ / 2))]
      exact pow_le_pow_left₀ (abs_nonneg _) hsin_le 2
    linarith [show 2 * ((n : ℝ) * θ / 2) ^ 2 = (n : ℝ) ^ 2 * θ ^ 2 / 2 by ring]
  have hjordan : θ ≤ Real.pi * Real.sin (θ / 2) := by
    have h := Real.mul_le_sin (by linarith : 0 ≤ θ / 2) (by linarith : θ / 2 ≤ Real.pi / 2)
    have hmul := mul_le_mul_of_nonneg_left h Real.pi_pos.le
    calc θ = Real.pi * (2 / Real.pi * (θ / 2)) := by field_simp [Real.pi_pos.ne']
      _ ≤ Real.pi * Real.sin (θ / 2) := hmul
  have hθ_sq : θ ^ 2 ≤ Real.pi ^ 2 / 2 * (√2 * Real.sin (θ / 2)) ^ 2 := by
    have h1' : θ ^ 2 ≤ (Real.pi * Real.sin (θ / 2)) ^ 2 :=
      pow_le_pow_left₀ h0 hjordan 2
    have h2' : (√2 * Real.sin (θ / 2)) ^ 2 = 2 * Real.sin (θ / 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt zero_le_two]
    rw [h2']
    calc θ ^ 2 ≤ (Real.pi * Real.sin (θ / 2)) ^ 2 := h1'
      _ = Real.pi ^ 2 / 2 * (2 * Real.sin (θ / 2) ^ 2) := by ring
  calc |Real.cos (n * θ) - 1| ≤ (n : ℝ) ^ 2 * θ ^ 2 / 2 := hcos_le
    _ ≤ (n : ℝ) ^ 2 * (Real.pi ^ 2 / 2 * (√2 * Real.sin (θ / 2)) ^ 2) / 2 := by gcongr
    _ = (n : ℝ) ^ 2 * Real.pi ^ 2 / 4 * (√2 * Real.sin (θ / 2)) ^ 2 := by ring

private lemma norm_besselIC_sub_besselI0C_le (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    ‖besselIC n z - besselI0C z‖ ≤
      (Real.exp z.re / Real.pi) *
        ((n : ℝ) ^ 2 * Real.pi ^ 2 * √Real.pi / (4 * z.re ^ (3 / 2 : ℝ)) +
          Real.pi * Real.exp (-z.re)) := by
  rw [besselIC_eq_integral n z, ← integration_besselI0C_eq_blowup]
  unfold Integration.besselI0C
  have hexp_ne : Complex.exp z ≠ 0 := Complex.exp_ne_zero z
  have hsub : ((Real.pi : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..Real.pi,
        Complex.exp (z * (Real.cos θ : ℝ)) * (Real.cos (n * θ) : ℝ)) -
      ((Real.pi : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..Real.pi, Complex.exp (z * (Real.cos θ : ℝ))) =
      (Complex.exp z / (Real.pi : ℂ)) *
        ∫ θ in (0 : ℝ)..Real.pi,
          Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) * ((Real.cos (n * θ) - 1 : ℝ) : ℂ) := by
    have h1 : IntervalIntegrable (fun θ : ℝ =>
        Complex.exp (z * (Real.cos θ : ℝ)) * (Real.cos (n * θ) : ℝ)) volume 0 Real.pi :=
      (by fun_prop : Continuous fun θ : ℝ =>
        Complex.exp (z * (Real.cos θ : ℝ)) * (Real.cos (n * θ) : ℝ)).intervalIntegrable 0 Real.pi
    have h2 : IntervalIntegrable (fun θ : ℝ => Complex.exp (z * (Real.cos θ : ℝ))) volume 0 Real.pi :=
      (by fun_prop : Continuous fun θ : ℝ =>
        Complex.exp (z * (Real.cos θ : ℝ))).intervalIntegrable 0 Real.pi
    calc ((Real.pi : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..Real.pi,
          Complex.exp (z * (Real.cos θ : ℝ)) * (Real.cos (n * θ) : ℝ)) -
        ((Real.pi : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..Real.pi, Complex.exp (z * (Real.cos θ : ℝ)))
        = (Real.pi : ℂ)⁻¹ * ((∫ θ in (0 : ℝ)..Real.pi,
            Complex.exp (z * (Real.cos θ : ℝ)) * (Real.cos (n * θ) : ℝ)) -
          (∫ θ in (0 : ℝ)..Real.pi, Complex.exp (z * (Real.cos θ : ℝ)))) := by ring
      _ = (Real.pi : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..Real.pi,
            (Complex.exp (z * (Real.cos θ : ℝ)) * (Real.cos (n * θ) : ℝ) -
              Complex.exp (z * (Real.cos θ : ℝ))) := by
          congr 1; exact (intervalIntegral.integral_sub h1 h2).symm
      _ = (Real.pi : ℂ)⁻¹ * (Complex.exp z * ∫ θ in (0 : ℝ)..Real.pi,
            Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) * ((Real.cos (n * θ) - 1 : ℝ) : ℂ)) := by
          congr 1
          rw [← intervalIntegral.integral_const_mul]
          refine intervalIntegral.integral_congr fun θ _ => ?_
          have hring : -z * ((1 - Real.cos θ : ℝ) : ℂ) = -z + z * (Real.cos θ : ℝ) := by
            push_cast; ring
          rw [← mul_assoc, hring, Complex.exp_add, ← mul_assoc, ← Complex.exp_add, add_neg_cancel,
            Complex.exp_zero, one_mul]
          push_cast; ring
      _ = (Complex.exp z / (Real.pi : ℂ)) * ∫ θ in (0 : ℝ)..Real.pi,
            Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) * ((Real.cos (n * θ) - 1 : ℝ) : ℂ) := by
          ring
  rw [hsub, norm_mul, norm_div, Complex.norm_exp, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hc_int : Continuous fun θ : ℝ =>
      Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) * ((Real.cos (n * θ) - 1 : ℝ) : ℂ) := by
    fun_prop
  have hsplit : ∫ θ in (0 : ℝ)..Real.pi,
        Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) * ((Real.cos (n * θ) - 1 : ℝ) : ℂ) =
      (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) * ((Real.cos (n * θ) - 1 : ℝ) : ℂ)) +
      (∫ θ in (Real.pi / 2)..Real.pi,
        Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) * ((Real.cos (n * θ) - 1 : ℝ) : ℂ)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hc_int.intervalIntegrable _ _) (hc_int.intervalIntegrable _ _)).symm
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · -- `[0, π / 2]` piece via `t = √2 sin(θ / 2)`
    let f : ℝ → ℝ := fun θ => √2 * Real.sin (θ / 2)
    let f' : ℝ → ℝ := fun θ => (√2 / 2) * Real.cos (θ / 2)
    have hbd_theta : ∀ θ ∈ Ioc (0 : ℝ) (Real.pi / 2),
        ‖Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) * ((Real.cos (n * θ) - 1 : ℝ) : ℂ)‖ ≤
          ((n : ℝ) ^ 2 * Real.pi ^ 2 / 4) *
            (Real.exp (-z.re * (f θ) ^ 2) * (f θ) ^ 2) := fun θ hθ => by
      have hf_sq : (f θ) ^ 2 = 1 - Real.cos θ := by
        dsimp [f]; rw [mul_pow, Real.sq_sqrt zero_le_two]
        have hcos := Real.cos_sq (θ / 2)
        have hsin := Real.sin_sq_add_cos_sq (θ / 2)
        rw [show 2 * (θ / 2) = θ by ring] at hcos
        linarith
      rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
      have hre : (-z * ((1 - Real.cos θ : ℝ) : ℂ)).re = -z.re * (f θ) ^ 2 := by
        rw [hf_sq, neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero, neg_mul]
      rw [hre]
      have hcos_bd := one_sub_cos_nat_mul_le n hθ.1.le hθ.2
      calc Real.exp (-z.re * (f θ) ^ 2) * |Real.cos (n * θ) - 1|
          ≤ Real.exp (-z.re * (f θ) ^ 2) *
              ((n : ℝ) ^ 2 * Real.pi ^ 2 / 4 * (f θ) ^ 2) := by
            gcongr
        _ = ((n : ℝ) ^ 2 * Real.pi ^ 2 / 4) * (Real.exp (-z.re * (f θ) ^ 2) * (f θ) ^ 2) := by
            ring
    have hint1 : ‖∫ θ in (0 : ℝ)..(Real.pi / 2),
        Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) * ((Real.cos (n * θ) - 1 : ℝ) : ℂ)‖ ≤
        ((n : ℝ) ^ 2 * Real.pi ^ 2 / 4) *
          ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp (-z.re * (f θ) ^ 2) * (f θ) ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.norm_integral_le_of_norm_le (by positivity) ?_
        ((by fun_prop : Continuous fun θ : ℝ => ((n : ℝ) ^ 2 * Real.pi ^ 2 / 4) *
          (Real.exp (-z.re * (f θ) ^ 2) * (f θ) ^ 2)).intervalIntegrable _ _)
      exact Eventually.of_forall hbd_theta
    have hcov : ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp (-z.re * (f θ) ^ 2) * (f θ) ^ 2 ≤
        2 * ∫ t in (0 : ℝ)..1, t ^ 2 * Real.exp (-z.re * t ^ 2) := by
      have hderiv : ∀ θ ∈ uIcc (0 : ℝ) (Real.pi / 2), HasDerivAt f (f' θ) θ := fun θ _ => by
        have h1 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) θ := (hasDerivAt_id θ).div_const 2
        exact ((h1.sin).const_mul √2).congr_deriv (by dsimp [f']; ring)
      let g : ℝ → ℝ := fun t =>
        (Real.exp (-z.re * t ^ 2) * t ^ 2) * (√2 / √(1 - t ^ 2 / 2))
      have himg : f '' uIcc (0 : ℝ) (Real.pi / 2) ⊆ Icc 0 1 := by
        rintro t ⟨θ, hθ, rfl⟩
        rw [uIcc_of_le (by positivity)] at hθ
        have hsin_nn : 0 ≤ Real.sin (θ / 2) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
        have hsin_le : Real.sin (θ / 2) ≤ Real.sin (Real.pi / 4) :=
          Real.strictMonoOn_sin.monotoneOn
            ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
            ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (by linarith [hθ.2])
        rw [Real.sin_pi_div_four] at hsin_le
        refine ⟨mul_nonneg (Real.sqrt_nonneg _) hsin_nn, ?_⟩
        calc √2 * Real.sin (θ / 2) ≤ √2 * (√2 / 2) := by gcongr
          _ = 1 := by rw [← mul_div_assoc, Real.mul_self_sqrt zero_le_two]; norm_num
      have hg_cont : ContinuousOn g (f '' uIcc (0 : ℝ) (Real.pi / 2)) := by
        refine ContinuousOn.mono ?_ himg
        intro t ht
        have hpos : 0 < 1 - t ^ 2 / 2 := by nlinarith [ht.1, ht.2]
        refine ContinuousAt.continuousWithinAt ?_
        have h1 : ContinuousAt (fun s : ℝ => Real.exp (-z.re * s ^ 2) * s ^ 2) t := by fun_prop
        have h2 : ContinuousAt (fun s : ℝ => √2 / √(1 - s ^ 2 / 2)) t :=
          continuousAt_const.div ((Real.continuous_sqrt.continuousAt.comp
            (by fun_prop : Continuous fun s : ℝ => 1 - s ^ 2 / 2).continuousAt))
            (Real.sqrt_ne_zero'.mpr hpos)
        exact h1.mul h2
      have hcomp := intervalIntegral.integral_deriv_smul_comp' hderiv
        (by fun_prop : Continuous f').continuousOn hg_cont
      have hf0 : f 0 = 0 := by simp [f]
      have hfpi : f (Real.pi / 2) = 1 := by
        dsimp [f]; rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring, Real.sin_pi_div_four,
          ← mul_div_assoc, Real.mul_self_sqrt zero_le_two]; norm_num
      rw [hf0, hfpi] at hcomp
      have heq_f : ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp (-z.re * (f θ) ^ 2) * (f θ) ^ 2 =
          ∫ t in (0 : ℝ)..1, g t := by
        rw [← hcomp]
        refine intervalIntegral.integral_congr fun θ hθ => ?_
        rw [uIcc_of_le (by positivity)] at hθ
        have hcos_pos : 0 < Real.cos (θ / 2) :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
        have hf_sq : f θ ^ 2 = 1 - Real.cos θ := by
          dsimp [f]; rw [mul_pow, Real.sq_sqrt zero_le_two]
          have hcos := Real.cos_sq (θ / 2)
          have hsin := Real.sin_sq_add_cos_sq (θ / 2)
          rw [show 2 * (θ / 2) = θ by ring] at hcos; linarith
        have hsqrt_eq : √(1 - f θ ^ 2 / 2) = Real.cos (θ / 2) := by
          rw [hf_sq, show 1 - (1 - Real.cos θ) / 2 = (1 + Real.cos θ) / 2 by ring]
          have hcos_half : Real.cos (θ / 2) ^ 2 = (1 + Real.cos θ) / 2 := by
            have := Real.cos_sq (θ / 2)
            rw [show 2 * (θ / 2) = θ by ring] at this; linarith
          rw [← hcos_half, Real.sqrt_sq hcos_pos.le]
        dsimp [g, f']
        rw [hsqrt_eq]
        have hcos_ne : Real.cos (θ / 2) ≠ 0 := hcos_pos.ne'
        have h2sq : √2 * √2 = 2 := Real.mul_self_sqrt zero_le_two
        field_simp [hcos_ne]
        nlinarith [h2sq]
      rw [heq_f, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on zero_le_one ?_
        ((by fun_prop : Continuous fun t : ℝ => 2 * (t ^ 2 * Real.exp (-z.re * t ^ 2))).intervalIntegrable 0 1)
        fun t ht => ?_
      · refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le zero_le_one]
        intro t ht'
        have hpos : 0 < 1 - t ^ 2 / 2 := by nlinarith [ht'.1, ht'.2]
        exact (ContinuousAt.mul (by fun_prop) (continuousAt_const.div
          (Real.continuous_sqrt.continuousAt.comp
            (continuousAt_const.sub ((continuousAt_id.pow 2).div_const 2)))
          (Real.sqrt_ne_zero'.mpr hpos))).continuousWithinAt
      · dsimp [g]
        have hden : (1 / √2 : ℝ) ≤ √(1 - t ^ 2 / 2) := by
          have h12 : (1 / √2 : ℝ) = √(1 / 2 : ℝ) := by
            rw [Real.sqrt_div zero_le_one, Real.sqrt_one]
          rw [h12]
          exact Real.sqrt_le_sqrt (by nlinarith [ht.1, ht.2])
        have hfac : √2 / √(1 - t ^ 2 / 2) ≤ 2 := by
          rw [div_le_iff₀ (Real.sqrt_pos.mpr (by nlinarith [ht.1, ht.2]))]
          calc √2 = 2 * (1 / √2) := by
                have : √2 * √2 = 2 := Real.mul_self_sqrt zero_le_two
                field_simp [(Real.sqrt_pos.mpr zero_lt_two).ne']; linarith
            _ ≤ 2 * √(1 - t ^ 2 / 2) := by gcongr
        calc (Real.exp (-z.re * t ^ 2) * t ^ 2) * (√2 / √(1 - t ^ 2 / 2))
            ≤ (Real.exp (-z.re * t ^ 2) * t ^ 2) * 2 := by gcongr
          _ = 2 * (t ^ 2 * Real.exp (-z.re * t ^ 2)) := by ring
    have hmom : ∫ t in (0 : ℝ)..1, t ^ 2 * Real.exp (-z.re * t ^ 2) ≤
        √Real.pi / (4 * z.re ^ (3 / 2 : ℝ)) := by
      have h1 := Bessel.moment_succ_succ_le hz 0
      simp only [pow_zero, one_mul, Nat.cast_zero, zero_add] at h1
      have h2 := Bessel.gauss_interval_le hz zero_le_one
      have hrpow : √(Real.pi / z.re) / (4 * z.re) = √Real.pi / (4 * z.re ^ (3 / 2 : ℝ)) := by
        rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_eq_rpow]
        have hz_rpow : z.re ^ (3 / 2 : ℝ) = z.re ^ (1 / 2 : ℝ) * z.re := by
          calc z.re ^ (3 / 2 : ℝ) = z.re ^ (1 / 2 + 1 : ℝ) := by norm_num
            _ = z.re ^ (1 / 2 : ℝ) * z.re ^ (1 : ℝ) := Real.rpow_add hz _ _
            _ = z.re ^ (1 / 2 : ℝ) * z.re := by rw [Real.rpow_one]
        rw [hz_rpow, Real.sqrt_eq_rpow]
        field_simp [hz.ne', (Real.rpow_pos_of_pos hz _).ne']
      calc ∫ t in (0 : ℝ)..1, t ^ 2 * Real.exp (-z.re * t ^ 2)
          ≤ 1 / (2 * z.re) * ∫ t in (0 : ℝ)..1, Real.exp (-z.re * t ^ 2) := h1
        _ ≤ 1 / (2 * z.re) * (√(Real.pi / z.re) / 2) := by gcongr
        _ = √(Real.pi / z.re) / (4 * z.re) := by ring
        _ = √Real.pi / (4 * z.re ^ (3 / 2 : ℝ)) := hrpow
    calc ‖∫ θ in (0 : ℝ)..(Real.pi / 2),
          Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) * ((Real.cos (n * θ) - 1 : ℝ) : ℂ)‖
        ≤ ((n : ℝ) ^ 2 * Real.pi ^ 2 / 4) *
            ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp (-z.re * (f θ) ^ 2) * (f θ) ^ 2 := hint1
      _ ≤ ((n : ℝ) ^ 2 * Real.pi ^ 2 / 4) *
            (2 * ∫ t in (0 : ℝ)..1, t ^ 2 * Real.exp (-z.re * t ^ 2)) := by gcongr
      _ ≤ ((n : ℝ) ^ 2 * Real.pi ^ 2 / 4) * (2 * (√Real.pi / (4 * z.re ^ (3 / 2 : ℝ)))) := by
            gcongr
      _ = (n : ℝ) ^ 2 * Real.pi ^ 2 * √Real.pi / (8 * z.re ^ (3 / 2 : ℝ)) := by ring
      _ ≤ (n : ℝ) ^ 2 * Real.pi ^ 2 * √Real.pi / (4 * z.re ^ (3 / 2 : ℝ)) := by
            gcongr; norm_num
  · -- `[π / 2, π]` tail
    have hle_pi : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
    have hbd : ∀ θ ∈ Ioc (Real.pi / 2) Real.pi,
        ‖Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) * ((Real.cos (n * θ) - 1 : ℝ) : ℂ)‖ ≤
          2 * Real.exp (-z.re) := fun θ hθ => by
      rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
      have hre : (-z * ((1 - Real.cos θ : ℝ) : ℂ)).re = -z.re * (1 - Real.cos θ) := by
        rw [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero, neg_mul]
      rw [hre]
      have hcos_nonpos : Real.cos θ ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1.le (by linarith [hθ.2, Real.pi_pos])
      have hexp : Real.exp (-z.re * (1 - Real.cos θ)) ≤ Real.exp (-z.re) :=
        Real.exp_le_exp.mpr (by nlinarith [hz])
      have hdiff : |Real.cos (n * θ) - 1| ≤ 2 := by
        have := Real.cos_le_one (n * θ)
        have := Real.neg_one_le_cos (n * θ)
        rw [abs_le]; constructor <;> linarith
      calc Real.exp (-z.re * (1 - Real.cos θ)) * |Real.cos (n * θ) - 1|
          ≤ Real.exp (-z.re) * 2 := mul_le_mul hexp hdiff (abs_nonneg _) (Real.exp_pos _).le
        _ = 2 * Real.exp (-z.re) := by ring
    have hint := intervalIntegral.norm_integral_le_of_norm_le hle_pi
      (Eventually.of_forall hbd) (intervalIntegrable_const (μ := volume))
    rw [intervalIntegral.integral_const, smul_eq_mul] at hint
    refine hint.trans_eq ?_
    ring

/-- Quantitative complex sector asymptotic for `I_n(z)` (`n : ℕ`) on
`{z : ℂ | 0 < z.re ∧ κ * ‖z‖ ≤ z.re}` (`0 < κ`), reusing `besselI0C_sector_asymptotic_of_re_pos`. -/
theorem besselIC_sector_asymptotic_of_re_pos (n : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 0 < z.re → κ * ‖z‖ ≤ z.re →
      ‖besselIC n z - asC z‖ ≤ (C / ‖z‖) * ‖asC z‖ := by
  obtain ⟨C₀, hC₀_nn, hI₀⟩ := besselI0C_sector_asymptotic_of_re_pos hκ
  let C_n : ℝ := ((n : ℝ) ^ 2 * Real.pi ^ 2 * √2 / 4 + 2 * √(2 * Real.pi)) / κ ^ (3 / 2 : ℝ)
  refine ⟨C₀ + C_n, by positivity, fun z hz_pos hsec => ?_⟩
  have hnorm_pos : 0 < ‖z‖ := lt_of_lt_of_le hz_pos (Complex.re_le_norm z)
  have h0 := hI₀ z hz_pos hsec
  have hdiff := norm_besselIC_sub_besselI0C_le n hz_pos
  have has_norm : ‖asC z‖ = Real.exp z.re / √(2 * Real.pi * ‖z‖) := by
    unfold asC
    have hz_ne : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz_pos; exact lt_irrefl 0 hz_pos
    have h2piz_ne : 2 * (Real.pi : ℂ) * z ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) hz_ne
    have hcpow_norm : ‖(2 * (Real.pi : ℂ) * z) ^ (1 / 2 : ℂ)‖ = √(2 * Real.pi * ‖z‖) := by
      rw [Complex.cpow_def_of_ne_zero h2piz_ne, Complex.norm_exp]
      have hre : (Complex.log (2 * (Real.pi : ℂ) * z) * (1 / 2 : ℂ)).re =
          Real.log (2 * Real.pi * ‖z‖) / 2 := by
        rw [Complex.mul_re, Complex.log_re, show (1 / 2 : ℂ).re = 1 / 2 by norm_num,
          show (1 / 2 : ℂ).im = 0 by norm_num, mul_zero, sub_zero, norm_mul, norm_mul,
          Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
        ring
      rw [hre, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
      congr 1; ring
    rw [norm_div, Complex.norm_exp, hcpow_norm]
  have has_eq : Real.exp z.re / Real.pi = √(2 * Real.pi * ‖z‖) / Real.pi * ‖asC z‖ := by
    rw [has_norm]
    have hs_ne : √(2 * Real.pi * ‖z‖) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp [hs_ne, Real.pi_pos.ne']
  have hexp_three_halves : Real.exp (-z.re) ≤ 2 / z.re ^ (3 / 2 : ℝ) := by
    have h1 : z.re ^ (3 / 2 : ℝ) ≤ 2 * Real.exp z.re := by
      rcases le_or_gt z.re 1 with hle | hgt
      · have hr : z.re ^ (3 / 2 : ℝ) ≤ 1 := by
          calc z.re ^ (3 / 2 : ℝ) ≤ 1 ^ (3 / 2 : ℝ) := Real.rpow_le_rpow hz_pos.le hle (by norm_num)
            _ = 1 := Real.one_rpow _
        linarith [Real.one_le_exp hz_pos.le]
      · have hr : z.re ^ (3 / 2 : ℝ) ≤ z.re ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hgt.le (by norm_num)
        rw [Real.rpow_two] at hr
        linarith [Real.quadratic_le_exp_of_nonneg hz_pos.le]
    have h2 : Real.exp z.re * Real.exp (-z.re) = 1 := by rw [← Real.exp_add]; simp
    have h3 : z.re ^ (3 / 2 : ℝ) * Real.exp (-z.re) ≤ 2 := by
      have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-z.re)).le
      linarith
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hz_pos _)]; linarith
  have hzr_pow : κ ^ (3 / 2 : ℝ) * ‖z‖ ^ (3 / 2 : ℝ) ≤ z.re ^ (3 / 2 : ℝ) := by
    rw [← Real.mul_rpow hκ.le (norm_nonneg z)]
    exact Real.rpow_le_rpow (by positivity) hsec (by norm_num)
  have hz_12_32 : ‖z‖ ^ (1 / 2 : ℝ) / ‖z‖ ^ (3 / 2 : ℝ) = 1 / ‖z‖ := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hnorm_pos, Real.rpow_one]
    have h12 : ‖z‖ ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hnorm_pos _).ne'
    field_simp [h12, hnorm_pos.ne']
  have hz_ratio : ‖z‖ ^ (1 / 2 : ℝ) / z.re ^ (3 / 2 : ℝ) ≤ 1 / (κ ^ (3 / 2 : ℝ) * ‖z‖) := by
    calc ‖z‖ ^ (1 / 2 : ℝ) / z.re ^ (3 / 2 : ℝ)
        ≤ ‖z‖ ^ (1 / 2 : ℝ) / (κ ^ (3 / 2 : ℝ) * ‖z‖ ^ (3 / 2 : ℝ)) := by gcongr
      _ = (‖z‖ ^ (1 / 2 : ℝ) / ‖z‖ ^ (3 / 2 : ℝ)) / κ ^ (3 / 2 : ℝ) := by ring
      _ = 1 / (κ ^ (3 / 2 : ℝ) * ‖z‖) := by rw [hz_12_32]; ring
  have hscale_eq : √(2 * Real.pi * ‖z‖) / Real.pi = √2 * ‖z‖ ^ (1 / 2 : ℝ) / √Real.pi := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul zero_le_two]
    have hp : √Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
    have hp_ne : √Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    field_simp [hp_ne, Real.pi_pos.ne']
    rw [← Real.sqrt_eq_rpow]
    rw [hp]
  have hpiece : √(2 * Real.pi * ‖z‖) / Real.pi *
      ((n : ℝ) ^ 2 * Real.pi ^ 2 * √Real.pi / (4 * z.re ^ (3 / 2 : ℝ)) +
        Real.pi * Real.exp (-z.re)) ≤ C_n / ‖z‖ := by
    rw [hscale_eq]
    have hp_ne : √Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hpi_sq : Real.pi / √Real.pi = √Real.pi := by
      have hp : √Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
      field_simp [hp_ne]; exact hp.symm
    have ht1 : √2 * ‖z‖ ^ (1 / 2 : ℝ) / √Real.pi *
        ((n : ℝ) ^ 2 * Real.pi ^ 2 * √Real.pi / (4 * z.re ^ (3 / 2 : ℝ))) ≤
        ((n : ℝ) ^ 2 * Real.pi ^ 2 * √2 / 4 / κ ^ (3 / 2 : ℝ)) / ‖z‖ := by
      have heq : √2 * ‖z‖ ^ (1 / 2 : ℝ) / √Real.pi *
          ((n : ℝ) ^ 2 * Real.pi ^ 2 * √Real.pi / (4 * z.re ^ (3 / 2 : ℝ))) =
          ((n : ℝ) ^ 2 * Real.pi ^ 2 * √2 / 4) * (‖z‖ ^ (1 / 2 : ℝ) / z.re ^ (3 / 2 : ℝ)) := by
        field_simp [hp_ne]
      rw [heq]
      calc ((n : ℝ) ^ 2 * Real.pi ^ 2 * √2 / 4) * (‖z‖ ^ (1 / 2 : ℝ) / z.re ^ (3 / 2 : ℝ))
          ≤ ((n : ℝ) ^ 2 * Real.pi ^ 2 * √2 / 4) * (1 / (κ ^ (3 / 2 : ℝ) * ‖z‖)) := by gcongr
        _ = ((n : ℝ) ^ 2 * Real.pi ^ 2 * √2 / 4 / κ ^ (3 / 2 : ℝ)) / ‖z‖ := by ring
    have ht2 : √2 * ‖z‖ ^ (1 / 2 : ℝ) / √Real.pi * (Real.pi * Real.exp (-z.re)) ≤
        (2 * √(2 * Real.pi) / κ ^ (3 / 2 : ℝ)) / ‖z‖ := by
      have h1 : √2 * ‖z‖ ^ (1 / 2 : ℝ) / √Real.pi * (Real.pi * Real.exp (-z.re)) =
          √(2 * Real.pi) * (‖z‖ ^ (1 / 2 : ℝ) * Real.exp (-z.re)) := by
        rw [Real.sqrt_mul zero_le_two]
        calc √2 * ‖z‖ ^ (1 / 2 : ℝ) / √Real.pi * (Real.pi * Real.exp (-z.re))
            = √2 * (Real.pi / √Real.pi) * (‖z‖ ^ (1 / 2 : ℝ) * Real.exp (-z.re)) := by ring
          _ = √2 * √Real.pi * (‖z‖ ^ (1 / 2 : ℝ) * Real.exp (-z.re)) := by rw [hpi_sq]
      rw [h1]
      calc √(2 * Real.pi) * (‖z‖ ^ (1 / 2 : ℝ) * Real.exp (-z.re))
          ≤ √(2 * Real.pi) * (‖z‖ ^ (1 / 2 : ℝ) * (2 / z.re ^ (3 / 2 : ℝ))) := by gcongr
        _ = 2 * √(2 * Real.pi) * (‖z‖ ^ (1 / 2 : ℝ) / z.re ^ (3 / 2 : ℝ)) := by ring
        _ ≤ 2 * √(2 * Real.pi) * (1 / (κ ^ (3 / 2 : ℝ) * ‖z‖)) := by gcongr
        _ = (2 * √(2 * Real.pi) / κ ^ (3 / 2 : ℝ)) / ‖z‖ := by ring
    rw [mul_add]
    calc _ ≤ ((n : ℝ) ^ 2 * Real.pi ^ 2 * √2 / 4 / κ ^ (3 / 2 : ℝ)) / ‖z‖ +
            (2 * √(2 * Real.pi) / κ ^ (3 / 2 : ℝ)) / ‖z‖ := add_le_add ht1 ht2
      _ = C_n / ‖z‖ := by dsimp [C_n]; ring
  have hdiff_bd : ‖besselIC n z - besselI0C z‖ ≤ (C_n / ‖z‖) * ‖asC z‖ := by
    calc ‖besselIC n z - besselI0C z‖
        ≤ (Real.exp z.re / Real.pi) *
            ((n : ℝ) ^ 2 * Real.pi ^ 2 * √Real.pi / (4 * z.re ^ (3 / 2 : ℝ)) +
              Real.pi * Real.exp (-z.re)) := hdiff
      _ = (√(2 * Real.pi * ‖z‖) / Real.pi *
            ((n : ℝ) ^ 2 * Real.pi ^ 2 * √Real.pi / (4 * z.re ^ (3 / 2 : ℝ)) +
              Real.pi * Real.exp (-z.re))) * ‖asC z‖ := by
          rw [has_eq]; ring
      _ ≤ (C_n / ‖z‖) * ‖asC z‖ := mul_le_mul_of_nonneg_right hpiece (norm_nonneg _)
  calc ‖besselIC n z - asC z‖
      = ‖(besselIC n z - besselI0C z) + (besselI0C z - asC z)‖ := by ring_nf
    _ ≤ ‖besselIC n z - besselI0C z‖ + ‖besselI0C z - asC z‖ := norm_add_le _ _
    _ ≤ (C_n / ‖z‖) * ‖asC z‖ + (C₀ / ‖z‖) * ‖asC z‖ := add_le_add hdiff_bd h0
    _ = ((C₀ + C_n) / ‖z‖) * ‖asC z‖ := by ring

/-- **Complex sector asymptotic of `I_n`** (`n1_super_virasoro.tex`, Lemma 4(f) proof):
uniformly in every closed sector `|arg z| ≤ π/2 - ε` (`0 < ε < π/2`),
`I_n(z) = e^z / √(2πz) · (1 + O_{n, ε}(1 / |z|))`. -/
theorem besselIC_sector_asymptotic (n : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z ≠ 0 → |z.arg| ≤ Real.pi / 2 - ε →
      ‖besselIC n z - asC z‖ ≤ (C / ‖z‖) * ‖asC z‖ := by
  have hsin_pos : 0 < Real.sin ε := Real.sin_pos_of_pos_of_lt_pi hε0 (by linarith [Real.pi_pos])
  obtain ⟨C, hC_nn, hbd⟩ := besselIC_sector_asymptotic_of_re_pos n hsin_pos
  refine ⟨C, hC_nn, fun z hz harg => ?_⟩
  have hcos_ge : Real.sin ε ≤ Real.cos z.arg := by
    have h1 : Real.cos (Real.pi / 2 - ε) ≤ Real.cos (|z.arg|) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) harg
    rwa [Real.cos_pi_div_two_sub, Real.cos_abs] at h1
  have hre_eq : z.re = ‖z‖ * Real.cos z.arg := by
    have := Complex.cos_arg hz
    rw [this]; field_simp [(norm_pos_iff.mpr hz).ne']
  have hsec : Real.sin ε * ‖z‖ ≤ z.re := by
    rw [hre_eq]
    nlinarith [norm_nonneg z]
  have hz_pos : 0 < z.re := lt_of_lt_of_le (mul_pos hsin_pos (norm_pos_iff.mpr hz)) hsec
  exact hbd z hz_pos hsec

/-- **Real large-argument asymptotic of `I_n`** (`n : ℕ`) as a direct corollary of
`besselIC_sector_asymptotic_of_re_pos`: `|I_n(x) / as(x) - 1| ≤ C_n / x` for all `x > 0`. -/
theorem besselI_asymptotic_real (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {x : ℝ}, 0 < x →
      |besselI n x / besselAs x - 1| ≤ C / x := by
  obtain ⟨C, hC_nn, hbd⟩ := besselIC_sector_asymptotic_of_re_pos n (κ := 1) zero_lt_one
  refine ⟨C, hC_nn, fun {x} hx => ?_⟩
  have h1 := hbd (x : ℂ) (by simpa using hx) (by simp [abs_of_pos hx])
  have hI : besselIC n (x : ℂ) = (besselI n x : ℂ) := besselIC_ofReal n x
  have hAs : asC (x : ℂ) = (besselAs x : ℂ) := by
    unfold asC besselAs
    rw [← Complex.ofReal_exp, show 2 * (Real.pi : ℂ) * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) by
      push_cast; ring, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow]
    push_cast; rfl
  have hAs_pos : 0 < besselAs x := besselAs_pos hx
  rw [hI, hAs, ← Complex.ofReal_sub] at h1
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hAs_pos, abs_of_pos hx] at h1
  rw [show besselI n x / besselAs x - 1 = (besselI n x - besselAs x) / besselAs x by
    field_simp [hAs_pos.ne'], abs_div, abs_of_pos hAs_pos, div_le_iff₀ hAs_pos]
  exact h1

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.besselIC_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselIC_eq_integral

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.besselSC_eq_sin_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselSC_eq_sin_integral

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.besselIC_sector_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselIC_sector_asymptotic

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.besselI_asymptotic_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselI_asymptotic_real

end FormalResearch.ModularBootstrap.WeightAxioms
