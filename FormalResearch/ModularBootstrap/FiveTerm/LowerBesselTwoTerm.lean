module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import FormalResearch.ModularBootstrap.Integration.StripKernel

/-!
# Two-term complex Laplace asymptotic of `I₀` (FIVE-L, Lemma C5(2), step 1)

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, proof of Lemma C5 (`cts:edge-hankel`)(2):
DLMF 10.40.1 `I₀(w) = e^w/√(2πw) (1 + 1/(8w) + O(w^{-2}))`, here for *complex* `w` with `Re w ≥ 1` and with
a quantitative remainder.  `besselI0C_sector_asymptotic` has the leading term only.

* `rotate_ray`: Cauchy rotation of the ray `[0,R]` to `[0,R e^{-iβ}]` inside a disc (primitives on balls);
* `psiC`, `psiC_taylor`: `Ψ(u) = (1 - u²/2)^{-1/2}` holomorphic on `|u| < √2` with `|Ψ - 1 - u²/4| ≤ (3/4)|u|⁴` on `|u| ≤ 1`;
* `laplaceA_bound`: `A(w) = ∫₀¹ e^{-w r²} Ψ(r) dr = (√π/2) w^{-1/2}(1 + 1/(8w)) + O(|w|^{-5/2} + e^{-Re w})`,
  rotating to the steepest ray `arg r = -arg w / 2` and using Gaussian moments;
* `besselI0C_two_term`: `‖I₀(w) - e^w/√(2πw)(1 + 1/(8w))‖ ≤ 70 e^{Re w} |w|^{-5/2} + 2` for `Re w ≥ 1`,
  by the chord substitution `t = √2 sin(θ/2)` (copy of the private lemma in `BesselI0Sector`).

Proved, unconditional.  The additive `2` is the cut at `θ = π/2` (relative size `e^{-Re w}`); it is the reason
the downstream form of `cts:edge-asymp` is stated for `v ≤ e^{κc'}`.
-/

@[expose] public section

open MeasureTheory intervalIntegral Set Metric
open Complex hiding exp_re
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

noncomputable section

/-- **Contour rotation inside a disc.**  For `f` holomorphic on `ball 0 ρ`, `0 < R < ρ` and a real angle `β`:
`∫₀^R f(s) ds = e^{-iβ} ∫₀^R f(s e^{-iβ}) ds + ∫_β^0 f(R e^{-iγ}) (-i R e^{-iγ}) dγ`
(the last term is the integral over the circular arc from `R e^{-iβ}` back to `R`). -/
theorem rotate_ray {f : ℂ → ℂ} {ρ R : ℝ} (hf : DifferentiableOn ℂ f (ball 0 ρ)) (hR0 : 0 < R)
    (hRρ : R < ρ) (β : ℝ) :
    ∫ s : ℝ in (0:ℝ)..R, f (s : ℂ) =
      Complex.exp (-(β * I)) * (∫ s : ℝ in (0:ℝ)..R, f ((s : ℂ) * Complex.exp (-(β * I)))) +
      ∫ γ : ℝ in β..0, f ((R : ℂ) * Complex.exp (-(γ * I))) * (-I * R * Complex.exp (-(γ * I))) := by
  obtain ⟨F, hF⟩ := hf.isExactOn_ball
  have hb : ∀ z : ℂ, ‖z‖ ≤ R → z ∈ ball (0:ℂ) ρ := fun z hz => by
    rw [mem_ball_zero_iff]; exact lt_of_le_of_lt hz hRρ
  have hnorm : ∀ γ : ℝ, ‖Complex.exp (-(γ * I))‖ = 1 := fun γ => by
    rw [Complex.norm_exp]; simp
  have hcont : ContinuousOn f (ball 0 ρ) := hf.continuousOn
  -- real segment
  have h1 : ∫ s : ℝ in (0:ℝ)..R, f (s : ℂ) = F R - F 0 := by
    refine integral_eq_sub_of_hasDerivAt (f := fun s : ℝ => F (s : ℂ)) (fun s hs => ?_) ?_
    · rw [uIcc_of_le hR0.le] at hs
      have hm : (s : ℂ) ∈ ball (0:ℂ) ρ := hb _ (by simp [abs_of_nonneg hs.1, hs.2])
      exact (hF _ hm).comp_ofReal
    · apply ContinuousOn.intervalIntegrable
      exact hcont.comp Complex.continuous_ofReal.continuousOn (fun s hs => by
        rw [uIcc_of_le hR0.le] at hs
        exact hb _ (by simp [abs_of_nonneg hs.1, hs.2]))
  -- rotated ray
  have h2 : Complex.exp (-(β * I)) * (∫ s : ℝ in (0:ℝ)..R, f ((s : ℂ) * Complex.exp (-(β * I)))) =
      F (R * Complex.exp (-(β * I))) - F 0 := by
    rw [← intervalIntegral.integral_const_mul]
    have := integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => F ((s : ℂ) * Complex.exp (-(β * I))))
      (f' := fun s : ℝ => Complex.exp (-(β * I)) * f ((s : ℂ) * Complex.exp (-(β * I))))
      (a := 0) (b := R) (fun s hs => ?_) ?_
    · simpa using this
    · rw [uIcc_of_le hR0.le] at hs
      have hm : (s : ℂ) * Complex.exp (-(β * I)) ∈ ball (0:ℂ) ρ := hb _ (by
        rw [norm_mul, hnorm, Complex.norm_real]; simpa [abs_of_nonneg hs.1] using hs.2)
      have h3 : HasDerivAt (fun z : ℂ => z * Complex.exp (-(β * I))) (Complex.exp (-(β * I))) (s : ℂ) := by
        simpa using (hasDerivAt_id (s : ℂ)).mul_const (Complex.exp (-(β * I)))
      have h4 := (hF _ hm).comp (s : ℂ) h3
      have h5 := HasDerivAt.comp_ofReal (e := fun z : ℂ => F (z * Complex.exp (-(β * I)))) (z := s) h4
      simpa [mul_comm] using h5
    · apply ContinuousOn.intervalIntegrable
      refine continuousOn_const.mul (hcont.comp (by fun_prop : Continuous fun s : ℝ => (s : ℂ) * Complex.exp (-(β * I))).continuousOn (fun s hs => ?_))
      rw [uIcc_of_le hR0.le] at hs
      exact hb _ (by rw [norm_mul, hnorm, Complex.norm_real]; simpa [abs_of_nonneg hs.1] using hs.2)
  -- arc
  have h3 : ∫ γ : ℝ in β..0, f ((R : ℂ) * Complex.exp (-(γ * I))) * (-I * R * Complex.exp (-(γ * I))) =
      F R - F (R * Complex.exp (-(β * I))) := by
    have hm : ∀ γ : ℝ, (R : ℂ) * Complex.exp (-(γ * I)) ∈ ball (0:ℂ) ρ := fun γ => hb _ (by
      rw [norm_mul, hnorm, Complex.norm_real]; simp [abs_of_pos hR0])
    have := integral_eq_sub_of_hasDerivAt
      (f := fun γ : ℝ => F ((R : ℂ) * Complex.exp (-(γ * I))))
      (f' := fun γ : ℝ => f ((R : ℂ) * Complex.exp (-(γ * I))) * (-I * R * Complex.exp (-(γ * I))))
      (a := β) (b := 0) (fun γ _ => ?_) ?_
    · simpa using this
    · have h3 : HasDerivAt (fun z : ℂ => (R : ℂ) * Complex.exp (-(z * I))) (-I * R * Complex.exp (-((γ : ℂ) * I))) (γ : ℂ) := by
        have h6 : HasDerivAt (fun z : ℂ => -(z * I)) (-I) (γ : ℂ) := by
          have := ((hasDerivAt_id (γ : ℂ)).mul_const I).neg
          convert this using 1 <;> first | rfl | simp
        have := (h6.cexp).const_mul (R : ℂ)
        refine this.congr_deriv ?_
        ring
      have h4 := (hF _ (hm γ)).comp (γ : ℂ) h3
      have h5 := HasDerivAt.comp_ofReal (e := fun z : ℂ => F ((R : ℂ) * Complex.exp (-(z * I)))) (z := γ) h4
      simpa using h5
    · apply ContinuousOn.intervalIntegrable
      refine ContinuousOn.mul (hcont.comp (by fun_prop : Continuous fun γ : ℝ => (R : ℂ) * Complex.exp (-(γ * I))).continuousOn (fun γ _ => hm γ)) (by fun_prop)
  rw [h2, h3, h1]; ring


/-- The Laplace amplitude `Ψ(u) = (1 - u²/2)^{-1/2}` (principal branch, via `exp ∘ log`). -/
def psiC (u : ℂ) : ℂ := Complex.exp (-(1 / 2 : ℂ) * Complex.log (1 - u ^ 2 / 2))

lemma one_sub_re_pos {u : ℂ} (hu : ‖u‖ < √2) : 0 < (1 - u ^ 2 / 2).re := by
  have h1 : ‖u ^ 2 / 2‖ < 1 := by
    rw [norm_div, norm_pow]
    have : ‖u‖ ^ 2 < 2 := by
      have := pow_lt_pow_left₀ hu (norm_nonneg u) (two_ne_zero)
      rwa [Real.sq_sqrt (by norm_num)] at this
    simp only [Complex.norm_ofNat]; linarith
  have h2 : |(u ^ 2 / 2).re| ≤ ‖u ^ 2 / 2‖ := Complex.abs_re_le_norm _
  simp only [Complex.sub_re, Complex.one_re]
  linarith [abs_le.mp h2]

lemma one_sub_mem_slit {u : ℂ} (hu : ‖u‖ < √2) : 1 - u ^ 2 / 2 ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inl (one_sub_re_pos hu))

lemma psiC_differentiableOn : DifferentiableOn ℂ psiC (ball 0 (√2)) := by
  intro u hu
  have hu' : ‖u‖ < √2 := by simpa using hu
  have hs := one_sub_mem_slit hu'
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold psiC
  have h1 : DifferentiableAt ℂ (fun z : ℂ => 1 - z ^ 2 / 2) u := by fun_prop
  have h2 := h1.clog hs
  exact (h2.const_mul _).cexp

lemma psiC_sq {u : ℂ} (hu : ‖u‖ < √2) : psiC u ^ 2 * (1 - u ^ 2 / 2) = 1 := by
  have hs := one_sub_mem_slit hu
  have hne : (1 - u ^ 2 / 2) ≠ 0 := Complex.slitPlane_ne_zero hs
  unfold psiC
  rw [← Complex.exp_nat_mul]
  have : ((2 : ℕ) : ℂ) * (-(1 / 2 : ℂ) * Complex.log (1 - u ^ 2 / 2)) = -Complex.log (1 - u ^ 2 / 2) := by
    push_cast; ring
  rw [this, Complex.exp_neg, Complex.exp_log hne]
  exact inv_mul_cancel₀ hne

lemma psiC_re_pos {u : ℂ} (hu : ‖u‖ < √2) : 0 < (psiC u).re := by
  unfold psiC
  rw [Complex.exp_re]
  refine mul_pos (Real.exp_pos _) ?_
  have harg : |(1 - u ^ 2 / 2).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (one_sub_re_pos hu))
  have him : (-(1 / 2 : ℂ) * Complex.log (1 - u ^ 2 / 2)).im = -(1 / 2) * (1 - u ^ 2 / 2).arg := by
    simp [Complex.mul_im, Complex.log_im, Complex.log_re]
  rw [him]
  apply Real.cos_pos_of_mem_Ioo
  have := abs_lt.1 harg
  constructor <;> linarith [this.1, this.2]


lemma norm_sub_one_ge {u : ℂ} (hu : ‖u‖ ≤ 1) : 1 / 2 ≤ ‖1 - u ^ 2 / 2‖ := by
  have h : ‖u ^ 2 / 2‖ ≤ 1 / 2 := by
    rw [norm_div, norm_pow]
    simp only [Complex.norm_ofNat]
    have : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
    linarith
  have := norm_sub_norm_le (1 : ℂ) (u ^ 2 / 2)
  simp only [norm_one] at this
  linarith

lemma psiC_norm_le {u : ℂ} (hu : ‖u‖ ≤ 1) : ‖psiC u‖ ≤ √2 := by
  have hu' : ‖u‖ < √2 := lt_of_le_of_lt hu (by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num))
  have hq := psiC_sq hu'
  have h1 := norm_sub_one_ge hu
  have h2 : ‖psiC u‖ ^ 2 * ‖1 - u ^ 2 / 2‖ = 1 := by
    rw [← norm_pow, ← norm_mul, hq]; simp
  have h3 : ‖psiC u‖ ^ 2 ≤ 2 := by
    by_contra hcon
    push Not at hcon
    nlinarith [norm_nonneg (psiC u)]
  exact Real.le_sqrt_of_sq_le h3


lemma sqrt_two_gt_one : (1 : ℝ) < √2 := by
  rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- Taylor remainder of the amplitude: `‖Ψ(u) - 1 - u²/4‖ ≤ (3/4)‖u‖⁴` for `‖u‖ ≤ 1`. -/
lemma psiC_taylor {u : ℂ} (hu : ‖u‖ ≤ 1) : ‖psiC u - 1 - u ^ 2 / 4‖ ≤ 3 / 4 * ‖u‖ ^ 4 := by
  have hu' : ‖u‖ < √2 := lt_of_le_of_lt hu sqrt_two_gt_one
  set s : ℂ := u ^ 2 / 2 with hs
  set q : ℂ := psiC u with hqdef
  have hq : q ^ 2 * (1 - s) = 1 := psiC_sq hu'
  have h1 := norm_sub_one_ge hu
  rw [← hs] at h1
  have hs0 : (1 - s) ≠ 0 := by
    intro h; rw [h] at h1; simp at h1; linarith
  have hsn : ‖s‖ ≤ 1 / 2 := by
    rw [hs, norm_div, norm_pow]; simp only [Complex.norm_ofNat]
    nlinarith [norm_nonneg u]
  have hq2 : q ^ 2 = (1 - s)⁻¹ := by field_simp; linear_combination hq
  have key : (q - 1 - s / 2) * (q + 1 + s / 2) = s ^ 2 * ((1 - s)⁻¹ - 1 / 4) := by
    have : (q - 1 - s / 2) * (q + 1 + s / 2) = q ^ 2 - (1 + s / 2) ^ 2 := by ring
    rw [this, hq2]
    field_simp
    ring
  have hre : 3 / 4 ≤ ‖q + 1 + s / 2‖ := by
    have hqre := psiC_re_pos hu'
    have h2 : (q + 1 + s / 2).re ≥ 3 / 4 := by
      simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re]
      have : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
      have := (abs_le.mp this).1
      rw [← hqdef] at hqre
      linarith
    exact h2.trans (Complex.re_le_norm _)
  have hinv : ‖(1 - s)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    calc (‖1 - s‖)⁻¹ ≤ (1 / 2)⁻¹ := inv_anti₀ (by norm_num) h1
      _ = 2 := by norm_num
  have hrhs : ‖s ^ 2 * ((1 - s)⁻¹ - 1 / 4)‖ ≤ ‖s‖ ^ 2 * (9 / 4) := by
    rw [norm_mul, norm_pow]
    gcongr
    calc ‖(1 - s)⁻¹ - 1 / 4‖ ≤ ‖(1 - s)⁻¹‖ + ‖(1 / 4 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 + 1 / 4 := by
          have : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
          rw [this]; linarith
      _ = 9 / 4 := by norm_num
  have hδ : ‖q - 1 - s / 2‖ * (3 / 4) ≤ ‖s‖ ^ 2 * (9 / 4) := by
    calc ‖q - 1 - s / 2‖ * (3 / 4) ≤ ‖q - 1 - s / 2‖ * ‖q + 1 + s / 2‖ := by gcongr
      _ = ‖s ^ 2 * ((1 - s)⁻¹ - 1 / 4)‖ := by rw [← norm_mul, key]
      _ ≤ _ := hrhs
  have hsq : ‖s‖ = ‖u‖ ^ 2 / 2 := by
    rw [hs, norm_div, norm_pow]; simp
  have e : q - 1 - u ^ 2 / 4 = q - 1 - s / 2 := by rw [hs]; ring
  rw [e]
  have : ‖s‖ ^ 2 = ‖u‖ ^ 4 / 4 := by rw [hsq]; ring
  rw [this] at hδ
  linarith


/-- half-line Gaussian moments `∫₀^∞ s^k e^{-p s²}` as `rpow` formulas. -/
lemma gauss_moment {p : ℝ} (hp : 0 < p) {q : ℝ} (hq : -1 < q) :
    ∫ s in Ioi (0 : ℝ), s ^ q * Real.exp (-p * s ^ 2) = p ^ (-(q + 1) / 2) * (1 / 2) * Real.Gamma ((q + 1) / 2) := by
  have := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := q) (b := p) (by norm_num) hq hp
  simpa [Real.rpow_two] using this

lemma gauss_moment0 {p : ℝ} (_hp : 0 < p) :
    ∫ s in Ioi (0 : ℝ), Real.exp (-p * s ^ 2) = √π / (2 * √p) := by
  rw [integral_gaussian_Ioi, Real.sqrt_div Real.pi_pos.le]; ring

lemma gauss_moment2 {p : ℝ} (hp : 0 < p) :
    ∫ s in Ioi (0 : ℝ), s ^ 2 * Real.exp (-p * s ^ 2) = √π / (4 * p * √p) := by
  have h := gauss_moment hp (q := 2) (by norm_num)
  have e : ∫ s in Ioi (0 : ℝ), s ^ 2 * Real.exp (-p * s ^ 2) =
      ∫ s in Ioi (0 : ℝ), s ^ (2 : ℝ) * Real.exp (-p * s ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    simp
  rw [e, h]
  have g32 : Real.Gamma (((2 : ℝ) + 1) / 2) = √π / 2 := by
    have := Real.Gamma_add_one (s := 1 / 2) (by norm_num)
    rw [show (1 / 2 : ℝ) + 1 = ((2 : ℝ) + 1) / 2 by norm_num] at this
    rw [this, Real.Gamma_one_half_eq]; ring
  rw [g32]
  have hs : 0 < √p := Real.sqrt_pos.2 hp
  have : p ^ (-((2 : ℝ) + 1) / 2) = (p * √p)⁻¹ := by
    rw [show -((2 : ℝ) + 1) / 2 = -(1 + 1 / 2) by ring, Real.rpow_neg hp.le, Real.rpow_add hp,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [this]
  field_simp
  norm_num

lemma gauss_moment4_le {p : ℝ} (hp : 0 < p) :
    ∫ s in Ioi (0 : ℝ), s ^ 4 * Real.exp (-p * s ^ 2) ≤ p ^ (-(5 : ℝ) / 2) := by
  have h := gauss_moment hp (q := 4) (by norm_num)
  have e : ∫ s in Ioi (0 : ℝ), s ^ 4 * Real.exp (-p * s ^ 2) =
      ∫ s in Ioi (0 : ℝ), s ^ (4 : ℝ) * Real.exp (-p * s ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e, h]
  have g52 : Real.Gamma (((4 : ℝ) + 1) / 2) ≤ 2 := by
    have := Real.Gamma_add_one (s := 3 / 2) (by norm_num)
    rw [show (3 / 2 : ℝ) + 1 = ((4 : ℝ) + 1) / 2 by norm_num] at this
    have g32 : Real.Gamma (3 / 2) = √π / 2 := by
      have := Real.Gamma_add_one (s := 1 / 2) (by norm_num)
      rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num] at this
      rw [this, Real.Gamma_one_half_eq]; ring
    rw [this, g32]
    have : √π ≤ 2 := by
      rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith [Real.pi_lt_d2])
    nlinarith [Real.sqrt_nonneg π]
  have hpp : 0 < p ^ (-((4 : ℝ) + 1) / 2) := Real.rpow_pos_of_pos hp _
  have : -((4 : ℝ) + 1) / 2 = -(5 : ℝ) / 2 := by norm_num
  rw [this] at hpp ⊢
  have hg0 : 0 < Real.Gamma (((4 : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos (by norm_num)
  nlinarith


/-- Gaussian tails `∫_{1}^∞ s^k e^{-p s²} ≤ 2 e^{-p/2}` for `k ∈ {0, 2}`, `p ≥ 1`. -/
lemma gauss_tail_le {p : ℝ} (hp : 1 ≤ p) {k : ℕ} (hk : k = 0 ∨ k = 2) :
    ∫ s in Ioi (1 : ℝ), s ^ k * Real.exp (-p * s ^ 2) ≤ 2 * Real.exp (-p / 2) := by
  have hp0 : 0 < p := by linarith
  have hp2 : 0 < p / 2 := by linarith
  have hI : IntegrableOn (fun s : ℝ => s ^ k * Real.exp (-(p / 2) * s ^ 2)) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_sq hp2 (s := (k : ℝ)) (by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith)
    simpa [Real.rpow_natCast] using this
  have hmono : ∫ s in Ioi (1 : ℝ), s ^ k * Real.exp (-p * s ^ 2) ≤
      ∫ s in Ioi (1 : ℝ), Real.exp (-p / 2) * (s ^ k * Real.exp (-(p / 2) * s ^ 2)) := by
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioi (fun s hs => ?_)
    · refine Integrable.mono' ((hI.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul (Real.exp (-p / 2))) ?_ ?_
      · exact (by fun_prop : Continuous fun s : ℝ => s ^ k * Real.exp (-p * s ^ 2)).aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
        have hs1 : (1 : ℝ) < s := hs
        rw [Real.norm_of_nonneg (by positivity)]
        have : Real.exp (-p * s ^ 2) ≤ Real.exp (-p / 2) * Real.exp (-(p / 2) * s ^ 2) := by
          rw [← Real.exp_add]; apply Real.exp_le_exp.2
          have hs2 : 1 ≤ s ^ 2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hs2 hp0.le]
        calc s ^ k * Real.exp (-p * s ^ 2) ≤ s ^ k * (Real.exp (-p / 2) * Real.exp (-(p / 2) * s ^ 2)) := by gcongr
          _ = _ := by ring
    · exact (hI.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul _
    · have hs1 : (1 : ℝ) < s := hs
      have : Real.exp (-p * s ^ 2) ≤ Real.exp (-p / 2) * Real.exp (-(p / 2) * s ^ 2) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.2
        have hs2 : 1 ≤ s ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hs2 hp0.le]
      calc s ^ k * Real.exp (-p * s ^ 2) ≤ s ^ k * (Real.exp (-p / 2) * Real.exp (-(p / 2) * s ^ 2)) := by gcongr
        _ = _ := by ring
  refine hmono.trans ?_
  rw [MeasureTheory.integral_const_mul]
  have hfull : ∫ s in Ioi (1 : ℝ), s ^ k * Real.exp (-(p / 2) * s ^ 2) ≤
      ∫ s in Ioi (0 : ℝ), s ^ k * Real.exp (-(p / 2) * s ^ 2) :=
    setIntegral_mono_set hI (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => by
      have : (0 : ℝ) < s := hs
      positivity) (Ioi_subset_Ioi zero_le_one).eventuallySubset
  have hval : ∫ s in Ioi (0 : ℝ), s ^ k * Real.exp (-(p / 2) * s ^ 2) ≤ 2 := by
    rcases hk with rfl | rfl
    · simp only [pow_zero, one_mul]
      rw [gauss_moment0 hp2]
      have h1 : (1 / 2 : ℝ) ≤ p / 2 := by linarith
      have h2 : √(1 / 2) ≤ √(p / 2) := Real.sqrt_le_sqrt h1
      have h3 : (2 / 3 : ℝ) ≤ √(1 / 2) := by
        apply Real.le_sqrt_of_sq_le; norm_num
      have h4 : √π ≤ 2 := by
        rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by linarith [Real.pi_lt_d2])
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.sqrt_nonneg π]
    · rw [gauss_moment2 hp2]
      have h1 : (1 / 2 : ℝ) ≤ p / 2 := by linarith
      have h2 : √(1 / 2) ≤ √(p / 2) := Real.sqrt_le_sqrt h1
      have h3 : (2 / 3 : ℝ) ≤ √(1 / 2) := by
        apply Real.le_sqrt_of_sq_le; norm_num
      have h4 : √π ≤ 2 := by
        rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by linarith [Real.pi_lt_d2])
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.sqrt_nonneg π, mul_pos hp2 (Real.sqrt_pos.2 hp2)]
  have := Real.exp_pos (-p / 2)
  nlinarith


/-- The Laplace integral `A(w) = ∫₀¹ e^{-w r²} Ψ(r) dr`. -/
def laplaceA (w : ℂ) : ℂ := ∫ r : ℝ in (0:ℝ)..1, Complex.exp (-w * (r : ℂ) ^ 2) * psiC (r : ℂ)

lemma norm_exp_neg_I (γ : ℝ) : ‖Complex.exp (-(γ * I))‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- Rotated-ray form of the Laplace integral. -/
lemma laplaceA_rotate {w : ℂ} (hw : 1 ≤ w.re) :
    ‖laplaceA w - Complex.exp (-((w.arg / 2 : ℝ) * I)) *
        ∫ s : ℝ in (0:ℝ)..1, Complex.exp (-(‖w‖ : ℂ) * (s : ℂ) ^ 2) *
          psiC ((s : ℂ) * Complex.exp (-((w.arg / 2 : ℝ) * I)))‖ ≤ 2 * Real.exp (-w.re) := by
  set β : ℝ := w.arg / 2 with hβ
  have hw0 : 0 < w.re := by linarith
  have harg : |w.arg| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hw0)
  have hwexp : w = (‖w‖ : ℂ) * Complex.exp ((2 * β : ℝ) * I) := by
    have := Complex.norm_mul_exp_arg_mul_I w
    rw [hβ]; push_cast; rw [show 2 * ((w.arg : ℂ) / 2) = (w.arg : ℂ) by ring]; exact this.symm
  have hf : DifferentiableOn ℂ (fun r : ℂ => Complex.exp (-w * r ^ 2) * psiC r) (ball 0 (√2)) :=
    (by fun_prop : Differentiable ℂ fun r : ℂ => Complex.exp (-w * r ^ 2)).differentiableOn.mul
      psiC_differentiableOn
  have hrot := rotate_ray hf one_pos sqrt_two_gt_one β
  have hA : laplaceA w = ∫ r : ℝ in (0:ℝ)..1, Complex.exp (-w * (r : ℂ) ^ 2) * psiC (r : ℂ) := rfl
  have hray : ∀ s : ℝ, Complex.exp (-w * ((s : ℂ) * Complex.exp (-(β * I))) ^ 2) =
      Complex.exp (-(‖w‖ : ℂ) * (s : ℂ) ^ 2) := by
    intro s
    congr 1
    conv_lhs => rw [hwexp]
    rw [mul_pow, ← Complex.exp_nat_mul]
    have : ((2 : ℕ) : ℂ) * -((β : ℂ) * I) = -((2 * β : ℝ) * I) := by push_cast; ring
    rw [this]
    have h2 : Complex.exp (((2 * β : ℝ) : ℂ) * I) * Complex.exp (-(((2 * β : ℝ) : ℂ) * I)) = 1 := by
      rw [← Complex.exp_add]; simp
    calc -((‖w‖ : ℂ) * Complex.exp (((2 * β : ℝ) : ℂ) * I)) * ((s : ℂ) ^ 2 * Complex.exp (-(((2 * β : ℝ) : ℂ) * I)))
        = -(‖w‖ : ℂ) * (s : ℂ) ^ 2 * (Complex.exp (((2 * β : ℝ) : ℂ) * I) * Complex.exp (-(((2 * β : ℝ) : ℂ) * I))) := by ring
      _ = _ := by rw [h2]; ring
  have hint_eq : ∫ s : ℝ in (0:ℝ)..1, Complex.exp (-w * ((s : ℂ) * Complex.exp (-(β * I))) ^ 2) *
      psiC ((s : ℂ) * Complex.exp (-(β * I))) =
      ∫ s : ℝ in (0:ℝ)..1, Complex.exp (-(‖w‖ : ℂ) * (s : ℂ) ^ 2) * psiC ((s : ℂ) * Complex.exp (-(β * I))) := by
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    simp only [hray]
  rw [hint_eq] at hrot
  rw [hA, hrot]
  simp only [add_sub_cancel_left]
  -- bound the arc
  have hβ' : |β| < π / 4 := by rw [hβ, abs_div]; simp; linarith
  have hb : ∀ γ ∈ uIoc β 0, ‖Complex.exp (-w * (((1 : ℝ) : ℂ) * Complex.exp (-((γ : ℂ) * I))) ^ 2) *
      psiC (((1 : ℝ) : ℂ) * Complex.exp (-((γ : ℂ) * I))) *
        (-I * ((1 : ℝ) : ℂ) * Complex.exp (-((γ : ℂ) * I)))‖ ≤ √2 * Real.exp (-w.re) := by
    intro γ hγ
    have hγ' : |β - γ| ≤ |β| := by
      rw [uIoc, Set.mem_Ioc] at hγ
      rcases le_total β 0 with h | h
      · rw [min_eq_left h, max_eq_right h] at hγ
        rw [abs_of_nonpos h, abs_le]; constructor <;> linarith [hγ.1, hγ.2]
      · rw [min_eq_right h, max_eq_left h] at hγ
        rw [abs_of_nonneg h, abs_le]; constructor <;> linarith [hγ.1, hγ.2]
    have hu1 : ‖((1 : ℝ) : ℂ) * Complex.exp (-((γ : ℂ) * I))‖ = 1 := by
      rw [norm_mul, norm_exp_neg_I]; simp
    have hcos : Real.cos (2 * β) ≤ Real.cos (2 * (β - γ)) := by
      have h1 : |2 * (β - γ)| ≤ |2 * β| := by
        rw [abs_mul, abs_mul]; simp; linarith
      have h2 : |2 * β| ≤ π := by rw [abs_mul]; simp; linarith [Real.pi_pos]
      rw [← Real.cos_abs (2 * β), ← Real.cos_abs (2 * (β - γ))]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) h2 h1
    have hre : (w * (((1 : ℝ) : ℂ) * Complex.exp (-((γ : ℂ) * I))) ^ 2).re =
        ‖w‖ * Real.cos (2 * (β - γ)) := by
      conv_lhs => rw [hwexp]
      rw [show ((‖w‖ : ℂ) * Complex.exp (((2 * β : ℝ) : ℂ) * I)) * (((1 : ℝ) : ℂ) * Complex.exp (-((γ : ℂ) * I))) ^ 2 =
        (‖w‖ : ℂ) * Complex.exp (((2 * (β - γ) : ℝ) : ℂ) * I) by
          rw [mul_pow, ← Complex.exp_nat_mul]
          simp only [Complex.ofReal_one, one_pow, one_mul]
          rw [mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring]
      rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    have hRe : w.re = ‖w‖ * Real.cos (2 * β) := by
      conv_lhs => rw [hwexp]
      rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    have hpsi : ‖psiC (((1 : ℝ) : ℂ) * Complex.exp (-((γ : ℂ) * I)))‖ ≤ √2 := psiC_norm_le hu1.le
    have hlast : ‖-I * ((1 : ℝ) : ℂ) * Complex.exp (-((γ : ℂ) * I))‖ = 1 := by
      rw [norm_mul, norm_mul, norm_exp_neg_I]; simp
    have hexpn : ‖Complex.exp (-w * (((1 : ℝ) : ℂ) * Complex.exp (-((γ : ℂ) * I))) ^ 2)‖ ≤
        Real.exp (-w.re) := by
      rw [Complex.norm_exp, neg_mul, Complex.neg_re, hre]
      apply Real.exp_le_exp.2
      rw [hRe]
      have := mul_le_mul_of_nonneg_left hcos (norm_nonneg w)
      linarith
    rw [norm_mul, norm_mul, hlast, mul_one]
    calc _ ≤ Real.exp (-w.re) * √2 :=
          mul_le_mul hexpn hpsi (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by ring
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [zero_sub, abs_neg] at hbound
  have hs2 : √2 ≤ 3 / 2 := by
    apply Real.sqrt_le_iff.2; constructor <;> norm_num
  have hpi : π < 4 := by linarith [Real.pi_lt_d2]
  have hex := Real.exp_pos (-w.re)
  calc _ ≤ √2 * Real.exp (-w.re) * |β| := hbound
    _ ≤ (3 / 2) * Real.exp (-w.re) * 1 := by
        gcongr
        linarith
    _ ≤ 2 * Real.exp (-w.re) := by linarith


lemma gauss_split {p : ℝ} (hp : 0 < p) {k : ℕ} :
    ∫ s : ℝ in (0:ℝ)..1, s ^ k * Real.exp (-p * s ^ 2) =
      (∫ s in Ioi (0 : ℝ), s ^ k * Real.exp (-p * s ^ 2)) -
        ∫ s in Ioi (1 : ℝ), s ^ k * Real.exp (-p * s ^ 2) := by
  have hI : IntegrableOn (fun s : ℝ => s ^ k * Real.exp (-p * s ^ 2)) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_sq hp (s := (k : ℝ)) (by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith)
    simpa [Real.rpow_natCast] using this
  rw [intervalIntegral.integral_of_le zero_le_one]
  have := setIntegral_union (μ := volume) (f := fun s : ℝ => s ^ k * Real.exp (-p * s ^ 2))
    (Ioc_disjoint_Ioi (le_refl (1 : ℝ))) measurableSet_Ioi
    (hI.mono_set Ioc_subset_Ioi_self) (hI.mono_set (Ioi_subset_Ioi zero_le_one))
  rw [Ioc_union_Ioi_eq_Ioi zero_le_one] at this
  linarith

lemma gauss_delta_le {p : ℝ} (hp : 1 ≤ p) {δ : ℝ → ℂ}
    (hδ : ∀ s ∈ Icc (0 : ℝ) 1, ‖δ s‖ ≤ 3 / 4 * s ^ 4) :
    ‖∫ s : ℝ in (0:ℝ)..1, ((Real.exp (-p * s ^ 2) : ℝ) : ℂ) * δ s‖ ≤ 3 / 4 * p ^ (-(5 : ℝ) / 2) := by
  have hp0 : 0 < p := by linarith
  have hI : IntegrableOn (fun s : ℝ => s ^ 4 * Real.exp (-p * s ^ 2)) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_sq hp0 (s := ((4 : ℕ) : ℝ)) (by norm_num)
    simpa [Real.rpow_natCast] using this
  have h1 : ‖∫ s : ℝ in (0:ℝ)..1, ((Real.exp (-p * s ^ 2) : ℝ) : ℂ) * δ s‖ ≤
      ∫ s : ℝ in (0:ℝ)..1, 3 / 4 * (s ^ 4 * Real.exp (-p * s ^ 2)) := by
    refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ ?_)
    · refine Filter.Eventually.of_forall (fun s hs => ?_)
      have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      calc Real.exp (-p * s ^ 2) * ‖δ s‖ ≤ Real.exp (-p * s ^ 2) * (3 / 4 * s ^ 4) := by
            gcongr; exact hδ s hs'
        _ = _ := by ring
    · apply Continuous.intervalIntegrable; fun_prop
  refine h1.trans ?_
  rw [intervalIntegral.integral_const_mul]
  have h2 : ∫ s : ℝ in (0:ℝ)..1, s ^ 4 * Real.exp (-p * s ^ 2) ≤
      ∫ s in Ioi (0 : ℝ), s ^ 4 * Real.exp (-p * s ^ 2) := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact setIntegral_mono_set hI (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => by
      have : (0 : ℝ) < s := hs
      positivity) Ioc_subset_Ioi_self.eventuallySubset
  have h3 := gauss_moment4_le hp0
  nlinarith


lemma exp_neg_half_le {p : ℝ} (hp : 1 ≤ p) : Real.exp (-p / 2) ≤ 48 * p ^ (-(5 : ℝ) / 2) := by
  have hp0 : 0 < p := by linarith
  have h1 := Real.pow_div_factorial_le_exp (p / 2) (by positivity) 3
  have h2 : Real.exp (-p / 2) = (Real.exp (p / 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  have h3 : (p / 2) ^ 3 / (Nat.factorial 3 : ℝ) ≤ Real.exp (p / 2) := h1
  have hpos : 0 < (p / 2) ^ 3 / (Nat.factorial 3 : ℝ) := by positivity
  have h4 : Real.exp (-p / 2) ≤ ((p / 2) ^ 3 / (Nat.factorial 3 : ℝ))⁻¹ := by
    rw [h2]; exact inv_anti₀ hpos h3
  have h5 : ((p / 2) ^ 3 / (Nat.factorial 3 : ℝ))⁻¹ = 48 * (p ^ 3)⁻¹ := by
    simp [Nat.factorial]; field_simp; norm_num
  have h6 : (p ^ 3)⁻¹ ≤ p ^ (-(5 : ℝ) / 2) := by
    rw [show (p ^ 3)⁻¹ = p ^ (-(3 : ℝ)) by rw [Real.rpow_neg hp0.le]; norm_cast]
    exact Real.rpow_le_rpow_of_exponent_le hp (by norm_num)
  rw [h5] at h4
  nlinarith

/-- The main term `(√π/2) w^{-1/2} (1 + 1/(8w))` of the Laplace integral. -/
def laplaceMain (w : ℂ) : ℂ :=
  (√Real.pi / 2 : ℝ) * Complex.exp (-(1 / 2 : ℂ) * Complex.log w) * (1 + 1 / (8 * w))


lemma exp_sq_arg (w : ℂ) :
    w * Complex.exp (-((w.arg / 2 : ℝ) * I)) ^ 2 = (‖w‖ : ℂ) := by
  have h := Complex.norm_mul_exp_arg_mul_I w
  rw [← Complex.exp_nat_mul]
  have e1 : w * Complex.exp (((2 : ℕ) : ℂ) * -(((w.arg / 2 : ℝ) : ℂ) * I)) =
      (‖w‖ : ℂ) * Complex.exp (w.arg * I) * Complex.exp (((2 : ℕ) : ℂ) * -(((w.arg / 2 : ℝ) : ℂ) * I)) := by
    rw [h]
  rw [e1, mul_assoc, ← Complex.exp_add]
  have : (↑w.arg * I + ((2 : ℕ) : ℂ) * -(((w.arg / 2 : ℝ) : ℂ) * I)) = 0 := by
    push_cast; ring
  rw [this, Complex.exp_zero, mul_one]

lemma laplaceMain_eq {w : ℂ} (hw : 0 < w.re) :
    laplaceMain w = ((√Real.pi / 2 / √‖w‖ : ℝ) : ℂ) * Complex.exp (-((w.arg / 2 : ℝ) * I)) *
      (1 + Complex.exp (-((w.arg / 2 : ℝ) * I)) ^ 2 / (8 * (‖w‖ : ℂ))) := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  have hp : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hw0
  have hsq := exp_sq_arg w
  have h1 : Complex.exp (-((w.arg / 2 : ℝ) * I)) ^ 2 / (8 * (‖w‖ : ℂ)) = 1 / (8 * w) := by
    have hpc : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    rw [← hsq]
    field_simp
  have h2 : Complex.exp (-(1 / 2 : ℂ) * Complex.log w) =
      ((1 / √‖w‖ : ℝ) : ℂ) * Complex.exp (-((w.arg / 2 : ℝ) * I)) := by
    rw [Complex.log, show -(1 / 2 : ℂ) * (((Real.log ‖w‖ : ℝ) : ℂ) + (w.arg : ℂ) * I) =
      (-(1 / 2 * Real.log ‖w‖) : ℝ) + -(((w.arg / 2 : ℝ) : ℂ) * I) by push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp]
    congr 2
    rw [Real.sqrt_eq_rpow]
    simp only [one_div]
    rw [← Real.rpow_neg hp.le, Real.rpow_def_of_pos hp]
    congr 1; ring
  rw [laplaceMain, h1, h2]
  push_cast
  ring

/-- Ray-integral expansion: after rotation the Laplace integral equals `laplaceMain` up to
`O(‖w‖^{-5/2})`. -/
lemma ray_integral {w : ℂ} (hw : 1 ≤ w.re) :
    ‖Complex.exp (-((w.arg / 2 : ℝ) * I)) *
        (∫ s : ℝ in (0:ℝ)..1, Complex.exp (-(‖w‖ : ℂ) * (s : ℂ) ^ 2) *
          psiC ((s : ℂ) * Complex.exp (-((w.arg / 2 : ℝ) * I)))) - laplaceMain w‖ ≤
      150 * ‖w‖ ^ (-(5 : ℝ) / 2) := by
  set e : ℂ := Complex.exp (-((w.arg / 2 : ℝ) * I)) with he
  have hw0 : 0 < w.re := by linarith
  set p : ℝ := ‖w‖ with hpdef
  have hp1 : 1 ≤ p := le_trans hw (Complex.re_le_norm w)
  have hp0 : 0 < p := by linarith
  have he1 : ‖e‖ = 1 := norm_exp_neg_I _
  -- decomposition of the integrand
  set δ : ℝ → ℂ := fun s => psiC ((s : ℂ) * e) - 1 - ((s : ℂ) * e) ^ 2 / 4 with hδdef
  have hδ : ∀ s ∈ Icc (0 : ℝ) 1, ‖δ s‖ ≤ 3 / 4 * s ^ 4 := by
    intro s hs
    have hn : ‖(s : ℂ) * e‖ ≤ 1 := by
      rw [norm_mul, he1, Complex.norm_real, Real.norm_of_nonneg hs.1]; simpa using hs.2
    have := psiC_taylor hn
    rw [norm_mul, he1, Complex.norm_real, Real.norm_of_nonneg hs.1, mul_one] at this
    exact this
  have hdecomp : ∀ s : ℝ, Complex.exp (-(p : ℂ) * (s : ℂ) ^ 2) * psiC ((s : ℂ) * e) =
      ((Real.exp (-p * s ^ 2) : ℝ) : ℂ) + (e ^ 2 / 4) * ((s ^ 2 * Real.exp (-p * s ^ 2) : ℝ) : ℂ) +
        ((Real.exp (-p * s ^ 2) : ℝ) : ℂ) * δ s := by
    intro s
    have : Complex.exp (-(p : ℂ) * (s : ℂ) ^ 2) = ((Real.exp (-p * s ^ 2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]; push_cast; ring_nf
    rw [this, hδdef]
    simp only []
    push_cast
    ring
  have hcont_psi : ContinuousOn (fun s : ℝ => psiC ((s : ℂ) * e)) (Icc 0 1) := by
    refine psiC_differentiableOn.continuousOn.comp (by fun_prop) (fun s hs => ?_)
    rw [mem_ball_zero_iff, norm_mul, he1, Complex.norm_real, Real.norm_of_nonneg hs.1, mul_one]
    exact lt_of_le_of_lt hs.2 sqrt_two_gt_one
  have hi_δ : IntervalIntegrable (fun s : ℝ => ((Real.exp (-p * s ^ 2) : ℝ) : ℂ) * δ s) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    have : ContinuousOn δ (Icc 0 1) := by
      refine (hcont_psi.sub continuousOn_const).sub (by fun_prop)
    exact (by fun_prop : Continuous fun s : ℝ => ((Real.exp (-p * s ^ 2) : ℝ) : ℂ)).continuousOn.mul this
  have hi0 : IntervalIntegrable (fun s : ℝ => ((Real.exp (-p * s ^ 2) : ℝ) : ℂ)) volume 0 1 :=
    (by fun_prop : Continuous fun s : ℝ => ((Real.exp (-p * s ^ 2) : ℝ) : ℂ)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun s : ℝ => (e ^ 2 / 4) * ((s ^ 2 * Real.exp (-p * s ^ 2) : ℝ) : ℂ))
      volume 0 1 :=
    (by fun_prop : Continuous fun s : ℝ => (e ^ 2 / 4) * ((s ^ 2 * Real.exp (-p * s ^ 2) : ℝ) : ℂ)).intervalIntegrable _ _
  have hI : (∫ s : ℝ in (0:ℝ)..1, Complex.exp (-(p : ℂ) * (s : ℂ) ^ 2) * psiC ((s : ℂ) * e)) =
      ((∫ s : ℝ in (0:ℝ)..1, Real.exp (-p * s ^ 2) : ℝ) : ℂ) +
        (e ^ 2 / 4) * ((∫ s : ℝ in (0:ℝ)..1, s ^ 2 * Real.exp (-p * s ^ 2) : ℝ) : ℂ) +
        ∫ s : ℝ in (0:ℝ)..1, ((Real.exp (-p * s ^ 2) : ℝ) : ℂ) * δ s := by
    simp_rw [hdecomp]
    rw [intervalIntegral.integral_add (hi0.add hi2) hi_δ, intervalIntegral.integral_add hi0 hi2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_ofReal]
  -- Gaussian values
  have hG0 := gauss_split hp0 (k := 0)
  have hG2 := gauss_split hp0 (k := 2)
  simp only [pow_zero, one_mul] at hG0
  rw [gauss_moment0 hp0] at hG0
  rw [gauss_moment2 hp0] at hG2
  have hT0 := gauss_tail_le hp1 (k := 0) (Or.inl rfl)
  have hT2 := gauss_tail_le hp1 (k := 2) (Or.inr rfl)
  simp only [pow_zero, one_mul] at hT0
  have hT0n : 0 ≤ ∫ s in Ioi (1 : ℝ), Real.exp (-p * s ^ 2) :=
    setIntegral_nonneg measurableSet_Ioi (fun s _ => (Real.exp_pos _).le)
  have hT2n : 0 ≤ ∫ s in Ioi (1 : ℝ), s ^ 2 * Real.exp (-p * s ^ 2) :=
    setIntegral_nonneg measurableSet_Ioi (fun s _ => by positivity)
  have hD := gauss_delta_le hp1 hδ
  have hexp := exp_neg_half_le hp1
  set T0 := ∫ s in Ioi (1 : ℝ), Real.exp (-p * s ^ 2)
  set T2 := ∫ s in Ioi (1 : ℝ), s ^ 2 * Real.exp (-p * s ^ 2)
  set D := ∫ s : ℝ in (0:ℝ)..1, ((Real.exp (-p * s ^ 2) : ℝ) : ℂ) * δ s with hDdef
  rw [hI, laplaceMain_eq hw0]
  have hsp : (√π / (2 * √p) : ℝ) = √π / 2 / √p := by ring
  have hmain : e * (((√π / (2 * √p) - T0 : ℝ) : ℂ) + e ^ 2 / 4 * ((√π / (4 * p * √p) - T2 : ℝ) : ℂ) + D) -
      ((√π / 2 / √p : ℝ) : ℂ) * e * (1 + e ^ 2 / (8 * (p : ℂ))) =
      e * (-(T0 : ℂ) - e ^ 2 / 4 * (T2 : ℂ) + D) := by
    have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
    have hsc : (√p : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hp0).ne'
    push_cast
    field_simp
    ring
  rw [hG0, hG2, hmain, norm_mul, he1, one_mul]
  have hn1 : ‖-(T0 : ℂ) - e ^ 2 / 4 * (T2 : ℂ) + D‖ ≤ T0 + T2 / 4 + ‖D‖ := by
    calc _ ≤ ‖-(T0 : ℂ) - e ^ 2 / 4 * (T2 : ℂ)‖ + ‖D‖ := norm_add_le _ _
      _ ≤ ‖-(T0 : ℂ)‖ + ‖e ^ 2 / 4 * (T2 : ℂ)‖ + ‖D‖ := by gcongr; exact norm_sub_le _ _
      _ = T0 + T2 / 4 + ‖D‖ := by
        rw [norm_neg, norm_mul, norm_div, norm_pow, he1, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg hT0n, Real.norm_of_nonneg hT2n]
        norm_num; ring
  have hpw : 0 < p ^ (-(5 : ℝ) / 2) := Real.rpow_pos_of_pos hp0 _
  refine hn1.trans ?_
  nlinarith


/-- Copy of the chord change of variables `t = √2 sin(θ/2)` from `BesselI0Sector` (private there). -/
private lemma lower_cos_half_change (z : ℂ) :
    ∫ θ in (0 : ℝ)..(Real.pi / 2), Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) =
      ∫ t in (0 : ℝ)..1, Complex.exp (-z * (t : ℂ) ^ 2) *
        ((√2 / √(1 - t ^ 2 / 2) : ℝ) : ℂ) := by
  let f : ℝ → ℝ := fun θ => √2 * Real.sin (θ / 2)
  let f' : ℝ → ℝ := fun θ => (√2 / 2) * Real.cos (θ / 2)
  let g : ℝ → ℂ := fun t => Complex.exp (-z * (t : ℂ) ^ 2) * ((√2 / √(1 - t ^ 2 / 2) : ℝ) : ℂ)
  have hderiv : ∀ θ ∈ uIcc (0 : ℝ) (Real.pi / 2), HasDerivAt f (f' θ) θ := by
    intro θ _
    have h1 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) θ := (hasDerivAt_id θ).div_const 2
    have h2 : HasDerivAt (fun x : ℝ => Real.sin (x / 2)) (Real.cos (θ / 2) * (1 / 2)) θ :=
      h1.sin
    exact (h2.const_mul √2).congr_deriv (by dsimp [f']; ring)
  have hf'_cont : ContinuousOn f' (uIcc (0 : ℝ) (Real.pi / 2)) :=
    (by fun_prop : Continuous f').continuousOn
  have hg_cont : ContinuousOn g (f '' uIcc (0 : ℝ) (Real.pi / 2)) := by
    have himg : f '' uIcc (0 : ℝ) (Real.pi / 2) ⊆ Icc 0 1 := by
      rintro t ⟨θ, hθ, rfl⟩
      rw [uIcc_of_le (by positivity)] at hθ
      have hsin_nn : 0 ≤ Real.sin (θ / 2) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      have hsin_le : Real.sin (θ / 2) ≤ Real.sin (Real.pi / 4) :=
        Real.strictMonoOn_sin.monotoneOn
          ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
          ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
          (by linarith [hθ.2])
      rw [Real.sin_pi_div_four] at hsin_le
      refine ⟨mul_nonneg (Real.sqrt_nonneg _) hsin_nn, ?_⟩
      calc √2 * Real.sin (θ / 2) ≤ √2 * (√2 / 2) := by gcongr
        _ = 1 := by rw [← mul_div_assoc, Real.mul_self_sqrt zero_le_two]; norm_num
    refine ContinuousOn.mono ?_ himg
    intro t ht
    have hpos : 0 < 1 - t ^ 2 / 2 := by
      have : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      linarith
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun s : ℝ => Complex.exp (-z * (s : ℂ) ^ 2)) t := by fun_prop
    have h2 : ContinuousAt (fun s : ℝ => ((√2 / √(1 - s ^ 2 / 2) : ℝ) : ℂ)) t :=
      Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_const.div ((Real.continuous_sqrt.continuousAt.comp
          (by fun_prop : Continuous fun s : ℝ => 1 - s ^ 2 / 2).continuousAt))
          (Real.sqrt_ne_zero'.mpr hpos))
    exact h1.mul h2
  have hcomp := intervalIntegral.integral_deriv_smul_comp' hderiv hf'_cont hg_cont
  have hf0 : f 0 = 0 := by simp [f]
  have hfpi : f (Real.pi / 2) = 1 := by
    dsimp [f]
    rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring, Real.sin_pi_div_four, ← mul_div_assoc,
      Real.mul_self_sqrt zero_le_two]
    norm_num
  rw [hf0, hfpi] at hcomp
  rw [← hcomp]
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [uIcc_of_le (by positivity)] at hθ
  have hcos_pos : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hf_sq : f θ ^ 2 = 1 - Real.cos θ := by
    dsimp [f]
    rw [mul_pow, Real.sq_sqrt zero_le_two]
    have hcos_sq := Real.cos_sq (θ / 2)
    have hsin_sq := Real.sin_sq_add_cos_sq (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at hcos_sq
    linarith
  have hsqrt_eq : √(1 - f θ ^ 2 / 2) = Real.cos (θ / 2) := by
    rw [hf_sq, show 1 - (1 - Real.cos θ) / 2 = (1 + Real.cos θ) / 2 by ring]
    have hcos_half : Real.cos (θ / 2) ^ 2 = (1 + Real.cos θ) / 2 := by
      have := Real.cos_sq (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring] at this
      linarith
    rw [← hcos_half, Real.sqrt_sq hcos_pos.le]
  dsimp only [Function.comp_apply, g, f']
  rw [Complex.real_smul, hsqrt_eq, ← Complex.ofReal_pow, hf_sq]
  have hcos_ne : (Real.cos (θ / 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcos_pos.ne'
  have h2_sq : ((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two]; norm_num
  rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_div]
  calc Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ))
      = Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) * ((((√2 : ℂ) * (√2 : ℂ)) / 2) *
          ((Real.cos (θ / 2) : ℂ) / (Real.cos (θ / 2) : ℂ))) := by
        rw [h2_sq, div_self hcos_ne]; norm_num
    _ = ((√2 : ℂ) / 2 * (Real.cos (θ / 2) : ℂ)) *
          (Complex.exp (-z * ((1 - Real.cos θ : ℝ) : ℂ)) * ((√2 : ℂ) / (Real.cos (θ / 2) : ℂ))) := by
        ring

lemma laplaceA_bound {w : ℂ} (hw : 1 ≤ w.re) :
    ‖laplaceA w - laplaceMain w‖ ≤ 2 * Real.exp (-w.re) + 150 * ‖w‖ ^ (-(5 : ℝ) / 2) := by
  have h1 := laplaceA_rotate hw
  have h2 := ray_integral hw
  calc ‖laplaceA w - laplaceMain w‖ ≤ _ := by
        have := norm_add_le (laplaceA w - Complex.exp (-((w.arg / 2 : ℝ) * I)) *
          ∫ s : ℝ in (0:ℝ)..1, Complex.exp (-(‖w‖ : ℂ) * (s : ℂ) ^ 2) *
            psiC ((s : ℂ) * Complex.exp (-((w.arg / 2 : ℝ) * I))))
          (Complex.exp (-((w.arg / 2 : ℝ) * I)) *
          (∫ s : ℝ in (0:ℝ)..1, Complex.exp (-(‖w‖ : ℂ) * (s : ℂ) ^ 2) *
            psiC ((s : ℂ) * Complex.exp (-((w.arg / 2 : ℝ) * I)))) - laplaceMain w)
        convert this using 2
        ring
    _ ≤ _ := add_le_add h1 h2

lemma psiC_real {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    psiC (r : ℂ) = ((1 / √(1 - r ^ 2 / 2) : ℝ) : ℂ) := by
  have hpos : 0 < 1 - r ^ 2 / 2 := by nlinarith
  rw [psiC]
  have : (1 : ℂ) - (r : ℂ) ^ 2 / 2 = ((1 - r ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_log hpos.le, show -(1 / 2 : ℂ) * ((Real.log (1 - r ^ 2 / 2) : ℝ) : ℂ) =
    ((-(1 / 2) * Real.log (1 - r ^ 2 / 2) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simp only [one_div]
  rw [← Real.rpow_neg hpos.le, Real.rpow_def_of_pos hpos]
  congr 1; ring


/-- The two-term asymptotic form `e^w/√(2π w) · (1 + 1/(8w))`. -/
def besselTwoTerm (w : ℂ) : ℂ :=
  (Complex.exp w / ((√(2 * Real.pi) : ℝ) : ℂ)) * Complex.exp (-(1 / 2 : ℂ) * Complex.log w) *
    (1 + 1 / (8 * w))

lemma besselI0C_eq_chord (w : ℂ) :
    Integration.besselI0C w = (Complex.exp w / (Real.pi : ℂ)) *
      ∫ θ in (0 : ℝ)..Real.pi, Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ)) := by
  unfold Integration.besselI0C
  have h1 : (Real.pi : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..Real.pi, Complex.exp (w * (Real.cos θ : ℝ)) =
      (Complex.exp w / (Real.pi : ℂ)) *
        ((Complex.exp w)⁻¹ * ∫ θ in (0 : ℝ)..Real.pi, Complex.exp (w * (Real.cos θ : ℝ))) := by
    have hexp : Complex.exp w ≠ 0 := Complex.exp_ne_zero w
    field_simp [hexp]
  rw [h1]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  rw [Complex.ofReal_sub, Complex.ofReal_one]
  ring

lemma chord_tail_le {w : ℂ} (hw : 0 < w.re) :
    ‖∫ θ in (Real.pi / 2)..Real.pi, Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ))‖ ≤
      Real.pi / 2 * Real.exp (-w.re) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun θ : ℝ => Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ))) (a := Real.pi / 2)
    (b := Real.pi) (C := Real.exp (-w.re)) (fun θ hθ => by
      rw [uIoc_of_le (by linarith [Real.pi_pos])] at hθ
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.2
      have hc : Real.cos θ ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1.le (by linarith [hθ.2, Real.pi_pos])
      have : (-w * ((1 - Real.cos θ : ℝ) : ℂ)).re = -(w.re * (1 - Real.cos θ)) := by
        rw [mul_comm, Complex.re_ofReal_mul, Complex.neg_re]; ring
      rw [this]
      nlinarith)
  refine h.trans (le_of_eq ?_)
  rw [abs_of_nonneg (by linarith [Real.pi_pos])]; ring

/-- **Two-term sector asymptotic of `I₀`.**  For `Re w ≥ 1`,
`|I₀(w) - e^w/√(2πw) (1 + 1/(8w))| ≤ 70 e^{Re w} |w|^{-5/2} + 2`. -/
theorem besselI0C_two_term {w : ℂ} (hw : 1 ≤ w.re) :
    ‖Integration.besselI0C w - besselTwoTerm w‖ ≤
      70 * Real.exp w.re * ‖w‖ ^ (-(5 : ℝ) / 2) + 2 := by
  have hw0 : 0 < w.re := by linarith
  have hchord : ∫ θ in (0 : ℝ)..(Real.pi / 2), Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ)) =
      √2 * laplaceA w := by
    rw [lower_cos_half_change, laplaceA, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    rw [psiC_real ht.1 ht.2]
    push_cast
    ring
  have hsplit : ∫ θ in (0 : ℝ)..Real.pi, Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ)) =
      (∫ θ in (0 : ℝ)..(Real.pi / 2), Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ))) +
        ∫ θ in (Real.pi / 2)..Real.pi, Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ)) := by
    have hc : Continuous fun θ : ℝ => Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ)) := by fun_prop
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm
  set R := ∫ θ in (Real.pi / 2)..Real.pi, Complex.exp (-w * ((1 - Real.cos θ : ℝ) : ℂ))
  have hmain : besselTwoTerm w = (Complex.exp w / (Real.pi : ℂ)) * (√2 * laplaceMain w) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    have h2π : (((√(2 * Real.pi)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
    have hs : ((√(2 * Real.pi) : ℝ) : ℂ) = (√2 : ℝ) * (√Real.pi : ℝ) := by
      rw [Real.sqrt_mul zero_le_two]; push_cast; ring
    have hsq : (((√2 : ℝ) : ℂ)) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt zero_le_two]; norm_num
    have hsp : (((√Real.pi : ℝ) : ℂ)) ^ 2 = (Real.pi : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
    have h20 : ((√2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
    have hp0 : ((√Real.pi : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
    rw [besselTwoTerm, laplaceMain, hs]
    push_cast
    field_simp
    rw [← hsp, ← hsq]
    ring
  rw [besselI0C_eq_chord, hsplit, hchord, hmain]
  have hexpn : ‖Complex.exp w / (Real.pi : ℂ)‖ = Real.exp w.re / Real.pi := by
    rw [norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hL := laplaceA_bound hw
  have hR := chord_tail_le hw0
  have hdiff : (Complex.exp w / (Real.pi : ℂ)) * (√2 * laplaceA w + R) -
      (Complex.exp w / (Real.pi : ℂ)) * (√2 * laplaceMain w) =
      (Complex.exp w / (Real.pi : ℂ)) * (√2 * (laplaceA w - laplaceMain w) + R) := by ring
  rw [hdiff, norm_mul, hexpn]
  have h1 : ‖(√2 : ℂ) * (laplaceA w - laplaceMain w) + R‖ ≤
      √2 * (2 * Real.exp (-w.re) + 150 * ‖w‖ ^ (-(5 : ℝ) / 2)) + Real.pi / 2 * Real.exp (-w.re) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ hR)
    rw [norm_mul]
    have : ‖(√2 : ℂ)‖ = √2 := by
      rw [show (√2 : ℂ) = ((√2 : ℝ) : ℂ) by simp, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    rw [this]
    gcongr
  have hpi := Real.pi_gt_three
  have hs2 : √2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs2' : 1 < √2 := sqrt_two_gt_one
  have hexp := Real.exp_pos w.re
  have hexpm : Real.exp w.re * Real.exp (-w.re) = 1 := by rw [← Real.exp_add]; simp
  have hpw : 0 < ‖w‖ ^ (-(5 : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith [Complex.re_le_norm w]) _
  calc Real.exp w.re / Real.pi * ‖(√2 : ℂ) * (laplaceA w - laplaceMain w) + R‖
      ≤ Real.exp w.re / Real.pi * (√2 * (2 * Real.exp (-w.re) + 150 * ‖w‖ ^ (-(5 : ℝ) / 2)) +
          Real.pi / 2 * Real.exp (-w.re)) := by gcongr
    _ = (2 * √2 / Real.pi + 1 / 2) * (Real.exp w.re * Real.exp (-w.re)) +
          150 * √2 / Real.pi * (Real.exp w.re * ‖w‖ ^ (-(5 : ℝ) / 2)) := by
        field_simp
        ring
    _ ≤ 70 * Real.exp w.re * ‖w‖ ^ (-(5 : ℝ) / 2) + 2 := by
        rw [hexpm]
        have a1 : 2 * √2 / Real.pi ≤ 1 := by
          rw [div_le_one (by linarith)]; linarith
        have a2 : 150 * √2 / Real.pi ≤ 70 := by
          have hs3 : √2 < 1.415 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
          rw [div_le_iff₀ (by linarith)]; nlinarith [Real.pi_gt_d2]
        have a3 : 0 ≤ Real.exp w.re * ‖w‖ ^ (-(5 : ℝ) / 2) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right a2 a3]

end
end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.besselI0C_two_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.besselI0C_two_term

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.laplaceA_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.laplaceA_bound
