module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Explicit Finite-Dimensional Cohn–Elkies Gaussian Bounds (`ce_finite_bounds.tex`)

Formalizes Theorems `E.1`, `E.2`, `E.2'`, and `E.3a` of
`CFT/sign_uncertainty/paper/ce_finite_bounds.tex` (PR 240, commit `c3d8c90fe`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform Polynomial RealInnerProductSpace SchwartzMap Matrix

namespace FormalResearch.CohnElkies

/-- `d`-dimensional Euclidean space `ℝ^d`. -/
abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-! ### Section 1: Cohn–Elkies Admissibility, Volumes, Schwartz Decay & Gaussian Fourier -/

/-- Admissibility of `(r, h)` as a Cohn–Elkies auxiliary function on `ℝ^d`. -/
structure IsCohnElkiesAdmissible (d : ℕ) (r : ℝ) (h : Euc d → ℝ) : Prop where
  r_pos : 0 < r
  continuous : Continuous h
  integrable : Integrable h
  fourier_integrable : Integrable (𝓕 (fun x : Euc d => (h x : ℂ)))
  origin_pos : 0 < h 0
  fourier_origin_pos : 0 < (𝓕 (fun x : Euc d => (h x : ℂ)) 0).re
  nonpos_outside : ∀ x : Euc d, r ≤ ‖x‖ → h x ≤ 0
  fourier_nonneg : ∀ y : Euc d,
    (𝓕 (fun x : Euc d => (h x : ℂ)) y).im = 0 ∧
      0 ≤ (𝓕 (fun x : Euc d => (h x : ℂ)) y).re

/-- A function `h : ℝ^d → ℝ` is radial and Schwartz (via `𝓢(ℝ^d, ℂ)`). -/
def IsRadialSchwartz (d : ℕ) (h : Euc d → ℝ) : Prop :=
  (∃ S : 𝓢(Euc d, ℂ), ∀ x : Euc d, S x = (h x : ℂ)) ∧
    (∀ x y : Euc d, ‖x‖ = ‖y‖ → h x = h y)

/-- Cohn–Elkies density upper bound `V(h) = (h(0) / ĥ(0)) · vol(B_{r/2})`. -/
noncomputable def cohnElkiesBound (d : ℕ) (r : ℝ) (h : Euc d → ℝ) : ℝ :=
  (h 0 / (𝓕 (fun x : Euc d => (h x : ℂ)) 0).re) *
    (volume : Measure (Euc d)).real (Metric.ball 0 (r / 2))

/-- Optimal Cohn–Elkies density bound `𝒟_d`. -/
noncomputable def optimalCohnElkiesBound (d : ℕ) : ℝ :=
  sInf { V : ℝ | ∃ r h, IsCohnElkiesAdmissible d r h ∧ V = cohnElkiesBound d r h }

theorem optimalCohnElkiesBound_le {d : ℕ} {r : ℝ} {h : Euc d → ℝ}
    (hadm : IsCohnElkiesAdmissible d r h) :
    optimalCohnElkiesBound d ≤ cohnElkiesBound d r h := by
  refine csInf_le ⟨0, ?_⟩ ⟨r, h, hadm, rfl⟩
  rintro V ⟨r', h', h', rfl⟩
  unfold cohnElkiesBound
  exact mul_nonneg (div_nonneg h'.origin_pos.le h'.fourier_origin_pos.le) ENNReal.toReal_nonneg

/-- Real volume of `B_{r/2} ⊂ ℝ^d` (`d ≥ 1`, `r ≥ 0`). -/
lemma volume_half_ball_eq {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Euc d)).real (Metric.ball 0 (r / 2)) =
      (π * r ^ 2 / 4) ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1) := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  rw [Measure.real_def, EuclideanSpace.volume_ball (Fin d) 0 (r / 2), Fintype.card_fin]
  have hpi : 0 ≤ √π ^ d / Real.Gamma ((d : ℝ) / 2 + 1) :=
    div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (Real.Gamma_pos_of_pos (by positivity)).le
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal hpi]
  have hpow : (r / 2) ^ d * √π ^ d = (π * r ^ 2 / 4) ^ ((d : ℝ) / 2) := by
    rw [← mul_pow, ← Real.rpow_natCast (r / 2 * √π) d]
    have hsq : (r / 2 * √π) ^ 2 = π * r ^ 2 / 4 := by
      rw [mul_pow, div_pow, Real.sq_sqrt Real.pi_pos.le]; ring
    rw [← hsq, ← Real.rpow_natCast (r / 2 * √π) 2, ← Real.rpow_mul (by positivity)]
    congr 1; ring
  rw [← mul_div_assoc, hpow]

private lemma hasTemperateGrowth_fderiv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {B : E → F} (hB : B.HasTemperateGrowth) :
    (fderiv ℝ B).HasTemperateGrowth := by
  refine ⟨(contDiff_infty_iff_fderiv.mp hB.1).2, fun n => ?_⟩
  rcases hB.2 (n + 1) with ⟨k, C, hC⟩
  exact ⟨k, C, fun x => by simpa only [norm_iteratedFDeriv_fderiv] using hC x⟩

private lemma poly_norm_mul_exp_neg_sq_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∃ C : ℝ, ∀ x : E, (1 + ‖x‖) ^ N * Real.exp (-a * ‖x‖ ^ 2) ≤ C := by
  refine ⟨2 ^ N * (1 + (Nat.factorial N : ℝ) / a ^ N), fun x => ?_⟩
  have h1 : (1 + ‖x‖) ^ N ≤ 2 ^ N * (1 + ‖x‖ ^ (2 * N)) := by
    by_cases hx : ‖x‖ ≤ 1
    · exact (pow_le_pow_left₀ (by positivity) (by linarith) N).trans
        (le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (by positivity)))
    · have hx1 : 1 ≤ ‖x‖ := le_of_not_ge hx
      calc (1 + ‖x‖) ^ N ≤ (2 * ‖x‖) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
        _ = 2 ^ N * ‖x‖ ^ N := mul_pow _ _ _
        _ ≤ 2 ^ N * (1 + ‖x‖ ^ (2 * N)) := by
          gcongr; linarith [pow_le_pow_right₀ hx1 (by omega : N ≤ 2 * N)]
  have hexp_le : Real.exp (-a * ‖x‖ ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
  have hterm : ‖x‖ ^ (2 * N) * Real.exp (-a * ‖x‖ ^ 2) ≤ (Nat.factorial N : ℝ) / a ^ N := by
    have hpow := Real.pow_div_factorial_le_exp (a * ‖x‖ ^ 2) (mul_nonneg ha.le (sq_nonneg ‖x‖)) N
    rw [mul_pow, ← pow_mul, div_le_iff₀ (by positivity)] at hpow
    rw [show -a * ‖x‖ ^ 2 = -(a * ‖x‖ ^ 2) by ring, Real.exp_neg, ← div_eq_mul_inv,
      div_le_div_iff₀ (Real.exp_pos _) (pow_pos ha N)]
    linarith [hpow]
  calc (1 + ‖x‖) ^ N * Real.exp (-a * ‖x‖ ^ 2)
      ≤ 2 ^ N * (1 + ‖x‖ ^ (2 * N)) * Real.exp (-a * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 2 ^ N * (Real.exp (-a * ‖x‖ ^ 2) + ‖x‖ ^ (2 * N) * Real.exp (-a * ‖x‖ ^ 2)) := by ring
    _ ≤ 2 ^ N * (1 + (Nat.factorial N : ℝ) / a ^ N) := by gcongr

private lemma gaussian_temperate_decay {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E → F),
      B.HasTemperateGrowth → ∀ k : ℕ, ∃ C : ℝ, ∀ x : E,
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => Real.exp (-a * ‖y‖ ^ 2) • B y) x‖ ≤ C := by
  induction n with
  | zero =>
    intro F _ _ B hB k
    rcases hB.2 0 with ⟨m, C₀, hC₀⟩
    obtain ⟨C₁, hC₁⟩ := poly_norm_mul_exp_neg_sq_le (E := E) ha (k + m)
    refine ⟨max C₀ 0 * C₁, fun x => ?_⟩
    rw [norm_iteratedFDeriv_zero, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hBx : ‖B x‖ ≤ max C₀ 0 * (1 + ‖x‖) ^ m := by
      simpa using (hC₀ x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := pow_le_pow_left₀ (norm_nonneg _) (by linarith) k
    calc ‖x‖ ^ k * (Real.exp (-a * ‖x‖ ^ 2) * ‖B x‖)
        ≤ (1 + ‖x‖) ^ k * (Real.exp (-a * ‖x‖ ^ 2) * (max C₀ 0 * (1 + ‖x‖) ^ m)) := by gcongr
      _ = max C₀ 0 * ((1 + ‖x‖) ^ (k + m) * Real.exp (-a * ‖x‖ ^ 2)) := by rw [pow_add]; ring
      _ ≤ max C₀ 0 * C₁ := mul_le_mul_of_nonneg_left (hC₁ x) (le_max_right _ _)
  | succ n ih =>
    intro F _ _ B hB k
    let B₁ : E → (E →L[ℝ] F) := fun y =>
      fderiv ℝ B y + (-2 * a) • (innerSL ℝ y).smulRight (B y)
    have hB₁ : B₁.HasTemperateGrowth := (hasTemperateGrowth_fderiv hB).add
      ((Function.HasTemperateGrowth.const (-2 * a)).smul
        ((ContinuousLinearMap.smulRightL ℝ E F).bilinear_hasTemperateGrowth
          (innerSL ℝ).hasTemperateGrowth hB))
    have hfderiv : fderiv ℝ (fun y => Real.exp (-a * ‖y‖ ^ 2) • B y) =
        fun y => Real.exp (-a * ‖y‖ ^ 2) • B₁ y := by
      ext y v
      have hexp : HasFDerivAt (fun z => Real.exp (-a * ‖z‖ ^ 2))
          ((Real.exp (-a * ‖y‖ ^ 2) * (-2 * a)) • innerSL ℝ y) y := by
        have hsq : HasFDerivAt (fun z : E => -a * ‖z‖ ^ 2) ((-2 * a) • innerSL ℝ y) y := by
          have hnsq : HasFDerivAt (fun z : E => ‖z‖ ^ 2) ((2 : ℕ) • innerSL ℝ y) y := by
            simpa [fderiv_norm_sq_apply] using
              ((contDiff_norm_sq ℝ (n := (1 : ℕ))).differentiable (by simp) y).hasFDerivAt
          convert hnsq.const_mul (-a) using 1; ext w; simp; ring
        convert hsq.exp using 1; ext w; simp; ring
      have hd : HasFDerivAt (fun z => Real.exp (-a * ‖z‖ ^ 2) • B z)
          (Real.exp (-a * ‖y‖ ^ 2) • fderiv ℝ B y +
            ((Real.exp (-a * ‖y‖ ^ 2) * (-2 * a)) • innerSL ℝ y).smulRight (B y)) y :=
        hexp.smul (hB.1.differentiable (by simp) y).hasFDerivAt
      rw [hd.fderiv]; simp [B₁, smul_add, smul_smul, mul_comm]
    obtain ⟨C, hC⟩ := ih (E →L[ℝ] F) B₁ hB₁ k
    exact ⟨C, fun x => by rw [← norm_iteratedFDeriv_fderiv, hfderiv]; exact hC x⟩

/-- Gaussian `x ↦ exp(-π t ‖x‖²)` as a Schwartz function `𝓢(ℝ^d, ℂ)`. -/
noncomputable def gaussianSchwartz (d : ℕ) {t : ℝ} (ht : 0 < t) : 𝓢(Euc d, ℂ) where
  toFun x := (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ)
  smooth' := Complex.ofRealCLM.contDiff.comp (ContDiff.exp (contDiff_const.mul (contDiff_norm_sq ℝ)))
  decay' k n := by
    obtain ⟨C, hC⟩ := gaussian_temperate_decay (E := Euc d) (mul_pos Real.pi_pos ht) n ℂ
      (fun _ => (1 : ℂ)) (Function.HasTemperateGrowth.const 1) k
    exact ⟨C, fun x => by simpa [Complex.real_smul] using hC x⟩

/-- Polynomial in `‖x‖²` times a Gaussian as a Schwartz function `𝓢(ℝ^d, ℂ)`. -/
noncomputable def polyGaussianSchwartz (d : ℕ) {t : ℝ} (ht : 0 < t) (P : ℝ[X]) :
    𝓢(Euc d, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : Euc d => ((P.eval (‖x‖ ^ 2) : ℝ) : ℂ))
    (gaussianSchwartz d ht)

lemma polyGaussianSchwartz_apply (d : ℕ) {t : ℝ} (ht : 0 < t) (P : ℝ[X]) (x : Euc d) :
    polyGaussianSchwartz d ht P x =
      ((P.eval (‖x‖ ^ 2) * Real.exp (-π * t * ‖x‖ ^ 2) : ℝ) : ℂ) := by
  have hP : (fun x : Euc d => ((P.eval (‖x‖ ^ 2) : ℝ) : ℂ)).HasTemperateGrowth := by
    have : (fun x : Euc d => ((P.eval (‖x‖ ^ 2) : ℝ) : ℂ)) =
        fun x => ∑ i ∈ P.support, (P.coeff i : ℂ) * ((‖x‖ ^ 2 : ℝ) : ℂ) ^ i := by
      ext x; rw [Polynomial.eval_eq_sum, Polynomial.sum_def]; push_cast; rfl
    rw [this]
    exact Function.HasTemperateGrowth.sum fun i _ => (Function.HasTemperateGrowth.const _).mul
      ((Complex.ofRealCLM.hasTemperateGrowth.comp (Function.hasTemperateGrowth_norm_sq _)).pow i)
  unfold polyGaussianSchwartz
  rw [SchwartzMap.smulLeftCLM_apply hP]
  change ((P.eval (‖x‖ ^ 2) : ℝ) : ℂ) * ((Real.exp (-π * t * ‖x‖ ^ 2) : ℝ) : ℂ) = _
  rw [← Complex.ofReal_mul]

lemma isRadialSchwartz_poly_gaussian (d : ℕ) {t : ℝ} (ht : 0 < t) (P : ℝ[X]) :
    IsRadialSchwartz d (fun x : Euc d => P.eval (‖x‖ ^ 2) * Real.exp (-π * t * ‖x‖ ^ 2)) :=
  ⟨⟨polyGaussianSchwartz d ht P, fun x => by rw [polyGaussianSchwartz_apply]⟩,
    fun x y hxy => by dsimp only; rw [hxy]⟩

/-- Polar integration on `ℝ^d` (`d ≥ 1`) with `s = π ‖x‖²`. -/
lemma polar_integral_eq {d : ℕ} (hd : 1 ≤ d) (f : ℝ → ℝ) :
    ∫ x : Euc d, f (π * ‖x‖ ^ 2) =
      (Real.Gamma ((d : ℝ) / 2))⁻¹ *
        ∫ s in Ioi (0 : ℝ), s ^ ((d : ℝ) / 2 - 1) * f s := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hrad := MeasureTheory.integral_fun_norm_addHaar
    (μ := (volume : Measure (Euc d))) (fun r : ℝ => f (π * r ^ 2))
  have hvol : (volume : Measure (Euc d)).real (Metric.ball 0 1) =
      π ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1) := by
    have := volume_half_ball_eq hd (r := 2) (by norm_num); norm_num at this; exact this
  rw [finrank_euclideanSpace_fin, hvol] at hrad
  let φ : ℝ → ℝ := fun r => π * r ^ 2
  have himg : φ '' Ioi 0 = Ioi 0 := by
    ext s; simp only [Set.mem_image, Set.mem_Ioi, φ]
    exact ⟨fun ⟨r, hr, h⟩ => h ▸ by positivity,
      fun hs => ⟨Real.sqrt (s / π), Real.sqrt_pos.mpr (by positivity),
        by rw [Real.sq_sqrt (by positivity)]; field_simp⟩⟩
  have hcov := integral_image_eq_integral_abs_deriv_smul (f := φ) (f' := fun r => 2 * π * r)
    measurableSet_Ioi
    (fun r _ => (((hasDerivAt_pow 2 r).const_mul π).congr_deriv (by ring)).hasDerivWithinAt)
    (fun r₁ hr₁ r₂ hr₂ heq => by
      have hr₁p : 0 < r₁ := Set.mem_Ioi.mp hr₁
      have hr₂p : 0 < r₂ := Set.mem_Ioi.mp hr₂
      nlinarith [mul_left_cancel₀ Real.pi_ne_zero heq])
    (fun s : ℝ => s ^ ((d : ℝ) / 2 - 1) * f s)
  rw [himg] at hcov
  have hcov' : ∫ s in Ioi (0 : ℝ), s ^ ((d : ℝ) / 2 - 1) * f s =
      2 * π ^ ((d : ℝ) / 2) * ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * f (π * r ^ 2) := by
    rw [hcov, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hrp : 0 < r := Set.mem_Ioi.mp hr
    rw [abs_of_pos (by positivity : 0 < 2 * π * r), smul_eq_mul]
    have hpow : (π * r ^ 2) ^ ((d : ℝ) / 2 - 1) =
        π ^ ((d : ℝ) / 2 - 1) * r ^ (2 * ((d : ℝ) / 2 - 1)) := by
      rw [Real.mul_rpow Real.pi_pos.le (sq_nonneg r), ← Real.rpow_natCast r 2,
        ← Real.rpow_mul hrp.le, Nat.cast_ofNat]
    have hr1 : r * r ^ (2 * ((d : ℝ) / 2 - 1)) = r ^ (d - 1) := by
      rw [show r * r ^ (2 * ((d : ℝ) / 2 - 1)) = r ^ (1 : ℝ) * r ^ (2 * ((d : ℝ) / 2 - 1)) by simp,
        ← Real.rpow_add hrp, ← Real.rpow_natCast r (d - 1)]
      congr 1; rw [Nat.cast_sub hd]; push_cast; ring
    have hpi : π * π ^ ((d : ℝ) / 2 - 1) = π ^ ((d : ℝ) / 2) := by
      rw [show π * π ^ ((d : ℝ) / 2 - 1) = π ^ (1 : ℝ) * π ^ ((d : ℝ) / 2 - 1) by simp,
        ← Real.rpow_add Real.pi_pos]
      congr 1; ring
    rw [hpow]
    calc 2 * π * r * (π ^ ((d : ℝ) / 2 - 1) * r ^ (2 * ((d : ℝ) / 2 - 1)) * f (π * r ^ 2))
        = 2 * (π * π ^ ((d : ℝ) / 2 - 1)) * (r * r ^ (2 * ((d : ℝ) / 2 - 1)) * f (π * r ^ 2)) := by ring
      _ = 2 * π ^ ((d : ℝ) / 2) * (r ^ (d - 1) * f (π * r ^ 2)) := by rw [hpi, hr1]
  rw [hrad, hcov']
  simp only [nsmul_eq_mul, smul_eq_mul]
  have hdpos : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  rw [Real.Gamma_add_one hdpos.ne']
  field_simp [(Real.Gamma_pos_of_pos hdpos).ne', (Real.rpow_pos_of_pos Real.pi_pos _).ne']

/-- Polynomial recurrence `R_k` for `𝓕((2π‖x‖²)^k exp(-π t ‖x‖²))`. -/
noncomputable def fourierBasisPoly (c : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | k + 1 => (Polynomial.C (2 * c + 2 * k) - Polynomial.X) * fourierBasisPoly c k +
      2 * Polynomial.X * (fourierBasisPoly c k).derivative

lemma fourierBasisPoly_natDegree_le (c : ℝ) : ∀ k : ℕ, (fourierBasisPoly c k).natDegree ≤ k
  | 0 => by simp [fourierBasisPoly]
  | k + 1 => by
    have ih := fourierBasisPoly_natDegree_le c k
    rw [fourierBasisPoly]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (Polynomial.natDegree_mul_le).trans (by
        have h1 : (Polynomial.C (2 * c + 2 * (k : ℝ)) - Polynomial.X).natDegree ≤ 1 := by
          compute_degree!
        omega)
    · exact (Polynomial.natDegree_mul_le).trans (by
        have h2 : (2 * Polynomial.X : ℝ[X]).natDegree ≤ 1 := by compute_degree!
        have h3 := Polynomial.natDegree_derivative_le (p := fourierBasisPoly c k)
        omega)

private lemma integrable_normSq_pow_gaussian (d k : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Euc d => (2 * π * ‖x‖ ^ 2) ^ k * Real.exp (-π * t * ‖x‖ ^ 2)) := by
  have hS : Integrable (polyGaussianSchwartz d ht ((2 * π) ^ k • Polynomial.X ^ k)) :=
    (polyGaussianSchwartz d ht _).integrable
  refine (Complex.reCLM.integrable_comp hS).congr (Eventually.of_forall fun x => ?_)
  simp only [polyGaussianSchwartz_apply, Polynomial.eval_smul, Polynomial.eval_pow,
    Polynomial.eval_X, smul_eq_mul, Complex.reCLM_apply, Complex.ofReal_re]
  ring

theorem fourier_normSq_pow_gaussian (d : ℕ) :
    ∀ (k : ℕ) {t : ℝ} (_ : 0 < t) (y : Euc d),
      𝓕 (fun x : Euc d => ((2 * π * ‖x‖ ^ 2) ^ k * Real.exp (-π * t * ‖x‖ ^ 2) : ℂ)) y =
        ((t ^ (-(d : ℝ) / 2 - k) *
          (fourierBasisPoly ((d : ℝ) / 2) k).eval (2 * π * ‖y‖ ^ 2 / t) *
          Real.exp (-π * ‖y‖ ^ 2 / t) : ℝ) : ℂ) := by
  intro k
  induction k with
  | zero =>
    intro t ht y
    have hG := fourier_gaussian_innerProductSpace (V := Euc d)
      (b := (π * t : ℂ)) (by simpa using mul_pos Real.pi_pos ht) y
    have hfun : (fun x : Euc d => ((2 * π * ‖x‖ ^ 2) ^ 0 * Real.exp (-π * t * ‖x‖ ^ 2) : ℂ)) =
        fun v => Complex.exp (-(π * t : ℂ) * ‖v‖ ^ 2) := by
      ext v; simp [Complex.ofReal_exp, mul_assoc]
    rw [hfun, hG, finrank_euclideanSpace_fin]
    have h1 : ((π : ℂ) / (π * t : ℂ)) ^ ((d : ℂ) / 2) = ((t ^ (-(d : ℝ) / 2) : ℝ) : ℂ) := by
      have hpt : (π : ℂ) / (π * t : ℂ) = ((t⁻¹ : ℝ) : ℂ) := by
        push_cast; field_simp [Real.pi_ne_zero, ht.ne']
      rw [hpt, show (d : ℂ) / 2 = (((d : ℝ) / 2 : ℝ) : ℂ) by push_cast; rfl,
        ← Complex.ofReal_cpow (inv_nonneg.mpr ht.le)]
      congr 1; rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]; congr 1; ring
    have h2 : Complex.exp (-π ^ 2 * ‖y‖ ^ 2 / (π * t : ℂ)) =
        ((Real.exp (-π * ‖y‖ ^ 2 / t) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]; congr 1; push_cast; field_simp [Real.pi_ne_zero, ht.ne']
    rw [h1, h2, ← Complex.ofReal_mul]
    simp [fourierBasisPoly]
  | succ k ih =>
    intro t₀ ht₀ y
    let F : ℝ → Euc d → ℂ := fun t x =>
      ((2 * π * ‖x‖ ^ 2) ^ k * Real.exp (-π * t * ‖x‖ ^ 2) : ℂ) *
        Complex.exp ((-2 * π * ⟪x, y⟫ : ℝ) * Complex.I)
    let F' : ℝ → Euc d → ℂ := fun t x =>
      -(1 / 2 : ℂ) * (((2 * π * ‖x‖ ^ 2) ^ (k + 1) * Real.exp (-π * t * ‖x‖ ^ 2) : ℂ) *
        Complex.exp ((-2 * π * ⟪x, y⟫ : ℝ) * Complex.I))
    have hF_int : Integrable (F t₀) volume := by
      refine (integrable_normSq_pow_gaussian d k ht₀).mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
      dsimp only [F]
      rw [show (2 * ↑π * ↑‖x‖ ^ 2) ^ k * ↑(Real.exp (-π * t₀ * ‖x‖ ^ 2)) =
        (((2 * π * ‖x‖ ^ 2) ^ k * Real.exp (-π * t₀ * ‖x‖ ^ 2) : ℝ) : ℂ) by push_cast; rfl,
        norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    have h_bound : ∀ᵐ x ∂volume, ∀ t ∈ Metric.ball t₀ (t₀ / 2),
        ‖F' t x‖ ≤ (1 / 2 : ℝ) * ((2 * π * ‖x‖ ^ 2) ^ (k + 1) * Real.exp (-π * (t₀ / 2) * ‖x‖ ^ 2)) := by
      refine Eventually.of_forall fun x t ht => ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
      dsimp only [F']
      rw [show (2 * ↑π * ↑‖x‖ ^ 2) ^ (k + 1) * ↑(Real.exp (-π * t * ‖x‖ ^ 2)) =
        (((2 * π * ‖x‖ ^ 2) ^ (k + 1) * Real.exp (-π * t * ‖x‖ ^ 2) : ℝ) : ℂ) by push_cast; rfl,
        norm_mul, norm_mul, norm_neg, norm_div, norm_one, Complex.norm_ofNat,
        Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
          (by nlinarith [Real.pi_pos, ht.1]) (sq_nonneg _)))
        (by positivity)) (by norm_num)
    have h_diff : ∀ᵐ x ∂volume, ∀ t ∈ Metric.ball t₀ (t₀ / 2),
        HasDerivAt (fun s => F s x) (F' t x) t := by
      refine Eventually.of_forall fun x t _ => ?_
      have hd1 : HasDerivAt (fun s : ℝ => Real.exp (-π * s * ‖x‖ ^ 2))
          ((-π * ‖x‖ ^ 2) * Real.exp (-π * t * ‖x‖ ^ 2)) t := by
        simpa [mul_comm] using (((hasDerivAt_id t).const_mul (-π)).mul_const (‖x‖ ^ 2)).exp
      have hd2 := ((hd1.const_mul ((2 * π * ‖x‖ ^ 2) ^ k)).ofReal_comp).mul_const
        (Complex.exp ((-2 * π * ⟪x, y⟫ : ℝ) * Complex.I))
      convert hd2 using 1
      · ext s; simp only [F]; push_cast; rfl
      · dsimp only [F']; push_cast; ring
    have hLHS := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds t₀ (half_pos ht₀))
      (Eventually.of_forall fun _ => by fun_prop) hF_int (by fun_prop)
      h_bound ((integrable_normSq_pow_gaussian d (k + 1) (half_pos ht₀)).const_mul _) h_diff).2
    let c : ℝ := (d : ℝ) / 2
    let R := fourierBasisPoly c k
    let r : ℝ := 2 * π * ‖y‖ ^ 2
    let G : ℝ → ℂ := fun t =>
      ((t ^ (-c - k) * R.eval (r / t) * Real.exp (-π * ‖y‖ ^ 2 / t) : ℝ) : ℂ)
    have heq_on : G =ᶠ[𝓝 t₀] fun s => ∫ x, F s x := by
      filter_upwards [Metric.ball_mem_nhds t₀ (half_pos ht₀)] with t ht
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
      have hih := ih (by linarith) y
      rw [Real.fourier_eq'] at hih
      dsimp only [G, R, c, r]
      rw [show -(↑d / 2 : ℝ) - ↑k = -↑d / 2 - ↑k by ring, ← hih]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [F, smul_eq_mul, mul_comm]
    have hLHS' := hLHS.congr_of_eventuallyEq heq_on
    have hpow_d := Real.hasDerivAt_rpow_const (p := -c - k) (Or.inl ht₀.ne')
    have hdiv : HasDerivAt (fun t : ℝ => r / t) (-(r / t₀ ^ 2)) t₀ :=
      ((hasDerivAt_const t₀ r).div (hasDerivAt_id t₀) ht₀.ne').congr_deriv
        (by simp only [id_eq]; ring)
    have heval_d : HasDerivAt (fun t : ℝ => R.eval (r / t))
        (R.derivative.eval (r / t₀) * -(r / t₀ ^ 2)) t₀ :=
      (R.hasDerivAt (r / t₀)).comp t₀ hdiv
    have hexp_d : HasDerivAt (fun t : ℝ => Real.exp (-π * ‖y‖ ^ 2 / t))
        ((π * ‖y‖ ^ 2 / t₀ ^ 2) * Real.exp (-π * ‖y‖ ^ 2 / t₀)) t₀ :=
      (((hasDerivAt_const t₀ (-π * ‖y‖ ^ 2)).div (hasDerivAt_id t₀) ht₀.ne').exp).congr_deriv
        (by simp only [Pi.div_apply, id_eq]; ring)
    have hG_real : HasDerivAt (fun t : ℝ => t ^ (-c - k) * R.eval (r / t) * Real.exp (-π * ‖y‖ ^ 2 / t))
        (-(1 / 2) * (t₀ ^ (-c - ((k + 1 : ℕ) : ℝ)) *
          (fourierBasisPoly c (k + 1)).eval (r / t₀) * Real.exp (-π * ‖y‖ ^ 2 / t₀))) t₀ := by
      refine ((hpow_d.mul heval_d).mul hexp_d).congr_deriv ?_
      have hR1 : (fourierBasisPoly c (k + 1)).eval (r / t₀) =
          (2 * c + 2 * k - r / t₀) * R.eval (r / t₀) + 2 * (r / t₀) * R.derivative.eval (r / t₀) := by
        simp [fourierBasisPoly, R]
      have hpow_m1 : t₀ ^ (-c - (k : ℝ) - 1) = t₀⁻¹ * t₀ ^ (-c - (k : ℝ)) := by
        rw [sub_eq_add_neg, Real.rpow_add ht₀, Real.rpow_neg_one]; ring
      have hpow_p1 : t₀ ^ (-c - ((k + 1 : ℕ) : ℝ)) = t₀⁻¹ * t₀ ^ (-c - (k : ℝ)) := by
        rw [← hpow_m1]; congr 1; push_cast; ring
      rw [hR1, hpow_m1, hpow_p1]; dsimp [r]; field_simp [ht₀.ne']; ring
    have h_eq := hLHS'.unique (by
      simpa [G, Complex.ofReal_mul, Complex.ofReal_neg] using hG_real.ofReal_comp)
    have hF'_eq : ∫ x : Euc d, F' t₀ x = -(1 / 2 : ℂ) * 𝓕 (fun x : Euc d =>
        ((2 * π * ‖x‖ ^ 2) ^ (k + 1) * Real.exp (-π * t₀ * ‖x‖ ^ 2) : ℂ)) y := by
      simp only [F', integral_const_mul, Real.fourier_eq', smul_eq_mul, mul_comm]
    rw [hF'_eq] at h_eq
    dsimp only [c, r] at h_eq
    rw [show -(↑d / 2 : ℝ) = -↑d / 2 by ring] at h_eq
    rw [Nat.cast_add, Nat.cast_one]
    exact mul_left_cancel₀ (show -(1 / 2 : ℂ) ≠ 0 by norm_num) (by simpa [one_div] using h_eq)

noncomputable def fourierPolyTransform (c : ℝ) (P : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ P.support, P.coeff k • fourierBasisPoly c k

lemma fourierPolyTransform_natDegree_le (c : ℝ) (P : ℝ[X]) :
    (fourierPolyTransform c P).natDegree ≤ P.natDegree :=
  (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun k hk =>
    (Polynomial.natDegree_smul_le _ _).trans
      ((fourierBasisPoly_natDegree_le c k).trans (Polynomial.le_natDegree_of_mem_supp k hk)))

lemma fourierPolyTransform_eval (c : ℝ) {N : ℕ} {P : ℝ[X]} (hP : P.natDegree ≤ N) (x : ℝ) :
    (fourierPolyTransform c P).eval x =
      ∑ k ∈ Finset.range (N + 1), P.coeff k * (fourierBasisPoly c k).eval x := by
  unfold fourierPolyTransform
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_smul, smul_eq_mul]
  refine Finset.sum_subset (fun k hk => Finset.mem_range.mpr
    ((Polynomial.le_natDegree_of_mem_supp k hk).trans_lt (Nat.lt_succ_of_le hP))) ?_
  intro k _ hk
  rw [Polynomial.notMem_support_iff.mp hk, zero_mul]

theorem fourier_poly_gaussian (d : ℕ) (P : ℝ[X]) :
    ∀ y : Euc d,
      𝓕 (fun x : Euc d => (P.eval (2 * π * ‖x‖ ^ 2) * Real.exp (-π * ‖x‖ ^ 2) : ℂ)) y =
        (((fourierPolyTransform ((d : ℝ) / 2) P).eval (2 * π * ‖y‖ ^ 2) *
          Real.exp (-π * ‖y‖ ^ 2) : ℝ) : ℂ) := by
  intro y
  have hsum : (fun x : Euc d => (P.eval (2 * π * ‖x‖ ^ 2) * Real.exp (-π * ‖x‖ ^ 2) : ℂ)) =
      fun x => ∑ k ∈ P.support, (P.coeff k : ℂ) *
        ((2 * π * ‖x‖ ^ 2) ^ k * Real.exp (-π * ‖x‖ ^ 2) : ℂ) := by
    ext x; rw [Polynomial.eval_eq_sum, Polynomial.sum_def]; push_cast; simp [Finset.sum_mul, mul_assoc]
  rw [hsum, Real.fourier_eq']
  simp_rw [smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum _ fun k _ => by
    refine ((integrable_normSq_pow_gaussian d k one_pos).const_mul |P.coeff k|).mono'
      (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [show Complex.exp (↑(-2 * π * ⟪x, y⟫) * I) *
        ((P.coeff k : ℂ) * ((2 * ↑π * ↑‖x‖ ^ 2) ^ k * ↑(Real.exp (-π * ‖x‖ ^ 2)))) =
      Complex.exp (↑(-2 * π * ⟪x, y⟫) * I) *
        (((P.coeff k * ((2 * π * ‖x‖ ^ 2) ^ k * Real.exp (-π * 1 * ‖x‖ ^ 2)) : ℝ) : ℂ)) by
          push_cast; ring_nf,
      norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg (show 0 ≤ (2 * π * ‖x‖ ^ 2) ^ k * Real.exp (-π * 1 * ‖x‖ ^ 2) by
        positivity)]]
  have hterm : ∀ k ∈ P.support,
      (∫ x : Euc d, Complex.exp (↑(-2 * π * ⟪x, y⟫) * I) *
        ((P.coeff k : ℂ) * ((2 * π * ‖x‖ ^ 2) ^ k * Real.exp (-π * ‖x‖ ^ 2) : ℂ))) =
        ((P.coeff k * (fourierBasisPoly ((d : ℝ) / 2) k).eval (2 * π * ‖y‖ ^ 2) *
          Real.exp (-π * ‖y‖ ^ 2) : ℝ) : ℂ) := by
    intro k _
    have hrew : (fun x : Euc d => Complex.exp (↑(-2 * π * ⟪x, y⟫) * I) *
        ((P.coeff k : ℂ) * ((2 * π * ‖x‖ ^ 2) ^ k * Real.exp (-π * ‖x‖ ^ 2) : ℂ))) =
        fun x => (P.coeff k : ℂ) * (Complex.exp (↑(-2 * π * ⟪x, y⟫) * I) *
          ((2 * π * ‖x‖ ^ 2) ^ k * Real.exp (-π * ‖x‖ ^ 2) : ℂ)) := funext fun x => by ring
    rw [hrew, integral_const_mul]
    have hf := fourier_normSq_pow_gaussian d k one_pos y
    rw [Real.fourier_eq'] at hf
    simp only [smul_eq_mul, mul_one, Real.one_rpow, div_one] at hf
    rw [hf, ← Complex.ofReal_mul]; ring_nf
  rw [Finset.sum_congr rfl hterm]
  simp only [fourierPolyTransform, Polynomial.eval_finsetSum, Polynomial.eval_smul, smul_eq_mul]
  push_cast; simp [Finset.sum_mul, mul_assoc]

/-! ### Section 2: Theorem E.1 — Optimized Quadratic Gaussian (`thm:ce-gaussian`, `(eq:finite:E.1)`) -/

noncomputable def quadT (d : ℕ) : ℝ := (2 / ((d : ℝ) + 2)) ^ (2 / (d : ℝ))
noncomputable def quadA (d : ℕ) : ℝ := 2 * π * quadT d / ((d : ℝ) + 2)
noncomputable def quadH (d : ℕ) (x : Euc d) : ℝ :=
  (1 - quadA d * ‖x‖ ^ 2) * Real.exp (-π * quadT d * ‖x‖ ^ 2)
noncomputable def quadR (d : ℕ) : ℝ := (quadA d) ^ (-(1 / 2 : ℝ))
noncomputable def quadD (d : ℕ) : ℝ :=
  ((d : ℝ) + 2) / (2 * Real.Gamma ((d : ℝ) / 2 + 1)) * (((d : ℝ) + 2) / 8) ^ ((d : ℝ) / 2)

lemma quadT_pos {d : ℕ} (hd : 2 ≤ d) : 0 < quadT d := by unfold quadT; positivity
lemma quadA_pos {d : ℕ} (hd : 2 ≤ d) : 0 < quadA d := by
  unfold quadA; exact div_pos (mul_pos (by positivity) (quadT_pos hd)) (by positivity)
lemma quadR_pos {d : ℕ} (hd : 2 ≤ d) : 0 < quadR d := by
  unfold quadR; exact Real.rpow_pos_of_pos (quadA_pos hd) _
lemma quadD_pos {d : ℕ} (hd : 2 ≤ d) : 0 < quadD d := by
  unfold quadD; have := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (d : ℝ) / 2 + 1); positivity

lemma quadT_rpow_half_dim {d : ℕ} (hd : 2 ≤ d) :
    quadT d ^ ((d : ℝ) / 2) = 2 / ((d : ℝ) + 2) := by
  unfold quadT
  rw [← Real.rpow_mul (by positivity), show (2 / (d : ℝ)) * ((d : ℝ) / 2) = 1 by
    have : (d : ℝ) ≠ 0 := by positivity
    field_simp, Real.rpow_one]

lemma quadR_sq {d : ℕ} (hd : 2 ≤ d) : quadR d ^ 2 = (quadA d)⁻¹ := by
  unfold quadR; rw [← Real.rpow_natCast, ← Real.rpow_mul (quadA_pos hd).le]; norm_num [Real.rpow_neg_one]

theorem fourier_quad_cone (d : ℕ) (c₀ a : ℝ) {t : ℝ} (ht : 0 < t) (y : Euc d) :
    𝓕 (fun x : Euc d => (c₀ * (1 - a * ‖x‖ ^ 2) * Real.exp (-π * t * ‖x‖ ^ 2) : ℂ)) y =
      ((c₀ * t ^ (-(d : ℝ) / 2) *
        (1 - a * (d : ℝ) / (2 * π * t) + a / t ^ 2 * ‖y‖ ^ 2) *
        Real.exp (-π * ‖y‖ ^ 2 / t) : ℝ) : ℂ) := by
  have h0 := fourier_normSq_pow_gaussian d 0 ht y
  have h1 := fourier_normSq_pow_gaussian d 1 ht y
  have hf0 : Integrable (fun x : Euc d =>
      Complex.exp (↑(-2 * π * ⟪x, y⟫) * I) * (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ)) :=
    (integrable_normSq_pow_gaussian d 0 ht).mono' (by fun_prop) (Eventually.of_forall fun x => by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le]; simp)
  have hf1 : Integrable (fun x : Euc d =>
      Complex.exp (↑(-2 * π * ⟪x, y⟫) * I) *
        ((2 * π * ‖x‖ ^ 2) * Real.exp (-π * t * ‖x‖ ^ 2) : ℂ)) :=
    (integrable_normSq_pow_gaussian d 1 ht).mono' (by fun_prop) (Eventually.of_forall fun x => by
      rw [show (2 * ↑π * ↑‖x‖ ^ 2 * ↑(Real.exp (-π * t * ‖x‖ ^ 2)) : ℂ) =
        ((((2 * π * ‖x‖ ^ 2) ^ 1 * Real.exp (-π * t * ‖x‖ ^ 2) : ℝ) : ℂ)) by push_cast; ring,
        norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)])
  have hrew : (fun x : Euc d => (c₀ * (1 - a * ‖x‖ ^ 2) * Real.exp (-π * t * ‖x‖ ^ 2) : ℂ)) =
      fun x => (c₀ : ℂ) * (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ) -
        (c₀ * a / (2 * π) : ℂ) * ((2 * π * ‖x‖ ^ 2) * Real.exp (-π * t * ‖x‖ ^ 2) : ℂ) := by
    ext x; push_cast; field_simp [Real.pi_ne_zero]
  rw [hrew, Real.fourier_eq']
  simp_rw [smul_eq_mul, mul_sub]
  rw [integral_sub (by simpa [mul_left_comm] using hf0.const_mul (c₀ : ℂ))
    (by simpa [mul_left_comm] using hf1.const_mul (c₀ * a / (2 * π) : ℂ))]
  have hL0 : ∫ x : Euc d, Complex.exp (↑(-2 * π * ⟪x, y⟫) * I) *
      ((c₀ : ℂ) * (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ)) =
      (c₀ : ℂ) * 𝓕 (fun x : Euc d => ((2 * π * ‖x‖ ^ 2) ^ 0 * Real.exp (-π * t * ‖x‖ ^ 2) : ℂ)) y := by
    rw [Real.fourier_eq', ← integral_const_mul]; congr 1; ext x; simp [smul_eq_mul]; ring
  have hL1 : ∫ x : Euc d, Complex.exp (↑(-2 * π * ⟪x, y⟫) * I) *
      ((c₀ * a / (2 * π) : ℂ) * ((2 * π * ‖x‖ ^ 2) * Real.exp (-π * t * ‖x‖ ^ 2) : ℂ)) =
      (c₀ * a / (2 * π) : ℂ) * 𝓕 (fun x : Euc d =>
        ((2 * π * ‖x‖ ^ 2) ^ 1 * Real.exp (-π * t * ‖x‖ ^ 2) : ℂ)) y := by
    rw [Real.fourier_eq', ← integral_const_mul]; congr 1; ext x; simp [smul_eq_mul]; ring
  rw [hL0, hL1, h0, h1]
  have hR0 : (fourierBasisPoly ((d : ℝ) / 2) 0).eval (2 * π * ‖y‖ ^ 2 / t) = 1 := by
    simp [fourierBasisPoly]
  have hR1 : (fourierBasisPoly ((d : ℝ) / 2) 1).eval (2 * π * ‖y‖ ^ 2 / t) =
      (d : ℝ) - 2 * π * ‖y‖ ^ 2 / t := by simp [fourierBasisPoly]; ring
  have hpow : t ^ (-(d : ℝ) / 2 - 1) = t ^ (-(d : ℝ) / 2) / t := by
    rw [sub_eq_add_neg, Real.rpow_add ht, Real.rpow_neg_one, ← div_eq_mul_inv]
  simp only [Nat.cast_zero, sub_zero, Nat.cast_one] at *
  rw [hR0, hR1, hpow]
  push_cast; field_simp [Real.pi_ne_zero, ht.ne']; ring

theorem quadH_fourier_eq {d : ℕ} (hd : 2 ≤ d) (y : Euc d) :
    𝓕 (fun x : Euc d => (quadH d x : ℂ)) y =
      ((quadT d ^ (-(d : ℝ) / 2) *
        (quadT d ^ ((d : ℝ) / 2) + quadA d / quadT d ^ 2 * ‖y‖ ^ 2) *
        Real.exp (-π * ‖y‖ ^ 2 / quadT d) : ℝ) : ℂ) := by
  have h := fourier_quad_cone d 1 (quadA d) (quadT_pos hd) y
  have hfun : (fun x : Euc d => (quadH d x : ℂ)) =
      fun x => ((1 : ℝ) : ℂ) * (1 - (quadA d : ℂ) * (‖x‖ : ℂ) ^ 2) *
        (Real.exp (-π * quadT d * ‖x‖ ^ 2) : ℂ) := by
    ext x; push_cast; simp [quadH]
  rw [hfun, h]; congr 1
  rw [show 1 - quadA d * (d : ℝ) / (2 * π * quadT d) = quadT d ^ ((d : ℝ) / 2) by
    rw [quadT_rpow_half_dim hd, quadA]; field_simp [Real.pi_ne_zero, (quadT_pos hd).ne']; ring]
  ring

theorem quadH_fourier_pos {d : ℕ} (hd : 2 ≤ d) (y : Euc d) :
    0 < (𝓕 (fun x : Euc d => (quadH d x : ℂ)) y).re := by
  rw [quadH_fourier_eq hd y, Complex.ofReal_re]
  have ht := quadT_pos hd; have ha := quadA_pos hd; positivity

theorem quadH_origin {d : ℕ} (hd : 2 ≤ d) :
    quadH d 0 = 1 ∧ 𝓕 (fun x : Euc d => (quadH d x : ℂ)) 0 = 1 := by
  refine ⟨by simp [quadH], ?_⟩
  rw [quadH_fourier_eq hd 0]
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    add_zero]
  rw [← Real.rpow_add (quadT_pos hd), neg_div, neg_add_cancel, Real.rpow_zero]; simp

theorem quadH_radial (d : ℕ) : IsRadialSchwartz d (quadH d) := by
  have h0 : quadH d = fun x =>
      (Polynomial.C 1 - Polynomial.C (quadA d) * Polynomial.X).eval (‖x‖ ^ 2) *
        Real.exp (-π * quadT d * ‖x‖ ^ 2) := by ext x; simp [quadH]
  rw [h0]
  exact isRadialSchwartz_poly_gaussian d (by unfold quadT; positivity) _

theorem quadH_admissible {d : ℕ} (hd : 2 ≤ d) :
    IsCohnElkiesAdmissible d (quadR d) (quadH d) := by
  obtain ⟨⟨S, hS⟩, _⟩ := quadH_radial d
  have hS_eq : (fun x : Euc d => (quadH d x : ℂ)) = S := funext fun x => (hS x).symm
  refine ⟨quadR_pos hd, by unfold quadH; fun_prop,
    Complex.reCLM.integrable_comp (hS_eq ▸ S.integrable) |>.congr (Eventually.of_forall fun _ => by simp),
    by rw [hS_eq]; exact (𝓕 S).integrable,
    by simp [(quadH_origin hd).1], by simp [(quadH_origin hd).2], ?_, ?_⟩
  · intro x hx
    refine mul_nonpos_of_nonpos_of_nonneg ?_ (Real.exp_pos _).le
    have hsq : (quadA d)⁻¹ ≤ ‖x‖ ^ 2 := by
      rw [← quadR_sq hd]; exact pow_le_pow_left₀ (quadR_pos hd).le hx 2
    linarith [calc (1 : ℝ) = quadA d * (quadA d)⁻¹ := (mul_inv_cancel₀ (quadA_pos hd).ne').symm
      _ ≤ quadA d * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_left hsq (quadA_pos hd).le]
  · intro y
    have hpos := quadH_fourier_pos hd y
    rw [quadH_fourier_eq hd y] at hpos ⊢
    exact ⟨rfl, hpos.le⟩

theorem quadH_bound_eq_quadD {d : ℕ} (hd : 2 ≤ d) :
    cohnElkiesBound d (quadR d) (quadH d) = quadD d := by
  unfold cohnElkiesBound
  rw [(quadH_origin hd).1, (quadH_origin hd).2, Complex.one_re, div_one, one_mul,
    volume_half_ball_eq (by omega) (quadR_pos hd).le, quadR_sq hd]
  have hpi : π * (quadA d)⁻¹ / 4 = (((d : ℝ) + 2) / 8) / quadT d := by
    unfold quadA; field_simp [Real.pi_ne_zero, (quadT_pos hd).ne']; ring
  rw [hpi, Real.div_rpow (by positivity) (quadT_pos hd).le, quadT_rpow_half_dim hd]
  unfold quadD
  field_simp [(Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (d : ℝ) / 2 + 1)).ne']

theorem optimalCohnElkiesBound_le_quadD {d : ℕ} (hd : 2 ≤ d) :
    optimalCohnElkiesBound d ≤ quadD d :=
  (optimalCohnElkiesBound_le (quadH_admissible hd)).trans_eq (quadH_bound_eq_quadD hd)

/-- **Optimality of `D_d` among the two-parameter cone (`thm:ce-gaussian`).** -/
theorem quadD_optimal_among_cone {d : ℕ} (hd : 2 ≤ d) {c₀ a t r : ℝ}
    (hc₀ : 0 < c₀) (ha : 0 < a) (ht : 0 < t) (hr : 0 < r)
    (hnonpos : ∀ x : Euc d, r ≤ ‖x‖ →
      c₀ * (1 - a * ‖x‖ ^ 2) * Real.exp (-π * t * ‖x‖ ^ 2) ≤ 0)
    (hft0 : 0 < (𝓕 (fun x : Euc d =>
      (c₀ * (1 - a * ‖x‖ ^ 2) * Real.exp (-π * t * ‖x‖ ^ 2) : ℂ)) 0).re) :
    quadD d ≤ cohnElkiesBound d r
      (fun x : Euc d => c₀ * (1 - a * ‖x‖ ^ 2) * Real.exp (-π * t * ‖x‖ ^ 2)) := by
  let h : Euc d → ℝ := fun x => c₀ * (1 - a * ‖x‖ ^ 2) * Real.exp (-π * t * ‖x‖ ^ 2)
  have h_cast : (fun x : Euc d => (h x : ℂ)) =
      fun x => (c₀ : ℂ) * (1 - (a : ℂ) * (‖x‖ : ℂ) ^ 2) * (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ) :=
    funext fun x => by dsimp [h]; push_cast; ring
  have h0 : h 0 = c₀ := by simp [h]
  have hft : (𝓕 (fun x : Euc d => (h x : ℂ)) 0).re =
      c₀ * t ^ (-(d : ℝ) / 2) * (1 - a * (d : ℝ) / (2 * π * t)) := by
    rw [h_cast, fourier_quad_cone d c₀ a ht 0, Complex.ofReal_re]; simp
  let u : ℝ := a * (d : ℝ) / (2 * π * t)
  have hu_pos : 0 < u := by positivity
  have hu_lt : u < 1 := by
    rw [← h_cast] at hft0; rw [hft] at hft0
    linarith [pos_of_mul_pos_right hft0 (mul_pos hc₀ (Real.rpow_pos_of_pos ht _)).le]
  have hr_sq : a⁻¹ ≤ r ^ 2 := by
    let x₀ : Euc d := WithLp.toLp 2 (fun i : Fin d => if i = ⟨0, by omega⟩ then r else 0)
    have hx₀ : ‖x₀‖ = r := by
      rw [EuclideanSpace.norm_eq]
      simp [x₀, Finset.sum_ite_eq', Finset.mem_univ, Real.sqrt_sq hr.le]
    have hle := hnonpos x₀ hx₀.symm.le
    rw [hx₀] at hle
    have h1a : 1 - a * r ^ 2 ≤ 0 := by
      by_contra hgt; rw [not_le] at hgt
      exact absurd hle (not_le.mpr (mul_pos (mul_pos hc₀ hgt) (Real.exp_pos _)))
    rw [inv_le_iff_one_le_mul₀' ha]; linarith
  have hbound_ge : ((d : ℝ) / 8) ^ ((d : ℝ) / 2) / (u ^ ((d : ℝ) / 2) * (1 - u) *
      Real.Gamma ((d : ℝ) / 2 + 1)) ≤ cohnElkiesBound d r h := by
    unfold cohnElkiesBound
    rw [h0, hft, volume_half_ball_eq (by omega) hr.le]
    have hpi_le : (d : ℝ) / (8 * t * u) ≤ π * r ^ 2 / 4 := by
      have ha_eq : a = 2 * π * t * u / (d : ℝ) := by
        dsimp [u]; field_simp [Real.pi_ne_zero, ht.ne', (show (d : ℝ) ≠ 0 by positivity)]
      rw [show (d : ℝ) / (8 * t * u) = π * a⁻¹ / 4 by
        rw [ha_eq]; field_simp [Real.pi_ne_zero, ht.ne', hu_pos.ne']; ring]
      gcongr
    have hrpow_le : ((d : ℝ) / (8 * t * u)) ^ ((d : ℝ) / 2) ≤ (π * r ^ 2 / 4) ^ ((d : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) hpi_le (by positivity)
    have h1u : 0 < 1 - u := by linarith
    have hG : 0 < Real.Gamma ((d : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
    have ht_eq : t ^ ((d : ℝ) / 2) * ((d : ℝ) / (8 * t * u)) ^ ((d : ℝ) / 2) =
        ((d : ℝ) / 8) ^ ((d : ℝ) / 2) / u ^ ((d : ℝ) / 2) := by
      rw [show (d : ℝ) / (8 * t * u) = ((d : ℝ) / 8) / (t * u) by ring,
        Real.div_rpow (by positivity) (by positivity), Real.mul_rpow ht.le hu_pos.le]
      field_simp [(Real.rpow_pos_of_pos ht _).ne']
    have hc_eq : c₀ / (c₀ * t ^ (-(d : ℝ) / 2) * (1 - u)) = t ^ ((d : ℝ) / 2) / (1 - u) := by
      have htinv : t ^ (-(d : ℝ) / 2) * t ^ ((d : ℝ) / 2) = 1 := by
        rw [← Real.rpow_add ht, neg_div, neg_add_cancel, Real.rpow_zero]
      calc c₀ / (c₀ * t ^ (-(d : ℝ) / 2) * (1 - u))
          = 1 / (t ^ (-(d : ℝ) / 2) * (1 - u)) := by
            field_simp [hc₀.ne', (Real.rpow_pos_of_pos ht _).ne', h1u.ne']
        _ = t ^ ((d : ℝ) / 2) / (1 - u) := by
            rw [← htinv]; field_simp [(Real.rpow_pos_of_pos ht _).ne', h1u.ne']
    calc ((d : ℝ) / 8) ^ ((d : ℝ) / 2) / (u ^ ((d : ℝ) / 2) * (1 - u) * Real.Gamma ((d : ℝ) / 2 + 1))
        = (t ^ ((d : ℝ) / 2) / (1 - u)) * (((d : ℝ) / (8 * t * u)) ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)) := by
          rw [div_mul_div_comm, ht_eq]
          field_simp [(Real.rpow_pos_of_pos hu_pos _).ne', h1u.ne', hG.ne']
      _ ≤ (c₀ / (c₀ * t ^ (-(d : ℝ) / 2) * (1 - u))) *
            ((π * r ^ 2 / 4) ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)) := by
          rw [hc_eq]; gcongr
  let u₀ : ℝ := (d : ℝ) / ((d : ℝ) + 2)
  have hu₀_pos : 0 < u₀ := by positivity
  have h1u₀_pos : 0 < 1 - u₀ := by
    rw [show 1 - u₀ = 2 / ((d : ℝ) + 2) by dsimp [u₀]; field_simp; ring]; positivity
  have hlog_le : Real.log (u ^ ((d : ℝ) / 2) * (1 - u)) ≤
      Real.log (u₀ ^ ((d : ℝ) / 2) * (1 - u₀)) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hu_pos hu₀_pos)
    have h2 := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < 1 - u) h1u₀_pos)
    have hlin : ((d : ℝ) / 2) * (u / u₀ - 1) + ((1 - u) / (1 - u₀) - 1) = 0 := by
      dsimp [u₀]; field_simp [(show (d : ℝ) ≠ 0 by positivity)]; ring
    have hcomb : ((d : ℝ) / 2) * Real.log (u / u₀) + Real.log ((1 - u) / (1 - u₀)) ≤ 0 := by
      nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ (d : ℝ) / 2)]
    rw [Real.log_div hu_pos.ne' hu₀_pos.ne', Real.log_div (by linarith) h1u₀_pos.ne'] at hcomb
    rw [Real.log_mul (Real.rpow_pos_of_pos hu_pos _).ne' (by linarith),
      Real.log_mul (Real.rpow_pos_of_pos hu₀_pos _).ne' h1u₀_pos.ne',
      Real.log_rpow hu_pos, Real.log_rpow hu₀_pos]
    linarith
  have hprod_le : u ^ ((d : ℝ) / 2) * (1 - u) ≤ u₀ ^ ((d : ℝ) / 2) * (1 - u₀) :=
    (Real.log_le_log_iff (mul_pos (Real.rpow_pos_of_pos hu_pos _) (by linarith))
      (mul_pos (Real.rpow_pos_of_pos hu₀_pos _) h1u₀_pos)).mp hlog_le
  have hD_eq : quadD d = ((d : ℝ) / 8) ^ ((d : ℝ) / 2) /
      (u₀ ^ ((d : ℝ) / 2) * (1 - u₀) * Real.Gamma ((d : ℝ) / 2 + 1)) := by
    have h1u₀ : 1 - u₀ = 2 / ((d : ℝ) + 2) := by dsimp [u₀]; field_simp; ring
    have hdu₀ : ((d : ℝ) / 8) / u₀ = ((d : ℝ) + 2) / 8 := by
      dsimp [u₀]; field_simp [(show (d : ℝ) ≠ 0 by positivity)]
    unfold quadD
    rw [h1u₀, ← hdu₀, Real.div_rpow (by positivity) hu₀_pos.le]
    field_simp [(Real.rpow_pos_of_pos hu₀_pos _).ne', (Real.Gamma_pos_of_pos (by positivity)).ne']
  refine le_trans ?_ hbound_ge
  rw [hD_eq]
  have hGpos : 0 < Real.Gamma ((d : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  exact div_le_div_of_nonneg_left (by positivity)
    (mul_pos (mul_pos (Real.rpow_pos_of_pos hu_pos _) (by linarith)) hGpos)
    (mul_le_mul_of_nonneg_right hprod_le hGpos.le)


/-! ### Axiom Verification -/

/-- info: 'FormalResearch.CohnElkies.optimalCohnElkiesBound_le_quadD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms optimalCohnElkiesBound_le_quadD

/-- info: 'FormalResearch.CohnElkies.quadD_optimal_among_cone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quadD_optimal_among_cone

end FormalResearch.CohnElkies
