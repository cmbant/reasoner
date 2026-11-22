module

public import Mathlib

/-!
# Paper J, Theorem B, L3.D step 2: the Fourier--Schur multiplier bound (`cor:thb-stable`)

Source: Paper J `thmB.tex`, Corollary `cor:thb-stable` (Section `sec:thb-stable`), proof, second step: for a
function `f` with integrable Fourier transform, the Hadamard product `(f(x_j - y_k) E_jk)` has operator norm at most
`(2 pi)^{-1} ||fhat||_1 ||E||`, the Bhatia--Davis--McIntosh Fourier--Schur argument (Paper J's `BhatiaDavisMcIntosh1983`).
Paper convention: `fhat(t) = int f(u) e^{-itu} du`, so that `f(u) = (2 pi)^{-1} int fhat(t) e^{itu} dt`.

Claim class: **proved** for the abstract form (hypothesis `hrep`, stated below); **proved** for the Mathlib form
(continuous `f` in `L^1` with Mathlib's `𝓕 f` in `L^1`), where `hrep` is Mathlib's Fourier inversion.

## Proved here (axiom-pinned)

* `thb_schur_fourier_norm_le` (abstract form).  Let `g : ℝ → ℂ` be integrable with
  `f(u) = (2 pi)^{-1} int g(t) e^{itu} dt` for all real `u` (`hrep`).  Then for `x : Fin n → ℝ`,
  `y : Fin m → ℝ`, `E : Matrix (Fin n) (Fin m) ℂ`,
  `||(f(x_j - y_k) E_jk)||_op <= (2 pi)^{-1} (int ||g(t)|| dt) ||E||_op`.
  No boundedness or measurability of `f` is assumed: `hrep` gives `|f| <= (2 pi)^{-1} ||g||_1`.
  `g` plays the role of `fhat`.
* `thb_fourier_inv_angular`: Mathlib's Fourier inversion (`Continuous.fourierInv_fourier_eq`, for `f` continuous,
  integrable and with integrable `𝓕 f`) in the angular normalisation of the paper:
  `f(u) = (2 pi)^{-1} int 𝓕 f((2 pi)^{-1} t) e^{itu} dt`.  So `hrep` holds with `g t = 𝓕 f ((2 pi)^{-1} t)`.
* `thb_schur_fourier_norm_le_L1` (Mathlib form): for continuous `f` in `L^1` with `𝓕 f` in `L^1`,
  `||(f(x_j - y_k) E_jk)||_op <= (int ||𝓕 f(v)|| dv) ||E||_op`.  With `c_f = ||fhat||_1 / (2 pi)` of the paper,
  `c_f = int |𝓕 f|`, so this is the paper's constant.

## Differences from the paper

* The paper states the bound for `f` with `fhat` in `L^1` and leaves the representation `hrep` implicit.  The
  abstract theorem takes `hrep` as a hypothesis, and the Mathlib-form theorem derives it from `L^1`
  inversion.
* Mathlib's `𝓕` uses `e^{-2 pi i v w}`; `thb_fourier_inv_angular` converts it to the paper's `e^{-itu}`.
* The paper's concrete `f = chi/x` is in `L^2` but not in `L^1` (it is `1/x` at infinity), so
  `thb_schur_fourier_norm_le_L1` does not apply to it.  Its representation needs `L^2` Fourier inversion, which
  this Mathlib pin does not have (inversion is stated for `L^1`).

## Not formalised

* The concrete `f = chi/x`: its representation `hrep` and `fhat in L^1` (the `L^2` inversion above).
* The scaling `f_gamma(x) = gamma^{-1} f(x/gamma)` and the eigenvector-side identities (`Lambda V - V Lambda' = E`,
  `V - diag V` as the Hadamard product); these are used by the assembly of `cor:thb-stable`, not here.
-/

@[expose] public section

open MeasureTheory Complex

namespace FormalResearch.JacobiEigenvectors.TheoremB

open scoped Matrix.Norms.L2Operator

namespace ThbSchur

variable {n m : ℕ}

/-- The unit-modulus diagonal `diag(exp(i t x_j))`. -/
noncomputable def phaseMat {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℝ) (x : ι → ℝ) :
    Matrix ι ι ℂ :=
  Matrix.diagonal fun j => Complex.exp (Complex.I * ((t * x j : ℝ) : ℂ))

lemma norm_phaseMat_le {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℝ) (x : ι → ℝ) :
    ‖phaseMat t x‖ ≤ 1 := by
  unfold phaseMat
  rw [Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  simp [Complex.norm_exp]

lemma continuous_phaseMat {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) :
    Continuous fun t : ℝ => phaseMat t x := by
  unfold phaseMat
  refine Continuous.matrix_diagonal ?_
  refine continuous_pi fun j => ?_
  fun_prop

/-- The conjugated kernel `diag(e^{itx}) E diag(e^{-ity})` has operator norm at most `||E||`. -/
lemma norm_T_le (t : ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ) (E : Matrix (Fin n) (Fin m) ℂ) :
    ‖phaseMat t x * E * phaseMat t (fun k => -y k)‖ ≤ ‖E‖ := by
  calc ‖phaseMat t x * E * phaseMat t (fun k => -y k)‖
      ≤ ‖phaseMat t x * E‖ * ‖phaseMat t (fun k => -y k)‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖phaseMat t x‖ * ‖E‖) * ‖phaseMat t (fun k => -y k)‖ := by
        gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * ‖E‖) * 1 := by
        gcongr
        · exact norm_phaseMat_le _ _
        · exact norm_phaseMat_le _ _
    _ = ‖E‖ := by ring

lemma T_apply (t : ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ) (E : Matrix (Fin n) (Fin m) ℂ) (j : Fin n)
    (k : Fin m) :
    (phaseMat t x * E * phaseMat t (fun k => -y k)) j k =
      Complex.exp (Complex.I * ((t * x j : ℝ) : ℂ)) * E j k *
        Complex.exp (Complex.I * ((t * (-y k) : ℝ) : ℂ)) := by
  simp [phaseMat]

/-- Evaluation of the entry `(j, k)` as a continuous linear functional on matrices. -/
noncomputable def entryCLM (j : Fin n) (k : Fin m) : Matrix (Fin n) (Fin m) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.proj k : (Fin m → ℂ) →ₗ[ℂ] ℂ).comp
      (LinearMap.proj j : (Fin n → Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)))

lemma entryCLM_apply (j : Fin n) (k : Fin m) (M : Matrix (Fin n) (Fin m) ℂ) :
    entryCLM j k M = M j k := rfl

end ThbSchur

open ThbSchur in
/-- **Fourier--Schur multiplier bound** (abstract form, Paper J `cor:thb-stable`, step 2).  With
`g` integrable and `f(u) = (2 pi)^{-1} int g(t) e^{itu} dt` (`hrep`), the Hadamard product
`(f(x_j - y_k) E_jk)` has operator norm at most `(2 pi)^{-1} ||g||_1 ||E||`. -/
theorem thb_schur_fourier_norm_le (f g : ℝ → ℂ) (hg : Integrable g)
    (hrep : ∀ u : ℝ, f u = ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ) *
      ∫ t : ℝ, g t * Complex.exp (Complex.I * ((t * u : ℝ) : ℂ)))
    {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ) (E : Matrix (Fin n) (Fin m) ℂ) :
    ‖Matrix.of fun j k => f (x j - y k) * E j k‖ ≤ (2 * Real.pi)⁻¹ * (∫ t, ‖g t‖) * ‖E‖ := by
  set c : ℂ := (((2 * Real.pi)⁻¹ : ℝ) : ℂ) with hc
  set F : ℝ → Matrix (Fin n) (Fin m) ℂ :=
    fun t => (c * g t) • (phaseMat t x * E * phaseMat t (fun k => -y k)) with hF
  have hTcont : Continuous fun t : ℝ => phaseMat t x * E * phaseMat t (fun k => -y k) :=
    ((continuous_phaseMat x).matrix_mul continuous_const).matrix_mul
      (continuous_phaseMat (fun k => -y k))
  have hFmeas : AEStronglyMeasurable F volume :=
    (hg.aestronglyMeasurable.const_mul c).smul hTcont.aestronglyMeasurable
  have hFbound : ∀ t, ‖F t‖ ≤ ‖c‖ * ‖g t‖ * ‖E‖ := by
    intro t
    simp only [hF, norm_smul, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_T_le t x y E) (by positivity)
  have hbdint : Integrable (fun t => ‖c‖ * ‖E‖ * ‖g t‖) volume := hg.norm.const_mul _
  have hFint : Integrable F volume :=
    Integrable.mono' hbdint hFmeas (ae_of_all _ fun t => (hFbound t).trans_eq (by ring))
  have hH : (Matrix.of fun j k => f (x j - y k) * E j k) = ∫ t, F t := by
    ext j k
    have h1 : entryCLM j k (∫ t, F t) = ∫ t, entryCLM j k (F t) :=
      ((entryCLM j k).integral_comp_comm hFint).symm
    have hLF : ∀ t, entryCLM j k (F t) =
        c * E j k * (g t * Complex.exp (Complex.I * ((t * (x j - y k) : ℝ) : ℂ))) := by
      intro t
      have hexp : Complex.exp (Complex.I * ((t * x j : ℝ) : ℂ)) *
          Complex.exp (Complex.I * ((t * (-y k) : ℝ) : ℂ)) =
          Complex.exp (Complex.I * ((t * (x j - y k) : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [entryCLM_apply, hF]
      simp only [Matrix.smul_apply, smul_eq_mul, T_apply]
      rw [← hexp]; ring
    simp only [entryCLM_apply, hLF, integral_const_mul] at h1
    simp only [Matrix.of_apply]
    rw [h1, hrep (x j - y k)]
    ring
  rw [hH]
  calc ‖∫ t, F t‖ ≤ ∫ t, ‖c‖ * ‖E‖ * ‖g t‖ :=
        norm_integral_le_of_norm_le hbdint (ae_of_all _ fun t => (hFbound t).trans_eq (by ring))
    _ = (2 * Real.pi)⁻¹ * (∫ t, ‖g t‖) * ‖E‖ := by
        rw [integral_const_mul, hc, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        ring

open FourierTransform in
/-- **Mathlib Fourier inversion in the paper's angular normalisation.**  For `f` continuous, integrable, with
`𝓕 f` integrable: `f(u) = (2 pi)^{-1} int 𝓕 f((2 pi)^{-1} t) e^{itu} dt`.  This is `hrep` with `g = 𝓕 f((2 pi)^{-1} ·)`. -/
theorem thb_fourier_inv_angular (f : ℝ → ℂ) (hc : Continuous f) (hf : Integrable f)
    (hF : Integrable (𝓕 f)) (u : ℝ) :
    f u = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
      ∫ t : ℝ, 𝓕 f ((2 * Real.pi)⁻¹ * t) * Complex.exp (Complex.I * ((t * u : ℝ) : ℂ)) := by
  have h1 := congrFun (hc.fourierInv_fourier_eq hf hF) u
  rw [Real.fourierInv_eq'] at h1
  have hin : ∀ a b : ℝ, (inner ℝ a b : ℝ) = b * a := fun a b => by simp
  have hscale := MeasureTheory.Measure.integral_comp_mul_left
    (fun v : ℝ => Complex.exp (((2 * Real.pi * inner ℝ v u : ℝ) : ℂ) * Complex.I) • 𝓕 f v)
    (2 * Real.pi)⁻¹
  have hpt : ∀ x : ℝ, Complex.exp (((2 * Real.pi * inner ℝ ((2 * Real.pi)⁻¹ * x) u : ℝ) : ℂ) *
      Complex.I) • 𝓕 f ((2 * Real.pi)⁻¹ * x) =
      𝓕 f ((2 * Real.pi)⁻¹ * x) * Complex.exp (Complex.I * ((x * u : ℝ) : ℂ)) := by
    intro x
    have hexp : ((2 * Real.pi * inner ℝ ((2 * Real.pi)⁻¹ * x) u : ℝ) : ℂ) * Complex.I =
        Complex.I * ((x * u : ℝ) : ℂ) := by
      rw [hin]
      push_cast
      field_simp
    rw [smul_eq_mul, mul_comm, hexp]
  have habs : |((2 * Real.pi)⁻¹)⁻¹| = 2 * Real.pi := by
    rw [inv_inv, abs_of_pos (by positivity)]
  rw [habs] at hscale
  simp only [hpt] at hscale
  rw [h1] at hscale
  rw [hscale, Complex.real_smul]
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ hπ, one_mul]

open FourierTransform in
/-- **Fourier--Schur bound, Mathlib form.**  For `f` continuous, integrable, with `𝓕 f` integrable:
`||(f(x_j - y_k) E_jk)||_op <= (int ||𝓕 f(v)|| dv) ||E||_op`, i.e. `(2 pi)^{-1} ||fhat||_1 ||E||` in the paper's
normalisation. -/
theorem thb_schur_fourier_norm_le_L1 (f : ℝ → ℂ) (hc : Continuous f) (hf : Integrable f)
    (hF : Integrable (𝓕 f)) {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ)
    (E : Matrix (Fin n) (Fin m) ℂ) :
    ‖Matrix.of fun j k => f (x j - y k) * E j k‖ ≤ (∫ v : ℝ, ‖𝓕 f v‖) * ‖E‖ := by
  have hg : Integrable (fun t : ℝ => 𝓕 f ((2 * Real.pi)⁻¹ * t)) :=
    hF.comp_mul_left' (R := (2 * Real.pi)⁻¹) (by positivity)
  refine (thb_schur_fourier_norm_le f (fun t : ℝ => 𝓕 f ((2 * Real.pi)⁻¹ * t)) hg
    (fun u => thb_fourier_inv_angular f hc hf hF u) x y E).trans (le_of_eq ?_)
  have hscale := MeasureTheory.Measure.integral_comp_mul_left (fun v : ℝ => ‖𝓕 f v‖)
    (2 * Real.pi)⁻¹
  have habs : |((2 * Real.pi)⁻¹)⁻¹| = 2 * Real.pi := by
    rw [inv_inv, abs_of_pos (by positivity)]
  rw [habs, smul_eq_mul] at hscale
  rw [hscale]
  field_simp

end FormalResearch.JacobiEigenvectors.TheoremB

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.thb_schur_fourier_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.thb_schur_fourier_norm_le

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.thb_fourier_inv_angular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.thb_fourier_inv_angular

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.thb_schur_fourier_norm_le_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.thb_schur_fourier_norm_le_L1
