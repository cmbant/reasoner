module

public import FormalResearch.CohnElkies.AiryGaussianTransform
public import FormalResearch.CohnElkies.AiryTwistedLaplace

/-!
# `uct:ce-band` (1), reference identity `(uct:hhat-ref-id)`

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:ce-band` (1),
equation `(uct:hhat-ref-id)`.

Main results:
* `airySquare_fourier_ref_general`: for every `a > 0` and `x : ℝ`,
  `(2π)⁻¹ ∫_ℝ (a + i v)^{-1/2} exp((a + i v)³/12 - i v x) dv = 2√π e^{a x} Ai(x)²`.
* `uct_hhat_ref_id`: the paper's scaled identity `(uct:hhat-ref-id)` for every `c > 0` and `x : ℝ`,
  with `ς = c^{-1/3}` and `c_s = (π²/3)^{1/3}` (`ceCs`):
  `(2π)⁻¹ ∫_ℝ (c^{-2/3} + i u)^{-1/2} exp(-i(π²/36)u³ - (π²/12)ς² u² + i(π²/12)ς⁴ u + (π²/36)ς⁶) e^{-i c_s u x} du = (2√π / √c_s) e^{c_s c^{-2/3} x} Ai(x)² ≥ 0`.
  (The paper states `c ≥ 60`; the identity holds for every `c > 0`.)

Class: proved, unconditional.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real FourierTransform

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

private lemma ofReal_mul_cpow_of_pos {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ≠ 0) (s : ℂ) :
    ((r : ℂ) * w) ^ s = (r : ℂ) ^ s * w ^ s := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hrC hw), Complex.cpow_def_of_ne_zero hrC,
    Complex.cpow_def_of_ne_zero hw, Complex.log_ofReal_mul hr hw, ← Complex.ofReal_log hr.le,
    add_mul, Complex.exp_add]

private lemma ofReal_cpow_neg_half {r : ℝ} (hr : 0 < r) :
    (r : ℂ) ^ (-(1 / 2 : ℂ)) = (((√r)⁻¹ : ℝ) : ℂ) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), ← Complex.ofReal_log hr.le]
  rw [show ((Real.log r : ℝ) : ℂ) * -(1 / 2 : ℂ) = ((-(Real.log r / 2) : ℝ) : ℂ) by
    push_cast; ring, ← Complex.ofReal_exp]
  congr 1
  rw [Real.exp_neg, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr]
  congr 2; ring

private lemma norm_add_mul_I_cpow_neg_half_le {a : ℝ} (ha : 0 < a) (v : ℝ) :
    ‖((a : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))‖ ≤ a ^ (-(1 / 2 : ℝ)) := by
  have hz_ne : (a : ℂ) + (v : ℂ) * Complex.I ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hnorm_ge : a ≤ ‖(a : ℂ) + (v : ℂ) * Complex.I‖ := by
    have := Complex.re_le_norm ((a : ℂ) + (v : ℂ) * Complex.I)
    simpa using this
  have hnorm_pos : 0 < ‖(a : ℂ) + (v : ℂ) * Complex.I‖ := lt_of_lt_of_le ha hnorm_ge
  rw [Complex.cpow_def_of_ne_zero hz_ne, Complex.norm_exp]
  have hre : (Complex.log ((a : ℂ) + (v : ℂ) * Complex.I) * -(1 / 2 : ℂ)).re =
      Real.log ‖(a : ℂ) + (v : ℂ) * Complex.I‖ * -(1 / 2 : ℝ) := by
    rw [show -(1 / 2 : ℂ) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.log_re]
  rw [hre, ← Real.rpow_def_of_pos hnorm_pos]
  exact Real.rpow_le_rpow_of_nonpos ha hnorm_ge (by norm_num)

private lemma re_add_mul_I_cube_div_12 (a v : ℝ) :
    (((a : ℂ) + (v : ℂ) * Complex.I) ^ 3 / 12).re = a ^ 3 / 12 - a * v ^ 2 / 4 := by
  have h : ((a : ℂ) + (v : ℂ) * Complex.I) ^ 3 / 12 =
      ((a ^ 3 / 12 - a * v ^ 2 / 4 : ℝ) : ℂ) +
        ((a ^ 2 * v / 4 - v ^ 3 / 12 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring_nf
    simp [Complex.I_sq, Complex.I_pow_three]
    ring
  rw [h, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

private lemma integrable_airySquare_fourier_ref {a : ℝ} (ha : 0 < a) :
    Integrable fun v : ℝ =>
      ((a : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
        Complex.exp (((a : ℂ) + (v : ℂ) * Complex.I) ^ 3 / 12) := by
  have hcont : Continuous fun v : ℝ =>
      ((a : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
        Complex.exp (((a : ℂ) + (v : ℂ) * Complex.I) ^ 3 / 12) := by
    refine Continuous.mul ?_ (by fun_prop)
    refine Continuous.cpow (by fun_prop) continuous_const fun v => Or.inl ?_
    simp [ha]
  have hgauss : Integrable fun v : ℝ => Real.exp (-(a / 4) * v ^ 2) :=
    integrable_exp_neg_mul_sq (by positivity)
  refine (hgauss.const_mul (a ^ (-(1 / 2 : ℝ)) * Real.exp (a ^ 3 / 12))).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  rw [norm_mul, Complex.norm_exp, re_add_mul_I_cube_div_12]
  have hexp : Real.exp (a ^ 3 / 12 - a * v ^ 2 / 4) =
      Real.exp (a ^ 3 / 12) * Real.exp (-(a / 4) * v ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]
  calc ‖((a : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))‖ *
        (Real.exp (a ^ 3 / 12) * Real.exp (-(a / 4) * v ^ 2))
      ≤ a ^ (-(1 / 2 : ℝ)) * (Real.exp (a ^ 3 / 12) * Real.exp (-(a / 4) * v ^ 2)) := by
        gcongr; exact norm_add_mul_I_cpow_neg_half_le ha v
    _ = a ^ (-(1 / 2 : ℝ)) * Real.exp (a ^ 3 / 12) * Real.exp (-(a / 4) * v ^ 2) := by ring

/-- **General Airy-square Fourier reference identity** (Fourier inversion of `(ceo:O11n.7)` at `t = s = 0`):
for every `a > 0` and `x : ℝ`,
`(2π)⁻¹ ∫_ℝ (a + i v)^{-1/2} exp((a + i v)³/12) e^{-i v x} dv = 2√π e^{a x} Ai(x)²`. -/
theorem airySquare_fourier_ref_general {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ((1 / (2 * π) : ℝ) : ℂ) *
        ∫ v : ℝ, ((a : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
          Complex.exp (((a : ℂ) + (v : ℂ) * Complex.I) ^ 3 / 12) *
          Complex.exp (-(((v * x : ℝ) : ℂ) * Complex.I)) =
      ((2 * √π * Real.exp (a * x) * airyAi x ^ 2 : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun u => ((airyAi u ^ 2 * Real.exp (a * u) : ℝ) : ℂ)
  have hf_cont : Continuous f := by
    have := continuous_airyAi; fun_prop
  have hf_int : Integrable f := by
    have h0 := (airy_pair_laplace_eq 0 0 (y := (a : ℂ)) (by simpa using ha)).1
    refine h0.congr (Eventually.of_forall fun u => ?_)
    simp only [f, add_zero, Complex.ofReal_mul, Complex.ofReal_exp, sq]
  have hF_eq : ∀ ξ : ℝ, (𝓕 f) ξ =
      (4 * (π : ℂ) * ((a : ℂ) - ((2 * π * ξ : ℝ) : ℂ) * Complex.I)) ^ (-(1 / 2 : ℂ)) *
        Complex.exp (((a : ℂ) - ((2 * π * ξ : ℝ) : ℂ) * Complex.I) ^ 3 / 12) := by
    intro ξ
    rw [Real.fourier_real_eq_integral_exp_smul]
    let y : ℂ := (a : ℂ) - ((2 * π * ξ : ℝ) : ℂ) * Complex.I
    have hy_re : 0 < y.re := by simp [y, ha]
    have hlap := (airy_pair_laplace_eq 0 0 hy_re).2
    have hcongr : ∫ u : ℝ, Complex.exp (((-2 * π * u * ξ : ℝ) : ℂ) * Complex.I) • f u =
        ∫ u : ℝ, (airyAi (u + 0) : ℂ) * (airyAi (u + 0) : ℂ) * Complex.exp (y * (u : ℂ)) := by
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp only [f, y, smul_eq_mul, add_zero, Complex.ofReal_mul, Complex.ofReal_exp, sq]
      rw [mul_left_comm (Complex.exp _) ((airyAi u : ℂ) * (airyAi u : ℂ)), ← Complex.exp_add]
      congr 2; push_cast; ring
    rw [hcongr, hlap]
    simp [y]
  have h4pi_cpow : ∀ w : ℂ, 0 < w.re →
      (4 * (π : ℂ) * w) ^ (-(1 / 2 : ℂ)) =
        (((2 * √π)⁻¹ : ℝ) : ℂ) * w ^ (-(1 / 2 : ℂ)) := by
    intro w hw
    have h4pi_pos : (0 : ℝ) < 4 * π := by positivity
    have hw_ne : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
    rw [show (4 * (π : ℂ) * w) = ((4 * π : ℝ) : ℂ) * w by push_cast; ring,
      ofReal_mul_cpow_of_pos h4pi_pos hw_ne, ofReal_cpow_neg_half h4pi_pos]
    congr 2
    rw [Real.sqrt_mul (by norm_num), show √4 = 2 by norm_num]
  have hF_int : Integrable (𝓕 f) := by
    have hbase := integrable_airySquare_fourier_ref ha
    have hcomp : Integrable fun ξ : ℝ =>
        ((a : ℂ) + ((-(2 * π * ξ) : ℝ) : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
          Complex.exp (((a : ℂ) + ((-(2 * π * ξ) : ℝ) : ℂ) * Complex.I) ^ 3 / 12) := by
      have h1 := hbase.comp_mul_left' (neg_ne_zero.mpr (by positivity : (2 * π : ℝ) ≠ 0))
      refine h1.congr (Eventually.of_forall fun ξ => ?_)
      simp [mul_assoc]
    refine (hcomp.const_mul (((2 * √π)⁻¹ : ℝ) : ℂ)).congr (Eventually.of_forall fun ξ => ?_)
    dsimp only
    rw [hF_eq ξ, h4pi_cpow _ (by simp [ha])]
    have hsub : (a : ℂ) - ((2 * π * ξ : ℝ) : ℂ) * Complex.I =
        (a : ℂ) + ((-(2 * π * ξ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hsub]; ring
  have hinv := congrFun (hf_cont.fourierInv_fourier_eq hf_int hF_int) x
  rw [Real.fourierInv_eq'] at hinv
  have hstep1 : f x = (((2 * √π)⁻¹ : ℝ) : ℂ) *
      ∫ ξ : ℝ, Complex.exp (2 * ↑π * ↑ξ * ↑x * Complex.I) *
        (((a : ℂ) + ((-(2 * π * ξ) : ℝ) : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
          Complex.exp (((a : ℂ) + ((-(2 * π * ξ) : ℝ) : ℂ) * Complex.I) ^ 3 / 12)) := by
    rw [← hinv, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    dsimp only
    rw [smul_eq_mul, hF_eq ξ, h4pi_cpow _ (by simp [ha])]
    have hsub : (a : ℂ) - ((2 * π * ξ : ℝ) : ℂ) * Complex.I =
        (a : ℂ) + ((-(2 * π * ξ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have hinner : inner ℝ ξ x = x * ξ := rfl
    rw [hsub, hinner]
    have hexp : Complex.exp (((2 * π * (x * ξ) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (2 * ↑π * ↑ξ * ↑x * Complex.I) := by congr 1; push_cast; ring
    rw [hexp]; ring
  have hcov : ∫ ξ : ℝ, Complex.exp (2 * ↑π * ↑ξ * ↑x * Complex.I) *
        (((a : ℂ) + ((-(2 * π * ξ) : ℝ) : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
          Complex.exp (((a : ℂ) + ((-(2 * π * ξ) : ℝ) : ℂ) * Complex.I) ^ 3 / 12)) =
      ((1 / (2 * π) : ℝ) : ℂ) *
        ∫ v : ℝ, ((a : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
          Complex.exp (((a : ℂ) + (v : ℂ) * Complex.I) ^ 3 / 12) *
          Complex.exp (-(((v * x : ℝ) : ℂ) * Complex.I)) := by
    have h1 := Measure.integral_comp_mul_left
      (g := fun v : ℝ => ((a : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
        Complex.exp (((a : ℂ) + (v : ℂ) * Complex.I) ^ 3 / 12) *
        Complex.exp (-(((v * x : ℝ) : ℂ) * Complex.I))) (a := -(2 * π))
    rw [abs_inv, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), Complex.real_smul, ← one_div] at h1
    rw [← h1]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    dsimp only
    have he : -((((-(2 * π) * ξ) * x : ℝ) : ℂ) * Complex.I) =
        2 * ↑π * ↑ξ * ↑x * Complex.I := by push_cast; ring
    rw [he]
    have hv : (-(2 * π) * ξ : ℝ) = -(2 * π * ξ) := by ring
    rw [hv]; ring
  rw [hcov] at hstep1
  have hmul := congrArg (fun z : ℂ => ((2 * √π : ℝ) : ℂ) * z) hstep1
  have hinv_cancel : ((2 * √π : ℝ) : ℂ) * (((2 * √π)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (by positivity : (2 * √π : ℝ) ≠ 0), Complex.ofReal_one]
  rw [← mul_assoc, hinv_cancel, one_mul] at hmul
  rw [← hmul]
  simp only [f, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp]
  ring

/-- **Lemma `uct:ce-band` (1), Airy-square reference identity `(uct:hhat-ref-id)`**
(`CFT/sign_uncertainty/paper/constant_terms_upper.tex`).

For every `c > 0` (with `ς = c^{-1/3}` and `c_s = (π²/3)^{1/3} = ceCs`) and every `x : ℝ`:
`(2π)⁻¹ ∫_ℝ (c^{-2/3} + i u)^{-1/2} exp(-i(π²/36)u³ - (π²/12)ς² u² + i(π²/12)ς⁴ u + (π²/36)ς⁶) e^{-i c_s u x} du = (2√π / √c_s) e^{c_s c^{-2/3} x} Ai(x)² ≥ 0`. -/
theorem uct_hhat_ref_id {c : ℝ} (hc : 0 < c) (x : ℝ) :
    let ς : ℝ := c ^ (-(1 / 3 : ℝ))
    ((1 / (2 * π) : ℝ) : ℂ) *
        ∫ u : ℝ, ((c ^ (-(2 / 3 : ℝ)) : ℝ) + (u : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
          Complex.exp (-Complex.I * ((π ^ 2 / 36 * u ^ 3 : ℝ) : ℂ) -
            ((π ^ 2 / 12 * ς ^ 2 * u ^ 2 : ℝ) : ℂ) +
            Complex.I * ((π ^ 2 / 12 * ς ^ 4 * u : ℝ) : ℂ) +
            ((π ^ 2 / 36 * ς ^ 6 : ℝ) : ℂ)) *
          Complex.exp (-(((ceCs * u * x : ℝ) : ℂ) * Complex.I)) =
      (((2 * √π / √ceCs) * Real.exp (ceCs * c ^ (-(2 / 3 : ℝ)) * x) * airyAi x ^ 2 : ℝ) : ℂ) ∧
    0 ≤ (2 * √π / √ceCs) * Real.exp (ceCs * c ^ (-(2 / 3 : ℝ)) * x) * airyAi x ^ 2 := by
  dsimp only
  have hcs_pos : 0 < ceCs := ceCs_pos
  have hc23_pos : 0 < c ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hc _
  have ha_pos : 0 < ceCs * c ^ (-(2 / 3 : ℝ)) := mul_pos hcs_pos hc23_pos
  refine ⟨?_, by positivity⟩
  have hgen := airySquare_fourier_ref_general ha_pos x
  have hς2 : (c ^ (-(1 / 3 : ℝ))) ^ 2 = c ^ (-(2 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; congr 1; norm_num
  have hcs3 : ceCs ^ 3 = π ^ 2 / 3 := by
    unfold ceCs
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hphase : ∀ u : ℝ,
      (((ceCs * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) + ((ceCs * u : ℝ) : ℂ) * Complex.I) ^ 3 / 12 =
        -Complex.I * ((π ^ 2 / 36 * u ^ 3 : ℝ) : ℂ) -
          ((π ^ 2 / 12 * (c ^ (-(1 / 3 : ℝ))) ^ 2 * u ^ 2 : ℝ) : ℂ) +
          Complex.I * ((π ^ 2 / 12 * (c ^ (-(1 / 3 : ℝ))) ^ 4 * u : ℝ) : ℂ) +
          ((π ^ 2 / 36 * (c ^ (-(1 / 3 : ℝ))) ^ 6 : ℝ) : ℂ) := by
    intro u
    have hfac : ((ceCs * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) + ((ceCs * u : ℝ) : ℂ) * Complex.I =
        (ceCs : ℂ) * (((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) ^ 2 + (u : ℂ) * Complex.I) := by
      rw [← hς2]; push_cast; ring
    rw [hfac, mul_pow, show (ceCs : ℂ) ^ 3 = ((π ^ 2 / 3 : ℝ) : ℂ) by exact_mod_cast hcs3]
    push_cast
    ring_nf
    simp [Complex.I_sq, Complex.I_pow_three]
    ring
  have hcpow_cs : ∀ u : ℝ,
      (((ceCs * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) + ((ceCs * u : ℝ) : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) =
        (((√ceCs)⁻¹ : ℝ) : ℂ) * (((c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) + (u : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) := by
    intro u
    have hu_ne : ((c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) + (u : ℂ) * Complex.I ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    rw [show ((ceCs * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) + ((ceCs * u : ℝ) : ℂ) * Complex.I =
        (ceCs : ℂ) * (((c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) + (u : ℂ) * Complex.I) by push_cast; ring,
      ofReal_mul_cpow_of_pos hcs_pos hu_ne, ofReal_cpow_neg_half hcs_pos]
  have hcov := Measure.integral_comp_mul_left
    (g := fun v : ℝ => (((ceCs * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
      Complex.exp ((((ceCs * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 / 12) *
      Complex.exp (-(((v * x : ℝ) : ℂ) * Complex.I))) (a := ceCs)
  rw [abs_inv, abs_of_pos hcs_pos] at hcov
  have hstep : ∫ u : ℝ, ((c ^ (-(2 / 3 : ℝ)) : ℝ) + (u : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
        Complex.exp (-Complex.I * ((π ^ 2 / 36 * u ^ 3 : ℝ) : ℂ) -
          ((π ^ 2 / 12 * (c ^ (-(1 / 3 : ℝ))) ^ 2 * u ^ 2 : ℝ) : ℂ) +
          Complex.I * ((π ^ 2 / 12 * (c ^ (-(1 / 3 : ℝ))) ^ 4 * u : ℝ) : ℂ) +
          ((π ^ 2 / 36 * (c ^ (-(1 / 3 : ℝ))) ^ 6 : ℝ) : ℂ)) *
        Complex.exp (-(((ceCs * u * x : ℝ) : ℂ) * Complex.I)) =
      ((1 / √ceCs : ℝ) : ℂ) *
        ∫ v : ℝ, (((ceCs * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
          Complex.exp ((((ceCs * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 / 12) *
          Complex.exp (-(((v * x : ℝ) : ℂ) * Complex.I)) := by
    have hmul := congrArg (fun z : ℂ => (√ceCs : ℂ) * z) hcov
    rw [Complex.real_smul] at hmul
    have h1 : (√ceCs : ℂ) * (((ceCs⁻¹ : ℝ) : ℂ) *
        ∫ v : ℝ, (((ceCs * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
          Complex.exp ((((ceCs * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 / 12) *
          Complex.exp (-(((v * x : ℝ) : ℂ) * Complex.I))) =
        ((1 / √ceCs : ℝ) : ℂ) *
          ∫ v : ℝ, (((ceCs * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
            Complex.exp ((((ceCs * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 / 12) *
            Complex.exp (-(((v * x : ℝ) : ℂ) * Complex.I)) := by
      rw [← mul_assoc, ← Complex.ofReal_mul]
      congr 2
      have hsq : √ceCs * √ceCs = ceCs := Real.mul_self_sqrt hcs_pos.le
      have hne : √ceCs ≠ 0 := (Real.sqrt_pos.mpr hcs_pos).ne'
      field_simp [hne, hcs_pos.ne']
      linarith [hsq]
    rw [← h1, ← hmul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    rw [hcpow_cs u, hphase u]
    have hinv : (√ceCs : ℂ) * (((√ceCs)⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.mpr hcs_pos).ne', Complex.ofReal_one]
    calc ((c ^ (-(2 / 3 : ℝ)) : ℝ) + (u : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) * _ * _
        = 1 * (((c ^ (-(2 / 3 : ℝ)) : ℝ) + (u : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) * _ * _) := (one_mul _).symm
      _ = (√ceCs : ℂ) * (((√ceCs)⁻¹ : ℝ) : ℂ) *
            (((c ^ (-(2 / 3 : ℝ)) : ℝ) + (u : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) * _ * _) := by rw [hinv]
      _ = _ := by ring
  rw [hstep, mul_left_comm, hgen]
  push_cast; ring

/-- info: 'FormalResearch.SignUncertainty.airySquare_fourier_ref_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airySquare_fourier_ref_general

/-- info: 'FormalResearch.SignUncertainty.uct_hhat_ref_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_hhat_ref_id

end FormalResearch.SignUncertainty
