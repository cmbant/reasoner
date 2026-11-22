module

public import FormalResearch.Complex.StripPoisson
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Strip Poisson Representation (Lemma TE.1(a))

Source: `CFT/common/two_edge_bootstrap.tex` (Lemma `TE.1` `teb:kernel`, part `(a)`, l.22–26).

* `stripCauchyKernel`: the holomorphic strip Schwarz/Poisson kernel
  `π i ((exp(i π (ζ - ζ₀)) - 1)⁻¹ - (exp(i π (ζ + conj ζ₀)) - 1)⁻¹)`.
* `stripPoisson_representation`: for `H : ℂ → ℂ` continuous and bounded on the closed strip
  `0 ≤ Re ζ ≤ 1` and holomorphic on `0 < Re ζ < 1`,
  `H ζ₀ = ∫ τ : ℝ, p(τ - η₀) H(i τ) + p₁(τ - η₀) H(1 + i τ)`.
* `stripPoisson_representation_symm`: when `H(1 - ζ) = ε H(ζ)` (`ε : ℝ`), folding by
  reflection gives `H ζ₀ = ∫ τ : ℝ, Q(τ) H(i τ)` with `Q(τ) = p(τ - η₀) + ε p₁(τ + η₀)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.StripBand

open FormalResearch.StripPoisson

section StripCauchyKernel

/-- Holomorphic strip Schwarz/Poisson kernel centered at `ζ₀`, with simple pole at `ζ₀`
and boundary values `-2π p(τ - η₀)` on `Re ζ = 0` and `+2π p₁(τ - η₀)` on `Re ζ = 1`. -/
noncomputable def stripCauchyKernel (ζ₀ ζ : ℂ) : ℂ :=
  (π : ℂ) * Complex.I *
    ((Complex.exp (Complex.I * (π : ℂ) * (ζ - ζ₀)) - 1)⁻¹ -
      (Complex.exp (Complex.I * (π : ℂ) * (ζ + starRingEnd ℂ ζ₀)) - 1)⁻¹)

private lemma exp_I_pi_mul_ne_one_of_re_mem_Ioo {w : ℂ} (h0 : -2 < w.re) (h2 : w.re < 2)
    (hw : w ≠ 0) :
    Complex.exp (Complex.I * (π : ℂ) * w) ≠ 1 := by
  rw [ne_eq, Complex.exp_eq_one_iff]
  rintro ⟨k, hk⟩
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h_eq : w = (2 * (k : ℂ)) := by
    have h1 : Complex.I * (π : ℂ) * w = (Complex.I * (π : ℂ)) * (2 * (k : ℂ)) := by
      rw [hk]; ring
    exact mul_left_cancel₀ (mul_ne_zero hI hpi) h1
  have hre : w.re = 2 * (k : ℝ) := by
    rw [h_eq]; simp
  have hk_int : k = 0 := by
    have hlt1 : (-1 : ℝ) < (k : ℝ) := by linarith
    have hlt2 : (k : ℝ) < 1 := by linarith
    have hk1 : (-1 : ℤ) < k := by exact_mod_cast hlt1
    have hk2 : k < (1 : ℤ) := by exact_mod_cast hlt2
    omega
  apply hw
  rw [h_eq, hk_int]
  simp

private lemma exp_I_pi_sub_ne_one {ζ₀ ζ : ℂ} (hσ₀ : 0 < ζ₀.re) (hσ₁ : ζ₀.re < 1)
    (hζ₀ : 0 ≤ ζ.re) (hζ₁ : ζ.re ≤ 1) (hne : ζ ≠ ζ₀) :
    Complex.exp (Complex.I * (π : ℂ) * (ζ - ζ₀)) - 1 ≠ 0 := by
  refine sub_ne_zero.mpr (exp_I_pi_mul_ne_one_of_re_mem_Ioo ?_ ?_ (sub_ne_zero.mpr hne))
  · simp only [Complex.sub_re]; linarith
  · simp only [Complex.sub_re]; linarith

private lemma exp_I_pi_add_conj_ne_one {ζ₀ ζ : ℂ} (hσ₀ : 0 < ζ₀.re) (hσ₁ : ζ₀.re < 1)
    (hζ₀ : 0 ≤ ζ.re) (hζ₁ : ζ.re ≤ 1) :
    Complex.exp (Complex.I * (π : ℂ) * (ζ + starRingEnd ℂ ζ₀)) - 1 ≠ 0 := by
  have hre_pos : 0 < (ζ + starRingEnd ℂ ζ₀).re := by
    simp only [Complex.add_re, Complex.conj_re]; linarith
  refine sub_ne_zero.mpr (exp_I_pi_mul_ne_one_of_re_mem_Ioo ?_ ?_ ?_)
  · linarith
  · simp only [Complex.add_re, Complex.conj_re]; linarith
  · intro h
    have h1 := congrArg Complex.re h
    simp only [Complex.zero_re] at h1
    linarith

private lemma stripCauchyKernel_left_edge {ζ₀ : ℂ} (hσ₀ : 0 < ζ₀.re) (hσ₁ : ζ₀.re < 1) (τ : ℝ) :
    stripCauchyKernel ζ₀ ((τ : ℂ) * Complex.I) =
      ((-2 * π * stripPoissonP ζ₀.re (τ - ζ₀.im) : ℝ) : ℂ) := by
  set σ₀ := ζ₀.re
  set s := τ - ζ₀.im
  have h1 : Complex.I * (π : ℂ) * ((τ : ℂ) * Complex.I - ζ₀) =
      ((-π * s : ℝ) : ℂ) + ((-π * σ₀ : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im]
      dsimp [σ₀, s]; ring
    · simp only [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im]
      dsimp [σ₀, s]; ring
  have h2 : Complex.I * (π : ℂ) * ((τ : ℂ) * Complex.I + starRingEnd ℂ ζ₀) =
      ((-π * s : ℝ) : ℂ) + ((π * σ₀ : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
      dsimp [σ₀, s]; ring
    · simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
      dsimp [σ₀, s]; ring
  set α : ℂ := ((Real.exp (-π * s) : ℝ) : ℂ)
  set c : ℂ := ((Real.cos (π * σ₀) : ℝ) : ℂ)
  set sn : ℂ := ((Real.sin (π * σ₀) : ℝ) : ℂ)
  have hu : Complex.exp (Complex.I * (π : ℂ) * ((τ : ℂ) * Complex.I - ζ₀)) =
      α * (c - sn * Complex.I) := by
    rw [h1, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I,
      show ((-π * σ₀ : ℝ) : ℂ) = -((π * σ₀ : ℝ) : ℂ) by push_cast; ring,
      Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    dsimp [α, c, sn]; ring
  have hv : Complex.exp (Complex.I * (π : ℂ) * ((τ : ℂ) * Complex.I + starRingEnd ℂ ζ₀)) =
      α * (c + sn * Complex.I) := by
    rw [h2, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
  have hne1 : α * (c - sn * Complex.I) - 1 ≠ 0 := by
    rw [← hu]
    exact exp_I_pi_sub_ne_one hσ₀ hσ₁ (by simp) (by simp) (fun heq => by
      have := congrArg Complex.re heq
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
        mul_zero] at this
      linarith)
  have hne2 : α * (c + sn * Complex.I) - 1 ≠ 0 := by
    rw [← hv]
    exact exp_I_pi_add_conj_ne_one hσ₀ hσ₁ (by simp) (by simp)
  have hα_ne : α ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hpy : c ^ 2 + sn ^ 2 = 1 := by
    dsimp [c, sn]; exact_mod_cast Real.cos_sq_add_sin_sq (π * σ₀)
  have hden_real : (α * (c - sn * Complex.I) - 1) * (α * (c + sn * Complex.I) - 1) =
      2 * α * (((Real.cosh (π * s) - Real.cos (π * σ₀) : ℝ) : ℂ)) := by
    have hcosh : (2 * α * ((Real.cosh (π * s) : ℝ) : ℂ)) = α ^ 2 + 1 := by
      have hα_inv : Real.exp (π * s) = (Real.exp (-π * s))⁻¹ := by
        rw [show -π * s = -(π * s) by ring, Real.exp_neg, inv_inv]
      have hreal : 2 * Real.exp (-π * s) * Real.cosh (π * s) = Real.exp (-π * s) ^ 2 + 1 := by
        rw [Real.cosh_eq, hα_inv]
        have he : Real.exp (-π * s) ≠ 0 := Real.exp_ne_zero _
        field_simp; ring
      have hC := congrArg (fun r : ℝ => (r : ℂ)) hreal
      push_cast at hC
      simpa [α] using hC
    calc (α * (c - sn * Complex.I) - 1) * (α * (c + sn * Complex.I) - 1)
        = α ^ 2 * (c ^ 2 + sn ^ 2 - sn ^ 2 * (1 + Complex.I ^ 2)) - 2 * α * c + 1 := by ring
      _ = α ^ 2 + 1 - 2 * α * c := by rw [Complex.I_sq, hpy]; ring
      _ = 2 * α * ((Real.cosh (π * s) : ℝ) : ℂ) - 2 * α * c := by rw [hcosh]
      _ = 2 * α * ((Real.cosh (π * s) - Real.cos (π * σ₀) : ℝ) : ℂ) := by
          dsimp [c]; push_cast; ring
  have hdiff : (α * (c - sn * Complex.I) - 1)⁻¹ - (α * (c + sn * Complex.I) - 1)⁻¹ =
      (2 * α * sn * Complex.I) /
        (2 * α * ((Real.cosh (π * s) - Real.cos (π * σ₀) : ℝ) : ℂ)) := by
    rw [inv_sub_inv hne1 hne2, hden_real]
    congr 1
    ring
  have hden_ne : (Real.cosh (π * s) : ℂ) - (Real.cos (π * σ₀) : ℂ) ≠ 0 := by
    exact_mod_cast (stripPoissonP_den_pos hσ₀ hσ₁ s).ne'
  unfold stripCauchyKernel
  rw [hu, hv, hdiff]
  unfold stripPoissonP
  dsimp [sn, σ₀, s]
  push_cast
  field_simp [hα_ne, hden_ne]
  rw [show Complex.I ^ 2 = -1 from Complex.I_sq]
  ring

private lemma stripCauchyKernel_right_edge {ζ₀ : ℂ} (hσ₀ : 0 < ζ₀.re) (hσ₁ : ζ₀.re < 1) (τ : ℝ) :
    stripCauchyKernel ζ₀ (1 + (τ : ℂ) * Complex.I) =
      ((2 * π * stripPoissonP1 ζ₀.re (τ - ζ₀.im) : ℝ) : ℂ) := by
  set σ₀ := ζ₀.re
  set s := τ - ζ₀.im
  have h1 : Complex.I * (π : ℂ) * (1 + (τ : ℂ) * Complex.I - ζ₀) =
      (π : ℂ) * Complex.I + (((-π * s : ℝ) : ℂ) + ((-π * σ₀ : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im]
      dsimp [σ₀, s]; ring
    · simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im]
      dsimp [σ₀, s]; ring
  have h2 : Complex.I * (π : ℂ) * (1 + (τ : ℂ) * Complex.I + starRingEnd ℂ ζ₀) =
      (π : ℂ) * Complex.I + (((-π * s : ℝ) : ℂ) + ((π * σ₀ : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im,
        Complex.one_re, Complex.one_im]
      dsimp [σ₀, s]; ring
    · simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im,
        Complex.one_re, Complex.one_im]
      dsimp [σ₀, s]; ring
  set α : ℂ := ((Real.exp (-π * s) : ℝ) : ℂ)
  set c : ℂ := ((Real.cos (π * σ₀) : ℝ) : ℂ)
  set sn : ℂ := ((Real.sin (π * σ₀) : ℝ) : ℂ)
  have hu : Complex.exp (Complex.I * (π : ℂ) * (1 + (τ : ℂ) * Complex.I - ζ₀)) =
      -(α * (c - sn * Complex.I)) := by
    rw [h1, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_add, ← Complex.ofReal_exp,
      Complex.exp_mul_I, show ((-π * σ₀ : ℝ) : ℂ) = -((π * σ₀ : ℝ) : ℂ) by push_cast; ring,
      Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    dsimp [α, c, sn]; ring
  have hv : Complex.exp (Complex.I * (π : ℂ) * (1 + (τ : ℂ) * Complex.I + starRingEnd ℂ ζ₀)) =
      -(α * (c + sn * Complex.I)) := by
    rw [h2, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_add, ← Complex.ofReal_exp,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    dsimp [α, c, sn]; ring
  have hne1 : -(α * (c - sn * Complex.I)) - 1 ≠ 0 := by
    rw [← hu]
    exact exp_I_pi_sub_ne_one hσ₀ hσ₁ (by simp) (by simp) (fun heq => by
      have := congrArg Complex.re heq
      simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im] at this
      linarith)
  have hne2 : -(α * (c + sn * Complex.I)) - 1 ≠ 0 := by
    rw [← hv]
    exact exp_I_pi_add_conj_ne_one hσ₀ hσ₁ (by simp) (by simp)
  have hα_ne : α ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hpy : c ^ 2 + sn ^ 2 = 1 := by
    dsimp [c, sn]; exact_mod_cast Real.cos_sq_add_sin_sq (π * σ₀)
  have hden_real : (-(α * (c - sn * Complex.I)) - 1) * (-(α * (c + sn * Complex.I)) - 1) =
      2 * α * (((Real.cosh (π * s) + Real.cos (π * σ₀) : ℝ) : ℂ)) := by
    have hcosh : (2 * α * ((Real.cosh (π * s) : ℝ) : ℂ)) = α ^ 2 + 1 := by
      have hα_inv : Real.exp (π * s) = (Real.exp (-π * s))⁻¹ := by
        rw [show -π * s = -(π * s) by ring, Real.exp_neg, inv_inv]
      have hreal : 2 * Real.exp (-π * s) * Real.cosh (π * s) = Real.exp (-π * s) ^ 2 + 1 := by
        rw [Real.cosh_eq, hα_inv]
        have he : Real.exp (-π * s) ≠ 0 := Real.exp_ne_zero _
        field_simp; ring
      have hC := congrArg (fun r : ℝ => (r : ℂ)) hreal
      push_cast at hC
      simpa [α] using hC
    calc (-(α * (c - sn * Complex.I)) - 1) * (-(α * (c + sn * Complex.I)) - 1)
        = α ^ 2 * (c ^ 2 + sn ^ 2 - sn ^ 2 * (1 + Complex.I ^ 2)) + 2 * α * c + 1 := by ring
      _ = α ^ 2 + 1 + 2 * α * c := by rw [Complex.I_sq, hpy]; ring
      _ = 2 * α * ((Real.cosh (π * s) : ℝ) : ℂ) + 2 * α * c := by rw [hcosh]
      _ = 2 * α * ((Real.cosh (π * s) + Real.cos (π * σ₀) : ℝ) : ℂ) := by
          dsimp [c]; push_cast; ring
  have hdiff : (-(α * (c - sn * Complex.I)) - 1)⁻¹ - (-(α * (c + sn * Complex.I)) - 1)⁻¹ =
      (-2 * α * sn * Complex.I) /
        (2 * α * ((Real.cosh (π * s) + Real.cos (π * σ₀) : ℝ) : ℂ)) := by
    rw [inv_sub_inv hne1 hne2, hden_real]
    congr 1
    ring
  have hden_ne : (Real.cosh (π * s) : ℂ) + (Real.cos (π * σ₀) : ℂ) ≠ 0 := by
    exact_mod_cast (stripPoissonP1_den_pos hσ₀ hσ₁ s).ne'
  unfold stripCauchyKernel
  rw [hu, hv, hdiff]
  unfold stripPoissonP1
  dsimp [sn, σ₀, s]
  push_cast
  field_simp [hα_ne, hden_ne]
  rw [show Complex.I ^ 2 = -1 from Complex.I_sq]
  ring

private lemma norm_stripCauchyKernel_top_le {ζ₀ : ℂ} {T x : ℝ} (hT : |ζ₀.im| + 1 ≤ T) :
    ‖stripCauchyKernel ζ₀ ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤
      8 * π * Real.exp (-π * (T - |ζ₀.im|)) := by
  set u := Complex.exp (Complex.I * (π : ℂ) * ((x : ℂ) + (T : ℂ) * Complex.I - ζ₀))
  set v := Complex.exp (Complex.I * (π : ℂ) * ((x : ℂ) + (T : ℂ) * Complex.I + starRingEnd ℂ ζ₀))
  have hre_u : (Complex.I * (π : ℂ) * ((x : ℂ) + (T : ℂ) * Complex.I - ζ₀)).re =
      -π * (T - ζ₀.im) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
    ring
  have hre_v : (Complex.I * (π : ℂ) * ((x : ℂ) + (T : ℂ) * Complex.I + starRingEnd ℂ ζ₀)).re =
      -π * (T - ζ₀.im) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
    ring
  have h_le : T - |ζ₀.im| ≤ T - ζ₀.im ∧ T - |ζ₀.im| ≤ T + ζ₀.im := by
    have := abs_le.mp (le_refl |ζ₀.im|)
    constructor <;> linarith
  have hpi1 : 1 ≤ π := by linarith [Real.pi_gt_three]
  have hexp_half : Real.exp (-π) ≤ 1 / 2 := by
    have h1 : Real.exp (-π) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg]
      have : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
    exact h1.trans h2
  have hu_norm : ‖u‖ ≤ Real.exp (-π * (T - |ζ₀.im|)) := by
    dsimp [u]; rw [Complex.norm_exp, hre_u]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hv_norm : ‖v‖ ≤ Real.exp (-π * (T - |ζ₀.im|)) := by
    dsimp [v]; rw [Complex.norm_exp, hre_v]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hu_half : ‖u‖ ≤ 1 / 2 := hu_norm.trans
    ((Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])).trans hexp_half)
  have hv_half : ‖v‖ ≤ 1 / 2 := hv_norm.trans
    ((Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])).trans hexp_half)
  have hu1 : 1 / 2 ≤ ‖u - 1‖ := by
    have h := norm_sub_norm_le 1 u
    rw [norm_one, norm_sub_rev] at h
    linarith
  have hv1 : 1 / 2 ≤ ‖v - 1‖ := by
    have h := norm_sub_norm_le 1 v
    rw [norm_one, norm_sub_rev] at h
    linarith
  have hu_ne : u - 1 ≠ 0 := norm_pos_iff.mp (by linarith)
  have hv_ne : v - 1 ≠ 0 := norm_pos_iff.mp (by linarith)
  have hdiff : (u - 1)⁻¹ - (v - 1)⁻¹ = (v - u) / ((u - 1) * (v - 1)) := by
    rw [inv_sub_inv hu_ne hv_ne]
    congr 1; ring
  unfold stripCauchyKernel
  change ‖(π : ℂ) * Complex.I * ((u - 1)⁻¹ - (v - 1)⁻¹)‖ ≤ _
  rw [hdiff, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_I, mul_one, norm_div, norm_mul]
  have hnum : ‖v - u‖ ≤ 2 * Real.exp (-π * (T - |ζ₀.im|)) := by
    calc ‖v - u‖ ≤ ‖v‖ + ‖u‖ := norm_sub_le v u
      _ ≤ 2 * Real.exp (-π * (T - |ζ₀.im|)) := by linarith
  have hden : 1 / 4 ≤ ‖u - 1‖ * ‖v - 1‖ := by nlinarith
  calc π * (‖v - u‖ / (‖u - 1‖ * ‖v - 1‖))
      ≤ π * (2 * Real.exp (-π * (T - |ζ₀.im|)) / (1 / 4)) := by
        gcongr
    _ = 8 * π * Real.exp (-π * (T - |ζ₀.im|)) := by ring

private lemma norm_stripCauchyKernel_bot_le {ζ₀ : ℂ} {T x : ℝ} (hT : |ζ₀.im| + 1 ≤ T) :
    ‖stripCauchyKernel ζ₀ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤
      4 * π * Real.exp (-π * (T - |ζ₀.im|)) := by
  set u := Complex.exp (Complex.I * (π : ℂ) * ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I - ζ₀))
  set v := Complex.exp (Complex.I * (π : ℂ) * ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I + starRingEnd ℂ ζ₀))
  have hre_u : (Complex.I * (π : ℂ) * ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I - ζ₀)).re =
      π * (T + ζ₀.im) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
    ring
  have hre_v : (Complex.I * (π : ℂ) * ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I + starRingEnd ℂ ζ₀)).re =
      π * (T + ζ₀.im) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
    ring
  have h_le : T - |ζ₀.im| ≤ T - ζ₀.im ∧ T - |ζ₀.im| ≤ T + ζ₀.im := by
    have := abs_le.mp (le_refl |ζ₀.im|)
    constructor <;> linarith
  have hexp_two : 2 ≤ Real.exp π := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 : Real.exp 1 ≤ Real.exp π := Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three])
    linarith
  have hu_norm : Real.exp (π * (T - |ζ₀.im|)) ≤ ‖u‖ := by
    dsimp [u]; rw [Complex.norm_exp, hre_u]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hv_norm : Real.exp (π * (T - |ζ₀.im|)) ≤ ‖v‖ := by
    dsimp [v]; rw [Complex.norm_exp, hre_v]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hu_two : 2 ≤ ‖u‖ := hexp_two.trans
    ((Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])).trans hu_norm)
  have hv_two : 2 ≤ ‖v‖ := hexp_two.trans
    ((Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])).trans hv_norm)
  have hu1 : ‖u‖ / 2 ≤ ‖u - 1‖ := by
    have h := norm_sub_norm_le u 1
    rw [norm_one] at h
    linarith
  have hv1 : ‖v‖ / 2 ≤ ‖v - 1‖ := by
    have h := norm_sub_norm_le v 1
    rw [norm_one] at h
    linarith
  have hu_inv : ‖(u - 1)⁻¹‖ ≤ 2 * Real.exp (-π * (T - |ζ₀.im|)) := by
    rw [norm_inv, show -π * (T - |ζ₀.im|) = -(π * (T - |ζ₀.im|)) by ring, Real.exp_neg]
    calc ‖u - 1‖⁻¹ ≤ (‖u‖ / 2)⁻¹ := inv_anti₀ (by linarith) hu1
      _ = 2 * ‖u‖⁻¹ := by ring
      _ ≤ 2 * (Real.exp (π * (T - |ζ₀.im|)))⁻¹ := by
          gcongr
  have hv_inv : ‖(v - 1)⁻¹‖ ≤ 2 * Real.exp (-π * (T - |ζ₀.im|)) := by
    rw [norm_inv, show -π * (T - |ζ₀.im|) = -(π * (T - |ζ₀.im|)) by ring, Real.exp_neg]
    calc ‖v - 1‖⁻¹ ≤ (‖v‖ / 2)⁻¹ := inv_anti₀ (by linarith) hv1
      _ = 2 * ‖v‖⁻¹ := by ring
      _ ≤ 2 * (Real.exp (π * (T - |ζ₀.im|)))⁻¹ := by
          gcongr
  unfold stripCauchyKernel
  change ‖(π : ℂ) * Complex.I * ((u - 1)⁻¹ - (v - 1)⁻¹)‖ ≤ _
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_I, mul_one]
  calc π * ‖(u - 1)⁻¹ - (v - 1)⁻¹‖
      ≤ π * (‖(u - 1)⁻¹‖ + ‖(v - 1)⁻¹‖) := by gcongr; exact norm_sub_le _ _
    _ ≤ π * (2 * Real.exp (-π * (T - |ζ₀.im|)) + 2 * Real.exp (-π * (T - |ζ₀.im|))) := by gcongr
    _ = 4 * π * Real.exp (-π * (T - |ζ₀.im|)) := by ring

/-- Auxiliary extension of `(ζ - ζ₀) * stripCauchyKernel ζ₀ ζ` across the simple pole at `ζ₀`. -/
private noncomputable def stripCauchyKernelAux (ζ₀ ζ : ℂ) : ℂ :=
  if ζ = ζ₀ then 1 else (ζ - ζ₀) * stripCauchyKernel ζ₀ ζ

private lemma continuousAt_stripCauchyKernelAux (ζ₀ : ℂ) (hσ₀ : 0 < ζ₀.re) (hσ₁ : ζ₀.re < 1) :
    ContinuousAt (stripCauchyKernelAux ζ₀) ζ₀ := by
  have h_tend_exp : Tendsto (fun w : ℂ => (Complex.exp w - 1) / w) (𝓝[≠] 0) (𝓝 1) := by
    have hd := (Complex.hasDerivAt_exp 0).tendsto_slope_zero
    simpa [slope, Complex.exp_zero, smul_eq_mul, div_eq_inv_mul] using hd
  have h_tend_inv : Tendsto (fun w : ℂ => w / (Complex.exp w - 1)) (𝓝[≠] 0) (𝓝 1) := by
    have h1 := h_tend_exp.inv₀ one_ne_zero
    rw [inv_one] at h1
    refine h1.congr' (Eventually.of_forall fun w => ?_)
    rw [inv_div]
  have h_lin : Tendsto (fun ζ : ℂ => Complex.I * (π : ℂ) * (ζ - ζ₀)) (𝓝[≠] ζ₀) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h0 : Complex.I * (π : ℂ) * (ζ₀ - ζ₀) = 0 := by simp
      rw [← h0]
      exact (((continuous_const.mul (continuous_id.sub continuous_const)).tendsto ζ₀).mono_left
        nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with ζ hζ
      exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))
        (sub_ne_zero.mpr hζ)
  have h_first : Tendsto (fun ζ : ℂ =>
      (ζ - ζ₀) * ((π : ℂ) * Complex.I * (Complex.exp (Complex.I * (π : ℂ) * (ζ - ζ₀)) - 1)⁻¹))
      (𝓝[≠] ζ₀) (𝓝 1) := by
    refine (h_tend_inv.comp h_lin).congr' (Eventually.of_forall fun ζ => ?_)
    dsimp [Function.comp_def]
    ring
  have h_second_den : Complex.exp (Complex.I * (π : ℂ) * (ζ₀ + starRingEnd ℂ ζ₀)) - 1 ≠ 0 :=
    exp_I_pi_add_conj_ne_one hσ₀ hσ₁ hσ₀.le hσ₁.le
  have h_second : Tendsto (fun ζ : ℂ =>
      (ζ - ζ₀) * ((π : ℂ) * Complex.I *
        (Complex.exp (Complex.I * (π : ℂ) * (ζ + starRingEnd ℂ ζ₀)) - 1)⁻¹))
      (𝓝[≠] ζ₀) (𝓝 0) := by
    have h0 : (ζ₀ - ζ₀) * ((π : ℂ) * Complex.I *
        (Complex.exp (Complex.I * (π : ℂ) * (ζ₀ + starRingEnd ℂ ζ₀)) - 1)⁻¹) = 0 := by simp
    rw [← h0]
    refine ContinuousAt.tendsto ?_ |>.mono_left nhdsWithin_le_nhds
    fun_prop (disch := exact h_second_den)
  have h_sub : Tendsto (stripCauchyKernelAux ζ₀) (𝓝[≠] ζ₀) (𝓝 (1 - 0)) := by
    refine (h_first.sub h_second).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ζ hζ
    have hζ' : ζ ≠ ζ₀ := hζ
    simp only [stripCauchyKernelAux, stripCauchyKernel, hζ', ↓reduceIte]
    ring
  rw [sub_zero] at h_sub
  exact continuousWithinAt_compl_self.mp (by simpa [ContinuousWithinAt, stripCauchyKernelAux] using h_sub)

private lemma continuousOn_stripCauchyKernelAux (ζ₀ : ℂ) (hσ₀ : 0 < ζ₀.re) (hσ₁ : ζ₀.re < 1) :
    ContinuousOn (stripCauchyKernelAux ζ₀) {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} := by
  intro ζ hζ
  by_cases heq : ζ = ζ₀
  · subst heq
    exact (continuousAt_stripCauchyKernelAux ζ hσ₀ hσ₁).continuousWithinAt
  · have h_ev : stripCauchyKernelAux ζ₀ =ᶠ[𝓝 ζ] fun w => (w - ζ₀) * stripCauchyKernel ζ₀ w := by
      filter_upwards [isOpen_ne.mem_nhds heq] with w hw
      simp [stripCauchyKernelAux, hw]
    refine ContinuousAt.continuousWithinAt ?_
    rw [continuousAt_congr h_ev]
    unfold stripCauchyKernel
    have hd1 := exp_I_pi_sub_ne_one hσ₀ hσ₁ hζ.1 hζ.2 heq
    have hd2 := exp_I_pi_add_conj_ne_one hσ₀ hσ₁ hζ.1 hζ.2
    fun_prop (disch := first | exact hd1 | exact hd2)

end StripCauchyKernel

section StripPoissonRep

/-- **Lemma TE.1(a), unfolded form**: for any `H : ℂ → ℂ` continuous and bounded on the closed
strip `0 ≤ Re ζ ≤ 1` and holomorphic on `0 < Re ζ < 1`, and any `ζ₀` with `0 < Re ζ₀ < 1`,
`H(ζ₀) = ∫_ℝ p(τ - η₀) H(iτ) dτ + ∫_ℝ p₁(τ - η₀) H(1 + iτ) dτ`. -/
theorem stripPoisson_representation_split {H : ℂ → ℂ} {M : ℝ}
    (hH_cont : ContinuousOn H {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1})
    (hH_holo : DifferentiableOn ℂ H {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1})
    (hH_bd : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖H ζ‖ ≤ M)
    {ζ₀ : ℂ} (hσ₀ : 0 < ζ₀.re) (hσ₁ : ζ₀.re < 1) :
    Integrable (fun τ : ℝ => (stripPoissonP ζ₀.re (τ - ζ₀.im) : ℂ) * H ((τ : ℂ) * Complex.I)) ∧
    Integrable (fun τ : ℝ => (stripPoissonP1 ζ₀.re (τ - ζ₀.im) : ℂ) * H (1 + (τ : ℂ) * Complex.I)) ∧
    H ζ₀ = (∫ τ : ℝ, (stripPoissonP ζ₀.re (τ - ζ₀.im) : ℂ) * H ((τ : ℂ) * Complex.I)) +
      ∫ τ : ℝ, (stripPoissonP1 ζ₀.re (τ - ζ₀.im) : ℂ) * H (1 + (τ : ℂ) * Complex.I) := by
  have hM_nn : 0 ≤ M := (norm_nonneg (H 0)).trans (hH_bd 0 le_rfl zero_le_one)
  have hP_int : Integrable (fun τ : ℝ => stripPoissonP ζ₀.re (τ - ζ₀.im)) :=
    (stripPoissonP_integrable hσ₀ hσ₁).comp_sub_right ζ₀.im
  have hP1_int : Integrable (fun τ : ℝ => stripPoissonP1 ζ₀.re (τ - ζ₀.im)) :=
    (stripPoissonP1_integrable hσ₀ hσ₁).comp_sub_right ζ₀.im
  have hH_left_cont : Continuous (fun τ : ℝ => H ((τ : ℂ) * Complex.I)) := by
    refine hH_cont.comp_continuous (by fun_prop) fun τ => ?_
    simp [Complex.mul_re]
  have hH_right_cont : Continuous (fun τ : ℝ => H (1 + (τ : ℂ) * Complex.I)) := by
    refine hH_cont.comp_continuous (by fun_prop) fun τ => ?_
    simp [Complex.add_re, Complex.mul_re]
  have hP_cont : Continuous (fun τ : ℝ => stripPoissonP ζ₀.re (τ - ζ₀.im)) := by
    unfold stripPoissonP
    exact Continuous.div continuous_const
      ((Real.continuous_cosh.comp (continuous_const.mul (continuous_id.sub continuous_const))).sub
        continuous_const)
      fun τ => (stripPoissonP_den_pos hσ₀ hσ₁ _).ne'
  have hP1_cont : Continuous (fun τ : ℝ => stripPoissonP1 ζ₀.re (τ - ζ₀.im)) := by
    unfold stripPoissonP1
    exact Continuous.div continuous_const
      ((Real.continuous_cosh.comp (continuous_const.mul (continuous_id.sub continuous_const))).add
        continuous_const)
      fun τ => (stripPoissonP1_den_pos hσ₀ hσ₁ _).ne'
  have hint_left : Integrable (fun τ : ℝ =>
      (stripPoissonP ζ₀.re (τ - ζ₀.im) : ℂ) * H ((τ : ℂ) * Complex.I)) := by
    refine (hP_int.const_mul M).mono' ?_ (Eventually.of_forall fun τ => ?_)
    · exact ((Complex.continuous_ofReal.comp hP_cont).mul hH_left_cont).aestronglyMeasurable
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (stripPoissonP_pos hσ₀ hσ₁ _).le]
      rw [mul_comm M]
      exact mul_le_mul_of_nonneg_left (hH_bd _ (by simp [Complex.mul_re]) (by simp [Complex.mul_re]))
        (stripPoissonP_pos hσ₀ hσ₁ _).le
  have hint_right : Integrable (fun τ : ℝ =>
      (stripPoissonP1 ζ₀.re (τ - ζ₀.im) : ℂ) * H (1 + (τ : ℂ) * Complex.I)) := by
    refine (hP1_int.const_mul M).mono' ?_ (Eventually.of_forall fun τ => ?_)
    · exact ((Complex.continuous_ofReal.comp hP1_cont).mul hH_right_cont).aestronglyMeasurable
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (stripPoissonP1_pos hσ₀ hσ₁ _).le]
      rw [mul_comm M]
      exact mul_le_mul_of_nonneg_left
        (hH_bd _ (by simp [Complex.add_re, Complex.mul_re]) (by simp [Complex.add_re, Complex.mul_re]))
        (stripPoissonP1_pos hσ₀ hσ₁ _).le
  refine ⟨hint_left, hint_right, ?_⟩
  let g : ℂ → ℂ := fun ζ => dslope H ζ₀ ζ * stripCauchyKernelAux ζ₀ ζ
  have h_open_strip : IsOpen {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have h_strip_nhds : {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} ∈ 𝓝 ζ₀ :=
    Filter.mem_of_superset (h_open_strip.mem_nhds ⟨hσ₀, hσ₁⟩) fun ζ hζ => ⟨hζ.1.le, hζ.2.le⟩
  have hH_diff_ζ₀ : DifferentiableAt ℂ H ζ₀ :=
    hH_holo.differentiableAt (h_open_strip.mem_nhds ⟨hσ₀, hσ₁⟩)
  have hg_cont : ContinuousOn g {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} :=
    ((continuousOn_dslope h_strip_nhds).mpr ⟨hH_cont, hH_diff_ζ₀⟩).mul
      (continuousOn_stripCauchyKernelAux ζ₀ hσ₀ hσ₁)
  have hg_eq_ne : ∀ {ζ : ℂ}, ζ ≠ ζ₀ → g ζ = (H ζ - H ζ₀) * stripCauchyKernel ζ₀ ζ := by
    intro ζ hne
    dsimp [g, dslope, stripCauchyKernelAux]
    rw [Function.update_of_ne hne, slope_def_module, smul_eq_mul]
    simp only [hne, ↓reduceIte]
    have hsub : ζ - ζ₀ ≠ 0 := sub_ne_zero.mpr hne
    field_simp [hsub]
  -- Rectangle Cauchy theorem for `T ≥ |ζ₀.im| + 1`
  have hrect : ∀ T : ℝ, |ζ₀.im| + 1 ≤ T →
      (((∫ x in (0 : ℝ)..1, g ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
          ∫ x in (0 : ℝ)..1, g ((x : ℂ) + (T : ℂ) * Complex.I)) +
        Complex.I • ∫ y in (-T)..T, g (1 + (y : ℂ) * Complex.I)) -
        Complex.I • ∫ y in (-T)..T, g ((y : ℂ) * Complex.I) = 0 := by
    intro T hT
    have hT_pos : 0 < T := by linarith [abs_nonneg ζ₀.im]
    set z : ℂ := ((-T : ℝ) : ℂ) * Complex.I
    set w : ℂ := (1 : ℂ) + (T : ℂ) * Complex.I
    have hz_re : z.re = 0 := by simp [z]
    have hw_re : w.re = 1 := by simp [w]
    have hz_im : z.im = -T := by simp [z]
    have hw_im : w.im = T := by simp [w]
    have Hc : ContinuousOn g (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
      refine hg_cont.mono fun ζ hζ => ?_
      rw [hz_re, hw_re, Set.uIcc_of_le zero_le_one] at hζ
      exact hζ.1
    have Hd : ∀ ζ ∈ Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
        Set.Ioo (min z.im w.im) (max z.im w.im) \ ({ζ₀} : Set ℂ), DifferentiableAt ℂ g ζ := by
      intro ζ hζ
      have hne : ζ ≠ ζ₀ := by simpa using hζ.2
      have hζ_mem : ζ ∈ {u : ℂ | 0 < u.re ∧ u.re < 1} := by
        have := hζ.1.1
        rw [hz_re, hw_re, min_eq_left zero_le_one, max_eq_right zero_le_one] at this
        exact this
      have h_ev : g =ᶠ[𝓝 ζ] fun u => (H u - H ζ₀) * stripCauchyKernel ζ₀ u := by
        filter_upwards [isOpen_ne.mem_nhds hne] with u hu
        exact hg_eq_ne hu
      have hd_H : DifferentiableAt ℂ H ζ := hH_holo.differentiableAt (h_open_strip.mem_nhds hζ_mem)
      have hd_K : DifferentiableAt ℂ (stripCauchyKernel ζ₀) ζ := by
        unfold stripCauchyKernel
        have hd1 := exp_I_pi_sub_ne_one hσ₀ hσ₁ hζ_mem.1.le hζ_mem.2.le hne
        have hd2 := exp_I_pi_add_conj_ne_one hσ₀ hσ₁ hζ_mem.1.le hζ_mem.2.le
        fun_prop (disch := first | exact hd1 | exact hd2)
      exact ((hd_H.sub_const _).mul hd_K).congr_of_eventuallyEq h_ev
    have h0 := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable g z w
      {ζ₀} (Set.countable_singleton ζ₀) Hc Hd
    simpa [z, w, hz_re, hw_re, hz_im, hw_im] using h0
  -- Horizontal segments tend to `0` as `T → ∞`
  have hhor_top : Tendsto (fun T : ℝ =>
      ∫ x in (0 : ℝ)..1, g ((x : ℂ) + (T : ℂ) * Complex.I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h_ev : ∀ᶠ T : ℝ in atTop,
        ‖∫ x in (0 : ℝ)..1, g ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤
          16 * π * M * Real.exp (-π * (T - |ζ₀.im|)) := by
      filter_upwards [eventually_ge_atTop (|ζ₀.im| + 1)] with T hT
      have hT_gt : |ζ₀.im| < T := by linarith
      have hint_x : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (T : ℂ) * Complex.I)) volume 0 1 := by
        refine ContinuousOn.intervalIntegrable ?_
        refine hg_cont.comp (Complex.continuous_ofReal.continuousOn.add continuousOn_const)
          fun x hx => ?_
        rw [Set.uIcc_of_le zero_le_one] at hx
        simpa [Complex.add_re, Complex.mul_re] using hx
      have h_norm_le : ∀ x ∈ Icc (0 : ℝ) 1,
          ‖g ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤ 16 * π * M * Real.exp (-π * (T - |ζ₀.im|)) := by
        intro x hx
        have hne : (x : ℂ) + (T : ℂ) * Complex.I ≠ ζ₀ := fun heq => by
          have := congrArg Complex.im heq
          simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im, Complex.I_im,
            mul_one, Complex.I_re, mul_zero, add_zero, Complex.ofReal_re] at this
          linarith [le_abs_self ζ₀.im]
        rw [hg_eq_ne hne, norm_mul]
        have hH_diff_bd : ‖H ((x : ℂ) + (T : ℂ) * Complex.I) - H ζ₀‖ ≤ 2 * M := by
          have h1 := hH_bd ((x : ℂ) + (T : ℂ) * Complex.I)
            (by simpa [Complex.add_re, Complex.mul_re] using hx.1)
            (by simpa [Complex.add_re, Complex.mul_re] using hx.2)
          have h2 := hH_bd ζ₀ hσ₀.le hσ₁.le
          calc ‖H ((x : ℂ) + (T : ℂ) * Complex.I) - H ζ₀‖
              ≤ ‖H ((x : ℂ) + (T : ℂ) * Complex.I)‖ + ‖H ζ₀‖ := norm_sub_le _ _
            _ ≤ M + M := add_le_add h1 h2
            _ = 2 * M := by ring
        calc ‖H ((x : ℂ) + (T : ℂ) * Complex.I) - H ζ₀‖ *
              ‖stripCauchyKernel ζ₀ ((x : ℂ) + (T : ℂ) * Complex.I)‖
            ≤ (2 * M) * (8 * π * Real.exp (-π * (T - |ζ₀.im|))) :=
              mul_le_mul hH_diff_bd (norm_stripCauchyKernel_top_le hT) (norm_nonneg _) (by positivity)
          _ = 16 * π * M * Real.exp (-π * (T - |ζ₀.im|)) := by ring
      calc ‖∫ x in (0 : ℝ)..1, g ((x : ℂ) + (T : ℂ) * Complex.I)‖
          ≤ ∫ x in (0 : ℝ)..1, ‖g ((x : ℂ) + (T : ℂ) * Complex.I)‖ :=
            intervalIntegral.norm_integral_le_integral_norm zero_le_one
        _ ≤ ∫ _ in (0 : ℝ)..1, 16 * π * M * Real.exp (-π * (T - |ζ₀.im|)) := by
            refine intervalIntegral.integral_mono_on zero_le_one hint_x.norm
              intervalIntegrable_const h_norm_le
        _ = 16 * π * M * Real.exp (-π * (T - |ζ₀.im|)) := by simp
    have h_exp : Tendsto (fun T : ℝ => 16 * π * M * Real.exp (-π * (T - |ζ₀.im|))) atTop (𝓝 0) := by
      have hsub : Tendsto (fun T : ℝ => T - |ζ₀.im|) atTop atTop :=
        tendsto_atTop_add_const_right atTop (-|ζ₀.im|) tendsto_id
      have harg : Tendsto (fun T : ℝ => -π * (T - |ζ₀.im|)) atTop atBot :=
        hsub.const_mul_atTop_of_neg (neg_lt_zero.mpr Real.pi_pos)
      simpa using ((Real.tendsto_exp_atBot.comp harg).const_mul (16 * π * M))
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) h_ev h_exp
  have hhor_bot : Tendsto (fun T : ℝ =>
      ∫ x in (0 : ℝ)..1, g ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h_ev : ∀ᶠ T : ℝ in atTop,
        ‖∫ x in (0 : ℝ)..1, g ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤
          8 * π * M * Real.exp (-π * (T - |ζ₀.im|)) := by
      filter_upwards [eventually_ge_atTop (|ζ₀.im| + 1)] with T hT
      have hT_gt : |ζ₀.im| < T := by linarith
      have hint_x : IntervalIntegrable
          (fun x : ℝ => g ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) volume 0 1 := by
        refine ContinuousOn.intervalIntegrable ?_
        refine hg_cont.comp (Complex.continuous_ofReal.continuousOn.add continuousOn_const)
          fun x hx => ?_
        rw [Set.uIcc_of_le zero_le_one] at hx
        simpa [Complex.add_re, Complex.mul_re] using hx
      have h_norm_le : ∀ x ∈ Icc (0 : ℝ) 1,
          ‖g ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ 8 * π * M * Real.exp (-π * (T - |ζ₀.im|)) := by
        intro x hx
        have hne : (x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I ≠ ζ₀ := fun heq => by
          have := congrArg Complex.im heq
          simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im, Complex.I_im,
            mul_one, Complex.I_re, mul_zero, add_zero, Complex.ofReal_re] at this
          have hle := neg_abs_le ζ₀.im
          linarith
        rw [hg_eq_ne hne, norm_mul]
        have hH_diff_bd : ‖H ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - H ζ₀‖ ≤ 2 * M := by
          have h1 := hH_bd ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
            (by simpa [Complex.add_re, Complex.mul_re] using hx.1)
            (by simpa [Complex.add_re, Complex.mul_re] using hx.2)
          have h2 := hH_bd ζ₀ hσ₀.le hσ₁.le
          calc ‖H ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - H ζ₀‖
              ≤ ‖H ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ + ‖H ζ₀‖ := norm_sub_le _ _
            _ ≤ M + M := add_le_add h1 h2
            _ = 2 * M := by ring
        calc ‖H ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - H ζ₀‖ *
              ‖stripCauchyKernel ζ₀ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖
            ≤ (2 * M) * (4 * π * Real.exp (-π * (T - |ζ₀.im|))) :=
              mul_le_mul hH_diff_bd (norm_stripCauchyKernel_bot_le hT) (norm_nonneg _) (by positivity)
          _ = 8 * π * M * Real.exp (-π * (T - |ζ₀.im|)) := by ring
      calc ‖∫ x in (0 : ℝ)..1, g ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖
          ≤ ∫ x in (0 : ℝ)..1, ‖g ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ :=
            intervalIntegral.norm_integral_le_integral_norm zero_le_one
        _ ≤ ∫ _ in (0 : ℝ)..1, 8 * π * M * Real.exp (-π * (T - |ζ₀.im|)) := by
            refine intervalIntegral.integral_mono_on zero_le_one hint_x.norm
              intervalIntegrable_const h_norm_le
        _ = 8 * π * M * Real.exp (-π * (T - |ζ₀.im|)) := by simp
    have h_exp : Tendsto (fun T : ℝ => 8 * π * M * Real.exp (-π * (T - |ζ₀.im|))) atTop (𝓝 0) := by
      have hsub : Tendsto (fun T : ℝ => T - |ζ₀.im|) atTop atTop :=
        tendsto_atTop_add_const_right atTop (-|ζ₀.im|) tendsto_id
      have harg : Tendsto (fun T : ℝ => -π * (T - |ζ₀.im|)) atTop atBot :=
        hsub.const_mul_atTop_of_neg (neg_lt_zero.mpr Real.pi_pos)
      simpa using ((Real.tendsto_exp_atBot.comp harg).const_mul (8 * π * M))
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) h_ev h_exp
  -- Vertical segments expressed via `p` and `p₁`
  let F_right : ℝ → ℂ := fun y =>
    (stripPoissonP1 ζ₀.re (y - ζ₀.im) : ℂ) * (H (1 + (y : ℂ) * Complex.I) - H ζ₀)
  let F_left : ℝ → ℂ := fun y =>
    (stripPoissonP ζ₀.re (y - ζ₀.im) : ℂ) * (H ((y : ℂ) * Complex.I) - H ζ₀)
  have hF_right_int : Integrable F_right :=
    hint_right.sub ((hP1_int.ofReal).mul_const (H ζ₀)) |>.congr (Eventually.of_forall fun y => by
      dsimp [F_right]; ring)
  have hF_left_int : Integrable F_left :=
    hint_left.sub ((hP_int.ofReal).mul_const (H ζ₀)) |>.congr (Eventually.of_forall fun y => by
      dsimp [F_left]; ring)
  have hvert_right : ∀ T : ℝ,
      Complex.I • ∫ y in (-T)..T, g (1 + (y : ℂ) * Complex.I) =
        ((2 * π : ℂ) * Complex.I) * ∫ y in (-T)..T, F_right y := by
    intro T
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    have hne : (1 : ℂ) + (y : ℂ) * Complex.I ≠ ζ₀ := fun heq => by
      have := congrArg Complex.re heq
      simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im] at this
      linarith
    rw [hg_eq_ne hne, stripCauchyKernel_right_edge hσ₀ hσ₁ y]
    dsimp [F_right]
    push_cast
    ring
  have hvert_left : ∀ T : ℝ,
      -(Complex.I • ∫ y in (-T)..T, g ((y : ℂ) * Complex.I)) =
        ((2 * π : ℂ) * Complex.I) * ∫ y in (-T)..T, F_left y := by
    intro T
    rw [smul_eq_mul, ← neg_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    have hne : (y : ℂ) * Complex.I ≠ ζ₀ := fun heq => by
      have := congrArg Complex.re heq
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im] at this
      linarith
    rw [hg_eq_ne hne, stripCauchyKernel_left_edge hσ₀ hσ₁ y]
    dsimp [F_left]
    push_cast
    ring
  have h_sum_zero : Tendsto (fun T : ℝ =>
      ((2 * π : ℂ) * Complex.I) * ((∫ y in (-T)..T, F_right y) + ∫ y in (-T)..T, F_left y))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ =>
        (∫ x in (0 : ℝ)..1, g ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
          ∫ x in (0 : ℝ)..1, g ((x : ℂ) + (T : ℂ) * Complex.I)) atTop (𝓝 (0 - 0)) :=
      hhor_bot.sub hhor_top
    rw [sub_zero] at h1
    have h_eq : ∀ᶠ T in atTop,
        ((2 * π : ℂ) * Complex.I) * ((∫ y in (-T)..T, F_right y) + ∫ y in (-T)..T, F_left y) =
        -((∫ x in (0 : ℝ)..1, g ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
            ∫ x in (0 : ℝ)..1, g ((x : ℂ) + (T : ℂ) * Complex.I)) := by
      filter_upwards [eventually_ge_atTop (|ζ₀.im| + 1)] with T hT
      have hr := hrect T hT
      rw [mul_add, ← hvert_right T, ← hvert_left T]
      linear_combination hr
    rw [tendsto_congr' h_eq]
    simpa using h1.neg
  have h_sum_lim : Tendsto (fun T : ℝ =>
      ((2 * π : ℂ) * Complex.I) * ((∫ y in (-T)..T, F_right y) + ∫ y in (-T)..T, F_left y))
      atTop (𝓝 (((2 * π : ℂ) * Complex.I) * ((∫ y : ℝ, F_right y) + ∫ y : ℝ, F_left y))) := by
    have hR := intervalIntegral_tendsto_integral hF_right_int tendsto_neg_atTop_atBot tendsto_id
    have hL := intervalIntegral_tendsto_integral hF_left_int tendsto_neg_atTop_atBot tendsto_id
    exact (hR.add hL).const_mul ((2 * π : ℂ) * Complex.I)
  have h_zero_eq : ((2 * π : ℂ) * Complex.I) * ((∫ y : ℝ, F_right y) + ∫ y : ℝ, F_left y) = 0 :=
    tendsto_nhds_unique h_sum_lim h_sum_zero
  have h2piI : (2 * π : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) Complex.I_ne_zero
  have h_int_zero : (∫ y : ℝ, F_right y) + ∫ y : ℝ, F_left y = 0 :=
    (mul_eq_zero.mp h_zero_eq).resolve_left h2piI
  have h_F_right_eq : ∫ y : ℝ, F_right y =
      (∫ y : ℝ, (stripPoissonP1 ζ₀.re (y - ζ₀.im) : ℂ) * H (1 + (y : ℂ) * Complex.I)) -
        (ζ₀.re : ℂ) * H ζ₀ := by
    have hR_c : Integrable (fun y : ℝ => (stripPoissonP1 ζ₀.re (y - ζ₀.im) : ℂ) * H ζ₀) :=
      (hP1_int.ofReal).mul_const (H ζ₀)
    have hsplit : ∫ y : ℝ, F_right y =
        (∫ y : ℝ, (stripPoissonP1 ζ₀.re (y - ζ₀.im) : ℂ) * H (1 + (y : ℂ) * Complex.I)) -
          ∫ y : ℝ, (stripPoissonP1 ζ₀.re (y - ζ₀.im) : ℂ) * H ζ₀ := by
      rw [← integral_sub hint_right hR_c]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      dsimp [F_right]; ring
    rw [hsplit, integral_mul_const, integral_complex_ofReal, integral_sub_right_eq_self,
      stripPoissonP1_integral hσ₀ hσ₁]
  have h_F_left_eq : ∫ y : ℝ, F_left y =
      (∫ y : ℝ, (stripPoissonP ζ₀.re (y - ζ₀.im) : ℂ) * H ((y : ℂ) * Complex.I)) -
        ((1 - ζ₀.re : ℝ) : ℂ) * H ζ₀ := by
    have hL_c : Integrable (fun y : ℝ => (stripPoissonP ζ₀.re (y - ζ₀.im) : ℂ) * H ζ₀) :=
      (hP_int.ofReal).mul_const (H ζ₀)
    have hsplit : ∫ y : ℝ, F_left y =
        (∫ y : ℝ, (stripPoissonP ζ₀.re (y - ζ₀.im) : ℂ) * H ((y : ℂ) * Complex.I)) -
          ∫ y : ℝ, (stripPoissonP ζ₀.re (y - ζ₀.im) : ℂ) * H ζ₀ := by
      rw [← integral_sub hint_left hL_c]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      dsimp [F_left]; ring
    rw [hsplit, integral_mul_const, integral_complex_ofReal, integral_sub_right_eq_self,
      stripPoissonP_integral hσ₀ hσ₁]
  rw [h_F_right_eq, h_F_left_eq] at h_int_zero
  push_cast at h_int_zero
  linear_combination -h_int_zero

/-- **Lemma TE.1(a), unfolded single-integral form**. -/
theorem stripPoisson_representation {H : ℂ → ℂ} {M : ℝ}
    (hH_cont : ContinuousOn H {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1})
    (hH_holo : DifferentiableOn ℂ H {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1})
    (hH_bd : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖H ζ‖ ≤ M)
    {ζ₀ : ℂ} (hσ₀ : 0 < ζ₀.re) (hσ₁ : ζ₀.re < 1) :
    H ζ₀ = ∫ τ : ℝ,
      (stripPoissonP ζ₀.re (τ - ζ₀.im) : ℂ) * H ((τ : ℂ) * Complex.I) +
      (stripPoissonP1 ζ₀.re (τ - ζ₀.im) : ℂ) * H (1 + (τ : ℂ) * Complex.I) := by
  obtain ⟨hL, hR, heq⟩ := stripPoisson_representation_split hH_cont hH_holo hH_bd hσ₀ hσ₁
  rw [heq, ← integral_add hL hR]

/-- **Lemma TE.1(a), symmetric strip Poisson representation (`teb:kernel`, `TE.2`)**:
for any `H : ℂ → ℂ` continuous and bounded on `0 ≤ Re ζ ≤ 1`, holomorphic on `0 < Re ζ < 1`,
satisfying `H(1 - ζ) = ε H(ζ)` (`ε : ℝ`, e.g. `ε = ±1`), and any `ζ₀` with `0 < Re ζ₀ < 1`,
`H(ζ₀) = ∫_ℝ Q(τ) H(iτ) dτ` with `Q(τ) = p(τ - η₀) + ε p₁(τ + η₀)`. -/
theorem stripPoisson_representation_symm {H : ℂ → ℂ} {M ε : ℝ}
    (hH_cont : ContinuousOn H {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1})
    (hH_holo : DifferentiableOn ℂ H {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1})
    (hH_bd : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖H ζ‖ ≤ M)
    (hH_symm : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → H (1 - ζ) = (ε : ℂ) * H ζ)
    {ζ₀ : ℂ} (hσ₀ : 0 < ζ₀.re) (hσ₁ : ζ₀.re < 1) :
    Integrable (fun τ : ℝ => (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) * H ((τ : ℂ) * Complex.I)) ∧
    H ζ₀ = ∫ τ : ℝ, (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) * H ((τ : ℂ) * Complex.I) := by
  obtain ⟨hL, hR, heq⟩ := stripPoisson_representation_split hH_cont hH_holo hH_bd hσ₀ hσ₁
  have h_right_eq : (fun τ : ℝ =>
      (stripPoissonP1 ζ₀.re (τ - ζ₀.im) : ℂ) * H (1 + (τ : ℂ) * Complex.I)) =
      fun τ : ℝ => (ε : ℂ) * ((stripPoissonP1 ζ₀.re (τ - ζ₀.im) : ℂ) * H ((-τ : ℝ) * Complex.I)) := by
    ext τ
    have hsym := hH_symm ((-τ : ℝ) * Complex.I) (by simp [Complex.mul_re]) (by simp [Complex.mul_re])
    have h1 : (1 : ℂ) - ((-τ : ℝ) : ℂ) * Complex.I = 1 + (τ : ℂ) * Complex.I := by
      push_cast; ring
    rw [h1] at hsym
    rw [hsym]
    ring
  have hR_neg : Integrable (fun τ : ℝ =>
      (ε : ℂ) * ((stripPoissonP1 ζ₀.re (-τ - ζ₀.im) : ℂ) * H ((τ : ℂ) * Complex.I))) := by
    have hR' : Integrable (fun τ : ℝ =>
        (ε : ℂ) * ((stripPoissonP1 ζ₀.re (τ - ζ₀.im) : ℂ) * H ((-τ : ℝ) * Complex.I))) :=
      h_right_eq ▸ hR
    simpa using hR'.comp_neg
  have hQ_eq : (fun τ : ℝ => (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) * H ((τ : ℂ) * Complex.I)) =
      fun τ : ℝ => (stripPoissonP ζ₀.re (τ - ζ₀.im) : ℂ) * H ((τ : ℂ) * Complex.I) +
        (ε : ℂ) * ((stripPoissonP1 ζ₀.re (-τ - ζ₀.im) : ℂ) * H ((τ : ℂ) * Complex.I)) := by
    ext τ
    unfold stripPoissonQ
    have heven : stripPoissonP1 ζ₀.re (-τ - ζ₀.im) = stripPoissonP1 ζ₀.re (τ + ζ₀.im) := by
      rw [← stripPoissonP1_even]
      congr 1; ring
    rw [heven]
    push_cast
    ring
  have hQ_int : Integrable (fun τ : ℝ =>
      (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) * H ((τ : ℂ) * Complex.I)) := by
    rw [hQ_eq]; exact hL.add hR_neg
  refine ⟨hQ_int, ?_⟩
  have h_neg_int :
      ∫ τ : ℝ, (stripPoissonP1 ζ₀.re (τ - ζ₀.im) : ℂ) * H (1 + (τ : ℂ) * Complex.I) =
      ∫ τ : ℝ, (ε : ℂ) * ((stripPoissonP1 ζ₀.re (-τ - ζ₀.im) : ℂ) * H ((τ : ℂ) * Complex.I)) := by
    rw [h_right_eq, ← integral_neg_eq_self]
    simp
  rw [heq, h_neg_int, ← integral_add hL hR_neg, ← hQ_eq]

end StripPoissonRep

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.StripBand.stripPoisson_representation_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.StripBand.stripPoisson_representation_split

/-- info: 'FormalResearch.ModularBootstrap.StripBand.stripPoisson_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.StripBand.stripPoisson_representation

/-- info: 'FormalResearch.ModularBootstrap.StripBand.stripPoisson_representation_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.StripBand.stripPoisson_representation_symm

end FormalResearch.ModularBootstrap.StripBand

