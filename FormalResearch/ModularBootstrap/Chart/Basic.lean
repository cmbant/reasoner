module

public import FormalResearch.ModularBootstrap.Constants
public import FormalResearch.ModularBootstrap.ComplexBessel.LemmaS2
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Mellin Chart Basic Definitions (`lower_o1_two_edge.tex`, §J2, Lemma S3)

Defines complex principal-branch `arsinhC`, `arccosC`, the strip chart functions `chartB` (`b(ζ)`),
`chartQ` (`q(ζ)`), `chartOmega` (`ω(ζ)`), `muStar` (`μ* = π ξ* / 3`), and the left-edge real
functions `edgeX0`, `edgeY0`, `edgeMu`, `edgeNu` (`x₀`, `y₀`, `μ`, `ν`).

Proves:
* Principal-branch identities, conjugation symmetries, and complex derivatives of `arsinhC`, `arccosC`.
* Positivity of `b(ζ)` and `q(ζ)` on `(0, 1/2)` and `Re b(ζ) > 0`, `0 < Re q(ζ) < 1` on
  `{0 ≤ Re ζ ≤ 1/2, ζ ≠ 1/2}`.
* Exact left-edge formulas `b(iτ) = x₀(τ)`, `q(iτ) = 1/2 - i y₀(τ)`, `ω(iτ) = μ(τ) - i ν(τ)`.
* Analyticity and conjugation symmetry of `b`, `q`, `ω` away from the midpoint `ζ = 1/2`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Chart

/-! ### Section 1: Principal-branch `cpow (1/2)` helpers and complex `arsinhC`, `arccosC` -/

lemma cpow_half_sq (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
  rw [← Complex.cpow_nat_mul]
  norm_num

lemma conj_mem_slitPlane_iff {z : ℂ} : starRingEnd ℂ z ∈ Complex.slitPlane ↔ z ∈ Complex.slitPlane := by
  simp only [Complex.mem_slitPlane_iff, Complex.conj_re, Complex.conj_im, neg_ne_zero]

lemma cpow_half_re_pos {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    0 < (z ^ (1 / 2 : ℂ)).re := by
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hz
  have harg : |z.arg| < Real.pi := by
    have hpi := (Complex.mem_slitPlane_iff_arg.mp hz).1
    exact abs_lt.mpr ⟨Complex.neg_pi_lt_arg z, lt_of_le_of_ne (Complex.arg_le_pi z) hpi⟩
  rw [Complex.cpow_def_of_ne_zero hz0]
  have hmul : Complex.log z * (1 / 2 : ℂ) =
      ((Real.log ‖z‖ / 2 : ℝ) : ℂ) + ((z.arg / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.log_re]; ring
    · simp [Complex.log_im]; ring
  rw [hmul, Complex.exp_add_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    sub_zero, add_zero]
  have hexp_pos : 0 < Real.exp (Real.log ‖z‖ / 2) := Real.exp_pos _
  have hcos_pos : 0 < Real.cos (z.arg / 2) := by
    have hlt := abs_lt.mp harg
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  nlinarith [mul_pos hexp_pos hcos_pos]

lemma cpow_half_conj {z : ℂ} (hz : z.arg ≠ Real.pi) :
    (starRingEnd ℂ z) ^ (1 / 2 : ℂ) = starRingEnd ℂ (z ^ (1 / 2 : ℂ)) := by
  have h := Complex.cpow_conj z (1 / 2 : ℂ) hz
  have hhalf : starRingEnd ℂ (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
    rw [map_div₀, map_one, map_ofNat]
  rw [hhalf] at h
  have h2 := congrArg (starRingEnd ℂ) h
  simpa using h2.symm

lemma cpow_half_ofReal_nonneg {x : ℝ} (hx : 0 ≤ x) :
    ((x : ℂ) ^ (1 / 2 : ℂ)) = (√x : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hx, Real.sqrt_eq_rpow]

/-- Principal-branch complex inverse hyperbolic sine `arsinh w = log(w + √(w^2 + 1))`. -/
noncomputable def arsinhC (w : ℂ) : ℂ :=
  Complex.log (w + (w ^ 2 + 1) ^ (1 / 2 : ℂ))

/-- Principal-branch complex inverse cosine `arccos Z = -i log(Z + i √(1 - Z^2))`. -/
noncomputable def arccosC (Z : ℂ) : ℂ :=
  -Complex.I * Complex.log (Z + Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ))

lemma arsinhC_inner_ne_zero (w : ℂ) : w + (w ^ 2 + 1) ^ (1 / 2 : ℂ) ≠ 0 := by
  set s : ℂ := (w ^ 2 + 1) ^ (1 / 2 : ℂ)
  have hs2 : s ^ 2 = w ^ 2 + 1 := cpow_half_sq (w ^ 2 + 1)
  intro h
  have hprod : (s + w) * (s - w) = 1 := by linear_combination hs2
  rw [add_comm s w, h, zero_mul] at hprod
  exact zero_ne_one hprod

lemma arccosC_inner_ne_zero (Z : ℂ) : Z + Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
  set s : ℂ := (1 - Z ^ 2) ^ (1 / 2 : ℂ)
  have hs2 : s ^ 2 = 1 - Z ^ 2 := cpow_half_sq (1 - Z ^ 2)
  intro h
  have hprod : (Z + Complex.I * s) * (Z - Complex.I * s) = 1 := by
    calc (Z + Complex.I * s) * (Z - Complex.I * s)
        = Z ^ 2 - Complex.I ^ 2 * s ^ 2 := by ring
      _ = Z ^ 2 + s ^ 2 := by rw [Complex.I_sq]; ring
      _ = 1 := by linear_combination hs2
  rw [h, zero_mul] at hprod
  exact zero_ne_one hprod

lemma sinh_arsinhC (w : ℂ) : Complex.sinh (arsinhC w) = w := by
  set u : ℂ := w + (w ^ 2 + 1) ^ (1 / 2 : ℂ)
  have hu : u ≠ 0 := arsinhC_inner_ne_zero w
  have hs2 : ((w ^ 2 + 1) ^ (1 / 2 : ℂ)) ^ 2 = w ^ 2 + 1 := cpow_half_sq _
  have hu_inv : u⁻¹ = (w ^ 2 + 1) ^ (1 / 2 : ℂ) - w := by
    refine inv_eq_of_mul_eq_one_right ?_
    dsimp [u]
    linear_combination hs2
  unfold arsinhC
  change (Complex.exp (Complex.log u) - Complex.exp (-Complex.log u)) / 2 = w
  rw [Complex.exp_log hu, Complex.exp_neg, Complex.exp_log hu, hu_inv]
  dsimp [u]
  ring

lemma cos_arccosC (Z : ℂ) : Complex.cos (arccosC Z) = Z := by
  set u : ℂ := Z + Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ)
  have hu : u ≠ 0 := arccosC_inner_ne_zero Z
  have hs2 : ((1 - Z ^ 2) ^ (1 / 2 : ℂ)) ^ 2 = 1 - Z ^ 2 := cpow_half_sq _
  have hu_inv : u⁻¹ = Z - Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ) := by
    refine inv_eq_of_mul_eq_one_right ?_
    dsimp [u]
    calc (Z + Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ)) * (Z - Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ))
        = Z ^ 2 - Complex.I ^ 2 * ((1 - Z ^ 2) ^ (1 / 2 : ℂ)) ^ 2 := by ring
      _ = Z ^ 2 + (1 - Z ^ 2) := by rw [Complex.I_sq, hs2]; ring
      _ = 1 := by ring
  unfold arccosC
  change (Complex.exp ((-Complex.I * Complex.log u) * Complex.I) +
    Complex.exp (-(-Complex.I * Complex.log u) * Complex.I)) / 2 = Z
  have hII : -Complex.I * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
  have h1 : Complex.exp ((-Complex.I * Complex.log u) * Complex.I) = u := by
    rw [show (-Complex.I * Complex.log u) * Complex.I = Complex.log u * (-Complex.I * Complex.I) by ring,
      hII, mul_one, Complex.exp_log hu]
  have h2 : Complex.exp (-(-Complex.I * Complex.log u) * Complex.I) = u⁻¹ := by
    rw [show -(-Complex.I * Complex.log u) * Complex.I = -Complex.log u * (-Complex.I * Complex.I) by ring,
      hII, mul_one, Complex.exp_neg, Complex.exp_log hu]
  rw [h1, h2, hu_inv]
  dsimp [u]
  ring

lemma arsinhC_ofReal (x : ℝ) : arsinhC (x : ℂ) = (Real.arsinh x : ℂ) := by
  unfold arsinhC Real.arsinh
  have hnn : 0 ≤ x ^ 2 + 1 := by positivity
  have hsq : ((x : ℂ) ^ 2 + 1) ^ (1 / 2 : ℂ) = (√(x ^ 2 + 1) : ℂ) := by
    rw [show (x : ℂ) ^ 2 + 1 = ((x ^ 2 + 1 : ℝ) : ℂ) by push_cast; rfl]
    exact cpow_half_ofReal_nonneg hnn
  have hpos : 0 < x + √(x ^ 2 + 1) := by
    have h1 : |x| < √(x ^ 2 + 1) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_lt_sqrt (sq_nonneg x) (by linarith)
    linarith [neg_abs_le x]
  rw [hsq, ← Complex.ofReal_add, ← Complex.ofReal_log hpos.le, add_comm (1 : ℝ) (x ^ 2)]

lemma arccosC_ofReal {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    arccosC (x : ℂ) = (Real.arccos x : ℂ) := by
  unfold arccosC
  have hnn : 0 ≤ 1 - x ^ 2 := by nlinarith
  have hsq : (1 - (x : ℂ) ^ 2) ^ (1 / 2 : ℂ) = (√(1 - x ^ 2) : ℂ) := by
    rw [show 1 - (x : ℂ) ^ 2 = ((1 - x ^ 2 : ℝ) : ℂ) by push_cast; rfl]
    exact cpow_half_ofReal_nonneg hnn
  have hexp : (x : ℂ) + Complex.I * (√(1 - x ^ 2) : ℂ) =
      Complex.exp ((Real.arccos x : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [Real.cos_arccos hx1 hx2, Real.sin_arccos]
    ring
  have him_gt : -Real.pi < ((Real.arccos x : ℂ) * Complex.I).im := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    linarith [Real.arccos_nonneg x, Real.pi_pos]
  have him_le : ((Real.arccos x : ℂ) * Complex.I).im ≤ Real.pi := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    exact Real.arccos_le_pi x
  rw [hsq, hexp, Complex.log_exp him_gt him_le]
  rw [← mul_assoc, show -Complex.I * (Real.arccos x : ℂ) * Complex.I =
    (Real.arccos x : ℂ) * (-Complex.I * Complex.I) by ring, neg_mul, Complex.I_mul_I, neg_neg,
    mul_one]

lemma hasDerivAt_arsinhC {w : ℂ} (h1 : w ^ 2 + 1 ∈ Complex.slitPlane)
    (h2 : w + (w ^ 2 + 1) ^ (1 / 2 : ℂ) ∈ Complex.slitPlane) :
    HasDerivAt arsinhC ((w ^ 2 + 1) ^ (-(1 / 2 : ℂ))) w := by
  have hw2 : HasDerivAt (fun z : ℂ => z ^ 2 + 1) (2 * w) w := by
    simpa using (hasDerivAt_pow 2 w).add_const 1
  have hsqrt : HasDerivAt (fun z : ℂ => (z ^ 2 + 1) ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * (w ^ 2 + 1) ^ ((1 / 2 : ℂ) - 1) * (2 * w)) w :=
    hw2.cpow_const h1
  have hsum : HasDerivAt (fun z : ℂ => z + (z ^ 2 + 1) ^ (1 / 2 : ℂ))
      (1 + (1 / 2 : ℂ) * (w ^ 2 + 1) ^ ((1 / 2 : ℂ) - 1) * (2 * w)) w :=
    (hasDerivAt_id w).add hsqrt
  have hlog := (Complex.hasDerivAt_log h2).comp w hsum
  refine hlog.congr_deriv ?_
  have hpow : (w ^ 2 + 1) ^ ((1 / 2 : ℂ) - 1) = (w ^ 2 + 1) ^ (-(1 / 2 : ℂ)) := by norm_num
  have hmul_pow : (w ^ 2 + 1) ^ (1 / 2 : ℂ) * (w ^ 2 + 1) ^ (-(1 / 2 : ℂ)) = 1 := by
    rw [← Complex.cpow_add _ _ (Complex.slitPlane_ne_zero h1)]
    norm_num
  have hsum_ne : w + (w ^ 2 + 1) ^ (1 / 2 : ℂ) ≠ 0 := arsinhC_inner_ne_zero w
  rw [hpow]
  calc (w + (w ^ 2 + 1) ^ (1 / 2 : ℂ))⁻¹ *
        (1 + 1 / 2 * (w ^ 2 + 1) ^ (-(1 / 2 : ℂ)) * (2 * w))
      = (w + (w ^ 2 + 1) ^ (1 / 2 : ℂ))⁻¹ *
          ((w ^ 2 + 1) ^ (1 / 2 : ℂ) * (w ^ 2 + 1) ^ (-(1 / 2 : ℂ)) +
            w * (w ^ 2 + 1) ^ (-(1 / 2 : ℂ))) := by
        rw [hmul_pow]; ring
    _ = (w + (w ^ 2 + 1) ^ (1 / 2 : ℂ))⁻¹ *
          ((w + (w ^ 2 + 1) ^ (1 / 2 : ℂ)) * (w ^ 2 + 1) ^ (-(1 / 2 : ℂ))) := by ring
    _ = (w ^ 2 + 1) ^ (-(1 / 2 : ℂ)) := by field_simp [hsum_ne]

lemma hasDerivAt_arccosC {Z : ℂ} (h1 : 1 - Z ^ 2 ∈ Complex.slitPlane)
    (h2 : Z + Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ) ∈ Complex.slitPlane) :
    HasDerivAt arccosC (-((1 - Z ^ 2) ^ (-(1 / 2 : ℂ)))) Z := by
  have hz2 : HasDerivAt (fun z : ℂ => 1 - z ^ 2) (-(2 * Z)) Z := by
    simpa using (hasDerivAt_pow 2 Z).const_sub (1 : ℂ)
  have hsqrt : HasDerivAt (fun z : ℂ => (1 - z ^ 2) ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * (1 - Z ^ 2) ^ ((1 / 2 : ℂ) - 1) * (-(2 * Z))) Z :=
    hz2.cpow_const h1
  have hsum : HasDerivAt (fun z : ℂ => z + Complex.I * (1 - z ^ 2) ^ (1 / 2 : ℂ))
      (1 + Complex.I * ((1 / 2 : ℂ) * (1 - Z ^ 2) ^ ((1 / 2 : ℂ) - 1) * (-(2 * Z)))) Z :=
    (hasDerivAt_id Z).add (hsqrt.const_mul Complex.I)
  have hlog := ((Complex.hasDerivAt_log h2).comp Z hsum).const_mul (-Complex.I)
  refine hlog.congr_deriv ?_
  have hpow : (1 - Z ^ 2) ^ ((1 / 2 : ℂ) - 1) = (1 - Z ^ 2) ^ (-(1 / 2 : ℂ)) := by norm_num
  have hmul_pow : (1 - Z ^ 2) ^ (1 / 2 : ℂ) * (1 - Z ^ 2) ^ (-(1 / 2 : ℂ)) = 1 := by
    rw [← Complex.cpow_add _ _ (Complex.slitPlane_ne_zero h1)]
    norm_num
  have hsum_ne : Z + Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := arccosC_inner_ne_zero Z
  rw [hpow]
  calc -Complex.I * ((Z + Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ))⁻¹ *
        (1 + Complex.I * (1 / 2 * (1 - Z ^ 2) ^ (-(1 / 2 : ℂ)) * -(2 * Z))))
      = -Complex.I * ((Z + Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ))⁻¹ *
          ((1 - Z ^ 2) ^ (1 / 2 : ℂ) * (1 - Z ^ 2) ^ (-(1 / 2 : ℂ)) -
            Complex.I * Z * (1 - Z ^ 2) ^ (-(1 / 2 : ℂ)))) := by
        rw [hmul_pow]; ring
    _ = (Z + Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ))⁻¹ *
          ((-Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ) + Complex.I ^ 2 * Z) *
            (1 - Z ^ 2) ^ (-(1 / 2 : ℂ))) := by ring
    _ = (Z + Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ))⁻¹ *
          (-(Z + Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ)) * (1 - Z ^ 2) ^ (-(1 / 2 : ℂ))) := by
        rw [Complex.I_sq]; ring
    _ = -((1 - Z ^ 2) ^ (-(1 / 2 : ℂ))) := by field_simp [hsum_ne]

lemma analyticAt_arsinhC {w : ℂ} (h1 : w ^ 2 + 1 ∈ Complex.slitPlane)
    (h2 : w + (w ^ 2 + 1) ^ (1 / 2 : ℂ) ∈ Complex.slitPlane) :
    AnalyticAt ℂ arsinhC w := by
  unfold arsinhC
  have hw2 : AnalyticAt ℂ (fun z : ℂ => z ^ 2 + 1) w := by fun_prop
  have hsqrt : AnalyticAt ℂ (fun z : ℂ => (z ^ 2 + 1) ^ (1 / 2 : ℂ)) w :=
    hw2.cpow analyticAt_const h1
  exact (analyticAt_id.add hsqrt).clog h2

lemma analyticAt_arccosC {Z : ℂ} (h1 : 1 - Z ^ 2 ∈ Complex.slitPlane)
    (h2 : Z + Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ) ∈ Complex.slitPlane) :
    AnalyticAt ℂ arccosC Z := by
  unfold arccosC
  have hz2 : AnalyticAt ℂ (fun z : ℂ => 1 - z ^ 2) Z := by fun_prop
  have hsqrt : AnalyticAt ℂ (fun z : ℂ => (1 - z ^ 2) ^ (1 / 2 : ℂ)) Z :=
    hz2.cpow analyticAt_const h1
  exact analyticAt_const.mul ((analyticAt_id.add (analyticAt_const.mul hsqrt)).clog h2)

lemma arsinhC_conj {w : ℂ} (h1 : w ^ 2 + 1 ∈ Complex.slitPlane)
    (h2 : w + (w ^ 2 + 1) ^ (1 / 2 : ℂ) ∈ Complex.slitPlane) :
    arsinhC (starRingEnd ℂ w) = starRingEnd ℂ (arsinhC w) := by
  unfold arsinhC
  have h1' : (w ^ 2 + 1).arg ≠ Real.pi := (Complex.mem_slitPlane_iff_arg.mp h1).1
  have h2' : (w + (w ^ 2 + 1) ^ (1 / 2 : ℂ)).arg ≠ Real.pi :=
    (Complex.mem_slitPlane_iff_arg.mp h2).1
  have hsq : ((starRingEnd ℂ w) ^ 2 + 1) ^ (1 / 2 : ℂ) =
      starRingEnd ℂ ((w ^ 2 + 1) ^ (1 / 2 : ℂ)) := by
    rw [show (starRingEnd ℂ w) ^ 2 + 1 = starRingEnd ℂ (w ^ 2 + 1) by simp]
    exact cpow_half_conj h1'
  rw [hsq, ← map_add, Complex.log_conj _ h2']

lemma arccosC_conj {Z : ℂ} (h1 : 1 - Z ^ 2 ∈ Complex.slitPlane)
    (h2 : Z + Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ) ∈ Complex.slitPlane) :
    arccosC (starRingEnd ℂ Z) = starRingEnd ℂ (arccosC Z) := by
  unfold arccosC
  set s : ℂ := (1 - Z ^ 2) ^ (1 / 2 : ℂ)
  set u : ℂ := Z + Complex.I * s
  have h1' : (1 - Z ^ 2).arg ≠ Real.pi := (Complex.mem_slitPlane_iff_arg.mp h1).1
  have hsq : (1 - (starRingEnd ℂ Z) ^ 2) ^ (1 / 2 : ℂ) = starRingEnd ℂ s := by
    rw [show 1 - (starRingEnd ℂ Z) ^ 2 = starRingEnd ℂ (1 - Z ^ 2) by simp]
    exact cpow_half_conj h1'
  have hs2 : s ^ 2 = 1 - Z ^ 2 := cpow_half_sq _
  have hu_inv : u⁻¹ = Z - Complex.I * s := by
    refine inv_eq_of_mul_eq_one_right ?_
    dsimp [u]
    calc (Z + Complex.I * s) * (Z - Complex.I * s)
        = Z ^ 2 - Complex.I ^ 2 * s ^ 2 := by ring
      _ = Z ^ 2 + (1 - Z ^ 2) := by rw [Complex.I_sq, hs2]; ring
      _ = 1 := by ring
  have h_inner : starRingEnd ℂ Z + Complex.I * (1 - (starRingEnd ℂ Z) ^ 2) ^ (1 / 2 : ℂ) =
      (starRingEnd ℂ u)⁻¹ := by
    rw [hsq, ← map_inv₀, hu_inv, map_sub, map_mul, Complex.conj_I, sub_eq_add_neg, neg_mul, neg_neg]
  have huc : starRingEnd ℂ u ∈ Complex.slitPlane := conj_mem_slitPlane_iff.mpr h2
  have hlog_inv : Complex.log ((starRingEnd ℂ u)⁻¹) = -Complex.log (starRingEnd ℂ u) :=
    Complex.log_inv _ (Complex.mem_slitPlane_iff_arg.mp huc).1
  have hu_arg : u.arg ≠ Real.pi := (Complex.mem_slitPlane_iff_arg.mp h2).1
  rw [h_inner, hlog_inv, Complex.log_conj _ hu_arg]
  simp only [map_mul, map_neg, Complex.conj_I]
  ring

lemma re_arsinhC_pos {w : ℂ} (hw : 0 < w.re) : 0 < (arsinhC w).re := by
  have hw2_slit : w ^ 2 + 1 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_cases him : w.im = 0
    · left
      rw [Complex.add_re, Complex.one_re, sq, Complex.mul_re, him, mul_zero, sub_zero]
      positivity
    · right
      rw [Complex.add_im, Complex.one_im, add_zero, sq, Complex.mul_im]
      intro h0'
      have : 2 * w.re * w.im = 0 := by linarith
      rcases mul_eq_zero.mp this with h2 | him'
      · linarith
      · exact him him'
  have hs_re : 0 < ((w ^ 2 + 1) ^ (1 / 2 : ℂ)).re := cpow_half_re_pos hw2_slit
  set u : ℂ := w + (w ^ 2 + 1) ^ (1 / 2 : ℂ)
  have hu_re : 0 < u.re := by
    have : u.re = w.re + ((w ^ 2 + 1) ^ (1 / 2 : ℂ)).re := Complex.add_re _ _
    linarith
  have hu_ne : u ≠ 0 := arsinhC_inner_ne_zero w
  have hs2 : ((w ^ 2 + 1) ^ (1 / 2 : ℂ)) ^ 2 = w ^ 2 + 1 := cpow_half_sq _
  have hu_inv : u⁻¹ = (w ^ 2 + 1) ^ (1 / 2 : ℂ) - w := by
    refine inv_eq_of_mul_eq_one_right ?_
    dsimp [u]; linear_combination hs2
  have hsub_re : (u - u⁻¹).re = 2 * w.re := by
    rw [hu_inv]
    change (w + (w ^ 2 + 1) ^ (1 / 2 : ℂ) - ((w ^ 2 + 1) ^ (1 / 2 : ℂ) - w)).re = 2 * w.re
    rw [Complex.sub_re, Complex.add_re, Complex.sub_re]
    ring
  have hinv_re : (u⁻¹).re = u.re / Complex.normSq u := Complex.inv_re u
  have hnorm_gt : 1 < ‖u‖ := by
    by_contra hle
    push Not at hle
    have hnsq : Complex.normSq u ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg u]
    have hnsq_pos : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu_ne
    have hle_inv : u.re ≤ (u⁻¹).re := by
      rw [hinv_re]
      exact (le_div_iff₀ hnsq_pos).mpr (by nlinarith)
    rw [Complex.sub_re] at hsub_re
    linarith
  unfold arsinhC
  rw [Complex.log_re]
  exact Real.log_pos hnorm_gt

/-! ### Section 2: Strip chart definitions (`chartB`, `chartQ`, `chartOmega`, `muStar`) -/

/-- Reference left-edge real part `μ* = π ξ* / 3` (`lower_o1_two_edge.tex`, eq. `vlo:eOm`). -/
noncomputable def muStar : ℝ := Real.pi * xiStar / 3

lemma muStar_pos : 0 < muStar := by
  unfold muStar; have := Real.pi_pos; have := xiStar_pos; positivity

/-- Chart function `b(ζ) = π⁻¹ arsinh √(cos πζ)` (`lower_o1_two_edge.tex`, eq. `vlo:ebq`). -/
noncomputable def chartB (ζ : ℂ) : ℂ :=
  (Real.pi : ℂ)⁻¹ * arsinhC ((Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ))

/-- Chart function `q(ζ) = π⁻¹ arccos(√2 sin(πζ/2))` (`lower_o1_two_edge.tex`, eq. `vlo:ebq`). -/
noncomputable def chartQ (ζ : ℂ) : ℂ :=
  (Real.pi : ℂ)⁻¹ * arccosC ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2))

/-- Product `(2π/3) b(ζ) q(ζ)` on the left half-strip (`lower_o1_two_edge.tex`, eq. `vlo:eOm`). -/
noncomputable def chartOmegaHalf (ζ : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) / 3) * chartB ζ * chartQ ζ

/-- Strip parametrization `ω(ζ)` extended to `0 ≤ Re ζ ≤ 1` by reflection `ω(1 - ζ) = -ω(ζ)`
(`lower_o1_two_edge.tex`, Lemma S3). -/
noncomputable def chartOmega (ζ : ℂ) : ℂ :=
  if ζ.re ≤ 1 / 2 then chartOmegaHalf ζ else -chartOmegaHalf (1 - ζ)

/-- Left-edge coordinate `x₀(τ) = π⁻¹ arsinh √(cosh πτ)` (`lower_o1_two_edge.tex`, Lemma S3). -/
noncomputable def edgeX0 (τ : ℝ) : ℝ :=
  Real.arsinh (√(Real.cosh (Real.pi * τ))) / Real.pi

/-- Left-edge coordinate `y₀(τ) = π⁻¹ arsinh(√2 sinh(πτ/2))` (`lower_o1_two_edge.tex`, Lemma S3). -/
noncomputable def edgeY0 (τ : ℝ) : ℝ :=
  Real.arsinh (√2 * Real.sinh (Real.pi * τ / 2)) / Real.pi

/-- Left-edge real part `μ(τ) = (π/3) x₀(τ)` (`lower_o1_two_edge.tex`, Lemma S3). -/
noncomputable def edgeMu (τ : ℝ) : ℝ := (Real.pi / 3) * edgeX0 τ

/-- Left-edge imaginary part `ν(τ) = (2π/3) x₀(τ) y₀(τ)` (`lower_o1_two_edge.tex`, Lemma S3). -/
noncomputable def edgeNu (τ : ℝ) : ℝ := (2 * Real.pi / 3) * edgeX0 τ * edgeY0 τ

lemma chartB_zero : chartB 0 = (xiStar : ℂ) := by
  unfold chartB xiStar
  have h1 : Complex.cos ((Real.pi : ℂ) * 0) = 1 := by simp
  rw [h1, Complex.one_cpow, show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num, arsinhC_ofReal]
  push_cast; ring

lemma chartQ_zero : chartQ 0 = (1 / 2 : ℂ) := by
  unfold chartQ
  rw [mul_zero, zero_div, Complex.sin_zero, mul_zero, show (0 : ℂ) = ((0 : ℝ) : ℂ) by norm_num,
    arccosC_ofReal (by norm_num) (by norm_num), Real.arccos_zero]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  push_cast; field_simp [hpi]

lemma chartOmega_zero : chartOmega 0 = (muStar : ℂ) := by
  unfold chartOmega chartOmegaHalf muStar
  simp only [Complex.zero_re, show (0 : ℝ) ≤ 1 / 2 by norm_num, ↓reduceIte]
  rw [chartB_zero, chartQ_zero]
  push_cast; ring

lemma chartB_half : chartB (1 / 2 : ℂ) = 0 := by
  unfold chartB arsinhC
  have hcos : Complex.cos ((Real.pi : ℂ) * (1 / 2 : ℂ)) = 0 := by
    rw [show (Real.pi : ℂ) * (1 / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero]
  rw [hcos]
  norm_num

lemma chartQ_half : chartQ (1 / 2 : ℂ) = 0 := by
  unfold chartQ
  have hsin : (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * (1 / 2 : ℂ) / 2) = ((1 : ℝ) : ℂ) := by
    rw [show (Real.pi : ℂ) * (1 / 2 : ℂ) / 2 = ((Real.pi / 4 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_sin, Real.sin_pi_div_four]
    have h2 : √2 * (√2 / 2) = 1 := by
      rw [mul_div_assoc', Real.mul_self_sqrt (by norm_num)]; norm_num
    rw [← Complex.ofReal_mul, h2, Complex.ofReal_one]
  rw [hsin, arccosC_ofReal (by norm_num) (by norm_num), Real.arccos_one]
  simp

lemma chartOmega_half : chartOmega (1 / 2 : ℂ) = 0 := by
  unfold chartOmega chartOmegaHalf
  simp only [Complex.div_ofNat_re, Complex.one_re, show (1 : ℝ) / 2 ≤ 1 / 2 by norm_num, ↓reduceIte]
  rw [chartB_half, mul_zero, zero_mul]

lemma chartB_ofReal_Icc {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    chartB (x : ℂ) = ((Real.arsinh (√(Real.cos (Real.pi * x))) / Real.pi : ℝ) : ℂ) := by
  unfold chartB
  have hcos_nn : 0 ≤ Real.cos (Real.pi * x) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  rw [show (Real.pi : ℂ) * (x : ℂ) = ((Real.pi * x : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cos, cpow_half_ofReal_nonneg hcos_nn, arsinhC_ofReal]
  push_cast; ring

lemma chartQ_ofReal_Icc {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    chartQ (x : ℂ) = ((Real.arccos (√2 * Real.sin (Real.pi * x / 2)) / Real.pi : ℝ) : ℂ) := by
  unfold chartQ
  have harg0 : 0 ≤ Real.pi * x / 2 := by nlinarith [Real.pi_pos]
  have harg1 : Real.pi * x / 2 ≤ Real.pi / 4 := by nlinarith [Real.pi_pos]
  have hsin_le : Real.sin (Real.pi * x / 2) ≤ Real.sin (Real.pi / 4) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) harg1
  have hsin_nn : 0 ≤ Real.sin (Real.pi * x / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi harg0 (by linarith [Real.pi_pos])
  have hZ0 : -1 ≤ √2 * Real.sin (Real.pi * x / 2) := by
    have : 0 ≤ √2 * Real.sin (Real.pi * x / 2) := by positivity
    linarith
  have hZ1 : √2 * Real.sin (Real.pi * x / 2) ≤ 1 := by
    have h2 : √2 * (√2 / 2) = 1 := by
      rw [mul_div_assoc', Real.mul_self_sqrt (by norm_num)]; norm_num
    calc √2 * Real.sin (Real.pi * x / 2)
        ≤ √2 * Real.sin (Real.pi / 4) := by gcongr
      _ = √2 * (√2 / 2) := by rw [Real.sin_pi_div_four]
      _ = 1 := h2
  rw [show (Real.pi : ℂ) * (x : ℂ) / 2 = ((Real.pi * x / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_sin,
    show (√2 : ℂ) * ((Real.sin (Real.pi * x / 2) : ℝ) : ℂ) =
      ((√2 * Real.sin (Real.pi * x / 2) : ℝ) : ℂ) by push_cast; rfl,
    arccosC_ofReal hZ0 hZ1]
  push_cast; ring

/-- **Lemma S3 (positivity on `(0, 1/2)`)** (`lower_o1_two_edge.tex`, Lemma S3):
for real `x ∈ (0, 1/2)`, `b(x)` is real and strictly positive. -/
theorem chartB_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    0 < (chartB (x : ℂ)).re ∧ (chartB (x : ℂ)).im = 0 := by
  rw [chartB_ofReal_Icc hx.1.le hx.2.le, Complex.ofReal_re, Complex.ofReal_im]
  have hcos : 0 < Real.cos (Real.pi * x) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos, hx.1], by nlinarith [Real.pi_pos, hx.2]⟩
  have harsinh : 0 < Real.arsinh (√(Real.cos (Real.pi * x))) := by
    rw [← Real.arsinh_zero]
    exact Real.arsinh_strictMono (Real.sqrt_pos.mpr hcos)
  exact ⟨div_pos harsinh Real.pi_pos, rfl⟩

/-- **Lemma S3 (positivity on `(0, 1/2)`)** (`lower_o1_two_edge.tex`, Lemma S3):
for real `x ∈ (0, 1/2)`, `q(x)` is real and strictly positive. -/
theorem chartQ_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    0 < (chartQ (x : ℂ)).re ∧ (chartQ (x : ℂ)).im = 0 := by
  rw [chartQ_ofReal_Icc hx.1.le hx.2.le, Complex.ofReal_re, Complex.ofReal_im]
  have harg1 : Real.pi * x / 2 < Real.pi / 4 := by nlinarith [Real.pi_pos, hx.2]
  have hsin : Real.sin (Real.pi * x / 2) < Real.sin (Real.pi / 4) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by nlinarith [Real.pi_pos, hx.1])
      (by linarith [Real.pi_pos]) harg1
  have hZ1 : √2 * Real.sin (Real.pi * x / 2) < 1 := by
    have h2 : √2 * (√2 / 2) = 1 := by
      rw [mul_div_assoc', Real.mul_self_sqrt (by norm_num)]; norm_num
    calc √2 * Real.sin (Real.pi * x / 2)
        < √2 * Real.sin (Real.pi / 4) := by gcongr
      _ = √2 * (√2 / 2) := by rw [Real.sin_pi_div_four]
      _ = 1 := h2
  have harccos : 0 < Real.arccos (√2 * Real.sin (Real.pi * x / 2)) :=
    Real.arccos_pos.mpr hZ1
  exact ⟨div_pos harccos Real.pi_pos, rfl⟩

lemma chartOmega_ofReal_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    0 < (chartOmega (x : ℂ)).re ∧ (chartOmega (x : ℂ)).im = 0 := by
  unfold chartOmega chartOmegaHalf
  simp only [Complex.ofReal_re, show x ≤ 1 / 2 by exact hx.2.le, ↓reduceIte]
  obtain ⟨hb_re, hb_im⟩ := chartB_pos_of_mem_Ioo hx
  obtain ⟨hq_re, hq_im⟩ := chartQ_pos_of_mem_Ioo hx
  have hb_eq : chartB (x : ℂ) = ((chartB (x : ℂ)).re : ℂ) := Complex.ext rfl hb_im
  have hq_eq : chartQ (x : ℂ) = ((chartQ (x : ℂ)).re : ℂ) := Complex.ext rfl hq_im
  rw [hb_eq, hq_eq]
  have hprod : (2 * (Real.pi : ℂ) / 3) * ((chartB (x : ℂ)).re : ℂ) * ((chartQ (x : ℂ)).re : ℂ) =
      (((2 * Real.pi / 3) * (chartB (x : ℂ)).re * (chartQ (x : ℂ)).re : ℝ) : ℂ) := by
    push_cast; ring
  rw [hprod, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨by have := Real.pi_pos; positivity, rfl⟩

/-! ### Section 3: Left-edge formulas (`ζ = iτ`) -/

lemma chartB_left_edge (τ : ℝ) : chartB (Complex.I * (τ : ℂ)) = (edgeX0 τ : ℂ) := by
  unfold chartB edgeX0
  have hcos : Complex.cos ((Real.pi : ℂ) * (Complex.I * (τ : ℂ))) = (Real.cosh (Real.pi * τ) : ℂ) := by
    rw [show (Real.pi : ℂ) * (Complex.I * (τ : ℂ)) = ((Real.pi * τ : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.cos_mul_I, Complex.ofReal_cosh]
  have hnn : 0 ≤ Real.cosh (Real.pi * τ) := (Real.cosh_pos _).le
  rw [hcos, cpow_half_ofReal_nonneg hnn, arsinhC_ofReal]
  push_cast; ring

lemma chartQ_left_edge (τ : ℝ) :
    chartQ (Complex.I * (τ : ℂ)) = (1 / 2 : ℂ) - Complex.I * (edgeY0 τ : ℂ) := by
  unfold chartQ arccosC edgeY0
  have hsin : (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * (Complex.I * (τ : ℂ)) / 2) =
      Complex.I * ((√2 * Real.sinh (Real.pi * τ / 2) : ℝ) : ℂ) := by
    rw [show (Real.pi : ℂ) * (Complex.I * (τ : ℂ)) / 2 = ((Real.pi * τ / 2 : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.sin_mul_I, ← Complex.ofReal_sinh]
    push_cast; ring
  set y : ℝ := √2 * Real.sinh (Real.pi * τ / 2)
  have h1z : 1 - (Complex.I * (y : ℂ)) ^ 2 = ((1 + y ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq]; push_cast; ring
  have hsq : (1 - (Complex.I * (y : ℂ)) ^ 2) ^ (1 / 2 : ℂ) = (√(1 + y ^ 2) : ℂ) := by
    rw [h1z]; exact cpow_half_ofReal_nonneg (by positivity)
  have hR_pos : 0 < √(1 + y ^ 2) + y := by
    have hlt : |y| < √(1 + y ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg y) (by linarith)
    linarith [neg_abs_le y]
  have hsum : Complex.I * (y : ℂ) + Complex.I * (√(1 + y ^ 2) : ℂ) =
      Complex.I * ((√(1 + y ^ 2) + y : ℝ) : ℂ) := by
    push_cast; ring
  have hlog : Complex.log (Complex.I * ((√(1 + y ^ 2) + y : ℝ) : ℂ)) =
      (Real.log (√(1 + y ^ 2) + y) : ℂ) + Complex.I * ((Real.pi / 2 : ℝ) : ℂ) := by
    have harg : Complex.I.arg + ((√(1 + y ^ 2) + y : ℝ) : ℂ).arg ∈ Ioc (-Real.pi) Real.pi := by
      rw [Complex.arg_I, Complex.arg_ofReal_of_nonneg hR_pos.le, add_zero]
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    rw [Complex.log_mul Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hR_pos.ne') harg,
      Complex.log_I, ← Complex.ofReal_log hR_pos.le]
    push_cast; ring
  have harsinh : Real.log (√(1 + y ^ 2) + y) = Real.arsinh y := by
    unfold Real.arsinh; rw [add_comm]
  rw [hsin, hsq, hsum, hlog, harsinh]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  calc (Real.pi : ℂ)⁻¹ * (-Complex.I * ((Real.arsinh y : ℂ) + Complex.I * ((Real.pi / 2 : ℝ) : ℂ)))
      = (Real.pi : ℂ)⁻¹ * (-Complex.I * (Real.arsinh y : ℂ) - Complex.I ^ 2 * ((Real.pi / 2 : ℝ) : ℂ)) := by
        ring
    _ = (Real.pi : ℂ)⁻¹ * (-Complex.I * (Real.arsinh y : ℂ) + ((Real.pi / 2 : ℝ) : ℂ)) := by
        rw [Complex.I_sq]; ring
    _ = (1 / 2 : ℂ) - Complex.I * ((Real.arsinh y / Real.pi : ℝ) : ℂ) := by
        push_cast; field_simp [hpi]; ring

lemma chartOmega_left_edge (τ : ℝ) :
    chartOmega (Complex.I * (τ : ℂ)) = (edgeMu τ : ℂ) - Complex.I * (edgeNu τ : ℂ) := by
  unfold chartOmega chartOmegaHalf edgeMu edgeNu
  simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
    Complex.ofReal_im, mul_zero, sub_self, show (0 : ℝ) ≤ 1 / 2 by norm_num, ↓reduceIte]
  rw [chartB_left_edge, chartQ_left_edge]
  push_cast; ring

lemma sinh_pi_edgeX0 (τ : ℝ) : Real.sinh (Real.pi * edgeX0 τ) = √(Real.cosh (Real.pi * τ)) := by
  unfold edgeX0
  rw [mul_div_cancel₀ _ Real.pi_pos.ne', Real.sinh_arsinh]

lemma sinh_pi_edgeY0 (τ : ℝ) : Real.sinh (Real.pi * edgeY0 τ) = √2 * Real.sinh (Real.pi * τ / 2) := by
  unfold edgeY0
  rw [mul_div_cancel₀ _ Real.pi_pos.ne', Real.sinh_arsinh]

/-! ### Section 4: Slit-plane avoidance, positivity of `Re b, Re q`, analyticity, conjugation -/

lemma cos_pi_re_pos {ζ : ℂ} (h1 : -(1 / 2 : ℝ) < ζ.re) (h2 : ζ.re < 1 / 2) :
    0 < (Complex.cos ((Real.pi : ℂ) * ζ)).re := by
  rw [show (Real.pi : ℂ) * ζ = ((Real.pi * ζ.re : ℝ) : ℂ) + ((Real.pi * ζ.im : ℝ) : ℂ) * Complex.I by
    apply Complex.ext <;> simp]
  rw [Complex.cos_add_mul_I, Complex.sub_re, Complex.mul_re, ← Complex.ofReal_cos,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]
  have hcos : 0 < Real.cos (Real.pi * ζ.re) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have hcosh : 0 < Real.cosh (Real.pi * ζ.im) := Real.cosh_pos _
  nlinarith

lemma cos_pi_mem_slitPlane {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    Complex.cos ((Real.pi : ℂ) * ζ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hlt : ζ.re < 1 / 2
  · left; exact cos_pi_re_pos (by linarith) hlt
  · have hre : ζ.re = 1 / 2 := le_antisymm h1 (not_lt.mp hlt)
    have him : ζ.im ≠ 0 := by
      intro h0im
      exact hne (Complex.ext (by simp [hre]) (by simp [h0im]))
    right
    rw [show (Real.pi : ℂ) * ζ = ((Real.pi / 2 : ℝ) : ℂ) + ((Real.pi * ζ.im : ℝ) : ℂ) * Complex.I by
      apply Complex.ext <;> simp [hre]; ring]
    rw [Complex.cos_add_mul_I, ← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero,
      zero_mul, zero_sub, Complex.neg_im, ← Complex.ofReal_sin, Real.sin_pi_div_two,
      Complex.ofReal_one, one_mul, ← Complex.ofReal_sinh]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero, neg_ne_zero]
    exact Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_pos.ne' him)

lemma re_chartB_pos {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    0 < (chartB ζ).re := by
  unfold chartB
  have hcos := cos_pi_mem_slitPlane h0 h1 hne
  have hs_re : 0 < ((Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ)).re := cpow_half_re_pos hcos
  have ha_re : 0 < (arsinhC ((Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ))).re :=
    re_arsinhC_pos hs_re
  rw [show (Real.pi : ℂ)⁻¹ = ((Real.pi⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  exact mul_pos (inv_pos.mpr Real.pi_pos) ha_re

private lemma one_sub_two_sin_sq_eq_cos (ζ : ℂ) :
    1 - ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)) ^ 2 = Complex.cos ((Real.pi : ℂ) * ζ) := by
  have hc := Complex.cos_two_mul ((Real.pi : ℂ) * ζ / 2)
  have hsq := Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * ζ / 2)
  rw [show 2 * ((Real.pi : ℂ) * ζ / 2) = (Real.pi : ℂ) * ζ by ring] at hc
  have hsin2 : 2 * Complex.sin ((Real.pi : ℂ) * ζ / 2) ^ 2 = 1 - Complex.cos ((Real.pi : ℂ) * ζ) := by
    linear_combination 2 * hsq + hc
  have h2 : (√2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num)
  calc 1 - ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)) ^ 2
      = 1 - (√2 : ℂ) ^ 2 * Complex.sin ((Real.pi : ℂ) * ζ / 2) ^ 2 := by ring
    _ = 1 - 2 * Complex.sin ((Real.pi : ℂ) * ζ / 2) ^ 2 := by rw [h2]
    _ = Complex.cos ((Real.pi : ℂ) * ζ) := by rw [hsin2]; ring

lemma chartQ_inner_im_pos {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    0 < ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2) +
      Complex.I * (1 - ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)) ^ 2) ^ (1 / 2 : ℂ)).im := by
  set x := ζ.re
  set y := ζ.im
  let Z : ℂ := (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)
  change 0 < (Z + Complex.I * (1 - Z ^ 2) ^ (1 / 2 : ℂ)).im
  rw [show 1 - Z ^ 2 = Complex.cos ((Real.pi : ℂ) * ζ) from one_sub_two_sin_sq_eq_cos ζ,
    Complex.add_im]
  nth_rw 2 [Complex.mul_im]
  rw [Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  set s : ℂ := (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ)
  have hcos_slit : Complex.cos ((Real.pi : ℂ) * ζ) ∈ Complex.slitPlane := cos_pi_mem_slitPlane h0 h1 hne
  have hs_re : 0 < s.re := cpow_half_re_pos hcos_slit
  have hZ_im : Z.im = √2 * Real.cos (Real.pi * x / 2) * Real.sinh (Real.pi * y / 2) := by
    dsimp [Z]
    have harg_eq : (Real.pi : ℂ) * ζ / 2 =
        ((Real.pi * x / 2 : ℝ) : ℂ) + ((Real.pi * y / 2 : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [x, y]
      · simp [x, y]
    rw [harg_eq, Complex.sin_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
      ← Complex.ofReal_cos, ← Complex.ofReal_sinh]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.add_im, Complex.I_im, mul_one, Complex.I_re, Complex.add_re, Complex.mul_re,
      mul_zero, sub_zero, zero_add]
    ring
  have hs2 : s ^ 2 = Complex.cos ((Real.pi : ℂ) * ζ) := cpow_half_sq _
  have hpi_ζ : (Real.pi : ℂ) * ζ = ((Real.pi * x : ℝ) : ℂ) + ((Real.pi * y : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [x, y]
    · simp [x, y]
  have hcos_re : (Complex.cos ((Real.pi : ℂ) * ζ)).re = Real.cos (Real.pi * x) * Real.cosh (Real.pi * y) := by
    rw [hpi_ζ, Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
      ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
    simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one, sub_zero, zero_mul, add_zero]
  have hcos_im : (Complex.cos ((Real.pi : ℂ) * ζ)).im = -Real.sin (Real.pi * x) * Real.sinh (Real.pi * y) := by
    rw [hpi_ζ, Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
      ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
    simp only [Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one, sub_zero, zero_mul, add_zero,
      zero_sub]
    ring
  have hs2_re : s.re ^ 2 - s.im ^ 2 = Real.cos (Real.pi * x) * Real.cosh (Real.pi * y) := by
    have := congrArg Complex.re hs2
    rw [sq, Complex.mul_re, hcos_re] at this
    linarith
  have hs2_im : 2 * s.re * s.im = -Real.sin (Real.pi * x) * Real.sinh (Real.pi * y) := by
    have := congrArg Complex.im hs2
    rw [sq, Complex.mul_im, hcos_im] at this
    linarith
  by_cases hy : y = 0
  · simp [hZ_im, hy, hs_re]
  · suffices hlt : Z.im ^ 2 < s.re ^ 2 by
      have habs : |Z.im| < s.re := by
        rw [← Real.sqrt_sq hs_re.le, ← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_lt_sqrt (sq_nonneg _) hlt
      linarith [neg_abs_le Z.im]
    have hnorm_sq : (s.re ^ 2 + s.im ^ 2) ^ 2 =
        Real.cosh (Real.pi * y) ^ 2 - Real.sin (Real.pi * x) ^ 2 := by
      have hsc : Real.sin (Real.pi * x) ^ 2 + Real.cos (Real.pi * x) ^ 2 = 1 :=
        Real.sin_sq_add_cos_sq _
      have hhc : Real.cosh (Real.pi * y) ^ 2 - Real.sinh (Real.pi * y) ^ 2 = 1 :=
        Real.cosh_sq_sub_sinh_sq _
      calc (s.re ^ 2 + s.im ^ 2) ^ 2
          = (s.re ^ 2 - s.im ^ 2) ^ 2 + (2 * s.re * s.im) ^ 2 := by ring
        _ = (Real.cos (Real.pi * x) * Real.cosh (Real.pi * y)) ^ 2 +
              (-Real.sin (Real.pi * x) * Real.sinh (Real.pi * y)) ^ 2 := by rw [hs2_re, hs2_im]
        _ = Real.cos (Real.pi * x) ^ 2 * Real.cosh (Real.pi * y) ^ 2 +
              Real.sin (Real.pi * x) ^ 2 * (Real.cosh (Real.pi * y) ^ 2 - 1) := by
            have : Real.sinh (Real.pi * y) ^ 2 = Real.cosh (Real.pi * y) ^ 2 - 1 := by linarith
            rw [mul_pow, mul_pow, neg_sq, this]
        _ = (Real.cos (Real.pi * x) ^ 2 + Real.sin (Real.pi * x) ^ 2) * Real.cosh (Real.pi * y) ^ 2 -
              Real.sin (Real.pi * x) ^ 2 := by ring
        _ = Real.cosh (Real.pi * y) ^ 2 - Real.sin (Real.pi * x) ^ 2 := by
            rw [add_comm, hsc, one_mul]
    have hZ_sq : 2 * Z.im ^ 2 = (1 + Real.cos (Real.pi * x)) * (Real.cosh (Real.pi * y) - 1) := by
      rw [hZ_im]
      have h2cos : 2 * Real.cos (Real.pi * x / 2) ^ 2 = 1 + Real.cos (Real.pi * x) := by
        have := Real.cos_two_mul (Real.pi * x / 2)
        rw [show 2 * (Real.pi * x / 2) = Real.pi * x by ring] at this
        linarith
      have h2sinh : 2 * Real.sinh (Real.pi * y / 2) ^ 2 = Real.cosh (Real.pi * y) - 1 := by
        have := Real.cosh_two_mul (Real.pi * y / 2)
        rw [show 2 * (Real.pi * y / 2) = Real.pi * y by ring] at this
        have h1 := Real.cosh_sq_sub_sinh_sq (Real.pi * y / 2)
        linarith
      calc 2 * (√2 * Real.cos (Real.pi * x / 2) * Real.sinh (Real.pi * y / 2)) ^ 2
          = (2 * Real.cos (Real.pi * x / 2) ^ 2) * (2 * Real.sinh (Real.pi * y / 2) ^ 2) := by
            rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring
        _ = (1 + Real.cos (Real.pi * x)) * (Real.cosh (Real.pi * y) - 1) := by
            rw [h2cos, h2sinh]
    have hcosh_gt1 : 1 < Real.cosh (Real.pi * y) := by
      have hne0 : Real.pi * y ≠ 0 := mul_ne_zero Real.pi_pos.ne' hy
      have hsq : Real.cosh (Real.pi * y) ^ 2 = 1 + Real.sinh (Real.pi * y) ^ 2 := by
        linarith [Real.cosh_sq_sub_sinh_sq (Real.pi * y)]
      have hsh : 0 < Real.sinh (Real.pi * y) ^ 2 := sq_pos_of_ne_zero (Real.sinh_ne_zero.mpr hne0)
      nlinarith [Real.cosh_pos (Real.pi * y)]
    have h1cos_pos : 0 < 1 + Real.cos (Real.pi * x) := by
      have : 0 ≤ Real.cos (Real.pi * x) :=
        Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
      linarith
    suffices hdiff : Real.cosh (Real.pi * y) - 1 - Real.cos (Real.pi * x) < s.re ^ 2 + s.im ^ 2 by
      linarith
    have hr_pos : 0 ≤ s.re ^ 2 + s.im ^ 2 := by positivity
    by_cases hrhs : Real.cosh (Real.pi * y) - 1 - Real.cos (Real.pi * x) < 0
    · exact lt_of_lt_of_le hrhs hr_pos
    · push Not at hrhs
      have hsq_lt : (Real.cosh (Real.pi * y) - 1 - Real.cos (Real.pi * x)) ^ 2 <
          (s.re ^ 2 + s.im ^ 2) ^ 2 := by
        rw [hnorm_sq]
        have hsc : Real.sin (Real.pi * x) ^ 2 = 1 - Real.cos (Real.pi * x) ^ 2 := by
          linarith [Real.sin_sq_add_cos_sq (Real.pi * x)]
        rw [hsc]
        have hdiff_id : (Real.cosh (Real.pi * y) ^ 2 - (1 - Real.cos (Real.pi * x) ^ 2)) -
            (Real.cosh (Real.pi * y) - 1 - Real.cos (Real.pi * x)) ^ 2 =
            2 * (1 + Real.cos (Real.pi * x)) * (Real.cosh (Real.pi * y) - 1) := by ring
        have hpos : 0 < 2 * (1 + Real.cos (Real.pi * x)) * (Real.cosh (Real.pi * y) - 1) := by
          positivity
        linarith
      nlinarith

lemma re_chartQ_Ioo {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    0 < (chartQ ζ).re ∧ (chartQ ζ).re < 1 := by
  unfold chartQ arccosC
  set u : ℂ := (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2) +
    Complex.I * (1 - ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)) ^ 2) ^ (1 / 2 : ℂ)
  have him : 0 < u.im := chartQ_inner_im_pos h0 h1 hne
  have hu_ne : u ≠ 0 := by intro h; rw [h, Complex.zero_im] at him; exact lt_irrefl 0 him
  have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  have harg_eq : u.arg = Real.arccos (u.re / ‖u‖) := Complex.arg_of_im_pos him
  have hnsq : u.re ^ 2 + u.im ^ 2 = ‖u‖ ^ 2 := by
    rw [sq, sq, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq, sq]
  have hlt1 : u.re / ‖u‖ < 1 := by
    rw [div_lt_one hnorm_pos]
    have hsq : u.re ^ 2 < u.re ^ 2 + u.im ^ 2 := by linarith [sq_pos_of_pos him]
    nlinarith [norm_nonneg u]
  have hgt_neg1 : -1 < u.re / ‖u‖ := by
    rw [lt_div_iff₀ hnorm_pos]
    have hsq : u.re ^ 2 < u.re ^ 2 + u.im ^ 2 := by linarith [sq_pos_of_pos him]
    nlinarith [norm_nonneg u]
  have harg_pos : 0 < u.arg := by rw [harg_eq]; exact Real.arccos_pos.mpr hlt1
  have harg_lt : u.arg < Real.pi := by rw [harg_eq]; exact Real.arccos_lt_pi.mpr hgt_neg1
  have hre : ((Real.pi : ℂ)⁻¹ * (-Complex.I * Complex.log u)).re = u.arg / Real.pi := by
    rw [show (Real.pi : ℂ)⁻¹ = ((Real.pi⁻¹ : ℝ) : ℂ) by push_cast; rfl,
      Complex.re_ofReal_mul, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.log_im]
    ring
  rw [hre]
  exact ⟨div_pos harg_pos Real.pi_pos, (div_lt_one Real.pi_pos).mpr harg_lt⟩

lemma re_chartQ_pos {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    0 < (chartQ ζ).re := (re_chartQ_Ioo h0 h1 hne).1

lemma chartB_slitPlane {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    chartB ζ ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (re_chartB_pos h0 h1 hne))

lemma chartQ_slitPlane {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    chartQ ζ ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (re_chartQ_pos h0 h1 hne))

lemma arsinh_cos_inner_slitPlane {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    ((Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ)) ^ 2 + 1 ∈ Complex.slitPlane ∧
    (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ) +
      (((Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ)) ^ 2 + 1) ^ (1 / 2 : ℂ) ∈ Complex.slitPlane := by
  set w : ℂ := (Complex.cos ((Real.pi : ℂ) * ζ)) ^ (1 / 2 : ℂ)
  have hcos := cos_pi_mem_slitPlane h0 h1 hne
  have hw_re : 0 < w.re := cpow_half_re_pos hcos
  have hw2_slit : w ^ 2 + 1 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_cases him : w.im = 0
    · left
      rw [Complex.add_re, Complex.one_re, sq, Complex.mul_re, him, mul_zero, sub_zero]
      positivity
    · right
      rw [Complex.add_im, Complex.one_im, add_zero, sq, Complex.mul_im]
      intro h0'
      have : 2 * w.re * w.im = 0 := by linarith
      rcases mul_eq_zero.mp this with h2 | him'
      · linarith
      · exact him him'
  have hs_re : 0 < ((w ^ 2 + 1) ^ (1 / 2 : ℂ)).re := cpow_half_re_pos hw2_slit
  refine ⟨hw2_slit, Complex.mem_slitPlane_iff.mpr (Or.inl ?_)⟩
  have : (w + (w ^ 2 + 1) ^ (1 / 2 : ℂ)).re = w.re + ((w ^ 2 + 1) ^ (1 / 2 : ℂ)).re :=
    Complex.add_re _ _
  linarith

lemma arccos_sin_inner_slitPlane {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    1 - ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)) ^ 2 ∈ Complex.slitPlane ∧
    (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2) +
      Complex.I * (1 - ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)) ^ 2) ^ (1 / 2 : ℂ) ∈
        Complex.slitPlane := by
  refine ⟨?_, Complex.mem_slitPlane_iff.mpr (Or.inr (chartQ_inner_im_pos h0 h1 hne).ne')⟩
  rw [one_sub_two_sin_sq_eq_cos ζ]
  exact cos_pi_mem_slitPlane h0 h1 hne

lemma analyticAt_chartB {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    AnalyticAt ℂ chartB ζ := by
  obtain ⟨h1', h2'⟩ := arsinh_cos_inner_slitPlane h0 h1 hne
  have hcos_slit := cos_pi_mem_slitPlane h0 h1 hne
  have hcos_an : AnalyticAt ℂ (fun z : ℂ => Complex.cos ((Real.pi : ℂ) * z)) ζ := by
    fun_prop
  have hsqrt_an : AnalyticAt ℂ (fun z : ℂ => (Complex.cos ((Real.pi : ℂ) * z)) ^ (1 / 2 : ℂ)) ζ :=
    hcos_an.cpow analyticAt_const hcos_slit
  have hcomp : AnalyticAt ℂ (fun z : ℂ => arsinhC ((Complex.cos ((Real.pi : ℂ) * z)) ^ (1 / 2 : ℂ))) ζ :=
    (analyticAt_arsinhC h1' h2').comp (f := fun z : ℂ => (Complex.cos ((Real.pi : ℂ) * z)) ^ (1 / 2 : ℂ)) hsqrt_an
  exact analyticAt_const.mul hcomp

lemma analyticAt_chartQ {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    AnalyticAt ℂ chartQ ζ := by
  obtain ⟨h1', h2'⟩ := arccos_sin_inner_slitPlane h0 h1 hne
  have hZ_an : AnalyticAt ℂ (fun z : ℂ => (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * z / 2)) ζ := by
    fun_prop
  have hcomp : AnalyticAt ℂ (fun z : ℂ => arccosC ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * z / 2))) ζ :=
    (analyticAt_arccosC h1' h2').comp (f := fun z : ℂ => (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * z / 2)) hZ_an
  exact analyticAt_const.mul hcomp

lemma analyticAt_chartOmegaHalf {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    AnalyticAt ℂ chartOmegaHalf ζ :=
  (analyticAt_const.mul (analyticAt_chartB h0 h1 hne)).mul (analyticAt_chartQ h0 h1 hne)

lemma chartB_conj {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    chartB (starRingEnd ℂ ζ) = starRingEnd ℂ (chartB ζ) := by
  unfold chartB
  have hcos_slit := cos_pi_mem_slitPlane h0 h1 hne
  have hcos_arg : (Complex.cos ((Real.pi : ℂ) * ζ)).arg ≠ Real.pi :=
    (Complex.mem_slitPlane_iff_arg.mp hcos_slit).1
  have hcos_conj : Complex.cos ((Real.pi : ℂ) * starRingEnd ℂ ζ) =
      starRingEnd ℂ (Complex.cos ((Real.pi : ℂ) * ζ)) := by
    rw [← Complex.cos_conj, map_mul, Complex.conj_ofReal]
  obtain ⟨h1', h2'⟩ := arsinh_cos_inner_slitPlane h0 h1 hne
  rw [hcos_conj, cpow_half_conj hcos_arg, arsinhC_conj h1' h2']
  simp [Complex.conj_ofReal]

lemma chartQ_conj {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    chartQ (starRingEnd ℂ ζ) = starRingEnd ℂ (chartQ ζ) := by
  unfold chartQ
  have hsin_conj : (√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * starRingEnd ℂ ζ / 2) =
      starRingEnd ℂ ((√2 : ℂ) * Complex.sin ((Real.pi : ℂ) * ζ / 2)) := by
    rw [map_mul, Complex.conj_ofReal, ← Complex.sin_conj, map_div₀, map_mul, Complex.conj_ofReal,
      map_ofNat]
  obtain ⟨h1', h2'⟩ := arccos_sin_inner_slitPlane h0 h1 hne
  rw [hsin_conj, arccosC_conj h1' h2']
  simp [Complex.conj_ofReal]

lemma chartOmegaHalf_conj {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    chartOmegaHalf (starRingEnd ℂ ζ) = starRingEnd ℂ (chartOmegaHalf ζ) := by
  unfold chartOmegaHalf
  rw [chartB_conj h0 h1 hne, chartQ_conj h0 h1 hne]
  simp only [map_mul, map_div₀, map_ofNat, Complex.conj_ofReal]

end FormalResearch.ModularBootstrap.Chart
