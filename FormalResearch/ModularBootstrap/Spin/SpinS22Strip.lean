module

public import FormalResearch.ModularBootstrap.Spin.Statements
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Lemma S2.2 (`spinnotes:S22`), Part 1: strip holomorphy, real agreement, and uniform bistrip bound

Proves the first four clauses of `SpinS22` (`spinning_foundations.tex`, lines 188–231):
1. `spinG_eq_cosine_integral`: for `Φ ∈ \overline{\mathcal A}_{\rm spin}`, Fourier oddness and
   `D_4` invariance give the cosine integral representation of `\mathcal G` on `ℝ²`.
2. `spinDaC_eq_spinDa`: `spinDaC a Φ (xL : ℂ) (xR : ℂ) = ((spinDa a Φ xL xR : ℝ) : ℂ)`.
3. `norm_spinWa_le`: `‖W_a(r; b)‖ ≤ (1 + 4 (Re b)²) V_1(r)` for `|Im b| ≤ 1/2`, independent of `a`.
4. `norm_spinDaC_le`: uniform bistrip bound
   `‖spinDaC a Φ bL bR‖ ≤ (1 + 4 (Re bL)²)(1 + 4 (Re bR)²) M_2[Φ]`.
5. `differentiableOn_spinDaC_left`, `differentiableOn_spinDaC_right`: separate holomorphy of
   `spinDaC a Φ` on `\mathcal S_{1/2}²` by dominated differentiation under the integral sign.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform RealInnerProductSpace

namespace FormalResearch.ModularBootstrap.Spin

/-! ### Section 1: The 1D difference kernel `W_a(r; b)` and its strip/derivative bounds -/

/-- One-dimensional difference Fourier kernel
`W_a(r; b) = cos(4π √a r b) - cos(4π √(a - 2) r b)`. -/
noncomputable def spinWa (a r : ℝ) (b : ℂ) : ℂ :=
  Complex.cos (4 * π * (Real.sqrt a : ℂ) * (r : ℂ) * b) -
    Complex.cos (4 * π * (Real.sqrt (a - 2) : ℂ) * (r : ℂ) * b)

lemma spinWa_neg_r (a r : ℝ) (b : ℂ) : spinWa a (-r) b = spinWa a r b := by
  unfold spinWa
  have h1 : 4 * π * (Real.sqrt a : ℂ) * ((-r : ℝ) : ℂ) * b =
      -(4 * π * (Real.sqrt a : ℂ) * (r : ℂ) * b) := by push_cast; ring
  have h2 : 4 * π * (Real.sqrt (a - 2) : ℂ) * ((-r : ℝ) : ℂ) * b =
      -(4 * π * (Real.sqrt (a - 2) : ℂ) * (r : ℂ) * b) := by push_cast; ring
  rw [h1, h2, Complex.cos_neg, Complex.cos_neg]

/-- Product factorisation `W_a(r; b) = -2 sin(2 u b) sin(2 v b)` with
`u = π r (√a + √(a - 2))`, `v = π r (√a - √(a - 2))`. -/
lemma spinWa_eq_mul_sin (a r : ℝ) (b : ℂ) :
    spinWa a r b =
      -2 * Complex.sin (2 * ((π * r * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) * b) *
        Complex.sin (2 * ((π * r * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) * b) := by
  unfold spinWa
  set U : ℂ := 2 * ((π * r * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) * b
  set V : ℂ := 2 * ((π * r * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) * b
  have hadd : 4 * π * (Real.sqrt a : ℂ) * (r : ℂ) * b = U + V := by
    dsimp [U, V]; push_cast; ring
  have hsub : 4 * π * (Real.sqrt (a - 2) : ℂ) * (r : ℂ) * b = U - V := by
    dsimp [U, V]; push_cast; ring
  rw [hadd, hsub, Complex.cos_add, Complex.cos_sub]
  ring

/-- Product factorisation `V_1(r) = 2 sinh(u) sinh(v)` with
`u = π r (√a + √(a - 2))`, `v = π r (√a - √(a - 2))`. -/
lemma spinV1_eq_mul_sinh (a r : ℝ) :
    spinV1 a r =
      2 * Real.sinh (π * r * (Real.sqrt a + Real.sqrt (a - 2))) *
        Real.sinh (π * r * (Real.sqrt a - Real.sqrt (a - 2))) := by
  unfold spinV1
  set u : ℝ := π * r * (Real.sqrt a + Real.sqrt (a - 2))
  set v : ℝ := π * r * (Real.sqrt a - Real.sqrt (a - 2))
  have hadd : 2 * π * Real.sqrt a * r = u + v := by dsimp [u, v]; ring
  have hsub : 2 * π * Real.sqrt (a - 2) * r = u - v := by dsimp [u, v]; ring
  rw [hadd, hsub, Real.cosh_add, Real.cosh_sub]
  ring

/-- Elementary inequality `z ≤ sinh z` for `z ≥ 0`. -/
private lemma le_sinh_of_nonneg {z : ℝ} (hz : 0 ≤ z) : z ≤ Real.sinh z := by
  have h1 : 1 + z ≤ Real.exp z := by linarith [Real.add_one_le_exp z]
  have h2 : 1 - z ≤ Real.exp (-z) := by linarith [Real.add_one_le_exp (-z)]
  -- Wait: we need `exp (-z) ≤ 1 - z + ...`? No! `sinh z - z` has derivative `cosh z - 1 ≥ 0`!
  have hmono : MonotoneOn (fun t : ℝ => Real.sinh t - t) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop) fun t _ => ?_
    have hd : HasDerivAt (fun t : ℝ => Real.sinh t - t) (Real.cosh t - 1) t :=
      (Real.hasDerivAt_sinh t).sub (hasDerivAt_id t)
    rw [hd.deriv]
    linarith [Real.one_le_cosh t]
  have := hmono (le_rfl : (0 : ℝ) ∈ Ici 0) hz hz
  simp only [Real.sinh_zero, sub_self] at this
  linarith

/-- Key 1D trigonometric bound: for `z ≥ 0` and `|Im b| ≤ 1/2`,
`‖sin(2 z b)‖² ≤ (1 + 4 (Re b)²) sinh(z)²`. -/
private lemma norm_sin_two_mul_sq_le {z : ℝ} (hz : 0 ≤ z) {b : ℂ} (hb : |b.im| ≤ 1 / 2) :
    ‖Complex.sin (2 * (z : ℂ) * b)‖ ^ 2 ≤ (1 + 4 * b.re ^ 2) * Real.sinh z ^ 2 := by
  have harg : 2 * (z : ℂ) * b = ((2 * z * b.re : ℝ) : ℂ) + ((2 * z * b.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [harg, Complex.sin_add, Complex.sin_mul_I, Complex.cos_mul_I]
  set α : ℝ := 2 * z * b.re
  set β : ℝ := 2 * z * b.im
  have hnorm_sq :
      ‖Complex.sin (α : ℂ) * Complex.cosh (β : ℂ) +
        Complex.cos (α : ℂ) * (Complex.sinh (β : ℂ) * I)‖ ^ 2 =
      Real.sin α ^ 2 + Real.sinh β ^ 2 := by
    rw [← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_cos, ← Complex.ofReal_sinh]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im,
      mul_zero, mul_one, sub_zero, add_zero, zero_mul, zero_add]
    have hcs : Real.cos α ^ 2 = 1 - Real.sin α ^ 2 := by linarith [Real.sin_sq_add_cos_sq α]
    have hch : Real.cosh β ^ 2 = 1 + Real.sinh β ^ 2 := by linarith [Real.cosh_sq_sub_sinh_sq β]
    calc Real.sin α * Real.cosh β * (Real.sin α * Real.cosh β) +
          Real.cos α * Real.sinh β * (Real.cos α * Real.sinh β)
        = Real.sin α ^ 2 * Real.cosh β ^ 2 + Real.cos α ^ 2 * Real.sinh β ^ 2 := by ring
      _ = Real.sin α ^ 2 * (1 + Real.sinh β ^ 2) + (1 - Real.sin α ^ 2) * Real.sinh β ^ 2 := by
          rw [hch, hcs]
      _ = Real.sin α ^ 2 + Real.sinh β ^ 2 := by ring
  rw [hnorm_sq]
  have hsin_le : Real.sin α ^ 2 ≤ 4 * b.re ^ 2 * Real.sinh z ^ 2 := by
    have h1 : |Real.sin α| ≤ |α| := Real.abs_sin_le_abs
    have h2 : |α| = 2 * |b.re| * z := by
      dsimp [α]; rw [abs_mul, abs_mul, abs_two, abs_of_nonneg hz]; ring
    have h3 : |Real.sin α| ≤ 2 * |b.re| * Real.sinh z := by
      calc |Real.sin α| ≤ 2 * |b.re| * z := h2 ▸ h1
        _ ≤ 2 * |b.re| * Real.sinh z := mul_le_mul_of_nonneg_left (le_sinh_of_nonneg hz) (by positivity)
    have hsq : |Real.sin α| ^ 2 ≤ (2 * |b.re| * Real.sinh z) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h3 2
    rw [sq_abs] at hsq
    calc Real.sin α ^ 2 ≤ (2 * |b.re| * Real.sinh z) ^ 2 := hsq
      _ = 4 * |b.re| ^ 2 * Real.sinh z ^ 2 := by ring
      _ = 4 * b.re ^ 2 * Real.sinh z ^ 2 := by rw [sq_abs]
  have hsinh_le : Real.sinh β ^ 2 ≤ Real.sinh z ^ 2 := by
    have hβ_le : |β| ≤ z := by
      dsimp [β]; rw [abs_mul, abs_mul, abs_two, abs_of_nonneg hz]
      nlinarith
    have hsh : |Real.sinh β| ≤ Real.sinh z := by
      have habs_sh : |Real.sinh β| = Real.sinh |β| := by
        rcases le_total 0 β with h | h
        · rw [abs_of_nonneg h, abs_of_nonneg (Real.sinh_nonneg_iff.mpr h)]
        · rw [abs_of_nonpos h, Real.sinh_neg, abs_of_nonpos (Real.sinh_nonpos_iff.mpr h)]
      rw [habs_sh]
      exact Real.sinh_le_sinh.mpr hβ_le
    have hsq : |Real.sinh β| ^ 2 ≤ Real.sinh z ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hsh 2
    rwa [sq_abs] at hsq
  linarith

/-- Uniform 1D kernel bound (`spinning_foundations.tex`, proof of Lemma S2.2):
`|W_a(r; b)| ≤ (1 + 4 (Re b)²) V_1(r)` for `a ≥ 2`, `r ∈ ℝ`, `|Im b| ≤ 1/2`. -/
theorem norm_spinWa_le {a : ℝ} (ha : 2 ≤ a) (r : ℝ) {b : ℂ} (hb : |b.im| ≤ 1 / 2) :
    ‖spinWa a r b‖ ≤ (1 + 4 * b.re ^ 2) * spinV1 a r := by
  have habs : ‖spinWa a r b‖ = ‖spinWa a |r| b‖ ∧ spinV1 a r = spinV1 a |r| := by
    rcases le_total 0 r with hr | hr
    · rw [abs_of_nonneg hr]; exact ⟨rfl, rfl⟩
    · rw [abs_of_nonpos hr, spinWa_neg_r, spinV1_even]; exact ⟨rfl, rfl⟩
  rw [habs.1, habs.2]
  rw [spinWa_eq_mul_sin, spinV1_eq_mul_sinh]
  set u : ℝ := π * |r| * (Real.sqrt a + Real.sqrt (a - 2))
  set v : ℝ := π * |r| * (Real.sqrt a - Real.sqrt (a - 2))
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by
    dsimp [v]
    have : Real.sqrt (a - 2) ≤ Real.sqrt a := Real.sqrt_le_sqrt (by linarith)
    exact mul_nonneg (by positivity) (by linarith)
  have h1 := norm_sin_two_mul_sq_le hu hb
  have h2 := norm_sin_two_mul_sq_le hv hb
  have h1' : ‖Complex.sin (2 * (u : ℂ) * b)‖ ≤ Real.sqrt (1 + 4 * b.re ^ 2) * Real.sinh u := by
    have hnn : 0 ≤ Real.sqrt (1 + 4 * b.re ^ 2) * Real.sinh u :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sinh_nonneg_iff.mpr hu)
    rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hnn]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact h1
  have h2' : ‖Complex.sin (2 * (v : ℂ) * b)‖ ≤ Real.sqrt (1 + 4 * b.re ^ 2) * Real.sinh v := by
    have hnn : 0 ≤ Real.sqrt (1 + 4 * b.re ^ 2) * Real.sinh v :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sinh_nonneg_iff.mpr hv)
    rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hnn]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact h2
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_ofNat]
  have hprod := mul_le_mul h1' h2' (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sinh_nonneg_iff.mpr hu))
  have hsq : Real.sqrt (1 + 4 * b.re ^ 2) * Real.sqrt (1 + 4 * b.re ^ 2) = 1 + 4 * b.re ^ 2 :=
    Real.mul_self_sqrt (by positivity)
  calc 2 * ‖Complex.sin (2 * (u : ℂ) * b)‖ * ‖Complex.sin (2 * (v : ℂ) * b)‖
      = 2 * (‖Complex.sin (2 * (u : ℂ) * b)‖ * ‖Complex.sin (2 * (v : ℂ) * b)‖) := by ring
    _ ≤ 2 * ((Real.sqrt (1 + 4 * b.re ^ 2) * Real.sinh u) *
          (Real.sqrt (1 + 4 * b.re ^ 2) * Real.sinh v)) := by gcongr
    _ = (Real.sqrt (1 + 4 * b.re ^ 2) * Real.sqrt (1 + 4 * b.re ^ 2)) *
          (2 * Real.sinh u * Real.sinh v) := by ring
    _ = (1 + 4 * b.re ^ 2) * (2 * Real.sinh u * Real.sinh v) := by rw [hsq]

/-- Elementary bound `z * ‖cos(2 z b)‖ ≤ max (e) (4 / (1 - 2 θ)) * sinh z` for `z ≥ 0` and
`|Im b| ≤ θ < 1/2`. -/
private lemma mul_norm_cos_two_mul_le {z θ : ℝ} (hz : 0 ≤ z) (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2)
    {b : ℂ} (hb : |b.im| ≤ θ) :
    z * ‖Complex.cos (2 * (z : ℂ) * b)‖ ≤ max (Real.exp 1) (4 / (1 - 2 * θ)) * Real.sinh z := by
  have hcos_le : ‖Complex.cos (2 * (z : ℂ) * b)‖ ≤ Real.cosh (2 * z * b.im) := by
    have harg : 2 * (z : ℂ) * b = ((2 * z * b.re : ℝ) : ℂ) + ((2 * z * b.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [harg, Complex.cos_add, Complex.sin_mul_I, Complex.cos_mul_I]
    set α : ℝ := 2 * z * b.re
    set β : ℝ := 2 * z * b.im
    rw [← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_cos, ← Complex.ofReal_sinh]
    have hsq : ‖(Real.cos α : ℂ) * (Real.cosh β : ℂ) - (Real.sin α : ℂ) * ((Real.sinh β : ℂ) * I)‖ ^ 2 ≤
        Real.cosh β ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.sub_im, Complex.mul_im,
        mul_zero, mul_one, sub_zero, add_zero, zero_mul, zero_sub]
      have hsh : Real.sinh β ^ 2 ≤ Real.cosh β ^ 2 := by linarith [Real.cosh_sq_sub_sinh_sq β]
      have hsc : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
      calc Real.cos α * Real.cosh β * (Real.cos α * Real.cosh β) +
            -(Real.sin α * Real.sinh β) * -(Real.sin α * Real.sinh β)
          = Real.cos α ^ 2 * Real.cosh β ^ 2 + Real.sin α ^ 2 * Real.sinh β ^ 2 := by ring
        _ ≤ Real.cos α ^ 2 * Real.cosh β ^ 2 + Real.sin α ^ 2 * Real.cosh β ^ 2 := by gcongr
        _ = (Real.cos α ^ 2 + Real.sin α ^ 2) * Real.cosh β ^ 2 := by ring
        _ = Real.cosh β ^ 2 := by rw [hsc, one_mul]
    calc ‖(Real.cos α : ℂ) * (Real.cosh β : ℂ) - (Real.sin α : ℂ) * ((Real.sinh β : ℂ) * I)‖
        = Real.sqrt (‖(Real.cos α : ℂ) * (Real.cosh β : ℂ) - (Real.sin α : ℂ) * ((Real.sinh β : ℂ) * I)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (Real.cosh β ^ 2) := Real.sqrt_le_sqrt hsq
      _ = Real.cosh β := Real.sqrt_sq (Real.cosh_pos β).le
  have hcosh_le : Real.cosh (2 * z * b.im) ≤ Real.exp (2 * θ * z) := by
    have h1 : |2 * z * b.im| ≤ 2 * θ * z := by
      rw [abs_mul, abs_mul, abs_two, abs_of_nonneg hz]; nlinarith
    have h2 : Real.cosh (2 * z * b.im) ≤ Real.cosh (2 * θ * z) :=
      Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg (mul_nonneg (mul_nonneg zero_le_two hθ0) hz)]; exact h1)
    have h3 : Real.cosh (2 * θ * z) ≤ Real.exp (2 * θ * z) := by
      rw [Real.cosh_eq]
      have hneg : Real.exp (-(2 * θ * z)) ≤ Real.exp (2 * θ * z) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith
    exact h2.trans h3
  have hstep : z * ‖Complex.cos (2 * (z : ℂ) * b)‖ ≤ z * Real.exp (2 * θ * z) :=
    mul_le_mul_of_nonneg_left (hcos_le.trans hcosh_le) hz
  refine hstep.trans ?_
  by_cases hz1 : z ≤ 1
  · have hexp_le : Real.exp (2 * θ * z) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by nlinarith)
    calc z * Real.exp (2 * θ * z)
        ≤ Real.sinh z * Real.exp 1 :=
          mul_le_mul (le_sinh_of_nonneg hz) hexp_le (Real.exp_pos _).le (Real.sinh_nonneg_iff.mpr hz)
      _ = Real.exp 1 * Real.sinh z := mul_comm _ _
      _ ≤ max (Real.exp 1) (4 / (1 - 2 * θ)) * Real.sinh z :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sinh_nonneg_iff.mpr hz)
  · push Not at hz1
    have hδ : 0 < 1 - 2 * θ := by linarith
    have hz_exp : (1 - 2 * θ) * z ≤ Real.exp ((1 - 2 * θ) * z) := by
      linarith [Real.add_one_le_exp ((1 - 2 * θ) * z)]
    have hze : z * Real.exp (2 * θ * z) ≤ (1 - 2 * θ)⁻¹ * Real.exp z := by
      have hmul : (1 - 2 * θ) * (z * Real.exp (2 * θ * z)) ≤ Real.exp z := by
        calc (1 - 2 * θ) * (z * Real.exp (2 * θ * z))
            = ((1 - 2 * θ) * z) * Real.exp (2 * θ * z) := by ring
          _ ≤ Real.exp ((1 - 2 * θ) * z) * Real.exp (2 * θ * z) := by gcongr
          _ = Real.exp ((1 - 2 * θ) * z + 2 * θ * z) := (Real.exp_add _ _).symm
          _ = Real.exp z := by congr 1; ring
      calc z * Real.exp (2 * θ * z)
          = (1 - 2 * θ)⁻¹ * ((1 - 2 * θ) * (z * Real.exp (2 * θ * z))) := by
            field_simp [hδ.ne']
        _ ≤ (1 - 2 * θ)⁻¹ * Real.exp z := mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hδ.le)
    have hsh : (1 / 4 : ℝ) * Real.exp z ≤ Real.sinh z := by
      rw [Real.sinh_eq]
      have h2z : Real.exp (-z) ≤ (1 / 2 : ℝ) * Real.exp z := by
        have h1 : (2 : ℝ) ≤ Real.exp (2 * z) := by linarith [Real.add_one_le_exp (2 * z)]
        have h2 : Real.exp (-z) * Real.exp (2 * z) = Real.exp z := by
          rw [← Real.exp_add]; congr 1; ring
        nlinarith [Real.exp_pos (-z)]
      linarith
    calc z * Real.exp (2 * θ * z)
        ≤ (1 - 2 * θ)⁻¹ * Real.exp z := hze
      _ = (4 / (1 - 2 * θ)) * ((1 / 4 : ℝ) * Real.exp z) := by ring
      _ ≤ (4 / (1 - 2 * θ)) * Real.sinh z := mul_le_mul_of_nonneg_left hsh (by positivity)
      _ ≤ max (Real.exp 1) (4 / (1 - 2 * θ)) * Real.sinh z :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sinh_nonneg_iff.mpr hz)

/-- Derivative of `spinWa a r` with respect to `b`. -/
private lemma hasDerivAt_spinWa (a r : ℝ) (b : ℂ) :
    HasDerivAt (spinWa a r)
      (-4 * ((π * r * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) *
          Complex.cos (2 * ((π * r * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) * b) *
          Complex.sin (2 * ((π * r * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) * b) -
       4 * ((π * r * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) *
          Complex.sin (2 * ((π * r * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) * b) *
          Complex.cos (2 * ((π * r * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) * b)) b := by
  have heq : spinWa a r = fun z =>
      -2 * Complex.sin (2 * ((π * r * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) * z) *
        Complex.sin (2 * ((π * r * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) * z) :=
    funext (spinWa_eq_mul_sin a r)
  rw [heq]
  set U : ℂ := ((π * r * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ)
  set V : ℂ := ((π * r * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ)
  have h1 : HasDerivAt (fun z => Complex.sin (2 * U * z)) (Complex.cos (2 * U * b) * (2 * U)) b := by
    have h := (Complex.hasDerivAt_sin (2 * U * b)).comp b ((hasDerivAt_id b).const_mul (2 * U))
    simpa [Function.comp_def] using h
  have h2 : HasDerivAt (fun z => Complex.sin (2 * V * z)) (Complex.cos (2 * V * b) * (2 * V)) b := by
    have h := (Complex.hasDerivAt_sin (2 * V * b)).comp b ((hasDerivAt_id b).const_mul (2 * V))
    simpa [Function.comp_def] using h
  have hprod := (h1.const_mul (-2 : ℂ)).mul h2
  convert hprod using 1
  ring

/-- Uniform bound on `deriv (spinWa a r) b` on `{|Im b| ≤ θ}` (`0 ≤ θ < 1/2`), controlled by `V_1(r)`. -/
private lemma norm_deriv_spinWa_le {a θ : ℝ} (ha : 2 ≤ a) (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2)
    (r : ℝ) {b : ℂ} (hb : |b.im| ≤ θ) :
    ‖deriv (spinWa a r) b‖ ≤
      4 * max (Real.exp 1) (4 / (1 - 2 * θ)) * Real.sqrt (1 + 4 * b.re ^ 2) * spinV1 a r := by
  have hd := (hasDerivAt_spinWa a r b).deriv
  rw [hd]
  have habs_v1 : spinV1 a r = spinV1 a |r| := by
    rcases le_total 0 r with hr | hr
    · rw [abs_of_nonneg hr]
    · rw [abs_of_nonpos hr, spinV1_even]
  rw [habs_v1, spinV1_eq_mul_sinh]
  set u : ℝ := π * |r| * (Real.sqrt a + Real.sqrt (a - 2))
  set v : ℝ := π * |r| * (Real.sqrt a - Real.sqrt (a - 2))
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by
    dsimp [v]
    have : Real.sqrt (a - 2) ≤ Real.sqrt a := Real.sqrt_le_sqrt (by linarith)
    exact mul_nonneg (by positivity) (by linarith)
  have hb_half : |b.im| ≤ 1 / 2 := hb.trans hθ.le
  have hM : 0 ≤ max (Real.exp 1) (4 / (1 - 2 * θ)) := le_trans (Real.exp_pos 1).le (le_max_left _ _)
  -- Replace `r` with `|r|` in the norms of `sin` and `cos`.
  have hnorm_eq : ∀ (c : ℝ), 0 ≤ c →
      ‖((π * r * c : ℝ) : ℂ)‖ = π * |r| * c ∧
      ‖Complex.cos (2 * ((π * r * c : ℝ) : ℂ) * b)‖ = ‖Complex.cos (2 * ((π * |r| * c : ℝ) : ℂ) * b)‖ ∧
      ‖Complex.sin (2 * ((π * r * c : ℝ) : ℂ) * b)‖ = ‖Complex.sin (2 * ((π * |r| * c : ℝ) : ℂ) * b)‖ := by
    intro c hc
    refine ⟨?_, ?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg hc]
    · rcases le_total 0 r with hr | hr
      · rw [abs_of_nonneg hr]
      · rw [abs_of_nonpos hr]
        have : 2 * ((π * -r * c : ℝ) : ℂ) * b = -(2 * ((π * r * c : ℝ) : ℂ) * b) := by push_cast; ring
        rw [this, Complex.cos_neg]
    · rcases le_total 0 r with hr | hr
      · rw [abs_of_nonneg hr]
      · rw [abs_of_nonpos hr]
        have : 2 * ((π * -r * c : ℝ) : ℂ) * b = -(2 * ((π * r * c : ℝ) : ℂ) * b) := by push_cast; ring
        rw [this, Complex.sin_neg, norm_neg]
  have hcu : 0 ≤ Real.sqrt a + Real.sqrt (a - 2) := by positivity
  have hcv : 0 ≤ Real.sqrt a - Real.sqrt (a - 2) := by
    have : Real.sqrt (a - 2) ≤ Real.sqrt a := Real.sqrt_le_sqrt (by linarith); linarith
  obtain ⟨hu1, hu2, hu3⟩ := hnorm_eq _ hcu
  obtain ⟨hv1, hv2, hv3⟩ := hnorm_eq _ hcv
  have hsin_u : ‖Complex.sin (2 * (u : ℂ) * b)‖ ≤ Real.sqrt (1 + 4 * b.re ^ 2) * Real.sinh u := by
    have hnn : 0 ≤ Real.sqrt (1 + 4 * b.re ^ 2) * Real.sinh u :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sinh_nonneg_iff.mpr hu)
    rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hnn]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact norm_sin_two_mul_sq_le hu hb_half
  have hsin_v : ‖Complex.sin (2 * (v : ℂ) * b)‖ ≤ Real.sqrt (1 + 4 * b.re ^ 2) * Real.sinh v := by
    have hnn : 0 ≤ Real.sqrt (1 + 4 * b.re ^ 2) * Real.sinh v :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sinh_nonneg_iff.mpr hv)
    rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hnn]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact norm_sin_two_mul_sq_le hv hb_half
  have hcos_u := mul_norm_cos_two_mul_le hu hθ0 hθ hb
  have hcos_v := mul_norm_cos_two_mul_le hv hθ0 hθ hb
  have hterm1 : ‖-4 * ((π * r * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) *
      Complex.cos (2 * ((π * r * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) * b) *
      Complex.sin (2 * ((π * r * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) * b)‖ ≤
      4 * (max (Real.exp 1) (4 / (1 - 2 * θ)) * Real.sinh u) *
        (Real.sqrt (1 + 4 * b.re ^ 2) * Real.sinh v) := by
    rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat, hu1, hu2, hv3]
    have hprod := mul_le_mul hcos_u hsin_v (norm_nonneg _) (mul_nonneg hM (Real.sinh_nonneg_iff.mpr hu))
    calc 4 * u * ‖Complex.cos (2 * (u : ℂ) * b)‖ * ‖Complex.sin (2 * (v : ℂ) * b)‖
        = 4 * ((u * ‖Complex.cos (2 * (u : ℂ) * b)‖) * ‖Complex.sin (2 * (v : ℂ) * b)‖) := by ring
      _ ≤ 4 * ((max (Real.exp 1) (4 / (1 - 2 * θ)) * Real.sinh u) *
            (Real.sqrt (1 + 4 * b.re ^ 2) * Real.sinh v)) := by gcongr
      _ = 4 * (max (Real.exp 1) (4 / (1 - 2 * θ)) * Real.sinh u) *
            (Real.sqrt (1 + 4 * b.re ^ 2) * Real.sinh v) := by ring
  have hterm2 : ‖4 * ((π * r * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) *
      Complex.sin (2 * ((π * r * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) * b) *
      Complex.cos (2 * ((π * r * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) * b)‖ ≤
      4 * (max (Real.exp 1) (4 / (1 - 2 * θ)) * Real.sinh v) *
        (Real.sqrt (1 + 4 * b.re ^ 2) * Real.sinh u) := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, hv1, hu3, hv2]
    have hprod := mul_le_mul hcos_v hsin_u (norm_nonneg _) (mul_nonneg hM (Real.sinh_nonneg_iff.mpr hv))
    calc 4 * v * ‖Complex.sin (2 * (u : ℂ) * b)‖ * ‖Complex.cos (2 * (v : ℂ) * b)‖
        = 4 * ((v * ‖Complex.cos (2 * (v : ℂ) * b)‖) * ‖Complex.sin (2 * (u : ℂ) * b)‖) := by ring
      _ ≤ 4 * ((max (Real.exp 1) (4 / (1 - 2 * θ)) * Real.sinh v) *
            (Real.sqrt (1 + 4 * b.re ^ 2) * Real.sinh u)) := by gcongr
      _ = 4 * (max (Real.exp 1) (4 / (1 - 2 * θ)) * Real.sinh v) *
            (Real.sqrt (1 + 4 * b.re ^ 2) * Real.sinh u) := by ring
  calc ‖-4 * ((π * r * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) *
            Complex.cos (2 * ((π * r * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) * b) *
            Complex.sin (2 * ((π * r * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) * b) -
          4 * ((π * r * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) *
            Complex.sin (2 * ((π * r * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) * b) *
            Complex.cos (2 * ((π * r * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) * b)‖
      ≤ ‖-4 * ((π * r * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) *
            Complex.cos (2 * ((π * r * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) * b) *
            Complex.sin (2 * ((π * r * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) * b)‖ +
        ‖4 * ((π * r * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) *
            Complex.sin (2 * ((π * r * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) * b) *
            Complex.cos (2 * ((π * r * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) * b)‖ :=
        norm_sub_le _ _
    _ ≤ 4 * (max (Real.exp 1) (4 / (1 - 2 * θ)) * Real.sinh u) *
          (Real.sqrt (1 + 4 * b.re ^ 2) * Real.sinh v) +
        4 * (max (Real.exp 1) (4 / (1 - 2 * θ)) * Real.sinh v) *
          (Real.sqrt (1 + 4 * b.re ^ 2) * Real.sinh u) := add_le_add hterm1 hterm2
    _ = 4 * max (Real.exp 1) (4 / (1 - 2 * θ)) * Real.sqrt (1 + 4 * b.re ^ 2) *
          (2 * Real.sinh u * Real.sinh v) := by ring

/-! ### Section 2: Uniform bistrip bound and separate holomorphy of `spinDaC` -/

lemma spinDaC_eq_spinWa (a : ℝ) (Φ : ℝ × ℝ → ℝ) (bL bR : ℂ) :
    spinDaC a Φ bL bR = -(∫ p : ℝ × ℝ, (Φ p : ℂ) * spinWa a p.1 bL * spinWa a p.2 bR) := rfl

/-- **Uniform bistrip bound** (`spinnotes:stripbound`, Lemma S2.2):
`|(D_a G)(b_L, b_R)| ≤ (1 + 4 (Re b_L)²)(1 + 4 (Re b_R)²) M_2[Φ]` for `|Im b_L|, |Im b_R| ≤ 1/2`. -/
theorem norm_spinDaC_le {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ)
    {bL bR : ℂ} (hbL : |bL.im| ≤ 1 / 2) (hbR : |bR.im| ≤ 1 / 2) :
    ‖spinDaC a Φ bL bR‖ ≤ (1 + 4 * bL.re ^ 2) * (1 + 4 * bR.re ^ 2) * spinM2 a Φ := by
  rw [spinDaC_eq_spinWa, norm_neg]
  have hdom : ∀ p : ℝ × ℝ,
      ‖(Φ p : ℂ) * spinWa a p.1 bL * spinWa a p.2 bR‖ ≤
        (1 + 4 * bL.re ^ 2) * (1 + 4 * bR.re ^ 2) * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by
    intro p
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := norm_spinWa_le ha p.1 hbL
    have h2 := norm_spinWa_le ha p.2 hbR
    have hprod := mul_le_mul h1 h2 (norm_nonneg _)
      (mul_nonneg (by positivity) (spinV1_nonneg ha p.1))
    calc |Φ p| * ‖spinWa a p.1 bL‖ * ‖spinWa a p.2 bR‖
        = |Φ p| * (‖spinWa a p.1 bL‖ * ‖spinWa a p.2 bR‖) := by ring
      _ ≤ |Φ p| * (((1 + 4 * bL.re ^ 2) * spinV1 a p.1) *
            ((1 + 4 * bR.re ^ 2) * spinV1 a p.2)) :=
          mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
      _ = (1 + 4 * bL.re ^ 2) * (1 + 4 * bR.re ^ 2) * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by
          ring
  have hint_norm : Integrable (fun p : ℝ × ℝ => ‖(Φ p : ℂ) * spinWa a p.1 bL * spinWa a p.2 bR‖) := by
    refine (hΦ.int_M2.const_mul ((1 + 4 * bL.re ^ 2) * (1 + 4 * bR.re ^ 2))).mono' ?_
      (Eventually.of_forall fun p => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hdom p)
    have hc1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
    have hc2 : Continuous (fun p : ℝ × ℝ => spinWa a p.1 bL) := by unfold spinWa; fun_prop
    have hc3 : Continuous (fun p : ℝ × ℝ => spinWa a p.2 bR) := by unfold spinWa; fun_prop
    exact ((hc1.mul hc2).mul hc3).norm.aestronglyMeasurable
  calc ‖∫ p : ℝ × ℝ, (Φ p : ℂ) * spinWa a p.1 bL * spinWa a p.2 bR‖
      ≤ ∫ p : ℝ × ℝ, ‖(Φ p : ℂ) * spinWa a p.1 bL * spinWa a p.2 bR‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ p : ℝ × ℝ, (1 + 4 * bL.re ^ 2) * (1 + 4 * bR.re ^ 2) *
          (|Φ p| * spinV1 a p.1 * spinV1 a p.2) :=
        integral_mono hint_norm (hΦ.int_M2.const_mul _) hdom
    _ = (1 + 4 * bL.re ^ 2) * (1 + 4 * bR.re ^ 2) * spinM2 a Φ :=
        integral_const_mul _ _

/-- Holomorphy of `spinDaC a Φ` in the first variable on `\mathcal S_{1/2}` (with `bR ∈ \mathcal S_{1/2}`). -/
theorem differentiableOn_spinDaC_left {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) {bR : ℂ} (hbR : bR ∈ spinStrip (1 / 2)) :
    DifferentiableOn ℂ (fun bL => spinDaC a Φ bL bR) (spinStrip (1 / 2)) := by
  intro b₀ hb₀
  have hε_pos : 0 < (1 / 2 - |b₀.im|) / 2 := by
    have : |b₀.im| < 1 / 2 := hb₀; linarith
  set ε : ℝ := (1 / 2 - |b₀.im|) / 2
  set θ : ℝ := |b₀.im| + ε
  have hθ0 : 0 ≤ θ := by dsimp [θ]; positivity
  have hθ_lt : θ < 1 / 2 := by dsimp [θ, ε]; have : |b₀.im| < 1 / 2 := hb₀; linarith
  have hbR_le : |bR.im| ≤ 1 / 2 := le_of_lt hbR
  let F : ℂ → ℝ × ℝ → ℂ := fun b p => (Φ p : ℂ) * spinWa a p.1 b * spinWa a p.2 bR
  let F' : ℂ → ℝ × ℝ → ℂ := fun b p => (Φ p : ℂ) * deriv (spinWa a p.1) b * spinWa a p.2 bR
  let R_re : ℝ := |b₀.re| + ε
  let C_bd : ℝ := 4 * max (Real.exp 1) (4 / (1 - 2 * θ)) * Real.sqrt (1 + 4 * R_re ^ 2) *
    (1 + 4 * bR.re ^ 2)
  let bound : ℝ × ℝ → ℝ := fun p => C_bd * (|Φ p| * spinV1 a p.1 * spinV1 a p.2)
  have hball_im : ∀ b ∈ Metric.ball b₀ ε, |b.im| ≤ θ := by
    intro b hb
    have h1 : |b.im - b₀.im| ≤ ‖b - b₀‖ := by
      rw [← Complex.sub_im]; exact Complex.abs_im_le_norm (b - b₀)
    have h2 : ‖b - b₀‖ < ε := by simpa [dist_eq_norm] using Metric.mem_ball.mp hb
    have h3 : |b.im| - |b₀.im| ≤ |b.im - b₀.im| := abs_sub_abs_le_abs_sub b.im b₀.im
    linarith
  have hball_re : ∀ b ∈ Metric.ball b₀ ε, |b.re| ≤ R_re := by
    intro b hb
    have h1 : |b.re - b₀.re| ≤ ‖b - b₀‖ := by
      rw [← Complex.sub_re]; exact Complex.abs_re_le_norm (b - b₀)
    have h2 : ‖b - b₀‖ < ε := by simpa [dist_eq_norm] using Metric.mem_ball.mp hb
    have h3 : |b.re| - |b₀.re| ≤ |b.re - b₀.re| := abs_sub_abs_le_abs_sub b.re b₀.re
    linarith
  have hF_meas : ∀ᶠ b in 𝓝 b₀, AEStronglyMeasurable (F b) volume :=
    Eventually.of_forall fun b => by
      have hc1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
      have hc2 : Continuous (fun p : ℝ × ℝ => spinWa a p.1 b) := by unfold spinWa; fun_prop
      have hc3 : Continuous (fun p : ℝ × ℝ => spinWa a p.2 bR) := by unfold spinWa; fun_prop
      exact ((hc1.mul hc2).mul hc3).aestronglyMeasurable
  have hF_int : Integrable (F b₀) volume := by
    refine (hΦ.int_M2.const_mul ((1 + 4 * b₀.re ^ 2) * (1 + 4 * bR.re ^ 2))).mono'
      (hF_meas.self_of_nhds) (Eventually.of_forall fun p => ?_)
    dsimp [F]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := norm_spinWa_le ha p.1 (le_of_lt hb₀)
    have h2 := norm_spinWa_le ha p.2 hbR_le
    have hprod := mul_le_mul h1 h2 (norm_nonneg _)
      (mul_nonneg (by positivity) (spinV1_nonneg ha p.1))
    calc |Φ p| * ‖spinWa a p.1 b₀‖ * ‖spinWa a p.2 bR‖
        = |Φ p| * (‖spinWa a p.1 b₀‖ * ‖spinWa a p.2 bR‖) := by ring
      _ ≤ |Φ p| * (((1 + 4 * b₀.re ^ 2) * spinV1 a p.1) *
            ((1 + 4 * bR.re ^ 2) * spinV1 a p.2)) :=
          mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
      _ = (1 + 4 * b₀.re ^ 2) * (1 + 4 * bR.re ^ 2) * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by
          ring
  have hF'_meas : AEStronglyMeasurable (F' b₀) volume := by
    have heq : F' b₀ = fun p : ℝ × ℝ =>
        (Φ p : ℂ) *
          (-4 * ((π * p.1 * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) *
              Complex.cos (2 * ((π * p.1 * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) * b₀) *
              Complex.sin (2 * ((π * p.1 * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) * b₀) -
           4 * ((π * p.1 * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) *
              Complex.sin (2 * ((π * p.1 * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) * b₀) *
              Complex.cos (2 * ((π * p.1 * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) * b₀)) *
          spinWa a p.2 bR := by
      ext p; dsimp [F']; rw [(hasDerivAt_spinWa a p.1 b₀).deriv]
    rw [heq]
    have hc1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
    have hc3 : Continuous (fun p : ℝ × ℝ => spinWa a p.2 bR) := by unfold spinWa; fun_prop
    have hc2 : Continuous (fun p : ℝ × ℝ =>
        -4 * ((π * p.1 * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) *
            Complex.cos (2 * ((π * p.1 * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) * b₀) *
            Complex.sin (2 * ((π * p.1 * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) * b₀) -
         4 * ((π * p.1 * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) *
            Complex.sin (2 * ((π * p.1 * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) * b₀) *
            Complex.cos (2 * ((π * p.1 * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) * b₀)) := by
      fun_prop
    exact ((hc1.mul hc2).mul hc3).aestronglyMeasurable
  have hbound_int : Integrable bound volume := hΦ.int_M2.const_mul C_bd
  have hbound_le : ∀ᵐ p : ℝ × ℝ ∂volume, ∀ b ∈ Metric.ball b₀ ε, ‖F' b p‖ ≤ bound p := by
    refine Eventually.of_forall fun p b hb => ?_
    dsimp [F', bound, C_bd]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hd1 := norm_deriv_spinWa_le ha hθ0 hθ_lt p.1 (hball_im b hb)
    have hre_sq : b.re ^ 2 ≤ R_re ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) (hball_re b hb) 2
      rwa [sq_abs] at h
    have hsq_le : Real.sqrt (1 + 4 * b.re ^ 2) ≤ Real.sqrt (1 + 4 * R_re ^ 2) :=
      Real.sqrt_le_sqrt (by linarith)
    have hM_nn : 0 ≤ max (Real.exp 1) (4 / (1 - 2 * θ)) := le_trans (Real.exp_pos 1).le (le_max_left _ _)
    have hd1' : ‖deriv (spinWa a p.1) b‖ ≤
        4 * max (Real.exp 1) (4 / (1 - 2 * θ)) * Real.sqrt (1 + 4 * R_re ^ 2) * spinV1 a p.1 := by
      refine hd1.trans ?_
      have hv1 := spinV1_nonneg ha p.1
      gcongr
    have h2 := norm_spinWa_le ha p.2 hbR_le
    have hprod := mul_le_mul hd1' h2 (norm_nonneg _)
      (mul_nonneg (by positivity) (spinV1_nonneg ha p.1))
    calc |Φ p| * ‖deriv (spinWa a p.1) b‖ * ‖spinWa a p.2 bR‖
        = |Φ p| * (‖deriv (spinWa a p.1) b‖ * ‖spinWa a p.2 bR‖) := by ring
      _ ≤ |Φ p| * ((4 * max (Real.exp 1) (4 / (1 - 2 * θ)) * Real.sqrt (1 + 4 * R_re ^ 2) * spinV1 a p.1) *
            ((1 + 4 * bR.re ^ 2) * spinV1 a p.2)) :=
          mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
      _ = 4 * max (Real.exp 1) (4 / (1 - 2 * θ)) * Real.sqrt (1 + 4 * R_re ^ 2) *
            (1 + 4 * bR.re ^ 2) * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by ring
  have hderiv_pt : ∀ᵐ p : ℝ × ℝ ∂volume, ∀ b ∈ Metric.ball b₀ ε,
      HasDerivAt (fun b => F b p) (F' b p) b := by
    refine Eventually.of_forall fun p b _ => ?_
    have hwa := hasDerivAt_spinWa a p.1 b
    rw [← hwa.deriv] at hwa
    have h1 := (hwa.const_mul (Φ p : ℂ)).mul_const (spinWa a p.2 bR)
    simpa [F, F'] using h1
  have hres := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds b₀ hε_pos)
    hF_meas hF_int hF'_meas hbound_le hbound_int hderiv_pt).2
  have hneg : HasDerivAt (fun bL => spinDaC a Φ bL bR) (-(∫ p : ℝ × ℝ, F' b₀ p)) b₀ := by
    have hfun : (fun bL => spinDaC a Φ bL bR) = fun bL => -(∫ p : ℝ × ℝ, F bL p) := rfl
    rw [hfun]
    exact hres.neg
  exact hneg.differentiableAt.differentiableWithinAt

/-- Holomorphy of `spinDaC a Φ` in the second variable on `\mathcal S_{1/2}` (by `D_4` swap symmetry). -/
theorem differentiableOn_spinDaC_right {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) {bL : ℂ} (hbL : bL ∈ spinStrip (1 / 2)) :
    DifferentiableOn ℂ (fun bR => spinDaC a Φ bL bR) (spinStrip (1 / 2)) := by
  have hswap : ∀ bR : ℂ, spinDaC a Φ bL bR = spinDaC a Φ bR bL := by
    intro bR
    rw [spinDaC_eq_spinWa, spinDaC_eq_spinWa]
    congr 1
    let e : ℝ × ℝ ≃ᵐ ℝ × ℝ := MeasurableEquiv.prodComm
    have hmp : Measure.map e (volume : Measure (ℝ × ℝ)) = volume := by
      rw [Measure.volume_eq_prod]
      exact Measure.prod_swap
    have h1 : ∫ p : ℝ × ℝ, (Φ (e p) : ℂ) * spinWa a (e p).1 bL * spinWa a (e p).2 bR =
        ∫ p : ℝ × ℝ, (Φ p : ℂ) * spinWa a p.1 bL * spinWa a p.2 bR := by
      have h := integral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) e
        (fun p : ℝ × ℝ => (Φ p : ℂ) * spinWa a p.1 bL * spinWa a p.2 bR)
      rw [hmp] at h
      exact h.symm
    rw [← h1]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    change (Φ (p.2, p.1) : ℂ) * spinWa a p.2 bL * spinWa a p.1 bR =
      (Φ p : ℂ) * spinWa a p.1 bR * spinWa a p.2 bL
    rw [hΦ.d4_inv.2.2 p.1 p.2]; ring
  have hfun : (fun bR => spinDaC a Φ bL bR) = fun bR => spinDaC a Φ bR bL := funext hswap
  rw [hfun]
  exact differentiableOn_spinDaC_left ha hΦ hbL

/-! ### Section 3: Cosine integral representation and agreement on `ℝ²` -/

/-- Cosine integral representation of `spinG a Φ` on `ℝ²` from Fourier oddness and `D_4` symmetry. -/
theorem spinG_eq_cosine_integral {a : ℝ} (_ha : 0 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) (xL xR : ℝ) :
    ((spinG a Φ xL xR : ℝ) : ℂ) =
      -(∫ p : ℝ × ℝ, (Φ p : ℂ) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (xL : ℂ)) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (xR : ℂ))) := by
  let w : EuclideanSpace ℝ (Fin 2) := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![2 * Real.sqrt a * xL, 2 * Real.sqrt a * xR]
  have hfo := congrFun hΦ.fourier_odd w
  simp only [Real.fourier_eq, Pi.neg_apply, spinToEuc] at hfo
  have hw0 : w 0 = 2 * Real.sqrt a * xL := rfl
  have hw1 : w 1 = 2 * Real.sqrt a * xR := rfl
  rw [hw0, hw1] at hfo
  let e : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))
  have hmpe : Measure.map e (volume : Measure (EuclideanSpace ℝ (Fin 2))) = volume :=
    ((volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).comp (PiLp.volume_preserving_ofLp (Fin 2))).map_eq
  have hI_eq : ∫ v : EuclideanSpace ℝ (Fin 2), 𝐞 (-⟪v, w⟫) • ((Φ (v 0, v 1) : ℝ) : ℂ) =
      ∫ p : ℝ × ℝ, Complex.exp (-2 * π * I * ((p.1 : ℂ) * (2 * (Real.sqrt a : ℂ) * (xL : ℂ)) +
        (p.2 : ℂ) * (2 * (Real.sqrt a : ℂ) * (xR : ℂ)))) * (Φ p : ℂ) := by
    have h1 := integral_map_equiv (μ := (volume : Measure (EuclideanSpace ℝ (Fin 2)))) e
      (fun p : ℝ × ℝ =>
        Complex.exp (-2 * π * I * ((p.1 : ℂ) * (2 * (Real.sqrt a : ℂ) * (xL : ℂ)) +
          (p.2 : ℂ) * (2 * (Real.sqrt a : ℂ) * (xR : ℂ)))) * (Φ p : ℂ))
    rw [hmpe] at h1
    rw [h1]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    dsimp only
    have hev : e v = (v 0, v 1) := rfl
    rw [hev, Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
    congr 1
    have hinner : ⟪v, w⟫ = v 0 * (2 * Real.sqrt a * xL) + v 1 * (2 * Real.sqrt a * xR) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
      simp [hw0, hw1, mul_comm]
    rw [hinner]
    congr 1; push_cast; ring
  rw [hI_eq] at hfo
  -- Now average over the 4 sign changes `(±p.1, ±p.2)` using `D_4` evenness of `Φ`.
  let f : ℝ × ℝ → ℂ := fun p =>
    Complex.exp (-2 * π * I * ((p.1 : ℂ) * (2 * (Real.sqrt a : ℂ) * (xL : ℂ)) +
      (p.2 : ℂ) * (2 * (Real.sqrt a : ℂ) * (xR : ℂ)))) * (Φ p : ℂ)
  have hf_int : Integrable f volume := by
    refine (hΦ.int.norm).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have h1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
      have h2 : Continuous (fun p : ℝ × ℝ => Complex.exp (-2 * π * I *
          ((p.1 : ℂ) * (2 * (Real.sqrt a : ℂ) * (xL : ℂ)) +
           (p.2 : ℂ) * (2 * (Real.sqrt a : ℂ) * (xR : ℂ))))) := by fun_prop
      exact (h2.mul h1).aestronglyMeasurable
    · dsimp [f]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hre : (-2 * π * I * ((p.1 : ℂ) * (2 * (Real.sqrt a : ℂ) * (xL : ℂ)) +
          (p.2 : ℂ) * (2 * (Real.sqrt a : ℂ) * (xR : ℂ)))).re = 0 := by
        simp [Complex.mul_re, Complex.add_re, Complex.I_re, Complex.I_im]
      rw [Complex.norm_exp, hre, Real.exp_zero, one_mul]
  have href1 : ∫ p : ℝ × ℝ, f (-p.1, p.2) = ∫ p : ℝ × ℝ, f p := by
    let e1 : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ)
    have hmp1 : Measure.map e1 (volume : Measure (ℝ × ℝ)) = volume := by
      have he : (e1 : ℝ × ℝ → ℝ × ℝ) = Prod.map (-·) id := rfl
      rw [he, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ measurable_neg measurable_id,
        Measure.map_neg_eq_self, Measure.map_id]
    have h := integral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) e1 f
    rw [hmp1] at h; exact h.symm
  have href2 : ∫ p : ℝ × ℝ, f (p.1, -p.2) = ∫ p : ℝ × ℝ, f p := by
    let e2 : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ)
    have hmp2' : Measure.map e2 (volume : Measure (ℝ × ℝ)) = volume := by
      have he : (e2 : ℝ × ℝ → ℝ × ℝ) = Prod.map id (-·) := rfl
      rw [he, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ measurable_id measurable_neg,
        Measure.map_id, Measure.map_neg_eq_self]
    have h := integral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) e2 f
    rw [hmp2'] at h; exact h.symm
  have href3 : ∫ p : ℝ × ℝ, f (-p.1, -p.2) = ∫ p : ℝ × ℝ, f p := by
    let e3 : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.neg ℝ)
    have hmp3 : Measure.map e3 (volume : Measure (ℝ × ℝ)) = volume := by
      have he : (e3 : ℝ × ℝ → ℝ × ℝ) = Prod.map (-·) (-·) := rfl
      rw [he, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ measurable_neg measurable_neg,
        Measure.map_neg_eq_self]
    have h := integral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) e3 f
    rw [hmp3] at h; exact h.symm
  have hint1 : Integrable (fun p : ℝ × ℝ => f (-p.1, p.2)) volume := by
    let e1 : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ)
    have hmp1 : MeasurePreserving e1 (volume : Measure (ℝ × ℝ)) volume := by
      refine ⟨e1.measurable, ?_⟩
      have he : (e1 : ℝ × ℝ → ℝ × ℝ) = Prod.map (-·) id := rfl
      rw [he, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ measurable_neg measurable_id,
        Measure.map_neg_eq_self, Measure.map_id]
    exact (hmp1.integrable_comp_emb e1.measurableEmbedding).mpr hf_int
  have hint2 : Integrable (fun p : ℝ × ℝ => f (p.1, -p.2)) volume := by
    let e2 : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ)
    have hmp2' : MeasurePreserving e2 (volume : Measure (ℝ × ℝ)) volume := by
      refine ⟨e2.measurable, ?_⟩
      have he : (e2 : ℝ × ℝ → ℝ × ℝ) = Prod.map id (-·) := rfl
      rw [he, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ measurable_id measurable_neg,
        Measure.map_id, Measure.map_neg_eq_self]
    exact (hmp2'.integrable_comp_emb e2.measurableEmbedding).mpr hf_int
  have hint3 : Integrable (fun p : ℝ × ℝ => f (-p.1, -p.2)) volume := by
    let e3 : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.neg ℝ)
    have hmp3 : MeasurePreserving e3 (volume : Measure (ℝ × ℝ)) volume := by
      refine ⟨e3.measurable, ?_⟩
      have he : (e3 : ℝ × ℝ → ℝ × ℝ) = Prod.map (-·) (-·) := rfl
      rw [he, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ measurable_neg measurable_neg,
        Measure.map_neg_eq_self]
    exact (hmp3.integrable_comp_emb e3.measurableEmbedding).mpr hf_int
  have havg : ∫ p : ℝ × ℝ, f p =
      ∫ p : ℝ × ℝ, (Φ p : ℂ) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (xL : ℂ)) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (xR : ℂ)) := by
    have h4 : (4 : ℂ) * ∫ p : ℝ × ℝ, f p =
        ∫ p : ℝ × ℝ, (f p + f (-p.1, p.2) + f (p.1, -p.2) + f (-p.1, -p.2)) := by
      have hint12 : Integrable (fun p : ℝ × ℝ => f p + f (-p.1, p.2)) volume := hf_int.add hint1
      have hint123 : Integrable (fun p : ℝ × ℝ => f p + f (-p.1, p.2) + f (p.1, -p.2)) volume :=
        hint12.add hint2
      rw [integral_add hint123 hint3, integral_add hint12 hint2, integral_add hf_int hint1,
        href1, href2, href3]
      ring
    have hpt : ∀ p : ℝ × ℝ,
        f p + f (-p.1, p.2) + f (p.1, -p.2) + f (-p.1, -p.2) =
          (4 : ℂ) * ((Φ p : ℂ) *
            Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (xL : ℂ)) *
            Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (xR : ℂ))) := by
      intro p
      dsimp [f]
      have hd1 : Φ (-p.1, p.2) = Φ p := hΦ.d4_inv.1 p.1 p.2
      have hd2 : Φ (p.1, -p.2) = Φ p := hΦ.d4_inv.2.1 p.1 p.2
      have hd3 : Φ (-p.1, -p.2) = Φ p := (hΦ.d4_inv.1 p.1 (-p.2)).trans (hΦ.d4_inv.2.1 p.1 p.2)
      rw [hd1, hd2, hd3]
      set A : ℂ := 4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (xL : ℂ)
      set B : ℂ := 4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (xR : ℂ)
      have he1 : -2 * π * I * ((p.1 : ℂ) * (2 * (Real.sqrt a : ℂ) * (xL : ℂ)) +
          (p.2 : ℂ) * (2 * (Real.sqrt a : ℂ) * (xR : ℂ))) = (-A) * I + (-B) * I := by
        dsimp [A, B]; ring
      have he2 : -2 * π * I * (((-p.1 : ℝ) : ℂ) * (2 * (Real.sqrt a : ℂ) * (xL : ℂ)) +
          (p.2 : ℂ) * (2 * (Real.sqrt a : ℂ) * (xR : ℂ))) = A * I + (-B) * I := by
        dsimp [A, B]; push_cast; ring
      have he3 : -2 * π * I * ((p.1 : ℂ) * (2 * (Real.sqrt a : ℂ) * (xL : ℂ)) +
          ((-p.2 : ℝ) : ℂ) * (2 * (Real.sqrt a : ℂ) * (xR : ℂ))) = (-A) * I + B * I := by
        dsimp [A, B]; push_cast; ring
      have he4 : -2 * π * I * (((-p.1 : ℝ) : ℂ) * (2 * (Real.sqrt a : ℂ) * (xL : ℂ)) +
          ((-p.2 : ℝ) : ℂ) * (2 * (Real.sqrt a : ℂ) * (xR : ℂ))) = A * I + B * I := by
        dsimp [A, B]; push_cast; ring
      rw [he1, he2, he3, he4, Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_add,
        Complex.cos, Complex.cos]
      ring
    have h4' : (4 : ℂ) * ∫ p : ℝ × ℝ, f p =
        (4 : ℂ) * ∫ p : ℝ × ℝ, (Φ p : ℂ) *
          Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (xL : ℂ)) *
          Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (xR : ℂ)) := by
      rw [h4, ← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall hpt)
    exact mul_left_cancel₀ (by norm_num : (4 : ℂ) ≠ 0) h4'
  have hG : ((spinG a Φ xL xR : ℝ) : ℂ) = -(∫ p : ℝ × ℝ, f p) := by
    unfold spinG
    have : ∫ p : ℝ × ℝ, f p = -((Φ (2 * Real.sqrt a * xL, 2 * Real.sqrt a * xR) : ℝ) : ℂ) := hfo
    rw [this, neg_neg]
  rw [hG, havg]

/-- Real agreement: `spinDaC a Φ (xL : ℂ) (xR : ℂ) = ((spinDa a Φ xL xR : ℝ) : ℂ)` for `a ≥ 2`. -/
theorem spinDaC_eq_spinDa {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) (xL xR : ℝ) :
    spinDaC a Φ (xL : ℂ) (xR : ℂ) = ((spinDa a Φ xL xR : ℝ) : ℂ) := by
  have ha0 : 0 ≤ a := by linarith
  have hg_mul : Real.sqrt a * spinGamma a = Real.sqrt (a - 2) := by
    unfold spinGamma
    rw [← Real.sqrt_mul ha0]
    congr 1; field_simp [(by linarith : a ≠ 0)]
  have hint_cos : ∀ u v : ℝ, Integrable (fun p : ℝ × ℝ =>
      (Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (u : ℂ)) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (v : ℂ))) volume := by
    intro u v
    refine (hΦ.int.norm).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have h1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
      have h2 : Continuous (fun p : ℝ × ℝ =>
          Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (u : ℂ))) := by fun_prop
      have h3 : Continuous (fun p : ℝ × ℝ =>
          Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (v : ℂ))) := by fun_prop
      exact ((h1.mul h2).mul h3).aestronglyMeasurable
    · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hc1 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (u : ℂ))‖ ≤ 1 := by
        have : 4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (u : ℂ) =
            ((4 * π * Real.sqrt a * p.1 * u : ℝ) : ℂ) := by push_cast; ring
        rw [this, ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
        exact Real.abs_cos_le_one _
      have hc2 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (v : ℂ))‖ ≤ 1 := by
        have : 4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (v : ℂ) =
            ((4 * π * Real.sqrt a * p.2 * v : ℝ) : ℂ) := by push_cast; ring
        rw [this, ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
        exact Real.abs_cos_le_one _
      calc |Φ p| * ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (u : ℂ))‖ *
            ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (v : ℂ))‖
          ≤ |Φ p| * 1 * 1 := by gcongr
        _ = |Φ p| := by ring
  unfold spinDa
  push_cast
  rw [spinG_eq_cosine_integral ha0 hΦ xL xR,
    spinG_eq_cosine_integral ha0 hΦ (spinGamma a * xL) xR,
    spinG_eq_cosine_integral ha0 hΦ xL (spinGamma a * xR),
    spinG_eq_cosine_integral ha0 hΦ (spinGamma a * xL) (spinGamma a * xR)]
  have hcomb :
      -(∫ p : ℝ × ℝ, (Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (xL : ℂ)) *
          Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (xR : ℂ))) -
      -(∫ p : ℝ × ℝ, (Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * ((spinGamma a * xL : ℝ) : ℂ)) *
          Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (xR : ℂ))) -
      -(∫ p : ℝ × ℝ, (Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (xL : ℂ)) *
          Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * ((spinGamma a * xR : ℝ) : ℂ))) +
      -(∫ p : ℝ × ℝ, (Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * ((spinGamma a * xL : ℝ) : ℂ)) *
          Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * ((spinGamma a * xR : ℝ) : ℂ))) =
      -(∫ p : ℝ × ℝ,
          ((Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (xL : ℂ)) *
            Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (xR : ℂ)) -
           (Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * ((spinGamma a * xL : ℝ) : ℂ)) *
            Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (xR : ℂ)) -
           (Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (xL : ℂ)) *
            Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * ((spinGamma a * xR : ℝ) : ℂ)) +
           (Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * ((spinGamma a * xL : ℝ) : ℂ)) *
            Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * ((spinGamma a * xR : ℝ) : ℂ)))) := by
    let g1 : ℝ × ℝ → ℂ := fun p => (Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (xL : ℂ)) *
      Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (xR : ℂ))
    let g2 : ℝ × ℝ → ℂ := fun p => (Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * ((spinGamma a * xL : ℝ) : ℂ)) *
      Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (xR : ℂ))
    let g3 : ℝ × ℝ → ℂ := fun p => (Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (xL : ℂ)) *
      Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * ((spinGamma a * xR : ℝ) : ℂ))
    let g4 : ℝ × ℝ → ℂ := fun p => (Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * ((spinGamma a * xL : ℝ) : ℂ)) *
      Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * ((spinGamma a * xR : ℝ) : ℂ))
    have h12 : Integrable (fun p => g1 p - g2 p) volume := (hint_cos _ _).sub (hint_cos _ _)
    have h123 : Integrable (fun p => g1 p - g2 p - g3 p) volume := h12.sub (hint_cos _ _)
    change -(∫ p, g1 p) - -(∫ p, g2 p) - -(∫ p, g3 p) + -(∫ p, g4 p) =
      -(∫ p, (g1 p - g2 p - g3 p + g4 p))
    rw [integral_add h123 (hint_cos _ _), integral_sub h12 (hint_cos _ _),
      integral_sub (hint_cos _ _) (hint_cos _ _)]
    ring
  rw [hcomb, spinDaC_eq_spinWa]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp only
  have h1 : 4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * ((spinGamma a * xL : ℝ) : ℂ) =
      4 * π * (Real.sqrt (a - 2) : ℂ) * (p.1 : ℂ) * (xL : ℂ) := by
    rw [← hg_mul]; push_cast; ring
  have h2 : 4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * ((spinGamma a * xR : ℝ) : ℂ) =
      4 * π * (Real.sqrt (a - 2) : ℂ) * (p.2 : ℂ) * (xR : ℂ) := by
    rw [← hg_mul]; push_cast; ring
  unfold spinWa
  rw [h1, h2]
  ring

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.norm_spinWa_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.norm_spinWa_le

/-- info: 'FormalResearch.ModularBootstrap.Spin.norm_spinDaC_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.norm_spinDaC_le

/-- info: 'FormalResearch.ModularBootstrap.Spin.differentiableOn_spinDaC_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.differentiableOn_spinDaC_left

/-- info: 'FormalResearch.ModularBootstrap.Spin.differentiableOn_spinDaC_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.differentiableOn_spinDaC_right

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinG_eq_cosine_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinG_eq_cosine_integral

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinDaC_eq_spinDa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinDaC_eq_spinDa

end FormalResearch.ModularBootstrap.Spin
