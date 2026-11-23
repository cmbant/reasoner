module

public import FormalResearch.ModularBootstrap.StripMultiplier.EdgeKernel
public import FormalResearch.ModularBootstrap.FixedWeightBand.LemmaS4W

/-!
# Kernel Factorization at Weight `w` (Lemma J4.2, `vlo:J42`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J4, Lemma J4.2 (`vlo:J42`).

For `prob : FixedWeightProblem` (weight `w = prob.w ≥ 1`, any `Q`), `V = prob.cardyV (c'/12)`,
`z = w/2 + c' ω(iτ)`, `t = c' x²/3`:

* `edgeKernelKW prob c' τ t = e^{-c' Υ(iτ)} (2π)^z t^{z-1} / (Γ(z) V(t))`, the edge kernel `K(τ, x)`;
* `edgeA1W w c' τ = S^{(w)}_{c'}(ω(iτ))^{-1} (2π/(3ω(iτ)))^{(w-1)/2}`, the amplitude `A₁(τ)`;
* `edgeA2W prob c' t = x^{w-1} t^{-1/2} e^{c' L(x)} / V(t)`, the amplitude `A₂(x)`.

Proved here (all unconditional, `c' ≥ c₀`):
* `edgeKernelKW_factorization`: `K = A₁ A₂ exp(c'(R_V + iΘ))` with the weight-free exponent
  `R_V = -D(x₀(τ), x)` and phase `Θ` of `StripMultiplier` (`edgeRV`, `edgeTheta`, whose evenness,
  oddness, unimodality and `τ`-derivative are weight free and are reused);
* `edgeA1W_norm_le`, `edgeA1W_deriv_refined`, `edgeA1W_deriv_le`: `|A₁| ≤ C_w` and
  `|A₁'(τ)| ≤ C/(c'(1+|τ|)³) + (w-1) C_F/(1+|τ|)`, hence `|A₁'| ≤ C_w/(1+|τ|)`.  The first term is the
  `S^{(w)}`-part (constants of `StirlingW`), the second the derivative of the factor
  `(2π/(3ω))^{(w-1)/2}`; it carries no `1/c'` and vanishes at `w = 1`;
* `edgeA2W_nonneg_le`: `0 ≤ A₂ ≤ C` on `x ≥ ξ*/2` (from the ratio bound `rho_bounds` of `LemmaS2W`);
* `edgeKernelKW_subCardy_bound`: `|K| ≤ C e^{-κ c'}` uniformly in `τ` on `0 < x ≤ ξ*/2`
  (second clause of `kernelBound_W` with `x_* = x₀(τ) ≥ ξ*`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing WeightAxioms ComplexBessel Chart ChartGeometry StripBand
open FormalResearch.ModularBootstrap.StripMultiplier
  (edgeRV edgePhi edgeTheta edgeTau0 wFactor edgeX0_pos_all xiStar_le_edgeX0_all
    edgeRV_nonpos edgeRV_even edgePhi_odd hasDerivAt_edgeTheta edgeRV_unimodal
    hasDerivAt_chartOmega_left_edge norm_chartOmega_left_edge_ge)

/-! ### Section 1: Definitions -/

/-- Edge Mellin kernel `K(τ, x) = e^{-c' Υ(iτ)} (2π)^z t^{z-1} / (Γ(z) V(t))`, `z = w/2 + c' ω(iτ)`,
`V = prob.cardyV (c'/12)` (`lower_o1_two_edge.tex`, Lemma J4.1, `vlo:J41`), as a function of `(τ, t)`
with `t = c' x² / 3`. -/
noncomputable def edgeKernelKW (prob : FixedWeightProblem) (c' : ℝ) (τ t : ℝ) : ℂ :=
  if 0 < t then
    let z : ℂ := (prob.w : ℂ) / 2 + (c' : ℂ) * chartOmega (Complex.I * (τ : ℂ))
    Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
      (2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) /
      (Complex.Gamma z * (prob.cardyV (c' / 12) t : ℂ))
  else 0

/-- The Stirling part `S^{(w)}_{c'}(ω(iτ))^{-1}` of the amplitude `A₁`. -/
noncomputable def edgeA1SW (w : ℕ) (c' τ : ℝ) : ℂ :=
  (stirlingSW w c' (chartOmega (Complex.I * (τ : ℂ))))⁻¹

/-- Edge amplitude `A₁(τ) = S^{(w)}_{c'}(ω(iτ))^{-1} (2π/(3 ω(iτ)))^{(w-1)/2}`
(`lower_o1_two_edge.tex`, Lemma J4.2, `vlo:J42`). -/
noncomputable def edgeA1W (w : ℕ) (c' τ : ℝ) : ℂ :=
  edgeA1SW w c' τ * wFactor (w : ℝ) (chartOmega (Complex.I * (τ : ℂ)))

/-- Energy amplitude `A₂(x) = x^{w-1} t^{-1/2} e^{c' L(x)} / V(t)` with `x = √(3t/c')`
(`lower_o1_two_edge.tex`, Lemma J4.2, `vlo:J42`). -/
noncomputable def edgeA2W (prob : FixedWeightProblem) (c' t : ℝ) : ℝ :=
  (√(3 * t / c')) ^ (prob.w - 1) * (1 / √t) *
    Real.exp (c' * Bessel.besselL (√(3 * t / c'))) / prob.cardyV (c' / 12) t

/-! ### Section 2: Left-edge facts for `ω(iτ)` -/

lemma re_chartOmega_edge (τ : ℝ) : (chartOmega (Complex.I * (τ : ℂ))).re = edgeMu τ := by
  rw [chartOmega_left_edge]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, Complex.ofReal_im, mul_zero, sub_zero, sub_self]

lemma muStar_le_re_chartOmega_edge (τ : ℝ) : muStar ≤ (chartOmega (Complex.I * (τ : ℂ))).re := by
  rw [re_chartOmega_edge]; exact edgeMu_ge_muStar_W τ

lemma re_chartOmega_edge_pos (τ : ℝ) : 0 < (chartOmega (Complex.I * (τ : ℂ))).re :=
  lt_of_lt_of_le muStar_pos (muStar_le_re_chartOmega_edge τ)

lemma chartOmega_edge_ne_zero (τ : ℝ) : chartOmega (Complex.I * (τ : ℂ)) ≠ 0 := by
  intro h
  have := re_chartOmega_edge_pos τ
  rw [h, Complex.zero_re] at this
  exact lt_irrefl 0 this

lemma muStar_le_norm_chartOmega_edge (τ : ℝ) : muStar ≤ ‖chartOmega (Complex.I * (τ : ℂ))‖ :=
  (muStar_le_re_chartOmega_edge τ).trans (Complex.re_le_norm _)

/-- `(x²)^{(w-1)/2} = x^{w-1}` for `x > 0`. -/
lemma rpow_sq_half_eq_pow {x : ℝ} (hx : 0 < x) {w : ℕ} (hw : 1 ≤ w) :
    (x ^ 2) ^ (((w : ℝ) - 1) / 2) = x ^ (w - 1) := by
  have hcast : ((w : ℝ) - 1) = ((w - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hw]; simp
  rw [hcast, ← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le]
  have h2 : ((2 : ℕ) : ℝ) * (((w - 1 : ℕ) : ℝ) / 2) = ((w - 1 : ℕ) : ℝ) := by push_cast; ring
  rw [h2, Real.rpow_natCast]

/-- The inverse Stirling prefactor splits into the real power `x^{w-1}` and the `ω`-factor of `A₁`:
`(3ω/(2π x²))^{-(w-1)/2} = x^{w-1} (2π/(3ω))^{(w-1)/2}` for `Re ω > 0`, `x > 0`. -/
lemma stirlingPrefW_inv_eq {w : ℕ} (hw : 1 ≤ w) {ω : ℂ} (hω_re : 0 < ω.re) {x : ℝ} (hx : 0 < x) :
    (stirlingPrefW w ω (x : ℂ))⁻¹ = ((x ^ (w - 1) : ℝ) : ℂ) * wFactor (w : ℝ) ω := by
  have hω_ne : ω ≠ 0 := by intro h; rw [h, Complex.zero_re] at hω_re; exact lt_irrefl 0 hω_re
  have hx_c : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  set a : ℂ := 3 * ω / (2 * (Real.pi : ℂ) * (x : ℂ) ^ 2) with ha_def
  have ha_eq : a = ((3 / (2 * Real.pi * x ^ 2) : ℝ) : ℂ) * ω := by
    rw [ha_def]; push_cast; field_simp
  have ha_re : 0 < a.re := by
    rw [ha_eq, Complex.re_ofReal_mul]; exact mul_pos (by positivity) hω_re
  have harg : a.arg ≠ Real.pi := by
    have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha_re)
    intro h
    rw [h, abs_of_pos Real.pi_pos] at this
    linarith [Real.pi_pos]
  have hinv : a⁻¹ = ((x ^ 2 : ℝ) : ℂ) * (2 * (Real.pi : ℂ) / (3 * ω)) := by
    rw [ha_def]; push_cast; field_simp
  have hq_ne : (2 * (Real.pi : ℂ) / (3 * ω)) ≠ 0 :=
    div_ne_zero (mul_ne_zero two_ne_zero hpi) (mul_ne_zero three_ne_zero hω_ne)
  have hx2_pos : 0 < x ^ 2 := by positivity
  unfold stirlingPrefW
  rw [← Complex.inv_cpow a _ harg, hinv]
  have hx2_ne : ((x ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx2_pos.ne'
  have hlog : Complex.log (((x ^ 2 : ℝ) : ℂ) * (2 * (Real.pi : ℂ) / (3 * ω))) =
      Complex.log ((x ^ 2 : ℝ) : ℂ) + Complex.log (2 * (Real.pi : ℂ) / (3 * ω)) := by
    have h1 := Complex.log_ofReal_mul hx2_pos hq_ne
    rw [h1, ← Complex.ofReal_log hx2_pos.le]
  have hmul : (((x ^ 2 : ℝ) : ℂ) * (2 * (Real.pi : ℂ) / (3 * ω))) ^ (((w : ℂ) - 1) / 2) =
      ((x ^ 2 : ℝ) : ℂ) ^ (((w : ℂ) - 1) / 2) *
        (2 * (Real.pi : ℂ) / (3 * ω)) ^ (((w : ℂ) - 1) / 2) := by
    rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hx2_ne hq_ne), hlog,
      Complex.cpow_def_of_ne_zero hx2_ne, Complex.cpow_def_of_ne_zero hq_ne, ← Complex.exp_add]
    congr 1; ring
  rw [hmul]
  unfold wFactor
  have hexp' : ((((w : ℝ) - 1) / 2 : ℝ) : ℂ) = ((w : ℂ) - 1) / 2 := by push_cast; ring
  have h := Complex.ofReal_cpow hx2_pos.le (((w : ℝ) - 1) / 2)
  rw [hexp', rpow_sq_half_eq_pow hx hw] at h
  rw [hexp', ← h]


/-! ### Section 3: The factorization `K = A₁ A₂ exp(c'(R_V - iΦ))` -/

lemma cardyV_pos_of_max {prob : FixedWeightProblem} {c' : ℝ}
    (hc' : max 1 (24 * prob.totalShift) ≤ c') {t : ℝ} (ht : 0 < t) :
    0 < prob.cardyV (c' / 12) t := by
  obtain ⟨hS, -, -⟩ := shift_le_of_max_le prob hc'
  exact prob.cardyV_pos hS ht

lemma edgeKernelKW_factorization (prob : FixedWeightProblem) {c' : ℝ}
    (hc' : max 1 (24 * prob.totalShift) ≤ c') (τ : ℝ) {t : ℝ} (ht : 0 < t) :
    edgeKernelKW prob c' τ t =
      edgeA1W prob.w c' τ * (edgeA2W prob c' t : ℂ) *
        Complex.exp ((c' : ℂ) * ((edgeRV c' τ t : ℂ) - Complex.I * (edgePhi c' τ t : ℂ))) := by
  obtain ⟨-, -, hc'_pos⟩ := shift_le_of_max_le prob hc'
  have hw := prob.hw
  let x : ℝ := √(3 * t / c')
  have hx_pos : 0 < x := Real.sqrt_pos.mpr (by positivity)
  have ht_eq : t = c' * x ^ 2 / 3 := by
    dsimp [x]; rw [Real.sq_sqrt (by positivity)]; field_simp [hc'_pos.ne']
  have ht_c_eq : (t : ℂ) = (c' : ℂ) * (x : ℂ) ^ 2 / 3 := by exact_mod_cast ht_eq
  let ω := chartOmega (Complex.I * (τ : ℂ))
  let z : ℂ := (prob.w : ℂ) / 2 + (c' : ℂ) * ω
  have hω_re : 0 < ω.re := re_chartOmega_edge_pos τ
  have hω_ne : ω ≠ 0 := chartOmega_edge_ne_zero τ
  have hz_re : 0 < z.re := by
    dsimp [z]
    have hw1 : (1 : ℝ) ≤ prob.w := by exact_mod_cast hw
    simp only [Complex.div_ofNat_re, Complex.natCast_re, Complex.re_ofReal_mul]
    nlinarith [mul_pos hc'_pos hω_re]
  have hgam_ne : Complex.Gamma z ≠ 0 :=
    Complex.Gamma_ne_zero fun m hm => by
      have := congrArg Complex.re hm
      simp only [Complex.neg_re, Complex.natCast_re] at this
      linarith [Nat.cast_nonneg (α := ℝ) m]
  have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have h2pi_ne : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  have h2pit_ne : (2 * (Real.pi : ℂ) * (t : ℂ)) ^ z ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero h2pi_ne ht_ne))
  have hb_arg : |(x : ℂ).arg| < Real.pi / 4 := by
    rw [Complex.arg_ofReal_of_nonneg hx_pos.le, abs_zero]; positivity
  have hst := gamma_mul_two_pi_t_cpow_neg_W hw hc'_pos hω_re.le hω_ne
    (show 0 < (x : ℂ).re by simpa using hx_pos) hb_arg
  dsimp only at hst
  rw [← ht_c_eq] at hst
  have hcpow_num : (2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) =
      (2 * (Real.pi : ℂ) * (t : ℂ)) ^ z * (t : ℂ)⁻¹ := by
    have hmul : (2 * (Real.pi : ℂ) * (t : ℂ)) ^ z = (2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ z := by
      have h1 : (2 * (Real.pi : ℂ) * (t : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) * (t : ℂ) := by
        push_cast; ring
      rw [h1, Complex.mul_cpow_ofReal_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) ht.le]
      push_cast; rfl
    have hsub : (t : ℂ) ^ (z - 1) = (t : ℂ) ^ z * (t : ℂ)⁻¹ := by
      rw [sub_eq_add_neg, Complex.cpow_add _ _ ht_ne, Complex.cpow_neg_one]
    rw [hmul, hsub]; ring
  have hS_ne : stirlingSW prob.w c' ω ≠ 0 := Complex.exp_ne_zero _
  have ht_half_ne : (t : ℂ) ^ (-(1 / 2 : ℂ)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl ht_ne)
  have hexp_J_ne : Complex.exp ((c' : ℂ) * stirlingJ ω (x : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hPref_inv := stirlingPrefW_inv_eq hw hω_re hx_pos
  have hPref_ne : stirlingPrefW prob.w ω (x : ℂ) ≠ 0 := by
    intro h0
    rw [h0, inv_zero] at hPref_inv
    have hxw : ((x ^ (prob.w - 1) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pow_pos hx_pos _).ne'
    have hwF : wFactor (prob.w : ℝ) ω ≠ 0 := by
      unfold wFactor
      refine Complex.cpow_ne_zero_iff.mpr (Or.inl ?_)
      exact div_ne_zero h2pi_ne (mul_ne_zero three_ne_zero hω_ne)
    exact mul_ne_zero hxw hwF hPref_inv.symm
  have hratio : (2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z =
      (stirlingPrefW prob.w ω (x : ℂ))⁻¹ * (stirlingSW prob.w c' ω)⁻¹ *
        (t : ℂ) ^ (-(1 / 2 : ℂ)) * Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) := by
    have hinv : Complex.Gamma z * ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ z)⁻¹ =
        stirlingPrefW prob.w ω (x : ℂ) * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
          Complex.exp ((c' : ℂ) * stirlingJ ω (x : ℂ)) * stirlingSW prob.w c' ω := by
      rwa [Complex.cpow_neg] at hst
    have hgam_eq : (2 * (Real.pi : ℂ) * (t : ℂ)) ^ z / Complex.Gamma z =
        (stirlingPrefW prob.w ω (x : ℂ))⁻¹ * (stirlingSW prob.w c' ω)⁻¹ *
          ((t : ℂ) ^ (-(1 / 2 : ℂ)))⁻¹ * Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) := by
      rw [Complex.exp_neg]
      calc (2 * (Real.pi : ℂ) * (t : ℂ)) ^ z / Complex.Gamma z
          = (Complex.Gamma z * ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ z)⁻¹)⁻¹ := by
            field_simp [hgam_ne, h2pit_ne]
        _ = (stirlingPrefW prob.w ω (x : ℂ) * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
              Complex.exp ((c' : ℂ) * stirlingJ ω (x : ℂ)) * stirlingSW prob.w c' ω)⁻¹ := by
            rw [hinv]
        _ = (stirlingPrefW prob.w ω (x : ℂ))⁻¹ * (stirlingSW prob.w c' ω)⁻¹ *
              ((t : ℂ) ^ (-(1 / 2 : ℂ)))⁻¹ *
              (Complex.exp ((c' : ℂ) * stirlingJ ω (x : ℂ)))⁻¹ := by
            field_simp [hS_ne, ht_half_ne, hexp_J_ne, hPref_ne]
    have hthalf_inv : ((t : ℂ) ^ (-(1 / 2 : ℂ)))⁻¹ * (t : ℂ)⁻¹ = (t : ℂ) ^ (-(1 / 2 : ℂ)) := by
      rw [← Complex.cpow_neg, neg_neg, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ ht_ne]
      congr 1; norm_num
    rw [hcpow_num, mul_div_right_comm, hgam_eq]
    calc (stirlingPrefW prob.w ω (x : ℂ))⁻¹ * (stirlingSW prob.w c' ω)⁻¹ *
          ((t : ℂ) ^ (-(1 / 2 : ℂ)))⁻¹ * Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) *
            (t : ℂ)⁻¹
        = (stirlingPrefW prob.w ω (x : ℂ))⁻¹ * (stirlingSW prob.w c' ω)⁻¹ *
            (((t : ℂ) ^ (-(1 / 2 : ℂ)))⁻¹ * (t : ℂ)⁻¹) *
            Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) := by ring
      _ = (stirlingPrefW prob.w ω (x : ℂ))⁻¹ * (stirlingSW prob.w c' ω)⁻¹ *
            (t : ℂ) ^ (-(1 / 2 : ℂ)) * Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) := by
          rw [hthalf_inv]
  have hthalf_c : (t : ℂ) ^ (-(1 / 2 : ℂ)) = ((1 / √t : ℝ) : ℂ) := by
    rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow ht.le, Real.rpow_neg ht.le, Real.sqrt_eq_rpow, one_div]
    norm_num
  have hV_pos : 0 < prob.cardyV (c' / 12) t := cardyV_pos_of_max hc' ht
  have hV_ne : (prob.cardyV (c' / 12) t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV_pos.ne'
  have hphi_re : -(chartPhiV (Complex.I * (τ : ℂ)) (x : ℂ)).re = edgeRV c' τ t := by
    rw [re_chartPhiV_edge_eq_Ec τ (x : ℂ)]
    have hE_eq : crudeExponentEc (chartOmega (Complex.I * (τ : ℂ))) (x : ℂ) =
        crudeDivergenceD (edgeX0 τ) x := by
      rw [crudeExponentEc_eq hω_re (Complex.ofReal_ne_zero.mpr hx_pos.ne')]
      have hx_norm : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real, Real.norm_of_nonneg hx_pos.le]
      have hx_re : (x : ℂ).re = x := Complex.ofReal_re x
      have hx_arg : (x : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg hx_pos.le
      have hω_re_eq : (chartOmega (Complex.I * (τ : ℂ))).re = edgeMu τ := re_chartOmega_edge τ
      have h3mu : 3 * (chartOmega (Complex.I * (τ : ℂ))).re / Real.pi = edgeX0 τ := by
        rw [hω_re_eq]; unfold edgeMu; field_simp [Real.pi_pos.ne']
      rw [hx_norm, hx_re, hx_arg, h3mu]
      simp
    rw [hE_eq]; rfl
  have hphi_eq : -chartPhiV (Complex.I * (τ : ℂ)) (x : ℂ) =
      (edgeRV c' τ t : ℂ) - Complex.I * (edgePhi c' τ t : ℂ) := by
    apply Complex.ext
    · simpa [Complex.neg_re, Complex.sub_re, Complex.mul_re] using hphi_re
    · dsimp [x]; simp [edgePhi, Complex.mul_im]
  have htipL_eq : tipL (x : ℂ) = ((Bessel.besselL x : ℝ) : ℂ) := by
    unfold tipL Bessel.besselL; push_cast; ring
  have hexp_L : Complex.exp ((c' : ℂ) * tipL (x : ℂ)) =
      ((Real.exp (c' * Bessel.besselL x) : ℝ) : ℂ) := by
    rw [htipL_eq, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  unfold edgeKernelKW edgeA1W edgeA1SW edgeA2W
  simp only [ht, ↓reduceIte]
  change Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
      (2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) /
      (Complex.Gamma z * (prob.cardyV (c' / 12) t : ℂ)) =
    ((stirlingSW prob.w c' ω)⁻¹ * wFactor (prob.w : ℝ) ω) *
      (((x ^ (prob.w - 1) * (1 / √t) * Real.exp (c' * Bessel.besselL x) /
        prob.cardyV (c' / 12) t : ℝ) : ℂ)) *
      Complex.exp ((c' : ℂ) * ((edgeRV c' τ t : ℂ) - Complex.I * (edgePhi c' τ t : ℂ)))
  rw [show Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
        (2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) /
        (Complex.Gamma z * (prob.cardyV (c' / 12) t : ℂ)) =
      Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
        ((2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z) /
        (prob.cardyV (c' / 12) t : ℂ) by ring,
    hratio, hthalf_c, hPref_inv]
  have hexp_split : Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
      Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) =
      Complex.exp ((c' : ℂ) * tipL (x : ℂ)) *
        Complex.exp ((c' : ℂ) * (-chartPhiV (Complex.I * (τ : ℂ)) (x : ℂ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold chartPhiV
    change -(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ)) +
        -((c' : ℂ) * stirlingJ ω (x : ℂ)) =
      (c' : ℂ) * tipL (x : ℂ) +
        (c' : ℂ) * -(chartUpsilon (Complex.I * (τ : ℂ)) + stirlingJ ω (x : ℂ) + tipL (x : ℂ))
    dsimp [ω]; ring
  calc Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
        (((x ^ (prob.w - 1) : ℝ) : ℂ) * wFactor (prob.w : ℝ) ω *
          (stirlingSW prob.w c' ω)⁻¹ * ((1 / √t : ℝ) : ℂ) *
          Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ)))) /
        (prob.cardyV (c' / 12) t : ℂ)
      = (stirlingSW prob.w c' ω)⁻¹ * wFactor (prob.w : ℝ) ω *
          (((x ^ (prob.w - 1) : ℝ) : ℂ) * ((1 / √t : ℝ) : ℂ) / (prob.cardyV (c' / 12) t : ℂ)) *
          (Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
            Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ)))) := by ring
    _ = (stirlingSW prob.w c' ω)⁻¹ * wFactor (prob.w : ℝ) ω *
          (((x ^ (prob.w - 1) : ℝ) : ℂ) * ((1 / √t : ℝ) : ℂ) / (prob.cardyV (c' / 12) t : ℂ)) *
          (Complex.exp ((c' : ℂ) * tipL (x : ℂ)) *
            Complex.exp ((c' : ℂ) * (-chartPhiV (Complex.I * (τ : ℂ)) (x : ℂ)))) := by
        rw [hexp_split]
    _ = (stirlingSW prob.w c' ω)⁻¹ * wFactor (prob.w : ℝ) ω *
          (((x ^ (prob.w - 1) * (1 / √t) * Real.exp (c' * Bessel.besselL x) /
            prob.cardyV (c' / 12) t : ℝ) : ℂ)) *
          Complex.exp ((c' : ℂ) * ((edgeRV c' τ t : ℂ) - Complex.I * (edgePhi c' τ t : ℂ))) := by
        rw [hexp_L, hphi_eq]
        push_cast; ring

lemma edgeKernelKW_factorization_theta (prob : FixedWeightProblem) {c' : ℝ}
    (hc' : max 1 (24 * prob.totalShift) ≤ c') (τ : ℝ) {t : ℝ} (ht : 0 < t) :
    edgeKernelKW prob c' τ t =
      edgeA1W prob.w c' τ * (edgeA2W prob c' t : ℂ) *
        Complex.exp ((c' : ℂ) * ((edgeRV c' τ t : ℂ) + Complex.I * (edgeTheta c' τ t : ℂ))) := by
  rw [edgeKernelKW_factorization prob hc' τ ht]
  congr 2
  unfold edgeTheta
  push_cast; ring


/-! ### Section 4: The amplitude `A₁` -/

lemma abs_edgeMuDeriv_le_W (τ : ℝ) : |edgeMuDeriv τ| ≤ Real.pi / 6 := by
  have habs : |edgeMuDeriv τ| = (Real.pi / 3) * |edgeX0Deriv τ| := by
    unfold edgeMuDeriv; rw [abs_mul, abs_of_pos (by positivity)]
  have hxd : |edgeX0Deriv τ| ≤ 1 / 2 := by
    rcases le_or_gt 0 τ with h | h
    · rw [abs_of_nonneg (edgeX0Deriv_nonneg h)]
      exact edgeX0Deriv_le_half h
    · have hm : 0 ≤ -τ := by linarith
      have hev : edgeX0Deriv τ = -edgeX0Deriv (-τ) := by
        calc edgeX0Deriv τ = edgeX0Deriv (-(-τ)) := by rw [neg_neg]
          _ = -edgeX0Deriv (-τ) := StripMultiplier.edgeX0Deriv_even (-τ)
      rw [hev, abs_neg, abs_of_nonneg (edgeX0Deriv_nonneg hm)]
      exact edgeX0Deriv_le_half hm
  rw [habs]
  calc (Real.pi / 3) * |edgeX0Deriv τ| ≤ (Real.pi / 3) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hxd (by positivity)
    _ = Real.pi / 6 := by ring

/-- `|ω'(iτ)| ≤ C (1 + |τ|)` for the derivative `ω' = μ' - iν'` of the left-edge parametrization. -/
lemma norm_chartOmega_edge_deriv_le :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ,
      ‖(edgeMuDeriv τ : ℂ) - Complex.I * (edgeNuDeriv τ : ℂ)‖ ≤ C * (1 + |τ|) := by
  obtain ⟨cnu₁, cnu₂, hcnu₁_pos, hcnu₂_pos, hnu_as⟩ := lemma_J4_0.2.2.2.2.1
  refine ⟨Real.pi / 6 + cnu₂, by have := Real.pi_pos; positivity, fun τ => ?_⟩
  have hmu_d : |edgeMuDeriv τ| ≤ Real.pi / 6 := abs_edgeMuDeriv_le_W τ
  have hnu_d : |edgeNuDeriv τ| ≤ cnu₂ * (1 + |τ|) := by
    have hnd : edgeNuDeriv τ = edgeNuDeriv |τ| := by
      rcases le_total 0 τ with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, StripMultiplier.edgeNuDeriv_even]
    rw [hnd]
    have h1 := (hnu_as |τ| (abs_nonneg τ)).2
    have h2 := (hnu_as |τ| (abs_nonneg τ)).1
    have hpos : 0 ≤ edgeNuDeriv |τ| := by
      have : 0 < cnu₁ * (1 + |τ|) := by positivity
      linarith
    rwa [abs_of_nonneg hpos]
  calc ‖(edgeMuDeriv τ : ℂ) - Complex.I * (edgeNuDeriv τ : ℂ)‖
      ≤ ‖(edgeMuDeriv τ : ℂ)‖ + ‖Complex.I * (edgeNuDeriv τ : ℂ)‖ := norm_sub_le _ _
    _ = |edgeMuDeriv τ| + |edgeNuDeriv τ| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (Real.pi / 6) * 1 + cnu₂ * (1 + |τ|) := by linarith
    _ ≤ (Real.pi / 6) * (1 + |τ|) + cnu₂ * (1 + |τ|) := by
        gcongr; linarith [abs_nonneg τ]
    _ = (Real.pi / 6 + cnu₂) * (1 + |τ|) := by ring

/-- The Stirling part of `A₁`: `|S^{-1}| ≤ e^{C_w}` and `|∂_τ S^{-1}| ≤ C/(c'(1+|τ|)³)` for
`c' ≥ 1/μ*` (`∂_ω log S = O(1/(c'|ω|²))`, `|∂_τ ω| ≲ 1 + |τ|`, `|ω| ≳ (1+|τ|)²`). -/
lemma edgeA1SW_bounds {w : ℕ} (hw : 1 ≤ w) :
    ∃ C : ℝ, 0 < C ∧ ∀ {c' : ℝ}, 1 / muStar ≤ c' → ∀ τ : ℝ,
      ‖edgeA1SW w c' τ‖ ≤ Real.exp (stirlingConstW w) ∧
      ∃ d : ℂ, HasDerivAt (edgeA1SW w c') d τ ∧ ‖d‖ ≤ C / (c' * (1 + |τ|) ^ 3) := by
  obtain ⟨c_ω, hc_ω_pos, hω_ge⟩ := norm_chartOmega_left_edge_ge
  obtain ⟨C_ω', hC_ω'_pos, hω'_bd⟩ := norm_chartOmega_edge_deriv_le
  have hCw := stirlingConstW_pos hw
  refine ⟨stirlingConstW w * Real.exp (stirlingConstW w) * C_ω' / c_ω ^ 2, by positivity,
    fun {c'} hc' τ => ?_⟩
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := muStar_pos; positivity) hc'
  let ω : ℂ := chartOmega (Complex.I * (τ : ℂ))
  have hω_re : 0 < ω.re := re_chartOmega_edge_pos τ
  have hω_ne : ω ≠ 0 := chartOmega_edge_ne_zero τ
  have hmu_norm : muStar ≤ ‖ω‖ := muStar_le_norm_chartOmega_edge τ
  have h1_cω : 1 ≤ c' * ‖ω‖ := by
    calc (1 : ℝ) = (1 / muStar) * muStar := by field_simp [muStar_pos.ne']
      _ ≤ c' * ‖ω‖ := mul_le_mul hc' hmu_norm muStar_pos.le hc'_pos.le
  have hA1_bd : ‖edgeA1SW w c' τ‖ ≤ Real.exp (stirlingConstW w) :=
    norm_stirlingSW_inv_le hw hc'_pos hω_re.le h1_cω
  refine ⟨hA1_bd, ?_⟩
  have hd_logS : HasDerivAt (stirlingLogSW w c') (deriv (stirlingLogSW w c') ω) ω :=
    (hasDerivAt_stirlingLogSW hw hc'_pos hω_re.le hω_ne).differentiableAt.hasDerivAt
  have hd_comp := hd_logS.comp τ (hasDerivAt_chartOmega_left_edge τ)
  have heq : edgeA1SW w c' =
      fun s : ℝ => Complex.exp (-stirlingLogSW w c' (chartOmega (Complex.I * (s : ℂ)))) := by
    ext s; unfold edgeA1SW stirlingSW; rw [Complex.exp_neg]
  have hd_A1 : HasDerivAt (edgeA1SW w c')
      (-(deriv (stirlingLogSW w c') ω * ((edgeMuDeriv τ : ℂ) - Complex.I * (edgeNuDeriv τ : ℂ))) *
        edgeA1SW w c' τ) τ := by
    rw [heq]
    refine (hd_comp.neg.cexp).congr_deriv ?_
    dsimp [edgeA1SW, stirlingSW, ω]
    rw [Complex.exp_neg]
    ring
  refine ⟨_, hd_A1, ?_⟩
  have hd_log_bd : ‖deriv (stirlingLogSW w c') ω‖ ≤ stirlingConstW w / (c' * ‖ω‖ ^ 2) :=
    norm_deriv_stirlingLogSW_le hw hc'_pos hω_re.le h1_cω
  have hω_lb := hω_ge τ
  have h1t : 1 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
  have hden_le : c' * (c_ω * (1 + |τ|) ^ 2) ^ 2 ≤ c' * ‖ω‖ ^ 2 := by gcongr
  have hden_pos : 0 < c' * (c_ω * (1 + |τ|) ^ 2) ^ 2 := by positivity
  calc ‖-(deriv (stirlingLogSW w c') ω *
          ((edgeMuDeriv τ : ℂ) - Complex.I * (edgeNuDeriv τ : ℂ))) * edgeA1SW w c' τ‖
      = ‖deriv (stirlingLogSW w c') ω‖ *
          ‖(edgeMuDeriv τ : ℂ) - Complex.I * (edgeNuDeriv τ : ℂ)‖ * ‖edgeA1SW w c' τ‖ := by
        rw [norm_mul, norm_neg, norm_mul]
    _ ≤ (stirlingConstW w / (c' * ‖ω‖ ^ 2)) * (C_ω' * (1 + |τ|)) *
          Real.exp (stirlingConstW w) := by
        gcongr
        exact hω'_bd τ
    _ ≤ (stirlingConstW w / (c' * (c_ω * (1 + |τ|) ^ 2) ^ 2)) * (C_ω' * (1 + |τ|)) *
          Real.exp (stirlingConstW w) := by
        gcongr
    _ = stirlingConstW w * Real.exp (stirlingConstW w) * C_ω' / c_ω ^ 2 /
          (c' * (1 + |τ|) ^ 3) := by
        field_simp [hc'_pos.ne', hc_ω_pos.ne', (by linarith : (1 + |τ|) ≠ 0)]

/-- The `ω`-factor of `A₁`: `|(2π/(3ω))^{(w-1)/2}| ≤ B` and its `τ`-derivative
`-(r) wF ω'/ω`, `r = (w-1)/2`, has norm at most `r C_F/(1+|τ|)` (no `1/c'`, vanishing at `w = 1`). -/
lemma wFactor_edge_bounds (w : ℕ) (hw : 1 ≤ w) :
    ∃ B C_F : ℝ, 0 < B ∧ 0 < C_F ∧ ∀ τ : ℝ,
      ‖wFactor (w : ℝ) (chartOmega (Complex.I * (τ : ℂ)))‖ ≤ B ∧
      ∃ d : ℂ, HasDerivAt (fun s : ℝ => wFactor (w : ℝ) (chartOmega (Complex.I * (s : ℂ)))) d τ ∧
        ‖d‖ ≤ (((w : ℝ) - 1) / 2) * (C_F / (1 + |τ|)) := by
  obtain ⟨c_ω, hc_ω_pos, hω_ge⟩ := norm_chartOmega_left_edge_ge
  obtain ⟨C_ω', hC_ω'_pos, hω'_bd⟩ := norm_chartOmega_edge_deriv_le
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  let r : ℝ := ((w : ℝ) - 1) / 2
  have hr_nn : 0 ≤ r := by dsimp [r]; linarith
  let B0 : ℝ := ((2 * Real.pi / 3) / muStar) ^ r
  have hB0_pos : 0 < B0 := by have := Real.pi_pos; have := muStar_pos; positivity
  refine ⟨B0, B0 * (C_ω' / c_ω), hB0_pos, by positivity, fun τ => ?_⟩
  let ω : ℂ := chartOmega (Complex.I * (τ : ℂ))
  have hω_re : 0 < ω.re := re_chartOmega_edge_pos τ
  have hω_ne : ω ≠ 0 := chartOmega_edge_ne_zero τ
  have hmu_norm : muStar ≤ ‖ω‖ := muStar_le_norm_chartOmega_edge τ
  have h2pi3_ne : (2 * (Real.pi : ℂ) / 3) ≠ 0 :=
    div_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) (by norm_num)
  have harg_ne : 2 * (Real.pi : ℂ) / (3 * ω) ≠ 0 := by
    rw [show 2 * (Real.pi : ℂ) / (3 * ω) = (2 * (Real.pi : ℂ) / 3) * ω⁻¹ by ring]
    exact mul_ne_zero h2pi3_ne (inv_ne_zero hω_ne)
  have hwF_norm : ‖wFactor (w : ℝ) ω‖ ≤ B0 := by
    unfold wFactor
    have hnorm_cp : ‖(2 * (Real.pi : ℂ) / (3 * ω)) ^ ((((w : ℝ) - 1) / 2 : ℝ) : ℂ)‖ =
        ‖2 * (Real.pi : ℂ) / (3 * ω)‖ ^ r := by
      rw [Complex.norm_cpow_of_ne_zero harg_ne]
      simp [r]
    rw [hnorm_cp]
    have hnorm_arg : ‖2 * (Real.pi : ℂ) / (3 * ω)‖ ≤ (2 * Real.pi / 3) / muStar := by
      rw [norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le]
      rw [show 2 * Real.pi / (3 * ‖ω‖) = (2 * Real.pi / 3) / ‖ω‖ by ring]
      exact div_le_div_of_nonneg_left (by positivity) muStar_pos hmu_norm
    exact Real.rpow_le_rpow (norm_nonneg _) hnorm_arg hr_nn
  refine ⟨hwF_norm, ?_⟩
  have hwF_re : 0 < (2 * (Real.pi : ℂ) / (3 * ω)).re := by
    have h_inv_re : 0 < (ω⁻¹).re := by
      rw [Complex.inv_re]
      exact div_pos hω_re (Complex.normSq_pos.mpr hω_ne)
    rw [show 2 * (Real.pi : ℂ) / (3 * ω) = ((2 * Real.pi / 3 : ℝ) : ℂ) * ω⁻¹ by push_cast; ring]
    rw [Complex.re_ofReal_mul]
    exact mul_pos (by positivity) h_inv_re
  have hslit : 2 * (Real.pi : ℂ) / (3 * ω) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl hwF_re)
  let ω' : ℂ := (edgeMuDeriv τ : ℂ) - Complex.I * (edgeNuDeriv τ : ℂ)
  have hd_wF : HasDerivAt (fun s : ℝ => wFactor (w : ℝ) (chartOmega (Complex.I * (s : ℂ))))
      (-(r : ℂ) * wFactor (w : ℝ) ω * (ω' / ω)) τ := by
    have hd_outer : HasDerivAt (fun z : ℂ => 2 * (Real.pi : ℂ) / (3 * z))
        (-(2 * (Real.pi : ℂ) / 3) / ω ^ 2) ω := by
      have h3 : HasDerivAt (fun z : ℂ => (3 : ℂ) * z) 3 ω := by
        simpa using (hasDerivAt_id ω).const_mul (3 : ℂ)
      have hd := (hasDerivAt_const ω (2 * (Real.pi : ℂ))).div h3 (mul_ne_zero (by norm_num) hω_ne)
      refine hd.congr_deriv ?_
      field_simp [hω_ne]; ring
    have hcp := (hd_outer.cpow_const (c := (r : ℂ)) hslit).scomp τ
      (hasDerivAt_chartOmega_left_edge τ)
    refine hcp.congr_deriv ?_
    unfold wFactor
    have hr1 : ω' * ((r : ℂ) * (2 * (Real.pi : ℂ) / (3 * ω)) ^ ((r : ℂ) - 1) *
        (-(2 * (Real.pi : ℂ) / 3) / ω ^ 2)) =
        -(r : ℂ) * (2 * (Real.pi : ℂ) / (3 * ω)) ^ (r : ℂ) * (ω' / ω) := by
      have hrw : (2 * (Real.pi : ℂ) / (3 * ω)) ^ (r : ℂ) =
          (2 * (Real.pi : ℂ) / (3 * ω)) ^ ((r : ℂ) - 1) * (2 * (Real.pi : ℂ) / (3 * ω)) := by
        calc (2 * (Real.pi : ℂ) / (3 * ω)) ^ (r : ℂ)
            = (2 * (Real.pi : ℂ) / (3 * ω)) ^ (((r : ℂ) - 1) + 1) := by ring_nf
          _ = (2 * (Real.pi : ℂ) / (3 * ω)) ^ ((r : ℂ) - 1) *
                (2 * (Real.pi : ℂ) / (3 * ω)) ^ (1 : ℂ) :=
              Complex.cpow_add _ 1 harg_ne
          _ = (2 * (Real.pi : ℂ) / (3 * ω)) ^ ((r : ℂ) - 1) * (2 * (Real.pi : ℂ) / (3 * ω)) := by
              rw [Complex.cpow_one]
      rw [hrw]
      field_simp [harg_ne, hω_ne, h2pi3_ne]
    simpa [r, ω, smul_eq_mul] using hr1
  refine ⟨_, hd_wF, ?_⟩
  have h1t : 0 < 1 + |τ| := by linarith [abs_nonneg τ]
  have hω_lb := hω_ge τ
  calc ‖-(r : ℂ) * wFactor (w : ℝ) ω * (ω' / ω)‖
      = r * ‖wFactor (w : ℝ) ω‖ * (‖ω'‖ / ‖ω‖) := by
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hr_nn, norm_div]
    _ ≤ r * B0 * (C_ω' * (1 + |τ|) / (c_ω * (1 + |τ|) ^ 2)) := by
        gcongr
        exact hω'_bd τ
    _ = r * (B0 * (C_ω' / c_ω) / (1 + |τ|)) := by
        field_simp [hc_ω_pos.ne', h1t.ne']

/-- **Bounds on the amplitude `A₁` at weight `w`** (`vlo:J42`): for `c' ≥ 1/μ*`,
`|A₁(τ)| ≤ C_A1` and `A₁` is differentiable with
`|A₁'(τ)| ≤ C_S/(c'(1+|τ|)³) + ((w-1)/2) C_F/(1+|τ|)`.
The first term (from `S^{(w)}`) has the `1/c'` decay of the weight-one case; the second (from the
`ω`-factor `(2π/(3ω))^{(w-1)/2}`) has none, and vanishes at `w = 1`. -/
lemma edgeA1W_bounds {w : ℕ} (hw : 1 ≤ w) :
    ∃ C_A1 C_S C_F : ℝ, 0 < C_A1 ∧ 0 < C_S ∧ 0 < C_F ∧ ∀ {c' : ℝ}, 1 / muStar ≤ c' →
      ∀ τ : ℝ, ‖edgeA1W w c' τ‖ ≤ C_A1 ∧
        ∃ d : ℂ, HasDerivAt (edgeA1W w c') d τ ∧
          ‖d‖ ≤ C_S / (c' * (1 + |τ|) ^ 3) + (((w : ℝ) - 1) / 2) * (C_F / (1 + |τ|)) := by
  obtain ⟨C, hC, hS⟩ := edgeA1SW_bounds hw
  obtain ⟨B, C_F, hB, hC_F, hF⟩ := wFactor_edge_bounds w hw
  let E : ℝ := Real.exp (stirlingConstW w)
  have hE : 0 < E := Real.exp_pos _
  refine ⟨E * B, C * B, E * C_F, by positivity, by positivity, by positivity,
    fun {c'} hc' τ => ?_⟩
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := muStar_pos; positivity) hc'
  obtain ⟨hS_norm, d1, hd1, hd1_norm⟩ := hS hc' τ
  obtain ⟨hF_norm, d2, hd2, hd2_norm⟩ := hF τ
  have hunf : edgeA1W w c' = fun s : ℝ => edgeA1SW w c' s *
      wFactor (w : ℝ) (chartOmega (Complex.I * (s : ℂ))) := rfl
  refine ⟨?_, d1 * wFactor (w : ℝ) (chartOmega (Complex.I * (τ : ℂ))) +
    edgeA1SW w c' τ * d2, ?_, ?_⟩
  · unfold edgeA1W
    rw [norm_mul]
    exact mul_le_mul hS_norm hF_norm (norm_nonneg _) hE.le
  · rw [hunf]; exact hd1.mul hd2
  · have h1t : 0 < 1 + |τ| := by linarith [abs_nonneg τ]
    have hr_nn : 0 ≤ ((w : ℝ) - 1) / 2 := by
      have : (1 : ℝ) ≤ w := by exact_mod_cast hw
      linarith
    calc ‖d1 * wFactor (w : ℝ) (chartOmega (Complex.I * (τ : ℂ))) + edgeA1SW w c' τ * d2‖
        ≤ ‖d1‖ * ‖wFactor (w : ℝ) (chartOmega (Complex.I * (τ : ℂ)))‖ +
            ‖edgeA1SW w c' τ‖ * ‖d2‖ := by
          refine (norm_add_le _ _).trans_eq ?_; rw [norm_mul, norm_mul]
      _ ≤ (C / (c' * (1 + |τ|) ^ 3)) * B + E * ((((w : ℝ) - 1) / 2) * (C_F / (1 + |τ|))) := by
          gcongr
      _ = C * B / (c' * (1 + |τ|) ^ 3) + (((w : ℝ) - 1) / 2) * (E * C_F / (1 + |τ|)) := by
          field_simp

/-- **`A₁` is bounded with derivative `O(1/(1+|τ|))`** (the form consumed by the band reduction):
for `c' ≥ max 1 (1/μ*)`, `|A₁| ≤ C_A1` and `|A₁'(τ)| ≤ C_A1'/(1+|τ|)`.  This is exactly the
`C_w (1+|τ|)^{-1}` of `vlo:J42`; at `w = 1` the sharper `C/(c'(1+|τ|)³)` holds
(`edgeA1W_bounds`, second term absent). -/
lemma edgeA1W_deriv_le {w : ℕ} (hw : 1 ≤ w) :
    ∃ C_A1 C_A1' : ℝ, 0 < C_A1 ∧ 0 < C_A1' ∧ ∀ {c' : ℝ}, max 1 (1 / muStar) ≤ c' →
      ∀ τ : ℝ, ‖edgeA1W w c' τ‖ ≤ C_A1 ∧
        ∃ d : ℂ, HasDerivAt (edgeA1W w c') d τ ∧ ‖d‖ ≤ C_A1' / (1 + |τ|) := by
  obtain ⟨C_A1, C_S, C_F, hA1, hS, hF, hb⟩ := edgeA1W_bounds hw
  have hr_nn : 0 ≤ ((w : ℝ) - 1) / 2 := by
    have : (1 : ℝ) ≤ w := by exact_mod_cast hw
    linarith
  refine ⟨C_A1, C_S + (((w : ℝ) - 1) / 2) * C_F, hA1, by positivity, fun {c'} hc' τ => ?_⟩
  obtain ⟨hn, d, hd, hdn⟩ := hb ((le_max_right _ _).trans hc') τ
  have hc1 : 1 ≤ c' := (le_max_left _ _).trans hc'
  have h1t : 1 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
  refine ⟨hn, d, hd, hdn.trans ?_⟩
  have hpow : 1 + |τ| ≤ c' * (1 + |τ|) ^ 3 := by
    have h1 : 1 + |τ| ≤ (1 + |τ|) ^ 3 := by nlinarith [sq_nonneg (1 + |τ|)]
    calc 1 + |τ| ≤ (1 + |τ|) ^ 3 := h1
      _ ≤ c' * (1 + |τ|) ^ 3 := le_mul_of_one_le_left (by positivity) hc1
  have h1t' : 0 < 1 + |τ| := by linarith
  calc C_S / (c' * (1 + |τ|) ^ 3) + (((w : ℝ) - 1) / 2) * (C_F / (1 + |τ|))
      ≤ C_S / (1 + |τ|) + (((w : ℝ) - 1) / 2) * (C_F / (1 + |τ|)) := by
        gcongr
    _ = (C_S + (((w : ℝ) - 1) / 2) * C_F) / (1 + |τ|) := by ring


/-! ### Section 5: The amplitude `A₂` -/

/-- **Bound on `A₂`** (`vlo:J42`): `0 ≤ A₂(x) ≤ C` for `x ≥ ξ*/2` and `c' ≥ c₀`.  From the ratio bound
`V(t) ≥ (c_Q/2) (2x)^{w-1} A_s(c' L(x))` (`rho_bounds`): the factor `x^{w-1}` of `A₂` cancels
`(2x)^{w-1}` up to `2^{-(w-1)} ≤ 1`, and `e^{c'L}/A_s(c'L) = √(2π c' L)`, `√(2π c' L)/√t = 2π/√x`. -/
lemma edgeA2W_nonneg_le (prob : FixedWeightProblem) :
    ∃ C_A2 c₀ : ℝ, 0 < C_A2 ∧ max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {t : ℝ}, 0 < t → xiStar / 2 ≤ √(3 * t / c') →
        0 ≤ edgeA2W prob c' t ∧ edgeA2W prob c' t ≤ C_A2 := by
  obtain ⟨U⟩ := fixedWeightAxioms_of_problem prob
  have hcQ := U.hcQ_pos
  refine ⟨4 * Real.pi / U.c_Q * √10, max U.c₀ (2 * U.C_V / U.c_Q), by positivity,
    U.hc₀_ge.trans (le_max_left _ _), fun {c'} hc' {t} ht hx_lo => ?_⟩
  have hc'U : U.c₀ ≤ c' := (le_max_left _ _).trans hc'
  have hCV : 2 * U.C_V ≤ c' * U.c_Q := by
    have h := (le_max_right _ _).trans hc'
    rwa [div_le_iff₀ hcQ] at h
  have hc'max : max 1 (24 * prob.totalShift) ≤ c' := U.hc₀_ge.trans hc'U
  obtain ⟨-, -, hc'_pos⟩ := shift_le_of_max_le prob hc'max
  let x : ℝ := √(3 * t / c')
  have hx_pos : 0 < x := Real.sqrt_pos.mpr (by positivity)
  have ht_eq : t = c' * x ^ 2 / 3 := by
    dsimp [x]; rw [Real.sq_sqrt (by positivity)]; field_simp [hc'_pos.ne']
  have hx10 : (1 / 10 : ℝ) ≤ x := by
    have := Bessel.one_fifth_le_xiStar
    dsimp [x] at hx_lo ⊢
    linarith
  have hρ := (rho_bounds U hc'U hCV (x := x) hx_lo).1
  rw [← ht_eq] at hρ
  have hV_pos : 0 < prob.cardyV (c' / 12) t := cardyV_pos_of_max hc'max ht
  have hL_pos : 0 < c' * Bessel.besselL x := by unfold Bessel.besselL; positivity
  have hAs_pos : 0 < Bessel.besselAs (c' * Bessel.besselL x) := Bessel.besselAs_pos hL_pos
  have hP_pos : 0 < (2 * x) ^ (prob.w - 1) := by positivity
  have hD_pos : 0 < (2 * x) ^ (prob.w - 1) * Bessel.besselAs (c' * Bessel.besselL x) :=
    mul_pos hP_pos hAs_pos
  have hV_ge : (U.c_Q / 2) * ((2 * x) ^ (prob.w - 1) * Bessel.besselAs (c' * Bessel.besselL x)) ≤
      prob.cardyV (c' / 12) t := by
    rw [le_div_iff₀ hD_pos] at hρ
    exact hρ
  have hsqrt_t : 0 < √t := Real.sqrt_pos.mpr ht
  refine ⟨by unfold edgeA2W; positivity, ?_⟩
  have hden_pos : 0 < (U.c_Q / 2) *
      ((2 * x) ^ (prob.w - 1) * Bessel.besselAs (c' * Bessel.besselL x)) := by positivity
  have hnum_nn : 0 ≤ x ^ (prob.w - 1) * (1 / √t) * Real.exp (c' * Bessel.besselL x) := by positivity
  have h1 : edgeA2W prob c' t ≤ x ^ (prob.w - 1) * (1 / √t) * Real.exp (c' * Bessel.besselL x) /
      ((U.c_Q / 2) * ((2 * x) ^ (prob.w - 1) * Bessel.besselAs (c' * Bessel.besselL x))) := by
    unfold edgeA2W
    exact div_le_div_of_nonneg_left hnum_nn hden_pos hV_ge
  refine h1.trans ?_
  have hAs : Bessel.besselAs (c' * Bessel.besselL x) =
      Real.exp (c' * Bessel.besselL x) / √(2 * Real.pi * (c' * Bessel.besselL x)) := rfl
  have hsq := sqrt_two_pi_mul_div_sqrt hc'_pos hx_pos
  rw [← ht_eq] at hsq
  have hsqL_pos : 0 < √(2 * Real.pi * (c' * Bessel.besselL x)) := Real.sqrt_pos.mpr (by positivity)
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx_pos
  have hpow : x ^ (prob.w - 1) / (2 * x) ^ (prob.w - 1) ≤ 1 := by
    rw [mul_pow, div_le_one (by positivity)]
    have h2 : (1 : ℝ) ≤ 2 ^ (prob.w - 1) := one_le_pow₀ (by norm_num)
    nlinarith [pow_pos hx_pos (prob.w - 1)]
  have hpow_nn : 0 ≤ x ^ (prob.w - 1) / (2 * x) ^ (prob.w - 1) := by positivity
  have heq : x ^ (prob.w - 1) * (1 / √t) * Real.exp (c' * Bessel.besselL x) /
      ((U.c_Q / 2) * ((2 * x) ^ (prob.w - 1) * Bessel.besselAs (c' * Bessel.besselL x))) =
      (2 / U.c_Q) * (x ^ (prob.w - 1) / (2 * x) ^ (prob.w - 1)) *
        (√(2 * Real.pi * (c' * Bessel.besselL x)) / √t) := by
    rw [hAs]
    field_simp
  rw [heq, hsq]
  have hinv : 2 * Real.pi / √x ≤ 2 * Real.pi * √10 := by
    have hsqrt_x : (1 / √10 : ℝ) ≤ √x := by
      have := Real.sqrt_le_sqrt hx10
      rwa [Real.sqrt_div (by norm_num), Real.sqrt_one] at this
    rw [div_le_iff₀ hsx]
    have hsq10 : √10 * (1 / √10) = 1 := by
      field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 10)]
    calc 2 * Real.pi = (2 * Real.pi * √10) * (1 / √10) := by rw [mul_assoc, hsq10, mul_one]
      _ ≤ (2 * Real.pi * √10) * √x := by gcongr
  calc 2 / U.c_Q * (x ^ (prob.w - 1) / (2 * x) ^ (prob.w - 1)) * (2 * Real.pi / √x)
      ≤ 2 / U.c_Q * 1 * (2 * Real.pi * √10) := by
        gcongr
    _ = 4 * Real.pi / U.c_Q * √10 := by ring

/-! ### Section 6: Sub-Cardy kernel bound -/

/-- **Sub-Cardy kernel bound** (`vlo:J42`, last clause): for `c' ≥ c₀`, `0 < t` with
`x = √(3t/c') ≤ ξ*/2` and every `τ`, `|K(τ, x)| ≤ C e^{-κ c'}`.  This is the second clause of
`kernelBound_W` with `Re ω(iτ) = μ(τ) ≥ μ*` (`x_* = 3 μ/π = x₀(τ) ≥ ξ*`), since
`|e^{-c'Υ(iτ)}| = e^{-c' B(ω(iτ))}`. -/
lemma edgeKernelKW_subCardy_bound (prob : FixedWeightProblem) :
    ∃ C_sub κ_sub c₀ : ℝ, 0 < C_sub ∧ 0 < κ_sub ∧ max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {t : ℝ}, 0 < t → √(3 * t / c') ≤ xiStar / 2 →
        ∀ τ : ℝ, ‖edgeKernelKW prob c' τ t‖ ≤ C_sub * Real.exp (-κ_sub * c') := by
  let μ₀ : ℝ := (Real.pi * xiStar / 6 + muStar) / 2
  have hμ₀ : Real.pi * xiStar / 6 < μ₀ := by
    dsimp [μ₀]; unfold muStar
    have : 0 < Real.pi * xiStar := mul_pos Real.pi_pos xiStar_pos
    linarith
  have hμ₀_le : μ₀ ≤ muStar := by
    dsimp [μ₀]; unfold muStar
    have : 0 < Real.pi * xiStar := mul_pos Real.pi_pos xiStar_pos
    linarith
  obtain ⟨C, κ, c₀, hC, hκ, hc₀, hker⟩ := kernelBound_W prob hμ₀
  refine ⟨C, κ, c₀, hC, hκ, hc₀, fun {c'} hc' {t} ht hx τ => ?_⟩
  have hc'max : max 1 (24 * prob.totalShift) ≤ c' := hc₀.trans hc'
  obtain ⟨-, -, hc'_pos⟩ := shift_le_of_max_le prob hc'max
  have hV_pos : 0 < prob.cardyV (c' / 12) t := cardyV_pos_of_max hc'max ht
  have hω : μ₀ ≤ (chartOmega (Complex.I * (τ : ℂ))).re :=
    hμ₀_le.trans (muStar_le_re_chartOmega_edge τ)
  have hk := (hker hc' hω ht).2 hx
  set z : ℂ := (prob.w : ℂ) / 2 + (c' : ℂ) * chartOmega (Complex.I * (τ : ℂ)) with hz
  have hexp_norm : ‖Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ)))‖ =
      Real.exp (-c' * crudeExponentB (chartOmega (Complex.I * (τ : ℂ)))) := by
    rw [Complex.norm_exp, neg_mul, Complex.neg_re, Complex.re_ofReal_mul,
      re_chartUpsilon_left_edge τ]
    ring_nf
  have hV_norm : ‖(prob.cardyV (c' / 12) t : ℂ)‖ = prob.cardyV (c' / 12) t := by
    rw [Complex.norm_real, Real.norm_of_nonneg hV_pos.le]
  unfold edgeKernelKW
  simp only [ht, ↓reduceIte]
  change ‖Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
      (2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) /
      (Complex.Gamma z * (prob.cardyV (c' / 12) t : ℂ))‖ ≤ C * Real.exp (-κ * c')
  rw [show Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
        (2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) /
        (Complex.Gamma z * (prob.cardyV (c' / 12) t : ℂ)) =
      Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
        ((2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z) /
        (prob.cardyV (c' / 12) t : ℂ) by ring,
    norm_div, norm_mul, hexp_norm, hV_norm, div_le_iff₀ hV_pos]
  calc Real.exp (-c' * crudeExponentB (chartOmega (Complex.I * (τ : ℂ)))) *
        ‖(2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z‖
      ≤ Real.exp (-c' * crudeExponentB (chartOmega (Complex.I * (τ : ℂ)))) *
          (C * Real.exp (c' * crudeExponentB (chartOmega (Complex.I * (τ : ℂ)))) *
            Real.exp (-κ * c') * prob.cardyV (c' / 12) t) := by
        gcongr
    _ = C * Real.exp (-κ * c') * prob.cardyV (c' / 12) t *
          (Real.exp (-c' * crudeExponentB (chartOmega (Complex.I * (τ : ℂ)))) *
            Real.exp (c' * crudeExponentB (chartOmega (Complex.I * (τ : ℂ))))) := by ring
    _ = C * Real.exp (-κ * c') * prob.cardyV (c' / 12) t := by
        rw [← Real.exp_add,
          show -c' * crudeExponentB (chartOmega (Complex.I * (τ : ℂ))) +
            c' * crudeExponentB (chartOmega (Complex.I * (τ : ℂ))) = 0 by ring,
          Real.exp_zero, mul_one]

/-! ### Axiom verification -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.stirlingPrefW_inv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stirlingPrefW_inv_eq

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.edgeKernelKW_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgeKernelKW_factorization

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.edgeA1W_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgeA1W_bounds

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.edgeA1W_deriv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgeA1W_deriv_le

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.edgeA2W_nonneg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgeA2W_nonneg_le

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.edgeKernelKW_subCardy_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgeKernelKW_subCardy_bound

end FormalResearch.ModularBootstrap.FixedWeightBand
