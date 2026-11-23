module

public import FormalResearch.ModularBootstrap.FixedWeightBand.LemmaS2WKernel
public import FormalResearch.ModularBootstrap.FixedWeightBand.MellinConvergenceW
public import FormalResearch.ModularBootstrap.WeightAxioms.Axioms

/-!
# Crude Legendre Bound at Weight `w` (Lemma S2, `vlo:S2`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J2, Lemma S2 (`vlo:S2`).

For `prob : FixedWeightProblem` (weight `w ≥ 1`, null-state product `Q`), `μ₀ > π ξ_*/6`,
`ω` with `Re ω ≥ μ₀`, `z = w/2 + c' ω`, `V = prob.cardyV (c'/12)` and all sufficiently large `c'`:

* `kernelBound_W`: the pointwise kernel bound
  `|(2π)^z t^{z-1}/Γ(z)| ≤ C e^{c' B(ω)} V(t)` for all `t > 0`, and the sub-Cardy kernel bound
  `|(2π)^z t^{z-1}/Γ(z)| ≤ C e^{c' B(ω)} e^{-κ c'} V(t)` on `0 < x = √(3t/c') ≤ x_c = ξ_*/2`;
* `lemma_S2_W`: for every `g ∈ TestClass prob (c'/12)` the Mellin integral `Mg(w/2 + c'ω)` converges
  absolutely and `|m_g(w/2 + c'ω)| ≤ C e^{c' B(ω)} M[g]`.

Proof (not the one-point derivative argument of the weight-one file `ComplexBessel.LemmaS2`).  The
kernel over `V` is `K₀ e^{-c' D(x_*, x)} 2π/(√x ρ(x))` with `x_* = 3 Re ω/π`, where `ρ(x) = V/((2x)^{w-1}
A_s(c' L(x)))` lies in `[c_Q/2, C_Q + c_Q/2]` for `x ≥ x_c` by the weight-`w` Cardy asymptote (W3)
(`kernel_div_eq_W`: the factor `(2x)^{w-1}` cancels the Stirling prefactor identically).  On `x ≥ x_c`
this is bounded since `D ≥ 0`.  On `t ≤ t(x_c)` the function `f(s) = (Re z - 1) s - log V(e^s)` is
concave (`cardyV_log_convex`), and `f(log t(x_c)) ≤ f(log t(X))` at the fixed point `X = 3μ₀/π > x_c`
because `D(y, x_c) - D(y, X) ≥ D(X, x_c) > 0` for `y = x_* ≥ X`; hence `f(s) ≤ f(log t(x_c))` for
`s ≤ log t(x_c)`, and the kernel over `V` is bounded by its value at `x_c`, which carries
`e^{-c' D(x_*, x_c)} ≤ e^{-κ c'}`, `κ = D(3μ₀/π, x_c) > 0`.  The small-`t` floor `V ≥ c₀ t^{p₀}` is not
needed because `log V(e^s)` is convex on all of `ℝ`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing WeightAxioms ComplexBessel

/-! ### Section 1: Concavity (three-point lemma) -/

/-- If `g` is convex and `α s - g s` does not decrease from `s_c` to `s_X > s_c`, then it does not
exceed its value at `s_c` anywhere to the left of `s_c`. -/
lemma concave_three_point {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g) (α : ℝ) {s sc sX : ℝ}
    (h1 : s ≤ sc) (h2 : sc < sX) (hX : α * sc - g sc ≤ α * sX - g sX) :
    α * s - g s ≤ α * sc - g sc := by
  rcases h1.eq_or_lt with rfl | hlt
  · exact le_rfl
  have hd : 0 < sX - s := by linarith
  set a : ℝ := (sX - sc) / (sX - s) with ha
  set b : ℝ := (sc - s) / (sX - s) with hb
  have ha0 : 0 < a := div_pos (by linarith) hd
  have hb0 : 0 < b := div_pos (by linarith) hd
  have hab : a + b = 1 := by rw [ha, hb, ← add_div]; field_simp; ring
  have hsc : a • s + b • sX = sc := by
    simp only [smul_eq_mul, ha, hb]; field_simp; ring
  have hconv := hg.2 (mem_univ s) (mem_univ sX) ha0.le hb0.le hab
  rw [hsc, smul_eq_mul, smul_eq_mul] at hconv
  have hlin : α * sc = a * (α * s) + b * (α * sX) := by
    rw [← hsc]; simp only [smul_eq_mul]; ring
  have hXm := mul_le_mul_of_nonneg_left hX hb0.le
  have hb' : b = 1 - a := by linarith
  rw [hb'] at hXm hlin hconv
  have h3 : a * (α * s - g s) ≤ a * (α * sc - g sc) := by nlinarith
  exact le_of_mul_le_mul_left h3 ha0

/-! ### Section 2: The Legendre divergence -/

lemma crudeDivergenceD_sub {y x X : ℝ} (hy : 0 < y) (hx : 0 < x) (hX : 0 < X) :
    crudeDivergenceD y x - crudeDivergenceD y X =
      (2 * Real.pi / 3) * ((x - X) + y * Real.log (X / x)) := by
  unfold crudeDivergenceD
  rw [Real.log_div hx.ne' hy.ne', Real.log_div hX.ne' hy.ne', Real.log_div hX.ne' hx.ne']
  ring

lemma crudeDivergenceD_self {y : ℝ} (hy : 0 < y) : crudeDivergenceD y y = 0 := by
  unfold crudeDivergenceD
  rw [div_self hy.ne', Real.log_one]; ring

lemma crudeDivergenceD_pos {y x : ℝ} (hy : 0 < y) (hx : 0 < x) (hne : x ≠ y) :
    0 < crudeDivergenceD y x := by
  unfold crudeDivergenceD
  have hq : x / y ≠ 1 := by
    intro h; apply hne; field_simp at h; exact h
  have hlog := Real.log_lt_sub_one_of_pos (div_pos hx hy) hq
  have h2 : y * Real.log (x / y) < x - y := by
    have := mul_lt_mul_of_pos_left hlog hy
    calc y * Real.log (x / y) < y * (x / y - 1) := this
      _ = x - y := by field_simp
  have : 0 < x - y - y * Real.log (x / y) := by linarith
  positivity

/-- For `0 < x_c < X ≤ y`: `D(y, x_c) - D(y, X) ≥ D(X, x_c)`. -/
lemma crudeDivergenceD_gap {xc X y : ℝ} (hxc : 0 < xc) (hlt : xc < X) (hy : X ≤ y) :
    crudeDivergenceD X xc ≤ crudeDivergenceD y xc - crudeDivergenceD y X := by
  have hX : 0 < X := hxc.trans hlt
  have hy0 : 0 < y := hX.trans_le hy
  rw [crudeDivergenceD_sub hy0 hxc hX]
  have h0 := crudeDivergenceD_sub hX hxc hX
  rw [crudeDivergenceD_self hX, sub_zero] at h0
  rw [h0]
  have hlog : 0 < Real.log (X / xc) := Real.log_pos ((one_lt_div hxc).mpr hlt)
  have hmul : X * Real.log (X / xc) ≤ y * Real.log (X / xc) :=
    mul_le_mul_of_nonneg_right hy hlog.le
  have hpi : 0 < 2 * Real.pi / 3 := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) hpi.le

/-! ### Section 3: Bounds for the Cardy asymptote ratio `ρ` -/

/-- For `x ≥ x_c` and `c'` large the ratio `ρ(x) = V/((2x)^{w-1} A_s(c' L(x)))` lies in
`[c_Q/2, C_Q + c_Q/2]` (weight-`w` asymptote (W3)). -/
lemma rho_bounds {prob : FixedWeightProblem} (U : FixedWeightUniformAxioms prob) {c' : ℝ}
    (hc' : U.c₀ ≤ c') (hCV : 2 * U.C_V ≤ c' * U.c_Q) {x : ℝ} (hx : xiStar / 2 ≤ x) :
    U.c_Q / 2 ≤ prob.cardyV (c' / 12) (c' * x ^ 2 / 3) /
        ((2 * x) ^ (prob.w - 1) * Bessel.besselAs (c' * Bessel.besselL x)) ∧
      prob.cardyV (c' / 12) (c' * x ^ 2 / 3) /
        ((2 * x) ^ (prob.w - 1) * Bessel.besselAs (c' * Bessel.besselL x)) ≤
        U.C_Q + U.c_Q / 2 := by
  have hc'1 : 1 ≤ c' := (le_max_left _ _).trans (U.hc₀_ge.trans hc')
  have hc'pos : 0 < c' := by linarith
  have h1 := (U.axioms_at hc').w3_real_asymp hx
  have h2 := (U.axioms_at hc').w3_Q_real_bounds hx
  rw [U.uniform_C_V hc'] at h1
  rw [U.uniform_c_Q hc', U.uniform_C_Q hc'] at h2
  have hsmall : U.C_V / c' ≤ U.c_Q / 2 := by
    rw [div_le_iff₀ hc'pos]; linarith
  change |prob.cardyV (c' / 12) (c' * x ^ 2 / 3) /
      ((2 * x) ^ (prob.w - 1) * Bessel.besselAs (c' * (2 * Real.pi * x / 3))) -
        ((U.axioms_at hc').Q_star (x : ℂ)).re| ≤ U.C_V / c' at h1
  have h3 := abs_le.mp (h1.trans hsmall)
  have hρ : prob.cardyV (c' / 12) (c' * x ^ 2 / 3) /
      ((2 * x) ^ (prob.w - 1) * Bessel.besselAs (c' * Bessel.besselL x)) =
      prob.cardyV (c' / 12) (c' * x ^ 2 / 3) /
        ((2 * x) ^ (prob.w - 1) * Bessel.besselAs (c' * (2 * Real.pi * x / 3))) := rfl
  rw [hρ]
  constructor <;> linarith [h2.1, h2.2.1, h2.2.2]

/-! ### Section 4: Pointwise kernel bound -/

/-- The modulus of the Mellin kernel `(2π)^z t^{z-1}/Γ(z)` is `(‖(2π)^z‖/‖Γ(z)‖) t^{Re z - 1}`. -/
lemma norm_kernel_eq_rpow (z : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖(2 * (Real.pi : ℂ)) ^ z * (u : ℂ) ^ (z - 1) / Complex.Gamma z‖ =
      (‖(2 * (Real.pi : ℂ)) ^ z‖ / ‖Complex.Gamma z‖) * u ^ (z.re - 1) := by
  rw [norm_div, norm_mul]
  have hcpow : ‖(u : ℂ) ^ (z - 1)‖ = u ^ (z.re - 1) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'), Complex.norm_exp,
      (Complex.ofReal_log hu.le).symm, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.one_re, zero_mul, sub_zero, Real.rpow_def_of_pos hu, mul_comm]
  rw [hcpow]; ring

/-- **Kernel bound (`vlo:S2`, pointwise form)**: for `μ₀ > π ξ_*/6` there are `C, κ > 0` and `c₀` such
that for `c' ≥ c₀`, `Re ω ≥ μ₀`, `z = w/2 + c' ω` and every `t > 0`,
`|(2π)^z t^{z-1}/Γ(z)| ≤ C e^{c' B(ω)} V(t)`, and if moreover `√(3t/c') ≤ ξ_*/2` (the sub-Cardy
region) the kernel is at most `C e^{c' B(ω)} e^{-κ c'} V(t)`. -/
theorem kernelBound_W (prob : FixedWeightProblem) {μ₀ : ℝ} (hμ₀ : Real.pi * xiStar / 6 < μ₀) :
    ∃ C κ c₀ : ℝ, 0 < C ∧ 0 < κ ∧ max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {ω : ℂ}, μ₀ ≤ ω.re → ∀ {t : ℝ}, 0 < t →
        ‖(2 * (Real.pi : ℂ)) ^ ((prob.w : ℂ) / 2 + (c' : ℂ) * ω) *
            (t : ℂ) ^ ((prob.w : ℂ) / 2 + (c' : ℂ) * ω - 1) /
            Complex.Gamma ((prob.w : ℂ) / 2 + (c' : ℂ) * ω)‖ ≤
          C * Real.exp (c' * crudeExponentB ω) * prob.cardyV (c' / 12) t ∧
        (√(3 * t / c') ≤ xiStar / 2 →
          ‖(2 * (Real.pi : ℂ)) ^ ((prob.w : ℂ) / 2 + (c' : ℂ) * ω) *
              (t : ℂ) ^ ((prob.w : ℂ) / 2 + (c' : ℂ) * ω - 1) /
              Complex.Gamma ((prob.w : ℂ) / 2 + (c' : ℂ) * ω)‖ ≤
            C * Real.exp (c' * crudeExponentB ω) * Real.exp (-κ * c') *
              prob.cardyV (c' / 12) t) := by
  obtain ⟨U⟩ := fixedWeightAxioms_of_problem prob
  have hw := prob.hw
  set xc : ℝ := xiStar / 2 with hxc_def
  have hxc : 0 < xc := by have := xiStar_pos; positivity
  have hμ0pos : 0 < μ₀ := by nlinarith [Real.pi_pos, xiStar_pos]
  set X : ℝ := 3 * μ₀ / Real.pi with hX_def
  have hX : 0 < X := by positivity
  have hXgt : xc < X := by
    rw [hX_def, lt_div_iff₀ Real.pi_pos, hxc_def]; linarith
  set κ : ℝ := crudeDivergenceD X xc with hκ_def
  have hκ : 0 < κ := crudeDivergenceD_pos hX hxc hXgt.ne
  set cQ : ℝ := U.c_Q with hcQ_def
  set CQ : ℝ := U.C_Q with hCQ_def
  have hcQ : 0 < cQ := U.hcQ_pos
  have hCQ : cQ ≤ CQ := U.hcQ_le
  set e : ℝ := ((prob.w : ℝ) - 1) / 2 with he_def
  have he : 0 ≤ e := by
    have : (1 : ℝ) ≤ prob.w := by exact_mod_cast hw
    rw [he_def]; linarith
  set K1 : ℝ := √xc * cQ / (2 * √X * (CQ + cQ / 2)) with hK1_def
  have hsxc : 0 < √xc := Real.sqrt_pos.mpr hxc
  have hsX : 0 < √X := Real.sqrt_pos.mpr hX
  have hCQpos : 0 < CQ + cQ / 2 := by linarith
  have hK1 : 0 < K1 := by
    rw [hK1_def]; exact div_pos (mul_pos hsxc hcQ) (mul_pos (mul_pos two_pos hsX) hCQpos)
  set c₁ : ℝ := |Real.log K1| / κ with hc₁_def
  set cstar : ℝ := max U.c₀ (max (2 * U.C_V / cQ) (max c₁ (1 / μ₀))) with hcstar_def
  set Cs : ℝ := Real.exp (stirlingConstW prob.w) * (Real.pi / (6 * μ₀)) ^ e *
    (4 * Real.pi / (cQ * √xc)) with hCs_def
  have hCs : 0 < Cs := by rw [hCs_def]; positivity
  refine ⟨Cs, κ, cstar, hCs, hκ, (U.hc₀_ge.trans (le_max_left _ _)), ?_⟩
  intro c' hc' ω hω t ht
  have hc'U : U.c₀ ≤ c' := (le_max_left _ _).trans hc'
  have hc'CV : 2 * U.C_V / cQ ≤ c' :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hc'
  have hc'1 : c₁ ≤ c' :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hc'
  have hc'μ : 1 / μ₀ ≤ c' :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hc'
  have hc'pos : 0 < c' := by
    have := (le_max_left _ _).trans (U.hc₀_ge.trans hc'U)
    linarith
  have hCV : 2 * U.C_V ≤ c' * cQ := by
    rw [div_le_iff₀ hcQ] at hc'CV; exact hc'CV
  have haS : prob.totalShift ≤ c' / 12 := (U.axioms_at hc'U).ha_shift
  have hω_pos : 0 < ω.re := hμ0pos.trans_le hω
  have hω_norm : μ₀ ≤ ‖ω‖ := hω.trans (Complex.re_le_norm ω)
  have hcω1 : 1 ≤ c' * ‖ω‖ := by
    have h1 : 1 ≤ c' * μ₀ := by
      rw [div_le_iff₀ hμ0pos] at hc'μ; linarith
    calc (1 : ℝ) ≤ c' * μ₀ := h1
      _ ≤ c' * ‖ω‖ := mul_le_mul_of_nonneg_left hω_norm hc'pos.le
  set z : ℂ := (prob.w : ℂ) / 2 + (c' : ℂ) * ω with hz_def
  have hz_re_pos : 0 < z.re := by
    simp only [hz_def, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re,
      Complex.re_ofReal_mul]
    have : (1 : ℝ) ≤ prob.w := by exact_mod_cast hw
    linarith [mul_pos hc'pos hω_pos]
  have hgam_ne : Complex.Gamma z ≠ 0 :=
    Complex.Gamma_ne_zero (fun n hn => by
      have : z.re = -(n : ℝ) := by rw [hn]; simp
      linarith [Nat.cast_nonneg (α := ℝ) n])
  have h2piz_ne : (2 * (Real.pi : ℂ)) ^ z ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')))
  have hVpos : ∀ {u : ℝ}, 0 < u → 0 < prob.cardyV (c' / 12) u :=
    fun {u} hu => prob.cardyV_pos haS hu
  -- the constant `K₀`
  set K0 : ℝ := ‖(stirlingSW prob.w c' ω)⁻¹‖ * (Real.pi / (6 * ‖ω‖)) ^ e *
    Real.exp (c' * crudeExponentB ω) with hK0_def
  have hK0_nn : 0 ≤ K0 := by rw [hK0_def]; positivity
  have hK0_le : K0 ≤ Real.exp (stirlingConstW prob.w) * (Real.pi / (6 * μ₀)) ^ e *
      Real.exp (c' * crudeExponentB ω) := by
    rw [hK0_def]
    have hS := norm_stirlingSW_inv_le hw hc'pos hω_pos.le hcω1
    have hP : (Real.pi / (6 * ‖ω‖)) ^ e ≤ (Real.pi / (6 * μ₀)) ^ e := by
      apply Real.rpow_le_rpow (by positivity) _ he
      exact div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (by linarith)
    gcongr
  -- formula for the kernel over `V` for `x ≥ x_c`
  set y : ℝ := 3 * ω.re / Real.pi with hy_def
  have hy : X ≤ y := by
    rw [hy_def, hX_def]
    exact div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le
  have hy0 : 0 < y := hX.trans_le hy
  have hpt : ∀ {x : ℝ}, xc ≤ x →
      ‖(2 * (Real.pi : ℂ)) ^ z * ((c' * x ^ 2 / 3 : ℝ) : ℂ) ^ (z - 1) / Complex.Gamma z‖ /
          prob.cardyV (c' / 12) (c' * x ^ 2 / 3) =
        K0 * Real.exp (-c' * crudeDivergenceD y x) *
          (2 * Real.pi / (√x * (prob.cardyV (c' / 12) (c' * x ^ 2 / 3) /
            ((2 * x) ^ (prob.w - 1) * Bessel.besselAs (c' * Bessel.besselL x))))) := by
    intro x hx
    have hx0 : 0 < x := hxc.trans_le hx
    have ht0 : 0 < c' * x ^ 2 / 3 := by positivity
    have hsq : √(3 * (c' * x ^ 2 / 3) / c') = x := by
      rw [show 3 * (c' * x ^ 2 / 3) / c' = x ^ 2 by field_simp, Real.sqrt_sq hx0.le]
    have hρ := rho_bounds U hc'U hCV hx
    have hρpos : 0 < prob.cardyV (c' / 12) (c' * x ^ 2 / 3) /
        ((2 * x) ^ (prob.w - 1) * Bessel.besselAs (c' * Bessel.besselL x)) :=
      lt_of_lt_of_le (by positivity) hρ.1
    have hden_ne : (2 * x) ^ (prob.w - 1) * Bessel.besselAs (c' * Bessel.besselL x) ≠ 0 := by
      have : 0 < Bessel.besselAs (c' * Bessel.besselL x) := by
        unfold Bessel.besselAs Bessel.besselL
        positivity
      positivity
    have hVeq : prob.cardyV (c' / 12) (c' * x ^ 2 / 3) =
        (prob.cardyV (c' / 12) (c' * x ^ 2 / 3) /
          ((2 * x) ^ (prob.w - 1) * Bessel.besselAs (c' * Bessel.besselL x))) *
          ((2 * x) ^ (prob.w - 1) * Bessel.besselAs (c' * Bessel.besselL x)) :=
      (div_mul_cancel₀ _ hden_ne).symm
    have := kernel_div_eq_W hw hc'pos hω_pos ht0 hρpos
      (V := prob.cardyV (c' / 12) (c' * x ^ 2 / 3)) (by rw [hsq]; exact hVeq)
    rw [hsq] at this
    rw [← hz_def] at this
    rw [this]
  -- bounds of the kernel over `V` for `x ≥ x_c`
  have hbound_x : ∀ {x : ℝ}, xc ≤ x →
      ‖(2 * (Real.pi : ℂ)) ^ z * ((c' * x ^ 2 / 3 : ℝ) : ℂ) ^ (z - 1) / Complex.Gamma z‖ /
          prob.cardyV (c' / 12) (c' * x ^ 2 / 3) ≤
        K0 * Real.exp (-c' * crudeDivergenceD y x) * (4 * Real.pi / (cQ * √xc)) := by
    intro x hx
    rw [hpt hx]
    have hx0 : 0 < x := hxc.trans_le hx
    have hρ := rho_bounds U hc'U hCV hx
    have hsx : 0 < √x := Real.sqrt_pos.mpr hx0
    have hsxc_le : √xc ≤ √x := Real.sqrt_le_sqrt hx
    have hden : cQ * √xc / 2 ≤ √x * (prob.cardyV (c' / 12) (c' * x ^ 2 / 3) /
        ((2 * x) ^ (prob.w - 1) * Bessel.besselAs (c' * Bessel.besselL x))) := by
      calc cQ * √xc / 2 = √xc * (cQ / 2) := by ring
        _ ≤ √x * (cQ / 2) := by gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_left hρ.1 hsx.le
    have hfrac : 2 * Real.pi / (√x * (prob.cardyV (c' / 12) (c' * x ^ 2 / 3) /
        ((2 * x) ^ (prob.w - 1) * Bessel.besselAs (c' * Bessel.besselL x)))) ≤
        4 * Real.pi / (cQ * √xc) := by
      calc _ ≤ 2 * Real.pi / (cQ * √xc / 2) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity) hden
        _ = 4 * Real.pi / (cQ * √xc) := by field_simp; ring
    gcongr
  -- comparison of `t(x_c)` and `t(X)`
  set tc : ℝ := c' * xc ^ 2 / 3 with htc_def
  set tX : ℝ := c' * X ^ 2 / 3 with htX_def
  have htc : 0 < tc := by positivity
  have htcX : tc < tX := by
    rw [htc_def, htX_def]
    have : xc ^ 2 < X ^ 2 := pow_lt_pow_left₀ hXgt hxc.le two_ne_zero
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left this hc'pos) three_pos
  have hexpκ : Real.exp (-(c' * κ)) ≤ K1 := by
    have hmul : |Real.log K1| ≤ c' * κ := by
      have : |Real.log K1| / κ ≤ c' := hc'1
      rw [div_le_iff₀ hκ] at this; linarith
    calc Real.exp (-(c' * κ)) ≤ Real.exp (Real.log K1) := by
          apply Real.exp_le_exp.mpr
          have := neg_abs_le (Real.log K1)
          linarith
      _ = K1 := Real.exp_log hK1
  have hcompare : ‖(2 * (Real.pi : ℂ)) ^ z * ((tc : ℝ) : ℂ) ^ (z - 1) / Complex.Gamma z‖ /
        prob.cardyV (c' / 12) tc ≤
      ‖(2 * (Real.pi : ℂ)) ^ z * ((tX : ℝ) : ℂ) ^ (z - 1) / Complex.Gamma z‖ /
        prob.cardyV (c' / 12) tX := by
    have hpc := hpt (le_refl xc)
    have hpX := hpt hXgt.le
    rw [← htc_def] at hpc
    rw [← htX_def] at hpX
    rw [hpc, hpX]
    have hρc := rho_bounds U hc'U hCV (le_refl xc)
    have hρX := rho_bounds U hc'U hCV hXgt.le
    rw [← htc_def] at hρc
    rw [← htX_def] at hρX
    set ρc := prob.cardyV (c' / 12) tc /
        ((2 * xc) ^ (prob.w - 1) * Bessel.besselAs (c' * Bessel.besselL xc)) with hρc_def
    set ρX := prob.cardyV (c' / 12) tX /
        ((2 * X) ^ (prob.w - 1) * Bessel.besselAs (c' * Bessel.besselL X)) with hρX_def
    have hgap := crudeDivergenceD_gap hxc hXgt hy
    rw [← hκ_def] at hgap
    have hexpD : Real.exp (-c' * crudeDivergenceD y xc) ≤
        Real.exp (-c' * crudeDivergenceD y X) * K1 := by
      have : -c' * crudeDivergenceD y xc ≤ -c' * crudeDivergenceD y X + -(c' * κ) := by
        have := mul_le_mul_of_nonneg_left hgap hc'pos.le
        linarith
      calc Real.exp (-c' * crudeDivergenceD y xc)
          ≤ Real.exp (-c' * crudeDivergenceD y X + -(c' * κ)) := Real.exp_le_exp.mpr this
        _ = Real.exp (-c' * crudeDivergenceD y X) * Real.exp (-(c' * κ)) := Real.exp_add _ _
        _ ≤ Real.exp (-c' * crudeDivergenceD y X) * K1 := by gcongr
    have hρcpos : 0 < ρc := lt_of_lt_of_le (by positivity) hρc.1
    have hρXpos : 0 < ρX := lt_of_lt_of_le (by positivity) hρX.1
    have hfc : 2 * Real.pi / (√xc * ρc) ≤ 4 * Real.pi / (cQ * √xc) := by
      calc 2 * Real.pi / (√xc * ρc) ≤ 2 * Real.pi / (√xc * (cQ / 2)) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left hρc.1 hsxc.le
        _ = 4 * Real.pi / (cQ * √xc) := by field_simp; ring
    have hfX : 2 * Real.pi / (√X * (CQ + cQ / 2)) ≤ 2 * Real.pi / (√X * ρX) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hρX.2 hsX.le
    have hK1fc : K1 * (4 * Real.pi / (cQ * √xc)) = 2 * Real.pi / (√X * (CQ + cQ / 2)) := by
      rw [hK1_def]; field_simp; ring
    have hK0e : 0 ≤ K0 := hK0_nn
    calc K0 * Real.exp (-c' * crudeDivergenceD y xc) * (2 * Real.pi / (√xc * ρc))
        ≤ K0 * (Real.exp (-c' * crudeDivergenceD y X) * K1) *
            (4 * Real.pi / (cQ * √xc)) := by
          gcongr
      _ = K0 * Real.exp (-c' * crudeDivergenceD y X) *
            (K1 * (4 * Real.pi / (cQ * √xc))) := by ring
      _ = K0 * Real.exp (-c' * crudeDivergenceD y X) *
            (2 * Real.pi / (√X * (CQ + cQ / 2))) := by rw [hK1fc]
      _ ≤ K0 * Real.exp (-c' * crudeDivergenceD y X) * (2 * Real.pi / (√X * ρX)) := by
          gcongr
  -- the function `f` and its concavity
  set α : ℝ := z.re - 1 with hα_def
  set A0 : ℝ := ‖(2 * (Real.pi : ℂ)) ^ z‖ / ‖Complex.Gamma z‖ with hA0_def
  have hA0 : 0 < A0 := by
    rw [hA0_def]
    exact div_pos (norm_pos_iff.mpr h2piz_ne) (norm_pos_iff.mpr hgam_ne)
  have hR : ∀ {u : ℝ}, 0 < u →
      ‖(2 * (Real.pi : ℂ)) ^ z * ((u : ℝ) : ℂ) ^ (z - 1) / Complex.Gamma z‖ /
          prob.cardyV (c' / 12) u =
        A0 * Real.exp (α * Real.log u - Real.log (prob.cardyV (c' / 12) u)) := by
    intro u hu
    rw [norm_kernel_eq_rpow z hu, Real.exp_sub, Real.exp_log (hVpos hu), mul_comm α,
      ← Real.rpow_def_of_pos hu]
    ring
  have hconv := cardyV_log_convex prob haS
  have hsub : ∀ {u : ℝ}, 0 < u → u ≤ tc →
      ‖(2 * (Real.pi : ℂ)) ^ z * ((u : ℝ) : ℂ) ^ (z - 1) / Complex.Gamma z‖ /
          prob.cardyV (c' / 12) u ≤
        ‖(2 * (Real.pi : ℂ)) ^ z * ((tc : ℝ) : ℂ) ^ (z - 1) / Complex.Gamma z‖ /
          prob.cardyV (c' / 12) tc := by
    intro u hu huc
    have hfX : α * Real.log tc - Real.log (prob.cardyV (c' / 12) tc) ≤
        α * Real.log tX - Real.log (prob.cardyV (c' / 12) tX) := by
      rw [hR htc, hR (htc.trans htcX)] at hcompare
      have := le_of_mul_le_mul_left hcompare hA0
      exact Real.exp_le_exp.mp this
    have hthree := concave_three_point
      (g := fun s : ℝ => Real.log (prob.cardyV (c' / 12) (Real.exp s))) hconv α
      (s := Real.log u) (sc := Real.log tc) (sX := Real.log tX)
      (Real.log_le_log hu huc) (Real.log_lt_log htc htcX)
      (by simpa only [Real.exp_log htc, Real.exp_log (htc.trans htcX)] using hfX)
    simp only [Real.exp_log hu, Real.exp_log htc] at hthree
    rw [hR hu, hR htc]
    gcongr
  -- the two bounds
  have hD_ge : κ ≤ crudeDivergenceD y xc := by
    have := crudeDivergenceD_gap hxc hXgt hy
    have h0 : 0 ≤ crudeDivergenceD y X := by
      have := crudeDivergenceD_pos hy0 hX
      unfold crudeDivergenceD
      have hlog : Real.log (X / y) ≤ X / y - 1 := Real.log_le_sub_one_of_pos (div_pos hX hy0)
      have hmul : y * Real.log (X / y) ≤ X - y := by
        calc y * Real.log (X / y) ≤ y * (X / y - 1) := mul_le_mul_of_nonneg_left hlog hy0.le
          _ = X - y := by field_simp
      have : 0 ≤ X - y - y * Real.log (X / y) := by linarith
      positivity
    linarith
  have hsubCardy : ∀ {u : ℝ}, 0 < u → u ≤ tc →
      ‖(2 * (Real.pi : ℂ)) ^ z * ((u : ℝ) : ℂ) ^ (z - 1) / Complex.Gamma z‖ /
          prob.cardyV (c' / 12) u ≤
        Cs * Real.exp (c' * crudeExponentB ω) * Real.exp (-κ * c') := by
    intro u hu huc
    refine (hsub hu huc).trans ?_
    have h1 := hbound_x (le_refl xc)
    rw [← htc_def] at h1
    refine h1.trans ?_
    have hexp : Real.exp (-c' * crudeDivergenceD y xc) ≤ Real.exp (-κ * c') := by
      apply Real.exp_le_exp.mpr
      linarith [mul_le_mul_of_nonneg_left hD_ge hc'pos.le]
    calc K0 * Real.exp (-c' * crudeDivergenceD y xc) * (4 * Real.pi / (cQ * √xc))
        ≤ (Real.exp (stirlingConstW prob.w) * (Real.pi / (6 * μ₀)) ^ e *
              Real.exp (c' * crudeExponentB ω)) * Real.exp (-κ * c') *
            (4 * Real.pi / (cQ * √xc)) := by
          gcongr
      _ = Cs * Real.exp (c' * crudeExponentB ω) * Real.exp (-κ * c') := by
          rw [hCs_def]; ring
  have hall : ∀ {u : ℝ}, 0 < u →
      ‖(2 * (Real.pi : ℂ)) ^ z * ((u : ℝ) : ℂ) ^ (z - 1) / Complex.Gamma z‖ /
          prob.cardyV (c' / 12) u ≤ Cs * Real.exp (c' * crudeExponentB ω) := by
    intro u hu
    have hexp1 : Real.exp (-κ * c') ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith [mul_pos hκ hc'pos]
    have hCe : 0 ≤ Cs * Real.exp (c' * crudeExponentB ω) := by positivity
    by_cases huc : u ≤ tc
    · calc _ ≤ Cs * Real.exp (c' * crudeExponentB ω) * Real.exp (-κ * c') := hsubCardy hu huc
        _ ≤ Cs * Real.exp (c' * crudeExponentB ω) * 1 := by gcongr
        _ = _ := mul_one _
    · replace huc := not_le.mp huc
      set x : ℝ := √(3 * u / c') with hx_def
      have hx0 : 0 < x := Real.sqrt_pos.mpr (by positivity)
      have hu_eq : u = c' * x ^ 2 / 3 := by
        rw [hx_def, Real.sq_sqrt (by positivity)]; field_simp
      have hxc_le : xc ≤ x := by
        by_contra hlt
        replace hlt := not_le.mp hlt
        have : c' * x ^ 2 / 3 < tc := by
          rw [htc_def]
          have : x ^ 2 < xc ^ 2 := pow_lt_pow_left₀ hlt hx0.le two_ne_zero
          exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left this hc'pos) three_pos
        linarith
      have h1 := hbound_x hxc_le
      rw [← hu_eq] at h1
      refine h1.trans ?_
      have hD_nn : 0 ≤ crudeDivergenceD y x := crudeDivergenceD_nonneg hy0 hx0
      have hexp : Real.exp (-c' * crudeDivergenceD y x) ≤ 1 := by
        rw [Real.exp_le_one_iff]; linarith [mul_nonneg hc'pos.le hD_nn]
      calc K0 * Real.exp (-c' * crudeDivergenceD y x) * (4 * Real.pi / (cQ * √xc))
          ≤ K0 * 1 * (4 * Real.pi / (cQ * √xc)) := by gcongr
        _ ≤ (Real.exp (stirlingConstW prob.w) * (Real.pi / (6 * μ₀)) ^ e *
              Real.exp (c' * crudeExponentB ω)) * (4 * Real.pi / (cQ * √xc)) := by
            rw [mul_one]; gcongr
        _ = Cs * Real.exp (c' * crudeExponentB ω) := by rw [hCs_def]; ring
  refine ⟨?_, ?_⟩
  · have := hall ht
    rw [div_le_iff₀ (hVpos ht)] at this
    exact this
  · intro hx_le
    have hut : t ≤ tc := by
      have hx0 : 0 ≤ √(3 * t / c') := Real.sqrt_nonneg _
      have hsq : t = c' * (√(3 * t / c')) ^ 2 / 3 := by
        rw [Real.sq_sqrt (by positivity)]; field_simp
      rw [hsq, htc_def]
      have : (√(3 * t / c')) ^ 2 ≤ xc ^ 2 := by
        exact pow_le_pow_left₀ hx0 hx_le 2
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this hc'pos.le) (by norm_num)
    have := hsubCardy ht hut
    rw [div_le_iff₀ (hVpos ht)] at this
    exact this

/-! ### Section 5: Lemma S2 at weight `w` -/

/-- **Lemma S2 at weight `w` (crude Legendre bound)** (`lower_o1_two_edge.tex`, `vlo:S2`):
for every fixed `μ₀ > π ξ_*/6` there exist `C > 0` and `c₀ ≥ max 1 (24 S)` such that for all `c' ≥ c₀`,
all `ω` with `Re ω ≥ μ₀`, and every `g ∈ TestClass prob (c'/12)`, the Mellin integral
`Mg(w/2 + c' ω)` converges absolutely and `‖m_g(w/2 + c' ω)‖ ≤ C exp(c' B(ω)) M[g]`. -/
theorem lemma_S2_W (prob : FixedWeightProblem) {μ₀ : ℝ} (hμ₀ : Real.pi * xiStar / 6 < μ₀) :
    ∃ C c₀ : ℝ, 0 < C ∧ max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {ω : ℂ}, μ₀ ≤ ω.re → ∀ {g : ℝ → ℝ},
        TestClass prob (c' / 12) g →
        IntegrableOn (fun t : ℝ => (g t : ℂ) *
            (t : ℂ) ^ (((prob.w : ℂ) / 2 + (c' : ℂ) * ω) - 1)) (Ioi 0) ∧
          ‖mellinMGW g ((prob.w : ℂ) / 2 + (c' : ℂ) * ω)‖ ≤
            C * Real.exp (c' * crudeExponentB ω) * prob.cardyNorm (c' / 12) g := by
  obtain ⟨C, κ, c₀, hC, hκ, hc₀, hker⟩ := kernelBound_W prob hμ₀
  refine ⟨C, c₀, hC, hc₀, fun {c'} hc' {ω} hω {g} hg => ?_⟩
  have hc'1 : 1 ≤ c' := (le_max_left _ _).trans (hc₀.trans hc')
  have hc'pos : 0 < c' := by linarith
  set z : ℂ := (prob.w : ℂ) / 2 + (c' : ℂ) * ω with hz_def
  have hμ0pos : 0 < μ₀ := by nlinarith [Real.pi_pos, xiStar_pos]
  have hz_re_pos : 0 < z.re := by
    have hw1 : (1 : ℝ) ≤ prob.w := by exact_mod_cast prob.hw
    simp only [hz_def, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re,
      Complex.re_ofReal_mul]
    linarith [mul_pos hc'pos (hμ0pos.trans_le hω)]
  have hgam_ne : Complex.Gamma z ≠ 0 :=
    Complex.Gamma_ne_zero (fun n hn => by
      have : z.re = -(n : ℝ) := by rw [hn]; simp
      linarith [Nat.cast_nonneg (α := ℝ) n])
  have h2piz_ne : (2 * (Real.pi : ℂ)) ^ z ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')))
  have hkb : ∀ t ∈ Ioi (0 : ℝ),
      ‖(2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z‖ ≤
        (C * Real.exp (c' * crudeExponentB ω)) * prob.cardyV (c' / 12) t := fun t ht =>
    (hker hc' hω (mem_Ioi.mp ht)).1
  have hmeas_mg : AEStronglyMeasurable
      (fun t : ℝ => (g t : ℂ) * ((2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z))
      (volume.restrict (Ioi 0)) := by
    have hcont_g : ContinuousOn (fun t : ℝ => (g t : ℂ)) (Ioi 0) :=
      Complex.continuous_ofReal.comp_continuousOn (hg.cont.mono Ioi_subset_Ici_self)
    have hcont_pow : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (z - 1)) (Ioi 0) := by
      intro t ht
      have hne : (t : ℂ) ∈ Complex.slitPlane :=
        Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using mem_Ioi.mp ht))
      exact ((Complex.continuous_ofReal.continuousAt.cpow continuousAt_const hne)).continuousWithinAt
    have hcont : ContinuousOn
        (fun t : ℝ => (g t : ℂ) * ((2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z))
        (Ioi 0) :=
      hcont_g.mul ((continuousOn_const.mul hcont_pow).div_const _)
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hint_mg : IntegrableOn
      (fun t : ℝ => (g t : ℂ) * ((2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z))
      (Ioi 0) := by
    refine Integrable.mono' (hg.int_cardy.const_mul (C * Real.exp (c' * crudeExponentB ω)))
      hmeas_mg ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hkb' := hkb t ht
    calc |g t| * ‖(2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z‖
        ≤ |g t| * ((C * Real.exp (c' * crudeExponentB ω)) * prob.cardyV (c' / 12) t) := by
          gcongr
      _ = C * Real.exp (c' * crudeExponentB ω) * (|g t| * prob.cardyV (c' / 12) t) := by ring
  have hint_g : IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioi 0) := by
    let fac : ℂ := Complex.Gamma z / (2 * (Real.pi : ℂ)) ^ z
    have heq : (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (z - 1)) =
        fun t : ℝ => fac *
          ((g t : ℂ) * ((2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z)) := by
      ext t; dsimp [fac]; field_simp [hgam_ne, h2piz_ne]
    rw [heq]
    exact hint_mg.const_mul fac
  refine ⟨hint_g, ?_⟩
  have hMG_eq : mellinMGW g z =
      ∫ t in Ioi (0 : ℝ),
        (g t : ℂ) * ((2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z) := by
    unfold mellinMGW mellinTransformW
    rw [div_eq_mul_inv, mul_comm _ (Complex.Gamma z)⁻¹, ← mul_assoc,
      mul_comm (Complex.Gamma z)⁻¹ _, ← integral_const_mul]
    congr 1; ext t; ring
  rw [hMG_eq]
  calc ‖∫ t in Ioi (0 : ℝ),
          (g t : ℂ) * ((2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z)‖
      ≤ ∫ t in Ioi (0 : ℝ),
          ‖(g t : ℂ) * ((2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ),
          (C * Real.exp (c' * crudeExponentB ω)) * (|g t| * prob.cardyV (c' / 12) t) := by
        refine setIntegral_mono_on hint_mg.norm
          (hg.int_cardy.const_mul (C * Real.exp (c' * crudeExponentB ω))) measurableSet_Ioi
          fun t ht => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc |g t| * ‖(2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z‖
            ≤ |g t| * ((C * Real.exp (c' * crudeExponentB ω)) * prob.cardyV (c' / 12) t) := by
              gcongr; exact hkb t ht
          _ = C * Real.exp (c' * crudeExponentB ω) * (|g t| * prob.cardyV (c' / 12) t) := by ring
    _ = C * Real.exp (c' * crudeExponentB ω) * prob.cardyNorm (c' / 12) g := by
        rw [integral_const_mul]; rfl

/-! ### Axiom verification -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.concave_three_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms concave_three_point

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.kernelBound_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernelBound_W

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_S2_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_S2_W

end FormalResearch.ModularBootstrap.FixedWeightBand
