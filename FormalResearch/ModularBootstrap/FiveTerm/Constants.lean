module

public import FormalResearch.ModularBootstrap.Constants

/-!
# Five-term constants `c_0^*`, `c_1^Langer`, `gamma_0`, `d_2^*` (Paper II, FIVE-0)

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex` (`cts:main`, `cts:langer`) and
`constant_term_universality.tex` (`ctu:main`, eq. `ctu:consts`).

The universal constants are `Λ_V`, `A_opt` and `c_1^Langer` (the Virasoro ones, valid at every
`(w,Q)`); the three `(w,Q)`-dependent coefficients are determined by the two odd jets `g_1`, `g_3`
of the logarithm of one outer function:

* `c_0^* = α_tip g_1`, `γ_0 = (3π/32)(g_3 - (7/15) g_1)`,
  `d_2^* = (2 c_0^*/A_opt) c_1^Langer - A_opt γ_0`   (`ctu:consts`).

The `(w,Q)` input enters only through `(g_1, g_3)`, so these are stated for arbitrary real jets
(`c0StarOf`, `gamma0Of`, `d2StarOf`), which is what a `FixedWeightProblem` instance (FIVE-W) supplies.
The Virasoro values are the closed forms of `cts:main` (`cts:g3-gamma0`), `c0Star`, `gamma0`, `d2Star`,
and are proved equal to the jet formulas at `g1Vir`, `g3Vir`.

All results are proved unconditionally (elementary algebra from the closed forms); the decimals quoted
in the paper are numerical and are not claimed here.
-/

@[expose] public section

open Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap

/-- `α_tip = ξ_* / (4√2)` (`cts:s4`). -/
noncomputable def alphaTip : ℝ := xiStar / (4 * √2)

/-- `α_C = ξ_* / (2√2 π) = (2/π) α_tip` (`cts:s4`). -/
noncomputable def alphaC : ℝ := xiStar / (2 * √2 * π)

lemma alphaC_eq_two_div_pi_mul_alphaTip : alphaC = 2 / π * alphaTip := by
  unfold alphaC alphaTip
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  have h2 : √2 ≠ 0 := by positivity
  field_simp
  ring

lemma alphaTip_pos : 0 < alphaTip := by
  unfold alphaTip; have := xiStar_pos; positivity

lemma alphaC_pos : 0 < alphaC := by
  unfold alphaC; have := xiStar_pos; have := Real.pi_pos; positivity

/-- First odd jet `g_1 = G_outer'(0) = 3 + 6/π - 16√2 ξ_*` of the Virasoro outer function
(`cts:g3-gamma0`). -/
noncomputable def g1Vir : ℝ := 3 + 6 / π - 16 * √2 * xiStar

/-- Third odd jet `g_3 = (1/6)(log G_outer)'''(0) = 7 - 18/π - (16√2/3) ξ_*` of the Virasoro outer
function (`cts:g3-gamma0`). -/
noncomputable def g3Vir : ℝ := 7 - 18 / π - 16 * √2 / 3 * xiStar

/-- `c_0^*(w,Q) = α_tip g_1` (`ctu:consts`), as a function of the first odd jet. -/
noncomputable def c0StarOf (g1 : ℝ) : ℝ := alphaTip * g1

/-- `γ_0(w,Q) = (3π/32)(g_3 - (7/15) g_1)` (`ctu:consts`), as a function of the odd jets. -/
noncomputable def gamma0Of (g1 g3 : ℝ) : ℝ := 3 * π / 32 * (g3 - 7 / 15 * g1)

/-- The Langer curvature coefficient
`c_1^Langer = (1/3 - π ξ_*/(45√2)) (|a_1|/β)^2` (`cts:langer-exp`). -/
noncomputable def c1Langer : ℝ := (1 / 3 - π * xiStar / (45 * √2)) * (|airyZero 1| / betaTip) ^ 2

/-- `d_2^*(w,Q) = (2 c_0^*/A_opt) c_1^Langer - A_opt γ_0` (`ctu:consts`), as a function of the jets. -/
noncomputable def d2StarOf (g1 g3 : ℝ) : ℝ :=
  2 * c0StarOf g1 / Aopt * c1Langer - Aopt * gamma0Of g1 g3

/-- Virasoro constant term, the closed form of `cts:main-eq`:
`c_0^* = (3/(4√2))(1 + 2/π) ξ_* - 4 ξ_*^2`. -/
noncomputable def c0Star : ℝ := 3 / (4 * √2) * (1 + 2 / π) * xiStar - 4 * xiStar ^ 2

/-- Virasoro affine saddle-phase slope, the closed form of `cts:g3-gamma0`:
`γ_0 = (21π - 78 + 8√2 π ξ_*)/40`. -/
noncomputable def gamma0 : ℝ := (21 * π - 78 + 8 * √2 * π * xiStar) / 40

/-- Virasoro coefficient of `c'^{-2/3}`: `d_2^* = (2 c_0^*/A_opt) c_1^Langer - A_opt γ_0`. -/
noncomputable def d2Star : ℝ := 2 * c0Star / Aopt * c1Langer - Aopt * gamma0

section algebra

private lemma sqrt2_sq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-- `c_0^* = α_tip g_1` at the Virasoro jets (`cts:main-eq`). -/
theorem c0Star_eq_alphaTip_mul_g1Vir : c0Star = alphaTip * g1Vir := by
  unfold c0Star alphaTip g1Vir
  have h2 : √2 ≠ 0 := by positivity
  have := sqrt2_sq
  field_simp
  nlinarith only [this]

theorem c0Star_eq_c0StarOf : c0Star = c0StarOf g1Vir := c0Star_eq_alphaTip_mul_g1Vir

/-- `γ_0 = (3π/32)(g_3 - (7/15)g_1)` at the Virasoro jets (`cts:g3-gamma0`). -/
theorem gamma0_eq_gamma0Of : gamma0 = gamma0Of g1Vir g3Vir := by
  unfold gamma0 gamma0Of g1Vir g3Vir
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  field_simp
  ring

theorem d2Star_eq_d2StarOf : d2Star = d2StarOf g1Vir g3Vir := by
  unfold d2Star d2StarOf
  rw [c0Star_eq_c0StarOf, gamma0_eq_gamma0Of]

end algebra

/-- `A_opt = (2/3) ξ_* · (|a_1|/β)`. -/
lemma Aopt_eq_mul_abs_airyZero_div_betaTip :
    Aopt = 2 / 3 * xiStar * (|airyZero 1| / betaTip) := by
  unfold Aopt cStar
  have hb : betaTip ≠ 0 := betaTip_pos.ne'
  field_simp

lemma Aopt_pos : 0 < Aopt := by
  rw [Aopt_eq_mul_abs_airyZero_div_betaTip]
  have h1 : airyZero 1 < 0 := airyZero_neg 1
  have := xiStar_pos
  have := betaTip_pos
  have := abs_pos.mpr h1.ne
  positivity

/-- `1/Λ_V = 1/12 + arsinh² 1 / (3π²)` (`cts:langer`(3)). -/
theorem inv_lambdaV_eq : 1 / lambdaV = 1 / 12 + Real.arsinh 1 ^ 2 / (3 * π ^ 2) := by
  have h := xiBar_eq_inv_lambdaV_sub
  have hxi : xiBar = Real.arsinh 1 ^ 2 / (3 * π ^ 2) := by
    unfold xiBar xiStar
    have hpi : π ≠ 0 := Real.pi_pos.ne'
    field_simp
  linarith

/-- `arsinh 1 < 1`. -/
lemma arsinh_one_lt_one : Real.arsinh 1 < 1 := by
  rw [← Real.sinh_lt_sinh, Real.sinh_arsinh]
  exact Real.self_lt_sinh_iff.mpr one_pos

/-- `c_1^Langer > 0`: the factor `1/3 - πξ_*/(45√2)` is positive because `π ξ_* = arsinh 1 < 1`. -/
theorem c1Langer_pos : 0 < c1Langer := by
  unfold c1Langer
  have hs : 0 < |airyZero 1| / betaTip := div_pos (abs_pos.mpr (airyZero_neg 1).ne) betaTip_pos
  have hxi : π * xiStar = Real.arsinh 1 := by
    unfold xiStar; field_simp
  have hA := arsinh_one_lt_one
  have hA0 : 0 < Real.arsinh 1 := by
    rw [← Real.sinh_lt_sinh, Real.sinh_zero, Real.sinh_arsinh]; exact one_pos
  have h2 : (1 : ℝ) < √2 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hfac : 0 < 1 / 3 - π * xiStar / (45 * √2) := by
    rw [hxi, sub_pos, div_lt_iff₀ (by positivity)]
    nlinarith only [hA, h2, hA0]
  positivity

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.c0Star_eq_alphaTip_mul_g1Vir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.c0Star_eq_alphaTip_mul_g1Vir

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.gamma0_eq_gamma0Of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.gamma0_eq_gamma0Of

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.d2Star_eq_d2StarOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.d2Star_eq_d2StarOf

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.c1Langer_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.c1Langer_pos

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.inv_lambdaV_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.inv_lambdaV_eq
