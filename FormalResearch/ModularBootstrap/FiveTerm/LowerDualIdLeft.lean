module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerDualContour
public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasFreezeWeps
public import FormalResearch.ModularBootstrap.FiveTerm.LowerEdgeAsymp
public import FormalResearch.ModularBootstrap.FiveTerm.PhaseLock
public import FormalResearch.ModularBootstrap.FiveTerm.OuterBridge

/-!
# Cauchy Dual Identity — Left Edge & Kernel Setup (`cts:dual-id`, Part 1)

Defines `phiDual`, `virasoroKedgeEps`, `virasoroKedge1Eps`, and reduces the left-edge
integral of `lowerDual_contour_eq` (`s = -i τ`) to the physical threshold integral over
`(c' * xiStar ^ 2 / 3, ∞)` with Bessel three-term error `O(M[g] / c'^2)`.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Integration
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.FixedWeightTip
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Saddle
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter
open FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

noncomputable section

/-! ### 1. Definitions of `φ(v; x')`, `K_edge^ε`, and `K_{edge,1}^ε` -/

/-- Dual edge saddle phase `φ(v; x') = (4π / 3) ∫₀^v (F(u) - x') du`. -/
def phiDual (v x' : ℝ) : ℝ :=
  (4 * π / 3) * ∫ u in (0 : ℝ)..v, (edgeF u - x')

/-- Inner factor of `K_edge^ε` (`cts:Kedge-eps`) evaluated at `v ≥ 0`. -/
def kedgeEpsIntegrand (c' ε x' v : ℝ) : ℂ :=
  lowerMt ε (Complex.I * (lowerY (edgeF v) : ℂ)) ^ 2 *
    Complex.exp (Complex.I * (thetaOut (lowerY (edgeF v)) : ℂ)) *
    ((((1 - Real.exp (-(4 * π * edgeF v))) ^ 2 / (1 - Real.exp (-(4 * π * x'))) ^ 2 *
      √(edgeF' v) : ℝ)) : ℂ) *
    Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))

/-- Dual edge kernel `K_edge^ε(x'; c')` (`cts:Kedge-eps`). -/
def virasoroKedgeEps (c' ε x' : ℝ) : ℝ :=
  -(√(2 * c' / 3)) *
    (Complex.exp (Complex.I * (π : ℂ) / 4) *
      ∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' v).re

/-- Subleading dual edge kernel `K_{edge,1}^ε(x'; c')` (`cts:Kedge-eps` with `(1 - 2iv)⁻¹`). -/
def virasoroKedge1Eps (c' ε x' : ℝ) : ℝ :=
  -(√(2 * c' / 3)) *
    (Complex.exp (Complex.I * (π : ℂ) / 4) *
      ∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' v *
        ((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹).re

/-- Normalization constant `π² √3 / (4 √2 √c' √ξ_* (1 - e^{-4πξ_*})²)` relating `lowerDualPsi`
and `cts:dual-id`. -/
def virasoroDualPref (c' : ℝ) : ℝ :=
  π ^ 2 * √3 / (4 * √2 * √c' * √xiStar * (1 - Real.exp (-(4 * π * xiStar))) ^ 2)

lemma virasoroDualPref_pos {c' : ℝ} (hc' : 0 < c') : 0 < virasoroDualPref c' := by
  have hpi := Real.pi_pos
  have hxi := xiStar_pos
  have hsub : 0 < 1 - Real.exp (-(4 * π * xiStar)) := by
    rw [sub_pos, Real.exp_lt_one_iff]; nlinarith
  unfold virasoroDualPref; positivity

/-! ### 2. Coordinate identities on `v = vT τ`, `x = xT τ`, `y = tanh(π τ / 4)` -/

lemma cosh_pi_mul_vT (τ : ℝ) : Real.cosh (π * vT τ) = √(Real.cosh (π * τ)) := by
  unfold vT
  rw [mul_div_cancel₀ _ Real.pi_pos.ne', Real.cosh_arsinh]
  congr 1
  rw [mul_pow, Real.sq_sqrt zero_le_two]
  linarith [cosh_eq_one_add_two_sinh_sq τ]

lemma edgeF_vT (τ : ℝ) : edgeF (vT τ) = xT τ := by
  unfold edgeF xT
  rw [cosh_pi_mul_vT]

lemma vT_nonneg {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ vT τ := by
  unfold vT
  refine div_nonneg (Real.arsinh_nonneg_iff.mpr ?_) Real.pi_pos.le
  exact mul_nonneg (Real.sqrt_nonneg 2) (Real.sinh_nonneg_iff.mpr (by positivity [Real.pi_pos]))

lemma vT_pos {τ : ℝ} (hτ : 0 < τ) : 0 < vT τ := by
  unfold vT
  refine div_pos (Real.arsinh_pos_iff.mpr ?_) Real.pi_pos
  exact mul_pos (Real.sqrt_pos.mpr zero_lt_two) (Real.sinh_pos_iff.mpr (by positivity [Real.pi_pos]))

lemma vTip_xT {τ : ℝ} (hτ : 0 ≤ τ) : vTip (xT τ) = vT τ := by
  have hx0 : xiStar ≤ xT τ := by
    rw [← xT_zero]
    rcases hτ.eq_or_lt with rfl | hp
    · exact le_rfl
    · exact (xT_strictMonoOn_Ici (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hτ) hp).le
  apply edgeF_strictMonoOn.injOn (vTip_nonneg hx0) (vT_nonneg hτ)
  rw [edgeF_vTip hx0, edgeF_vT]

/-- `y(xT τ) = tanh(π τ / 4)` for `τ ≥ 0`. -/
lemma lowerY_xT {τ : ℝ} (hτ : 0 ≤ τ) : lowerY (xT τ) = Real.tanh (π * τ / 4) := by
  set y := Real.tanh (π * τ / 4)
  have hy_nn : 0 ≤ y := by
    dsimp [y]; rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr (by positivity [Real.pi_pos])) (Real.cosh_pos _).le
  have hpi := Real.pi_pos
  have hcosh_x : Real.cosh (π * xT τ) = √2 * Real.cosh (π * τ / 2) := by
    unfold xT
    rw [mul_div_cancel₀ _ hpi.ne', Real.cosh_arsinh, Real.sq_sqrt (Real.cosh_pos _).le]
    have h1 := one_add_cosh_eq τ
    have hsq : √(1 + Real.cosh (π * τ)) = √2 * Real.cosh (π * τ / 2) := by
      rw [h1, Real.sqrt_mul zero_le_two, Real.sqrt_sq (Real.cosh_pos _).le]
    linarith [hsq]
  have hden : Real.cosh (π * xT τ) + √2 = 2 * √2 * Real.cosh (π * τ / 4) ^ 2 := by
    rw [hcosh_x, show π * τ / 2 = 2 * (π * τ / 4) by ring, cosh_two_mul_aux]
    ring
  have hnum : Real.cosh (π * xT τ) - √2 = 2 * √2 * Real.sinh (π * τ / 4) ^ 2 := by
    have hs := Real.cosh_sq (π * τ / 4)
    have hsub : Real.cosh (π * xT τ) - √2 = Real.cosh (π * xT τ) + √2 - 2 * √2 := by ring
    rw [hsub, hden]
    nlinarith [Real.sqrt_pos.mpr zero_lt_two]
  unfold lowerY
  rw [hnum, hden]
  have hs2 : √2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
  rw [show 2 * √2 * Real.sinh (π * τ / 4) ^ 2 / (2 * √2 * Real.cosh (π * τ / 4) ^ 2) =
      Real.tanh (π * τ / 4) ^ 2 by rw [Real.tanh_eq_sinh_div_cosh, div_pow]; field_simp]
  exact Real.sqrt_sq hy_nn

lemma vD_pos (τ : ℝ) : 0 < vD τ := by
  unfold vD; positivity [Real.cosh_pos (π * τ / 2), Real.cosh_pos (π * τ)]

lemma vD_le_one (τ : ℝ) : vD τ ≤ 1 := by
  unfold vD
  have hch : Real.cosh (π * τ / 2) ≤ √(Real.cosh (π * τ)) := by
    have h1 : Real.cosh (π * τ / 2) ^ 2 ≤ Real.cosh (π * τ) := by
      have h2 := cosh_eq_one_add_two_sinh_sq τ
      nlinarith [Real.cosh_sq (π * τ / 2), Real.one_le_cosh (π * τ / 2)]
    exact Real.le_sqrt_of_sq_le h1
  have hs2 : √2 ≤ 2 := by nlinarith [Real.sq_sqrt zero_le_two]
  rw [div_le_one (by positivity [Real.cosh_pos (π * τ)])]
  nlinarith [Real.cosh_pos (π * τ / 2)]

lemma continuous_vD : Continuous vD := by
  unfold vD
  exact (continuous_const.mul (Real.continuous_cosh.comp (continuous_const.mul continuous_id |>.div_const 2))).div
    (continuous_const.mul (Real.continuous_sqrt.comp (Real.continuous_cosh.comp (continuous_const.mul continuous_id))))
    fun τ => by positivity [Real.cosh_pos (π * τ)]

lemma tendsto_vT_atTop : Tendsto vT atTop atTop := by
  have hge : ∀ τ : ℝ, 0 ≤ τ → τ / 2 - Real.log 2 / π ≤ vT τ := fun τ _ => by
    unfold vT
    have hsinh : Real.exp (π * τ / 2) / 2 - 1 / 2 ≤ Real.sinh (π * τ / 2) := by
      rw [Real.sinh_eq]
      have : Real.exp (-(π * τ / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
      linarith
    have hs2 : 1 ≤ √2 := Real.one_le_sqrt.mpr (by norm_num)
    have hs_ge1 : 1 ≤ √(1 + (√2 * Real.sinh (π * τ / 2)) ^ 2) :=
      Real.one_le_sqrt.mpr (by linarith [sq_nonneg (√2 * Real.sinh (π * τ / 2))])
    have h1 : Real.exp (π * τ / 2) / 2 ≤ √2 * Real.sinh (π * τ / 2) + √(1 + (√2 * Real.sinh (π * τ / 2)) ^ 2) := by
      have hn : 0 ≤ Real.exp (π * τ / 2) / 2 - 1 / 2 := by
        have := Real.one_le_exp (by positivity [Real.pi_pos] : 0 ≤ π * τ / 2); linarith
      nlinarith
    have hlog : π * τ / 2 - Real.log 2 ≤ Real.arsinh (√2 * Real.sinh (π * τ / 2)) := by
      rw [Real.arsinh]
      calc π * τ / 2 - Real.log 2 = Real.log (Real.exp (π * τ / 2) / 2) := by
            rw [Real.log_div (Real.exp_pos _).ne' two_ne_zero, Real.log_exp]
        _ ≤ Real.log (√2 * Real.sinh (π * τ / 2) + √(1 + (√2 * Real.sinh (π * τ / 2)) ^ 2)) :=
            Real.log_le_log (by positivity) h1
    rw [le_div_iff₀ Real.pi_pos, sub_mul, div_mul_cancel₀ _ Real.pi_pos.ne']
    linarith [hlog]
  refine tendsto_atTop_mono' atTop ((eventually_ge_atTop 0).mono hge) ?_
  simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(Real.log 2 / π)) (tendsto_id.atTop_div_const zero_lt_two)

lemma xD_eq_edgeF'_mul_vD (τ : ℝ) : xD τ = edgeF' (vT τ) * vD τ := by
  have hd1 := hasDerivAt_xT τ
  have hd2 := ((hasDerivAt_edgeF (vT τ)).comp τ (hasDerivAt_vT τ)).congr_of_eventuallyEq
    (Eventually.of_forall fun t => (edgeF_vT t).symm)
  exact hd1.unique hd2

lemma phiDual_eq {v x' : ℝ} (hv : 0 ≤ v) :
    phiDual v x' = (4 * π / 3) * (edgeF v - x') * v - 2 * π * cumulN (edgeF v) := by
  let g : ℝ → ℝ := fun u =>
    phiDual u x' - ((4 * π / 3) * (edgeF u - x') * u - 2 * π * cumulN (edgeF u))
  have hg0 : g 0 = 0 := by
    dsimp [g, phiDual]
    simp [edgeF_zero, cumulN_xiStar]
  have hF_ge : ∀ u : ℝ, 0 ≤ u → xiStar ≤ edgeF u := fun u hu => by
    rw [← edgeF_zero]; exact edgeF_strictMonoOn.monotoneOn le_rfl hu hu
  have hg_cont : ContinuousOn g (Ici 0) := by
    have hcont1 : Continuous fun u => phiDual u x' := by
      unfold phiDual
      refine continuous_const.mul (intervalIntegral.continuous_primitive (fun a b => ?_) 0)
      exact ((continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeF t).continuousAt).sub
        continuous_const).intervalIntegrable a b
    have hcont2 : ContinuousOn (fun u => cumulN (edgeF u)) (Ici 0) :=
      continuousOn_cumulN.comp (continuous_iff_continuousAt.mpr fun t =>
        (hasDerivAt_edgeF t).continuousAt).continuousOn hF_ge
    have hcont3 : Continuous fun u => (4 * π / 3) * (edgeF u - x') * u :=
      (continuous_const.mul ((continuous_iff_continuousAt.mpr fun t =>
        (hasDerivAt_edgeF t).continuousAt).sub continuous_const)).mul continuous_id
    exact hcont1.continuousOn.sub (hcont3.continuousOn.sub (continuousOn_const.mul hcont2))
  have hg_deriv : ∀ u : ℝ, u ∈ Ioi 0 → HasDerivAt g 0 u := fun u hu => by
    have hu_pos : 0 < u := mem_Ioi.mp hu
    have hphi_deriv : HasDerivAt (fun w => phiDual w x') ((4 * π / 3) * (edgeF u - x')) u := by
      unfold phiDual
      refine (intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_).const_mul _
      · exact ((continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeF t).continuousAt).sub
          continuous_const).intervalIntegrable 0 u
      · exact ((continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeF t).continuousAt).sub
          continuous_const).stronglyMeasurableAtFilter _ _
      · exact (hasDerivAt_edgeF u).continuousAt.sub continuousAt_const
    have hFx_gt : xiStar < edgeF u := by
      rw [← edgeF_zero]; exact edgeF_strictMonoOn le_rfl hu_pos.le hu_pos
    have hN_deriv : HasDerivAt (fun w => cumulN (edgeF w))
        ((rhoU (edgeF u) / 2) * edgeF' u) u :=
      (hasDerivAt_cumulN hFx_gt).comp u (hasDerivAt_edgeF u)
    have hrho_eq : rhoU (edgeF u) = 4 / 3 * u := by
      have hv_eq : vTip (edgeF u) = u := by
        apply edgeF_strictMonoOn.injOn (vTip_nonneg hFx_gt.le) hu_pos.le
        rw [edgeF_vTip hFx_gt.le]
      have h1 := vTip_eq_rhoU hFx_gt.le
      linarith
    have hmid : HasDerivAt (fun w => (4 * π / 3) * (edgeF w - x') * w)
        ((4 * π / 3) * edgeF' u * u + (4 * π / 3) * (edgeF u - x') * 1) u :=
      (((hasDerivAt_edgeF u).sub_const x').const_mul (4 * π / 3)).mul (hasDerivAt_id u)
    refine (hphi_deriv.sub (hmid.sub (hN_deriv.const_mul (2 * π)))).congr_deriv ?_
    rw [hrho_eq]; ring
  rcases hv.eq_or_lt with rfl | hv_pos
  · linarith only [hg0]
  · obtain ⟨c, _, hc'⟩ := exists_hasDerivAt_eq_slope g (fun _ => (0 : ℝ)) hv_pos
      (hg_cont.mono (Icc_subset_Ici_self)) (fun u hu => hg_deriv u (Ioo_subset_Ioi_self hu))
    rw [hg0, sub_zero, eq_comm, div_eq_zero_iff] at hc'
    rcases hc' with h | h
    · dsimp [g] at h; linarith only [h]
    · exfalso; linarith only [hv_pos, h]

/-! ### 3. Outer multiplier `lowerMt` identity & Bessel `V` three-term difference -/

lemma virasoroV1_abs_le_30 {x : ℝ} (hx : xiStar / 2 ≤ x) :
    |virasoroV1 x| ≤ 30 := by
  have hx1 : (1 : ℝ) / 10 ≤ x := by linarith [Bessel.one_fifth_le_xiStar]
  have hpi := Real.pi_pos
  have hpi3 : 3 ≤ π := by linarith [Real.pi_gt_three]
  have hexp_mul1 : 4 * π * x * Real.exp (-4 * π * x) ≤ 1 := by
    have h := Real.add_one_le_exp (4 * π * x)
    rw [show -4 * π * x = -(4 * π * x) by ring, Real.exp_neg, ← div_eq_mul_inv,
      div_le_one (Real.exp_pos _)]
    linarith
  have hexp_mul2 : 8 * π * x * Real.exp (-8 * π * x) ≤ 1 := by
    have h := Real.add_one_le_exp (8 * π * x)
    rw [show -8 * π * x = -(8 * π * x) by ring, Real.exp_neg, ← div_eq_mul_inv,
      div_le_one (Real.exp_pos _)]
    linarith
  have hA : |3 / (16 * π * x) * (1 - Real.exp (-4 * π * x)) ^ 2| ≤ 1 := by
    have hexp1 : Real.exp (-4 * π * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hexp0 : 0 ≤ Real.exp (-4 * π * x) := (Real.exp_pos _).le
    have hsq : (1 - Real.exp (-4 * π * x)) ^ 2 ≤ 1 := by nlinarith
    have hden : 3 ≤ 16 * π * x := by nlinarith
    rw [abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul (div_le_one_of_le₀ hden (by positivity)) hsq (sq_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hB : |2 * Real.exp (-4 * π * x) * (3 - 12 * π * x)| ≤ 12 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have h1 : |3 - 12 * π * x| ≤ 3 + 12 * π * x :=
      (abs_sub _ _).trans (by rw [abs_of_pos (by positivity), abs_of_nonneg (by positivity)])
    calc 2 * Real.exp (-4 * π * x) * |3 - 12 * π * x|
        ≤ 2 * Real.exp (-4 * π * x) * (3 + 12 * π * x) := by gcongr
      _ = 6 * Real.exp (-4 * π * x) + 6 * (4 * π * x * Real.exp (-4 * π * x)) := by ring
      _ ≤ 6 * 1 + 6 * 1 := by gcongr; exact Real.exp_le_one_iff.mpr (by nlinarith)
      _ = 12 := by norm_num
  have hC : |Real.exp (-8 * π * x) * (6 - 48 * π * x)| ≤ 12 := by
    rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    have h1 : |6 - 48 * π * x| ≤ 6 + 48 * π * x :=
      (abs_sub _ _).trans (by rw [abs_of_pos (by positivity), abs_of_nonneg (by positivity)])
    calc Real.exp (-8 * π * x) * |6 - 48 * π * x|
        ≤ Real.exp (-8 * π * x) * (6 + 48 * π * x) := by gcongr
      _ = 6 * Real.exp (-8 * π * x) + 6 * (8 * π * x * Real.exp (-8 * π * x)) := by ring
      _ ≤ 6 * 1 + 6 * 1 := by gcongr; exact Real.exp_le_one_iff.mpr (by nlinarith)
      _ = 12 := by norm_num
  unfold virasoroV1
  calc |3 / (16 * π * x) * (1 - Real.exp (-4 * π * x)) ^ 2 -
        2 * Real.exp (-4 * π * x) * (3 - 12 * π * x) +
        Real.exp (-8 * π * x) * (6 - 48 * π * x)|
      ≤ (|3 / (16 * π * x) * (1 - Real.exp (-4 * π * x)) ^ 2| +
          |2 * Real.exp (-4 * π * x) * (3 - 12 * π * x)|) +
        |Real.exp (-8 * π * x) * (6 - 48 * π * x)| := (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ (1 + 12) + 12 := add_le_add (add_le_add hA hB) hC
    _ ≤ 30 := by norm_num

lemma besselAs_le_three_besselV {c' x : ℝ} (hc' : 10000 ≤ c') (hx : xiStar / 2 ≤ x) :
    Bessel.besselAs (c' * Bessel.besselL x) ≤ 3 * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) := by
  have hc0 : 0 < c' := by linarith
  have hx0 : 0 < x := by linarith [Bessel.one_fifth_le_xiStar]
  have hpi := Real.pi_pos
  have hV_nn : 0 ≤ Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) := by
    have hshift : virasoroProblem.totalShift ≤ c' / 12 := by rw [virasoroProblem_totalShift]; linarith
    rw [← Integration.virasoro_cardyV_eq_besselV (by linarith) (by positivity)]
    exact virasoroProblem.cardyV_nonneg hshift (by positivity)
  have hVpos : 0 < Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) := by
    by_contra h0
    have hV0 : Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) = 0 := le_antisymm (not_lt.mp h0) hV_nn
    have hbes1 := (Bessel.besselV_comparison hc' hx).1
    rw [hV0, div_zero] at hbes1
    have : 0 < 5 * π / 3 / √x := by positivity
    linarith
  have hbes := (Bessel.besselV_comparison hc' hx).2
  have hmul : 1 / √(c' * x ^ 2 / 3) * Real.exp (c' * Bessel.besselL x) ≤
      6 * π / √x * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) := by
    rwa [div_le_iff₀ hVpos] at hbes
  have ht_eq : √(c' * x ^ 2 / 3) = √(c' / 3) * x := by
    rw [show c' * x ^ 2 / 3 = (c' / 3) * x ^ 2 by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hx0.le]
  have hexp' : Real.exp (c' * Bessel.besselL x) ≤
      6 * π * √(c' / 3) * (x / √x) * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) := by
    have h1 := mul_le_mul_of_nonneg_right hmul (Real.sqrt_pos.mpr (by positivity : 0 < c' * x ^ 2 / 3)).le
    have lid : 1 / √(c' * x ^ 2 / 3) * Real.exp (c' * Bessel.besselL x) * √(c' * x ^ 2 / 3) =
        Real.exp (c' * Bessel.besselL x) := by field_simp
    rw [lid, ht_eq] at h1
    exact h1.trans_eq (by ring)
  have hAs_eq : Bessel.besselAs (c' * Bessel.besselL x) =
      √3 / (2 * π * √(c' * x)) * Real.exp (c' * Bessel.besselL x) := by
    unfold Bessel.besselAs Bessel.besselL
    rw [show 2 * π * (c' * (2 * π * x / 3)) = (2 * π) ^ 2 * (c' * x / 3) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
      show c' * x / 3 = (c' * x) / 3 by ring, Real.sqrt_div (by positivity)]
    field_simp
  rw [hAs_eq]
  have hxsq : √x * √x = x := Real.mul_self_sqrt hx0.le
  calc √3 / (2 * π * √(c' * x)) * Real.exp (c' * Bessel.besselL x)
      ≤ √3 / (2 * π * √(c' * x)) *
          (6 * π * √(c' / 3) * (x / √x) * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3)) := by gcongr
    _ = 3 * (√3 / √3) * (x / (√x * √x)) * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) := by
        rw [Real.sqrt_mul hc0.le x, Real.sqrt_div hc0.le]; field_simp; ring
    _ = 3 * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) := by
        rw [hxsq, div_self (Real.sqrt_pos.mpr (by positivity)).ne', div_self hx0.ne']; ring

lemma besselAs_sub_besselV_bound {c' x : ℝ} (hc' : 10000 ≤ c') (hx : xiStar / 2 ≤ x) :
    |Bessel.besselAs (c' * Bessel.besselL x) * (1 - Real.exp (-4 * π * x)) ^ 2 -
        Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) *
          (1 - virasoroV1 x / (c' * (1 - Real.exp (-4 * π * x)) ^ 2))| ≤
      1260000 / c' ^ 2 * Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) := by
  have hc0 : 0 < c' := by linarith
  have hx0 : 0 < x := by linarith [Bessel.one_fifth_le_xiStar]
  have hpi := Real.pi_pos
  have hx1 : (1 : ℝ) / 10 ≤ x := by linarith [Bessel.one_fifth_le_xiStar]
  have h4x : 1 ≤ 4 * π * x := by nlinarith [Real.pi_gt_three]
  have hexp_le : Real.exp (-4 * π * x) ≤ 1 / 2 := by
    rw [show -4 * π * x = -(4 * π * x) by ring, Real.exp_neg]
    calc (Real.exp (4 * π * x))⁻¹ ≤ (1 + 4 * π * x)⁻¹ :=
          inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp (4 * π * x)])
      _ ≤ 2⁻¹ := inv_anti₀ zero_lt_two (by linarith)
      _ = 1 / 2 := by norm_num
  have hq : 1 / 2 ≤ 1 - Real.exp (-4 * π * x) := by linarith
  have hqsq : 1 / 4 ≤ (1 - Real.exp (-4 * π * x)) ^ 2 := by nlinarith
  have hz0 : 0 < c' * Bessel.besselL x := by unfold Bessel.besselL; positivity
  have hApos : 0 < Bessel.besselAs (c' * Bessel.besselL x) := Bessel.besselAs_pos hz0
  have hV3 := besselV_three_term hc' hx
  set A := Bessel.besselAs (c' * Bessel.besselL x)
  set V := Bessel.besselV (c' / 12) (c' * x ^ 2 / 3)
  set d := (1 - Real.exp (-4 * π * x)) ^ 2
  set E := V - A * (d + virasoroV1 x / c')
  have hE : |E| ≤ 400000 / c' ^ 2 * A := by
    dsimp [E]
    have h1 : |V / A - (d + virasoroV1 x / c')| * A ≤ (400000 / c' ^ 2) * A :=
      mul_le_mul_of_nonneg_right hV3 hApos.le
    calc |V - A * (d + virasoroV1 x / c')|
        = |(V / A - (d + virasoroV1 x / c')) * A| := by
            rw [sub_mul, div_mul_cancel₀ _ hApos.ne']; ring_nf
      _ = |V / A - (d + virasoroV1 x / c')| * A := by rw [abs_mul, abs_of_pos hApos]
      _ ≤ 400000 / c' ^ 2 * A := h1
  have hid : A * d - V * (1 - virasoroV1 x / (c' * d)) =
      -E + (E + A * (virasoroV1 x / c')) * (virasoroV1 x / (c' * d)) := by
    dsimp [E]; field_simp [show d ≠ 0 by linarith]; ring
  have hV1 : |virasoroV1 x| ≤ 30 := virasoroV1_abs_le_30 hx
  have hvd : |virasoroV1 x / (c' * d)| ≤ 120 / c' := by
    rw [abs_div, abs_of_pos (mul_pos hc0 (by positivity))]
    calc |virasoroV1 x| / (c' * d) ≤ 30 / (c' * (1 / 4)) := by gcongr
      _ = 120 / c' := by ring
  have hA_bound : |A * d - V * (1 - virasoroV1 x / (c' * d))| ≤ 420000 / c' ^ 2 * A := by
    rw [hid]
    calc |-E + (E + A * (virasoroV1 x / c')) * (virasoroV1 x / (c' * d))|
        ≤ |E| + (|E| + A * (|virasoroV1 x| / c')) * |virasoroV1 x / (c' * d)| := by
          refine (abs_add_le _ _).trans (add_le_add (by rw [abs_neg]) ?_)
          rw [abs_mul]
          gcongr
          refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [abs_mul, abs_of_pos hApos, abs_div, abs_of_pos hc0]
      _ ≤ (400000 / c' ^ 2 * A) +
            ((400000 / c' ^ 2 * A) + A * (30 / c')) * (120 / c') := by gcongr
      _ = (400000 + 400000 * 120 / c' + 3600) / c' ^ 2 * A := by ring
      _ ≤ (400000 + 400000 * 120 / 10000 + 3600) / c' ^ 2 * A := by gcongr
      _ ≤ 420000 / c' ^ 2 * A := by
          have : (400000 + 400000 * 120 / 10000 + 3600 : ℝ) ≤ 420000 := by norm_num
          gcongr
  have hAs_le_V := besselAs_le_three_besselV hc' hx
  calc |A * d - V * (1 - virasoroV1 x / (c' * d))|
      ≤ 420000 / c' ^ 2 * A := hA_bound
    _ ≤ 420000 / c' ^ 2 * (3 * V) := by gcongr
    _ = 1260000 / c' ^ 2 * V := by ring

/-! ### 4. Left-edge reduction (`s = -i τ`) -/

private lemma lowerDualPsi_left_re_eq {c' ε : ℝ} (hc' : 0 < c') (hε : 0 ≤ ε)
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g) {τ : ℝ} (hτ : 0 < τ) :
    (lowerDualPsi c' ε 0 g (-((τ : ℂ) * Complex.I))).re =
      -virasoroDualPref c' * g (c' * xT τ ^ 2 / 3) *
        Bessel.besselAs (c' * Bessel.besselL (xT τ)) * (1 - Real.exp (-4 * π * xT τ)) ^ 2 *
        lowerWeps ε (lowerY (xT τ)) *
        Real.sin (lowerThetaEps Gout ε (lowerY (xT τ)) - 2 * π * c' * cumulN (xT τ)) *
        (2 * c' * xT τ / 3 * xD τ) := by
  let y : ℝ := Real.tanh (π * τ / 4)
  have hy_mem : y ∈ Ioo (0 : ℝ) 1 :=
    ⟨by dsimp [y]; rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (Real.sinh_pos_iff.mpr (by positivity [Real.pi_pos])) (Real.cosh_pos _),
      Real.tanh_lt_one _⟩
  have hy_eq : lowerY (xT τ) = y := lowerY_xT hτ.le
  have hz_eq : sTan (-((τ : ℂ) * Complex.I)) = -Complex.I * (y : ℂ) := by
    rw [show -((τ : ℂ) * Complex.I) = ((-τ : ℝ) : ℂ) * Complex.I by push_cast; ring, sTan_I_mul,
      show π * -τ / 4 = -(π * τ / 4) by ring, Real.tanh_neg]
    push_cast; simp [y]
  have h1z2_ne : (1 : ℂ) + sTan (-((τ : ℂ) * Complex.I)) ^ 2 ≠ 0 := by
    rw [hz_eq, mul_pow, neg_sq, Complex.I_sq]
    intro h; have hre := congrArg Complex.re h
    rw [show (1 : ℂ) + -1 * (y : ℂ) ^ 2 = ((1 - y ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re,
      Complex.zero_re] at hre
    nlinarith [hy_mem.1, hy_mem.2]
  have hm0 : lowerMt 0 (-Complex.I * (y : ℂ)) = 1 := by
    rw [← hz_eq]; unfold lowerMt; simp [h1z2_ne]
  have hb_eq : dualBStrip (-((τ : ℂ) * Complex.I)) = (xT τ : ℂ) := dualBStrip_imag_neg hτ
  have hG_eq : hankelContinuation c' g (xT τ : ℂ) = (g (c' * xT τ ^ 2 / 3) : ℂ) :=
    hankelContinuation_ofReal hc' hg (xT τ)
  have hΦ_eq : Complex.exp (-((c' : ℂ) * dualPhi0Strip (-((τ : ℂ) * Complex.I)))) =
      ((Real.exp (c' * Bessel.besselL (xT τ)) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((2 * π * c' * cumulN (xT τ) : ℝ) : ℂ)) := by
    rw [dualPhi0Strip_imag_neg hτ]
    have : -((c' : ℂ) * (-((Bessel.besselL (xT τ) : ℝ) : ℂ) -
        Complex.I * ((2 * π * cumulN (xT τ) : ℝ) : ℂ))) =
        ((c' * Bessel.besselL (xT τ) : ℝ) : ℂ) +
        Complex.I * ((2 * π * c' * cumulN (xT τ) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.exp_add, ← Complex.ofReal_exp]
  have hGout_conj : Gout (-Complex.I * (y : ℂ)) =
      ((‖Gout (Complex.I * (y : ℂ))‖ : ℝ) : ℂ) *
        Complex.exp (-Complex.I * (Complex.arg (Gout (Complex.I * (y : ℂ))) : ℂ)) := by
    have hc := gout_conj_closure (slit_mem_diff hy_mem)
    rw [show starRingEnd ℂ (Complex.I * (y : ℂ)) = -Complex.I * (y : ℂ) by
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal]] at hc
    rw [hc]
    nth_rewrite 1 [← Complex.norm_mul_exp_arg_mul_I (Gout (Complex.I * (y : ℂ)))]
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2; rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  have hGout_norm : ‖Gout (Complex.I * (y : ℂ))‖ = Wslit y := by
    rw [gout_polar hy_mem, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by
      unfold Wslit; positivity [xOf_pos hy_mem, xiStar_pos, show 0 < 1 - y ^ 2 by nlinarith [hy_mem.1, hy_mem.2]]),
      show Complex.I * (thetaOut y : ℂ) = (thetaOut y : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hM_conj : lowerMt ε (-Complex.I * (y : ℂ)) = starRingEnd ℂ (lowerMt ε (Complex.I * (y : ℂ))) := by
    rw [show -Complex.I * (y : ℂ) = starRingEnd ℂ (Complex.I * (y : ℂ)) by
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal], lowerMt_conj]
  have hM_sq : lowerMt ε (-Complex.I * (y : ℂ)) ^ 2 =
      ((lowerWeps ε y : ℝ) : ℂ) *
        Complex.exp (-Complex.I * ((2 * Complex.arg (lowerMt ε (Complex.I * (y : ℂ))) : ℝ) : ℂ)) := by
    rw [hM_conj, ← map_pow]
    nth_rewrite 1 [← Complex.norm_mul_exp_arg_mul_I (lowerMt ε (Complex.I * (y : ℂ)))]
    rw [mul_pow, ← Complex.ofReal_pow, ← Complex.exp_nat_mul, map_mul, Complex.conj_ofReal,
      ← Complex.exp_conj, show ‖lowerMt ε (Complex.I * (y : ℂ))‖ ^ 2 = lowerWeps ε y by rfl]
    congr 2; rw [map_mul, map_mul, map_natCast, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
  have h1z2 : (1 : ℂ) + (-Complex.I * (y : ℂ)) ^ 2 = ((1 - y ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, neg_sq, Complex.I_sq]; push_cast; ring
  have hphase_prod : (-Complex.I) *
      Complex.exp (Complex.I * ((2 * π * c' * cumulN (xT τ) : ℝ) : ℂ)) *
      Complex.exp (-Complex.I * (Complex.arg (Gout (Complex.I * (y : ℂ))) : ℂ)) *
      Complex.exp (-Complex.I * ((2 * Complex.arg (lowerMt ε (Complex.I * (y : ℂ))) : ℝ) : ℂ)) =
      (-Complex.I) * Complex.exp (-Complex.I * ((lowerThetaEps Gout ε y - 2 * π * c' * cumulN (xT τ) : ℝ) : ℂ)) := by
    rw [mul_assoc (-Complex.I), mul_assoc (-Complex.I), ← Complex.exp_add, ← Complex.exp_add]
    congr 2; unfold lowerThetaEps; push_cast; ring
  have hre_sin : ((-Complex.I) *
      Complex.exp (-Complex.I * ((lowerThetaEps Gout ε y - 2 * π * c' * cumulN (xT τ) : ℝ) : ℂ))).re =
      -Real.sin (lowerThetaEps Gout ε y - 2 * π * c' * cumulN (xT τ)) := by
    set α := lowerThetaEps Gout ε y - 2 * π * c' * cumulN (xT τ)
    rw [show -Complex.I * (α : ℂ) = ((-α : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.mul_re,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
    ring
  have hjacob := wslit_xD_identity hτ
  change y * Wslit y * (1 - y ^ 2) * (π / 4) =
    (π / (4 * √2 * √xiStar * (1 - Real.exp (-(4 * π * xiStar))) ^ 2)) *
      √(xT τ) * (1 - Real.exp (-(4 * π * xT τ))) ^ 2 * xD τ at hjacob
  have hAs_eq : √(xT τ) * Real.exp (c' * Bessel.besselL (xT τ)) =
      (π * √3 / √c') * Bessel.besselAs (c' * Bessel.besselL (xT τ)) * (2 * c' * xT τ / 3) := by
    unfold Bessel.besselAs Bessel.besselL
    have hpi := Real.pi_pos
    have hx := xT_pos τ
    rw [show 2 * π * (c' * (2 * π * xT τ / 3)) = (2 * π) ^ 2 * (c' * xT τ / 3) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
      show c' * xT τ / 3 = (c' * xT τ) / 3 by ring, Real.sqrt_div (by positivity),
      Real.sqrt_mul hc'.le (xT τ)]
    field_simp
    rw [Real.sq_sqrt hx.le, Real.sq_sqrt hc'.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  unfold lowerDualPsi
  dsimp only
  rw [hz_eq, hb_eq, hG_eq, hm0, one_pow, mul_one, hΦ_eq, hGout_conj, hGout_norm, hM_sq, h1z2]
  have hfac : (-Complex.I * (y : ℂ)) * (g (c' * xT τ ^ 2 / 3) : ℂ) *
      (((Real.exp (c' * Bessel.besselL (xT τ)) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((2 * π * c' * cumulN (xT τ) : ℝ) : ℂ))) *
      (((Wslit y : ℝ) : ℂ) *
        Complex.exp (-Complex.I * (Complex.arg (Gout (Complex.I * (y : ℂ))) : ℂ))) *
      (((lowerWeps ε y : ℝ) : ℂ) *
        Complex.exp (-Complex.I * ((2 * Complex.arg (lowerMt ε (Complex.I * (y : ℂ))) : ℝ) : ℂ))) *
      (((π / 4 : ℝ) : ℂ) * ((1 - y ^ 2 : ℝ) : ℂ)) =
      (((y * Wslit y * (1 - y ^ 2) * (π / 4) * g (c' * xT τ ^ 2 / 3) *
        Real.exp (c' * Bessel.besselL (xT τ)) * lowerWeps ε y : ℝ) : ℂ) *
        ((-Complex.I) * Complex.exp (-Complex.I *
          ((lowerThetaEps Gout ε y - 2 * π * c' * cumulN (xT τ) : ℝ) : ℂ)))) := by
    rw [← hphase_prod]; push_cast; ring
  rw [hfac, Complex.re_ofReal_mul, hre_sin, hy_eq, hjacob]
  rw [show -4 * π * xT τ = -(4 * π * xT τ) by ring]
  have hrw : (π / (4 * √2 * √xiStar * (1 - Real.exp (-(4 * π * xiStar))) ^ 2)) *
        √(xT τ) * (1 - Real.exp (-(4 * π * xT τ))) ^ 2 * xD τ *
        g (c' * xT τ ^ 2 / 3) * Real.exp (c' * Bessel.besselL (xT τ)) * lowerWeps ε y *
        (-Real.sin (lowerThetaEps Gout ε y - 2 * π * c' * cumulN (xT τ))) =
      -(π / (4 * √2 * √xiStar * (1 - Real.exp (-(4 * π * xiStar))) ^ 2)) *
        (√(xT τ) * Real.exp (c' * Bessel.besselL (xT τ))) * xD τ *
        g (c' * xT τ ^ 2 / 3) * (1 - Real.exp (-(4 * π * xT τ))) ^ 2 * lowerWeps ε y *
        Real.sin (lowerThetaEps Gout ε y - 2 * π * c' * cumulN (xT τ)) := by ring
  rw [hrw, hAs_eq]
  unfold virasoroDualPref
  have h1 : (√2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
  have h2 : √xiStar ≠ 0 := (Real.sqrt_pos.mpr xiStar_pos).ne'
  have h3 : √c' ≠ 0 := (Real.sqrt_pos.mpr hc').ne'
  have h4 : 1 - Real.exp (-(4 * π * xiStar)) ≠ 0 := by
    intro h; have : Real.exp (-(4 * π * xiStar)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, xiStar_pos])
    linarith [sub_eq_zero.mp h]
  field_simp

private lemma sin_lowerThetaEps_cont_eq {ε c' x : ℝ} (hε : 0 ≤ ε) (hx : xiStar < x) :
    Real.sin (lowerThetaEps Gout ε (lowerY x) - 2 * π * c' * cumulN x) =
      Real.sin (thetaOut (lowerY x) -
        2 * Real.arctan (ε * lowerY x / ((1 - lowerY x ^ 2) + ε)) - 2 * π * c' * cumulN x) := by
  rw [sin_lowerThetaEps_eq hε hx]
  unfold unwrappedTheta
  rw [← thetaOut_yOfX hx, one_sub_lowerY_sq hx]
  rfl

lemma change_of_vars_Ioi_xT {c' : ℝ} (hc' : 0 < c') (ha : 2 ≤ c' / 12)
    (H : ℝ → ℝ) (hH_cont : ContinuousOn H (Ici 0))
    (hHV_int : IntegrableOn (fun t => |H t| * Bessel.besselV (c' / 12) t) (Ioi 0))
    (F : ℝ → ℝ) (hF_cont : ContinuousOn F (Ici xiStar))
    (hF_bd : ∃ B : ℝ, ∀ x : ℝ, xiStar < x → |F x| ≤ B)
    (h_int_τ : IntegrableOn (fun τ : ℝ =>
      H (c' * xT τ ^ 2 / 3) * Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) *
        F (xT τ) * (2 * c' * xT τ / 3 * xD τ)) (Ioi 0)) :
    ∫ τ in Ioi (0 : ℝ),
        H (c' * xT τ ^ 2 / 3) * Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) *
          F (xT τ) * (2 * c' * xT τ / 3 * xD τ) =
      ∫ t in Ioi (c' * xiStar ^ 2 / 3),
        H t * Bessel.besselV (c' / 12) t * F (√(3 * t / c')) := by
  obtain ⟨B, hB⟩ := hF_bd
  have hshift : virasoroProblem.totalShift ≤ c' / 12 := by rw [virasoroProblem_totalShift]; linarith
  let φ : ℝ → ℝ := fun τ => c' * xT τ ^ 2 / 3
  let φ' : ℝ → ℝ := fun τ => 2 * c' * xT τ / 3 * xD τ
  set t₀ : ℝ := φ 0 with ht₀_def
  have ht₀_val : t₀ = c' * xiStar ^ 2 / 3 := by dsimp [t₀, φ]; rw [xT_zero]
  have ht₀_pos : 0 < t₀ := by rw [ht₀_val]; positivity [xiStar_pos]
  have hV_cont : ContinuousOn (Bessel.besselV (c' / 12)) (Ici 0) :=
    (continuous_cardyV virasoroProblem (c' / 12)).continuousOn.congr fun t ht =>
      (Integration.virasoro_cardyV_eq_besselV ha (mem_Ici.mp ht)).symm
  have h_int_t : IntegrableOn (fun t => H t * Bessel.besselV (c' / 12) t * F (√(3 * t / c'))) (Ioi t₀) := by
    refine ((hHV_int.mono_set (Ioi_subset_Ioi ht₀_pos.le)).const_mul (max B 0)).mono' ?_ ?_
    · have hcont_t : ContinuousOn (fun t => H t * Bessel.besselV (c' / 12) t * F (√(3 * t / c'))) (Ioi t₀) := by
        refine ((hH_cont.mono (Ioi_subset_Ici ht₀_pos.le)).mul (hV_cont.mono (Ioi_subset_Ici ht₀_pos.le))).mul ?_
        refine hF_cont.comp (Real.continuous_sqrt.continuousOn.comp
          ((continuousOn_const.mul continuousOn_id).div_const c') fun _ _ => mem_univ _) fun t ht => ?_
        have ht_gt : c' * xiStar ^ 2 / 3 < t := by linarith [ht₀_val, mem_Ioi.mp ht]
        have hx_lt : xiStar ≤ √(3 * t / c') := by
          simpa [Real.sqrt_sq xiStar_pos.le] using Real.sqrt_le_sqrt
            (show xiStar ^ 2 ≤ 3 * t / c' by rw [le_div_iff₀ hc']; linarith)
        exact hx_lt
      exact hcont_t.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht_gt : t₀ < t := mem_Ioi.mp ht
      have hx_lt : xiStar < √(3 * t / c') := by
        rw [ht₀_val] at ht_gt
        simpa [Real.sqrt_sq xiStar_pos.le] using Real.sqrt_lt_sqrt (sq_nonneg _)
          (show xiStar ^ 2 < 3 * t / c' by rw [lt_div_iff₀ hc']; linarith)
      have hV_nn : 0 ≤ Bessel.besselV (c' / 12) t := by
        rw [← Integration.virasoro_cardyV_eq_besselV ha (ht₀_pos.le.trans ht_gt.le)]
        exact virasoroProblem.cardyV_nonneg hshift (ht₀_pos.le.trans ht_gt.le)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hV_nn]
      calc |H t| * Bessel.besselV (c' / 12) t * |F (√(3 * t / c'))|
          ≤ |H t| * Bessel.besselV (c' / 12) t * max B 0 := by gcongr; exact (hB _ hx_lt).trans (le_max_left _ _)
        _ = max B 0 * (|H t| * Bessel.besselV (c' / 12) t) := by ring
  have hL : Tendsto (fun R : ℝ => ∫ τ in (0 : ℝ)..R,
      H (φ τ) * Bessel.besselV (c' / 12) (φ τ) * F (xT τ) * φ' τ) atTop
      (𝓝 (∫ τ in Ioi (0 : ℝ), H (φ τ) * Bessel.besselV (c' / 12) (φ τ) * F (xT τ) * φ' τ)) :=
    intervalIntegral_tendsto_integral_Ioi 0 h_int_τ tendsto_id
  have hφ_tend : Tendsto φ atTop atTop := by
    have hx_tend : Tendsto xT atTop atTop := by
      have : ∀ τ : ℝ, 0 ≤ τ → τ / 2 - Real.log 2 / π ≤ xT τ := fun τ _ => by
        unfold xT
        have hch : Real.exp (π * τ) / 2 ≤ Real.cosh (π * τ) := by
          rw [Real.cosh_eq]; have := Real.exp_pos (-(π * τ)); linarith
        have h1 : Real.exp (π * τ / 2) / √2 ≤ √(Real.cosh (π * τ)) := by
          have : (Real.exp (π * τ / 2) / √2) ^ 2 ≤ Real.cosh (π * τ) := by
            rw [div_pow, Real.sq_sqrt zero_le_two, ← Real.exp_nat_mul]; exact hch.trans_eq' (by congr 1; ring)
          exact Real.le_sqrt_of_sq_le this
        have h2 : Real.log (√(Real.cosh (π * τ))) ≤ Real.arsinh (√(Real.cosh (π * τ))) := by
          unfold Real.arsinh
          exact Real.log_le_log (Real.sqrt_pos.mpr (Real.cosh_pos _))
            (by linarith [Real.sqrt_nonneg (1 + √(Real.cosh (π * τ)) ^ 2)])
        have h3 : π * τ / 2 - Real.log √2 ≤ Real.log (√(Real.cosh (π * τ))) := by
          calc π * τ / 2 - Real.log √2 = Real.log (Real.exp (π * τ / 2) / √2) := by
                rw [Real.log_div (Real.exp_pos _).ne' (Real.sqrt_pos.mpr zero_lt_two).ne', Real.log_exp]
            _ ≤ Real.log (√(Real.cosh (π * τ))) := Real.log_le_log (by positivity) h1
        have h4 : Real.log √2 ≤ Real.log 2 := Real.log_le_log (by positivity) (by nlinarith [Real.sq_sqrt zero_le_two])
        rw [le_div_iff₀ Real.pi_pos, sub_mul, div_mul_cancel₀ _ Real.pi_pos.ne']
        linarith
      refine tendsto_atTop_mono' atTop ((eventually_ge_atTop 0).mono this) ?_
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(Real.log 2 / π))
        (tendsto_id.atTop_div_const zero_lt_two)
    dsimp [φ]
    exact ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hx_tend).const_mul_atTop hc' |>.atTop_div_const (by norm_num)
  have hR : Tendsto (fun R : ℝ => ∫ t in t₀..(φ R),
      H t * Bessel.besselV (c' / 12) t * F (√(3 * t / c'))) atTop
      (𝓝 (∫ t in Ioi t₀, H t * Bessel.besselV (c' / 12) t * F (√(3 * t / c')))) :=
    (intervalIntegral_tendsto_integral_Ioi t₀ h_int_t tendsto_id).comp hφ_tend
  have heq : ∀ᶠ R : ℝ in atTop,
      (∫ τ in (0 : ℝ)..R, H (φ τ) * Bessel.besselV (c' / 12) (φ τ) * F (xT τ) * φ' τ) =
        (∫ t in t₀..(φ R), H t * Bessel.besselV (c' / 12) t * F (√(3 * t / c'))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR_pos
    have hd : ∀ τ ∈ uIcc (0 : ℝ) R, HasDerivAt φ (φ' τ) τ := fun τ _ => by
      dsimp [φ, φ']; exact ((((hasDerivAt_xT τ).pow 2).const_mul c').div_const 3).congr_deriv (by ring)
    have hφ'_cont : ContinuousOn φ' (uIcc 0 R) := by
      dsimp [φ']; unfold xD
      exact ((((continuous_iff_continuousAt.mpr fun t => (hasDerivAt_xT t).continuousAt).const_mul (2 * c')).div_const 3).mul
        ((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).div
          (continuous_const.mul ((Real.continuous_sqrt.comp (Real.continuous_cosh.comp
            (continuous_const.mul continuous_id))).mul (Real.continuous_sqrt.comp (continuous_const.add
              (Real.continuous_cosh.comp (continuous_const.mul continuous_id))))))
          fun τ => ne_of_gt (by positivity [Real.cosh_pos (π * τ)]))).continuousOn
    have hcont_t : ContinuousOn (fun t => H t * Bessel.besselV (c' / 12) t * F (√(3 * t / c'))) (φ '' uIcc 0 R) := by
      have himg : φ '' uIcc 0 R ⊆ Ici t₀ := by
        rintro t ⟨τ, hτ, rfl⟩
        rw [uIcc_of_le hR_pos.le] at hτ
        rcases hτ.1.eq_or_lt with rfl | hτ_pos
        · exact le_rfl
        · have hlt := xT_strictMonoOn_Ici (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hτ.1) hτ_pos
          change t₀ ≤ c' * xT τ ^ 2 / 3
          dsimp [t₀, φ]
          have h0 := (xT_pos 0).le
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (sq_le_sq' (by linarith) hlt.le) hc'.le) (by norm_num)
      have h_all : ContinuousOn (fun t => H t * Bessel.besselV (c' / 12) t * F (√(3 * t / c'))) (Ici t₀) := by
        refine ((hH_cont.mono (Ici_subset_Ici.mpr ht₀_pos.le)).mul
          (hV_cont.mono (Ici_subset_Ici.mpr ht₀_pos.le))).mul ?_
        refine hF_cont.comp (Real.continuous_sqrt.continuousOn.comp
          ((continuousOn_const.mul continuousOn_id).div_const c') fun _ _ => mem_univ _)
          fun t ht => ?_
        have hle : c' * xiStar ^ 2 / 3 ≤ t := ht₀_val ▸ mem_Ici.mp ht
        have hsq : xiStar ^ 2 ≤ 3 * t / c' := by rw [le_div_iff₀ hc']; linarith
        simpa [Real.sqrt_sq xiStar_pos.le] using Real.sqrt_le_sqrt hsq
      exact h_all.mono himg
    have hcov := intervalIntegral.integral_comp_mul_deriv' hd hφ'_cont hcont_t
    dsimp only [Function.comp] at hcov
    rw [← ht₀_def] at hcov
    rw [← hcov]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    dsimp [φ, φ']
    have hsq : √(3 * (c' * xT τ ^ 2 / 3) / c') = xT τ := by
      rw [show 3 * (c' * xT τ ^ 2 / 3) / c' = xT τ ^ 2 by field_simp, Real.sqrt_sq (xT_pos τ).le]
    rw [hsq]
  rw [← ht₀_val]
  exact tendsto_nhds_unique (hL.congr' heq) hR

/-- Left-edge integral reduction of `cts:dual-id`. -/
lemma lowerDualPsi_left_integral_eq {c' ε : ℝ} (hc' : 10000 ≤ c')
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g) (hε : 0 < ε) :
    ∃ E : ℝ, |E| ≤ 1260000 * virasoroProblem.cardyNorm (c' / 12) g / c' ^ 2 ∧
      ∫ τ in Ioi (0 : ℝ), (lowerDualPsi c' ε 0 g (-((τ : ℂ) * Complex.I))).re =
        -virasoroDualPref c' *
          ((∫ t in Ioi (c' * xiStar ^ 2 / 3),
              g t * Bessel.besselV (c' / 12) t *
                (1 - virasoroV1 (√(3 * t / c')) /
                  (c' * (1 - Real.exp (-4 * π * √(3 * t / c'))) ^ 2)) *
                lowerWeps ε (lowerY (√(3 * t / c'))) *
                Real.sin (lowerThetaEps Gout ε (lowerY (√(3 * t / c'))) -
                  2 * π * c' * cumulN (√(3 * t / c')))) + E) := by
  have hc0 : 0 < c' := by linarith
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  have hshift : virasoroProblem.totalShift ≤ c' / 12 := by rw [virasoroProblem_totalShift]; linarith
  have hx_cont : Continuous xT := continuous_iff_continuousAt.mpr fun τ => (hasDerivAt_xT τ).continuousAt
  let F : ℝ → ℝ := fun x =>
    (1 - virasoroV1 x / (c' * (1 - Real.exp (-4 * π * x)) ^ 2)) * lowerWeps ε (lowerY x) *
      Real.sin (thetaOut (lowerY x) - 2 * Real.arctan (ε * lowerY x / ((1 - lowerY x ^ 2) + ε)) -
        2 * π * c' * cumulN x)
  have hF_eq : ∀ x : ℝ, xiStar < x →
      F x = (1 - virasoroV1 x / (c' * (1 - Real.exp (-4 * π * x)) ^ 2)) * lowerWeps ε (lowerY x) *
        Real.sin (lowerThetaEps Gout ε (lowerY x) - 2 * π * c' * cumulN x) := fun x hx => by
    dsimp [F]; rw [sin_lowerThetaEps_cont_eq hε.le hx]
  have hy_lt1 : ∀ x : ℝ, xiStar ≤ x → lowerY x ∈ Ioo (-1 : ℝ) 1 := fun x hx => by
    have hch : √2 ≤ Real.cosh (π * x) := by
      calc √2 = Real.cosh (π * xiStar) := cosh_pi_xiStar.symm
        _ ≤ Real.cosh (π * x) := Real.cosh_le_cosh.mpr (by
          rw [abs_of_pos (mul_pos Real.pi_pos xiStar_pos), abs_of_pos (mul_pos Real.pi_pos (by linarith [xiStar_pos]))]
          exact mul_le_mul_of_nonneg_left hx Real.pi_pos.le)
    have hden_pos : 0 < Real.cosh (π * x) + √2 := by linarith [Real.sqrt_pos.mpr zero_lt_two]
    have hy1 : lowerY x < 1 := by
      unfold lowerY
      rw [Real.sqrt_lt' zero_lt_one, one_pow, div_lt_one hden_pos]
      linarith [Real.sqrt_pos.mpr zero_lt_two]
    have hy0 : 0 ≤ lowerY x := by unfold lowerY; positivity
    exact ⟨by linarith, hy1⟩
  have hy_cont : ContinuousOn lowerY (Ici xiStar) := by
    unfold lowerY
    refine Real.continuous_sqrt.continuousOn.comp
      (((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).sub continuous_const).continuousOn.div
        ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).add continuous_const).continuousOn
        fun x _ => by positivity [Real.cosh_pos (π * x)])
      fun _ _ => mem_univ _
  have hF_cont : ContinuousOn F (Ici xiStar) := by
    have hV1_c : ContinuousOn (fun x => virasoroV1 x / (c' * (1 - Real.exp (-4 * π * x)) ^ 2)) (Ici xiStar) := by
      have hvv : ContinuousOn virasoroV1 (Ici xiStar) := by
        unfold virasoroV1
        refine (((continuousOn_const.div (continuousOn_const.mul continuousOn_id) fun x hx =>
          ne_of_gt (mul_pos (by positivity) (xiStar_pos.trans_le (mem_Ici.mp hx)))).mul ((continuousOn_const.sub
            (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).pow 2)).sub
            ((continuousOn_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
              (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)))).add
            ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
              (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)))
      refine hvv.div (continuousOn_const.mul ((continuousOn_const.sub
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).pow 2)) fun x hx => ?_
      have hxp : 0 < x := xiStar_pos.trans_le (mem_Ici.mp hx)
      have hlt : Real.exp (-4 * π * x) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
      positivity [show 0 < 1 - Real.exp (-4 * π * x) by linarith]
    have hWeps_c : ContinuousOn (fun x => lowerWeps ε (lowerY x)) (Ici xiStar) := by
      have hmt : ContinuousOn (fun y : ℝ => ‖lowerMt ε (Complex.I * (y : ℂ))‖ ^ 2) (Ioo (-1) 1) := by
        refine (ContinuousOn.norm ?_).pow 2
        unfold lowerMt
        refine (continuousOn_const.mul (continuousOn_const.add ((continuousOn_const.mul
          Complex.continuous_ofReal.continuousOn).pow 2))).div
          ((continuousOn_const.add ((continuousOn_const.mul Complex.continuous_ofReal.continuousOn).pow 2)).add
            (continuousOn_const.mul (continuousOn_const.add (continuousOn_const.mul Complex.continuous_ofReal.continuousOn))))
          fun y hy => by
            intro h
            rw [show (1 : ℂ) + (Complex.I * (y : ℂ)) ^ 2 + (ε : ℂ) * (1 + Complex.I * (y : ℂ)) =
              ((1 - y ^ 2 + ε : ℝ) : ℂ) + Complex.I * ((ε * y : ℝ) : ℂ) by
              rw [mul_pow, Complex.I_sq]; push_cast; ring] at h
            have hre' := congrArg Complex.re h
            simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
              Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at hre'
            nlinarith [hy.1, hy.2]
      exact hmt.comp hy_cont hy_lt1
    have hsin_c : ContinuousOn (fun x => Real.sin (thetaOut (lowerY x) -
        2 * Real.arctan (ε * lowerY x / ((1 - lowerY x ^ 2) + ε)) - 2 * π * c' * cumulN x)) (Ici xiStar) := by
      refine Real.continuous_sin.continuousOn.comp ?_ fun _ _ => mem_univ _
      have hth := thetaOut_soft.2.2.comp hy_cont hy_lt1
      have harctan : ContinuousOn (fun x => Real.arctan (ε * lowerY x / ((1 - lowerY x ^ 2) + ε))) (Ici xiStar) :=
        Real.continuous_arctan.continuousOn.comp ((continuousOn_const.mul hy_cont).div
          ((continuousOn_const.sub (hy_cont.pow 2)).add continuousOn_const) fun x hx => by
            have := hy_lt1 x hx; nlinarith [this.1, this.2]) fun _ _ => mem_univ _
      exact (hth.sub (continuousOn_const.mul harctan)).sub (continuousOn_const.mul continuousOn_cumulN)
    exact ((continuousOn_const.sub hV1_c).mul hWeps_c).mul hsin_c
  have hF_bd : ∀ x : ℝ, xiStar < x → |F x| ≤ 2 := fun x hx => by
    have hq4 : 1 / 4 ≤ (1 - Real.exp (-4 * π * x)) ^ 2 := by
      have hxp : 0 < x := xiStar_pos.trans hx
      have h1 : Real.exp (-4 * π * x) ≤ 1 / 2 := by
        rw [show -4 * π * x = -(4 * π * x) by ring, Real.exp_neg]
        calc (Real.exp (4 * π * x))⁻¹ ≤ (1 + 4 * π * x)⁻¹ :=
              inv_anti₀ (by positivity : 0 < 1 + 4 * π * x) (by linarith [Real.add_one_le_exp (4 * π * x)])
          _ ≤ 2⁻¹ := inv_anti₀ zero_lt_two (by nlinarith [Real.pi_gt_three, Bessel.one_fifth_le_xiStar])
          _ = 1 / 2 := by norm_num
      nlinarith
    have hvv : |virasoroV1 x / (c' * (1 - Real.exp (-4 * π * x)) ^ 2)| ≤ 120 / c' := by
      rw [abs_div, abs_of_pos (mul_pos hc0 (by positivity))]
      calc |virasoroV1 x| / (c' * (1 - Real.exp (-4 * π * x)) ^ 2)
          ≤ 30 / (c' * (1 / 4)) := by gcongr; exact virasoroV1_abs_le_30 (by linarith [xiStar_pos])
        _ = 120 / c' := by ring
    have hW := lowerWeps_mem_Icc hε.le hx
    rw [hF_eq x hx, abs_mul, abs_mul, abs_of_nonneg hW.1]
    have h12 : |1 - virasoroV1 x / (c' * (1 - Real.exp (-4 * π * x)) ^ 2)| ≤ 2 := by
      calc |1 - virasoroV1 x / (c' * (1 - Real.exp (-4 * π * x)) ^ 2)|
          ≤ |1| + |virasoroV1 x / (c' * (1 - Real.exp (-4 * π * x)) ^ 2)| := abs_sub _ _
        _ ≤ 1 + 120 / c' := by rw [abs_one]; linarith
        _ ≤ 2 := by have : 120 / c' ≤ 1 := (div_le_one hc0).mpr (by linarith); linarith
    calc |1 - virasoroV1 x / (c' * (1 - Real.exp (-4 * π * x)) ^ 2)| * lowerWeps ε (lowerY x) *
          |Real.sin (lowerThetaEps Gout ε (lowerY x) - 2 * π * c' * cumulN x)|
        ≤ 2 * 1 * 1 := by
          refine mul_le_mul (mul_le_mul h12 hW.2 hW.1 (by norm_num)) (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  let h_main : ℝ → ℝ := fun τ =>
    g (c' * xT τ ^ 2 / 3) * Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) *
      F (xT τ) * (2 * c' * xT τ / 3 * xD τ)
  have hV_cont : ContinuousOn (Bessel.besselV (c' / 12)) (Ici 0) :=
    (continuous_cardyV virasoroProblem (c' / 12)).continuousOn.congr fun t ht =>
      (Integration.virasoro_cardyV_eq_besselV ha (mem_Ici.mp ht)).symm
  have h_main_int : IntegrableOn h_main (Ioi 0) := by
    refine ((integrableOn_Ioi_comp_xT hc' hg).const_mul 2).mono' ?_ ?_
    · have hφ_cont : Continuous (fun τ => c' * xT τ ^ 2 / 3) := ((hx_cont.pow 2).const_mul c').div_const 3
      have hg_c : Continuous (fun τ => g (c' * xT τ ^ 2 / 3)) :=
        hg.cont.comp_continuous hφ_cont fun τ => Set.mem_Ici.mpr (by positivity)
      have hV_c : Continuous (fun τ => Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3)) :=
        hV_cont.comp_continuous hφ_cont fun τ => Set.mem_Ici.mpr (by positivity)
      have hxD_c : Continuous xD := by
        unfold xD
        exact (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).div
          (continuous_const.mul ((Real.continuous_sqrt.comp (Real.continuous_cosh.comp
            (continuous_const.mul continuous_id))).mul (Real.continuous_sqrt.comp
              (continuous_const.add (Real.continuous_cosh.comp (continuous_const.mul continuous_id))))))
          fun τ => by positivity [Real.cosh_pos (π * τ)]
      have hFc : ContinuousOn (fun τ => F (xT τ)) (Ioi 0) :=
        hF_cont.comp hx_cont.continuousOn fun τ hτ => (xT_gt_xiStar (mem_Ioi.mp hτ)).le
      exact (((hg_c.continuousOn.mul hV_c.continuousOn).mul hFc).mul
        (((hx_cont.const_mul (2 * c')).div_const 3).mul hxD_c).continuousOn).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
      have hτ_pos : 0 < τ := mem_Ioi.mp hτ
      have hV_nn : 0 ≤ Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) := by
        rw [← Integration.virasoro_cardyV_eq_besselV ha (by positivity)]
        exact virasoroProblem.cardyV_nonneg hshift (by positivity)
      have hφ'_nn : 0 ≤ 2 * c' * xT τ / 3 * xD τ := by positivity [(xT_pos τ).le, (xD_pos τ hτ_pos).le]
      dsimp [h_main]
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hV_nn, abs_of_nonneg hφ'_nn]
      calc |g (c' * xT τ ^ 2 / 3)| * Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) * |F (xT τ)| *
            (2 * c' * xT τ / 3 * xD τ)
          ≤ |g (c' * xT τ ^ 2 / 3)| * Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) * 2 *
              (2 * c' * xT τ / 3 * xD τ) := by gcongr; exact hF_bd _ (xT_gt_xiStar hτ_pos)
        _ = 2 * (|g (c' * xT τ ^ 2 / 3)| * Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) *
              (2 * c' * xT τ / 3 * xD τ)) := by ring
  have hC₀ : 0 < virasoroDualPref c' := virasoroDualPref_pos hc0
  have h_lhs_int : IntegrableOn (fun τ : ℝ => (lowerDualPsi c' ε 0 g (-((τ : ℂ) * Complex.I))).re) (Ioi (0 : ℝ)) := by
    have hre_cont : ContinuousOn (fun τ : ℝ => (lowerDualPsi c' ε 0 g (-((τ : ℂ) * Complex.I))).re) (Ioi (0 : ℝ)) := by
      refine Complex.continuous_re.comp_continuousOn ((lowerDualPsi_continuousOn (by linarith) hg hε le_rfl).comp
        (by fun_prop : Continuous fun τ : ℝ => -((τ : ℂ) * Complex.I)).continuousOn fun τ hτ => ?_)
      exact ⟨⟨by simp, by norm_num, by simp; exact (mem_Ioi.mp hτ).le⟩, fun h => by
        simp only [mem_insert_iff, mem_singleton_iff] at h
        rcases h with h | h
        · have := congrArg Complex.im h; simp at this; linarith [mem_Ioi.mp hτ]
        · have := congrArg Complex.re h; simp at this⟩
    have hdom := (integrableOn_Ioi_comp_xT hc' hg).const_mul (virasoroDualPref c' * 3)
    refine hdom.mono' (hre_cont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    have hτ_pos : 0 < τ := mem_Ioi.mp hτ
    have hx_gt : xiStar < xT τ := xT_gt_xiStar hτ_pos
    have hA_le3 := besselAs_le_three_besselV hc' (by linarith [xiStar_pos] : xiStar / 2 ≤ xT τ)
    have hsub1 : (1 - Real.exp (-4 * π * xT τ)) ^ 2 ≤ 1 := by
      have : 0 ≤ Real.exp (-4 * π * xT τ) := (Real.exp_pos _).le
      have : Real.exp (-4 * π * xT τ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, xT_pos τ])
      nlinarith
    have hW := lowerWeps_mem_Icc hε.le hx_gt
    have hV_nn : 0 ≤ Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) := by
      rw [← Integration.virasoro_cardyV_eq_besselV ha (by positivity)]
      exact virasoroProblem.cardyV_nonneg hshift (by positivity)
    have hxD_nn : 0 ≤ 2 * c' * xT τ / 3 * xD τ := by positivity [(xT_pos τ).le, (xD_pos τ hτ_pos).le]
    rw [Real.norm_eq_abs, lowerDualPsi_left_re_eq hc0 hε.le hg hτ_pos]
    simp only [abs_mul, abs_neg]
    rw [abs_of_pos hC₀, abs_of_pos (Bessel.besselAs_pos (by unfold Bessel.besselL; positivity [xT_pos τ])),
      abs_of_nonneg (sq_nonneg (1 - Real.exp (-4 * π * xT τ))), abs_of_nonneg hW.1,
      abs_of_nonneg (by positivity [(xT_pos τ).le] : 0 ≤ 2 * c' * xT τ / 3), abs_of_nonneg (xD_pos τ hτ_pos).le]
    calc virasoroDualPref c' * |g (c' * xT τ ^ 2 / 3)| *
          Bessel.besselAs (c' * Bessel.besselL (xT τ)) * (1 - Real.exp (-4 * π * xT τ)) ^ 2 *
          lowerWeps ε (lowerY (xT τ)) *
          |Real.sin (lowerThetaEps Gout ε (lowerY (xT τ)) - 2 * π * c' * cumulN (xT τ))| *
          (2 * c' * xT τ / 3 * xD τ)
        ≤ virasoroDualPref c' * |g (c' * xT τ ^ 2 / 3)| *
            (3 * Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3)) * 1 * 1 * 1 *
            (2 * c' * xT τ / 3 * xD τ) := by
          gcongr
          · exact hW.1
          · exact hW.2
          · exact Real.abs_sin_le_one _
      _ = virasoroDualPref c' * 3 * (|g (c' * xT τ ^ 2 / 3)| *
            Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) * (2 * c' * xT τ / 3 * xD τ)) := by ring
  let h_err : ℝ → ℝ := fun τ =>
    -(lowerDualPsi c' ε 0 g (-((τ : ℂ) * Complex.I))).re / virasoroDualPref c' - h_main τ
  have h_err_int : IntegrableOn h_err (Ioi 0) :=
    ((h_lhs_int.neg).div_const (virasoroDualPref c')).sub h_main_int
  have h_err_bd : |∫ τ in Ioi (0 : ℝ), h_err τ| ≤
      1260000 * virasoroProblem.cardyNorm (c' / 12) g / c' ^ 2 := by
    have hV_int_xT := integrableOn_Ioi_comp_xT hc' hg
    have hpt : ∀ τ ∈ Ioi (0 : ℝ), ‖h_err τ‖ ≤
        (1260000 / c' ^ 2) * (|g (c' * xT τ ^ 2 / 3)| * Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) *
          (2 * c' * xT τ / 3 * xD τ)) := fun τ hτ => by
      have hτ_pos : 0 < τ := mem_Ioi.mp hτ
      have hx_gt : xiStar < xT τ := xT_gt_xiStar hτ_pos
      have hdiff := besselAs_sub_besselV_bound hc' (by linarith [xiStar_pos] : xiStar / 2 ≤ xT τ)
      have hW := lowerWeps_mem_Icc hε.le hx_gt
      have hV_nn : 0 ≤ Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) := by
        rw [← Integration.virasoro_cardyV_eq_besselV ha (by positivity)]
        exact virasoroProblem.cardyV_nonneg hshift (by positivity)
      have hxD_nn : 0 ≤ 2 * c' * xT τ / 3 * xD τ := by positivity [(xT_pos τ).le, (xD_pos τ hτ_pos).le]
      have h_eq : h_err τ =
          g (c' * xT τ ^ 2 / 3) *
            (Bessel.besselAs (c' * Bessel.besselL (xT τ)) * (1 - Real.exp (-4 * π * xT τ)) ^ 2 -
              Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) *
                (1 - virasoroV1 (xT τ) / (c' * (1 - Real.exp (-4 * π * xT τ)) ^ 2))) *
            lowerWeps ε (lowerY (xT τ)) *
            Real.sin (lowerThetaEps Gout ε (lowerY (xT τ)) - 2 * π * c' * cumulN (xT τ)) *
            (2 * c' * xT τ / 3 * xD τ) := by
        dsimp [h_err, h_main]
        rw [lowerDualPsi_left_re_eq hc0 hε.le hg hτ_pos, hF_eq (xT τ) hx_gt]
        field_simp [hC₀.ne']
      rw [Real.norm_eq_abs, h_eq, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg hW.1, abs_of_nonneg hxD_nn]
      calc |g (c' * xT τ ^ 2 / 3)| * |_| * lowerWeps ε (lowerY (xT τ)) *
            |Real.sin (lowerThetaEps Gout ε (lowerY (xT τ)) - 2 * π * c' * cumulN (xT τ))| *
            (2 * c' * xT τ / 3 * xD τ)
          ≤ |g (c' * xT τ ^ 2 / 3)| * (1260000 / c' ^ 2 * Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3)) *
              1 * 1 * (2 * c' * xT τ / 3 * xD τ) := by
            gcongr
            · exact hW.1
            · exact hW.2
            · exact Real.abs_sin_le_one _
        _ = (1260000 / c' ^ 2) * (|g (c' * xT τ ^ 2 / 3)| * Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) *
              (2 * c' * xT τ / 3 * xD τ)) := by ring
    have hnorm_le : ‖∫ τ in Ioi (0 : ℝ), h_err τ‖ ≤
        ∫ τ in Ioi (0 : ℝ), (1260000 / c' ^ 2) *
          (|g (c' * xT τ ^ 2 / 3)| * Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) *
            (2 * c' * xT τ / 3 * xD τ)) :=
      (MeasureTheory.norm_integral_le_integral_norm _).trans
        (integral_mono_of_nonneg (ae_restrict_of_forall_mem measurableSet_Ioi fun _ _ => norm_nonneg _)
          (hV_int_xT.const_mul _) (ae_restrict_of_forall_mem measurableSet_Ioi hpt))
    rw [Real.norm_eq_abs, MeasureTheory.integral_const_mul] at hnorm_le
    -- bound ∫ τ > 0, |g(φ τ)| V(φ τ) φ' τ ≤ M[g] by change_of_vars_Ioi_xT
    have hV_int : IntegrableOn (fun t => |g t| * Bessel.besselV (c' / 12) t) (Ioi 0) :=
      hg.int_cardy.congr_fun (fun t ht => by
        dsimp only; rw [Integration.virasoro_cardyV_eq_besselV ha (mem_Ioi.mp ht).le]) measurableSet_Ioi
    have hcov_le : ∫ τ in Ioi (0 : ℝ), |g (c' * xT τ ^ 2 / 3)| * Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) *
          (2 * c' * xT τ / 3 * xD τ) ≤ virasoroProblem.cardyNorm (c' / 12) g := by
      have hcov0 := change_of_vars_Ioi_xT hc0 ha (fun t => |g t|) hg.cont.abs
        (hV_int.congr_fun (fun t _ => by simp only [abs_abs]) measurableSet_Ioi)
        (fun _ => 1) continuousOn_const ⟨1, fun _ _ => by norm_num⟩
        (hV_int_xT.congr_fun (fun τ _ => by ring) measurableSet_Ioi)
      simp only [mul_one] at hcov0
      rw [hcov0]
      have hmono : ∫ t in Ioi (c' * xiStar ^ 2 / 3), |g t| * Bessel.besselV (c' / 12) t ≤
          ∫ t in Ioi (0 : ℝ), |g t| * Bessel.besselV (c' / 12) t := by
        refine setIntegral_mono_set hV_int ?_
          (Eventually.of_forall fun t ht => Ioi_subset_Ioi (by positivity [xiStar_pos]) ht)
        exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
          mul_nonneg (abs_nonneg _) (by
            rw [← Integration.virasoro_cardyV_eq_besselV ha (mem_Ioi.mp ht).le]
            exact virasoroProblem.cardyV_nonneg hshift (mem_Ioi.mp ht).le)
      refine hmono.trans_eq ?_
      change ∫ t in Ioi (0 : ℝ), |g t| * Bessel.besselV (c' / 12) t =
        ∫ t in Ioi (0 : ℝ), |g t| * virasoroProblem.cardyV (c' / 12) t
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [← Integration.virasoro_cardyV_eq_besselV ha (mem_Ioi.mp ht).le]
    calc |∫ τ in Ioi (0 : ℝ), h_err τ|
        ≤ (1260000 / c' ^ 2) * ∫ τ in Ioi (0 : ℝ), |g (c' * xT τ ^ 2 / 3)| *
            Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) * (2 * c' * xT τ / 3 * xD τ) := hnorm_le
      _ ≤ (1260000 / c' ^ 2) * virasoroProblem.cardyNorm (c' / 12) g := by gcongr
      _ = 1260000 * virasoroProblem.cardyNorm (c' / 12) g / c' ^ 2 := by ring
  have hcov_main : ∫ τ in Ioi (0 : ℝ), h_main τ =
      ∫ t in Ioi (c' * xiStar ^ 2 / 3),
        g t * Bessel.besselV (c' / 12) t *
          (1 - virasoroV1 (√(3 * t / c')) / (c' * (1 - Real.exp (-4 * π * √(3 * t / c'))) ^ 2)) *
          lowerWeps ε (lowerY (√(3 * t / c'))) *
          Real.sin (lowerThetaEps Gout ε (lowerY (√(3 * t / c'))) -
            2 * π * c' * cumulN (√(3 * t / c'))) := by
    have hcov1 := change_of_vars_Ioi_xT hc0 ha g hg.cont
      (hg.int_cardy.congr_fun (fun t ht => by
        dsimp only; rw [Integration.virasoro_cardyV_eq_besselV ha (mem_Ioi.mp ht).le]) measurableSet_Ioi)
      F hF_cont ⟨2, hF_bd⟩ h_main_int
    refine hcov1.trans (setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_)
    have ht_gt : c' * xiStar ^ 2 / 3 < t := mem_Ioi.mp ht
    have hx_gt : xiStar < √(3 * t / c') := by
      simpa [Real.sqrt_sq xiStar_pos.le] using Real.sqrt_lt_sqrt (sq_nonneg _)
        (show xiStar ^ 2 < 3 * t / c' by rw [lt_div_iff₀ hc0]; linarith)
    rw [hF_eq _ hx_gt]
    ring
  refine ⟨∫ τ in Ioi (0 : ℝ), h_err τ, h_err_bd, ?_⟩
  have hsum : (∫ τ in Ioi (0 : ℝ), h_main τ) + (∫ τ in Ioi (0 : ℝ), h_err τ) =
      -(∫ τ in Ioi (0 : ℝ), (lowerDualPsi c' ε 0 g (-((τ : ℂ) * Complex.I))).re) / virasoroDualPref c' := by
    rw [← MeasureTheory.integral_add h_main_int h_err_int]
    have heq : (fun τ => h_main τ + h_err τ) =
        fun τ : ℝ => -(lowerDualPsi c' ε 0 g (-((τ : ℂ) * Complex.I))).re / virasoroDualPref c' := by
      ext τ; dsimp [h_err]; ring
    rw [heq, MeasureTheory.integral_div, MeasureTheory.integral_neg]
  rw [← hcov_main, hsum]
  have heq_I : ∫ τ in Ioi (0 : ℝ), (lowerDualPsi c' ε 0 g (-((τ : ℂ) * Complex.I))).re =
      ∫ τ in Ioi (0 : ℝ), (lowerDualPsi c' ε 0 g (-(Complex.I * (τ : ℂ)))).re :=
    setIntegral_congr_fun measurableSet_Ioi fun τ _ => by rw [mul_comm (τ : ℂ) Complex.I]
  field_simp [hC₀.ne']
  try ring
  exact heq_I

end

end FormalResearch.ModularBootstrap.FiveTerm
