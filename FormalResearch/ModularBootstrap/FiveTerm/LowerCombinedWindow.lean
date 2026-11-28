module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerRoscOrth
public import FormalResearch.ModularBootstrap.FiveTerm.LowerChartMain
public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasFreezeWeps

/-!
# Virasoro Slit-Phase Cancellation and General-Radius `calD_up` Orthogonality (`LowerCombinedWindow`)

Proves the window slit-phase cancellation needed for `cts:combined` (`cts:combined-residual`):

* `airyUpSqrt` and `lowerEc`: smooth/holomorphic continuation of
  `(4/3) φ_c(u)^{3/2} + 2 φ_c(u)^{1/2} (u - φ_c(u))` on `closedHalfDisc R` / `openHalfDisc R`;
* `virasoro_D_orth_of_holo`: general-radius `calD_up` orthogonality for any real-symmetric holomorphic `F`
  (`O(R^{-3/2} ∫_0^π R ‖F‖ / airyEnv)`), covering both `R` and the CFU radius `R₂`;
* `virasoro_slit_phase_window_bound`:
  `|I_win(R) + X₀(R)| ≤ C (c⁻¹ lowerEta(R) + c^{-4/3})` for all `cl c^{2/3} ≤ R ≤ lowerRmax virasoroC1 c`.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology intervalIntegral
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.FixedWeightTip
open FormalResearch.ModularBootstrap.FixedWeightBand
open FormalResearch.ModularBootstrap.Contour
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
open FormalResearch.HalfDiscCauchy
open FormalResearch.SignUncertainty
open FormalResearch.SignUncertainty.FineOrderSigned

noncomputable section

/-! ### 1. Complex half-power `airyUpSqrt` and upper-half-plane phase `lowerEc` -/

/-- Upper-half-plane square root matching `airyUpE w = cexp ((4/3) w airyUpSqrt w)` cleanly at `0`. -/
def airyUpSqrt (w : ℂ) : ℂ :=
  if w = 0 then 0 else Complex.exp ((1 / 2 : ℂ) * airyUpL w)

lemma norm_airyUpSqrt (w : ℂ) : ‖airyUpSqrt w‖ = √‖w‖ := by
  unfold airyUpSqrt
  split_ifs with hw
  · simp [hw]
  · rw [Complex.norm_exp]
    have hre : ((1 / 2 : ℂ) * airyUpL w).re = (1 / 2 : ℝ) * Real.log ‖w‖ := by
      unfold airyUpL
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, neg_mul]
      have hlog : (Complex.log (-(I * w))).re = Real.log ‖w‖ := by
        rw [Complex.log_re, norm_neg, norm_mul, Complex.norm_I, one_mul]
      norm_num [hlog]
    rw [hre, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (norm_pos_iff.mpr hw), mul_comm]

lemma airyUpE_eq_exp_airyUpSqrt (w : ℂ) :
    airyUpE w = Complex.exp ((4 / 3 : ℂ) * w * airyUpSqrt w) := by
  unfold airyUpE airyUpSqrt
  split_ifs with hw
  · simp [hw]
  · simp only [mul_assoc]

private lemma neg_I_mul_mem_slitPlane {w : ℂ} (hw : 0 ≤ w.im) (hw0 : w ≠ 0) :
    -I * w ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  have hre : (-I * w).re = w.im := by simp
  have him : (-I * w).im = -w.re := by simp
  rcases eq_or_lt_of_le hw with hw_eq | hw_gt
  · right
    intro h0
    apply hw0
    rw [him] at h0
    have hwre : w.re = 0 := by linarith only [h0]
    exact Complex.ext hwre hw_eq.symm
  · left; exact hre ▸ hw_gt

lemma hasDerivAt_airyUpSqrt {w : ℂ} (hw : 0 ≤ w.im) (hw0 : w ≠ 0) :
    HasDerivAt airyUpSqrt ((1 / 2 : ℂ) * w⁻¹ * airyUpSqrt w) w := by
  have hslit : -I * w ∈ Complex.slitPlane := neg_I_mul_mem_slitPlane hw hw0
  have hlog : HasDerivAt (fun z : ℂ => Complex.log (-I * z)) w⁻¹ w := by
    have hm : HasDerivAt (fun z : ℂ => -I * z) (-I * 1) w :=
      (hasDerivAt_id w).const_mul (-I)
    refine ((Complex.hasDerivAt_log hslit).comp w hm).congr_deriv ?_
    have hi : (-I : ℂ) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
    field_simp [hi, hw0]
  have hL : HasDerivAt airyUpL w⁻¹ w := by
    unfold airyUpL
    exact (hlog.add (hasDerivAt_const w (((π / 2 : ℝ) : ℂ) * I))).congr_deriv (add_zero _)
  have hexp : HasDerivAt (fun z : ℂ => Complex.exp ((1 / 2 : ℂ) * airyUpL z))
      (Complex.exp ((1 / 2 : ℂ) * airyUpL w) * ((1 / 2 : ℂ) * w⁻¹)) w :=
    (hL.const_mul (1 / 2 : ℂ)).cexp
  have heq : (fun z : ℂ => Complex.exp ((1 / 2 : ℂ) * airyUpL z)) =ᶠ[𝓝 w] airyUpSqrt := by
    filter_upwards [isOpen_ne.mem_nhds hw0] with z hz
    dsimp only; unfold airyUpSqrt
    exact (if_neg hz).symm
  refine (hexp.congr_of_eventuallyEq heq.symm).congr_deriv ?_
  have hw_if : airyUpSqrt w = Complex.exp ((1 / 2 : ℂ) * airyUpL w) := by
    unfold airyUpSqrt; exact if_neg hw0
  rw [hw_if]; ring

lemma continuousAt_airyUpSqrt {w : ℂ} (hw : 0 ≤ w.im) : ContinuousAt airyUpSqrt w := by
  rcases eq_or_ne w 0 with rfl | hw0
  · rw [ContinuousAt, show airyUpSqrt 0 = 0 from if_pos rfl, tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : (fun z : ℂ => ‖airyUpSqrt z‖) = fun z : ℂ => √‖z‖ := funext norm_airyUpSqrt
    rw [hnorm]
    have hcont : Continuous (fun z : ℂ => √‖z‖) := Real.continuous_sqrt.comp continuous_norm
    simpa using hcont.tendsto 0
  · exact (hasDerivAt_airyUpSqrt hw hw0).continuousAt

lemma continuousOn_airyUpSqrt_half : ContinuousOn airyUpSqrt {w : ℂ | 0 ≤ w.im} :=
  fun _ hw => (continuousAt_airyUpSqrt hw).continuousWithinAt

lemma airyUpSqrt_ofReal_nonneg {x : ℝ} (hx : 0 ≤ x) :
    airyUpSqrt (x : ℂ) = ((√x : ℝ) : ℂ) := by
  rcases eq_or_lt_of_le hx with rfl | hx_pos
  · simp [airyUpSqrt]
  · have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
    have hpow := airyUp_pow_eq (u := (x : ℂ)) (by simp) hx0
    have hsq : (x : ℂ) * Complex.exp ((1 / 2 : ℂ) * airyUpL (x : ℂ)) =
        (((x ^ (3 / 2 : ℝ) : ℝ)) : ℂ) := by
      rw [hpow, show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hx]
    have hsqrt : (x : ℂ) * ((√x : ℝ) : ℂ) = (((x ^ (3 / 2 : ℝ) : ℝ)) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.sqrt_eq_rpow]
      congr 1
      calc x * x ^ (1 / 2 : ℝ) = x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ) := by simp
        _ = x ^ (1 + 1 / 2 : ℝ) := (Real.rpow_add hx_pos 1 (1 / 2)).symm
        _ = x ^ (3 / 2 : ℝ) := by norm_num
    have hmul : (x : ℂ) * airyUpSqrt (x : ℂ) = (x : ℂ) * ((√x : ℝ) : ℂ) := by
      unfold airyUpSqrt; rw [if_neg hx0, hsq, hsqrt]
    exact mul_left_cancel₀ hx0 hmul

lemma airyUpSqrt_ofReal_neg {v : ℝ} (hv : 0 < v) :
    airyUpSqrt ((-v : ℝ) : ℂ) = ((√v : ℝ) : ℂ) * I := by
  have hv0 : ((-v : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith only [hv])
  have heq : -I * ((-v : ℝ) : ℂ) = ((v : ℝ) : ℂ) * I := by push_cast; ring
  have hlog : Complex.log (-I * ((-v : ℝ) : ℂ)) =
      (Real.log v : ℂ) + ((π / 2 : ℝ) : ℂ) * I := by
    rw [heq]
    have hexp : ((v : ℝ) : ℂ) * I = Complex.exp ((Real.log v : ℂ) + ((π / 2 : ℝ) : ℂ) * I) := by
      rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hv, Complex.exp_mul_I]
      simp
    have him1 : -π < ((Real.log v : ℂ) + ((π / 2 : ℝ) : ℂ) * I).im := by
      simp [Real.pi_pos]
      linarith only [Real.pi_pos]
    have him2 : ((Real.log v : ℂ) + ((π / 2 : ℝ) : ℂ) * I).im ≤ π := by
      simp [Real.pi_pos]
      linarith only [Real.pi_pos]
    rw [hexp, Complex.log_exp him1 him2]
  unfold airyUpSqrt airyUpL
  rw [if_neg hv0, hlog]
  have harg : (1 / 2 : ℂ) * ((Real.log v : ℂ) + ((π / 2 : ℝ) : ℂ) * I + ((π / 2 : ℝ) : ℂ) * I) =
      ((1 / 2 * Real.log v : ℝ) : ℂ) + ((π / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [harg, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I]
  rw [show (1 / 2 * Real.log v : ℝ) = Real.log v * (1 / 2) by ring,
    ← Real.rpow_def_of_pos hv, ← Real.sqrt_eq_rpow]
  simp

/-! ### 2. `lowerEc` holomorphicity, continuity, and semicircle difference bound -/

/-- Exact slit-phase exponent `(4/3) φ_c(u) airyUpSqrt(φ_c(u)) + 2 airyUpSqrt(φ_c(u)) (u - φ_c(u))`. -/
def lowerEc (phi : ℝ → ℂ → ℂ) (c : ℝ) (u : ℂ) : ℂ :=
  (4 / 3 : ℂ) * phi c u * airyUpSqrt (phi c u) +
    2 * airyUpSqrt (phi c u) * (u - phi c u)

lemma phi_im_ge_half_im {phi : ℝ → ℂ → ℂ} {c R ρ : ℝ}
    (_hR : 0 ≤ R) (hRρ : R < ρ)
    (hφ_diff : DifferentiableOn ℂ (phi c) (ball 0 ρ))
    (hφ_real : ∀ x : ℝ, |x| ≤ R → (phi c (x : ℂ)).im = 0)
    (hφ_der : ∀ z ∈ closedBall (0 : ℂ) R, ‖deriv (phi c) z - 1‖ ≤ 1 / 2) :
    ∀ u ∈ closedHalfDisc R, (1 / 2 : ℝ) * u.im ≤ (phi c u).im := by
  intro u hu
  have hu_le : ‖u‖ ≤ R := mem_closedBall_zero_iff.mp hu.1
  have hu_im : 0 ≤ u.im := hu.2
  have hure_le : |u.re| ≤ R := (Complex.abs_re_le_norm u).trans hu_le
  have hseg_mem : ∀ t ∈ Icc (0 : ℝ) u.im,
      ((u.re : ℂ) + (t : ℂ) * I) ∈ closedBall (0 : ℂ) R := fun t ht => by
    rw [mem_closedBall_zero_iff]
    have hnorm : ‖(u.re : ℂ) + (t : ℂ) * I‖ = √(u.re ^ 2 + t ^ 2) := by
      simpa using Complex.norm_add_mul_I u.re t
    have hnorm_u : ‖u‖ = √(u.re ^ 2 + u.im ^ 2) := by
      calc ‖u‖ = ‖(u.re : ℂ) + (u.im : ℂ) * I‖ := by congr 1; exact (Complex.re_add_im u).symm
        _ = √(u.re ^ 2 + u.im ^ 2) := Complex.norm_add_mul_I u.re u.im
    rw [hnorm]
    calc √(u.re ^ 2 + t ^ 2) ≤ √(u.re ^ 2 + u.im ^ 2) := by
          gcongr; nlinarith only [ht.1, ht.2]
      _ = ‖u‖ := hnorm_u.symm
      _ ≤ R := hu_le
  let g : ℝ → ℝ := fun t => (phi c ((u.re : ℂ) + (t : ℂ) * I)).im
  let g' : ℝ → ℝ := fun t => (deriv (phi c) ((u.re : ℂ) + (t : ℂ) * I)).re
  have hhd : ∀ t ∈ uIcc (0 : ℝ) u.im, HasDerivAt g (g' t) t := fun t ht => by
    rw [uIcc_of_le hu_im] at ht
    have hz_ball : (u.re : ℂ) + (t : ℂ) * I ∈ ball (0 : ℂ) ρ :=
      (closedBall_subset_ball hRρ) (hseg_mem t ht)
    have hφ_at := (hφ_diff.differentiableAt (isOpen_ball.mem_nhds hz_ball)).hasDerivAt
    have hline : HasDerivAt (fun s : ℝ => (u.re : ℂ) + (s : ℂ) * I) I t := by
      have h1 := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add (u.re : ℂ)
      simpa only [Complex.ofRealCLM_apply, one_mul] using h1
    have hcompC : HasDerivAt (fun s : ℝ => phi c ((u.re : ℂ) + (s : ℂ) * I))
        (deriv (phi c) ((u.re : ℂ) + (t : ℂ) * I) * I) t :=
      hφ_at.scomp t hline
    have him : HasDerivAt g (Complex.imCLM (deriv (phi c) ((u.re : ℂ) + (t : ℂ) * I) * I)) t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hcompC
    refine him.congr_deriv ?_
    simp [g', Complex.imCLM_apply]
  have hg'_cont : ContinuousOn g' (uIcc (0 : ℝ) u.im) := by
    rw [uIcc_of_le hu_im]
    have hd_an : AnalyticOnNhd ℂ (deriv (phi c)) (ball 0 ρ) :=
      (hφ_diff.analyticOnNhd isOpen_ball).deriv
    refine Complex.continuous_re.comp_continuousOn (hd_an.continuousOn.comp ?_ ?_)
    · exact continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const)
    · intro t ht; exact (closedBall_subset_ball hRρ) (hseg_mem t ht)
  have hftc : ∫ t in (0 : ℝ)..u.im, g' t = g u.im - g 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hhd hg'_cont.intervalIntegrable
  have hg0 : g 0 = 0 := by
    dsimp [g]; simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hφ_real u.re hure_le
  have hgu : g u.im = (phi c u).im := by
    dsimp [g]; rw [Complex.re_add_im]
  have hge : ∀ t ∈ Icc (0 : ℝ) u.im, (1 / 2 : ℝ) ≤ g' t := fun t ht => by
    have hbd := hφ_der ((u.re : ℂ) + (t : ℂ) * I) (hseg_mem t ht)
    have hre : 1 - (deriv (phi c) ((u.re : ℂ) + (t : ℂ) * I)).re ≤
        ‖deriv (phi c) ((u.re : ℂ) + (t : ℂ) * I) - 1‖ := by
      have h1 : |1 - g' t| ≤ ‖(1 : ℂ) - deriv (phi c) ((u.re : ℂ) + (t : ℂ) * I)‖ := by
        simpa [g'] using Complex.abs_re_le_norm ((1 : ℂ) - deriv (phi c) ((u.re : ℂ) + (t : ℂ) * I))
      rw [norm_sub_rev] at h1
      exact (le_abs_self _).trans h1
    dsimp [g'] at hre ⊢
    linarith only [hbd, hre]
  have hint_lb : ∫ t in (0 : ℝ)..u.im, (1 / 2 : ℝ) ≤ ∫ t in (0 : ℝ)..u.im, g' t :=
    intervalIntegral.integral_mono_on hu_im intervalIntegrable_const hg'_cont.intervalIntegrable hge
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm, hftc, hg0, hgu, sub_zero] at hint_lb
  exact hint_lb

lemma lowerEc_holo_cont {phi : ℝ → ℂ → ℂ} {c R ρ : ℝ}
    (hR : 0 ≤ R) (hRρ : R < ρ)
    (hφ_diff : DifferentiableOn ℂ (phi c) (ball 0 ρ))
    (hφ_real : ∀ x : ℝ, |x| ≤ R → (phi c (x : ℂ)).im = 0)
    (hφ_der : ∀ z ∈ closedBall (0 : ℂ) R, ‖deriv (phi c) z - 1‖ ≤ 1 / 2) :
    ContinuousOn (lowerEc phi c) (closedHalfDisc R) ∧
    DifferentiableOn ℂ (lowerEc phi c) (openHalfDisc R) := by
  have him_ge := phi_im_ge_half_im hR hRρ hφ_diff hφ_real hφ_der
  have hφ_cont : ContinuousOn (phi c) (closedHalfDisc R) :=
    hφ_diff.continuousOn.mono fun u hu => closedBall_subset_ball hRρ hu.1
  have hs_cont : ContinuousOn (fun u => airyUpSqrt (phi c u)) (closedHalfDisc R) :=
    continuousOn_airyUpSqrt_half.comp hφ_cont fun u hu =>
      le_trans (by linarith only [hu.2]) (him_ge u hu)
  refine ⟨?_, ?_⟩
  · unfold lowerEc
    exact ((continuousOn_const.mul hφ_cont).mul hs_cont).add
      ((continuousOn_const.mul hs_cont).mul (continuousOn_id.sub hφ_cont))
  · intro u hu
    have hu_cl : u ∈ closedHalfDisc R := ⟨ball_subset_closedBall hu.1, hu.2.le⟩
    have hu_rho : u ∈ ball (0 : ℂ) ρ := (ball_subset_ball hRρ.le) hu.1
    have hφ_at : DifferentiableAt ℂ (phi c) u :=
      hφ_diff.differentiableAt (isOpen_ball.mem_nhds hu_rho)
    have him_pos : 0 < (phi c u).im := lt_of_lt_of_le (by linarith only [hu.2]) (him_ge u hu_cl)
    have hne : phi c u ≠ 0 := fun h0 => by rw [h0] at him_pos; simp at him_pos
    have hs_at : DifferentiableAt ℂ airyUpSqrt (phi c u) :=
      (hasDerivAt_airyUpSqrt him_pos.le hne).differentiableAt
    have hcomp : DifferentiableAt ℂ (fun z => airyUpSqrt (phi c z)) u :=
      hs_at.comp u hφ_at
    unfold lowerEc
    exact (((differentiableAt_const _).mul hφ_at).mul hcomp).add
      (((differentiableAt_const _).mul hcomp).mul (differentiableAt_id.sub hφ_at)) |>.differentiableWithinAt

private lemma hasDerivAt_E_main {z : ℂ} (hz : 0 ≤ z.im) (hz0 : z ≠ 0) :
    HasDerivAt (fun w : ℂ => (4 / 3 : ℂ) * w * airyUpSqrt w) (2 * airyUpSqrt z) z := by
  have hs := hasDerivAt_airyUpSqrt hz hz0
  have hid := hasDerivAt_id z
  have hm := (hid.const_mul (4 / 3 : ℂ)).mul hs
  refine hm.congr_deriv ?_
  calc (4 / 3 : ℂ) * 1 * airyUpSqrt z + (4 / 3 : ℂ) * z * ((1 / 2 : ℂ) * z⁻¹ * airyUpSqrt z)
      = (4 / 3 : ℂ) * airyUpSqrt z + ((2 / 3 : ℂ) * (z * z⁻¹)) * airyUpSqrt z := by ring
    _ = 2 * airyUpSqrt z := by rw [mul_inv_cancel₀ hz0]; ring

lemma exp_lowerEc_sub_airyUpE_circle_bound {phi : ℝ → ℂ → ℂ} {c R ρ Cφ : ℝ}
    (hR4 : 4 ≤ R) (hRρ : R < ρ)
    (hφ_diff : DifferentiableOn ℂ (phi c) (ball 0 ρ))
    (hφ_real : ∀ x : ℝ, |x| ≤ R → (phi c (x : ℂ)).im = 0)
    (hφ_close : ∀ z ∈ closedBall (0 : ℂ) R, ‖phi c z - z‖ ≤ Cφ * c ^ (-(1 / 3 : ℝ)))
    (hφ_der : ∀ z ∈ closedBall (0 : ℂ) R, ‖deriv (phi c) z - 1‖ ≤ 1 / 2)
    (hstep : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ R / 4)
    (hsq_bd : 4 * R ^ (-(1 / 2 : ℝ)) * (Cφ * c ^ (-(1 / 3 : ℝ))) ^ 2 ≤ 1) :
    ∀ θ ∈ Icc (0 : ℝ) π,
      ‖Complex.exp (lowerEc phi c (circleMap 0 R θ)) - airyUpE (circleMap 0 R θ)‖ ≤
        (8 * R ^ (-(1 / 2 : ℝ)) * (Cφ * c ^ (-(1 / 3 : ℝ))) ^ 2) *
          ‖airyUpE (circleMap 0 R θ)‖ := by
  have hR0 : 0 < R := by linarith only [hR4]
  have him_ge := phi_im_ge_half_im hR0.le hRρ hφ_diff hφ_real hφ_der
  intro θ hθ
  set u := circleMap 0 R θ
  set w := phi c u
  have hu_norm : ‖u‖ = R := by simp [u, abs_of_pos hR0]
  have hu_im : 0 ≤ u.im := by
    rw [circleMap_zero_im]; exact mul_nonneg hR0.le (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)
  have hu_cl : u ∈ closedHalfDisc R := ⟨mem_closedBall_zero_iff.mpr hu_norm.le, hu_im⟩
  have hw_im : 0 ≤ w.im := le_trans (by linarith only [hu_im]) (him_ge u hu_cl)
  have hwu : ‖w - u‖ ≤ Cφ * c ^ (-(1 / 3 : ℝ)) := hφ_close u hu_cl.1
  let γ : ℝ → ℂ := fun t => (1 - (t : ℂ)) * w + (t : ℂ) * u
  have hγ_props : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (γ t).im ∧ 3 * R / 4 ≤ ‖γ t‖ := fun t ht => by
    have him : (γ t).im = (1 - t) * w.im + t * u.im := by
      dsimp [γ]; simp
    have him_nn : 0 ≤ (γ t).im := by
      rw [him]; exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hw_im) (mul_nonneg ht.1 hu_im)
    have hsub : γ t - u = ((1 - t : ℝ) : ℂ) * (w - u) := by dsimp [γ]; push_cast; ring
    have hnorm_sub : ‖γ t - u‖ ≤ R / 4 := by
      rw [hsub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr ht.2)]
      calc (1 - t) * ‖w - u‖ ≤ 1 * (R / 4) :=
            mul_le_mul (by linarith only [ht.1]) (hwu.trans hstep) (norm_nonneg _) zero_le_one
        _ = R / 4 := one_mul _
    have hge : 3 * R / 4 ≤ ‖γ t‖ := by
      have htri := norm_sub_norm_le u (γ t)
      rw [norm_sub_rev, hu_norm] at htri
      linarith only [htri, hnorm_sub]
    exact ⟨him_nn, hge⟩
  have hγ_ne : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ 0 := fun t ht h0 => by
    have hge := (hγ_props t ht).2
    rw [h0, norm_zero] at hge
    linarith only [hge, hR4]
  have hγ_deriv : ∀ t : ℝ, HasDerivAt γ (u - w) t := fun t => by
    have h1 := ((Complex.ofRealCLM.hasDerivAt (x := t)).const_sub 1).mul_const w
    have h2 := (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const u
    refine (h1.add h2).congr_deriv ?_
    simp [Complex.ofRealCLM_apply]; ring
  let E : ℂ → ℂ := fun z => (4 / 3 : ℂ) * z * airyUpSqrt z
  let E' : ℂ → ℂ := fun z => 2 * airyUpSqrt z
  let E'' : ℂ → ℂ := fun z => z⁻¹ * airyUpSqrt z
  have hE_d : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s => E (γ s)) (E' (γ t) * (u - w)) t := fun t ht => by
    rw [uIcc_of_le zero_le_one] at ht
    exact (hasDerivAt_E_main (hγ_props t ht).1 (hγ_ne t ht)).comp t (hγ_deriv t)
  have hE'_d : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (fun τ => E' (γ τ)) (E'' (γ s) * (u - w)) s := fun s hs => by
    have hs1 := (hasDerivAt_airyUpSqrt (hγ_props s hs).1 (hγ_ne s hs)).const_mul (2 : ℂ)
    have hc : HasDerivAt (fun τ => E' (γ τ)) ((2 * ((1 / 2 : ℂ) * (γ s)⁻¹ * airyUpSqrt (γ s))) * (u - w)) s :=
      hs1.comp s (hγ_deriv s)
    refine hc.congr_deriv ?_
    dsimp [E'']; ring
  have hE''_cont : ContinuousOn (fun s => E'' (γ s) * (u - w)) (Icc 0 1) := by
    refine (((ContinuousOn.inv₀ ?_ fun s hs => hγ_ne s hs).mul ?_).mul continuousOn_const)
    · exact fun s _ => (hγ_deriv s).continuousAt.continuousWithinAt
    · exact continuousOn_airyUpSqrt_half.comp (fun s _ => (hγ_deriv s).continuousAt.continuousWithinAt)
        fun s hs => (hγ_props s hs).1
  have hE'_cont : ContinuousOn (fun t => E' (γ t) * (u - w)) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact (continuousOn_const.mul (continuousOn_airyUpSqrt_half.comp
      (fun t _ => (hγ_deriv t).continuousAt.continuousWithinAt) fun t ht => (hγ_props t ht).1)).mul
      continuousOn_const
  have hftc1 : ∫ t in (0 : ℝ)..1, E' (γ t) * (u - w) = E u - E w := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hE_d hE'_cont.intervalIntegrable
    have hg0 : γ 0 = w := by dsimp [γ]; simp
    have hg1 : γ 1 = u := by dsimp [γ]; simp
    simpa only [hg0, hg1] using h
  have hdiff_eq : lowerEc phi c u - (4 / 3 : ℂ) * u * airyUpSqrt u =
      ∫ t in (0 : ℝ)..1, (E' w - E' (γ t)) * (u - w) := by
    have hlhs : lowerEc phi c u - (4 / 3 : ℂ) * u * airyUpSqrt u =
        E' w * (u - w) - (E u - E w) := by
      dsimp [lowerEc, E, E', w]; ring
    rw [hlhs, ← hftc1, ← intervalIntegral.integral_const (a := (0 : ℝ)) (b := 1) (E' w * (u - w)),
      sub_zero, one_smul]
    rw [← intervalIntegral.integral_sub intervalIntegrable_const hE'_cont.intervalIntegrable]
    refine intervalIntegral.integral_congr fun t _ => by ring
  have h_pt_diff : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖E' w - E' (γ t)‖ ≤ 4 * R ^ (-(1 / 2 : ℝ)) * ‖u - w‖ := fun t ht => by
    have hftc2 : ∫ s in (0 : ℝ)..t, E'' (γ s) * (u - w) = E' (γ t) - E' w := by
      have hh : ∀ s ∈ uIcc (0 : ℝ) t, HasDerivAt (fun τ => E' (γ τ)) (E'' (γ s) * (u - w)) s := by
        intro s hs; rw [uIcc_of_le ht.1] at hs
        exact hE'_d s ⟨hs.1, hs.2.trans ht.2⟩
      have hc : IntervalIntegrable (fun s => E'' (γ s) * (u - w)) volume 0 t :=
        (hE''_cont.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hh hc
      have hg0 : γ 0 = w := by dsimp [γ]; simp
      simpa only [hg0] using h
    rw [norm_sub_rev, ← hftc2]
    have hni := intervalIntegral.norm_integral_le_of_le_const (a := (0 : ℝ)) (b := t)
      (C := 4 * R ^ (-(1 / 2 : ℝ)) * ‖u - w‖) (fun s hs => by
        rw [uIoc_of_le ht.1] at hs
        have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.trans ht.2⟩
        have hgs := (hγ_props s hsI).2
        have hgs_pos : 0 < ‖γ s‖ := by linarith only [hgs, hR4]
        have hn : ‖E'' (γ s) * (u - w)‖ = ‖γ s‖ ^ (-(1 / 2 : ℝ)) * ‖u - w‖ := by
          dsimp [E'']
          rw [norm_mul, norm_mul, norm_inv, norm_airyUpSqrt, Real.sqrt_eq_rpow]
          have hpow : ‖γ s‖⁻¹ * ‖γ s‖ ^ (1 / 2 : ℝ) = ‖γ s‖ ^ (-(1 / 2 : ℝ)) := by
            rw [← Real.rpow_neg_one, ← Real.rpow_add hgs_pos]; norm_num
          rw [hpow]
        rw [hn]
        have hrpow : ‖γ s‖ ^ (-(1 / 2 : ℝ)) ≤ 4 * R ^ (-(1 / 2 : ℝ)) := by
          have h1 : ‖γ s‖ ^ (-(1 / 2 : ℝ)) ≤ (3 * R / 4) ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hgs (by norm_num)
          have h2 : (3 * R / 4) ^ (-(1 / 2 : ℝ)) ≤ (R / 16) ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith only [hR0]) (by norm_num)
          have h3 : (R / 16) ^ (-(1 / 2 : ℝ)) = 4 * R ^ (-(1 / 2 : ℝ)) := by
            rw [div_eq_mul_inv, Real.mul_rpow hR0.le (by positivity),
              show ((16 : ℝ)⁻¹) ^ (-(1 / 2 : ℝ)) = 4 by
                rw [Real.rpow_neg (by positivity), Real.inv_rpow (by positivity), inv_inv,
                  show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast,
                  ← Real.rpow_mul (by positivity)]
                norm_num]
            ring
          exact h1.trans (h2.trans_eq h3)
        exact mul_le_mul_of_nonneg_right hrpow (norm_nonneg _))
    calc ‖∫ s in (0 : ℝ)..t, E'' (γ s) * (u - w)‖
        ≤ (4 * R ^ (-(1 / 2 : ℝ)) * ‖u - w‖) * |t - 0| := hni
      _ ≤ (4 * R ^ (-(1 / 2 : ℝ)) * ‖u - w‖) * 1 := by
          gcongr; rw [sub_zero, abs_of_nonneg ht.1]; exact ht.2
      _ = 4 * R ^ (-(1 / 2 : ℝ)) * ‖u - w‖ := mul_one _
  have hΔ_bd : ‖lowerEc phi c u - (4 / 3 : ℂ) * u * airyUpSqrt u‖ ≤
      4 * R ^ (-(1 / 2 : ℝ)) * (Cφ * c ^ (-(1 / 3 : ℝ))) ^ 2 := by
    rw [hdiff_eq]
    have hni := intervalIntegral.norm_integral_le_of_le_const (a := (0 : ℝ)) (b := 1)
      (C := 4 * R ^ (-(1 / 2 : ℝ)) * (Cφ * c ^ (-(1 / 3 : ℝ))) ^ 2) (fun t ht => by
        rw [uIoc_of_le zero_le_one] at ht
        rw [norm_mul]
        calc ‖E' w - E' (γ t)‖ * ‖u - w‖
            ≤ (4 * R ^ (-(1 / 2 : ℝ)) * ‖u - w‖) * ‖u - w‖ :=
              mul_le_mul_of_nonneg_right (h_pt_diff t ⟨ht.1.le, ht.2⟩) (norm_nonneg _)
          _ = 4 * R ^ (-(1 / 2 : ℝ)) * ‖u - w‖ ^ 2 := by ring
          _ ≤ 4 * R ^ (-(1 / 2 : ℝ)) * (Cφ * c ^ (-(1 / 3 : ℝ))) ^ 2 := by gcongr)
    simpa only [sub_zero, abs_one, mul_one] using hni
  have hΔ_le1 : ‖lowerEc phi c u - (4 / 3 : ℂ) * u * airyUpSqrt u‖ ≤ 1 := hΔ_bd.trans hsq_bd
  have hexp_sub : Complex.exp (lowerEc phi c u) - airyUpE u =
      airyUpE u * (Complex.exp (lowerEc phi c u - (4 / 3 : ℂ) * u * airyUpSqrt u) - 1) := by
    rw [airyUpE_eq_exp_airyUpSqrt, mul_sub, ← Complex.exp_add, mul_one]
    ring_nf
  rw [hexp_sub, norm_mul, mul_comm ‖airyUpE u‖]
  have hexp1 : ‖Complex.exp (lowerEc phi c u - (4 / 3 : ℂ) * u * airyUpSqrt u) - 1‖ ≤
      2 * ‖lowerEc phi c u - (4 / 3 : ℂ) * u * airyUpSqrt u‖ :=
    Complex.norm_exp_sub_one_le hΔ_le1
  have h2Δ : 2 * ‖lowerEc phi c u - (4 / 3 : ℂ) * u * airyUpSqrt u‖ ≤
      8 * R ^ (-(1 / 2 : ℝ)) * (Cφ * c ^ (-(1 / 3 : ℝ))) ^ 2 := by
    linarith only [hΔ_bd]
  exact mul_le_mul_of_nonneg_right (hexp1.trans h2Δ) (norm_nonneg _)

/-! ### 3. General-radius `calD_up` orthogonality and `fsK` match -/

lemma calD_up_im_add_airyUpE_im_eq_fsK (x : ℝ) :
    (calD_up (x : ℂ)).im + (airyUpE (x : ℂ)).im = fsK x := by
  rw [calD_up_im_real, airyUpE_im_real]
  unfold fsK
  split_ifs <;> ring

/-- General-radius `calD_up` orthogonality (`cts:D-orth`) for any real-symmetric holomorphic `F`. -/
theorem virasoro_D_orth_of_holo {F : ℂ → ℂ} {ρ R : ℝ}
    (hR1 : 1 ≤ R) (hRρ : R < ρ)
    (hF_diff : DifferentiableOn ℂ F (ball 0 ρ))
    (hF_real : ∀ x : ℝ, |x| ≤ R → (F (x : ℂ)).im = 0) :
    |∫ x in (-R)..R, (F (x : ℂ)).re * (calD_up (x : ℂ)).im| ≤
      (11 * R ^ (-(3 / 2 : ℝ))) *
        ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) := by
  have hR0 : 0 < R := by linarith only [hR1]
  have hK_bd : ∀ θ ∈ Icc (0 : ℝ) π,
      ‖calD_up (circleMap 0 R θ)‖ ≤ (11 * R ^ (-(3 / 2 : ℝ))) * ‖airyUpE (circleMap 0 R θ)‖ := by
    intro θ hθ
    have hu0 : circleMap 0 R θ ≠ 0 := by simp [circleMap, hR0.ne']
    have huim : 0 ≤ (circleMap 0 R θ).im := by
      rw [circleMap_zero_im]; exact mul_nonneg hR0.le (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)
    have hun : ‖circleMap 0 R θ‖ = R := by simp [norm_circleMap_zero, abs_of_pos hR0]
    rw [calD_up_eq_calD huim hu0]
    have hcb := CtAiryHplus.calD_bound (u := circleMap 0 R θ) huim hu0 (by rw [hun]; exact hR1)
    rw [hun] at hcb
    have hE : ‖airyUpE (circleMap 0 R θ)‖ = Real.exp ((4 / 3) * (circleMap 0 R θ ^ (3 / 2 : ℂ)).re) := by
      rw [airyUpE_eq_cexp huim hu0, Complex.norm_exp]; simp [Complex.mul_re]
    rwa [← hE] at hcb
  have hmain := halfDisc_im_bound (F := F) (K := calD_up) hR0 hRρ (by positivity)
    (fun z hz => hF_diff.differentiableAt (isOpen_ball.mem_nhds ((ball_subset_ball hRρ.le) hz.1)) |>.differentiableWithinAt)
    hF_real continuousOn_calD_up differentiableOn_calD_up hK_bd
  have hcongr : ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖ =
      ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) := by
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le Real.pi_pos.le] at hθ
    have huim : 0 ≤ (circleMap 0 R θ).im := by
      rw [circleMap_zero_im]; exact mul_nonneg hR0.le (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)
    rw [div_eq_mul_inv, ← norm_airyUpE huim]
  rwa [hcongr] at hmain

/-! ### 4. Real-axis `lowerEc` match and slit-phase window cancellation (`virasoro_slit_phase_window_bound`) -/

private lemma lowerEc_ofReal_neg_sin {c u ut : ℝ} (hc2 : 2 ≤ c)
    (hut_lo : -(5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ)) ≤ ut) (hut_neg : ut < 0)
    (hu_eq : virasoroUhat c ut = u) :
    let x := √(3 * virasoroDeltaChart c ut / c)
    (Complex.exp ((4 / 3 : ℂ) * (ut : ℂ) * airyUpSqrt (ut : ℂ) +
      2 * airyUpSqrt (ut : ℂ) * ((u : ℂ) - (ut : ℂ)))).im =
      Real.sin (lowerThetaEps Gout (c ^ (-2 : ℝ)) (lowerY x) - 2 * π * c * cumulN x) := by
  intro x
  have hc0 : 0 < c := by linarith only [hc2]
  have hv_pos : 0 < -ut := by linarith only [hut_neg]
  have hsqrt : airyUpSqrt (ut : ℂ) = ((√(-ut) : ℝ) : ℂ) * I := by
    simpa only [neg_neg] using airyUpSqrt_ofReal_neg hv_pos
  rw [hsqrt]
  have hexp_eq : (4 / 3 : ℂ) * (ut : ℂ) * (((√(-ut) : ℝ) : ℂ) * I) +
      2 * (((√(-ut) : ℝ) : ℂ) * I) * ((u : ℂ) - (ut : ℂ)) =
      (((2 * √(-ut) * (u - ut) - 4 / 3 * (-ut) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * I) := by
    have hpow : -ut * √(-ut) = (-ut) ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      calc -ut * (-ut) ^ (1 / 2 : ℝ) = (-ut) ^ (1 : ℝ) * (-ut) ^ (1 / 2 : ℝ) := by simp
        _ = (-ut) ^ (1 + 1 / 2 : ℝ) := (Real.rpow_add hv_pos 1 (1 / 2)).symm
        _ = (-ut) ^ (3 / 2 : ℝ) := by norm_num
    have hpowC : ((ut : ℂ) * ((√(-ut) : ℝ) : ℂ)) = -(((-ut) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, show ut * √(-ut) = -(-ut * √(-ut)) by ring, hpow, Complex.ofReal_neg]
    calc (4 / 3 : ℂ) * (ut : ℂ) * (((√(-ut) : ℝ) : ℂ) * I) +
          2 * (((√(-ut) : ℝ) : ℂ) * I) * ((u : ℂ) - (ut : ℂ))
        = (4 / 3 : ℂ) * ((ut : ℂ) * ((√(-ut) : ℝ) : ℂ)) * I +
            2 * ((√(-ut) : ℝ) : ℂ) * ((u : ℂ) - (ut : ℂ)) * I := by ring
      _ = (-(4 / 3 : ℂ) * (((-ut) ^ (3 / 2 : ℝ) : ℝ) : ℂ) +
            2 * ((√(-ut) : ℝ) : ℂ) * ((u : ℂ) - (ut : ℂ))) * I := by rw [hpowC]; ring
      _ = (((2 * √(-ut) * (u - ut) - 4 / 3 * (-ut) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * I) := by
          push_cast; ring
  rw [hexp_eq, Complex.exp_mul_I]
  have him : (Complex.cos ((2 * √(-ut) * (u - ut) - 4 / 3 * (-ut) ^ (3 / 2 : ℝ) : ℝ) : ℂ) +
      Complex.sin ((2 * √(-ut) * (u - ut) - 4 / 3 * (-ut) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * I).im =
      Real.sin (2 * √(-ut) * (u - ut) - 4 / 3 * (-ut) ^ (3 / 2 : ℝ)) := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]; simp
  rw [him]
  have hpm := virasoroUhat_phase_match hc2 hut_lo hut_neg
  have hth_eq : 2 * √(-ut) * (u - ut) = lowerThetaEps Gout (c ^ (-2 : ℝ)) (lowerY x) := by
    rw [← hu_eq]
    unfold lowerThetaEps lowerMt lowerY
    exact hpm.2.2
  have htau : tauPhase x = -ut / (betaTip * c ^ (2 / 3 : ℝ)) := (lowerLangerPhase_band hc0 hut_lo hut_neg).1
  have hcum_eq : 4 / 3 * (-ut) ^ (3 / 2 : ℝ) = 2 * π * c * cumulN x := by
    have hbeta : betaTip ^ (3 / 2 : ℝ) = 3 * KTip / 4 := by
      unfold betaTip
      rw [← Real.rpow_mul (by unfold KTip kTip; have := Real.pi_pos; positivity)]
      norm_num
    have htau_pow : tauPhase x ^ (3 / 2 : ℝ) = cumulN x / kTip := by
      unfold tauPhase
      have hc_nn : 0 ≤ cumulN x := by
        have hlt := (lowerLangerPhase_band hc0 hut_lo hut_neg).2.2
        have h1 := cumulN_strictMonoOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hlt.le) hlt
        rw [cumulN_xiStar] at h1; exact h1.le
      rw [← Real.rpow_mul (div_nonneg hc_nn kTip_pos.le)]
      norm_num
    have hut_eq : -ut = betaTip * c ^ (2 / 3 : ℝ) * tauPhase x := by
      rw [htau]; have hβ := betaTip_pos.ne'; have hc23 := (Real.rpow_pos_of_pos hc0 (2 / 3 : ℝ)).ne'
      field_simp [hβ, hc23]
    have htau_nn : 0 ≤ tauPhase x := by
      rw [htau]; exact div_nonneg hv_pos.le (mul_nonneg betaTip_pos.le (Real.rpow_nonneg hc0.le _))
    rw [hut_eq, Real.mul_rpow (mul_nonneg betaTip_pos.le (Real.rpow_nonneg hc0.le _)) htau_nn,
      Real.mul_rpow betaTip_pos.le (Real.rpow_nonneg hc0.le _),
      ← Real.rpow_mul hc0.le, show (2 / 3 : ℝ) * (3 / 2 : ℝ) = 1 by norm_num, Real.rpow_one,
      hbeta, htau_pow]
    unfold KTip
    have hk := kTip_pos.ne'
    field_simp [hk]; ring
  rw [hth_eq, hcum_eq]

private lemma one_sub_lowerWeps_le_on_window {c x X_hi : ℝ} (hc2 : 2 ≤ c)
    (hx_gt : xiStar < x) (hx_le : x ≤ X_hi) :
    |1 - lowerWeps (c ^ (-2 : ℝ)) (lowerY x)| ≤
      (4 / slitA X_hi ^ 2) * c ^ (-2 : ℝ) := by
  have hc0 : 0 < c := by linarith only [hc2]
  have hε0 : 0 ≤ c ^ (-2 : ℝ) := Real.rpow_nonneg hc0.le _
  have hε1 : c ^ (-2 : ℝ) ≤ 1 / 4 := by
    rw [Real.rpow_neg hc0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (c ^ 2)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by nlinarith only [hc2])
      _ = 1 / 4 := by norm_num
  have hW_eq := lowerWeps_eq hε0 hx_gt
  set ε := c ^ (-2 : ℝ)
  set a := slitA x
  have ha_pos : 0 < a := slitA_pos x
  have ha_lt1 : a < 1 := slitA_lt_one hx_gt
  have hden_ge : a ^ 2 ≤ mtDen ε a := by
    unfold mtDen
    have h1 : 0 ≤ ε ^ 2 * (1 - a) := mul_nonneg (sq_nonneg _) (by linarith only [ha_lt1])
    nlinarith only [ha_pos, hε0, h1]
  have hsub_eq : 1 - lowerWeps ε (lowerY x) =
      (2 * a * (1 - a) * ε + (2 - a - a ^ 2) * ε ^ 2) / mtDen ε a := by
    rw [hW_eq]
    have hden_pos : 0 < mtDen ε a := by linarith only [sq_pos_of_pos ha_pos, hden_ge]
    unfold mtDen
    field_simp [hden_pos.ne']
    ring
  have hnum_nn : 0 ≤ 2 * a * (1 - a) * ε + (2 - a - a ^ 2) * ε ^ 2 := by
    have h1 : 0 ≤ 2 * a * (1 - a) * ε := mul_nonneg (mul_nonneg (by positivity) (by linarith only [ha_lt1])) hε0
    have h2 : 0 ≤ (2 - a - a ^ 2) * ε ^ 2 := by
      have ha2 : a ^ 2 < 1 := by nlinarith only [ha_pos, ha_lt1]
      exact mul_nonneg (by linarith only [ha_lt1, ha2]) (sq_nonneg _)
    linarith only [h1, h2]
  have hnum_le : 2 * a * (1 - a) * ε + (2 - a - a ^ 2) * ε ^ 2 ≤ 4 * ε := by
    have h1 : 2 * a * (1 - a) * ε ≤ 2 * ε := by
      have hm : a * (1 - a) ≤ 1 := by nlinarith only [ha_pos, ha_lt1]
      nlinarith only [hm, hε0]
    have h2 : (2 - a - a ^ 2) * ε ^ 2 ≤ 2 * ε := by
      have hesq : ε ^ 2 ≤ ε := by nlinarith only [hε0, hε1]
      have ha2 : 0 ≤ 2 - a - a ^ 2 := by nlinarith only [ha_pos, ha_lt1]
      have hbd : 2 - a - a ^ 2 ≤ 2 := by nlinarith only [ha_pos]
      calc (2 - a - a ^ 2) * ε ^ 2 ≤ 2 * ε ^ 2 := mul_le_mul_of_nonneg_right hbd (sq_nonneg _)
        _ ≤ 2 * ε := mul_le_mul_of_nonneg_left hesq (by norm_num)
    linarith only [h1, h2]
  have ha_ge : slitA X_hi ≤ a := by
    unfold slitA
    have hX_pos : 0 < X_hi := xiStar_pos.trans (hx_gt.trans_le hx_le)
    have hcosh : Real.cosh (π * x) ≤ Real.cosh (π * X_hi) := by
      rw [Real.cosh_le_cosh, abs_of_pos (mul_pos Real.pi_pos (xiStar_pos.trans hx_gt)),
        abs_of_pos (mul_pos Real.pi_pos hX_pos)]
      exact mul_le_mul_of_nonneg_left hx_le Real.pi_pos.le
    exact div_le_div_of_nonneg_left (by positivity) (by have := Real.cosh_pos (π * x); positivity)
      (by linarith only [hcosh])
  have hden_ge_hi : slitA X_hi ^ 2 ≤ mtDen ε a :=
    (pow_le_pow_left₀ (slitA_pos X_hi).le ha_ge 2).trans hden_ge
  have hden_pos : 0 < mtDen ε a := lt_of_lt_of_le (sq_pos_of_pos (slitA_pos X_hi)) hden_ge_hi
  rw [hsub_eq, abs_of_nonneg (div_nonneg hnum_nn hden_pos.le)]
  calc (2 * a * (1 - a) * ε + (2 - a - a ^ 2) * ε ^ 2) / mtDen ε a
      ≤ (4 * ε) / slitA X_hi ^ 2 :=
        div_le_div₀ (by positivity) hnum_le (sq_pos_of_pos (slitA_pos X_hi)) hden_ge_hi
    _ = (4 / slitA X_hi ^ 2) * ε := by ring

/-- **`cts:combined-residual` (window slit-phase cancellation)**:
for every fixed `cl > 0`, uniformly for `cl * c^{2/3} ≤ R ≤ lowerRmax virasoroC1 c` and weakly feasible
`g` of `virasoroProblem`,
`|I_win(R) + X₀(R)| ≤ C * (c⁻¹ * lowerEta virasoroProblem virasoroPhi c g R + c ^ (-(4 / 3 : ℝ)))`. -/
theorem virasoro_slit_phase_window_bound {cl : ℝ} (hcl : 0 < cl) :
    ∃ cc C : ℝ, virasoroCQEnv ≤ cc ∧ 0 ≤ C ∧
      ∀ {c T R : ℝ} {g : ℝ → ℝ}, cc ≤ c →
        virasoroProblem.IsWeaklyFeasible (c / 12) T g →
        cl * c ^ (2 / 3 : ℝ) ≤ R → R ≤ lowerRmax virasoroC1 c →
          |(virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
              ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c (virasoroPhi c ((-R : ℝ) : ℂ)).re),
                (g t * virasoroProblem.cardyV (c / 12) t) *
                  lowerWeps (c ^ (-2 : ℝ)) (lowerY (√(3 * t / c))) *
                  Real.sin (lowerThetaEps Gout (c ^ (-2 : ℝ)) (lowerY (√(3 * t / c))) -
                    2 * π * c * cumulN (√(3 * t / c))) +
            ∫ v in (0 : ℝ)..R,
              (lowerF virasoroProblem virasoroPhi c g ((-v : ℝ) : ℂ)).re *
                Real.sin (4 / 3 * v ^ (3 / 2 : ℝ))| ≤
            C * (c⁻¹ * lowerEta virasoroProblem virasoroPhi c g R + c ^ (-(4 / 3 : ℝ))) := by
  obtain ⟨cc_h, _, hcc_hQ, _, hHolo⟩ := lowerF_virasoro_holo_real
  obtain ⟨cc_ch, Cφ, hCφ_nn, hCh⟩ := virasoroChart_holds
  let C_arc := 8 * cl ^ (-(1 / 2 : ℝ)) * Cφ ^ 2
  let X_hi := xiStar + chartParams.r_τ
  let C_w := 4 / slitA X_hi ^ 2
  let cc : ℝ := max (max cc_h cc_ch) (max (max ((4 / cl) ^ (3 / 2 : ℝ) + 1)
    ((max (4 * Cφ) (4 * cl ^ (-(1 / 2 : ℝ)) * Cφ ^ 2) + 2) ^ 3 + 1))
    ((1 / (2 * virasoroC1 ^ 2)) ^ (3 / 2 : ℝ) + 1))
  refine ⟨cc, max C_arc C_w, hcc_hQ.trans ((le_max_left _ _).trans (le_max_left _ _)),
    le_max_of_le_left (by positivity), ?_⟩
  intro c T R g hc hwf hR_lo hR_hi
  have hc_h : cc_h ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hc_ch : cc_ch ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hc_R4 : (4 / cl) ^ (3 / 2 : ℝ) + 1 ≤ c :=
    ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hc
  have hc_step : (max (4 * Cφ) (4 * cl ^ (-(1 / 2 : ℝ)) * Cφ ^ 2) + 2) ^ 3 + 1 ≤ c :=
    ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hc
  have hc_rmin : (1 / (2 * virasoroC1 ^ 2)) ^ (3 / 2 : ℝ) + 1 ≤ c :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  have hc_Q : virasoroCQEnv ≤ c := hcc_hQ.trans hc_h
  have hc_10000 : 10000 ≤ c :=
    (by unfold virasoroCQEnv; norm_num : (10000 : ℝ) ≤ virasoroCQEnv).trans hc_Q
  have hc0 : 0 < c := by linarith only [hc_10000]
  have hc2 : 2 ≤ c := by linarith only [hc_10000]
  have hc23_pos : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hR4 : 4 ≤ R := by
    have hp := Real.rpow_le_rpow (by positivity) (by linarith only [hc_R4] : (4 / cl) ^ (3 / 2 : ℝ) ≤ c)
      (by norm_num : (0 : ℝ) ≤ 2 / 3)
    rw [← Real.rpow_mul (by positivity)] at hp
    norm_num at hp
    calc 4 = cl * (4 / cl) := by field_simp [hcl.ne']
      _ ≤ cl * c ^ (2 / 3 : ℝ) := mul_le_mul_of_nonneg_left hp hcl.le
      _ ≤ R := hR_lo
  have hR0 : 0 < R := by linarith only [hR4]
  have hc_pos3 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hc13_ge : max (4 * Cφ) (4 * cl ^ (-(1 / 2 : ℝ)) * Cφ ^ 2) + 2 ≤ c ^ (1 / 3 : ℝ) := by
    have h1 : (max (4 * Cφ) (4 * cl ^ (-(1 / 2 : ℝ)) * Cφ ^ 2) + 2) ^ (3 : ℕ) ≤ c := by
      linarith only [hc_step]
    have hp := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rwa [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity),
      show ((3 : ℕ) : ℝ) * (1 / 3 : ℝ) = 1 by norm_num, Real.rpow_one] at hp
  have hCφ_c13 : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 4 := by
    rw [Real.rpow_neg hc0.le]
    have h4 : 4 * Cφ ≤ c ^ (1 / 3 : ℝ) := le_trans (le_trans (le_max_left _ _) (by linarith)) hc13_ge
    rw [← div_eq_mul_inv, div_le_iff₀ hc_pos3]; linarith only [h4]
  have hCφ_step : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ R / 4 := hCφ_c13.trans (by linarith only [hR4])
  have hsq_bd : 4 * R ^ (-(1 / 2 : ℝ)) * (Cφ * c ^ (-(1 / 3 : ℝ))) ^ 2 ≤ 1 := by
    have hR12 : R ^ (-(1 / 2 : ℝ)) ≤ (cl * c ^ (2 / 3 : ℝ)) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hR_lo (by norm_num)
    have hcl_pow : (cl * c ^ (2 / 3 : ℝ)) ^ (-(1 / 2 : ℝ)) =
        cl ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 3 : ℝ)) := by
      rw [Real.mul_rpow hcl.le hc23_pos.le, ← Real.rpow_mul hc0.le]; norm_num
    rw [hcl_pow] at hR12
    have hpow3 : c ^ (-(1 / 3 : ℝ)) * (c ^ (-(1 / 3 : ℝ))) ^ 2 = c⁻¹ := by
      rw [Real.rpow_neg hc0.le, show (c ^ (1 / 3 : ℝ))⁻¹ * ((c ^ (1 / 3 : ℝ))⁻¹) ^ 2 =
        ((c ^ (1 / 3 : ℝ)) ^ (3 : ℕ))⁻¹ by ring, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
      norm_num
    have h1 : 4 * R ^ (-(1 / 2 : ℝ)) * (Cφ * c ^ (-(1 / 3 : ℝ))) ^ 2 ≤
        4 * cl ^ (-(1 / 2 : ℝ)) * Cφ ^ 2 * c⁻¹ := by
      calc 4 * R ^ (-(1 / 2 : ℝ)) * (Cφ * c ^ (-(1 / 3 : ℝ))) ^ 2
          ≤ 4 * (cl ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 3 : ℝ))) * (Cφ ^ 2 * (c ^ (-(1 / 3 : ℝ))) ^ 2) := by
            gcongr
        _ = 4 * cl ^ (-(1 / 2 : ℝ)) * Cφ ^ 2 * (c ^ (-(1 / 3 : ℝ)) * (c ^ (-(1 / 3 : ℝ))) ^ 2) := by ring
        _ = _ := by rw [hpow3]
    have h2 : 4 * cl ^ (-(1 / 2 : ℝ)) * Cφ ^ 2 ≤ c := by
      have hle : 4 * cl ^ (-(1 / 2 : ℝ)) * Cφ ^ 2 ≤ c ^ (1 / 3 : ℝ) :=
        (le_max_right _ _).trans (by linarith only [hc13_ge])
      have h13_le_c : c ^ (1 / 3 : ℝ) ≤ c :=
        Real.rpow_le_self_of_one_le (by linarith only [hc_10000]) (by norm_num)
      exact hle.trans h13_le_c
    exact h1.trans (by rw [← div_eq_mul_inv, div_le_one hc0]; exact h2)
  have hCφ_c1 : Cφ * c ^ (-1 : ℝ) ≤ 1 / 2 := by
    have hc13_le_c : c ^ (-(1 : ℝ)) ≤ c ^ (-(1 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith only [hc_10000]) (by norm_num)
    exact (mul_le_mul_of_nonneg_left hc13_le_c hCφ_nn).trans (hCφ_c13.trans (by norm_num))
  -- Construct `R_top ∈ [lowerRmin, lowerRmax]` to apply `lowerF_virasoro_holo_real`:
  let R_top := max R (lowerRmin virasoroC1 c)
  have hR_top_range : LowerRadiusRange virasoroC1 c R_top := by
    have hc1_pos := virasoroC1_pos
    refine ⟨le_max_right _ _, max_le hR_hi ?_⟩
    unfold lowerRmin lowerRmax
    nlinarith only [hc23_pos, sq_nonneg virasoroC1]
  have hR_le_top : R ≤ R_top := le_max_left _ _
  obtain ⟨R', hR_top_lt, hf_diff, _, hf_real, hR'_A2, _, _⟩ :=
    hHolo hc_h hwf hR_top_range
  have hRρ' : R < R' := hR_le_top.trans_lt hR_top_lt
  obtain ⟨ρ_ch, hrm_lt_ρ, hφ_diff, hφ_im_ch, hφ_der_ch, hφ_uhat_ch, _⟩ := hCh c hc_ch
  have hR_lt_ρch : R < ρ_ch := hR_hi.trans_lt hrm_lt_ρ
  have hφ_real_R : ∀ x : ℝ, |x| ≤ R → (virasoroPhi c (x : ℂ)).im = 0 := fun x hx =>
    hφ_im_ch x (hx.trans hR_hi)
  have hφ_close_R : ∀ z ∈ closedBall (0 : ℂ) R, ‖virasoroPhi c z - z‖ ≤ Cφ * c ^ (-(1 / 3 : ℝ)) :=
    fun z hz => (hφ_der_ch z ((mem_closedBall_zero_iff.mp hz).trans hR_hi)).1
  have hφ_der_R : ∀ z ∈ closedBall (0 : ℂ) R, ‖deriv (virasoroPhi c) z - 1‖ ≤ 1 / 2 :=
    fun z hz => ((hφ_der_ch z ((mem_closedBall_zero_iff.mp hz).trans hR_hi)).2).trans hCφ_c1
  have hf_real_R : ∀ x : ℝ, |x| ≤ R → (lowerF virasoroProblem virasoroPhi c g (x : ℂ)).im = 0 :=
    fun x hx => hf_real x (hx.trans hR_le_top)
  -- 1. Apply `halfDisc_im_bound` to `F = lowerF` and `K = exp(lowerEc) - airyUpE`:
  obtain ⟨hK_cont_ec, hK_diff_ec⟩ := lowerEc_holo_cont hR0.le hR_lt_ρch hφ_diff hφ_real_R hφ_der_R
  let K : ℂ → ℂ := fun u => Complex.exp (lowerEc virasoroPhi c u) - airyUpE u
  have hK_cont : ContinuousOn K (closedHalfDisc R) :=
    hK_cont_ec.cexp.sub (continuousOn_airyUpE.mono fun _ hu => hu.2)
  have hK_diff : DifferentiableOn ℂ K (openHalfDisc R) :=
    hK_diff_ec.cexp.sub fun _ hu => (differentiableAt_airyUpE hu.2).differentiableWithinAt
  have hK_circ_bd := exp_lowerEc_sub_airyUpE_circle_bound hR4 hR_lt_ρch hφ_diff hφ_real_R
    hφ_close_R hφ_der_R hCφ_step hsq_bd
  have hB_nn : 0 ≤ 8 * R ^ (-(1 / 2 : ℝ)) * (Cφ * c ^ (-(1 / 3 : ℝ))) ^ 2 := by positivity
  have him_bd := halfDisc_im_bound hR0 hRρ' hB_nn
    (fun z hz => hf_diff.differentiableAt (isOpen_ball.mem_nhds ((ball_subset_ball hRρ'.le) hz.1)) |>.differentiableWithinAt)
    hf_real_R hK_cont hK_diff hK_circ_bd
  have hcoef_le : 8 * R ^ (-(1 / 2 : ℝ)) * (Cφ * c ^ (-(1 / 3 : ℝ))) ^ 2 ≤ C_arc * c⁻¹ := by
    have hR12 : R ^ (-(1 / 2 : ℝ)) ≤ (cl * c ^ (2 / 3 : ℝ)) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hR_lo (by norm_num)
    have hcl_pow : (cl * c ^ (2 / 3 : ℝ)) ^ (-(1 / 2 : ℝ)) =
        cl ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 3 : ℝ)) := by
      rw [Real.mul_rpow hcl.le hc23_pos.le, ← Real.rpow_mul hc0.le]; norm_num
    rw [hcl_pow] at hR12
    have hpow3 : c ^ (-(1 / 3 : ℝ)) * (c ^ (-(1 / 3 : ℝ))) ^ 2 = c⁻¹ := by
      rw [Real.rpow_neg hc0.le, show (c ^ (1 / 3 : ℝ))⁻¹ * ((c ^ (1 / 3 : ℝ))⁻¹) ^ 2 =
        ((c ^ (1 / 3 : ℝ)) ^ (3 : ℕ))⁻¹ by ring, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
      norm_num
    calc 8 * R ^ (-(1 / 2 : ℝ)) * (Cφ * c ^ (-(1 / 3 : ℝ))) ^ 2
        ≤ 8 * (cl ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 3 : ℝ))) * (Cφ ^ 2 * (c ^ (-(1 / 3 : ℝ))) ^ 2) := by
          gcongr
      _ = 8 * cl ^ (-(1 / 2 : ℝ)) * Cφ ^ 2 * (c ^ (-(1 / 3 : ℝ)) * (c ^ (-(1 / 3 : ℝ))) ^ 2) := by ring
      _ = C_arc * c⁻¹ := by dsimp [C_arc]; rw [hpow3]
  -- Bound the circle integral by `lowerEta`:
  have hη_ge_half :
      (∫ θ in (0 : ℝ)..π, R * ‖lowerF virasoroProblem virasoroPhi c g (circleMap 0 R θ)‖ *
        ‖airyUpE (circleMap 0 R θ)‖) ≤ lowerEta virasoroProblem virasoroPhi c g R := by
    have hR_lt_A2 : R < virasoroAC c ^ 2 := by
      have hbv := virasoroC1_small.trans virasoroBVChoice_le
      have h4 : 4 * virasoroC1 ^ 2 < 2 * virasoroBV ^ 2 := by
        have := virasoroC1_pos; nlinarith only [hbv, this]
      have hrm : R ≤ 4 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) := hR_hi
      rw [virasoroAC_sq c hc0.le]
      nlinarith only [hrm, h4, hc23_pos]
    have hψ_cont : ContinuousOn (psiTilde virasoroProblem c g) (sphere (0 : ℂ) R) := by
      rw [funext (psiTilde_virasoroProblem hc0.le g)]
      exact (virasoroPsiTilde_analyticOnNhd (by linarith only [hc_10000]) hwf.1).continuousOn.mono
        (fun z hz => virasoro_closedBall_subset_psiDom hc0
          (mem_closedBall_zero_iff.mpr ((mem_sphere_zero_iff_norm.mp hz).le.trans hR_lt_A2.le)))
    have hf_cont : ContinuousOn (lowerF virasoroProblem virasoroPhi c g) (sphere (0 : ℂ) R) :=
      hf_diff.continuousOn.mono fun z hz =>
        mem_ball_zero_iff.mpr ((mem_sphere_zero_iff_norm.mp hz).symm ▸ hRρ')
    exact ctEta_ge_half hR0 hψ_cont hf_cont
  have hdiff_win :
      |∫ u in (-R)..R, (lowerF virasoroProblem virasoroPhi c g (u : ℂ)).re * (K (u : ℂ)).im| ≤
        C_arc * c⁻¹ * lowerEta virasoroProblem virasoroPhi c g R := by
    refine him_bd.trans ?_
    calc 8 * R ^ (-(1 / 2 : ℝ)) * (Cφ * c ^ (-(1 / 3 : ℝ))) ^ 2 *
          ∫ θ in (0 : ℝ)..π, R * ‖lowerF virasoroProblem virasoroPhi c g (circleMap 0 R θ)‖ *
            ‖airyUpE (circleMap 0 R θ)‖
        ≤ (C_arc * c⁻¹) * lowerEta virasoroProblem virasoroPhi c g R :=
          mul_le_mul hcoef_le hη_ge_half
            (intervalIntegral.integral_nonneg Real.pi_pos.le fun _ _ => by positivity)
            (by dsimp [C_arc]; positivity)
  -- Express `∫_{-R}^R Re(f) Im(K)` as `I_win^{(W=1)} + X₀(R)`:
  have hK_im_eq : ∀ u : ℝ, (K (u : ℂ)).im =
      (Complex.exp (lowerEc virasoroPhi c (u : ℂ))).im - (airyUpE (u : ℂ)).im := fun u => rfl
  let F_re : ℝ → ℝ := fun u => (lowerF virasoroProblem virasoroPhi c g (u : ℂ)).re
  have hF_re_cont : ContinuousOn F_re (Icc (-R) R) :=
    Complex.continuous_re.comp_continuousOn (hf_diff.continuousOn.comp Complex.continuous_ofReal.continuousOn
      fun u hu => by rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact (abs_le.mpr hu).trans_lt hRρ')
  have hi_ec : IntervalIntegrable (fun u : ℝ => F_re u * (Complex.exp (lowerEc virasoroPhi c (u : ℂ))).im)
      volume (-R) R := by
    have hcont : ContinuousOn (fun u : ℝ => F_re u * (Complex.exp (lowerEc virasoroPhi c (u : ℂ))).im)
        (Icc (-R) R) := by
      refine hF_re_cont.mul (Complex.continuous_im.comp_continuousOn (hK_cont_ec.cexp.comp
        Complex.continuous_ofReal.continuousOn fun u hu => ?_))
      exact ⟨mem_closedBall_zero_iff.mpr (by rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_le.mpr hu),
        by simp⟩
    exact hcont.intervalIntegrable_of_Icc (by linarith only [hR0])
  have hi_airy : IntervalIntegrable (fun u : ℝ => F_re u * (airyUpE (u : ℂ)).im) volume (-R) R := by
    have hcont : ContinuousOn (fun u : ℝ => F_re u * (airyUpE (u : ℂ)).im) (Icc (-R) R) := by
      refine hF_re_cont.mul (Complex.continuous_im.comp_continuousOn
        ((continuousOn_airyUpE (R := R)).comp Complex.continuous_ofReal.continuousOn fun u hu => ?_))
      exact ⟨mem_closedBall_zero_iff.mpr (by rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_le.mpr hu),
        by simp⟩
    exact hcont.intervalIntegrable_of_Icc (by linarith only [hR0])
  have hK_split :
      ∫ u in (-R)..R, F_re u * (K (u : ℂ)).im =
        (∫ u in (-R)..R, F_re u * (Complex.exp (lowerEc virasoroPhi c (u : ℂ))).im) -
          ∫ u in (-R)..R, F_re u * (airyUpE (u : ℂ)).im := by
    rw [← intervalIntegral.integral_sub hi_ec hi_airy]
    refine intervalIntegral.integral_congr fun u _ => by dsimp [K]; simp [sub_eq_add_neg]; ring
  have hAiry_eq :
      -(∫ u in (-R)..R, F_re u * (airyUpE (u : ℂ)).im) =
        ∫ v in (0 : ℝ)..R, (lowerF virasoroProblem virasoroPhi c g ((-v : ℝ) : ℂ)).re *
          Real.sin (4 / 3 * v ^ (3 / 2 : ℝ)) := by
    have hsplit0 := intervalIntegral.integral_add_adjacent_intervals
      (hi_airy.mono_set (uIcc_subset_uIcc_left ⟨by linarith only [hR0], hR0.le⟩))
      (hi_airy.mono_set (uIcc_subset_uIcc_right ⟨by linarith only [hR0], hR0.le⟩))
    have hi_pos0 : ∫ u in (0 : ℝ)..R, F_re u * (airyUpE (u : ℂ)).im = 0 := by
      refine intervalIntegral.integral_eq_zero_of_forall_eq_zero fun u hu => ?_
      rw [uIoc_of_le hR0.le] at hu
      rw [airyUpE_im_real, if_neg (not_lt.mpr hu.1.le), mul_zero]
    rw [← hsplit0, hi_pos0, add_zero, ← intervalIntegral.integral_comp_neg
      (a := 0) (b := R) (fun v => -(F_re v * (airyUpE (v : ℂ)).im))]
    simp only [neg_zero, neg_neg]
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ u ∂volume, u ≠ 0 := ae_iff.mpr (by simp)
    filter_upwards [hne] with u hu0 hu_mem
    rw [uIoc_of_le hR0.le] at hu_mem
    have hu_lt : -(-u) < 0 := by linarith only [hu_mem.1, hu0]
    rw [airyUpE_im_real, if_pos (by linarith only [hu_mem.1, hu0])]
    dsimp [F_re]; ring
  -- Evaluate `∫_{-R}^R F_re u * (cexp (lowerEc u)).im`:
  let φR : ℝ → ℝ := fun u => (virasoroPhi c (u : ℂ)).re
  let φR' : ℝ → ℝ := fun u => (deriv (virasoroPhi c) (u : ℂ)).re
  have hφ_deriv_im0 : ∀ u ∈ Icc (-R) R, (deriv (virasoroPhi c) (u : ℂ)).im = 0 := fun u hu => by
    have hz_ball : (u : ℂ) ∈ ball (0 : ℂ) ρ_ch :=
      mem_ball_zero_iff.mpr (by rw [Complex.norm_real, Real.norm_eq_abs]; exact (abs_le.mpr hu).trans_lt hR_lt_ρch)
    have h_at := (hφ_diff.differentiableAt (isOpen_ball.mem_nhds hz_ball)).hasDerivAt
    have hd_real : HasDerivWithinAt (fun x : ℝ => (virasoroPhi c (x : ℂ)).im) 0 (Icc (-R) R) u := by
      refine (hasDerivWithinAt_const u (Icc (-R) R) 0).congr ?_ ?_
      · intro x hx; exact (hφ_real_R x (abs_le.mpr hx)).symm
      · exact (hφ_real_R u (abs_le.mpr hu)).symm
    have hd_cplx : HasDerivAt (fun x : ℝ => (virasoroPhi c (x : ℂ)).im)
        (deriv (virasoroPhi c) (u : ℂ)).im u := by
      have h1 := Complex.imCLM.hasDerivAt.comp u (h_at.comp_ofReal)
      simpa only [Complex.imCLM_apply] using h1
    exact ((hd_cplx.hasDerivWithinAt).unique (uniqueDiffOn_Icc (by linarith only [hR0]) u hu)
      hd_real).symm
  have hφR_deriv : ∀ u ∈ Icc (-R) R, HasDerivAt φR (φR' u) u := fun u hu => by
    have hz_ball : (u : ℂ) ∈ ball (0 : ℂ) ρ_ch :=
      mem_ball_zero_iff.mpr (by rw [Complex.norm_real, Real.norm_eq_abs]; exact (abs_le.mpr hu).trans_lt hR_lt_ρch)
    have h_at := (hφ_diff.differentiableAt (isOpen_ball.mem_nhds hz_ball)).hasDerivAt
    have h1 := Complex.reCLM.hasDerivAt.comp u (h_at.comp_ofReal)
    exact h1.congr_deriv (by simp [φR', Complex.reCLM_apply])
  have hφR_deriv_pos : ∀ u ∈ Icc (-R) R, (1 / 2 : ℝ) ≤ φR' u := fun u hu => by
    have hbd := hφ_der_R (u : ℂ) (mem_closedBall_zero_iff.mpr (by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_le.mpr hu))
    have hre : 1 - φR' u ≤ ‖deriv (virasoroPhi c) (u : ℂ) - 1‖ := by
      have h1 : |1 - φR' u| ≤ ‖(1 : ℂ) - deriv (virasoroPhi c) (u : ℂ)‖ := by
        simpa [φR'] using Complex.abs_re_le_norm ((1 : ℂ) - deriv (virasoroPhi c) (u : ℂ))
      rw [norm_sub_rev] at h1
      exact (le_abs_self _).trans h1
    linarith only [hbd, hre]
  have hφR_strictMono : StrictMonoOn φR (Icc (-R) R) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc (-R) R)
    · exact fun u hu => (hφR_deriv u hu).continuousAt.continuousWithinAt
    · intro u hu; exact (hφR_deriv u (interior_subset hu)).hasDerivWithinAt
    · intro u hu; linarith only [hφR_deriv_pos u (interior_subset hu)]
  have hφR_negR : φR (-R) < 0 := by
    have h1 := hφ_close_R (-R : ℂ) (mem_closedBall_zero_iff.mpr (by simp [abs_of_pos hR0]))
    have hre : |φR (-R) - (-R)| ≤ 1 / 4 :=
      ((Complex.abs_re_le_norm _).trans h1).trans hCφ_c13
    linarith only [(abs_le.mp hre).2, hR4]
  have hφR_posR : 0 < φR R := by
    have h1 := hφ_close_R (R : ℂ) (mem_closedBall_zero_iff.mpr (by simp [abs_of_pos hR0]))
    have hre : |φR R - R| ≤ 1 / 4 :=
      ((Complex.abs_re_le_norm _).trans h1).trans hCφ_c13
    linarith only [(abs_le.mp hre).1, hR4]
  obtain ⟨u_star, hu_star_mem, hu_star_eq⟩ := intermediate_value_Icc (by linarith only [hR0] : -R ≤ R)
    (fun u hu => (hφR_deriv u hu).continuousAt.continuousWithinAt) ⟨hφR_negR.le, hφR_posR.le⟩
  have h_band_phiR : ∀ u ∈ Icc (-R) R, -(5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ)) ≤ φR u ∧
      |φR u| ≤ virasoroAC c ^ 2 := fun u hu => by
    have hu_abs : |u| ≤ R := abs_le.mpr hu
    have h1 := hφ_close_R (u : ℂ) (mem_closedBall_zero_iff.mpr (by simpa [Real.norm_eq_abs] using hu_abs))
    have hre : |φR u - u| ≤ 1 / 4 := ((Complex.abs_re_le_norm _).trans h1).trans hCφ_c13
    have hrm : R ≤ 4 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) := hR_hi
    have hc1_pos := virasoroC1_pos
    have h12 : (1 / 2 : ℝ) ≤ virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) := by
      have hp := Real.rpow_le_rpow (by positivity)
        (by linarith only [hc_rmin] : (1 / (2 * virasoroC1 ^ 2)) ^ (3 / 2 : ℝ) ≤ c) (by norm_num : (0 : ℝ) ≤ 2 / 3)
      rw [← Real.rpow_mul (by positivity)] at hp
      norm_num at hp
      rw [div_le_iff₀ (by positivity)] at hp
      linarith only [hp]
    have hphi_abs : |φR u| ≤ 5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) := by
      have := abs_sub_abs_le_abs_sub (φR u) u
      linarith only [this, abs_le.mp hre, hu_abs, hrm, h12]
    have h5bv : 5 * virasoroC1 ^ 2 ≤ 2 * virasoroBV ^ 2 := by
      have hbv := virasoroC1_small.trans virasoroBVChoice_le
      have hsq : (10 * virasoroC1) ^ 2 ≤ virasoroBV ^ 2 := pow_le_pow_left₀ hc1_pos.le hbv 2
      nlinarith only [hsq]
    have hA2_bd : |φR u| ≤ virasoroAC c ^ 2 := by
      rw [virasoroAC_sq c hc0.le]
      nlinarith only [hphi_abs, h5bv, hc23_pos]
    exact ⟨(abs_le.mp hphi_abs).1, hA2_bd⟩
  have hF_re_eq : ∀ u ∈ Icc (-R) R,
      F_re u = (psiTilde virasoroProblem c g (φR u : ℂ)).re * φR' u := fun u hu => by
    have him0 : (virasoroPhi c (u : ℂ)).im = 0 := hφ_real_R u (abs_le.mpr hu)
    have hφ_c : virasoroPhi c (u : ℂ) = (φR u : ℂ) := Complex.ext rfl him0
    have hdφ_c : deriv (virasoroPhi c) (u : ℂ) = (φR' u : ℂ) := Complex.ext rfl (hφ_deriv_im0 u hu)
    dsimp [F_re, lowerF]
    rw [hφ_c, hdφ_c, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.ofReal_re]
  have hi_ec_1 := hi_ec.mono_set (uIcc_subset_uIcc_left hu_star_mem)
  have hi_ec_2 := hi_ec.mono_set (uIcc_subset_uIcc_right hu_star_mem)
  have h_ec_split := intervalIntegral.integral_add_adjacent_intervals hi_ec_1 hi_ec_2
  have h_ec_right :
      ∫ u in u_star..R, F_re u * (Complex.exp (lowerEc virasoroPhi c (u : ℂ))).im = 0 := by
    refine intervalIntegral.integral_eq_zero_of_forall_eq_zero fun u hu => ?_
    rw [uIoc_of_le hu_star_mem.2] at hu
    have hu_in : u ∈ Icc (-R) R := ⟨hu_star_mem.1.trans hu.1.le, hu.2⟩
    have hphi_nn : 0 ≤ φR u := by
      have hm := hφR_strictMono.monotoneOn hu_star_mem hu_in hu.1.le
      rwa [hu_star_eq] at hm
    have him0 : (virasoroPhi c (u : ℂ)).im = 0 := hφ_real_R u (abs_le.mpr hu_in)
    have hφ_c : virasoroPhi c (u : ℂ) = (φR u : ℂ) := Complex.ext rfl him0
    have hsqrt_re : airyUpSqrt (φR u : ℂ) = ((√(φR u) : ℝ) : ℂ) := airyUpSqrt_ofReal_nonneg hphi_nn
    have hec_re : (lowerEc virasoroPhi c (u : ℂ)).im = 0 := by
      unfold lowerEc; rw [hφ_c, hsqrt_re]; push_cast; simp
    have hexp_re : Complex.exp (lowerEc virasoroPhi c (u : ℂ)) =
        ((Real.exp (lowerEc virasoroPhi c (u : ℂ)).re : ℝ) : ℂ) := by
      rw [← Complex.ofReal_exp]; congr 1; exact Complex.ext rfl hec_re
    rw [hexp_re, Complex.ofReal_im, mul_zero]
  let K_ut : ℝ → ℝ := fun ut =>
    (Complex.exp ((4 / 3 : ℂ) * (ut : ℂ) * airyUpSqrt (ut : ℂ) +
      2 * airyUpSqrt (ut : ℂ) * ((virasoroUhat c ut : ℂ) - (ut : ℂ)))).im
  have h_uhat_cont : ContinuousOn (virasoroUhat c)
      (Icc (-(5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ))) 0) := by
    unfold virasoroUhat fjUhat virasoroPsiChart
    have hε0 : 0 ≤ c ^ (-2 : ℝ) := Real.rpow_nonneg hc0.le (-2)
    have hε1 : c ^ (-2 : ℝ) ≤ 1 / 4 := by
      rw [Real.rpow_neg hc0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc (c ^ 2)⁻¹ ≤ (10000 ^ 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by nlinarith only [hc_10000])
        _ ≤ 1 / 4 := by norm_num
    have hψc := (chartParams.hψ_spec (c ^ (-2 : ℝ)) hε0 hε1).1.continuousOn
    have hc1_r0 : 5 * virasoroC1 ^ 2 * betaTip⁻¹ ≤ chartParams.r_ψ := by
      have h1 : virasoroC1 ≤ √(chartParams.r_ψ * betaTip / 16) := (min_le_right _ _).trans (min_le_left _ _)
      have hnn : 0 ≤ chartParams.r_ψ * betaTip / 16 := by
        have := chartParams.hrψ_pos; have := betaTip_pos; positivity
      have hsq : virasoroC1 ^ 2 ≤ chartParams.r_ψ * betaTip / 16 :=
        (pow_le_pow_left₀ virasoroC1_pos.le h1 2).trans_eq (Real.sq_sqrt hnn)
      have hβ := betaTip_pos
      calc 5 * virasoroC1 ^ 2 * betaTip⁻¹ ≤ 5 * (chartParams.r_ψ * betaTip / 16) * betaTip⁻¹ := by gcongr
        _ = 5 / 16 * chartParams.r_ψ := by field_simp [hβ.ne']
        _ ≤ chartParams.r_ψ := by linarith only [chartParams.hrψ_pos]
    have hmaps : MapsTo (fun w : ℝ => ((virasoroMu c * w : ℝ) : ℂ))
        (Icc (-(5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ))) 0) (ball 0 chartParams.ρ_ψ) := by
      intro w hw
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos (by unfold virasoroMu; have := betaTip_pos; positivity)]
      have hmu_le : virasoroMu c * |w| ≤ 5 * virasoroC1 ^ 2 * betaTip⁻¹ := by
        unfold virasoroMu
        have hβ := betaTip_pos
        have hwabs : |w| ≤ 5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) := by
          rw [abs_of_nonpos hw.2]; linarith only [hw.1]
        calc betaTip⁻¹ * c ^ (-(2 / 3 : ℝ)) * |w|
            ≤ betaTip⁻¹ * c ^ (-(2 / 3 : ℝ)) * (5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ)) := by gcongr
          _ = 5 * virasoroC1 ^ 2 * betaTip⁻¹ * (c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) := by ring
          _ = 5 * virasoroC1 ^ 2 * betaTip⁻¹ := by rw [← Real.rpow_add hc0]; norm_num
      exact hmu_le.trans_lt (lt_of_le_of_lt hc1_r0 chartParams.hrψ_lt)
    refine continuousOn_id.add (continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      (hψc.comp (Complex.continuous_ofReal.continuousOn.comp
        (continuous_const.mul continuous_id).continuousOn (mapsTo_univ _ _)) hmaps)))
  have hK_ut_cont : ContinuousOn K_ut (Icc (φR (-R)) 0) := by
    have hband_sub : Icc (φR (-R)) 0 ⊆ Icc (-(5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ))) 0 :=
      Icc_subset_Icc_left (h_band_phiR (-R) ⟨le_rfl, by linarith only [hR0]⟩).1
    have huc := h_uhat_cont.mono hband_sub
    have hsqrt_c : ContinuousOn (fun ut : ℝ => airyUpSqrt (ut : ℂ)) (Icc (φR (-R)) 0) :=
      continuousOn_airyUpSqrt_half.comp Complex.continuous_ofReal.continuousOn fun _ _ => by simp
    dsimp [K_ut]
    exact Complex.continuous_im.comp_continuousOn
      ((((continuousOn_const.mul Complex.continuous_ofReal.continuousOn).mul hsqrt_c).add
        ((continuousOn_const.mul hsqrt_c).mul
          ((Complex.continuous_ofReal.comp_continuousOn huc).sub
            Complex.continuous_ofReal.continuousOn))).cexp)
  have hψ_re_cont_A2 : ContinuousOn (fun ut : ℝ => (psiTilde virasoroProblem c g (ut : ℂ)).re)
      (Icc (-(virasoroAC c ^ 2)) (virasoroAC c ^ 2)) := by
    rw [funext (psiTilde_virasoroProblem hc0.le g)]
    exact Complex.continuous_re.comp_continuousOn
      (((virasoroPsiTilde_analyticOnNhd (by linarith only [hc_10000]) hwf.1).continuousOn.mono
        (virasoro_closedBall_subset_psiDom hc0)).comp Complex.continuous_ofReal.continuousOn
        fun ut hut => mem_closedBall_zero_iff.mpr (by simpa [Real.norm_eq_abs] using abs_le.mpr hut))
  have hφR_deriv_cont : ContinuousOn φR' (Icc (-R) R) := by
    have hd_an : AnalyticOnNhd ℂ (deriv (virasoroPhi c)) (ball 0 ρ_ch) :=
      (hφ_diff.analyticOnNhd isOpen_ball).deriv
    exact Complex.continuous_re.comp_continuousOn (hd_an.continuousOn.comp
      Complex.continuous_ofReal.continuousOn fun u hu => by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        exact (abs_le.mpr hu).trans_lt hR_lt_ρch)
  have h_ec_eq_ut :
      ∫ u in (-R)..u_star, F_re u * (Complex.exp (lowerEc virasoroPhi c (u : ℂ))).im =
        ∫ ut in (φR (-R))..0, (psiTilde virasoroProblem c g (ut : ℂ)).re * K_ut ut := by
    have hfn : EqOn (fun u => F_re u * (Complex.exp (lowerEc virasoroPhi c (u : ℂ))).im)
        (fun u => ((psiTilde virasoroProblem c g (φR u : ℂ)).re * K_ut (φR u)) * φR' u)
        (uIcc (-R) u_star) := fun u hu => by
      rw [uIcc_of_le hu_star_mem.1] at hu
      have hu_in : u ∈ Icc (-R) R := ⟨hu.1, hu.2.trans hu_star_mem.2⟩
      have hu_rm : |u| ≤ lowerRmax virasoroC1 c := (abs_le.mpr hu_in).trans hR_hi
      have him0 : (virasoroPhi c (u : ℂ)).im = 0 := hφ_real_R u (abs_le.mpr hu_in)
      have hφ_c : virasoroPhi c (u : ℂ) = (φR u : ℂ) := Complex.ext rfl him0
      have hu_eq : virasoroUhat c (φR u) = u := hφ_uhat_ch u hu_rm
      have hK_eq : (Complex.exp (lowerEc virasoroPhi c (u : ℂ))).im = K_ut (φR u) := by
        unfold lowerEc K_ut
        rw [hφ_c, hu_eq]
      rw [hK_eq, hF_re_eq u hu_in]; ring
    rw [intervalIntegral.integral_congr hfn]
    have himg : φR '' uIcc (-R) u_star ⊆ Icc (φR (-R)) 0 := by
      rintro ut ⟨u, hu, rfl⟩
      rw [uIcc_of_le hu_star_mem.1] at hu
      have hu_in : u ∈ Icc (-R) R := ⟨hu.1, hu.2.trans hu_star_mem.2⟩
      exact ⟨hφR_strictMono.monotoneOn ⟨le_rfl, by linarith only [hR0]⟩ hu_in hu.1,
        (hφR_strictMono.monotoneOn hu_in hu_star_mem hu.2).trans_eq hu_star_eq⟩
    have hcont_ut : ContinuousOn (fun ut => (psiTilde virasoroProblem c g (ut : ℂ)).re * K_ut ut)
        (φR '' uIcc (-R) u_star) := by
      refine (hψ_re_cont_A2.mono ?_).mul (hK_ut_cont.mono himg)
      intro ut hut
      have hle := himg hut
      have hA2 := (h_band_phiR (-R) ⟨le_rfl, by linarith only [hR0]⟩).2
      exact ⟨(abs_le.mp hA2).1.trans hle.1, hle.2.trans (sq_nonneg _)⟩
    have hcov := intervalIntegral.integral_comp_mul_deriv'
      (fun u hu => hφR_deriv u (by rw [uIcc_of_le hu_star_mem.1] at hu; exact ⟨hu.1, hu.2.trans hu_star_mem.2⟩))
      (hφR_deriv_cont.mono (by rw [uIcc_of_le hu_star_mem.1]; exact Icc_subset_Icc_right hu_star_mem.2))
      hcont_ut
    simpa only [hu_star_eq] using hcov
  -- Now substitute `t = virasoroDeltaChart c ut` on `[φR (-R), 0]`:
  have ha_shift : virasoroProblem.totalShift ≤ c / 12 := by
    rw [virasoroProblem_totalShift]; linarith only [hc_10000]
  have hΔ0_pos : 0 < virasoroDeltaChart c 0 :=
    virasoroDeltaChart_pos hc0 (by rw [abs_zero]; positivity)
  have hΔ_le : virasoroDeltaChart c 0 ≤ virasoroDeltaChart c (φR (-R)) := by
    have h1 := (h_band_phiR (-R) ⟨le_rfl, by linarith only [hR0]⟩).2
    exact (virasoroDeltaChart_strictAnti hc0).antitoneOn
      ⟨(abs_le.mp h1).1, hφR_negR.le.trans (sq_nonneg _)⟩
      ⟨neg_nonpos.mpr (sq_nonneg _), sq_nonneg _⟩ hφR_negR.le
  have hut_A2 : ∀ ut ∈ Icc (φR (-R)) 0, |ut| ≤ virasoroAC c ^ 2 := fun ut hut =>
    abs_le.mpr ⟨(abs_le.mp (h_band_phiR (-R) ⟨le_rfl, by linarith only [hR0]⟩).2).1.trans hut.1,
      hut.2.trans (sq_nonneg _)⟩
  have h_ut_to_t :
      ∫ ut in (φR (-R))..0, (psiTilde virasoroProblem c g (ut : ℂ)).re * K_ut ut =
        (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
          ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c (φR (-R))),
            (g t * virasoroProblem.cardyV (c / 12) t) * K_ut (virasoroUChart c (t / c)) := by
    have hd_all : ∀ ut ∈ uIcc (φR (-R)) 0,
        HasDerivAt (virasoroDeltaChart c) (deriv (virasoroDeltaChart c) ut) ut := fun ut hut => by
      rw [uIcc_of_le hφR_negR.le] at hut
      exact virasoroDeltaChart_hasDerivAt hc0 (hut_A2 ut hut)
    have hcont_der : ContinuousOn (deriv (virasoroDeltaChart c)) (uIcc (φR (-R)) 0) := by
      rw [uIcc_of_le hφR_negR.le]
      let G : ℝ → ℝ := fun ut => c ^ (1 / 3 : ℝ) * (deriv virasoroXiInf ((ut * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re
      have hG : ContinuousOn G (Icc (φR (-R)) 0) := fun ut hut => by
        have hw : ((ut * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) ∈ ball (0 : ℂ) virasoroRUInf := by
          have h1 := virasoro_u_mem_open_ball hc0 (u := (ut : ℂ))
            (mem_closedBall_zero_iff.mpr (by simpa [Real.norm_eq_abs] using hut_A2 ut hut))
          rwa [← Complex.ofReal_mul] at h1
        have hd_at := (virasoroXiInf_analyticOnNhd.deriv ((ut * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) hw).continuousAt
        exact (continuousAt_const.mul (Complex.continuous_re.continuousAt.comp
          (hd_at.comp (Complex.continuous_ofReal.continuousAt.comp (continuousAt_id.mul continuousAt_const))))).continuousWithinAt
      exact hG.congr fun ut hut => (virasoroDeltaChart_hasDerivAt hc0 (hut_A2 ut hut)).deriv
    have h_uChart_cont : ContinuousOn (fun t : ℝ => virasoroUChart c (t / c))
        (virasoroDeltaChart c '' uIcc (φR (-R)) 0) := by
      rintro t ⟨ut, hut, rfl⟩
      rw [uIcc_of_le hφR_negR.le] at hut
      have hdiv := virasoroDeltaChart_div_mem hc0 (hut_A2 ut hut)
      have hξ_open : ((virasoroDeltaChart c ut / c : ℝ) : ℂ) ∈ ball (xiBar : ℂ) virasoroRXiInf := by
        rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact abs_sub_lt_iff.mpr ⟨by linarith only [hdiv.2, virasoroChartR0_lt_RXiInf],
          by linarith only [hdiv.1, virasoroChartR0_lt_RXiInf]⟩
      unfold virasoroUChart
      exact (continuousAt_const.mul (Complex.continuous_re.continuousAt.comp
        ((virasoroUInf_analyticOnNhd _ hξ_open).continuousAt.comp
          (Complex.continuous_ofReal.continuousAt.comp
            (continuousAt_id.div_const c))))).continuousWithinAt
    have h_t_cont : ContinuousOn
        (fun t : ℝ => (g t * virasoroProblem.cardyV (c / 12) t) * K_ut (virasoroUChart c (t / c)))
        (virasoroDeltaChart c '' uIcc (φR (-R)) 0) := by
      refine ((hwf.1.cont.mul ?_).mono ?_).mul (hK_ut_cont.comp h_uChart_cont ?_)
      · exact (continuous_cardyV virasoroProblem (c / 12)).continuousOn
      · rintro t ⟨ut, hut, rfl⟩
        rw [uIcc_of_le hφR_negR.le] at hut
        exact (virasoroDeltaChart_pos hc0 (hut_A2 ut hut)).le
      · rintro t ⟨ut, hut, rfl⟩
        rw [uIcc_of_le hφR_negR.le] at hut
        rw [virasoroUChart_deltaChart hc0 (hut_A2 ut hut)]
        exact hut
    have hfn_sub : EqOn
        (fun ut : ℝ => (psiTilde virasoroProblem c g (ut : ℂ)).re * K_ut ut)
        (fun ut : ℝ => -((virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
          ((g (virasoroDeltaChart c ut) * virasoroProblem.cardyV (c / 12) (virasoroDeltaChart c ut)) *
            K_ut (virasoroUChart c (virasoroDeltaChart c ut / c))) *
          deriv (virasoroDeltaChart c) ut))
        (uIcc (φR (-R)) 0) := fun ut hut => by
      rw [uIcc_of_le hφR_negR.le] at hut
      rw [psiTilde_re_ofReal virasoroProblem hc0 hwf.1 (hut_A2 ut hut),
        virasoroUChart_deltaChart hc0 (hut_A2 ut hut)]
      ring
    rw [intervalIntegral.integral_congr hfn_sub, intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul, ← intervalIntegral.integral_symm]
    congr 1
    exact intervalIntegral.integral_comp_mul_deriv' hd_all hcont_der (h_t_cont.const_mul _)
  -- Rewrite `K_ut (virasoroUChart c (t / c))` as `sin(...)` a.e. and split off `1 - lowerWeps`:
  have hM_pos : 0 < virasoroProblem.cardyNorm (c / 12) g :=
    cardyNorm_pos_of_nonzero ha_shift hwf.1 hwf.2.1
  -- Relate `t ∈ (Δ 0, Δ (φR(-R)))` to `ut = virasoroUChart c (t / c) < 0`, replace `K_ut` by `sin(...)`,
  -- and bound the `(1 - lowerWeps)` difference by `C_w c⁻² ≤ C_w c^{-4/3}`:
  have himg_eq : virasoroDeltaChart c '' uIcc (φR (-R)) 0 =
      Icc (virasoroDeltaChart c 0) (virasoroDeltaChart c (φR (-R))) := by
    refine Subset.antisymm ?_ ?_
    · rintro t ⟨ut, hut, rfl⟩
      rw [uIcc_of_le hφR_negR.le] at hut
      exact ⟨(virasoroDeltaChart_strictAnti hc0).antitoneOn (hut_A2 ut hut)
          ⟨neg_nonpos.mpr (sq_nonneg _), sq_nonneg _⟩ hut.2,
        (virasoroDeltaChart_strictAnti hc0).antitoneOn
          (hut_A2 (φR (-R)) ⟨le_rfl, hφR_negR.le⟩) (hut_A2 ut hut) hut.1⟩
    · intro t ht
      have hcont_Δ : ContinuousOn (virasoroDeltaChart c) (Icc (φR (-R)) 0) := fun ut hut =>
        (virasoroDeltaChart_hasDerivAt hc0 (hut_A2 ut hut)).continuousAt.continuousWithinAt
      obtain ⟨ut, hut, hut_eq⟩ := intermediate_value_Icc' hφR_negR.le hcont_Δ ht
      exact ⟨ut, by rwa [uIcc_of_le hφR_negR.le], hut_eq⟩
  have h_ut_props : ∀ t ∈ Ioo (virasoroDeltaChart c 0) (virasoroDeltaChart c (φR (-R))),
      let ut := virasoroUChart c (t / c)
      let x := √(3 * t / c)
      ut ∈ Ico (φR (-R)) 0 ∧ -(5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ)) ≤ ut ∧
        xiStar < x ∧ x ≤ X_hi ∧
        K_ut ut = Real.sin (lowerThetaEps Gout (c ^ (-2 : ℝ)) (lowerY x) - 2 * π * c * cumulN x) := by
    intro t ht
    obtain ⟨ut, hut, hut_eq⟩ : ∃ ut ∈ Icc (φR (-R)) 0, virasoroDeltaChart c ut = t := by
      have hsub : t ∈ Icc (virasoroDeltaChart c 0) (virasoroDeltaChart c (φR (-R))) :=
        ⟨ht.1.le, ht.2.le⟩
      rw [← himg_eq] at hsub
      rcases hsub with ⟨ut, hut, rfl⟩
      rw [uIcc_of_le hφR_negR.le] at hut
      exact ⟨ut, hut, rfl⟩
    have hut_A2_pt := hut_A2 ut hut
    have hut_uc : virasoroUChart c (t / c) = ut := by rw [← hut_eq]; exact virasoroUChart_deltaChart hc0 hut_A2_pt
    have hut_neg : ut < 0 := by
      by_contra hge
      have hut0 : ut = 0 := le_antisymm hut.2 (not_lt.mp hge)
      rw [hut0] at hut_eq
      linarith only [ht.1, hut_eq]
    have hut_lo : -(5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ)) ≤ ut :=
      (h_band_phiR (-R) ⟨le_rfl, by linarith only [hR0]⟩).1.trans hut.1
    have hlb := lowerLangerPhase_band hc0 hut_lo hut_neg
    have hx_lt_X : √(3 * virasoroDeltaChart c ut / c) < X_hi :=
      (chartParams.hψ_phase _ hlb.2.2 hlb.2.1).1
    have hsin_eq := lowerEc_ofReal_neg_sin hc2 hut_lo hut_neg (rfl : virasoroUhat c ut = virasoroUhat c ut)
    rw [hut_eq] at hlb hx_lt_X hsin_eq
    refine ⟨⟨hut.1, hut_neg⟩, hut_lo, hlb.2.2, hx_lt_X.le, ?_⟩
    rw [hut_uc, ← hsin_eq]
    dsimp [K_ut]
    congr 1; congr 1; congr 1
    rw [Complex.ofReal_eq_coe]
    rfl
  let gV : ℝ → ℝ := fun t => g t * virasoroProblem.cardyV (c / 12) t
  let sinF : ℝ → ℝ := fun t =>
    Real.sin (lowerThetaEps Gout (c ^ (-2 : ℝ)) (lowerY (√(3 * t / c))) -
      2 * π * c * cumulN (√(3 * t / c)))
  let Wf : ℝ → ℝ := fun t => lowerWeps (c ^ (-2 : ℝ)) (lowerY (√(3 * t / c)))
  have hcont_t_K : ContinuousOn (fun t => gV t * K_ut (virasoroUChart c (t / c)))
      (Icc (virasoroDeltaChart c 0) (virasoroDeltaChart c (φR (-R)))) := by
    have hcont_im := (hwf.1.cont.mul (continuous_cardyV virasoroProblem (c / 12)).continuousOn).mono
      (fun t ht => hΔ0_pos.le.trans ht.1)
    have h_uChart_c2 : ContinuousOn (fun t : ℝ => virasoroUChart c (t / c))
        (Icc (virasoroDeltaChart c 0) (virasoroDeltaChart c (φR (-R)))) := by
      rw [← himg_eq]
      rintro t ⟨ut, hut, rfl⟩
      rw [uIcc_of_le hφR_negR.le] at hut
      have hdiv := virasoroDeltaChart_div_mem hc0 (hut_A2 ut hut)
      have hξ_open : ((virasoroDeltaChart c ut / c : ℝ) : ℂ) ∈ ball (xiBar : ℂ) virasoroRXiInf := by
        rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact abs_sub_lt_iff.mpr ⟨by linarith only [hdiv.2, virasoroChartR0_lt_RXiInf],
          by linarith only [hdiv.1, virasoroChartR0_lt_RXiInf]⟩
      unfold virasoroUChart
      exact (continuousAt_const.mul (Complex.continuous_re.continuousAt.comp
        ((virasoroUInf_analyticOnNhd _ hξ_open).continuousAt.comp
          (Complex.continuous_ofReal.continuousAt.comp
            (continuousAt_id.div_const c))))).continuousWithinAt
    refine hcont_im.mul (hK_ut_cont.comp h_uChart_c2 ?_)
    intro t ht
    rw [← himg_eq] at ht
    rcases ht with ⟨ut, hut, rfl⟩
    rw [uIcc_of_le hφR_negR.le] at hut
    rwa [virasoroUChart_deltaChart hc0 (hut_A2 ut hut)]
  have hi_t_K : IntervalIntegrable (fun t => gV t * K_ut (virasoroUChart c (t / c)))
      volume (virasoroDeltaChart c 0) (virasoroDeltaChart c (φR (-R))) :=
    hcont_t_K.intervalIntegrable_of_Icc hΔ_le
  have hi_t_sin : IntervalIntegrable (fun t => gV t * sinF t)
      volume (virasoroDeltaChart c 0) (virasoroDeltaChart c (φR (-R))) := by
    refine hi_t_K.congr_ae ?_
    have hne0 : ∀ᵐ t ∂volume, t ≠ virasoroDeltaChart c 0 := ae_iff.mpr (by simp)
    have hne1 : ∀ᵐ t ∂volume, t ≠ virasoroDeltaChart c (φR (-R)) := ae_iff.mpr (by simp)
    filter_upwards [hne0, hne1] with t ht0 ht1 ht_mem
    rw [uIoc_of_le hΔ_le] at ht_mem
    have ht_oo : t ∈ Ioo (virasoroDeltaChart c 0) (virasoroDeltaChart c (φR (-R))) :=
      ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 ht1⟩
    rw [(h_ut_props t ht_oo).2.2.2.2]
  have h_ec_eq_sin :
      ∫ u in (-R)..u_star, F_re u * (Complex.exp (lowerEc virasoroPhi c (u : ℂ))).im =
        (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
          ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c (φR (-R))), gV t * sinF t := by
    rw [h_ec_eq_ut, h_ut_to_t]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    have hne1 : ∀ᵐ t ∂volume, t ≠ virasoroDeltaChart c (φR (-R)) := ae_iff.mpr (by simp)
    filter_upwards [hne1] with t ht1 ht_mem
    rw [uIoc_of_le hΔ_le] at ht_mem
    have ht_oo : t ∈ Ioo (virasoroDeltaChart c 0) (virasoroDeltaChart c (φR (-R))) :=
      ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 ht1⟩
    rw [(h_ut_props t ht_oo).2.2.2.2]
  have hWf_cont : ContinuousOn Wf (Icc (virasoroDeltaChart c 0) (virasoroDeltaChart c (φR (-R)))) := by
    let ε := c ^ (-2 : ℝ)
    have hε0 : 0 ≤ ε := Real.rpow_nonneg hc0.le _
    let Wf_rat : ℝ → ℝ := fun t =>
      (1 + ε) ^ 2 * slitA (√(3 * t / c)) ^ 2 / mtDen ε (slitA (√(3 * t / c)))
    have h_eq : EqOn Wf Wf_rat (Icc (virasoroDeltaChart c 0) (virasoroDeltaChart c (φR (-R)))) := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with rfl | ht_gt
      · have h0 : virasoroDeltaChart c 0 = c * xiStar ^ 2 / 3 := by
          unfold virasoroDeltaChart
          rw [zero_mul, virasoroXiInf_zero, Complex.ofReal_re]
          have := xiStar_pos.le; field_simp
        have hx0 : √(3 * virasoroDeltaChart c 0 / c) = xiStar := by
          rw [h0, show 3 * (c * xiStar ^ 2 / 3) / c = xiStar ^ 2 by field_simp [hc0.ne'],
            Real.sqrt_sq xiStar_pos.le]
        have hy0 : lowerY xiStar = 0 := by unfold lowerY; rw [cosh_pi_mul_xiStar]; simp
        have ha0 : slitA xiStar = 1 := by
          unfold slitA; rw [cosh_pi_mul_xiStar]; have : (0 : ℝ) < √2 := by positivity; field_simp [this.ne']
        dsimp [Wf, Wf_rat]; rw [hx0, hy0, ha0]
        unfold lowerWeps lowerMt mtDen
        have h1ε : (1 + ε : ℝ) ≠ 0 := by positivity
        have h1εC : (1 + (ε : ℂ)) ≠ 0 := by exact_mod_cast h1ε
        simp [h1εC, norm_pow]; field_simp [h1ε]; ring
      · have hx_gt : xiStar < √(3 * t / c) := by
          rcases eq_or_lt_of_le ht.2 with rfl | ht_lt
          · have hut_lo := (h_band_phiR (-R) ⟨le_rfl, by linarith only [hR0]⟩).1
            exact (lowerLangerPhase_band hc0 hut_lo hφR_negR).2.2
          · exact (h_ut_props t ⟨ht_gt, ht_lt⟩).2.2.1
        exact lowerWeps_eq hε0 hx_gt
    refine ContinuousOn.congr ?_ h_eq
    have hx_c : ContinuousOn (fun t : ℝ => √(3 * t / c))
        (Icc (virasoroDeltaChart c 0) (virasoroDeltaChart c (φR (-R)))) :=
      ((continuousOn_const.mul continuousOn_id).div_const c).sqrt
    have ha_c : ContinuousOn (fun t : ℝ => slitA (√(3 * t / c)))
        (Icc (virasoroDeltaChart c 0) (virasoroDeltaChart c (φR (-R)))) := by
      unfold slitA
      exact continuousOn_const.div
        ((Real.continuous_cosh.comp_continuousOn (continuousOn_const.mul hx_c)).add continuousOn_const)
        fun t _ => by have := Real.cosh_pos (π * √(3 * t / c)); positivity
    dsimp [Wf_rat]
    refine ((continuousOn_const.mul (ha_c.pow 2)).div ?_ ?_)
    · unfold mtDen
      exact ((ha_c.add continuousOn_const).pow 2).add
        (continuousOn_const.mul (continuousOn_const.sub ha_c))
    · intro t ht
      have hx_nn : xiStar ≤ √(3 * t / c) := by
        have hx0 : virasoroDeltaChart c 0 = c * xiStar ^ 2 / 3 := by
          unfold virasoroDeltaChart
          rw [zero_mul, virasoroXiInf_zero, Complex.ofReal_re]
          have := xiStar_pos.le; field_simp
        rw [← Real.sqrt_sq xiStar_pos.le]
        apply Real.sqrt_le_sqrt
        rw [← hx0]
        exact (le_div_iff₀ hc0).mpr (by linarith only [ht.1] : _ ) |> fun _ => by
          have : 3 * virasoroDeltaChart c 0 / c = xiStar ^ 2 := by
            rw [hx0]; field_simp [hc0.ne']
          rw [← this]; gcongr; exact ht.1
      have ha_pos : 0 < slitA (√(3 * t / c)) := slitA_pos _
      have ha_lt1 : slitA (√(3 * t / c)) ≤ 1 := by
        rcases eq_or_lt_of_le hx_nn with heq | hgt
        · rw [← heq]; unfold slitA; rw [cosh_pi_mul_xiStar]
          have : (0 : ℝ) < √2 := by positivity; field_simp [this.ne']; rfl
        · exact (slitA_lt_one hgt).le
      unfold mtDen; nlinarith only [ha_pos, ha_lt1, hε0]
  have hi_t_wsin : IntervalIntegrable (fun t => gV t * Wf t * sinF t)
      volume (virasoroDeltaChart c 0) (virasoroDeltaChart c (φR (-R))) := by
    have h1 := hi_t_sin.mul_continuousOn hWf_cont
    refine h1.congr_fun (fun t _ => by ring) measurableSet_uIoc
  -- Bound the `(Wf t - 1)` residual by `C_w * c⁻² ≤ C_w * c^{-4/3}`:
  have hw_res :
      |(virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
          ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c (φR (-R))), gV t * Wf t * sinF t -
        (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
          ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c (φR (-R))), gV t * sinF t| ≤
        C_w * c ^ (-(4 / 3 : ℝ)) := by
    rw [← mul_sub, ← intervalIntegral.integral_sub hi_t_wsin hi_t_sin, abs_mul,
      abs_of_pos (inv_pos.mpr hM_pos)]
    have hint_diff :
        |∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c (φR (-R))),
            (gV t * Wf t * sinF t - gV t * sinF t)| ≤
          ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c (φR (-R))),
            (C_w * c ^ (-2 : ℝ)) * (|g t| * virasoroProblem.cardyV (c / 12) t) := by
      have hV_nn : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ virasoroProblem.cardyV (c / 12) t := fun {t} ht =>
        virasoroProblem.cardyV_nonneg ha_shift ht
      have h_norm_int : IntervalIntegrable
          (fun t => (C_w * c ^ (-2 : ℝ)) * (|g t| * virasoroProblem.cardyV (c / 12) t))
          volume (virasoroDeltaChart c 0) (virasoroDeltaChart c (φR (-R))) :=
        (((hwf.1.cont.abs.mul (continuous_cardyV virasoroProblem (c / 12)).continuousOn).mono
          fun t ht => hΔ0_pos.le.trans ht.1).const_mul _).intervalIntegrable_of_Icc hΔ_le
      have h_le_norm := intervalIntegral.norm_integral_le_integral_norm
        (a := virasoroDeltaChart c 0) (b := virasoroDeltaChart c (φR (-R)))
        (f := fun t => gV t * Wf t * sinF t - gV t * sinF t)
      rw [Real.norm_eq_abs] at h_le_norm
      refine h_le_norm.trans ?_
      refine intervalIntegral.integral_mono_ae_restrict hΔ_le (hi_t_wsin.sub hi_t_sin).norm h_norm_int ?_
      have hne1 : ∀ᵐ t ∂volume, t ≠ virasoroDeltaChart c (φR (-R)) := ae_iff.mpr (by simp)
      refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
      filter_upwards [hne1] with t ht1 ht_mem
      have ht_oo : t ∈ Ioo (virasoroDeltaChart c 0) (virasoroDeltaChart c (φR (-R))) :=
        ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 ht1⟩
      have hp := h_ut_props t ht_oo
      have hw1 := one_sub_lowerWeps_le_on_window hc2 hp.2.2.1 hp.2.2.2.1
      have hV_pt : 0 ≤ virasoroProblem.cardyV (c / 12) t := hV_nn (hΔ0_pos.le.trans ht_mem.1.le)
      have hsin_le : |sinF t| ≤ 1 := Real.abs_sin_le_one _
      calc ‖gV t * Wf t * sinF t - gV t * sinF t‖
          = |g t| * virasoroProblem.cardyV (c / 12) t * |Wf t - 1| * |sinF t| := by
            dsimp [gV]; rw [Real.norm_eq_abs, show g t * virasoroProblem.cardyV (c / 12) t * Wf t * sinF t -
              g t * virasoroProblem.cardyV (c / 12) t * sinF t =
              g t * virasoroProblem.cardyV (c / 12) t * (Wf t - 1) * sinF t by ring,
              abs_mul, abs_mul, abs_mul, abs_of_nonneg hV_pt]
        _ ≤ |g t| * virasoroProblem.cardyV (c / 12) t * (C_w * c ^ (-2 : ℝ)) * 1 := by
            gcongr; rw [abs_sub_comm]; exact hw1
        _ = (C_w * c ^ (-2 : ℝ)) * (|g t| * virasoroProblem.cardyV (c / 12) t) := by ring
    have hM_le : ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c (φR (-R))),
          |g t| * virasoroProblem.cardyV (c / 12) t ≤ virasoroProblem.cardyNorm (c / 12) g := by
      rw [intervalIntegral.integral_of_le hΔ_le]
      change ∫ t in Ioc (virasoroDeltaChart c 0) (virasoroDeltaChart c (φR (-R))),
          |g t| * virasoroProblem.cardyV (c / 12) t ≤
        ∫ t in Ioi (0 : ℝ), |g t| * virasoroProblem.cardyV (c / 12) t
      refine setIntegral_mono_set hwf.1.int_cardy ?_
        ((Ioc_subset_Ioc_left hΔ0_pos.le).trans Ioc_subset_Ioi_self).eventuallySubset
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
        mul_nonneg (abs_nonneg _) (virasoroProblem.cardyV_nonneg ha_shift ht.le)
    rw [intervalIntegral.integral_const_mul] at hint_diff
    have hC_w_nn : 0 ≤ C_w := by dsimp [C_w]; positivity
    have hcw_le : C_w * c ^ (-2 : ℝ) ≤ C_w * c ^ (-(4 / 3 : ℝ)) := by
      have hc_1 : 1 ≤ c := by linarith only [hc_10000]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hc_1 (by norm_num)) hC_w_nn
    calc (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
          |∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c (φR (-R))),
              (gV t * Wf t * sinF t - gV t * sinF t)|
        ≤ (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
            ((C_w * c ^ (-2 : ℝ)) * virasoroProblem.cardyNorm (c / 12) g) := by
          gcongr
          exact hint_diff.trans (mul_le_mul_of_nonneg_left hM_le (by positivity))
      _ = C_w * c ^ (-2 : ℝ) := by field_simp [hM_pos.ne']
      _ ≤ C_w * c ^ (-(4 / 3 : ℝ)) := hcw_le
  -- Combine `hdiff_win` and `hw_res`:
  have h_all_eq :
      (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
          ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c (φR (-R))), gV t * sinF t +
        ∫ v in (0 : ℝ)..R, (lowerF virasoroProblem virasoroPhi c g ((-v : ℝ) : ℂ)).re *
          Real.sin (4 / 3 * v ^ (3 / 2 : ℝ)) =
      ∫ u in (-R)..R, (lowerF virasoroProblem virasoroPhi c g (u : ℂ)).re * (K (u : ℂ)).im := by
    rw [hK_split, hAiry_eq, ← h_ec_eq_sin, ← h_ec_split, h_ec_right, add_zero]
  have hC_eta_nn : 0 ≤ lowerEta virasoroProblem virasoroPhi c g R := by
    unfold lowerEta
    refine intervalIntegral.integral_nonneg (by positivity) fun θ _ =>
      div_nonneg (mul_nonneg hR0.le (add_nonneg (norm_nonneg _) (norm_nonneg _))) (airyEnv_pos _).le
  have h1 :
      |(virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
          ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c (φR (-R))), gV t * Wf t * sinF t +
        ∫ v in (0 : ℝ)..R, (lowerF virasoroProblem virasoroPhi c g ((-v : ℝ) : ℂ)).re *
          Real.sin (4 / 3 * v ^ (3 / 2 : ℝ))| ≤
      C_w * c ^ (-(4 / 3 : ℝ)) + C_arc * c⁻¹ * lowerEta virasoroProblem virasoroPhi c g R := by
    have htri := abs_add_le
      ((virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
          ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c (φR (-R))), gV t * Wf t * sinF t -
        (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
          ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c (φR (-R))), gV t * sinF t)
      ((virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
          ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c (φR (-R))), gV t * sinF t +
        ∫ v in (0 : ℝ)..R, (lowerF virasoroProblem virasoroPhi c g ((-v : ℝ) : ℂ)).re *
          Real.sin (4 / 3 * v ^ (3 / 2 : ℝ)))
    have hsum :
        ((virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
            ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c (φR (-R))), gV t * Wf t * sinF t -
          (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
            ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c (φR (-R))), gV t * sinF t) +
        ((virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
            ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c (φR (-R))), gV t * sinF t +
          ∫ v in (0 : ℝ)..R, (lowerF virasoroProblem virasoroPhi c g ((-v : ℝ) : ℂ)).re *
            Real.sin (4 / 3 * v ^ (3 / 2 : ℝ))) =
        (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
            ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c (φR (-R))), gV t * Wf t * sinF t +
          ∫ v in (0 : ℝ)..R, (lowerF virasoroProblem virasoroPhi c g ((-v : ℝ) : ℂ)).re *
            Real.sin (4 / 3 * v ^ (3 / 2 : ℝ)) := by ring
    rw [← hsum]
    refine htri.trans (add_le_add hw_res ?_)
    rw [h_all_eq]
    exact hdiff_win
  calc _ ≤ C_w * c ^ (-(4 / 3 : ℝ)) + C_arc * c⁻¹ * lowerEta virasoroProblem virasoroPhi c g R := h1
    _ ≤ max C_arc C_w * c ^ (-(4 / 3 : ℝ)) +
          max C_arc C_w * c⁻¹ * lowerEta virasoroProblem virasoroPhi c g R := by
        gcongr
        · exact le_max_right _ _
        · exact le_max_left _ _
    _ = max C_arc C_w * (c⁻¹ * lowerEta virasoroProblem virasoroPhi c g R + c ^ (-(4 / 3 : ℝ))) := by ring

#print axioms virasoro_D_orth_of_holo
#print axioms virasoro_slit_phase_window_bound

end

end FormalResearch.ModularBootstrap.FiveTerm
