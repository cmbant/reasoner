module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerKedgeGepsDeriv
public import FormalResearch.SignUncertainty.CtOscStat

/-!
# Global `D2` Phase and Smooth Amplitude Pieces (`LowerKedgeOuterBase`)

Base `D2` helpers and global smooth `C²` bounds for `LowerKedgeOuterAmp`:

* `D2_mulC`, `D2_re`: complex product and real-part combinators for `CtOsc.D2`.
* `edgeF_deriv_bounds_of_ge`: `edgeF'` increasing on `[0, ∞)` with `edgeF' ≤ 1`,
  `0 < edgeF'' ≤ 8 π`, `|edgeF'''| ≤ 16 π²`.
* `tauOfV` + `tanh_tauOfV_eq_lowerY_edgeF` + `continuous_thetaOut_data` + `expThetaOut_D2_global`:
  uniform `D2 (Ioi 0)` bound for `v ↦ exp(i θ_out(y(F(v))))`.
* `oneSubExp_D2_global`, `auxInv_D2_global`: uniform `D2 (Ici 0)` bounds for
  `(1 - exp(-4π F(v)))²` and `(1 - 2iv)⁻¹`.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Saddle
open FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.CtOsc

noncomputable section

/-! ### 1. `D2` combinators -/

lemma D2_mulC {I : Set ℝ} {f f1 f2 g g1 g2 : ℝ → ℂ} {Kf Kg : ℝ}
    (hf : D2 I f f1 f2 Kf) (hg : D2 I g g1 g2 Kg) :
    D2 I (fun v => f v * g v) (fun v => f1 v * g v + f v * g1 v)
      (fun v => f2 v * g v + 2 * (f1 v * g1 v) + f v * g2 v) (4 * Kf * Kg) where
  d1 v hv := (hf.d1 v hv).mul (hg.d1 v hv)
  d2 v hv := ((hf.d2 v hv).mul (hg.d1 v hv)).add ((hf.d1 v hv).mul (hg.d2 v hv)) |>.congr_deriv (by ring)
  c2 := ((hf.c2.mul hg.cont0).add (continuousOn_const.mul (hf.cont1.mul hg.cont1))).add
    (hf.cont0.mul hg.c2)
  K0 := by have := hf.K0; have := hg.K0; positivity
  b0 v hv := by
    have h0 := norm_mul_le (f v) (g v)
    have h1 := mul_le_mul (hf.b0 v hv) (hg.b0 v hv) (norm_nonneg _) hf.K0
    have hnn : 0 ≤ Kf * Kg := mul_nonneg hf.K0 hg.K0
    nlinarith only [h0, h1, hnn]
  b1 v hv := by
    have h1 := (norm_mul_le (f1 v) (g v)).trans (mul_le_mul (hf.b1 v hv) (hg.b0 v hv) (norm_nonneg _) hf.K0)
    have h2 := (norm_mul_le (f v) (g1 v)).trans (mul_le_mul (hf.b0 v hv) (hg.b1 v hv) (norm_nonneg _) hf.K0)
    have hnn : 0 ≤ Kf * Kg := mul_nonneg hf.K0 hg.K0
    exact (norm_add_le _ _).trans (by nlinarith only [h1, h2, hnn])
  b2 v hv := by
    have h1 := (norm_mul_le (f2 v) (g v)).trans (mul_le_mul (hf.b2 v hv) (hg.b0 v hv) (norm_nonneg _) hf.K0)
    have h2 := (norm_mul_le (f1 v) (g1 v)).trans (mul_le_mul (hf.b1 v hv) (hg.b1 v hv) (norm_nonneg _) hf.K0)
    have h3 := (norm_mul_le (f v) (g2 v)).trans (mul_le_mul (hf.b0 v hv) (hg.b2 v hv) (norm_nonneg _) hf.K0)
    have h2n : ‖2 * (f1 v * g1 v)‖ ≤ 2 * (Kf * Kg) := by
      rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]; linarith only [h2]
    exact (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2n)) h3).trans_eq (by ring))

lemma D2_re {I : Set ℝ} {f f1 f2 : ℝ → ℂ} {K : ℝ} (hf : D2 I f f1 f2 K) :
    D2 I (fun v => (f v).re) (fun v => (f1 v).re) (fun v => (f2 v).re) K where
  d1 v hv := Complex.reCLM.hasFDerivAt.comp_hasDerivAt v (hf.d1 v hv)
  d2 v hv := Complex.reCLM.hasFDerivAt.comp_hasDerivAt v (hf.d2 v hv)
  c2 := Complex.continuous_re.comp_continuousOn hf.c2
  K0 := hf.K0
  b0 v hv := by rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hf.b0 v hv)
  b1 v hv := by rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hf.b1 v hv)
  b2 v hv := by rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hf.b2 v hv)

/-! ### 2. Global `edgeF` derivative bounds on `[0, ∞)` -/

lemma edgeF'_strictMonoOn_nonneg : StrictMonoOn edgeF' (Ici (0 : ℝ)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0)
    (continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF' v).continuousAt).continuousOn ?_
  intro v _
  rw [(hasDerivAt_edgeF' v).deriv]
  exact edgeF''_pos v

lemma edgeF'_le_one (v : ℝ) : edgeF' v ≤ 1 := by
  unfold edgeF'
  have h1 : Real.sinh (π * v) ≤ Real.cosh (π * v) := (Real.sinh_lt_cosh (π * v)).le
  have h2 : Real.cosh (π * v) ≤ √(1 + Real.cosh (π * v) ^ 2) := by
    rw [Real.le_sqrt (Real.cosh_pos _).le (by positivity)]; linarith
  exact (div_le_one (Real.sqrt_pos.mpr (by positivity))).mpr (h1.trans h2)

lemma edgeF'_ge_of_ge {v₀ v : ℝ} (hv₀ : 0 ≤ v₀) (hv : v₀ ≤ v) :
    edgeF' v₀ ≤ edgeF' v :=
  edgeF'_strictMonoOn_nonneg.monotoneOn (Set.mem_Ici.mpr hv₀) (Set.mem_Ici.mpr (hv₀.trans hv)) hv

lemma edgeF_sub_ge_mul_of_ge {v₀ v₁ v₂ : ℝ} (hv₀ : 0 < v₀) (hv1 : v₀ ≤ v₁) (hv12 : v₁ ≤ v₂) :
    edgeF' v₀ * (v₂ - v₁) ≤ edgeF v₂ - edgeF v₁ := by
  rcases eq_or_lt_of_le hv12 with rfl | hlt
  · simp
  · obtain ⟨c, hc, hce⟩ := exists_hasDerivAt_eq_slope edgeF edgeF' hlt
      (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeF t).continuousAt).continuousOn
      fun t _ => hasDerivAt_edgeF t
    rw [eq_div_iff (sub_ne_zero.mpr hlt.ne')] at hce
    have hge : edgeF' v₀ ≤ edgeF' c := edgeF'_ge_of_ge hv₀.le (hv1.trans hc.1.le)
    rw [← hce]
    exact mul_le_mul_of_nonneg_right hge (sub_nonneg.mpr hv12)

lemma edgeF_deriv_bounds_of_ge {v₀ : ℝ} (hv₀ : 0 < v₀) {v : ℝ} (hv : v₀ ≤ v) :
    edgeF' v₀ ≤ edgeF' v ∧ edgeF' v ≤ 1 ∧ 0 < edgeF'' v ∧ edgeF'' v ≤ 8 * π ∧
      |edgeF''' v| ≤ 16 * π ^ 2 := by
  have hv0 : 0 ≤ v := hv₀.le.trans hv
  have h1 : Real.exp (-(2 * π * v)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hv0])
  have h2 := edgeF''_bound hv0
  have h3 := edgeF'''_bound hv0
  refine ⟨edgeF'_ge_of_ge hv₀.le hv, edgeF'_le_one v, h2.1,
    h2.2.trans (by nlinarith [Real.pi_pos, h1]),
    h3.trans (by nlinarith [pow_pos Real.pi_pos 2, h1])⟩

/-! ### 3. Smooth strip coordinate `tauOfV` matching `lowerY (edgeF v)` and `Continuous Θ₂` -/

/-- Smooth coordinate `τ(v) = (2/π) arsinh(sinh(πv)/√2)` satisfying `tanh(π τ(v)/4) = lowerY (edgeF v)`. -/
def tauOfV (v : ℝ) : ℝ :=
  (2 / π) * Real.arsinh (Real.sinh (π * v) / √2)

lemma tauOfV_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ tauOfV v := by
  unfold tauOfV
  exact mul_nonneg (by positivity) (Real.arsinh_nonneg_iff.mpr
    (div_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg Real.pi_pos.le hv)) (Real.sqrt_nonneg 2)))

lemma tanh_tauOfV_eq_lowerY_edgeF {v : ℝ} (hv : 0 ≤ v) :
    Real.tanh (π * tauOfV v / 4) = lowerY (edgeF v) := by
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  have hτ_eq : vT (tauOfV v) = v := by
    have hcos_eq : Real.cosh (π * vT (tauOfV v)) = Real.cosh (π * v) := by
      unfold vT
      rw [mul_div_cancel₀ _ hpi, Real.cosh_arsinh]
      have hsh1 : Real.sinh (π * tauOfV v / 2) = Real.sinh (π * v) / √2 := by
        unfold tauOfV
        rw [show π * ((2 / π) * Real.arsinh (Real.sinh (π * v) / √2)) / 2 =
            Real.arsinh (Real.sinh (π * v) / √2) by field_simp, Real.sinh_arsinh]
      rw [hsh1, mul_pow, Real.sq_sqrt zero_le_two, div_pow, Real.sq_sqrt zero_le_two]
      have hch := Real.cosh_sq_sub_sinh_sq (π * v)
      rw [show 1 + 2 * (Real.sinh (π * v) ^ 2 / 2) = Real.cosh (π * v) ^ 2 by linarith]
      exact Real.sqrt_sq (Real.cosh_pos _).le
    have hvT_nn : 0 ≤ vT (tauOfV v) := vT_nonneg (tauOfV_nonneg hv)
    have hch_inj := (Real.cosh_injOn.eq_iff (Set.mem_Ici.mpr (mul_nonneg Real.pi_pos.le hvT_nn))
      (Set.mem_Ici.mpr (mul_nonneg Real.pi_pos.le hv))).mp hcos_eq
    exact mul_left_cancel₀ hpi hch_inj
  have hlower := lowerY_xT (tauOfV_nonneg hv)
  rw [← edgeF_vT (tauOfV v), hτ_eq] at hlower
  exact hlower.symm

lemma continuous_thetaOut_data :
    ∃ C : ℝ, 0 < C ∧ ∃ Θ1 Θ2 : ℝ → ℝ,
      (∀ τ, HasDerivAt thetaOutT (Θ1 τ) τ) ∧
      (∀ τ, HasDerivAt Θ1 (Θ2 τ) τ) ∧
      Continuous Θ2 ∧
      (∀ τ : ℝ, 0 ≤ τ → |Θ1 τ| ≤ C * Real.exp (-((π / 2) * τ)) ∧
        |Θ2 τ| ≤ C * Real.exp (-((π / 2) * τ))) := by
  obtain ⟨d1, d2, d3, h1, h2, h3, ⟨B1, hB1⟩, ⟨A, hA⟩⟩ := aRest_deriv_data
  have hexp1 : ∀ t : ℝ, Real.exp (-((π / 2) * |t|)) ≤ 1 := fun t => by
    rw [← Real.exp_zero]; apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos, abs_nonneg t]
  have hd2_bd : ∀ t, |d2 t| ≤ A := fun t => ((hA t).1).trans (by
    have hA0 : 0 ≤ A := by have := (hA 0).1; simp at this; exact (abs_nonneg _).trans this
    nlinarith [hexp1 t, Real.exp_pos (-((π / 2) * |t|))])
  have hd3_bd : ∀ t, |d3 t| ≤ A := fun t => ((hA t).2).trans (by
    have hA0 : 0 ≤ A := by have := (hA 0).2; simp at this; exact (abs_nonneg _).trans this
    nlinarith [hexp1 t, Real.exp_pos (-((π / 2) * |t|))])
  have hc_d2 : Continuous d2 := continuous_iff_continuousAt.mpr fun t => (h3 t).continuousAt
  have hc_bdry : Continuous (bdryF d2) := by
    have hfun : bdryF d2 = fun x : ℝ => ∫ s : ℝ, (d2 (x + s) - d2 x) / Real.sinh (π * s) :=
      funext (bdryF_eq_shift d2)
    rw [hfun]
    refine continuous_of_dominated (bound := StripBdry.majL A) ?_ ?_ (StripBdry.integrable_majL A) ?_
    · intro x
      exact (((hc_d2.comp (continuous_const.add continuous_id)).measurable.sub
        measurable_const).div ((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).measurable)).aestronglyMeasurable
    · intro x
      filter_upwards with s
      rw [Real.norm_eq_abs]
      exact StripBdry.shift_integrand_le_lin h3 hd3_bd x s
    · have hae : ∀ᵐ s : ℝ ∂volume, s ≠ 0 := by
        rw [ae_iff, show {s : ℝ | ¬ s ≠ 0} = {(0 : ℝ)} by ext s; simp]; simp
      filter_upwards [hae] with s _hs
      exact (((hc_d2.comp (continuous_id.add continuous_const)).sub hc_d2).div_const _)
  have hc_e2 : Continuous e2 := by
    unfold e2
    have hpos1 : ∀ τ : ℝ, Real.cosh (π * τ / 1) ^ 2 ≠ 0 := fun τ => pow_ne_zero 2 (Real.cosh_pos _).ne'
    have hpos2 : ∀ τ : ℝ, Real.cosh (π * τ / 2) ^ 2 ≠ 0 := fun τ => pow_ne_zero 2 (Real.cosh_pos _).ne'
    exact (continuous_const.mul
        (((Real.continuous_sinh.comp ((continuous_const.mul continuous_id).div_const 1)).mul continuous_const).neg.div
          ((Real.continuous_cosh.comp ((continuous_const.mul continuous_id).div_const 1)).pow 2) hpos1)).sub
      (continuous_const.mul
        (((Real.continuous_sinh.comp ((continuous_const.mul continuous_id).div_const 2)).mul continuous_const).neg.div
          ((Real.continuous_cosh.comp ((continuous_const.mul continuous_id).div_const 2)).pow 2) hpos2))
  obtain ⟨C0, _hC0pos, hC0⟩ := StripBdry.abs_bdryF_decay_half
  have hfun : thetaOutT = fun τ => epsT τ + bdryF aRest τ := by
    funext τ; rw [thetaOutT_eq]; unfold epsT; ring
  have hF1 : ∀ τ, HasDerivAt (bdryF aRest) (bdryF d1 τ) τ :=
    fun τ => StripBdry.hasDerivAt_bdryF_lin h1 h2 hB1 hd2_bd τ
  have hF2 : ∀ τ, HasDerivAt (bdryF d1) (bdryF d2 τ) τ :=
    fun τ => StripBdry.hasDerivAt_bdryF_lin h2 h3 hd2_bd hd3_bd τ
  have hth1 : ∀ τ, HasDerivAt thetaOutT (e1 τ + bdryF d1 τ) τ := fun τ => by
    rw [hfun]; exact (hasDerivAt_epsT τ).add (hF1 τ)
  have hth2 : ∀ τ, HasDerivAt (fun τ => e1 τ + bdryF d1 τ) (e2 τ + bdryF d2 τ) τ :=
    fun τ => (hasDerivAt_e1 τ).add (hF2 τ)
  have conv : ∀ {A' : ℝ} {g' : ℝ → ℝ}, (∀ t, |g' t| ≤ A' * Real.exp (-((π / 2) * |t|))) →
      ∀ t, |g' t| ≤ A' * Real.exp (-(π / 2) * |t|) := fun h t => by rw [neg_mul]; exact h t
  have hb1 : ∀ τ : ℝ, 0 ≤ τ → |bdryF d1 τ| ≤ C0 * (A + B1) * Real.exp (-((π / 2) * τ)) := fun τ hτ => by
    have := hC0 h2 (conv (fun t => (hA t).1)) hB1 τ hτ
    rwa [neg_mul] at this
  have hb2 : ∀ τ : ℝ, 0 ≤ τ → |bdryF d2 τ| ≤ C0 * (A + A) * Real.exp (-((π / 2) * τ)) := fun τ hτ => by
    have := hC0 h3 (conv (fun t => (hA t).2)) hd2_bd τ hτ
    rwa [neg_mul] at this
  have hB1_nn : 0 ≤ B1 := (abs_nonneg _).trans (hB1 0)
  have hA_nn : 0 ≤ A := (abs_nonneg _).trans (hd2_bd 0)
  let K : ℝ := (π / 2 + 5 * π / 4) + C0 * (A + B1) + ((π ^ 2 / 2 + 5 * π ^ 2 / 8) + C0 * (A + A)) + 1
  refine ⟨K, by positivity, fun τ => e1 τ + bdryF d1 τ, fun τ => e2 τ + bdryF d2 τ,
    hth1, hth2, hc_e2.add hc_bdry, fun τ hτ => ?_⟩
  have hE := Real.exp_pos (-((π / 2) * τ))
  have he12 := abs_e1_e2_le τ
  rw [abs_of_nonneg hτ] at he12
  have hb1t := hb1 τ hτ
  have hb2t := hb2 τ hτ
  refine ⟨(abs_add_le _ _).trans ?_, (abs_add_le _ _).trans ?_⟩
  · have hxa : 0 ≤ C0 * (A + A) := by positivity
    have hpi := Real.pi_pos
    have hK : ((π / 2 + 5 * π / 4) + C0 * (A + B1)) ≤ K := by
      dsimp [K]; linarith [sq_nonneg π]
    calc |e1 τ| + |bdryF d1 τ|
        ≤ (π / 2 + 5 * π / 4) * Real.exp (-((π / 2) * τ)) + C0 * (A + B1) * Real.exp (-((π / 2) * τ)) :=
          add_le_add he12.1 hb1t
      _ = ((π / 2 + 5 * π / 4) + C0 * (A + B1)) * Real.exp (-((π / 2) * τ)) := by ring
      _ ≤ K * Real.exp (-((π / 2) * τ)) := mul_le_mul_of_nonneg_right hK hE.le
  · have hxb : 0 ≤ C0 * (A + B1) := by positivity
    have hpi := Real.pi_pos
    have hK : ((π ^ 2 / 2 + 5 * π ^ 2 / 8) + C0 * (A + A)) ≤ K := by
      dsimp [K]; linarith
    calc |e2 τ| + |bdryF d2 τ|
        ≤ (π ^ 2 / 2 + 5 * π ^ 2 / 8) * Real.exp (-((π / 2) * τ)) + C0 * (A + A) * Real.exp (-((π / 2) * τ)) :=
          add_le_add he12.2 hb2t
      _ = ((π ^ 2 / 2 + 5 * π ^ 2 / 8) + C0 * (A + A)) * Real.exp (-((π / 2) * τ)) := by ring
      _ ≤ K * Real.exp (-((π / 2) * τ)) := mul_le_mul_of_nonneg_right hK hE.le

lemma tauOfV_derivs :
    let τ1 : ℝ → ℝ := fun v => 2 * Real.cosh (π * v) / √(1 + Real.cosh (π * v) ^ 2)
    let τ2 : ℝ → ℝ := fun v => 2 * π * Real.sinh (π * v) / (1 + Real.cosh (π * v) ^ 2) ^ (3 / 2 : ℝ)
    (∀ v, HasDerivAt tauOfV (τ1 v) v) ∧
    (∀ v, HasDerivAt τ1 (τ2 v) v) ∧
    Continuous τ2 ∧
    (∀ v : ℝ, 0 ≤ v → |τ1 v| ≤ 2 ∧ |τ2 v| ≤ 2 * π) := by
  let τ1 : ℝ → ℝ := fun v => 2 * Real.cosh (π * v) / √(1 + Real.cosh (π * v) ^ 2)
  let τ2 : ℝ → ℝ := fun v => 2 * π * Real.sinh (π * v) / (1 + Real.cosh (π * v) ^ 2) ^ (3 / 2 : ℝ)
  have hpi := Real.pi_pos
  have hd_tau : ∀ v : ℝ, HasDerivAt tauOfV (τ1 v) v := fun v => by
    unfold tauOfV
    have hsh : HasDerivAt (fun t => Real.sinh (π * t) / √2) (Real.cosh (π * v) * π / √2) v :=
      (((Real.hasDerivAt_sinh (π * v)).comp v ((hasDerivAt_id v).const_mul π)).div_const √2).congr_deriv
        (by simp)
    have hars := (Real.hasDerivAt_arsinh _).comp v hsh
    have hsq : 1 + (Real.sinh (π * v) / √2) ^ 2 = (1 + Real.cosh (π * v) ^ 2) / 2 := by
      rw [div_pow, Real.sq_sqrt zero_le_two]
      linarith [Real.cosh_sq_sub_sinh_sq (π * v)]
    refine (hars.const_mul (2 / π)).congr_deriv ?_
    rw [hsq, Real.sqrt_div (by positivity)]
    dsimp [τ1]
    have hrt : √(1 + Real.cosh (π * v) ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have hrt2 : √2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
    field_simp [hpi.ne', hrt, hrt2]
  have hd_τ1 : ∀ v : ℝ, HasDerivAt τ1 (τ2 v) v := fun v => by
    have hch : HasDerivAt (fun t => 2 * Real.cosh (π * t)) (2 * π * Real.sinh (π * v)) v :=
      (((Real.hasDerivAt_cosh (π * v)).comp v ((hasDerivAt_id v).const_mul π)).const_mul 2).congr_deriv
        (by ring)
    have hc1 : HasDerivAt (fun t => Real.cosh (π * t)) (π * Real.sinh (π * v)) v :=
      ((Real.hasDerivAt_cosh (π * v)).comp v ((hasDerivAt_id v).const_mul π)).congr_deriv (by ring)
    have hch2 : HasDerivAt (fun t => 1 + Real.cosh (π * t) ^ 2)
        (2 * Real.cosh (π * v) * (π * Real.sinh (π * v))) v :=
      ((hc1.pow 2).const_add 1).congr_deriv (by ring)
    have hsq_pos : 0 < 1 + Real.cosh (π * v) ^ 2 := by positivity
    have hsqrt : HasDerivAt (fun t => √(1 + Real.cosh (π * t) ^ 2))
        (π * Real.cosh (π * v) * Real.sinh (π * v) / √(1 + Real.cosh (π * v) ^ 2)) v :=
      (hch2.sqrt hsq_pos.ne').congr_deriv (by ring)
    have hd := hch.div hsqrt (Real.sqrt_pos.mpr hsq_pos).ne'
    refine hd.congr_deriv ?_
    have h32 : (1 + Real.cosh (π * v) ^ 2) ^ (3 / 2 : ℝ) =
        (1 + Real.cosh (π * v) ^ 2) * √(1 + Real.cosh (π * v) ^ 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hsq_pos.le (by norm_num : (1 : ℝ) + 1 / 2 ≠ 0)]
      norm_num
    dsimp [τ2]
    rw [h32]
    have hrt : √(1 + Real.cosh (π * v) ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hsq_pos).ne'
    have hsq_r := Real.sq_sqrt hsq_pos.le
    field_simp [hsq_pos.ne', hrt]
    rw [hsq_r]
    ring
  have hc_τ2 : Continuous τ2 := by
    dsimp [τ2]
    exact (continuous_const.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).div
      ((continuous_const.add ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).pow 2)).rpow_const
        fun t => Or.inl (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _)).ne')
      fun t => (Real.rpow_pos_of_pos (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _)) _).ne'
  refine ⟨hd_tau, hd_τ1, hc_τ2, fun v hv => ?_⟩
  have hc_pos : 0 < Real.cosh (π * v) := Real.cosh_pos _
  have hsq_le : Real.cosh (π * v) ≤ √(1 + Real.cosh (π * v) ^ 2) := by
    rw [Real.le_sqrt hc_pos.le (by positivity)]; linarith
  have hτ1_bd : |τ1 v| ≤ 2 := by
    dsimp [τ1]
    rw [abs_of_pos (div_pos (by positivity) (Real.sqrt_pos.mpr (by positivity)))]
    exact (div_le_iff₀ (Real.sqrt_pos.mpr (by positivity))).mpr (by nlinarith)
  have hs_nn : 0 ≤ Real.sinh (π * v) := Real.sinh_nonneg_iff.mpr (mul_nonneg hpi.le hv)
  have hs_le : Real.sinh (π * v) ≤ Real.cosh (π * v) := (Real.sinh_lt_cosh _).le
  have hc_pow : Real.cosh (π * v) ≤ (1 + Real.cosh (π * v) ^ 2) ^ (3 / 2 : ℝ) := by
    have h1 : 1 ≤ (1 + Real.cosh (π * v) ^ 2) := by nlinarith [Real.one_le_cosh (π * v)]
    have h2 : Real.cosh (π * v) ≤ 1 + Real.cosh (π * v) ^ 2 := by nlinarith [Real.one_le_cosh (π * v)]
    have h3 : (1 + Real.cosh (π * v) ^ 2) ^ (1 : ℝ) ≤ (1 + Real.cosh (π * v) ^ 2) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    rw [Real.rpow_one] at h3
    exact h2.trans h3
  have hτ2_bd : |τ2 v| ≤ 2 * π := by
    dsimp [τ2]
    rw [abs_of_nonneg (div_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _))]
    rw [div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)]
    calc 2 * π * Real.sinh (π * v) ≤ 2 * π * Real.cosh (π * v) := by gcongr
      _ ≤ 2 * π * (1 + Real.cosh (π * v) ^ 2) ^ (3 / 2 : ℝ) := by gcongr
  exact ⟨hτ1_bd, hτ2_bd⟩

lemma expThetaOut_D2_global :
    ∃ K_th : ℝ, 0 < K_th ∧ ∃ E1 E2 : ℝ → ℂ,
      D2 (Ioi (0 : ℝ)) (fun v => Complex.exp (Complex.I * (thetaOut (lowerY (edgeF v)) : ℂ))) E1 E2 K_th := by
  obtain ⟨C, hC_pos, Θ1, Θ2, hd1, hd2, hc_Θ2, hb⟩ := continuous_thetaOut_data
  obtain ⟨hd_tau, hd_τ1, hc_τ2, hτ_bd⟩ := tauOfV_derivs
  let τ1 : ℝ → ℝ := fun v => 2 * Real.cosh (π * v) / √(1 + Real.cosh (π * v) ^ 2)
  let τ2 : ℝ → ℝ := fun v => 2 * π * Real.sinh (π * v) / (1 + Real.cosh (π * v) ^ 2) ^ (3 / 2 : ℝ)
  let θ1 : ℝ → ℝ := fun v => Θ1 (tauOfV v) * τ1 v
  let θ2 : ℝ → ℝ := fun v => Θ2 (tauOfV v) * τ1 v ^ 2 + Θ1 (tauOfV v) * τ2 v
  let E := fun v : ℝ => Complex.exp (Complex.I * (thetaOutT (tauOfV v) : ℂ))
  let E1 : ℝ → ℂ := fun v => Complex.I * (θ1 v : ℂ) * E v
  let E2 : ℝ → ℂ := fun v => (Complex.I * (θ2 v : ℂ) - ((θ1 v ^ 2 : ℝ) : ℂ)) * E v
  have hd_th : ∀ v, HasDerivAt (fun t => thetaOutT (tauOfV t)) (θ1 v) v := fun v =>
    (hd1 (tauOfV v)).comp v (hd_tau v)
  have hd_th1 : ∀ v, HasDerivAt θ1 (θ2 v) v := fun v =>
    (((hd2 (tauOfV v)).comp v (hd_tau v)).mul (hd_τ1 v)).congr_deriv (by dsimp [θ2]; ring)
  have hc_tau : Continuous tauOfV := continuous_iff_continuousAt.mpr fun v => (hd_tau v).continuousAt
  have hc_τ1 : Continuous τ1 := continuous_iff_continuousAt.mpr fun v => (hd_τ1 v).continuousAt
  have hc_Θ1 : Continuous Θ1 := continuous_iff_continuousAt.mpr fun τ => (hd2 τ).continuousAt
  have hc_thT : Continuous thetaOutT := continuous_iff_continuousAt.mpr fun τ => (hd1 τ).continuousAt
  have hc_E : Continuous E := Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp (hc_thT.comp hc_tau)))
  have hc_θ1 : Continuous θ1 := (hc_Θ1.comp hc_tau).mul hc_τ1
  have hc_θ2 : Continuous θ2 := ((hc_Θ2.comp hc_tau).mul (hc_τ1.pow 2)).add ((hc_Θ1.comp hc_tau).mul hc_τ2)
  have hc_E2 : Continuous E2 := ((continuous_const.mul (Complex.continuous_ofReal.comp hc_θ2)).sub
    (Complex.continuous_ofReal.comp (hc_θ1.pow 2))).mul hc_E
  let K_th : ℝ := (2 * C) ^ 2 + (4 * C + 2 * π * C) + 1
  have hKth_pos : 0 < K_th := by have := Real.pi_pos; dsimp [K_th]; positivity
  have hD2_th : D2 (Ici (0 : ℝ)) E E1 E2 K_th := {
    d1 := fun v _ => (((hd_th v).ofReal_comp.const_mul Complex.I).cexp).congr_deriv (by dsimp [E1, E]; ring)
    d2 := fun v _ => by
      have hcE : HasDerivAt E (E1 v) v :=
        (((hd_th v).ofReal_comp.const_mul Complex.I).cexp).congr_deriv (by dsimp [E1, E]; ring)
      have h1 := ((hd_th1 v).ofReal_comp.const_mul Complex.I).mul hcE
      refine h1.congr_deriv ?_
      dsimp [E2, E1, E]; push_cast
      linear_combination ((θ1 v : ℂ) ^ 2 * Complex.exp (Complex.I * (thetaOutT (tauOfV v) : ℂ))) * Complex.I_sq
    c2 := hc_E2.continuousOn
    K0 := hKth_pos.le
    b0 := fun v _ => by
      have hEn : ‖E v‖ = 1 := by dsimp [E]; rw [mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]
      rw [hEn]; nlinarith [sq_nonneg (2 * C), Real.pi_pos]
    b1 := fun v hv => by
      rw [Set.mem_Ici] at hv
      have hEn : ‖E v‖ = 1 := by dsimp [E]; rw [mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]
      have hbd := hb (tauOfV v) (tauOfV_nonneg hv)
      have hexp_le : Real.exp (-((π / 2) * tauOfV v)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, tauOfV_nonneg hv])
      have hΘ1_bd : |Θ1 (tauOfV v)| ≤ C := hbd.1.trans (by nlinarith)
      have hτ_v := hτ_bd v hv
      have hθ1_bd : |θ1 v| ≤ 2 * C := by
        dsimp [θ1]; rw [abs_mul]
        exact (mul_le_mul hΘ1_bd hτ_v.1 (abs_nonneg _) hC_pos.le).trans_eq (mul_comm C 2)
      dsimp [E1]
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, hEn, mul_one]
      have h2C : 0 ≤ 2 * C := by linarith
      nlinarith [sq_nonneg (2 * C), Real.pi_pos]
    b2 := fun v hv => by
      rw [Set.mem_Ici] at hv
      have hEn : ‖E v‖ = 1 := by dsimp [E]; rw [mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]
      have hbd := hb (tauOfV v) (tauOfV_nonneg hv)
      have hexp_le : Real.exp (-((π / 2) * tauOfV v)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, tauOfV_nonneg hv])
      have hΘ1_bd : |Θ1 (tauOfV v)| ≤ C := hbd.1.trans (by nlinarith)
      have hΘ2_bd : |Θ2 (tauOfV v)| ≤ C := hbd.2.trans (by nlinarith)
      have hτ_v := hτ_bd v hv
      have hθ1_bd : |θ1 v| ≤ 2 * C := by
        dsimp [θ1]; rw [abs_mul]
        exact (mul_le_mul hΘ1_bd hτ_v.1 (abs_nonneg _) hC_pos.le).trans_eq (mul_comm C 2)
      have hθ2_bd : |θ2 v| ≤ 4 * C + 2 * π * C := by
        dsimp [θ2]
        have ht1 : |Θ2 (tauOfV v) * τ1 v ^ 2| ≤ C * 4 := by
          rw [abs_mul, abs_pow]
          exact mul_le_mul hΘ2_bd (by rw [← (by norm_num : (2 : ℝ) ^ 2 = 4)]; exact pow_le_pow_left₀ (abs_nonneg _) hτ_v.1 2)
            (sq_nonneg _) hC_pos.le
        have ht2 : |Θ1 (tauOfV v) * τ2 v| ≤ C * (2 * π) := by
          rw [abs_mul]; exact mul_le_mul hΘ1_bd hτ_v.2 (abs_nonneg _) hC_pos.le
        exact (abs_add_le _ _).trans (by linarith)
      dsimp [E2]
      rw [norm_mul, hEn, mul_one]
      have hsub := norm_sub_le (Complex.I * (θ2 v : ℂ)) ((θ1 v ^ 2 : ℝ) : ℂ)
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_pow] at hsub
      have hsq : |θ1 v| ^ 2 ≤ (2 * C) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hθ1_bd 2
      dsimp [K_th]; linarith }
  have hcongr_eq : ∀ v ∈ Ioi (0 : ℝ),
      Complex.exp (Complex.I * (thetaOut (lowerY (edgeF v)) : ℂ)) = E v := fun v hv => by
    dsimp [E, thetaOut]
    rw [← tanh_tauOfV_eq_lowerY_edgeF (Set.mem_Ioi.mp hv).le, Real.artanh_tanh]
    congr 2; congr 1
    have hpi : π ≠ 0 := Real.pi_pos.ne'
    field_simp [hpi]
  refine ⟨K_th, hKth_pos, E1, E2, {
    d1 := fun v hv => (hD2_th.d1 v (Ioi_subset_Ici_self hv)).congr_of_eventuallyEq
      (Eventually.mono (Ioi_mem_nhds hv) hcongr_eq)
    d2 := fun v hv => hD2_th.d2 v (Ioi_subset_Ici_self hv)
    c2 := hD2_th.c2.mono Ioi_subset_Ici_self
    K0 := hD2_th.K0
    b0 := fun v hv => by rw [hcongr_eq v hv]; exact hD2_th.b0 v (Ioi_subset_Ici_self hv)
    b1 := fun v hv => hD2_th.b1 v (Ioi_subset_Ici_self hv)
    b2 := fun v hv => hD2_th.b2 v (Ioi_subset_Ici_self hv) }⟩

/-! ### 4. Global `oneSubExp` and `auxInv` `D2` bounds -/

lemma oneSubExp_D2_global :
    ∃ K_e : ℝ, 0 < K_e ∧ ∃ G1 G2 : ℝ → ℂ,
      D2 (Ici (0 : ℝ)) (fun v => (((1 - Real.exp (-(4 * π * edgeF v))) ^ 2 : ℝ) : ℂ)) G1 G2 K_e := by
  have hpi := Real.pi_pos
  have hexp_le : ∀ v : ℝ, 0 ≤ v → Real.exp (-(4 * π * edgeF v)) ≤ 1 := fun v hv => by
    rw [Real.exp_le_one_iff]
    have hx : 0 ≤ edgeF v := xiStar_pos.le.trans (by
      rw [← edgeF_zero]
      rcases eq_or_lt_of_le hv with rfl | hp
      · exact le_rfl
      · exact (edgeF_strictMonoOn le_rfl hv hp).le)
    nlinarith
  let e := fun v : ℝ => Real.exp (-(4 * π * edgeF v))
  let h := fun v : ℝ => (1 - e v) ^ 2
  let h1 : ℝ → ℝ := fun v => 2 * (1 - e v) * (4 * π * edgeF' v * e v)
  let h2 : ℝ → ℝ := fun v =>
    2 * (4 * π * edgeF' v * e v) ^ 2 + 2 * (1 - e v) * (4 * π * (edgeF'' v - 4 * π * edgeF' v ^ 2) * e v)
  have hd_e : ∀ v, HasDerivAt e (-(4 * π * edgeF' v * e v)) v := fun v => by
    have h1 := ((hasDerivAt_edgeF v).const_mul (-(4 * π))).exp
    have heq : e = fun t => Real.exp (-(4 * π) * edgeF t) := by ext t; dsimp [e]; ring_nf
    rw [heq]; exact h1.congr_deriv (by dsimp [e]; ring)
  have hd_h : ∀ v, HasDerivAt h (h1 v) v := fun v =>
    (((hasDerivAt_const v (1 : ℝ)).sub (hd_e v)).pow 2).congr_deriv (by dsimp [h1, e]; ring)
  have hd_h1 : ∀ v, HasDerivAt h1 (h2 v) v := fun v => by
    have hp1 : HasDerivAt (fun t => 2 * (1 - e t)) (2 * (4 * π * edgeF' v * e v)) v :=
      (((hasDerivAt_const v (1 : ℝ)).sub (hd_e v)).const_mul 2).congr_deriv (by ring)
    have hp2 : HasDerivAt (fun t => 4 * π * edgeF' t * e t)
        (4 * π * (edgeF'' v - 4 * π * edgeF' v ^ 2) * e v) v :=
      (((hasDerivAt_edgeF' v).const_mul (4 * π)).mul (hd_e v)).congr_deriv (by ring)
    exact (hp1.mul hp2).congr_deriv (by dsimp [h2]; ring)
  have hF_c : Continuous edgeF := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF v).continuousAt
  have hF'_c : Continuous edgeF' := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF' v).continuousAt
  have hF''_c : Continuous edgeF'' := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF'' v).continuousAt
  have he_c : Continuous e := Real.continuous_exp.comp ((continuous_const.mul hF_c).neg)
  have hc_h2 : Continuous h2 := by
    dsimp [h2]
    exact (continuous_const.mul ((continuous_const.mul hF'_c |>.mul he_c).pow 2)).add
      ((continuous_const.mul (continuous_const.sub he_c)).mul
        ((continuous_const.mul (hF''_c.sub (continuous_const.mul (hF'_c.pow 2)))).mul he_c))
  let K_e : ℝ := 1 + 8 * π + 2 * (4 * π) ^ 2 + 2 * (4 * π * (8 * π + 4 * π))
  have hKe_pos : 0 < K_e := by positivity
  refine ⟨K_e, hKe_pos, fun v => (h1 v : ℂ), fun v => (h2 v : ℂ), {
    d1 := fun v _ => (hd_h v).ofReal_comp
    d2 := fun v _ => (hd_h1 v).ofReal_comp
    c2 := (Complex.continuous_ofReal.comp hc_h2).continuousOn
    K0 := hKe_pos.le
    b0 := fun v hv => by
      have he_nn : 0 ≤ e v := (Real.exp_pos _).le
      have he_1 : e v ≤ 1 := hexp_le v (Set.mem_Ici.mp hv)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hsub : (1 - e v) ^ 2 ≤ 1 := by nlinarith
      dsimp [K_e]; nlinarith [pow_pos hpi 2]
    b1 := fun v hv => by
      have hv0 := Set.mem_Ici.mp hv
      have he_nn : 0 ≤ e v := (Real.exp_pos _).le
      have he_1 : e v ≤ 1 := hexp_le v hv0
      have hF'_nn : 0 ≤ edgeF' v := edgeF'_nonneg hv0
      have hF'_1 : edgeF' v ≤ 1 := edgeF'_le_one v
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h1_nn : 0 ≤ h1 v := by dsimp [h1]; positivity
      rw [abs_of_nonneg h1_nn]
      have hle : h1 v ≤ 2 * 1 * (4 * π * 1 * 1) := by dsimp [h1]; gcongr; linarith
      dsimp [K_e]; nlinarith [pow_pos hpi 2]
    b2 := fun v hv => by
      have hv0 := Set.mem_Ici.mp hv
      have he_nn : 0 ≤ e v := (Real.exp_pos _).le
      have he_1 : e v ≤ 1 := hexp_le v hv0
      have hF'_nn : 0 ≤ edgeF' v := edgeF'_nonneg hv0
      have hF'_1 : edgeF' v ≤ 1 := edgeF'_le_one v
      have hF''_pos := (edgeF''_pos v).le
      have hF''_bd : edgeF'' v ≤ 8 * π := (edgeF''_bound hv0).2.trans (by
        have : Real.exp (-(2 * π * v)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        nlinarith)
      rw [Complex.norm_real, Real.norm_eq_abs]
      have ht1 : |2 * (4 * π * edgeF' v * e v) ^ 2| ≤ 2 * (4 * π) ^ 2 := by
        rw [abs_of_nonneg (by positivity)]
        have hmul : 4 * π * edgeF' v * e v ≤ 4 * π := by
          have : edgeF' v * e v ≤ 1 := by nlinarith
          nlinarith
        nlinarith [pow_le_pow_left₀ (by positivity : 0 ≤ 4 * π * edgeF' v * e v) hmul 2]
      have ht2 : |2 * (1 - e v) * (4 * π * (edgeF'' v - 4 * π * edgeF' v ^ 2) * e v)| ≤
          2 * (4 * π * (8 * π + 4 * π)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_mul, abs_mul,
          abs_of_nonneg (by positivity : 0 ≤ 4 * π), abs_of_nonneg he_nn]
        have hsub : |edgeF'' v - 4 * π * edgeF' v ^ 2| ≤ 8 * π + 4 * π := by
          refine (abs_sub _ _).trans ?_
          rw [abs_of_nonneg hF''_pos, abs_of_nonneg (by positivity)]
          have hsq1 : edgeF' v ^ 2 ≤ 1 := by
            nlinarith [mul_nonneg hF'_nn hF'_nn, hF'_1, hF'_nn]
          nlinarith
        have hm1 : |edgeF'' v - 4 * π * edgeF' v ^ 2| * e v ≤ (8 * π + 4 * π) * 1 :=
          mul_le_mul hsub he_1 he_nn (by positivity)
        have hm2 : 4 * π * |edgeF'' v - 4 * π * edgeF' v ^ 2| * e v ≤ 4 * π * (8 * π + 4 * π) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have hm3 : 2 * |1 - e v| ≤ 2 := by
          rw [abs_of_nonneg (by linarith)]; linarith
        exact mul_le_mul hm3 hm2 (by positivity) (by positivity)
      exact (abs_add_le _ _).trans (by dsimp [K_e]; linarith) }⟩

lemma auxInv_D2_global :
    ∃ G1 G2 : ℝ → ℂ,
      D2 (Ici (0 : ℝ)) (fun v => ((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹) G1 G2 8 := by
  let g := fun v : ℝ => ((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹
  let g1 : ℝ → ℂ := fun v => (2 * Complex.I) * g v ^ 2
  let g2 : ℝ → ℂ := fun v => (-8 : ℂ) * g v ^ 3
  have hne : ∀ v : ℝ, (1 : ℂ) - 2 * Complex.I * (v : ℂ) ≠ 0 := fun v h => by
    have := congrArg Complex.re h; simp at this
  have hnorm_le : ∀ v : ℝ, ‖g v‖ ≤ 1 := fun v => by
    dsimp [g]; rw [norm_inv]
    have h1 : 1 ≤ ‖(1 : ℂ) - 2 * Complex.I * (v : ℂ)‖ := by
      calc (1 : ℝ) = |((1 : ℂ) - 2 * Complex.I * (v : ℂ)).re| := by simp
        _ ≤ ‖(1 : ℂ) - 2 * Complex.I * (v : ℂ)‖ := Complex.abs_re_le_norm _
    exact inv_le_one_of_one_le₀ h1
  have hd_lin : ∀ v : ℝ, HasDerivAt (fun t : ℝ => (1 : ℂ) - 2 * Complex.I * (t : ℂ)) (-(2 * Complex.I)) v :=
    fun v => by
      have h1 := ((hasDerivAt_id v).ofReal_comp.const_mul (2 * Complex.I)).const_sub (1 : ℂ)
      exact h1.congr_deriv (by simp [mul_comm])
  have hd_g : ∀ v : ℝ, HasDerivAt g (g1 v) v := fun v =>
    ((hd_lin v).inv (hne v)).congr_deriv (by dsimp [g1, g]; field_simp [hne v])
  have hd_g1 : ∀ v : ℝ, HasDerivAt g1 (g2 v) v := fun v => by
    refine (((hd_g v).pow 2).const_mul (2 * Complex.I)).congr_deriv ?_
    dsimp [g2, g1, g]
    rw [show 2 * Complex.I * (2 * ((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹ ^ 1 *
          (2 * Complex.I * ((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹ ^ 2)) =
        (8 * Complex.I ^ 2) * ((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹ ^ 3 by ring,
      Complex.I_sq]
    ring
  have hc_g : Continuous g := by fun_prop (disch := exact hne)
  refine ⟨g1, g2, {
    d1 := fun v _ => hd_g v
    d2 := fun v _ => hd_g1 v
    c2 := (continuous_const.mul (hc_g.pow 3)).continuousOn
    K0 := by norm_num
    b0 := fun v _ => (hnorm_le v).trans (by norm_num)
    b1 := fun v _ => by
      dsimp [g1]; rw [norm_mul, norm_mul, norm_pow, show ‖(2 : ℂ)‖ = 2 by norm_num, Complex.norm_I, mul_one]
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) (hnorm_le v)) (by norm_num)).trans (by norm_num)
    b2 := fun v _ => by
      dsimp [g2]; rw [norm_mul, norm_pow, show ‖(-8 : ℂ)‖ = 8 by norm_num]
      simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) (hnorm_le v)) (by norm_num : (0 : ℝ) ≤ 8) }⟩

end

end FormalResearch.ModularBootstrap.FiveTerm
