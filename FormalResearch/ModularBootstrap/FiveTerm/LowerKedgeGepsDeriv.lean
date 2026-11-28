module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerKedgeAmpBase

/-!
# Uniform `ε`-Derivative Bounds (`cts:geps-deriv`)

Proves `mtSq_oscAmpBound` and `virasoro_geps_deriv` (`cts:geps-deriv`): for any `v₀ > 0`,
`kedgeAmp0 ε` and `kedgeAmp0Aux ε` satisfy `OscAmpBound v₀` with `L^∞` and `L¹` bounds on
`j = 0, 1, 2` derivatives uniformly for `ε ∈ Ioo 0 (1 / 2)`.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Saddle
open FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

noncomputable section

/-- The `x'`-independent edge-kernel amplitude without `(1 - 2 i v)⁻¹`. -/
def kedgeAmp0 (ε v : ℝ) : ℂ :=
  lowerMt ε (Complex.I * (lowerY (edgeF v) : ℂ)) ^ 2 *
    Complex.exp (Complex.I * (thetaOut (lowerY (edgeF v)) : ℂ)) *
    (((1 - Real.exp (-(4 * π * edgeF v))) ^ 2 * √(edgeF' v) : ℝ) : ℂ)

/-- Auxiliary amplitude `kedgeAmp0 * (1 - 2 i v)⁻¹`. -/
def kedgeAmp0Aux (ε v : ℝ) : ℂ :=
  kedgeAmp0 ε v * ((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹

private lemma sinh_div_cosh_add_mono {s t : ℝ} (_hs : 0 ≤ s) (hst : s ≤ t) :
    Real.sinh s / (Real.cosh s + √2) ≤ Real.sinh t / (Real.cosh t + √2) := by
  have h1 : 0 < Real.cosh s + √2 := by have := Real.cosh_pos s; positivity
  have h2 : 0 < Real.cosh t + √2 := by have := Real.cosh_pos t; positivity
  rw [div_le_div_iff₀ h1 h2]
  have hdiff : Real.sinh t * Real.cosh s - Real.cosh t * Real.sinh s = Real.sinh (t - s) := by
    rw [Real.sinh_sub]
  have hsnn : 0 ≤ Real.sinh (t - s) := Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr hst)
  have hsh_le : Real.sinh s ≤ Real.sinh t := Real.sinh_le_sinh.mpr hst
  nlinarith [Real.sqrt_nonneg 2]

private lemma lowerY_mono_on {x₁ x₂ : ℝ} (hx₁ : xiStar < x₁) (hx : x₁ ≤ x₂) :
    0 < lowerY x₁ ∧ lowerY x₁ ≤ lowerY x₂ ∧ lowerY x₂ < 1 := by
  have hx₂ : xiStar < x₂ := hx₁.trans_le hx
  have hy₁ : 0 < lowerY x₁ := (yOfX_mem hx₁).1
  have hy₂_0 : 0 < lowerY x₂ := (yOfX_mem hx₂).1
  have hy₂ : lowerY x₂ < 1 := (yOfX_mem hx₂).2
  have ha_le : slitA x₂ ≤ slitA x₁ := by
    unfold slitA
    have hx₁_nn : 0 ≤ π * x₁ := mul_nonneg Real.pi_pos.le (xiStar_pos.trans hx₁).le
    have hx₂_nn : 0 ≤ π * x₂ := mul_nonneg Real.pi_pos.le (xiStar_pos.trans hx₂).le
    have hc : Real.cosh (π * x₁) ≤ Real.cosh (π * x₂) := by
      rw [Real.cosh_le_cosh, abs_of_nonneg hx₁_nn, abs_of_nonneg hx₂_nn]
      exact mul_le_mul_of_nonneg_left hx Real.pi_pos.le
    have hden : 0 < Real.cosh (π * x₁) + √2 := by have := Real.cosh_pos (π * x₁); positivity
    exact div_le_div_of_nonneg_left (by positivity) hden (by linarith)
  have hsq : lowerY x₁ ^ 2 ≤ lowerY x₂ ^ 2 := by
    linarith [one_sub_lowerY_sq hx₁, one_sub_lowerY_sq hx₂]
  have hy_le : lowerY x₁ ≤ lowerY x₂ := by nlinarith [hy₁, hy₂_0]
  exact ⟨hy₁, hy_le, hy₂⟩

private lemma slitA_le_exp {x : ℝ} (_hx : 0 ≤ x) :
    slitA x ≤ 4 * √2 * Real.exp (-(π * x)) := by
  unfold slitA
  have hcosh : (1 / 2 : ℝ) * Real.exp (π * x) ≤ Real.cosh (π * x) + √2 := by
    rw [Real.cosh_eq]
    have he : 0 ≤ Real.exp (-(π * x)) := (Real.exp_pos _).le
    have hs : 0 ≤ √2 := Real.sqrt_nonneg 2
    linarith
  have hden : 0 < Real.cosh (π * x) + √2 := by have := Real.cosh_pos (π * x); positivity
  calc 2 * √2 / (Real.cosh (π * x) + √2)
      ≤ 2 * √2 / ((1 / 2 : ℝ) * Real.exp (π * x)) := by gcongr
    _ = 4 * √2 * Real.exp (-(π * x)) := by rw [Real.exp_neg]; field_simp; ring

/-- Integrability and uniform integral bound of
`ε * slitA(edgeF v) / (slitA(edgeF v) + ε)^2 * edgeF' v` on `Ioi v₀`. -/
private lemma mtWeight_integrableOn {v₀ ε : ℝ} (hv₀ : 0 < v₀) (hε : 0 < ε) :
    let w := fun v => ε * slitA (edgeF v) / (slitA (edgeF v) + ε) ^ 2 * edgeF' v
    IntegrableOn w (Ioi v₀) ∧
      ∫ v in Ioi v₀, w v ≤
        (π * (Real.sinh (π * edgeF v₀) / (Real.cosh (π * edgeF v₀) + √2)))⁻¹ := by
  intro w
  let x₀ := edgeF v₀
  let csh := Real.sinh (π * x₀) / (Real.cosh (π * x₀) + √2)
  have hx₀ : xiStar < x₀ := (edgeF_ge_of_ge hv₀ le_rfl).1
  have hcsh_pos : 0 < csh := by
    have h1 : 0 < Real.sinh (π * x₀) := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos (xiStar_pos.trans hx₀))
    have h2 : 0 < Real.cosh (π * x₀) + √2 := by have := Real.cosh_pos (π * x₀); positivity
    exact div_pos h1 h2
  let G : ℝ → ℝ := fun v => ε / (slitA (edgeF v) + ε)
  let G' : ℝ → ℝ := fun v =>
    -(ε * (-(π * Real.sinh (π * edgeF v) / (Real.cosh (π * edgeF v) + √2)) * slitA (edgeF v)) *
      edgeF' v) / (slitA (edgeF v) + ε) ^ 2
  have hG_deriv : ∀ v ∈ Ici v₀, HasDerivAt G (G' v) v := fun v _ => by
    have hda := ((slitA_derivs (edgeF v)).1.comp v (hasDerivAt_edgeF v)).add_const ε
    have hne : slitA (edgeF v) + ε ≠ 0 := (add_pos (slitA_pos _) hε).ne'
    exact ((hasDerivAt_const v ε).div hda hne).congr_deriv (by dsimp [G']; ring)
  have hG'_nonneg : ∀ v ∈ Ioi v₀, 0 ≤ G' v := fun v hv => by
    have hF' : 0 ≤ edgeF' v := (edgeF'_pos (hv₀.trans hv)).le
    have hsa : 0 ≤ slitA (edgeF v) := (slitA_pos _).le
    have hsh : 0 ≤ Real.sinh (π * edgeF v) :=
      Real.sinh_nonneg_iff.mpr (mul_nonneg Real.pi_pos.le ((xiStar_pos.trans hx₀).trans_le
        (edgeF_ge_of_ge hv₀ hv.le).2).le)
    have hden1 : 0 ≤ Real.cosh (π * edgeF v) + √2 := by have := Real.cosh_pos (π * edgeF v); positivity
    have hden2 : 0 ≤ (slitA (edgeF v) + ε) ^ 2 := by positivity
    dsimp [G']
    rw [show -(ε * (-(π * Real.sinh (π * edgeF v) / (Real.cosh (π * edgeF v) + √2)) * slitA (edgeF v)) *
        edgeF' v) = ε * (π * Real.sinh (π * edgeF v) / (Real.cosh (π * edgeF v) + √2)) * slitA (edgeF v) *
        edgeF' v by ring]
    positivity
  have ha_tend : Tendsto (fun v => slitA (edgeF v)) atTop (𝓝 0) := by
    have hexp_t : Tendsto (fun v : ℝ => 4 * √2 * Real.exp (-(π * v))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun v : ℝ => -(π * v)) atTop atBot := by
        simpa [neg_mul] using tendsto_id.const_mul_atTop_of_neg (neg_neg_iff_pos.2 Real.pi_pos)
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (4 * √2)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp_t
      (Eventually.of_forall fun v => (slitA_pos (edgeF v)).le) ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
    calc slitA (edgeF v) ≤ 4 * √2 * Real.exp (-(π * edgeF v)) :=
          slitA_le_exp (hv.trans (v_lt_edgeF v).le)
      _ ≤ 4 * √2 * Real.exp (-(π * v)) := by gcongr; exact (v_lt_edgeF v).le
  have hG_tend : Tendsto G atTop (𝓝 1) := by
    have h1 : Tendsto (fun v => ε / (slitA (edgeF v) + ε)) atTop (𝓝 (ε / (0 + ε))) :=
      tendsto_const_nhds.div (ha_tend.add tendsto_const_nhds) (by linarith)
    simpa [G, div_self hε.ne'] using h1
  have hGi := integrableOn_Ioi_deriv_of_nonneg' hG_deriv hG'_nonneg hG_tend
  have hGint := integral_Ioi_of_hasDerivAt_of_nonneg' hG_deriv hG'_nonneg hG_tend
  have h_le : ∀ v ∈ Ici v₀, π * csh * w v ≤ G' v := fun v hv => by
    have hF' : 0 ≤ edgeF' v := (edgeF'_pos (hv₀.trans_le hv)).le
    have hsa : 0 ≤ slitA (edgeF v) := (slitA_pos _).le
    have hFx := (edgeF_ge_of_ge hv₀ hv).2
    have hm := sinh_div_cosh_add_mono (mul_nonneg Real.pi_pos.le (xiStar_pos.trans hx₀).le)
      (mul_le_mul_of_nonneg_left hFx Real.pi_pos.le)
    dsimp [G', w]
    rw [show -(ε * (-(π * Real.sinh (π * edgeF v) / (Real.cosh (π * edgeF v) + √2)) * slitA (edgeF v)) *
        edgeF' v) = ε * (π * (Real.sinh (π * edgeF v) / (Real.cosh (π * edgeF v) + √2))) *
        slitA (edgeF v) * edgeF' v by ring]
    rw [show π * csh * (ε * slitA (edgeF v) / (slitA (edgeF v) + ε) ^ 2 * edgeF' v) =
        (ε * (π * csh) * slitA (edgeF v) * edgeF' v) / (slitA (edgeF v) + ε) ^ 2 by ring]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm Real.pi_pos.le) hε.le) hsa) hF')
      (sq_nonneg _)
  have hwc : ContinuousOn w (Ici v₀) := by
    have hF_c : Continuous edgeF := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF v).continuousAt
    have hF'_c : Continuous edgeF' := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF' v).continuousAt
    have ha_c : Continuous slitA := continuous_iff_continuousAt.mpr fun x => (slitA_derivs x).1.continuousAt
    exact ((continuousOn_const.mul (ha_c.comp hF_c).continuousOn).div
      (((ha_c.comp hF_c).continuousOn.add continuousOn_const).pow 2)
      (fun v _ => pow_ne_zero 2 (add_pos (slitA_pos _) hε).ne')).mul hF'_c.continuousOn
  have hw_int : IntegrableOn w (Ioi v₀) := by
    have hdom : IntegrableOn (fun v => (π * csh)⁻¹ * G' v) (Ioi v₀) := hGi.const_mul _
    refine hdom.mono' ((hwc.aestronglyMeasurable measurableSet_Ici).mono_set Ioi_subset_Ici_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hw_nn : 0 ≤ w v := by
      have := (edgeF'_pos (hv₀.trans hv)).le
      have := (slitA_pos (edgeF v)).le
      dsimp [w]; positivity
    rw [Real.norm_of_nonneg hw_nn, inv_mul_eq_div, le_div_iff₀ (mul_pos Real.pi_pos hcsh_pos)]
    linarith [h_le v hv.le]
  refine ⟨hw_int, ?_⟩
  have hint_le : ∫ v in Ioi v₀, π * csh * w v ≤ ∫ v in Ioi v₀, G' v :=
    integral_mono_ae (hw_int.const_mul _) hGi
      ((ae_restrict_mem measurableSet_Ioi).mono fun v hv => h_le v hv.le)
  have hG_nn : 0 ≤ G v₀ := div_nonneg hε.le (add_pos (slitA_pos _) hε).le
  rw [integral_const_mul, hGint] at hint_le
  rw [← one_div, le_div_iff₀' (mul_pos Real.pi_pos hcsh_pos)]
  linarith

private def mtA1 (t : ℝ) : ℝ := -(π * Real.sinh (π * t) / (Real.cosh (π * t) + √2)) * slitA t
private def mtA2 (t : ℝ) : ℝ :=
  π ^ 2 * (2 * Real.sinh (π * t) ^ 2 / (Real.cosh (π * t) + √2) ^ 2 -
    Real.cosh (π * t) / (Real.cosh (π * t) + √2)) * slitA t
private def mtY1 (t : ℝ) : ℝ := -mtA1 t / (2 * lowerY t)
private def mtY2 (t : ℝ) : ℝ := -mtA2 t / (2 * lowerY t) - mtA1 t ^ 2 / (4 * lowerY t ^ 3)
private def mtD (ε t : ℝ) : ℂ := ((slitA t + ε : ℝ) : ℂ) + Complex.I * ((ε * lowerY t : ℝ) : ℂ)
private def mtD1 (ε t : ℝ) : ℂ := (mtA1 t : ℂ) + Complex.I * ((ε * mtY1 t : ℝ) : ℂ)
private def mtN1 (t : ℝ) : ℂ :=
  (mtA1 t : ℂ) * (1 + Complex.I * (lowerY t : ℂ)) - Complex.I * ((slitA t * mtY1 t : ℝ) : ℂ)
private def mtN2 (t : ℝ) : ℂ :=
  (mtA2 t : ℂ) * (1 + Complex.I * (lowerY t : ℂ)) - Complex.I * ((slitA t * mtY2 t : ℝ) : ℂ)
private def mtQ (ε t : ℝ) : ℂ := (slitA t : ℂ) / mtD ε t
private def mtQ1 (ε t : ℝ) : ℂ := (ε : ℂ) * mtN1 t / mtD ε t ^ 2
private def mtQ2 (ε t : ℝ) : ℂ := (ε : ℂ) * (mtN2 t * mtD ε t - 2 * mtN1 t * mtD1 ε t) / mtD ε t ^ 3
private def mtM1x (ε t : ℝ) : ℂ := ((1 + ε : ℝ) : ℂ) ^ 2 * (2 * mtQ ε t * mtQ1 ε t)
private def mtM2x (ε t : ℝ) : ℂ := ((1 + ε : ℝ) : ℂ) ^ 2 * (2 * (mtQ1 ε t ^ 2 + mtQ ε t * mtQ2 ε t))

private lemma mtSq_x_derivs {ε x : ℝ} (hε : 0 < ε) (hx : xiStar < x) :
    HasDerivAt (fun t => ((1 + ε : ℝ) : ℂ) ^ 2 * mtQ ε t ^ 2) (mtM1x ε x) x ∧
    HasDerivAt (mtM1x ε) (mtM2x ε x) x := by
  have ha0 : 0 < slitA x := slitA_pos x
  have hy0 : 0 < lowerY x := (yOfX_mem hx).1
  have hsa := slitA_derivs x
  have hy_eq : ∀ᶠ t in 𝓝 x, lowerY t = √(1 - slitA t) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
    have hsq : lowerY t ^ 2 = 1 - slitA t := by linarith [one_sub_lowerY_sq ht]
    have hyn : 0 ≤ lowerY t := (yOfX_mem ht).1.le
    rw [← hsq]
    exact (Real.sqrt_sq hyn).symm
  have hy_deriv : HasDerivAt lowerY (mtY1 x) x := by
    have hs := ((hasDerivAt_const x (1 : ℝ)).sub hsa.1).sqrt
      (show (1 : ℝ) - slitA x ≠ 0 by linarith [one_sub_lowerY_sq hx, sq_pos_of_pos hy0])
    refine (hs.congr_of_eventuallyEq hy_eq).congr_deriv ?_
    unfold mtY1 mtA1
    have hsq : (1 : ℝ) - slitA x = lowerY x ^ 2 := by linarith [one_sub_lowerY_sq hx]
    simp only [Pi.sub_apply, hsq, Real.sqrt_sq hy0.le]; ring
  have hD_re : (mtD ε x).re = slitA x + ε := by unfold mtD; simp
  have hD_ne : mtD ε x ≠ 0 := by intro hz; rw [hz, Complex.zero_re] at hD_re; linarith
  have hD_deriv : HasDerivAt (mtD ε) (mtD1 ε x) x := by
    have h1 := ((hsa.1.add_const ε).ofReal_comp)
    have h2 := ((hy_deriv.const_mul ε).ofReal_comp).const_mul Complex.I
    exact (h1.add h2).congr_deriv (by simp only [mtD1, mtA1, mtY1])
  have hq : HasDerivAt (mtQ ε) (mtQ1 ε x) x := by
    have hd := (hsa.1.ofReal_comp).div hD_deriv hD_ne
    refine hd.congr_deriv ?_
    simp only [mtQ1, mtD, mtD1, mtN1, mtA1, mtY1]; push_cast; ring
  have hy1_deriv : HasDerivAt mtY1 (mtY2 x) x := by
    have ha1_d : HasDerivAt mtA1 (mtA2 x) x := hsa.2.1
    have hnum_d : HasDerivAt (fun t => -mtA1 t) (-mtA2 x) x := ha1_d.neg
    have hden_d : HasDerivAt (fun t => 2 * lowerY t) (2 * mtY1 x) x := hy_deriv.const_mul 2
    have hd := hnum_d.div hden_d (mul_ne_zero two_ne_zero hy0.ne')
    refine (hd.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    simp only [mtY2, mtY1, mtA1, mtA2]; field_simp [hy0.ne']; ring
  have hN1_deriv : HasDerivAt mtN1 (mtN2 x) x := by
    have hp1 := (hsa.2.1.ofReal_comp).mul ((hy_deriv.ofReal_comp.const_mul Complex.I).const_add 1)
    have hp2 := ((hsa.1.mul hy1_deriv).ofReal_comp).const_mul Complex.I
    refine (hp1.sub hp2).congr_deriv ?_
    simp only [mtN2, mtA1, mtA2, mtY1, mtY2]; push_cast; ring
  have hq1 : HasDerivAt (mtQ1 ε) (mtQ2 ε x) x := by
    have hd := (hN1_deriv.const_mul (ε : ℂ)).div (hD_deriv.pow 2) (pow_ne_zero 2 hD_ne)
    refine hd.congr_deriv ?_
    simp only [Pi.pow_apply, mtQ2]; field_simp [hD_ne]; ring
  refine ⟨?_, ?_⟩
  · exact ((hq.pow 2).const_mul (((1 + ε : ℝ) : ℂ) ^ 2)).congr_deriv (by unfold mtM1x; ring)
  · have hm1_eq : mtM1x ε = fun t => ((1 + ε : ℝ) : ℂ) ^ 2 * (2 * (mtQ ε t * mtQ1 ε t)) := by
      ext t; unfold mtM1x; ring
    rw [hm1_eq]
    exact (((hq.mul hq1).const_mul 2).const_mul (((1 + ε : ℝ) : ℂ) ^ 2)).congr_deriv (by unfold mtM2x; ring)

private lemma mtSq_continuousOn {v₀ ε : ℝ} (hv₀ : 0 < v₀) (_hε : 0 < ε) :
    ContinuousOn (fun v => mtM2x ε (edgeF v) * ((edgeF' v ^ 2 : ℝ) : ℂ) +
      mtM1x ε (edgeF v) * (edgeF'' v : ℂ)) (Ici v₀) := by
  have hx₀ : xiStar < edgeF v₀ := (edgeF_ge_of_ge hv₀ le_rfl).1
  have ha_c : Continuous slitA := continuous_iff_continuousAt.mpr fun x => (slitA_derivs x).1.continuousAt
  have ha1_c : Continuous mtA1 := continuous_iff_continuousAt.mpr fun x => (slitA_derivs x).2.1.continuousAt
  have hF_c : Continuous edgeF := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF v).continuousAt
  have hF'_c : Continuous edgeF' := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF' v).continuousAt
  have hF''_c : Continuous edgeF'' := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF'' v).continuousAt
  have hsh_c : Continuous (fun t : ℝ => Real.sinh (π * t)) := Real.continuous_sinh.comp (continuous_const.mul continuous_id)
  have hch_c : Continuous (fun t : ℝ => Real.cosh (π * t)) := Real.continuous_cosh.comp (continuous_const.mul continuous_id)
  have hden_c : Continuous (fun t : ℝ => Real.cosh (π * t) + √2) := hch_c.add continuous_const
  have hden_ne : ∀ t : ℝ, Real.cosh (π * t) + √2 ≠ 0 := fun t => by have := Real.cosh_pos (π * t); positivity
  have ha2_c : Continuous mtA2 :=
    ((continuous_const.mul (((continuous_const.mul (hsh_c.pow 2)).div (hden_c.pow 2) (fun t => pow_ne_zero 2 (hden_ne t))).sub
      (hch_c.div hden_c hden_ne)))).mul ha_c
  have hy_c : ContinuousOn lowerY (Ioi xiStar) := fun x hx => by
    have hc_sq : ContinuousAt (fun t : ℝ => √(1 - slitA t)) x :=
      ((continuousAt_const.sub ha_c.continuousAt) : ContinuousAt (fun t : ℝ => 1 - slitA t) x).sqrt
    have hy_eq : lowerY =ᶠ[𝓝 x] fun t : ℝ => √(1 - slitA t) := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
      have hsq : lowerY t ^ 2 = 1 - slitA t := by linarith [one_sub_lowerY_sq ht]
      have hyn : 0 ≤ lowerY t := (yOfX_mem ht).1.le
      rw [← hsq]
      exact (Real.sqrt_sq hyn).symm
    exact (hc_sq.congr_of_eventuallyEq hy_eq).continuousWithinAt
  have hD_c : ContinuousOn (mtD ε) (Ioi xiStar) :=
    ((Complex.continuous_ofReal.comp_continuousOn (ha_c.continuousOn.add continuousOn_const)).add
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hy_c))))
  have hy1_c : ContinuousOn mtY1 (Ioi xiStar) :=
    ha1_c.continuousOn.neg.div (continuousOn_const.mul hy_c)
      (fun x hx => mul_ne_zero two_ne_zero (yOfX_mem hx).1.ne')
  have hy2_c : ContinuousOn mtY2 (Ioi xiStar) :=
    ((ha2_c.continuousOn.neg.div (continuousOn_const.mul hy_c)
        (fun x hx => mul_ne_zero two_ne_zero (yOfX_mem hx).1.ne')).sub
      ((ha1_c.continuousOn.pow 2).div (continuousOn_const.mul (hy_c.pow 3))
        (fun x hx => mul_ne_zero (by norm_num) (pow_ne_zero 3 (yOfX_mem hx).1.ne'))))
  have hD_ne : ∀ x ∈ Ioi xiStar, mtD ε x ≠ 0 := fun x _ hz => by
    have hre : (mtD ε x).re = slitA x + ε := by unfold mtD; simp
    rw [hz, Complex.zero_re] at hre; linarith [slitA_pos x]
  have hq_c : ContinuousOn (mtQ ε) (Ioi xiStar) := (Complex.continuous_ofReal.comp ha_c).continuousOn.div hD_c hD_ne
  have hD1_c : ContinuousOn (mtD1 ε) (Ioi xiStar) :=
    (Complex.continuous_ofReal.comp ha1_c).continuousOn.add
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hy1_c)))
  have hN1_c : ContinuousOn mtN1 (Ioi xiStar) :=
    ((Complex.continuous_ofReal.comp ha1_c).continuousOn.mul
      (continuousOn_const.add (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hy_c)))).sub
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (ha_c.continuousOn.mul hy1_c)))
  have hN2_c : ContinuousOn mtN2 (Ioi xiStar) :=
    ((Complex.continuous_ofReal.comp ha2_c).continuousOn.mul
      (continuousOn_const.add (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hy_c)))).sub
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (ha_c.continuousOn.mul hy2_c)))
  have hq1_c : ContinuousOn (mtQ1 ε) (Ioi xiStar) :=
    (continuousOn_const.mul hN1_c).div (hD_c.pow 2) (fun x hx => pow_ne_zero 2 (hD_ne x hx))
  have hq2_c : ContinuousOn (mtQ2 ε) (Ioi xiStar) :=
    (continuousOn_const.mul ((hN2_c.mul hD_c).sub ((continuousOn_const.mul hN1_c).mul hD1_c))).div
      (hD_c.pow 3) (fun x hx => pow_ne_zero 3 (hD_ne x hx))
  have hM1_c : ContinuousOn (mtM1x ε) (Ioi xiStar) :=
    continuousOn_const.mul ((continuousOn_const.mul hq_c).mul hq1_c)
  have hM2_c : ContinuousOn (mtM2x ε) (Ioi xiStar) :=
    continuousOn_const.mul (continuousOn_const.mul ((hq1_c.pow 2).add (hq_c.mul hq2_c)))
  have hmaps : MapsTo edgeF (Ici v₀) (Ioi xiStar) := fun v hv =>
    hx₀.trans_le (edgeF_ge_of_ge hv₀ hv).2
  exact ((hM2_c.comp hF_c.continuousOn hmaps).mul (Complex.continuous_ofReal.comp (hF'_c.pow 2)).continuousOn).add
    ((hM1_c.comp hF_c.continuousOn hmaps).mul (Complex.continuous_ofReal.comp hF''_c).continuousOn)

private lemma mtSq_pointwise_bounds {v₀ ε : ℝ} (hv₀ : 0 < v₀) (hε : ε ∈ Ioo 0 (1 / 2)) {v : ℝ} (hv : v ∈ Ici v₀) :
    let x₀ := edgeF v₀
    let CN1 := 2 * π + π / (2 * lowerY x₀)
    let CN2 := 6 * π ^ 2 + 3 * π ^ 2 / (2 * lowerY x₀) + π ^ 2 / (4 * lowerY x₀ ^ 3)
    let CD1 := π + π / (4 * lowerY x₀)
    let CM1 := (9 / 2 : ℝ) * CN1
    let CM2 := (9 / 2 : ℝ) * (CN1 ^ 2 / 4 + CN2 + 2 * CN1 * CD1)
    let w := ε * slitA (edgeF v) / (slitA (edgeF v) + ε) ^ 2
    ‖lowerMt ε (Complex.I * (lowerY (edgeF v) : ℂ)) ^ 2‖ ≤ 9 / 4 ∧
    ‖mtM1x ε (edgeF v)‖ ≤ CM1 * w ∧
    ‖mtM2x ε (edgeF v)‖ ≤ CM2 * w := by
  intro x₀ CN1 CN2 CD1 CM1 CM2 w
  have hε0 : 0 < ε := hε.1
  have hε1 : ε < 1 / 2 := hε.2
  have hx₀ : xiStar < x₀ := (edgeF_ge_of_ge hv₀ le_rfl).1
  set x := edgeF v
  have hx : x₀ ≤ x := (edgeF_ge_of_ge hv₀ hv).2
  have hx_gt : xiStar < x := hx₀.trans_le hx
  have hx_nn : 0 ≤ x := (xiStar_pos.trans hx_gt).le
  have ha0 : 0 < slitA x := slitA_pos x
  have ha1 : slitA x < 1 := slitA_lt_one hx_gt
  have hy_bds := lowerY_mono_on hx₀ hx
  have hy_pos : 0 < lowerY x := hy_bds.1.trans_le hy_bds.2.1
  have hy0_le : lowerY x₀ ≤ lowerY x := hy_bds.2.1
  have hy0_pos : 0 < lowerY x₀ := hy_bds.1
  have hD_lb : slitA x + ε ≤ ‖mtD ε x‖ := by
    have hre : (mtD ε x).re = slitA x + ε := by unfold mtD; simp
    calc slitA x + ε ≤ |(mtD ε x).re| := by rw [hre]; exact le_abs_self _
      _ ≤ ‖mtD ε x‖ := Complex.abs_re_le_norm _
  have hD_pos : 0 < ‖mtD ε x‖ := (add_pos ha0 hε0).trans_le hD_lb
  have hsa_bd := (slitA_derivs x).2.2 hx_nn
  have ha1_bd : |mtA1 x| ≤ π * slitA x := hsa_bd.1
  have ha2_bd : |mtA2 x| ≤ 3 * π ^ 2 * slitA x := hsa_bd.2
  have hy1_bd : |mtY1 x| ≤ (π / (2 * lowerY x₀)) * slitA x := by
    unfold mtY1
    rw [abs_div, abs_neg, abs_of_pos (mul_pos two_pos hy_pos)]
    calc |mtA1 x| / (2 * lowerY x) ≤ (π * slitA x) / (2 * lowerY x₀) :=
          div_le_div₀ (by positivity) ha1_bd (by positivity) (by gcongr)
      _ = (π / (2 * lowerY x₀)) * slitA x := by ring
  have hy2_bd : |mtY2 x| ≤ (3 * π ^ 2 / (2 * lowerY x₀) + π ^ 2 / (4 * lowerY x₀ ^ 3)) * slitA x := by
    unfold mtY2
    refine (abs_sub _ _).trans ?_
    have h1 : |(-mtA2 x) / (2 * lowerY x)| ≤ (3 * π ^ 2 / (2 * lowerY x₀)) * slitA x := by
      rw [abs_div, abs_neg, abs_of_pos (mul_pos two_pos hy_pos)]
      calc |mtA2 x| / (2 * lowerY x) ≤ (3 * π ^ 2 * slitA x) / (2 * lowerY x₀) :=
            div_le_div₀ (by positivity) ha2_bd (by positivity) (by gcongr)
        _ = (3 * π ^ 2 / (2 * lowerY x₀)) * slitA x := by ring
    have h2 : |mtA1 x ^ 2 / (4 * lowerY x ^ 3)| ≤ (π ^ 2 / (4 * lowerY x₀ ^ 3)) * slitA x := by
      rw [abs_div, abs_pow, abs_of_pos (mul_pos (by norm_num) (pow_pos hy_pos 3))]
      have ha1sq : |mtA1 x| ^ 2 ≤ (π * slitA x) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ha1_bd 2
      have hsq_le : slitA x ^ 2 ≤ slitA x := by nlinarith [ha0, ha1]
      calc |mtA1 x| ^ 2 / (4 * lowerY x ^ 3) ≤ (π * slitA x) ^ 2 / (4 * lowerY x₀ ^ 3) :=
            div_le_div₀ (by positivity) ha1sq (by positivity) (by gcongr)
        _ = (π ^ 2 / (4 * lowerY x₀ ^ 3)) * slitA x ^ 2 := by ring
        _ ≤ (π ^ 2 / (4 * lowerY x₀ ^ 3)) * slitA x := by gcongr
    linarith
  have h1Iy : ‖(1 : ℂ) + Complex.I * (lowerY x : ℂ)‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy_pos]
    linarith [hy_bds.2.2]
  have hN1 : ‖mtN1 x‖ ≤ CN1 * slitA x := by
    unfold mtN1
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos ha0]
    calc |mtA1 x| * ‖(1 : ℂ) + Complex.I * (lowerY x : ℂ)‖ + slitA x * |mtY1 x|
        ≤ (π * slitA x) * 2 + slitA x * ((π / (2 * lowerY x₀)) * slitA x) :=
          add_le_add (mul_le_mul ha1_bd h1Iy (norm_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_left hy1_bd ha0.le)
      _ ≤ (π * slitA x) * 2 + slitA x * ((π / (2 * lowerY x₀)) * 1) := by gcongr
      _ = CN1 * slitA x := by dsimp [CN1]; ring
  have hN2 : ‖mtN2 x‖ ≤ CN2 * slitA x := by
    unfold mtN2
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos ha0]
    calc |mtA2 x| * ‖(1 : ℂ) + Complex.I * (lowerY x : ℂ)‖ + slitA x * |mtY2 x|
        ≤ (3 * π ^ 2 * slitA x) * 2 + slitA x * ((3 * π ^ 2 / (2 * lowerY x₀) + π ^ 2 / (4 * lowerY x₀ ^ 3)) * slitA x) :=
          add_le_add (mul_le_mul ha2_bd h1Iy (norm_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_left hy2_bd ha0.le)
      _ ≤ (3 * π ^ 2 * slitA x) * 2 + slitA x * ((3 * π ^ 2 / (2 * lowerY x₀) + π ^ 2 / (4 * lowerY x₀ ^ 3)) * 1) := by gcongr
      _ = CN2 * slitA x := by dsimp [CN2]; ring
  have hD1 : ‖mtD1 ε x‖ ≤ CD1 * slitA x := by
    unfold mtD1
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos hε0]
    calc |mtA1 x| + ε * |mtY1 x|
        ≤ π * slitA x + (1 / 2 : ℝ) * ((π / (2 * lowerY x₀)) * slitA x) := by gcongr
      _ = CD1 * slitA x := by dsimp [CD1]; ring
  have hq_bd : ‖mtQ ε x‖ ≤ 1 := by
    unfold mtQ
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
    exact (div_le_one hD_pos).mpr (by linarith)
  have hw_nn : 0 ≤ w := by positivity
  have hw_le4 : w ≤ 1 / 4 := by
    dsimp [w]; rw [div_le_iff₀ (pow_pos (add_pos ha0 hε0) 2)]
    nlinarith [sq_nonneg (slitA x - ε)]
  have hq1_bd : ‖mtQ1 ε x‖ ≤ CN1 * w := by
    unfold mtQ1
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
    calc ε * ‖mtN1 x‖ / ‖mtD ε x‖ ^ 2
        ≤ ε * (CN1 * slitA x) / (slitA x + ε) ^ 2 := by gcongr
      _ = CN1 * w := by dsimp [w]; ring
  have hq2_bd : ‖mtQ2 ε x‖ ≤ (CN2 + 2 * CN1 * CD1) * w := by
    have hsplit : mtQ2 ε x = (ε : ℂ) * mtN2 x / mtD ε x ^ 2 - 2 * (ε : ℂ) * mtN1 x * mtD1 ε x / mtD ε x ^ 3 := by
      unfold mtQ2
      have hDne : mtD ε x ≠ 0 := norm_ne_zero_iff.mp hD_pos.ne'
      field_simp [hDne]
    rw [hsplit]
    refine (norm_sub_le _ _).trans ?_
    have ht1 : ‖(ε : ℂ) * mtN2 x / mtD ε x ^ 2‖ ≤ CN2 * w := by
      rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
      calc ε * ‖mtN2 x‖ / ‖mtD ε x‖ ^ 2 ≤ ε * (CN2 * slitA x) / (slitA x + ε) ^ 2 := by gcongr
        _ = CN2 * w := by dsimp [w]; ring
    have ht2 : ‖2 * (ε : ℂ) * mtN1 x * mtD1 ε x / mtD ε x ^ 3‖ ≤ (2 * CN1 * CD1) * w := by
      rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow, show ‖(2 : ℂ)‖ = 2 by norm_num,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
      have h3 : (slitA x + ε) ^ 3 ≤ ‖mtD ε x‖ ^ 3 := pow_le_pow_left₀ (by positivity) hD_lb 3
      calc 2 * ε * ‖mtN1 x‖ * ‖mtD1 ε x‖ / ‖mtD ε x‖ ^ 3
          ≤ 2 * ε * (CN1 * slitA x) * (CD1 * slitA x) / (slitA x + ε) ^ 3 :=
            div_le_div₀ (by positivity)
              (mul_le_mul (mul_le_mul_of_nonneg_left hN1 (by positivity)) hD1 (norm_nonneg _) (by positivity))
              (pow_pos (add_pos ha0 hε0) 3) h3
        _ = (2 * CN1 * CD1) * (ε * slitA x / (slitA x + ε) ^ 2) * (slitA x / (slitA x + ε)) := by
            field_simp [(add_pos ha0 hε0).ne']
        _ ≤ (2 * CN1 * CD1) * (ε * slitA x / (slitA x + ε) ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left ((div_le_one (add_pos ha0 hε0)).mpr (by linarith)) (by positivity)
        _ = (2 * CN1 * CD1) * w := by dsimp [w, x]; ring
    linarith
  have h1e_sq : ‖((1 + ε : ℝ) : ℂ) ^ 2‖ ≤ 9 / 4 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    nlinarith
  have hF_eq : lowerMt ε (Complex.I * (lowerY x : ℂ)) ^ 2 = ((1 + ε : ℝ) : ℂ) ^ 2 * mtQ ε x ^ 2 := by
    have h1y : 1 + (Complex.I * (lowerY x : ℂ)) ^ 2 = (slitA x : ℂ) := by
      calc 1 + (Complex.I * (lowerY x : ℂ)) ^ 2
          = ((1 - lowerY x ^ 2 : ℝ) : ℂ) := by push_cast; rw [mul_pow, Complex.I_sq]; ring
        _ = (slitA x : ℂ) := by rw [one_sub_lowerY_sq hx_gt]
    unfold lowerMt mtQ mtD
    rw [h1y]; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hF_eq, norm_mul, norm_pow (mtQ ε x) 2]
    calc ‖((1 + ε : ℝ) : ℂ) ^ 2‖ * ‖mtQ ε x‖ ^ 2 ≤ (9 / 4) * 1 :=
          mul_le_mul h1e_sq (pow_le_one₀ (norm_nonneg _) hq_bd) (sq_nonneg _) (by positivity)
      _ = 9 / 4 := by ring
  · unfold mtM1x
    rw [norm_mul, norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    calc ‖((1 + ε : ℝ) : ℂ) ^ 2‖ * (2 * ‖mtQ ε x‖ * ‖mtQ1 ε x‖)
        ≤ (9 / 4) * (2 * 1 * (CN1 * w)) := by gcongr
      _ = CM1 * w := by dsimp [CM1]; ring
  · unfold mtM2x
    rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hinner : ‖mtQ1 ε x ^ 2 + mtQ ε x * mtQ2 ε x‖ ≤ (CN1 ^ 2 / 4 + CN2 + 2 * CN1 * CD1) * w := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_pow, norm_mul]
      have hq1_sq : ‖mtQ1 ε x‖ ^ 2 ≤ (CN1 ^ 2 / 4) * w := by
        calc ‖mtQ1 ε x‖ ^ 2 ≤ (CN1 * w) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hq1_bd 2
          _ = CN1 ^ 2 * w * w := by ring
          _ ≤ CN1 ^ 2 * (1 / 4) * w := by gcongr
          _ = (CN1 ^ 2 / 4) * w := by ring
      have hq2_m : ‖mtQ ε x‖ * ‖mtQ2 ε x‖ ≤ (CN2 + 2 * CN1 * CD1) * w := by
        calc ‖mtQ ε x‖ * ‖mtQ2 ε x‖ ≤ 1 * ((CN2 + 2 * CN1 * CD1) * w) := by gcongr
          _ = (CN2 + 2 * CN1 * CD1) * w := by ring
      linarith
    calc ‖((1 + ε : ℝ) : ℂ) ^ 2‖ * (2 * ‖mtQ1 ε x ^ 2 + mtQ ε x * mtQ2 ε x‖)
        ≤ (9 / 4) * (2 * ((CN1 ^ 2 / 4 + CN2 + 2 * CN1 * CD1) * w)) := by gcongr
      _ = CM2 * w := by dsimp [CM2]; ring

/-- Uniform `ε`-bounds (`0 < ε < 1/2`) for `(lowerMt ε (I * lowerY (edgeF v)))^2` on `[v₀, ∞)`. -/
lemma mtSq_oscAmpBound {v₀ : ℝ} (hv₀ : 0 < v₀) :
    ∃ K0 K1 K2 L1 L2 : ℝ, 0 ≤ K0 ∧ 0 ≤ K1 ∧ 0 ≤ K2 ∧ 0 ≤ L1 ∧ 0 ≤ L2 ∧
      ∀ {ε : ℝ}, ε ∈ Ioo 0 (1 / 2) →
        ∃ F1 F2 : ℝ → ℂ,
          ∃ h : OscAmpBound v₀ (fun v => lowerMt ε (Complex.I * (lowerY (edgeF v) : ℂ)) ^ 2) F1 F2,
            h.HasConsts K0 K1 K2 L1 L2 := by
  let x₀ := edgeF v₀
  have hx₀ : xiStar < x₀ := (edgeF_ge_of_ge hv₀ le_rfl).1
  have hy₀ : 0 < lowerY x₀ := (yOfX_mem hx₀).1
  have hF'₀ : 0 < edgeF' v₀ := edgeF'_pos hv₀
  let csh := Real.sinh (π * x₀) / (Real.cosh (π * x₀) + √2)
  have hcsh : 0 < csh := by
    have := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos (xiStar_pos.trans hx₀))
    have := Real.cosh_pos (π * x₀)
    positivity
  let CN1 : ℝ := 2 * π + π / (2 * lowerY x₀)
  let CN2 : ℝ := 6 * π ^ 2 + 3 * π ^ 2 / (2 * lowerY x₀) + π ^ 2 / (4 * lowerY x₀ ^ 3)
  let CD1 : ℝ := π + π / (4 * lowerY x₀)
  let CM1 : ℝ := (9 / 2 : ℝ) * CN1
  let CM2 : ℝ := (9 / 2 : ℝ) * (CN1 ^ 2 / 4 + CN2 + 2 * CN1 * CD1)
  let Ctot2 : ℝ := CM2 + CM1 * (8 * π / edgeF' v₀)
  refine ⟨9 / 4, CM1 / 4, Ctot2 / 4, CM1 / (π * csh), Ctot2 / (π * csh),
    by positivity, by positivity, by positivity, by positivity, by positivity, ?_⟩
  intro ε hε
  have hε0 : 0 < ε := hε.1
  let F1 : ℝ → ℂ := fun v => mtM1x ε (edgeF v) * (edgeF' v : ℂ)
  let F2 : ℝ → ℂ := fun v => mtM2x ε (edgeF v) * ((edgeF' v ^ 2 : ℝ) : ℂ) + mtM1x ε (edgeF v) * (edgeF'' v : ℂ)
  have hwt := mtWeight_integrableOn hv₀ hε0
  let wt : ℝ → ℝ := fun v => ε * slitA (edgeF v) / (slitA (edgeF v) + ε) ^ 2 * edgeF' v
  have hF1_bd : ∀ v ∈ Ici v₀, ‖F1 v‖ ≤ CM1 * wt v := fun v hv => by
    have hF'nn : 0 ≤ edgeF' v := (edgeF'_pos (hv₀.trans_le hv)).le
    dsimp [F1]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hF'nn]
    calc ‖mtM1x ε (edgeF v)‖ * edgeF' v
        ≤ (CM1 * (ε * slitA (edgeF v) / (slitA (edgeF v) + ε) ^ 2)) * edgeF' v := by
          gcongr; exact (mtSq_pointwise_bounds hv₀ hε hv).2.1
      _ = CM1 * wt v := by dsimp [wt]; ring
  have hF2_bd : ∀ v ∈ Ici v₀, ‖F2 v‖ ≤ Ctot2 * wt v := fun v hv => by
    have hF' := edgeF'_v_bounds hv₀ hv
    have hF'' := edgeF''_bound (hv₀.le.trans hv)
    have hF''_le : edgeF'' v ≤ (8 * π / edgeF' v₀) * edgeF' v := by
      have h8 : edgeF'' v ≤ 8 * π := by
        have hex1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hv₀.le.trans hv] : -(2 * π * v) ≤ 0)
        nlinarith [hF''.2, Real.pi_pos]
      calc edgeF'' v ≤ 8 * π := h8
        _ = (8 * π / edgeF' v₀) * edgeF' v₀ := by field_simp [hF'₀.ne']
        _ ≤ (8 * π / edgeF' v₀) * edgeF' v := by gcongr; exact hF'.1
    have hF'sq : edgeF' v ^ 2 ≤ edgeF' v := by nlinarith [hF'.1, hF'.2, hF'₀]
    dsimp [F2]; refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _), abs_of_pos hF''.1]
    have ha_pos : 0 < slitA (edgeF v) := slitA_pos _
    have hCM1_nn : 0 ≤ CM1 := by positivity
    have hCM2_nn : 0 ≤ CM2 := by positivity
    have hw_nn : 0 ≤ ε * slitA (edgeF v) / (slitA (edgeF v) + ε) ^ 2 := by positivity
    have ht1 : ‖mtM2x ε (edgeF v)‖ * edgeF' v ^ 2 ≤ CM2 * wt v := by
      calc ‖mtM2x ε (edgeF v)‖ * edgeF' v ^ 2
          ≤ (CM2 * (ε * slitA (edgeF v) / (slitA (edgeF v) + ε) ^ 2)) * edgeF' v :=
            mul_le_mul (mtSq_pointwise_bounds hv₀ hε hv).2.2 hF'sq (sq_nonneg _) (mul_nonneg hCM2_nn hw_nn)
        _ = CM2 * wt v := by dsimp [wt]; ring
    have ht2 : ‖mtM1x ε (edgeF v)‖ * edgeF'' v ≤ (CM1 * (8 * π / edgeF' v₀)) * wt v := by
      calc ‖mtM1x ε (edgeF v)‖ * edgeF'' v
          ≤ (CM1 * (ε * slitA (edgeF v) / (slitA (edgeF v) + ε) ^ 2)) * ((8 * π / edgeF' v₀) * edgeF' v) :=
            mul_le_mul (mtSq_pointwise_bounds hv₀ hε hv).2.1 hF''_le hF''.1.le (mul_nonneg hCM1_nn hw_nn)
        _ = (CM1 * (8 * π / edgeF' v₀)) * wt v := by dsimp [wt]; ring
    dsimp [Ctot2]; linarith
  have hwt_le4 : ∀ v ∈ Ici v₀, wt v ≤ 1 / 4 := fun v hv => by
    have hF' := edgeF'_v_bounds hv₀ hv
    have ha0 : 0 < slitA (edgeF v) := slitA_pos _
    have hw4 : ε * slitA (edgeF v) / (slitA (edgeF v) + ε) ^ 2 ≤ 1 / 4 := by
      rw [div_le_iff₀ (pow_pos (add_pos ha0 hε0) 2)]
      nlinarith [sq_nonneg (slitA (edgeF v) - ε)]
    dsimp [wt]
    calc (ε * slitA (edgeF v) / (slitA (edgeF v) + ε) ^ 2) * edgeF' v ≤ (1 / 4) * 1 :=
          mul_le_mul hw4 hF'.2.le (edgeF'_pos (hv₀.trans_le hv)).le (by positivity)
      _ = 1 / 4 := by ring
  have hhd1 : ∀ v ∈ Ici v₀, HasDerivAt (fun t => lowerMt ε (Complex.I * (lowerY (edgeF t) : ℂ)) ^ 2) (F1 v) v := by
    intro v hv
    have hx_gt : xiStar < edgeF v := hx₀.trans_le (edgeF_ge_of_ge hv₀ hv).2
    have heq : ∀ᶠ t in 𝓝 v,
        lowerMt ε (Complex.I * (lowerY (edgeF t) : ℂ)) ^ 2 = ((1 + ε : ℝ) : ℂ) ^ 2 * mtQ ε (edgeF t) ^ 2 := by
      have hF_c : ContinuousAt edgeF v := (hasDerivAt_edgeF v).continuousAt
      filter_upwards [hF_c.preimage_mem_nhds (isOpen_Ioi.mem_nhds hx_gt)] with t ht
      have h1y : 1 + (Complex.I * (lowerY (edgeF t) : ℂ)) ^ 2 = (slitA (edgeF t) : ℂ) := by
        calc 1 + (Complex.I * (lowerY (edgeF t) : ℂ)) ^ 2
            = ((1 - lowerY (edgeF t) ^ 2 : ℝ) : ℂ) := by push_cast; rw [mul_pow, Complex.I_sq]; ring
          _ = (slitA (edgeF t) : ℂ) := by rw [one_sub_lowerY_sq ht]
      unfold lowerMt mtQ mtD; rw [h1y]; push_cast; ring
    have hd : HasDerivAt (fun t => ((1 + ε : ℝ) : ℂ) ^ 2 * mtQ ε (edgeF t) ^ 2) (F1 v) v :=
      ((mtSq_x_derivs hε0 hx_gt).1.scomp v (hasDerivAt_edgeF v)).congr_deriv
        (by rw [Complex.real_smul]; dsimp [F1]; ring)
    exact hd.congr_of_eventuallyEq heq
  have hhd2 : ∀ v ∈ Ici v₀, HasDerivAt F1 (F2 v) v := fun v hv => by
    have hx_gt : xiStar < edgeF v := hx₀.trans_le (edgeF_ge_of_ge hv₀ hv).2
    have hM1 : HasDerivAt (fun t => mtM1x ε (edgeF t)) (mtM2x ε (edgeF v) * (edgeF' v : ℂ)) v :=
      ((mtSq_x_derivs hε0 hx_gt).2.scomp v (hasDerivAt_edgeF v)).congr_deriv
        (by rw [Complex.real_smul]; ring)
    have hF' : HasDerivAt (fun t => (edgeF' t : ℂ)) (edgeF'' v : ℂ) v := (hasDerivAt_edgeF' v).ofReal_comp
    refine (hM1.mul hF').congr_deriv ?_
    dsimp [F2]; push_cast; ring
  have hF1_c : ContinuousOn F1 (Ici v₀) := fun v hv => (hhd2 v hv).continuousAt.continuousWithinAt
  have hF2_c : ContinuousOn F2 (Ici v₀) := mtSq_continuousOn hv₀ hε0
  have hi1 : IntegrableOn F1 (Ioi v₀) := by
    refine (hwt.1.const_mul CM1).mono' ((hF1_c.aestronglyMeasurable measurableSet_Ici).mono_set Ioi_subset_Ici_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact hF1_bd v hv.le
  have hi2 : IntegrableOn F2 (Ioi v₀) := by
    refine (hwt.1.const_mul Ctot2).mono' ((hF2_c.aestronglyMeasurable measurableSet_Ici).mono_set Ioi_subset_Ici_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact hF2_bd v hv.le
  refine ⟨F1, F2, {
    hd1 := hhd1
    hd2 := hhd2
    K0 := 9 / 4
    K1 := CM1 / 4
    K2 := Ctot2 / 4
    L1 := CM1 / (π * csh)
    L2 := Ctot2 / (π * csh)
    hK0 := by positivity
    hK1 := by positivity
    hK2 := by positivity
    hL1 := by positivity
    hL2 := by positivity
    b0 := fun v hv => (mtSq_pointwise_bounds hv₀ hε hv).1
    b1 := fun v hv => (hF1_bd v hv).trans (by
      calc CM1 * wt v ≤ CM1 * (1 / 4) := mul_le_mul_of_nonneg_left (hwt_le4 v hv) (by positivity)
        _ = CM1 / 4 := by ring)
    b2 := fun v hv => (hF2_bd v hv).trans (by
      calc Ctot2 * wt v ≤ Ctot2 * (1 / 4) := mul_le_mul_of_nonneg_left (hwt_le4 v hv) (by positivity)
        _ = Ctot2 / 4 := by ring)
    i1 := hi1
    int1 := by
      calc ∫ v in Ioi v₀, ‖F1 v‖ ≤ ∫ v in Ioi v₀, CM1 * wt v :=
            integral_mono_ae hi1.norm (hwt.1.const_mul CM1)
              ((ae_restrict_mem measurableSet_Ioi).mono fun v hv => hF1_bd v hv.le)
        _ = CM1 * ∫ v in Ioi v₀, wt v := integral_const_mul CM1 _
        _ ≤ CM1 * (π * csh)⁻¹ := mul_le_mul_of_nonneg_left hwt.2 (by positivity)
        _ = CM1 / (π * csh) := (div_eq_mul_inv _ _).symm
    i2 := hi2
    int2 := by
      calc ∫ v in Ioi v₀, ‖F2 v‖ ≤ ∫ v in Ioi v₀, Ctot2 * wt v :=
            integral_mono_ae hi2.norm (hwt.1.const_mul Ctot2)
              ((ae_restrict_mem measurableSet_Ioi).mono fun v hv => hF2_bd v hv.le)
        _ = Ctot2 * ∫ v in Ioi v₀, wt v := integral_const_mul Ctot2 _
        _ ≤ Ctot2 * (π * csh)⁻¹ := mul_le_mul_of_nonneg_left hwt.2 (by positivity)
        _ = Ctot2 / (π * csh) := (div_eq_mul_inv _ _).symm
  }, ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩⟩

/-- **`virasoro_geps_deriv`** (`cts:geps-deriv`): for any `v₀ > 0`, `kedgeAmp0 ε` and
`kedgeAmp0Aux ε` satisfy `OscAmpBound` on `[v₀, ∞)` with constants `K0, K1, K2, L1, L2`
independent of `ε ∈ Ioo 0 (1 / 2)`. -/
theorem virasoro_geps_deriv {v₀ : ℝ} (hv₀ : 0 < v₀) :
    (∃ K0 K1 K2 L1 L2 : ℝ, 0 ≤ K0 ∧ 0 ≤ K1 ∧ 0 ≤ K2 ∧ 0 ≤ L1 ∧ 0 ≤ L2 ∧
      ∀ {ε : ℝ}, ε ∈ Ioo 0 (1 / 2) →
        ∃ F1 F2 : ℝ → ℂ, ∃ h : OscAmpBound v₀ (kedgeAmp0 ε) F1 F2,
          h.HasConsts K0 K1 K2 L1 L2) ∧
    (∃ K0 K1 K2 L1 L2 : ℝ, 0 ≤ K0 ∧ 0 ≤ K1 ∧ 0 ≤ K2 ∧ 0 ≤ L1 ∧ 0 ≤ L2 ∧
      ∀ {ε : ℝ}, ε ∈ Ioo 0 (1 / 2) →
        ∃ F1 F2 : ℝ → ℂ, ∃ h : OscAmpBound v₀ (kedgeAmp0Aux ε) F1 F2,
          h.HasConsts K0 K1 K2 L1 L2) := by
  obtain ⟨M0, M1, M2, ML1, ML2, hM0, hM1, hM2, hML1, hML2, hM⟩ := mtSq_oscAmpBound hv₀
  obtain ⟨_, _, ⟨hT⟩⟩ := theta_oscAmpBound hv₀
  obtain ⟨_, _, ⟨hE⟩⟩ := oneSubExp_oscAmpBound hv₀
  obtain ⟨_, _, ⟨hS⟩⟩ := sqrtEdgeF'_oscAmpBound hv₀
  obtain ⟨_, _, ⟨hR⟩⟩ := auxInv_oscAmpBound hv₀
  let hES := (hE.mul hE).mul hS
  let hTES := hT.mul hES
  have hES_eq : ∀ v, (((1 - Real.exp (-(4 * π * edgeF v))) ^ 2 * √(edgeF' v) : ℝ) : ℂ) =
      (((1 - Real.exp (-(4 * π * edgeF v)) : ℝ) : ℂ) *
        ((1 - Real.exp (-(4 * π * edgeF v)) : ℝ) : ℂ)) * (√(edgeF' v) : ℂ) := fun v => by
    push_cast; ring
  let CK0 := M0 * hTES.K0
  let CK1 := M1 * hTES.K0 + M0 * hTES.K1
  let CK2 := M2 * hTES.K0 + 2 * (M1 * hTES.K1) + M0 * hTES.K2
  let CL1 := hTES.K0 * ML1 + M0 * hTES.L1
  let CL2 := hTES.K0 * ML2 + 2 * (M1 * hTES.L1) + M0 * hTES.L2
  have hCK0 : 0 ≤ CK0 := mul_nonneg hM0 hTES.hK0
  have hCK1 : 0 ≤ CK1 := add_nonneg (mul_nonneg hM1 hTES.hK0) (mul_nonneg hM0 hTES.hK1)
  have hCK2 : 0 ≤ CK2 := add_nonneg (add_nonneg (mul_nonneg hM2 hTES.hK0) (by nlinarith [hM1, hTES.hK1]))
    (mul_nonneg hM0 hTES.hK2)
  have hCL1 : 0 ≤ CL1 := add_nonneg (mul_nonneg hTES.hK0 hML1) (mul_nonneg hM0 hTES.hL1)
  have hCL2 : 0 ≤ CL2 := add_nonneg (add_nonneg (mul_nonneg hTES.hK0 hML2) (by nlinarith [hM1, hTES.hL1]))
    (mul_nonneg hM0 hTES.hL2)
  have hpart1 : ∀ {ε : ℝ}, ε ∈ Ioo 0 (1 / 2) →
      ∃ F1 F2 : ℝ → ℂ, ∃ h : OscAmpBound v₀ (kedgeAmp0 ε) F1 F2,
        h.HasConsts CK0 CK1 CK2 CL1 CL2 := by
    intro ε hε
    obtain ⟨_, _, hm, hm0, hm1, hm2, hml1, hml2⟩ := hM hε
    let hprod := hm.mul hTES
    have heq : kedgeAmp0 ε = fun v =>
        (lowerMt ε (Complex.I * (lowerY (edgeF v) : ℂ)) ^ 2) *
          (Complex.exp (Complex.I * (thetaOut (lowerY (edgeF v)) : ℂ)) *
            ((((1 - Real.exp (-(4 * π * edgeF v)) : ℝ) : ℂ) *
              ((1 - Real.exp (-(4 * π * edgeF v)) : ℝ) : ℂ)) * (√(edgeF' v) : ℂ))) := by
      ext v; unfold kedgeAmp0; rw [← hES_eq v]; ring
    rw [heq]
    have := hTES.hK0; have := hTES.hK1; have := hTES.hK2; have := hTES.hL1; have := hTES.hL2
    refine ⟨_, _, hprod, ?_, ?_, ?_, ?_, ?_⟩ <;>
      dsimp [hprod, OscAmpBound.mul, CK0, CK1, CK2, CL1, CL2] <;>
      gcongr
  refine ⟨⟨CK0, CK1, CK2, CL1, CL2, hCK0, hCK1, hCK2, hCL1, hCL2, hpart1⟩, ?_⟩
  let AK0 := CK0 * hR.K0
  let AK1 := CK1 * hR.K0 + CK0 * hR.K1
  let AK2 := CK2 * hR.K0 + 2 * (CK1 * hR.K1) + CK0 * hR.K2
  let AL1 := hR.K0 * CL1 + CK0 * hR.L1
  let AL2 := hR.K0 * CL2 + 2 * (CK1 * hR.L1) + CK0 * hR.L2
  refine ⟨AK0, AK1, AK2, AL1, AL2,
    mul_nonneg hCK0 hR.hK0,
    add_nonneg (mul_nonneg hCK1 hR.hK0) (mul_nonneg hCK0 hR.hK1),
    add_nonneg (add_nonneg (mul_nonneg hCK2 hR.hK0) (by nlinarith [hCK1, hR.hK1])) (mul_nonneg hCK0 hR.hK2),
    add_nonneg (mul_nonneg hR.hK0 hCL1) (mul_nonneg hCK0 hR.hL1),
    add_nonneg (add_nonneg (mul_nonneg hR.hK0 hCL2) (by nlinarith [hCK1, hR.hL1])) (mul_nonneg hCK0 hR.hL2), ?_⟩
  intro ε hε
  obtain ⟨_, _, hk, hk0, hk1, hk2, hkl1, hkl2⟩ := hpart1 hε
  let haux := hk.mul hR
  have := hR.hK0; have := hR.hK1; have := hR.hK2; have := hR.hL1; have := hR.hL2
  refine ⟨_, _, haux, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp [haux, OscAmpBound.mul, AK0, AK1, AK2, AL1, AL2] <;>
    gcongr

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.virasoro_geps_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoro_geps_deriv

end
end FormalResearch.ModularBootstrap.FiveTerm
