module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerKedgeAmpBase
public import FormalResearch.SignUncertainty.CtOscIBP

/-!
# Tail Double Integration by Parts (`ibp_twice_ae` and `phiDual_tail_ibp2`)

Provides:
* `ibp_twice_ae`: `CtOsc.ibp_twice` assuming `IntervalIntegrable B2 volume a b` instead of
  `ContinuousOn B2 (Icc a b)`, so `deriv (deriv thetaOutX)` from `outerS2` applies directly.
* `phiDual_tail_ibp2`: double integration by parts on `[v₁, ∞)` for `v₁ ≥ v₀ > 0` and
  `x' < edgeF v₁`, with exact `CtOsc.ibpH` boundary terms at `v₁` and explicit `O(c'⁻²)` tail.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Saddle
open FormalResearch.SignUncertainty
open FormalResearch.SignUncertainty.CtOsc

noncomputable section

/-- Two integrations by parts on `[a, b]` assuming only `IntervalIntegrable B2 volume a b`
instead of `ContinuousOn B2 (Icc a b)`. -/
lemma ibp_twice_ae {a b lam : ℝ} (hab : a ≤ b) (hlam : lam ≠ 0)
    {ϕ ϕ1 ϕ2 ϕ3 : ℝ → ℝ} {B B1 B2 : ℝ → ℂ}
    (hϕ : ∀ x ∈ Icc a b, HasDerivAt ϕ (ϕ1 x) x) (hϕ1 : ∀ x ∈ Icc a b, HasDerivAt ϕ1 (ϕ2 x) x)
    (hϕ2 : ∀ x ∈ Icc a b, HasDerivAt ϕ2 (ϕ3 x) x) (hne : ∀ x ∈ Icc a b, ϕ1 x ≠ 0)
    (hB : ∀ x ∈ Icc a b, HasDerivAt B (B1 x) x) (hB1 : ∀ x ∈ Icc a b, HasDerivAt B1 (B2 x) x)
    (hi2 : IntervalIntegrable B2 volume a b) (hc3 : ContinuousOn ϕ3 (Icc a b)) :
    ∫ x in a..b, B x * Complex.exp (Complex.I * lam * (ϕ x : ℂ)) =
      (1 / (Complex.I * lam)) * (B b / (ϕ1 b : ℂ) * Complex.exp (Complex.I * lam * (ϕ b : ℂ)) -
          B a / (ϕ1 a : ℂ) * Complex.exp (Complex.I * lam * (ϕ a : ℂ))) -
        (1 / (Complex.I * lam)) ^ 2 * (ibpH B B1 ϕ1 ϕ2 b / (ϕ1 b : ℂ) * Complex.exp (Complex.I * lam * (ϕ b : ℂ)) -
          ibpH B B1 ϕ1 ϕ2 a / (ϕ1 a : ℂ) * Complex.exp (Complex.I * lam * (ϕ a : ℂ))) +
        (1 / (Complex.I * lam)) ^ 2 * ∫ x in a..b, ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 x * Complex.exp (Complex.I * lam * (ϕ x : ℂ)) := by
  have hcB1 : ContinuousOn B1 (Icc a b) := fun x hx => (hB1 x hx).continuousAt.continuousWithinAt
  have hcB : ContinuousOn B (Icc a b) := fun x hx => (hB x hx).continuousAt.continuousWithinAt
  have hcϕ : ContinuousOn ϕ (Icc a b) := fun x hx => (hϕ x hx).continuousAt.continuousWithinAt
  have hcϕ1 : ContinuousOn ϕ1 (Icc a b) := fun x hx => (hϕ1 x hx).continuousAt.continuousWithinAt
  have hcϕ2 : ContinuousOn ϕ2 (Icc a b) := fun x hx => (hϕ2 x hx).continuousAt.continuousWithinAt
  have h1 := CtOsc.ibp_once hab hlam hϕ hϕ1 hne hB hcB1 hcϕ2
  have hlamC : (Complex.I * (lam : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hlam)
  let H' : ℝ → ℂ := fun x =>
    B2 x / (ϕ1 x : ℂ) - 2 * B1 x * (ϕ2 x : ℂ) / (ϕ1 x : ℂ) ^ 2 -
      B x * (ϕ3 x : ℂ) / (ϕ1 x : ℂ) ^ 2 + 2 * B x * (ϕ2 x : ℂ) ^ 2 / (ϕ1 x : ℂ) ^ 3
  have hH_d : ∀ x ∈ Icc a b, HasDerivAt (ibpH B B1 ϕ1 ϕ2) (H' x) x := fun x hx => by
    have hne' : (ϕ1 x : ℂ) ≠ 0 := by exact_mod_cast hne x hx
    have e1 : HasDerivAt (fun y => (ϕ1 y : ℂ)) (ϕ2 x : ℂ) x := (hϕ1 x hx).ofReal_comp
    have e2 : HasDerivAt (fun y => (ϕ2 y : ℂ)) (ϕ3 x : ℂ) x := (hϕ2 x hx).ofReal_comp
    have num : HasDerivAt (fun y => B1 y * (ϕ1 y : ℂ) - B y * (ϕ2 y : ℂ))
        (B2 x * (ϕ1 x : ℂ) + B1 x * (ϕ2 x : ℂ) - (B1 x * (ϕ2 x : ℂ) + B x * (ϕ3 x : ℂ))) x :=
      ((hB1 x hx).mul e1).sub ((hB x hx).mul e2)
    have := num.div (e1.pow 2) (pow_ne_zero 2 hne')
    unfold ibpH; refine this.congr_deriv ?_
    dsimp [H']; norm_num; field_simp; ring
  have hF : ∀ x ∈ Icc a b,
      HasDerivAt (fun y => ibpH B B1 ϕ1 ϕ2 y / (ϕ1 y : ℂ) * Complex.exp (Complex.I * lam * (ϕ y : ℂ)))
        (ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 x * Complex.exp (Complex.I * lam * (ϕ x : ℂ)) +
          Complex.I * lam * (ibpH B B1 ϕ1 ϕ2 x * Complex.exp (Complex.I * lam * (ϕ x : ℂ)))) x := by
    intro x hx
    have hne' : (ϕ1 x : ℂ) ≠ 0 := by exact_mod_cast hne x hx
    have h1' : HasDerivAt (fun y => (ϕ1 y : ℂ)) (ϕ2 x : ℂ) x := (hϕ1 x hx).ofReal_comp
    have h2' := (hH_d x hx).div h1' hne'
    have h3 : HasDerivAt (fun y => Complex.exp (Complex.I * lam * (ϕ y : ℂ)))
        (Complex.exp (Complex.I * lam * (ϕ x : ℂ)) * (Complex.I * lam * (ϕ1 x : ℂ))) x :=
      ((hϕ x hx).ofReal_comp.const_mul (Complex.I * lam)).cexp
    refine (h2'.mul h3).congr_deriv ?_
    dsimp [H', ibpQ, ibpH]
    field_simp
    ring
  have hcexp : ContinuousOn (fun x => Complex.exp (Complex.I * lam * (ϕ x : ℂ))) (Icc a b) :=
    Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hcϕ))
  have hϕ1C : ContinuousOn (fun x => (ϕ1 x : ℂ)) (Icc a b) := Complex.continuous_ofReal.comp_continuousOn hcϕ1
  have hϕ2C : ContinuousOn (fun x => (ϕ2 x : ℂ)) (Icc a b) := Complex.continuous_ofReal.comp_continuousOn hcϕ2
  have hϕ3C : ContinuousOn (fun x => (ϕ3 x : ℂ)) (Icc a b) := Complex.continuous_ofReal.comp_continuousOn hc3
  have hnC : ∀ n : ℕ, ∀ x ∈ Icc a b, (ϕ1 x : ℂ) ^ n ≠ 0 := fun n x hx => pow_ne_zero n (by exact_mod_cast hne x hx)
  have hinv_c : ContinuousOn (fun x => ((ϕ1 x : ℂ) ^ 2)⁻¹) (Icc a b) :=
    (hϕ1C.pow 2).inv₀ (hnC 2)
  have hG_int : IntervalIntegrable (fun x => ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 x *
      Complex.exp (Complex.I * lam * (ϕ x : ℂ))) volume a b := by
    have ht1 : IntervalIntegrable (fun x => B2 x / (ϕ1 x : ℂ) ^ 2) volume a b := by
      simpa [div_eq_mul_inv] using hi2.mul_continuousOn (by rw [uIcc_of_le hab]; exact hinv_c)
    have hrem : ContinuousOn (fun x => -3 * B1 x * (ϕ2 x : ℂ) / (ϕ1 x : ℂ) ^ 3 -
        B x * (ϕ3 x : ℂ) / (ϕ1 x : ℂ) ^ 3 + 3 * B x * (ϕ2 x : ℂ) ^ 2 / (ϕ1 x : ℂ) ^ 4) (Icc a b) :=
      ((((continuousOn_const.mul hcB1).mul hϕ2C).div (hϕ1C.pow 3) (hnC 3)).sub
        ((hcB.mul hϕ3C).div (hϕ1C.pow 3) (hnC 3))).add
        (((continuousOn_const.mul hcB).mul (hϕ2C.pow 2)).div (hϕ1C.pow 4) (hnC 4))
    have hq_int : IntervalIntegrable (ibpQ B B1 B2 ϕ1 ϕ2 ϕ3) volume a b := by
      have heq : ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 = fun x =>
          B2 x / (ϕ1 x : ℂ) ^ 2 + (-3 * B1 x * (ϕ2 x : ℂ) / (ϕ1 x : ℂ) ^ 3 -
            B x * (ϕ3 x : ℂ) / (ϕ1 x : ℂ) ^ 3 + 3 * B x * (ϕ2 x : ℂ) ^ 2 / (ϕ1 x : ℂ) ^ 4) := by
        ext x; unfold ibpQ; ring
      rw [heq]
      exact ht1.add (hrem.intervalIntegrable_of_Icc hab)
    exact hq_int.mul_continuousOn (by rw [uIcc_of_le hab]; exact hcexp)
  have hH_c : ContinuousOn (fun x => Complex.I * lam * (ibpH B B1 ϕ1 ϕ2 x *
      Complex.exp (Complex.I * lam * (ϕ x : ℂ)))) (Icc a b) := by
    have hibp_c : ContinuousOn (ibpH B B1 ϕ1 ϕ2) (Icc a b) :=
      ((hcB1.mul hϕ1C).sub (hcB.mul hϕ2C)).div (hϕ1C.pow 2) (hnC 2)
    exact continuousOn_const.mul (hibp_c.mul hcexp)
  have hH_int : IntervalIntegrable _ volume a b := hH_c.intervalIntegrable_of_Icc hab
  have hFtc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
    (by rw [uIcc_of_le hab]; exact hF) (hG_int.add hH_int)
  rw [intervalIntegral.integral_add hG_int hH_int, intervalIntegral.integral_const_mul] at hFtc
  have h2 : ∫ x in a..b, ibpH B B1 ϕ1 ϕ2 x * Complex.exp (Complex.I * lam * (ϕ x : ℂ)) =
      (1 / (Complex.I * lam)) * (ibpH B B1 ϕ1 ϕ2 b / (ϕ1 b : ℂ) * Complex.exp (Complex.I * lam * (ϕ b : ℂ)) -
        ibpH B B1 ϕ1 ϕ2 a / (ϕ1 a : ℂ) * Complex.exp (Complex.I * lam * (ϕ a : ℂ))) -
      (1 / (Complex.I * lam)) * ∫ x in a..b, ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 x * Complex.exp (Complex.I * lam * (ϕ x : ℂ)) := by
    have e1 : (Complex.I * (lam : ℂ)) * ∫ x in a..b, ibpH B B1 ϕ1 ϕ2 x * Complex.exp (Complex.I * lam * (ϕ x : ℂ)) =
        (ibpH B B1 ϕ1 ϕ2 b / (ϕ1 b : ℂ) * Complex.exp (Complex.I * lam * (ϕ b : ℂ)) -
          ibpH B B1 ϕ1 ϕ2 a / (ϕ1 a : ℂ) * Complex.exp (Complex.I * lam * (ϕ a : ℂ))) -
        ∫ x in a..b, ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 x * Complex.exp (Complex.I * lam * (ϕ x : ℂ)) := by
      linear_combination -hFtc.symm
    calc ∫ x in a..b, ibpH B B1 ϕ1 ϕ2 x * Complex.exp (Complex.I * lam * (ϕ x : ℂ))
        = (Complex.I * lam)⁻¹ * ((Complex.I * lam) *
            ∫ x in a..b, ibpH B B1 ϕ1 ϕ2 x * Complex.exp (Complex.I * lam * (ϕ x : ℂ))) :=
          (inv_mul_cancel_left₀ hlamC _).symm
      _ = _ := by rw [e1]; field_simp
  have e2 : ∫ x in a..b, ibpH B B1 ϕ1 ϕ2 x * Complex.exp (Complex.I * lam * (ϕ x : ℂ)) =
      ∫ x in a..b, (B1 x * (ϕ1 x : ℂ) - B x * (ϕ2 x : ℂ)) / (ϕ1 x : ℂ) ^ 2 *
        Complex.exp (Complex.I * lam * (ϕ x : ℂ)) := rfl
  rw [h1, ← e2, h2]
  ring

/-- Tail double-IBP on `[v₁, ∞)` for `v₁ ≥ v₀ > 0` and `x' < edgeF v₁`, with exact
`CtOsc.ibpH` boundary terms at `v₁` and explicit `ε`-uniform `O(c'⁻²)` remainder. -/
theorem phiDual_tail_ibp2 {v₀ v₁ c' x' : ℝ} (hv₀ : 0 < v₀) (hv₁ : v₀ ≤ v₁)
    (hc' : 0 < c') (hx' : x' < edgeF v₁) {B B1 B2 : ℝ → ℂ} (hB : OscAmpBound v₀ B B1 B2)
    (hint : IntegrableOn (fun v => B v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) (Ioi v₁)) :
    let ϕ1 : ℝ → ℝ := fun v => (4 * π / 3) * (edgeF v - x')
    let ϕ2 : ℝ → ℝ := fun v => (4 * π / 3) * edgeF' v
    let ϕ3 : ℝ → ℝ := fun v => (4 * π / 3) * edgeF'' v
    let δ₁ : ℝ := ϕ1 v₁
    (∫ v in Ioi v₁, B v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)) =
      -(1 / (Complex.I * (c' : ℂ))) *
        (B v₁ / (ϕ1 v₁ : ℂ) * Complex.exp (Complex.I * ((c' * phiDual v₁ x' : ℝ) : ℂ))) +
        (1 / (Complex.I * (c' : ℂ))) ^ 2 *
          (ibpH B B1 ϕ1 ϕ2 v₁ / (ϕ1 v₁ : ℂ) * Complex.exp (Complex.I * ((c' * phiDual v₁ x' : ℝ) : ℂ))) +
        (1 / (Complex.I * (c' : ℂ))) ^ 2 *
          ∫ v in Ioi v₁, ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 v *
            Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) ∧
    IntegrableOn (fun v => ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 v *
      Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) (Ioi v₁) ∧
    ‖∫ v in Ioi v₁, ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 v *
      Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))‖ ≤
        hB.L2 / δ₁ ^ 2 + (3 / 2 : ℝ) * hB.K1 / δ₁ ^ 2 +
          (1 / 2 : ℝ) * hB.K0 * ((2 * π) / edgeF' v₀) / δ₁ ^ 2 +
          (4 * π / 3) * hB.K0 / δ₁ ^ 3 := by
  intro ϕ1 ϕ2 ϕ3 δ₁
  have hF_c : Continuous edgeF := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF v).continuousAt
  have hF'_c : Continuous edgeF' := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF' v).continuousAt
  have hF''_c : Continuous edgeF'' := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF'' v).continuousAt
  have hϕ_d : ∀ v : ℝ, HasDerivAt (fun u => phiDual u x') (ϕ1 v) v := fun v => by
    unfold phiDual
    have hi : IntervalIntegrable (fun u => edgeF u - x') volume 0 v :=
      (hF_c.sub continuous_const).intervalIntegrable 0 v
    have hd := intervalIntegral.integral_hasDerivAt_right hi
      ((hF_c.sub continuous_const).stronglyMeasurableAtFilter _ _)
      (hF_c.sub continuous_const).continuousAt
    exact hd.const_mul (4 * π / 3)
  have hϕ1_d : ∀ v : ℝ, HasDerivAt ϕ1 (ϕ2 v) v := fun v =>
    ((hasDerivAt_edgeF v).sub_const x').const_mul (4 * π / 3)
  have hϕ2_d : ∀ v : ℝ, HasDerivAt ϕ2 (ϕ3 v) v := fun v =>
    (hasDerivAt_edgeF' v).const_mul (4 * π / 3)
  have hδ₁_pos : 0 < δ₁ := by dsimp [δ₁, ϕ1]; have := Real.pi_pos; positivity
  have hϕ1_ge : ∀ v ∈ Ici v₁, δ₁ ≤ ϕ1 v := fun v hv => by
    dsimp [δ₁, ϕ1]
    have hmono : edgeF v₁ ≤ edgeF v := by
      rcases hv.eq_or_lt with rfl | hlt
      · exact le_rfl
      · exact (edgeF_strictMonoOn (hv₀.le.trans hv₁) (hv₀.le.trans (hv₁.trans hv)) hlt).le
    have := Real.pi_pos
    gcongr
  have hϕ1_ne : ∀ v ∈ Ici v₁, ϕ1 v ≠ 0 := fun v hv => (hδ₁_pos.trans_le (hϕ1_ge v hv)).ne'
  have hϕ1_tend : Tendsto ϕ1 atTop atTop := by
    have hsub : Tendsto (fun v => v - x') atTop atTop := tendsto_id.atTop_add tendsto_const_nhds
    have hbig : Tendsto (fun v => (4 * π / 3) * (v - x')) atTop atTop :=
      hsub.const_mul_atTop (by positivity)
    exact tendsto_atTop_mono (fun v => by
      dsimp [ϕ1]; exact mul_le_mul_of_nonneg_left (by linarith [v_lt_edgeF v]) (by positivity)) hbig
  have hF'₀ : 0 < edgeF' v₀ := edgeF'_pos hv₀
  let C_F : ℝ := (2 * π) / edgeF' v₀
  have hϕ2_pos : ∀ v ∈ Ici v₁, 0 < ϕ2 v := fun v hv => by
    dsimp [ϕ2]; exact mul_pos (by positivity) (edgeF'_pos (hv₀.trans_le (hv₁.trans hv)))
  have hϕ2_le : ∀ v ∈ Ici v₁, ϕ2 v ≤ 4 * π / 3 := fun v _ => by
    dsimp [ϕ2]; nlinarith [Real.pi_pos, edgeF'_lt_one v]
  have hϕ3_le : ∀ v ∈ Ici v₁, |ϕ3 v| ≤ C_F * ϕ2 v := fun v hv => by
    have hv₀_le : v₀ ≤ v := hv₁.trans hv
    have hF' := edgeF'_v_bounds hv₀ hv₀_le
    have hF'' := edgeF''_bound (hv₀.le.trans hv₀_le)
    have h2 : edgeF'' v ≤ 2 * π := by
      unfold edgeF''
      have hc : 1 ≤ Real.cosh (π * v) := Real.one_le_cosh _
      have hden : Real.cosh (π * v) ≤ (1 + Real.cosh (π * v) ^ 2) ^ (3 / 2 : ℝ) := by
        have hc3 : Real.cosh (π * v) ^ 3 ≤ (1 + Real.cosh (π * v) ^ 2) ^ (3 / 2 : ℝ) := by
          have h1 : Real.cosh (π * v) ^ 3 = (Real.cosh (π * v) ^ 2) ^ (3 / 2 : ℝ) := by
            rw [← Real.rpow_natCast (Real.cosh (π * v)), ← Real.rpow_natCast (Real.cosh (π * v)) 2,
              ← Real.rpow_mul (Real.cosh_pos _).le]; norm_num
          rw [h1]; exact Real.rpow_le_rpow (by positivity) (by linarith [sq_nonneg (Real.cosh (π * v))]) (by norm_num)
        nlinarith [hc]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
    dsimp [ϕ3, ϕ2, C_F]
    rw [abs_of_pos (mul_pos (by positivity) hF''.1)]
    have h2' : edgeF'' v ≤ ((2 * π) / edgeF' v₀) * edgeF' v := by
      calc edgeF'' v ≤ 2 * π := h2
        _ = ((2 * π) / edgeF' v₀) * edgeF' v₀ := by field_simp [hF'₀.ne']
        _ ≤ ((2 * π) / edgeF' v₀) * edgeF' v := by gcongr; exact hF'.1
    calc (4 * π / 3) * edgeF'' v ≤ (4 * π / 3) * (((2 * π) / edgeF' v₀) * edgeF' v) := by
          gcongr
      _ = ((2 * π) / edgeF' v₀) * ((4 * π / 3) * edgeF' v) := by ring
  have hK3_int : IntegrableOn (fun v => ϕ2 v / ϕ1 v ^ 3) (Ioi v₁) ∧
      ∫ v in Ioi v₁, ϕ2 v / ϕ1 v ^ 3 ≤ (2 * δ₁ ^ 2)⁻¹ := by
    have hd : ∀ v ∈ Ici v₁, HasDerivAt (fun t => -(2 * ϕ1 t ^ 2)⁻¹) (ϕ2 v / ϕ1 v ^ 3) v := fun v hv => by
      have hne := hϕ1_ne v hv
      have hpos : 0 < ϕ1 v := hδ₁_pos.trans_le (hϕ1_ge v hv)
      have h1 := ((hϕ1_d v).pow 2).const_mul (2 : ℝ)
      have h2 := h1.inv (by simp only [Pi.pow_apply]; positivity)
      refine h2.neg.congr_deriv ?_
      simp only [Pi.pow_apply]; field_simp [hne]; ring
    have ht : Tendsto (fun t => -(2 * ϕ1 t ^ 2)⁻¹) atTop (𝓝 0) := by
      have hsq : Tendsto (fun t => 2 * ϕ1 t ^ 2) atTop atTop :=
        ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hϕ1_tend).const_mul_atTop zero_lt_two
      simpa using hsq.inv_tendsto_atTop.neg
    have hnn : ∀ v ∈ Ioi v₁, 0 ≤ ϕ2 v / ϕ1 v ^ 3 := fun v hv =>
      div_nonneg (hϕ2_pos v hv.le).le (pow_nonneg (hδ₁_pos.trans_le (hϕ1_ge v hv.le)).le 3)
    have hi := integrableOn_Ioi_deriv_of_nonneg' hd hnn ht
    have hint := integral_Ioi_of_hasDerivAt_of_nonneg' hd hnn ht
    refine ⟨hi, ?_⟩
    rw [hint, zero_sub, neg_neg]
  have hK4_int : IntegrableOn (fun v => ϕ2 v / ϕ1 v ^ 4) (Ioi v₁) ∧
      ∫ v in Ioi v₁, ϕ2 v / ϕ1 v ^ 4 ≤ (3 * δ₁ ^ 3)⁻¹ := by
    have hd : ∀ v ∈ Ici v₁, HasDerivAt (fun t => -(3 * ϕ1 t ^ 3)⁻¹) (ϕ2 v / ϕ1 v ^ 4) v := fun v hv => by
      have hne := hϕ1_ne v hv
      have h1 := ((hϕ1_d v).pow 3).const_mul (3 : ℝ)
      have hpos : 0 < ϕ1 v := hδ₁_pos.trans_le (hϕ1_ge v hv)
      have h2 := h1.inv (by simp only [Pi.pow_apply]; positivity)
      refine h2.neg.congr_deriv ?_
      simp only [Pi.pow_apply]; field_simp [hne]; ring
    have ht : Tendsto (fun t => -(3 * ϕ1 t ^ 3)⁻¹) atTop (𝓝 0) := by
      have hcub : Tendsto (fun t => 3 * ϕ1 t ^ 3) atTop atTop :=
        ((tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp hϕ1_tend).const_mul_atTop (by norm_num)
      simpa using hcub.inv_tendsto_atTop.neg
    have hnn : ∀ v ∈ Ioi v₁, 0 ≤ ϕ2 v / ϕ1 v ^ 4 := fun v hv =>
      div_nonneg (hϕ2_pos v hv.le).le (pow_nonneg (hδ₁_pos.trans_le (hϕ1_ge v hv.le)).le 4)
    have hi := integrableOn_Ioi_deriv_of_nonneg' hd hnn ht
    have hint := integral_Ioi_of_hasDerivAt_of_nonneg' hd hnn ht
    refine ⟨hi, ?_⟩
    rw [hint, zero_sub, neg_neg]
  let Qmaj : ℝ → ℝ := fun v =>
    ‖B2 v‖ / δ₁ ^ 2 + (3 * hB.K1 + hB.K0 * C_F) * (ϕ2 v / ϕ1 v ^ 3) +
      (4 * π * hB.K0) * (ϕ2 v / ϕ1 v ^ 4)
  have hi2_v1 : IntegrableOn B2 (Ioi v₁) := hB.i2.mono_set (Ioi_subset_Ioi hv₁)
  have hQmaj_int : IntegrableOn Qmaj (Ioi v₁) :=
    ((hi2_v1.norm.div_const (δ₁ ^ 2)).add (hK3_int.1.const_mul _)).add (hK4_int.1.const_mul _)
  have hQ_dom : ∀ v ∈ Ici v₁, ‖ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 v‖ ≤ Qmaj v := fun v hv => by
    have hv₀_le : v₀ ≤ v := hv₁.trans hv
    have h1_ge : δ₁ ≤ ϕ1 v := hϕ1_ge v hv
    have h1_pos : 0 < ϕ1 v := hδ₁_pos.trans_le h1_ge
    have h2_pos : 0 < ϕ2 v := hϕ2_pos v hv
    have h2_le : ϕ2 v ≤ 4 * π / 3 := hϕ2_le v hv
    have h3_le : |ϕ3 v| ≤ C_F * ϕ2 v := hϕ3_le v hv
    have hK0_nn : 0 ≤ hB.K0 := (norm_nonneg _).trans (hB.b0 v₀ le_rfl)
    have hK1_nn : 0 ≤ hB.K1 := (norm_nonneg _).trans (hB.b1 v₀ le_rfl)
    have ht1 : ‖B2 v / (ϕ1 v : ℂ) ^ 2‖ ≤ ‖B2 v‖ / δ₁ ^ 2 := by
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1_pos]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hδ₁_pos 2) (pow_le_pow_left₀ hδ₁_pos.le h1_ge 2)
    have ht2 : ‖3 * B1 v * (ϕ2 v : ℂ) / (ϕ1 v : ℂ) ^ 3‖ ≤ (3 * hB.K1) * (ϕ2 v / ϕ1 v ^ 3) := by
      simp only [norm_div, norm_mul, show ‖(3 : ℂ)‖ = 3 by norm_num, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1_pos, abs_of_pos h2_pos]
      have hb1 : 3 * ‖B1 v‖ * ϕ2 v ≤ 3 * hB.K1 * ϕ2 v :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hB.b1 v hv₀_le) (by norm_num)) h2_pos.le
      calc 3 * ‖B1 v‖ * ϕ2 v / ϕ1 v ^ 3 ≤ 3 * hB.K1 * ϕ2 v / ϕ1 v ^ 3 :=
            div_le_div_of_nonneg_right hb1 (by positivity)
        _ = (3 * hB.K1) * (ϕ2 v / ϕ1 v ^ 3) := by ring
    have ht3 : ‖B v * (ϕ3 v : ℂ) / (ϕ1 v : ℂ) ^ 3‖ ≤ (hB.K0 * C_F) * (ϕ2 v / ϕ1 v ^ 3) := by
      simp only [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1_pos]
      have hnum : ‖B v‖ * |ϕ3 v| ≤ hB.K0 * (C_F * ϕ2 v) :=
        mul_le_mul (hB.b0 v hv₀_le) (hϕ3_le v hv) (abs_nonneg _) hK0_nn
      calc ‖B v‖ * |ϕ3 v| / ϕ1 v ^ 3 ≤ hB.K0 * (C_F * ϕ2 v) / ϕ1 v ^ 3 :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ = (hB.K0 * C_F) * (ϕ2 v / ϕ1 v ^ 3) := by ring
    have ht4 : ‖3 * B v * (ϕ2 v : ℂ) ^ 2 / (ϕ1 v : ℂ) ^ 4‖ ≤ (4 * π * hB.K0) * (ϕ2 v / ϕ1 v ^ 4) := by
      simp only [norm_div, norm_mul, show ‖(3 : ℂ)‖ = 3 by norm_num, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1_pos, abs_of_pos h2_pos]
      have h2sq : ϕ2 v ^ 2 ≤ (4 * π / 3) * ϕ2 v := by nlinarith [h2_pos, h2_le]
      have hnum : 3 * ‖B v‖ * ϕ2 v ^ 2 ≤ 3 * hB.K0 * ((4 * π / 3) * ϕ2 v) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hB.b0 v hv₀_le) (by norm_num)) h2sq (sq_nonneg _) (by positivity)
      calc 3 * ‖B v‖ * ϕ2 v ^ 2 / ϕ1 v ^ 4 ≤ 3 * hB.K0 * ((4 * π / 3) * ϕ2 v) / ϕ1 v ^ 4 :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ = (4 * π * hB.K0) * (ϕ2 v / ϕ1 v ^ 4) := by ring
    unfold ibpQ
    have htri : ‖B2 v / (ϕ1 v : ℂ) ^ 2 - 3 * B1 v * (ϕ2 v : ℂ) / (ϕ1 v : ℂ) ^ 3 -
        B v * (ϕ3 v : ℂ) / (ϕ1 v : ℂ) ^ 3 + 3 * B v * (ϕ2 v : ℂ) ^ 2 / (ϕ1 v : ℂ) ^ 4‖ ≤
        ‖B2 v / (ϕ1 v : ℂ) ^ 2‖ + ‖3 * B1 v * (ϕ2 v : ℂ) / (ϕ1 v : ℂ) ^ 3‖ +
          ‖B v * (ϕ3 v : ℂ) / (ϕ1 v : ℂ) ^ 3‖ + ‖3 * B v * (ϕ2 v : ℂ) ^ 2 / (ϕ1 v : ℂ) ^ 4‖ := by
      refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
      refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
      exact norm_sub_le _ _
    dsimp [Qmaj]
    linarith
  have hphase_meas : Measurable (fun v => Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) :=
    Complex.continuous_exp.measurable.comp ((Complex.continuous_ofReal.measurable.comp
      ((continuous_iff_continuousAt.mpr fun v => (hϕ_d v).continuousAt).measurable.const_mul c')).const_mul Complex.I)
  have hQ_meas : AEStronglyMeasurable (fun v => ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 v *
      Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) (volume.restrict (Ioi v₁)) := by
    have hBc_on : ContinuousOn B (Ici v₁) := fun v hv => (hB.hd1 v (hv₁.trans hv)).continuousAt.continuousWithinAt
    have hB1c_on : ContinuousOn B1 (Ici v₁) := fun v hv => (hB.hd2 v (hv₁.trans hv)).continuousAt.continuousWithinAt
    have hBc : AEStronglyMeasurable B (volume.restrict (Ioi v₁)) :=
      (hBc_on.aestronglyMeasurable measurableSet_Ici).mono_set Ioi_subset_Ici_self
    have hB1c : AEStronglyMeasurable B1 (volume.restrict (Ioi v₁)) :=
      (hB1c_on.aestronglyMeasurable measurableSet_Ici).mono_set Ioi_subset_Ici_self
    have hB2m : AEStronglyMeasurable B2 (volume.restrict (Ioi v₁)) := hi2_v1.aestronglyMeasurable
    have h1_meas : Measurable (fun v => (ϕ1 v : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (continuous_iff_continuousAt.mpr fun v => (hϕ1_d v).continuousAt).measurable
    have h2_meas : Measurable (fun v => (ϕ2 v : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (continuous_iff_continuousAt.mpr fun v => (hϕ2_d v).continuousAt).measurable
    have h3_meas : Measurable (fun v => (ϕ3 v : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (continuous_const.mul hF''_c).measurable
    have hinv2 : AEStronglyMeasurable (fun v => ((ϕ1 v : ℂ) ^ 2)⁻¹) (volume.restrict (Ioi v₁)) :=
      (h1_meas.pow_const 2).inv.aestronglyMeasurable
    have hinv3 : AEStronglyMeasurable (fun v => ((ϕ1 v : ℂ) ^ 3)⁻¹) (volume.restrict (Ioi v₁)) :=
      (h1_meas.pow_const 3).inv.aestronglyMeasurable
    have hinv4 : AEStronglyMeasurable (fun v => ((ϕ1 v : ℂ) ^ 4)⁻¹) (volume.restrict (Ioi v₁)) :=
      (h1_meas.pow_const 4).inv.aestronglyMeasurable
    have h2m : AEStronglyMeasurable (fun v => (ϕ2 v : ℂ)) (volume.restrict (Ioi v₁)) :=
      h2_meas.aestronglyMeasurable
    have h3m : AEStronglyMeasurable (fun v => (ϕ3 v : ℂ)) (volume.restrict (Ioi v₁)) :=
      h3_meas.aestronglyMeasurable
    have hQm : AEStronglyMeasurable (ibpQ B B1 B2 ϕ1 ϕ2 ϕ3) (volume.restrict (Ioi v₁)) := by
      have heq : ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 = fun v =>
          B2 v * ((ϕ1 v : ℂ) ^ 2)⁻¹ - 3 * B1 v * (ϕ2 v : ℂ) * ((ϕ1 v : ℂ) ^ 3)⁻¹ -
            B v * (ϕ3 v : ℂ) * ((ϕ1 v : ℂ) ^ 3)⁻¹ + 3 * B v * (ϕ2 v : ℂ) ^ 2 * ((ϕ1 v : ℂ) ^ 4)⁻¹ := by
        ext v; unfold ibpQ; ring
      rw [heq]
      exact (((hB2m.mul hinv2).sub (((hB1c.const_mul 3).mul h2m).mul hinv3)).sub
        ((hBc.mul h3m).mul hinv3)).add (((hBc.const_mul 3).mul (h2m.pow 2)).mul hinv4)
    exact hQm.mul hphase_meas.aestronglyMeasurable
  have hQ_int : IntegrableOn (fun v => ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 v *
      Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) (Ioi v₁) := by
    refine hQmaj_int.mono' hQ_meas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
    exact hQ_dom v hv.le
  have hI_tend := intervalIntegral_tendsto_integral_Ioi v₁ hint tendsto_id
  have hQ_tend := intervalIntegral_tendsto_integral_Ioi v₁ hQ_int tendsto_id
  have heq_on : ∀ᶠ T : ℝ in atTop,
      ∫ v in v₁..T, B v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)) =
        ((1 / (Complex.I * (c' : ℂ))) *
          (B T / (ϕ1 T : ℂ) * Complex.exp (Complex.I * ((c' * phiDual T x' : ℝ) : ℂ)) -
            B v₁ / (ϕ1 v₁ : ℂ) * Complex.exp (Complex.I * ((c' * phiDual v₁ x' : ℝ) : ℂ))) -
          (1 / (Complex.I * (c' : ℂ))) ^ 2 *
            (ibpH B B1 ϕ1 ϕ2 T / (ϕ1 T : ℂ) * Complex.exp (Complex.I * ((c' * phiDual T x' : ℝ) : ℂ)) -
              ibpH B B1 ϕ1 ϕ2 v₁ / (ϕ1 v₁ : ℂ) * Complex.exp (Complex.I * ((c' * phiDual v₁ x' : ℝ) : ℂ))) +
          (1 / (Complex.I * (c' : ℂ))) ^ 2 *
            ∫ v in v₁..T, ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 v *
              Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) := by
    filter_upwards [eventually_ge_atTop v₁] with T hT
    have hi2_T : IntervalIntegrable B2 volume v₁ T :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr (hi2_v1.mono_set Ioc_subset_Ioi_self)
    have hc3_T : ContinuousOn ϕ3 (Icc v₁ T) := (continuous_const.mul hF''_c).continuousOn
    have h2 := ibp_twice_ae hT hc'.ne'
      (fun v _ => hϕ_d v) (fun v _ => hϕ1_d v) (fun v _ => hϕ2_d v)
      (fun v hv => hϕ1_ne v hv.1)
      (fun v hv => hB.hd1 v (hv₁.trans hv.1))
      (fun v hv => hB.hd2 v (hv₁.trans hv.1)) hi2_T hc3_T
    simpa [Complex.ofReal_mul, mul_assoc] using h2
  have hb1_tend : Tendsto (fun T : ℝ =>
      B T / (ϕ1 T : ℂ) * Complex.exp (Complex.I * ((c' * phiDual T x' : ℝ) : ℂ))) atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa [div_eq_mul_inv] using hϕ1_tend.inv_tendsto_atTop.const_mul hB.K0)
    filter_upwards [eventually_ge_atTop v₁] with T hT
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hδ₁_pos.trans_le (hϕ1_ge T hT))]
    exact div_le_div_of_nonneg_right (hB.b0 T (hv₁.trans hT)) (hδ₁_pos.trans_le (hϕ1_ge T hT)).le
  have hb2_tend : Tendsto (fun T : ℝ =>
      ibpH B B1 ϕ1 ϕ2 T / (ϕ1 T : ℂ) * Complex.exp (Complex.I * ((c' * phiDual T x' : ℝ) : ℂ))) atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    let M : ℝ := hB.K1 + hB.K0 * (4 * π / 3) / δ₁
    have hsq : Tendsto (fun T => M / ϕ1 T ^ 2) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hϕ1_tend).inv_tendsto_atTop.const_mul M
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hsq
    filter_upwards [eventually_ge_atTop v₁] with T hT
    have hT0 : v₀ ≤ T := hv₁.trans hT
    have h1_pos : 0 < ϕ1 T := hδ₁_pos.trans_le (hϕ1_ge T hT)
    have h2_pos : 0 < ϕ2 T := hϕ2_pos T hT
    have h2_le : ϕ2 T ≤ 4 * π / 3 := hϕ2_le T hT
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos h1_pos]
    unfold ibpH
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1_pos]
    have hnum : ‖B1 T * (ϕ1 T : ℂ) - B T * (ϕ2 T : ℂ)‖ ≤ hB.K1 * ϕ1 T + hB.K0 * (4 * π / 3) := by
      refine (norm_sub_le _ _).trans ?_
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1_pos, abs_of_pos h2_pos]
      exact add_le_add (mul_le_mul_of_nonneg_right (hB.b1 T hT0) h1_pos.le)
        (mul_le_mul (hB.b0 T hT0) h2_le h2_pos.le hB.hK0)
    calc (‖B1 T * (ϕ1 T : ℂ) - B T * (ϕ2 T : ℂ)‖ / ϕ1 T ^ 2) / ϕ1 T
        ≤ ((hB.K1 * ϕ1 T + hB.K0 * (4 * π / 3)) / ϕ1 T ^ 2) / ϕ1 T := by gcongr
      _ = (hB.K1 + hB.K0 * (4 * π / 3) / ϕ1 T) / ϕ1 T ^ 2 := by field_simp [h1_pos.ne']
      _ ≤ M / ϕ1 T ^ 2 := by
          dsimp [M]
          have := hB.hK0
          gcongr
          exact hϕ1_ge T hT
  have hrhs_tend : Tendsto (fun T : ℝ =>
      (1 / (Complex.I * (c' : ℂ))) *
        (B T / (ϕ1 T : ℂ) * Complex.exp (Complex.I * ((c' * phiDual T x' : ℝ) : ℂ)) -
          B v₁ / (ϕ1 v₁ : ℂ) * Complex.exp (Complex.I * ((c' * phiDual v₁ x' : ℝ) : ℂ))) -
      (1 / (Complex.I * (c' : ℂ))) ^ 2 *
        (ibpH B B1 ϕ1 ϕ2 T / (ϕ1 T : ℂ) * Complex.exp (Complex.I * ((c' * phiDual T x' : ℝ) : ℂ)) -
          ibpH B B1 ϕ1 ϕ2 v₁ / (ϕ1 v₁ : ℂ) * Complex.exp (Complex.I * ((c' * phiDual v₁ x' : ℝ) : ℂ))) +
      (1 / (Complex.I * (c' : ℂ))) ^ 2 *
        ∫ v in v₁..T, ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 v *
          Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) atTop
      (𝓝 ((1 / (Complex.I * (c' : ℂ))) *
          ((0 : ℂ) - B v₁ / (ϕ1 v₁ : ℂ) * Complex.exp (Complex.I * ((c' * phiDual v₁ x' : ℝ) : ℂ))) -
        (1 / (Complex.I * (c' : ℂ))) ^ 2 *
          ((0 : ℂ) - ibpH B B1 ϕ1 ϕ2 v₁ / (ϕ1 v₁ : ℂ) * Complex.exp (Complex.I * ((c' * phiDual v₁ x' : ℝ) : ℂ))) +
        (1 / (Complex.I * (c' : ℂ))) ^ 2 *
          ∫ v in Ioi v₁, ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 v *
            Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)))) :=
    (((tendsto_const_nhds.mul (hb1_tend.sub_const _)).sub
      (tendsto_const_nhds.mul (hb2_tend.sub_const _))).add (tendsto_const_nhds.mul hQ_tend))
  have hlimit :
      ∫ v in Ioi v₁, B v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)) =
        (1 / (Complex.I * (c' : ℂ))) *
          ((0 : ℂ) - B v₁ / (ϕ1 v₁ : ℂ) * Complex.exp (Complex.I * ((c' * phiDual v₁ x' : ℝ) : ℂ))) -
        (1 / (Complex.I * (c' : ℂ))) ^ 2 *
          ((0 : ℂ) - ibpH B B1 ϕ1 ϕ2 v₁ / (ϕ1 v₁ : ℂ) * Complex.exp (Complex.I * ((c' * phiDual v₁ x' : ℝ) : ℂ))) +
        (1 / (Complex.I * (c' : ℂ))) ^ 2 *
          ∫ v in Ioi v₁, ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 v *
            Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)) :=
    tendsto_nhds_unique hI_tend (hrhs_tend.congr' (heq_on.mono fun _ h => h.symm))
  refine ⟨?_, hQ_int, ?_⟩
  · rw [hlimit]; ring
  · have hnorm_int : ‖∫ v in Ioi v₁, ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 v *
        Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))‖ ≤
        ∫ v in Ioi v₁, Qmaj v := by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine integral_mono_ae hQ_int.norm hQmaj_int ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
      exact hQ_dom v hv.le
    have hiA : IntegrableOn (fun v => ‖B2 v‖ / δ₁ ^ 2) (Ioi v₁) := hi2_v1.norm.div_const _
    have hiB : IntegrableOn (fun v => (3 * hB.K1 + hB.K0 * C_F) * (ϕ2 v / ϕ1 v ^ 3)) (Ioi v₁) :=
      hK3_int.1.const_mul _
    have hiC : IntegrableOn (fun v => 4 * π * hB.K0 * (ϕ2 v / ϕ1 v ^ 4)) (Ioi v₁) :=
      hK4_int.1.const_mul _
    have he1 := integral_add (hiA.add hiB) hiC
    have he2 := integral_add hiA hiB
    have hQmaj_eq : ∫ v in Ioi v₁, Qmaj v =
        (∫ v in Ioi v₁, ‖B2 v‖) / δ₁ ^ 2 +
          (3 * hB.K1 + hB.K0 * C_F) * (∫ v in Ioi v₁, ϕ2 v / ϕ1 v ^ 3) +
          (4 * π * hB.K0) * (∫ v in Ioi v₁, ϕ2 v / ϕ1 v ^ 4) := by
      dsimp [Qmaj]
      rw [show (∫ v in Ioi v₁, ‖B2 v‖ / δ₁ ^ 2 + (3 * hB.K1 + hB.K0 * C_F) * (ϕ2 v / ϕ1 v ^ 3) +
          4 * π * hB.K0 * (ϕ2 v / ϕ1 v ^ 4)) =
          (∫ v in Ioi v₁, ‖B2 v‖ / δ₁ ^ 2 + (3 * hB.K1 + hB.K0 * C_F) * (ϕ2 v / ϕ1 v ^ 3)) +
            ∫ v in Ioi v₁, 4 * π * hB.K0 * (ϕ2 v / ϕ1 v ^ 4) from he1,
        show (∫ v in Ioi v₁, ‖B2 v‖ / δ₁ ^ 2 + (3 * hB.K1 + hB.K0 * C_F) * (ϕ2 v / ϕ1 v ^ 3)) =
          (∫ v in Ioi v₁, ‖B2 v‖ / δ₁ ^ 2) +
            ∫ v in Ioi v₁, (3 * hB.K1 + hB.K0 * C_F) * (ϕ2 v / ϕ1 v ^ 3) from he2,
        integral_div, integral_const_mul, integral_const_mul]
    have hL2_v1 : ∫ v in Ioi v₁, ‖B2 v‖ ≤ hB.L2 :=
      (MeasureTheory.integral_mono_measure (Measure.restrict_mono (Ioi_subset_Ioi hv₁) le_rfl)
        (Eventually.of_forall fun _ => norm_nonneg _) hB.i2.norm).trans hB.int2
    calc ‖∫ v in Ioi v₁, ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 v *
          Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))‖
        ≤ ∫ v in Ioi v₁, Qmaj v := hnorm_int
      _ = (∫ v in Ioi v₁, ‖B2 v‖) / δ₁ ^ 2 +
            (3 * hB.K1 + hB.K0 * C_F) * (∫ v in Ioi v₁, ϕ2 v / ϕ1 v ^ 3) +
            (4 * π * hB.K0) * (∫ v in Ioi v₁, ϕ2 v / ϕ1 v ^ 4) := hQmaj_eq
      _ ≤ hB.L2 / δ₁ ^ 2 + (3 * hB.K1 + hB.K0 * C_F) * (2 * δ₁ ^ 2)⁻¹ +
            (4 * π * hB.K0) * (3 * δ₁ ^ 3)⁻¹ := by
          have h1 : 0 ≤ 3 * hB.K1 + hB.K0 * C_F := by have := hB.hK1; have := hB.hK0; positivity
          have h2 : 0 ≤ 4 * π * hB.K0 := by have := hB.hK0; positivity
          exact add_le_add (add_le_add (div_le_div_of_nonneg_right hL2_v1 (sq_nonneg δ₁))
            (mul_le_mul_of_nonneg_left hK3_int.2 h1))
            (mul_le_mul_of_nonneg_left hK4_int.2 h2)
      _ = hB.L2 / δ₁ ^ 2 + (3 / 2 : ℝ) * hB.K1 / δ₁ ^ 2 +
            (1 / 2 : ℝ) * hB.K0 * C_F / δ₁ ^ 2 + (4 * π / 3) * hB.K0 / δ₁ ^ 3 := by ring

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.phiDual_tail_ibp2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms phiDual_tail_ibp2

end
end FormalResearch.ModularBootstrap.FiveTerm
