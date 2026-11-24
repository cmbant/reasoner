module

public import FormalResearch.SignUncertainty.HankelBootDataTmp
public import FormalResearch.SignUncertainty.HankelLangerPsi
public import FormalResearch.SignUncertainty.HankelTransportMass
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.QuadratureBounds

/-!
# Hankel line estimate pieces (`hI_line`), with explicit `r_∞` slack

Transcription of the line-estimate pieces of `FormalResearch/ModularBootstrap/FixedWeightBand/BootstrapWLine.lean`
to the Hankel Langer-disc function `Re Ψ̃ = hankelPsiR c f`. Every step that used `Re Ψ̃ ≥ 0` now uses
`-hankelRinf c ≤ Re Ψ̃` (`hankel_psi_sign`), and the slack is carried in the statements.

* `hankelBoot_line_band`: the band piece on `[-R, u_T]`, slack `(R + 1) r_∞`.
* `hankelBoot_line_mid`: the middle piece on `[u_T, 1]`, using the total mass bound `hankel_psi_abs_mass`.
* `hankelBoot_line_right`: the right piece on `[1, R + ℓ]`, from the envelope `hankelPsi_envelope`.
* `hankelBoot_line_tail`: the positive tail beyond the line, `[R + ℓ, A]`.
* `hankelBoot_tail_le_coeff`: the tail is at most `60 (k+1)/R` for `k ≥ 5`.

The top piece and the assembly are not in this module.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.ModularBootstrap.ConcreteBootstrap
  (sixtythree_hundredths_min_le_one_sub_exp abs_one_add_pow_sub_one_le)

/-- Pointwise weight inequality: if `0 ≤ a ≤ b ≤ 1` and `x ≥ -r ≥ -∞`, then `a x ≤ b x + r`. -/
theorem hankelBoot_weight_pt {a b x r : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (hx : -r ≤ x)
    (hr : 0 ≤ r) : a * x ≤ b * x + r := by
  nlinarith [mul_nonneg (sub_nonneg.2 hab) (by linarith : (0 : ℝ) ≤ x + r),
    mul_nonneg hr (by linarith : (0 : ℝ) ≤ 1 - b + a)]

/-- Integrated form of the pointwise weight inequality on `[p, q]`. -/
theorem hankelBoot_weight_integral {p q r : ℝ} {x a b : ℝ → ℝ} (hpq : p ≤ q)
    (ha : IntervalIntegrable (fun v => a v * x v) volume p q)
    (hb : IntervalIntegrable (fun v => b v * x v) volume p q)
    (hpt : ∀ v ∈ Icc p q, a v * x v ≤ b v * x v + r) :
    (∫ v in p..q, a v * x v) ≤ (∫ v in p..q, b v * x v) + (q - p) * r := by
  have h1 : (∫ v in p..q, a v * x v) ≤ ∫ v in p..q, (b v * x v + r) :=
    intervalIntegral.integral_mono_on hpq ha (hb.add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_add hb intervalIntegrable_const, intervalIntegral.integral_const,
    smul_eq_mul] at h1
  exact h1

/-- Envelope for real points: `|Re Ψ̃(v)| ≤ 60 exp(-(4/3) v^{3/2})` for `1 ≤ v ≤ A`. -/
theorem hankelBoot_psi_real_env {c ε : ℝ} (hc : 3e6 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) {v : ℝ} (hv1 : 1 ≤ v)
    (hvA : v ≤ langerRadius c) :
    |hankelPsiR c f v| ≤ 60 * Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ)) := by
  have hv_pos : 0 < v := by linarith
  have hc2 : (2 : ℝ) ≤ c := by linarith
  have hu : ‖(v : ℂ)‖ ≤ c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv_pos]
    have hA : langerRadius c = c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := by
      unfold langerRadius langerScale; ring
    linarith
  have hcut : ¬ ((v : ℂ).im = 0 ∧ (v : ℂ).re ≤ 0) := fun h0 => by
    have h2 : (v : ℂ).re ≤ 0 := h0.2
    rw [Complex.ofReal_re] at h2
    linarith
  have henv := hankelPsi_envelope hc2 hf hε hM hu hcut
  have hre : ((v : ℂ) ^ (1 / 2 : ℂ)).re = √v := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hv_pos.le,
      Complex.ofReal_re, Real.sqrt_eq_rpow]
  have h32 : (v : ℂ) ^ (3 / 2 : ℂ) = ((v ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hv_pos.le]; norm_num
  have hexp : ‖Complex.exp (-(4 / 3 : ℂ) * (v : ℂ) ^ (3 / 2 : ℂ))‖ =
      Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ)) := by
    have e : -(4 / 3 : ℂ) * ((v ^ (3 / 2 : ℝ) : ℝ) : ℂ) =
        ((-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [h32, e, Complex.norm_exp_ofReal]
  have hsq1 : 1 ≤ √v := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hv1
  have hfac : (√v) ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hsq1 (by norm_num)
  rw [hre, hexp] at henv
  have h1 : |hankelPsiR c f v| ≤ ‖hankelPsi c f (v : ℂ)‖ := Complex.abs_re_le_norm _
  have hE : 0 ≤ 60 * Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ)) := by positivity
  have h2 : 60 * Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ)) * (√v) ^ (-(1 / 2 : ℝ)) ≤
      60 * Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ)) := mul_le_of_le_one_right hE hfac
  linarith [h1, henv, h2]

/-- Elementary exponential inequality for the right piece: `v e^{(3/10)v - (4/3)v^{3/2}} ≤ e^{-(8/15)v}`, `v ≥ 1`. -/
theorem hankelBoot_exp_right {v : ℝ} (hv1 : 1 ≤ v) :
    v * Real.exp ((3 / 10 : ℝ) * v - (4 / 3 : ℝ) * v ^ (3 / 2 : ℝ)) ≤
      Real.exp (-(8 / 15 : ℝ) * v) := by
  have hs : v ^ (3 / 2 : ℝ) = v * √v := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hsq : √v ^ 2 = v := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ √v := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hv1
  have ht : 0 ≤ √v - 1 := by linarith
  have key : (11 / 6 : ℝ) * (√v) ^ 2 - 1 ≤ (4 / 3 : ℝ) * ((√v) ^ 2 * √v) := by
    nlinarith [mul_nonneg ht ht, mul_nonneg (mul_nonneg ht ht) ht]
  rw [hsq] at key
  have h1 : v ≤ Real.exp (v - 1) := by linarith [Real.add_one_le_exp (v - 1)]
  have hpoly : (11 / 6 : ℝ) * v - 1 ≤ (4 / 3 : ℝ) * (v * √v) := key
  calc v * Real.exp ((3 / 10 : ℝ) * v - (4 / 3 : ℝ) * v ^ (3 / 2 : ℝ))
      ≤ Real.exp (v - 1) * Real.exp ((3 / 10 : ℝ) * v - (4 / 3 : ℝ) * v ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (v - 1 + ((3 / 10 : ℝ) * v - (4 / 3 : ℝ) * v ^ (3 / 2 : ℝ))) :=
        (Real.exp_add _ _).symm
    _ ≤ Real.exp (-(8 / 15 : ℝ) * v) := Real.exp_le_exp.mpr (by rw [hs]; linarith)

/-- `∫_1^b K e^{-(8/15)v} dv ≤ 2K` for `K ≥ 0`, `b ≥ 1`. -/
theorem hankelBoot_exp_int_le {K b : ℝ} (hK : 0 ≤ K) (hb : 1 ≤ b) :
    (∫ v in (1 : ℝ)..b, K * Real.exp (-(8 / 15 : ℝ) * v)) ≤ 2 * K := by
  have h1 : HasDerivAt (fun t : ℝ => -(8 / 15 : ℝ) * t) (-(8 / 15 : ℝ)) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (-(8 / 15 : ℝ))
  have hderiv : ∀ v ∈ Set.uIcc (1 : ℝ) b,
      HasDerivAt (fun t : ℝ => -((15 / 8 : ℝ) * K) * Real.exp (-(8 / 15 : ℝ) * t))
        (K * Real.exp (-(8 / 15 : ℝ) * v)) v := fun v _ => by
    have h1v : HasDerivAt (fun t : ℝ => -(8 / 15 : ℝ) * t) (-(8 / 15 : ℝ)) v := by
      simpa using (hasDerivAt_id v).const_mul (-(8 / 15 : ℝ))
    refine (h1v.exp.const_mul (-((15 / 8 : ℝ) * K))).congr_deriv ?_
    ring
  have h_eq := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable
      1 b)
  have h1_le : Real.exp (-(8 / 15 : ℝ) * 1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have e1 : K * Real.exp (-(8 / 15 : ℝ) * 1) ≤ K * 1 := mul_le_mul_of_nonneg_left h1_le hK
  have e2 : 0 ≤ K * Real.exp (-(8 / 15 : ℝ) * b) := mul_nonneg hK (Real.exp_pos _).le
  linarith [h_eq, e1, e2]

/-- `∫_a^A 60 e^{-(5/6)v} dv ≤ 72 e^{-(5/6)R}` for `R ≤ a ≤ A`. -/
theorem hankelBoot_gauss_tail_int {R a A : ℝ} (hRa : R ≤ a) (haA : a ≤ A) :
    (∫ v in a..A, 60 * Real.exp (-(5 / 6 : ℝ) * v)) ≤ 72 * Real.exp (-(5 / 6 : ℝ) * R) := by
  have hderiv : ∀ v ∈ Set.uIcc a A,
      HasDerivAt (fun t : ℝ => -72 * Real.exp (-(5 / 6 : ℝ) * t))
        (60 * Real.exp (-(5 / 6 : ℝ) * v)) v := fun v _ => by
    have h1v : HasDerivAt (fun t : ℝ => -(5 / 6 : ℝ) * t) (-(5 / 6 : ℝ)) v := by
      simpa using (hasDerivAt_id v).const_mul (-(5 / 6 : ℝ))
    refine (h1v.exp.const_mul (-72 : ℝ)).congr_deriv ?_
    ring
  have h_eq := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable
      a A)
  have hle : Real.exp (-(5 / 6 : ℝ) * a) ≤ Real.exp (-(5 / 6 : ℝ) * R) :=
    Real.exp_le_exp.mpr (by linarith)
  have hpos : 0 ≤ Real.exp (-(5 / 6 : ℝ) * A) := (Real.exp_pos _).le
  linarith [h_eq, hle, hpos]

/-- **Band piece** (`line_band_pieceW` transcribed): on `[-R, u_T]` with explicit slack `(R+1) r_∞`. -/
theorem hankelBoot_line_band {c ε T u_T R ℓ : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T) (hR10 : 10 ≤ R)
    (hRA : R + 1 ≤ langerRadius c) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1 / 2) (k : ℕ) :
    -(∫ v in (-R + ℓ)..u_T, (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v)
      - (∫ v in (-R)..(-R + ℓ), hankelPsiR c f v)
    ≤ -(63 / 100 : ℝ) * hankelBootMoment c f R u_T k + (R + 1) * hankelRinf c := by
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have hR_pos : 0 < R := by linarith
  have hA : 0 < langerRadius c := langerRadius_pos hc0
  have hfe := hf.toIsHankelEigenfn
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hfe hε hM
  have hcont := continuousOn_hankelPsiR hc0 hfe
  have hsub : ∀ {a b : ℝ}, -R ≤ a → b ≤ R + ℓ → Icc a b ⊆ Icc (-(langerRadius c)) (langerRadius c) :=
    fun ha hb => Icc_subset_Icc (by linarith) (by linarith)
  have hI : ∀ {a b : ℝ}, -R ≤ a → a ≤ b → b ≤ R + ℓ →
      IntervalIntegrable (hankelPsiR c f) volume a b :=
    fun ha hab hb => (hcont.mono (hsub ha hb)).intervalIntegrable_of_Icc hab
  have hWc : Continuous (fun v : ℝ => (1 + (v - ℓ) / R) ^ (k + 1)) :=
    (continuous_const.add ((continuous_id.sub continuous_const).div_const R)).pow (k + 1)
  have hmc : Continuous (fun v : ℝ => min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R)) :=
    continuous_const.min ((continuous_const.mul continuous_neg).div_const R)
  have hc63 : Continuous (fun _ : ℝ => (63 / 100 : ℝ)) := continuous_const
  have hI_w : ∀ {a b : ℝ}, -R ≤ a → a ≤ b → b ≤ R + ℓ →
      IntervalIntegrable (fun v : ℝ => (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v)
        volume a b :=
    fun ha hab hb => ((continuousOn_const.sub hWc.continuousOn).mul
      (hcont.mono (hsub ha hb))).intervalIntegrable_of_Icc hab
  have hI_m0 : ∀ {a b : ℝ}, -R ≤ a → a ≤ b → b ≤ R + ℓ →
      IntervalIntegrable (fun v : ℝ => min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) * hankelPsiR c f v)
        volume a b :=
    fun ha hab hb => (hmc.continuousOn.mul (hcont.mono (hsub ha hb))).intervalIntegrable_of_Icc hab
  have hI_m : ∀ {a b : ℝ}, -R ≤ a → a ≤ b → b ≤ R + ℓ →
      IntervalIntegrable (fun v : ℝ => (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) *
        hankelPsiR c f v) volume a b :=
    fun ha hab hb => ((hc63.continuousOn.mul hmc.continuousOn).mul
      (hcont.mono (hsub ha hb))).intervalIntegrable_of_Icc hab
  have hAv : ∀ v ∈ Icc (-R) u_T, |v| ≤ langerRadius c := fun v hv =>
    abs_le.2 ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hAu : |u_T| ≤ langerRadius c := abs_le.2 ⟨by linarith, by linarith⟩
  have hsign : ∀ v ∈ Icc (-R) u_T, -hankelRinf c ≤ hankelPsiR c f v := by
    intro v hv
    refine hankel_psi_sign hc5 hf hε hM (x := v) (hAv v hv) ?_
    rw [← hT]
    exact hankel_phi_anti hc0 (hAv v hv) hAu hv.2
  have hnegRl_le_uT : -R + ℓ ≤ u_T := by linarith
  -- low piece: weight `(63/100) min ≤ 1`
  have hlowpt : ∀ v ∈ Icc (-R) (-R + ℓ),
      (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) * hankelPsiR c f v ≤
        (1 : ℝ) * hankelPsiR c f v + hankelRinf c := by
    intro v hv
    have hyv : 0 ≤ ((k : ℝ) + 1) * (-v) / R :=
      div_nonneg (mul_nonneg (by positivity) (by linarith [hv.2, hℓ0])) hR_pos.le
    have hmin0 : 0 ≤ (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) :=
      mul_nonneg (by norm_num) (le_min zero_le_one hyv)
    have hmin1 : (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) ≤ 1 := by
      linarith [min_le_left (1 : ℝ) (((k : ℝ) + 1) * (-v) / R)]
    exact hankelBoot_weight_pt hmin0 hmin1 (le_refl _) (hsign v ⟨hv.1, by linarith [hv.2]⟩) hr
  -- main piece: weight `(63/100) min ≤ 1 - W` (`sixtythree_hundredths_min_le_one_sub_exp`)
  have hmainpt : ∀ v ∈ Icc (-R + ℓ) u_T,
      (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) * hankelPsiR c f v ≤
        (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v + hankelRinf c := by
    intro v hv
    have hv0 : v ≤ 0 := by linarith [hv.2]
    have hyv : 0 ≤ ((k : ℝ) + 1) * (-v) / R :=
      div_nonneg (mul_nonneg (by positivity) (by linarith)) hR_pos.le
    have hq : -1 ≤ (v - ℓ) / R := by rw [le_div_iff₀ hR_pos]; linarith [hv.1]
    have hbase : 0 ≤ 1 + (v - ℓ) / R := by linarith
    have hbase_le : 1 + (v - ℓ) / R ≤ Real.exp (-(-v / R)) := by
      have hv_div : (v - ℓ) / R ≤ v / R := div_le_div_of_nonneg_right (by linarith) hR_pos.le
      have hexp1 : 1 + v / R ≤ Real.exp (v / R) := by linarith [Real.add_one_le_exp (v / R)]
      rw [show -(-v / R) = v / R by ring]
      linarith only [hv_div, hexp1]
    have hW_le : (1 + (v - ℓ) / R) ^ (k + 1) ≤ Real.exp (-(((k : ℝ) + 1) * (-v) / R)) := by
      calc (1 + (v - ℓ) / R) ^ (k + 1) ≤ (Real.exp (-(-v / R))) ^ (k + 1) :=
            pow_le_pow_left₀ hbase hbase_le _
        _ = Real.exp (((k + 1 : ℕ) : ℝ) * (-(-v / R))) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp (-(((k : ℝ) + 1) * (-v) / R)) := by congr 1; push_cast; ring
    have hmin : (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) ≤
        1 - (1 + (v - ℓ) / R) ^ (k + 1) :=
      (sixtythree_hundredths_min_le_one_sub_exp hyv).trans (sub_le_sub_left hW_le 1)
    have hW0 : 0 ≤ (1 + (v - ℓ) / R) ^ (k + 1) := pow_nonneg hbase _
    have hmin0 : 0 ≤ (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) :=
      mul_nonneg (by norm_num) (le_min zero_le_one hyv)
    exact hankelBoot_weight_pt hmin0 hmin (by linarith) (hsign v ⟨by linarith [hv.1], hv.2⟩) hr
  have hlow_int := hankelBoot_weight_integral (r := hankelRinf c) (x := hankelPsiR c f)
    (a := fun v : ℝ => (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R))
    (b := fun _ : ℝ => (1 : ℝ)) (p := -R) (q := -R + ℓ) (by linarith)
    (hI_m le_rfl (by linarith) (by linarith))
    (by simpa only [one_mul] using hI le_rfl (by linarith) (by linarith)) hlowpt
  have hmain_int := hankelBoot_weight_integral (r := hankelRinf c) (x := hankelPsiR c f)
    (a := fun v : ℝ => (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R))
    (b := fun v : ℝ => 1 - (1 + (v - ℓ) / R) ^ (k + 1)) (p := -R + ℓ) (q := u_T) hnegRl_le_uT
    (hI_m (by linarith) hnegRl_le_uT (by linarith))
    (hI_w (by linarith) hnegRl_le_uT (by linarith)) hmainpt
  beta_reduce at hlow_int hmain_int
  simp only [one_mul] at hlow_int
  -- pull the constant `63/100` out of the integrals
  have eL : (∫ v in (-R)..(-R + ℓ), (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) *
      hankelPsiR c f v) = (63 / 100 : ℝ) * ∫ v in (-R)..(-R + ℓ),
        min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) * hankelPsiR c f v := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext v; ring
  have eM : (∫ v in (-R + ℓ)..u_T, (63 / 100 : ℝ) * min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) *
      hankelPsiR c f v) = (63 / 100 : ℝ) * ∫ v in (-R + ℓ)..u_T,
        min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) * hankelPsiR c f v := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext v; ring
  have hsplit : (∫ v in (-R)..u_T, min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) * hankelPsiR c f v) =
      (∫ v in (-R)..(-R + ℓ), min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) * hankelPsiR c f v) +
        ∫ v in (-R + ℓ)..u_T, min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) * hankelPsiR c f v :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hI_m0 le_rfl (by linarith) (by linarith)) (hI_m0 (by linarith) hnegRl_le_uT (by linarith))).symm
  unfold hankelBootMoment
  rw [hsplit]
  rw [eL] at hlow_int
  rw [eM] at hmain_int
  nlinarith [hlow_int, hmain_int, mul_nonneg (by linarith : (0 : ℝ) ≤ -u_T) hr, hr]

/-- **Mid piece** (`line_mid_and_rightW`, first half): on `[u_T, 1]`, `∫_{-A}^{A} |Re Ψ̃| ≤ 1 + 2 A r_∞` replaces
`∫‖Ψ̃‖ ≤ 1`. -/
theorem hankelBoot_line_mid {c ε T u_T R ℓ : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T) (hR10 : 10 ≤ R)
    (hRA : R + 1 ≤ langerRadius c) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1 / 2) (k : ℕ)
    (hkR : (k : ℝ) ≤ R / 5) :
    -(∫ v in u_T..(1 : ℝ), (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v)
    ≤ 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R * (1 + 2 * langerRadius c * hankelRinf c) := by
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have hR_pos : 0 < R := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hcont := continuousOn_hankelPsiR hc0 hfe
  have hA : 0 < langerRadius c := langerRadius_pos hc0
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hfe hε hM
  have hu_le1 : u_T ≤ 1 := by linarith
  have hsubA : Icc u_T (1 : ℝ) ⊆ Icc (-(langerRadius c)) (langerRadius c) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hWc : Continuous (fun v : ℝ => (1 + (v - ℓ) / R) ^ (k + 1)) :=
    (continuous_const.add ((continuous_id.sub continuous_const).div_const R)).pow (k + 1)
  have hi_w : IntervalIntegrable (fun v : ℝ => (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v)
      volume u_T 1 :=
    ((continuousOn_const.sub hWc.continuousOn).mul (hcont.mono hsubA)).intervalIntegrable_of_Icc hu_le1
  have hΨabs : IntervalIntegrable (fun v : ℝ => |hankelPsiR c f v|) volume u_T 1 :=
    (continuous_abs.comp_continuousOn (hcont.mono hsubA)).intervalIntegrable_of_Icc hu_le1
  have hC_nonneg : 0 ≤ 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R := by positivity
  have hpt : ∀ v ∈ Icc u_T (1 : ℝ),
      |(1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v| ≤
        4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R * |hankelPsiR c f v| := by
    intro v hv
    have hvl4 : |v - ℓ| ≤ 4 := abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hpow := abs_one_add_pow_sub_one_le ((v - ℓ) / R) (k + 1)
    have h_exp_65 : ((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R| ≤ 6 / 5 := by
      rw [abs_div, abs_of_pos hR_pos]
      have hk1_le : ((k + 1 : ℕ) : ℝ) ≤ R / 5 + 1 := by push_cast; linarith
      calc ((k + 1 : ℕ) : ℝ) * (|v - ℓ| / R) ≤ (R / 5 + 1) * (4 / R) := by gcongr
        _ = 4 / 5 + 4 / R := by field_simp [hR_pos.ne']
        _ ≤ 4 / 5 + 4 / 10 := by gcongr
        _ = 6 / 5 := by norm_num
    have hW_bd : |1 - (1 + (v - ℓ) / R) ^ (k + 1)| ≤ 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R := by
      rw [abs_sub_comm]
      calc |(1 + (v - ℓ) / R) ^ (k + 1) - 1|
          ≤ ((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R| * Real.exp (((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R|) := hpow
        _ ≤ ((k + 1 : ℕ) : ℝ) * (4 / R) * Real.exp (6 / 5) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (by positivity))
              (Real.exp_le_exp.mpr h_exp_65) (Real.exp_pos _).le (by positivity)
            rw [abs_div, abs_of_pos hR_pos]
            exact div_le_div_of_nonneg_right hvl4 hR_pos.le
        _ = 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R := by push_cast; ring
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hW_bd (abs_nonneg _)
  have hint_abs : |∫ v in u_T..(1 : ℝ), (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v| ≤
      ∫ v in u_T..(1 : ℝ), |(1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v| := by
    simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
      (f := fun v : ℝ => (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v) (μ := volume) hu_le1
  have hpt2 : (∫ v in u_T..(1 : ℝ), |(1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v|) ≤
      ∫ v in u_T..(1 : ℝ), 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R * |hankelPsiR c f v| :=
    intervalIntegral.integral_mono_on hu_le1 hi_w.abs (hΨabs.const_mul _) hpt
  have hfull : IntegrableOn (fun v : ℝ => |hankelPsiR c f v|) (Icc (-(langerRadius c)) (langerRadius c)) :=
    (continuous_abs.comp_continuousOn hcont).integrableOn_Icc
  have hL1 : (∫ v in u_T..(1 : ℝ), |hankelPsiR c f v|) ≤ 1 + 2 * langerRadius c * hankelRinf c := by
    have hsub : (∫ v in u_T..(1 : ℝ), |hankelPsiR c f v|) ≤
        ∫ v in (-(langerRadius c))..(langerRadius c), |hankelPsiR c f v| := by
      rw [intervalIntegral.integral_of_le hu_le1,
        intervalIntegral.integral_of_le (by linarith [hA])]
      exact setIntegral_mono_set (hfull.mono_set Ioc_subset_Icc_self)
        (Eventually.of_forall fun _ => abs_nonneg _)
        (Eventually.of_forall (Ioc_subset_Ioc (by linarith) (by linarith)))
    exact hsub.trans (hankel_psi_abs_mass hc5 hfe hε hM)
  calc -(∫ v in u_T..(1 : ℝ), (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v)
      ≤ |∫ v in u_T..(1 : ℝ), (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v| :=
        neg_le_abs _
    _ ≤ ∫ v in u_T..(1 : ℝ), |(1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v| := hint_abs
    _ ≤ ∫ v in u_T..(1 : ℝ), 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R * |hankelPsiR c f v| := hpt2
    _ = 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R * ∫ v in u_T..(1 : ℝ), |hankelPsiR c f v| :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R * (1 + 2 * langerRadius c * hankelRinf c) :=
        mul_le_mul_of_nonneg_left hL1 hC_nonneg

/-- **Right piece** (`line_mid_and_rightW`, second half): on `[1, R + ℓ]`, with the envelope `hankelPsi_envelope`. -/
theorem hankelBoot_line_right {c ε T u_T R ℓ : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T) (hR10 : 10 ≤ R)
    (hRA : R + 1 ≤ langerRadius c) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1 / 2) (k : ℕ)
    (hkR : (k : ℝ) ≤ R / 5) :
    -(∫ v in (1 : ℝ)..(R + ℓ), (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v)
    ≤ 120 * ((k : ℝ) + 1) / R := by
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have hR_pos : 0 < R := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hcont := continuousOn_hankelPsiR hc0 hfe
  have hA : 0 < langerRadius c := langerRadius_pos hc0
  have h1R : (1 : ℝ) ≤ R + ℓ := by linarith
  have hsubA : Icc (1 : ℝ) (R + ℓ) ⊆ Icc (-(langerRadius c)) (langerRadius c) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hWc : Continuous (fun v : ℝ => (1 + (v - ℓ) / R) ^ (k + 1)) :=
    (continuous_const.add ((continuous_id.sub continuous_const).div_const R)).pow (k + 1)
  have hi_w : IntervalIntegrable (fun v : ℝ => (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v)
      volume 1 (R + ℓ) :=
    ((continuousOn_const.sub hWc.continuousOn).mul (hcont.mono hsubA)).intervalIntegrable_of_Icc h1R
  have hpt : ∀ v ∈ Icc (1 : ℝ) (R + ℓ),
      |(1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v| ≤
        60 * (((k : ℝ) + 1) / R) * Real.exp (-(8 / 15 : ℝ) * v) := by
    intro v hv
    have hv1 : 1 ≤ v := hv.1
    have hvA : v ≤ langerRadius c := by linarith [hv.2]
    have hΨb := hankelBoot_psi_real_env hc hfe hε hM hv1 hvA
    have hv_pos : 0 < v := by linarith
    have hvl : |v - ℓ| ≤ v := abs_le.mpr ⟨by linarith, by linarith⟩
    have hpow := abs_one_add_pow_sub_one_le ((v - ℓ) / R) (k + 1)
    have h_exp_310 : ((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R| ≤ (3 / 10 : ℝ) * v := by
      rw [abs_div, abs_of_pos hR_pos]
      have hk1R : ((k + 1 : ℕ) : ℝ) / R ≤ 3 / 10 := by
        push_cast; rw [div_le_iff₀ hR_pos]; linarith
      calc ((k + 1 : ℕ) : ℝ) * (|v - ℓ| / R) = (((k + 1 : ℕ) : ℝ) / R) * |v - ℓ| := by ring
        _ ≤ (3 / 10 : ℝ) * v := mul_le_mul hk1R hvl (abs_nonneg _) (by norm_num)
    have hW_bd : |1 - (1 + (v - ℓ) / R) ^ (k + 1)| ≤
        (((k : ℝ) + 1) / R) * v * Real.exp ((3 / 10 : ℝ) * v) := by
      rw [abs_sub_comm]
      calc |(1 + (v - ℓ) / R) ^ (k + 1) - 1|
          ≤ ((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R| * Real.exp (((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R|) := hpow
        _ ≤ (((k + 1 : ℕ) : ℝ) * (v / R)) * Real.exp ((3 / 10 : ℝ) * v) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (by positivity))
              (Real.exp_le_exp.mpr h_exp_310) (Real.exp_pos _).le (by positivity)
            rw [abs_div, abs_of_pos hR_pos]
            exact div_le_div_of_nonneg_right hvl hR_pos.le
        _ = (((k : ℝ) + 1) / R) * v * Real.exp ((3 / 10 : ℝ) * v) := by push_cast; ring
    have hexp_eq : Real.exp ((3 / 10 : ℝ) * v) * Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ)) =
        Real.exp ((3 / 10 : ℝ) * v - (4 / 3 : ℝ) * v ^ (3 / 2 : ℝ)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc |(1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v|
        = |1 - (1 + (v - ℓ) / R) ^ (k + 1)| * |hankelPsiR c f v| := abs_mul _ _
      _ ≤ ((((k : ℝ) + 1) / R) * v * Real.exp ((3 / 10 : ℝ) * v)) *
            (60 * Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ))) :=
          mul_le_mul hW_bd hΨb (abs_nonneg _) (by positivity)
      _ = (60 * (((k : ℝ) + 1) / R)) *
            (v * Real.exp ((3 / 10 : ℝ) * v - (4 / 3 : ℝ) * v ^ (3 / 2 : ℝ))) := by
          rw [← hexp_eq]; ring
      _ ≤ (60 * (((k : ℝ) + 1) / R)) * Real.exp (-(8 / 15 : ℝ) * v) :=
          mul_le_mul_of_nonneg_left (hankelBoot_exp_right hv1) (by positivity)
      _ = 60 * (((k : ℝ) + 1) / R) * Real.exp (-(8 / 15 : ℝ) * v) := rfl
  have hint_abs : |∫ v in (1 : ℝ)..(R + ℓ), (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v| ≤
      ∫ v in (1 : ℝ)..(R + ℓ), |(1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v| := by
    simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
      (f := fun v : ℝ => (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v) (μ := volume) h1R
  have hmono : (∫ v in (1 : ℝ)..(R + ℓ), |(1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v|) ≤
      ∫ v in (1 : ℝ)..(R + ℓ), 60 * (((k : ℝ) + 1) / R) * Real.exp (-(8 / 15 : ℝ) * v) :=
    intervalIntegral.integral_mono_on h1R hi_w.abs
      ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable
        1 (R + ℓ)) hpt
  have hK0 : 0 ≤ 60 * (((k : ℝ) + 1) / R) := by positivity
  calc -(∫ v in (1 : ℝ)..(R + ℓ), (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v)
      ≤ |∫ v in (1 : ℝ)..(R + ℓ), (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v| :=
        neg_le_abs _
    _ ≤ ∫ v in (1 : ℝ)..(R + ℓ), |(1 - (1 + (v - ℓ) / R) ^ (k + 1)) * hankelPsiR c f v| := hint_abs
    _ ≤ ∫ v in (1 : ℝ)..(R + ℓ), 60 * (((k : ℝ) + 1) / R) * Real.exp (-(8 / 15 : ℝ) * v) := hmono
    _ ≤ 2 * (60 * (((k : ℝ) + 1) / R)) := hankelBoot_exp_int_le hK0 h1R
    _ = 120 * ((k : ℝ) + 1) / R := by ring

/-- **Positive tail** (`h_pos_tail` transcribed): `-∫_{R+ℓ}^{A} Re Ψ̃ ≤ (6/5) 60 e^{-(5/6) R}`. -/
theorem hankelBoot_line_tail {c ε T u_T R ℓ : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T) (hR10 : 10 ≤ R)
    (hRA : R + 1 ≤ langerRadius c) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1 / 2) (k : ℕ) :
    -(∫ v in (R + ℓ)..(langerRadius c), hankelPsiR c f v)
    ≤ (6 / 5 : ℝ) * 60 * Real.exp (-(5 / 6 : ℝ) * R) := by
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hcont := continuousOn_hankelPsiR hc0 hfe
  have hA : 0 < langerRadius c := langerRadius_pos hc0
  have hab : R + ℓ ≤ langerRadius c := by linarith
  have hsubA : Icc (R + ℓ) (langerRadius c) ⊆ Icc (-(langerRadius c)) (langerRadius c) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hΨi : IntervalIntegrable (hankelPsiR c f) volume (R + ℓ) (langerRadius c) :=
    (hcont.mono hsubA).intervalIntegrable_of_Icc hab
  have hpt : ∀ v ∈ Icc (R + ℓ) (langerRadius c),
      -hankelPsiR c f v ≤ 60 * Real.exp (-(5 / 6 : ℝ) * v) := by
    intro v hv
    have hv1 : 1 ≤ v := by linarith [hv.1]
    have hb := hankelBoot_psi_real_env hc hfe hε hM hv1 hv.2
    have hv32 : v ≤ v ^ (3 / 2 : ℝ) := by
      conv_lhs => rw [← Real.rpow_one v]
      exact Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
    have hex : Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ)) ≤ Real.exp (-(5 / 6 : ℝ) * v) :=
      Real.exp_le_exp.mpr (by linarith)
    have habs : -hankelPsiR c f v ≤ |hankelPsiR c f v| := neg_le_abs _
    linarith [mul_le_mul_of_nonneg_left hex (by norm_num : (0 : ℝ) ≤ 60)]
  calc -(∫ v in (R + ℓ)..(langerRadius c), hankelPsiR c f v)
      = ∫ v in (R + ℓ)..(langerRadius c), -hankelPsiR c f v := (intervalIntegral.integral_neg).symm
    _ ≤ ∫ v in (R + ℓ)..(langerRadius c), 60 * Real.exp (-(5 / 6 : ℝ) * v) :=
        intervalIntegral.integral_mono_on hab hΨi.neg
          ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable
            _ _) hpt
    _ ≤ 72 * Real.exp (-(5 / 6 : ℝ) * R) := hankelBoot_gauss_tail_int (by linarith) hab
    _ = (6 / 5 : ℝ) * 60 * Real.exp (-(5 / 6 : ℝ) * R) := by ring

/-- **Tail coefficient** (`h_pos_tail_R` transcribed): for `5 ≤ k` and `R ≥ 10`, `(6/5) 60 e^{-(5/6)R} ≤ 60 (k+1)/R`. -/
theorem hankelBoot_tail_le_coeff {R : ℝ} (hR10 : 10 ≤ R) {k : ℕ} (hk5 : 5 ≤ k) :
    (6 / 5 : ℝ) * 60 * Real.exp (-(5 / 6 : ℝ) * R) ≤ 60 * ((k : ℝ) + 1) / R := by
  have hR_pos : 0 < R := by linarith
  have hk : (5 : ℝ) ≤ k := by exact_mod_cast hk5
  have hexp1 : 1 + (5 / 6 : ℝ) * R ≤ Real.exp ((5 / 6 : ℝ) * R) := by
    linarith [Real.add_one_le_exp ((5 / 6 : ℝ) * R)]
  have hprod : Real.exp (-(5 / 6 : ℝ) * R) * (1 + (5 / 6 : ℝ) * R) ≤ 1 := by
    have hmul : Real.exp (-(5 / 6 : ℝ) * R) * Real.exp ((5 / 6 : ℝ) * R) = 1 := by
      rw [← Real.exp_add]; simp
    calc Real.exp (-(5 / 6 : ℝ) * R) * (1 + (5 / 6 : ℝ) * R)
        ≤ Real.exp (-(5 / 6 : ℝ) * R) * Real.exp ((5 / 6 : ℝ) * R) :=
          mul_le_mul_of_nonneg_left hexp1 (Real.exp_pos _).le
      _ = 1 := hmul
  have he := Real.exp_pos (-(5 / 6 : ℝ) * R)
  rw [le_div_iff₀ hR_pos]
  nlinarith [hprod, he, hk]

/-! Pinned guards: each declaration above depends only on the three standard foundations. -/

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_weight_pt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_weight_pt

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_weight_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_weight_integral

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_psi_real_env' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_psi_real_env

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_exp_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_exp_right

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_exp_int_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_exp_int_le

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_gauss_tail_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_gauss_tail_int

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_line_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_line_band

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_line_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_line_mid

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_line_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_line_right

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_line_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_line_tail

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_tail_le_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_tail_le_coeff

end FormalResearch.SignUncertainty
