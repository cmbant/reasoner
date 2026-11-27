module

public import FormalResearch.SignUncertainty.CeLiftAssembly
public import FormalResearch.SignUncertainty.GenRationalO6Family
public import FormalResearch.SignUncertainty.ConvSourceFamily
public import FormalResearch.SignUncertainty.MiddleBandPositivityDual
public import FormalResearch.SignUncertainty.CeShiftedLiftDefs

/-!
# Window negativity and Mellin–`hbS` estimates for `ce_twoEdge_lift`

Shared analytic helpers (`o6DualEst_const_mul`, quadratic log/exp estimates, `hbS_near_shell`,
`hbS_tail_lower`, `airySeedG0_neg_ray_full_le`, `scaled_witness_neg_iff`, `window_e5_pos_of_floor`)
and the compact-window negativity theorem `shifted_compact_window_neg`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

lemma o6DualEst_const_mul {m : ℕ} {D : ℝ → ℝ → ℝ → ℝ} (hD : O6DualEst m D)
    {lam : ℝ} (hlam : 0 < lam) : O6DualEst m (fun K c u => lam * D K c u) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨C, hC, he3⟩ := hD.e3
    refine ⟨lam * C, mul_pos hlam hC, fun {K c ξ} hδ hc hξ hS => ?_⟩
    rw [iDual_const_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam.le]
    calc lam * ‖iDual (D K c) (ceBeta1 * K * liftEps c / 2) m c ξ‖
        ≤ lam * (C * ξ⁻¹ * (1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) * c⁻¹ *
            min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ)))
              (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left (he3 hδ hc hξ hS) hlam.le
      _ = _ := by ring
  · intro Sw
    obtain ⟨C, hC, he5⟩ := hD.e5 Sw
    refine ⟨lam * C, mul_pos hlam hC, fun {K c ξ} hK hc hξ hSw => ?_⟩
    rw [iDual_const_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam.le]
    calc lam * ‖iDual (D K c) (ceBeta1 * K * liftEps c / 2) m c ξ‖
        ≤ lam * (C * ξ⁻¹ * c ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left (he5 hK hc hξ hSw) hlam.le
      _ = (lam * C) * ξ⁻¹ * c ^ (-(1 / 2 : ℝ)) := by ring

lemma abs_log_one_add_sub_le {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |Real.log (1 + t) - t| ≤ 2 * t ^ 2 := by
  have h1 : |-t| < 1 := by rw [abs_neg]; linarith
  have hser := Real.abs_log_sub_add_sum_range_le h1 1
  simp only [Finset.sum_range_one, pow_one, Nat.cast_zero, zero_add, div_one, sub_neg_eq_add,
    abs_neg, show (1 : ℕ) + 1 = 2 by rfl] at hser
  have hden : 1 / 2 ≤ 1 - |t| := by linarith
  rw [add_comm, ← sub_eq_add_neg, sq_abs] at hser
  calc |Real.log (1 + t) - t|
      ≤ t ^ 2 / (1 - |t|) := hser
    _ ≤ t ^ 2 / (1 / 2) := div_le_div_of_nonneg_left (sq_nonneg t) (by norm_num) hden
    _ = 2 * t ^ 2 := by ring

lemma exp_le_quad_of_abs_le_one {y : ℝ} (hy : |y| ≤ 1) :
    Real.exp y ≤ 1 + y + 2 * y ^ 2 := by
  have hb := Real.exp_bound (x := y) hy (n := 2) (by norm_num)
  have hsum : (∑ m ∈ Finset.range 2, y ^ m / (Nat.factorial m : ℝ)) = 1 + y := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  rw [hsum] at hb
  have hfac : |y| ^ 2 * (((2 : ℕ).succ : ℝ) / ((Nat.factorial 2 : ℝ) * (2 : ℝ))) ≤ 2 * y ^ 2 := by
    rw [sq_abs]
    norm_num
    nlinarith [sq_nonneg y]
  linarith [(abs_sub_le_iff.mp hb).1, hfac]

lemma airySeedG0_re_continuous : Continuous (fun u : ℝ => (airySeedG 0 (u : ℂ)).re) := by
  rw [airySeedG0_eq_ceG1]
  exact continuous_ceG1 (airyZero 1)

private lemma airySeedG0_neg_ray_le_local :
    ∃ R_g C_g : ℝ, 5 ≤ R_g ∧ 0 < C_g ∧
      ∀ u : ℝ, u ≤ -R_g →
        (airySeedG 0 (u : ℂ)).re ≤ C_g * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨R₀, K₀, hR5, hK0, hwkb⟩ := (hasGenRationalAiryCoeffs_airySeedG 0).neg_axis_wkb
  refine ⟨R₀, (2 : ℝ) ^ (3 / 2 : ℝ) * (K₀ + 1) / Real.pi, hR5, by positivity, fun u hu => ?_⟩
  let x : ℝ := -u
  have hxR : R₀ ≤ x := by dsimp [x]; linarith
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hw := hwkb x hxR
  simp only [zero_mul, add_zero, sub_zero] at hw
  have hxw : Real.pi * x ^ (3 / 2 : ℝ) * (airySeedG 0 (u : ℂ)).re ≤ K₀ + 1 := by
    have h1 : K₀ * x ^ (-(1 / 2 : ℝ)) ≤ K₀ :=
      mul_le_of_le_one_right hK0 (Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num))
    have h2 : Real.pi * x ^ (3 / 2 : ℝ) * (airySeedG 0 ((-x : ℝ) : ℂ)).re ≤ K₀ * x ^ (-(1 / 2 : ℝ)) :=
      (abs_le.mp hw).2
    have hux : ((-x : ℝ) : ℂ) = (u : ℂ) := by dsimp [x]; simp
    rw [hux] at h2
    linarith
  have hgu : (airySeedG 0 (u : ℂ)).re ≤ ((K₀ + 1) / Real.pi) * x ^ (-(3 / 2 : ℝ)) := by
    have hinv_p : Real.pi⁻¹ * Real.pi = 1 := inv_mul_cancel₀ hpi0.ne'
    have hinv_x : x ^ (-(3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add hx0]; simp
    calc (airySeedG 0 (u : ℂ)).re
        = (Real.pi * x ^ (3 / 2 : ℝ) * (airySeedG 0 (u : ℂ)).re) * (Real.pi⁻¹ * x ^ (-(3 / 2 : ℝ))) := by
            calc (airySeedG 0 (u : ℂ)).re
                = 1 * 1 * (airySeedG 0 (u : ℂ)).re := by ring
              _ = (Real.pi⁻¹ * Real.pi) * (x ^ (-(3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ)) *
                    (airySeedG 0 (u : ℂ)).re := by rw [hinv_p, hinv_x]
              _ = (Real.pi * x ^ (3 / 2 : ℝ) * (airySeedG 0 (u : ℂ)).re) *
                    (Real.pi⁻¹ * x ^ (-(3 / 2 : ℝ))) := by ring
      _ ≤ (K₀ + 1) * (Real.pi⁻¹ * x ^ (-(3 / 2 : ℝ))) := mul_le_mul_of_nonneg_right hxw (by positivity)
      _ = ((K₀ + 1) / Real.pi) * x ^ (-(3 / 2 : ℝ)) := by ring
  have h1u : 0 < 1 + |u| := by linarith [abs_nonneg u]
  have h1x : 1 + |u| ≤ 2 * x := by
    rw [abs_of_neg (by linarith : u < 0)]
    change 1 + x ≤ 2 * x; linarith
  have hrpow : x ^ (-(3 / 2 : ℝ)) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by
    have hle := Real.rpow_le_rpow_of_nonpos h1u h1x (by norm_num : -(3 / 2 : ℝ) ≤ 0)
    rw [Real.mul_rpow (by norm_num) hx0.le] at hle
    calc x ^ (-(3 / 2 : ℝ))
        = (2 : ℝ) ^ (3 / 2 : ℝ) * ((2 : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (-(3 / 2 : ℝ))) := by
            rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; simp
      _ ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * (1 + |u|) ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
  calc (airySeedG 0 (u : ℂ)).re ≤ ((K₀ + 1) / Real.pi) * x ^ (-(3 / 2 : ℝ)) := hgu
    _ ≤ ((K₀ + 1) / Real.pi) * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 + |u|) ^ (-(3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hrpow (by positivity)
    _ = ((2 : ℝ) ^ (3 / 2 : ℝ) * (K₀ + 1) / Real.pi) * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by ring

lemma integrableOn_bspline_const {m : ℕ} (hm : 1 ≤ m) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (C : ℝ) :
    IntegrableOn (fun t : ℝ => C * bspline m δ₀ t) (Icc 0 δ₀) := by
  refine IntegrableOn.of_bound measure_Icc_lt_top
    ((bspline_aestronglyMeasurable m hδ₀).const_mul C).restrict (|C| * (m / δ₀)) ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (bspline_nonneg m hδ₀ t)]
  exact mul_le_mul_of_nonneg_left (bspline_le hm hδ₀ t) (abs_nonneg C)

lemma integrableOn_continuous_shift_bspline {m : ℕ} (hm : 1 ≤ m) {δ₀ x : ℝ} (hδ₀ : 0 < δ₀)
    {F : ℝ → ℝ} (hF : Continuous F) :
    IntegrableOn (fun t : ℝ => F (-x + t) * bspline m δ₀ t) (Icc 0 δ₀) := by
  have h1 : IntegrableOn (fun t : ℝ => F (-x + t)) (Icc 0 δ₀) :=
    (hF.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_Icc
  have h2 : IntegrableOn (fun t : ℝ => bspline m δ₀ t * F (-x + t)) (Icc 0 δ₀) :=
    h1.bdd_mul (bspline_aestronglyMeasurable m hδ₀).restrict
      (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (bspline_nonneg m hδ₀ t)]
        exact bspline_le hm hδ₀ t)
  exact h2.congr_fun (fun _ _ => mul_comm _ _) measurableSet_Icc

lemma airySeedG0_neg_ray_full_le :
    ∃ C_g > (0 : ℝ), ∀ u : ℝ, u ≤ 0 →
      0 ≤ (airySeedG 0 (u : ℂ)).re ∧ (airySeedG 0 (u : ℂ)).re ≤ C_g * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨R_g, C_g_neg, hRg5, hCg_neg, hg_neg_le⟩ := airySeedG0_neg_ray_le_local
  have hne : (Icc (-R_g) 0).Nonempty := ⟨0, by linarith, le_rfl⟩
  obtain ⟨u_m, _, hu_m⟩ := isCompact_Icc.exists_isMaxOn hne airySeedG0_re_continuous.continuousOn
  let M_g : ℝ := max ((airySeedG 0 (u_m : ℂ)).re) 0
  let C_g : ℝ := max C_g_neg (M_g * (1 + R_g) ^ (3 / 2 : ℝ) + 1)
  have hCg0 : 0 < C_g := lt_of_lt_of_le hCg_neg (le_max_left _ _)
  refine ⟨C_g, hCg0, fun u hu => ⟨airySeedG_re_nonneg 0 u, ?_⟩⟩
  by_cases hle : u ≤ -R_g
  · exact (hg_neg_le u hle).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hu_mem : u ∈ Icc (-R_g) 0 := ⟨by linarith, hu⟩
    have hbd : (airySeedG 0 (u : ℂ)).re ≤ M_g := (hu_m hu_mem).trans (le_max_left _ _)
    have h1u : 1 + |u| ≤ 1 + R_g := by
      have habs : |u| ≤ R_g := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    have hrp : (1 + R_g) ^ (-(3 / 2 : ℝ)) ≤ (1 + |u|) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h1u (by norm_num)
    have hmul : (1 + R_g) ^ (3 / 2 : ℝ) * (1 + R_g) ^ (-(3 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add (by linarith), show (3 / 2 : ℝ) + -(3 / 2 : ℝ) = 0 by norm_num, Real.rpow_zero]
    calc (airySeedG 0 (u : ℂ)).re ≤ M_g * 1 := by linarith
      _ = M_g * ((1 + R_g) ^ (3 / 2 : ℝ) * (1 + R_g) ^ (-(3 / 2 : ℝ))) := by rw [hmul]
      _ = (M_g * (1 + R_g) ^ (3 / 2 : ℝ)) * (1 + R_g) ^ (-(3 / 2 : ℝ)) := by ring
      _ ≤ C_g * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by
          refine mul_le_mul ?_ hrp (by positivity) hCg0.le
          exact le_trans (by linarith) (le_max_right _ _)

lemma scaled_witness_neg_iff {X_base : ℂ → ℂ} {p γ θ lam K lam_β : ℝ}
    (hlamβ : 0 < lam_β) (W : CeTwoEdgeLiftWitness X_base p γ θ lam K)
    {c ξ : ℝ} (hc : W.c_min ≤ c) (hξ : 0 < ξ)
    (hpos : 0 < (iMain (fun u => (-lam_β) * ((X_base (u : ℂ)).re + liftEps c * W.α₁ c * (airySeedG 0 (u : ℂ)).re))
        (ceBeta1 * K * liftEps c / 2) 4 c ξ +
      iDual (fun u => (-lam_β) * convSourceFamily p γ θ lam c u)
        (ceBeta1 * K * liftEps c / 2) 4 c ξ).re) :
    (W.fp c (c * ξ) + W.fm c (c * ξ)) / 2 < 0 := by
  have hc2k : 2000 ≤ c := W.hc2k.trans hc
  have hc0 : 0 < c := by linarith
  have hphys := congrArg Complex.re (W.hphys_eq hc hξ)
  rw [Complex.ofReal_re] at hphys
  rw [iMain_const_mul (-lam_β), iDual_const_mul (-lam_β)] at hpos
  have hfac : (((-lam_β : ℝ) : ℂ) * iMain (fun u => (X_base (u : ℂ)).re + liftEps c * W.α₁ c * (airySeedG 0 (u : ℂ)).re)
      (ceBeta1 * K * liftEps c / 2) 4 c ξ +
    ((-lam_β : ℝ) : ℂ) * iDual (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) 4 c ξ).re =
      (-lam_β) * (c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * ((W.fp c (c * ξ) + W.fm c (c * ξ)) / 2)) := by
    have heq : ((-lam_β : ℝ) : ℂ) * iMain (fun u => (X_base (u : ℂ)).re + liftEps c * W.α₁ c * (airySeedG 0 (u : ℂ)).re)
        (ceBeta1 * K * liftEps c / 2) 4 c ξ +
      ((-lam_β : ℝ) : ℂ) * iDual (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) 4 c ξ =
        ((-lam_β : ℝ) : ℂ) * (iMain (fun u => (X_base (u : ℂ)).re + liftEps c * W.α₁ c * (airySeedG 0 (u : ℂ)).re)
          (ceBeta1 * K * liftEps c / 2) 4 c ξ +
          iDual (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) 4 c ξ) := by ring
    rw [heq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hphys]
  rw [hfac] at hpos
  have hpre : 0 < lam_β * (c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ)) :=
    mul_pos hlamβ (mul_pos (Real.rpow_pos_of_pos hc0 _) (hankelRho0_pos hc0 (mul_pos hc0 hξ)))
  nlinarith

lemma hbS_near_shell {B_t R_off t r c : ℝ} (_hBt : 0 ≤ B_t) (_hR : 0 ≤ R_off)
    (ht : |t| ≤ B_t) (hr : |r| ≤ R_off) (hc2 : 2 ≤ c)
    (hΔ_lo : c / (2 * Real.pi ^ 2) ≤ c / Real.pi ^ 2 - (t / ceBeta1) * c ^ (1 / 3 : ℝ) + r)
    (hy_half : Real.pi ^ 2 * (B_t / ceBeta1 * liftEps c ^ 2 + R_off * liftEps c ^ 3) ≤ 1 / 2) :
    let Δ := c / Real.pi ^ 2 - (t / ceBeta1) * c ^ (1 / 3 : ℝ) + r
    let ξ := Δ / c
    0 < ξ ∧
      |ceBeta1 * hbS c ξ + t| ≤
        (ceBeta1 * R_off + 2 * ceBeta1 * Real.pi ^ 2 * (B_t / ceBeta1 + R_off) ^ 2) * liftEps c := by
  intro Δ ξ
  have hc0 : 0 < c := by linarith
  have hpi : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have hβ0 : 0 < ceBeta1 := ceBeta1_pos
  have hΔ_pos : 0 < Δ := lt_of_lt_of_le (by positivity) hΔ_lo
  have hξ_pos : 0 < ξ := div_pos hΔ_pos hc0
  refine ⟨hξ_pos, ?_⟩
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  have hε1 : liftEps c ≤ 1 := liftEps_le_one (by linarith)
  have hcube : liftEps c ^ 3 * c = 1 := liftEps_cube_mul hc0
  have hc13_div : c ^ (1 / 3 : ℝ) / c = liftEps c ^ 2 := by
    have hpow : c ^ (1 / 3 : ℝ) = liftEps c ^ 2 * c := by
      have hc_eq : c ^ (1 / 3 : ℝ) * liftEps c = 1 := by
        unfold liftEps
        rw [← Real.rpow_add hc0, show (1 / 3 : ℝ) + -(1 / 3 : ℝ) = 0 by norm_num, Real.rpow_zero]
      calc c ^ (1 / 3 : ℝ) = c ^ (1 / 3 : ℝ) * (liftEps c * (liftEps c ^ 2 * c)) := by
            have : liftEps c * (liftEps c ^ 2 * c) = 1 := by linarith [hcube]
            rw [this, mul_one]
        _ = (c ^ (1 / 3 : ℝ) * liftEps c) * (liftEps c ^ 2 * c) := by ring
        _ = liftEps c ^ 2 * c := by rw [hc_eq, one_mul]
    rw [hpow]; field_simp [hc0.ne']
  have hcinv : c⁻¹ = liftEps c ^ 3 := by
    field_simp [hc0.ne']; linarith [hcube]
  let y : ℝ := Real.pi ^ 2 * ((-t / ceBeta1) * liftEps c ^ 2 + r * liftEps c ^ 3)
  have hpi_ξ : Real.pi ^ 2 * ξ = 1 + y := by
    have : Real.pi ^ 2 * ξ = 1 - Real.pi ^ 2 * (t / ceBeta1) * (c ^ (1 / 3 : ℝ) / c) + Real.pi ^ 2 * r * c⁻¹ := by
      dsimp [ξ, Δ]; field_simp [hc0.ne']
    rw [this, hc13_div, hcinv]
    dsimp [y]; ring
  have hy_bd : |y| ≤ Real.pi ^ 2 * (B_t / ceBeta1 * liftEps c ^ 2 + R_off * liftEps c ^ 3) := by
    dsimp [y]
    rw [abs_mul, abs_of_pos hpi]
    refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) hpi.le
    rw [abs_mul, abs_div, abs_neg, abs_of_pos hβ0, abs_of_nonneg (sq_nonneg (liftEps c)),
      abs_mul, abs_of_nonneg (pow_nonneg hε0.le 3)]
    exact add_le_add
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ht hβ0.le) (sq_nonneg _))
      (mul_le_mul_of_nonneg_right hr (pow_nonneg hε0.le 3))
  have hy_h : |y| ≤ 1 / 2 := hy_bd.trans hy_half
  have hhb : ceBeta1 * hbS c ξ + t =
      ceBeta1 * (Real.log (1 + y) - y) / (Real.pi ^ 2 * liftEps c ^ 2) + ceBeta1 * r * liftEps c := by
    unfold hbS
    rw [hpi_ξ]
    have hlog : Real.log (1 + y) = (Real.log (1 + y) - y) + y := by ring
    rw [hlog]
    dsimp [y]
    have hb_ne : ceBeta1 ≠ 0 := hβ0.ne'
    have hpi_ne : Real.pi ^ 2 ≠ 0 := hpi.ne'
    have hε_ne : liftEps c ≠ 0 := hε0.ne'
    field_simp
    ring
  rw [hhb]
  have hy_sq : |y| ≤ Real.pi ^ 2 * (B_t / ceBeta1 + R_off) * liftEps c ^ 2 := by
    refine hy_bd.trans ?_
    have hε3_le : liftEps c ^ 3 ≤ liftEps c ^ 2 := by nlinarith [hε0, hε1]
    calc Real.pi ^ 2 * (B_t / ceBeta1 * liftEps c ^ 2 + R_off * liftEps c ^ 3)
        ≤ Real.pi ^ 2 * (B_t / ceBeta1 * liftEps c ^ 2 + R_off * liftEps c ^ 2) := by gcongr
      _ = Real.pi ^ 2 * (B_t / ceBeta1 + R_off) * liftEps c ^ 2 := by ring
  have hlog_err : |Real.log (1 + y) - y| ≤ 2 * (Real.pi ^ 2 * (B_t / ceBeta1 + R_off)) ^ 2 * liftEps c ^ 4 := by
    have h1 := abs_log_one_add_sub_le hy_h
    have h2 : y ^ 2 ≤ (Real.pi ^ 2 * (B_t / ceBeta1 + R_off) * liftEps c ^ 2) ^ 2 := by
      rw [← sq_abs y]
      exact pow_le_pow_left₀ (abs_nonneg _) hy_sq 2
    calc |Real.log (1 + y) - y| ≤ 2 * y ^ 2 := h1
      _ ≤ 2 * (Real.pi ^ 2 * (B_t / ceBeta1 + R_off) * liftEps c ^ 2) ^ 2 := by gcongr
      _ = 2 * (Real.pi ^ 2 * (B_t / ceBeta1 + R_off)) ^ 2 * liftEps c ^ 4 := by ring
  have hterm1 : |ceBeta1 * (Real.log (1 + y) - y) / (Real.pi ^ 2 * liftEps c ^ 2)| ≤
      2 * ceBeta1 * Real.pi ^ 2 * (B_t / ceBeta1 + R_off) ^ 2 * liftEps c ^ 2 := by
    rw [abs_div, abs_mul, abs_of_pos hβ0, abs_of_pos (mul_pos hpi (sq_pos_of_pos hε0))]
    calc ceBeta1 * |Real.log (1 + y) - y| / (Real.pi ^ 2 * liftEps c ^ 2)
        ≤ ceBeta1 * (2 * (Real.pi ^ 2 * (B_t / ceBeta1 + R_off)) ^ 2 * liftEps c ^ 4) / (Real.pi ^ 2 * liftEps c ^ 2) := by
          gcongr
      _ = 2 * ceBeta1 * Real.pi ^ 2 * (B_t / ceBeta1 + R_off) ^ 2 * liftEps c ^ 2 := by
          have hpi_ne : Real.pi ^ 2 ≠ 0 := hpi.ne'
          have hε_ne : liftEps c ≠ 0 := hε0.ne'
          field_simp
  have hterm2 : |ceBeta1 * r * liftEps c| ≤ ceBeta1 * R_off * liftEps c := by
    rw [abs_mul, abs_mul, abs_of_pos hβ0, abs_of_pos hε0]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hβ0.le) hε0.le
  have hε2_le : liftEps c ^ 2 ≤ liftEps c := by nlinarith [hε0, hε1]
  have hterm1' : 2 * ceBeta1 * Real.pi ^ 2 * (B_t / ceBeta1 + R_off) ^ 2 * liftEps c ^ 2 ≤
      2 * ceBeta1 * Real.pi ^ 2 * (B_t / ceBeta1 + R_off) ^ 2 * liftEps c :=
    mul_le_mul_of_nonneg_left hε2_le (by positivity)
  calc |ceBeta1 * (Real.log (1 + y) - y) / (Real.pi ^ 2 * liftEps c ^ 2) + ceBeta1 * r * liftEps c|
      ≤ |ceBeta1 * (Real.log (1 + y) - y) / (Real.pi ^ 2 * liftEps c ^ 2)| + |ceBeta1 * r * liftEps c| :=
        abs_add_le _ _
    _ ≤ 2 * ceBeta1 * Real.pi ^ 2 * (B_t / ceBeta1 + R_off) ^ 2 * liftEps c + ceBeta1 * R_off * liftEps c :=
        add_le_add (hterm1.trans hterm1') hterm2
    _ = _ := by ring

lemma hbS_tail_lower {u_star η_tail c Δ : ℝ} (hη : 0 < η_tail) (hc2 : 2 ≤ c)
    (hy_half : Real.pi ^ 2 * ((|u_star| / ceBeta1) * liftEps c ^ 2 + η_tail * liftEps c ^ 3) ≤ 1 / 2)
    (hquad : 2 * Real.pi ^ 2 * liftEps c * (|u_star| / ceBeta1 + η_tail) ^ 2 ≤ 1)
    (hΔ : c / Real.pi ^ 2 - (u_star / ceBeta1) * c ^ (1 / 3 : ℝ) + (η_tail + 1) ≤ Δ) :
    0 < Δ ∧ (-u_star / ceBeta1 + η_tail * liftEps c ≤ hbS c (Δ / c)) := by
  have hc0 : 0 < c := by linarith
  have hpi : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have hβ0 : 0 < ceBeta1 := ceBeta1_pos
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  have hε1 : liftEps c ≤ 1 := liftEps_le_one (by linarith)
  have hcube : liftEps c ^ 3 * c = 1 := liftEps_cube_mul hc0
  have hc23_mul : liftEps c ^ 2 * c ^ (2 / 3 : ℝ) = 1 := by
    unfold liftEps; rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; norm_num
  have hc13_eq : c ^ (1 / 3 : ℝ) = liftEps c ^ 2 * c := by
    calc c ^ (1 / 3 : ℝ) = c ^ (1 / 3 : ℝ) * (liftEps c ^ 2 * c ^ (2 / 3 : ℝ)) := by rw [hc23_mul, mul_one]
      _ = liftEps c ^ 2 * (c ^ (1 / 3 : ℝ) * c ^ (2 / 3 : ℝ)) := by ring
      _ = liftEps c ^ 2 * c := by
          rw [← Real.rpow_add hc0, show (1 / 3 : ℝ) + 2 / 3 = 1 by norm_num, Real.rpow_one]
  let y : ℝ := -Real.pi ^ 2 * (u_star / ceBeta1) * liftEps c ^ 2 + Real.pi ^ 2 * η_tail * liftEps c ^ 3
  have hy_bd : |y| ≤ Real.pi ^ 2 * ((|u_star| / ceBeta1) * liftEps c ^ 2 + η_tail * liftEps c ^ 3) := by
    dsimp [y]
    calc |(-Real.pi ^ 2 * (u_star / ceBeta1) * liftEps c ^ 2) + Real.pi ^ 2 * η_tail * liftEps c ^ 3|
        ≤ |-Real.pi ^ 2 * (u_star / ceBeta1) * liftEps c ^ 2| + |Real.pi ^ 2 * η_tail * liftEps c ^ 3| :=
          abs_add_le _ _
      _ = Real.pi ^ 2 * ((|u_star| / ceBeta1) * liftEps c ^ 2 + η_tail * liftEps c ^ 3) := by
          rw [abs_mul, abs_mul, abs_neg, abs_of_pos hpi, abs_div, abs_of_pos hβ0,
            abs_of_nonneg (sq_nonneg (liftEps c)), abs_mul, abs_mul, abs_of_pos hpi, abs_of_pos hη,
            abs_of_nonneg (pow_nonneg hε0.le 3)]
          ring
  have hy1 : |y| ≤ 1 := (hy_bd.trans hy_half).trans (by norm_num)
  have hexp := exp_le_quad_of_abs_le_one hy1
  have hy_sq : y ^ 2 ≤ (Real.pi ^ 2 * (|u_star| / ceBeta1 + η_tail) * liftEps c ^ 2) ^ 2 := by
    rw [← sq_abs y]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    have hε3 : liftEps c ^ 3 ≤ liftEps c ^ 2 := by nlinarith only [hε0, hε1]
    exact hy_bd.trans (by
      calc Real.pi ^ 2 * ((|u_star| / ceBeta1) * liftEps c ^ 2 + η_tail * liftEps c ^ 3)
          ≤ Real.pi ^ 2 * ((|u_star| / ceBeta1) * liftEps c ^ 2 + η_tail * liftEps c ^ 2) :=
            mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hε3 hη.le) _) hpi.le
        _ = Real.pi ^ 2 * (|u_star| / ceBeta1 + η_tail) * liftEps c ^ 2 := by ring)
  have hc_eps4 : (c / Real.pi ^ 2) * (2 * y ^ 2) ≤ 1 := by
    have hc4_eq : c * liftEps c ^ 4 = liftEps c := by
      calc c * liftEps c ^ 4 = (liftEps c ^ 3 * c) * liftEps c := by ring
        _ = liftEps c := by rw [hcube, one_mul]
    calc (c / Real.pi ^ 2) * (2 * y ^ 2)
        ≤ (c / Real.pi ^ 2) * (2 * (Real.pi ^ 2 * (|u_star| / ceBeta1 + η_tail) * liftEps c ^ 2) ^ 2) := by gcongr
      _ = 2 * Real.pi ^ 2 * (c * liftEps c ^ 4) * (|u_star| / ceBeta1 + η_tail) ^ 2 := by
          field_simp [Real.pi_ne_zero]
      _ = 2 * Real.pi ^ 2 * liftEps c * (|u_star| / ceBeta1 + η_tail) ^ 2 := by rw [hc4_eq]
      _ ≤ 1 := hquad
  have h1y_main : (c / Real.pi ^ 2) * (1 + y) = c / Real.pi ^ 2 - (u_star / ceBeta1) * c ^ (1 / 3 : ℝ) + η_tail := by
    dsimp [y]
    rw [hc13_eq]
    have h1 : (c / Real.pi ^ 2) * (Real.pi ^ 2 * η_tail * liftEps c ^ 3) = η_tail := by
      have : (c / Real.pi ^ 2) * (Real.pi ^ 2 * η_tail * liftEps c ^ 3) = η_tail * (liftEps c ^ 3 * c) := by
        field_simp [Real.pi_ne_zero]
      rw [this, hcube, mul_one]
    have h2 : (c / Real.pi ^ 2) * (-Real.pi ^ 2 * (u_star / ceBeta1) * liftEps c ^ 2) =
        -(u_star / ceBeta1) * (liftEps c ^ 2 * c) := by
      field_simp [Real.pi_ne_zero]
    nlinarith only [h1, h2]
  have hmain : (c / Real.pi ^ 2) * Real.exp y ≤ Δ := by
    have hexp_mul : (c / Real.pi ^ 2) * Real.exp y ≤ (c / Real.pi ^ 2) * (1 + y + 2 * y ^ 2) :=
      mul_le_mul_of_nonneg_left hexp (div_nonneg hc0.le hpi.le)
    nlinarith only [hexp_mul, h1y_main, hc_eps4, hΔ]
  have hΔ_pos : 0 < Δ := lt_of_lt_of_le (mul_pos (div_pos hc0 hpi) (Real.exp_pos y)) hmain
  refine ⟨hΔ_pos, ?_⟩
  have hpi_ξ : Real.exp y ≤ Real.pi ^ 2 * (Δ / c) := by
    have h1 : Real.exp y ≤ Δ / (c / Real.pi ^ 2) := (le_div_iff₀' (div_pos hc0 hpi)).2 hmain
    exact h1.trans_eq (by field_simp [Real.pi_ne_zero, hc0.ne'])
  have hlog : y ≤ Real.log (Real.pi ^ 2 * (Δ / c)) := by
    rw [← Real.log_exp y]
    exact Real.log_le_log (Real.exp_pos y) hpi_ξ
  have hy_div : y / (Real.pi ^ 2 * liftEps c ^ 2) = -u_star / ceBeta1 + η_tail * liftEps c := by
    dsimp [y]
    have hpi_ne : Real.pi ^ 2 ≠ 0 := hpi.ne'
    have hε_ne : liftEps c ≠ 0 := hε0.ne'
    have hb_ne : ceBeta1 ≠ 0 := hβ0.ne'
    field_simp
  unfold hbS
  rw [← hy_div]
  exact div_le_div_of_nonneg_right hlog (mul_pos hpi (sq_pos_of_pos hε0)).le

lemma window_e5_pos_of_floor {X_base : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF_base : HasGenRationalAiryCoeffs X_base β₀₀ β₁₁)
    {p γ θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 ≤ γ) (hθ : 0 ≤ θ) (hlam : 0 < lam)
    {K : ℝ} (hK1 : 1 ≤ K) (W : CeTwoEdgeLiftWitness X_base p γ θ lam K)
    (lam_β Sw η_w : ℝ) (hlamβ : 0 < lam_β) (hηw : 0 < η_w) :
    ∃ c_e5 : ℝ, max 32768 W.c_min ≤ c_e5 ∧ ∀ {c ξ : ℝ}, c_e5 ≤ c → 0 < ξ → |hbS c ξ| ≤ Sw →
      (∀ t ∈ Icc (0 : ℝ) (ceBeta1 * K * liftEps c / 2),
        η_w * liftEps c ≤
          (-lam_β) * ((X_base ((-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs) + t : ℝ) : ℂ)).re +
            liftEps c * W.α₁ c * (airySeedG 0 ((-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs) + t : ℝ) : ℂ)).re)) →
      (W.fp c (c * ξ) + W.fm c (c * ξ)) / 2 < 0 := by
  let s₂ : Finset (Fin 2) := Finset.univ
  let B₂ : Fin 2 → ℂ → ℂ := fun i => if i = 0 then X_base else airySeedG 0
  let b₂₀ : Fin 2 → ℝ := fun i => if i = 0 then β₀₀ else 0
  let b₂₁ : Fin 2 → ℝ := fun i => if i = 0 then β₁₁ else 0
  let α_fn : Fin 2 → ℝ → ℝ → ℝ := fun i _ c =>
    if i = 0 then -lam_β else if W.c_min ≤ c then -lam_β * liftEps c * W.α₁ c else 0
  let F : ℝ → ℝ → ℝ → ℝ := fun K' c u => ∑ i ∈ s₂, α_fn i K' c * (B₂ i (u : ℂ)).re
  let β_inf : ℝ → ℝ → ℝ := fun K' c => ∑ i ∈ s₂, α_fn i K' c * (b₂₀ i + b₂₁ i)
  have hB₂ : ∀ i ∈ s₂, HasGenRationalAiryCoeffs (B₂ i) (b₂₀ i) (b₂₁ i) := fun i _ => by
    fin_cases i <;> [exact hF_base; exact hasGenRationalAiryCoeffs_airySeedG 0]
  have hR_pos : 0 ≤ max lam_β (lam_β * W.M_α) := by positivity
  have hα_bd : ∀ i ∈ s₂, ∀ K' c : ℝ, 1 ≤ K' → 2000 ≤ c → 8 * K' ^ 3 ≤ c → (K' / 1) ^ 3 ≤ c →
      |α_fn i K' c| ≤ max lam_β (lam_β * W.M_α) := fun i _ _ c _ hc2k _ _ => by
    have hε0 : 0 ≤ liftEps c := (liftEps_pos (by linarith)).le
    have hε1 : liftEps c ≤ 1 := liftEps_le_one (by linarith)
    fin_cases i
    · dsimp [α_fn]; rw [abs_neg, abs_of_pos hlamβ]; exact le_max_left _ _
    · dsimp [α_fn]; split_ifs with hc
      · have hα_pos : 0 ≤ W.α₁ c := W.hm_α.le.trans (W.hα₁_bd hc).1
        have hα_hi : W.α₁ c ≤ W.M_α := (W.hα₁_bd hc).2
        rw [abs_of_nonpos (by nlinarith [mul_nonneg hlamβ.le hε0])]
        calc -(-lam_β * liftEps c * W.α₁ c) = lam_β * (liftEps c * W.α₁ c) := by ring
          _ ≤ lam_β * (1 * W.M_α) := by gcongr
          _ ≤ max lam_β (lam_β * W.M_α) := by rw [one_mul]; exact le_max_right _ _
      · rw [abs_zero]; exact hR_pos
  have hEst := o6FamilyEst_of_genRational_family s₂ B₂ b₂₀ b₂₁ hB₂ α_fn
    (max lam_β (lam_β * W.M_α)) 1 hR_pos one_pos hα_bd (m := 4) (by norm_num)
  have hDE := o6DualEst_const_mul (convSourceFamily_dual hp hp1 hγ hθ hlam) hlamβ
  obtain ⟨C5, hC5, he5⟩ := hEst.e5 Sw
  obtain ⟨CD5, hCD5, hd5⟩ := hDE.e5 Sw
  let η_main : ℝ := ceK * ceBeta1 * η_w / Real.pi ^ 2
  have hη_main : 0 < η_main := by
    have := ceK_pos; have := ceBeta1_pos; positivity
  let C_err : ℝ := 2 * C5 + CD5
  have hC_err : 0 < C_err := by positivity
  let M_c : ℝ := 2 * C_err / η_main + 1
  let c_e5 : ℝ := max (max 32768 W.c_min) (M_c ^ 6)
  refine ⟨c_e5, le_max_left _ _, fun {c ξ} hc hξ hSw hfloor => ?_⟩
  have h32k : 32768 ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hc)
  have hc_min : W.c_min ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
  have hc8K : 8 * K ^ 3 ≤ c := W.hcK.trans hc_min
  have hc0 : 0 < c := by linarith
  have hcK1 : (K / 1) ^ 3 ≤ c := by
    calc (K / 1) ^ 3 = K ^ 3 := by ring
      _ ≤ 8 * K ^ 3 := by nlinarith [pow_pos (by linarith : 0 < K) 3]
      _ ≤ c := hc8K
  have hc_pow : M_c ^ 6 ≤ c := (le_max_right _ _).trans hc
  have hc_16 : M_c ≤ c ^ (1 / 6 : ℝ) := by
    have hM0 : 0 ≤ M_c := by positivity
    calc M_c = (M_c ^ 6) ^ (1 / 6 : ℝ) := by
          rw [← Real.rpow_natCast _ 6, ← Real.rpow_mul hM0]; norm_num
      _ ≤ c ^ (1 / 6 : ℝ) := Real.rpow_le_rpow (by positivity) hc_pow (by norm_num)
  have hc_neg16 : c ^ (-(1 / 6 : ℝ)) ≤ η_main / (2 * C_err) := by
    have hc16_pos : 0 < c ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hc0 _
    rw [Real.rpow_neg hc0.le, ← one_div, div_le_iff₀ hc16_pos]
    calc 1 = (η_main / (2 * C_err)) * (2 * C_err / η_main) := by field_simp [hη_main.ne', hC_err.ne']
      _ ≤ (η_main / (2 * C_err)) * M_c := by gcongr; linarith
      _ ≤ (η_main / (2 * C_err)) * c ^ (1 / 6 : ℝ) := by gcongr
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  have hδ_pos : 0 < ceBeta1 * K * liftEps c / 2 := by have := ceBeta1_pos; positivity
  have hFcont : Continuous (F K c) := hEst.F_cont hK1 (by linarith) hc8K hcK1
  have hwin_eq := hEst.conv hFcont hδ_pos (-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs))
  have hint_const := integrableOn_bspline_const (by norm_num : 1 ≤ 4) hδ_pos (η_w * liftEps c)
  have hint_F := integrableOn_continuous_shift_bspline (by norm_num : 1 ≤ 4) hδ_pos
    (x := ceBeta1 * hbS c ξ + liftEps c / (2 * ceCs)) hFcont
  have hint_F' : IntegrableOn (fun t : ℝ => F K c (-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs) + t) *
      bspline 4 (ceBeta1 * K * liftEps c / 2) t) (Icc 0 (ceBeta1 * K * liftEps c / 2)) := by
    refine hint_F.congr_fun (fun t _ => ?_) measurableSet_Icc
    ring_nf
  have hF_eval : ∀ u : ℝ, F K c u =
      (-lam_β) * ((X_base (u : ℂ)).re + liftEps c * W.α₁ c * (airySeedG 0 (u : ℂ)).re) := fun u => by
    dsimp [F, s₂, B₂, α_fn]
    rw [Fin.sum_univ_two]
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp [h10, hc_min]
    ring
  have hwin_lo : η_w * liftEps c ≤
      windowSmooth (ceBeta1 * K * liftEps c / 2) 4 (F K c) (-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs)) := by
    rw [hwin_eq]
    calc η_w * liftEps c = (η_w * liftEps c) * 1 := (mul_one _).symm
      _ = (η_w * liftEps c) * ∫ t in Icc (0 : ℝ) (ceBeta1 * K * liftEps c / 2),
            bspline 4 (ceBeta1 * K * liftEps c / 2) t := by rw [bspline_setIntegral_one (by norm_num) hδ_pos]
      _ = ∫ t in Icc (0 : ℝ) (ceBeta1 * K * liftEps c / 2),
            (η_w * liftEps c) * bspline 4 (ceBeta1 * K * liftEps c / 2) t := (integral_const_mul _ _).symm
      _ ≤ ∫ t in Icc (0 : ℝ) (ceBeta1 * K * liftEps c / 2),
            F K c (-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs) + t) * bspline 4 (ceBeta1 * K * liftEps c / 2) t := by
          refine setIntegral_mono_on hint_const hint_F' measurableSet_Icc fun t ht => ?_
          refine mul_le_mul_of_nonneg_right ?_ (bspline_nonneg 4 hδ_pos t)
          rw [hF_eval]
          exact hfloor t ht
  have he_main := he5 hK1 hc8K hcK1 h32k hξ hSw
  have he_dual := hd5 hK1 h32k hξ hSw
  have hinv_le : ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ ≤ 1 := by
    have : 0 ≤ ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ) := by
      have := ceBeta1_pos; positivity
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have hc23_le : liftEps c ^ 2 ≤ c ^ (-(1 / 2 : ℝ)) := by
    unfold liftEps
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hc0.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have herr_main : C5 * ξ⁻¹ * (liftEps c ^ 2 + ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ *
      c ^ (-(1 / 2 : ℝ))) ≤ 2 * C5 * ξ⁻¹ * c ^ (-(1 / 2 : ℝ)) := by
    have : liftEps c ^ 2 + ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ * c ^ (-(1 / 2 : ℝ)) ≤
        2 * c ^ (-(1 / 2 : ℝ)) := by
      have hc12 : 0 ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hc0.le _
      calc liftEps c ^ 2 + ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ * c ^ (-(1 / 2 : ℝ))
          ≤ c ^ (-(1 / 2 : ℝ)) + 1 * c ^ (-(1 / 2 : ℝ)) := by gcongr
        _ = 2 * c ^ (-(1 / 2 : ℝ)) := by ring
    calc C5 * ξ⁻¹ * _ ≤ C5 * ξ⁻¹ * (2 * c ^ (-(1 / 2 : ℝ))) := by gcongr
      _ = 2 * C5 * ξ⁻¹ * c ^ (-(1 / 2 : ℝ)) := by ring
  let targ : ℝ := ceK * ceBeta1 / (Real.pi ^ 2 * ξ) *
    windowSmooth (ceBeta1 * K * liftEps c / 2) 4 (F K c) (-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs))
  have htarg_lo : η_main * liftEps c * ξ⁻¹ ≤ targ := by
    have hpref : 0 ≤ ceK * ceBeta1 / (Real.pi ^ 2 * ξ) := by
      have := ceK_pos; have := ceBeta1_pos; positivity
    calc η_main * liftEps c * ξ⁻¹ = ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * (η_w * liftEps c) := by
          dsimp [η_main]; field_simp [hξ.ne', Real.pi_ne_zero]
      _ ≤ targ := mul_le_mul_of_nonneg_left hwin_lo hpref
  have hnorm_tot : ‖iMain (F K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ +
      iDual (fun u => lam_β * -convSourceFamily p γ θ lam c u) (ceBeta1 * K * liftEps c / 2) 4 c ξ -
      (targ : ℂ)‖ < targ := by
    have htri : ‖(iMain (F K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ +
        iDual (fun u => lam_β * -convSourceFamily p γ θ lam c u) (ceBeta1 * K * liftEps c / 2) 4 c ξ) - (targ : ℂ)‖ ≤
        ‖iMain (F K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ - (targ : ℂ)‖ +
          ‖iDual (fun u => lam_β * -convSourceFamily p γ θ lam c u) (ceBeta1 * K * liftEps c / 2) 4 c ξ‖ := by
      simpa only [add_sub_right_comm] using norm_add_le
        (iMain (F K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ - (targ : ℂ))
        (iDual (fun u => lam_β * -convSourceFamily p γ θ lam c u) (ceBeta1 * K * liftEps c / 2) 4 c ξ)
    have herr_c13 : C_err * c ^ (-(1 / 2 : ℝ)) < η_main * liftEps c := by
      have hprod : liftEps c * c ^ (-(1 / 6 : ℝ)) = c ^ (-(1 / 2 : ℝ)) := by
        unfold liftEps; rw [← Real.rpow_add hc0]; norm_num
      have hlt : C_err * c ^ (-(1 / 6 : ℝ)) ≤ η_main / 2 := by
        calc C_err * c ^ (-(1 / 6 : ℝ)) ≤ C_err * (η_main / (2 * C_err)) := by gcongr
          _ = η_main / 2 := by field_simp [hC_err.ne']
      calc C_err * c ^ (-(1 / 2 : ℝ)) = (C_err * c ^ (-(1 / 6 : ℝ))) * liftEps c := by rw [← hprod]; ring
        _ ≤ (η_main / 2) * liftEps c := mul_le_mul_of_nonneg_right hlt hε0.le
        _ < η_main * liftEps c := by linarith [mul_pos hη_main hε0]
    calc ‖_‖ ≤ 2 * C5 * ξ⁻¹ * c ^ (-(1 / 2 : ℝ)) + CD5 * ξ⁻¹ * c ^ (-(1 / 2 : ℝ)) :=
          htri.trans (add_le_add (he_main.trans herr_main) he_dual)
      _ = (C_err * c ^ (-(1 / 2 : ℝ))) * ξ⁻¹ := by dsimp [C_err]; ring
      _ < (η_main * liftEps c) * ξ⁻¹ := mul_lt_mul_of_pos_right herr_c13 (inv_pos.mpr hξ)
      _ ≤ targ := htarg_lo
  have hre_pos := re_pos_of_norm_lt hnorm_tot
  have hF_fun : F K c = fun u : ℝ => (-lam_β) * ((X_base (u : ℂ)).re + liftEps c * W.α₁ c * (airySeedG 0 (u : ℂ)).re) :=
    funext hF_eval
  have hD_fun : (fun u => lam_β * -convSourceFamily p γ θ lam c u) = fun u => (-lam_β) * convSourceFamily p γ θ lam c u :=
    funext fun u => by ring
  rw [hF_fun] at hre_pos
  dsimp at hre_pos
  rw [hD_fun] at hre_pos
  exact scaled_witness_neg_iff hlamβ W hc_min hξ hre_pos

/-- **Shifted compact-window negativity:** for a fixed `CeTwoEdgeLiftWitness W` and any compact
site bound `|s'| ≤ B_t`, offset bound `|r| ≤ R_off` where `-X_base ≥ η₀` on `[s' - ρ₀, s' + ρ₀]`,
all `c ≥ c_win` have `Δ = c / π² - (s' / β₁) c^{1/3} + r > 0` and `(W.fp c Δ + W.fm c Δ) / 2 < 0`. -/
theorem shifted_compact_window_neg
    {X_base : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF_base : HasGenRationalAiryCoeffs X_base β₀₀ β₁₁)
    {p γ θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 ≤ γ) (hθ : 0 ≤ θ) (hlam : 0 < lam)
    {K : ℝ} (hK1 : 1 ≤ K) (W : CeTwoEdgeLiftWitness X_base p γ θ lam K)
    {B_t R_off ρ₀ η₀ : ℝ} (hBt : 0 ≤ B_t) (hR : 0 ≤ R_off) (hρ : 0 < ρ₀) (hη : 0 < η₀) :
    ∃ c_win : ℝ, W.c_min ≤ c_win ∧ ∀ {c : ℝ}, c_win ≤ c → ∀ {s' r : ℝ},
      |s'| ≤ B_t → |r| ≤ R_off → (∀ u : ℝ, |u - s'| ≤ ρ₀ → (X_base (u : ℂ)).re ≤ -η₀) →
      let Δ := c / Real.pi ^ 2 - (s' / hankelBeta1) * c ^ (1 / 3 : ℝ) + r
      0 < Δ ∧ (W.fp c Δ + W.fm c Δ) / 2 < 0 := by
  have hβeq : hankelBeta1 = ceBeta1 := rfl
  let g₁ : ℝ → ℝ := fun u => (airySeedG 0 (u : ℂ)).re
  let R_box : ℝ := B_t + ρ₀
  have hR_box : 0 ≤ R_box := by linarith
  obtain ⟨u_gm, -, hu_gm⟩ := isCompact_Icc.exists_isMaxOn
    (⟨0, neg_nonpos.mpr hR_box, hR_box⟩ : (Icc (-R_box) R_box).Nonempty)
    airySeedG0_re_continuous.continuousOn
  let M_g : ℝ := max (g₁ u_gm) 0
  have hg_bd : ∀ u ∈ Icc (-R_box) R_box, g₁ u ≤ M_g := fun u hu => (hu_gm hu).trans (le_max_left _ _)
  let C_drift : ℝ := ceBeta1 * R_off + 2 * ceBeta1 * Real.pi ^ 2 * (B_t / ceBeta1 + R_off) ^ 2
  have hCd : 0 ≤ C_drift := by have := ceBeta1_pos; positivity
  let Sw : ℝ := B_t / ceBeta1 + C_drift / ceBeta1 + 1
  obtain ⟨c_e5, hc_e5, he5_neg⟩ := window_e5_pos_of_floor hF_base hp hp1 hγ hθ hlam hK1 W 1 Sw (η₀ / 2) one_pos (half_pos hη)
  let C_shift : ℝ := C_drift + 1 / (2 * ceCs) + ceBeta1 * K / 2 + 1
  have hCsh : 0 < C_shift := by have := ceCs_pos; have := ceBeta1_pos; positivity
  let B_arg : ℝ := 2 * Real.pi ^ 2 * (B_t / ceBeta1 + R_off + 1)
  have hBarg_0 : 0 ≤ B_arg := by have := ceBeta1_pos; positivity
  let c_lo : ℝ := max (B_arg ^ (3 / 2 : ℝ))
    (max ((C_shift / ρ₀ + 1) ^ 3) (max ((2 * W.M_α * M_g / η₀ + 1) ^ 3) ((C_drift / ceBeta1 + 1) ^ 3)))
  let c_win : ℝ := max c_e5 c_lo
  have hc_win : W.c_min ≤ c_win := (le_max_right _ _).trans (hc_e5.trans (le_max_left _ _))
  refine ⟨c_win, hc_win, fun {c} hc {s' r} hs' hr hX_neg => ?_⟩
  rw [hβeq]
  have hc_e : c_e5 ≤ c := (le_max_left _ _).trans hc
  have hc_lo_c : c_lo ≤ c := (le_max_right _ _).trans hc
  have hc32k : 32768 ≤ c := (le_max_left _ _).trans (hc_e5.trans hc_e)
  have hc0 : 0 < c := by linarith only [hc32k]
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  have hε1 : liftEps c ≤ 1 := liftEps_le_one (by linarith only [hc32k])
  have hrpow_le : ∀ {A : ℝ}, 0 ≤ A → (A + 1) ^ 3 ≤ c → A * liftEps c ≤ 1 := fun {A} hA hcA => by
    have h1 : A + 1 ≤ c ^ (1 / 3 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity) hcA (by norm_num : (0 : ℝ) ≤ 1 / 3)
      rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)] at this
      simpa using this
    rw [show liftEps c = (c ^ (1 / 3 : ℝ))⁻¹ by unfold liftEps; rw [Real.rpow_neg hc0.le],
      ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hc0 _)]
    linarith only [h1]
  have hMα0 : 0 ≤ W.M_α := (W.hm_α.trans_le W.hM_α).le
  have hMg0 : 0 ≤ M_g := le_max_right _ _
  have hCsh_ε : C_shift * liftEps c ≤ ρ₀ := by
    have hc1 : (C_shift / ρ₀ + 1) ^ 3 ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hc_lo_c)
    have hdiv : (C_shift / ρ₀) * liftEps c ≤ 1 := hrpow_le (by positivity) hc1
    calc C_shift * liftEps c = ρ₀ * ((C_shift / ρ₀) * liftEps c) := by field_simp [hρ.ne']
      _ ≤ ρ₀ * 1 := mul_le_mul_of_nonneg_left hdiv hρ.le
      _ = ρ₀ := mul_one _
  have hMg_ε : liftEps c * W.M_α * M_g ≤ η₀ / 2 := by
    have hc1 : (2 * W.M_α * M_g / η₀ + 1) ^ 3 ≤ c :=
      (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc_lo_c))
    have hdiv : (2 * W.M_α * M_g / η₀) * liftEps c ≤ 1 := hrpow_le (by positivity) hc1
    calc liftEps c * W.M_α * M_g = (η₀ / 2) * ((2 * W.M_α * M_g / η₀) * liftEps c) := by
          field_simp [hη.ne']
      _ ≤ (η₀ / 2) * 1 := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = η₀ / 2 := mul_one _
  have hCd_ε : (C_drift / ceBeta1) * liftEps c ≤ 1 := by
    have hc1 : (C_drift / ceBeta1 + 1) ^ 3 ≤ c :=
      (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc_lo_c))
    exact hrpow_le (div_nonneg hCd ceBeta1_pos.le) hc1
  have hB_23 : B_arg ^ (3 / 2 : ℝ) ≤ c := (le_max_left _ _).trans hc_lo_c
  have hB_23_le : B_arg ≤ c ^ (2 / 3 : ℝ) := by
    calc B_arg = (B_arg ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
          rw [← Real.rpow_mul hBarg_0]; norm_num
      _ ≤ c ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hB_23 (by norm_num)
  have hc23_mul : liftEps c ^ 2 * c ^ (2 / 3 : ℝ) = 1 := by
    unfold liftEps; rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; norm_num
  have hB_eps2 : B_arg * liftEps c ^ 2 ≤ 1 := by
    calc B_arg * liftEps c ^ 2 ≤ c ^ (2 / 3 : ℝ) * liftEps c ^ 2 := mul_le_mul_of_nonneg_right hB_23_le (sq_nonneg _)
      _ = liftEps c ^ 2 * c ^ (2 / 3 : ℝ) := by ring
      _ = 1 := hc23_mul
  have hy_half : Real.pi ^ 2 * (B_t / ceBeta1 * liftEps c ^ 2 + R_off * liftEps c ^ 3) ≤ 1 / 2 := by
    have hε3 : liftEps c ^ 3 ≤ liftEps c ^ 2 := by nlinarith only [hε0, hε1]
    have hle_sum : B_t / ceBeta1 + R_off ≤ B_t / ceBeta1 + R_off + 1 := by linarith only
    calc Real.pi ^ 2 * (B_t / ceBeta1 * liftEps c ^ 2 + R_off * liftEps c ^ 3)
        ≤ Real.pi ^ 2 * (B_t / ceBeta1 * liftEps c ^ 2 + R_off * liftEps c ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hε3 hR) _) (sq_nonneg Real.pi)
      _ = Real.pi ^ 2 * ((B_t / ceBeta1 + R_off) * liftEps c ^ 2) := by ring
      _ ≤ Real.pi ^ 2 * ((B_t / ceBeta1 + R_off + 1) * liftEps c ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle_sum (sq_nonneg _)) (sq_nonneg Real.pi)
      _ = (1 / 2) * (B_arg * liftEps c ^ 2) := by dsimp [B_arg]; ring
      _ ≤ (1 / 2) * 1 := mul_le_mul_of_nonneg_left hB_eps2 (by norm_num)
      _ = 1 / 2 := mul_one _
  have hΔ_lo : c / (2 * Real.pi ^ 2) ≤ c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r := by
    have habs_sub : |(s' / ceBeta1) * c ^ (1 / 3 : ℝ) - r| ≤ (B_t / ceBeta1 + R_off) * c ^ (1 / 3 : ℝ) := by
      have hc13 : 1 ≤ c ^ (1 / 3 : ℝ) := Real.one_le_rpow (by linarith only [hc32k]) (by norm_num)
      have hβ_nn : 0 ≤ ceBeta1 := ceBeta1_pos.le
      calc |(s' / ceBeta1) * c ^ (1 / 3 : ℝ) - r|
          ≤ |(s' / ceBeta1) * c ^ (1 / 3 : ℝ)| + |r| := abs_sub _ _
        _ = |s'| / ceBeta1 * c ^ (1 / 3 : ℝ) + |r| := by
            rw [abs_mul, abs_div, abs_of_pos ceBeta1_pos, abs_of_pos (Real.rpow_pos_of_pos hc0 _)]
        _ ≤ B_t / ceBeta1 * c ^ (1 / 3 : ℝ) + R_off * c ^ (1 / 3 : ℝ) :=
            add_le_add (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hs' hβ_nn) (Real.rpow_nonneg hc0.le _))
              (hr.trans (le_mul_of_one_le_right hR hc13))
        _ = (B_t / ceBeta1 + R_off) * c ^ (1 / 3 : ℝ) := by ring
    have hstep : (B_t / ceBeta1 + R_off) * c ^ (1 / 3 : ℝ) ≤ c / (2 * Real.pi ^ 2) := by
      have hc13_eq : c ^ (1 / 3 : ℝ) = liftEps c ^ 2 * c := by
        calc c ^ (1 / 3 : ℝ) = c ^ (1 / 3 : ℝ) * (liftEps c ^ 2 * c ^ (2 / 3 : ℝ)) := by rw [hc23_mul, mul_one]
          _ = liftEps c ^ 2 * (c ^ (1 / 3 : ℝ) * c ^ (2 / 3 : ℝ)) := by ring
          _ = liftEps c ^ 2 * c := by
              rw [← Real.rpow_add hc0, show (1 / 3 : ℝ) + 2 / 3 = 1 by norm_num, Real.rpow_one]
      have hle_sum : B_t / ceBeta1 + R_off ≤ B_t / ceBeta1 + R_off + 1 := by linarith only
      have hpi2_eq : ((B_t / ceBeta1 + R_off + 1) * liftEps c ^ 2) * c =
          (1 / 2) * (B_arg * liftEps c ^ 2) * (c / Real.pi ^ 2) := by
        dsimp [B_arg]
        calc ((B_t / ceBeta1 + R_off + 1) * liftEps c ^ 2) * c
            = ((B_t / ceBeta1 + R_off + 1) * liftEps c ^ 2 * c) * (Real.pi ^ 2 / Real.pi ^ 2) := by
                rw [div_self (pow_ne_zero 2 Real.pi_ne_zero), mul_one]
          _ = (1 / 2) * (2 * Real.pi ^ 2 * (B_t / ceBeta1 + R_off + 1) * liftEps c ^ 2) * (c / Real.pi ^ 2) := by ring
      rw [hc13_eq]
      calc (B_t / ceBeta1 + R_off) * (liftEps c ^ 2 * c)
          = (B_t / ceBeta1 + R_off) * liftEps c ^ 2 * c := by ring
        _ ≤ (B_t / ceBeta1 + R_off + 1) * liftEps c ^ 2 * c :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle_sum (sq_nonneg _)) hc0.le
        _ = (1 / 2) * (B_arg * liftEps c ^ 2) * (c / Real.pi ^ 2) := hpi2_eq
        _ ≤ (1 / 2) * 1 * (c / Real.pi ^ 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB_eps2 (by norm_num))
              (div_nonneg hc0.le (sq_nonneg Real.pi))
        _ = c / (2 * Real.pi ^ 2) := by ring
    have hsub_le : (s' / ceBeta1) * c ^ (1 / 3 : ℝ) - r ≤ c / (2 * Real.pi ^ 2) :=
      ((abs_le.mp habs_sub).2).trans hstep
    calc c / (2 * Real.pi ^ 2) = c / Real.pi ^ 2 - c / (2 * Real.pi ^ 2) := by ring
      _ ≤ c / Real.pi ^ 2 - ((s' / ceBeta1) * c ^ (1 / 3 : ℝ) - r) := sub_le_sub_left hsub_le _
      _ = c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r := by ring
  have hnb := hbS_near_shell hBt hR hs' hr (by linarith only [hc32k]) hΔ_lo hy_half
  have hΔ_pos : 0 < c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r :=
    lt_of_lt_of_le (by positivity) hΔ_lo
  have hξ_pos : 0 < (c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r) / c := hnb.1
  have hξ_c : c * ((c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r) / c) =
      c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r := by field_simp [hc0.ne']
  have hSw : |hbS c ((c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r) / c)| ≤ Sw := by
    have hdiff : |ceBeta1 * hbS c ((c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r) / c) + s'| ≤
        C_drift * liftEps c := hnb.2
    have hdiv : |hbS c ((c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r) / c) + s' / ceBeta1| ≤
        (C_drift / ceBeta1) * liftEps c := by
      have : hbS c ((c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r) / c) + s' / ceBeta1 =
          (ceBeta1 * hbS c ((c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r) / c) + s') / ceBeta1 := by
        field_simp [ceBeta1_pos.ne']
      rw [this, abs_div, abs_of_pos ceBeta1_pos]
      exact (div_le_div_of_nonneg_right hdiff ceBeta1_pos.le).trans_eq (by ring)
    have hsplit : hbS c ((c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r) / c) =
        (hbS c ((c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r) / c) + s' / ceBeta1) - s' / ceBeta1 :=
      (add_sub_cancel_right _ _).symm
    have hdiv_s : |s' / ceBeta1| ≤ B_t / ceBeta1 := by
      rw [abs_div, abs_of_pos ceBeta1_pos]
      exact div_le_div_of_nonneg_right hs' ceBeta1_pos.le
    calc |hbS c ((c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r) / c)|
        = |(hbS c ((c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r) / c) + s' / ceBeta1) - s' / ceBeta1| :=
          congrArg abs hsplit
      _ ≤ |hbS c ((c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r) / c) + s' / ceBeta1| + |s' / ceBeta1| :=
          abs_sub _ _
      _ ≤ (C_drift / ceBeta1) * liftEps c + B_t / ceBeta1 := add_le_add hdiv hdiv_s
      _ ≤ 1 + B_t / ceBeta1 := add_le_add_left hCd_ε _
      _ ≤ Sw := by dsimp [Sw]; linarith only [div_nonneg hCd ceBeta1_pos.le]
  have hneg := he5_neg hc_e hξ_pos hSw fun t ht => by
    let u : ℝ := -(ceBeta1 * hbS c ((c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r) / c)) -
      liftEps c / (2 * ceCs) + t
    have hu_dist : |u - s'| ≤ ρ₀ := by
      have hus : u - s' =
          -(ceBeta1 * hbS c ((c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r) / c) + s') -
            liftEps c / (2 * ceCs) + t := by dsimp [u]; ring
      have ht_bd : |t| ≤ (ceBeta1 * K / 2) * liftEps c := by
        rw [abs_of_nonneg ht.1]; exact ht.2.trans_eq (by ring)
      have hcs_bd : |liftEps c / (2 * ceCs)| = (1 / (2 * ceCs)) * liftEps c := by
        have := ceCs_pos; rw [abs_of_nonneg (by positivity)]; ring
      have hlt1 : C_drift + 1 / (2 * ceCs) + ceBeta1 * K / 2 ≤ C_shift := by dsimp [C_shift]; linarith
      rw [hus]
      calc |-(ceBeta1 * hbS c ((c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r) / c) + s') -
              liftEps c / (2 * ceCs) + t|
          ≤ |-(ceBeta1 * hbS c ((c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r) / c) + s') -
              liftEps c / (2 * ceCs)| + |t| := abs_add_le _ _
        _ ≤ (|ceBeta1 * hbS c ((c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r) / c) + s'| +
              |liftEps c / (2 * ceCs)|) + |t| :=
            add_le_add_left
              ((abs_sub (-(ceBeta1 * hbS c ((c / Real.pi ^ 2 - (s' / ceBeta1) * c ^ (1 / 3 : ℝ) + r) / c) + s'))
                (liftEps c / (2 * ceCs))).trans_eq (by rw [abs_neg])) _
        _ ≤ C_drift * liftEps c + (1 / (2 * ceCs)) * liftEps c + (ceBeta1 * K / 2) * liftEps c := by
            rw [hcs_bd]; exact add_le_add (add_le_add_left hnb.2 _) ht_bd
        _ = (C_drift + 1 / (2 * ceCs) + ceBeta1 * K / 2) * liftEps c := by ring
        _ ≤ C_shift * liftEps c := mul_le_mul_of_nonneg_right hlt1 hε0.le
        _ ≤ ρ₀ := hCsh_ε
    have hu_X : (X_base (u : ℂ)).re ≤ -η₀ := hX_neg u hu_dist
    have hu_box : u ∈ Icc (-R_box) R_box := by
      have habs : |u| ≤ R_box := calc |u| = |(u - s') + s'| := congrArg abs (by ring)
        _ ≤ |u - s'| + |s'| := abs_add_le _ _
        _ ≤ ρ₀ + B_t := add_le_add hu_dist hs'
        _ = R_box := by ring
      exact abs_le.mp habs
    have hu_g : |liftEps c * W.α₁ c * g₁ u| ≤ η₀ / 2 := by
      have hα_bd := W.hα₁_bd ((le_max_right _ _).trans (hc_e5.trans hc_e))
      have hgnn : 0 ≤ g₁ u := airySeedG_re_nonneg 0 u
      have hg_hi : g₁ u ≤ M_g := hg_bd u hu_box
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg hε0.le (W.hm_α.le.trans hα_bd.1)) hgnn)]
      calc liftEps c * W.α₁ c * g₁ u ≤ liftEps c * W.M_α * M_g :=
            mul_le_mul (mul_le_mul_of_nonneg_left hα_bd.2 hε0.le) hg_hi hgnn (mul_nonneg hε0.le hMα0)
        _ ≤ η₀ / 2 := hMg_ε
    have hmul1 : (-1 : ℝ) * ((X_base (u : ℂ)).re + liftEps c * W.α₁ c * g₁ u) =
        -(X_base (u : ℂ)).re - liftEps c * W.α₁ c * g₁ u := by ring
    change (η₀ / 2) * liftEps c ≤ (-1 : ℝ) * ((X_base (u : ℂ)).re + liftEps c * W.α₁ c * g₁ u)
    rw [hmul1]
    have hlow : η₀ / 2 ≤ -(X_base (u : ℂ)).re - liftEps c * W.α₁ c * g₁ u := by linarith only [hu_X, (abs_le.mp hu_g).2]
    calc (η₀ / 2) * liftEps c ≤ (η₀ / 2) * 1 := mul_le_mul_of_nonneg_left hε1 (by positivity)
      _ = η₀ / 2 := mul_one _
      _ ≤ _ := hlow
  dsimp only
  refine ⟨hΔ_pos, ?_⟩
  rw [← hξ_c]
  exact hneg

/-- info: 'FormalResearch.SignUncertainty.shifted_compact_window_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.shifted_compact_window_neg

end FormalResearch.SignUncertainty