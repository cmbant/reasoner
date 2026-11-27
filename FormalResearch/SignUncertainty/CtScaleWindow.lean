module

public import FormalResearch.Special.AiryEnvelope
public import FormalResearch.SignUncertainty.CtScaleBand
public import FormalResearch.SignUncertainty.HankelWindowLocal
public import FormalResearch.SignUncertainty.HankelWindowGeom
public import FormalResearch.SignUncertainty.HankelWindowAux
public import FormalResearch.SignUncertainty.HankelWindowArith
public import FormalResearch.SignUncertainty.HankelBootData

/-!
# Scale-`r` saddle window bound for `Ψ̃` (`ct:cov`, P1 Step 1b)

Generalizes `HankelWindow.hankel_cov_window` from the top scale `R_J ≍ c^{2/3}` to every scale
`r ∈ [256, R_J]` satisfying the angular condition `250 log c ≤ θ r^{3/2}` (in particular all
`θ ≥ C₂ r^{-3/4} (log c)^{1/2}` with `r ≥ C₃ (log c)²`):

  `‖hankelPsi c f u‖ ≤ hankelScaleWindowC * L_r * airyEnv u * (Re u^{1/2})^{-3/2} * ‖u‖^{-3/4}`,

where `L_r = 1 + r^{1/2} B₂(r) + r_til^{1/2} B₁(r_til) + R_J^{1/2} B₂(R_J)` with `r_til = min (1028 * r) R_J`.
-/

@[expose] public section

open Complex Set FormalResearch.Special
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.ModularBootstrap.StripBand

/-- Constant in `hankel_scale_cov_window`. -/
noncomputable def hankelScaleWindowC : ℝ := 40 * hankelScaleBandC

lemma hankelScaleWindowC_pos : 0 < hankelScaleWindowC := by
  unfold hankelScaleWindowC hankelScaleBandC; positivity

/-- Scale-`r` window moment factor
`L_r = 1 + r^{1/2} B₂(r) + r_til^{1/2} B₁(r_til) + R_J^{1/2} B₂(R_J)`. -/
noncomputable def hankelScaleL (c R_J r u_T : ℝ) (f : ℝ → ℝ) : ℝ :=
  let r_til := min (1028 * r) R_J
  1 + r ^ (1 / 2 : ℝ) * hankelBootB2 c f r +
    r_til ^ (1 / 2 : ℝ) * hankelBootB1 c f r_til u_T +
    R_J ^ (1 / 2 : ℝ) * hankelBootB2 c f R_J

lemma hankelScaleB1_til_nonneg {c ε T u_T R_J r : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hmass : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T)
    (hr_lb : 256 ≤ r) (hr_RJ : r ≤ R_J) (hRJ_A : R_J ≤ langerRadius c) :
    0 ≤ hankelBootB1 c f (min (1028 * r) R_J) u_T := by
  have hrt_lb : 256 ≤ min (1028 * r) R_J := le_min (by linarith) (by linarith)
  exact hankelBootB1_nonneg hc hf hε hmass hT hu0 hu3 (by linarith) (by linarith)
    ((min_le_right _ _).trans hRJ_A)

lemma hankelScaleL_ge_one {c ε T u_T R_J r : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hmass : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T)
    (hr_lb : 256 ≤ r) (hr_RJ : r ≤ R_J) (hRJ_A : R_J ≤ langerRadius c) :
    1 ≤ hankelScaleL c R_J r u_T f := by
  unfold hankelScaleL
  dsimp only
  have h1 := hankelScaleB1_til_nonneg hc hf hε hmass hT hu0 hu3 hr_lb hr_RJ hRJ_A
  have h2 := hankelBootB2_nonneg c f r
  have h3 := hankelBootB2_nonneg c f R_J
  have hp1 : 0 ≤ r ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hp2 : 0 ≤ (min (1028 * r) R_J) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (le_min (by linarith) (by linarith)) _
  have hp3 : 0 ≤ R_J ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  nlinarith [mul_nonneg hp1 h2, mul_nonneg hp2 h1, mul_nonneg hp3 h3]

private lemma scale_norm_exp_eq_airyEnv (u : ℂ) :
    ‖Complex.exp (-(4 / 3 : ℂ) * u ^ (3 / 2 : ℂ))‖ = airyEnv u := by
  rw [Complex.norm_exp]
  unfold airyEnv
  congr 1
  have h : (-(4 / 3 : ℂ)) = ((-(4 / 3 : ℝ) : ℝ) : ℂ) := by norm_num
  rw [h]; simp [Complex.mul_re]

private lemma scale_not_neg_real {u : ℂ} (hnorm : 0 < ‖u‖) (hre : 0 < (u ^ (1 / 2 : ℂ)).re) :
    ¬ (u.im = 0 ∧ u.re ≤ 0) := by
  intro hcut
  rcases eq_or_lt_of_le hcut.2 with hu0 | hu_lt
  · have : u = 0 := Complex.ext hu0 hcut.1
    rw [this, norm_zero] at hnorm
    exact lt_irrefl 0 hnorm
  · have hune : u ≠ 0 := fun h => by rw [h, norm_zero] at hnorm; exact lt_irrefl 0 hnorm
    have harg : Complex.arg u = π := Complex.arg_eq_pi_iff.mpr ⟨hu_lt, hcut.1⟩
    have hpow : u ^ (1 / 2 : ℂ) = Complex.exp (Complex.log u * (1 / 2 : ℂ)) :=
      Complex.cpow_def_of_ne_zero hune _
    have hlog_im : (Complex.log u).im = π := by rw [Complex.log_im]; exact harg
    have hre0 : (u ^ (1 / 2 : ℂ)).re = 0 := by
      rw [hpow, Complex.exp_re]
      have him : (Complex.log u * (1 / 2 : ℂ)).im = π / 2 := by
        simp [Complex.mul_im, hlog_im]; ring
      rw [him, Real.cos_pi_div_two, mul_zero]
    linarith

private lemma scale_langerMu_ge : (0.7 : ℝ) ≤ langerMu := by
  have hsq : (0.7 : ℝ) ^ 2 ≤ langerMu ^ 2 := by nlinarith [langerMu_sq_ge]
  exact (abs_le_of_sq_le_sq' (by nlinarith) langerMu_pos.le).2

private lemma scale_c23_ge {c : ℝ} (hc : 1e14 ≤ c) : (1e9 : ℝ) ≤ c ^ (2 / 3 : ℝ) := by
  have h1 : (1e9 : ℝ) ≤ (1e14 : ℝ) ^ (2 / 3 : ℝ) := by
    by_contra hlt; push Not at hlt
    have h3 : ((1e14 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 < (1e9 : ℝ) ^ 3 :=
      pow_lt_pow_left₀ hlt (Real.rpow_nonneg (by positivity) _) (by norm_num)
    rw [← Real.rpow_natCast ((1e14 : ℝ) ^ (2 / 3 : ℝ)) 3, ← Real.rpow_mul (by positivity)] at h3
    norm_num at h3
  exact h1.trans (Real.rpow_le_rpow (by positivity) hc (by norm_num))

private lemma scale_radius_bounds {c R_J r : ℝ} {u : ℂ}
    (hc : 1e14 ≤ c)
    (hRJ_ub : R_J ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1)
    (hr_lb : 256 ≤ r) (hr_RJ : r ≤ R_J)
    (hlo : r - 1 ≤ ‖u‖) (hhi : ‖u‖ ≤ r + 1) :
    R_J ≤ langerRadius c ∧ ‖u‖ ≤ langerRadius c ∧ ‖u‖ ≤ c ^ (2 / 3 : ℝ) ∧
      0.99 * √r ≤ ‖u‖ ^ (1 / 2 : ℝ) ∧ ‖u‖ ^ (1 / 2 : ℝ) ≤ 1.01 * √r := by
  have hc0 : 0 < c := by linarith
  have hc23 : (1e9 : ℝ) ≤ c ^ (2 / 3 : ℝ) := scale_c23_ge hc
  have hκ := hankelLangerKappa_bounds
  have hdisc_RJ : R_J ≤ langerRadius c := by
    have hr_def : langerRadius c = c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := rfl
    have hκ_c23 : (1 / 2 : ℝ) * c ^ (2 / 3 : ℝ) ≤ langerKappa * c ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hκ.1 (Real.rpow_nonneg hc0.le (2 / 3 : ℝ))
    rw [hr_def]
    nlinarith [hRJ_ub, hc23]
  have hu_le_RJ1 : ‖u‖ ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 2 := by linarith
  have hdisc : ‖u‖ ≤ langerRadius c := by
    have hr_def : langerRadius c = c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := rfl
    have hκ_c23 : (1 / 2 : ℝ) * c ^ (2 / 3 : ℝ) ≤ langerKappa * c ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hκ.1 (Real.rpow_nonneg hc0.le (2 / 3 : ℝ))
    rw [hr_def]
    nlinarith [hu_le_RJ1, hc23]
  have huc : ‖u‖ ≤ c ^ (2 / 3 : ℝ) := by linarith
  have hr0 : 0 < r := by linarith
  have hN0 : 0 < ‖u‖ := by linarith
  set R' := √r
  have hR'sq : R' ^ 2 = r := Real.sq_sqrt hr0.le
  set s := ‖u‖ ^ (1 / 2 : ℝ)
  have hs0 : 0 < s := Real.rpow_pos_of_pos hN0 _
  have hssq : s ^ 2 = ‖u‖ := by
    rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hN0.le]; norm_num
  have hs1 : 0.99 * R' ≤ s := by
    have : (0.99 * R') ^ 2 ≤ s ^ 2 := by rw [hssq]; nlinarith [hR'sq, hlo, hr_lb]
    exact (abs_le_of_sq_le_sq' this hs0.le).2
  have hs2 : s ≤ 1.01 * R' := by
    have : s ^ 2 ≤ (1.01 * R') ^ 2 := by rw [hssq]; nlinarith [hR'sq, hhi, hr_lb]
    exact (abs_le_of_sq_le_sq' this (by positivity)).2
  exact ⟨hdisc_RJ, hdisc, huc, hs1, hs2⟩

private lemma scale_sqrt_ratio_le {r r_til : ℝ} (hr0 : 0 < r) (hrt0 : 0 < r_til) (hrt : r_til ≤ 1028 * r) :
    r ^ (-(1 / 2 : ℝ)) * r_til ^ (1 / 2 : ℝ) ≤ 33 := by
  have h1 : (r ^ (-(1 / 2 : ℝ)) * r_til ^ (1 / 2 : ℝ)) ^ 2 ≤ 33 ^ 2 := by
    rw [mul_pow, Real.rpow_neg hr0.le, inv_pow,
      ← Real.rpow_natCast (r ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hr0.le,
      ← Real.rpow_natCast (r_til ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hrt0.le]
    norm_num
    rw [← div_eq_inv_mul, div_le_iff₀ hr0]
    linarith
  exact (abs_le_of_sq_le_sq' (by nlinarith) (by positivity)).2

private lemma scale_Q_r54_le {r R_J L_r B1_til B2_r B2_RJ : ℝ}
    (hr_lb : 256 ≤ r) (hr_RJ : r ≤ R_J)
    (hB1_nn : 0 ≤ B1_til) (hB2r_nn : 0 ≤ B2_r) (hB2R_nn : 0 ≤ B2_RJ)
    (hL_def : L_r = 1 + r ^ (1 / 2 : ℝ) * B2_r +
      (min (1028 * r) R_J) ^ (1 / 2 : ℝ) * B1_til + R_J ^ (1 / 2 : ℝ) * B2_RJ) :
    let r_til := min (1028 * r) R_J
    r ^ (5 / 4 : ℝ) *
      (r ^ (-(3 / 2 : ℝ)) + r ^ (-(7 / 4 : ℝ)) * r_til * B1_til +
        r ^ (-(3 / 4 : ℝ)) * (B2_r + B2_RJ)) ≤ 33 * L_r := by
  dsimp only
  have hr0 : 0 < r := by linarith
  have hrt0 : 0 < min (1028 * r) R_J := lt_min (by positivity) (by linarith)
  set r_til := min (1028 * r) R_J
  have h54_32 : r ^ (5 / 4 : ℝ) * r ^ (-(3 / 2 : ℝ)) ≤ 1 := by
    rw [← Real.rpow_add hr0]
    have hnorm : (5 / 4 : ℝ) + -(3 / 2 : ℝ) = -(1 / 4 : ℝ) := by norm_num
    rw [hnorm, Real.rpow_neg hr0.le]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by linarith) (by norm_num))
  have h54_74 : r ^ (5 / 4 : ℝ) * (r ^ (-(7 / 4 : ℝ)) * r_til * B1_til) ≤
      33 * (r_til ^ (1 / 2 : ℝ) * B1_til) := by
    have hpow : r ^ (5 / 4 : ℝ) * r ^ (-(7 / 4 : ℝ)) = r ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hr0]; norm_num
    have hsplit : r_til = r_til ^ (1 / 2 : ℝ) * r_til ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hrt0]; norm_num
    have hratio := scale_sqrt_ratio_le hr0 hrt0 (min_le_left _ _)
    calc r ^ (5 / 4 : ℝ) * (r ^ (-(7 / 4 : ℝ)) * r_til * B1_til)
        = (r ^ (5 / 4 : ℝ) * r ^ (-(7 / 4 : ℝ))) * (r_til ^ (1 / 2 : ℝ) * r_til ^ (1 / 2 : ℝ)) * B1_til := by
            rw [← hsplit]; ring
      _ = (r ^ (-(1 / 2 : ℝ)) * r_til ^ (1 / 2 : ℝ)) * (r_til ^ (1 / 2 : ℝ) * B1_til) := by
            rw [hpow]; ring
      _ ≤ 33 * (r_til ^ (1 / 2 : ℝ) * B1_til) := by gcongr
  have h54_34 : r ^ (5 / 4 : ℝ) * (r ^ (-(3 / 4 : ℝ)) * (B2_r + B2_RJ)) ≤
      r ^ (1 / 2 : ℝ) * B2_r + R_J ^ (1 / 2 : ℝ) * B2_RJ := by
    have hpow : r ^ (5 / 4 : ℝ) * r ^ (-(3 / 4 : ℝ)) = r ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hr0]; norm_num
    have hr12_le : r ^ (1 / 2 : ℝ) ≤ R_J ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hr0.le hr_RJ (by norm_num)
    calc r ^ (5 / 4 : ℝ) * (r ^ (-(3 / 4 : ℝ)) * (B2_r + B2_RJ))
        = r ^ (1 / 2 : ℝ) * B2_r + r ^ (1 / 2 : ℝ) * B2_RJ := by rw [← hpow]; ring
      _ ≤ r ^ (1 / 2 : ℝ) * B2_r + R_J ^ (1 / 2 : ℝ) * B2_RJ := by gcongr
  rw [mul_add, mul_add, hL_def]
  have hp_r : 0 ≤ r ^ (1 / 2 : ℝ) := Real.rpow_nonneg hr0.le _
  have hp_RJ : 0 ≤ R_J ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  linarith [h54_32, h54_74, h54_34, mul_nonneg hp_r hB2r_nn, mul_nonneg hp_RJ hB2R_nn]

private lemma scale_u12_to_r54 {r u_norm : ℝ} (hr0 : 0 < r) (hN0 : 0 < u_norm)
    (hs2 : u_norm ^ (1 / 2 : ℝ) ≤ 1.01 * √r) :
    u_norm ^ (1 / 2 : ℝ) ≤ 1.031 * r ^ (5 / 4 : ℝ) * u_norm ^ (-(3 / 4 : ℝ)) := by
  have hu34_pos : 0 < u_norm ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have h_r12 : √r = r ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow r
  have h12 : u_norm ^ (1 / 2 : ℝ) ≤ 1.01 * r ^ (1 / 2 : ℝ) := by rwa [← h_r12]
  have h101 : (1.01 : ℝ) ^ (3 / 2 : ℝ) ≤ 1.02 := by
    have hs : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
    rw [hs, Real.rpow_add (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
    have hsq : √1.01 ≤ 1.005 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    linarith
  have h34 : u_norm ^ (3 / 4 : ℝ) ≤ 1.02 * r ^ (3 / 4 : ℝ) := by
    have hr34_eq : r ^ (3 / 4 : ℝ) = (√r) ^ (3 / 2 : ℝ) := by
      rw [h_r12, ← Real.rpow_mul hr0.le]; norm_num
    have hu34_eq : u_norm ^ (3 / 4 : ℝ) = (u_norm ^ (1 / 2 : ℝ)) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_mul hN0.le]; norm_num
    rw [hu34_eq, hr34_eq]
    calc (u_norm ^ (1 / 2 : ℝ)) ^ (3 / 2 : ℝ)
        ≤ (1.01 * √r) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hs2 (by norm_num)
      _ = (1.01 : ℝ) ^ (3 / 2 : ℝ) * (√r) ^ (3 / 2 : ℝ) :=
          Real.mul_rpow (by norm_num) (Real.sqrt_nonneg r)
      _ ≤ 1.02 * (√r) ^ (3 / 2 : ℝ) := by gcongr
  have hr54 : r ^ (1 / 2 : ℝ) * r ^ (3 / 4 : ℝ) = r ^ (5 / 4 : ℝ) := by
    rw [← Real.rpow_add hr0]; norm_num
  have hprod : u_norm ^ (1 / 2 : ℝ) * u_norm ^ (3 / 4 : ℝ) ≤ 1.031 * r ^ (5 / 4 : ℝ) := by
    have hmul := mul_le_mul h12 h34 (Real.rpow_nonneg hN0.le _) (by positivity)
    calc u_norm ^ (1 / 2 : ℝ) * u_norm ^ (3 / 4 : ℝ)
        ≤ (1.01 * r ^ (1 / 2 : ℝ)) * (1.02 * r ^ (3 / 4 : ℝ)) := hmul
      _ = (1.01 * 1.02) * (r ^ (1 / 2 : ℝ) * r ^ (3 / 4 : ℝ)) := by ring
      _ = (1.01 * 1.02) * r ^ (5 / 4 : ℝ) := by rw [hr54]
      _ ≤ 1.031 * r ^ (5 / 4 : ℝ) := by
          gcongr; norm_num
  have h_inv_bd : u_norm ^ (1 / 2 : ℝ) ≤ 1.031 * r ^ (5 / 4 : ℝ) * (u_norm ^ (3 / 4 : ℝ))⁻¹ := by
    rw [← div_eq_mul_inv (1.031 * r ^ (5 / 4 : ℝ)) (u_norm ^ (3 / 4 : ℝ)), le_div_iff₀ hu34_pos]
    exact hprod
  rwa [Real.rpow_neg hN0.le]

private lemma scale_comb_algebra {c r R_J u_norm X L_r B1_til B2_r B2_RJ : ℝ}
    (hc : 1e14 ≤ c) (hr_lb : 256 ≤ r) (hr_RJ : r ≤ R_J)
    (hN0 : 0 < u_norm) (hNc : u_norm ≤ c ^ (2 / 3 : ℝ))
    (hs2 : u_norm ^ (1 / 2 : ℝ) ≤ 1.01 * √r)
    (hX0 : 0 < X) (hXN : X ≤ u_norm ^ (1 / 2 : ℝ))
    (hB1_nn : 0 ≤ B1_til) (hB2r_nn : 0 ≤ B2_r) (hB2R_nn : 0 ≤ B2_RJ)
    (hL_def : L_r = 1 + r ^ (1 / 2 : ℝ) * B2_r +
      (min (1028 * r) R_J) ^ (1 / 2 : ℝ) * B1_til + R_J ^ (1 / 2 : ℝ) * B2_RJ)
    (hL_ge1 : 1 ≤ L_r) :
    let r_til := min (1028 * r) R_J
    let Q_r := hankelScaleBandC *
      (r ^ (-(3 / 2 : ℝ)) + r ^ (-(7 / 4 : ℝ)) * r_til * B1_til +
        r ^ (-(3 / 4 : ℝ)) * (B2_r + B2_RJ))
    c ^ (1 / 3 : ℝ) *
      ((100 / 81 : ℝ) * (Q_r * (1.11 * u_norm ^ (1 / 2 : ℝ) / X)) *
          (2.5 * c ^ (-(1 / 3 : ℝ)) * X ^ (-(1 / 2 : ℝ))) +
        62 * c ^ (-(2 : ℝ))) ≤
      125 * hankelScaleBandC * L_r * X ^ (-(3 / 2 : ℝ)) * u_norm ^ (-(3 / 4 : ℝ)) := by
  dsimp only
  have hc0 : 0 < c := by linarith
  have hr0 : 0 < r := by linarith
  have hHSC : 0 < hankelScaleBandC := by unfold hankelScaleBandC; norm_num
  set r_til := min (1028 * r) R_J
  set S_r := r ^ (-(3 / 2 : ℝ)) + r ^ (-(7 / 4 : ℝ)) * r_til * B1_til +
    r ^ (-(3 / 4 : ℝ)) * (B2_r + B2_RJ)
  have hS_nn : 0 ≤ S_r := by
    have : 0 ≤ r ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hr0.le _
    have : 0 ≤ r ^ (-(7 / 4 : ℝ)) := Real.rpow_nonneg hr0.le _
    have : 0 ≤ r ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hr0.le _
    have : 0 ≤ r_til := le_min (by positivity) (by linarith)
    positivity
  have hQ_r54 := scale_Q_r54_le hr_lb hr_RJ hB1_nn hB2r_nn hB2R_nn hL_def
  have hu12_bd := scale_u12_to_r54 hr0 hN0 hs2
  have hQ_u : hankelScaleBandC * S_r * u_norm ^ (1 / 2 : ℝ) ≤
      34.1 * hankelScaleBandC * L_r * u_norm ^ (-(3 / 4 : ℝ)) := by
    have hu_nn : 0 ≤ u_norm ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hN0.le _
    calc hankelScaleBandC * S_r * u_norm ^ (1 / 2 : ℝ)
        ≤ hankelScaleBandC * S_r * (1.031 * r ^ (5 / 4 : ℝ) * u_norm ^ (-(3 / 4 : ℝ))) := by gcongr
      _ = 1.031 * hankelScaleBandC * (r ^ (5 / 4 : ℝ) * S_r) * u_norm ^ (-(3 / 4 : ℝ)) := by ring
      _ ≤ 1.031 * hankelScaleBandC * (33 * L_r) * u_norm ^ (-(3 / 4 : ℝ)) := by gcongr
      _ ≤ 34.1 * hankelScaleBandC * L_r * u_norm ^ (-(3 / 4 : ℝ)) := by
          have : 0 ≤ hankelScaleBandC * L_r * u_norm ^ (-(3 / 4 : ℝ)) := by positivity
          nlinarith
  have hX32 : X⁻¹ * X ^ (-(1 / 2 : ℝ)) = X ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one X, ← Real.rpow_add hX0]; norm_num
  have hc_cancel : c ^ (1 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add hc0, add_neg_cancel, Real.rpow_zero]
  have hmain :
      c ^ (1 / 3 : ℝ) *
        ((100 / 81 : ℝ) * (hankelScaleBandC * S_r * (1.11 * u_norm ^ (1 / 2 : ℝ) / X)) *
          (2.5 * c ^ (-(1 / 3 : ℝ)) * X ^ (-(1 / 2 : ℝ)))) ≤
      118 * hankelScaleBandC * L_r * X ^ (-(3 / 2 : ℝ)) * u_norm ^ (-(3 / 4 : ℝ)) := by
    have heq :
        c ^ (1 / 3 : ℝ) *
          ((100 / 81 : ℝ) * (hankelScaleBandC * S_r * (1.11 * u_norm ^ (1 / 2 : ℝ) / X)) *
            (2.5 * c ^ (-(1 / 3 : ℝ)) * X ^ (-(1 / 2 : ℝ)))) =
        ((100 / 81 : ℝ) * 1.11 * 2.5) * (c ^ (1 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ))) *
          (hankelScaleBandC * S_r * u_norm ^ (1 / 2 : ℝ)) * (X⁻¹ * X ^ (-(1 / 2 : ℝ))) := by
      rw [div_eq_mul_inv]; ring
    rw [heq, hc_cancel, hX32, mul_one]
    have hX32_nn : 0 ≤ X ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hX0.le _
    calc ((100 / 81 : ℝ) * 1.11 * 2.5) * (hankelScaleBandC * S_r * u_norm ^ (1 / 2 : ℝ)) * X ^ (-(3 / 2 : ℝ))
        ≤ ((100 / 81 : ℝ) * 1.11 * 2.5) * (34.1 * hankelScaleBandC * L_r * u_norm ^ (-(3 / 4 : ℝ))) *
            X ^ (-(3 / 2 : ℝ)) := by gcongr
      _ ≤ 118 * hankelScaleBandC * L_r * X ^ (-(3 / 2 : ℝ)) * u_norm ^ (-(3 / 4 : ℝ)) := by
          have : 0 ≤ hankelScaleBandC * L_r * X ^ (-(3 / 2 : ℝ)) * u_norm ^ (-(3 / 4 : ℝ)) := by
            have := Real.rpow_nonneg hN0.le (-(3 / 4 : ℝ))
            positivity
          nlinarith
  have herr : c ^ (1 / 3 : ℝ) * (62 * c ^ (-(2 : ℝ))) ≤
      hankelScaleBandC * L_r * X ^ (-(3 / 2 : ℝ)) * u_norm ^ (-(3 / 4 : ℝ)) := by
    have hc_inv : c ^ (1 / 3 : ℝ) * c ^ (-(2 : ℝ)) ≤ c⁻¹ := by
      rw [← Real.rpow_add hc0, ← Real.rpow_neg_one c]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hL2 := hankel_window_L2 hc0 hN0 hNc hX0 hXN
    have hX_inv_eq : u_norm ^ (-(3 / 4 : ℝ)) / (X * √X) = X ^ (-(3 / 2 : ℝ)) * u_norm ^ (-(3 / 4 : ℝ)) := by
      have h1 : X * √X = X ^ (3 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        calc X * X ^ (1 / 2 : ℝ) = X ^ (1 : ℝ) * X ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
          _ = X ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hX0]; norm_num
      rw [h1, div_eq_mul_inv, ← Real.rpow_neg hX0.le, mul_comm]
    rw [hX_inv_eq] at hL2
    have h62_le : (62 : ℝ) ≤ hankelScaleBandC := by unfold hankelScaleBandC; norm_num
    have hpow_nn : 0 ≤ X ^ (-(3 / 2 : ℝ)) * u_norm ^ (-(3 / 4 : ℝ)) :=
      mul_nonneg (Real.rpow_nonneg hX0.le _) (Real.rpow_nonneg hN0.le _)
    calc c ^ (1 / 3 : ℝ) * (62 * c ^ (-(2 : ℝ)))
        = 62 * (c ^ (1 / 3 : ℝ) * c ^ (-(2 : ℝ))) := by ring
      _ ≤ 62 * c⁻¹ := by gcongr
      _ ≤ hankelScaleBandC * c⁻¹ := by gcongr
      _ ≤ hankelScaleBandC * (X ^ (-(3 / 2 : ℝ)) * u_norm ^ (-(3 / 4 : ℝ))) := by gcongr
      _ ≤ hankelScaleBandC * L_r * X ^ (-(3 / 2 : ℝ)) * u_norm ^ (-(3 / 4 : ℝ)) := by
          nlinarith [mul_nonneg hHSC.le (sub_nonneg.2 hL_ge1)]
  have h_res_nn : 0 ≤ hankelScaleBandC * L_r * X ^ (-(3 / 2 : ℝ)) * u_norm ^ (-(3 / 4 : ℝ)) := by
    have := Real.rpow_nonneg hX0.le (-(3 / 2 : ℝ))
    have := Real.rpow_nonneg hN0.le (-(3 / 4 : ℝ))
    have := hL_ge1
    positivity
  rw [mul_add]
  linarith [hmain, herr, h_res_nn]

private structure ScaleSaddleData (c r : ℝ) (u : ℂ) where
  q : ℂ
  ζ : ℂ
  σ : ℝ
  τ0 : ℝ
  h : ℝ
  hq : q ∈ slitPlane
  hqn : ‖q‖ ≤ 0.035 ^ 2
  hqu : langerUtilde etaC c q = u
  hζdef : ζ = saddleRoot q
  hqg : -gSer etaC ζ = Complex.log (1 + chartYinv etaC (u / ((c ^ (2 / 3 : ℝ) * langerKappa : ℝ) : ℂ)))
  hζeq : ζ = (σ : ℂ) + (τ0 : ℂ) * Complex.I
  hσpos : 0 < σ
  hσle : σ ≤ 0.035
  hτ0 : |τ0| ≤ 0.035
  hζn : ‖ζ‖ ≤ 0.035
  hh0 : 0 ≤ h
  hhsq : h ^ 2 = 5 * Real.log c / (c * σ)
  hhle : h ≤ 1 / 10 * ‖ζ‖
  hcσ_lb : 30 * Real.log c ≤ c * σ
  hcσ_X23 : (u ^ (1 / 2 : ℂ)).re * c ^ (2 / 3 : ℝ) / 0.751 ≤ c * σ
  hζ_rho_lo : 9 / 10 * rhoR hankelBandParams c r ≤ ‖ζ‖
  hζ_rho_hi : ‖ζ‖ ≤ 11 / 10 * rhoR hankelBandParams c r
  hζsig_ratio : ‖ζ‖ / σ ≤ 1.002 * ‖u‖ ^ (1 / 2 : ℝ) / (u ^ (1 / 2 : ℂ)).re

private lemma scale_cσ_bounds {c R_J r θ σ ζ_norm u_norm : ℝ}
    (hc : 1e14 ≤ c) (hRJ_ub : R_J ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1)
    (hr_lb : 256 ≤ r) (hr_RJ : r ≤ R_J) (hlo : r - 1 ≤ u_norm) (_hhi : u_norm ≤ r + 1)
    (hs1 : 0.99 * √r ≤ u_norm ^ (1 / 2 : ℝ))
    (hθ_pos : 0 < θ) (hθr : 250 * Real.log c ≤ θ * r ^ (3 / 2 : ℝ))
    (hσ_lb : θ * √u_norm / (0.751 * c ^ (1 / 3 : ℝ)) ≤ σ)
    (hζ_lb : u_norm ^ (1 / 2 : ℝ) / (0.751 * c ^ (1 / 3 : ℝ)) ≤ ζ_norm) :
    500 * Real.log c ≤ c * σ * ζ_norm ^ 2 ∧ 30 * Real.log c ≤ c * σ := by
  have hc0 : 0 < c := by linarith
  have hr0 : 0 < r := by linarith
  have hN0 : 0 < u_norm := by linarith
  set k : ℝ := c ^ (1 / 3 : ℝ)
  have hk0 : 0 < k := Real.rpow_pos_of_pos hc0 _
  have hkc23 : c = k * k ^ 2 := by
    dsimp [k]; rw [← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; norm_num
  have hc23_eq : k ^ 2 = c ^ (2 / 3 : ℝ) := by
    dsimp [k]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hsqrtN_eq : √u_norm = u_norm ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hu32_eq : √u_norm * (u_norm ^ (1 / 2 : ℝ)) ^ 2 = u_norm ^ (3 / 2 : ℝ) := by
    rw [hsqrtN_eq, ← Real.rpow_natCast (u_norm ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]; norm_num
  have hu32_lb : 0.99 * r ^ (3 / 2 : ℝ) ≤ u_norm ^ (3 / 2 : ℝ) := by
    have h1 : 0.994 * r ≤ u_norm := by linarith
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 3 / 2)
    rw [Real.mul_rpow (by norm_num) hr0.le] at h2
    have h0994 : (0.99 : ℝ) ≤ (0.994 : ℝ) ^ (3 / 2 : ℝ) := by
      have hsq : (0.99 : ℝ) ^ 2 ≤ ((0.994 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 := by
        rw [← Real.rpow_natCast ((0.994 : ℝ) ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul (by norm_num)]; norm_num
      exact (abs_le_of_sq_le_sq' hsq (Real.rpow_nonneg (by norm_num) _)).2
    calc 0.99 * r ^ (3 / 2 : ℝ) ≤ (0.994 : ℝ) ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right h0994 (Real.rpow_nonneg hr0.le _)
      _ ≤ u_norm ^ (3 / 2 : ℝ) := h2
  have hcσζ : 500 * Real.log c ≤ c * σ * ζ_norm ^ 2 := by
    have h1 : (u_norm ^ (1 / 2 : ℝ)) ^ 2 / (0.751 * k) ^ 2 ≤ ζ_norm ^ 2 := by
      rw [← div_pow]; exact pow_le_pow_left₀ (by positivity) hζ_lb 2
    have hσ0_nn : 0 ≤ σ :=
      (div_nonneg (mul_nonneg hθ_pos.le (Real.sqrt_nonneg _)) (by positivity)).trans hσ_lb
    have h2 : (θ * √u_norm / (0.751 * k)) * ((u_norm ^ (1 / 2 : ℝ)) ^ 2 / (0.751 * k) ^ 2) ≤ σ * ζ_norm ^ 2 :=
      mul_le_mul hσ_lb h1 (by positivity) hσ0_nn
    have h3 : c * ((θ * √u_norm / (0.751 * k)) * ((u_norm ^ (1 / 2 : ℝ)) ^ 2 / (0.751 * k) ^ 2)) =
        θ * u_norm ^ (3 / 2 : ℝ) / 0.751 ^ 3 := by
      have hden : c = k ^ 3 := by rw [hkc23]; ring
      rw [hden, ← hu32_eq]; field_simp [hk0.ne']
    have h4 : 500 * Real.log c ≤ θ * u_norm ^ (3 / 2 : ℝ) / 0.751 ^ 3 := by
      have hlog0 : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
      have hmul : 0.99 * (θ * r ^ (3 / 2 : ℝ)) ≤ θ * u_norm ^ (3 / 2 : ℝ) := by
        calc 0.99 * (θ * r ^ (3 / 2 : ℝ)) = θ * (0.99 * r ^ (3 / 2 : ℝ)) := by ring
          _ ≤ θ * u_norm ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_left hu32_lb hθ_pos.le
      rw [le_div_iff₀ (by positivity)]
      calc (500 * Real.log c) * 0.751 ^ 3 ≤ 0.99 * (250 * Real.log c) := by nlinarith [hlog0]
        _ ≤ 0.99 * (θ * r ^ (3 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hθr (by norm_num)
        _ ≤ θ * u_norm ^ (3 / 2 : ℝ) := hmul
    linarith [h3, h4, mul_le_mul_of_nonneg_left h2 hc0.le]
  have hcσ_lb : 30 * Real.log c ≤ c * σ := by
    have hr_half : √r = r ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow r
    have h1 : 0.99 * r ^ (1 / 2 : ℝ) ≤ √u_norm := by rwa [← hsqrtN_eq, hr_half] at hs1
    have h2 : c / (0.751 * k) = k ^ 2 / 0.751 := by rw [hkc23]; field_simp [hk0.ne']
    have h3 : (k ^ 2 / 0.751) * (θ * (0.99 * r ^ (1 / 2 : ℝ))) ≤ c * σ := by
      calc (k ^ 2 / 0.751) * (θ * (0.99 * r ^ (1 / 2 : ℝ)))
          = c * (θ * (0.99 * r ^ (1 / 2 : ℝ)) / (0.751 * k)) := by rw [← h2]; ring
        _ ≤ c * (θ * √u_norm / (0.751 * k)) := by gcongr
        _ ≤ c * σ := mul_le_mul_of_nonneg_left hσ_lb hc0.le
    have hk2_r : 5000 * r ≤ k ^ 2 := by
      rw [hc23_eq]
      have hc23_1e9 := scale_c23_ge hc
      have : r ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1 := hr_RJ.trans hRJ_ub
      linarith
    have hr32_eq : r ^ (3 / 2 : ℝ) = r * r ^ (1 / 2 : ℝ) := by
      have hadd := Real.rpow_add hr0 1 (1 / 2)
      rw [Real.rpow_one] at hadd
      rw [← hadd]; congr 1; norm_num
    have h4 : 5000 * (θ * r ^ (3 / 2 : ℝ)) = 5000 * r * (θ * r ^ (1 / 2 : ℝ)) := by rw [hr32_eq]; ring
    have h5 : 5000 * (250 * Real.log c) ≤ k ^ 2 * (θ * r ^ (1 / 2 : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_right hk2_r (mul_nonneg hθ_pos.le (Real.rpow_nonneg hr0.le (1 / 2 : ℝ)))
      linarith [hθr, h4]
    have hlog0 : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
    calc 30 * Real.log c ≤ (0.99 / 0.751) * (5000 * (250 * Real.log c)) := by nlinarith only [hlog0]
      _ ≤ (0.99 / 0.751) * (k ^ 2 * (θ * r ^ (1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h5 (by norm_num)
      _ = (k ^ 2 / 0.751) * (θ * (0.99 * r ^ (1 / 2 : ℝ))) := by ring
      _ ≤ c * σ := h3
  exact ⟨hcσζ, hcσ_lb⟩

private noncomputable def scale_saddle_params {c R_J r θ : ℝ} {u : ℂ}
    (hc : 1e14 ≤ c)
    (hRJ_ub : R_J ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1)
    (hr_lb : 256 ≤ r) (hr_RJ : r ≤ R_J)
    (hlo : r - 1 ≤ ‖u‖) (hhi : ‖u‖ ≤ r + 1)
    (hθ_pos : 0 < θ) (hθr : 250 * Real.log c ≤ θ * r ^ (3 / 2 : ℝ))
    (hX_lb : θ * √‖u‖ ≤ (u ^ (1 / 2 : ℂ)).re) : ScaleSaddleData c r u := by
  have hc0 : 0 < c := by linarith
  have hr0 : 0 < r := by linarith
  have hN0 : 0 < ‖u‖ := by linarith
  obtain ⟨_, hdisc, _, hs1, hs2⟩ := scale_radius_bounds hc hRJ_ub hr_lb hr_RJ hlo hhi
  set X : ℝ := (u ^ (1 / 2 : ℂ)).re
  have hXpos : 0 < X := lt_of_lt_of_le (mul_pos hθ_pos (Real.sqrt_pos.mpr hN0)) hX_lb
  have hcut : ¬ (u.im = 0 ∧ u.re ≤ 0) := scale_not_neg_real hN0 hXpos
  set K : ℝ := c ^ (2 / 3 : ℝ) * langerKappa
  have hK0 : 0 < K := mul_pos (Real.rpow_pos_of_pos hc0 _) langerKappa_pos
  set y : ℂ := u / (K : ℂ)
  have huy : (K : ℂ) * y = u := by
    dsimp [y]; field_simp [show (K : ℂ) ≠ 0 by exact_mod_cast hK0.ne']
  have hyn : ‖y‖ ≤ 4.94e-4 := by
    dsimp [y]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK0, div_le_iff₀ hK0]
    exact hdisc.trans_eq (by unfold langerRadius langerScale; ring)
  have hsd := chart_saddle_data langerEta_etaC hc0 hyn (by rw [huy]; exact hcut)
  let q := hsd.choose
  have hq : q ∈ slitPlane := hsd.choose_spec.1
  have hqn : ‖q‖ ≤ 0.035 ^ 2 := hsd.choose_spec.2.1
  have hqu : langerUtilde etaC c q = u := by rw [← huy]; exact hsd.choose_spec.2.2.1
  have hqg : -gSer etaC (saddleRoot q) = Complex.log (1 + chartYinv etaC y) :=
    hsd.choose_spec.2.2.2
  have hgeom := hankel_saddle_geom hc0 hq hqn hqu
  set ζ := saddleRoot q
  have hζn : ‖ζ‖ ≤ 0.035 := norm_saddleRoot_le hqn
  have hσpos : 0 < ζ.re := re_saddleRoot_pos hq
  set σ : ℝ := ζ.re
  set τ0 : ℝ := ζ.im
  have hζeq : ζ = (σ : ℂ) + (τ0 : ℂ) * Complex.I := (Complex.re_add_im ζ).symm
  have hσle : σ ≤ 0.035 := (Complex.re_le_norm ζ).trans hζn
  have hτ0 : |τ0| ≤ 0.035 := (Complex.abs_im_le_norm ζ).trans hζn
  set k : ℝ := c ^ (1 / 3 : ℝ)
  have hk0 : 0 < k := Real.rpow_pos_of_pos hc0 _
  set M : ℝ := k * langerMu
  have hM0 : 0 < M := mul_pos hk0 langerMu_pos
  obtain ⟨g1, g2, _, g4⟩ := hgeom
  have hμ_bound : 1.0009 * M ≤ 0.751 * k := by
    have : 1.0009 * langerMu ≤ 0.751 := by nlinarith [langerMu_lt]
    calc 1.0009 * (k * langerMu) = k * (1.0009 * langerMu) := by ring
      _ ≤ k * 0.751 := mul_le_mul_of_nonneg_left this hk0.le
      _ = 0.751 * k := by ring
  have hσ_lb : θ * √‖u‖ / (0.751 * k) ≤ σ := by
    have h1 : θ * √‖u‖ ≤ 0.751 * k * σ := (hX_lb.trans g4).trans (mul_le_mul_of_nonneg_right hμ_bound hσpos.le)
    rw [div_le_iff₀ (by positivity)]; linarith
  have hζ_lb : ‖u‖ ^ (1 / 2 : ℝ) / (0.751 * k) ≤ ‖ζ‖ := by
    have h1 : ‖u‖ ^ (1 / 2 : ℝ) ≤ 0.751 * k * ‖ζ‖ := g2.trans (mul_le_mul_of_nonneg_right hμ_bound (norm_nonneg ζ))
    rw [div_le_iff₀ (by positivity)]; linarith
  obtain ⟨hcσζ, hcσ_lb⟩ := scale_cσ_bounds hc hRJ_ub hr_lb hr_RJ hlo hhi hs1 hθ_pos hθr hσ_lb hζ_lb
  have hc23_eq : k ^ 2 = c ^ (2 / 3 : ℝ) := by
    dsimp [k]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hkc23 : c = k * k ^ 2 := by
    dsimp [k]; rw [← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; norm_num
  have hcσ_X23 : X * c ^ (2 / 3 : ℝ) / 0.751 ≤ c * σ := by
    have h1 : X ≤ 0.751 * k * σ := g4.trans (mul_le_mul_of_nonneg_right hμ_bound hσpos.le)
    rw [div_le_iff₀ (by norm_num), ← hc23_eq]
    calc X * k ^ 2 ≤ (0.751 * k * σ) * k ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 0.751 * (k * k ^ 2 * σ) := by ring
      _ = c * σ * 0.751 := by rw [← hkc23]; ring
  set h := Real.sqrt (5 * Real.log c / (c * σ))
  have hcσ0 : 0 < c * σ := by positivity
  have hlog0 : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  have hh0 : 0 ≤ h := Real.sqrt_nonneg _
  have hhsq : h ^ 2 = 5 * Real.log c / (c * σ) := Real.sq_sqrt (by positivity)
  have hhle : h ≤ 1 / 10 * ‖ζ‖ := by
    refine (Real.sqrt_le_left (by positivity)).mpr ?_
    rw [div_le_iff₀ hcσ0]
    nlinarith [hcσζ]
  have hρ : rhoR hankelBandParams c r = √r / M := rhoR_hankel_eq hc0
  have hζ_rho_lo : 9 / 10 * rhoR hankelBandParams c r ≤ ‖ζ‖ := by
    rw [hρ, mul_div_assoc', div_le_iff₀ hM0]; linarith [g2, hs1]
  have hζ_rho_hi : ‖ζ‖ ≤ 11 / 10 * rhoR hankelBandParams c r := by
    rw [hρ, mul_div_assoc', le_div_iff₀ hM0]; linarith [g1, hs2]
  have hζsig_ratio : ‖ζ‖ / σ ≤ 1.002 * ‖u‖ ^ (1 / 2 : ℝ) / X := by
    rw [div_le_div_iff₀ hσpos hXpos]
    have h1 : ‖ζ‖ * X ≤ 1.0009 * (M * ‖ζ‖ * σ) := by
      calc ‖ζ‖ * X ≤ ‖ζ‖ * (1.0009 * M * σ) := mul_le_mul_of_nonneg_left g4 (norm_nonneg ζ)
        _ = 1.0009 * (M * ‖ζ‖ * σ) := by ring
    have h2 : 0.9991 * (M * ‖ζ‖ * σ) ≤ ‖u‖ ^ (1 / 2 : ℝ) * σ := by
      calc 0.9991 * (M * ‖ζ‖ * σ) = (0.9991 * M * ‖ζ‖) * σ := by ring
        _ ≤ ‖u‖ ^ (1 / 2 : ℝ) * σ := mul_le_mul_of_nonneg_right g1 hσpos.le
    have hMζσ : 0 ≤ M * ‖ζ‖ * σ := mul_nonneg (mul_nonneg hM0.le (norm_nonneg ζ)) hσpos.le
    have hmul : 1.0009 * (M * ‖ζ‖ * σ) ≤ 1.002 * (0.9991 * (M * ‖ζ‖ * σ)) := by nlinarith only [hMζσ]
    calc ‖ζ‖ * X ≤ 1.0009 * (M * ‖ζ‖ * σ) := h1
      _ ≤ 1.002 * (0.9991 * (M * ‖ζ‖ * σ)) := hmul
      _ ≤ 1.002 * (‖u‖ ^ (1 / 2 : ℝ) * σ) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 1.002 * ‖u‖ ^ (1 / 2 : ℝ) * σ := by ring
  exact ⟨q, ζ, σ, τ0, h, hq, hqn, hqu, rfl, hqg, hζeq, hσpos, hσle, hτ0, hζn, hh0, hhsq, hhle,
    hcσ_lb, hcσ_X23, hζ_rho_lo, hζ_rho_hi, hζsig_ratio⟩

private lemma scale_W_bound {c ε T u_T R_J r σ τ0 h u_norm X Q_r : ℝ} {f : ℝ → ℝ} {ζ : ℂ}
    (hc3e6 : 3e6 ≤ c) (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1)
    (hmass : hankelMass c f = 1) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T) (hT : c * hankelXi c u_T = T)
    (hRJ_lb : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R_J)
    (hRJ_ub : R_J ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1)
    (hr_lb : 256 ≤ r) (hr_RJ : r ≤ R_J)
    (hζeq : ζ = (σ : ℂ) + (τ0 : ℂ) * Complex.I)
    (hσpos : 0 < σ) (hσ1 : σ < 1) (hXpos : 0 < X)
    (hhle : h ≤ 1 / 10 * ‖ζ‖)
    (hζ_rho_lo : 9 / 10 * rhoR hankelBandParams c r ≤ ‖ζ‖)
    (hζ_rho_hi : ‖ζ‖ ≤ 11 / 10 * rhoR hankelBandParams c r)
    (hζsig_ratio : ‖ζ‖ / σ ≤ 1.002 * u_norm ^ (1 / 2 : ℝ) / X)
    (hQ_def : Q_r = hankelScaleBandC *
      (r ^ (-(3 / 2 : ℝ)) + r ^ (-(7 / 4 : ℝ)) * min (1028 * r) R_J * hankelBootB1 c f (min (1028 * r) R_J) u_T +
        r ^ (-(3 / 4 : ℝ)) * (hankelBootB2 c f r + hankelBootB2 c f R_J)))
    (hQ_nn : 0 ≤ Q_r) (hu_nn : 0 ≤ u_norm) :
    ∀ y0 : ℝ, |y0 - τ0| ≤ h →
      ‖hankelWt c f ((σ : ℂ) + (y0 : ℂ) * Complex.I)‖ ≤ Q_r * (1.11 * u_norm ^ (1 / 2 : ℝ) / X) := by
  intro y0 hy0
  set ζ₀ : ℂ := (σ : ℂ) + (y0 : ℂ) * Complex.I
  have hdiff : ‖ζ₀ - ζ‖ = |y0 - τ0| := by
    have : ζ₀ - ζ = ((y0 - τ0 : ℝ) : ℂ) * Complex.I := by rw [hζeq]; push_cast; ring
    rw [this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  have hd1 := norm_sub_norm_le ζ₀ ζ
  have hd2 := norm_sub_norm_le ζ ζ₀
  rw [norm_sub_rev] at hd2
  rw [hdiff] at hd1 hd2
  have hζ₀lo : 9 / 10 * ‖ζ‖ ≤ ‖ζ₀‖ := by linarith
  have hζ₀hi : ‖ζ₀‖ ≤ 11 / 10 * ‖ζ‖ := by linarith
  have hre₀ : ζ₀.re = σ := by simp [ζ₀]
  have hζ₀pos : 0 < ‖ζ₀‖ := by
    have hre_le := Complex.re_le_norm ζ₀
    rw [hre₀] at hre_le
    linarith
  have hlo₀ : rhoR hankelBandParams c r / 3 ≤ ‖ζ₀‖ := by
    have : 0 ≤ rhoR hankelBandParams c r := by
      unfold rhoR; have := hankelBandParams.hκ_ζ; positivity
    linarith
  have hhi₀ : ‖ζ₀‖ ≤ 2 * rhoR hankelBandParams c r := by linarith
  have hq₀ : σ / ‖ζ₀‖ ≤ 1 := by
    rw [div_le_one hζ₀pos]
    have hre_le := Complex.re_le_norm ζ₀
    rwa [hre₀] at hre_le
  set ψ := Real.arccos (σ / ‖ζ₀‖)
  have hq_ge : -(1 : ℝ) ≤ σ / ‖ζ₀‖ := by
    have : 0 ≤ σ / ‖ζ₀‖ := div_nonneg hσpos.le hζ₀pos.le
    linarith
  have hcosψ : Real.cos ψ = σ / ‖ζ₀‖ := Real.cos_arccos hq_ge hq₀
  have hcos_eq : ζ₀.re = ‖ζ₀‖ * Real.cos ψ := by
    rw [hcosψ, hre₀]; field_simp [hζ₀pos.ne']
  have hcos_pos : 0 < Real.cos ψ := by rw [hcosψ]; positivity
  have hfe := hf.toIsHankelEigenfn
  have hband := hankel_scale_band_reduction_B1 hc3e6 hε hfe hmass hu0 hu3 hT
    (fun Δ hΔ => hf.tail_nonneg Δ hΔ) hRJ_lb hRJ_ub hr_lb hr_RJ hlo₀ hhi₀ hcos_eq hcos_pos
  rw [hankelWtS_eq (by linarith) hfe (by rw [hre₀]; exact hσpos.le) (by rw [hre₀]; exact hσ1)] at hband
  refine hband.trans ?_
  rw [← hQ_def, hcosψ, div_div_eq_mul_div, mul_div_assoc Q_r ‖ζ₀‖ σ]
  refine mul_le_mul_of_nonneg_left ?_ hQ_nn
  calc ‖ζ₀‖ / σ ≤ (11 / 10 * ‖ζ‖) / σ := div_le_div_of_nonneg_right hζ₀hi hσpos.le
    _ = (11 / 10) * (‖ζ‖ / σ) := by ring
    _ ≤ (11 / 10) * (1.002 * u_norm ^ (1 / 2 : ℝ) / X) := by gcongr
    _ = ((11 / 10 : ℝ) * 1.002) * (u_norm ^ (1 / 2 : ℝ) / X) := by ring
    _ ≤ 1.11 * (u_norm ^ (1 / 2 : ℝ) / X) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = 1.11 * u_norm ^ (1 / 2 : ℝ) / X := by ring

set_option maxHeartbeats 800000 in
/-- **Scale-`r` covered window bound** (`ct:cov`, P1 Step 1b):
for `c ≥ 10¹⁴`, `R_J ∈ [(1/100)² c^{2/3}, (1/100)² c^{2/3} + 1]`, any scale `r ∈ [256, R_J]`,
and any `u ∈ ℂ` in the annulus `r - 1 ≤ ‖u‖ ≤ r + 1` satisfying `θ √‖u‖ ≤ Re(u^{1/2})` with
`250 log c ≤ θ r^{3/2}`, we have
`‖Ψ̃_c(u)‖ ≤ hankelScaleWindowC * L_r * airyEnv u * (Re u^{1/2})^{-3/2} * ‖u‖^{-3/4}`. -/
theorem hankel_scale_cov_window {c ε T u_T R_J r θ : ℝ} {f : ℝ → ℝ} {u : ℂ}
    (hc : 1e14 ≤ c) (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1)
    (hmass : hankelMass c f = 1) (hT : c * hankelXi c u_T = T)
    (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T)
    (hRJ_lb : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R_J)
    (hRJ_ub : R_J ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1)
    (hr_lb : 256 ≤ r) (hr_RJ : r ≤ R_J)
    (hlo : r - 1 ≤ ‖u‖) (hhi : ‖u‖ ≤ r + 1)
    (hθ_pos : 0 < θ) (hθr : 250 * Real.log c ≤ θ * r ^ (3 / 2 : ℝ))
    (hX_lb : θ * √‖u‖ ≤ (u ^ (1 / 2 : ℂ)).re) :
    ‖hankelPsi c f u‖ ≤ hankelScaleWindowC * hankelScaleL c R_J r u_T f *
      airyEnv u * ((u ^ (1 / 2 : ℂ)).re) ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hc3e6 : 3e6 ≤ c := by linarith
  have hN0 : 0 < ‖u‖ := by linarith
  have hfe := hf.toIsHankelEigenfn
  obtain ⟨hRJ_A, _, huc, _, hs2⟩ := scale_radius_bounds hc hRJ_ub hr_lb hr_RJ hlo hhi
  set X : ℝ := (u ^ (1 / 2 : ℂ)).re
  have hXpos : 0 < X := lt_of_lt_of_le (mul_pos hθ_pos (Real.sqrt_pos.mpr hN0)) hX_lb
  have hXN : X ≤ ‖u‖ ^ (1 / 2 : ℝ) := by
    have hnorm : ‖u ^ (1 / 2 : ℂ)‖ = ‖u‖ ^ (1 / 2 : ℝ) := by
      rw [Complex.norm_cpow_of_ne_zero (norm_pos_iff.mp hN0)]
      simp
    exact (Complex.re_le_norm _).trans_eq hnorm
  have sd := scale_saddle_params hc hRJ_ub hr_lb hr_RJ hlo hhi hθ_pos hθr hX_lb
  set q := sd.q; set ζ := sd.ζ; set σ := sd.σ; set τ0 := sd.τ0; set h := sd.h
  have hq := sd.hq; have hqn := sd.hqn; have hqu := sd.hqu; have hζdef := sd.hζdef
  have hqg := sd.hqg; have hζeq := sd.hζeq; have hσpos := sd.hσpos; have hσle := sd.hσle
  have hτ0 := sd.hτ0; have hζn := sd.hζn; have hh0 := sd.hh0; have hhsq := sd.hhsq
  have hhle := sd.hhle; have hcσ_lb := sd.hcσ_lb; have hcσ_X23 := sd.hcσ_X23
  have hζ_rho_lo := sd.hζ_rho_lo; have hζ_rho_hi := sd.hζ_rho_hi; have hζsig_ratio := sd.hζsig_ratio
  have hσ1 : σ < 1 := by linarith
  set r_til := min (1028 * r) R_J
  set Q_r : ℝ := hankelScaleBandC *
    (r ^ (-(3 / 2 : ℝ)) + r ^ (-(7 / 4 : ℝ)) * r_til * hankelBootB1 c f r_til u_T +
      r ^ (-(3 / 4 : ℝ)) * (hankelBootB2 c f r + hankelBootB2 c f R_J))
  set W : ℝ := Q_r * (1.11 * ‖u‖ ^ (1 / 2 : ℝ) / X)
  have hB1_nn := hankelScaleB1_til_nonneg hc3e6 hf hε hmass hT hu0 hu3 hr_lb hr_RJ hRJ_A
  have hQ_nn : 0 ≤ Q_r := by
    have h2 := hankelBootB2_nonneg c f r
    have h3 := hankelBootB2_nonneg c f R_J
    have hHSC : 0 ≤ hankelScaleBandC := by unfold hankelScaleBandC; norm_num
    have hp1 : 0 ≤ r ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
    have hp2 : 0 ≤ r ^ (-(7 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
    have hp3 : 0 ≤ r ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
    have hrt0 : 0 ≤ r_til := le_min (by positivity) (by linarith)
    positivity
  have hW0 : 0 ≤ W := by
    have : 0 ≤ ‖u‖ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hN0.le _
    positivity
  have hW_bd : ∀ y0 : ℝ, |y0| ≤ 1 / 3 → |y0 - τ0| ≤ h →
      ‖hankelWt c f ((σ : ℂ) + (y0 : ℂ) * Complex.I)‖ ≤ W :=
    fun y0 _ hy0 => scale_W_bound hc3e6 hf hε hmass hu0 hu3 hT hRJ_lb hRJ_ub hr_lb hr_RJ
      hζeq hσpos hσ1 hXpos hhle hζ_rho_lo hζ_rho_hi hζsig_ratio rfl hQ_nn hN0.le y0 hy0
  set ℓ : ℂ := -(gSer etaC ζ)
  have hl : ℓ.re ≤ 1 / 200 := by
    have h1 := Complex.re_le_norm ℓ
    rw [show ℓ = -(gSer etaC ζ) from rfl, norm_neg] at h1
    exact h1.trans (norm_gSer_small hζn)
  have hcrit : gSer etaC ((σ : ℂ) + (τ0 : ℂ) * Complex.I) + ℓ = 0 := by
    dsimp [ℓ, ζ]; rw [← hζeq]; ring
  have hwin := hankel_local_density_window (by linarith) hfe hε hmass ℓ hl hσpos hσle hτ0 hcrit
    hh0 hW0 hW_bd
  have hph : (c : ℂ) * hankelLocPhi ℓ ((σ : ℂ) + (τ0 : ℂ) * Complex.I) =
      -(4 / 3 : ℂ) * u ^ (3 / 2 : ℂ) := by
    rw [← hζeq]
    conv_rhs => rw [← hqu]
    dsimp [ℓ, ζ]
    rw [hζdef, ← phase_at_saddle langerEta_etaC hc0 hq hqn]
    unfold hankelLocPhi; ring
  have hexp : Real.exp (c * (hankelLocPhi ℓ ((σ : ℂ) + (τ0 : ℂ) * Complex.I)).re) = airyEnv u := by
    rw [← scale_norm_exp_eq_airyEnv u, ← hph, Complex.norm_exp]
    congr 1; simp [Complex.mul_re]
  rw [hexp] at hwin
  set y_c : ℂ := u / ((c ^ (2 / 3 : ℝ) * langerKappa : ℝ) : ℂ)
  have hloc_eq : hankelLocal c f (Complex.log (1 + chartYinv etaC y_c)) =
      ∫ τ in (-(1 / 3 : ℝ))..(1 / 3), hankelJ c f ℓ (((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) := by
    unfold hankelLocal
    rw [← hqg]
  have hcσ0 : 0 < c * σ := by positivity
  have hsqrt_le : Real.sqrt (Real.pi / ((2 / 5) * c * σ)) ≤
      2.5 * c ^ (-(1 / 3 : ℝ)) * X ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hpi : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
    have hc23 : (c ^ (-(1 / 3 : ℝ))) ^ 2 = c ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    have hX_inv : (X ^ (-(1 / 2 : ℝ))) ^ 2 = X⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]; norm_num; exact Real.rpow_neg_one X
    rw [mul_pow, mul_pow, hc23, hX_inv, div_le_iff₀ (by positivity)]
    have hc23_pos : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    have h_inv23 : c ^ (-(2 / 3 : ℝ)) = (c ^ (2 / 3 : ℝ))⁻¹ := Real.rpow_neg hc0.le _
    rw [h_inv23]
    have hprod_id : (c ^ (2 / 3 : ℝ))⁻¹ * X⁻¹ * (X * c ^ (2 / 3 : ℝ) / 0.751) = 1 / 0.751 := by
      field_simp [hc23_pos.ne', hXpos.ne']
    calc Real.pi ≤ 2.5 ^ 2 * (2 / 5 : ℝ) * (1 / 0.751) := by linarith
      _ = 2.5 ^ 2 * ((c ^ (2 / 3 : ℝ))⁻¹ * X⁻¹) * ((2 / 5 : ℝ) * (X * c ^ (2 / 3 : ℝ) / 0.751)) := by
          rw [← hprod_id]; ring
      _ ≤ 2.5 ^ 2 * ((c ^ (2 / 3 : ℝ))⁻¹ * X⁻¹) * ((2 / 5 : ℝ) * (c * σ)) := by
          have := mul_le_mul_of_nonneg_left hcσ_X23 (by norm_num : (0 : ℝ) ≤ 2 / 5)
          gcongr
      _ = 2.5 ^ 2 * (c ^ (2 / 3 : ℝ))⁻¹ * X⁻¹ * ((2 / 5) * c * σ) := by ring
  have hgauss : Real.exp (-((2 / 5) * c * σ * h ^ 2)) = c ^ (-(2 : ℝ)) := by
    rw [hhsq]
    have hmul_eq : (2 / 5 : ℝ) * c * σ * (5 * Real.log c / (c * sd.σ)) = 2 * Real.log c := by
      change (2 / 5 : ℝ) * c * sd.σ * (5 * Real.log c / (c * sd.σ)) = 2 * Real.log c
      field_simp [hc0.ne', hσpos.ne']
    rw [hmul_eq, neg_mul_eq_mul_neg, mul_comm, Real.exp_mul, Real.exp_neg, Real.exp_log hc0,
      ← Real.rpow_neg_one, ← Real.rpow_mul hc0.le]
    congr 1; norm_num
  have htail_e : 2 * (2 * Real.exp (-(0.035 * c * σ)) / (0.07 * c)) ≤ 60 * c ^ (-(2 : ℝ)) := by
    have hexp_le : Real.exp (-(0.035 * c * σ)) ≤ c⁻¹ := by
      calc Real.exp (-(0.035 * c * σ)) ≤ Real.exp (-Real.log c) :=
            Real.exp_le_exp.mpr (by nlinarith [hcσ_lb])
        _ = c⁻¹ := by rw [Real.exp_neg, Real.exp_log hc0]
    have hfrac : 2 * (2 * Real.exp (-(0.035 * c * σ)) / (0.07 * c)) ≤ 2 * (2 * c⁻¹ / (0.07 * c)) := by
      gcongr
    refine hfrac.trans ?_
    have hc2 : c ^ (-(2 : ℝ)) = (c ^ 2)⁻¹ := by
      rw [Real.rpow_neg hc0.le]; norm_cast
    rw [hc2]
    calc 2 * (2 * c⁻¹ / (0.07 * c)) = (4 / 0.07) * (c ^ 2)⁻¹ := by field_simp [hc0.ne']; ring
      _ ≤ 60 * (c ^ 2)⁻¹ := by gcongr; norm_num
  have hloc_le :
      ‖hankelLocal c f (Complex.log (1 + chartYinv etaC y_c))‖ ≤
        airyEnv u *
          ((100 / 81 : ℝ) * W * (2.5 * c ^ (-(1 / 3 : ℝ)) * X ^ (-(1 / 2 : ℝ))) +
            62 * c ^ (-(2 : ℝ))) := by
    rw [hloc_eq]
    refine hwin.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (airyEnv_pos u).le
    have he1 : (100 / 81 : ℝ) * W * Real.sqrt (Real.pi / ((2 / 5) * c * σ)) ≤
        (100 / 81 : ℝ) * W * (2.5 * c ^ (-(1 / 3 : ℝ)) * X ^ (-(1 / 2 : ℝ))) := by gcongr
    have hc2_nn : 0 ≤ c ^ (-(2 : ℝ)) := Real.rpow_nonneg hc0.le _
    linarith [he1, hgauss, htail_e, hc2_nn]
  have hK0 : 0 < c ^ (2 / 3 : ℝ) * langerKappa := mul_pos (Real.rpow_pos_of_pos hc0 _) langerKappa_pos
  have hyn : ‖y_c‖ ≤ 4.94e-4 := by
    dsimp [y_c]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK0, div_le_iff₀ hK0]
    have hdisc2 := (scale_radius_bounds hc hRJ_ub hr_lb hr_RJ hlo hhi).2.1
    exact hdisc2.trans_eq (by unfold langerRadius langerScale; ring)
  have h1w : 0.9995 ≤ ‖1 + chartYinv etaC y_c‖ := by
    have hwn := norm_chartYinv_le langerEta_etaC hyn
    have := norm_sub_norm_le (1 : ℂ) (-(chartYinv etaC y_c))
    rw [norm_neg, norm_one, sub_neg_eq_add] at this; linarith
  have hder := norm_deriv_chartYinv_le hyn
  have hpref : c ^ (1 / 3 : ℝ) / (2 * π * langerKappa) ≤ c ^ (1 / 3 : ℝ) * 0.27 :=
    langer_pref_le hc0
  have hnorm_psi : ‖hankelPsi c f u‖ = (c ^ (1 / 3 : ℝ) / (2 * π * langerKappa)) *
      ‖deriv (chartYinv etaC) y_c‖ / ‖1 + chartYinv etaC y_c‖ *
      ‖hankelLocal c f (Complex.log (1 + chartYinv etaC y_c))‖ := by
    have : hankelPsi c f u = hankelPsiY c f y_c := rfl
    rw [this]
    unfold hankelPsiY
    rw [norm_mul, norm_div, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by have := langerKappa_pos; positivity)]
  rw [hnorm_psi]
  have hpref_nn : 0 ≤ c ^ (1 / 3 : ℝ) / (2 * π * langerKappa) := by
    have := langerKappa_pos; positivity
  have hder_nn := norm_nonneg (deriv (chartYinv etaC) y_c)
  have hL_ge1 := hankelScaleL_ge_one hc3e6 hf hε hmass hT hu0 hu3 hr_lb hr_RJ hRJ_A
  have hcomb := scale_comb_algebra hc hr_lb hr_RJ hN0 huc hs2 hXpos hXN
    hB1_nn (hankelBootB2_nonneg c f r) (hankelBootB2_nonneg c f R_J) rfl hL_ge1
  have h_env_nn : 0 ≤ airyEnv u := (airyEnv_pos u).le
  have h_bracket_nn : 0 ≤ (100 / 81 : ℝ) * W * (2.5 * c ^ (-(1 / 3 : ℝ)) * X ^ (-(1 / 2 : ℝ))) +
      62 * c ^ (-(2 : ℝ)) := by positivity
  calc (c ^ (1 / 3 : ℝ) / (2 * π * langerKappa)) * ‖deriv (chartYinv etaC) y_c‖ / ‖1 + chartYinv etaC y_c‖ *
        ‖hankelLocal c f (Complex.log (1 + chartYinv etaC y_c))‖
      ≤ (c ^ (1 / 3 : ℝ) * 0.27) * (1 / 0.996) / 0.9995 *
          (airyEnv u * ((100 / 81 : ℝ) * W * (2.5 * c ^ (-(1 / 3 : ℝ)) * X ^ (-(1 / 2 : ℝ))) +
            62 * c ^ (-(2 : ℝ)))) := by gcongr
    _ = (0.27 / 0.996 / 0.9995) * airyEnv u *
          (c ^ (1 / 3 : ℝ) * ((100 / 81 : ℝ) * W * (2.5 * c ^ (-(1 / 3 : ℝ)) * X ^ (-(1 / 2 : ℝ))) +
            62 * c ^ (-(2 : ℝ)))) := by ring
    _ ≤ 0.3 * airyEnv u *
          (125 * hankelScaleBandC * hankelScaleL c R_J r u_T f * X ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ))) := by
          have h027 : (0.27 / 0.996 / 0.9995 : ℝ) ≤ 0.3 := by norm_num
          have h12 : c ^ (1 / 3 : ℝ) * ((100 / 81 : ℝ) * W * (2.5 * c ^ (-(1 / 3 : ℝ)) * X ^ (-(1 / 2 : ℝ))) +
              62 * c ^ (-(2 : ℝ))) ≤
              125 * hankelScaleBandC * hankelScaleL c R_J r u_T f * X ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ)) :=
            hcomb
          gcongr
    _ ≤ (40 * hankelScaleBandC) * hankelScaleL c R_J r u_T f *
          airyEnv u * X ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ)) := by
          have : 0 ≤ hankelScaleBandC * hankelScaleL c R_J r u_T f * airyEnv u *
              X ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ)) := by
            have hHSC : 0 ≤ hankelScaleBandC := by unfold hankelScaleBandC; norm_num
            have hX_nn : 0 ≤ X ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hXpos.le _
            have hN_nn : 0 ≤ ‖u‖ ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hN0.le _
            positivity
          nlinarith

/-- info: 'FormalResearch.SignUncertainty.hankel_scale_cov_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_scale_cov_window

end FormalResearch.SignUncertainty
