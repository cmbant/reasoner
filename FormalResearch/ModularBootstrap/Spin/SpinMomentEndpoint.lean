module

public import FormalResearch.ModularBootstrap.Spin.SpinMomentMeasure

/-!
# Endpoint limit for `SPIN-M`

Source: `CFT/modular_bootstrap/paper/spinning_airy_moment_proof.tex` (`sd:spinmoment-endpoint`).

* `spinMoment_endpoint_tendsto` (`sd:spinmoment-endpoint`): locally uniform convergence
  `ψ_{5,c'}^V(u) → (ξ_*^3 / (3π)) W(u)` on `Icc (-R) R`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.Special
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Bessel
open FormalResearch.ModularBootstrap.Upper
open FormalResearch.ModularBootstrap.Upper.Rigidity
open FormalResearch.ModularBootstrap.Upper.Assembly
open FormalResearch.ModularBootstrap.Upper.Positivity
open FormalResearch.ModularBootstrap.Upper.Window
open FormalResearch.ModularBootstrap.Upper.Window.Cardy
open FormalResearch.ModularBootstrap.Upper.Bump
open FormalResearch.ModularBootstrap.Upper.Comb

private noncomputable def volterraKernelV (N : ℕ) (η : ℝ) (σs : ℕ → ℝ) (c' u z : ℝ) : ℝ :=
  let x := bAiry c' u
  let y := x + z / c'
  ((x ^ 2 - y ^ 2 / 3) / 2) * (2 * y / 3) *
    (psiScale virasoroProblem c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) *
      jAiry c' (c' * x ^ 2 / 3) *
      bumpG spinMomentW5Prob (rpParams 4).bumpData N η σs c' (c' * y ^ 2 / 3))

private lemma tendsto_exp_neg_mul_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun z : ℝ => Real.exp (-a * z)) atTop (nhds 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr ha))

private lemma far_poly_exp_bound (y : ℝ) (hy0 : 0 ≤ y) :
    (1 + y) ^ 3 * Real.exp (-π * y) ≤ 4 * (1 + 6 / π ^ 3) := by
  have hpi := Real.pi_pos
  have hexp3 := Real.pow_div_factorial_le_exp (π * y) (by positivity) 3
  rw [show ((Nat.factorial 3 : ℕ) : ℝ) = 6 by norm_num] at hexp3
  have hy3_exp : y ^ 3 * Real.exp (-π * y) ≤ 6 / π ^ 3 := by
    have h1 : π ^ 3 * y ^ 3 ≤ 6 * Real.exp (π * y) := by
      rw [mul_pow] at hexp3; have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 6)).mp hexp3; linarith
    calc y ^ 3 * Real.exp (-π * y) = (π ^ 3 * y ^ 3 * Real.exp (-π * y)) / π ^ 3 := by field_simp
      _ ≤ (6 * Real.exp (π * y) * Real.exp (-π * y)) / π ^ 3 := by gcongr
      _ = 6 / π ^ 3 := by
          rw [mul_assoc, ← Real.exp_add, show π * y + -π * y = 0 by ring, Real.exp_zero, mul_one]
  have hexp_pi1 : Real.exp (-π * y) ≤ 1 := by
    rw [show -π * y = -(π * y) by ring, Real.exp_le_one_iff, neg_nonpos]; positivity
  have hp : (1 + y) ^ 3 ≤ 4 * (1 + y ^ 3) := by nlinarith [sq_nonneg (y - 1)]
  calc (1 + y) ^ 3 * Real.exp (-π * y) ≤ 4 * (1 + y ^ 3) * Real.exp (-π * y) := by gcongr
    _ = 4 * (Real.exp (-π * y) + y ^ 3 * Real.exp (-π * y)) := by ring
    _ ≤ 4 * (1 + 6 / π ^ 3) := by gcongr

private lemma geom_far_bound {x y xi : ℝ} (hx0 : 0 ≤ x) (hxi : x ≤ xi + 1) (hy0 : 0 ≤ y)
    (hxi0 : 0 ≤ xi) :
    |((x ^ 2 - y ^ 2 / 3) / 2) * (2 * y / 3)| ≤ (1 + (xi + 1) ^ 2) * (1 + y) ^ 3 := by
  have hx2 : x ^ 2 ≤ (xi + 1) ^ 2 := pow_le_pow_left₀ hx0 hxi 2
  have h1 : |(x ^ 2 - y ^ 2 / 3) / 2| ≤ (1 + (xi + 1) ^ 2) * (1 + y) ^ 2 := by
    have hy2_le : y ^ 2 ≤ (1 + y) ^ 2 := by nlinarith
    have hx_nn : 0 ≤ x ^ 2 := sq_nonneg x
    have hy_nn : 0 ≤ y ^ 2 := sq_nonneg y
    have h1y : 1 ≤ (1 + y) ^ 2 := by nlinarith
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have h2 : |2 * y / 3| ≤ 1 + y := by rw [abs_of_nonneg (by positivity)]; linarith
  rw [abs_mul]; exact (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)).trans_eq (by ring)

private lemma psiAiry_virasoro_eq_w5_mul {c' y : ℝ} (hc' : 0 < c') (hy : 0 < y)
    (g : ℝ → ℝ) :
    psiScale virasoroProblem c' *
        psiAiry virasoroProblem c' g (uAiry c' (c' * y ^ 2 / 3)) =
      (qProb spinMomentW5Prob * virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) /
          kernelK 5 (c' / 12) (c' * y ^ 2 / 3)) *
        (psiScale spinMomentW5Prob c' *
          psiAiry spinMomentW5Prob c' g (uAiry c' (c' * y ^ 2 / 3))) := by
  have ht : tAiry c' (uAiry c' (c' * y ^ 2 / 3)) = c' * y ^ 2 / 3 :=
    tAiry_uAiry hc' (by positivity)
  unfold psiAiry psiScale
  rw [ht, qProb_virasoro, spinMomentW5Prob_cardyV, FKc_q_eq (qProb spinMomentW5Prob) 1 c']
  have hCS : CStar ≠ 0 := CStar_pos.ne'
  have hFK : FKc 1 1 c' ≠ 0 := (FKc_pos zero_lt_one 1 hc').ne'
  have hq5 : qProb spinMomentW5Prob ≠ 0 := (qProb_pos spinMomentW5Prob).ne'
  have hK5 : kernelK 5 (c' / 12) (c' * y ^ 2 / 3) ≠ 0 := by
    have h5 := spinMomentW5Prob.cardyV_pos (a := c' / 12) (t := c' * y ^ 2 / 3)
      (by rw [spinMomentW5Prob_totalShift]; positivity) (by positivity)
    rw [spinMomentW5Prob_cardyV] at h5
    exact h5.ne'
  field_simp

private lemma endpoint_integrand_dom (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C_dom : ℝ, 0 < C_dom ∧ ∀ᶠ c' in atTop, ∀ u ∈ Icc (-R) R, ∀ z : ℝ, 0 ≤ z →
      |volterraKernelV N η σs c' u z| ≤ C_dom * Real.exp (-2 * π * z / 3) := by
  set d5 := (rpParams 4).bumpData
  obtain ⟨c_lo, C_hi, hc_lo, hC_hi, hcj⟩ :=
    virasoro_cardy_jAiry_bounds (half_pos xiStar_pos) (by linarith [xiStar_pos] : xiStar / 2 ≤ xiStar + 1)
  obtain ⟨Sg0, C_g, hSg0, hCg, hmid⟩ := bumpG_mid_exp_le N hN hη0.le hη1 σs
  obtain ⟨C₀, hC₀, hfar⟩ := bumpG_far_exp_le N hN hη0.le hη1 σs zero_lt_one
  set R₁ := max R (kappaAiry * Sg0) + 1
  have hR₁ : 0 ≤ R₁ := by have := kappaAiry_pos; positivity
  obtain ⟨M_W, hMW⟩ := (isCompact_Icc (a := -R₁) (b := R₁)).exists_bound_of_continuousOn
    (continuousOn_sigWinW N hN hη0 hη1 σs hR₁)
  have hpi := Real.pi_pos
  have hξ := xiStar_pos
  have hk_pos := kTip_pos
  set M_W' := max M_W 0 + 1
  set C_1 := (2 * M_W') * (C_hi / c_lo) * (xiStar + 1) ^ 3
  set C_S := kTip * Sg0 ^ (-(3 / 2 : ℝ))
  set C_2 := C_hi * C_g * C_S * (xiStar + 1) ^ 3
  set C_far_fac := (1 + (xiStar + 1) ^ 2) * (4 * (1 + 6 / π ^ 3))
  set C_3 := C_hi * C₀ * C_far_fac
  set C_dom := max C_1 (max C_2 C_3) + 1
  refine ⟨C_dom, by positivity, ?_⟩
  have hlam0 : Tendsto (fun c' => lambdaComb c' * Sg0) atTop (nhds 0) := by
    have heq : (fun c' => lambdaComb c' * Sg0) =ᶠ[atTop]
        fun c' => (kTip ^ (-(2 / 3 : ℝ)) * Sg0) * c' ^ (-(2 / 3 : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with c' hc'
      unfold lambdaComb; rw [Real.mul_rpow hk_pos.le hc'.le]; ring
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3) |>.const_mul
      (kTip ^ (-(2 / 3 : ℝ)) * Sg0)).congr' heq.symm
  obtain ⟨ρw, hρw, hw5rat⟩ := virasoro_w5_cardy_ratio_tendsto (half_pos xiStar_pos)
    (by linarith [xiStar_pos] : xiStar / 2 ≤ xiStar + 1) (1 / 2 : ℝ) (by norm_num)
  have hslope_rw : Tendsto slopeAiry atTop (nhds 0) := by
    have heq : slopeAiry = fun c => c ^ (-(2 / 3 : ℝ)) / betaTip := by
      ext c; unfold slopeAiry epsAiry; rfl
    rw [heq]; simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).div_const betaTip
  have hlam_rw : ∀ᶠ c' in atTop, R * slopeAiry c' ≤ ρw / 2 ∧ lambdaComb c' * Sg0 ≤ min (1 / 2) (ρw / 2) := by
    have h1 : ∀ᶠ c' in atTop, R * slopeAiry c' ≤ ρw / 2 := by
      have ht : Tendsto (fun c' => R * slopeAiry c') atTop (nhds 0) := by
        simpa only [mul_zero] using hslope_rw.const_mul R
      exact ht.eventually_le_const (by positivity : 0 < ρw / 2)
    have h2 : ∀ᶠ c' in atTop, lambdaComb c' * Sg0 ≤ min (1 / 2) (ρw / 2) :=
      hlam0.eventually_le_const (lt_min (by norm_num) (half_pos hρw))
    exact h1.and h2
  filter_upwards [bAiry_eq_of_Icc hR, hcj, hmid, hfar,
    bump_psi_uniform spinMomentW5Prob d5 N hN hη0 hη1 σs hR₁ zero_lt_one,
    hw5rat, hlam_rw, eventually_ge_atTop (1 : ℝ)]
    with c' hbx hcj' hmid' hfar' hpsi' hw5' ⟨_, hlam1⟩ hc1 u hu z hz
  have hc0 : 0 < c' := by linarith
  obtain ⟨hbx_eq, hx_lo, hx_hi'⟩ := hbx u hu
  set x := bAiry c' u
  set y := x + z / c'
  have hy_x : x ≤ y := by dsimp [y]; exact le_add_of_nonneg_right (div_nonneg hz hc0.le)
  have hy_lo : xiStar / 2 ≤ y := hx_lo.trans hy_x
  have hx_hi1 : x ≤ xiStar + 1 := by linarith
  have hcb_x := hcj' x ⟨hx_lo, hx_hi1⟩
  have hfront_nn : 0 ≤ psiScale virasoroProblem c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) *
      jAiry c' (c' * x ^ 2 / 3) :=
    le_trans (by positivity) hcb_x.1
  have hcL_diff : c' * besselL x - c' * besselL y = -2 * π * z / 3 := by
    unfold besselL; dsimp [y]; field_simp; ring
  have hlam_Sg : -kappaAiry * Sg0 = uAiry c' (c' * (xiStar + lambdaComb c' * Sg0) ^ 2 / 3) := by
    have hpos : 0 ≤ xiStar + lambdaComb c' * Sg0 := by unfold lambdaComb; positivity
    unfold uAiry
    rw [show 3 * (c' * (xiStar + lambdaComb c' * Sg0) ^ 2 / 3) / c' =
      (xiStar + lambdaComb c' * Sg0) ^ 2 by field_simp, Real.sqrt_sq hpos,
      show xiStar + lambdaComb c' * Sg0 - xiStar = lambdaComb c' * Sg0 by ring]
    have hbk : betaTip * kTip ^ (-(2 / 3 : ℝ)) = kappaAiry := by
      unfold betaTip KTip kappaAiry
      rw [show 3 * (2 * π * kTip) / 4 = (3 * π / 2) * kTip by ring,
        Real.mul_rpow (by positivity) hk_pos.le, mul_assoc, ← Real.rpow_add hk_pos]
      norm_num
    unfold lambdaComb
    rw [Real.mul_rpow hk_pos.le hc0.le]
    have hc_mul : c' ^ (-(2 / 3 : ℝ)) * c' ^ ((2 : ℝ) / 3) = 1 := by
      rw [← Real.rpow_add hc0]; norm_num
    calc -kappaAiry * Sg0 = -(betaTip * kTip ^ (-(2 / 3 : ℝ))) * Sg0 * (c' ^ (-(2 / 3 : ℝ)) * c' ^ ((2 : ℝ) / 3)) := by
          rw [hbk, hc_mul, mul_one]
      _ = -betaTip * (kTip ^ (-(2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) * Sg0) * c' ^ ((2 : ℝ) / 3) := by ring
  by_cases hy_reg1 : y ≤ xiStar + lambdaComb c' * Sg0
  · have hy_hi1 : y ≤ xiStar + 1 := by linarith [hlam1, min_le_left (1 / 2) (ρw / 2)]
    have hy0 : 0 < y := (half_pos xiStar_pos).trans_le hy_lo
    have hcb_y := hcj' y ⟨hy_lo, hy_hi1⟩
    set u' := uAiry c' (c' * y ^ 2 / 3)
    have hu'_le : u' ≤ R := by
      have hu_eq : u = uAiry c' (c' * x ^ 2 / 3) := (uAiry_bAiry_eq hc0 (by linarith) hbx_eq).symm
      have hty_le : c' * x ^ 2 / 3 ≤ c' * y ^ 2 / 3 := by gcongr; linarith
      exact (hu_eq ▸ uAiry_antitone hc0 hty_le).trans hu.2
    have hu'_ge : -R₁ ≤ u' := by
      have hty_ge : c' * y ^ 2 / 3 ≤ c' * (xiStar + lambdaComb c' * Sg0) ^ 2 / 3 := by
        gcongr
      have h1 : -kappaAiry * Sg0 ≤ u' := hlam_Sg ▸ uAiry_antitone hc0 hty_ge
      have : -R₁ ≤ -kappaAiry * Sg0 := by dsimp [R₁]; linarith [le_max_right R (kappaAiry * Sg0)]
      exact this.trans h1
    have hu'_mem : u' ∈ Icc (-R₁) R₁ := ⟨hu'_ge, hu'_le.trans (by dsimp [R₁]; linarith [le_max_left R (kappaAiry * Sg0)])⟩
    have hcb_y_pos : 0 < psiScale virasoroProblem c' * virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) *
        jAiry c' (c' * y ^ 2 / 3) := lt_of_lt_of_le (by positivity) hcb_y.1
    have hy_rho : |y - xiStar| ≤ ρw := by
      have hsub1 : xiStar / 2 ≤ y := hy_lo
      have hsub2 : y - xiStar ≤ ρw / 2 := by linarith [hlam1, min_le_right (1 / 2) (ρw / 2)]
      have hlow_x : xiStar - ρw / 2 ≤ y := by
        have hx_rw : x = xiStar - u * slopeAiry c' := hbx_eq
        have h_sl : u * slopeAiry c' ≤ R * slopeAiry c' :=
          mul_le_mul_of_nonneg_right hu.2 (slopeAiry_pos hc0).le
        linarith [‹R * slopeAiry c' ≤ ρw / 2›]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hw5_rat_bd : |qProb spinMomentW5Prob * virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) /
        kernelK 5 (c' / 12) (c' * y ^ 2 / 3)| ≤ 2 := by
      have h1 := hw5' y hy_rho
      have h2 := abs_sub_abs_le_abs_sub
        (qProb spinMomentW5Prob * virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) /
          kernelK 5 (c' / 12) (c' * y ^ 2 / 3)) (1 : ℝ)
      rw [abs_one] at h2
      linarith
    have hg_psi : |bumpG spinMomentW5Prob d5 N η σs c' (c' * y ^ 2 / 3)| *
        (psiScale virasoroProblem c' * virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) *
          jAiry c' (c' * y ^ 2 / 3)) ≤ 2 * M_W' := by
      have hpsi_bd : |psiScale spinMomentW5Prob c' *
          psiAiry spinMomentW5Prob c' (bumpG spinMomentW5Prob d5 N η σs c') u'| ≤ M_W' := by
        have h1 := hpsi' u' hu'_mem
        have h2 := hMW u' hu'_mem
        rw [Real.norm_eq_abs] at h2
        have h3 : |psiScale spinMomentW5Prob c' *
            psiAiry spinMomentW5Prob c' (bumpG spinMomentW5Prob d5 N η σs c') u'| ≤
            |sigWinW N η σs u'| + 1 := by
          have := abs_sub_abs_le_abs_sub
            (psiScale spinMomentW5Prob c' *
              psiAiry spinMomentW5Prob c' (bumpG spinMomentW5Prob d5 N η σs c') u')
            (sigWinW N η σs u')
          linarith
        dsimp [M_W']; linarith [le_max_left M_W 0]
      have hvir : |psiScale virasoroProblem c' *
          psiAiry virasoroProblem c' (bumpG spinMomentW5Prob d5 N η σs c') u'| ≤ 2 * M_W' := by
        rw [psiAiry_virasoro_eq_w5_mul hc0 hy0, abs_mul]
        exact mul_le_mul hw5_rat_bd hpsi_bd (abs_nonneg _) zero_le_two
      unfold psiAiry at hvir
      rw [tAiry_uAiry hc0 (by positivity)] at hvir
      rwa [show psiScale virasoroProblem c' * (bumpG spinMomentW5Prob d5 N η σs c' (c' * y ^ 2 / 3) *
          virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) * jAiry c' (c' * y ^ 2 / 3)) =
          bumpG spinMomentW5Prob d5 N η σs c' (c' * y ^ 2 / 3) *
            (psiScale virasoroProblem c' * virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) *
              jAiry c' (c' * y ^ 2 / 3)) by ring, abs_mul, abs_of_pos hcb_y_pos] at hvir
    have hrat : (psiScale virasoroProblem c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) *
          jAiry c' (c' * x ^ 2 / 3)) /
        (psiScale virasoroProblem c' * virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) *
          jAiry c' (c' * y ^ 2 / 3)) ≤ (C_hi / c_lo) * Real.exp (-2 * π * z / 3) := by
      have hden_pos : 0 < c_lo / c' * Real.exp (c' * besselL y) := by positivity
      calc _ ≤ (C_hi / c' * Real.exp (c' * besselL x)) / (c_lo / c' * Real.exp (c' * besselL y)) :=
            div_le_div₀ (by positivity) hcb_x.2 hden_pos hcb_y.1
        _ = (C_hi / c_lo) * (Real.exp (c' * besselL x) / Real.exp (c' * besselL y)) := by field_simp
        _ = (C_hi / c_lo) * Real.exp (-2 * π * z / 3) := by rw [← Real.exp_sub, hcL_diff]
    have hgeom : |((x ^ 2 - y ^ 2 / 3) / 2) * (2 * y / 3)| ≤ (xiStar + 1) ^ 3 := by
      have h1 : |(x ^ 2 - y ^ 2 / 3) / 2| ≤ (xiStar + 1) ^ 2 := by
        have hx2 : 0 ≤ x ^ 2 := sq_nonneg x; have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
        have hx2b : x ^ 2 ≤ (xiStar + 1) ^ 2 := pow_le_pow_left₀ (by linarith) hx_hi1 2
        have hy2b : y ^ 2 ≤ (xiStar + 1) ^ 2 := pow_le_pow_left₀ (by linarith) hy_hi1 2
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      have h2 : |2 * y / 3| ≤ xiStar + 1 := by rw [abs_of_nonneg (by linarith)]; linarith
      rw [abs_mul]; exact (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)).trans_eq (by ring)
    have hKV_abs : |volterraKernelV N η σs c' u z| = |((x ^ 2 - y ^ 2 / 3) / 2) * (2 * y / 3)| *
        ((psiScale virasoroProblem c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) *
            jAiry c' (c' * x ^ 2 / 3)) *
          |bumpG spinMomentW5Prob d5 N η σs c' (c' * y ^ 2 / 3)|) := by
      unfold volterraKernelV
      rw [abs_mul, abs_mul _ (bumpG _ _ _ _ _ _ _), abs_of_nonneg hfront_nn]
    rw [hKV_abs]
    calc |((x ^ 2 - y ^ 2 / 3) / 2) * (2 * y / 3)| *
          ((psiScale virasoroProblem c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) *
              jAiry c' (c' * x ^ 2 / 3)) *
            |bumpG spinMomentW5Prob d5 N η σs c' (c' * y ^ 2 / 3)|)
      _ = |((x ^ 2 - y ^ 2 / 3) / 2) * (2 * y / 3)| *
            ((psiScale virasoroProblem c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) *
                jAiry c' (c' * x ^ 2 / 3)) /
              (psiScale virasoroProblem c' * virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) *
                jAiry c' (c' * y ^ 2 / 3))) *
            (|bumpG spinMomentW5Prob d5 N η σs c' (c' * y ^ 2 / 3)| *
              (psiScale virasoroProblem c' * virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) *
                jAiry c' (c' * y ^ 2 / 3))) := by
          rw [mul_assoc (|((x ^ 2 - y ^ 2 / 3) / 2) * (2 * y / 3)|)]
          have hswap : ∀ b g cy : ℝ, cy ≠ 0 → b * g = (b / cy) * (g * cy) := fun b g cy h => by
            field_simp [h]
          exact congrArg (|((x ^ 2 - y ^ 2 / 3) / 2) * (2 * y / 3)| * ·)
            (hswap _ _ _ hcb_y_pos.ne')
      _ ≤ (xiStar + 1) ^ 3 * ((C_hi / c_lo) * Real.exp (-2 * π * z / 3)) * (2 * M_W') := by gcongr
      _ = C_1 * Real.exp (-2 * π * z / 3) := by dsimp [C_1]; ring
      _ ≤ C_dom * Real.exp (-2 * π * z / 3) := by
          gcongr; dsimp [C_dom]; linarith [le_max_left C_1 (max C_2 C_3)]
  · by_cases hy_hi1 : y ≤ xiStar + 1
    · have hy_mid := hmid' y (by linarith) hy_hi1
      have hlam_pos : 0 < lambdaComb c' := by unfold lambdaComb; positivity
      have hrpow_le : (y - xiStar) ^ (-(3 / 2 : ℝ)) ≤ C_S * c' := by
        have hyx_sub : lambdaComb c' * Sg0 ≤ y - xiStar := by linarith
        calc (y - xiStar) ^ (-(3 / 2 : ℝ))
            ≤ (lambdaComb c' * Sg0) ^ (-(3 / 2 : ℝ)) :=
              Real.rpow_le_rpow_of_nonpos (mul_pos hlam_pos hSg0) hyx_sub (by norm_num)
          _ = (lambdaComb c') ^ (-(3 / 2 : ℝ)) * Sg0 ^ (-(3 / 2 : ℝ)) := Real.mul_rpow hlam_pos.le hSg0.le
          _ = C_S * c' := by
              unfold lambdaComb
              rw [← Real.rpow_mul (by positivity), show -(2 / 3 : ℝ) * -(3 / 2 : ℝ) = 1 by norm_num, Real.rpow_one]
              dsimp [C_S]; ring
      have hgeom : |((x ^ 2 - y ^ 2 / 3) / 2) * (2 * y / 3)| ≤ (xiStar + 1) ^ 3 := by
        have h1 : |(x ^ 2 - y ^ 2 / 3) / 2| ≤ (xiStar + 1) ^ 2 := by
          have hx2 : 0 ≤ x ^ 2 := sq_nonneg x; have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
          have hx2b : x ^ 2 ≤ (xiStar + 1) ^ 2 := pow_le_pow_left₀ (by linarith) hx_hi1 2
          have hy2b : y ^ 2 ≤ (xiStar + 1) ^ 2 := pow_le_pow_left₀ (by linarith) hy_hi1 2
          exact abs_le.mpr ⟨by linarith, by linarith⟩
        have h2 : |2 * y / 3| ≤ xiStar + 1 := by rw [abs_of_nonneg (by linarith)]; linarith
        rw [abs_mul]; exact (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)).trans_eq (by ring)
      have hKV_abs : |volterraKernelV N η σs c' u z| = |((x ^ 2 - y ^ 2 / 3) / 2) * (2 * y / 3)| *
          ((psiScale virasoroProblem c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) *
              jAiry c' (c' * x ^ 2 / 3)) *
            |bumpG spinMomentW5Prob d5 N η σs c' (c' * y ^ 2 / 3)|) := by
        unfold volterraKernelV
        rw [abs_mul, abs_mul _ (bumpG _ _ _ _ _ _ _), abs_of_nonneg hfront_nn]
      rw [hKV_abs]
      calc |((x ^ 2 - y ^ 2 / 3) / 2) * (2 * y / 3)| *
            ((psiScale virasoroProblem c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) *
                jAiry c' (c' * x ^ 2 / 3)) *
              |bumpG spinMomentW5Prob d5 N η σs c' (c' * y ^ 2 / 3)|)
          ≤ (xiStar + 1) ^ 3 *
              ((C_hi / c' * Real.exp (c' * besselL x)) *
                (C_g * (C_S * c') * Real.exp (-c' * besselL y))) := by
            refine mul_le_mul hgeom (mul_le_mul hcb_x.2 ?_ (abs_nonneg _) (by positivity))
              (by positivity) (by positivity)
            exact hy_mid.trans (by gcongr)
        _ = C_2 * (Real.exp (c' * besselL x) * Real.exp (-c' * besselL y)) := by
            dsimp [C_2]; field_simp
        _ = C_2 * Real.exp (-2 * π * z / 3) := by
            rw [← Real.exp_add, show c' * besselL x + -c' * besselL y = c' * besselL x - c' * besselL y by ring,
              hcL_diff]
        _ ≤ C_dom * Real.exp (-2 * π * z / 3) := by
            gcongr; dsimp [C_dom]; linarith [le_max_left C_2 C_3, le_max_right C_1 (max C_2 C_3)]
    · have hy_far := hfar' y (by linarith)
      have hy0 : 0 ≤ y := by linarith
      have h1y3 : (1 + y) ^ 3 * Real.exp (-π * y) ≤ 4 * (1 + 6 / π ^ 3) :=
        far_poly_exp_bound y hy0
      have hgeom : |((x ^ 2 - y ^ 2 / 3) / 2) * (2 * y / 3)| ≤ (1 + (xiStar + 1) ^ 2) * (1 + y) ^ 3 :=
        geom_far_bound (by linarith) hx_hi1 hy0 xiStar_pos.le
      have hC_hi_div : C_hi / c' ≤ C_hi := div_le_self hC_hi.le hc1
      have hKV_abs : |volterraKernelV N η σs c' u z| = |((x ^ 2 - y ^ 2 / 3) / 2) * (2 * y / 3)| *
          ((psiScale virasoroProblem c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) *
              jAiry c' (c' * x ^ 2 / 3)) *
            |bumpG spinMomentW5Prob d5 N η σs c' (c' * y ^ 2 / 3)|) := by
        unfold volterraKernelV
        rw [abs_mul, abs_mul _ (bumpG _ _ _ _ _ _ _), abs_of_nonneg hfront_nn]
      rw [hKV_abs]
      calc |((x ^ 2 - y ^ 2 / 3) / 2) * (2 * y / 3)| *
            ((psiScale virasoroProblem c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) *
                jAiry c' (c' * x ^ 2 / 3)) *
              |bumpG spinMomentW5Prob d5 N η σs c' (c' * y ^ 2 / 3)|)
          ≤ ((1 + (xiStar + 1) ^ 2) * (1 + y) ^ 3) *
              ((C_hi * Real.exp (c' * besselL x)) * (C₀ * Real.exp (-c' * besselL y - π * y))) := by
            refine mul_le_mul hgeom (mul_le_mul ?_ hy_far (abs_nonneg _) (by positivity))
              (by positivity) (by positivity)
            exact hcb_x.2.trans (mul_le_mul_of_nonneg_right hC_hi_div (Real.exp_pos _).le)
        _ = C_hi * C₀ * ((1 + (xiStar + 1) ^ 2) * ((1 + y) ^ 3 * Real.exp (-π * y))) *
              (Real.exp (c' * besselL x) * Real.exp (-c' * besselL y)) := by
            rw [sub_eq_add_neg, Real.exp_add]; ring
        _ ≤ C_3 * Real.exp (-2 * π * z / 3) := by
            dsimp [C_3, C_far_fac]
            rw [← Real.exp_add, show c' * besselL x + -c' * besselL y = c' * besselL x - c' * besselL y by ring,
              hcL_diff]
            gcongr
        _ ≤ C_dom * Real.exp (-2 * π * z / 3) := by
            gcongr; dsimp [C_dom]; linarith [le_max_right C_2 C_3, le_max_right C_1 (max C_2 C_3)]

private lemma endpoint_Ici_comp_sq {c' x : ℝ} (hc' : 0 < c') (hx : 0 < x) (f : ℝ → ℝ) :
    ∫ t in Ici (c' * x ^ 2 / 3), f t = ∫ y in Ici x, (2 * c' * y / 3) * f (c' * y ^ 2 / 3) := by
  have him : (fun y => c' * y ^ 2 / 3) '' Ioi x = Ioi (c' * x ^ 2 / 3) := by
    ext t; simp only [mem_image, mem_Ioi]; constructor
    · rintro ⟨y, hy, rfl⟩
      nlinarith [sq_nonneg (y - x), mul_pos hc' (sub_pos.mpr hy)]
    · intro ht
      refine ⟨√(3 * t / c'), ?_, ?_⟩
      · have hsq : x ^ 2 < 3 * t / c' := (lt_div_iff₀ hc').2 (by linarith)
        calc x = √(x ^ 2) := (Real.sqrt_sq hx.le).symm
          _ < √(3 * t / c') := Real.sqrt_lt_sqrt (sq_nonneg x) hsq
      · have ht0 : 0 ≤ 3 * t / c' := by
          have : 0 < c' * x ^ 2 / 3 := by positivity
          have : 0 < t := this.trans ht
          positivity
        rw [Real.sq_sqrt ht0]; field_simp
  have hderiv : ∀ y ∈ Ioi x, HasDerivWithinAt (fun z => c' * z ^ 2 / 3) (2 * c' * y / 3) (Ioi x) y := by
    intro y _
    exact (((hasDerivAt_pow 2 y).const_mul c').div_const 3).hasDerivWithinAt.congr_deriv (by ring)
  have hinj : InjOn (fun y => c' * y ^ 2 / 3) (Ioi x) := fun y₁ hy₁ y₂ hy₂ heq => by
    have h1 : 0 ≤ y₁ := hx.le.trans (le_of_lt hy₁)
    have h2 : 0 ≤ y₂ := hx.le.trans (le_of_lt hy₂)
    have hsq : y₁ ^ 2 = y₂ ^ 2 := by nlinarith
    rw [← Real.sqrt_sq h1, hsq, Real.sqrt_sq h2]
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi, MeasureTheory.integral_Ici_eq_integral_Ioi,
    ← him, MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj f]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : 0 < y := hx.trans hy
  rw [smul_eq_mul, abs_of_nonneg (by positivity)]

private lemma cancel_mid_factor (a b c g cy : ℝ) (hcy : cy ≠ 0) :
    a * b * c * g = (b * c / cy) * (a * (g * cy)) := by
  field_simp [hcy]

private lemma endpoint_poly_bound {x y xi C_A ε₁ : ℝ} (hξ : 0 < xi)
    (hx_lo : 0 ≤ x) (hx_hi : x ≤ xi + 1) (hy_lo : 0 ≤ y) (hy_hi : y ≤ xi + 1)
    (hC_A : C_A = 2 * (xi + 1) ^ 2 + 1)
    (hxz : |x - xi| ≤ ε₁ / (3 * C_A)) (hyz : |y - xi| ≤ 2 * (ε₁ / (3 * C_A))) :
    |((x ^ 2 - y ^ 2 / 3) / 2) * (2 * y / 3) - 2 * xi ^ 3 / 9| ≤ ε₁ := by
  have h_sq1 : |x ^ 2 - xi ^ 2| ≤ 2 * (xi + 1) * |x - xi| := by
    rw [show x ^ 2 - xi ^ 2 = (x + xi) * (x - xi) by ring, abs_mul]
    have : |x + xi| ≤ 2 * (xi + 1) := by rw [abs_of_nonneg (by positivity)]; linarith
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have h_sq2 : |y ^ 2 - xi ^ 2| ≤ 2 * (xi + 1) * |y - xi| := by
    rw [show y ^ 2 - xi ^ 2 = (y + xi) * (y - xi) by ring, abs_mul]
    have : |y + xi| ≤ 2 * (xi + 1) := by rw [abs_of_nonneg (by positivity)]; linarith
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have h_part1 : |(x ^ 2 - y ^ 2 / 3) / 2 - xi ^ 2 / 3| ≤
      (xi + 1) * (|x - xi| + |y - xi|) := by
    rw [show (x ^ 2 - y ^ 2 / 3) / 2 - xi ^ 2 / 3 =
        (x ^ 2 - xi ^ 2) / 2 - (y ^ 2 - xi ^ 2) / 6 by ring]
    calc |(x ^ 2 - xi ^ 2) / 2 - (y ^ 2 - xi ^ 2) / 6|
        ≤ |(x ^ 2 - xi ^ 2) / 2| + |(y ^ 2 - xi ^ 2) / 6| := abs_sub _ _
      _ = |x ^ 2 - xi ^ 2| / 2 + |y ^ 2 - xi ^ 2| / 6 := by
          rw [abs_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
            abs_of_pos (by norm_num : (0 : ℝ) < 6)]
      _ ≤ (2 * (xi + 1) * |x - xi|) / 2 + (2 * (xi + 1) * |y - xi|) / 6 := by gcongr
      _ ≤ (xi + 1) * (|x - xi| + |y - xi|) := by nlinarith [abs_nonneg (y - xi)]
  have h_part2 : |2 * y / 3 - 2 * xi / 3| ≤ |y - xi| := by
    rw [show 2 * y / 3 - 2 * xi / 3 = (2 / 3) * (y - xi) by ring, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
    linarith [abs_nonneg (y - xi)]
  have hb1 : |2 * y / 3| ≤ xi + 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  have hb2 : |xi ^ 2 / 3| ≤ (xi + 1) ^ 2 := by rw [abs_of_nonneg (by positivity)]; nlinarith
  have hid_A : ((x ^ 2 - y ^ 2 / 3) / 2) * (2 * y / 3) - 2 * xi ^ 3 / 9 =
      ((x ^ 2 - y ^ 2 / 3) / 2 - xi ^ 2 / 3) * (2 * y / 3) +
        (xi ^ 2 / 3) * (2 * y / 3 - 2 * xi / 3) := by ring
  rw [hid_A]
  have hCA0 : 0 < C_A := by rw [hC_A]; positivity
  calc |((x ^ 2 - y ^ 2 / 3) / 2 - xi ^ 2 / 3) * (2 * y / 3) +
        (xi ^ 2 / 3) * (2 * y / 3 - 2 * xi / 3)|
      ≤ |(x ^ 2 - y ^ 2 / 3) / 2 - xi ^ 2 / 3| * |2 * y / 3| +
          |xi ^ 2 / 3| * |2 * y / 3 - 2 * xi / 3| :=
        (abs_add_le (((x ^ 2 - y ^ 2 / 3) / 2 - xi ^ 2 / 3) * (2 * y / 3))
          ((xi ^ 2 / 3) * (2 * y / 3 - 2 * xi / 3))).trans_eq
          (by rw [abs_mul, abs_mul])
    _ ≤ ((xi + 1) * (|x - xi| + |y - xi|)) * (xi + 1) + (xi + 1) ^ 2 * |y - xi| := by gcongr
    _ ≤ (xi + 1) ^ 2 * (2 * (|x - xi| + |y - xi|)) := by
        nlinarith [abs_nonneg (x - xi), abs_nonneg (y - xi)]
    _ = (2 * (xi + 1) ^ 2) * (|x - xi| + |y - xi|) := by ring
    _ ≤ C_A * (|x - xi| + |y - xi|) := by
        gcongr; rw [hC_A]; linarith
    _ ≤ C_A * (ε₁ / (3 * C_A) + 2 * (ε₁ / (3 * C_A))) := by gcongr
    _ = ε₁ := by field_simp [hCA0.ne']; ring

private lemma endpoint_w_diff_bound {W_v q_rat W5 W_u W_u' M_W' ε₁ : ℝ}
    (hWv : W_v = q_rat * W5) (hq : |q_rat - 1| ≤ ε₁) (h1 : |W5 - W_u'| ≤ ε₁)
    (h2 : |W_u' - W_u| ≤ ε₁) (hW0 : |W_u| ≤ M_W') (hMW1 : 1 ≤ M_W') (hε₁ : ε₁ ≤ 1) :
    |W_v - W_u| ≤ 5 * M_W' * ε₁ := by
  have hε₁0 : 0 ≤ ε₁ := le_trans (abs_nonneg (q_rat - 1)) hq
  have hW5_u : |W5 - W_u| ≤ 2 * ε₁ := by
    calc |W5 - W_u| ≤ |W5 - W_u'| + |W_u' - W_u| := abs_sub_le _ _ _
      _ ≤ ε₁ + ε₁ := by gcongr
      _ = 2 * ε₁ := by ring
  have hW5_bd : |W5| ≤ 3 * M_W' := by
    have hsub := abs_sub_abs_le_abs_sub W5 W_u
    linarith
  rw [hWv, show q_rat * W5 - W_u = (q_rat - 1) * W5 + (W5 - W_u) by ring]
  calc |(q_rat - 1) * W5 + (W5 - W_u)|
      ≤ |(q_rat - 1) * W5| + |W5 - W_u| := abs_add_le _ _
    _ = |q_rat - 1| * |W5| + |W5 - W_u| := by rw [abs_mul]
    _ ≤ ε₁ * (3 * M_W') + 2 * ε₁ := by gcongr
    _ ≤ 5 * M_W' * ε₁ := by nlinarith

private lemma endpoint_three_way_bound {A_v A₀ R_v R₀ W_v W₀ M_W' ε₁ ε₀ : ℝ}
    (hε₁0 : 0 ≤ ε₁) (hε₁1 : ε₁ ≤ 1) (hA₀ : 0 ≤ A₀) (hMW1 : 1 ≤ M_W')
    (hA : |A_v - A₀| ≤ ε₁) (hR : |R_v - R₀| ≤ ε₁) (hW : |W_v - W₀| ≤ 5 * M_W' * ε₁)
    (hR₀ : |R₀| ≤ 1) (hW₀ : |W₀| ≤ M_W') (hbd : ε₁ * (14 * (A₀ + 1) * M_W') ≤ ε₀) :
    |A_v * R_v * W_v - A₀ * R₀ * W₀| ≤ ε₀ := by
  have hRv_bd : |R_v| ≤ 2 := by
    have := abs_sub_abs_le_abs_sub R_v R₀; linarith
  have hWv_bd : |W_v| ≤ 6 * M_W' := by
    have := abs_sub_abs_le_abs_sub W_v W₀
    have : 5 * M_W' * ε₁ ≤ 5 * M_W' := by nlinarith
    linarith
  rw [show A_v * R_v * W_v - A₀ * R₀ * W₀ =
      (A_v - A₀) * (R_v * W_v) + A₀ * ((R_v - R₀) * W_v) + A₀ * R₀ * (W_v - W₀) by ring]
  calc |(A_v - A₀) * (R_v * W_v) + A₀ * ((R_v - R₀) * W_v) + A₀ * R₀ * (W_v - W₀)|
      ≤ |(A_v - A₀) * (R_v * W_v) + A₀ * ((R_v - R₀) * W_v)| +
          |A₀ * R₀ * (W_v - W₀)| := abs_add_le _ _
    _ ≤ |(A_v - A₀) * (R_v * W_v)| + |A₀ * ((R_v - R₀) * W_v)| +
          |A₀ * R₀ * (W_v - W₀)| := by gcongr; exact abs_add_le _ _
    _ = |A_v - A₀| * (|R_v| * |W_v|) + A₀ * (|R_v - R₀| * |W_v|) +
          A₀ * |R₀| * |W_v - W₀| := by
        simp only [abs_mul, abs_of_nonneg hA₀]
    _ ≤ ε₁ * (2 * (6 * M_W')) + A₀ * (ε₁ * (6 * M_W')) + A₀ * 1 * (5 * M_W' * ε₁) := by
        gcongr
    _ = ε₁ * (12 * M_W' + 11 * A₀ * M_W') := by ring
    _ ≤ ε₁ * (14 * (A₀ + 1) * M_W') := by gcongr; nlinarith
    _ ≤ ε₀ := hbd

/-- **`sd:spinmoment-endpoint`**: locally uniform convergence of `ψ_{5,c'}^V(u)` to
`(ξ_*^3 / (3π)) W(u)` on `Icc (-R) R`. -/
theorem spinMoment_endpoint_tendsto (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) {R : ℝ} (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c' in atTop, ∀ u ∈ Icc (-R) R,
      |psiScale virasoroProblem c' *
          psiAiry virasoroProblem c' (spinMomentVolterraScaled (rpParams 4).bumpData N η σs c') u -
        (xiStar ^ 3 / (3 * π)) * sigWinW N η σs u| ≤ ε := by
  set d5 := (rpParams 4).bumpData
  obtain ⟨C_dom, hCdom, hdom⟩ := endpoint_integrand_dom N hN hη0 hη1 σs hR
  obtain ⟨M_W, hMW⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    (continuousOn_sigWinW N hN hη0 hη1 σs hR)
  have hpi := Real.pi_pos
  have hξ := xiStar_pos
  have hbt := betaTip_pos
  set M_W' := max M_W 0 + 1
  set A_tail := C_dom * (3 / (2 * π)) + (xiStar ^ 3 / (3 * π)) * M_W' + 1
  have hAtail : 0 < A_tail := by positivity
  have ht_tail : Tendsto (fun z => A_tail * Real.exp (-(2 * π / 3) * z)) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_exp_neg_mul_atTop (by positivity : 0 < 2 * π / 3)).const_mul A_tail
  obtain ⟨Z, hZ_ge1, hZ_lt⟩ := ((eventually_ge_atTop (1 : ℝ)).and
    (ht_tail.eventually_le_const (by linarith : (0 : ℝ) < ε / 4))).exists
  have hZ_lt : A_tail * Real.exp (-2 * π * Z / 3) ≤ ε / 4 := by
    convert hZ_lt using 3; ring
  have hZ0 : 0 ≤ Z := by linarith
  have hR1 : 0 ≤ R + 1 := by linarith
  have hucW : UniformContinuousOn (sigWinW N η σs) (Icc (-(R + 1)) (R + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (continuousOn_sigWinW N hN hη0 hη1 σs hR1)
  set A₀ := 2 * xiStar ^ 3 / 9
  set ε₀ := ε / (4 * (Z + 1))
  set ε₁ := min 1 (ε₀ / (14 * (A₀ + 1) * M_W' + 1))
  have hε₁_pos : 0 < ε₁ := by positivity
  have hε₁_le1 : ε₁ ≤ 1 := min_le_left _ _
  have hε₁_bd : ε₁ * (14 * (A₀ + 1) * M_W') ≤ ε₀ := by
    have h1 : ε₁ ≤ ε₀ / (14 * (A₀ + 1) * M_W' + 1) := min_le_right _ _
    have hden : 0 < 14 * (A₀ + 1) * M_W' + 1 := by positivity
    calc ε₁ * (14 * (A₀ + 1) * M_W') ≤ ε₀ / (14 * (A₀ + 1) * M_W' + 1) * (14 * (A₀ + 1) * M_W') := by gcongr
      _ ≤ ε₀ / (14 * (A₀ + 1) * M_W' + 1) * (14 * (A₀ + 1) * M_W' + 1) := by gcongr; linarith
      _ = ε₀ := div_mul_cancel₀ _ hden.ne'
  obtain ⟨δW, hδW0, hδW⟩ := Metric.uniformContinuousOn_iff.mp hucW ε₁ hε₁_pos
  set η_u : ℝ := min 1 δW
  have hη_u : 0 < η_u := lt_min zero_lt_one hδW0
  obtain ⟨c_lo, C_hi, hc_lo, hC_hi, hcj⟩ :=
    virasoro_cardy_jAiry_bounds (half_pos xiStar_pos) (by linarith : xiStar / 2 ≤ xiStar + 1)
  have hrat_ev := virasoro_cardy_jAiry_ratio_tendsto (half_pos xiStar_pos)
    (by linarith : xiStar / 2 ≤ xiStar + 1) hZ0 ε₁ hε₁_pos
  have hpsi_ev := bump_psi_uniform spinMomentW5Prob d5 N hN hη0 hη1 σs hR1 hε₁_pos
  obtain ⟨ρw, hρw, hw5rat⟩ := virasoro_w5_cardy_ratio_tendsto (half_pos xiStar_pos)
    (by linarith : xiStar / 2 ≤ xiStar + 1) ε₁ hε₁_pos
  set C_A := 2 * (xiStar + 1) ^ 2 + 1
  have hslope_Z : ∀ᶠ c' in atTop, betaTip * Z * c' ^ (-(1 / 3 : ℝ)) < η_u ∧
      Z / c' ≤ min (min (1 / 2) (ρw / 2)) (ε₁ / (3 * C_A)) ∧
      R * slopeAiry c' ≤ min (min (1 / 2) (ρw / 2)) (ε₁ / (3 * C_A)) := by
    have ht1 : Tendsto (fun c' : ℝ => betaTip * Z * c' ^ (-(1 / 3 : ℝ))) atTop (nhds 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul (betaTip * Z)
    have ht2 : Tendsto (fun c' : ℝ => Z / c') atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have ht3 : Tendsto (fun c' : ℝ => R * slopeAiry c') atTop (nhds 0) := by
      have heq : slopeAiry = fun c => c ^ (-(2 / 3 : ℝ)) / betaTip := by
        ext c; unfold slopeAiry epsAiry; rfl
      rw [heq]
      simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).div_const betaTip).const_mul R
    exact (ht1.eventually (gt_mem_nhds hη_u)).and
      ((ht2.eventually_le_const (by positivity)).and (ht3.eventually_le_const (by positivity)))
  filter_upwards [hdom, bAiry_eq_of_Icc hR, hcj, hrat_ev, hpsi_ev, hw5rat, hslope_Z,
    bumpG_good spinMomentW5Prob d5 N hN hη0.le hη1 σs, eventually_ge_atTop (1 : ℝ)]
    with c' hdom' hbx hcj' hrat' hpsi' hw5' ⟨hs1, hs2, hs3⟩ ⟨hc', htest, _⟩ hc1 u hu
  obtain ⟨hbx_eq, hx_lo, hx_hi'⟩ := hbx u hu
  set x := bAiry c' u
  have hx0 : 0 < x := (half_pos xiStar_pos).trans_le hx_lo
  have ht_eq : tAiry c' u = c' * x ^ 2 / 3 := by unfold tAiry; ring
  have hint_z : IntegrableOn (fun z => volterraKernelV N η σs c' u z) (Ici 0) volume := by
    have hcont_t : ContinuousOn (fun z : ℝ => c' * (x + z / c') ^ 2 / 3) (Ici 0) :=
      ContinuousOn.div_const (ContinuousOn.mul continuousOn_const
        ((continuousOn_const.add (continuousOn_id.div_const c')).pow 2)) 3
    have hcont_z : ContinuousOn (fun z => volterraKernelV N η σs c' u z) (Ici 0) := by
      unfold volterraKernelV
      refine (((continuousOn_const.sub (((continuousOn_const.add
        (continuousOn_id.div_const c')).pow 2).div_const 3)).div_const 2).mul
        ((continuousOn_const.mul (continuousOn_const.add (continuousOn_id.div_const c'))).div_const 3)).mul ?_
      exact continuousOn_const.mul (htest.cont.comp hcont_t fun z hz => by
        simp only [mem_Ici] at hz ⊢; positivity)
    have hI_dom : IntegrableOn (fun z => C_dom * Real.exp (-2 * π * z / 3)) (Ici 0) volume := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      have : (fun z => C_dom * Real.exp (-2 * π * z / 3)) = fun z => C_dom * Real.exp (-(2 * π / 3) * z) := by
        ext z; ring_nf
      rw [this]
      exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (by positivity)) 0).const_mul _
    refine hI_dom.mono' (hcont_z.aestronglyMeasurable measurableSet_Ici) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    exact (Real.norm_eq_abs _).le.trans (hdom' u hu z (mem_Ici.mp hz))
  have hid_int : psiScale virasoroProblem c' *
      psiAiry virasoroProblem c' (spinMomentVolterraScaled d5 N η σs c') u =
      ∫ z in Ici 0, volterraKernelV N η σs c' u z := by
    unfold psiAiry spinMomentVolterraScaled spinVolterraAdjoint
    rw [ht_eq, endpoint_Ici_comp_sq hc' hx0 (fun t => (3 * (c' * x ^ 2 / 3) - t) / 2 *
      bumpG spinMomentW5Prob d5 N η σs c' t), integral_Ici_shift_div hc' x]
    rw [show ∀ a b d : ℝ, psiScale virasoroProblem c' * ((1 / c' * a) / c' * b * d) =
        (psiScale virasoroProblem c' * b * d / c' ^ 2) * a from fun _ _ _ => by ring,
      ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    unfold volterraKernelV
    dsimp only []
    rw [show (3 * (c' * x ^ 2 / 3) - c' * (x + z / c') ^ 2 / 3) / 2 =
        c' * ((x ^ 2 - (x + z / c') ^ 2 / 3) / 2) by ring]
    have hid : ∀ P R₁ R₂ G : ℝ,
        (P / c' ^ 2) * (2 * c' * R₁ / 3 * (c' * R₂ * G)) = R₂ * (2 * R₁ / 3) * (P * G) :=
      fun P R₁ R₂ G => by field_simp [hc'.ne']
    exact hid _ _ _ _
  have hI_exp0 : (∫ z in Ici (0 : ℝ), A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u) =
      (xiStar ^ 3 / (3 * π)) * sigWinW N η σs u := by
    have heq : (fun z : ℝ => A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u) =
        fun z => (A₀ * sigWinW N η σs u) * Real.exp (-(2 * π / 3) * z) := by
      ext z; ring_nf
    rw [heq, integral_const_mul, MeasureTheory.integral_Ici_eq_integral_Ioi,
      integral_exp_mul_Ioi (neg_lt_zero.mpr (by positivity)) 0, mul_zero, Real.exp_zero]
    dsimp [A₀]; field_simp; ring
  have hint_lim : IntegrableOn (fun z : ℝ => A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u)
      (Ici 0) volume := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have : (fun z : ℝ => A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u) =
        fun z => (A₀ * sigWinW N η σs u) * Real.exp (-(2 * π / 3) * z) := by
      ext z; ring_nf
    rw [this]
    exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (by positivity)) 0).const_mul _
  have hsplit_V : ∫ z in Ici 0, volterraKernelV N η σs c' u z =
      (∫ z in Ico 0 Z, volterraKernelV N η σs c' u z) + ∫ z in Ici Z, volterraKernelV N η σs c' u z := by
    rw [← Ico_union_Ici_eq_Ici hZ0]
    exact setIntegral_union (Set.disjoint_iff.mpr fun z ⟨hz1, hz2⟩ => by
        simp only [mem_Ico, mem_Ici] at hz1 hz2; linarith)
      measurableSet_Ici (hint_z.mono_set Ico_subset_Ici_self) (hint_z.mono_set (Ici_subset_Ici.mpr hZ0))
  have hsplit_L : ∫ z in Ici 0, A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u =
      (∫ z in Ico 0 Z, A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u) +
        ∫ z in Ici Z, A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u := by
    rw [← Ico_union_Ici_eq_Ici hZ0]
    exact setIntegral_union (Set.disjoint_iff.mpr fun z ⟨hz1, hz2⟩ => by
        simp only [mem_Ico, mem_Ici] at hz1 hz2; linarith)
      measurableSet_Ici (hint_lim.mono_set Ico_subset_Ici_self)
      (hint_lim.mono_set (Ici_subset_Ici.mpr hZ0))
  have htail_V : |∫ z in Ici Z, volterraKernelV N η σs c' u z| ≤ ε / 4 := by
    have hnorm := MeasureTheory.norm_integral_le_integral_norm
      (μ := volume.restrict (Ici Z)) (fun z => volterraKernelV N η σs c' u z)
    rw [Real.norm_eq_abs] at hnorm
    have hi_dom : IntegrableOn (fun z => C_dom * Real.exp (-2 * π * z / 3)) (Ici Z) volume := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      have : (fun z => C_dom * Real.exp (-2 * π * z / 3)) = fun z => C_dom * Real.exp (-(2 * π / 3) * z) := by
        ext z; ring_nf
      rw [this]; exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (by positivity)) Z).const_mul _
    have hle : ∫ z in Ici Z, ‖volterraKernelV N η σs c' u z‖ ≤ ∫ z in Ici Z, C_dom * Real.exp (-2 * π * z / 3) :=
      setIntegral_mono_on (hint_z.mono_set (Ici_subset_Ici.mpr hZ0)).norm hi_dom measurableSet_Ici
        fun z hz => by simpa [Real.norm_eq_abs] using hdom' u hu z (hZ0.trans (mem_Ici.mp hz))
    have hval : ∫ z in Ici Z, C_dom * Real.exp (-2 * π * z / 3) =
        (C_dom * (3 / (2 * π))) * Real.exp (-2 * π * Z / 3) := by
      have : (fun z => C_dom * Real.exp (-2 * π * z / 3)) = fun z => C_dom * Real.exp (-(2 * π / 3) * z) := by
        ext z; ring_nf
      rw [this, integral_const_mul, MeasureTheory.integral_Ici_eq_integral_Ioi,
        integral_exp_mul_Ioi (neg_lt_zero.mpr (by positivity)) Z,
        show -(2 * π / 3) * Z = -2 * π * Z / 3 by ring]
      field_simp
    have htail_bd : (C_dom * (3 / (2 * π))) * Real.exp (-2 * π * Z / 3) ≤ ε / 4 := by
      have : C_dom * (3 / (2 * π)) ≤ A_tail := by
        dsimp [A_tail]; linarith [show 0 ≤ xiStar ^ 3 / (3 * π) * M_W' + 1 by positivity]
      calc (C_dom * (3 / (2 * π))) * Real.exp (-2 * π * Z / 3)
          ≤ A_tail * Real.exp (-2 * π * Z / 3) := by gcongr
        _ ≤ ε / 4 := hZ_lt
    exact hnorm.trans (hle.trans (hval ▸ htail_bd))
  have htail_L : |∫ z in Ici Z, A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u| ≤ ε / 4 := by
    have hval : ∫ z in Ici Z, A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u =
        ((xiStar ^ 3 / (3 * π)) * sigWinW N η σs u) * Real.exp (-2 * π * Z / 3) := by
      have : (fun z => A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u) =
          fun z => (A₀ * sigWinW N η σs u) * Real.exp (-(2 * π / 3) * z) := by
        ext z; ring_nf
      rw [this, integral_const_mul, MeasureTheory.integral_Ici_eq_integral_Ioi,
        integral_exp_mul_Ioi (neg_lt_zero.mpr (by positivity)) Z,
        show -(2 * π / 3) * Z = -2 * π * Z / 3 by ring]
      dsimp [A₀]; field_simp; ring
    rw [hval, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hW_bd : |sigWinW N η σs u| ≤ M_W' := by
      have := hMW u hu; rw [Real.norm_eq_abs] at this
      dsimp [M_W']; linarith [le_max_left M_W 0]
    have h1 : (xiStar ^ 3 / (3 * π)) * |sigWinW N η σs u| ≤ A_tail := by
      calc (xiStar ^ 3 / (3 * π)) * |sigWinW N η σs u| ≤ (xiStar ^ 3 / (3 * π)) * M_W' := by gcongr
        _ ≤ A_tail := by dsimp [A_tail]; linarith [show 0 ≤ C_dom * (3 / (2 * π)) + 1 by positivity]
    calc |(xiStar ^ 3 / (3 * π)) * sigWinW N η σs u| * Real.exp (-2 * π * Z / 3)
        = (xiStar ^ 3 / (3 * π)) * |sigWinW N η σs u| * Real.exp (-2 * π * Z / 3) := by
          rw [abs_mul, abs_of_pos (by positivity)]
      _ ≤ A_tail * Real.exp (-2 * π * Z / 3) := by gcongr
      _ ≤ ε / 4 := hZ_lt
  have hmid_diff : |(∫ z in Ico 0 Z, volterraKernelV N η σs c' u z) -
      ∫ z in Ico 0 Z, A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u| ≤ ε / 4 := by
    rw [← integral_sub (hint_z.mono_set Ico_subset_Ici_self) (hint_lim.mono_set Ico_subset_Ici_self)]
    have hpt : ∀ z ∈ Ico 0 Z,
        |volterraKernelV N η σs c' u z - A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u| ≤ ε₀ := by
      intro z hz
      have hzIcc : z ∈ Icc 0 Z := ⟨hz.1, hz.2.le⟩
      set y := x + z / c'
      have hyx : y - x = z / c' := by dsimp [y]; ring
      have hxz : |x - xiStar| ≤ min (min (1 / 2) (ρw / 2)) (ε₁ / (3 * C_A)) := by
        rw [hbx_eq, show xiStar - u * slopeAiry c' - xiStar = -(u * slopeAiry c') by ring,
          abs_neg, abs_mul, abs_of_pos (slopeAiry_pos hc')]
        exact (mul_le_mul_of_nonneg_right (abs_le.mpr ⟨hu.1, hu.2⟩) (slopeAiry_pos hc').le).trans hs3
      have hyz : |y - xiStar| ≤ min (min (1 / 2) (ρw / 2)) (ε₁ / (3 * C_A)) + Z / c' := by
        calc |y - xiStar| = |(y - x) + (x - xiStar)| := by congr 1; ring
          _ ≤ |y - x| + |x - xiStar| := abs_add_le _ _
          _ ≤ Z / c' + min (min (1 / 2) (ρw / 2)) (ε₁ / (3 * C_A)) := by
              gcongr; rw [hyx, abs_of_nonneg (div_nonneg hz.1 hc'.le)]
              exact div_le_div_of_nonneg_right hz.2.le hc'.le
          _ = _ := add_comm _ _
      have hy_lo : xiStar / 2 ≤ y := by linarith [div_nonneg hz.1 hc'.le]
      have hy_hi1 : y ≤ xiStar + 1 := by
        linarith [(abs_le.mp hyz).2, min_le_left (1 / 2) (ρw / 2),
          min_le_left (min (1 / 2) (ρw / 2)) (ε₁ / (3 * C_A)),
          (le_trans hs2 (min_le_left _ _ |>.trans (min_le_left _ _)) : Z / c' ≤ 1 / 2)]
      have hy_rho : |y - xiStar| ≤ ρw := by
        have h1 : min (min (1 / 2) (ρw / 2)) (ε₁ / (3 * C_A)) ≤ ρw / 2 :=
          (min_le_left _ _).trans (min_le_right _ _)
        have h2 : Z / c' ≤ ρw / 2 := hs2.trans ((min_le_left _ _).trans (min_le_right _ _))
        linarith
      have hcb_y := hcj' y ⟨hy_lo, hy_hi1⟩
      have hcb_y_pos : 0 < psiScale virasoroProblem c' * virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) *
          jAiry c' (c' * y ^ 2 / 3) := lt_of_lt_of_le (by positivity) hcb_y.1
      set u' := uAiry c' (c' * y ^ 2 / 3)
      have hu'_eq : u' = u - betaTip * z * c' ^ (-(1 / 3 : ℝ)) := by
        have hu_eq : u = uAiry c' (c' * x ^ 2 / 3) := (uAiry_bAiry_eq hc' hx0 hbx_eq).symm
        change uAiry c' (c' * y ^ 2 / 3) = _
        unfold uAiry at hu_eq ⊢
        rw [show 3 * (c' * y ^ 2 / 3) / c' = y ^ 2 by field_simp, Real.sqrt_sq (by linarith)]
        rw [show 3 * (c' * x ^ 2 / 3) / c' = x ^ 2 by field_simp, Real.sqrt_sq hx0.le] at hu_eq
        have hc_p : c' ^ ((2 : ℝ) / 3) / c' = c' ^ (-(1 / 3 : ℝ)) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg_one c', ← Real.rpow_add hc']; norm_num
        dsimp [y]
        calc -betaTip * (x + z / c' - xiStar) * c' ^ ((2 : ℝ) / 3)
            = -betaTip * (x - xiStar) * c' ^ ((2 : ℝ) / 3) - betaTip * z * (c' ^ ((2 : ℝ) / 3) / c') := by ring
          _ = u - betaTip * z * c' ^ (-(1 / 3 : ℝ)) := by rw [← hu_eq, hc_p]
      have hbz_nn : 0 ≤ betaTip * z * c' ^ (-(1 / 3 : ℝ)) :=
        mul_nonneg (mul_nonneg hbt.le hz.1) (Real.rpow_nonneg hc'.le _)
      have hu'_dist : dist u' u < δW := by
        rw [Real.dist_eq, hu'_eq, show u - betaTip * z * c' ^ (-(1 / 3 : ℝ)) - u =
            -(betaTip * z * c' ^ (-(1 / 3 : ℝ))) by ring, abs_neg,
          abs_of_nonneg hbz_nn]
        have h1 : betaTip * z * c' ^ (-(1 / 3 : ℝ)) ≤ betaTip * Z * c' ^ (-(1 / 3 : ℝ)) := by
          gcongr; exact hz.2.le
        exact lt_of_lt_of_le (h1.trans_lt hs1) (min_le_right 1 δW)
      have hu'_mem : u' ∈ Icc (-(R + 1)) (R + 1) := by
        have h1 : betaTip * z * c' ^ (-(1 / 3 : ℝ)) ≤ 1 := by
          have : betaTip * z * c' ^ (-(1 / 3 : ℝ)) ≤ betaTip * Z * c' ^ (-(1 / 3 : ℝ)) := by
            gcongr; exact hz.2.le
          linarith [hs1, min_le_left (1 : ℝ) δW]
        rw [hu'_eq]; constructor <;> linarith [hu.1, hu.2]
      have hu_mem1 : u ∈ Icc (-(R + 1)) (R + 1) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hKV_eq : volterraKernelV N η σs c' u z =
          (((x ^ 2 - y ^ 2 / 3) / 2) * (2 * y / 3)) *
          (virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) * jAiry c' (c' * x ^ 2 / 3) /
            (virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) * jAiry c' (c' * y ^ 2 / 3))) *
          (psiScale virasoroProblem c' * psiAiry virasoroProblem c' (bumpG spinMomentW5Prob d5 N η σs c') u') := by
        have hcy : virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) * jAiry c' (c' * y ^ 2 / 3) ≠ 0 := by
          intro h0
          rw [mul_assoc (psiScale virasoroProblem c'), h0, mul_zero] at hcb_y_pos
          exact lt_irrefl 0 hcb_y_pos
        have hpsi_y : psiScale virasoroProblem c' *
            psiAiry virasoroProblem c' (bumpG spinMomentW5Prob d5 N η σs c') u' =
            psiScale virasoroProblem c' *
              (bumpG spinMomentW5Prob d5 N η σs c' (c' * y ^ 2 / 3) *
                (virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) * jAiry c' (c' * y ^ 2 / 3))) := by
          unfold psiAiry; rw [tAiry_uAiry hc' (by positivity)]; ring
        unfold volterraKernelV
        dsimp only []
        rw [hpsi_y, mul_assoc (((x ^ 2 - y ^ 2 / 3) / 2) * (2 * y / 3))]
        exact congrArg ((((x ^ 2 - y ^ 2 / 3) / 2) * (2 * y / 3)) * ·)
          (cancel_mid_factor (psiScale virasoroProblem c')
            (virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3))
            (jAiry c' (c' * x ^ 2 / 3))
            (bumpG spinMomentW5Prob d5 N η σs c' (c' * y ^ 2 / 3))
            (virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) * jAiry c' (c' * y ^ 2 / 3)) hcy)
      have hA_diff : |((x ^ 2 - y ^ 2 / 3) / 2) * (2 * y / 3) - A₀| ≤ ε₁ :=
        endpoint_poly_bound hξ (by linarith) (by linarith) (by linarith) hy_hi1 rfl
          (hxz.trans (min_le_right _ _))
          (hyz.trans (by
            have h1 : min (min (1 / 2) (ρw / 2)) (ε₁ / (3 * C_A)) ≤ ε₁ / (3 * C_A) := min_le_right _ _
            have h2 : Z / c' ≤ ε₁ / (3 * C_A) := hs2.trans (min_le_right _ _)
            linarith))
      have hR_diff : |virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) * jAiry c' (c' * x ^ 2 / 3) /
            (virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) * jAiry c' (c' * y ^ 2 / 3)) -
          Real.exp (-2 * π * z / 3)| ≤ ε₁ :=
        hrat' x ⟨hx_lo, by linarith⟩ z hzIcc
      have hW0_bd : |sigWinW N η σs u| ≤ M_W' := by
        have := hMW u hu; rw [Real.norm_eq_abs] at this
        dsimp [M_W']; linarith [le_max_left M_W 0]
      have hMW1 : 1 ≤ M_W' := by dsimp [M_W']; linarith [le_max_right M_W 0]
      have hW_diff : |psiScale virasoroProblem c' *
            psiAiry virasoroProblem c' (bumpG spinMomentW5Prob d5 N η σs c') u' -
          sigWinW N η σs u| ≤ 5 * M_W' * ε₁ :=
        endpoint_w_diff_bound (psiAiry_virasoro_eq_w5_mul hc' (by linarith) _)
          (hw5' y hy_rho) (hpsi' u' hu'_mem)
          (by simpa only [Real.dist_eq] using (hδW u' hu'_mem u hu_mem1 hu'_dist).le)
          hW0_bd hMW1 hε₁_le1
      have hR0_bd : |Real.exp (-2 * π * z / 3)| ≤ 1 := by
        rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
        have hpi_z : 0 ≤ π * z := mul_nonneg Real.pi_pos.le hz.1
        linarith
      rw [hKV_eq]
      exact @endpoint_three_way_bound
        (((x ^ 2 - y ^ 2 / 3) / 2) * (2 * y / 3)) A₀
        (virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) * jAiry c' (c' * x ^ 2 / 3) /
          (virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) * jAiry c' (c' * y ^ 2 / 3)))
        (Real.exp (-2 * π * z / 3))
        (psiScale virasoroProblem c' *
          psiAiry virasoroProblem c' (bumpG spinMomentW5Prob d5 N η σs c') u')
        (sigWinW N η σs u) M_W' ε₁ ε₀
        hε₁_pos.le hε₁_le1 (by positivity) hMW1
        hA_diff hR_diff hW_diff hR0_bd hW0_bd hε₁_bd
    have hnorm := MeasureTheory.norm_integral_le_integral_norm
      (μ := volume.restrict (Ico 0 Z))
      (fun z => volterraKernelV N η σs c' u z - A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u)
    rw [Real.norm_eq_abs] at hnorm
    calc |∫ z in Ico 0 Z, (volterraKernelV N η σs c' u z - A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u)|
        ≤ ∫ z in Ico 0 Z, ‖volterraKernelV N η σs c' u z - A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u‖ :=
          hnorm
      _ ≤ ∫ _ in Ico 0 Z, ε₀ := setIntegral_mono_on
          ((hint_z.mono_set Ico_subset_Ici_self).sub (hint_lim.mono_set Ico_subset_Ici_self)).norm
          (integrableOn_const (C := ε₀) (by simp)) measurableSet_Ico
          fun z hz => by simpa [Real.norm_eq_abs] using hpt z hz
      _ = Z * ε₀ := by
          rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ico,
            ENNReal.toReal_ofReal (by linarith), sub_zero]
      _ ≤ ε / 4 := by
          dsimp [ε₀]
          rw [show Z * (ε / (4 * (Z + 1))) = (Z / (Z + 1)) * (ε / 4) by
            field_simp [show Z + 1 ≠ 0 by linarith]]
          exact mul_le_of_le_one_left (by linarith) (div_le_one_of_le₀ (by linarith) (by linarith))
  rw [hid_int, hsplit_V, ← hI_exp0, hsplit_L]
  calc |((∫ z in Ico 0 Z, volterraKernelV N η σs c' u z) + ∫ z in Ici Z, volterraKernelV N η σs c' u z) -
        ((∫ z in Ico 0 Z, A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u) +
          ∫ z in Ici Z, A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u)|
      = |((∫ z in Ico 0 Z, volterraKernelV N η σs c' u z) -
            ∫ z in Ico 0 Z, A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u) +
          ((∫ z in Ici Z, volterraKernelV N η σs c' u z) -
            ∫ z in Ici Z, A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u)| := by
        congr 1; ring
    _ ≤ |(∫ z in Ico 0 Z, volterraKernelV N η σs c' u z) -
            ∫ z in Ico 0 Z, A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u| +
          |(∫ z in Ici Z, volterraKernelV N η σs c' u z) -
            ∫ z in Ici Z, A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u| := abs_add_le _ _
    _ ≤ ε / 4 + (|∫ z in Ici Z, volterraKernelV N η σs c' u z| +
          |∫ z in Ici Z, A₀ * Real.exp (-2 * π * z / 3) * sigWinW N η σs u|) := by
        gcongr; exact abs_sub _ _
    _ ≤ ε / 4 + (ε / 4 + ε / 4) := by gcongr
    _ ≤ ε := by linarith

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinMoment_endpoint_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spinMoment_endpoint_tendsto

end FormalResearch.ModularBootstrap.Spin
