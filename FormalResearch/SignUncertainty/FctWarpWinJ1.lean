/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpWinJ0

/-!
# Window `J₁ - J₀` and `L`-difference symbol bounds (`fct:warp-win`)

Leaf module establishing `win_J1_sub_J0_and_diff` for `0 ≤ ell1 ≤ ell2 ≤ Sw_ell * c^{-1/6}`:
* `J₁(ell₂, Y(u)) - J₀(ell₂, Y(u)) ∈ 𝒮^8(C c^{-17/12})` (`ChartSetup.dJ_jets` + `win_dJ_comp_Y_sym (m := 4)`);
* `(J₁(ell₂, Y(u)) - J₀(ell₂, Y(u))) - (J₁(ell₁, Y(u)) - J₀(ell₁, Y(u))) ∈ 𝒮^8(C c^{-5/4} (ell₂ - ell₁))`
  via `hasDerivAt_iteratedDeriv_path`, `ChartSetup.dJ_jets_u` (`v = (0, 1, 0)`, `u = (1, 0, 0)`), and
  `win_dJ_comp_Y_sym (m := 3)`.

Class: proved.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped Real ContDiff BigOperators
open FormalResearch.CohnElkies FormalResearch.Special FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD FormalResearch.SignUncertainty.FctMoment
open FormalResearch.SignUncertainty.FctSymA FormalResearch.SignUncertainty.CtCfu

namespace FormalResearch.SignUncertainty

private noncomputable def winDJBeta (C_H : ℝ) : ℝ :=
  max 4 (max ((4 + 2 ^ 16) * ((Nat.factorial 16 : ℝ) * pbM)) C_H)

private structure WinDJProps (Sw_ell c α : ℝ) (S : ChartSetup (ℝ × ℝ × ℝ))
    (τ₁ β δH : ℝ) (θ : (ℝ × ℝ × ℝ) × ℝ → ℝ) : Prop where
  hτ₁_pos : 0 < τ₁
  hτ₁_3 : τ₁ ^ 3 = c ^ (-(3 / 4 : ℝ))
  hτ₁_sq_le1 : τ₁ ^ 2 ≤ 1
  hψ : ∀ q ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6,
    fderiv ℝ (fun q : (ℝ × ℝ × ℝ) × ℝ => S.ℓ q.1 - π ^ 2 / 36 * q.2 + S.r q) q ((0, 1, 0), 0) =
      τ₁ ^ 3 * q.2 ^ 5 * θ q
  hθ_jc : JCΦ 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) θ (Φb^[3] β) 0
  hH_jcΦ : JCΦ 16 (Ioo (-δH) δH) fctH (Φb^[3] β) 0
  hHT : ∀ q ∈ S.Ω ×ˢ Yint, τ₁ ^ 2 * (q.2 * S.V q ^ 2) ∈ Ioo (-δH) δH
  hJcd : ∀ p ∈ S.Ω, ContDiffOn ℝ 15 (fun s => Jfun S.V fctH (τ₁ ^ 2) (p, s)) Yint
  hJ_cd15 : ContDiffOn ℝ 15 (Jfun S.V fctH (τ₁ ^ 2)) (S.Ω ×ˢ Yint)
  hseg_pt : ∀ {ell : ℝ}, 0 ≤ ell → ell ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) →
    ∀ t ∈ Icc (0 : ℝ) 1, (ell, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) ∈ S.Ω
  hSA_of : ∀ {ell : ℝ}, 0 ≤ ell → ell ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) →
    ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ S.A ((ell, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) ∧
      S.A ((ell, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) ≤ max 8 (2 * Sw_ell) * c ^ (-(1 / 6 : ℝ))

private lemma rho_bound_of_15 {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {S : ChartSetup P} (h15 : 15 * S.ε ≤ 1 / 2) (hr0 : ∀ p ∈ S.Ω, S.r (p, 0) = 0)
    {p : P} (hp : p ∈ S.Ω) {z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 6) :
    |rhoF S.r (p, z)| ≤ 1 / 2 * |z| := by
  have hO : IsOpen (S.Ω ×ˢ Ioo (-1 : ℝ) 6) := S.hΩ.prod isOpen_Ioo
  have h17 := (S.hr.succ_fderiv hO).clm_apply_const hO.uniqueDiffOn ((0 : P), (1 : ℝ))
  have hp_emb : ContDiffOn ℝ 18 (fun w : ℝ => (p, w)) (Ioo (-1 : ℝ) 6) := by fun_prop
  have hr_w : ContDiffOn ℝ 18 (fun w => S.r (p, w)) (Ioo (-1 : ℝ) 6) :=
    S.hr.1.comp hp_emb fun w hw => ⟨hp, hw⟩
  have hfd_w : ContDiffOn ℝ 17 (fun w => fderiv ℝ S.r (p, w) (0, 1)) (Ioo (-1 : ℝ) 6) :=
    h17.1.comp (hp_emb.of_le (by norm_num : (17 : WithTop ℕ∞) ≤ 18)) fun w hw => ⟨hp, hw⟩
  have hrho_cd : ContDiffOn ℝ 1 (fun w => rhoF S.r (p, w)) (Ioo (-1 : ℝ) 6) :=
    ((hr_w.of_le (by norm_num)).add
      (contDiffOn_const.mul (contDiffOn_id.mul (hfd_w.of_le (by norm_num))))).congr fun _ _ => rfl
  have hderiv_bd : ∀ w ∈ Ioo (-1 : ℝ) 6, |deriv (fun t => rhoF S.r (p, t)) w| ≤ 1 / 2 := by
    intro w hw
    have hq : (p, w) ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6 := ⟨hp, hw⟩
    have hdr : HasDerivAt (fun t => S.r (p, t)) (fderiv ℝ S.r (p, w) (0, 1)) w :=
      (((S.hr.1.contDiffAt (hO.mem_nhds hq)).differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt w
        (by simpa using (hasDerivAt_const w p).prodMk (hasDerivAt_id w))
    have hd2 : HasDerivAt (fun t => fderiv ℝ S.r (p, t) (0, 1))
        (fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)) w :=
      (((h17.1.contDiffAt (hO.mem_nhds hq)).differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt w
        (by simpa using (hasDerivAt_const w p).prodMk (hasDerivAt_id w))
    have htot : HasDerivAt (fun t => rhoF S.r (p, t))
        (fderiv ℝ S.r (p, w) (0, 1) + 2 * (1 * fderiv ℝ S.r (p, w) (0, 1) +
          w * fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1))) w :=
      (hdr.add (((hasDerivAt_id w).mul hd2).const_mul 2)).congr_of_eventuallyEq
        (Eventually.of_forall fun t => by simp [rhoF])
    rw [htot.deriv]
    have hn1 : ‖((0 : P), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
    have hb1 : |fderiv ℝ S.r (p, w) (0, 1)| ≤ S.ε := by
      have hbd := S.hr.2 1 (by norm_num) (p, w) hq
      rw [norm_iteratedFDerivWithin_one _ (hO.uniqueDiffOn _ hq), fderivWithin_of_isOpen hO hq] at hbd
      calc |fderiv ℝ S.r (p, w) (0, 1)| = ‖fderiv ℝ S.r (p, w) (0, 1)‖ := Real.norm_eq_abs _
        _ ≤ ‖fderiv ℝ S.r (p, w)‖ * ‖((0 : P), (1 : ℝ))‖ := (fderiv ℝ S.r _).le_opNorm _
        _ ≤ S.ε * 1 := mul_le_mul hbd (le_of_eq hn1) (norm_nonneg _) S.hε
        _ = S.ε := mul_one _
    have hb2 : |fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)| ≤ S.ε := by
      have hbd := h17.2 1 (by norm_num) (p, w) hq
      rw [norm_iteratedFDerivWithin_one _ (hO.uniqueDiffOn _ hq), fderivWithin_of_isOpen hO hq] at hbd
      rw [hn1, one_mul] at hbd
      calc |fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)|
          = ‖fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)‖ := Real.norm_eq_abs _
        _ ≤ ‖fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w)‖ * ‖((0 : P), (1 : ℝ))‖ := (fderiv ℝ _ _).le_opNorm _
        _ ≤ S.ε * 1 := mul_le_mul hbd (le_of_eq hn1) (norm_nonneg _) S.hε
        _ = S.ε := mul_one _
    have hw6 : |w| ≤ 6 := by rw [abs_le]; constructor <;> linarith only [hw.1, hw.2]
    calc |fderiv ℝ S.r (p, w) (0, 1) + 2 * (1 * fderiv ℝ S.r (p, w) (0, 1) +
            w * fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1))|
        = |3 * fderiv ℝ S.r (p, w) (0, 1) +
            2 * w * fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)| := by congr 1; ring
      _ ≤ |3 * fderiv ℝ S.r (p, w) (0, 1)| +
            |2 * w * fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)| := abs_add_le _ _
      _ = 3 * |fderiv ℝ S.r (p, w) (0, 1)| +
            2 * |w| * |fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)| := by
          rw [abs_mul, abs_mul, abs_mul, show |(3 : ℝ)| = 3 by norm_num, show |(2 : ℝ)| = 2 by norm_num]
      _ ≤ 3 * S.ε + 2 * 6 * S.ε := by gcongr
      _ = 15 * S.ε := by ring
      _ ≤ 1 / 2 := h15
  have hmv := (convex_Ioo (-1 : ℝ) 6).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun w hw => ((hrho_cd.differentiableOn (by norm_num) w hw).hasDerivWithinAt).congr_deriv
      (by rw [derivWithin_of_isOpen isOpen_Ioo hw]))
    (fun w hw => by rw [Real.norm_eq_abs]; exact hderiv_bd w hw)
    (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 6 from ⟨by norm_num, by norm_num⟩) hz
  simpa [hr0 p hp, rhoF, Real.norm_eq_abs, sub_zero] using hmv

private lemma win_dj_props {K4 Sw_ell ε c α : ℝ} (hK4 : 1 ≤ K4)
    (hε : ε = 1 ∨ ε = -1) (hc160000 : (160000 : ℝ) ≤ c) (hcC0 : (30 * pbC0 + 1) ^ 2 ≤ c)
    (hSw_lt : Sw_ell * c ^ (-(1 / 6 : ℝ)) < 27 / 10)
    (hτ_lim : c ^ (-(1 / 4 : ℝ)) ≤ pbTauLim) (hK4t : K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1)
    {δH C_H : ℝ} (hH_jc : JC 16 (Ioo (-δH) δH) fctH C_H) (hτ1_δH : (c ^ (-(1 / 4 : ℝ))) ^ 2 < δH / 6)
    (hα : |α| ≤ c ^ (-(1 / 2 : ℝ))) :
    WinDJProps Sw_ell c α (concreteBoxS K4 ε c) (c ^ (-(1 / 4 : ℝ))) (winDJBeta C_H) δH
      (fun q => (concreteBoxT K4 ε c).Th (c ^ (-(1 / 4 : ℝ))) K4 q.1.2.2 q.2) := by
  have hc0 : 0 < c := by linarith only [hc160000]
  have hvalid : concreteBoxValid K4 ε c := ⟨hK4, hε, hc0, hτ_lim, hK4t⟩
  set T := concreteBoxT K4 ε c
  set S := concreteBoxS K4 ε c
  obtain ⟨hTM, _, _, hSΩ, hSℓ, hSr, hSε, _, _, _⟩ := concreteBox_spec hvalid
  set τ₁ : ℝ := c ^ (-(1 / 4 : ℝ))
  have hτ₁_pos : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hτ₁_20 : τ₁ ≤ 1 / 20 := by
    have h2 := Real.rpow_le_rpow_of_nonpos (by norm_num) hc160000 (by norm_num : -(1 / 4 : ℝ) ≤ 0)
    have h3 : (160000 : ℝ) ^ (-(1 / 4 : ℝ)) = 1 / 20 := by
      rw [show (160000 : ℝ) = (20 : ℝ) ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num)]
      norm_num [Real.rpow_neg_one]
    exact h2.trans_eq h3
  have hτ₁_1 : τ₁ ≤ 1 := by linarith only [hτ₁_20]
  have hτ₁_sq_le1 : τ₁ ^ 2 ≤ 1 := by nlinarith only [hτ₁_1, hτ₁_pos]
  have hτ₁_sq : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
    dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hτ₁_3 : τ₁ ^ 3 = c ^ (-(3 / 4 : ℝ)) := by
    dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hSε_bd : 15 * S.ε ≤ 1 / 2 := by
    have h1 : 30 * pbC0 + 1 ≤ c ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le hcC0
    have hpos : (0 : ℝ) < 30 * pbC0 + 1 := by linarith only [pbC0_nonneg]
    rw [hSε, hτ₁_sq, Real.rpow_neg hc0.le]
    have h2 : pbC0 * (c ^ (1 / 2 : ℝ))⁻¹ ≤ 1 / 30 := by
      calc pbC0 * (c ^ (1 / 2 : ℝ))⁻¹ ≤ pbC0 * (30 * pbC0 + 1)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ hpos h1) pbC0_nonneg
        _ ≤ 1 / 30 := by rw [← div_eq_mul_inv, div_le_div_iff₀ hpos (by norm_num)]; linarith only
    linarith only [h2]
  have hr0 : ∀ p ∈ S.Ω, S.r (p, 0) = 0 := fun p _ => by
    rw [hSr]; simp only [CfuTheta.r]; norm_num
  have hρ_bd : ∀ p ∈ S.Ω, ∀ z ∈ Ioo (-1 : ℝ) 6, |rhoF S.r (p, z)| ≤ 1 / 2 * |z| :=
    fun p hp z hz => rho_bound_of_15 hSε_bd hr0 hp hz
  have hα_om : |α| < 2 * (c ^ (-(1 / 4 : ℝ))) ^ 2 := by
    rw [← show τ₁ = c ^ (-(1 / 4 : ℝ)) from rfl, hτ₁_sq]
    linarith only [hα, Real.rpow_pos_of_pos hc0 (-(1 / 2 : ℝ))]
  have hseg_pt : ∀ {ell : ℝ}, 0 ≤ ell → ell ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) →
      ∀ t ∈ Icc (0 : ℝ) 1, (ell, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) ∈ S.Ω := by
    intro ell hell0 hell_ub t ht
    have hpt : (ell, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) = (ell, t, α) := by ext <;> simp
    rw [hpt, hSΩ]
    exact ⟨⟨by linarith only [hell0], by linarith only [hell_ub, hSw_lt]⟩,
      ⟨by linarith only [ht.1], by linarith only [ht.2]⟩, abs_lt.mp hα_om⟩
  have hSA_of : ∀ {ell : ℝ}, 0 ≤ ell → ell ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) →
      ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ S.A ((ell, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) ∧
        S.A ((ell, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) ≤ max 8 (2 * Sw_ell) * c ^ (-(1 / 6 : ℝ)) := by
    intro ell hell0 hell_ub t ht
    have hmem := hseg_pt hell0 hell_ub t ht
    have hpt : (ell, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) = (ell, t, α) := by ext <;> simp
    have hzp : S.ZeroPath ((ell, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) := by
      refine ⟨hmem, ?_, (1, 0, 0), by simp [Prod.norm_def], fun s hs => ?_⟩
      · rw [hSℓ, hpt]; exact hell0
      · rw [hpt] at hs ⊢
        rw [hSℓ] at hs; simp only at hs
        have hsub : (ell, t, α) - s • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) = (ell - s, t, α) := by ext <;> simp
        rw [hsub, hSℓ]
        refine ⟨?_, rfl⟩
        rw [hSΩ]
        exact ⟨⟨by linarith only [hs.1, hs.2, hell0], by linarith only [hs.1, hell_ub, hSw_lt]⟩,
          ⟨by linarith only [ht.1], by linarith only [ht.2]⟩, abs_lt.mp hα_om⟩
    have hAnn : 0 ≤ S.A ((ell, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) :=
      (S.A_comp hρ_bd hzp hzp rfl).1
    have hB := S.B_comp hρ_bd hzp
    rw [hSℓ, hpt] at hB
    have hB_le : S.B ((ell, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) ≤ 2 * ell := by
      have hpi3 : (3 : ℝ) < π := Real.pi_gt_three
      have h12 : (12 : ℝ) / π ^ 2 < 4 / 3 := by
        rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith only [hpi3]
      have hba := (abs_le.mp hB).2
      rw [hpt]
      nlinarith only [hba, h12, hell0]
    have hB_nn : 0 ≤ S.B ((ell, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) := by
      have hpi4 : π < 4 := Real.pi_lt_four
      have h12 : (3 / 4 : ℝ) < 12 / π ^ 2 := by
        rw [div_lt_div_iff₀ (by norm_num) (by positivity)]; nlinarith only [hpi4, Real.pi_pos]
      have hba := (abs_le.mp hB).1
      rw [hpt]
      nlinarith only [hba, h12, hell0]
    have hd_abs := abs_le.mp (S.d_dev hmem)
    have hd_lo : (92 / 100 : ℝ) ≤ S.d ((ell, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) := by
      linarith only [hd_abs.1, dStar_bounds.1]
    have hd_hi : S.d ((ell, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) ≤ 95 / 100 := by
      linarith only [hd_abs.2, dStar_bounds.2]
    have hd2_le1 : S.d ((ell, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) ^ 2 ≤ 1 := by
      nlinarith only [hd_lo, hd_hi]
    have hA_eq : S.A ((ell, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) =
        S.d ((ell, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) ^ 2 *
          S.B ((ell, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) := rfl
    have hA_le : S.A ((ell, 0, α) + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) ≤ 2 * Sw_ell * c ^ (-(1 / 6 : ℝ)) := by
      rw [hA_eq]
      calc S.d _ ^ 2 * S.B _ ≤ 1 * (2 * ell) := mul_le_mul hd2_le1 hB_le hB_nn zero_le_one
        _ = 2 * ell := one_mul _
        _ ≤ 2 * (Sw_ell * c ^ (-(1 / 6 : ℝ))) := by gcongr
        _ = 2 * Sw_ell * c ^ (-(1 / 6 : ℝ)) := by ring
    exact ⟨hAnn, hA_le.trans (mul_le_mul_of_nonneg_right (le_max_right 8 (2 * Sw_ell)) (by positivity))⟩
  let θ : (ℝ × ℝ × ℝ) × ℝ → ℝ := fun q => T.Th τ₁ K4 q.1.2.2 q.2
  let B_Th : ℝ := (4 + 2 ^ 16) * ((Nat.factorial 16 : ℝ) * pbM)
  let β : ℝ := winDJBeta C_H
  have hβ4 : 4 ≤ β := le_max_left _ _
  have hpbM : 0 ≤ pbM := pbM_nonneg
  have hψ : ∀ q ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6,
      fderiv ℝ (fun q : (ℝ × ℝ × ℝ) × ℝ => S.ℓ q.1 - π ^ 2 / 36 * q.2 + S.r q) q ((0, 1, 0), 0) =
        τ₁ ^ 3 * q.2 ^ 5 * θ q := by
    intro q hq
    have hO : IsOpen (S.Ω ×ˢ Ioo (-1 : ℝ) 6) := S.hΩ.prod isOpen_Ioo
    have hℓc : ContDiffAt ℝ 1 (fun x : (ℝ × ℝ × ℝ) × ℝ => S.ℓ x.1) q :=
      (S.hℓj.1.comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ × ℝ) ℝ).contDiff.contDiffOn
        (fun (x : (ℝ × ℝ × ℝ) × ℝ) (hx : x ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6) => hx.1)).contDiffAt
        (hO.mem_nhds hq) |>.of_le (by norm_num)
    have hrc : ContDiffAt ℝ 1 S.r q := (S.hr.1.contDiffAt (hO.mem_nhds hq)).of_le (by norm_num)
    have hline : HasDerivAt (fun s : ℝ =>
        S.ℓ (q.1 + s • (0, 1, 0)) - π ^ 2 / 36 * q.2 + S.r (q.1 + s • (0, 1, 0), q.2))
        (τ₁ ^ 3 * q.2 ^ 5 * θ q) 0 := by
      have heq : ∀ s : ℝ, S.ℓ (q.1 + s • (0, 1, 0)) - π ^ 2 / 36 * q.2 + S.r (q.1 + s • (0, 1, 0), q.2) =
          (q.1.1 - π ^ 2 / 36 * q.2 + τ₁ ^ 2 * (q.2 ^ 2 * T.mt (τ₁ ^ 2 * q.2)) -
            τ₁ ^ 4 * (q.2 * T.θt (τ₁ ^ 2 * q.2)) + q.1.2.1 * (τ₁ ^ 3 * (q.2 ^ 5 * θ q))) +
            s * (τ₁ ^ 3 * q.2 ^ 5 * θ q) := fun s => by
        rw [hSℓ, hSr]
        simp only [CfuTheta.r, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul,
          mul_zero, mul_one, add_zero, θ]
        ring
      let c_val : ℝ := q.1.1 - π ^ 2 / 36 * q.2 + τ₁ ^ 2 * (q.2 ^ 2 * T.mt (τ₁ ^ 2 * q.2)) -
        τ₁ ^ 4 * (q.2 * T.θt (τ₁ ^ 2 * q.2)) + q.1.2.1 * (τ₁ ^ 3 * (q.2 ^ 5 * θ q))
      have hd : HasDerivAt (fun s : ℝ => c_val + s * (τ₁ ^ 3 * q.2 ^ 5 * θ q))
          (0 + 1 * (τ₁ ^ 3 * q.2 ^ 5 * θ q)) 0 :=
        (hasDerivAt_const (0 : ℝ) c_val).add ((hasDerivAt_id (0 : ℝ)).mul_const (τ₁ ^ 3 * q.2 ^ 5 * θ q))
      exact (hd.congr_deriv (by ring)).congr_of_eventuallyEq (Eventually.of_forall fun s => heq s)
    have hpt0 : (q.1 + (0 : ℝ) • ((0 : ℝ), (1 : ℝ), (0 : ℝ)), q.2) = q := by simp
    have hf1 : HasFDerivAt (fun x : (ℝ × ℝ × ℝ) × ℝ => S.ℓ x.1 - π ^ 2 / 36 * x.2 + S.r x)
        (fderiv ℝ (fun x => S.ℓ x.1 - π ^ 2 / 36 * x.2 + S.r x) q)
        (q.1 + (0 : ℝ) • ((0 : ℝ), (1 : ℝ), (0 : ℝ)), q.2) :=
      hpt0.symm ▸ ((hℓc.sub (by fun_prop)).add hrc |>.differentiableAt (by norm_num)).hasFDerivAt
    have hcurve : HasDerivAt (fun s : ℝ => (q.1 + s • ((0 : ℝ), (1 : ℝ), (0 : ℝ)), q.2)) ((0, 1, 0), 0) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => q.1 + s • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) ((0 : ℝ), (1 : ℝ), (0 : ℝ)) 0 :=
        ((hasDerivAt_const (0 : ℝ) q.1).add ((hasDerivAt_id (0 : ℝ)).smul_const ((0 : ℝ), (1 : ℝ), (0 : ℝ)))).congr_deriv
          (by simp)
      exact h1.prodMk (hasDerivAt_const (0 : ℝ) q.2)
    have hf2 : HasDerivAt (fun s : ℝ => S.ℓ (q.1 + s • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) - π ^ 2 / 36 * q.2 +
        S.r (q.1 + s • ((0 : ℝ), (1 : ℝ), (0 : ℝ)), q.2))
        (fderiv ℝ (fun x => S.ℓ x.1 - π ^ 2 / 36 * x.2 + S.r x) q ((0, 1, 0), 0)) 0 := by
      simpa [Function.comp_def] using hf1.comp_hasDerivAt 0 hcurve
    exact hf2.unique hline
  have hθ_jc : JCΦ 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) θ (Φb^[3] β) 0 := by
    have hO : IsOpen (S.Ω ×ˢ Ioo (-1 : ℝ) 6) := S.hΩ.prod isOpen_Ioo
    have hUd : UniqueDiffOn ℝ (S.Ω ×ˢ Ioo (-1 : ℝ) 6) := hO.uniqueDiffOn
    let L_snd : ((ℝ × ℝ × ℝ) × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ (ℝ × ℝ × ℝ) ℝ
    have hLsnd_norm : ‖L_snd‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => ?_
      simpa [L_snd] using norm_snd_le p
    have hcomp : ∀ f : ℝ → ℝ, JC 18 (Ioo (-1 : ℝ) 6) f T.M →
        JC 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q => f q.2) ((Nat.factorial 16 : ℝ) * pbM) := fun f hf => by
      have h16 : JC 16 (Ioo (-1 : ℝ) 6) f pbM := (hf.mono_order (by norm_num)).mono (le_of_eq hTM)
      exact JC.comp_clm hUd isOpen_Ioo.uniqueDiffOn L_snd hLsnd_norm hpbM h16 fun q hq => hq.2
    have h0b := hcomp T.Θ0b T.jc_Θ0b
    have hfac_nn : 0 ≤ (Nat.factorial 16 : ℝ) * pbM := mul_nonneg (Nat.cast_nonneg _) hpbM
    have h0m : JC 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q => (K4 * τ₁ ^ 2) * T.Θ0m q.2)
        ((Nat.factorial 16 : ℝ) * pbM) := by
      have h1 := (hcomp T.Θ0m T.jc_Θ0m).const_smul hUd (K4 * τ₁ ^ 2)
      refine (h1.mono ?_).congr fun _ _ => rfl
      rw [abs_of_nonneg (mul_nonneg (by linarith only [hK4]) (sq_nonneg τ₁))]
      exact mul_le_of_le_one_left hfac_nn hK4t
    have h1b : JC 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q => τ₁ * T.Θ1b q.2)
        ((Nat.factorial 16 : ℝ) * pbM) := by
      have h1 := (hcomp T.Θ1b T.jc_Θ1b).const_smul hUd τ₁
      refine (h1.mono ?_).congr fun _ _ => rfl
      rw [abs_of_pos hτ₁_pos]; exact mul_le_of_le_one_left hfac_nn hτ₁_1
    have h1m : JC 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q => (K4 * τ₁ ^ 3) * T.Θ1m q.2)
        ((Nat.factorial 16 : ℝ) * pbM) := by
      have h1 := (hcomp T.Θ1m T.jc_Θ1m).const_smul hUd (K4 * τ₁ ^ 3)
      refine (h1.mono ?_).congr fun _ _ => rfl
      rw [abs_of_nonneg (mul_nonneg (by linarith only [hK4]) (pow_nonneg hτ₁_pos.le 3))]
      have hK3 : K4 * τ₁ ^ 3 ≤ 1 := by
        calc K4 * τ₁ ^ 3 = (K4 * τ₁ ^ 2) * τ₁ := by ring
          _ ≤ 1 * 1 := mul_le_mul hK4t hτ₁_1 hτ₁_pos.le zero_le_one
          _ = 1 := one_mul 1
      exact mul_le_of_le_one_left hfac_nn hK3
    let L_α : ((ℝ × ℝ × ℝ) × ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ × ℝ) ℝ))
    have hLα_norm : ‖L_α‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => ?_
      have h1 : ‖p.1.2.2‖ ≤ ‖p.1.2‖ := norm_snd_le p.1.2
      have h2 : ‖p.1.2‖ ≤ ‖p.1‖ := norm_snd_le p.1
      have h3 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
      simpa [L_α, one_mul] using (h1.trans h2).trans h3
    have hα_jc : JC 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q => q.1.2.2) 1 :=
      JC.clm hUd L_α hLα_norm fun q hq => by
        rw [hSΩ] at hq
        have hqα := hq.1.2.2
        have h2τ : 2 * τ₁ ^ 2 ≤ 1 := by nlinarith only [hτ₁_20, hτ₁_pos]
        simpa [L_α, Real.norm_eq_abs, abs_le] using ⟨by linarith only [hqα.1, h2τ], by linarith only [hqα.2, h2τ]⟩
    have hα_term := JC.mul hUd zero_le_one hfac_nn hα_jc (hcomp T.Θα T.jc_Θα)
    have hsum := (((h0b.add hUd h0m).add hUd h1b).add hUd h1m).add hUd hα_term
    have hB_eq : ((Nat.factorial 16 : ℝ) * pbM + (Nat.factorial 16 : ℝ) * pbM +
        (Nat.factorial 16 : ℝ) * pbM + (Nat.factorial 16 : ℝ) * pbM +
        2 ^ 16 * 1 * ((Nat.factorial 16 : ℝ) * pbM)) = B_Th := by
      dsimp only [B_Th]; ring
    have hθ_B : JC 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) θ B_Th :=
      (hsum.mono (le_of_eq hB_eq)).congr fun q _ => by simp only [θ, CfuTheta.Th]
    exact hθ_B.mono ((le_max_left B_Th C_H |>.trans (le_max_right 4 _)).trans (Φb_iter_ge 3 β))
  have hH_jcΦ : JCΦ 16 (Ioo (-δH) δH) fctH (Φb^[3] β) 0 :=
    hH_jc.mono ((le_max_right B_Th C_H |>.trans (le_max_right 4 _)).trans (Φb_iter_ge 3 β))
  have hHT : ∀ q ∈ S.Ω ×ˢ Yint, τ₁ ^ 2 * (q.2 * S.V q ^ 2) ∈ Ioo (-δH) δH := by
    intro q hq
    have hVb := S.V_bounds hq
    have hV2 : S.V q ^ 2 ≤ 36 / 25 := by nlinarith only [hVb.1, hVb.2]
    have hq2 : |q.2| < 3.6 := by rw [abs_lt]; constructor <;> linarith only [hq.2.1, hq.2.2]
    have hprod : |τ₁ ^ 2 * (q.2 * S.V q ^ 2)| < 6 * τ₁ ^ 2 := by
      have hqV : |q.2| * S.V q ^ 2 < 6 := by nlinarith only [abs_nonneg q.2, hq2, hV2, hVb.1]
      rw [abs_mul, abs_of_nonneg (sq_nonneg τ₁), abs_mul, abs_of_nonneg (sq_nonneg (S.V q))]
      exact (mul_lt_mul_of_pos_left hqV (pow_pos hτ₁_pos 2)).trans_eq (mul_comm _ 6)
    exact abs_lt.mp (hprod.trans (by linarith only [hτ1_δH]))
  have hβ8 : 8 ≤ Φb^[3] β := by
    have h1 := Φb_ge2 β
    have h2 : Φb^[1] β ≤ Φb^[3] β := Φb_iter_mono (by norm_num) β
    have h3 : max 1 β = β := max_eq_right (by linarith only [hβ4])
    simp only [Function.iterate_one] at h2
    linarith only [h1, h2, h3, hβ4]
  have hV_jc3 : JCΦ 16 (S.Ω ×ˢ Yint) S.V (Φb^[3] β) 0 := (S.V_jc hβ4).mono_m (by norm_num : 1 ≤ 3)
  have hJ_jc := J_coef_jc S.hΩ hβ8 hV_jc3 (fun _ hq => S.V_bounds hq)
    isOpen_Ioo hH_jcΦ (by rw [abs_of_nonneg (sq_nonneg τ₁)]; exact hτ₁_sq_le1) hHT
  have hJcd : ∀ p ∈ S.Ω, ContDiffOn ℝ 15 (fun s => Jfun S.V fctH (τ₁ ^ 2) (p, s)) Yint := fun p hp =>
    hJ_jc.2.2.2.1.comp (contDiffOn_const.prodMk contDiffOn_id) fun s hs => ⟨hp, hs⟩
  exact ⟨hτ₁_pos, hτ₁_3, hτ₁_sq_le1, hψ, hθ_jc, hH_jcΦ, hHT, hJcd, hJ_jc.2.2.2.1, hseg_pt, hSA_of⟩

/-- On `[0, Sw_ell c^{-1/6}]`, `J₁(ell₂, Y(u)) - J₀(ell₂, Y(u)) ∈ 𝒮^8(C c^{-17/12})` and
`(J₁(ell₂, Y(u)) - J₀(ell₂, Y(u))) - (J₁(ell₁, Y(u)) - J₀(ell₁, Y(u))) ∈ 𝒮^8(C c^{-5/4} (ell₂ - ell₁))`. -/
theorem win_J1_sub_J0_and_diff {K4 Sw_ell : ℝ} (hK4 : 1 ≤ K4) (_hSw : 1 ≤ Sw_ell) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 32 ^ 4 ≤ c₀ ∧ ∀ {ε c α ell1 ell2 : ℝ},
      (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      c ^ (-(1 / 4 : ℝ)) ≤ pbTauLim → K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 →
      |α| ≤ c ^ (-(1 / 2 : ℝ)) →
      0 ≤ ell1 → ell1 ≤ ell2 → ell2 ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) →
      let S := concreteBoxS K4 ε c
      let τ₁ := c ^ (-(1 / 4 : ℝ))
      FctSymClsOn (Icc 0 (fctUc c)) 8 8 (C * c ^ (-(17 / 12 : ℝ)))
        (fun u => ((Jfun S.V fctH (τ₁ ^ 2) ((ell2, 1, α), fctInnerY c u) -
          Jfun S.V fctH (τ₁ ^ 2) ((ell2, 0, α), fctInnerY c u) : ℝ) : ℂ)) ∧
      FctSymClsOn (Icc 0 (fctUc c)) 8 8 (C * c ^ (-(5 / 4 : ℝ)) * (ell2 - ell1))
        (fun u => (((Jfun S.V fctH (τ₁ ^ 2) ((ell2, 1, α), fctInnerY c u) -
          Jfun S.V fctH (τ₁ ^ 2) ((ell2, 0, α), fctInnerY c u)) -
          (Jfun S.V fctH (τ₁ ^ 2) ((ell1, 1, α), fctInnerY c u) -
          Jfun S.V fctH (τ₁ ^ 2) ((ell1, 0, α), fctInnerY c u)) : ℝ) : ℂ)) := by
  obtain ⟨δH, C_H, _, _, _, hH_jc, _⟩ := fctH_spec
  let β : ℝ := winDJBeta C_H
  have hβ4 : 4 ≤ β := le_max_left _ _
  have hβ0 : 0 ≤ β := by linarith only [hβ4]
  let M_A : ℝ := max 8 (2 * Sw_ell)
  have hMA8 : 8 ≤ M_A := le_max_left _ _
  let CJmax : ℝ := ∑ n ∈ Finset.range 9, CJ n (Φb^[3] β)
  let CJuMax : ℝ := ∑ n ∈ Finset.range 9, CJu n (Φb^[3] β)
  have hCJ_nn : ∀ n, 0 ≤ CJ n (Φb^[3] β) := fun n => CJ_nonneg n (Φb_iter_nonneg hβ0 3)
  have hCJu_nn : ∀ n, 0 ≤ CJu n (Φb^[3] β) := fun n => CJu_nonneg n (Φb_iter_nonneg hβ0 3)
  have hCJmax_nn : 0 ≤ CJmax := Finset.sum_nonneg fun n _ => hCJ_nn n
  have hCJuMax_nn : 0 ≤ CJuMax := Finset.sum_nonneg fun n _ => hCJu_nn n
  let C1 : ℝ := (Nat.factorial 8 : ℝ) * 16 ^ 8 * M_A ^ 4 * 100 ^ 8 * CJmax
  let C2 : ℝ := (Nat.factorial 8 : ℝ) * 16 ^ 8 * M_A ^ 4 * 100 ^ 8 * CJuMax
  let C_tot : ℝ := max C1 C2
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      (32 : ℝ) ^ 4 ≤ c ∧ (160000 : ℝ) ≤ c ∧ (30 * pbC0 + 1) ^ 2 ≤ c ∧
      (c ^ (-(1 / 4 : ℝ))) ^ 2 < δH / 6 ∧ Sw_ell * c ^ (-(1 / 6 : ℝ)) < 27 / 10 := by
    refine Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
      (Eventually.and (eventually_ge_atTop _) (Eventually.and ?_ ?_)))
    · have h0 : Tendsto (fun c : ℝ => (c ^ (-(1 / 4 : ℝ))) ^ 2) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).pow 2
      exact h0.eventually (Iio_mem_nhds (by positivity))
    · have h0 : Tendsto (fun c : ℝ => Sw_ell * c ^ (-(1 / 6 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).const_mul Sw_ell
      exact h0.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 27 / 10))
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  refine ⟨C_tot, max (32 ^ 4) c₀, by positivity, le_max_left _ _,
    fun {ε c α ell1 ell2} hε hc hτ_lim hK4t hα hell1 h12 hell2 => ?_⟩
  obtain ⟨hc32, hc160000, hcC0, hτ1_δH, hSw_lt⟩ := hc₀ c ((le_max_right _ _).trans hc)
  have hc100 : (100 : ℝ) ≤ c := le_trans (by norm_num) hc32
  have hc0 : 0 < c := by linarith only [hc100]
  set S := concreteBoxS K4 ε c
  set τ₁ := c ^ (-(1 / 4 : ℝ))
  let θ : (ℝ × ℝ × ℝ) × ℝ → ℝ := fun q => (concreteBoxT K4 ε c).Th τ₁ K4 q.1.2.2 q.2
  have D := win_dj_props hK4 hε hc160000 hcC0 hSw_lt hτ_lim hK4t hH_jc hτ1_δH hα
  have hell2_nn : 0 ≤ ell2 := hell1.trans h12
  have hp20_mem : (ell2, (0 : ℝ), α) ∈ S.Ω := by
    simpa using D.hseg_pt hell2_nn hell2 0 (left_mem_Icc.mpr zero_le_one)
  have hp21_mem : (ell2, (1 : ℝ), α) ∈ S.Ω := by
    have hsum : (ell2, (0 : ℝ), α) + (1 : ℝ) • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) = (ell2, (1 : ℝ), α) := by ext <;> simp
    rw [← hsum]; exact D.hseg_pt hell2_nn hell2 1 (right_mem_Icc.mpr zero_le_one)
  have hp10_mem : (ell1, (0 : ℝ), α) ∈ S.Ω := by
    simpa using D.hseg_pt hell1 (h12.trans hell2) 0 (left_mem_Icc.mpr zero_le_one)
  have hp11_mem : (ell1, (1 : ℝ), α) ∈ S.Ω := by
    have hsum : (ell1, (0 : ℝ), α) + (1 : ℝ) • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) = (ell1, (1 : ℝ), α) := by ext <;> simp
    rw [← hsum]; exact D.hseg_pt hell1 (h12.trans hell2) 1 (right_mem_Icc.mpr zero_le_one)
  -- Part 1: `(J1 - J0)(ell2)`
  have hpart1 : FctSymClsOn (Icc 0 (fctUc c)) 8 8 (C_tot * c ^ (-(17 / 12 : ℝ)))
      (fun u => ((Jfun S.V fctH (τ₁ ^ 2) ((ell2, 1, α), fctInnerY c u) -
        Jfun S.V fctH (τ₁ ^ 2) ((ell2, 0, α), fctInnerY c u) : ℝ) : ℂ)) := by
    have hJdiff_bd : ∀ k : ℕ, k ≤ 8 → ∀ y ∈ Yint, 0 ≤ y →
        |iteratedDeriv k (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell2, 1, α), s) -
          Jfun S.V fctH (τ₁ ^ 2) ((ell2, 0, α), s)) y| ≤
          (τ₁ ^ 3 * CJmax) * max y (M_A * c ^ (-(1 / 6 : ℝ))) ^ (4 - k) := by
      intro k hk y hy hy0
      have hdJ := S.dJ_jets hβ4 (0, 1, 0) θ (τ₁ ^ 3) D.hψ D.hθ_jc isOpen_Ioo D.hH_jcΦ
        (by rw [abs_of_nonneg (sq_nonneg τ₁)]; exact D.hτ₁_sq_le1) D.hHT
        (D.hseg_pt hell2_nn hell2)
        (fun t ht => (D.hSA_of hell2_nn hell2 t ht).1)
        (fun t ht => (D.hSA_of hell2_nn hell2 t ht).2) hy hy0 (by omega : k ≤ 13)
      have hsum : (ell2, (0 : ℝ), α) + ((0 : ℝ), (1 : ℝ), (0 : ℝ)) = (ell2, (1 : ℝ), α) := by ext <;> simp
      rw [hsum] at hdJ
      have hk15 : ((k : ℕ∞) : WithTop ℕ∞) ≤ 15 := by
        rw [show (15 : WithTop ℕ∞) = (((15 : ℕ) : ℕ∞) : WithTop ℕ∞) by rfl]; exact_mod_cast (by omega : k ≤ 15)
      have hcd1 : ContDiffAt ℝ k (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell2, 1, α), s)) y :=
        ((D.hJcd (ell2, 1, α) hp21_mem).contDiffAt (isOpen_Ioo.mem_nhds hy)).of_le (m := (k : ℕ∞)) hk15
      have hcd0 : ContDiffAt ℝ k (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell2, 0, α), s)) y :=
        ((D.hJcd (ell2, 0, α) hp20_mem).contDiffAt (isOpen_Ioo.mem_nhds hy)).of_le (m := (k : ℕ∞)) hk15
      rw [show (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell2, 1, α), s) -
            Jfun S.V fctH (τ₁ ^ 2) ((ell2, 0, α), s)) =
          (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell2, 1, α), s)) -
            (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell2, 0, α), s)) from rfl,
        iteratedDeriv_sub hcd1 hcd0]
      have hCJ_le : CJ k (Φb^[3] β) ≤ CJmax :=
        Finset.single_le_sum (fun m _ => hCJ_nn m) (Finset.mem_range.mpr (by omega))
      calc |iteratedDeriv k (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell2, 1, α), s)) y -
              iteratedDeriv k (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell2, 0, α), s)) y|
          ≤ |τ₁ ^ 3| * CJ k (Φb^[3] β) * max y (M_A * c ^ (-(1 / 6 : ℝ))) ^ (4 - k) := hdJ
        _ = τ₁ ^ 3 * CJ k (Φb^[3] β) * max y (M_A * c ^ (-(1 / 6 : ℝ))) ^ (4 - k) := by
            rw [abs_of_pos (pow_pos D.hτ₁_pos 3)]
        _ ≤ (τ₁ ^ 3 * CJmax) * max y (M_A * c ^ (-(1 / 6 : ℝ))) ^ (4 - k) := by gcongr
    have hJdiff_cd : ContDiffOn ℝ 8 (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell2, 1, α), s) -
        Jfun S.V fctH (τ₁ ^ 2) ((ell2, 0, α), s)) Yint :=
      ((D.hJcd (ell2, 1, α) hp21_mem).of_le (by norm_num)).sub ((D.hJcd (ell2, 0, α) hp20_mem).of_le (by norm_num))
    have hcomp := win_dJ_comp_Y_sym (m := 4) hc100 (mul_nonneg (pow_nonneg D.hτ₁_pos.le 3) hCJmax_nn)
      hMA8 (by norm_num) hJdiff_cd hJdiff_bd
    have hB_le : (Nat.factorial 8 : ℝ) * 16 ^ 8 * M_A ^ 4 * 100 ^ 8 * (τ₁ ^ 3 * CJmax) * c ^ (-((4 : ℝ) / 6)) ≤
        C_tot * c ^ (-(17 / 12 : ℝ)) := by
      have hc_pow : c ^ (-(3 / 4 : ℝ)) * c ^ (-((4 : ℝ) / 6)) = c ^ (-(17 / 12 : ℝ)) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      have h1 : (Nat.factorial 8 : ℝ) * 16 ^ 8 * M_A ^ 4 * 100 ^ 8 * (τ₁ ^ 3 * CJmax) * c ^ (-((4 : ℝ) / 6)) =
          C1 * c ^ (-(17 / 12 : ℝ)) := by
        dsimp only [C1]; rw [D.hτ₁_3]
        calc (Nat.factorial 8 : ℝ) * 16 ^ 8 * M_A ^ 4 * 100 ^ 8 * (c ^ (-(3 / 4 : ℝ)) * CJmax) * c ^ (-((4 : ℝ) / 6))
            = (Nat.factorial 8 : ℝ) * 16 ^ 8 * M_A ^ 4 * 100 ^ 8 * CJmax * (c ^ (-(3 / 4 : ℝ)) * c ^ (-((4 : ℝ) / 6))) := by ring
          _ = (Nat.factorial 8 : ℝ) * 16 ^ 8 * M_A ^ 4 * 100 ^ 8 * CJmax * c ^ (-(17 / 12 : ℝ)) := by rw [hc_pow]
      rw [h1]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    exact hcomp.mono_B Icc_subset_Ici_self hB_le
  -- Part 2: `(J1(ell2) - J0(ell2)) - (J1(ell1) - J0(ell1))`
  have hpart2 : FctSymClsOn (Icc 0 (fctUc c)) 8 8 (C_tot * c ^ (-(5 / 4 : ℝ)) * (ell2 - ell1))
      (fun u => (((Jfun S.V fctH (τ₁ ^ 2) ((ell2, 1, α), fctInnerY c u) -
        Jfun S.V fctH (τ₁ ^ 2) ((ell2, 0, α), fctInnerY c u)) -
        (Jfun S.V fctH (τ₁ ^ 2) ((ell1, 1, α), fctInnerY c u) -
        Jfun S.V fctH (τ₁ ^ 2) ((ell1, 0, α), fctInnerY c u)) : ℝ) : ℂ)) := by
    let v : ℝ × ℝ × ℝ := (ell2 - ell1, 0, 0)
    let p10 : ℝ × ℝ × ℝ := (ell1, 0, α)
    let p11 : ℝ × ℝ × ℝ := (ell1, 1, α)
    have hO_S : IsOpen (S.Ω ×ˢ Yint) := S.hΩ.prod isOpen_Ioo
    have hu_n : ‖((1 : ℝ), (0 : ℝ), (0 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]
    have hJdiff_bd : ∀ k : ℕ, k ≤ 8 → ∀ y ∈ Yint, 0 ≤ y →
        |iteratedDeriv k (fun s => (Jfun S.V fctH (τ₁ ^ 2) ((ell2, 1, α), s) -
          Jfun S.V fctH (τ₁ ^ 2) ((ell2, 0, α), s)) -
          (Jfun S.V fctH (τ₁ ^ 2) ((ell1, 1, α), s) -
          Jfun S.V fctH (τ₁ ^ 2) ((ell1, 0, α), s))) y| ≤
          ((ell2 - ell1) * τ₁ ^ 3 * CJuMax) * max y (M_A * c ^ (-(1 / 6 : ℝ))) ^ (3 - k) := by
      intro k hk y hy hy0
      have hk15 : ((k : ℕ∞) : WithTop ℕ∞) ≤ 15 := by
        rw [show (15 : WithTop ℕ∞) = (((15 : ℕ) : ℕ∞) : WithTop ℕ∞) by rfl]; exact_mod_cast (by omega : k ≤ 15)
      have hcd21 : ContDiffAt ℝ k (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell2, 1, α), s)) y :=
        ((D.hJcd (ell2, 1, α) hp21_mem).contDiffAt (isOpen_Ioo.mem_nhds hy)).of_le (m := (k : ℕ∞)) hk15
      have hcd20 : ContDiffAt ℝ k (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell2, 0, α), s)) y :=
        ((D.hJcd (ell2, 0, α) hp20_mem).contDiffAt (isOpen_Ioo.mem_nhds hy)).of_le (m := (k : ℕ∞)) hk15
      have hcd11 : ContDiffAt ℝ k (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell1, 1, α), s)) y :=
        ((D.hJcd (ell1, 1, α) hp11_mem).contDiffAt (isOpen_Ioo.mem_nhds hy)).of_le (m := (k : ℕ∞)) hk15
      have hcd10 : ContDiffAt ℝ k (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell1, 0, α), s)) y :=
        ((D.hJcd (ell1, 0, α) hp10_mem).contDiffAt (isOpen_Ioo.mem_nhds hy)).of_le (m := (k : ℕ∞)) hk15
      let f2 : ℝ → ℝ := fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell2, 1, α), s) -
        Jfun S.V fctH (τ₁ ^ 2) ((ell2, 0, α), s)
      let f1 : ℝ → ℝ := fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell1, 1, α), s) -
        Jfun S.V fctH (τ₁ ^ 2) ((ell1, 0, α), s)
      change |iteratedDeriv k (fun s => f2 s - f1 s) y| ≤ _
      rw [show (fun s => f2 s - f1 s) = f2 - f1 from rfl, iteratedDeriv_sub (hcd21.sub hcd20) (hcd11.sub hcd10)]
      rw [show (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell2, 1, α), s) - Jfun S.V fctH (τ₁ ^ 2) ((ell2, 0, α), s)) =
          (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell2, 1, α), s)) - (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell2, 0, α), s)) from rfl,
        show (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell1, 1, α), s) - Jfun S.V fctH (τ₁ ^ 2) ((ell1, 0, α), s)) =
          (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell1, 1, α), s)) - (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell1, 0, α), s)) from rfl,
        iteratedDeriv_sub hcd21 hcd20, iteratedDeriv_sub hcd11 hcd10]
      let φ : ℝ → ℝ := fun t =>
        iteratedDeriv k (fun s => Jfun S.V fctH (τ₁ ^ 2) (p11 + t • v, s)) y -
        iteratedDeriv k (fun s => Jfun S.V fctH (τ₁ ^ 2) (p10 + t • v, s)) y
      have hJk2 : ContDiffOn ℝ (k + 2) (Jfun S.V fctH (τ₁ ^ 2)) (S.Ω ×ˢ Yint) :=
        D.hJ_cd15.of_le (by exact_mod_cast (by omega : k + 2 ≤ 15))
      have hell_t : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ell1 + t * (ell2 - ell1) ∧
          ell1 + t * (ell2 - ell1) ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) := fun t ht =>
        ⟨by nlinarith only [hell1, h12, ht.1], by nlinarith only [h12, hell2, ht.1, ht.2]⟩
      have hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt φ
          (iteratedDeriv k (fun s => fderiv ℝ (Jfun S.V fctH (τ₁ ^ 2)) (p11 + t • v, s) (v, 0)) y -
           iteratedDeriv k (fun s => fderiv ℝ (Jfun S.V fctH (τ₁ ^ 2)) (p10 + t • v, s) (v, 0)) y)
          (Icc (0 : ℝ) 1) t := fun t ht => by
        obtain ⟨ht0, htu⟩ := hell_t t ht
        have hp1t_eq : p11 + t • v = (ell1 + t * (ell2 - ell1), 1, α) := by ext <;> simp [p11, v]
        have hp0t_eq : p10 + t • v = (ell1 + t * (ell2 - ell1), 0, α) := by ext <;> simp [p10, v]
        have hm1 : p11 + t • v ∈ S.Ω := by
          rw [hp1t_eq]
          have hsum : (ell1 + t * (ell2 - ell1), (0 : ℝ), α) + (1 : ℝ) • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) =
              (ell1 + t * (ell2 - ell1), (1 : ℝ), α) := by ext <;> simp
          rw [← hsum]; exact D.hseg_pt ht0 htu 1 (right_mem_Icc.mpr zero_le_one)
        have hm0 : p10 + t • v ∈ S.Ω := by
          rw [hp0t_eq]
          simpa using D.hseg_pt ht0 htu 0 (left_mem_Icc.mpr zero_le_one)
        exact ((hasDerivAt_iteratedDeriv_path hO_S p11 v y k _ hJk2 t ⟨hm1, hy⟩).sub
          (hasDerivAt_iteratedDeriv_path hO_S p10 v y k _ hJk2 t ⟨hm0, hy⟩)).hasDerivWithinAt
      have hbd : ∀ t ∈ Icc (0 : ℝ) 1,
          ‖iteratedDeriv k (fun s => fderiv ℝ (Jfun S.V fctH (τ₁ ^ 2)) (p11 + t • v, s) (v, 0)) y -
           iteratedDeriv k (fun s => fderiv ℝ (Jfun S.V fctH (τ₁ ^ 2)) (p10 + t • v, s) (v, 0)) y‖ ≤
            ((ell2 - ell1) * τ₁ ^ 3 * CJuMax) * max y (M_A * c ^ (-(1 / 6 : ℝ))) ^ (3 - k) := fun t ht => by
        obtain ⟨ht0, htu⟩ := hell_t t ht
        let p_t : ℝ × ℝ × ℝ := (ell1 + t * (ell2 - ell1), 0, α)
        have hp1t_eq : p11 + t • v = p_t + ((0 : ℝ), (1 : ℝ), (0 : ℝ)) := by ext <;> simp [p11, v, p_t]
        have hp0t_eq : p10 + t • v = p_t := by ext <;> simp [p10, v, p_t]
        have hv_eq : (v, (0 : ℝ)) = (ell2 - ell1) • (((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0 : ℝ)) := by
          ext <;> simp [v]
        have hfn1 : (fun s => fderiv ℝ (Jfun S.V fctH (τ₁ ^ 2)) (p11 + t • v, s) (v, 0)) =
            fun s => (ell2 - ell1) * fderiv ℝ (Jfun S.V fctH (τ₁ ^ 2)) (p_t + (0, 1, 0), s) ((1, 0, 0), 0) := by
          ext s; rw [hp1t_eq, hv_eq, map_smul, smul_eq_mul]
        have hfn0 : (fun s => fderiv ℝ (Jfun S.V fctH (τ₁ ^ 2)) (p10 + t • v, s) (v, 0)) =
            fun s => (ell2 - ell1) * fderiv ℝ (Jfun S.V fctH (τ₁ ^ 2)) (p_t, s) ((1, 0, 0), 0) := by
          ext s; rw [hp0t_eq, hv_eq, map_smul, smul_eq_mul]
        rw [hfn1, hfn0, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field, ← mul_sub,
          Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr h12)]
        have hdJu := S.dJ_jets_u hβ4 (0, 1, 0) (1, 0, 0) hu_n θ (τ₁ ^ 3) D.hψ D.hθ_jc
          isOpen_Ioo D.hH_jcΦ (by rw [abs_of_nonneg (sq_nonneg τ₁)]; exact D.hτ₁_sq_le1) D.hHT
          (D.hseg_pt ht0 htu) (fun s hs => (D.hSA_of ht0 htu s hs).1)
          (fun s hs => (D.hSA_of ht0 htu s hs).2) hy hy0 (by omega : k ≤ 12)
        have hCJu_le : CJu k (Φb^[3] β) ≤ CJuMax :=
          Finset.single_le_sum (fun m _ => hCJu_nn m) (Finset.mem_range.mpr (by omega))
        calc (ell2 - ell1) * |iteratedDeriv k (fun s => fderiv ℝ (Jfun S.V fctH (τ₁ ^ 2)) (p_t + (0, 1, 0), s) ((1, 0, 0), 0)) y -
              iteratedDeriv k (fun s => fderiv ℝ (Jfun S.V fctH (τ₁ ^ 2)) (p_t, s) ((1, 0, 0), 0)) y|
            ≤ (ell2 - ell1) * (|τ₁ ^ 3| * CJu k (Φb^[3] β) * max y (M_A * c ^ (-(1 / 6 : ℝ))) ^ (3 - k)) := by gcongr
          _ = (ell2 - ell1) * (τ₁ ^ 3 * CJu k (Φb^[3] β) * max y (M_A * c ^ (-(1 / 6 : ℝ))) ^ (3 - k)) := by
              rw [abs_of_pos (pow_pos D.hτ₁_pos 3)]
          _ ≤ (ell2 - ell1) * (τ₁ ^ 3 * CJuMax * max y (M_A * c ^ (-(1 / 6 : ℝ))) ^ (3 - k)) := by gcongr
          _ = ((ell2 - ell1) * τ₁ ^ 3 * CJuMax) * max y (M_A * c ^ (-(1 / 6 : ℝ))) ^ (3 - k) := by ring
      have hmv := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd
        (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
      have hp11_eq : p11 + (1 : ℝ) • v = (ell2, 1, α) := by ext <;> simp [p11, v]
      have hp10_eq : p10 + (1 : ℝ) • v = (ell2, 0, α) := by ext <;> simp [p10, v]
      have hφ1 : φ 1 = iteratedDeriv k (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell2, 1, α), s)) y -
          iteratedDeriv k (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell2, 0, α), s)) y := by
        dsimp only [φ]; rw [hp11_eq, hp10_eq]
      have hφ0 : φ 0 = iteratedDeriv k (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell1, 1, α), s)) y -
          iteratedDeriv k (fun s => Jfun S.V fctH (τ₁ ^ 2) ((ell1, 0, α), s)) y := by
        dsimp only [φ]; rw [zero_smul, add_zero, add_zero]
      simpa [Real.norm_eq_abs, hφ1, hφ0, sub_zero, mul_one] using hmv
    have hJdiff_cd : ContDiffOn ℝ 8 (fun s => (Jfun S.V fctH (τ₁ ^ 2) ((ell2, 1, α), s) -
        Jfun S.V fctH (τ₁ ^ 2) ((ell2, 0, α), s)) -
        (Jfun S.V fctH (τ₁ ^ 2) ((ell1, 1, α), s) -
        Jfun S.V fctH (τ₁ ^ 2) ((ell1, 0, α), s))) Yint :=
      (((D.hJcd (ell2, 1, α) hp21_mem).of_le (by norm_num)).sub
        ((D.hJcd (ell2, 0, α) hp20_mem).of_le (by norm_num))).sub
      (((D.hJcd (ell1, 1, α) hp11_mem).of_le (by norm_num)).sub
        ((D.hJcd (ell1, 0, α) hp10_mem).of_le (by norm_num)))
    have hcomp := win_dJ_comp_Y_sym (m := 3) hc100
      (mul_nonneg (mul_nonneg (sub_nonneg.mpr h12) (pow_nonneg D.hτ₁_pos.le 3)) hCJuMax_nn)
      hMA8 (by norm_num) hJdiff_cd hJdiff_bd
    have hB_le : (Nat.factorial 8 : ℝ) * 16 ^ 8 * M_A ^ 4 * 100 ^ 8 * ((ell2 - ell1) * τ₁ ^ 3 * CJuMax) * c ^ (-((3 : ℝ) / 6)) ≤
        C_tot * c ^ (-(5 / 4 : ℝ)) * (ell2 - ell1) := by
      have hc_pow : c ^ (-(3 / 4 : ℝ)) * c ^ (-((3 : ℝ) / 6)) = c ^ (-(5 / 4 : ℝ)) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      have h1 : (Nat.factorial 8 : ℝ) * 16 ^ 8 * M_A ^ 4 * 100 ^ 8 * ((ell2 - ell1) * τ₁ ^ 3 * CJuMax) * c ^ (-((3 : ℝ) / 6)) =
          C2 * c ^ (-(5 / 4 : ℝ)) * (ell2 - ell1) := by
        dsimp only [C2]; rw [D.hτ₁_3]
        calc (Nat.factorial 8 : ℝ) * 16 ^ 8 * M_A ^ 4 * 100 ^ 8 * ((ell2 - ell1) * c ^ (-(3 / 4 : ℝ)) * CJuMax) * c ^ (-((3 : ℝ) / 6))
            = (Nat.factorial 8 : ℝ) * 16 ^ 8 * M_A ^ 4 * 100 ^ 8 * CJuMax * (c ^ (-(3 / 4 : ℝ)) * c ^ (-((3 : ℝ) / 6))) * (ell2 - ell1) := by ring
          _ = (Nat.factorial 8 : ℝ) * 16 ^ 8 * M_A ^ 4 * 100 ^ 8 * CJuMax * c ^ (-(5 / 4 : ℝ)) * (ell2 - ell1) := by rw [hc_pow]
      rw [h1]
      have hnn : 0 ≤ c ^ (-(5 / 4 : ℝ)) * (ell2 - ell1) := mul_nonneg (by positivity) (sub_nonneg.mpr h12)
      calc C2 * c ^ (-(5 / 4 : ℝ)) * (ell2 - ell1)
          = C2 * (c ^ (-(5 / 4 : ℝ)) * (ell2 - ell1)) := by ring
        _ ≤ C_tot * (c ^ (-(5 / 4 : ℝ)) * (ell2 - ell1)) := mul_le_mul_of_nonneg_right (le_max_right _ _) hnn
        _ = C_tot * c ^ (-(5 / 4 : ℝ)) * (ell2 - ell1) := by ring
    exact hcomp.mono_B Icc_subset_Ici_self hB_le
  exact ⟨hpart1, hpart2⟩

/-- info: 'FormalResearch.SignUncertainty.win_J1_sub_J0_and_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_J1_sub_J0_and_diff

end FormalResearch.SignUncertainty
