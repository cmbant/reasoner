module

public import FormalResearch.SignUncertainty.HbConstructionSeed
public import FormalResearch.SignUncertainty.CeHbSeedMass
public import FormalResearch.SignUncertainty.GenRationalO6Family
public import FormalResearch.SignUncertainty.CeLiftWindowNeg
public import FormalResearch.SignUncertainty.MellinLiftGeneral
public import FormalResearch.SignUncertainty.HbMultilevelDefs

/-!
# Proof of `HbConstruction` (`u1co:O9p`, all Hermite–Biehler levels `m₀ ≥ 1`)

Proves `hbConstruction_proved : ∀ D : ShellHBData, HbConstruction D`:
for every `D : ShellHBData` (covering both odd and even `D.S.card`), `κ ≥ 4`, and `R_off ≥ 0`,
there exist `K > 0` and `c₁ ≥ 2` such that for all real `c ≥ c₁` and either eigenvalue `σ = ±1`,
there exists `f ∈ 𝒜_c^σ` with `σ f(0) < 0`, `f > 0` on `[T_j - R_off, T_j + R_off]` for every
`t_j ∈ D.S \ {D.tm}`, and `f > 0` on `[c/π² + (|D.tm|/β₁) c^{1/3} + K, ∞)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

private noncomputable def hbConBasis (D : ShellHBData) (b : ℝ) : Fin 3 → ℂ → ℂ :=
  ![D.G, dslope (fun z => -D.G z) (D.tm : ℂ), airySbC b]

private noncomputable def hbConAlpha (C_G γ₁ γ₂ : ℝ) : Fin 3 → ℝ → ℝ → ℝ := fun i K c =>
  match i with
  | ⟨0, _⟩ => C_G
  | ⟨1, _⟩ => -(C_G * (K * liftEps c * γ₁))
  | ⟨2, _⟩ => C_G * (K * liftEps c * γ₂)

private lemma hbCon_dual_est {ι : Type*} (s : Finset ι) (B : ι → ℂ → ℂ) (b₀₀ b₁₁ : ι → ℝ)
    (hB : ∀ i ∈ s, HasGenRationalAiryCoeffs (B i) (b₀₀ i) (b₁₁ i))
    (α : ι → ℝ → ℝ → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hα : ∀ i ∈ s, ∀ K c : ℝ, 1 ≤ K → 2000 ≤ c → K * liftEps c ≤ 2 → |α i K c| ≤ R)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    O6DualEst 4 (fun K c u =>
      if 1 ≤ K ∧ 2000 ≤ c ∧ K * liftEps c ≤ 2 then
        σ * ∑ i ∈ s, α i K c * (B i (u : ℂ)).re
      else 0) := by
  classical
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  let D_fam : ℝ → ℝ → ℝ → ℝ := fun K c u =>
    if 1 ≤ K ∧ 2000 ≤ c ∧ K * liftEps c ≤ 2 then
      σ * ∑ i ∈ s, α i K c * (B i (u : ℂ)).re
    else 0
  have hZ_rhp_i : ∀ i ∈ s, ∃ Ci > 0, ∀ w : ℂ, 0 ≤ w.re →
      ‖airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) ((ceCs : ℂ) * w)‖ ≤
        Ci * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) :=
    fun i hi => (hasU2_of_genRational (hB i hi)).rhp
  choose CZi hCZi_pos hCZi_bd using hZ_rhp_i
  let CD_fam : ℝ := R * (∑ i ∈ s, if hi : i ∈ s then CZi i hi else 0) + 1
  have hCD_fam : 0 ≤ CD_fam := by
    have : 0 ≤ ∑ i ∈ s, if hi : i ∈ s then CZi i hi else 0 := by
      refine Finset.sum_nonneg fun i hi => ?_
      split_ifs; exact (hCZi_pos i hi).le
    positivity
  have hbd_fam : ∀ {K c : ℝ} {w : ℂ}, 0 ≤ w.re →
      ‖airyTwistedLaplaceC (D_fam K c) ((ceCs : ℂ) * w)‖ ≤ CD_fam * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
    intro K c w hw
    have hT : 0 ≤ ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    by_cases hcond : 1 ≤ K ∧ 2000 ≤ c ∧ K * liftEps c ≤ 2
    · have hfn : D_fam K c = fun (u : ℝ) => ∑ i ∈ s, (σ * α i K c) * (B i (u : ℂ)).re := by
        ext u; simp [D_fam, hcond, Finset.mul_sum, mul_assoc]
      rw [hfn, airyTwistedLaplaceC_finset_sum s B b₀₀ b₁₁ hB (fun i => σ * α i K c) hw]
      calc ‖∑ i ∈ s, ((σ * α i K c : ℝ) : ℂ) *
              airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) ((ceCs : ℂ) * w)‖
          ≤ ∑ i ∈ s, ‖((σ * α i K c : ℝ) : ℂ) *
              airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) ((ceCs : ℂ) * w)‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ s, R * ((if hi : i ∈ s then CZi i hi else 0) * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) := by
            refine Finset.sum_le_sum fun i hi => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, hσabs, one_mul]
            split_ifs
            exact mul_le_mul (hα i hi K c hcond.1 hcond.2.1 hcond.2.2)
              (hCZi_bd i hi w hw) (norm_nonneg _) hR
        _ = (R * ∑ i ∈ s, if hi : i ∈ s then CZi i hi else 0) * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
            simp_rw [← mul_assoc, ← Finset.sum_mul, ← Finset.mul_sum]
        _ ≤ CD_fam * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right (by dsimp [CD_fam]; linarith) hT
    · have hfn : D_fam K c = fun _ => 0 := by ext u; simp [D_fam, hcond]
      rw [hfn, show airyTwistedLaplaceC (fun _ : ℝ => (0 : ℝ)) ((ceCs : ℂ) * w) = 0 by
        unfold airyTwistedLaplaceC; simp, norm_zero]
      exact mul_nonneg hCD_fam hT
  have hdiff_fam : ∀ {K c : ℝ},
      DifferentiableOn ℂ (airyTwistedLaplaceC (D_fam K c)) {y : ℂ | 0 < y.re} := by
    intro K c
    by_cases hcond : 1 ≤ K ∧ 2000 ≤ c ∧ K * liftEps c ≤ 2
    · have hfn : D_fam K c = fun (u : ℝ) => ∑ i ∈ s, (σ * α i K c) * (B i (u : ℂ)).re := by
        ext u; simp [D_fam, hcond, Finset.mul_sum, mul_assoc]
      rw [hfn]; exact (hasU2_finset_sum s B b₀₀ b₁₁ hB (fun i => σ * α i K c)).differentiable
    · have hfn : D_fam K c = fun _ => 0 := by ext u; simp [D_fam, hcond]
      rw [hfn, show (fun _ : ℝ => (0 : ℝ)) = airySeedU2 0 0 0 from funext fun _ => by simp [airySeedU2]]
      exact (hasU2_airySeedU2 0 0 0).differentiable
  constructor
  · obtain ⟨C3, hC3, h3⟩ := iDual_bound_e3 (m := 4) (by norm_num) hCD_fam
    exact ⟨C3, hC3, fun {K c ξ} hδ hc hξ hS => h3 hdiff_fam hbd_fam hδ hc hξ hS⟩
  · intro Sw
    obtain ⟨C5, hC5, h5⟩ := dual_bound_window 4 (by norm_num) (max CD_fam 1) (by positivity)
    refine ⟨C5, hC5, fun {K c ξ} hK hc hξ _ => ?_⟩
    have hc0 : 0 < c := by linarith
    have hδ : 0 ≤ ceBeta1 * K * liftEps c / 2 := by
      have := ceBeta1_pos; have := liftEps_pos hc0; positivity
    have hbd1 : ∀ {w : ℂ}, 0 ≤ w.re →
        ‖airyTwistedLaplaceC (D_fam K c) ((ceCs : ℂ) * w)‖ ≤ max CD_fam 1 * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) :=
      fun {w} hw => (hbd_fam hw).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (norm_nonneg _) _))
    refine (h5 (D := D_fam K c) hbd1 hδ hc0 hξ).trans ?_
    have hinv : ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ ≤ 1 := by
      refine inv_le_one_of_one_le₀ (one_le_pow₀ ?_)
      have : 0 ≤ ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ) := mul_nonneg hδ (Real.rpow_nonneg hc0.le _)
      linarith
    have hξ1 : (2 * Real.pi * ξ)⁻¹ ≤ ξ⁻¹ := by
      rw [mul_inv]
      have : (2 * Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
      have hξi : 0 ≤ ξ⁻¹ := inv_nonneg.mpr hξ.le
      nlinarith
    have hrest : C5 * ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ * c ^ (-(1 / 2 : ℝ)) ≤
        C5 * c ^ (-(1 / 2 : ℝ)) := by
      have : 0 ≤ C5 * c ^ (-(1 / 2 : ℝ)) := by positivity
      calc _ ≤ C5 * 1 * c ^ (-(1 / 2 : ℝ)) := by gcongr
        _ = _ := by ring
    calc (2 * Real.pi * ξ)⁻¹ * (C5 * ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ *
          c ^ (-(1 / 2 : ℝ)))
        ≤ ξ⁻¹ * (C5 * c ^ (-(1 / 2 : ℝ))) := mul_le_mul hξ1 hrest (by positivity) (inv_nonneg.mpr hξ.le)
      _ = C5 * ξ⁻¹ * c ^ (-(1 / 2 : ℝ)) := by ring

private lemma hbCon_tail_decay {ι : Type*} (s : Finset ι) (B : ι → ℂ → ℂ) (b₀₀ b₁₁ : ι → ℝ)
    (hB : ∀ i ∈ s, HasGenRationalAiryCoeffs (B i) (b₀₀ i) (b₁₁ i))
    (a : ι → ℝ) {δ₀ c : ℝ} (hδ0 : 0 ≤ δ₀) (hδ2 : δ₀ ≤ 2) (hc8 : 8 ≤ c)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    let F : ℝ → ℝ := fun u => ∑ i ∈ s, a i * (B i (u : ℂ)).re
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∀ ξ : ℝ, ξ₀ ≤ ξ →
      ‖iMain F δ₀ 4 c ξ + (σ : ℂ) * iDual F δ₀ 4 c ξ‖ ≤
        C * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by
  classical
  have hc0 : 0 < c := by linarith
  have hσ1 : ‖(σ : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; rcases hσ with rfl | rfl <;> simp
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, le_rfl, 1, one_pos, fun ξ hξ => ?_⟩
      have hF0 : (fun u : ℝ => ∑ i ∈ (∅ : Finset ι), a i * (B i (u : ℂ)).re) = fun _ => 0 := rfl
      have hm0 : iMain (fun _ : ℝ => (0 : ℝ)) δ₀ 4 c ξ = 0 := by
        simp [iMain, iMainIntegrand, liftSymbol, airyTwistedLaplaceC]
      have hd0 : iDual (fun _ : ℝ => (0 : ℝ)) δ₀ 4 c ξ = 0 := by
        simp [iDual, iDualIntegrand, liftSymbol, airyTwistedLaplaceC]
      rw [hF0, hm0, hd0, mul_zero, add_zero, norm_zero]
      have hlog0 : 0 ≤ Real.log (Real.pi ^ 2 * ξ) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
      positivity
  | @insert j t hjt ih =>
      obtain ⟨Ct, hCt0, ξt, hξt0, ht_bd⟩ := ih (fun i hi => hB i (Finset.mem_insert_of_mem hi))
      have hBj := hB j (Finset.mem_insert_self j t)
      have htj := convTailData_of_genRational hBj (by norm_num : 3 ≤ 4) ⟨hδ0, hδ2⟩ hc8
      obtain ⟨Cm, hCm0, ξm, hξm0, hm_bd⟩ := htj.main
      obtain ⟨Cd, hCd0, ξd, hξd0, hd_bd⟩ := htj.dual
      have hUj : HasU2 (fun u => a j * (B j (u : ℂ)).re) := (hasU2_of_genRational hBj).smul _
      have hUt : HasU2 (fun u => ∑ i ∈ t, a i * (B i (u : ℂ)).re) :=
        hasU2_finset_sum t B b₀₀ b₁₁ (fun i hi => hB i (Finset.mem_insert_of_mem hi)) a
      refine ⟨Ct + |a j| * (Cm + Cd), by positivity, max ξt (max ξm ξd),
        lt_max_of_lt_left hξt0, fun ξ hξ => ?_⟩
      have hξ0 : 0 < ξ := lt_of_lt_of_le (lt_max_of_lt_left hξt0) hξ
      have hfn : (fun u : ℝ => ∑ i ∈ insert j t, a i * (B i (u : ℂ)).re) =
          fun u : ℝ => a j * (B j (u : ℂ)).re + ∑ i ∈ t, a i * (B i (u : ℂ)).re :=
        funext fun u => Finset.sum_insert hjt
      rw [hfn, iMain_add hUj hUt hδ0 4 hc0 hξ0, iDual_add hUj hUt hδ0 4 hc0 hξ0,
        iMain_const_mul, iDual_const_mul]
      have hterm_t := ht_bd ξ ((le_max_left _ _).trans hξ)
      have hmj := hm_bd ξ ((le_max_left _ _).trans ((le_max_right _ _).trans hξ))
      have hdj := hd_bd ξ ((le_max_right _ _).trans ((le_max_right _ _).trans hξ))
      have hdj' : ‖(σ : ℂ) * iDual (fun u => (B j (u : ℂ)).re) δ₀ 4 c ξ‖ ≤
          Cd * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by
        rw [norm_mul, hσ1, one_mul]; exact hdj
      have hbj : ‖(a j : ℂ) * (iMain (fun u => (B j (u : ℂ)).re) δ₀ 4 c ξ +
            (σ : ℂ) * iDual (fun u => (B j (u : ℂ)).re) δ₀ 4 c ξ)‖ ≤
          |a j| * (Cm + Cd) * (ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
        exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ((add_le_add hmj hdj').trans_eq (by ring)))
          (abs_nonneg _)
      calc ‖_‖ = ‖((a j : ℂ) * (iMain (fun u => (B j (u : ℂ)).re) δ₀ 4 c ξ +
              (σ : ℂ) * iDual (fun u => (B j (u : ℂ)).re) δ₀ 4 c ξ)) +
            (iMain (fun u => ∑ i ∈ t, a i * (B i (u : ℂ)).re) δ₀ 4 c ξ +
              (σ : ℂ) * iDual (fun u => ∑ i ∈ t, a i * (B i (u : ℂ)).re) δ₀ 4 c ξ)‖ := by
            congr 1; ring
        _ ≤ _ := norm_add_le _ _
        _ ≤ |a j| * (Cm + Cd) * (ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) +
              Ct * (ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) :=
            add_le_add hbj (hterm_t.trans_eq (by ring))
        _ = (Ct + |a j| * (Cm + Cd)) * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by ring

private lemma hbCon_window_pos
    {R_off B_t C_drift K_seed C_G δ₀ Sw C_m C_d η_main C_err B_shell c t x : ℝ}
    {F D_clamp f F_node : ℝ → ℝ}
    (hR : 0 ≤ R_off) (hc0 : 0 < c) (hc2 : 2 ≤ c) (hcB6 : B_shell ^ 6 ≤ c) (hB_sh : 0 ≤ B_shell)
    (hBt : 0 ≤ B_t) (ht_bd : |t| ≤ B_t) (hx_off : |x - hankelLevel t c 0| ≤ R_off)
    (hCd_def : C_drift = ceBeta1 * R_off + 2 * ceBeta1 * Real.pi ^ 2 * (B_t / ceBeta1 + R_off) ^ 2)
    (hB_sh1 : 2 * Real.pi ^ 2 * (B_t / ceBeta1 + R_off) + 1 ≤ B_shell)
    (hB_sh2 : C_drift / ceBeta1 + 1 ≤ B_shell)
    (hB_sh3 : 2 * C_err / η_main + 1 ≤ B_shell)
    (hKwin : 2 * (C_drift + 1 / (2 * ceCs)) / ceBeta1 + 1 ≤ K_seed) (hKs1 : 1 ≤ K_seed)
    (hCG_1 : 1 ≤ C_G) (hCG_pos : 0 < C_G)
    (hη_def : η_main = ceK * ceBeta1 * K_seed / (2 * Real.pi ^ 2)) (hη_main : 0 < η_main)
    (hSw_ge : 1 + B_t / ceBeta1 ≤ Sw) (hCm : 0 < C_m)
    (hCerr_def : C_err = 2 * C_m + C_d) (hC_err : 0 < C_err)
    (hδ₀_def : δ₀ = ceBeta1 * K_seed * liftEps c / 2) (hδ₀_pos : 0 < δ₀)
    (hε0 : 0 < liftEps c) (hε1 : liftEps c ≤ 1)
    (hFcont : Continuous F)
    (hconv : ∀ y, windowSmooth δ₀ 4 F y = ∫ t' in Icc (0 : ℝ) δ₀, F (y + t') * bspline 4 δ₀ t')
    (hFeq : ∀ u, F u = C_G * F_node u)
    (hsb_node : ∀ u, |u - t| ≤ ceBeta1 * (K_seed * liftEps c) → K_seed * liftEps c / 2 ≤ F_node u)
    (he_m : ∀ {ξ}, 0 < ξ → |hbS c ξ| ≤ Sw →
      ‖iMain F δ₀ 4 c ξ -
          ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) *
            windowSmooth δ₀ 4 F (-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs)) : ℝ) : ℂ)‖ ≤
        C_m * ξ⁻¹ * (liftEps c ^ 2 + ((1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ * c ^ (-(1 / 2 : ℝ))))
    (he_d : ∀ {ξ}, 0 < ξ → |hbS c ξ| ≤ Sw →
      ‖iDual D_clamp δ₀ 4 c ξ‖ ≤ C_d * ξ⁻¹ * c ^ (-(1 / 2 : ℝ)))
    (hfrep : ∀ ξ, 0 < ξ →
      ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * f (c * ξ) : ℝ) : ℂ) =
        iMain F δ₀ 4 c ξ + iDual D_clamp δ₀ 4 c ξ) :
    0 < f x := by
  set r : ℝ := x - hankelLevel t c 0
  have hr : |r| ≤ R_off := hx_off
  have hx_eq : x = c / Real.pi ^ 2 - (t / ceBeta1) * c ^ (1 / 3 : ℝ) + r := by
    dsimp [r, hankelLevel]; simp only [show hankelBeta1 = ceBeta1 from rfl]; ring
  have hB_c16 : B_shell ≤ c ^ (1 / 6 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity) hcB6 (by norm_num : (0 : ℝ) ≤ 1 / 6)
    rw [← Real.rpow_natCast _ 6, ← Real.rpow_mul hB_sh] at h; simpa using h
  have h_c13_le : B_shell * liftEps c ≤ 1 := by
    have hc13 : B_shell ≤ c ^ (1 / 3 : ℝ) :=
      hB_c16.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
    rw [show liftEps c = (c ^ (1 / 3 : ℝ))⁻¹ by unfold liftEps; rw [Real.rpow_neg hc0.le],
      ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hc0 _)]
    exact hc13
  have hy_half : Real.pi ^ 2 * ((B_t / ceBeta1) * liftEps c ^ 2 + R_off * liftEps c ^ 3) ≤ 1 / 2 := by
    have hε32 : liftEps c ^ 3 ≤ liftEps c ^ 2 := by
      simpa [pow_succ] using mul_le_mul_of_nonneg_left hε1 (sq_nonneg (liftEps c))
    have hε21 : liftEps c ^ 2 ≤ liftEps c := by
      simpa [pow_two] using mul_le_mul_of_nonneg_left hε1 hε0.le
    have h1 : 2 * Real.pi ^ 2 * (B_t / ceBeta1 + R_off) ≤ B_shell := by linarith
    calc Real.pi ^ 2 * ((B_t / ceBeta1) * liftEps c ^ 2 + R_off * liftEps c ^ 3)
        ≤ Real.pi ^ 2 * ((B_t / ceBeta1) * liftEps c ^ 2 + R_off * liftEps c ^ 2) := by gcongr
      _ = (Real.pi ^ 2 * (B_t / ceBeta1 + R_off)) * liftEps c ^ 2 := by ring
      _ ≤ (Real.pi ^ 2 * (B_t / ceBeta1 + R_off)) * liftEps c := by gcongr; have := ceBeta1_pos; positivity
      _ ≤ (B_shell / 2) * liftEps c := mul_le_mul_of_nonneg_right (by linarith) hε0.le
      _ ≤ 1 / 2 := by linarith [h_c13_le]
  have hΔ_lo : c / (2 * Real.pi ^ 2) ≤ c / Real.pi ^ 2 - (t / ceBeta1) * c ^ (1 / 3 : ℝ) + r := by
    have hΔ' : Real.pi ^ 2 * (|t| / ceBeta1 * liftEps c ^ 2 + |r| * liftEps c ^ 3) ≤ 1 / 2 := by
      refine le_trans ?_ hy_half; have := ceBeta1_pos; gcongr
    have hmul := mul_le_mul_of_nonneg_left hΔ' (div_nonneg hc0.le (sq_nonneg Real.pi))
    have hcube : liftEps c ^ 3 * c = 1 := liftEps_cube_mul hc0
    have hc13_eq : c ^ (1 / 3 : ℝ) = liftEps c ^ 2 * c := by
      have hc_eq : c ^ (1 / 3 : ℝ) * liftEps c = 1 := by unfold liftEps; rw [← Real.rpow_add hc0]; norm_num
      calc c ^ (1 / 3 : ℝ) = c ^ (1 / 3 : ℝ) * (liftEps c * (liftEps c ^ 2 * c)) := by
            have : liftEps c * (liftEps c ^ 2 * c) = 1 := by linarith [hcube]
            rw [this, mul_one]
        _ = (c ^ (1 / 3 : ℝ) * liftEps c) * (liftEps c ^ 2 * c) := by ring
        _ = liftEps c ^ 2 * c := by rw [hc_eq, one_mul]
    have hpi_ne : Real.pi ^ 2 ≠ 0 := (sq_pos_of_ne_zero Real.pi_ne_zero).ne'
    have h1 : (c / Real.pi ^ 2) * (Real.pi ^ 2 * (|t| / ceBeta1 * liftEps c ^ 2 + |r| * liftEps c ^ 3)) =
        (|t| / ceBeta1) * c ^ (1 / 3 : ℝ) + |r| := by
      rw [hc13_eq]; field_simp [hpi_ne]; linear_combination |r| * hcube
    have h2 : (c / Real.pi ^ 2) * (1 / 2) = c / (2 * Real.pi ^ 2) := by ring
    have hbd_tr : |t| / ceBeta1 * c ^ (1 / 3 : ℝ) + |r| ≤ c / (2 * Real.pi ^ 2) := by linarith
    have ht_tr : (t / ceBeta1) * c ^ (1 / 3 : ℝ) ≤ (|t| / ceBeta1) * c ^ (1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_abs_self t) ceBeta1_pos.le)
        (Real.rpow_nonneg hc0.le _)
    linarith [neg_abs_le r]
  have hnb := hbS_near_shell hBt hR ht_bd hr hc2 hΔ_lo hy_half
  dsimp only at hnb
  have hx_pos : 0 < x := by rw [hx_eq]; exact lt_of_lt_of_le (by positivity) hΔ_lo
  set ξ : ℝ := x / c
  have hξ_pos : 0 < ξ := div_pos hx_pos hc0
  have hcξ : c * ξ = x := by dsimp [ξ]; field_simp [hc0.ne']
  have hnb1 : |ceBeta1 * hbS c ξ + t| ≤ C_drift * liftEps c := by
    rw [hCd_def]; simpa only [← hx_eq] using hnb.2
  have hSw : |hbS c ξ| ≤ Sw := by
    have hdiv : |hbS c ξ + t / ceBeta1| ≤ (C_drift / ceBeta1) * liftEps c := by
      rw [show hbS c ξ + t / ceBeta1 = (ceBeta1 * hbS c ξ + t) / ceBeta1 by field_simp [ceBeta1_pos.ne']]
      rw [abs_div, abs_of_pos ceBeta1_pos, div_le_iff₀ ceBeta1_pos]
      exact hnb1.trans_eq (by field_simp [ceBeta1_pos.ne'])
    have hCd1 : (C_drift / ceBeta1) * liftEps c ≤ 1 :=
      (mul_le_mul_of_nonneg_right (by linarith : C_drift / ceBeta1 ≤ B_shell) hε0.le).trans h_c13_le
    have hts : |t / ceBeta1| ≤ B_t / ceBeta1 := by
      rw [abs_div, abs_of_pos ceBeta1_pos]; exact div_le_div_of_nonneg_right ht_bd ceBeta1_pos.le
    calc |hbS c ξ| = |(hbS c ξ + t / ceBeta1) - t / ceBeta1| := by ring_nf
      _ ≤ |hbS c ξ + t / ceBeta1| + |t / ceBeta1| := abs_sub _ _
      _ ≤ 1 + B_t / ceBeta1 := add_le_add (hdiv.trans hCd1) hts
      _ ≤ Sw := hSw_ge
  have hfloor_val : (K_seed / 2) * liftEps c ≤
      windowSmooth δ₀ 4 F (-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs)) := by
    rw [hconv]
    have hint_c := integrableOn_bspline_const (by norm_num : 1 ≤ 4) hδ₀_pos ((K_seed / 2) * liftEps c)
    have hint_F : IntegrableOn (fun t' =>
        F (-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs) + t') * bspline 4 δ₀ t')
        (Icc (0 : ℝ) δ₀) volume :=
      (integrableOn_continuous_shift_bspline (by norm_num : 1 ≤ 4) hδ₀_pos
        (x := ceBeta1 * hbS c ξ + liftEps c / (2 * ceCs)) hFcont).congr_fun
        (fun t' _ => congrArg (· * bspline 4 δ₀ t') (congrArg F (by ring)))
        measurableSet_Icc
    calc (K_seed / 2) * liftEps c = ((K_seed / 2) * liftEps c) * 1 := (mul_one _).symm
      _ = ((K_seed / 2) * liftEps c) * ∫ t' in Icc (0 : ℝ) δ₀, bspline 4 δ₀ t' := by
          rw [bspline_setIntegral_one (by norm_num) hδ₀_pos]
      _ = ∫ t' in Icc (0 : ℝ) δ₀, ((K_seed / 2) * liftEps c) * bspline 4 δ₀ t' := (integral_const_mul _ _).symm
      _ ≤ _ := by
          refine setIntegral_mono_on hint_c hint_F measurableSet_Icc fun t' ht' => ?_
          refine mul_le_mul_of_nonneg_right ?_ (bspline_nonneg 4 hδ₀_pos t')
          let u : ℝ := -(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs) + t'
          have hu_dist : |u - t| ≤ ceBeta1 * (K_seed * liftEps c) := by
            have hK2 : C_drift + 1 / (2 * ceCs) ≤ ceBeta1 * K_seed / 2 := by
              have hβ0 := ceBeta1_pos
              calc C_drift + 1 / (2 * ceCs) = ceBeta1 * (2 * (C_drift + 1 / (2 * ceCs)) / ceBeta1) / 2 := by
                    field_simp [hβ0.ne']
                _ ≤ ceBeta1 * K_seed / 2 := by gcongr; linarith
            have ht'_bd : |t'| ≤ (ceBeta1 * K_seed / 2) * liftEps c := by
              rw [abs_of_nonneg ht'.1]; exact ht'.2.trans_eq (by rw [hδ₀_def]; ring)
            have hcs_bd : |liftEps c / (2 * ceCs)| = (1 / (2 * ceCs)) * liftEps c := by
              have := ceCs_pos; rw [abs_of_nonneg (by positivity)]; ring
            calc |u - t| = |-(ceBeta1 * hbS c ξ + t) - liftEps c / (2 * ceCs) + t'| := congrArg abs (by dsimp [u]; ring)
              _ ≤ |-(ceBeta1 * hbS c ξ + t) - liftEps c / (2 * ceCs)| + |t'| := abs_add_le _ _
              _ ≤ (|ceBeta1 * hbS c ξ + t| + |liftEps c / (2 * ceCs)|) + |t'| :=
                  add_le_add_left ((abs_sub (-(ceBeta1 * hbS c ξ + t)) _).trans_eq (by rw [abs_neg])) _
              _ ≤ C_drift * liftEps c + (1 / (2 * ceCs)) * liftEps c + (ceBeta1 * K_seed / 2) * liftEps c := by
                  rw [hcs_bd]; exact add_le_add (add_le_add hnb1 le_rfl) ht'_bd
              _ = (C_drift + 1 / (2 * ceCs) + ceBeta1 * K_seed / 2) * liftEps c := by ring
              _ ≤ (ceBeta1 * K_seed / 2 + ceBeta1 * K_seed / 2) * liftEps c := by gcongr
              _ = ceBeta1 * (K_seed * liftEps c) := by ring
          have hfl := hsb_node u hu_dist
          rw [hFeq u]
          calc (K_seed / 2) * liftEps c = 1 * (K_seed * liftEps c / 2) := by ring
            _ ≤ C_G * (K_seed * liftEps c / 2) :=
                mul_le_mul_of_nonneg_right hCG_1 (div_nonneg (mul_nonneg (by linarith) hε0.le) zero_le_two)
            _ ≤ _ := mul_le_mul_of_nonneg_left hfl hCG_pos.le
  have hinv_le : ((1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ ≤ 1 := by
    have : 0 ≤ δ₀ * c ^ (1 / 3 : ℝ) := mul_nonneg hδ₀_pos.le (Real.rpow_nonneg hc0.le _)
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have hc23_le : liftEps c ^ 2 ≤ c ^ (-(1 / 2 : ℝ)) := by
    unfold liftEps; rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hc0.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have herr_m : C_m * ξ⁻¹ * (liftEps c ^ 2 + ((1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ * c ^ (-(1 / 2 : ℝ))) ≤
      2 * C_m * ξ⁻¹ * c ^ (-(1 / 2 : ℝ)) := by
    have : liftEps c ^ 2 + ((1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ * c ^ (-(1 / 2 : ℝ)) ≤
        2 * c ^ (-(1 / 2 : ℝ)) := by
      have hc12 : 0 ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hc0.le _
      calc _ ≤ c ^ (-(1 / 2 : ℝ)) + 1 * c ^ (-(1 / 2 : ℝ)) := by gcongr
        _ = 2 * c ^ (-(1 / 2 : ℝ)) := by ring
    calc C_m * ξ⁻¹ * _ ≤ C_m * ξ⁻¹ * (2 * c ^ (-(1 / 2 : ℝ))) := by gcongr
      _ = 2 * C_m * ξ⁻¹ * c ^ (-(1 / 2 : ℝ)) := by ring
  let targ : ℝ := ceK * ceBeta1 / (Real.pi ^ 2 * ξ) *
    windowSmooth δ₀ 4 F (-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs))
  have htarg_lo : η_main * liftEps c * ξ⁻¹ ≤ targ := by
    have hpref : 0 ≤ ceK * ceBeta1 / (Real.pi ^ 2 * ξ) := by have := ceK_pos; have := ceBeta1_pos; positivity
    calc η_main * liftEps c * ξ⁻¹
        = (ceK * ceBeta1 * K_seed / (2 * Real.pi ^ 2)) * liftEps c * ξ⁻¹ := by rw [hη_def]
      _ = ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * ((K_seed / 2) * liftEps c) := by
          simp only [div_eq_mul_inv, mul_inv]; ring
      _ ≤ targ := mul_le_mul_of_nonneg_left hfloor_val hpref
  have hnorm_tot : ‖iMain F δ₀ 4 c ξ + iDual D_clamp δ₀ 4 c ξ - (targ : ℂ)‖ < targ := by
    have htri : ‖(iMain F δ₀ 4 c ξ + iDual D_clamp δ₀ 4 c ξ) - (targ : ℂ)‖ ≤
        ‖iMain F δ₀ 4 c ξ - (targ : ℂ)‖ + ‖iDual D_clamp δ₀ 4 c ξ‖ := by
      simpa only [add_sub_right_comm] using norm_add_le
        (iMain F δ₀ 4 c ξ - (targ : ℂ)) (iDual D_clamp δ₀ 4 c ξ)
    have hc16_bound : c ^ (-(1 / 6 : ℝ)) ≤ η_main / (2 * C_err) := by
      have hc16_pos : 0 < c ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hc0 _
      rw [Real.rpow_neg hc0.le, ← one_div, div_le_iff₀ hc16_pos]
      have h1 : 2 * C_err / η_main ≤ B_shell := by linarith
      have h2C_ne : 2 * C_err ≠ 0 := by positivity
      calc (1 : ℝ) = (η_main / (2 * C_err)) * (2 * C_err / η_main) := by
            rw [div_mul_div_comm, mul_comm η_main (2 * C_err), div_self (mul_ne_zero h2C_ne hη_main.ne')]
        _ ≤ (η_main / (2 * C_err)) * B_shell := by gcongr
        _ ≤ (η_main / (2 * C_err)) * c ^ (1 / 6 : ℝ) := by gcongr
    have herr_c13 : C_err * c ^ (-(1 / 2 : ℝ)) < η_main * liftEps c := by
      have hprod : liftEps c * c ^ (-(1 / 6 : ℝ)) = c ^ (-(1 / 2 : ℝ)) := by
        unfold liftEps; rw [← Real.rpow_add hc0]; norm_num
      have hlt : C_err * c ^ (-(1 / 6 : ℝ)) ≤ η_main / 2 := by
        calc C_err * c ^ (-(1 / 6 : ℝ)) ≤ C_err * (η_main / (2 * C_err)) := by gcongr
          _ = (C_err * η_main) / (C_err * 2) := by rw [mul_div_assoc', mul_comm 2 C_err]
          _ = η_main / 2 := mul_div_mul_left η_main 2 hC_err.ne'
      calc C_err * c ^ (-(1 / 2 : ℝ)) = (C_err * c ^ (-(1 / 6 : ℝ))) * liftEps c := by rw [← hprod]; ring
        _ ≤ (η_main / 2) * liftEps c := mul_le_mul_of_nonneg_right hlt hε0.le
        _ < η_main * liftEps c := mul_lt_mul_of_pos_right (half_lt_self hη_main) hε0
    calc ‖_‖ ≤ 2 * C_m * ξ⁻¹ * c ^ (-(1 / 2 : ℝ)) + C_d * ξ⁻¹ * c ^ (-(1 / 2 : ℝ)) :=
          htri.trans (add_le_add ((he_m hξ_pos hSw).trans herr_m) (he_d hξ_pos hSw))
      _ = (C_err * c ^ (-(1 / 2 : ℝ))) * ξ⁻¹ := by rw [hCerr_def]; ring
      _ < (η_main * liftEps c) * ξ⁻¹ := mul_lt_mul_of_pos_right herr_c13 (inv_pos.mpr hξ_pos)
      _ ≤ targ := htarg_lo
  have hre_pos := re_pos_of_norm_lt hnorm_tot
  rw [← hfrep ξ hξ_pos, Complex.ofReal_re, hcξ] at hre_pos
  have hpref : 0 < c ^ (1 / 3 : ℝ) * hankelRho0 c x :=
    mul_pos (Real.rpow_pos_of_pos hc0 _) (hankelRho0_pos hc0 hx_pos)
  exact (mul_pos_iff_of_pos_left hpref).mp hre_pos

private lemma hbCon_tail_pos
    {tm γ₁ K_seed η_tail K₀_tail B_tl c x : ℝ} {F D_clamp f : ℝ → ℝ} {δ₀ : ℝ}
    (htm_neg : tm < 0) (hc0 : 0 < c) (hc2 : 2 ≤ c) (hcB3 : B_tl ^ 3 ≤ c) (hB_tl : 0 ≤ B_tl)
    (hη_tail : 0 < η_tail) (hη_def : η_tail = (2 * γ₁ / ceBeta1 + 1 / 2) * K_seed + 1)
    (hK₀_def : K₀_tail = η_tail + 1)
    (hBtl1 : 2 * Real.pi ^ 2 * (|tm| / ceBeta1 + η_tail) ≤ B_tl)
    (hBtl2 : 2 * Real.pi ^ 2 * (|tm| / ceBeta1 + η_tail) ^ 2 ≤ B_tl)
    (hε0 : 0 < liftEps c) (hε1 : liftEps c ≤ 1)
    (ho6_c : ∀ {ξ}, 0 < ξ →
      (-tm + 2 * γ₁ * (K_seed * liftEps c) + ceBeta1 * (K_seed * liftEps c) / 2) / ceBeta1 ≤ hbS c ξ →
      0 < (iMain F δ₀ 4 c ξ + iDual D_clamp δ₀ 4 c ξ).re)
    (hfrep : ∀ ξ, 0 < ξ →
      ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * f (c * ξ) : ℝ) : ℂ) =
        iMain F δ₀ 4 c ξ + iDual D_clamp δ₀ 4 c ξ)
    (hx : c / π ^ 2 + (|tm| / hankelBeta1) * c ^ (1 / 3 : ℝ) + K₀_tail ≤ x) :
    0 < f x := by
  have hB_eps : B_tl * liftEps c ≤ 1 := by
    have hle13 : B_tl ≤ c ^ (1 / 3 : ℝ) := by
      have h := Real.rpow_le_rpow (by positivity) hcB3 (by norm_num : (0 : ℝ) ≤ 1 / 3)
      rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul hB_tl] at h; simpa using h
    rw [show liftEps c = (c ^ (1 / 3 : ℝ))⁻¹ by unfold liftEps; rw [Real.rpow_neg hc0.le],
      ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hc0 _)]
    exact hle13
  have hy_half : Real.pi ^ 2 * ((|tm| / ceBeta1) * liftEps c ^ 2 + η_tail * liftEps c ^ 3) ≤ 1 / 2 := by
    have hε32 : liftEps c ^ 3 ≤ liftEps c ^ 2 := by
      simpa [pow_succ] using mul_le_mul_of_nonneg_left hε1 (sq_nonneg (liftEps c))
    have hε21 : liftEps c ^ 2 ≤ liftEps c := by
      simpa [pow_two] using mul_le_mul_of_nonneg_left hε1 hε0.le
    calc Real.pi ^ 2 * ((|tm| / ceBeta1) * liftEps c ^ 2 + η_tail * liftEps c ^ 3)
        ≤ Real.pi ^ 2 * ((|tm| / ceBeta1) * liftEps c ^ 2 + η_tail * liftEps c ^ 2) := by gcongr
      _ = (Real.pi ^ 2 * (|tm| / ceBeta1 + η_tail)) * liftEps c ^ 2 := by ring
      _ ≤ (Real.pi ^ 2 * (|tm| / ceBeta1 + η_tail)) * liftEps c := by gcongr; have := ceBeta1_pos; positivity
      _ ≤ (B_tl / 2) * liftEps c := mul_le_mul_of_nonneg_right (by linarith [hBtl1]) hε0.le
      _ = (B_tl * liftEps c) / 2 := by ring
      _ ≤ 1 / 2 := by linarith
  have hquad : 2 * Real.pi ^ 2 * liftEps c * (|tm| / ceBeta1 + η_tail) ^ 2 ≤ 1 := by
    calc 2 * Real.pi ^ 2 * liftEps c * (|tm| / ceBeta1 + η_tail) ^ 2
        = (2 * Real.pi ^ 2 * (|tm| / ceBeta1 + η_tail) ^ 2) * liftEps c := by ring
      _ ≤ B_tl * liftEps c := by gcongr
      _ ≤ 1 := hB_eps
  have hx' : c / Real.pi ^ 2 - (tm / ceBeta1) * c ^ (1 / 3 : ℝ) + (η_tail + 1) ≤ x := by
    have htm_abs : |tm| = -tm := abs_of_neg htm_neg
    have hβeq : hankelBeta1 = ceBeta1 := rfl
    rw [htm_abs, hβeq, hK₀_def] at hx
    exact hx.trans_eq' (by ring)
  obtain ⟨hx_pos, hS_lo⟩ := hbS_tail_lower hη_tail hc2 hy_half hquad hx'
  have hS_o6 : (-tm + 2 * γ₁ * (K_seed * liftEps c) + ceBeta1 * (K_seed * liftEps c) / 2) / ceBeta1 ≤
      hbS c (x / c) := by
    have hβ0 := ceBeta1_pos
    have h_eq : (-tm + 2 * γ₁ * (K_seed * liftEps c) + ceBeta1 * (K_seed * liftEps c) / 2) / ceBeta1 =
        -tm / ceBeta1 + (2 * γ₁ / ceBeta1 + 1 / 2) * K_seed * liftEps c := by
      rw [div_eq_iff hβ0.ne']
      calc -tm + 2 * γ₁ * (K_seed * liftEps c) + ceBeta1 * (K_seed * liftEps c) / 2
          = (-tm / ceBeta1) * ceBeta1 + ((2 * γ₁ / ceBeta1) * ceBeta1 + ceBeta1 / 2) * K_seed * liftEps c := by
              rw [div_mul_cancel₀ _ hβ0.ne', div_mul_cancel₀ _ hβ0.ne']; ring
        _ = (-tm / ceBeta1 + (2 * γ₁ / ceBeta1 + 1 / 2) * K_seed * liftEps c) * ceBeta1 := by ring
    rw [h_eq]
    have h_diff : (2 * γ₁ / ceBeta1 + 1 / 2) * K_seed * liftEps c ≤ η_tail * liftEps c :=
      mul_le_mul_of_nonneg_right (by linarith [hη_def]) hε0.le
    linarith
  set ξ : ℝ := x / c
  have hξ_pos : 0 < ξ := div_pos hx_pos hc0
  have hcξ : c * ξ = x := by dsimp [ξ]; field_simp [hc0.ne']
  have hre_pos := ho6_c hξ_pos hS_o6
  rw [← hfrep ξ hξ_pos, Complex.ofReal_re, hcξ] at hre_pos
  have hpref : 0 < c ^ (1 / 3 : ℝ) * hankelRho0 c x :=
    mul_pos (Real.rpow_pos_of_pos hc0 _) (hankelRho0_pos hc0 hx_pos)
  exact (mul_pos_iff_of_pos_left hpref).mp hre_pos

private lemma hbCon_sigma (D : ShellHBData) (R_off : ℝ) (hR : 0 ≤ R_off)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ K c₁ : ℝ, 0 < K ∧ 2 ≤ c₁ ∧
      ∀ c : ℝ, c₁ ≤ c → ∃ f : ℝ → ℝ, IsHankelEigenfn c σ f ∧ σ * f 0 < 0 ∧
        (∀ t ∈ D.S, t ≠ D.tm → ∀ x : ℝ, |x - hankelLevel t c 0| ≤ R_off → 0 < f x) ∧
        (∀ x : ℝ, c / π ^ 2 + (|D.tm| / hankelBeta1) * c ^ (1 / 3 : ℝ) + K ≤ x → 0 < f x) := by
  classical
  obtain ⟨S, β₀₀, β₁₁, hβ_pos, hS_last, _, hS_site, hS_GN, hS_HN, hG_cl, hH_cl⟩ :=
    hbSeedSpec_of_shellHBData_all D
  obtain ⟨b, hb, hb_nodes⟩ := exists_ceSb_pos_at_nodes S
  obtain ⟨γ₂, hγ₂, hseed_unif⟩ := hb_seed_mass_exists_unif S hb hb_nodes (ε₀ := 0) le_rfl
  obtain ⟨δ₁, hδ₁, c₁_fl, hc₁_fl, c₂_fl, hc₂_fl, hseed_body⟩ := hseed_unif (V_max := 1) zero_le_one
  let γ₁ : ℝ := (γ₂ * (1 + |airyDerivFirstZero|) + 1) / S.I_N
  have hγ₁ : 0 < γ₁ := div_pos (by have := S.I_N_pos; positivity) S.I_N_pos
  let β_D : ℝ := β₀₀ + β₁₁
  let C_G : ℝ := max 1 (2 / β_D)
  have hCG_1 : 1 ≤ C_G := le_max_left _ _
  have hCG_pos : 0 < C_G := by positivity
  let B3 := hbConBasis D b
  let b00 : Fin 3 → ℝ := ![β₀₀, 0, b]
  let b11 : Fin 3 → ℝ := ![β₁₁, 0, 1]
  have hB3 : ∀ i ∈ (Finset.univ : Finset (Fin 3)), HasGenRationalAiryCoeffs (B3 i) (b00 i) (b11 i) := by
    intro i _; fin_cases i <;> [exact hG_cl; exact hH_cl; exact hasGenRationalAiryCoeffs_airySbC b]
  let α := hbConAlpha C_G γ₁ γ₂
  let R_cl : ℝ := C_G * max 1 (max (2 * γ₁) (2 * γ₂))
  have hR_cl : 0 ≤ R_cl := by positivity
  have hα_bd : ∀ i ∈ (Finset.univ : Finset (Fin 3)), ∀ K c : ℝ,
      1 ≤ K → 2000 ≤ c → K * liftEps c ≤ 2 → |α i K c| ≤ R_cl := by
    intro i _ K c hK hc2k hKε
    have hc0 : 0 < c := by linarith
    have hKε0 : 0 ≤ K * liftEps c := mul_nonneg (by linarith) (liftEps_pos hc0).le
    fin_cases i
    · dsimp [α, hbConAlpha, R_cl]; rw [abs_of_pos hCG_pos]
      calc C_G = C_G * 1 := (mul_one _).symm
        _ ≤ C_G * max 1 (max (2 * γ₁) (2 * γ₂)) :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) hCG_pos.le
    · dsimp [α, hbConAlpha, R_cl]
      rw [abs_neg, abs_mul, abs_of_pos hCG_pos, abs_of_nonneg (mul_nonneg hKε0 hγ₁.le)]
      refine mul_le_mul_of_nonneg_left ((le_trans ?_ (le_max_left _ _)).trans (le_max_right _ _)) hCG_pos.le
      nlinarith [hγ₁]
    · dsimp [α, hbConAlpha, R_cl]
      rw [abs_mul, abs_of_pos hCG_pos, abs_of_nonneg (mul_nonneg hKε0 hγ₂.le)]
      refine mul_le_mul_of_nonneg_left ((le_trans ?_ (le_max_right _ _)).trans (le_max_right _ _)) hCG_pos.le
      nlinarith [hγ₂]
  have hα_bd4 : ∀ i ∈ (Finset.univ : Finset (Fin 3)), ∀ K c : ℝ,
      1 ≤ K → 2000 ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c → |α i K c| ≤ R_cl :=
    fun i hi K c hK hc2k hc8K _ => hα_bd i hi K c hK hc2k ((liftEps_mul_le_half (by linarith) hc8K).trans (by norm_num))
  have hE := o6FamilyEst_of_genRational_family Finset.univ B3 b00 b11 hB3 α R_cl δ₁ hR_cl hδ₁ hα_bd4 (by norm_num : 3 ≤ 4)
  have hDE := hbCon_dual_est Finset.univ B3 b00 b11 hB3 α hR_cl hα_bd hσ
  let F_seed : ℝ → ℝ → ℝ → ℝ := fun K c u => ∑ i ∈ (Finset.univ : Finset (Fin 3)), α i K c * (B3 i (u : ℂ)).re
  have hF_seed_eq : ∀ K c u, F_seed K c u = C_G * (S.G_N u - γ₁ * (K * liftEps c) * S.H_N u + γ₂ * (K * liftEps c) * ceSb b u) := by
    intro K c u
    simp only [F_seed, Fin.sum_univ_three, B3, hbConBasis, α, hbConAlpha,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, airySbC_re]
    have hG := congr_fun hS_GN u
    have hH := congr_fun hS_HN u
    rw [← hG, ← hH]
    ring
  have hlead : ∀ {K c : ℝ}, 1 ≤ K → 2000 ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c →
      1 ≤ ∑ i ∈ (Finset.univ : Finset (Fin 3)), α i K c * (b00 i + b11 i) := by
    intro K c _ hc2k _ _
    have hc0 : 0 < c := by linarith
    simp only [Fin.sum_univ_three, α, hbConAlpha, b00, b11, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    have h1 : 2 ≤ C_G * β_D := by
      have : 2 / β_D ≤ C_G := le_max_right _ _
      dsimp [β_D] at this ⊢
      calc (2 : ℝ) = (2 / (β₀₀ + β₁₁)) * (β₀₀ + β₁₁) := by field_simp [hβ_pos.ne']
        _ ≤ C_G * (β₀₀ + β₁₁) := mul_le_mul_of_nonneg_right this hβ_pos.le
    have h2 : 0 ≤ C_G * (K * liftEps c * γ₂) * (b + 1) := by have := liftEps_pos hc0; positivity
    dsimp [β_D] at h1; linarith
  have htm_neg : D.tm < 0 := lt_of_le_of_lt D.tm_le_airyZero_one (by linarith [airyZero_one.2])
  have hU0 : 0 ≤ -D.tm := by linarith
  have hU1 : 0 ≤ 2 * γ₁ := by positivity
  have hKε_le_δ : ∀ {K c : ℝ}, 1 ≤ K → 2000 ≤ c → (K / δ₁) ^ 3 ≤ c → K * liftEps c ≤ δ₁ := fun {K c} hK hc2k hcδ => by
    have hc0 : 0 < c := by linarith
    have hcube := liftEps_cube_mul hc0
    have h3 : (K * liftEps c) ^ 3 ≤ δ₁ ^ 3 := by
      have : K ^ 3 ≤ δ₁ ^ 3 * c := by rw [div_pow, div_le_iff₀ (by positivity)] at hcδ; linarith
      by_contra hcon; push Not at hcon
      have := mul_lt_mul_of_pos_right hcon hc0
      nlinarith [show (K * liftEps c) ^ 3 * c = K ^ 3 from by linear_combination K ^ 3 * hcube]
    exact le_of_pow_le_pow_left₀ (by norm_num) hδ₁.le h3
  have hfloor : ∀ {K c : ℝ}, 1 ≤ K → 2000 ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c →
      ∀ x : ℝ, -D.tm + (2 * γ₁) * (K * liftEps c) + ceBeta1 * (K * liftEps c) / 2 ≤ x →
      (1 + x) ^ (-(3 / 2 : ℝ)) * ((C_G * c₁_fl) * (K * liftEps c) + (C_G * c₂_fl) * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x)) ≤
        ∫ t in Icc (0 : ℝ) (ceBeta1 * (K * liftEps c) / 2),
          F_seed K c (-x + t) * bspline 4 (ceBeta1 * (K * liftEps c) / 2) t := by
    intro K c hK hc2k _ hcδ x hx
    have hc0 : 0 < c := by linarith
    have hKε_pos : 0 < K * liftEps c := mul_pos (by linarith) (liftEps_pos hc0)
    have hKεδ := hKε_le_δ hK hc2k hcδ
    have hsb := hseed_body 1 ⟨zero_le_one, le_rfl⟩ (K * liftEps c) ⟨hKε_pos, hKεδ⟩ 0 (by simp)
    dsimp only at hsb
    have hγ₁_eq : (γ₂ * (1 + |airyDerivFirstZero|) + 1) / S.I_N = γ₁ := rfl
    rw [hγ₁_eq] at hsb
    have hu0 : |S.lastNode - 2 * γ₁ * (K * liftEps c)| = -D.tm + (2 * γ₁) * (K * liftEps c) := by
      rw [hS_last, abs_of_nonpos (by nlinarith [hγ₁, hKε_pos])]; ring
    have hfl := hsb.2.2.1 x (by linarith)
    have hFeq : ∀ t, F_seed K c (-x + t) = C_G * (S.G_N (-x + t) - γ₁ * (K * liftEps c) * S.H_N (-x + t) +
        γ₂ * (K * liftEps c) * ceSb b (-x + t) + 0 * ceG1 (airyZero 1) (-x + t)) := fun t => by
      rw [hF_seed_eq, zero_mul, add_zero]
    calc (1 + x) ^ (-(3 / 2 : ℝ)) * ((C_G * c₁_fl) * (K * liftEps c) + (C_G * c₂_fl) * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x))
        = C_G * ((1 + x) ^ (-(3 / 2 : ℝ)) * (c₁_fl * (K * liftEps c) + c₂_fl * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x))) := by ring
      _ ≤ C_G * ∫ t in Icc (0 : ℝ) (ceBeta1 * (K * liftEps c) / 2),
            (S.G_N (-x + t) - γ₁ * (K * liftEps c) * S.H_N (-x + t) +
              γ₂ * (K * liftEps c) * ceSb b (-x + t) + 0 * ceG1 (airyZero 1) (-x + t)) *
              bspline 4 (ceBeta1 * (K * liftEps c) / 2) t := mul_le_mul_of_nonneg_left hfl hCG_pos.le
      _ = ∫ t in Icc (0 : ℝ) (ceBeta1 * (K * liftEps c) / 2),
            F_seed K c (-x + t) * bspline 4 (ceBeta1 * (K * liftEps c) / 2) t := by
          rw [← integral_const_mul]
          refine setIntegral_congr_fun measurableSet_Icc fun t _ => by rw [hFeq t]; ring
  obtain ⟨K_o6, c_o6, hKo6, hco6, ho6⟩ := o6_positivity_dual_family (m := 4) (by norm_num) hE _ hDE
    hδ₁ (mul_pos hCG_pos hc₁_fl) (mul_pos hCG_pos hc₂_fl) hU0 hU1 hlead hfloor
  -- Window constant `K_win` (shared across `c` and `σ`)
  let B_t : ℝ := D.S.sup' D.S_nonempty (fun t => |t|)
  have hBt : 0 ≤ B_t := le_trans (abs_nonneg D.tm) (Finset.le_sup' (fun t => |t|) D.tm_mem)
  let C_drift : ℝ := ceBeta1 * R_off + 2 * ceBeta1 * Real.pi ^ 2 * (B_t / ceBeta1 + R_off) ^ 2
  have hCd : 0 ≤ C_drift := by have := ceBeta1_pos; positivity
  let K_win : ℝ := max 1 (2 * (C_drift + 1 / (2 * ceCs)) / ceBeta1 + 1)
  have hK_win : 1 ≤ K_win := le_max_left _ _
  let K_seed : ℝ := max K_o6 K_win
  have hKs1 : 1 ≤ K_seed := hKo6.trans (le_max_left _ _)
  have hKs_o6 : K_o6 ≤ K_seed := le_max_left _ _
  have hKs_win : K_win ≤ K_seed := le_max_right _ _
  -- Tail threshold constants at `K = K_seed`
  let η_tail : ℝ := (2 * γ₁ / ceBeta1 + 1 / 2) * K_seed + 1
  have hη_tail : 0 < η_tail := by have := ceBeta1_pos; positivity
  let K₀_tail : ℝ := η_tail + 1
  have hK₀_tail : 0 < K₀_tail := by linarith
  let B_tl : ℝ := max (2 * Real.pi ^ 2 * (|D.tm| / ceBeta1 + η_tail))
    (2 * Real.pi ^ 2 * (|D.tm| / ceBeta1 + η_tail) ^ 2) + 1
  have hB_tl : 0 ≤ B_tl := by positivity
  -- Window threshold constants at `K = K_seed`
  let Sw : ℝ := 1 + B_t / ceBeta1
  obtain ⟨C_m, hCm, he5_m⟩ := hE.e5 Sw
  obtain ⟨C_d, hCd5, he5_d⟩ := hDE.e5 Sw
  let η_main : ℝ := ceK * ceBeta1 * K_seed / (2 * Real.pi ^ 2)
  have hη_main : 0 < η_main := by have := ceK_pos; have := ceBeta1_pos; positivity
  let C_err : ℝ := 2 * C_m + C_d
  have hC_err : 0 < C_err := by positivity
  let B_shell : ℝ := max (2 * Real.pi ^ 2 * (B_t / ceBeta1 + R_off) + 1)
    (max (C_drift / ceBeta1 + 1) (2 * C_err / η_main + 1))
  have hB_sh : 0 ≤ B_shell := by have := ceBeta1_pos; positivity
  -- Origin symbol bound constant `C_orig`
  have hRhp_i : ∀ i ∈ (Finset.univ : Finset (Fin 3)), ∃ Ci > 0, ∀ w : ℂ, 0 ≤ w.re →
      ‖airyTwistedLaplaceC (fun u => (B3 i (u : ℂ)).re) ((ceCs : ℂ) * w)‖ ≤
        Ci * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := fun i hi => (hasU2_of_genRational (hB3 i hi)).rhp
  choose CRhp hCRhp_pos hCRhp_bd using hRhp_i
  let C_orig : ℝ := R_cl * (∑ i ∈ (Finset.univ : Finset (Fin 3)), CRhp i (Finset.mem_univ i)) + 1
  have hC_orig : 0 < C_orig := by
    have : 0 ≤ ∑ i ∈ (Finset.univ : Finset (Fin 3)), CRhp i (Finset.mem_univ i) :=
      Finset.sum_nonneg fun i _ => (hCRhp_pos i _).le
    positivity
  let c_orig : ℝ := (4 * C_orig / (ceK * C_G * K_seed) + 1) ^ 2
  let c₁ : ℝ := max (max (max c_o6 32768) (max (8 * K_seed ^ 3) ((K_seed / δ₁) ^ 3)))
    (max (max (B_tl ^ 3) (B_shell ^ 6)) c_orig)
  have hc₁_o6 : c_o6 ≤ c₁ := ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)
  have hc₁_32 : 32768 ≤ c₁ := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)
  have hc₁_2k : 2000 ≤ c₁ := by linarith
  have hc₁_8K : 8 * K_seed ^ 3 ≤ c₁ := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
  have hc₁_δ : (K_seed / δ₁) ^ 3 ≤ c₁ := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
  have hc₁_Btl : B_tl ^ 3 ≤ c₁ := ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hc₁_Bsh : B_shell ^ 6 ≤ c₁ := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hc₁_orig : c_orig ≤ c₁ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K₀_tail, c₁, hK₀_tail, by linarith, fun c hc => ?_⟩
  have hc0 : 0 < c := by linarith
  have hc2 : 2 ≤ c := by linarith
  have hc2k : 2000 ≤ c := hc₁_2k.trans hc
  have hc32 : 32768 ≤ c := hc₁_32.trans hc
  have hc8K : 8 * K_seed ^ 3 ≤ c := hc₁_8K.trans hc
  have hcδ : (K_seed / δ₁) ^ 3 ≤ c := hc₁_δ.trans hc
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  have hε1 : liftEps c ≤ 1 := liftEps_le_one (by linarith)
  have hKeps : K_seed * liftEps c ≤ 1 / 2 := liftEps_mul_le_half (by linarith) hc8K
  have hKε_pos : 0 < K_seed * liftEps c := mul_pos (by linarith) hε0
  let δ₀ : ℝ := ceBeta1 * K_seed * liftEps c / 2
  have hδ0 : 0 ≤ δ₀ := by have := ceBeta1_pos; positivity
  have hδ2 : δ₀ ≤ 2 := by
    have h2 := ceBeta1_lt_eight
    calc δ₀ = ceBeta1 * (K_seed * liftEps c) / 2 := by dsimp [δ₀]; ring
      _ ≤ 8 * (1 / 2) / 2 := by gcongr
      _ = 2 := by norm_num
  have hU_F : HasU2 (F_seed K_seed c) := hasU2_finset_sum Finset.univ B3 b00 b11 hB3 (fun i => α i K_seed c)
  have htail_F := hbCon_tail_decay Finset.univ B3 b00 b11 hB3 (fun i => α i K_seed c) (c := c) hδ0 hδ2 (by linarith [hc2k]) hσ
  obtain ⟨f, hfeig, hfrep, -, hf0⟩ := exists_hankelEigenfn_lift_general hU_F hδ0 4 (by linarith) hσ htail_F
  have hcond : 1 ≤ K_seed ∧ 2000 ≤ c ∧ K_seed * liftEps c ≤ 2 := ⟨hKs1, hc2k, by linarith⟩
  have hD_eq : (fun u => if 1 ≤ K_seed ∧ 2000 ≤ c ∧ K_seed * liftEps c ≤ 2 then σ * F_seed K_seed c u else 0) =
      fun u => σ * F_seed K_seed c u := by ext u; simp [hcond]
  have hfrep_dual : ∀ ξ : ℝ, 0 < ξ →
      ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * f (c * ξ) : ℝ) : ℂ) =
        iMain (F_seed K_seed c) δ₀ 4 c ξ +
          iDual (fun u => if 1 ≤ K_seed ∧ 2000 ≤ c ∧ K_seed * liftEps c ≤ 2 then
            σ * F_seed K_seed c u else 0) δ₀ 4 c ξ := fun ξ hξ => by
    rw [hD_eq, iDual_const_mul]; exact hfrep ξ hξ
  -- 1. Origin sign `σ * f 0 < 0`
  have horigin : σ * f 0 < 0 := by
    have hKεδ := hKε_le_δ hKs1 hc2k hcδ
    have hsb := hseed_body 1 ⟨zero_le_one, le_rfl⟩ (K_seed * liftEps c) ⟨hKε_pos, hKεδ⟩ 0 (by simp)
    dsimp only at hsb
    have hF_int : ∫ u : ℝ, F_seed K_seed c u = -(C_G * K_seed * liftEps c) := by
      have hFeq : F_seed K_seed c = fun u => C_G * (S.G_N u - γ₁ * (K_seed * liftEps c) * S.H_N u +
          γ₂ * (K_seed * liftEps c) * ceSb b u + 0 * ceG1 (airyZero 1) u) := funext fun u => by
        rw [hF_seed_eq, zero_mul, add_zero]
      rw [hFeq, integral_const_mul, hsb.2.1.2]; ring
    have hW0 := liftSymbol_zero_eq hU_F δ₀ 4
    rw [hF_int] at hW0
    have hWc13 : ‖liftSymbol (F_seed K_seed c) δ₀ 4 (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ))‖ ≤
        C_orig * c ^ (-(5 / 6 : ℝ)) := by
      let w : ℂ := ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ)
      have hw_re : 0 ≤ w.re := by simp [w]; positivity
      have h1w : c ^ (1 / 3 : ℝ) ≤ ‖1 + w‖ := by
        have : (1 + w).re = 1 + c ^ (1 / 3 : ℝ) := by simp [w]
        calc c ^ (1 / 3 : ℝ) ≤ 1 + c ^ (1 / 3 : ℝ) := by linarith
          _ = |(1 + w).re| := by rw [this, abs_of_pos (by positivity)]
          _ ≤ ‖1 + w‖ := Complex.abs_re_le_norm _
      have hpow_w : ‖1 + w‖ ^ (-(5 / 2 : ℝ)) ≤ c ^ (-(5 / 6 : ℝ)) := by
        calc ‖1 + w‖ ^ (-(5 / 2 : ℝ))
            ≤ (c ^ (1 / 3 : ℝ)) ^ (-(5 / 2 : ℝ)) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) h1w (by norm_num)
          _ = c ^ (-(5 / 6 : ℝ)) := by rw [← Real.rpow_mul hc0.le]; norm_num
      have hsplit : liftSymbol (F_seed K_seed c) δ₀ 4 w =
          liftMultiplier δ₀ 4 w *
            ∑ i ∈ (Finset.univ : Finset (Fin 3)), (α i K_seed c : ℂ) *
              airyTwistedLaplaceC (fun u => (B3 i (u : ℂ)).re) ((ceCs : ℂ) * w) := by
        unfold liftSymbol
        rw [airyTwistedLaplaceC_finset_sum Finset.univ B3 b00 b11 hB3 (fun i => α i K_seed c) hw_re]
      rw [hsplit, norm_mul]
      calc ‖liftMultiplier δ₀ 4 w‖ * ‖∑ i ∈ (Finset.univ : Finset (Fin 3)), (α i K_seed c : ℂ) *
              airyTwistedLaplaceC (fun u => (B3 i (u : ℂ)).re) ((ceCs : ℂ) * w)‖
          ≤ 1 * ∑ i ∈ (Finset.univ : Finset (Fin 3)), ‖(α i K_seed c : ℂ) *
              airyTwistedLaplaceC (fun u => (B3 i (u : ℂ)).re) ((ceCs : ℂ) * w)‖ :=
            mul_le_mul (norm_liftMultiplier_le_one hδ0 4 hw_re) (norm_sum_le _ _) (norm_nonneg _) zero_le_one
        _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin 3)), R_cl * (CRhp i (Finset.mem_univ i) * c ^ (-(5 / 6 : ℝ))) := by
            rw [one_mul]; refine Finset.sum_le_sum fun i hi => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul (hα_bd4 i hi K_seed c hKs1 hc2k hc8K hcδ)
              ((hCRhp_bd i hi w hw_re).trans (mul_le_mul_of_nonneg_left hpow_w (hCRhp_pos i hi).le))
              (norm_nonneg _) hR_cl
        _ = (R_cl * ∑ i ∈ (Finset.univ : Finset (Fin 3)), CRhp i (Finset.mem_univ i)) * c ^ (-(5 / 6 : ℝ)) := by
            simp_rw [← mul_assoc, ← Finset.sum_mul, ← Finset.mul_sum]
        _ ≤ C_orig * c ^ (-(5 / 6 : ℝ)) :=
            mul_le_mul_of_nonneg_right (by dsimp [C_orig]; linarith) (Real.rpow_nonneg hc0.le _)
    have hre := congrArg Complex.re hf0
    rw [Complex.ofReal_re, Complex.add_re, hW0] at hre
    have h2 : (((σ : ℂ)) * (((ceK * -(C_G * K_seed * liftEps c) : ℝ)) : ℂ)).re =
        σ * (ceK * -(C_G * K_seed * liftEps c)) := by
      rw [← Complex.ofReal_mul, Complex.ofReal_re]
    rw [h2] at hre
    have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> ring
    have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
    have hsr : σ * (liftSymbol (F_seed K_seed c) δ₀ 4 (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ))).re ≤
        C_orig * c ^ (-(5 / 6 : ℝ)) := by
      calc _ ≤ |σ * (liftSymbol _ _ _ _).re| := le_abs_self _
        _ = |σ| * |(liftSymbol _ _ _ _).re| := abs_mul _ _
        _ ≤ 1 * (C_orig * c ^ (-(5 / 6 : ℝ))) :=
            mul_le_mul hσabs.le ((Complex.abs_re_le_norm _).trans hWc13) (abs_nonneg _) zero_le_one
        _ = C_orig * c ^ (-(5 / 6 : ℝ)) := one_mul _
    have hc12_lt : C_orig * c ^ (-(1 / 2 : ℝ)) < ceK * C_G * K_seed / 2 := by
      have hsqrt_ge : 4 * C_orig / (ceK * C_G * K_seed) + 1 ≤ √c := by
        exact Real.le_sqrt_of_sq_le ((hc₁_orig.trans hc))
      have hc12_eq : c ^ (-(1 / 2 : ℝ)) = (√c)⁻¹ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hc0.le]
      have hsq_pos : 0 < √c := Real.sqrt_pos.mpr hc0
      have hlt : 4 * C_orig / (ceK * C_G * K_seed) < √c := by linarith
      rw [div_lt_iff₀ (by have := ceK_pos; positivity)] at hlt
      rw [hc12_eq, mul_inv_lt_iff₀ hsq_pos]
      have hC_nn : 0 ≤ C_orig := by dsimp [C_orig]; positivity
      have h42 : 2 * C_orig < √c * (ceK * C_G * K_seed) := by linarith
      calc C_orig < (√c * (ceK * C_G * K_seed)) / 2 := by linarith
        _ = ceK * C_G * K_seed / 2 * √c := by ring
    have hc56 : c ^ (-(5 / 6 : ℝ)) = liftEps c * c ^ (-(1 / 2 : ℝ)) := by
      unfold liftEps; rw [← Real.rpow_add hc0]; norm_num
    have hlt_orig : C_orig * c ^ (-(5 / 6 : ℝ)) < ceK * (C_G * K_seed * liftEps c) := by
      rw [hc56]
      calc C_orig * (liftEps c * c ^ (-(1 / 2 : ℝ))) = (C_orig * c ^ (-(1 / 2 : ℝ))) * liftEps c := by ring
        _ < (ceK * C_G * K_seed / 2) * liftEps c := mul_lt_mul_of_pos_right hc12_lt hε0
        _ = (ceK * (C_G * K_seed * liftEps c)) / 2 := by ring
        _ < ceK * (C_G * K_seed * liftEps c) :=
            half_lt_self (mul_pos (mul_pos ceK_pos hCG_pos) (by simpa [mul_assoc] using hKε_pos) |>.trans_eq (by ring))
    have e : ∀ w x : ℝ, σ * (w + σ * x) = σ * w + (σ * σ) * x := fun w x => by ring
    rw [hre, e, hσ2]
    linarith
  -- 2. Window site positivity
  have hwin_pos : ∀ t ∈ D.S, t ≠ D.tm → ∀ x : ℝ, |x - hankelLevel t c 0| ≤ R_off → 0 < f x := by
    intro t htS htm x hx_off
    obtain ⟨j, hj', hjt'⟩ := hS_site t htS htm
    have hKεδ := hKε_le_δ hKs1 hc2k hcδ
    have hsb := hseed_body 1 ⟨zero_le_one, le_rfl⟩ (K_seed * liftEps c) ⟨hKε_pos, hKεδ⟩ 0 (by simp)
    have hδ₀_pos : 0 < δ₀ := div_pos (mul_pos (mul_pos ceBeta1_pos (by linarith : 0 < K_seed)) hε0) two_pos
    refine hbCon_window_pos hR hc0 hc2 (hc₁_Bsh.trans hc) hB_sh hBt
      (Finset.le_sup' (fun t => |t|) htS) hx_off rfl
      (le_max_left _ _)
      ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans hKs_win) hKs1
      hCG_1 hCG_pos rfl hη_main le_rfl hCm rfl hC_err rfl hδ₀_pos hε0 hε1
      (hE.F_cont hKs1 hc2k hc8K hcδ) (fun y => hE.conv (hE.F_cont hKs1 hc2k hc8K hcδ) hδ₀_pos y)
      (fun u => (hF_seed_eq K_seed c u).trans (by rw [zero_mul, add_zero]))
      (fun u hu => hsb.2.2.2 j hj' u (by rw [hjt']; exact hu))
      (fun {ξ} hξ hSw => by simpa only [show δ₀ = ceBeta1 * K_seed * liftEps c / 2 from rfl] using he5_m hKs1 hc8K hcδ hc32 hξ hSw)
      (fun {ξ} hξ hSw => he5_d hKs1 hc32 hξ hSw) hfrep_dual
  -- 3. Tail ray positivity
  have htail_pos : ∀ x : ℝ, c / π ^ 2 + (|D.tm| / hankelBeta1) * c ^ (1 / 3 : ℝ) + K₀_tail ≤ x → 0 < f x := by
    intro x hx
    exact hbCon_tail_pos htm_neg hc0 hc2 (hc₁_Btl.trans hc) hB_tl hη_tail rfl rfl
      ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
      ((le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one))
      hε0 hε1 (fun {ξ} hξ hS => ho6 hKs_o6 (hc₁_o6.trans hc) hc8K hcδ hξ hS) hfrep_dual hx
  exact ⟨f, hfeig, horigin, hwin_pos, htail_pos⟩

/-- **Theorem O.9'** (`u1co:O9p`, `thm:hb-construction`, unconditional): for every `D : ShellHBData`,
smoothness parameter `κ ≥ 4`, and `R_off ≥ 0`, there exist `K > 0` and `c₁ ≥ 2` such that for all real
`c ≥ c₁` and either eigenvalue `σ = ±1`, there is `f ∈ 𝒜_c^σ` with `σ f(0) < 0`, `f > 0` on every
prescribed shell window `[T_j - R_off, T_j + R_off]` (`t_j ∈ D.S \ {D.tm}`), and `f > 0` on
`[c/π² + (|D.tm|/β₁) c^{1/3} + K, ∞)`. -/
theorem hbConstruction_proved (D : ShellHBData) : HbConstruction D := by
  intro _ _ R_off hR
  obtain ⟨K_p, c₁_p, hKp, hc₁p, hp⟩ := hbCon_sigma D R_off hR (Or.inl rfl)
  obtain ⟨K_m, c₁_m, hKm, hc₁m, hm⟩ := hbCon_sigma D R_off hR (Or.inr rfl)
  refine ⟨max K_p K_m, max c₁_p c₁_m, lt_max_of_lt_left hKp, (le_max_left _ _).trans' hc₁p,
    fun c hc σ hσ => ?_⟩
  rcases hσ with rfl | rfl
  · obtain ⟨f, hfeig, horig, hwin, htail⟩ := hp c ((le_max_left _ _).trans hc)
    exact ⟨f, hfeig, horig, hwin, fun x hx => htail x (le_trans (by gcongr; exact le_max_left _ _) hx)⟩
  · obtain ⟨f, hfeig, horig, hwin, htail⟩ := hm c ((le_max_right _ _).trans hc)
    exact ⟨f, hfeig, horig, hwin, fun x hx => htail x (le_trans (by gcongr; exact le_max_right _ _) hx)⟩

/-- info: 'FormalResearch.SignUncertainty.hbConstruction_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hbConstruction_proved

end FormalResearch.SignUncertainty
