/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpInnerBridge
public import FormalResearch.SignUncertainty.FctInnerSymbolsA
public import FormalResearch.SignUncertainty.FctInnerSymbolsMono
public import FormalResearch.SignUncertainty.FctInnerSymbolsG0Init

/-!
# Inner integral identities and `(fct:RI-bounds)` pointwise estimates for `fct:warp-asymp` (1)

Paper I (`constant_terms_five.tex`), Proposition FCT.5 (1), Step 2:
proves the three concrete inner pullback identities (`I_ε`, `∂_α I_ε`, `∂_{L₁} I_ε` on
`1 - outerChiOut`), establishes linearity of `fctS` on `FctSymCls` symbols and the cutoff tail
symbol class for `1 - chiExt`, and bounds the full-axis residuals `R_I(L₁, 0)` (`O(c^{-4/3})`),
`∂_{û} (N₀ I_ε) - i G₀'(û)` (`O(c^{-1/2})`), and `∂_{α̃} (N₀ I_ε) + i c₂* G₀''(û)` (`O(c^{-1/2})`)
uniformly over admissible `(L₁, α)`.

Class: proved, unconditional.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped Real ContDiff
open FormalResearch.CohnElkies
open FormalResearch.Special
open FormalResearch.Asymptotics
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctMoment
open FormalResearch.SignUncertainty.FctPhiKill
open FormalResearch.SignUncertainty.FctSymA

namespace FormalResearch.SignUncertainty

/-! ### 1. Exact inner pullback identities (`I_ε`, `∂_α I_ε`, `∂_{L₁} I_ε`) -/

private lemma tauD_pos : 0 < (fct_comp_D_part1 StripKernelChoice.star).choose :=
  (fct_comp_D_part1 StripKernelChoice.star).choose_spec.1

lemma vAlpha_one_inner {c t : ℝ} (hc0 : 0 < c)
    (hτD : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose)
    (ht : |t| ≤ 2 * c ^ (-(1 / 4 : ℝ))) :
    vAlpha 1 (c ^ (-(1 / 4 : ℝ))) t = t ^ 2 := by
  set τ₁ := c ^ (-(1 / 4 : ℝ))
  have hτ₁ : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hcτ : τ₁ ^ 4 * c = 1 := by
    have : τ₁ ^ 4 = c⁻¹ := by
      dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num [Real.rpow_neg_one]
    rw [this]; field_simp [hc0.ne']
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmain_D⟩ :=
    (fct_comp_D_part1 StripKernelChoice.star).choose_spec
  have hmain := hmain_D (K4 := 1) (c := c) (α := τ₁ ^ 2) (τ₁ := τ₁) le_rfl hc0 hτ₁ hτD hcτ
    (by rw [abs_of_nonneg (sq_nonneg _)])
  have hva : vAlpha (τ₁ ^ 2) τ₁ t = τ₁ ^ 2 * t ^ 2 := (hmain.2.2.2.2.2.1 t ht).2.2.1
  rw [vAlpha_eq_inv_mul (τ₁ ^ 2) τ₁ t (sq_pos_of_pos hτ₁).ne', hva]
  field_simp [(sq_pos_of_pos hτ₁).ne']

lemma concrete_adm_pk_half {K4 ε : ℝ} :
    ∃ c₀ : ℝ, max 100 ((30 * pbC0 + 1) ^ 2) ≤ c₀ ∧
      ∀ {c L1 α : ℝ}, c₀ ≤ c → (concreteInnerFamily K4 ε).adm c L1 α →
        ∀ u ∈ Icc (0 : ℝ) (fctUc c),
          ‖(L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c (concreteInnerV K4 ε c L1 α) u)‖ ≤ 1 / 2 := by
  let cbase : ℝ := max 100 ((30 * pbC0 + 1) ^ 2)
  obtain ⟨C_pk, c_pk, hCpk0, hc_pk, hPk⟩ := fctInner_phiKillDivM_sym pbKV_nonneg
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      cbase ≤ c ∧ c_pk ≤ c ∧ pbKV * c ^ (-(1 / 2 : ℝ)) ≤ 1e-3 ∧
      (8 + |ctTheta1 ε|) * C_pk * (4 : ℝ) ^ 6 * c ^ (-(3 / 2 : ℝ)) ≤ 1 / 2 := by
    refine Eventually.and (eventually_ge_atTop cbase)
      (Eventually.and (eventually_ge_atTop c_pk) (Eventually.and ?_ ?_))
    · have h0 : Tendsto (fun c : ℝ => pbKV * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul pbKV
      exact h0.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1e-3))
    · have h0 : Tendsto (fun c : ℝ => (8 + |ctTheta1 ε|) * C_pk * (4 : ℝ) ^ 6 * c ^ (-(3 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).const_mul _
      exact h0.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  refine ⟨max cbase c₀, le_max_left _ _, fun {c L1 α} hc hadm u hu => ?_⟩
  obtain ⟨hcbase, hcpk, hKV_bd, hhalf⟩ := hc₀ c ((le_max_right cbase c₀).trans hc)
  have hfacts := concrete_adm_facts hcbase hadm
  have hc0 : 0 < c := hfacts.1
  have h100 : 100 ≤ c := hfacts.2.1
  have hL1_bd : |L1| ≤ (8 + |ctTheta1 ε|) * c ^ (-(2 / 3 : ℝ)) := hfacts.2.2.2.2.2.2.2.1
  have hVjets : FctVJets pbKV c (concreteInnerV K4 ε c L1 α) := hfacts.2.2.2.2.2.2.2.2.2.1.1
  have hsym := hPk hcpk hVjets
  have h0 := hsym.2 0 (by norm_num) u hu
  rw [iteratedDerivWithin_zero] at h0
  have hu1 : 1 + u ≤ 4 * c ^ ((1 : ℝ) / 12) := by
    have h1c : (1 : ℝ) ≤ c ^ ((1 : ℝ) / 12) := Real.one_le_rpow (by linarith only [h100]) (by norm_num)
    have hu2 : u ≤ 2.96 * c ^ ((1 : ℝ) / 12) := hu.2
    linarith only [h1c, hu2]
  have hu6 : (1 + u) ^ (6 : ℝ) ≤ (4 : ℝ) ^ 6 * c ^ (1 / 2 : ℝ) := by
    calc (1 + u) ^ (6 : ℝ) ≤ (4 * c ^ ((1 : ℝ) / 12)) ^ (6 : ℝ) := by
          gcongr; linarith only [hu.1]
      _ = (4 : ℝ) ^ (6 : ℝ) * (c ^ ((1 : ℝ) / 12)) ^ (6 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hc0.le _)]
      _ = (4 : ℝ) ^ 6 * c ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul hc0.le, show ((6 : ℝ) = (6 : ℕ)) from by norm_num, Real.rpow_natCast]; norm_num
  have hpk_bd : ‖phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c (concreteInnerV K4 ε c L1 α) u)‖ ≤
      C_pk * (4 : ℝ) ^ 6 * c ^ (-(5 / 6 : ℝ)) := by
    calc ‖phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c (concreteInnerV K4 ε c L1 α) u)‖
        ≤ C_pk * c ^ (-(4 / 3 : ℝ)) * (1 + u) ^ ((6 : ℝ) - (0 : ℕ)) := h0
      _ = C_pk * c ^ (-(4 / 3 : ℝ)) * (1 + u) ^ (6 : ℝ) := by norm_num
      _ ≤ C_pk * c ^ (-(4 / 3 : ℝ)) * ((4 : ℝ) ^ 6 * c ^ (1 / 2 : ℝ)) := by gcongr
      _ = C_pk * (4 : ℝ) ^ 6 * (c ^ (-(4 / 3 : ℝ)) * c ^ (1 / 2 : ℝ)) := by ring
      _ = C_pk * (4 : ℝ) ^ 6 * c ^ (-(5 / 6 : ℝ)) := by
          rw [← Real.rpow_add hc0]; norm_num
  have hc_pow : c ^ (-(2 / 3 : ℝ)) * c ^ (-(5 / 6 : ℝ)) = c ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_add hc0]; norm_num
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |L1| * ‖phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c (concreteInnerV K4 ε c L1 α) u)‖
      ≤ ((8 + |ctTheta1 ε|) * c ^ (-(2 / 3 : ℝ))) * (C_pk * (4 : ℝ) ^ 6 * c ^ (-(5 / 6 : ℝ))) :=
        mul_le_mul hL1_bd hpk_bd (norm_nonneg _) (by positivity)
    _ = (8 + |ctTheta1 ε|) * C_pk * (4 : ℝ) ^ 6 * (c ^ (-(2 / 3 : ℝ)) * c ^ (-(5 / 6 : ℝ))) := by ring
    _ = (8 + |ctTheta1 ε|) * C_pk * (4 : ℝ) ^ 6 * c ^ (-(3 / 2 : ℝ)) := by rw [hc_pow]
    _ ≤ 1 / 2 := hhalf

private lemma adm_mu_cont {K4 ε c L1 α : ℝ} (_hK4 : 1 ≤ K4)
    (hB3 : FctInnerB3 (concreteInnerFamily K4 ε))
    (hc3 : hB3.choose_spec.choose ≤ c) (hadm : (concreteInnerFamily K4 ε).adm c L1 α) :
    ContinuousOn ((concreteInnerFamily K4 ε).mu c L1 α) (Icc 0 (fctUc c)) := by
  have hb3 := hB3.choose_spec.choose_spec c hc3 L1 α hadm
  have hc0 : 0 < c := hadm.1.2.2.1
  have h1 : ContinuousOn (fun u : ℝ =>
      (concreteInnerFamily K4 ε).mu c L1 α u - 1 -
        ((c ^ (-(2 / 3 : ℝ)) * α * (concreteInnerFamily K4 ε).c2 c L1 α * u ^ 2 : ℝ) : ℂ))
      (Icc 0 (fctUc c)) := hb3.1.continuousOn
  have h2 : ContinuousOn (fun u : ℝ =>
      (1 : ℂ) + ((c ^ (-(2 / 3 : ℝ)) * α * (concreteInnerFamily K4 ε).c2 c L1 α * u ^ 2 : ℝ) : ℂ))
      (Icc 0 (fctUc c)) := by fun_prop
  exact (h1.add h2).congr fun u _ => by dsimp only [Pi.add_def]; ring

private lemma fctInner_edgeAmp_pullback_eq {K4 ε c L1 α u : ℝ}
    (hK4 : 1 ≤ K4) (hc0 : 0 < c)
    (hτ1_14 : c ^ (-(1 / 4 : ℝ)) ≤ 1 / 8)
    (hτD : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose)
    (hKV : pbKV * c ^ (-(1 / 2 : ℝ)) ≤ 1e-3)
    (hadm : (concreteInnerFamily K4 ε).adm c L1 α)
    (hVjets : FctVJets pbKV c (concreteInnerV K4 ε c L1 α))
    (hVeq : ∀ Y ∈ Icc (0 : ℝ) 3.5, concreteInnerV K4 ε c L1 α Y =
      (concreteBoxS K4 ε c).V ((concreteEll1 ε c L1, (1 : ℝ), α), Y))
    (hu : u ∈ Ioo 0 (fctUc c))
    (hT_lt : fctInnerT c (concreteInnerV K4 ε c L1 α) u < 2 * c ^ (-(1 / 4 : ℝ))) :
    let V := concreteInnerV K4 ε c L1 α
    let T := fctInnerT c V
    let S := concreteBoxS K4 ε c
    let q := (concreteEll1 ε c L1, (1 : ℝ), α)
    let T' := (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) *
      (V (fctInnerY c u) + 2 * fctInnerY c u * fderiv ℝ S.V (q, fctInnerY c u) (0, 1))
    ((warpN0 c : ℝ) : ℂ) * concreteEdgeAmp K4 c L1 α (T u) * ((T' : ℝ) : ℂ) =
      ((warpNu K4 ε c L1 α : ℝ) : ℂ) * ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (concreteInnerFamily K4 ε).mu c L1 α u := by
  intro V T S q T'
  set τ₁ := c ^ (-(1 / 4 : ℝ))
  have hτ₁0 : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hY35 : fctInnerY c u ∈ Icc (0 : ℝ) 3.5 := by
    refine ⟨by dsimp only [fctInnerY]; have := hu.1; positivity, ?_⟩
    have h43 := fctB2_two_rpow_neg43_le
    have hc_pow : c ^ (-(1 / 6 : ℝ)) * (c ^ ((1 : ℝ) / 12)) ^ 2 = 1 := by
      rw [← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; norm_num
    have hu2 : u ^ 2 ≤ (2.96 * c ^ ((1 : ℝ) / 12)) ^ 2 := pow_le_pow_left₀ hu.1.le hu.2.le 2
    dsimp only [fctInnerY]
    calc (2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2
        ≤ 0.3969 * c ^ (-(1 / 6 : ℝ)) * (2.96 * c ^ ((1 : ℝ) / 12)) ^ 2 := by gcongr
      _ = (0.3969 * 2.96 ^ 2) * (c ^ (-(1 / 6 : ℝ)) * (c ^ ((1 : ℝ) / 12)) ^ 2) := by ring
      _ = 0.3969 * 2.96 ^ 2 := by rw [hc_pow, mul_one]
      _ ≤ 3.5 := by norm_num
  have hVY_pos : 0 < V (fctInnerY c u) := by
    have h0 := hVjets.2 0 (by norm_num) (fctInnerY c u) ⟨hY35.1, by linarith only [hY35.2]⟩
    rw [iteratedDerivWithin_zero] at h0
    have htau := (abs_le.mp (h0.trans hKV)).1
    have hwg : (1.06 : ℝ) ≤ (12 / π ^ 2) ^ (1 / 3 : ℝ) := warpTauStar_ge
    linarith only [htau, hwg]
  have hT_pos : 0 < T u := by
    dsimp only [T, fctInnerT]
    exact mul_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hc0 _)) hu.1) hVY_pos
  have hα_bd : |α| ≤ τ₁ ^ 2 := by
    have hc_sq : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
      dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    rw [hc_sq]; exact hadm.2.2.2
  rw [concreteEdgeAmp_inner hK4 hc0 hτD hα_bd hT_pos hT_lt.le]
  have hjac := fctInner_edge_jac_eq (K4 := K4) (ε := ε) (c := c) (L1 := L1) (α := α) (u := u)
    hc0 hτ1_14 hKV hVjets hVeq hu hT_lt
  have hpk : FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((T u : ℂ) * Complex.I) / (uctM (T u) : ℂ) =
      phiKillDivM (c ^ (-(1 / 12 : ℝ))) (T u) := by
    unfold phiKillDivM; simp only [hT_pos.ne', ↓reduceIte]
  simp_rw [mul_div_assoc, hpk]
  have hjac_c := congrArg (fun r : ℝ => (r : ℂ)) hjac
  dsimp only [concreteInnerFamily, q, S, T, V]
  calc ((warpN0 c : ℝ) : ℂ) *
        ((((π ^ 2 / 12 * Real.sqrt (uctMderiv (T u) / (2 * uctM (T u))) : ℝ) : ℂ)) *
          Complex.exp (-((K4 * (T u) ^ 4 : ℝ) : ℂ) +
            ((v1 StripKernelChoice.star K4 c τ₁ (T u) : ℝ) : ℂ) +
            ((α * (T u) ^ 2 : ℝ) : ℂ) + binetDiff c (Complex.I * (T u : ℂ))) *
          ((1 : ℂ) - (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) (T u))) *
        ((T' : ℝ) : ℂ)
      = ((warpN0 c * (π ^ 2 / 12) * Real.sqrt (uctMderiv (T u) / (2 * uctM (T u))) * T' : ℝ) : ℂ) *
          Complex.exp (-((K4 * (T u) ^ 4 : ℝ) : ℂ) +
            ((v1 StripKernelChoice.star K4 c τ₁ (T u) : ℝ) : ℂ) +
            ((α * (T u) ^ 2 : ℝ) : ℂ) + binetDiff c (Complex.I * (T u : ℂ))) *
          ((1 : ℂ) - (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) (T u)) := by
          push_cast; ring
    _ = ((warpNu K4 ε c L1 α * u ^ (-(1 / 2 : ℝ)) * Jfun S.V fctH ((c ^ (-(1 / 4 : ℝ))) ^ 2) (q, fctInnerY c u) : ℝ) : ℂ) *
          Complex.exp (-((K4 * (T u) ^ 4 : ℝ) : ℂ) +
            ((v1 StripKernelChoice.star K4 c τ₁ (T u) : ℝ) : ℂ) +
            ((α * (T u) ^ 2 : ℝ) : ℂ) + binetDiff c (Complex.I * (T u : ℂ))) *
          ((1 : ℂ) - (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) (T u)) := by
          rw [hjac_c]
    _ = ((warpNu K4 ε c L1 α : ℝ) : ℂ) * ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          (((Jfun S.V fctH (τ₁ ^ 2) (q, fctInnerY c u) : ℝ) : ℂ) *
            Complex.exp (-((K4 * (T u) ^ 4 : ℝ) : ℂ) +
              ((v1 StripKernelChoice.star K4 c τ₁ (T u) : ℝ) : ℂ) +
              ((α * (T u) ^ 2 : ℝ) : ℂ) + binetDiff c (Complex.I * (T u : ℂ))) *
            ((1 : ℂ) - (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) (T u))) := by
          push_cast; ring

lemma fctInner_warpI_in_eq {K4 ε : ℝ} (hK4 : 1 ≤ K4) :
    ∃ c₀ : ℝ, max 100 ((30 * pbC0 + 1) ^ 2) ≤ c₀ ∧
      ∀ {c L1 α : ℝ}, c₀ ≤ c → (concreteInnerFamily K4 ε).adm c L1 α →
        let S := concreteBoxS K4 ε c
        let V := concreteInnerV K4 ε c L1 α
        let û := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, α)
        ((warpN0 c : ℝ) : ℂ) * Complex.I *
            ∫ τ in Ioi (0 : ℝ), ((1 - outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrand K4 ε c L1 α τ =
          Complex.I * ((warpNu K4 ε c L1 α : ℝ) : ℂ) *
            fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
              (concreteInnerFamily K4 ε).mu c L1 α u)) := by
  let cbase : ℝ := max 100 ((30 * pbC0 + 1) ^ 2)
  have hB3 := concreteInnerB3 (K4 := K4) (ε := ε) hK4
  obtain ⟨C_χ, c_χ, hB2⟩ := fctInnerB2 outerChiIn_cutoff pbKV_nonneg
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      cbase ≤ c ∧ hB3.choose_spec.choose ≤ c ∧ c_χ ≤ c ∧
      c ^ (-(1 / 4 : ℝ)) ≤ 1 / 8 ∧
      c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose ∧
      pbKV * c ^ (-(1 / 2 : ℝ)) ≤ 1e-3 := by
    refine Eventually.and (eventually_ge_atTop cbase)
      (Eventually.and (eventually_ge_atTop hB3.choose_spec.choose)
        (Eventually.and (eventually_ge_atTop c_χ)
          (Eventually.and ?_ (Eventually.and ?_ ?_))))
    · have h0 : Tendsto (fun c : ℝ => c ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
        tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)
      exact h0.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
    · have h0 : Tendsto (fun c : ℝ => c ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
        tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)
      exact h0.eventually (Iic_mem_nhds tauD_pos)
    · have h0 : Tendsto (fun c : ℝ => pbKV * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul pbKV
      exact h0.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1e-3))
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  refine ⟨max cbase c₀, le_max_left _ _, fun {c L1 α} hc hadm => ?_⟩
  obtain ⟨hcbase, hc3, hcχ, hτ1_14, hτD, hKV⟩ := hc₀ c ((le_max_right cbase c₀).trans hc)
  have hfacts := concrete_adm_facts hcbase hadm
  have hvalid := hadm.1
  have hε := hvalid.2.1
  have hc0 := hfacts.1
  have hqΩ := hfacts.2.2.2.1
  have hVjets := hfacts.2.2.2.2.2.2.2.2.2.1.1
  have hVeq := hfacts.2.2.2.2.2.2.2.2.2.1.2
  have hb2 := hB2 c hcχ _ hVjets
  obtain ⟨hT_mono, hT_img, hT_lo, hT_deriv⟩ :=
    fctInnerT_deriv_and_image hc0 hKV hVjets hqΩ hVeq
  dsimp only
  set S := concreteBoxS K4 ε c
  set V := concreteInnerV K4 ε c L1 α
  set û := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, α)
  set f : ℝ → ℂ := fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) * (concreteInnerFamily K4 ε).mu c L1 α u
  have hf_cont : ContinuousOn f (Icc 0 (fctUc c)) :=
    (hb2.2.2.1.1.continuousOn).mul (adm_mu_cont hK4 hB3 hc3 hadm)
  have hS_lim := fctS_extUc_eq (c := c) (û := û) hc0 hf_cont
  rw [hS_lim.fctS_eq, fctInner_split_integral hc0 hT_mono hT_img hT_lo.1 hT_deriv]
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_const_mul]
  have heq : EqOn
      (fun u => ((warpN0 c : ℝ) : ℂ) * Complex.I * (((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        fctWarpIntegrand K4 ε c L1 α (fctInnerT c V u) *
        (((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) *
          (V (fctInnerY c u) + 2 * fctInnerY c u * fderiv ℝ S.V ((concreteEll1 ε c L1, 1, α), fctInnerY c u) (0, 1)) : ℝ) : ℂ)))
      (fun u => Complex.I * ((warpNu K4 ε c L1 α : ℝ) : ℂ) *
        (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
          (((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ))) * f u)))
      (Ioo 0 (fctUc c)) := by
    intro u hu
    dsimp only
    have hT_lt : fctInnerT c V u < 2 * c ^ (-(1 / 4 : ℝ)) :=
      lt_trans (hT_mono (Ioo_subset_Icc_self hu) ⟨(fctUc_pos hc0).le, le_rfl⟩ hu.2) hb2.2.1
    have hT_pos : 0 < fctInnerT c V u := by
      have hm := hT_img ▸ mem_image_of_mem (fctInnerT c V) hu
      exact hm.1
    have hph := fctInnerT_phase_eq hvalid hadm.2.1 hKV hVjets hVeq (Ioo_subset_Icc_self hu) hT_lt.le
    have hamp := fctInner_edgeAmp_pullback_eq hK4 hc0 hτ1_14 hτD hKV hadm hVjets hVeq hu hT_lt
    rw [fctWarpIntegrand_eq_edge hε hc0 hT_pos, hph]
    have hexp_eq : Complex.exp (Complex.I * ((-(û * u + u ^ 3 / 12) - π / 4 : ℝ) : ℂ)) =
        Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [hexp_eq]
    dsimp only [f]
    set T' : ℝ := (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) *
      (V (fctInnerY c u) + 2 * fctInnerY c u * fderiv ℝ S.V ((concreteEll1 ε c L1, 1, α), fctInnerY c u) (0, 1))
    calc ((warpN0 c : ℝ) : ℂ) * Complex.I *
          (((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
            (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
              Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ))) *
              concreteEdgeAmp K4 c L1 α (fctInnerT c V u)) * ((T' : ℝ) : ℂ))
        = Complex.I * ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
            (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
              Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)))) *
            (((warpN0 c : ℝ) : ℂ) * concreteEdgeAmp K4 c L1 α (fctInnerT c V u) * ((T' : ℝ) : ℂ)) := by ring
      _ = Complex.I * ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
            (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
              Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)))) *
            (((warpNu K4 ε c L1 α : ℝ) : ℂ) * ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              (concreteInnerFamily K4 ε).mu c L1 α u) := by rw [hamp]
      _ = Complex.I * ((warpNu K4 ε c L1 α : ℝ) : ℂ) *
            (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
              (((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ))) *
                (((fctInnerChi outerChiIn c V u : ℝ) : ℂ) * (concreteInnerFamily K4 ε).mu c L1 α u))) := by ring
  rw [setIntegral_congr_fun measurableSet_Ioo heq]

lemma fctInner_warpI_derivAlpha_in_eq {K4 ε : ℝ} (hK4 : 1 ≤ K4) :
    ∃ c₀ : ℝ, max 100 ((30 * pbC0 + 1) ^ 2) ≤ c₀ ∧
      ∀ {c L1 α : ℝ}, c₀ ≤ c → (concreteInnerFamily K4 ε).adm c L1 α →
        let S := concreteBoxS K4 ε c
        let V := concreteInnerV K4 ε c L1 α
        let û := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, α)
        ((c ^ (2 / 3 : ℝ) * warpN0 c : ℝ) : ℂ) * Complex.I *
            ∫ τ in Ioi (0 : ℝ), ((1 - outerChiOut c τ : ℝ) : ℂ) *
              fctWarpIntegrandDerivAlpha K4 ε c L1 α τ =
          Complex.I * ((warpNu K4 ε c L1 α : ℝ) : ℂ) *
            fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
              (((warpC2Star * u ^ 2 : ℝ) : ℂ) + (concreteInnerFamily K4 ε).eB c L1 α u) *
              (concreteInnerFamily K4 ε).mu c L1 α u)) := by
  let cbase : ℝ := max 100 ((30 * pbC0 + 1) ^ 2)
  have hB3 := concreteInnerB3 (K4 := K4) (ε := ε) hK4
  have hB4 := concreteInnerB4 (K4 := K4) (ε := ε)
  obtain ⟨C_χ, c_χ, hB2⟩ := fctInnerB2 outerChiIn_cutoff pbKV_nonneg
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      cbase ≤ c ∧ hB3.choose_spec.choose ≤ c ∧ hB4.choose_spec.choose ≤ c ∧ c_χ ≤ c ∧
      c ^ (-(1 / 4 : ℝ)) ≤ 1 / 8 ∧
      c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose ∧
      pbKV * c ^ (-(1 / 2 : ℝ)) ≤ 1e-3 := by
    refine Eventually.and (eventually_ge_atTop cbase)
      (Eventually.and (eventually_ge_atTop hB3.choose_spec.choose)
        (Eventually.and (eventually_ge_atTop hB4.choose_spec.choose)
          (Eventually.and (eventually_ge_atTop c_χ)
            (Eventually.and ?_ (Eventually.and ?_ ?_)))))
    · have h0 : Tendsto (fun c : ℝ => c ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
        tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)
      exact h0.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
    · have h0 : Tendsto (fun c : ℝ => c ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
        tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)
      exact h0.eventually (Iic_mem_nhds tauD_pos)
    · have h0 : Tendsto (fun c : ℝ => pbKV * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul pbKV
      exact h0.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1e-3))
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  refine ⟨max cbase c₀, le_max_left _ _, fun {c L1 α} hc hadm => ?_⟩
  obtain ⟨hcbase, hc3, hc4, hcχ, hτ1_14, hτD, hKV⟩ := hc₀ c ((le_max_right cbase c₀).trans hc)
  have hfacts := concrete_adm_facts hcbase hadm
  have hvalid := hadm.1
  have hε := hvalid.2.1
  have hc0 := hfacts.1
  have hqΩ := hfacts.2.2.2.1
  have hVjets := hfacts.2.2.2.2.2.2.2.2.2.1.1
  have hVeq := hfacts.2.2.2.2.2.2.2.2.2.1.2
  have hb2 := hB2 c hcχ _ hVjets
  have hb4 := hB4.choose_spec.choose_spec c hc4 L1 α hadm
  obtain ⟨hT_mono, hT_img, hT_lo, hT_deriv⟩ :=
    fctInnerT_deriv_and_image hc0 hKV hVjets hqΩ hVeq
  dsimp only
  set S := concreteBoxS K4 ε c
  set V := concreteInnerV K4 ε c L1 α
  set û := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, α)
  set f : ℝ → ℂ := fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
    (((warpC2Star * u ^ 2 : ℝ) : ℂ) + (concreteInnerFamily K4 ε).eB c L1 α u) *
    (concreteInnerFamily K4 ε).mu c L1 α u
  have hf_cont : ContinuousOn f (Icc 0 (fctUc c)) := by
    have hpoly : ContinuousOn (fun u : ℝ => ((warpC2Star * u ^ 2 : ℝ) : ℂ) + (concreteInnerFamily K4 ε).eB c L1 α u)
        (Icc 0 (fctUc c)) := (by fun_prop : Continuous (fun u : ℝ => ((warpC2Star * u ^ 2 : ℝ) : ℂ))).continuousOn.add
      hb4.1.1.continuousOn
    exact ((hb2.2.2.1.1.continuousOn).mul hpoly).mul (adm_mu_cont hK4 hB3 hc3 hadm)
  have hS_lim := fctS_extUc_eq (c := c) (û := û) hc0 hf_cont
  rw [hS_lim.fctS_eq, fctInner_split_integral hc0 hT_mono hT_img hT_lo.1 hT_deriv]
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_const_mul]
  have heq : EqOn
      (fun u => ((c ^ (2 / 3 : ℝ) * warpN0 c : ℝ) : ℂ) * Complex.I *
        (((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
          fctWarpIntegrandDerivAlpha K4 ε c L1 α (fctInnerT c V u) *
          (((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) *
            (V (fctInnerY c u) + 2 * fctInnerY c u * fderiv ℝ S.V ((concreteEll1 ε c L1, 1, α), fctInnerY c u) (0, 1)) : ℝ) : ℂ)))
      (fun u => Complex.I * ((warpNu K4 ε c L1 α : ℝ) : ℂ) *
        (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
          (((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ))) * f u)))
      (Ioo 0 (fctUc c)) := by
    intro u hu
    dsimp only
    have hT_lt : fctInnerT c V u < 2 * c ^ (-(1 / 4 : ℝ)) :=
      lt_trans (hT_mono (Ioo_subset_Icc_self hu) ⟨(fctUc_pos hc0).le, le_rfl⟩ hu.2) hb2.2.1
    have hT_pos : 0 < fctInnerT c V u := (hT_img ▸ mem_image_of_mem (fctInnerT c V) hu).1
    have hph := fctInnerT_phase_eq hvalid hadm.2.1 hKV hVjets hVeq (Ioo_subset_Icc_self hu) hT_lt.le
    have hamp := fctInner_edgeAmp_pullback_eq hK4 hc0 hτ1_14 hτD hKV hadm hVjets hVeq hu hT_lt
    have hvα : vAlpha 1 (c ^ (-(1 / 4 : ℝ))) (fctInnerT c V u) = (fctInnerT c V u) ^ 2 :=
      vAlpha_one_inner hc0 hτD (by rw [abs_of_pos hT_pos]; exact hT_lt.le)
    have heB := concrete_eB_id (K4 := K4) (ε := ε) (c := c) (L1 := L1) (α := α) (u := u) hc0
    rw [fctWarpIntegrandDerivAlpha_eq_edge hε hc0 hT_pos, hph, hvα]
    have hexp_eq : Complex.exp (Complex.I * ((-(û * u + u ^ 3 / 12) - π / 4 : ℝ) : ℂ)) =
        Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [hexp_eq]
    dsimp only [f]
    set T' : ℝ := (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) *
      (V (fctInnerY c u) + 2 * fctInnerY c u * fderiv ℝ S.V ((concreteEll1 ε c L1, 1, α), fctInnerY c u) (0, 1))
    calc ((c ^ (2 / 3 : ℝ) * warpN0 c : ℝ) : ℂ) * Complex.I *
          (((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
            (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
              Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ))) *
              concreteEdgeAmp K4 c L1 α (fctInnerT c V u) *
              (((fctInnerT c V u) ^ 2 : ℝ) +
                Complex.I * ((fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) (fctInnerT c V u) : ℝ) : ℂ))) * ((T' : ℝ) : ℂ))
        = Complex.I * ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
            (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
              Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)))) *
            (((warpN0 c : ℝ) : ℂ) * concreteEdgeAmp K4 c L1 α (fctInnerT c V u) * ((T' : ℝ) : ℂ)) *
            (((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
              (((fctInnerT c V u) ^ 2 : ℝ) +
                Complex.I * ((fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) (fctInnerT c V u) : ℝ) : ℂ))) := by
            push_cast; ring
      _ = Complex.I * ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
            (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
              Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)))) *
            (((warpNu K4 ε c L1 α : ℝ) : ℂ) * ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              (concreteInnerFamily K4 ε).mu c L1 α u) *
            ((((warpC2Star * u ^ 2 : ℝ) : ℂ) + (concreteInnerFamily K4 ε).eB c L1 α u)) := by
            rw [hamp]; erw [heB]; dsimp only [warpC2Star, warpTauStar]
      _ = Complex.I * ((warpNu K4 ε c L1 α : ℝ) : ℂ) *
            (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
              (((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ))) *
                (((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
                  (((warpC2Star * u ^ 2 : ℝ) : ℂ) + (concreteInnerFamily K4 ε).eB c L1 α u) *
                  (concreteInnerFamily K4 ε).mu c L1 α u))) := by ring
  rw [setIntegral_congr_fun measurableSet_Ioo heq]

lemma fctInner_warpI_derivL_in_eq {K4 ε : ℝ} (hK4 : 1 ≤ K4) :
    ∃ c₀ : ℝ, max 100 ((30 * pbC0 + 1) ^ 2) ≤ c₀ ∧
      ∀ {c L1 α : ℝ}, c₀ ≤ c → (concreteInnerFamily K4 ε).adm c L1 α →
        let S := concreteBoxS K4 ε c
        let V := concreteInnerV K4 ε c L1 α
        let û := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, α)
        let uL := -fctKappa c * S.V ((concreteEll1 ε c L1, 1, α), S.A (concreteEll1 ε c L1, 1, α))
        ((warpN0 c / uL : ℝ) : ℂ) * Complex.I *
            ∫ τ in Ioi (0 : ℝ), ((1 - outerChiOut c τ : ℝ) : ℂ) *
              fctWarpIntegrandDerivL K4 ε c L1 α τ =
          Complex.I * ((warpNu K4 ε c L1 α : ℝ) : ℂ) *
            fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
              (-(Complex.I * (u : ℂ)) + (concreteInnerFamily K4 ε).eA c L1 α u) *
              (concreteInnerFamily K4 ε).mu c L1 α u)) := by
  let cbase : ℝ := max 100 ((30 * pbC0 + 1) ^ 2)
  have hB3 := concreteInnerB3 (K4 := K4) (ε := ε) hK4
  have hB4 := concreteInnerB4 (K4 := K4) (ε := ε)
  obtain ⟨C_χ, c_χ, hB2⟩ := fctInnerB2 outerChiIn_cutoff pbKV_nonneg
  obtain ⟨c_pk, hc_pk_base, hpk_half⟩ := concrete_adm_pk_half (K4 := K4) (ε := ε)
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      cbase ≤ c ∧ hB3.choose_spec.choose ≤ c ∧ hB4.choose_spec.choose ≤ c ∧
      c_χ ≤ c ∧ c_pk ≤ c ∧
      c ^ (-(1 / 4 : ℝ)) ≤ 1 / 8 ∧
      c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose ∧
      pbKV * c ^ (-(1 / 2 : ℝ)) ≤ 1e-3 ∧
      pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) ≤ 0.5 := by
    refine Eventually.and (eventually_ge_atTop cbase)
      (Eventually.and (eventually_ge_atTop hB3.choose_spec.choose)
        (Eventually.and (eventually_ge_atTop hB4.choose_spec.choose)
          (Eventually.and (eventually_ge_atTop c_χ)
            (Eventually.and (eventually_ge_atTop c_pk)
              (Eventually.and ?_ (Eventually.and ?_ (Eventually.and ?_ ?_)))))))
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually (Iic_mem_nhds tauD_pos)
    · have h0 : Tendsto (fun c : ℝ => pbKV * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul pbKV
      exact h0.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1e-3))
    · have h0 : Tendsto (fun c : ℝ => pbcV * pbC0 * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (pbcV * pbC0)
      exact h0.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 0.5))
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  refine ⟨max cbase c₀, le_max_left _ _, fun {c L1 α} hc hadm => ?_⟩
  obtain ⟨hcbase, hc3, hc4, hcχ, hcpk, hτ1_14, hτD, hKV, hVA_small⟩ := hc₀ c ((le_max_right cbase c₀).trans hc)
  have hfacts := concrete_adm_facts hcbase hadm
  have hvalid := hadm.1
  have hε := hvalid.2.1
  have hc0 := hfacts.1
  have hqΩ := hfacts.2.2.2.1
  have hVjets := hfacts.2.2.2.2.2.2.2.2.2.1.1
  have hVeq := hfacts.2.2.2.2.2.2.2.2.2.1.2
  have hVA_diff := hfacts.2.2.2.2.2.2.2.2.2.2.1
  have hVA_ne : (concreteBoxS K4 ε c).V ((concreteEll1 ε c L1, (1 : ℝ), α),
      (concreteBoxS K4 ε c).A (concreteEll1 ε c L1, (1 : ℝ), α)) ≠ 0 := by
    have htau := (abs_le.mp (hVA_diff.trans hVA_small)).1
    have hwg : (1.06 : ℝ) ≤ warpTauStar := warpTauStar_ge
    unfold warpTauStar at hwg
    linarith only [htau, hwg]
  have hb2 := hB2 c hcχ _ hVjets
  have hb4 := hB4.choose_spec.choose_spec c hc4 L1 α hadm
  obtain ⟨hT_mono, hT_img, hT_lo, hT_deriv⟩ :=
    fctInnerT_deriv_and_image hc0 hKV hVjets hqΩ hVeq
  dsimp only
  set S := concreteBoxS K4 ε c
  set V := concreteInnerV K4 ε c L1 α
  set û := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, α)
  set uL := -fctKappa c * S.V ((concreteEll1 ε c L1, 1, α), S.A (concreteEll1 ε c L1, 1, α))
  set f : ℝ → ℂ := fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
    (-(Complex.I * (u : ℂ)) + (concreteInnerFamily K4 ε).eA c L1 α u) *
    (concreteInnerFamily K4 ε).mu c L1 α u
  have hf_cont : ContinuousOn f (Icc 0 (fctUc c)) := by
    have hlin : ContinuousOn (fun u : ℝ => -(Complex.I * (u : ℂ)) + (concreteInnerFamily K4 ε).eA c L1 α u)
        (Icc 0 (fctUc c)) :=
      (by fun_prop : Continuous (fun u : ℝ => -(Complex.I * (u : ℂ)))).continuousOn.add hb4.2.1.continuousOn
    exact ((hb2.2.2.1.1.continuousOn).mul hlin).mul (adm_mu_cont hK4 hB3 hc3 hadm)
  have hS_lim := fctS_extUc_eq (c := c) (û := û) hc0 hf_cont
  rw [hS_lim.fctS_eq, fctInner_split_integral hc0 hT_mono hT_img hT_lo.1 hT_deriv]
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_const_mul]
  have huL_ne : uL ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (fctKappa_pos hc0).ne') hVA_ne
  have heq : EqOn
      (fun u => ((warpN0 c / uL : ℝ) : ℂ) * Complex.I *
        (((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
          fctWarpIntegrandDerivL K4 ε c L1 α (fctInnerT c V u) *
          (((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) *
            (V (fctInnerY c u) + 2 * fctInnerY c u * fderiv ℝ S.V ((concreteEll1 ε c L1, 1, α), fctInnerY c u) (0, 1)) : ℝ) : ℂ)))
      (fun u => Complex.I * ((warpNu K4 ε c L1 α : ℝ) : ℂ) *
        (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
          (((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ))) * f u)))
      (Ioo 0 (fctUc c)) := by
    intro u hu
    dsimp only
    have hT_lt : fctInnerT c V u < 2 * c ^ (-(1 / 4 : ℝ)) :=
      lt_trans (hT_mono (Ioo_subset_Icc_self hu) ⟨(fctUc_pos hc0).le, le_rfl⟩ hu.2) hb2.2.1
    have hT_pos : 0 < fctInnerT c V u := (hT_img ▸ mem_image_of_mem (fctInnerT c V) hu).1
    have hph := fctInnerT_phase_eq hvalid hadm.2.1 hKV hVjets hVeq (Ioo_subset_Icc_self hu) hT_lt.le
    have hamp := fctInner_edgeAmp_pullback_eq hK4 hc0 hτ1_14 hτD hKV hadm hVjets hVeq hu hT_lt
    have hpk_half_u := hpk_half hcpk hadm u (Ioo_subset_Icc_self hu)
    have hden_ne : (1 : ℂ) - (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c V u) ≠ 0 := by
      intro hz
      have h1 : (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c V u) = 1 :=
        (sub_eq_zero.mp hz).symm
      rw [h1, norm_one] at hpk_half_u
      linarith
    have hpk : FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((fctInnerT c V u : ℂ) * Complex.I) /
        (uctM (fctInnerT c V u) : ℂ) = phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c V u) := by
      unfold phiKillDivM; simp only [hT_pos.ne', ↓reduceIte]
    have heA := concrete_eA_id (K4 := K4) (ε := ε) (c := c) (L1 := L1) (α := α) (u := u) hc0 hVA_ne
    have hexp_eq : Complex.exp (Complex.I * ((-(û * u + u ^ 3 / 12) - π / 4 : ℝ) : ℂ)) =
        Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hbase_alg : concreteEdgeAmpBase K4 c α (fctInnerT c V u) *
        (Complex.I * ((c * fctInnerT c V u : ℝ) : ℂ) *
            ((1 : ℂ) - (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c V u)) -
          phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c V u)) / (uL : ℂ) =
        concreteEdgeAmp K4 c L1 α (fctInnerT c V u) *
          ((Complex.I * ((c * fctInnerT c V u : ℝ) : ℂ) -
            phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c V u) /
              ((1 : ℂ) - (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c V u))) / (uL : ℂ)) := by
      rw [concreteEdgeAmp_eq_base_mul]; simp_rw [mul_div_assoc, hpk]
      field_simp [hden_ne, Complex.ofReal_ne_zero.mpr huL_ne]
    rw [fctWarpIntegrandDerivL_eq_edge hε hc0 hT_pos, hph, hexp_eq]; simp_rw [mul_div_assoc, hpk]
    dsimp only [f]
    set T' : ℝ := (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) *
      (V (fctInnerY c u) + 2 * fctInnerY c u * fderiv ℝ S.V ((concreteEll1 ε c L1, 1, α), fctInnerY c u) (0, 1))
    calc ((warpN0 c / uL : ℝ) : ℂ) * Complex.I *
          (((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
            ((Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
                Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)))) *
              concreteEdgeAmpBase K4 c α (fctInnerT c V u) *
              (Complex.I * ((c * fctInnerT c V u : ℝ) : ℂ) *
                  ((1 : ℂ) - (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c V u)) -
                phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c V u))) * ((T' : ℝ) : ℂ))
        = Complex.I * ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
            (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
              Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)))) *
            (((warpN0 c : ℝ) : ℂ) *
              (concreteEdgeAmpBase K4 c α (fctInnerT c V u) *
                (Complex.I * ((c * fctInnerT c V u : ℝ) : ℂ) *
                    ((1 : ℂ) - (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c V u)) -
                  phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c V u)) / (uL : ℂ)) * ((T' : ℝ) : ℂ)) := by
            rw [Complex.ofReal_div]
            field_simp [Complex.ofReal_ne_zero.mpr huL_ne]
      _ = Complex.I * ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
            (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
              Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)))) *
            (((warpN0 c : ℝ) : ℂ) * concreteEdgeAmp K4 c L1 α (fctInnerT c V u) * ((T' : ℝ) : ℂ)) *
            ((Complex.I * ((c * fctInnerT c V u : ℝ) : ℂ) -
              phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c V u) /
                ((1 : ℂ) - (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c V u))) / (uL : ℂ)) := by
            rw [hbase_alg]; ring
      _ = Complex.I * ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
            (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
              Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)))) *
            (((warpNu K4 ε c L1 α : ℝ) : ℂ) * ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              (concreteInnerFamily K4 ε).mu c L1 α u) *
            (-(Complex.I * (u : ℂ)) + (concreteInnerFamily K4 ε).eA c L1 α u) := by
            rw [hamp]; dsimp only at heA; rw [heA]
      _ = Complex.I * ((warpNu K4 ε c L1 α : ℝ) : ℂ) *
            (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
              (((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ))) *
                (((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
                  (-(Complex.I * (u : ℂ)) + (concreteInnerFamily K4 ε).eA c L1 α u) *
                  (concreteInnerFamily K4 ε).mu c L1 α u))) := by ring
  rw [setIntegral_congr_fun measurableSet_Ioo heq]

/-! ### 2. `fctS` linearity on `FctSymCls` and cutoff tail bounds -/

private lemma integrableOn_fctSEps_of_symCls {û ε : ℝ} {n : ℕ} {p B : ℝ} {κ : ℝ → ℂ}
    (hε : 0 < ε) (hB : 0 ≤ B) (hκ : FctSymCls n p B κ) :
    IntegrableOn (fun u : ℝ =>
      ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ)) * κ u)
      (Ioi (0 : ℝ)) := by
  have hp_ge : 0 ≤ max p 0 := le_max_right _ _
  have hm0 : AEStronglyMeasurable (fun u : ℝ =>
      ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ)) * κ u)
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have hrpow : ContinuousOn (fun u : ℝ => ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (Ioi 0) :=
      Complex.continuous_ofReal.comp_continuousOn (continuousOn_id.rpow_const fun x hx => Or.inl hx.ne')
    have hexp : Continuous (fun u : ℝ =>
        Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ))) := by fun_prop
    exact (hrpow.mul hexp.continuousOn).mul (hκ.1.continuousOn.mono Ioi_subset_Ici_self)
  have h1 : IntegrableOn (fun u : ℝ =>
      ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ)) * κ u)
      (Ioc (0 : ℝ) 1) := by
    have hMaj : IntegrableOn (fun u : ℝ => (B * (2 : ℝ) ^ max p 0) * u ^ (-(1 / 2 : ℝ))) (Ioc 0 1) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by norm_num))).const_mul _
    refine hMaj.mono' (hm0.mono_set Ioc_subset_Ioi_self) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hu.1.le _),
      Complex.norm_exp]
    have hre : (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ)).re = -(ε * u ^ 2) := by
      rw [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re]; ring
    have hexp1 : Real.exp (-(ε * u ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hε, sq_nonneg u])
    have hκ0 := hκ.2 0 (Nat.zero_le _) u hu.1.le
    rw [iteratedDerivWithin_zero, Nat.cast_zero, sub_zero] at hκ0
    have hp_le : (1 + u) ^ p ≤ (2 : ℝ) ^ max p 0 :=
      (Real.rpow_le_rpow_of_exponent_le (by linarith only [hu.1]) (le_max_left p 0)).trans
        (Real.rpow_le_rpow (by linarith only [hu.1]) (by linarith only [hu.2]) hp_ge)
    rw [hre]
    calc u ^ (-(1 / 2 : ℝ)) * Real.exp (-(ε * u ^ 2)) * ‖κ u‖
        ≤ u ^ (-(1 / 2 : ℝ)) * 1 * (B * (1 + u) ^ p) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp1 (Real.rpow_nonneg hu.1.le _)) hκ0 (norm_nonneg _)
            (mul_nonneg (Real.rpow_nonneg hu.1.le _) zero_le_one)
      _ ≤ u ^ (-(1 / 2 : ℝ)) * 1 * (B * (2 : ℝ) ^ max p 0) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp_le hB) (mul_nonneg (Real.rpow_nonneg hu.1.le _) zero_le_one)
      _ = (B * (2 : ℝ) ^ max p 0) * u ^ (-(1 / 2 : ℝ)) := by ring
  have h2 : IntegrableOn (fun u : ℝ =>
      ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ)) * κ u)
      (Ioi (1 : ℝ)) := by
    have hMaj : IntegrableOn (fun u : ℝ => (B * (2 : ℝ) ^ max p 0) *
        (u ^ (max p 0 - 1 / 2 : ℝ) * Real.exp (-ε * u ^ 2))) (Ioi 1) :=
      ((integrableOn_rpow_mul_exp_neg_mul_sq hε (by linarith only [hp_ge])).mono_set
        (Ioi_subset_Ioi zero_le_one)).const_mul _
    refine hMaj.mono' (hm0.mono_set (Ioi_subset_Ioi zero_le_one)) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    have hu1 : (1 : ℝ) < u := hu
    have hu0 : (0 : ℝ) < u := by linarith only [hu1]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hu0.le _),
      Complex.norm_exp]
    have hre : (-(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ)).re = -ε * u ^ 2 := by
      rw [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re]; ring
    have hκ0 := hκ.2 0 (Nat.zero_le _) u hu0.le
    rw [iteratedDerivWithin_zero, Nat.cast_zero, sub_zero] at hκ0
    have hp_le : (1 + u) ^ p ≤ (2 : ℝ) ^ max p 0 * u ^ max p 0 := by
      calc (1 + u) ^ p ≤ (1 + u) ^ max p 0 :=
            Real.rpow_le_rpow_of_exponent_le (by linarith only [hu0]) (le_max_left p 0)
        _ ≤ (2 * u) ^ max p 0 :=
            Real.rpow_le_rpow (by linarith only [hu0]) (by linarith only [hu1]) hp_ge
        _ = (2 : ℝ) ^ max p 0 * u ^ max p 0 := Real.mul_rpow (by norm_num) hu0.le
    have hpow : u ^ (-(1 / 2 : ℝ)) * u ^ max p 0 = u ^ (max p 0 - 1 / 2 : ℝ) := by
      rw [← Real.rpow_add hu0]; ring_nf
    rw [hre]
    calc u ^ (-(1 / 2 : ℝ)) * Real.exp (-ε * u ^ 2) * ‖κ u‖
        ≤ u ^ (-(1 / 2 : ℝ)) * Real.exp (-ε * u ^ 2) * (B * ((2 : ℝ) ^ max p 0 * u ^ max p 0)) :=
          mul_le_mul_of_nonneg_left (hκ0.trans (mul_le_mul_of_nonneg_left hp_le hB)) (by positivity)
      _ = (B * (2 : ℝ) ^ max p 0) * ((u ^ (-(1 / 2 : ℝ)) * u ^ max p 0) * Real.exp (-ε * u ^ 2)) := by ring
      _ = (B * (2 : ℝ) ^ max p 0) * (u ^ (max p 0 - 1 / 2 : ℝ) * Real.exp (-ε * u ^ 2)) := by rw [hpow]
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext x; simp only [mem_union, mem_Ioc, mem_Ioi]; exact ⟨fun h => h.elim (fun a => a.1) (fun a => by linarith),
      fun hx => le_or_gt x 1 |>.imp (fun h => ⟨hx, h⟩) id⟩
  rw [← hunion]
  exact h1.union h2

lemma fctSLimit_add {û : ℝ} {n₁ n₂ : ℕ} {p₁ p₂ B₁ B₂ : ℝ} {κ₁ κ₂ : ℝ → ℂ} {L₁ L₂ : ℂ}
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hκ₁ : FctSymCls n₁ p₁ B₁ κ₁) (hκ₂ : FctSymCls n₂ p₂ B₂ κ₂)
    (hL₁ : FctSLimit û κ₁ L₁) (hL₂ : FctSLimit û κ₂ L₂) :
    FctSLimit û (fun u => κ₁ u + κ₂ u) (L₁ + L₂) := by
  have heq : ∀ᶠ ε : ℝ in 𝓝[>] 0, fctSEps û ε κ₁ + fctSEps û ε κ₂ = fctSEps û ε (fun u => κ₁ u + κ₂ u) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have h1 := integrableOn_fctSEps_of_symCls (û := û) hε hB₁ hκ₁
    have h2 := integrableOn_fctSEps_of_symCls (û := û) hε hB₂ hκ₂
    simp only [fctSEps, ← mul_add]
    congr 1
    rw [← MeasureTheory.integral_add h1 h2]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_; ring
  exact (hL₁.add hL₂).congr' heq

lemma fctSLimit_sub {û : ℝ} {n₁ n₂ : ℕ} {p₁ p₂ B₁ B₂ : ℝ} {κ₁ κ₂ : ℝ → ℂ} {L₁ L₂ : ℂ}
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hκ₁ : FctSymCls n₁ p₁ B₁ κ₁) (hκ₂ : FctSymCls n₂ p₂ B₂ κ₂)
    (hL₁ : FctSLimit û κ₁ L₁) (hL₂ : FctSLimit û κ₂ L₂) :
    FctSLimit û (fun u => κ₁ u - κ₂ u) (L₁ - L₂) := by
  have heq : ∀ᶠ ε : ℝ in 𝓝[>] 0, fctSEps û ε κ₁ - fctSEps û ε κ₂ = fctSEps û ε (fun u => κ₁ u - κ₂ u) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have h1 := integrableOn_fctSEps_of_symCls (û := û) hε hB₁ hκ₁
    have h2 := integrableOn_fctSEps_of_symCls (û := û) hε hB₂ hκ₂
    simp only [fctSEps, ← mul_sub]
    congr 1
    rw [← MeasureTheory.integral_sub h1 h2]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_; ring
  exact (hL₁.sub hL₂).congr' heq

lemma fctSLimit_const_mul {û : ℝ} (c₀ : ℂ) {κ : ℝ → ℂ} {L : ℂ} (hL : FctSLimit û κ L) :
    FctSLimit û (fun u => c₀ * κ u) (c₀ * L) := by
  have heq : ∀ ε : ℝ, c₀ * fctSEps û ε κ = fctSEps û ε (fun u => c₀ * κ u) := fun ε => by
    simp only [fctSEps]
    rw [← mul_assoc, mul_comm c₀ _, mul_assoc, ← MeasureTheory.integral_const_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_; ring
  exact (hL.const_mul c₀).congr' (Eventually.of_forall heq)

lemma one_sub_chiExt_symCls {c C_χ : ℝ} {V : ℝ → ℝ} (hc : 1 ≤ c) (_hCχ : 0 ≤ C_χ)
    (hχ_sym : FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_χ (fun u => ((1 - fctInnerChi outerChiIn c V u : ℝ) : ℂ)))
    (hχ_zero : ∀ u ∈ Icc (2.95 * c ^ ((1 : ℝ) / 12)) (fctUc c), fctInnerChi outerChiIn c V u = 0) :
    FctSymCls 8 0 (max C_χ 1) (fun u => 1 - chiExt c V u) := by
  have hc0 : 0 < c := by linarith
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  have hDi : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  set ucut : ℝ := 2.95 * c ^ ((1 : ℝ) / 12)
  have hucut_pos : 0 < ucut := by positivity
  have hucut_lt : ucut < fctUc c := by dsimp only [ucut, fctUc]; linarith [Real.rpow_pos_of_pos hc0 ((1 : ℝ) / 12)]
  have hIco_eq : Ici (0 : ℝ) ∩ Ioo (-1 : ℝ) (fctUc c) = Ico (0 : ℝ) (fctUc c) := by
    ext x; simp only [mem_inter_iff, mem_Ici, mem_Ioo, mem_Ico]
    exact ⟨fun ⟨hx0, _, hxc⟩ => ⟨hx0, hxc⟩, fun ⟨hx0, hxc⟩ => ⟨hx0, by linarith only [hx0], hxc⟩⟩
  have h1_oi : ∀ x ∈ Ioi ucut, 1 - chiExt c V x = 1 := by
    intro x hx
    rcases le_or_gt x (fctUc c) with hxle | hxgt
    · have hc0' : chiExt c V x = 0 := by simp [chiExt, extUc, hxle, hχ_zero x ⟨hx.out.le, hxle⟩]
      rw [hc0', sub_zero]
    · simp [chiExt, extUc_zero_of_gt _ hxgt]
  have hcd_oi : ContDiffOn ℝ (8 : ℕ) (fun u => 1 - chiExt c V u) (Ioi ucut) :=
    (contDiffOn_const (c := (1 : ℂ))).congr (fun x hx => h1_oi x hx)
  have hcd_loc : ∀ u ∈ Ici (0 : ℝ), ContDiffWithinAt ℝ (8 : ℕ) (fun u => 1 - chiExt c V u) (Ici 0) u := by
    intro u hu
    rcases lt_or_ge u (fctUc c) with hlt | hge
    · have hU1 : Ioo (-1 : ℝ) (fctUc c) ∈ 𝓝 u := isOpen_Ioo.mem_nhds ⟨by linarith only [hu.out], hlt⟩
      rw [← contDiffWithinAt_inter hU1, hIco_eq]
      have hcon : EqOn (fun u => 1 - chiExt c V u)
          (fun u => ((1 - fctInnerChi outerChiIn c V u : ℝ) : ℂ)) (Ico 0 (fctUc c)) := fun x hx => by
        simp [chiExt, extUc, hx.2.le]
      exact (hχ_sym.1.mono Ico_subset_Icc_self).contDiffWithinAt ⟨hu.out, hlt⟩ |>.congr hcon (hcon ⟨hu.out, hlt⟩)
    · have hu_gt : ucut < u := lt_of_lt_of_le hucut_lt hge
      exact (hcd_oi.contDiffAt (isOpen_Ioi.mem_nhds hu_gt)).contDiffWithinAt
  refine ⟨fun u hu => hcd_loc u hu, fun r hr u hu => ?_⟩
  rcases lt_or_ge u (fctUc c) with hlt | hge
  · have hDco : UniqueDiffOn ℝ (Ico (0 : ℝ) (fctUc c)) := uniqueDiffOn_Ico 0 (fctUc c)
    have hu_co : u ∈ Ico (0 : ℝ) (fctUc c) := ⟨hu.out, hlt⟩
    have hcon : iteratedFDerivWithin ℝ r (fun u => 1 - chiExt c V u) (Ico 0 (fctUc c)) u =
        iteratedFDerivWithin ℝ r (fun u => ((1 - fctInnerChi outerChiIn c V u : ℝ) : ℂ)) (Ico 0 (fctUc c)) u :=
      iteratedFDerivWithin_congr (fun x hx => by simp [chiExt, extUc, hx.2.le]) hu_co r
    have h1u : 0 ≤ 1 + u := by linarith only [hu.out]
    rw [← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      ← iteratedFDerivWithin_subset Ico_subset_Ici_self hDco hDi
        (ContDiffOn.of_le (fun u hu => hcd_loc u hu) (by exact_mod_cast hr)) hu_co,
      hcon,
      iteratedFDerivWithin_subset Ico_subset_Icc_self hDco hDu (hχ_sym.1.of_le (by exact_mod_cast hr)) hu_co,
      norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    exact (hχ_sym.2 r hr u ⟨hu.out, hlt.le⟩).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg h1u _))
  · have hu_gt : ucut < u := lt_of_lt_of_le hucut_lt hge
    have hDoi : UniqueDiffOn ℝ (Ioi ucut) := isOpen_Ioi.uniqueDiffOn
    have hsub_oi : Ioi ucut ⊆ Ici (0 : ℝ) := fun x hx => le_of_lt (lt_trans hucut_pos hx)
    have hcon : iteratedFDerivWithin ℝ r (fun u => 1 - chiExt c V u) (Ioi ucut) u =
        iteratedFDerivWithin ℝ r (fun _ : ℝ => (1 : ℂ)) (Ioi ucut) u :=
      iteratedFDerivWithin_congr h1_oi hu_gt r
    rw [← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      ← iteratedFDerivWithin_subset hsub_oi hDoi hDi
        (ContDiffOn.of_le (fun u hu => hcd_loc u hu) (by exact_mod_cast hr)) hu_gt,
      hcon]
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · rw [norm_iteratedFDerivWithin_zero, norm_one]
      simp only [Nat.cast_zero, sub_zero, Real.rpow_zero, mul_one]
      exact le_max_right _ _
    · rw [iteratedFDerivWithin_const_of_ne hr0.ne', Pi.zero_apply, norm_zero]
      exact mul_nonneg (le_max_of_le_right zero_le_one) (Real.rpow_nonneg (by linarith only [hu.out]) _)

lemma one_symCls (n : ℕ) : FctSymCls n 0 1 (fun _ : ℝ => (1 : ℂ)) := by
  refine ⟨contDiffOn_const, fun r _ u hu => ?_⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · simp
  · rw [← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      iteratedFDerivWithin_const_of_ne hr0.ne', Pi.zero_apply, norm_zero]
    exact mul_nonneg zero_le_one (Real.rpow_nonneg (by linarith only [hu.out]) _)

lemma id_symCls (n : ℕ) : FctSymCls n 1 1 (fun u : ℝ => (u : ℂ)) := by
  have hDi := uniqueDiffOn_Ici (0 : ℝ)
  refine FctSymClsOn.ofReal_cast hDi contDiffOn_id fun r _ u hu => ?_
  rw [show (fun u : ℝ => u) = id from rfl, iteratedDerivWithin_eq_iteratedDeriv hDi contDiffAt_id hu]
  have hid : (id : ℝ → ℝ) = fun x => x := rfl
  rw [hid]
  have h1u : 1 ≤ 1 + u := by linarith [hu.out]
  rcases (by omega : r = 0 ∨ r = 1 ∨ 2 ≤ r) with rfl | rfl | hr2
  · rw [iteratedDeriv_zero, abs_of_nonneg hu.out, Nat.cast_zero, sub_zero, Real.rpow_one, one_mul]
    linarith only [hu.out]
  · rw [iteratedDeriv_one, deriv_id'', abs_one]; simp
  · obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
    have h2 : ∀ n : ℕ, ∀ x : ℝ, iteratedDeriv (n + 2) (fun x : ℝ => x) x = 0 := by
      intro n
      induction n with
      | zero => intro x; rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_id'', deriv_const']
      | succ n ih => intro x; rw [iteratedDeriv_succ, show iteratedDeriv (n + 2) (fun x : ℝ => x) = fun _ => 0 from funext ih, deriv_const']
    rw [h2 m u, abs_zero, one_mul]; exact Real.rpow_nonneg (by linarith [hu.out]) _

lemma sq_symCls (n : ℕ) : FctSymCls n 2 (2 ^ n) (fun u : ℝ => (u : ℂ) ^ 2) := by
  have heq : (fun u : ℝ => (u : ℂ) ^ 2) = fun u : ℝ => (u : ℂ) * (u : ℂ) := by ext u; ring
  rw [heq]
  simpa only [mul_one] using
    ((id_symCls n).mul Subset.rfl (uniqueDiffOn_Ici 0) (id_symCls n)).mono_p Subset.rfl
      (by positivity) (by norm_num : (1 : ℝ) + 1 ≤ 2)

end FormalResearch.SignUncertainty
