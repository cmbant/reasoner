/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpWinJ1
public import FormalResearch.SignUncertainty.FctWarpWinS
public import FormalResearch.SignUncertainty.FctWarpInnerRed

/-!
# Window symbol and `L`-difference bounds for `winMuMix` and `chi` (`fct:warp-win`)

Leaf helper module for `FctWarpWinInner.lean`:
* `winMuMix K4 ε c L1 L α u`: mixed inner integrand factor using CFU phase `(L, α)` and kill factor `L₁`.
* `win_comp_scale_T_diff_jc`: scaled composition difference `g(scale * T₂ u) - g(scale * T₁ u)` for `0 < scale ≤ c^{1/4}`.
* `concreteInnerV_win_props`: `ContDiffOn ℝ 10`, `FctVJets pbKV`, `[0, 1.1]` bounds, and `V₂ - V₁`/`T₂ - T₁` window differences.
* `win_E_diff_sym`, `win_K_diff_sym`, `win_muMix_diff_sym`, `win_muMix_sub_one_sym`, `win_chi_diff_sym`:
  window differences and `𝒮^{10}`/`𝒮^1` bounds for `winMuMix` and `χ`.

Class: proved.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped Real ContDiff BigOperators
open FormalResearch.CohnElkies FormalResearch.Special FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD FormalResearch.SignUncertainty.FctMoment
open FormalResearch.SignUncertainty.FctPhiKill FormalResearch.SignUncertainty.FctSymA
open FormalResearch.SignUncertainty.CtCfu

namespace FormalResearch.SignUncertainty

local notation "τs" => ((12 / π ^ 2) ^ (1 / 3 : ℝ))

/-! ### 1. Mixed window amplitude `winMuMix` -/

/-- Mixed inner integrand amplitude at phase point `(L, α)` with kill factor `L₁` (`fct:warp-win`). -/
noncomputable def winMuMix (K4 ε c L1 L α u : ℝ) : ℂ :=
  let S := concreteBoxS K4 ε c
  let q := (concreteEll1 ε c L, (1 : ℝ), α)
  let τ₁ := c ^ (-(1 / 4 : ℝ))
  let T := fctInnerT c (concreteInnerV K4 ε c L α) u
  ((Jfun S.V fctH (τ₁ ^ 2) (q, fctInnerY c u) : ℝ) : ℂ) *
    Complex.exp (-((K4 * T ^ 4 : ℝ) : ℂ) +
      ((v1 StripKernelChoice.star K4 c τ₁ T : ℝ) : ℂ) +
      ((α * T ^ 2 : ℝ) : ℂ) +
      FormalResearch.Asymptotics.binetDiff c (Complex.I * (T : ℂ))) *
    (1 - (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) T)

lemma winMuMix_diag_eq {K4 ε c L1 α u : ℝ} :
    winMuMix K4 ε c L1 L1 α u = (concreteInnerFamily K4 ε).mu c L1 α u := rfl

/-! ### 2. Scaled composition difference `g(scale * T₂ u) - g(scale * T₁ u)` -/

private lemma re_iteratedDeriv' (r : ℕ) {f : ℝ → ℂ} {O : Set ℝ} (hO : IsOpen O)
    (hf : ContDiffOn ℝ r f O) {u : ℝ} (hu : u ∈ O) :
    iteratedDeriv r (fun x => (f x).re) u = (iteratedDeriv r f u).re := by
  induction r generalizing f with
  | zero => simp
  | succ r ih =>
    have hdf : ContDiffOn ℝ r (deriv f) O := by
      have h0 := hf.derivWithin (m := (r : WithTop ℕ∞)) hO.uniqueDiffOn (by simp)
      exact h0.congr fun x hx => (derivWithin_of_isOpen hO hx).symm
    have hre : deriv (fun x => (f x).re) =ᶠ[𝓝 u] fun x => (deriv f x).re := by
      filter_upwards [hO.mem_nhds hu] with x hx
      have hd := ((hf.contDiffAt (hO.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
      exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd).deriv
    rw [iteratedDeriv_succ', hre.iteratedDeriv_eq r, ih hdf, ← iteratedDeriv_succ']

private lemma im_iteratedDeriv' (r : ℕ) {f : ℝ → ℂ} {O : Set ℝ} (hO : IsOpen O)
    (hf : ContDiffOn ℝ r f O) {u : ℝ} (hu : u ∈ O) :
    iteratedDeriv r (fun x => (f x).im) u = (iteratedDeriv r f u).im := by
  induction r generalizing f with
  | zero => simp
  | succ r ih =>
    have hdf : ContDiffOn ℝ r (deriv f) O := by
      have h0 := hf.derivWithin (m := (r : WithTop ℕ∞)) hO.uniqueDiffOn (by simp)
      exact h0.congr fun x hx => (derivWithin_of_isOpen hO hx).symm
    have him : deriv (fun x => (f x).im) =ᶠ[𝓝 u] fun x => (deriv f x).im := by
      filter_upwards [hO.mem_nhds hu] with x hx
      have hd := ((hf.contDiffAt (hO.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
      exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hd).deriv
    rw [iteratedDeriv_succ', him.iteratedDeriv_eq r, ih hdf, ← iteratedDeriv_succ']

private lemma fctVJets_convex' {K c s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {V1 V2 : ℝ → ℝ} (h1 : FctVJets K c V1) (h2 : FctVJets K c V2) :
    FctVJets K c (fun Y => (1 - s) * V1 Y + s * V2 Y) := by
  have hDu36 := uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 3.6)
  refine ⟨(contDiffOn_const.mul h1.1).add (contDiffOn_const.mul h2.1), fun j hj Y hY => ?_⟩
  have h1s : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
  have hs0 : 0 ≤ s := hs.1
  have hj14 : ((j : ℕ∞) : WithTop ℕ∞) ≤ 14 := by
    rw [show (14 : WithTop ℕ∞) = (((14 : ℕ) : ℕ∞) : WithTop ℕ∞) by rfl]; exact_mod_cast hj
  have hd1 : ContDiffOn ℝ j (fun Y => V1 Y - τs) (Icc 0 3.6) := (h1.1.of_le hj14).sub contDiffOn_const
  have hd2 : ContDiffOn ℝ j (fun Y => V2 Y - τs) (Icc 0 3.6) := (h2.1.of_le hj14).sub contDiffOn_const
  have heq : EqOn (fun Y => (1 - s) * V1 Y + s * V2 Y - τs)
      (fun Y => (1 - s) * (V1 Y - τs) + s * (V2 Y - τs)) (Icc 0 3.6) := fun z _ => by ring
  rw [iteratedDerivWithin_congr heq hY]
  change |iteratedDerivWithin j
      ((fun Y => (1 - s) * (V1 Y - τs)) + (fun Y => s * (V2 Y - τs))) (Icc 0 3.6) Y| ≤ _
  rw [iteratedDerivWithin_add hY hDu36
      ((contDiffOn_const.mul hd1).contDiffWithinAt hY)
      ((contDiffOn_const.mul hd2).contDiffWithinAt hY),
    iteratedDerivWithin_const_mul (n := j) (c := 1 - s) hY hDu36 (hd1.contDiffWithinAt hY),
    iteratedDerivWithin_const_mul (n := j) (c := s) hY hDu36 (hd2.contDiffWithinAt hY)]
  have hb1 := h1.2 j hj Y hY
  have hb2 := h2.2 j hj Y hY
  calc |(1 - s) * iteratedDerivWithin j (fun Y => V1 Y - τs) (Icc 0 3.6) Y +
        s * iteratedDerivWithin j (fun Y => V2 Y - τs) (Icc 0 3.6) Y|
      ≤ (1 - s) * |iteratedDerivWithin j (fun Y => V1 Y - τs) (Icc 0 3.6) Y| +
        s * |iteratedDerivWithin j (fun Y => V2 Y - τs) (Icc 0 3.6) Y| := by
        simpa [abs_mul, abs_of_nonneg h1s, abs_of_nonneg hs0] using abs_add_le
          ((1 - s) * _) (s * _)
    _ ≤ (1 - s) * (K * c ^ (-(1 / 2 : ℝ))) + s * (K * c ^ (-(1 / 2 : ℝ))) := by gcongr
    _ = K * c ^ (-(1 / 2 : ℝ)) := by ring

/-- Scaled composition difference: if `0 < scale ≤ c^{1/4}` and `3 * scale * τ₁ ≤ R`,
then `g(scale * T₂ u) - g(scale * T₁ u) ∈ 𝒮^8_1 (C * B_g * scale * D * c^{-1/3})`. -/
theorem win_comp_scale_T_diff_jc {K : ℝ} (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c scale R B_g D : ℝ},
      (10000 : ℝ) ≤ c → K * c ^ (-(1 / 2 : ℝ)) ≤ 0.001 →
      0 < scale → scale ≤ c ^ (1 / 4 : ℝ) → 3 * scale * fctTau1 c ≤ R →
      0 ≤ B_g → 0 ≤ D →
      ∀ {V1 V2 : ℝ → ℝ},
        ContDiffOn ℝ 10 V1 Yint → ContDiffOn ℝ 10 V2 Yint →
        FctVJets K c V1 → FctVJets K c V2 →
        (∀ y ∈ Yint, 0 ≤ V1 y ∧ V1 y ≤ 1.1) →
        (∀ y ∈ Yint, 0 ≤ V2 y ∧ V2 y ≤ 1.1) →
        FctSymClsOn (Icc 0 (fctUc c)) 8 1 (D * c ^ (-(1 / 3 : ℝ)))
          (fun u => ((fctInnerT c V2 u - fctInnerT c V1 u : ℝ) : ℂ)) →
        ∀ {g : ℝ → ℂ}, ContDiffOn ℝ 10 g (Ioo (-R) R) → JC 8 (Ioo (-R) R) (deriv g) B_g →
          FctSymClsOn (Icc 0 (fctUc c)) 8 1 (C * B_g * scale * D * c ^ (-(1 / 3 : ℝ)))
            (fun u => g (scale * fctInnerT c V2 u) - g (scale * fctInnerT c V1 u)) := by
  obtain ⟨B_T, hBT1, hBT⟩ := fctInnerT_sym_bounds hK
  let M_m : ℝ := max 1 (4 * B_T)
  let C_g : ℝ := (Nat.factorial 8 : ℝ) * M_m ^ 8
  let C_fin : ℝ := 2 ^ 8 * C_g
  refine ⟨C_fin, by positivity, fun {c scale R B_g D} hc10000 hη hsc0 hsc_le hR hBg0 hD0
      {V1 V2} hV1_cd hV2_cd hV1_j hV2_j hV1_Y hV2_Y hT_diff {g} hg_cd hg_jc => ?_⟩
  have hc1 : 1 ≤ c := by linarith only [hc10000]
  have hc0 : 0 < c := by linarith only [hc10000]
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  let O_u : Set ℝ := Ioo (-0.01 : ℝ) (fctUc c + 0.01)
  have hOu_open : IsOpen O_u := isOpen_Ioo
  have hIcc_Ou : Icc 0 (fctUc c) ⊆ O_u := fun u hu => ⟨by linarith only [hu.1], by linarith only [hu.2]⟩
  have hc12_gt : (2.15 : ℝ) < c ^ ((1 : ℝ) / 12) := by
    by_contra hle; push Not at hle
    have h1 : (c ^ ((1 : ℝ) / 12)) ^ 12 ≤ (2.15 : ℝ) ^ 12 := pow_le_pow_left₀ (by positivity) hle 12
    have h2 : (c ^ ((1 : ℝ) / 12)) ^ 12 = c := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    rw [h2] at h1
    have h3 : (2.15 : ℝ) ^ 12 < 10000 := by norm_num
    linarith only [hc10000, h1, h3]
  have hOu_Y : ∀ u ∈ O_u, fctInnerY c u ∈ Yint := fun u hu => by
    have hy0 : 0 ≤ fctInnerY c u := by dsimp only [fctInnerY]; positivity
    have hu_abs : |u| ≤ 2.965 * c ^ ((1 : ℝ) / 12) := by
      have hu_lo : -(2.965 * c ^ ((1 : ℝ) / 12)) ≤ u := by linarith only [hu.1, hc12_gt]
      have hu_hi : u ≤ 2.965 * c ^ ((1 : ℝ) / 12) := by
        have h01 : (0.01 : ℝ) ≤ 0.005 * c ^ ((1 : ℝ) / 12) := by linarith only [hc12_gt]
        have hu2 : u ≤ fctUc c + 0.01 := hu.2.le
        dsimp only [fctUc] at hu2; linarith only [hu2, h01]
      exact abs_le.mpr ⟨hu_lo, hu_hi⟩
    have h16 : (c ^ ((1 : ℝ) / 12)) ^ 2 = c ^ ((1 : ℝ) / 6) := by
      rw [← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le]; norm_num
    have hc_prod : c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6) = 1 := by
      rw [← Real.rpow_add hc0]; norm_num
    have hu2 : u ^ 2 ≤ 2.965 ^ 2 * c ^ ((1 : ℝ) / 6) := by
      calc u ^ 2 = |u| ^ 2 := (sq_abs u).symm
        _ ≤ (2.965 * c ^ ((1 : ℝ) / 12)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hu_abs 2
        _ = 2.965 ^ 2 * c ^ ((1 : ℝ) / 6) := by rw [mul_pow, h16]
    have h43 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 0.3969 := fctB2_two_rpow_neg43_le
    have hy_hi : fctInnerY c u < 36 / 10 := by
      dsimp only [fctInnerY]
      calc (2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2
          ≤ 0.3969 * c ^ (-(1 / 6 : ℝ)) * (2.965 ^ 2 * c ^ ((1 : ℝ) / 6)) := by gcongr
        _ = 0.3969 * 2.965 ^ 2 * (c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6)) := by ring
        _ = 0.3969 * 2.965 ^ 2 := by rw [hc_prod, mul_one]
        _ < 36 / 10 := by norm_num
    exact ⟨by linarith only [hy0], hy_hi⟩
  have hT_map_R : ∀ s ∈ Ioo (-0.1 : ℝ) 1.1, ∀ u ∈ O_u,
      (1 - s) * (scale * fctInnerT c V1 u) + s * (scale * fctInnerT c V2 u) ∈ Ioo (-R) R := fun s hs u hu => by
    have hY := hOu_Y u hu
    have h23 : (2 : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 0.63 := fctB2_two_rpow_neg23_le
    have hu_abs : |u| ≤ 2.965 * c ^ ((1 : ℝ) / 12) := by
      have h01 : (0.01 : ℝ) ≤ 0.005 * c ^ ((1 : ℝ) / 12) := by linarith only [hc12_gt]
      have hu2 : u ≤ fctUc c + 0.01 := hu.2.le
      dsimp only [fctUc] at hu2
      rw [abs_le]; constructor <;> linarith only [hu.1, hu2, hc12_gt, h01]
    have hc14 : c ^ (-(1 / 3 : ℝ)) * c ^ ((1 : ℝ) / 12) = fctTau1 c := by
      unfold fctTau1; rw [← Real.rpow_add hc0]; congr 1; norm_num
    have hτ_pos : 0 < fctTau1 c := Real.rpow_pos_of_pos hc0 _
    have hT_bd : ∀ {V : ℝ → ℝ}, (∀ y ∈ Yint, 0 ≤ V y ∧ V y ≤ 1.1) → |fctInnerT c V u| ≤ 2.06 * fctTau1 c := by
      intro V hVY
      have hVy := hVY _ hY
      have hVy0 : 0 ≤ V (fctInnerY c u) := hVy.1
      have hc130 : 0 ≤ c ^ (-(1 / 3 : ℝ)) := by positivity
      rw [show fctInnerT c V u = (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * u * V (fctInnerY c u) from rfl,
        abs_mul, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _),
        abs_of_pos (Real.rpow_pos_of_pos hc0 _), abs_of_nonneg hVy0]
      calc (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * |u| * V (fctInnerY c u)
          ≤ 0.63 * c ^ (-(1 / 3 : ℝ)) * (2.965 * c ^ ((1 : ℝ) / 12)) * 1.1 := by gcongr; exact hVy.2
        _ = (0.63 * 2.965 * 1.1) * fctTau1 c := by rw [← hc14]; ring
        _ ≤ 2.06 * fctTau1 c := mul_le_mul_of_nonneg_right (by norm_num) hτ_pos.le
    have h1 := hT_bd hV1_Y
    have h2 := hT_bd hV2_Y
    have hs1 : |1 - s| + |s| ≤ 1.2 := by
      rcases le_total s 0 with hs0 | hs0
      · rw [abs_of_nonneg (by linarith only [hs0]), abs_of_nonpos hs0]; linarith only [hs.1]
      · rcases le_total s 1 with hs1' | hs1'
        · rw [abs_of_nonneg (by linarith only [hs1']), abs_of_nonneg hs0]; norm_num
        · rw [abs_of_nonpos (by linarith only [hs1']), abs_of_nonneg hs0]; linarith only [hs.2]
    have htot : |(1 - s) * (scale * fctInnerT c V1 u) + s * (scale * fctInnerT c V2 u)| ≤
        1.2 * (scale * (2.06 * fctTau1 c)) := by
      calc |(1 - s) * (scale * fctInnerT c V1 u) + s * (scale * fctInnerT c V2 u)|
          ≤ |1 - s| * |scale * fctInnerT c V1 u| + |s| * |scale * fctInnerT c V2 u| := by
            simpa [abs_mul] using abs_add_le ((1 - s) * (scale * fctInnerT c V1 u))
              (s * (scale * fctInnerT c V2 u))
        _ = |1 - s| * (scale * |fctInnerT c V1 u|) + |s| * (scale * |fctInnerT c V2 u|) := by
            rw [abs_mul, abs_of_nonneg hsc0.le, abs_mul, abs_of_nonneg hsc0.le]
        _ ≤ |1 - s| * (scale * (2.06 * fctTau1 c)) + |s| * (scale * (2.06 * fctTau1 c)) := by gcongr
        _ = (|1 - s| + |s|) * (scale * (2.06 * fctTau1 c)) := by ring
        _ ≤ 1.2 * (scale * (2.06 * fctTau1 c)) := by gcongr
    have hlt : 1.2 * (scale * (2.06 * fctTau1 c)) < 3 * scale * fctTau1 c := by nlinarith only [hτ_pos, hsc0]
    exact abs_lt.mp (lt_of_le_of_lt htot (lt_of_lt_of_le hlt hR))
  have hT1_cd : ContDiffOn ℝ 10 (fun u => scale * fctInnerT c V1 u) O_u := by
    have hYc : ContDiff ℝ 10 (fctInnerY c) := by unfold fctInnerY; fun_prop
    exact contDiffOn_const.mul
      (((contDiff_const.mul contDiff_id).contDiffOn).mul (hV1_cd.comp hYc.contDiffOn fun u hu => hOu_Y u hu))
  have hT2_cd : ContDiffOn ℝ 10 (fun u => scale * fctInnerT c V2 u) O_u := by
    have hYc : ContDiff ℝ 10 (fctInnerY c) := by unfold fctInnerY; fun_prop
    exact contDiffOn_const.mul
      (((contDiff_const.mul contDiff_id).contDiffOn).mul (hV2_cd.comp hYc.contDiffOn fun u hu => hOu_Y u hu))
  have hg1_cd : ContDiffOn ℝ 10 (fun u => g (scale * fctInnerT c V1 u)) O_u :=
    hg_cd.comp hT1_cd fun u hu => by simpa using hT_map_R 0 ⟨by norm_num, by norm_num⟩ u hu
  have hg2_cd : ContDiffOn ℝ 10 (fun u => g (scale * fctInnerT c V2 u)) O_u :=
    hg_cd.comp hT2_cd fun u hu => by simpa using hT_map_R 1 ⟨by norm_num, by norm_num⟩ u hu
  refine ⟨(hg2_cd.sub hg1_cd |>.of_le (by norm_num)).mono hIcc_Ou, fun r hr u₀ hu₀ => ?_⟩
  have hk10 : ((r : ℕ∞) : WithTop ℕ∞) ≤ 10 := by
    rw [show (10 : WithTop ℕ∞) = (((10 : ℕ) : ℕ∞) : WithTop ℕ∞) by rfl]; exact_mod_cast (by omega : r ≤ 10)
  rw [iteratedDerivWithin_eq_iteratedDeriv hDu
    (((hg2_cd.sub hg1_cd).contDiffAt (hOu_open.mem_nhds (hIcc_Ou hu₀))).of_le hk10) hu₀]
  rw [show (fun u => g (scale * fctInnerT c V2 u) - g (scale * fctInnerT c V1 u)) =
      (fun u => g (scale * fctInnerT c V2 u)) - (fun u => g (scale * fctInnerT c V1 u)) from rfl,
    iteratedDeriv_sub ((hg2_cd.contDiffAt (hOu_open.mem_nhds (hIcc_Ou hu₀))).of_le hk10)
      ((hg1_cd.contDiffAt (hOu_open.mem_nhds (hIcc_Ou hu₀))).of_le hk10)]
  let H : ℝ × ℝ → ℂ := fun q => g ((1 - q.1) * (scale * fctInnerT c V1 q.2) + q.1 * (scale * fctInnerT c V2 q.2))
  have hO_prod : IsOpen (Ioo (-0.1 : ℝ) 1.1 ×ˢ O_u) := isOpen_Ioo.prod hOu_open
  have hH_cd : ContDiffOn ℝ 10 H (Ioo (-0.1 : ℝ) 1.1 ×ˢ O_u) := by
    have harg : ContDiffOn ℝ 10
        (fun q : ℝ × ℝ => (1 - q.1) * (scale * fctInnerT c V1 q.2) + q.1 * (scale * fctInnerT c V2 q.2))
        (Ioo (-0.1 : ℝ) 1.1 ×ˢ O_u) :=
      ((contDiffOn_const.sub ((contDiff_fst : ContDiff ℝ 10 (Prod.fst : ℝ × ℝ → ℝ)).contDiffOn
          (s := Ioo (-0.1 : ℝ) 1.1 ×ˢ O_u))).mul
        (hT1_cd.comp ((contDiff_snd : ContDiff ℝ 10 (Prod.snd : ℝ × ℝ → ℝ)).contDiffOn
          (s := Ioo (-0.1 : ℝ) 1.1 ×ˢ O_u)) fun _ hq => hq.2)).add
        (((contDiff_fst : ContDiff ℝ 10 (Prod.fst : ℝ × ℝ → ℝ)).contDiffOn
          (s := Ioo (-0.1 : ℝ) 1.1 ×ˢ O_u)).mul
          (hT2_cd.comp ((contDiff_snd : ContDiff ℝ 10 (Prod.snd : ℝ × ℝ → ℝ)).contDiffOn
            (s := Ioo (-0.1 : ℝ) 1.1 ×ˢ O_u)) fun _ hq => hq.2))
    exact hg_cd.comp harg fun q hq => hT_map_R q.1 hq.1 q.2 hq.2
  let φ : ℝ → ℂ := fun s => iteratedDeriv r (fun u => H (s, u)) u₀
  have hHr2 : ContDiffOn ℝ (r + 2) H (Ioo (-0.1 : ℝ) 1.1 ×ˢ O_u) :=
    hH_cd.of_le (by exact_mod_cast (by omega : r + 2 ≤ 10))
  have hpath_re := hasDerivAt_iteratedDeriv_path hO_prod (0 : ℝ) (1 : ℝ) u₀ r (fun q => (H q).re)
    (Complex.reCLM.contDiff.comp_contDiffOn hHr2)
  have hpath_im := hasDerivAt_iteratedDeriv_path hO_prod (0 : ℝ) (1 : ℝ) u₀ r (fun q => (H q).im)
    (Complex.imCLM.contDiff.comp_contDiffOn hHr2)
  have hfderiv_H : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ O_u,
      fderiv ℝ (fun q => (H q).re) (s, u) (1, 0) =
        (deriv g ((1 - s) * (scale * fctInnerT c V1 u) + s * (scale * fctInnerT c V2 u)) *
          ((scale * (fctInnerT c V2 u - fctInnerT c V1 u) : ℝ) : ℂ)).re ∧
      fderiv ℝ (fun q => (H q).im) (s, u) (1, 0) =
        (deriv g ((1 - s) * (scale * fctInnerT c V1 u) + s * (scale * fctInnerT c V2 u)) *
          ((scale * (fctInnerT c V2 u - fctInnerT c V1 u) : ℝ) : ℂ)).im := by
    intro s hs u hu
    have hs_mem : s ∈ Ioo (-0.1 : ℝ) 1.1 := ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
    have hT_z := hT_map_R s hs_mem u hu
    have hdg : HasDerivAt g (deriv g ((1 - s) * (scale * fctInnerT c V1 u) + s * (scale * fctInnerT c V2 u)))
        ((1 - s) * (scale * fctInnerT c V1 u) + s * (scale * fctInnerT c V2 u)) :=
      ((hg_cd.contDiffAt (isOpen_Ioo.mem_nhds hT_z)).differentiableAt (by norm_num)).hasDerivAt
    have hlin : HasDerivAt (fun t : ℝ => (1 - t) * (scale * fctInnerT c V1 u) + t * (scale * fctInnerT c V2 u))
        (scale * (fctInnerT c V2 u - fctInnerT c V1 u)) s := by
      have := (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).mul_const (scale * fctInnerT c V1 u)).add
        ((hasDerivAt_id s).mul_const (scale * fctInnerT c V2 u))
      exact this.congr_deriv (by ring)
    have hHc := (hdg.scomp s hlin).congr_of_eventuallyEq (Eventually.of_forall fun t => by
      dsimp only [H, Function.comp_def])
    have hH_fd : HasFDerivAt H (fderiv ℝ H (s, u)) (s, u) :=
      ((hH_cd.contDiffAt (hO_prod.mem_nhds ⟨hs_mem, hu⟩)).differentiableAt (by norm_num)).hasFDerivAt
    have hline : HasDerivAt (fun t : ℝ => H (s + t * 1, u)) (fderiv ℝ H (s, u) (1, 0)) 0 := by
      have hc : HasDerivAt (fun t : ℝ => (s + t * 1, u)) (1, 0) 0 :=
        (((hasDerivAt_const 0 s).add ((hasDerivAt_id 0).mul_const 1)).congr_deriv (by ring)).prodMk
          (hasDerivAt_const 0 u)
      have hH0 : HasFDerivAt H (fderiv ℝ H (s, u)) (s + 0 * 1, u) := by
        simpa only [zero_mul, add_zero] using hH_fd
      exact hH0.comp_hasDerivAt 0 hc
    have hline' : HasDerivAt (fun t : ℝ => H (s + t * 1, u))
        (deriv g ((1 - s) * (scale * fctInnerT c V1 u) + s * (scale * fctInnerT c V2 u)) *
          ((scale * (fctInnerT c V2 u - fctInnerT c V1 u) : ℝ) : ℂ)) 0 := by
      have hc2 : HasDerivAt (fun t : ℝ => s + t * 1) 1 0 :=
        ((hasDerivAt_const 0 s).add ((hasDerivAt_id 0).mul_const 1)).congr_deriv (by ring)
      have hHc0 : HasDerivAt (fun t => g ((1 - t) * (scale * fctInnerT c V1 u) + t * (scale * fctInnerT c V2 u)))
          ((scale * (fctInnerT c V2 u - fctInnerT c V1 u)) •
            deriv g ((1 - s) * (scale * fctInnerT c V1 u) + s * (scale * fctInnerT c V2 u))) (s + 0 * 1) := by
        simpa only [zero_mul, add_zero] using hHc
      exact (hHc0.scomp 0 hc2).congr_deriv (by rw [one_smul, Complex.real_smul, mul_comm])
    have heq_der := hline.unique hline'
    have hre_fd := (Complex.reCLM.hasFDerivAt.comp (s, u) hH_fd).fderiv
    have him_fd := (Complex.imCLM.hasFDerivAt.comp (s, u) hH_fd).fderiv
    have heq_re : (⇑Complex.reCLM ∘ H) = fun q => (H q).re := rfl
    have heq_im : (⇑Complex.imCLM ∘ H) = fun q => (H q).im := rfl
    rw [heq_re] at hre_fd
    rw [heq_im] at him_fd
    rw [hre_fd, him_fd]
    simp [heq_der]
  have hder : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt φ
      (iteratedDeriv r (fun u => deriv g ((1 - s) * (scale * fctInnerT c V1 u) + s * (scale * fctInnerT c V2 u)) *
        ((scale * (fctInnerT c V2 u - fctInnerT c V1 u) : ℝ) : ℂ)) u₀) (Icc (0 : ℝ) 1) s := fun s hs => by
    have hs_mem : s ∈ Ioo (-0.1 : ℝ) 1.1 := ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
    have hpr := hpath_re s ⟨by simpa using hs_mem, hIcc_Ou hu₀⟩
    have hpi := hpath_im s ⟨by simpa using hs_mem, hIcc_Ou hu₀⟩
    have hHr_u : ∀ t : ℝ, t ∈ Ioo (-0.1 : ℝ) 1.1 → ContDiffOn ℝ r (fun u => H (t, u)) O_u := fun t ht =>
      (hH_cd.of_le hk10).comp (contDiffOn_const.prodMk contDiffOn_id) fun u hu => ⟨ht, hu⟩
    have hre_eq : (fun t => iteratedDeriv r (fun u => (H (0 + t • 1, u)).re) u₀) =ᶠ[𝓝 s]
        fun t => (φ t).re := by
      filter_upwards [isOpen_Ioo.mem_nhds hs_mem] with t ht
      rw [zero_add, smul_eq_mul, mul_one]
      exact re_iteratedDeriv' r hOu_open (hHr_u t ht) (hIcc_Ou hu₀)
    have him_eq : (fun t => iteratedDeriv r (fun u => (H (0 + t • 1, u)).im) u₀) =ᶠ[𝓝 s]
        fun t => (φ t).im := by
      filter_upwards [isOpen_Ioo.mem_nhds hs_mem] with t ht
      rw [zero_add, smul_eq_mul, mul_one]
      exact im_iteratedDeriv' r hOu_open (hHr_u t ht) (hIcc_Ou hu₀)
    have hd_cd : ContDiffOn ℝ r
        (fun u => deriv g ((1 - s) * (scale * fctInnerT c V1 u) + s * (scale * fctInnerT c V2 u)) *
          ((scale * (fctInnerT c V2 u - fctInnerT c V1 u) : ℝ) : ℂ)) O_u := by
      have hg' : ContDiffOn ℝ 9 (deriv g) (Ioo (-R) R) := by
        have h0 := hg_cd.derivWithin isOpen_Ioo.uniqueDiffOn (by norm_num : ((9 : WithTop ℕ∞) + 1 ≤ 10))
        exact h0.congr fun x hx => (derivWithin_of_isOpen isOpen_Ioo hx).symm
      have harg_u : ContDiffOn ℝ 10
          (fun u => (1 - s) * (scale * fctInnerT c V1 u) + s * (scale * fctInnerT c V2 u)) O_u :=
        (contDiffOn_const.mul hT1_cd).add (contDiffOn_const.mul hT2_cd)
      exact ((hg'.of_le (by exact_mod_cast (by omega : r ≤ 9))).comp (harg_u.of_le (by exact_mod_cast (by omega : r ≤ 10)))
        fun u hu => hT_map_R s hs_mem u hu).mul
        (Complex.ofRealCLM.contDiff.comp_contDiffOn
          (((hT2_cd.sub hT1_cd).of_le (by exact_mod_cast (by omega : r ≤ 10))).congr fun u _ => by
            change scale * (fctInnerT c V2 u - fctInnerT c V1 u) =
              scale * fctInnerT c V2 u - scale * fctInnerT c V1 u
            ring))
    have hval_re : iteratedDeriv r (fun u => fderiv ℝ (fun q => (H q).re) (0 + s • 1, u) (1, 0)) u₀ =
        (iteratedDeriv r (fun u => deriv g ((1 - s) * (scale * fctInnerT c V1 u) + s * (scale * fctInnerT c V2 u)) *
          ((scale * (fctInnerT c V2 u - fctInnerT c V1 u) : ℝ) : ℂ)) u₀).re := by
      rw [← re_iteratedDeriv' r hOu_open hd_cd (hIcc_Ou hu₀)]
      refine Filter.EventuallyEq.iteratedDeriv_eq r ?_
      filter_upwards [hOu_open.mem_nhds (hIcc_Ou hu₀)] with u hu
      rw [zero_add, smul_eq_mul, mul_one]
      exact (hfderiv_H s hs u hu).1
    have hval_im : iteratedDeriv r (fun u => fderiv ℝ (fun q => (H q).im) (0 + s • 1, u) (1, 0)) u₀ =
        (iteratedDeriv r (fun u => deriv g ((1 - s) * (scale * fctInnerT c V1 u) + s * (scale * fctInnerT c V2 u)) *
          ((scale * (fctInnerT c V2 u - fctInnerT c V1 u) : ℝ) : ℂ)) u₀).im := by
      rw [← im_iteratedDeriv' r hOu_open hd_cd (hIcc_Ou hu₀)]
      refine Filter.EventuallyEq.iteratedDeriv_eq r ?_
      filter_upwards [hOu_open.mem_nhds (hIcc_Ou hu₀)] with u hu
      rw [zero_add, smul_eq_mul, mul_one]
      exact (hfderiv_H s hs u hu).2
    have hre_at := ((hpr.congr_of_eventuallyEq hre_eq.symm).congr_deriv hval_re)
    have him_at := ((hpi.congr_of_eventuallyEq him_eq.symm).congr_deriv hval_im)
    have htot := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s hre_at).add
      ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s him_at).mul_const Complex.I)
    exact ((htot.congr_of_eventuallyEq (Eventually.of_forall fun t => by simp)).congr_deriv
      (by apply Complex.ext <;> simp)).hasDerivWithinAt
  have hbd : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv r (fun u => deriv g ((1 - s) * (scale * fctInnerT c V1 u) + s * (scale * fctInnerT c V2 u)) *
        ((scale * (fctInnerT c V2 u - fctInnerT c V1 u) : ℝ) : ℂ)) u₀‖ ≤
        C_fin * B_g * scale * D * c ^ (-(1 / 3 : ℝ)) * (1 + u₀) ^ ((1 : ℝ) - r) := fun s hs => by
    let V_s : ℝ → ℝ := fun Y => (1 - s) * V1 Y + s * V2 Y
    have hVs_j := fctVJets_convex' hs hV1_j hV2_j
    obtain ⟨hTs_cd, _, hTs_deriv, _⟩ := hBT hc1 hη hVs_j
    have hTs_eq : ∀ u : ℝ, (1 - s) * (scale * fctInnerT c V1 u) + s * (scale * fctInnerT c V2 u) =
        scale * fctInnerT c V_s u := fun u => by dsimp only [fctInnerT, V_s]; ring
    have hs_mem : s ∈ Ioo (-0.1 : ℝ) 1.1 := ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
    have hTs_maps : MapsTo (fun u => scale * fctInnerT c V_s u) (Icc 0 (fctUc c)) (Ioo (-R) R) := fun u hu => by
      dsimp only; rw [← hTs_eq u]; exact hT_map_R s hs_mem u (hIcc_Ou hu)
    have hBfM : scale * B_T * c ^ (-(1 / 3 : ℝ)) * (1 + fctUc c) ≤ M_m := by
      have h1 := one_add_fctUc_le hc1
      have hc14 : c ^ (1 / 4 : ℝ) * c ^ (-(1 / 3 : ℝ)) * c ^ ((1 : ℝ) / 12) = 1 := by
        rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
      calc scale * B_T * c ^ (-(1 / 3 : ℝ)) * (1 + fctUc c)
          ≤ c ^ (1 / 4 : ℝ) * B_T * c ^ (-(1 / 3 : ℝ)) * (4 * c ^ ((1 : ℝ) / 12)) := by gcongr
        _ = 4 * B_T * (c ^ (1 / 4 : ℝ) * c ^ (-(1 / 3 : ℝ)) * c ^ ((1 : ℝ) / 12)) := by ring
        _ = 4 * B_T := by rw [hc14, mul_one]
        _ ≤ M_m := le_max_right _ _
    have hdg_sym := FctSymClsOn.comp_T_zero hUc0 (le_max_left _ _ : 1 ≤ M_m) isOpen_Ioo.uniqueDiffOn
      (hg_jc.1.mono (by rfl) |>.of_le (by norm_num)) hBg0
      (fun i hi t ht => by
        have := hg_jc.2 i hi t ht
        rwa [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin] at this)
      (contDiffOn_const.mul hTs_cd) hTs_maps (by positivity) hBfM
      (fun j hj1 hj8 u hu => by
        have hTs_j : ContDiffWithinAt ℝ j (fctInnerT c V_s) (Icc 0 (fctUc c)) u :=
          (hTs_cd.of_le (by exact_mod_cast hj8)).contDiffWithinAt hu
        rw [iteratedDerivWithin_const_mul (n := j) (c := scale) hu hDu hTs_j,
          abs_mul, abs_of_pos hsc0]
        exact (mul_le_mul_of_nonneg_left (hTs_deriv j hj1 hj8 u hu) hsc0.le).trans_eq (by ring))
    have hdg_sym' : FctSymClsOn (Icc 0 (fctUc c)) 8 0 (C_g * B_g)
        (fun u => deriv g ((1 - s) * (scale * fctInnerT c V1 u) + s * (scale * fctInnerT c V2 u))) :=
      (hdg_sym.mono_B Icc_subset_Ici_self (le_of_eq (by dsimp only [C_g]; ring))).congr hDu
        fun u _ => by dsimp only [Function.comp_apply]; rw [hTs_eq u]
    have hT_diff_sc : FctSymClsOn (Icc 0 (fctUc c)) 8 1 (scale * D * c ^ (-(1 / 3 : ℝ)))
        (fun u => ((scale * (fctInnerT c V2 u - fctInnerT c V1 u) : ℝ) : ℂ)) := by
      have hsm := hT_diff.const_mul hDu (scale : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsc0] at hsm
      exact (hsm.mono_B Icc_subset_Ici_self (le_of_eq (by ring))).congr hDu fun u _ => by push_cast; ring
    have hprod : FctSymClsOn (Icc 0 (fctUc c)) 8 (0 + 1) (C_fin * B_g * scale * D * c ^ (-(1 / 3 : ℝ)))
        (fun u => deriv g ((1 - s) * (scale * fctInnerT c V1 u) + s * (scale * fctInnerT c V2 u)) *
          ((scale * (fctInnerT c V2 u - fctInnerT c V1 u) : ℝ) : ℂ)) :=
      (hdg_sym'.mul Icc_subset_Ici_self hDu hT_diff_sc).mono_B Icc_subset_Ici_self
        (le_of_eq (by dsimp only [C_fin]; ring))
    have hprod1 := hprod.mono_p Icc_subset_Ici_self (by positivity) (by norm_num : (0 : ℝ) + 1 ≤ 1)
    have hb_u0 : ‖iteratedDerivWithin r
          (fun u => deriv g ((1 - s) * (scale * fctInnerT c V1 u) + s * (scale * fctInnerT c V2 u)) *
            ((scale * (fctInnerT c V2 u - fctInnerT c V1 u) : ℝ) : ℂ)) (Icc 0 (fctUc c)) u₀‖ ≤
        C_fin * B_g * scale * D * c ^ (-(1 / 3 : ℝ)) * (1 + u₀) ^ ((1 : ℝ) - r) :=
      hprod1.2 r hr u₀ hu₀
    have hg'_cd : ContDiffOn ℝ r
        (fun u => deriv g ((1 - s) * (scale * fctInnerT c V1 u) + s * (scale * fctInnerT c V2 u)) *
          ((scale * (fctInnerT c V2 u - fctInnerT c V1 u) : ℝ) : ℂ)) O_u := by
      have hg9 : ContDiffOn ℝ 9 (deriv g) (Ioo (-R) R) := by
        have h0 := hg_cd.derivWithin isOpen_Ioo.uniqueDiffOn (by norm_num : ((9 : WithTop ℕ∞) + 1 ≤ 10))
        exact h0.congr fun x hx => (derivWithin_of_isOpen isOpen_Ioo hx).symm
      have harg_u : ContDiffOn ℝ 10
          (fun u => (1 - s) * (scale * fctInnerT c V1 u) + s * (scale * fctInnerT c V2 u)) O_u :=
        (contDiffOn_const.mul hT1_cd).add (contDiffOn_const.mul hT2_cd)
      exact ((hg9.of_le (by exact_mod_cast (by omega : r ≤ 9))).comp (harg_u.of_le (by exact_mod_cast (by omega : r ≤ 10)))
        fun u hu => hT_map_R s hs_mem u hu).mul
        (Complex.ofRealCLM.contDiff.comp_contDiffOn
          (((hT2_cd.sub hT1_cd).of_le (by exact_mod_cast (by omega : r ≤ 10))).congr fun u _ => by
            change scale * (fctInnerT c V2 u - fctInnerT c V1 u) =
              scale * fctInnerT c V2 u - scale * fctInnerT c V1 u
            ring))
    rwa [iteratedDerivWithin_eq_iteratedDeriv hDu (hg'_cd.contDiffAt (hOu_open.mem_nhds (hIcc_Ou hu₀))) hu₀] at hb_u0
  have hmv := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd
    (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
  have hφ1 : φ 1 = iteratedDeriv r (fun u => g (scale * fctInnerT c V2 u)) u₀ := by
    dsimp only [φ, H]; congr 1; ext u; simp
  have hφ0 : φ 0 = iteratedDeriv r (fun u => g (scale * fctInnerT c V1 u)) u₀ := by
    dsimp only [φ, H]; congr 1; ext u; simp
  simpa [Real.norm_eq_abs, hφ1, hφ0, sub_zero, mul_one] using hmv

/-! ### 3. Concrete window `V` properties (`concreteInnerV_win_props`) -/

private lemma tauStar_lt_107 : τs < 1.07 := by
  have hpi : 3.1415 < π := Real.pi_gt_d4
  have h12 : (12 : ℝ) / π ^ 2 < 1.07 ^ 3 := by
    rw [div_lt_iff₀ (sq_pos_of_pos Real.pi_pos)]
    have hsq : 3.1415 ^ 2 ≤ π ^ 2 := by nlinarith only [hpi]
    nlinarith only [hsq]
  calc τs = (12 / π ^ 2) ^ (1 / 3 : ℝ) := rfl
    _ < (1.07 ^ 3) ^ (1 / 3 : ℝ) := Real.rpow_lt_rpow (by positivity) h12 (by norm_num)
    _ = 1.07 := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

structure WinVProps (K4 ε c α L_lo L_hi : ℝ) : Prop where
  hc0 : 0 < c
  hc10000 : 10000 ≤ c
  hτD : c ^ (-(1 / 4 : ℝ)) ≤ pbTauLim
  hK4t : K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1
  hKV_small : pbKV * c ^ (-(1 / 2 : ℝ)) ≤ 0.001
  hV0_small : pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) ≤ 0.02
  hcd_lo : ContDiffOn ℝ 10 (concreteInnerV K4 ε c L_lo α) Yint
  hcd_hi : ContDiffOn ℝ 10 (concreteInnerV K4 ε c L_hi α) Yint
  hjets_lo : FctVJets pbKV c (concreteInnerV K4 ε c L_lo α)
  hjets_hi : FctVJets pbKV c (concreteInnerV K4 ε c L_hi α)
  hbd_lo : ∀ y ∈ Yint, 0 ≤ concreteInnerV K4 ε c L_lo α y ∧ concreteInnerV K4 ε c L_lo α y ≤ 1.1
  hbd_hi : ∀ y ∈ Yint, 0 ≤ concreteInnerV K4 ε c L_hi α y ∧ concreteInnerV K4 ε c L_hi α y ≤ 1.1
  heq_lo : ∀ y ∈ Icc (0 : ℝ) 3.5, concreteInnerV K4 ε c L_lo α y =
    (concreteBoxS K4 ε c).V ((concreteEll1 ε c L_lo, (1 : ℝ), α), y)
  heq_hi : ∀ y ∈ Icc (0 : ℝ) 3.5, concreteInnerV K4 ε c L_hi α y =
    (concreteBoxS K4 ε c).V ((concreteEll1 ε c L_hi, (1 : ℝ), α), y)

private lemma clampY_mem_Yint_of_Yint {y : ℝ} (hy : y ∈ Yint) : clampY y ∈ Yint := by
  rcases le_or_gt y 3.5 with hle | hgt
  · rw [clampY_eq_self hle]; exact hy
  · exact clampY_mem_Yint ⟨by linarith only [hgt], by linarith only [hy.2]⟩

lemma winVProps_of_window {K4 Sw_ell : ℝ} (hK4 : 1 ≤ K4) (_hSw : 1 ≤ Sw_ell) :
    ∃ c₀ : ℝ, 10000 ≤ c₀ ∧ ∀ {ε c α L_lo L_hi : ℝ},
      (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      c ^ (-(1 / 4 : ℝ)) ≤ pbTauLim → K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 →
      |α| ≤ c ^ (-(1 / 2 : ℝ)) →
      0 ≤ concreteEll1 ε c L_lo → L_lo ≤ L_hi →
      concreteEll1 ε c L_hi ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) →
      WinVProps K4 ε c α L_lo L_hi := by
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      (10000 : ℝ) ≤ c ∧ (32 : ℝ) ^ 4 ≤ c ∧
      Sw_ell * c ^ (-(1 / 6 : ℝ)) < 27 / 10 ∧
      pbKV * c ^ (-(1 / 2 : ℝ)) ≤ 0.001 ∧
      pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) ≤ 0.02 := by
    refine Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
      (Eventually.and ?_ (Eventually.and ?_ ?_)))
    · have h0 : Tendsto (fun c : ℝ => Sw_ell * c ^ (-(1 / 6 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).const_mul Sw_ell
      exact h0.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 27 / 10))
    · have h0 : Tendsto (fun c : ℝ => pbKV * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul pbKV
      exact h0.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 0.001))
    · have h0 : Tendsto (fun c : ℝ => pbcV * pbC0 * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (pbcV * pbC0)
      exact h0.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 0.02))
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  refine ⟨max 10000 c₀, le_max_left _ _, fun {ε c α L_lo L_hi} hε hc hτ_lim hK4t hα hell1 h12 hell2 => ?_⟩
  obtain ⟨hc10000, _, hSw_lt, hKV_small, hV0_small⟩ := hc₀ c ((le_max_right _ _).trans hc)
  have hc0 : 0 < c := by linarith only [hc10000]
  have hvalid : concreteBoxValid K4 ε c := ⟨hK4, hε, hc0, hτ_lim, hK4t⟩
  set S := concreteBoxS K4 ε c
  obtain ⟨_, _, _, hSΩ, _, _, hSε, hScV, _, _⟩ := concreteBox_spec hvalid
  set τ₁ : ℝ := c ^ (-(1 / 4 : ℝ))
  have hτ₁_sq : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
    dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hα_om : |α| < 2 * τ₁ ^ 2 := by
    rw [hτ₁_sq]; linarith only [hα, Real.rpow_pos_of_pos hc0 (-(1 / 2 : ℝ))]
  have hO : IsOpen (S.Ω ×ˢ Yint) := S.hΩ.prod isOpen_Ioo
  have hV_sub_jc : JC 16 (S.Ω ×ˢ Yint) (fun y => S.V y - τs) (pbcV * pbC0 * c ^ (-(1 / 2 : ℝ))) := by
    refine (S.out.2.2.2.2.2.2.2.2.2.1.congr ?_).mono (le_of_eq ?_)
    · intro y _; simp only [ChartSetup.V, ChartSetup.D, tauStar_eq_dStar_inv]
    · rw [hScV, hSε, hτ₁_sq]; ring
  have hV_cd : ContDiffOn ℝ 16 S.V (S.Ω ×ˢ Yint) := by
    have heq : S.V = fun y => (S.V y - τs) + τs := funext fun y => by ring
    rw [heq]; exact hV_sub_jc.1.add contDiffOn_const
  have hUd_Yint : UniqueDiffOn ℝ Yint := isOpen_Ioo.uniqueDiffOn
  have one_pt : ∀ {L : ℝ}, 0 ≤ concreteEll1 ε c L → concreteEll1 ε c L ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) →
      ContDiffOn ℝ 10 (concreteInnerV K4 ε c L α) Yint ∧
      FctVJets pbKV c (concreteInnerV K4 ε c L α) ∧
      (∀ y ∈ Yint, 0 ≤ concreteInnerV K4 ε c L α y ∧ concreteInnerV K4 ε c L α y ≤ 1.1) ∧
      (∀ y ∈ Icc (0 : ℝ) 3.5, concreteInnerV K4 ε c L α y = S.V ((concreteEll1 ε c L, (1 : ℝ), α), y)) := by
    intro L hL0 hL_hi
    set q : ℝ × ℝ × ℝ := (concreteEll1 ε c L, 1, α)
    have hqΩ : q ∈ S.Ω := by
      rw [hSΩ]
      exact ⟨⟨by linarith only [hL0], by linarith only [hL_hi, hSw_lt]⟩, ⟨by norm_num, by norm_num⟩, abs_lt.mp hα_om⟩
    have hV_slice_jc : JC 16 Yint (fun y => S.V (q, y) - τs)
        (((Nat.factorial 16 : ℝ) * (pbcV * pbC0)) * c ^ (-(1 / 2 : ℝ))) := by
      have hK_nn : 0 ≤ pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) :=
        mul_nonneg (mul_nonneg pbcV_nonneg pbC0_nonneg) (by positivity)
      have hcomp := JC.comp_pair (k := 16) hUd_Yint hO.uniqueDiffOn
        (b1 := 1) (b2 := 1) hK_nn hV_sub_jc contDiffOn_const contDiffOn_id
        (fun j hj1 _ t ht => by
          change ‖iteratedFDerivWithin ℝ j (fun _ : ℝ => q) Yint t‖ ≤ 1
          rw [iteratedFDerivWithin_eq_iteratedFDeriv hUd_Yint contDiffAt_const ht,
            iteratedFDeriv_const_of_ne (by omega : j ≠ 0)]
          simp)
        (fun j hj1 _ t ht => by
          change ‖iteratedFDerivWithin ℝ j (id : ℝ → ℝ) Yint t‖ ≤ 1
          exact norm_iteratedFDerivWithin_id_le hUd_Yint hj1 ht)
        (fun t ht => ⟨hqΩ, ht⟩)
      refine hcomp.mono (le_of_eq ?_)
      have hmax1 : max (1 : ℝ) (max 1 1) = 1 := by norm_num
      rw [hmax1, one_pow, mul_one]; ring
    have hnn : 0 ≤ (Nat.factorial 16 : ℝ) * (pbcV * pbC0) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg pbcV_nonneg pbC0_nonneg)
    have hV_jets_ex :=
      fctVJets_of_chartV.choose_spec.2 (c := c) (K₀ := (Nat.factorial 16 : ℝ) * (pbcV * pbC0)) hc0 hnn hV_slice_jc
    have hcd : ContDiffOn ℝ 10 (concreteInnerV K4 ε c L α) Yint := by
      have hpair : ContDiffOn ℝ 10 (fun y => (q, clampY y)) Yint :=
        contDiffOn_const.prodMk (clampY_contDiff.of_le (by norm_num)).contDiffOn
      exact (hV_cd.of_le (by norm_num)).comp hpair fun y hy => ⟨hqΩ, clampY_mem_Yint_of_Yint hy⟩
    have hbd : ∀ y ∈ Yint, 0 ≤ concreteInnerV K4 ε c L α y ∧ concreteInnerV K4 ε c L α y ≤ 1.1 := fun y hy => by
      have hsub := hV_sub_jc.2 0 (by norm_num) (q, clampY y) ⟨hqΩ, clampY_mem_Yint_of_Yint hy⟩
      rw [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs] at hsub
      have hab := abs_le.mp (hsub.trans hV0_small)
      have hτ106 : (1.06 : ℝ) ≤ τs := warpTauStar_ge
      have hτ107 : τs < 1.07 := tauStar_lt_107
      change 0 ≤ S.V (q, clampY y) ∧ S.V (q, clampY y) ≤ 1.1
      exact ⟨by linarith only [hab.1, hτ106], by linarith only [hab.2, hτ107]⟩
    exact ⟨hcd, hV_jets_ex.1, hbd, hV_jets_ex.2⟩
  have hell2_nn : 0 ≤ concreteEll1 ε c L_hi := by
    have : concreteEll1 ε c L_lo ≤ concreteEll1 ε c L_hi := by dsimp only [concreteEll1]; gcongr
    linarith only [hell1, this]
  have hell1_hi : concreteEll1 ε c L_lo ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) := by
    have : concreteEll1 ε c L_lo ≤ concreteEll1 ε c L_hi := by dsimp only [concreteEll1]; gcongr
    linarith only [this, hell2]
  obtain ⟨hcd_lo, hj_lo, hbd_lo, heq_lo⟩ := one_pt hell1 hell1_hi
  obtain ⟨hcd_hi, hj_hi, hbd_hi, heq_hi⟩ := one_pt hell2_nn hell2
  exact ⟨hc0, hc10000, hτ_lim, hK4t, hKV_small, hV0_small, hcd_lo, hcd_hi, hj_lo, hj_hi, hbd_lo, hbd_hi, heq_lo, heq_hi⟩

/-- info: 'FormalResearch.SignUncertainty.win_comp_scale_T_diff_jc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_comp_scale_T_diff_jc

end FormalResearch.SignUncertainty