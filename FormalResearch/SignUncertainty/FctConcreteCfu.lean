/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctEvenDivide
public import FormalResearch.SignUncertainty.FctDJet
public import FormalResearch.SignUncertainty.FctEJetsU
public import FormalResearch.SignUncertainty.FctCompDPart1
public import FormalResearch.SignUncertainty.CtCfuGerm
public import FormalResearch.SignUncertainty.CtMDeriv
public import FormalResearch.SignUncertainty.CtCfuTheta

/-!
# Concrete instantiation of `CfuTheta` and `ChartSetup` (`fct:comp-cfu`)

Instantiates `CfuTheta` (`FctCfuTheta`) from:
* `ntilCut`: smooth cutoff of `CtCfu.ntil` inside `(-rr, rr)` equal to `ntil` on `[-1/30, 1/30]`,
  giving `concreteMt` with uniform `JC 18 (Ioo (-1) 6)` bound;
* `concreteThetaT ε`: global even lifting (`FctEvenDivide.evenLift 20`) of `(outerTheta ε τ - θ₁^ε τ)/τ³`,
  giving `JC 18 (Ioo (-1) 6)` with no cutoff approximation;
* `compTheta`: `evenLift 20 (hadamardRem 11 ...)` of the five compensator components from `fct_comp_D_part1`
  (including `vAlpha 1 τ₁`, using `vAlpha_eq_smul` and calling `fct_comp_D_part1` at `α = τ₁²`),
  giving `JC 18 (Ioo (-1) 6)` bounds **uniformly in `(c, K₄, ε, α)`**.

Invokes `cfu_chart` to obtain `concreteChartSetup K4 ε c : ChartSetup (ℝ × ℝ × ℝ)` with fixed
perturbation bound `C₀ c^{-1/2}` (constants independent of `(c, K₄)` once `K₄ c^{-1/2} ≤ 1`),
together with `concretePhiPh`, `concretePhiLambda`, `concretePhiTilde`, their exact matching
identity with the cubic normal form `S.ℓ - (π²/36) z + S.r`, and joint `ContDiffOn ℝ ∞` on
`Ioi 0 ×ˢ univ`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real ContDiff BigOperators
open FormalResearch.SignUncertainty.CtCfu FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD FormalResearch.SignUncertainty.FctMoment

namespace FormalResearch.SignUncertainty

/-! ### 1. Linearity of `vAlpha` and `fctThetaD (vTotal ...)` in `α` -/

lemma tildeF_smul (τ₁ a : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    tildeF τ₁ (fun s => a * f s) t = a * tildeF τ₁ f t := by
  unfold tildeF; ring

lemma solverCoeff_smul (N : ℕ) (τ₁ a : ℝ) (f : ℝ → ℝ) (j : Fin N) :
    solverCoeff N τ₁ (fun s => a * f s) j = a * solverCoeff N τ₁ f j := by
  have hm : ∀ k : ℕ, fctMoment k (tildeF τ₁ (fun s => a * f s)) = a * fctMoment k (tildeF τ₁ f) := by
    intro k
    unfold fctMoment
    have hfun : (fun t : ℝ => iteratedDeriv (2 * k + 1) (tildeF τ₁ (fun s => a * f s)) t / Real.sinh (π * t)) =
        fun t => a * (iteratedDeriv (2 * k + 1) (tildeF τ₁ f) t / Real.sinh (π * t)) := by
      ext t
      have htf : tildeF τ₁ (fun s => a * f s) = fun s => a * tildeF τ₁ f s := funext (tildeF_smul τ₁ a f)
      rw [htf, iteratedDeriv_const_mul_field, mul_div_assoc]
    rw [hfun, integral_const_mul, mul_left_comm]
  let v : Fin N → ℝ := fun k =>
    τ₁⁻¹ ^ 2 * (π ^ 2 * τ₁ ^ (1 + 2 * k.1) / ((2 * k.1 + 1).factorial : ℝ)) * fctMoment k.1 (tildeF τ₁ f)
  have hvec : (fun k : Fin N => τ₁⁻¹ ^ 2 * (π ^ 2 * τ₁ ^ (1 + 2 * k.1) / ((2 * k.1 + 1).factorial : ℝ)) *
      fctMoment k.1 (tildeF τ₁ (fun s => a * f s))) = a • v := by
    ext k; simp only [v, Pi.smul_apply, smul_eq_mul, hm]; ring
  unfold solverCoeff
  change -((momentMatrix N τ₁)⁻¹.mulVec _ j) = a * -((momentMatrix N τ₁)⁻¹.mulVec v j)
  rw [hvec, Matrix.mulVec_smul]
  simp [smul_eq_mul]

lemma vAlpha_eq_smul (α τ₁ s : ℝ) : vAlpha α τ₁ s = α * vAlpha 1 τ₁ s := by
  unfold vAlpha momentSolver
  have h1 : (fun t => α * t ^ 2) = fun t => α * (fun u => 1 * u ^ 2) t := by ext t; ring
  rw [h1, tildeF_smul]
  simp_rw [solverCoeff_smul, mul_assoc, ← Finset.mul_sum]
  ring

lemma vAlpha_eq_inv_mul (α τ₁ s : ℝ) (hα : α ≠ 0) : vAlpha 1 τ₁ s = α⁻¹ * vAlpha α τ₁ s := by
  rw [vAlpha_eq_smul α τ₁ s]; field_simp [hα]

lemma fctThetaD_const_mul {w : ℝ → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hs : HasCompactSupport w) (a t : ℝ) :
    fctThetaD (fun s => a * w s) t = a * fctThetaD w t := by
  have h := fctThetaD_linear hw hs hw hs a 0 t
  simpa using h

lemma fctThetaD_vAlpha_eq {K4 c τ₁ : ℝ} (hK4 : 1 ≤ K4) (hc : 0 < c) (hτ₁ : 0 < τ₁)
    (hτ_le : τ₁ ≤ (fct_comp_D_part1 StripKernelChoice.star).choose) (hcτ : τ₁ ^ 4 * c = 1) (α t : ℝ) :
    fctThetaD (vAlpha α τ₁) t = α * fctThetaD (vAlpha 1 τ₁) t ∧
      ContDiff ℝ (⊤ : ℕ∞) (vAlpha 1 τ₁) ∧ HasCompactSupport (vAlpha 1 τ₁) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmain⟩ :=
    (fct_comp_D_part1 StripKernelChoice.star).choose_spec
  have hb := hmain hK4 hc hτ₁ hτ_le hcτ (show |τ₁ ^ 2| ≤ τ₁ ^ 2 by rw [abs_of_nonneg (sq_nonneg _)])
  have hva_cd : ContDiff ℝ (⊤ : ℕ∞) (vAlpha (τ₁ ^ 2) τ₁) := hb.1.2.2.1
  rcases hb.2.2.2.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hva_cs, _, _, _, _, _⟩
  have hv1_eq : vAlpha 1 τ₁ = fun s => (τ₁ ^ 2)⁻¹ * vAlpha (τ₁ ^ 2) τ₁ s :=
    funext fun s => vAlpha_eq_inv_mul (τ₁ ^ 2) τ₁ s (pow_ne_zero 2 hτ₁.ne')
  have hv1_cd : ContDiff ℝ (⊤ : ℕ∞) (vAlpha 1 τ₁) := by
    rw [hv1_eq]; exact contDiff_const.mul hva_cd
  have hv1_cs : HasCompactSupport (vAlpha 1 τ₁) := by
    rw [hv1_eq]; exact hva_cs.comp_left (mul_zero _)
  have htheq : fctThetaD (vAlpha α τ₁) t = α * fctThetaD (vAlpha 1 τ₁) t := by
    have hfun : vAlpha α τ₁ = fun s => α * vAlpha 1 τ₁ s := funext (vAlpha_eq_smul α τ₁)
    rw [hfun]
    exact fctThetaD_const_mul hv1_cd hv1_cs α t
  exact ⟨htheq, hv1_cd, hv1_cs⟩

/-! ### 2. `concreteMt` from `CtCfu.ntil` and `concreteThetaT` from `CtOuter.outerTheta` -/

lemma tenth_lt_rr : (1 / 10 : ℝ) < rr := by
  unfold rr
  have hpi : π ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  rw [one_div_lt_one_div (by norm_num) (pow_pos Real.pi_pos 2)]
  exact hpi

/-- Globally smooth cutoff of `CtCfu.ntil` equal to `ntil` on `[-1/30, 1/30]`. -/
noncomputable def ntilCut (y : ℝ) : ℝ :=
  if |y| < 1 / 10 then etaCut (60 * y) * ntil y else 0

lemma ntilCut_eq_ntil {y : ℝ} (hy : |y| ≤ 1 / 30) : ntilCut y = ntil y := by
  have hy10 : |y| < 1 / 10 := by linarith
  have h60 : |60 * y| ≤ 2 := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 60)]; linarith
  unfold ntilCut
  split_ifs with h
  · rw [etaCut_eq_one h60, one_mul]
  · exact absurd hy10 h

lemma contDiff_ntilCut : ContDiff ℝ (⊤ : ℕ∞) ntilCut := by
  rw [contDiff_iff_contDiffAt]
  intro y
  rcases lt_or_ge |y| (1 / 16) with hlt | hge
  · have hev : (fun z => etaCut (60 * z) * ntil z) =ᶠ[𝓝 y] ntilCut := by
      have ho : IsOpen {z : ℝ | |z| < 1 / 10} := isOpen_lt continuous_abs continuous_const
      filter_upwards [ho.mem_nhds (by linarith : |y| < 1 / 10)] with z hz
      unfold ntilCut
      split_ifs with h
      · rfl
      · exact absurd hz h
    have hmem : y ∈ Ioo (-rr) rr := abs_lt.mp (lt_of_lt_of_le (by linarith) tenth_lt_rr.le)
    have hnt_at : ContDiffAt ℝ (⊤ : ℕ∞) ntil y :=
      (contDiffOn_ntil.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt (isOpen_Ioo.mem_nhds hmem)
    have heta_at : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => etaCut (60 * z)) y :=
      (contDiff_etaCut.comp (contDiff_const.mul contDiff_id)).contDiffAt
    exact (heta_at.mul hnt_at).congr_of_eventuallyEq hev.symm
  · have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 y] ntilCut := by
      have ho : IsOpen {z : ℝ | 1 / 24 < |z|} := isOpen_lt continuous_const continuous_abs
      filter_upwards [ho.mem_nhds (by linarith : 1 / 24 < |y|)] with z hz
      unfold ntilCut
      split_ifs
      · have h60 : 5 / 2 ≤ |60 * z| := by
          have hz' : 1 / 24 < |z| := hz
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 60)]; linarith
        simp [etaCut_eq_zero h60]
      · rfl
    exact contDiffAt_const.congr_of_eventuallyEq hev.symm

/-- `concreteMt y = -(ntilCut y - π²/36) / y` extended smoothly across `y = 0`. -/
noncomputable def concreteMt (y : ℝ) : ℝ :=
  -(hadamardRem 1 (fun z => ntilCut z - π ^ 2 / 36) y)

lemma concreteMt_eq {y : ℝ} (hy : |y| ≤ 1 / 30) : ntil y = π ^ 2 / 36 - y * concreteMt y := by
  have hnt0 : ntilCut 0 = π ^ 2 / 36 := by
    rw [ntilCut_eq_ntil (by norm_num), ntil_zero]
  have hid := hadamardRem_identity (k := 1) ((contDiff_ntilCut.sub contDiff_const).of_le (WithTop.coe_le_coe.mpr le_top))
    (fun j hj => by
      obtain rfl := Nat.lt_one_iff.mp hj
      rw [iteratedDeriv_zero, hnt0, sub_self])
    y
  simp only [pow_one] at hid
  rw [← ntilCut_eq_ntil hy]
  unfold concreteMt
  linarith

private lemma jc_of_contDiff {M : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ M f) {a b : ℝ} :
    ∃ B : ℝ, 0 ≤ B ∧ JC M (Ioo a b) f B := by
  have hbd : ∀ r ≤ M, ∃ Br : ℝ, 0 ≤ Br ∧ ∀ x ∈ Ioo a b, |iteratedDeriv r f x| ≤ Br := fun r hr => by
    rcases le_or_gt b a with hba | hab
    · exact ⟨0, le_rfl, fun x hx => False.elim (by linarith [hx.1, hx.2])⟩
    · obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
        ((hf.continuous_iteratedDeriv r (by exact_mod_cast hr)).continuousOn (s := Icc a b))
      refine ⟨max B 0, le_max_right _ _, fun x hx => ?_⟩
      exact (Real.norm_eq_abs _ ▸ hB x ⟨hx.1.le, hx.2.le⟩).trans (le_max_left _ _)
  choose Br hBr0 hBr using fun r : Fin (M + 1) => hbd r.1 (Nat.lt_succ_iff.mp r.2)
  refine ⟨∑ r : Fin (M + 1), Br r, Finset.sum_nonneg fun r _ => hBr0 r, hf.contDiffOn, fun i hi x hx => ?_⟩
  rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioo hx, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact (hBr ⟨i, Nat.lt_succ_of_le hi⟩ x hx).trans
    (Finset.single_le_sum (f := fun r : Fin (M + 1) => Br r) (fun r _ => hBr0 r) (Finset.mem_univ _))

private lemma jc_Ioo_subset {M : ℕ} {a b c d : ℝ} (hac : a ≤ c) (hdb : d ≤ b) {f : ℝ → ℝ} {B : ℝ}
    (h : JC M (Ioo a b) f B) : JC M (Ioo c d) f B := by
  have hsub : Ioo c d ⊆ Ioo a b := fun x hx => ⟨hac.trans_lt hx.1, hx.2.trans_le hdb⟩
  refine ⟨h.1.mono hsub, fun i hi x hx => ?_⟩
  rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioo hx, ← iteratedFDerivWithin_of_isOpen i isOpen_Ioo (hsub hx)]
  exact h.2 i hi x (hsub hx)

lemma jc_concreteMt : ∃ M : ℝ, 0 ≤ M ∧ JC 18 (Ioo (-1 : ℝ) 6) concreteMt M := by
  have hcd : ContDiff ℝ 18 concreteMt :=
    (hadamardRem_contDiff_and_iteratedDeriv ((contDiff_ntilCut.sub contDiff_const).of_le
      (WithTop.coe_le_coe.mpr le_top))).1.neg
  exact jc_of_contDiff hcd

private lemma hadamardRem_even_of_odd {k : ℕ} (hk : Odd k) {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (y : ℝ) :
    hadamardRem k f (-y) = hadamardRem k f y := by
  have hk0 : k ≠ 0 := by obtain ⟨m, rfl⟩ := hk; omega
  simp only [hadamardRem, hk0, ↓reduceIte]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hderiv : ∀ u : ℝ, iteratedDeriv k f (-u) = iteratedDeriv k f u := fun u => by
    have hc := iteratedDeriv_comp_neg k f u
    have hcomp : (fun x : ℝ => f (-x)) = -f := funext hodd
    rw [hcomp, iteratedDeriv_neg, hk.neg_one_pow, smul_eq_mul, neg_one_mul] at hc
    linarith
  rw [show t * (-y) = -(t * y) by ring, hderiv]

private lemma hadamardRem_even_of_even {k : ℕ} {f : ℝ → ℝ} (hk : Even k) (heven : ∀ x, f (-x) = f x) (y : ℝ) :
    hadamardRem k f (-y) = hadamardRem k f y := by
  by_cases hk0 : k = 0
  · subst hk0; simp [hadamardRem, heven]
  · simp only [hadamardRem, hk0, ↓reduceIte]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hderiv : ∀ u : ℝ, iteratedDeriv k f (-u) = iteratedDeriv k f u := fun u => by
      have hc := iteratedDeriv_comp_neg k f u
      have hcomp : (fun x : ℝ => f (-x)) = f := funext heven
      rw [hcomp, hk.neg_one_pow, one_smul] at hc
      linarith
    rw [show t * (-y) = -(t * y) by ring, hderiv]

lemma deriv_outerTheta_zero {ε : ℝ} (hε : ε = 1 ∨ ε = -1) : deriv (outerTheta ε) 0 = ctTheta1 ε := by
  obtain ⟨th, hth, hrel, hth0, -⟩ := theta_hat hε
  have hd : HasDerivAt (fun τ : ℝ => τ * th (τ ^ 2)) (th 0) 0 := by
    have hpow : HasDerivAt (fun τ : ℝ => τ ^ 2) 0 0 := by simpa using hasDerivAt_pow 2 (0 : ℝ)
    have hcomp : HasDerivAt (fun τ : ℝ => th (τ ^ 2)) (deriv th 0 * 0) 0 :=
      HasDerivAt.comp (0 : ℝ) (by simpa only [sq, mul_zero] using hth.differentiableAt.hasDerivAt) hpow
    have h1 := (hasDerivAt_id (0 : ℝ)).mul hcomp
    simpa only [Pi.mul_def, id_eq, sq, mul_zero, add_zero, one_mul] using h1
  have hd' : HasDerivAt (outerTheta ε) (th 0) 0 := hd.congr_of_eventuallyEq hrel
  rw [hd'.deriv, hth0]

/-- Smooth even `θ_ε(τ)/τ` on `ℝ`. -/
noncomputable def thetaEven (ε y : ℝ) : ℝ := hadamardRem 1 (outerTheta ε) y

/-- Smooth even remainder `(θ_ε(τ) - θ₁^ε τ) / τ³` as a function of `τ`, extended across `0`. -/
noncomputable def thetaRemEven (ε y : ℝ) : ℝ := hadamardRem 2 (fun u => thetaEven ε u - ctTheta1 ε) y

/-- Smooth lifted `θ̃_ε(z)` on `ℝ` (`evenLift 20 (thetaRemEven ε)`), satisfying
`θ_ε(τ) = θ₁^ε τ + τ³ θ̃_ε(τ²)` for all `τ : ℝ`. -/
noncomputable def concreteThetaT (ε z : ℝ) : ℝ := evenLift 20 (thetaRemEven ε) z

lemma concreteThetaT_spec {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    (∀ τ : ℝ, outerTheta ε τ = ctTheta1 ε * τ + τ ^ 3 * concreteThetaT ε (τ ^ 2)) ∧
      ∃ M : ℝ, 0 ≤ M ∧ JC 18 (Ioo (-1 : ℝ) 6) (concreteThetaT ε) M := by
  have hθ_cd : ContDiff ℝ (⊤ : ℕ∞) (outerTheta ε) := (contDiff_outerTheta ε).of_le le_top
  have hθ_0 : outerTheta ε 0 = 0 := by have := outerTheta_neg ε 0; simp at this; linarith
  have hte_cd : ContDiff ℝ 60 (thetaEven ε) :=
    (hadamardRem_contDiff_and_iteratedDeriv (k := 1) (n := 60) (hθ_cd.of_le (WithTop.coe_le_coe.mpr le_top))).1
  have hte_even : ∀ x, thetaEven ε (-x) = thetaEven ε x :=
    hadamardRem_even_of_odd (by decide : Odd 1) (outerTheta_neg ε)
  have hte_0 : thetaEven ε 0 = ctTheta1 ε := by
    unfold thetaEven hadamardRem
    simp [iteratedDeriv_one, deriv_outerTheta_zero hε]
  have htre_cd : ContDiff ℝ 58 (thetaRemEven ε) :=
    (hadamardRem_contDiff_and_iteratedDeriv (k := 2) (n := 58) (hte_cd.sub contDiff_const)).1
  have htre_even : ∀ x, thetaRemEven ε (-x) = thetaRemEven ε x :=
    hadamardRem_even_of_even (by decide : Even 2) (fun u => by simp [hte_even u])
  have hrem1 : ∀ x : ℝ, outerTheta ε x = x * thetaEven ε x := fun x => by
    unfold thetaEven
    simpa only [pow_one] using hadamardRem_identity (k := 1) (hθ_cd.of_le (WithTop.coe_le_coe.mpr le_top))
      (fun j hj => by obtain rfl := Nat.lt_one_iff.mp hj; simpa [iteratedDeriv_zero] using hθ_0) x
  have hrem2 : ∀ x : ℝ, thetaEven ε x - ctTheta1 ε = x ^ 2 * thetaRemEven ε x := fun x =>
    hadamardRem_identity (k := 2) (hte_cd.sub contDiff_const |>.of_le (by norm_cast))
      (fun j hj => by
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
        · simp [iteratedDeriv_zero, hte_0]
        · have he : ∀ u, (fun w => thetaEven ε w - ctTheta1 ε) (-u) = thetaEven ε u - ctTheta1 ε :=
            fun u => by simp [hte_even u]
          exact iteratedDeriv_even_odd_zero he (by decide)) x
  constructor
  · intro τ
    have hel : concreteThetaT ε (τ ^ 2) = thetaRemEven ε τ :=
      evenLift_sq (by norm_num) (htre_cd.of_le (by norm_cast)) htre_even τ
    have h2 := hrem2 τ
    calc outerTheta ε τ = τ * thetaEven ε τ := hrem1 τ
      _ = ctTheta1 ε * τ + τ * (thetaEven ε τ - ctTheta1 ε) := by ring
      _ = ctTheta1 ε * τ + τ * (τ ^ 2 * thetaRemEven ε τ) := by rw [h2]
      _ = ctTheta1 ε * τ + τ ^ 3 * concreteThetaT ε (τ ^ 2) := by rw [hel]; ring
  · obtain ⟨B, hB0, _, hB⟩ := jc_of_contDiff (M := 58) (a := -3.1) (b := 3.1) htre_cd
    have hbd : ∀ k ≤ 2 * 20 + 18, ∀ y : ℝ, |y| ≤ 3 → |iteratedDeriv k (thetaRemEven ε) y| ≤ B := by
      intro k hk y hy
      have hy' : y ∈ Ioo (-3.1 : ℝ) 3.1 := abs_lt.mp (by linarith [abs_le.mp hy])
      have h := hB k (by omega) y hy'
      rwa [iteratedFDerivWithin_of_isOpen k isOpen_Ioo hy', norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at h
    have hjc9 := evenLift_jc (M := 18) (N := 20) (by norm_num) (by norm_num : (1 : ℝ) ≤ 3) hB0 htre_cd hbd
    exact ⟨evenLiftBound 18 20 3 B, evenLiftBound_nonneg 18 20 3 B (by norm_num) hB0,
      jc_Ioo_subset (by norm_num) (by norm_num) hjc9⟩

lemma jc_concreteThetaT : ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, ε = 1 ∨ ε = -1 →
    JC 18 (Ioo (-1 : ℝ) 6) (concreteThetaT ε) M := by
  obtain ⟨M1, hM1, h1⟩ := (concreteThetaT_spec (Or.inl rfl)).2
  obtain ⟨M2, hM2, h2⟩ := (concreteThetaT_spec (Or.inr rfl)).2
  refine ⟨max M1 M2, le_max_of_le_left hM1, fun ε hε => ?_⟩
  rcases hε with rfl | rfl
  · exact h1.mono (le_max_left _ _)
  · exact h2.mono (le_max_right _ _)

/-! ### 3. Generic compensator lift `compTheta` and uniform `concreteCfuTheta` -/

/-- Rescaled even lift `Θ_X` of a compensator phase block `ϑ_X` with `|ϑ_X^{(r)}(τ₁ s)| ≤ C_r S τ₁^{k₀ - r} min(1, |s|^{11-r})`. -/
noncomputable def compTheta (k0 : ℤ) (S : ℝ) (ϑ : ℝ → ℝ) (τ₁ z : ℝ) : ℝ :=
  evenLift 20 (hadamardRem 11 (fun s : ℝ => τ₁ ^ (-k0) * S⁻¹ * ϑ (τ₁ * s))) z

lemma compTheta_spec (k0 : ℤ) {S τ₁ : ℝ} (hS : 0 < S) (hτ₁ : 0 < τ₁)
    {ϑ : ℝ → ℝ} (hϑ_cd : ContDiff ℝ (⊤ : ℕ∞) ϑ) (hϑ_odd : ∀ t, ϑ (-t) = -ϑ t)
    {C : ℕ → ℝ} (hC : ∀ r, 0 ≤ C r)
    (hϑ_bd : ∀ r t, |t| ≤ 12 * τ₁ → |iteratedDeriv r ϑ t| ≤ C r * S * τ₁ ^ (k0 - r) * min 1 ((|t| / τ₁) ^ (11 - r))) :
    (∀ x : ℝ, τ₁ ^ (-k0) * S⁻¹ * ϑ (τ₁ * x) = x ^ 11 * compTheta k0 S ϑ τ₁ (x ^ 2)) ∧
      JC 18 (Ioo (-1 : ℝ) 6) (compTheta k0 S ϑ τ₁) (evenLiftBound 18 20 3 (∑ j ∈ Finset.range 70, C j)) := by
  let f : ℝ → ℝ := fun s => τ₁ ^ (-k0) * S⁻¹ * ϑ (τ₁ * s)
  let g : ℝ → ℝ := hadamardRem 11 f
  have hf_cd : ContDiff ℝ (⊤ : ℕ∞) f :=
    contDiff_const.mul (hϑ_cd.comp (contDiff_const.mul contDiff_id))
  have hg_cd : ContDiff ℝ 58 g :=
    (hadamardRem_contDiff_and_iteratedDeriv (k := 11) (n := 58) (hf_cd.of_le (WithTop.coe_le_coe.mpr le_top))).1
  have hf_odd : ∀ x, f (-x) = -f x := fun x => by
    simp only [f, mul_neg, hϑ_odd, mul_neg]
  have hg_even : ∀ x, g (-x) = g x :=
    hadamardRem_even_of_odd (by decide : Odd 11) hf_odd
  have hf_deriv : ∀ r y, iteratedDeriv r f y = τ₁ ^ (-k0) * S⁻¹ * (τ₁ ^ r * iteratedDeriv r ϑ (τ₁ * y)) := by
    intro r y
    have hmul : (fun s => τ₁ ^ (-k0) * S⁻¹ * ϑ (τ₁ * s)) = fun s => (τ₁ ^ (-k0) * S⁻¹) * (fun u => ϑ (τ₁ * u)) s := rfl
    rw [show f = _ from hmul, iteratedDeriv_const_mul_field]
    congr 1
    exact congrFun (iteratedDeriv_comp_const_mul (n := r) (hϑ_cd.of_le (WithTop.coe_le_coe.mpr le_top)) τ₁) y
  have hf_zero : ∀ j < 11, iteratedDeriv j f 0 = 0 := by
    intro j hj
    have h0 := hϑ_bd j 0 (by rw [abs_zero]; positivity)
    have hj_pos : 11 - j ≠ 0 := by omega
    rw [abs_zero, zero_div, zero_pow hj_pos, min_eq_right zero_le_one, mul_zero] at h0
    have hϑ0 : iteratedDeriv j ϑ 0 = 0 := abs_nonpos_iff.mp h0
    rw [hf_deriv j 0, mul_zero, hϑ0, mul_zero, mul_zero]
  have hf_bd : ∀ k ≤ 69, ∀ y : ℝ, |y| ≤ 3 → |iteratedDeriv k f y| ≤ ∑ j ∈ Finset.range 70, C j := by
    intro k hk y hy
    have hty : |τ₁ * y| ≤ 12 * τ₁ := by
      rw [abs_mul, abs_of_pos hτ₁]
      nlinarith
    have h1 := hϑ_bd k (τ₁ * y) hty
    have hk_bd : |iteratedDeriv k ϑ (τ₁ * y)| ≤ C k * S * τ₁ ^ (k0 - k) :=
      h1.trans (mul_le_of_le_one_right (mul_nonneg (mul_nonneg (hC k) hS.le) (zpow_nonneg hτ₁.le _)) (min_le_left _ _))
    rw [hf_deriv k y, abs_mul, abs_mul, abs_mul, abs_of_pos (zpow_pos hτ₁ _), abs_of_pos (inv_pos.mpr hS),
      abs_of_pos (pow_pos hτ₁ _)]
    have hpow_eq : τ₁ ^ (-k0) * S⁻¹ * (τ₁ ^ k * (C k * S * τ₁ ^ (k0 - k))) = C k := by
      have hcomb : τ₁ ^ (-k0) * (τ₁ ^ (k : ℤ) * τ₁ ^ (k0 - k)) = 1 := by
        rw [← zpow_add₀ hτ₁.ne', ← zpow_add₀ hτ₁.ne']
        have hsum : -k0 + ((k : ℤ) + (k0 - k)) = 0 := by omega
        rw [hsum, zpow_zero]
      rw [← zpow_natCast τ₁ k]
      calc τ₁ ^ (-k0) * S⁻¹ * (τ₁ ^ (k : ℤ) * (C k * S * τ₁ ^ (k0 - k)))
          = C k * (S⁻¹ * S) * (τ₁ ^ (-k0) * (τ₁ ^ (k : ℤ) * τ₁ ^ (k0 - k))) := by ring
        _ = C k * 1 * 1 := by rw [inv_mul_cancel₀ hS.ne', hcomb]
        _ = C k := by ring
    calc τ₁ ^ (-k0) * S⁻¹ * (τ₁ ^ k * |iteratedDeriv k ϑ (τ₁ * y)|)
        ≤ τ₁ ^ (-k0) * S⁻¹ * (τ₁ ^ k * (C k * S * τ₁ ^ (k0 - k))) := by gcongr
      _ = C k := hpow_eq
      _ ≤ ∑ j ∈ Finset.range 70, C j :=
          Finset.single_le_sum (f := fun j => C j) (fun j _ => hC j) (Finset.mem_range.mpr (by omega))
  let Bsum := ∑ j ∈ Finset.range 70, C j
  have hB0 : 0 ≤ Bsum := Finset.sum_nonneg fun j _ => hC j
  have hg_bd : ∀ k ≤ 2 * 20 + 18, ∀ y : ℝ, |y| ≤ 3 → |iteratedDeriv k g y| ≤ Bsum := fun k hk y hy =>
    abs_iteratedDeriv_hadamardRem_le (k := 11) (r := k) (hf_cd.of_le (WithTop.coe_le_coe.mpr le_top))
      hB0 (fun y' hy' => hf_bd (11 + k) (by omega) y' hy') hy
  constructor
  · intro x
    have hel : compTheta k0 S ϑ τ₁ (x ^ 2) = g x :=
      evenLift_sq (by norm_num) (hg_cd.of_le (by norm_cast)) hg_even x
    change f x = x ^ 11 * compTheta k0 S ϑ τ₁ (x ^ 2)
    rw [hel]
    exact hadamardRem_identity (k := 11) (hf_cd.of_le (WithTop.coe_le_coe.mpr le_top)) hf_zero x
  · have hjc9 := evenLift_jc (M := 18) (N := 20) (by norm_num) (by norm_num : (1 : ℝ) ≤ 3) hB0 hg_cd hg_bd
    exact jc_Ioo_subset (by norm_num) (by norm_num) hjc9

/-! ### 4. Concrete `CfuTheta`, `ChartSetup`, and `concretePhiLambda` -/

/-- Exact unperturbed Mellin phase `Φ_Ph(τ; L₁) = L₁ τ - ∫₀^τ hankelEdgeM u du`. -/
noncomputable def concretePhiPh (τ L1 : ℝ) : ℝ :=
  L1 * τ - ∫ u in (0 : ℝ)..τ, hankelEdgeM u

/-- Exact homotopy phase `Φ_λ(τ; L₁, α) = Φ_Ph(τ; L₁) - c⁻¹ θ_ε(τ) + λ c⁻¹ ϑ_D(τ)` (`fct:comp-cfu`). -/
noncomputable def concretePhiLambda (K4 ε c lam τ L1 α : ℝ) : ℝ :=
  concretePhiPh τ L1 - c⁻¹ * outerTheta ε τ + lam * c⁻¹ * fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ)))) τ

/-- Full compensated phase `Φ̃(τ; L₁, α) = Φ_1(τ; L₁, α)` (`fct:warp-asymp`). -/
noncomputable def concretePhiTilde (K4 ε c τ : ℝ) (p : ℝ × ℝ) : ℝ :=
  concretePhiLambda K4 ε c 1 τ p.1 p.2

lemma concretePhiPh_eq_ntil {τ L1 : ℝ} (hτ : 0 ≤ τ) (hτ2 : τ ^ 2 < rr) :
    concretePhiPh τ L1 = L1 * τ - τ ^ 3 * ntil (τ ^ 2) := by
  unfold concretePhiPh
  rw [integral_hankelEdgeM_eq hτ hτ2]

lemma concretePhiLambda_contDiffOn {K4 ε c lam : ℝ} (hK4 : 1 ≤ K4) (hc : 0 < c)
    (hτ_le : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × (ℝ × ℝ) => concretePhiLambda K4 ε c lam q.1 q.2.1 q.2.2) (Ioi 0 ×ˢ univ) := by
  set τ₁ : ℝ := c ^ (-(1 / 4 : ℝ))
  have hτ₁ : 0 < τ₁ := Real.rpow_pos_of_pos hc _
  have hcτ : τ₁ ^ 4 * c = 1 := by
    have : τ₁ ^ 4 = c⁻¹ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num [Real.rpow_neg_one]
    rw [this]; field_simp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmain⟩ :=
    (fct_comp_D_part1 StripKernelChoice.star).choose_spec
  have h0 := hmain hK4 hc hτ₁ hτ_le hcτ (show |(0 : ℝ)| ≤ τ₁ ^ 2 by rw [abs_zero]; positivity)
  have hva_info := fun α => fctThetaD_vAlpha_eq hK4 hc hτ₁ hτ_le hcτ α
  have hv1_cd : ContDiff ℝ (⊤ : ℕ∞) (vAlpha 1 τ₁) := (hva_info 1 0).2.1
  have hv1_cs : HasCompactSupport (vAlpha 1 τ₁) := (hva_info 1 0).2.2
  have hv0_cd : ContDiff ℝ (⊤ : ℕ∞) (v0 StripKernelChoice.star K4 τ₁) := h0.1.1.add (contDiff_const.mul h0.1.2.1)
  have hv1b_cd : ContDiff ℝ (⊤ : ℕ∞) (v1 StripKernelChoice.star K4 c τ₁) := h0.1.2.2.2.1.add (contDiff_const.mul h0.1.2.2.2.2.1)
  have hv0_cs : HasCompactSupport (v0 StripKernelChoice.star K4 τ₁) :=
    hasCompactSupport_of_support_Ioo (fun t ht => by
      by_contra hnot; apply ht; unfold v0
      have h1 : v0Base StripKernelChoice.star τ₁ t = 0 := by by_contra hne; exact hnot (h0.2.2.2.1.1 hne)
      have h2 : v0Marg τ₁ t = 0 := by by_contra hne; exact hnot (h0.2.2.2.1.2.1 hne)
      simp [h1, h2])
  have hv1b_cs : HasCompactSupport (v1 StripKernelChoice.star K4 c τ₁) :=
    hasCompactSupport_of_support_Ioo (fun t ht => by
      by_contra hnot; apply ht; unfold v1
      have h1 : v1Base StripKernelChoice.star c τ₁ t = 0 := by by_contra hne; exact hnot (h0.2.2.2.1.2.2.2.1 hne)
      have h2 : v1Marg c τ₁ t = 0 := by by_contra hne; exact hnot (h0.2.2.2.1.2.2.2.2.1 hne)
      simp [h1, h2])
  have hv01_cd := hv0_cd.add hv1b_cd
  have hv01_cs := hv0_cs.add hv1b_cs
  have hth01_cd : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD (fun s => v0 StripKernelChoice.star K4 τ₁ s +
      v1 StripKernelChoice.star K4 c τ₁ s)) := contDiff_fctThetaD hv01_cd hv01_cs
  have hthα_cd : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD (vAlpha 1 τ₁)) := contDiff_fctThetaD hv1_cd hv1_cs
  have hint_cd : ContDiffOn ℝ (⊤ : ℕ∞) (fun τ : ℝ => ∫ u in (0 : ℝ)..τ, hankelEdgeM u) (Ioi 0) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    have hder : ∀ τ ∈ Ioi (0 : ℝ), HasDerivAt (fun x => ∫ u in (0 : ℝ)..x, hankelEdgeM u) (hankelEdgeM τ) τ := by
      intro τ hτ
      have hint : IntervalIntegrable hankelEdgeM volume 0 τ :=
        (hankelEdgeM_continuousOn.mono fun x hx => by
          rw [Set.uIcc_of_le (le_of_lt hτ)] at hx; exact hx.1).intervalIntegrable
      have hmeas : StronglyMeasurableAtFilter hankelEdgeM (𝓝 τ) :=
        (hankelEdgeM_continuousOn.mono Set.Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi τ hτ
      exact intervalIntegral.integral_hasDerivAt_right hint hmeas (hankelEdgeM_hasDerivAt hτ).continuousAt
    refine ⟨fun τ hτ => (hder τ hτ).differentiableAt.differentiableWithinAt, ?_⟩
    exact CtMDeriv.contDiffOn_hankelEdgeM.congr fun τ hτ => (hder τ hτ).deriv
  have hfst : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (ℝ × ℝ) => q.1) := contDiff_fst
  have hsnd1 : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (ℝ × ℝ) => q.2.1) := contDiff_snd.fst
  have hsnd2 : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (ℝ × ℝ) => q.2.2) := contDiff_snd.snd
  have hbase : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × (ℝ × ℝ) =>
      (q.2.1 * q.1 - ∫ u in (0 : ℝ)..q.1, hankelEdgeM u) - c⁻¹ * outerTheta ε q.1 +
        lam * c⁻¹ * (fctThetaD (fun s => v0 StripKernelChoice.star K4 τ₁ s +
          v1 StripKernelChoice.star K4 c τ₁ s) q.1 + q.2.2 * fctThetaD (vAlpha 1 τ₁) q.1))
      (Ioi 0 ×ˢ univ) := by
    have h1 := (hsnd1.mul hfst).contDiffOn.sub
      (hint_cd.comp hfst.contDiffOn fun q (hq : q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) => hq.1)
    have h2 := (contDiff_const (c := c⁻¹)).mul (((contDiff_outerTheta ε).of_le le_top).comp hfst)
    have h3 := (contDiff_const (c := lam * c⁻¹)).mul ((hth01_cd.comp hfst).add (hsnd2.mul (hthα_cd.comp hfst)))
    exact (h1.sub h2.contDiffOn).add h3.contDiffOn
  refine hbase.congr fun q _ => ?_
  unfold concretePhiLambda concretePhiPh vTotal
  have hva_cd : ContDiff ℝ (⊤ : ℕ∞) (vAlpha q.2.2 τ₁) := by
    have hfun : vAlpha q.2.2 τ₁ = fun s => q.2.2 * vAlpha 1 τ₁ s := funext (vAlpha_eq_smul q.2.2 τ₁)
    rw [hfun]; exact contDiff_const.mul hv1_cd
  have hva_cs : HasCompactSupport (vAlpha q.2.2 τ₁) := by
    have hfun : vAlpha q.2.2 τ₁ = fun s => q.2.2 * vAlpha 1 τ₁ s := funext (vAlpha_eq_smul q.2.2 τ₁)
    rw [hfun]; exact hv1_cs.comp_left (mul_zero _)
  have hlin := fctThetaD_linear hv01_cd hv01_cs hva_cd hva_cs 1 1 q.1
  simp only [one_mul] at hlin
  change (q.2.1 * q.1 - ∫ u in (0 : ℝ)..q.1, hankelEdgeM u) - c⁻¹ * outerTheta ε q.1 +
      lam * c⁻¹ * fctThetaD (fun s => (v0 StripKernelChoice.star K4 τ₁ s +
        v1 StripKernelChoice.star K4 c τ₁ s) + vAlpha q.2.2 τ₁ s) q.1 = _
  rw [hlin, (hva_info q.2.2 q.1).1]

lemma chartOut_mono_eps {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {cB cd cR cD cZ cV : ℝ} (hcB : 0 ≤ cB) (hcd : 0 ≤ cd) (hcR : 0 ≤ cR)
    (hcD : 0 ≤ cD) (hcZ : 0 ≤ cZ) (hcV : 0 ≤ cV)
    {Ω : Set P} {r : P × ℝ → ℝ} {ℓ : P → ℝ} {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂)
    {B d : P → ℝ} {R Z : P × ℝ → ℝ}
    (h : ChartOut cB cd cR cD cZ cV Ω r ℓ ε₁ B d R Z) :
    ChartOut cB cd cR cD cZ cV Ω r ℓ ε₂ B d R Z :=
  ⟨h.1.mono (by nlinarith), h.2.1, h.2.2.1.mono (by nlinarith), h.2.2.2.1,
   h.2.2.2.2.1.mono (by nlinarith), h.2.2.2.2.2.1, h.2.2.2.2.2.2.1.mono (by nlinarith),
   h.2.2.2.2.2.2.2.1.mono (by nlinarith), h.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.1.mono (by nlinarith), h.2.2.2.2.2.2.2.2.2.2⟩

/-- Packaged uniform `CfuTheta` and `ChartSetup` output from `cfu_chart`, with all bounds
uniform in `(c, K₄, ε, α)` for `c ≥ c₀(K₄)` (`K₄ τ₁² ≤ 1` and `τ₁ ≤ tau_cut`). -/
theorem concrete_cfu_exist :
    ∃ (M_cfu cB cd cR cD cZ cV C0 τ_lim : ℝ),
      0 ≤ M_cfu ∧ 0 ≤ cB ∧ 0 ≤ cd ∧ 0 ≤ cR ∧ 0 ≤ cD ∧ 0 ≤ cZ ∧ 0 ≤ cV ∧ 0 ≤ C0 ∧ 0 < τ_lim ∧
      τ_lim ≤ 1 / 20 ∧
      ∀ {K4 ε c : ℝ}, 1 ≤ K4 → (ε = 1 ∨ ε = -1) → 0 < c →
        let τ₁ := c ^ (-(1 / 4 : ℝ))
        τ₁ ≤ τ_lim → K4 * τ₁ ^ 2 ≤ 1 →
        ∃ T : CfuTheta, T.M = M_cfu ∧
          (∀ {lam L1 α x : ℝ}, 0 ≤ x → x ≤ 2.4 →
            τ₁ ^ 3 * (x * ((L1 - ctTheta1 ε / c) / τ₁ ^ 2 - π ^ 2 / 36 * x ^ 2 +
              T.r τ₁ K4 (((L1 - ctTheta1 ε / c) / τ₁ ^ 2, lam, α), x ^ 2))) =
              concretePhiLambda K4 ε c lam (τ₁ * x) L1 α) ∧
          ∃ (B d : ℝ × ℝ × ℝ → ℝ) (R Z : (ℝ × ℝ × ℝ) × ℝ → ℝ)
            (S : ChartSetup (ℝ × ℝ × ℝ)),
            S.Ω = OmT τ₁ ∧ S.ℓ = (fun p : ℝ × ℝ × ℝ => p.1) ∧ S.r = T.r τ₁ K4 ∧
            S.ε = C0 * τ₁ ^ 2 ∧ S.cB = cB ∧ S.cd = cd ∧ S.cR = cR ∧ S.cD = cD ∧ S.cZ = cZ ∧ S.cV = cV ∧
            S.B = B ∧ S.d = d ∧ S.R = R ∧ S.Z = Z ∧
            ChartOut cB cd cR cD cZ cV (OmT τ₁) (T.r τ₁ K4) (fun p => p.1) (C0 * τ₁ ^ 2) B d R Z := by
  let τD := (fct_comp_D_part1 StripKernelChoice.star).choose
  obtain ⟨hτD_pos, hτD_le, _, _, _, _, _, Cth0b, Cth0m, Ctha, Cth1b, Cth1m, _, _, _, _, _,
    _, _, _, hCth_nn, _, _, hmain⟩ := (fct_comp_D_part1 StripKernelChoice.star).choose_spec
  obtain ⟨Mmt, hMmt0, hmt_jc⟩ := jc_concreteMt
  obtain ⟨Mθ, hMθ0, hθ_jc⟩ := jc_concreteThetaT
  obtain ⟨M_cfu, hM_cfu, hMmt_le, hMθ_le, hB0b_le, hB0m_le, hB1b_le, hB1m_le, hBα_le⟩ :
      ∃ M : ℝ, 0 ≤ M ∧ Mmt ≤ M ∧ Mθ ≤ M ∧
        evenLiftBound 18 20 3 (∑ j ∈ Finset.range 70, Cth0b j) ≤ M ∧
        evenLiftBound 18 20 3 (∑ j ∈ Finset.range 70, Cth0m j) ≤ M ∧
        evenLiftBound 18 20 3 (∑ j ∈ Finset.range 70, Cth1b j) ≤ M ∧
        evenLiftBound 18 20 3 (∑ j ∈ Finset.range 70, Cth1m j) ≤ M ∧
        evenLiftBound 18 20 3 (∑ j ∈ Finset.range 70, Ctha j) ≤ M := by
    let B0b := evenLiftBound 18 20 3 (∑ j ∈ Finset.range 70, Cth0b j)
    let B0m := evenLiftBound 18 20 3 (∑ j ∈ Finset.range 70, Cth0m j)
    let B1b := evenLiftBound 18 20 3 (∑ j ∈ Finset.range 70, Cth1b j)
    let B1m := evenLiftBound 18 20 3 (∑ j ∈ Finset.range 70, Cth1m j)
    let Bα := evenLiftBound 18 20 3 (∑ j ∈ Finset.range 70, Ctha j)
    refine ⟨max (max Mmt Mθ) (max (max B0b B0m) (max (max B1b B1m) Bα)),
      le_max_of_le_left (le_max_of_le_left hMmt0),
      (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _),
      ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _),
      ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _),
      (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans (le_max_right _ _),
      (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans (le_max_right _ _),
      ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)⟩
  obtain ⟨C0_raw, cB, cd, cR, cD, cZ, cV, t0, hC0_raw, hcB, hcd, hcR, hcD, hcZ, hcV, ht0, hchart⟩ :=
    cfu_chart M_cfu hM_cfu
  obtain ⟨C0', hC0', hr_jc⟩ := cfuR_jc M_cfu hM_cfu
  let C0 := max C0_raw C0'
  have hC0 : 0 ≤ C0 := le_max_of_le_left hC0_raw
  -- Also ensure `τ_lim` is small enough for `τ₁^2 * 6 ≤ 1/30` and `c_* * (C0 * τ₁^2) ≤ 1/100`
  let cm := max cV (max cB (max cd cD))
  let t1 := (100 * (cm * C0 + 1)) ^ (-(1 / 2 : ℝ))
  let τ_lim := min (min τD (1 / 20)) (min (min t0 (1 / 15)) (min t1 1))
  have ht1_pos : 0 < t1 := Real.rpow_pos_of_pos (by positivity) _
  have hτlim_pos : 0 < τ_lim := by positivity
  have hτlim_le : τ_lim ≤ 1 / 20 := (min_le_left _ _).trans (min_le_right _ _)
  refine ⟨M_cfu, cB, cd, cR, cD, cZ, cV, C0, τ_lim, hM_cfu, hcB, hcd, hcR, hcD, hcZ, hcV, hC0,
    hτlim_pos, hτlim_le, ?_⟩
  intro K4 ε c hK4 hε hc τ₁ hτ₁_lim hK4t
  have hτ₁_pos : 0 < τ₁ := Real.rpow_pos_of_pos hc _
  have hτ₁_τD : τ₁ ≤ τD := hτ₁_lim.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hτ₁_t0 : τ₁ ≤ t0 := hτ₁_lim.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hτ₁_15 : τ₁ ≤ 1 / 15 := hτ₁_lim.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hτ₁_t1 : τ₁ ≤ t1 := hτ₁_lim.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hτ₁_1 : τ₁ ≤ 1 := hτ₁_lim.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hcτ : τ₁ ^ 4 * c = 1 := by
    have : τ₁ ^ 4 = c⁻¹ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num [Real.rpow_neg_one]
    rw [this]; field_simp
  have hcinv : c⁻¹ = τ₁ ^ 4 := by
    calc c⁻¹ = τ₁ ^ 4 * c * c⁻¹ := by rw [hcτ, one_mul]
      _ = τ₁ ^ 4 := by field_simp [hc.ne']
  have hc_τ := hmain hK4 hc hτ₁_pos hτ₁_τD hcτ (show |τ₁ ^ 2| ≤ τ₁ ^ 2 by rw [abs_of_nonneg (sq_nonneg _)])
  have hva_eq := fctThetaD_vAlpha_eq hK4 hc hτ₁_pos hτ₁_τD hcτ
  -- Construct the 5 `compTheta` lifts
  rcases hc_τ with ⟨hcd_v, hev_v, _, hsupp_v, _, _, _, _, hth_in, _⟩
  rcases hsupp_v with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hv0b_cs, hv0m_cs, _, hv1b_cs, hv1m_cs, hv0_cs, hv1_cs, _⟩
  have hv0b_s := compTheta_spec 2 one_pos hτ₁_pos (contDiff_fctThetaD hcd_v.1 hv0b_cs)
    (fctThetaD_odd hev_v.1) (fun r => (hCth_nn r).1)
    (fun r t ht => by simpa only [mul_one] using (hth_in r t ht).1)
  have hv0m_s := compTheta_spec 4 one_pos hτ₁_pos (contDiff_fctThetaD hcd_v.2.1 hv0m_cs)
    (fctThetaD_odd hev_v.2.1) (fun r => (hCth_nn r).2.1)
    (fun r t ht => by simpa only [mul_one] using (hth_in r t ht).2.1)
  have hv1b_s := compTheta_spec (-1) (inv_pos.mpr hc) hτ₁_pos
    (contDiff_fctThetaD hcd_v.2.2.2.1 hv1b_cs)
    (fctThetaD_odd hev_v.2.2.2.1) (fun r => (hCth_nn r).2.2.2.1)
    (fun r t ht => (hth_in r t ht).2.2.2.1)
  have hv1m_s := compTheta_spec 1 (inv_pos.mpr hc) hτ₁_pos
    (contDiff_fctThetaD hcd_v.2.2.2.2.1 hv1m_cs)
    (fctThetaD_odd hev_v.2.2.2.2.1) (fun r => (hCth_nn r).2.2.2.2)
    (fun r t ht => (hth_in r t ht).2.2.2.2)
  have hv1a_cd := (hva_eq 1 0).2.1
  have hv1a_cs := (hva_eq 1 0).2.2
  have hv1a_odd : ∀ t, vAlpha 1 τ₁ (-t) = vAlpha 1 τ₁ t := fun t => by
    rw [vAlpha_eq_inv_mul (τ₁ ^ 2) τ₁ (-t) (pow_ne_zero 2 hτ₁_pos.ne'),
        vAlpha_eq_inv_mul (τ₁ ^ 2) τ₁ t (pow_ne_zero 2 hτ₁_pos.ne'), hev_v.2.2.1 t]
  have hvα_s := compTheta_spec 2 one_pos hτ₁_pos (contDiff_fctThetaD hv1a_cd hv1a_cs)
    (fctThetaD_odd hv1a_odd) (fun r => (hCth_nn r).2.2.1)
    (fun r t ht => by
      have hbd := (hth_in r t ht).2.2.1
      have hva_r : iteratedDeriv r (fctThetaD (vAlpha (τ₁ ^ 2) τ₁)) t =
          τ₁ ^ 2 * iteratedDeriv r (fctThetaD (vAlpha 1 τ₁)) t := by
        have hfn : fctThetaD (vAlpha (τ₁ ^ 2) τ₁) = fun s => τ₁ ^ 2 * fctThetaD (vAlpha 1 τ₁) s :=
          funext (fun s => (hva_eq (τ₁ ^ 2) s).1)
        rw [hfn, iteratedDeriv_const_mul_field]
      rw [hva_r, abs_mul, abs_of_pos (sq_pos_of_pos hτ₁_pos)] at hbd
      rw [mul_one]
      exact le_of_mul_le_mul_left (hbd.trans_eq (by ring)) (sq_pos_of_pos hτ₁_pos))
  let T : CfuTheta :=
    { mt := concreteMt
      θt := concreteThetaT ε
      Θ0b := compTheta 2 1 (fctThetaD (v0Base StripKernelChoice.star τ₁)) τ₁
      Θ0m := compTheta 4 1 (fctThetaD (v0Marg τ₁)) τ₁
      Θ1b := compTheta (-1) c⁻¹ (fctThetaD (v1Base StripKernelChoice.star c τ₁)) τ₁
      Θ1m := compTheta 1 c⁻¹ (fctThetaD (v1Marg c τ₁)) τ₁
      Θα := compTheta 2 1 (fctThetaD (vAlpha 1 τ₁)) τ₁
      M := M_cfu
      hM := hM_cfu
      jc_mt := hmt_jc.mono hMmt_le
      jc_θt := (hθ_jc ε hε).mono hMθ_le
      jc_Θ0b := hv0b_s.2.mono hB0b_le
      jc_Θ0m := hv0m_s.2.mono hB0m_le
      jc_Θ1b := hv1b_s.2.mono hB1b_le
      jc_Θ1m := hv1m_s.2.mono hB1m_le
      jc_Θα := hvα_s.2.mono hBα_le }
  refine ⟨T, rfl, ?_, ?_⟩
  · -- Exact polynomial-phase matching identity on `0 ≤ x ≤ 2.4`
    intro lam L1 α x hx0 hx24
    have ht2x2_30 : |τ₁ ^ 2 * x ^ 2| ≤ 1 / 30 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg τ₁), abs_of_nonneg (sq_nonneg x)]
      have hτ2 : τ₁ ^ 2 ≤ 1 / 225 := by nlinarith only [hτ₁_pos, hτ₁_15]
      have hx2 : x ^ 2 ≤ 5.76 := by nlinarith only [hx0, hx24]
      nlinarith only [hτ2, hx2, sq_nonneg τ₁, sq_nonneg x]
    have hτx_rr : (τ₁ * x) ^ 2 < rr := by
      have : (τ₁ * x) ^ 2 ≤ 1 / 30 := by
        nlinarith only [le_abs_self (τ₁ ^ 2 * x ^ 2), ht2x2_30]
      exact this.trans_lt (by linarith only [tenth_lt_rr])
    have hph : concretePhiPh (τ₁ * x) L1 =
        L1 * (τ₁ * x) - (τ₁ * x) ^ 3 * (π ^ 2 / 36 - (τ₁ ^ 2 * x ^ 2) * concreteMt (τ₁ ^ 2 * x ^ 2)) := by
      rw [concretePhiPh_eq_ntil (mul_nonneg hτ₁_pos.le hx0) hτx_rr,
        show (τ₁ * x) ^ 2 = τ₁ ^ 2 * x ^ 2 by ring, concreteMt_eq ht2x2_30]
    have hth : outerTheta ε (τ₁ * x) =
        ctTheta1 ε * (τ₁ * x) + (τ₁ * x) ^ 3 * concreteThetaT ε (τ₁ ^ 2 * x ^ 2) := by
      rw [(concreteThetaT_spec hε).1 (τ₁ * x), show (τ₁ * x) ^ 2 = τ₁ ^ 2 * x ^ 2 by ring]
    -- Compensator decomposition
    have hv0_cd : ContDiff ℝ (⊤ : ℕ∞) (v0 StripKernelChoice.star K4 τ₁) :=
      hcd_v.1.add (contDiff_const.mul hcd_v.2.1)
    have hv1_cd : ContDiff ℝ (⊤ : ℕ∞) (v1 StripKernelChoice.star K4 c τ₁) :=
      hcd_v.2.2.2.1.add (contDiff_const.mul hcd_v.2.2.2.2.1)
    have hva_cd : ContDiff ℝ (⊤ : ℕ∞) (vAlpha α τ₁) := by
      have hfun : vAlpha α τ₁ = fun s => α * vAlpha 1 τ₁ s := funext (vAlpha_eq_smul α τ₁)
      rw [hfun]; exact contDiff_const.mul hv1a_cd
    have hva_cs : HasCompactSupport (vAlpha α τ₁) := by
      have hfun : vAlpha α τ₁ = fun s => α * vAlpha 1 τ₁ s := funext (vAlpha_eq_smul α τ₁)
      rw [hfun]; exact hv1a_cs.comp_left (mul_zero _)
    have hD_lin : fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁) (τ₁ * x) =
        fctThetaD (v0Base StripKernelChoice.star τ₁) (τ₁ * x) +
          K4 * fctThetaD (v0Marg τ₁) (τ₁ * x) +
          fctThetaD (v1Base StripKernelChoice.star c τ₁) (τ₁ * x) +
          K4 * fctThetaD (v1Marg c τ₁) (τ₁ * x) +
          α * fctThetaD (vAlpha 1 τ₁) (τ₁ * x) := by
      have h1 := fctThetaD_linear hv0_cd hv0_cs hv1_cd hv1_cs 1 1 (τ₁ * x)
      have h2 := fctThetaD_linear (hv0_cd.add hv1_cd) (hv0_cs.add hv1_cs) hva_cd hva_cs 1 1 (τ₁ * x)
      have h0 := fctThetaD_linear hcd_v.1 hv0b_cs hcd_v.2.1 hv0m_cs 1 K4 (τ₁ * x)
      have h1' := fctThetaD_linear hcd_v.2.2.2.1 hv1b_cs hcd_v.2.2.2.2.1 hv1m_cs 1 K4 (τ₁ * x)
      simp only [one_mul] at h1 h2 h0 h1'
      change fctThetaD (fun s => (v0 StripKernelChoice.star K4 τ₁ s +
        v1 StripKernelChoice.star K4 c τ₁ s) + vAlpha α τ₁ s) (τ₁ * x) = _
      rw [h2, h1, show v0 StripKernelChoice.star K4 τ₁ = fun s => v0Base StripKernelChoice.star τ₁ s +
        K4 * v0Marg τ₁ s from rfl,
        show v1 StripKernelChoice.star K4 c τ₁ = fun s => v1Base StripKernelChoice.star c τ₁ s +
        K4 * v1Marg c τ₁ s from rfl]
      rw [h0, h1', (hva_eq α (τ₁ * x)).1]
      ring
    have e0b : fctThetaD (v0Base StripKernelChoice.star τ₁) (τ₁ * x) = τ₁ ^ 2 * (x ^ 11 * T.Θ0b (x ^ 2)) := by
      have h := hv0b_s.1 x
      rw [inv_one, mul_one, show τ₁ ^ (-(2 : ℤ)) = (τ₁ ^ 2)⁻¹ from by
        rw [zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]] at h
      calc fctThetaD (v0Base StripKernelChoice.star τ₁) (τ₁ * x)
          = τ₁ ^ 2 * ((τ₁ ^ 2)⁻¹ * fctThetaD (v0Base StripKernelChoice.star τ₁) (τ₁ * x)) := by
            field_simp [hτ₁_pos.ne']
        _ = τ₁ ^ 2 * (x ^ 11 * T.Θ0b (x ^ 2)) := by rw [h]
    have e0m : fctThetaD (v0Marg τ₁) (τ₁ * x) = τ₁ ^ 4 * (x ^ 11 * T.Θ0m (x ^ 2)) := by
      have h := hv0m_s.1 x
      rw [inv_one, mul_one, show τ₁ ^ (-(4 : ℤ)) = (τ₁ ^ 4)⁻¹ from by
        rw [zpow_neg, show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]] at h
      calc fctThetaD (v0Marg τ₁) (τ₁ * x)
          = τ₁ ^ 4 * ((τ₁ ^ 4)⁻¹ * fctThetaD (v0Marg τ₁) (τ₁ * x)) := by field_simp [hτ₁_pos.ne']
        _ = τ₁ ^ 4 * (x ^ 11 * T.Θ0m (x ^ 2)) := by rw [h]
    have e1b : fctThetaD (v1Base StripKernelChoice.star c τ₁) (τ₁ * x) =
        c⁻¹ * τ₁ ^ (-1 : ℤ) * (x ^ 11 * T.Θ1b (x ^ 2)) := by
      have h := hv1b_s.1 x
      simp only [neg_neg, zpow_one, inv_inv] at h
      calc fctThetaD (v1Base StripKernelChoice.star c τ₁) (τ₁ * x)
          = c⁻¹ * τ₁ ^ (-1 : ℤ) * (τ₁ * c * fctThetaD (v1Base StripKernelChoice.star c τ₁) (τ₁ * x)) := by
            rw [zpow_neg_one]; field_simp [hc.ne', hτ₁_pos.ne']
        _ = c⁻¹ * τ₁ ^ (-1 : ℤ) * (x ^ 11 * T.Θ1b (x ^ 2)) := by rw [h]
    have e1m : fctThetaD (v1Marg c τ₁) (τ₁ * x) =
        c⁻¹ * τ₁ * (x ^ 11 * T.Θ1m (x ^ 2)) := by
      have h := hv1m_s.1 x
      simp only [zpow_neg_one, inv_inv] at h
      calc fctThetaD (v1Marg c τ₁) (τ₁ * x)
          = c⁻¹ * τ₁ * (τ₁⁻¹ * c * fctThetaD (v1Marg c τ₁) (τ₁ * x)) := by
            field_simp [hc.ne', hτ₁_pos.ne']
        _ = c⁻¹ * τ₁ * (x ^ 11 * T.Θ1m (x ^ 2)) := by rw [h]
    have eα : fctThetaD (vAlpha 1 τ₁) (τ₁ * x) = τ₁ ^ 2 * (x ^ 11 * T.Θα (x ^ 2)) := by
      have h := hvα_s.1 x
      rw [inv_one, mul_one, show τ₁ ^ (-(2 : ℤ)) = (τ₁ ^ 2)⁻¹ from by
        rw [zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]] at h
      calc fctThetaD (vAlpha 1 τ₁) (τ₁ * x)
          = τ₁ ^ 2 * ((τ₁ ^ 2)⁻¹ * fctThetaD (vAlpha 1 τ₁) (τ₁ * x)) := by field_simp [hτ₁_pos.ne']
        _ = τ₁ ^ 2 * (x ^ 11 * T.Θα (x ^ 2)) := by rw [h]
    unfold concretePhiLambda
    rw [hph, hth, hD_lin, e0b, e0m, e1b, e1m, eα]
    dsimp only [T]
    simp only [CfuTheta.r, CfuTheta.Th, div_eq_mul_inv]
    rw [hcinv, zpow_neg_one]
    field_simp [hτ₁_pos.ne']
    ring
  · -- Construct `ChartSetup`
    obtain ⟨B, d, R, Z, hout_raw⟩ := hchart T rfl hτ₁_pos hτ₁_t0 (zero_le_one.trans hK4) hK4t
    have hout : ChartOut cB cd cR cD cZ cV (OmT τ₁) (T.r τ₁ K4) (fun p => p.1) (C0 * τ₁ ^ 2) B d R Z :=
      chartOut_mono_eps hcB hcd hcR hcD hcZ hcV
        (mul_le_mul_of_nonneg_right (le_max_left C0_raw C0') (sq_nonneg _)) hout_raw
    have hcm_bd : cm * (C0 * τ₁ ^ 2) ≤ 1 / 100 := by
      have ht1_sq : τ₁ ^ 2 ≤ t1 ^ 2 := pow_le_pow_left₀ hτ₁_pos.le hτ₁_t1 2
      have ht1_val : t1 ^ 2 = (100 * (cm * C0 + 1))⁻¹ := by
        simp only [t1]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num [Real.rpow_neg_one]
      have hpos : (0 : ℝ) < cm * C0 + 1 := by positivity
      calc cm * (C0 * τ₁ ^ 2) = (cm * C0) * τ₁ ^ 2 := by ring
        _ ≤ (cm * C0 + 1) * τ₁ ^ 2 := by nlinarith only [sq_nonneg τ₁]
        _ ≤ (cm * C0 + 1) * t1 ^ 2 := mul_le_mul_of_nonneg_left ht1_sq hpos.le
        _ = (cm * C0 + 1) * (100 * (cm * C0 + 1))⁻¹ := by rw [ht1_val]
        _ = 1 / 100 := by field_simp [hpos.ne']
    have hτ20 : 0 ≤ C0 * τ₁ ^ 2 := by positivity
    have hS_hr : JC 18 (OmT τ₁ ×ˢ Ioo (-1 : ℝ) 6) (T.r τ₁ K4) (C0 * τ₁ ^ 2) :=
      (hr_jc T rfl hτ₁_pos hτ₁_1 (zero_le_one.trans hK4) hK4t).mono
        (mul_le_mul_of_nonneg_right (le_max_right C0_raw C0') (sq_nonneg _))
    let S : ChartSetup (ℝ × ℝ × ℝ) :=
      { Ω := OmT τ₁
        hΩ := OmT_open τ₁
        r := T.r τ₁ K4
        ℓ := fun p => p.1
        cB := cB
        cd := cd
        cR := cR
        cD := cD
        cZ := cZ
        cV := cV
        ε := C0 * τ₁ ^ 2
        B := B
        d := d
        R := R
        Z := Z
        out := hout
        hr := hS_hr
        hℓ := fun p hp => hp.1
        hℓd := (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).differentiable.differentiableOn
        hℓj := JC.clm (OmT_open τ₁).uniqueDiffOn (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
          ((norm_fst_le_one _ _).trans (by norm_num)) fun p hp => by
            simp only [ContinuousLinearMap.coe_fst', Real.norm_eq_abs, abs_le]
            constructor <;> linarith only [hp.1.1, hp.1.2]
        hcV := (mul_le_mul_of_nonneg_right (le_max_left _ _) hτ20).trans hcm_bd
        hcV0 := hcV
        hε := hτ20
        hcB := (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hτ20).trans hcm_bd
        hcd := (mul_le_mul_of_nonneg_right (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) hτ20).trans hcm_bd
        hcD := (mul_le_mul_of_nonneg_right (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) hτ20).trans hcm_bd
        hcB0 := hcB
        hcd0 := hcd
        hcD0 := hcD }
    exact ⟨B, d, R, Z, S, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hout⟩

/-- info: 'FormalResearch.SignUncertainty.concrete_cfu_exist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms concrete_cfu_exist

end FormalResearch.SignUncertainty
