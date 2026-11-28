/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpIntegrand
public import FormalResearch.SignUncertainty.FctEdgeIbp
public import FormalResearch.SignUncertainty.FctMInvSymbol
public import FormalResearch.SignUncertainty.CtOuterPart3Plus
public import FormalResearch.SignUncertainty.FctInnerB2

/-!
# Edge-IBP building blocks for the outer warp tail (`fct:warp-asymp` (1))

Leaf helper module for `FctWarpOuterIbp.lean`:
* `cexp_iteratedDeriv_bound`: general Leibniz induction bounding `‖∂^k exp(f τ)‖` in terms
  of `edgeW τ ^ (-k)` on `{τ | r < |τ|}`.
* `warpAmpScal`: the real-valued edge factor `m(τ) ‖H_*(iτ)‖ / √((6/π²) m'(τ))` with
  all-order bounds `≤ C_k τ^{-1/2} (1+τ)^{-2} edgeW(τ)^{-k}` on `τ > 0` (`Ioc 0 (1/8)` via
  `mQ, mD, uctAstar`, `Ici (1/8)` via `uctM_deriv_symbol, theta_symW_Ici, y = e^{-πτ}`).
* `outerPhi_shoulder_bounds`: lower bound `(1/10) c^{-1/2} ≤ |Φ'(τ)|` and relative
  higher-derivative bounds `|Φ^{(k+1)}(τ)| ≤ K k * edgeW τ ^ (-k) * |Φ'(τ)|` for `1 ≤ k ≤ 11`
  on `τ > 1.85 c^{-1/4}`.

Class: proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Real ContDiff Nat
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctMoment FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctEdgeIbp FormalResearch.SignUncertainty.FctSym

namespace FormalResearch.SignUncertainty

/-! ### General Leibniz induction for `edgeW`-weighted derivative bounds -/

lemma one_le_edgeW_inv {τ : ℝ} (hτ : τ ≠ 0) (k : ℕ) :
    1 ≤ edgeW τ ^ (-(k : ℤ)) := by
  have hw0 : 0 < edgeW τ := edgeW_pos hτ
  have hw1 : edgeW τ ≤ 1 := edgeW_le_one τ
  rw [zpow_neg, zpow_natCast]
  exact (one_le_inv₀ (pow_pos hw0 k)).mpr (pow_le_one₀ hw0.le hw1)

lemma abs_inv_le_edgeW_inv {τ : ℝ} (hτ : τ ≠ 0) (k : ℕ) :
    |τ| ^ (-(k : ℤ)) ≤ edgeW τ ^ (-(k : ℤ)) := by
  have hw0 : 0 < edgeW τ := edgeW_pos hτ
  have ha0 : 0 < |τ| := abs_pos.mpr hτ
  have hle : edgeW τ ≤ |τ| := edgeW_le_abs τ
  rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast]
  exact inv_anti₀ (pow_pos hw0 k) (pow_le_pow_left₀ hw0.le hle k)

lemma edgeW_zpow_mul {τ : ℝ} (hτ : τ ≠ 0) (a b : ℕ) :
    edgeW τ ^ (-(a : ℤ)) * edgeW τ ^ (-(b : ℤ)) = edgeW τ ^ (-((a + b : ℕ) : ℤ)) := by
  have hw0 : 0 < edgeW τ := edgeW_pos hτ
  rw [← zpow_add₀ hw0.ne']
  congr 1; omega

lemma iteratedDeriv_mul_edgeW {S : Set ℝ} (hS : IsOpen S) (hS0 : ∀ τ ∈ S, τ ≠ 0)
    {n : ℕ} {f g : ℝ → ℂ} {wf wg : ℝ → ℝ} {Cf Cg : ℕ → ℝ}
    (hf_cd : ContDiffOn ℝ n f S) (hg_cd : ContDiffOn ℝ n g S)
    (hwf : ∀ τ ∈ S, 0 ≤ wf τ) (_hwg : ∀ τ ∈ S, 0 ≤ wg τ)
    (hCf : ∀ k ≤ n, 0 ≤ Cf k) (_hCg : ∀ k ≤ n, 0 ≤ Cg k)
    (hf_bd : ∀ k ≤ n, ∀ τ ∈ S, ‖iteratedDeriv k f τ‖ ≤ Cf k * wf τ * edgeW τ ^ (-(k : ℤ)))
    (hg_bd : ∀ k ≤ n, ∀ τ ∈ S, ‖iteratedDeriv k g τ‖ ≤ Cg k * wg τ * edgeW τ ^ (-(k : ℤ))) :
    ∀ k ≤ n, ∀ τ ∈ S,
      ‖iteratedDeriv k (fun t => f t * g t) τ‖ ≤
        (∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * Cf j * Cg (k - j)) *
          (wf τ * wg τ) * edgeW τ ^ (-(k : ℤ)) := by
  intro k hk τ hτ
  have hτ0 : τ ≠ 0 := hS0 τ hτ
  have hfa : ContDiffAt ℝ k f τ := (hf_cd.contDiffAt (hS.mem_nhds hτ)).of_le (by exact_mod_cast hk)
  have hga : ContDiffAt ℝ k g τ := (hg_cd.contDiffAt (hS.mem_nhds hτ)).of_le (by exact_mod_cast hk)
  rw [show (fun t => f t * g t) = f * g from rfl, iteratedDeriv_mul hfa hga]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj_le : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hf1 := hf_bd j (hj_le.trans hk) τ hτ
  have hg1 := hg_bd (k - j) (by omega) τ hτ
  rw [norm_mul, norm_mul, Complex.norm_natCast]
  have hch_nn : (0 : ℝ) ≤ (Nat.choose k j : ℝ) := Nat.cast_nonneg _
  have hw_eq : edgeW τ ^ (-(j : ℤ)) * edgeW τ ^ (-((k - j : ℕ) : ℤ)) = edgeW τ ^ (-(k : ℤ)) := by
    rw [edgeW_zpow_mul hτ0]; congr 2; omega
  calc (Nat.choose k j : ℝ) * ‖iteratedDeriv j f τ‖ * ‖iteratedDeriv (k - j) g τ‖
      ≤ (Nat.choose k j : ℝ) * (Cf j * wf τ * edgeW τ ^ (-(j : ℤ))) *
          (Cg (k - j) * wg τ * edgeW τ ^ (-((k - j : ℕ) : ℤ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hf1 hch_nn) hg1 (norm_nonneg _)
          (mul_nonneg hch_nn (mul_nonneg (mul_nonneg (hCf j (hj_le.trans hk)) (hwf τ hτ))
            (zpow_nonneg (edgeW_pos hτ0).le _)))
    _ = (Nat.choose k j : ℝ) * Cf j * Cg (k - j) * (wf τ * wg τ) *
          (edgeW τ ^ (-(j : ℤ)) * edgeW τ ^ (-((k - j : ℕ) : ℤ))) := by ring
    _ = _ := by rw [hw_eq]

private noncomputable def expDerivCoeff (Cf : ℕ → ℝ) (k : ℕ) : ℝ :=
  match k with
  | 0 => 1
  | m + 1 => (range (m + 1)).attach.sum fun p =>
      (Nat.choose m p.1 : ℝ) * expDerivCoeff Cf p.1 * Cf (m + 1 - p.1)
termination_by k
decreasing_by
  have hj := p.2
  simp only [Finset.mem_range] at hj
  omega

private lemma expDerivCoeff_zero (Cf : ℕ → ℝ) : expDerivCoeff Cf 0 = 1 := by
  rw [expDerivCoeff]

private lemma expDerivCoeff_succ (Cf : ℕ → ℝ) (m : ℕ) :
    expDerivCoeff Cf (m + 1) = ∑ j ∈ range (m + 1), (Nat.choose m j : ℝ) * expDerivCoeff Cf j * Cf (m + 1 - j) := by
  conv_lhs => rw [expDerivCoeff]
  exact Finset.sum_attach (range (m + 1)) fun j => (Nat.choose m j : ℝ) * expDerivCoeff Cf j * Cf (m + 1 - j)

private lemma expDerivCoeff_nonneg {Cf : ℕ → ℝ} (hCf : ∀ k, 0 ≤ Cf k) (m : ℕ) :
    0 ≤ expDerivCoeff Cf m := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    cases m with
    | zero => simp [expDerivCoeff_zero]
    | succ k =>
      rw [expDerivCoeff_succ]
      exact Finset.sum_nonneg fun j hj =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ih j (Finset.mem_range.mp hj))) (hCf _)

lemma cexp_iteratedDeriv_bound {S : Set ℝ} (hS : IsOpen S) (hS0 : ∀ τ ∈ S, τ ≠ 0)
    {n : ℕ} {f : ℝ → ℂ} {B : ℝ} {Cf : ℕ → ℝ}
    (hf_cd : ContDiffOn ℝ (n : ℕ) f S) (hB : 0 ≤ B)
    (hCf : ∀ k, 0 ≤ Cf k)
    (hexp : ∀ τ ∈ S, ‖Complex.exp (f τ)‖ ≤ B)
    (hf_bd : ∀ k, 1 ≤ k → k ≤ n → ∀ τ ∈ S, ‖iteratedDeriv k f τ‖ ≤ Cf k * edgeW τ ^ (-(k : ℤ))) :
    ∃ D : ℕ → ℝ, (∀ k, 0 ≤ D k) ∧ ∀ k ≤ n, ∀ τ ∈ S,
      ‖iteratedDeriv k (fun t => Complex.exp (f t)) τ‖ ≤ D k * B * edgeW τ ^ (-(k : ℤ)) := by
  let D : ℕ → ℝ := expDerivCoeff Cf
  have hD_nn : ∀ m : ℕ, 0 ≤ D m := expDerivCoeff_nonneg hCf
  refine ⟨D, hD_nn, ?_⟩
  intro k hk
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro τ hτ
    have hτ0 : τ ≠ 0 := hS0 τ hτ
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · simpa [D, expDerivCoeff_zero] using hexp τ hτ
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have hm_le : m ≤ n := by omega
      have hf_exp_cd : ContDiffOn ℝ (n : ℕ) (fun t => Complex.exp (f t)) S := hf_cd.cexp
      have hev_deriv : EqOn (deriv (fun t => Complex.exp (f t)))
          (fun t => Complex.exp (f t) * deriv f t) S := by
        intro t ht
        have hdf : HasDerivAt f (deriv f t) t :=
          ((hf_cd.differentiableOn (by exact_mod_cast (show n ≠ 0 by omega))).differentiableAt
            (hS.mem_nhds ht)).hasDerivAt
        exact (hdf.cexp).deriv
      have hev_eq : deriv (fun t => Complex.exp (f t)) =ᶠ[𝓝 τ]
          fun t => Complex.exp (f t) * deriv f t :=
        Filter.eventually_of_mem (hS.mem_nhds hτ) fun t ht => hev_deriv ht
      rw [iteratedDeriv_succ', hev_eq.iteratedDeriv_eq m]
      have hcd_m1 : ContDiffAt ℝ m (fun t => Complex.exp (f t)) τ :=
        (hf_exp_cd.contDiffAt (hS.mem_nhds hτ)).of_le (by exact_mod_cast hm_le)
      have hcd_m2 : ContDiffAt ℝ m (deriv f) τ := by
        have hdf : ContDiffOn ℝ m (deriv f) S := by
          have : (m : WithTop ℕ∞) + 1 ≤ n := by exact_mod_cast (by omega : m + 1 ≤ n)
          exact ((contDiffOn_succ_iff_deriv_of_isOpen hS (n := m)).mp (hf_cd.of_le this)).2.2
        exact hdf.contDiffAt (hS.mem_nhds hτ)
      rw [show (fun t => Complex.exp (f t) * deriv f t) = (fun t => Complex.exp (f t)) * deriv f from rfl,
        iteratedDeriv_mul hcd_m1 hcd_m2]
      refine (norm_sum_le _ _).trans ?_
      have hD_succ : D (m + 1) = ∑ j ∈ range (m + 1), (Nat.choose m j : ℝ) * D j * Cf (m + 1 - j) :=
        expDerivCoeff_succ Cf m
      rw [hD_succ, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj => ?_
      have hj_le : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hih_j := ih j (by omega) (by omega) τ hτ
      have hdf_eq : iteratedDeriv (m - j) (deriv f) τ = iteratedDeriv (m - j + 1) f τ := by
        rw [← iteratedDeriv_succ']
      rw [norm_mul, norm_mul, Complex.norm_natCast, hdf_eq]
      have hm_sub : m - j + 1 = m + 1 - j := by omega
      have hbd_df := hf_bd (m - j + 1) (Nat.succ_pos _) (by omega) τ hτ
      rw [hm_sub] at hbd_df ⊢
      have hw_eq : edgeW τ ^ (-(j : ℤ)) * edgeW τ ^ (-((m + 1 - j : ℕ) : ℤ)) =
          edgeW τ ^ (-((m + 1 : ℕ) : ℤ)) := by
        rw [edgeW_zpow_mul hτ0]; congr 2; omega
      calc (Nat.choose m j : ℝ) * ‖iteratedDeriv j (fun t => Complex.exp (f t)) τ‖ *
            ‖iteratedDeriv (m + 1 - j) f τ‖
          ≤ (Nat.choose m j : ℝ) * (D j * B * edgeW τ ^ (-(j : ℤ))) *
              (Cf (m + 1 - j) * edgeW τ ^ (-((m + 1 - j : ℕ) : ℤ))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hih_j (Nat.cast_nonneg _)) hbd_df (norm_nonneg _)
              (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (hD_nn j) hB)
                (zpow_nonneg (edgeW_pos hτ0).le _)))
        _ = (Nat.choose m j : ℝ) * D j * Cf (m + 1 - j) * B *
              (edgeW τ ^ (-(j : ℤ)) * edgeW τ ^ (-((m + 1 - j : ℕ) : ℤ))) := by ring
        _ = _ := by rw [hw_eq]

/-! ### All-order `SymW` / `edgeW` bounds for `warpAmpScal`, `uctM`, `uctM⁻¹` on `(0, ∞)` -/

noncomputable def warpAmpScal (τ : ℝ) : ℝ :=
  uctM τ * ‖uctHstar (Complex.I * (τ : ℂ))‖ / Real.sqrt (6 / π ^ 2 * uctMderiv τ)

lemma warpAmpScal_eq_Ioc {τ : ℝ} (hτ : 0 < τ) (hτ14 : τ < 1 / 4) :
    warpAmpScal τ =
      τ ^ (-(1 / 2 : ℝ)) * (π / Real.sqrt 6 * mQ τ * (mD τ) ^ (-(1 / 2 : ℝ)) *
        (Real.cosh (π * τ) * uctSincH (π * τ) ^ 2)) := by
  have hH := norm_uctHstar_edge hτ
  have hm := uctM_eq_sq_mul_mQ hτ
  have hmd := uctMderiv_eq_mul_mD hτ hτ14
  have hmD_pos : 0 < mD τ := mD_pos_of_mem (by rw [abs_of_pos hτ]; exact hτ14)
  have hs_eq : uctSincH (π * τ) = (π * τ) / Real.sinh (π * τ) := uctSincH_eq (by positivity)
  have hsq_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hsm_pos : 0 < Real.sqrt (mD τ) := Real.sqrt_pos.mpr hmD_pos
  have hs6_pos : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hsh_pos : 0 < Real.sinh (π * τ) := Real.sinh_pos_iff.mpr (by positivity)
  have hτm12 : τ ^ (-(1 / 2 : ℝ)) = (Real.sqrt τ)⁻¹ := by
    rw [Real.rpow_neg hτ.le, ← Real.sqrt_eq_rpow]
  have hmDm12 : (mD τ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (mD τ))⁻¹ := by
    rw [Real.rpow_neg hmD_pos.le, ← Real.sqrt_eq_rpow]
  have hden : Real.sqrt (6 / π ^ 2 * (τ * mD τ)) = Real.sqrt 6 / π * Real.sqrt τ * Real.sqrt (mD τ) := by
    rw [show 6 / π ^ 2 * (τ * mD τ) = (6 / π ^ 2) * τ * mD τ by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_div (by norm_num), Real.sqrt_sq Real.pi_pos.le]
  unfold warpAmpScal
  rw [hH, hm, hmd, hden, hs_eq, hτm12, hmDm12]
  field_simp [hsq_pos.ne', hsm_pos.ne', hs6_pos.ne', hsh_pos.ne', Real.pi_pos.ne', hτ.ne']

lemma warpAmpScal_eq_Ici {τ : ℝ} (hτ : 0 < τ) :
    warpAmpScal τ =
      (π ^ 2 * Real.sqrt (π ^ 2 / 6)) * uctM τ * (τ * mPrime τ) ^ (-(1 / 2 : ℝ)) *
        τ ^ (1 / 2 : ℝ) * (Real.cosh (π * τ) / Real.sinh (π * τ) ^ 2) := by
  have hH := norm_uctHstar_edge hτ
  have hmp : uctMderiv τ = mPrime τ := uctMderiv_eq_mPrime hτ
  have hmp_pos : 0 < mPrime τ := CtOuter.mPrime_pos hτ
  have htmp_pos : 0 < τ * mPrime τ := mul_pos hτ hmp_pos
  have hden : Real.sqrt (6 / π ^ 2 * mPrime τ) =
      (Real.sqrt (π ^ 2 / 6))⁻¹ * (Real.sqrt (τ * mPrime τ) * (Real.sqrt τ)⁻¹) := by
    have h6p : Real.sqrt (6 / π ^ 2) = (Real.sqrt (π ^ 2 / 6))⁻¹ := by
      rw [← Real.sqrt_inv, inv_div]
    rw [Real.sqrt_mul (by positivity), h6p, Real.sqrt_mul hτ.le]
    field_simp [(Real.sqrt_pos.mpr hτ).ne']
  have hr1 : (τ * mPrime τ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (τ * mPrime τ))⁻¹ := by
    rw [Real.rpow_neg htmp_pos.le, ← Real.sqrt_eq_rpow]
  have hr2 : τ ^ (1 / 2 : ℝ) = Real.sqrt τ := (Real.sqrt_eq_rpow τ).symm
  unfold warpAmpScal
  rw [hH, hmp, hden, hr1, hr2]
  have hsh_pos : 0 < Real.sinh (π * τ) := Real.sinh_pos_iff.mpr (by positivity)
  have hsqp : 0 < Real.sqrt (π ^ 2 / 6) := Real.sqrt_pos.mpr (by positivity)
  field_simp [(Real.sqrt_pos.mpr htmp_pos).ne', (Real.sqrt_pos.mpr hτ).ne', hsh_pos.ne', hsqp.ne']

lemma sinh_kernel_Ici_symW :
    ∃ K : ℕ → ℝ, FctSym.SymW (Ici (1 / 8 : ℝ)) (fun τ => Real.exp (-(π / 2 * τ))) K
      (fun τ => Real.cosh (π * τ) / Real.sinh (π * τ) ^ 2) := by
  let y : ℝ → ℝ := fun τ => Real.exp (-(π * τ))
  have hy_cd : ContDiff ℝ ∞ y := Real.contDiff_exp.comp (contDiff_const.mul contDiff_id).neg
  have hy_bd : ∀ k : ℕ, ∀ τ : ℝ, |iteratedDeriv k y τ| ≤ π ^ k * Real.exp (-(π * τ)) := by
    intro k τ
    have hpow : iteratedDeriv k y τ = (-π) ^ k * Real.exp (-(π * τ)) := by
      induction k generalizing τ with
      | zero => simp [y]
      | succ k ih =>
        rw [iteratedDeriv_succ, show iteratedDeriv k y = fun s => (-π) ^ k * Real.exp (-(π * s)) from funext ih]
        have hd : HasDerivAt (fun s => (-π) ^ k * Real.exp (-(π * s)))
            ((-π) ^ k * ((-π) * Real.exp (-(π * τ)))) τ := by
          have h1 : HasDerivAt (fun s => -(π * s)) (-π) τ := by
            have hd0 := ((hasDerivAt_id τ).const_mul π).neg
            exact hd0.congr_deriv (by ring)
          exact ((h1.exp).const_mul ((-π) ^ k)).congr_deriv (by ring)
        rw [hd.deriv, pow_succ]; ring
    rw [hpow, abs_mul, abs_pow, abs_neg, abs_of_pos Real.pi_pos, abs_of_pos (Real.exp_pos _)]
  let r0 : ℝ := Real.exp (-(π / 8))
  have hr0_lt : r0 < 3 / 4 := by
    have h1 : (π / 8 : ℝ) > 3 / 8 := by linarith [Real.pi_gt_three]
    have h2 : (4 / 3 : ℝ) < Real.exp (3 / 8 : ℝ) := by
      have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 / 8 by norm_num) 2
      norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
      linarith
    have h3 : 4 / 3 < Real.exp (π / 8) := h2.trans (Real.exp_lt_exp.mpr h1)
    dsimp only [r0]; rw [Real.exp_neg]
    exact inv_lt_of_inv_lt₀ (by positivity) (by linarith)
  let Ψ : ℝ → ℝ := fun z => 2 * (1 + z ^ 2) / (1 - z ^ 2) ^ 2
  have hΨ_cd : ContDiffOn ℝ ∞ Ψ (Ioo (-9 / 10 : ℝ) (9 / 10)) := by
    have hnum : ContDiffOn ℝ ∞ (fun z : ℝ => 2 * (1 + z ^ 2)) (Ioo (-9 / 10 : ℝ) (9 / 10)) :=
      (contDiff_const.mul (contDiff_const.add (contDiff_id.pow 2))).contDiffOn
    have hden : ContDiffOn ℝ ∞ (fun z : ℝ => (1 - z ^ 2) ^ 2) (Ioo (-9 / 10 : ℝ) (9 / 10)) :=
      ((contDiff_const.sub (contDiff_id.pow 2)).pow 2).contDiffOn
    refine hnum.div hden fun z hz => ?_
    have hz1 : z ^ 2 ≤ (9 / 10 : ℝ) ^ 2 := by nlinarith [hz.1, hz.2]
    exact pow_ne_zero 2 (by linarith)
  have hmem : ∀ τ : ℝ, 1 / 8 ≤ τ → y τ ∈ Icc (0 : ℝ) (3 / 4) := fun τ hτ => by
    refine ⟨(Real.exp_pos _).le, ?_⟩
    have h1 : y τ ≤ r0 := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    exact h1.trans hr0_lt.le
  have hbΨ : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ Icc (0 : ℝ) (3 / 4), |iteratedDeriv j Ψ z| ≤ B := by
    intro j
    have hcdj : ContinuousOn (iteratedDeriv j Ψ) (Icc (0 : ℝ) (3 / 4)) := by
      have hcd_j := (FctSym.contDiffOn_iteratedDeriv_gen isOpen_Ioo hΨ_cd j).continuousOn
      exact hcd_j.mono fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcdj
    exact ⟨max B 0, le_max_right _ _, fun z hz => (Real.norm_eq_abs _ ▸ hB z hz).trans (le_max_left _ _)⟩
  choose BΨ hBΨ_nn hBΨ using hbΨ
  have h_comp_bd : ∀ k : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ τ : ℝ, 1 / 8 ≤ τ →
      |iteratedDeriv k (fun t => Ψ (y t)) τ| ≤ D := by
    intro k
    let U : Set ℝ := Ioi (1 / 16 : ℝ)
    have hU : IsOpen U := isOpen_Ioi
    have huΨ : MapsTo y U (Ioo (-9 / 10 : ℝ) (9 / 10)) := fun τ hτ => by
      have hτ16 : 1 / 16 < τ := hτ
      have h1 : y τ ≤ Real.exp (-(π / 16)) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hτ16])
      have h2 : Real.exp (-(π / 16)) < 9 / 10 := by
        have hpi : (π / 16 : ℝ) > 3 / 16 := by linarith [Real.pi_gt_three]
        have h3 : 10 / 9 < Real.exp (3 / 16 : ℝ) := by
          have hs := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 / 16 by norm_num) 3
          norm_num [Finset.sum_range_succ, Nat.factorial] at hs
          linarith
        have h4 : 10 / 9 < Real.exp (π / 16) := h3.trans (Real.exp_lt_exp.mpr hpi)
        rw [Real.exp_neg]; exact inv_lt_of_inv_lt₀ (by positivity) (by linarith)
      exact ⟨by linarith [Real.exp_pos (-(π * τ))], h1.trans_lt h2⟩
    let Bmax : ℝ := 1 + ∑ j ∈ range (k + 1), BΨ j
    have hBmax_nn : 0 ≤ Bmax := by
      have hs : 0 ≤ ∑ j ∈ range (k + 1), BΨ j := Finset.sum_nonneg fun j _ => hBΨ_nn j
      dsimp only [Bmax]; linarith
    let Pmax : ℝ := 1 + max 1 π
    have hP1 : 1 ≤ Pmax := by linarith [le_max_left (1 : ℝ) π]
    refine ⟨(Nat.factorial k : ℝ) * Bmax * Pmax ^ k, by positivity, fun τ hτ => ?_⟩
    have hV_o : IsOpen (Ioo (-9 / 10 : ℝ) (9 / 10)) := isOpen_Ioo
    have hmem_τ : τ ∈ U := lt_of_lt_of_le (by norm_num) hτ
    have hΨ_V : ContDiffOn ℝ k Ψ (Ioo (-9 / 10 : ℝ) (9 / 10)) :=
      hΨ_cd.of_le (by exact_mod_cast le_top)
    have hy_U : ContDiffOn ℝ k y U := hy_cd.contDiffOn.of_le (by exact_mod_cast le_top)
    have hcomp := norm_iteratedFDerivWithin_comp_le (g := Ψ) (f := y) (n := k) (N := k)
      hΨ_V hy_U (by exact_mod_cast (le_refl k)) hV_o.uniqueDiffOn hU.uniqueDiffOn huΨ hmem_τ
      (C := Bmax) (D := Pmax)
      (fun {j} hj => by
        rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
          iteratedDerivWithin_of_isOpen hV_o (huΨ hmem_τ), Real.norm_eq_abs]
        have hBj := hBΨ j (y τ) (hmem τ hτ)
        have hle := Finset.single_le_sum (f := BΨ) (fun m _ => hBΨ_nn m) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
        linarith)
      (fun {j} _ hj => by
        rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
          iteratedDerivWithin_of_isOpen hU hmem_τ, Real.norm_eq_abs]
        have hyj := hy_bd j τ
        have hexp1 : Real.exp (-(π * τ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hτ])
        have hpi_le : π ^ j ≤ Pmax ^ j := pow_le_pow_left₀ Real.pi_pos.le (by linarith [le_max_right (1 : ℝ) π]) j
        calc |iteratedDeriv j y τ| ≤ π ^ j * Real.exp (-(π * τ)) := hyj
          _ ≤ π ^ j * 1 := mul_le_mul_of_nonneg_left hexp1 (pow_nonneg Real.pi_pos.le j)
          _ ≤ Pmax ^ j := by linarith)
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, iteratedDerivWithin_of_isOpen hU hmem_τ,
      Real.norm_eq_abs] at hcomp
    simpa [Function.comp_def] using hcomp
  choose DΨ hDΨ_nn hDΨ using h_comp_bd
  have heq_cs : EqOn (fun τ : ℝ => y τ * Ψ (y τ)) (fun τ : ℝ => Real.cosh (π * τ) / Real.sinh (π * τ) ^ 2)
      (Ioi (1 / 16 : ℝ)) := by
    intro τ hτ
    have hτ16 : (1 / 16 : ℝ) < τ := hτ
    have hτ_pos : (0 : ℝ) < τ := lt_trans (by norm_num) hτ16
    have hpi : 0 < π * τ := mul_pos Real.pi_pos hτ_pos
    have hsh_ne : Real.sinh (π * τ) ≠ 0 := (Real.sinh_pos_iff.mpr hpi).ne'
    have h1y : 1 - y τ ^ 2 ≠ 0 := by
      have hy1 : y τ < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      have hy0 : 0 < y τ := Real.exp_pos _
      nlinarith
    dsimp only [y, Ψ]
    rw [Real.cosh_eq, Real.sinh_eq]
    have hm1 : Real.exp (-(π * τ)) * Real.exp (π * τ) = 1 := by rw [← Real.exp_add]; simp
    have hsub : 1 - Real.exp (-(π * τ)) ^ 2 = Real.exp (-(π * τ)) * (Real.exp (π * τ) - Real.exp (-(π * τ))) := by
      calc 1 - Real.exp (-(π * τ)) ^ 2 = Real.exp (-(π * τ)) * Real.exp (π * τ) - Real.exp (-(π * τ)) ^ 2 := by rw [hm1]
        _ = Real.exp (-(π * τ)) * (Real.exp (π * τ) - Real.exp (-(π * τ))) := by ring
    have hadd : 1 + Real.exp (-(π * τ)) ^ 2 = Real.exp (-(π * τ)) * (Real.exp (π * τ) + Real.exp (-(π * τ))) := by
      calc 1 + Real.exp (-(π * τ)) ^ 2 = Real.exp (-(π * τ)) * Real.exp (π * τ) + Real.exp (-(π * τ)) ^ 2 := by rw [hm1]
        _ = Real.exp (-(π * τ)) * (Real.exp (π * τ) + Real.exp (-(π * τ))) := by ring
    rw [hsub, hadd]
    have hexp_pos : Real.exp (-(π * τ)) ≠ 0 := Real.exp_ne_zero _
    have hs_pos : Real.exp (π * τ) - Real.exp (-(π * τ)) ≠ 0 := by
      have hlt : Real.exp (-(π * τ)) < Real.exp (π * τ) := Real.exp_lt_exp.mpr (by linarith)
      linarith
    field_simp
  have hev_cs : ∀ τ : ℝ, 1 / 8 ≤ τ →
      (fun t => Real.cosh (π * t) / Real.sinh (π * t) ^ 2) =ᶠ[𝓝 τ] fun t => y t * Ψ (y t) := fun τ hτ =>
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds (by linarith : (1 / 16 : ℝ) < τ)) fun t ht => (heq_cs ht).symm
  have hpow_exp : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : ℝ, 0 ≤ τ → τ ^ k * Real.exp (-(π / 2 * τ)) ≤ M := by
    intro k
    obtain ⟨M, hM0, hM⟩ := poly_exp_le_n k
    refine ⟨M * (2 ^ k), by positivity, fun τ hτ => ?_⟩
    have hk2 : τ ^ k ≤ 2 ^ k * (1 + τ / 2) ^ k := by
      have h1 : τ ≤ 2 * (1 + τ / 2) := by linarith
      calc τ ^ k ≤ (2 * (1 + τ / 2)) ^ k := pow_le_pow_left₀ hτ h1 k
        _ = 2 ^ k * (1 + τ / 2) ^ k := mul_pow 2 (1 + τ / 2) k
    have hm := hM (τ / 2) (by linarith)
    calc τ ^ k * Real.exp (-(π / 2 * τ))
        ≤ 2 ^ k * ((1 + τ / 2) ^ k * Real.exp (-(π * (τ / 2)))) := by
          have hex : -(π / 2 * τ) = -(π * (τ / 2)) := by ring
          rw [hex]
          calc τ ^ k * Real.exp (-(π * (τ / 2))) ≤ (2 ^ k * (1 + τ / 2) ^ k) * Real.exp (-(π * (τ / 2))) :=
                mul_le_mul_of_nonneg_right hk2 (Real.exp_pos _).le
            _ = _ := by ring
      _ ≤ 2 ^ k * M := mul_le_mul_of_nonneg_left hm (pow_nonneg (by norm_num) k)
      _ = M * 2 ^ k := by ring
  choose Mpe hMpe_nn hMpe using hpow_exp
  refine ⟨fun k => (∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * π ^ j * DΨ (k - j)) * Mpe k, ?_⟩
  refine
    { pos := fun _ hx => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ _ from hx)
      smooth := ?_
      K_nonneg := fun k => mul_nonneg (Finset.sum_nonneg fun j _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg Real.pi_pos.le j)) (hDΨ_nn _)) (hMpe_nn k)
      w_nonneg := fun _ _ => (Real.exp_pos _).le
      bound := fun k τ hτ => ?_ }
  · refine ⟨Ioi (1 / 16 : ℝ), isOpen_Ioi, fun τ hτ => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ τ from hτ), ?_⟩
    have hc2 : ContDiffOn ℝ ∞ (fun t => Real.cosh (π * t)) (Ioi (1 / 16 : ℝ)) :=
      (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)).contDiffOn
    have hs2 : ContDiffOn ℝ ∞ (fun t => Real.sinh (π * t) ^ 2) (Ioi (1 / 16 : ℝ)) :=
      ((Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id)).pow 2).contDiffOn
    exact hc2.div hs2 fun t ht => pow_ne_zero 2 (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos (lt_trans (by norm_num) (show (1 / 16 : ℝ) < t from ht)))).ne'
  · rw [(hev_cs τ hτ).iteratedDeriv_eq k]
    have hy_at : ContDiffAt ℝ k y τ := hy_cd.contDiffAt.of_le (by exact_mod_cast le_top)
    have hΨ_at : ContDiffAt ℝ k (fun t => Ψ (y t)) τ := by
      have hm_τ : y τ ∈ Ioo (-9 / 10 : ℝ) (9 / 10) :=
        ⟨by linarith [(hmem τ hτ).1], by linarith [(hmem τ hτ).2]⟩
      exact ((hΨ_cd.contDiffAt (isOpen_Ioo.mem_nhds hm_τ)).comp τ hy_cd.contDiffAt).of_le
        (by exact_mod_cast le_top)
    rw [show (fun t => y t * Ψ (y t)) = y * (fun t => Ψ (y t)) from rfl, iteratedDeriv_mul hy_at hΨ_at]
    have hτ_pos : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
    have hτ_nn : 0 ≤ τ := hτ_pos.le
    have hsum_bd : |∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * iteratedDeriv j y τ * iteratedDeriv (k - j) (fun t => Ψ (y t)) τ| ≤
        (∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * π ^ j * DΨ (k - j)) * Real.exp (-(π * τ)) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      have h1 := hy_bd j τ
      have h2 := hDΨ (k - j) τ hτ
      have hexp0 : 0 ≤ Real.exp (-(π * τ)) := (Real.exp_pos _).le
      calc (Nat.choose k j : ℝ) * |iteratedDeriv j y τ| * |iteratedDeriv (k - j) (fun t => Ψ (y t)) τ|
          ≤ (Nat.choose k j : ℝ) * (π ^ j * Real.exp (-(π * τ))) * DΨ (k - j) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (abs_nonneg _) (by positivity)
        _ = (Nat.choose k j : ℝ) * π ^ j * DΨ (k - j) * Real.exp (-(π * τ)) := by ring
    have hexp_split : Real.exp (-(π * τ)) = Real.exp (-(π / 2 * τ)) * Real.exp (-(π / 2 * τ)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hS_nn : 0 ≤ ∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * π ^ j * DΨ (k - j) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg Real.pi_pos.le j)) (hDΨ_nn _)
    have hpe : τ ^ k * Real.exp (-(π / 2 * τ)) ≤ Mpe k := hMpe k τ hτ_nn
    have hpk_pos : 0 < τ ^ k := pow_pos hτ_pos k
    have hexp_pe : Real.exp (-(π / 2 * τ)) ≤ Mpe k * (τ ^ k)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpk_pos, mul_comm]
      exact hpe
    calc |∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * iteratedDeriv j y τ * iteratedDeriv (k - j) (fun t => Ψ (y t)) τ|
        ≤ (∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * π ^ j * DΨ (k - j)) *
            (Real.exp (-(π / 2 * τ)) * Real.exp (-(π / 2 * τ))) := by rw [← hexp_split]; exact hsum_bd
      _ ≤ (∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * π ^ j * DΨ (k - j)) *
            ((Mpe k * (τ ^ k)⁻¹) * Real.exp (-(π / 2 * τ))) := by
            gcongr
      _ = (∑ j ∈ range (k + 1), (Nat.choose k j : ℝ) * π ^ j * DΨ (k - j)) * Mpe k *
            Real.exp (-(π / 2 * τ)) * (τ ^ k)⁻¹ := by ring

lemma warpAmpScal_Ioc_symW :
    ∃ K : ℕ → ℝ, FctSym.SymW (Ioc (0 : ℝ) (1 / 8)) (fun τ => τ ^ (-(1 / 2 : ℝ))) K warpAmpScal := by
  have hmD_sym : ∃ K, FctSym.SymW (Ioc (0 : ℝ) (1 / 8)) (fun _ => 1) K (fun τ => (mD τ) ^ (-(1 / 2 : ℝ))) := by
    obtain ⟨K, hK⟩ := FctSym.mD_symW
    obtain ⟨m0, hm0, hge⟩ := FctSym.mD_ge
    have hmD_le : ∃ M0 : ℝ, 0 ≤ M0 ∧ ∀ τ ∈ Ioc (0 : ℝ) (1 / 8), mD τ ≤ M0 := by
      obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 8)).exists_bound_of_continuousOn
        (contDiffOn_mD.continuousOn.mono fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      refine ⟨max M 0, le_max_right _ _, fun t ht => ?_⟩
      exact ((le_abs_self _).trans (Real.norm_eq_abs _ ▸ hM t ⟨ht.1.le, ht.2⟩)).trans (le_max_left M 0)
    obtain ⟨M0, hM0, hm_le⟩ := hmD_le
    have hΦ_cd : ContDiffOn ℝ ∞ (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) (Ioi 0) := fun y hy =>
      (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hy)).contDiffWithinAt
    have hbP : ∀ j : ℕ, ∃ P : ℝ, 0 ≤ P ∧ ∀ z ∈ Icc m0 (max m0 M0),
        |iteratedDeriv j (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) z| ≤ P := fun j => by
      have hcdj := (FctSym.contDiffOn_iteratedDeriv_gen isOpen_Ioi hΦ_cd j).continuousOn
      obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (hcdj.mono fun z hz => lt_of_lt_of_le hm0 hz.1)
      exact ⟨max B 0, le_max_right _ _, fun z hz => (Real.norm_eq_abs _ ▸ hB z hz).trans (le_max_left _ _)⟩
    choose P hP0 hP using hbP
    have hL0 : 0 ≤ m0 ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos hm0 _).le
    refine ⟨_, hK.comp_smooth (B := 1) (L := m0 ^ (-(1 / 2 : ℝ))) isOpen_Ioi hΦ_cd
      (fun τ hτ => hm0.trans_le (hge τ hτ))
      (fun j τ hτ => hP j (mD τ) ⟨hge τ hτ, (hm_le τ hτ).trans (le_max_right _ _)⟩) hP0
      (fun _ _ => le_rfl) hL0 (fun τ hτ => by
        rw [mul_one, abs_of_pos (Real.rpow_pos_of_pos (hm0.trans_le (hge τ hτ)) _)]
        exact Real.rpow_le_rpow_of_nonpos hm0 (hge τ hτ) (by norm_num))⟩
  obtain ⟨KmD, hmD⟩ := hmD_sym
  have hQ_sym : ∃ K, FctSym.SymW (Ioc (0 : ℝ) (1 / 8)) (fun _ => 1) K mQ := by
    choose B hB using fun j => CtMDeriv.bdd_iter_on_compact (isOpen_Ioo (a := (-1 / 4 : ℝ)) (b := 1 / 4)) contDiffOn_mQ
      (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 8)) (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) j
    exact ⟨_, FctSym.SymW.of_bdd (b := 1 / 8) (by norm_num) isOpen_Ioo
      (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) contDiffOn_mQ (fun r x hx => hB r x ⟨hx.1.le, hx.2⟩)⟩
  obtain ⟨KmQ, hmQ⟩ := hQ_sym
  let G0 : ℝ → ℝ := fun τ => (π / Real.sqrt 6) * Real.cosh (π * τ) * uctSincH (π * τ) ^ 2
  have hG0_cd : ContDiff ℝ ⊤ G0 :=
    ((contDiff_const.mul (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)))).mul
      ((contDiff_uctSincH.comp (contDiff_const.mul contDiff_id)).pow 2)
  have hG0_sym : ∃ K, FctSym.SymW (Ioc (0 : ℝ) (1 / 8)) (fun _ => 1) K G0 := by
    choose B hB using fun j => CtMDeriv.bdd_iter_on_compact isOpen_univ (hG0_cd.of_le le_top).contDiffOn
      (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 8)) (fun _ _ => mem_univ _) j
    exact ⟨_, FctSym.SymW.of_bdd (b := 1 / 8) (by norm_num) isOpen_univ (subset_univ _)
      (hG0_cd.of_le le_top).contDiffOn (fun r x hx => hB r x ⟨hx.1.le, hx.2⟩)⟩
  obtain ⟨KG0, hG0⟩ := hG0_sym
  have hrp_neg12 := FctSym.SymW.rpow_gen (S := Ioc (0 : ℝ) (1 / 8)) (fun _ hx => hx.1) 1 (-(1 / 2 : ℝ))
  have hprod_Ioc := ((hrp_neg12.mul hmQ).mul hmD).mul hG0
  have hcon := hprod_Ioc.congr (U := Ioo (0 : ℝ) (1 / 4)) isOpen_Ioo
    (fun τ hτ => ⟨hτ.1, by linarith [hτ.2]⟩) (g := warpAmpScal) fun τ hτ => by
      rw [warpAmpScal_eq_Ioc hτ.1 hτ.2]; dsimp only [G0]; ring
  refine ⟨_, hcon.of_le (fun τ hτ => ?_) (fun _ => le_rfl)⟩
  rw [abs_one, one_mul, mul_one, mul_one, mul_one]

lemma warpAmpScal_Ici_symW :
    ∃ K : ℕ → ℝ, FctSym.SymW (Ici (1 / 8 : ℝ)) (fun τ => Real.exp (-(π / 4 * τ))) K warpAmpScal := by
  have hm_sym : ∃ K, FctSym.SymW (Ici (1 / 8 : ℝ)) (fun τ => 1 + τ) K uctM := by
    obtain ⟨Am, hAm0, hAm⟩ := FctSym.uctM_deriv_symbol
    have hCm0 : 0 ≤ π / 2 := by positivity
    refine ⟨Nat.rec (π / 2) (fun j _ => Am j), ?_⟩
    refine
      { pos := fun _ hx => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ _ from hx)
        smooth := ⟨Ioi 0, isOpen_Ioi, fun _ hx => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ _ from hx),
          contDiffOn_uctM⟩
        K_nonneg := fun r => by cases r with
          | zero => exact hCm0
          | succ j => exact hAm0 j
        w_nonneg := fun τ hτ => by linarith [show (1 / 8 : ℝ) ≤ τ from hτ]
        bound := fun r τ hτ => ?_ }
    have hτ0 : 0 < τ := lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ τ from hτ)
    cases r with
    | zero =>
      simp only [iteratedDeriv_zero, pow_zero, inv_one, mul_one, abs_of_pos (uctM_pos hτ0)]
      have h1 : uctM τ ≤ π * τ / 2 := FctSym.uctM_le_linear hτ0
      have h2 : π * τ / 2 ≤ π / 2 * (1 + τ) := by nlinarith [Real.pi_pos]
      exact h1.trans h2
    | succ j =>
      rw [iteratedDeriv_succ']
      have hbd := hAm j τ hτ0
      have h1t : 1 ≤ 1 + τ := by linarith
      have hnn : 0 ≤ Am j := hAm0 j
      have hpinv : 0 ≤ (τ ^ (j + 1))⁻¹ := inv_nonneg.mpr (pow_nonneg hτ0.le _)
      calc |iteratedDeriv j (deriv uctM) τ| ≤ Am j * 1 * (τ ^ (j + 1))⁻¹ := hbd
        _ ≤ Am j * (1 + τ) * (τ ^ (j + 1))⁻¹ := by gcongr
  obtain ⟨Km, hm⟩ := hm_sym
  have hθm12_sym : ∃ K, FctSym.SymW (Ici (1 / 8 : ℝ)) (fun _ => 1) K
      (fun τ => (τ * mPrime τ) ^ (-(1 / 2 : ℝ))) := by
    obtain ⟨Kth, hKth⟩ := FctSym.theta_symW_Ici
    obtain ⟨Kmp, hKmp⟩ := FctSym.mPrime_symW
    have hθ_ge : ∀ τ ∈ Ici (1 / 8 : ℝ), (π * (1 / 8)) ^ 2 / (6 + (π * (1 / 8)) ^ 2) ≤ τ * mPrime τ :=
      fun _ hx => theta_ge_Ici hx
    let θ0 : ℝ := (π * (1 / 8)) ^ 2 / (6 + (π * (1 / 8)) ^ 2)
    have hθ0_pos : 0 < θ0 := by positivity
    have hθ_le : ∀ τ ∈ Ici (1 / 8 : ℝ), τ * mPrime τ ≤ Kmp 0 + θ0 := fun τ hτ => by
      have hτ0 : 0 < τ := lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ τ from hτ)
      have hb := hKmp.bound 0 τ hτ0
      simp only [iteratedDeriv_zero, pow_zero, inv_one, mul_one] at hb
      have hdiv : τ / (1 + τ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      have hmp_nn : 0 ≤ mPrime τ := (CtOuter.mPrime_pos hτ0).le
      calc τ * mPrime τ ≤ τ * (Kmp 0 * (1 + τ)⁻¹) :=
            mul_le_mul_of_nonneg_left ((le_abs_self _).trans hb) hτ0.le
        _ = Kmp 0 * (τ / (1 + τ)) := by ring
        _ ≤ Kmp 0 * 1 := mul_le_mul_of_nonneg_left hdiv (hKmp.K_nonneg 0)
        _ ≤ Kmp 0 + θ0 := by linarith [hθ0_pos]
    have hΦ_cd : ContDiffOn ℝ ∞ (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) (Ioi 0) := fun y hy =>
      (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hy)).contDiffWithinAt
    have hbP : ∀ j : ℕ, ∃ P : ℝ, 0 ≤ P ∧ ∀ z ∈ Icc θ0 (Kmp 0 + θ0),
        |iteratedDeriv j (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) z| ≤ P := fun j => by
      have hcdj := (FctSym.contDiffOn_iteratedDeriv_gen isOpen_Ioi hΦ_cd j).continuousOn
      obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (hcdj.mono fun z hz => lt_of_lt_of_le hθ0_pos hz.1)
      exact ⟨max B 0, le_max_right _ _, fun z hz => (Real.norm_eq_abs _ ▸ hB z hz).trans (le_max_left _ _)⟩
    choose P hP0 hP using hbP
    refine ⟨_, hKth.comp_smooth (B := 1) (L := θ0 ^ (-(1 / 2 : ℝ))) isOpen_Ioi hΦ_cd
      (fun τ hτ => hθ0_pos.trans_le (hθ_ge τ hτ))
      (fun j τ hτ => hP j (τ * mPrime τ) ⟨hθ_ge τ hτ, hθ_le τ hτ⟩) hP0 (fun _ _ => le_rfl)
      (Real.rpow_pos_of_pos hθ0_pos _).le (fun τ hτ => by
        rw [mul_one, abs_of_pos (Real.rpow_pos_of_pos (hθ0_pos.trans_le (hθ_ge τ hτ)) _)]
        exact Real.rpow_le_rpow_of_nonpos hθ0_pos (hθ_ge τ hτ) (by norm_num))⟩
  obtain ⟨Kth, hth⟩ := hθm12_sym
  obtain ⟨Ks, hs⟩ := sinh_kernel_Ici_symW
  have hrp := FctSym.SymW.rpow_gen (S := Ici (1 / 8 : ℝ))
    (fun _ hx => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ _ from hx)) 1 (1 / 2 : ℝ)
  let c0 : ℝ := π ^ 2 * Real.sqrt (π ^ 2 / 6)
  have hprod := (((hm.smul c0).mul hth).mul hrp).mul hs
  have hcon := hprod.congr (U := Ioi 0) isOpen_Ioi
    (fun τ hτ => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ _ from hτ))
    (g := warpAmpScal) fun τ hτ => by rw [warpAmpScal_eq_Ici hτ]; ring
  obtain ⟨M2, hM20, hM2⟩ := poly_exp_le_n 2
  let C_e : ℝ := |c0| * (16 * M2) + 1
  have hCe_pos : 0 < C_e := by positivity
  let K_all : ℕ → ℝ :=
    FctSym.SymW.Kmul (FctSym.SymW.Kmul (FctSym.SymW.Kmul Km Kth) (fun r => ∏ i ∈ range r, |(1 / 2 : ℝ) - (i : ℝ)|)) Ks
  refine ⟨fun k => C_e * K_all k, ?_⟩
  exact
    { pos := hcon.pos
      smooth := hcon.smooth
      K_nonneg := fun k => mul_nonneg hCe_pos.le (hcon.K_nonneg k)
      w_nonneg := fun _ _ => (Real.exp_pos _).le
      bound := fun k τ hτ => by
        have hτ0 : 0 < τ := lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ _ from hτ)
        have hbd := hcon.bound k τ hτ
        have hw_le : |c0| * (1 + τ) * 1 * (|1| * τ ^ (1 / 2 : ℝ)) * Real.exp (-(π / 2 * τ)) ≤
            C_e * Real.exp (-(π / 4 * τ)) := by
          have hexp_split : Real.exp (-(π / 2 * τ)) = Real.exp (-(π / 4 * τ)) * Real.exp (-(π / 4 * τ)) := by
            rw [← Real.exp_add]; congr 1; ring
          have hr12 : τ ^ (1 / 2 : ℝ) ≤ 1 + τ := by
            rw [← Real.sqrt_eq_rpow]
            exact (Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith [hτ0]⟩)
          have hsq4 : (1 + τ) ^ 2 ≤ 16 * (1 + τ / 4) ^ 2 := by
            have h1 : 1 + τ ≤ 4 * (1 + τ / 4) := by linarith
            calc (1 + τ) ^ 2 ≤ (4 * (1 + τ / 4)) ^ 2 := sq_le_sq' (by linarith) h1
              _ = 16 * (1 + τ / 4) ^ 2 := by ring
          have hm2 := hM2 (τ / 4) (by linarith)
          have hexp4 : Real.exp (-(π / 4 * τ)) = Real.exp (-(π * (τ / 4))) := by congr 1; ring
          have he1 : (1 + τ) * τ ^ (1 / 2 : ℝ) * Real.exp (-(π / 4 * τ)) ≤ 16 * M2 := by
            calc (1 + τ) * τ ^ (1 / 2 : ℝ) * Real.exp (-(π / 4 * τ))
                ≤ (1 + τ) * (1 + τ) * Real.exp (-(π / 4 * τ)) := by
                  gcongr
              _ = (1 + τ) ^ 2 * Real.exp (-(π / 4 * τ)) := by ring
              _ ≤ 16 * (1 + τ / 4) ^ 2 * Real.exp (-(π * (τ / 4))) := by
                  rw [hexp4]; gcongr
              _ = 16 * ((1 + τ / 4) ^ 2 * Real.exp (-(π * (τ / 4)))) := by ring
              _ ≤ 16 * M2 := mul_le_mul_of_nonneg_left hm2 (by norm_num)
          rw [abs_one, one_mul, mul_one, hexp_split]
          calc |c0| * (1 + τ) * τ ^ (1 / 2 : ℝ) * (Real.exp (-(π / 4 * τ)) * Real.exp (-(π / 4 * τ)))
              = |c0| * ((1 + τ) * τ ^ (1 / 2 : ℝ) * Real.exp (-(π / 4 * τ))) * Real.exp (-(π / 4 * τ)) := by ring
            _ ≤ |c0| * (16 * M2) * Real.exp (-(π / 4 * τ)) := by
                  gcongr
            _ ≤ C_e * Real.exp (-(π / 4 * τ)) := by
                  gcongr; linarith
        refine hbd.trans ?_
        have hK_nn : 0 ≤ K_all k := hcon.K_nonneg k
        have htauk_nn : 0 ≤ (τ ^ k)⁻¹ := inv_nonneg.mpr (pow_nonneg hτ0.le k)
        calc K_all k * (|c0| * (1 + τ) * 1 * (|1| * τ ^ (1 / 2 : ℝ)) * Real.exp (-(π / 2 * τ))) * (τ ^ k)⁻¹
            ≤ K_all k * (C_e * Real.exp (-(π / 4 * τ))) * (τ ^ k)⁻¹ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw_le hK_nn) htauk_nn
          _ = C_e * K_all k * Real.exp (-(π / 4 * τ)) * (τ ^ k)⁻¹ := by ring }

lemma contDiffOn_warpAmpScal : ContDiffOn ℝ ∞ warpAmpScal (Ioi 0) := by
  obtain ⟨_, hIoc⟩ := warpAmpScal_Ioc_symW
  obtain ⟨_, hIci⟩ := warpAmpScal_Ici_symW
  obtain ⟨U1, hU1o, hSU1, hcd1⟩ := hIoc.smooth
  obtain ⟨U2, hU2o, hSU2, hcd2⟩ := hIci.smooth
  intro τ hτ
  rcases le_or_gt τ (1 / 8) with hle | hgt
  · exact ((hcd1.contDiffAt (hU1o.mem_nhds (hSU1 ⟨hτ, hle⟩))).contDiffWithinAt).of_le
      (WithTop.coe_le_coe.mpr le_top)
  · exact ((hcd2.contDiffAt (hU2o.mem_nhds (hSU2 hgt.le))).contDiffWithinAt).of_le
      (WithTop.coe_le_coe.mpr le_top)

lemma warpAmpScal_edge_bounds (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ n, ∀ τ : ℝ, 0 < τ →
      |iteratedDeriv k warpAmpScal τ| ≤ C * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) * edgeW τ ^ (-(k : ℤ)) := by
  obtain ⟨K1, h1⟩ := warpAmpScal_Ioc_symW
  obtain ⟨K2, h2⟩ := warpAmpScal_Ici_symW
  obtain ⟨M3, hM30, hM3⟩ := poly_exp_le_n 3
  let S1 : ℝ := ∑ j ∈ range (n + 1), K1 j
  let S2 : ℝ := ∑ j ∈ range (n + 1), K2 j
  have hS1 : 0 ≤ S1 := Finset.sum_nonneg fun j _ => h1.K_nonneg j
  have hS2 : 0 ≤ S2 := Finset.sum_nonneg fun j _ => h2.K_nonneg j
  let M_exp : ℝ := 4 ^ 3 * M3
  have hMexp : 0 ≤ M_exp := by positivity
  refine ⟨max (2 * S1) (M_exp * S2), by positivity, fun k hk τ hτ => ?_⟩
  have hτ0 : τ ≠ 0 := hτ.ne'
  have hK1_le : K1 k ≤ S1 := Finset.single_le_sum (fun j _ => h1.K_nonneg j) (Finset.mem_range.mpr (by omega))
  have hK2_le : K2 k ≤ S2 := Finset.single_le_sum (fun j _ => h2.K_nonneg j) (Finset.mem_range.mpr (by omega))
  have htau_inv : (τ ^ k)⁻¹ ≤ edgeW τ ^ (-(k : ℤ)) := by
    rw [show (τ ^ k)⁻¹ = |τ| ^ (-(k : ℤ)) by rw [abs_of_pos hτ, zpow_neg, zpow_natCast]]
    exact abs_inv_le_edgeW_inv hτ0 k
  have hwk_nn : 0 ≤ edgeW τ ^ (-(k : ℤ)) := zpow_nonneg (edgeW_pos hτ0).le _
  have h1t_nn : 0 ≤ (1 + τ) ^ (-2 : ℤ) := zpow_nonneg (by linarith) _
  rcases le_or_gt τ (1 / 8) with hle | hgt
  · have hb := h1.bound k τ ⟨hτ, hle⟩
    have h1t : (1 : ℝ) ≤ 2 * (1 + τ) ^ (-2 : ℤ) := by
      have hsq : (1 + τ) ^ 2 ≤ 2 := by nlinarith
      rw [zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
      have hp : 0 < (1 + τ) ^ 2 := by positivity
      calc (1 : ℝ) = 2 * 2⁻¹ := by ring
        _ ≤ 2 * ((1 + τ) ^ 2)⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ hp hsq) (by norm_num)
    have hrp : 0 ≤ τ ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos hτ _).le
    calc |iteratedDeriv k warpAmpScal τ| ≤ K1 k * τ ^ (-(1 / 2 : ℝ)) * (τ ^ k)⁻¹ := hb
      _ ≤ S1 * τ ^ (-(1 / 2 : ℝ)) * edgeW τ ^ (-(k : ℤ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hK1_le hrp) htau_inv
              (inv_nonneg.mpr (pow_nonneg hτ.le _)) (mul_nonneg hS1 hrp)
      _ = S1 * (1 * τ ^ (-(1 / 2 : ℝ))) * edgeW τ ^ (-(k : ℤ)) := by ring
      _ ≤ S1 * (2 * (1 + τ) ^ (-2 : ℤ) * τ ^ (-(1 / 2 : ℝ))) * edgeW τ ^ (-(k : ℤ)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1t hrp) hS1) hwk_nn
      _ = (2 * S1) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) * edgeW τ ^ (-(k : ℤ)) := by ring
      _ ≤ max (2 * S1) (M_exp * S2) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) * edgeW τ ^ (-(k : ℤ)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hrp) h1t_nn) hwk_nn
  · have hb := h2.bound k τ hgt.le
    have hexp_le : Real.exp (-(π / 4 * τ)) ≤ M_exp * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) := by
      have hm3 := hM3 (τ / 4) (by linarith)
      have hcb : (1 + τ) ^ 3 ≤ 4 ^ 3 * (1 + τ / 4) ^ 3 := by
        have h1' : 1 + τ ≤ 4 * (1 + τ / 4) := by linarith
        calc (1 + τ) ^ 3 ≤ (4 * (1 + τ / 4)) ^ 3 := pow_le_pow_left₀ (by linarith) h1' 3
          _ = 4 ^ 3 * (1 + τ / 4) ^ 3 := by ring
      have hr12 : τ ^ (1 / 2 : ℝ) ≤ 1 + τ := by
        rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
      have hexp4 : Real.exp (-(π / 4 * τ)) = Real.exp (-(π * (τ / 4))) := by congr 1; ring
      have hmain : τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 2 * Real.exp (-(π / 4 * τ)) ≤ M_exp := by
        calc τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 2 * Real.exp (-(π / 4 * τ))
            ≤ (1 + τ) * (1 + τ) ^ 2 * Real.exp (-(π / 4 * τ)) := by gcongr
          _ = (1 + τ) ^ 3 * Real.exp (-(π / 4 * τ)) := by ring
          _ ≤ (4 ^ 3 * (1 + τ / 4) ^ 3) * Real.exp (-(π * (τ / 4))) := by rw [hexp4]; gcongr
          _ = 4 ^ 3 * ((1 + τ / 4) ^ 3 * Real.exp (-(π * (τ / 4)))) := by ring
          _ ≤ M_exp := mul_le_mul_of_nonneg_left hm3 (by positivity)
      have hrneg : (τ ^ (1 / 2 : ℝ))⁻¹ = τ ^ (-(1 / 2 : ℝ)) := (Real.rpow_neg hτ.le _).symm
      have hp1 : 0 < τ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hτ _
      have hp2 : 0 < (1 + τ) ^ 2 := by positivity
      rw [zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, ← hrneg]
      calc Real.exp (-(π / 4 * τ)) = (τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 2 * Real.exp (-(π / 4 * τ))) *
              (τ ^ (1 / 2 : ℝ))⁻¹ * ((1 + τ) ^ 2)⁻¹ := by field_simp
        _ ≤ M_exp * (τ ^ (1 / 2 : ℝ))⁻¹ * ((1 + τ) ^ 2)⁻¹ := by gcongr
    have hrp : 0 ≤ τ ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos hτ _).le
    calc |iteratedDeriv k warpAmpScal τ| ≤ K2 k * Real.exp (-(π / 4 * τ)) * (τ ^ k)⁻¹ := hb
      _ ≤ S2 * (M_exp * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) :=
            mul_le_mul (mul_le_mul hK2_le hexp_le (Real.exp_pos _).le hS2) htau_inv
              (inv_nonneg.mpr (pow_nonneg hτ.le _)) (mul_nonneg hS2 (by positivity))
      _ = (M_exp * S2) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) * edgeW τ ^ (-(k : ℤ)) := by ring
      _ ≤ max (2 * S1) (M_exp * S2) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) * edgeW τ ^ (-(k : ℤ)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hrp) h1t_nn) hwk_nn

lemma tau_mul_warpAmpScal_edge_bounds (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ n, ∀ τ : ℝ, 0 < τ →
      |iteratedDeriv k (fun t => t * warpAmpScal t) τ| ≤
        C * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) * edgeW τ ^ (-(k : ℤ)) := by
  obtain ⟨K1, h1⟩ := warpAmpScal_Ioc_symW
  obtain ⟨K2, h2⟩ := warpAmpScal_Ici_symW
  have hid_Ioc := FctSym.SymW.rpow_gen (S := Ioc (0 : ℝ) (1 / 8)) (fun _ hx => hx.1) 1 (1 : ℝ)
  have hid_Ici := FctSym.SymW.rpow_gen (S := Ici (1 / 8 : ℝ))
    (fun _ hx => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ _ from hx)) 1 (1 : ℝ)
  have hm1 := (hid_Ioc.mul h1).congr (U := Ioo 0 (1 / 4)) isOpen_Ioo
    (fun _ hx => ⟨hx.1, by linarith [hx.2]⟩) (g := fun t => t * warpAmpScal t) fun t ht => by
      simp only [one_mul, Real.rpow_one]
  have hm2 := (hid_Ici.mul h2).congr (U := Ioi 0) isOpen_Ioi
    (fun _ hx => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ _ from hx))
    (g := fun t => t * warpAmpScal t) fun t ht => by
      simp only [one_mul, Real.rpow_one]
  obtain ⟨M4, hM40, hM4⟩ := poly_exp_le_n 4
  let Kp : ℕ → ℝ := fun r => ∏ i ∈ range r, |(1 : ℝ) - (i : ℝ)|
  let Kprod1 : ℕ → ℝ := FctSym.SymW.Kmul Kp K1
  let Kprod2 : ℕ → ℝ := FctSym.SymW.Kmul Kp K2
  let S1 : ℝ := ∑ j ∈ range (n + 1), Kprod1 j
  let S2 : ℝ := ∑ j ∈ range (n + 1), Kprod2 j
  let M_exp : ℝ := 4 ^ 4 * M4
  have hS1 : 0 ≤ S1 := Finset.sum_nonneg fun j _ => hm1.K_nonneg j
  have hS2 : 0 ≤ S2 := Finset.sum_nonneg fun j _ => hm2.K_nonneg j
  have hMexp : 0 ≤ M_exp := by positivity
  refine ⟨max (2 * S1) (M_exp * S2), by positivity, fun k hk τ hτ => ?_⟩
  have hτ0 : τ ≠ 0 := hτ.ne'
  have hK1_le : Kprod1 k ≤ S1 := Finset.single_le_sum (fun j _ => hm1.K_nonneg j) (Finset.mem_range.mpr (by omega))
  have hK2_le : Kprod2 k ≤ S2 := Finset.single_le_sum (fun j _ => hm2.K_nonneg j) (Finset.mem_range.mpr (by omega))
  have htau_inv : (τ ^ k)⁻¹ ≤ edgeW τ ^ (-(k : ℤ)) := by
    rw [show (τ ^ k)⁻¹ = |τ| ^ (-(k : ℤ)) by rw [abs_of_pos hτ, zpow_neg, zpow_natCast]]
    exact abs_inv_le_edgeW_inv hτ0 k
  have hwk_nn : 0 ≤ edgeW τ ^ (-(k : ℤ)) := zpow_nonneg (edgeW_pos hτ0).le _
  have h1t_nn : 0 ≤ (1 + τ) ^ (-2 : ℤ) := zpow_nonneg (by linarith) _
  have hrp_nn : 0 ≤ τ ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos hτ _).le
  rcases le_or_gt τ (1 / 8) with hle | hgt
  · have hb : |iteratedDeriv k (fun t => t * warpAmpScal t) τ| ≤
        Kprod1 k * (|1| * τ ^ (1 : ℝ) * τ ^ (-(1 / 2 : ℝ))) * (τ ^ k)⁻¹ := hm1.bound k τ ⟨hτ, hle⟩
    rw [abs_one, one_mul, Real.rpow_one] at hb
    have hw_le : τ * τ ^ (-(1 / 2 : ℝ)) ≤ 2 * (1 + τ) ^ (-2 : ℤ) * τ ^ (-(1 / 2 : ℝ)) := by
      have hτ1 : τ ≤ 1 := by linarith
      have h1t : (1 : ℝ) ≤ 2 * (1 + τ) ^ (-2 : ℤ) := by
        have hsq : (1 + τ) ^ 2 ≤ 2 := by nlinarith
        rw [zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
        calc (1 : ℝ) = 2 * 2⁻¹ := by ring
          _ ≤ 2 * ((1 + τ) ^ 2)⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hsq) (by norm_num)
      have hcomb := mul_le_mul hτ1 h1t zero_le_one zero_le_one
      rw [mul_one, one_mul] at hcomb
      exact mul_le_mul_of_nonneg_right hcomb hrp_nn
    calc |iteratedDeriv k (fun t => t * warpAmpScal t) τ|
        ≤ Kprod1 k * (τ * τ ^ (-(1 / 2 : ℝ))) * (τ ^ k)⁻¹ := hb
      _ ≤ S1 * (2 * (1 + τ) ^ (-2 : ℤ) * τ ^ (-(1 / 2 : ℝ))) * edgeW τ ^ (-(k : ℤ)) :=
            mul_le_mul (mul_le_mul hK1_le hw_le (mul_nonneg hτ.le hrp_nn) hS1) htau_inv
              (inv_nonneg.mpr (pow_nonneg hτ.le _)) (mul_nonneg hS1 (by positivity))
      _ = (2 * S1) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) * edgeW τ ^ (-(k : ℤ)) := by ring
      _ ≤ max (2 * S1) (M_exp * S2) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) * edgeW τ ^ (-(k : ℤ)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hrp_nn) h1t_nn) hwk_nn
  · have hb : |iteratedDeriv k (fun t => t * warpAmpScal t) τ| ≤
        Kprod2 k * (|1| * τ ^ (1 : ℝ) * Real.exp (-(π / 4 * τ))) * (τ ^ k)⁻¹ := hm2.bound k τ hgt.le
    rw [abs_one, one_mul, Real.rpow_one] at hb
    have hm4 := hM4 (τ / 4) (by linarith)
    have hq4 : (1 + τ) ^ 4 ≤ 4 ^ 4 * (1 + τ / 4) ^ 4 := by
      have h1' : 1 + τ ≤ 4 * (1 + τ / 4) := by linarith
      calc (1 + τ) ^ 4 ≤ (4 * (1 + τ / 4)) ^ 4 := pow_le_pow_left₀ (by linarith) h1' 4
        _ = 4 ^ 4 * (1 + τ / 4) ^ 4 := by ring
    have hr12 : τ ^ (1 / 2 : ℝ) ≤ 1 + τ := by
      rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
    have hexp4 : Real.exp (-(π / 4 * τ)) = Real.exp (-(π * (τ / 4))) := by congr 1; ring
    have hmain : τ * τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 2 * Real.exp (-(π / 4 * τ)) ≤ M_exp := by
      calc τ * τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 2 * Real.exp (-(π / 4 * τ))
          ≤ (1 + τ) * (1 + τ) * (1 + τ) ^ 2 * Real.exp (-(π / 4 * τ)) := by gcongr; linarith
        _ = (1 + τ) ^ 4 * Real.exp (-(π / 4 * τ)) := by ring
        _ ≤ (4 ^ 4 * (1 + τ / 4) ^ 4) * Real.exp (-(π * (τ / 4))) := by rw [hexp4]; gcongr
        _ = 4 ^ 4 * ((1 + τ / 4) ^ 4 * Real.exp (-(π * (τ / 4)))) := by ring
        _ ≤ M_exp := mul_le_mul_of_nonneg_left hm4 (by positivity)
    have hrneg : (τ ^ (1 / 2 : ℝ))⁻¹ = τ ^ (-(1 / 2 : ℝ)) := (Real.rpow_neg hτ.le _).symm
    have h_tau_exp : τ * Real.exp (-(π / 4 * τ)) ≤ M_exp * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) := by
      have hp1 : 0 < τ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hτ _
      have hp2 : 0 < (1 + τ) ^ 2 := by positivity
      rw [zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, ← hrneg]
      calc τ * Real.exp (-(π / 4 * τ)) =
            (τ * τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 2 * Real.exp (-(π / 4 * τ))) *
              (τ ^ (1 / 2 : ℝ))⁻¹ * ((1 + τ) ^ 2)⁻¹ := by field_simp
        _ ≤ M_exp * (τ ^ (1 / 2 : ℝ))⁻¹ * ((1 + τ) ^ 2)⁻¹ := by gcongr
    calc |iteratedDeriv k (fun t => t * warpAmpScal t) τ|
        ≤ Kprod2 k * (τ * Real.exp (-(π / 4 * τ))) * (τ ^ k)⁻¹ := hb
      _ ≤ S2 * (M_exp * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) * edgeW τ ^ (-(k : ℤ)) :=
            mul_le_mul (mul_le_mul hK2_le h_tau_exp (mul_nonneg hτ.le (Real.exp_pos _).le) hS2) htau_inv
              (inv_nonneg.mpr (pow_nonneg hτ.le _)) (mul_nonneg hS2 (by positivity))
      _ = (M_exp * S2) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) * edgeW τ ^ (-(k : ℤ)) := by ring
      _ ≤ max (2 * S1) (M_exp * S2) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) * edgeW τ ^ (-(k : ℤ)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hrp_nn) h1t_nn) hwk_nn

/-- info: 'FormalResearch.SignUncertainty.warpAmpScal_edge_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms warpAmpScal_edge_bounds

/-- info: 'FormalResearch.SignUncertainty.tau_mul_warpAmpScal_edge_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tau_mul_warpAmpScal_edge_bounds

end FormalResearch.SignUncertainty
