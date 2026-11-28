/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpSqOuter
public import FormalResearch.SignUncertainty.FctWarpSolve

/-!
# Window `J₀ - 1` and `L`-difference symbol bounds (`fct:warp-win`)

Leaf helper module for `FctWarpWinInner.lean` and `FctWarpAsympWin.lean`:
* `win_dJ_comp_Y_sym`: generalized `Y(u) = 2^{-4/3} c^{-1/6} u²` chain rule on `[0, U_c]` for `max(y, M_A c^{-1/6})^{m - k}` (`m ≤ 4`).
* `win_Q_w_sym_of_jc`: composes a `JC 8` function on `(-1/10, 1)` with `w(u) = lam * fctInnerY c u` into `𝒮^8_0`.
* `win_J0_sub_one_and_diff`: on `[0, Sw_ell c^{-1/6}]`, `J₀(q₀(ell₂), Y(u)) - 1 ∈ 𝒮^{10}(C c^{-4/3})` and
  `J₀(q₀(ell₂), Y(u)) - J₀(q₀(ell₁), Y(u)) ∈ 𝒮^{10}(C c^{-7/6} (ell₂ - ell₁))`.

Class: proved.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped Real ContDiff BigOperators
open FormalResearch.CohnElkies FormalResearch.Special FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD FormalResearch.SignUncertainty.FctMoment
open FormalResearch.SignUncertainty.FctSymA FormalResearch.SignUncertainty.CtCfu

namespace FormalResearch.SignUncertainty

/-! ### 1. Generalized `Y(u)` composition and `w(u)` composition helpers -/

lemma win_dJ_comp_Y_sym {c B M_A : ℝ} {m : ℕ} (hc : 100 ≤ c) (hB : 0 ≤ B) (hMA : 8 ≤ M_A) (hm : m ≤ 4)
    {g : ℝ → ℝ} (hg_cd : ContDiffOn ℝ 8 g Yint)
    (hg_bd : ∀ k : ℕ, k ≤ 8 → ∀ y ∈ Yint, 0 ≤ y →
      |iteratedDeriv k g y| ≤ B * max y (M_A * c ^ (-(1 / 6 : ℝ))) ^ (m - k)) :
    FctSymClsOn (Icc 0 (fctUc c)) 8 8
      ((Nat.factorial 8 : ℝ) * 16 ^ 8 * M_A ^ 4 * 100 ^ 8 * B * c ^ (-((m : ℝ) / 6)))
      (fun u => ((g (fctInnerY c u) : ℝ) : ℂ)) := by
  have hc0 : 0 < c := by linarith
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  have hY_cd : ContDiff ℝ 8 (fctInnerY c) := by unfold fctInnerY; fun_prop
  have hcd_real : ContDiffOn ℝ 8 (fun u => g (fctInnerY c u)) (Icc 0 (fctUc c)) := by
    refine hg_cd.comp hY_cd.contDiffOn fun u hu => ?_
    have h35 := fctInnerY_mem_35 (by linarith) hu
    exact ⟨by linarith [h35.1], by linarith [h35.2]⟩
  have hgY_cd : ContDiffOn ℝ 8 (fun u => ((g (fctInnerY c u) : ℝ) : ℂ)) (Icc 0 (fctUc c)) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hcd_real
  refine ⟨hgY_cd, fun r hr u₀ hu₀ => ?_⟩
  rw [iteratedDerivWithin_ofReal_cast hDu hcd_real hr u₀ hu₀, Complex.norm_real, Real.norm_eq_abs]
  let r₀ : ℝ := (1 + u₀) / 100
  have hr₀_pos : 0 < r₀ := by dsimp only [r₀]; linarith [hu₀.1]
  let L₀ : ℝ := c ^ (-(1 / 6 : ℝ)) * (1 + u₀) ^ 2
  have h1u_pos : 0 < 1 + u₀ := by linarith [hu₀.1]
  have hL₀_pos : 0 < L₀ := by dsimp only [L₀]; positivity
  have hL₀_16 : L₀ ≤ 16 := by
    have hsq : (1 + u₀) ^ 2 ≤ 16 * c ^ ((1 : ℝ) / 6) := by
      have hu_b : 1 + u₀ ≤ 4 * c ^ ((1 : ℝ) / 12) := by
        have hc12 : 1 ≤ c ^ ((1 : ℝ) / 12) := Real.one_le_rpow (by linarith) (by norm_num)
        have hu2 : u₀ ≤ 2.96 * c ^ ((1 : ℝ) / 12) := hu₀.2
        linarith only [hc12, hu2]
      calc (1 + u₀) ^ 2 ≤ (4 * c ^ ((1 : ℝ) / 12)) ^ 2 := pow_le_pow_left₀ h1u_pos.le hu_b 2
        _ = 16 * (c ^ ((1 : ℝ) / 12)) ^ 2 := by ring
        _ = 16 * c ^ ((1 : ℝ) / 6) := by
            rw [← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le]; norm_num
    have hprod : c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6) = 1 := by
      rw [← Real.rpow_add hc0]; norm_num
    calc L₀ = c ^ (-(1 / 6 : ℝ)) * (1 + u₀) ^ 2 := rfl
      _ ≤ c ^ (-(1 / 6 : ℝ)) * (16 * c ^ ((1 : ℝ) / 6)) := by gcongr
      _ = 16 * (c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6)) := by ring
      _ = 16 := by rw [hprod, mul_one]
  have hY35 := fctInnerY_mem_35 (by linarith) hu₀
  have hY_le_L0 : fctInnerY c u₀ ≤ L₀ := by
    have h243 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    have hsq : u₀ ^ 2 ≤ (1 + u₀) ^ 2 := pow_le_pow_left₀ hu₀.1 (by linarith) 2
    unfold fctInnerY
    calc 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u₀ ^ 2
        ≤ 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * (1 + u₀) ^ 2 := by gcongr
      _ ≤ 1 * (c ^ (-(1 / 6 : ℝ)) * (1 + u₀) ^ 2) := by rw [mul_assoc]; gcongr
      _ = L₀ := one_mul L₀
  have hY_map : ∀ t ∈ Ioo (-1 : ℝ) 1,
      fctInnerY c (u₀ + r₀ * t) ∈ Yint ∧ 0 ≤ fctInnerY c (u₀ + r₀ * t) := fun t ht => by
    have hy0 : 0 ≤ fctInnerY c (u₀ + r₀ * t) := by unfold fctInnerY; positivity
    have hc12 : 1 ≤ c ^ ((1 : ℝ) / 12) := Real.one_le_rpow (by linarith) (by norm_num)
    have h1 : |u₀ + r₀ * t| ≤ 3 * c ^ ((1 : ℝ) / 12) := by
      have hu2 : u₀ ≤ 2.96 * c ^ ((1 : ℝ) / 12) := hu₀.2
      calc |u₀ + r₀ * t| ≤ u₀ + r₀ := by
            rw [abs_le]; constructor <;> nlinarith [hu₀.1, ht.1, ht.2, hr₀_pos.le]
        _ = 1.01 * u₀ + 0.01 := by dsimp only [r₀]; ring
        _ ≤ 1.01 * (2.96 * c ^ ((1 : ℝ) / 12)) + 0.01 * c ^ ((1 : ℝ) / 12) := by nlinarith [hc12]
        _ ≤ 3 * c ^ ((1 : ℝ) / 12) := by linarith
    have hu_sq : (u₀ + r₀ * t) ^ 2 ≤ 9 * c ^ ((1 : ℝ) / 6) := by
      calc (u₀ + r₀ * t) ^ 2 = |u₀ + r₀ * t| ^ 2 := (sq_abs _).symm
        _ ≤ (3 * c ^ ((1 : ℝ) / 12)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = 9 * c ^ ((1 : ℝ) / 6) := by
            rw [mul_pow, ← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le]; norm_num
    have hprod : c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6) = 1 := by
      rw [← Real.rpow_add hc0]; norm_num
    have hy36 : fctInnerY c (u₀ + r₀ * t) < 3.6 := by
      have hm43 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 0.3969 := fctB2_two_rpow_neg43_le
      unfold fctInnerY
      calc 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * (u₀ + r₀ * t) ^ 2
          ≤ 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * (9 * c ^ ((1 : ℝ) / 6)) := by gcongr
        _ = 2 ^ (-(4 / 3 : ℝ)) * 9 := by
            calc _ = 2 ^ (-(4 / 3 : ℝ)) * 9 * (c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6)) := by ring
              _ = _ := by rw [hprod, mul_one]
        _ ≤ 0.3969 * 9 := by gcongr
        _ < 3.6 := by norm_num
    exact ⟨⟨by linarith, by linarith⟩, hy0⟩
  let htilde : ℝ → ℝ := fun t => (fctInnerY c (u₀ + r₀ * t) - fctInnerY c u₀) / L₀
  let gtilde : ℝ → ℝ := fun s => g (fctInnerY c u₀ + L₀ * s)
  have hht_cd : ContDiff ℝ ⊤ htilde := by dsimp only [htilde, fctInnerY]; fun_prop
  have hht_range : ∀ t ∈ Ioo (-1 : ℝ) 1, |htilde t| ≤ 1 := fun t ht => by
    have h243 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    have hdiff : htilde t = 2 ^ (-(4 / 3 : ℝ)) * (2 * u₀ * r₀ * t + r₀ ^ 2 * t ^ 2) / (1 + u₀) ^ 2 := by
      dsimp only [htilde, fctInnerY, L₀]
      have hne : c ^ (-(1 / 6 : ℝ)) ≠ 0 := by positivity
      field_simp [hne, hL₀_pos.ne']; ring
    rw [hdiff, abs_div, abs_of_pos (sq_pos_of_pos h1u_pos),
      abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ (-(4 / 3 : ℝ)))]
    have hnum : |2 * u₀ * r₀ * t + r₀ ^ 2 * t ^ 2| ≤ (1 + u₀) ^ 2 := by
      have ha1 : |2 * u₀ * r₀ * t| ≤ 2 * u₀ * r₀ := by
        rw [abs_mul, abs_of_nonneg (mul_nonneg (mul_nonneg zero_le_two hu₀.1) hr₀_pos.le)]
        exact mul_le_of_le_one_right (mul_nonneg (mul_nonneg zero_le_two hu₀.1) hr₀_pos.le) (abs_lt.mpr ht).le
      have ha2 : |r₀ ^ 2 * t ^ 2| ≤ r₀ ^ 2 := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_sq]
        have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
        exact mul_le_of_le_one_right (sq_nonneg r₀) ht2
      exact ((abs_add_le _ _).trans (add_le_add ha1 ha2)).trans (by dsimp only [r₀]; nlinarith [hu₀.1])
    rw [div_le_one (sq_pos_of_pos h1u_pos)]
    calc (2 : ℝ) ^ (-(4 / 3 : ℝ)) * |2 * u₀ * r₀ * t + r₀ ^ 2 * t ^ 2|
        ≤ 1 * (1 + u₀) ^ 2 := mul_le_mul h243 hnum (abs_nonneg _) zero_le_one
      _ = (1 + u₀) ^ 2 := one_mul _
  have hht_jb : JB 8 (Ioo (-1 : ℝ) 1) htilde 1 := by
    have ha_coeff : ∀ t : ℝ, htilde t = (2 ^ (-(4 / 3 : ℝ)) / (1 + u₀) ^ 2) *
        (2 * u₀ * r₀ * t + r₀ ^ 2 * t ^ 2) := fun t => by
      dsimp only [htilde, fctInnerY, L₀]
      have hne : c ^ (-(1 / 6 : ℝ)) ≠ 0 := by positivity
      have hLne : c ^ (-(1 / 6 : ℝ)) * (1 + u₀) ^ 2 ≠ 0 := by positivity
      field_simp [hne, hLne]; ring
    have hd1fn : iteratedDeriv 1 htilde = fun s =>
        (2 ^ (-(4 / 3 : ℝ)) / (1 + u₀) ^ 2) * (2 * u₀ * r₀ + 2 * r₀ ^ 2 * s) := funext fun s => by
      have hfun : htilde = fun w => (2 ^ (-(4 / 3 : ℝ)) / (1 + u₀) ^ 2) * (2 * u₀ * r₀ * w + r₀ ^ 2 * w ^ 2) :=
        funext ha_coeff
      rw [hfun, iteratedDeriv_one, deriv_const_mul _ (by fun_prop)]
      have hd : HasDerivAt (fun w => 2 * u₀ * r₀ * w + r₀ ^ 2 * w ^ 2) (2 * u₀ * r₀ + 2 * r₀ ^ 2 * s) s :=
        (((hasDerivAt_id s).const_mul (2 * u₀ * r₀)).add ((hasDerivAt_pow 2 s).const_mul (r₀ ^ 2))).congr_deriv (by ring)
      rw [hd.deriv]
    have hd2fn : iteratedDeriv 2 htilde = fun _ => (2 ^ (-(4 / 3 : ℝ)) / (1 + u₀) ^ 2) * (2 * r₀ ^ 2) := funext fun z => by
      rw [iteratedDeriv_succ, hd1fn, deriv_const_mul _ (by fun_prop)]
      have hd : HasDerivAt (fun s => 2 * u₀ * r₀ + 2 * r₀ ^ 2 * s) (2 * r₀ ^ 2) z :=
        ((hasDerivAt_const z (2 * u₀ * r₀)).add ((hasDerivAt_id z).const_mul (2 * r₀ ^ 2))).congr_deriv (by ring)
      rw [hd.deriv]
    have h0_ge3 : ∀ m0 : ℕ, iteratedDeriv (m0 + 3) htilde = 0 := by
      intro m0
      induction m0 with
      | zero => rw [iteratedDeriv_succ, hd2fn]; ext; simp
      | succ m0 ih => rw [show m0 + 1 + 3 = (m0 + 3) + 1 by omega, iteratedDeriv_succ, ih]; simp
    intro k hk t ht
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      iteratedDerivWithin_of_isOpen isOpen_Ioo ht, Real.norm_eq_abs]
    have h243 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    rcases Nat.lt_trichotomy k 1 with hk0 | hk1 | _
    · have : k = 0 := by omega
      subst this; simpa only [iteratedDeriv_zero] using hht_range t ht
    · subst hk1; rw [hd1fn, abs_mul, abs_div, abs_of_nonneg (by positivity), abs_of_pos (sq_pos_of_pos h1u_pos)]
      have hnum : |2 * u₀ * r₀ + 2 * r₀ ^ 2 * t| ≤ (1 + u₀) ^ 2 := by
        have ha1 : |2 * u₀ * r₀| ≤ 2 * u₀ * r₀ := (abs_of_nonneg (mul_nonneg (mul_nonneg zero_le_two hu₀.1) hr₀_pos.le)).le
        have ha2 : |2 * r₀ ^ 2 * t| ≤ 2 * r₀ ^ 2 := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
          exact mul_le_of_le_one_right (by positivity) (abs_lt.mpr ht).le
        exact ((abs_add_le _ _).trans (add_le_add ha1 ha2)).trans (by dsimp only [r₀]; nlinarith [hu₀.1])
      rw [div_mul_eq_mul_div, div_le_one (sq_pos_of_pos h1u_pos)]
      calc (2 : ℝ) ^ (-(4 / 3 : ℝ)) * |2 * u₀ * r₀ + 2 * r₀ ^ 2 * t| ≤ 1 * (1 + u₀) ^ 2 := by gcongr
        _ = (1 + u₀) ^ 2 := one_mul _
    · rcases Nat.lt_trichotomy k 2 with _ | hk2 | _
      · omega
      · subst hk2; rw [hd2fn, abs_mul, abs_div, abs_of_nonneg (by positivity), abs_of_pos (sq_pos_of_pos h1u_pos)]
        have hnum : |2 * r₀ ^ 2| ≤ (1 + u₀) ^ 2 := by
          rw [abs_of_nonneg (by positivity)]; dsimp only [r₀]; nlinarith [hu₀.1]
        rw [div_mul_eq_mul_div, div_le_one (sq_pos_of_pos h1u_pos)]
        calc (2 : ℝ) ^ (-(4 / 3 : ℝ)) * |2 * r₀ ^ 2| ≤ 1 * (1 + u₀) ^ 2 := by gcongr
          _ = (1 + u₀) ^ 2 := one_mul _
      · obtain ⟨m0, rfl⟩ : ∃ m0, k = m0 + 3 := ⟨k - 3, by omega⟩
        rw [h0_ge3 m0, Pi.zero_apply, abs_zero]; exact zero_le_one
  let a_lo : ℝ := max (-1.5 : ℝ) (-fctInnerY c u₀ / L₀)
  let b_hi : ℝ := min (1.5 : ℝ) ((3.6 - fctInnerY c u₀) / L₀)
  have hT_u : UniqueDiffOn ℝ (Ico a_lo b_hi) := uniqueDiffOn_Ico a_lo b_hi
  have hT_map : ∀ s ∈ Ico a_lo b_hi, fctInnerY c u₀ + L₀ * s ∈ Yint ∧ 0 ≤ fctInnerY c u₀ + L₀ * s := fun s hs => by
    have hs_lo : -fctInnerY c u₀ / L₀ ≤ s := (le_max_right _ _).trans hs.1
    have hs_hi : s < (3.6 - fctInnerY c u₀) / L₀ := lt_of_lt_of_le hs.2 (min_le_right _ _)
    have hy0 : 0 ≤ fctInnerY c u₀ + L₀ * s := by have := (div_le_iff₀ hL₀_pos).mp hs_lo; linarith
    have hy36 : fctInnerY c u₀ + L₀ * s < 3.6 := by have := (lt_div_iff₀ hL₀_pos).mp hs_hi; linarith
    exact ⟨⟨by linarith, by linarith⟩, hy0⟩
  have hht_maps : MapsTo htilde (Ioo (-1 : ℝ) 1) (Ico a_lo b_hi) := fun t ht => by
    obtain ⟨hyY, _⟩ := hY_map t ht
    have hbd := abs_le.mp (hht_range t ht)
    refine ⟨max_le (by linarith [hbd.1]) ?_, lt_min (by linarith [hbd.2]) ?_⟩
    · rw [div_le_iff₀ hL₀_pos]; dsimp only [htilde]; rw [div_mul_cancel₀ _ hL₀_pos.ne']; linarith
    · rw [lt_div_iff₀ hL₀_pos]; dsimp only [htilde]; rw [div_mul_cancel₀ _ hL₀_pos.ne']; linarith [hyY.2]
  have hg_cd_m : ∀ (k0 : ℕ), k0 ≤ 8 → ContDiffOn ℝ ((8 - k0 : ℕ) : WithTop ℕ∞) (iteratedDeriv k0 g) Yint := by
    intro k0
    induction k0 with
    | zero => intro _; simpa using hg_cd
    | succ k0 ih =>
      intro hk0
      have hprev := ih (Nat.le_of_succ_le hk0)
      have hsplit : ((8 - k0 : ℕ) : WithTop ℕ∞) = (((8 - (k0 + 1) : ℕ) : ℕ∞) + 1 : ℕ∞) := by
        have hn : 8 - k0 = (8 - (k0 + 1)) + 1 := by omega
        rw [hn]; push_cast; rfl
      rw [hsplit] at hprev
      have hd := hprev.derivWithin (m := ((8 - (k0 + 1) : ℕ) : ℕ∞)) isOpen_Ioo.uniqueDiffOn
        (by rw [← WithTop.coe_one, ← WithTop.coe_add])
      have hcongr : EqOn (derivWithin (iteratedDeriv k0 g) Yint) (iteratedDeriv (k0 + 1) g) Yint :=
        fun z hz => by rw [iteratedDeriv_succ, derivWithin_of_isOpen isOpen_Ioo hz]
      exact (hd.congr fun z hz => (hcongr hz).symm).of_le (by norm_cast)
  have hgt_jc : JC 8 (Ico a_lo b_hi) gtilde (B * (16 ^ 8 * M_A ^ 4) * L₀ ^ m) := by
    have hgt_cd : ContDiffOn ℝ 8 gtilde (Ico a_lo b_hi) :=
      hg_cd.comp (by fun_prop) fun s hs => (hT_map s hs).1
    refine ⟨hgt_cd, fun k hk s hs => ?_⟩
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, Real.norm_eq_abs]
    have haff_eq : gtilde = fun w => g (L₀ * w + fctInnerY c u₀) := by ext w; dsimp only [gtilde]; rw [add_comm]
    have hd_lin : ∀ (k0 : ℕ), k0 ≤ 8 → ∀ z ∈ Ico a_lo b_hi,
        iteratedDerivWithin k0 (fun w => g (L₀ * w + fctInnerY c u₀)) (Ico a_lo b_hi) z =
          L₀ ^ k0 * iteratedDeriv k0 g (L₀ * z + fctInnerY c u₀) := by
      intro k0
      induction k0 with
      | zero => intro _ z _; simp
      | succ k0 ih =>
        intro hk0 z hz
        have hcongr : EqOn (iteratedDerivWithin k0 (fun w => g (L₀ * w + fctInnerY c u₀)) (Ico a_lo b_hi))
            (fun w => L₀ ^ k0 * iteratedDeriv k0 g (L₀ * w + fctInnerY c u₀)) (Ico a_lo b_hi) :=
          fun w hw => ih (Nat.le_of_succ_le hk0) w hw
        rw [iteratedDerivWithin_succ, derivWithin_congr hcongr (hcongr hz)]
        have hz_in : L₀ * z + fctInnerY c u₀ ∈ Yint := by simpa [add_comm] using (hT_map z hz).1
        have hdg : ContDiffAt ℝ 1 (iteratedDeriv k0 g) (L₀ * z + fctInnerY c u₀) :=
          ((hg_cd_m k0 (Nat.le_of_succ_le hk0)).contDiffAt (isOpen_Ioo.mem_nhds hz_in)).of_le
            (by exact_mod_cast (by omega : 1 ≤ 8 - k0))
        have hda : HasDerivAt (fun w => L₀ ^ k0 * iteratedDeriv k0 g (L₀ * w + fctInnerY c u₀))
            (L₀ ^ k0 * (iteratedDeriv (k0 + 1) g (L₀ * z + fctInnerY c u₀) * L₀)) z := by
          have h1 : HasDerivAt (iteratedDeriv k0 g) (iteratedDeriv (k0 + 1) g (L₀ * z + fctInnerY c u₀))
              (L₀ * z + fctInnerY c u₀) := by
            rw [iteratedDeriv_succ]; exact (hdg.differentiableAt (by norm_num)).hasDerivAt
          have h2 : HasDerivAt (fun w : ℝ => L₀ * w + fctInnerY c u₀) L₀ z := by
            simpa using ((hasDerivAt_id z).const_mul L₀).add_const (fctInnerY c u₀)
          exact (HasDerivAt.comp z h1 h2).const_mul (L₀ ^ k0)
        rw [hda.hasDerivWithinAt.derivWithin (hT_u z hz)]; ring
    rw [haff_eq, hd_lin k hk s hs, abs_mul, abs_pow, abs_of_pos hL₀_pos]
    obtain ⟨hy_int, _⟩ := hT_map s hs
    have hgb := hg_bd k hk (L₀ * s + fctInnerY c u₀) (by simpa [add_comm] using hy_int) (by linarith)
    have hs_15 : s ≤ 1.5 := (lt_of_lt_of_le hs.2 (min_le_left _ _)).le
    have hy_le : L₀ * s + fctInnerY c u₀ ≤ M_A * L₀ := by
      have hLs : L₀ * s ≤ L₀ * 1.5 := mul_le_mul_of_nonneg_left hs_15 hL₀_pos.le
      nlinarith [hY_le_L0, hL₀_pos, hMA]
    have hMAc : M_A * c ^ (-(1 / 6 : ℝ)) ≤ M_A * L₀ := by
      have h1u : 1 ≤ (1 + u₀) ^ 2 := by nlinarith [hu₀.1]
      dsimp only [L₀]; nlinarith [show (0 : ℝ) < c ^ (-(1 / 6 : ℝ)) by positivity, hMA]
    have hmax_le : max (L₀ * s + fctInnerY c u₀) (M_A * c ^ (-(1 / 6 : ℝ))) ≤ M_A * L₀ :=
      max_le hy_le hMAc
    have hMA_pow : M_A ^ (m - k) ≤ M_A ^ 4 := pow_le_pow_right₀ (by linarith) (by omega)
    have hMA4_ge1 : (1 : ℝ) ≤ M_A ^ 4 := one_le_pow₀ (by linarith)
    by_cases hkm : k ≤ m
    · have hpow : max (L₀ * s + fctInnerY c u₀) (M_A * c ^ (-(1 / 6 : ℝ))) ^ (m - k) ≤ (M_A * L₀) ^ (m - k) :=
        pow_le_pow_left₀ (le_max_of_le_left (by linarith)) hmax_le (m - k)
      calc L₀ ^ k * |iteratedDeriv k g (L₀ * s + fctInnerY c u₀)|
          ≤ L₀ ^ k * (B * max (L₀ * s + fctInnerY c u₀) (M_A * c ^ (-(1 / 6 : ℝ))) ^ (m - k)) := by gcongr
        _ ≤ L₀ ^ k * (B * (M_A * L₀) ^ (m - k)) := by gcongr
        _ = B * M_A ^ (m - k) * (L₀ ^ k * L₀ ^ (m - k)) := by rw [mul_pow]; ring
        _ = B * M_A ^ (m - k) * L₀ ^ m := by rw [← pow_add, Nat.add_sub_of_le hkm]
        _ ≤ B * M_A ^ 4 * L₀ ^ m := by gcongr
        _ ≤ B * (16 ^ 8 * M_A ^ 4) * L₀ ^ m := by
            have : (1 : ℝ) ≤ 16 ^ 8 := by norm_num
            nlinarith [mul_nonneg hB (pow_nonneg hL₀_pos.le m), hMA4_ge1]
    · have hkm' : m ≤ k := by omega
      have hsub0 : m - k = 0 := Nat.sub_eq_zero_of_le hkm'
      have hpow_le : L₀ ^ k ≤ 16 ^ 8 * L₀ ^ m := by
        have hsplit : L₀ ^ k = L₀ ^ m * L₀ ^ (k - m) := by rw [← pow_add, Nat.add_sub_of_le hkm']
        rw [hsplit, mul_comm (16 ^ 8)]
        gcongr
        exact (pow_le_pow_left₀ hL₀_pos.le hL₀_16 (k - m)).trans
          (pow_le_pow_right₀ (by norm_num) (by omega : k - m ≤ 8))
      calc L₀ ^ k * |iteratedDeriv k g (L₀ * s + fctInnerY c u₀)|
          ≤ L₀ ^ k * (B * 1) := by simpa [hsub0] using mul_le_mul_of_nonneg_left hgb (pow_nonneg hL₀_pos.le k)
        _ ≤ (16 ^ 8 * L₀ ^ m) * B := by rw [mul_one]; exact mul_le_mul_of_nonneg_right hpow_le hB
        _ ≤ B * (16 ^ 8 * M_A ^ 4) * L₀ ^ m := by
            have : (1 : ℝ) ≤ 16 ^ 8 := by norm_num
            nlinarith [mul_nonneg hB (pow_nonneg hL₀_pos.le m), hMA4_ge1]
  have hjb := JB.comp (k := 8) isOpen_Ioo.uniqueDiffOn hT_u hgt_jc.1
    ((hht_cd.of_le le_top).contDiffOn) hht_maps (by positivity)
    (fun s hs i hi => hgt_jc.2 i hi (htilde s) (hht_maps hs))
    (fun i _ hi8 t ht => hht_jb i hi8 t ht)
  have h0_mem : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hcomp_val : gtilde ∘ htilde = fun t => g (fctInnerY c (u₀ + r₀ * t)) := by
    ext t; dsimp only [Function.comp_apply, gtilde, htilde]
    rw [mul_div_cancel₀ _ hL₀_pos.ne', add_sub_cancel]
  have hle := hjb r hr 0 h0_mem
  rw [hcomp_val, norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, Real.norm_eq_abs, max_self,
    iteratedDerivWithin_of_isOpen isOpen_Ioo h0_mem] at hle
  have haff_rel : iteratedDeriv r (fun t => g (fctInnerY c (u₀ + r₀ * t))) 0 =
      r₀ ^ r * iteratedDerivWithin r (fun u => g (fctInnerY c u)) (Icc 0 (fctUc c)) u₀ := by
    let U_big : Set ℝ := (fctInnerY c) ⁻¹' Yint
    have hU_open : IsOpen U_big := isOpen_Ioo.preimage hY_cd.continuous
    have hU_sub : Icc 0 (fctUc c) ⊆ U_big := fun u hu => by
      have h35 := fctInnerY_mem_35 (by linarith) hu; exact ⟨by linarith [h35.1], by linarith [h35.2]⟩
    have hcd_big : ContDiffOn ℝ 8 (fun u => g (fctInnerY c u)) U_big :=
      hg_cd.comp hY_cd.contDiffOn fun u hu => hu
    have h0_in_big : u₀ ∈ U_big := hU_sub hu₀
    let Pre_U : Set ℝ := (fun w : ℝ => u₀ + r₀ * w) ⁻¹' U_big
    have hPre_open : IsOpen Pre_U := hU_open.preimage (by fun_prop)
    have h0_in_pre : (0 : ℝ) ∈ Pre_U := by simpa [Pre_U] using h0_in_big
    have hcomp_big := iteratedDerivWithin_comp_affine hU_open.uniqueDiffOn hPre_open.uniqueDiffOn
      hcd_big hr (v := 0) (by simpa using h0_in_big)
    change iteratedDerivWithin r (fun t => g (fctInnerY c (u₀ + r₀ * t))) Pre_U 0 = _ at hcomp_big
    rw [iteratedDerivWithin_of_isOpen hPre_open h0_in_pre, mul_zero, add_zero, smul_eq_mul,
      iteratedDerivWithin_of_isOpen hU_open h0_in_big] at hcomp_big
    rw [hcomp_big, iteratedDerivWithin_eq_iteratedDeriv hDu
      ((hcd_big.contDiffAt (hU_open.mem_nhds h0_in_big)).of_le (by exact_mod_cast hr)) hu₀]
  rw [haff_rel, abs_mul, abs_pow, abs_of_pos hr₀_pos] at hle
  have hr₀_inv_le : (r₀ ^ r)⁻¹ ≤ 100 ^ 8 * (1 + u₀) ^ (-(r : ℝ)) := by
    have hpow_le : (100 : ℝ) ^ r ≤ 100 ^ 8 := pow_le_pow_right₀ (by norm_num) hr
    have hr0_inv : r₀⁻¹ = 100 * (1 + u₀)⁻¹ := by dsimp only [r₀]; rw [inv_div]; ring
    rw [← inv_pow, hr0_inv, mul_pow, inv_pow, Real.rpow_neg h1u_pos.le r, Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_right hpow_le (inv_nonneg.mpr (pow_nonneg h1u_pos.le r))
  have hL_rpow : L₀ ^ m = c ^ (-((m : ℝ) / 6)) * (1 + u₀) ^ (2 * m : ℝ) := by
    dsimp only [L₀]
    rw [mul_pow, ← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le,
      ← Real.rpow_natCast ((1 + u₀) ^ 2), ← Real.rpow_natCast (1 + u₀),
      ← Real.rpow_mul h1u_pos.le]
    congr 1; congr 1; norm_cast; ring
  calc |iteratedDerivWithin r (fun u => g (fctInnerY c u)) (Icc 0 (fctUc c)) u₀|
      ≤ (r₀ ^ r)⁻¹ * ((Nat.factorial 8 : ℝ) * (B * (16 ^ 8 * M_A ^ 4) * L₀ ^ m)) :=
        (le_inv_mul_iff₀ (pow_pos hr₀_pos r)).mpr (by simpa [mul_assoc] using hle)
    _ ≤ (100 ^ 8 * (1 + u₀) ^ (-(r : ℝ))) *
          ((Nat.factorial 8 : ℝ) * (B * (16 ^ 8 * M_A ^ 4) * (c ^ (-((m : ℝ) / 6)) * (1 + u₀) ^ (2 * m : ℝ)))) := by
        rw [← hL_rpow]; gcongr
    _ = (Nat.factorial 8 : ℝ) * 16 ^ 8 * M_A ^ 4 * 100 ^ 8 * B * c ^ (-((m : ℝ) / 6)) *
          ((1 + u₀) ^ (2 * m : ℝ) * (1 + u₀) ^ (-(r : ℝ))) := by ring
    _ ≤ (Nat.factorial 8 : ℝ) * 16 ^ 8 * M_A ^ 4 * 100 ^ 8 * B * c ^ (-((m : ℝ) / 6)) *
          (1 + u₀) ^ ((8 : ℝ) - (r : ℝ)) := by
        gcongr
        rw [← Real.rpow_add h1u_pos]
        refine Real.rpow_le_rpow_of_exponent_le (by linarith [hu₀.1]) ?_
        have h2m : (2 * (m : ℝ)) ≤ 8 := by exact_mod_cast (by omega : 2 * m ≤ 8)
        linarith only [h2m]

lemma win_Q_w_sym_of_jc {r_star B_Q c lam : ℝ} (hr2_pos : 0 < r_star ^ 2)
    (hBQ0 : 0 ≤ B_Q) (hc100 : 100 ≤ c) (hc_neg_half : c ^ (-(1 / 2 : ℝ)) ≤ r_star ^ 2 / 161)
    (hlam_pos : 0 < lam) (hlam_le : lam ≤ c ^ (-(1 / 2 : ℝ)) / r_star ^ 2)
    {Q_p : ℝ → ℝ} (hQ_p_jc : JC 8 (Ioo (-(1 / 10 : ℝ)) 1) Q_p B_Q) :
    FctSymClsOn (Icc 0 (fctUc c)) 8 0 (100 ^ 8 * ((Nat.factorial 8 : ℝ) * B_Q))
      (fun u => ((Q_p (lam * fctInnerY c u) : ℝ) : ℂ)) := by
  have hc0 : 0 < c := by linarith only [hc100]
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  let Y_Q : Set ℝ := Ioo (-(1 / 10 : ℝ)) 1
  have hUd_YQ : UniqueDiffOn ℝ Y_Q := isOpen_Ioo.uniqueDiffOn
  let k_w : ℝ := lam * 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ))
  let w_fn : ℝ → ℝ := fun u => lam * fctInnerY c u
  have hw_fn_eq : ∀ u : ℝ, w_fn u = k_w * u ^ 2 := fun u => by
    dsimp only [w_fn, k_w, fctInnerY]; ring
  have hkw_nn : 0 ≤ k_w := by dsimp only [k_w]; positivity
  have hr_ne : r_star ≠ 0 := fun h0 => by simp [h0] at hr2_pos
  have hw_maps_YQ : ∀ u₀ ∈ Icc 0 (fctUc c), ∀ t ∈ Ioo (-1 : ℝ) 1,
      w_fn (u₀ + (1 + u₀) / 100 * t) ∈ Y_Q := fun u₀ hu₀ t ht => by
    have hc12_1 : 1 ≤ c ^ ((1 : ℝ) / 12) := Real.one_le_rpow (by linarith only [hc100]) (by norm_num)
    have hr0_nn : 0 ≤ (1 + u₀) / 100 := by linarith only [hu₀.1]
    have harg_abs : |u₀ + (1 + u₀) / 100 * t| ≤ 4 * c ^ ((1 : ℝ) / 12) := by
      have h1 : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith only [ht.1, ht.2]
      have h2 : |u₀ + (1 + u₀) / 100 * t| ≤ u₀ + (1 + u₀) / 100 := by
        calc |u₀ + (1 + u₀) / 100 * t| ≤ |u₀| + |(1 + u₀) / 100 * t| := abs_add_le _ _
          _ = u₀ + (1 + u₀) / 100 * |t| := by rw [abs_of_nonneg hu₀.1, abs_mul, abs_of_nonneg hr0_nn]
          _ ≤ u₀ + (1 + u₀) / 100 * 1 := by gcongr
          _ = u₀ + (1 + u₀) / 100 := by ring
      have hu2 : u₀ ≤ 2.96 * c ^ ((1 : ℝ) / 12) := hu₀.2
      linarith only [h2, hu2, hc12_1]
    have hc16 : (c ^ ((1 : ℝ) / 12)) ^ 2 = c ^ ((1 : ℝ) / 6) := by
      rw [← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le]; norm_num
    have hsq : (u₀ + (1 + u₀) / 100 * t) ^ 2 ≤ 16 * c ^ ((1 : ℝ) / 6) := by
      rw [← sq_abs]
      calc |u₀ + (1 + u₀) / 100 * t| ^ 2 ≤ (4 * c ^ ((1 : ℝ) / 12)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) harg_abs 2
        _ = 16 * c ^ ((1 : ℝ) / 6) := by rw [mul_pow, hc16]; ring
    have hlam_w : w_fn (u₀ + (1 + u₀) / 100 * t) ≤ 1 / 10 := by
      have h243 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
      have hc160 : c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6) = 1 := by
        rw [← Real.rpow_add hc0]; norm_num
      rw [hw_fn_eq]; dsimp only [k_w]
      calc lam * 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * (u₀ + (1 + u₀) / 100 * t) ^ 2
          ≤ (c ^ (-(1 / 2 : ℝ)) / r_star ^ 2) * 1 * c ^ (-(1 / 6 : ℝ)) * (16 * c ^ ((1 : ℝ) / 6)) := by gcongr
        _ = 16 * ((c ^ (-(1 / 2 : ℝ)) / r_star ^ 2) * (c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6))) := by ring
        _ = 16 * (c ^ (-(1 / 2 : ℝ)) / r_star ^ 2) := by rw [hc160, mul_one]
        _ ≤ 16 * ((r_star ^ 2 / 161) / r_star ^ 2) := by gcongr
        _ = 16 / 161 := by field_simp [hr_ne]
        _ ≤ 1 / 10 := by norm_num
    have hw_nn : 0 ≤ w_fn (u₀ + (1 + u₀) / 100 * t) := by rw [hw_fn_eq]; positivity
    exact ⟨by linarith only [hw_nn], by linarith only [hlam_w]⟩
  have hU_big_open : IsOpen (w_fn ⁻¹' Y_Q) := isOpen_Ioo.preimage (by
    have heq : w_fn = fun u => k_w * u ^ 2 := funext hw_fn_eq; rw [heq]; fun_prop)
  have hsub_big : Icc 0 (fctUc c) ⊆ w_fn ⁻¹' Y_Q := fun u hu => by
    simpa using hw_maps_YQ u hu 0 ⟨by norm_num, by norm_num⟩
  have hw_cd : ContDiffOn ℝ 8 w_fn (Icc 0 (fctUc c)) := by
    have heq : w_fn = fun u => k_w * u ^ 2 := funext hw_fn_eq; rw [heq]; fun_prop
  have hcd_real : ContDiffOn ℝ 8 (fun u => Q_p (w_fn u)) (Icc 0 (fctUc c)) :=
    hQ_p_jc.1.comp hw_cd hsub_big
  refine FctSymClsOn.ofReal_cast hDu hcd_real fun r hr u₀ hu₀ => ?_
  let r₀ : ℝ := (1 + u₀) / 100
  have hr₀_pos : 0 < r₀ := by dsimp only [r₀]; linarith only [hu₀.1]
  let w_aff : ℝ → ℝ := fun t => w_fn (u₀ + r₀ * t)
  have hw_aff_cd : ContDiffOn ℝ 8 w_aff (Ioo (-1 : ℝ) 1) := by
    have heq : w_aff = fun t => k_w * (u₀ + r₀ * t) ^ 2 := by ext t; exact hw_fn_eq _
    rw [heq]; fun_prop
  have hw_aff_jb : ∀ i, 1 ≤ i → i ≤ 8 → ∀ t ∈ Ioo (-1 : ℝ) 1,
      ‖iteratedFDerivWithin ℝ i w_aff (Ioo (-1 : ℝ) 1) t‖ ≤ 1 := fun i hi1 hi8 t ht => by
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      iteratedDerivWithin_of_isOpen isOpen_Ioo ht, Real.norm_eq_abs]
    have hkw_eq : w_aff = fun s => k_w * (u₀ + r₀ * s) ^ 2 := by ext s; exact hw_fn_eq _
    have hkw_c16 : k_w * (1 + u₀) ^ 2 ≤ 16 / 161 := by
      have hc12_1 : 1 ≤ c ^ ((1 : ℝ) / 12) := Real.one_le_rpow (by linarith only [hc100]) (by norm_num)
      have hu_le : u₀ ≤ 2.96 * c ^ ((1 : ℝ) / 12) := hu₀.2
      have h1u : 1 + u₀ ≤ 4 * c ^ ((1 : ℝ) / 12) := by linarith only [hu_le, hc12_1]
      have hc16 : (c ^ ((1 : ℝ) / 12)) ^ 2 = c ^ ((1 : ℝ) / 6) := by
        rw [← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le]; norm_num
      have h1u2 : (1 + u₀) ^ 2 ≤ 16 * c ^ ((1 : ℝ) / 6) := by
        calc (1 + u₀) ^ 2 ≤ (4 * c ^ ((1 : ℝ) / 12)) ^ 2 := pow_le_pow_left₀ (by linarith only [hu₀.1]) h1u 2
          _ = 16 * c ^ ((1 : ℝ) / 6) := by rw [mul_pow, hc16]; ring
      have h243 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
      have hc160 : c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6) = 1 := by rw [← Real.rpow_add hc0]; norm_num
      calc k_w * (1 + u₀) ^ 2
          ≤ (c ^ (-(1 / 2 : ℝ)) / r_star ^ 2 * 1 * c ^ (-(1 / 6 : ℝ))) * (16 * c ^ ((1 : ℝ) / 6)) := by
            dsimp only [k_w]; gcongr
        _ = 16 * ((c ^ (-(1 / 2 : ℝ)) / r_star ^ 2) * (c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 6))) := by ring
        _ = 16 * (c ^ (-(1 / 2 : ℝ)) / r_star ^ 2) := by rw [hc160, mul_one]
        _ ≤ 16 * ((r_star ^ 2 / 161) / r_star ^ 2) := by gcongr
        _ = 16 / 161 := by field_simp [hr_ne]
    have hd1 : deriv (fun s => k_w * (u₀ + r₀ * s) ^ 2) = fun s => 2 * k_w * r₀ * (u₀ + r₀ * s) := funext fun s => by
      have harg : HasDerivAt (fun x => u₀ + r₀ * x) r₀ s :=
        by simpa using ((hasDerivAt_id s).const_mul r₀).const_add u₀
      exact (((harg.pow 2).const_mul k_w).congr_deriv (by ring)).deriv
    rcases eq_or_lt_of_le hi1 with rfl | hi2
    · rw [iteratedDeriv_one, hkw_eq, hd1]
      have harg : |u₀ + r₀ * t| ≤ 1.01 * (1 + u₀) := by
        have ht1 : |t| ≤ 1 := (abs_lt.mpr ht).le
        calc |u₀ + r₀ * t| ≤ |u₀| + |r₀ * t| := abs_add_le _ _
          _ = u₀ + r₀ * |t| := by rw [abs_of_nonneg hu₀.1, abs_mul, abs_of_pos hr₀_pos]
          _ ≤ u₀ + r₀ * 1 := by gcongr
          _ ≤ 1.01 * (1 + u₀) := by dsimp only [r₀]; linarith only [hu₀.1]
      have hmul : |2 * k_w * r₀ * (u₀ + r₀ * t)| ≤ (2.02 / 100) * (k_w * (1 + u₀) ^ 2) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_nonneg hkw_nn, abs_of_pos hr₀_pos]
        calc 2 * k_w * r₀ * |u₀ + r₀ * t|
            ≤ 2 * k_w * ((1 + u₀) / 100) * (1.01 * (1 + u₀)) := by gcongr
          _ = (2.02 / 100) * (k_w * (1 + u₀) ^ 2) := by ring
      linarith only [hmul, hkw_c16]
    · rcases eq_or_lt_of_le (by omega : 2 ≤ i) with rfl | _
      · rw [iteratedDeriv_succ, iteratedDeriv_one, hkw_eq, hd1]
        have hd2 : deriv (fun s => 2 * k_w * r₀ * (u₀ + r₀ * s)) t = 2 * k_w * r₀ ^ 2 := by
          have harg : HasDerivAt (fun x => u₀ + r₀ * x) r₀ t :=
            by simpa using ((hasDerivAt_id t).const_mul r₀).const_add u₀
          exact ((harg.const_mul (2 * k_w * r₀)).congr_deriv (by ring)).deriv
        rw [hd2, abs_of_nonneg (by positivity)]
        have halg : 2 * k_w * r₀ ^ 2 = (2 / 10000) * (k_w * (1 + u₀) ^ 2) := by dsimp only [r₀]; ring
        linarith only [halg, hkw_c16]
      · obtain ⟨m, rfl⟩ : ∃ m, i = m + 3 := ⟨i - 3, by omega⟩
        have h2 : iteratedDeriv 2 (fun s => k_w * (u₀ + r₀ * s) ^ 2) = fun _ => 2 * k_w * r₀ ^ 2 := funext fun y => by
          rw [iteratedDeriv_succ, iteratedDeriv_one, hd1]
          have harg : HasDerivAt (fun x => u₀ + r₀ * x) r₀ y :=
            by simpa using ((hasDerivAt_id y).const_mul r₀).const_add u₀
          exact ((harg.const_mul (2 * k_w * r₀)).congr_deriv (by ring)).deriv
        have h3 : ∀ n : ℕ, ∀ x : ℝ, iteratedDeriv (n + 3) (fun s => k_w * (u₀ + r₀ * s) ^ 2) x = 0 := by
          intro n
          induction n with
          | zero => intro x; rw [zero_add, iteratedDeriv_succ, h2]; simp
          | succ n ih =>
            intro x
            rw [show n + 1 + 3 = (n + 3) + 1 by omega, iteratedDeriv_succ]
            have hf : iteratedDeriv (n + 3) (fun s => k_w * (u₀ + r₀ * s) ^ 2) = fun _ => 0 := funext ih
            rw [hf]; simp
        rw [hkw_eq, h3 m t, abs_zero]; exact zero_le_one
  have hjb := JB.comp (k := 8) isOpen_Ioo.uniqueDiffOn hUd_YQ hQ_p_jc.1 hw_aff_cd
    (fun t ht => hw_maps_YQ u₀ hu₀ t ht) hBQ0
    (fun s hs i hi => hQ_p_jc.2 i hi (w_aff s) (hw_maps_YQ u₀ hu₀ s hs)) hw_aff_jb
  have h0_mem : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hle := hjb r hr 0 h0_mem
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_of_isOpen isOpen_Ioo h0_mem, Real.norm_eq_abs, max_self, one_pow, mul_one] at hle
  have haff_rel : iteratedDeriv r (Q_p ∘ w_aff) 0 =
      r₀ ^ r * iteratedDerivWithin r (fun u => Q_p (w_fn u)) (Icc 0 (fctUc c)) u₀ := by
    have hcd_big : ContDiffOn ℝ 8 (fun u => Q_p (w_fn u)) (w_fn ⁻¹' Y_Q) :=
      hQ_p_jc.1.comp (by
        have heq : w_fn = fun u => k_w * u ^ 2 := funext hw_fn_eq; rw [heq]; fun_prop)
        fun _ hu => hu
    let Pre_U : Set ℝ := (fun w : ℝ => u₀ + r₀ * w) ⁻¹' (w_fn ⁻¹' Y_Q)
    have hPre_open : IsOpen Pre_U := hU_big_open.preimage (by fun_prop)
    have h0_in_pre : (0 : ℝ) ∈ Pre_U := by simpa [Pre_U] using hsub_big hu₀
    have hcomp_big := iteratedDerivWithin_comp_affine hU_big_open.uniqueDiffOn hPre_open.uniqueDiffOn
      hcd_big hr (v := 0) (by simpa using hsub_big hu₀)
    change iteratedDerivWithin r (fun t => Q_p (w_fn (u₀ + r₀ * t))) Pre_U 0 = _ at hcomp_big
    rw [iteratedDerivWithin_of_isOpen hPre_open h0_in_pre, mul_zero, add_zero, smul_eq_mul,
      iteratedDerivWithin_of_isOpen hU_big_open (hsub_big hu₀)] at hcomp_big
    change iteratedDeriv r (Q_p ∘ w_aff) 0 = r₀ ^ r * iteratedDeriv r (fun u => Q_p (w_fn u)) u₀ at hcomp_big
    rw [hcomp_big, iteratedDerivWithin_eq_iteratedDeriv hDu
      ((hcd_big.contDiffAt (hU_big_open.mem_nhds (hsub_big hu₀))).of_le (by exact_mod_cast hr)) hu₀]
  rw [haff_rel, abs_mul, abs_pow, abs_of_pos hr₀_pos] at hle
  have h1u_pos : 0 < 1 + u₀ := by linarith only [hu₀.1]
  have hr₀_inv_le : (r₀ ^ r)⁻¹ ≤ 100 ^ 8 * (1 + u₀) ^ ((0 : ℝ) - r) := by
    have hpow_le : (100 : ℝ) ^ r ≤ 100 ^ 8 := pow_le_pow_right₀ (by norm_num) hr
    have hr0_inv : r₀⁻¹ = 100 * (1 + u₀)⁻¹ := by dsimp only [r₀]; rw [inv_div]; ring
    rw [← inv_pow, hr0_inv, mul_pow, inv_pow, zero_sub, Real.rpow_neg h1u_pos.le, Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_right hpow_le (inv_nonneg.mpr (pow_nonneg h1u_pos.le r))
  calc |iteratedDerivWithin r (fun u => Q_p (w_fn u)) (Icc 0 (fctUc c)) u₀|
      ≤ (r₀ ^ r)⁻¹ * ((Nat.factorial 8 : ℝ) * B_Q) :=
        (le_inv_mul_iff₀ (pow_pos hr₀_pos r)).mpr hle
    _ ≤ (100 ^ 8 * (1 + u₀) ^ ((0 : ℝ) - r)) * ((Nat.factorial 8 : ℝ) * B_Q) := by gcongr
    _ = 100 ^ 8 * ((Nat.factorial 8 : ℝ) * B_Q) * (1 + u₀) ^ ((0 : ℝ) - r) := by ring

/-! ### 2. Window `J₀ - 1` and `J₀(ell₂) - J₀(ell₁)` bounds -/

private lemma u_sq_sym_win {c : ℝ} (hc0 : 0 < c) :
    FctSymClsOn (Icc 0 (fctUc c)) 8 2 2 (fun u : ℝ => (u : ℂ) ^ 2) := by
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  have hcd : ContDiffOn ℝ 8 (fun u : ℝ => (u : ℂ) ^ 2) (Icc 0 (fctUc c)) :=
    ((Complex.ofRealCLM.contDiff (n := 8)).pow 2).contDiffOn
  refine ⟨hcd, fun r hr u hu => ?_⟩
  have heq : (fun u : ℝ => (u : ℂ) ^ 2) = fun u : ℝ => ((u ^ 2 : ℝ) : ℂ) := funext fun u => by simp
  have hcd_r : ContDiffAt ℝ r (fun u : ℝ => u ^ 2) u :=
    (contDiff_id.pow 2).contDiffAt.of_le le_top
  rw [heq, iteratedDerivWithin_ofReal_cast hDu (by fun_prop) hr u hu, Complex.norm_real, Real.norm_eq_abs]
  have h1u : 0 < 1 + u := by linarith only [hu.1]
  have hu0 : 0 ≤ u := hu.1
  rcases Nat.lt_trichotomy r 1 with hr0 | hr1 | _
  · have : r = 0 := by omega
    subst this; rw [iteratedDerivWithin_zero, abs_of_nonneg (sq_nonneg u)]
    have hsq : u ^ 2 ≤ (1 + u) ^ 2 := pow_le_pow_left₀ hu0 (by linarith) 2
    have h2 : (1 + u) ^ ((2 : ℝ) - (0 : ℕ)) = (1 + u) ^ 2 := by norm_num
    rw [h2]; linarith [sq_nonneg (1 + u)]
  · subst hr1
    rw [iteratedDerivWithin_eq_iteratedDeriv hDu hcd_r hu, iteratedDeriv_one]
    have hdp : deriv (fun u : ℝ => u ^ 2) u = 2 * u := by simp
    rw [hdp, abs_mul, abs_of_pos zero_lt_two, abs_of_nonneg hu0]
    have h1 : (1 + u) ^ ((2 : ℝ) - (1 : ℕ)) = 1 + u := by norm_num
    rw [h1]; linarith
  · rcases Nat.lt_trichotomy r 2 with _ | hr2 | _
    · omega
    · subst hr2
      rw [iteratedDerivWithin_eq_iteratedDeriv hDu hcd_r hu, iteratedDeriv_succ, iteratedDeriv_one]
      have hd1 : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := funext fun x => by simp
      rw [hd1, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one, abs_of_pos zero_lt_two]
      have h0 : (1 + u) ^ ((2 : ℝ) - (2 : ℕ)) = 1 := by norm_num
      rw [h0, mul_one]
    · obtain ⟨m, rfl⟩ : ∃ m, r = m + 3 := ⟨r - 3, by omega⟩
      rw [iteratedDerivWithin_eq_iteratedDeriv hDu hcd_r hu]
      have h2 : iteratedDeriv 2 (fun x : ℝ => x ^ 2) = fun _ => 2 := funext fun x => by
        rw [iteratedDeriv_succ, iteratedDeriv_one]
        have hd1 : deriv (fun y : ℝ => y ^ 2) = fun y => 2 * y := funext fun y => by simp
        rw [hd1]
        simp
      have h3 : ∀ n : ℕ, ∀ x : ℝ, iteratedDeriv (n + 3) (fun y : ℝ => y ^ 2) x = 0 := by
        intro n
        induction n with
        | zero => intro x; rw [zero_add, iteratedDeriv_succ, h2]; simp
        | succ n ih =>
          intro x; rw [show n + 1 + 3 = (n + 3) + 1 by omega, iteratedDeriv_succ]
          have hf : iteratedDeriv (n + 3) (fun y : ℝ => y ^ 2) = fun _ => 0 := funext ih
          rw [hf]; simp
      rw [h3 m u, abs_zero]; exact mul_nonneg zero_le_two (Real.rpow_nonneg h1u.le _)

private lemma hadamard_first_order {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f Yint) (hf0 : f 0 = 0)
    {w : ℝ} (hw : w ∈ Yint) :
    f w = w * ∫ σ in Icc (0 : ℝ) 1, deriv f (σ * w) := by
  have hconv : Convex ℝ Yint := convex_Ioo _ _
  have h0_Y : (0 : ℝ) ∈ Yint := zero_mem_Yint
  have hmap : ∀ σ ∈ Set.uIcc (0 : ℝ) 1, σ * w ∈ Yint := fun σ hσ => by
    rw [uIcc_of_le zero_le_one] at hσ
    simpa [smul_eq_mul] using hconv.smul_mem_of_zero_mem h0_Y hw hσ
  let φ : ℝ → ℝ := fun σ => f (σ * w)
  have hφ_deriv : ∀ σ ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt φ (w * deriv f (σ * w)) σ := fun σ hσ => by
    have hcd := hf.contDiffAt (isOpen_Ioo.mem_nhds (hmap σ hσ))
    have hdf : HasDerivAt f (deriv f (σ * w)) (σ * w) := (hcd.differentiableAt (by norm_num)).hasDerivAt
    have hdσ : HasDerivAt (fun s => s * w) w σ := by simpa using (hasDerivAt_id σ).mul_const w
    exact (HasDerivAt.comp σ hdf hdσ).congr_deriv (mul_comm _ _)
  have hcd1 : ContDiffOn ℝ 1 (deriv f) Yint := by
    have h0 := hf.derivWithin isOpen_Ioo.uniqueDiffOn (by norm_num : ((1 : WithTop ℕ∞) + 1 ≤ 2))
    exact h0.congr fun x hx => (derivWithin_of_isOpen isOpen_Ioo hx).symm
  have hφ_cont : ContinuousOn (fun σ => w * deriv f (σ * w)) (Set.uIcc (0 : ℝ) 1) :=
    continuousOn_const.mul (hcd1.continuousOn.comp (continuous_id.mul continuous_const).continuousOn
      fun σ hσ => hmap σ hσ)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hφ_deriv hφ_cont.intervalIntegrable
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc] at hftc
  simpa [φ, zero_mul, one_mul, hf0, sub_zero] using hftc.symm

private lemma hadamard_second_order_win {f : ℝ → ℝ} (hf : ContDiffOn ℝ 3 f Yint) (hf0 : f 0 = 0)
    {w : ℝ} (hw : w ∈ Yint) :
    f w - deriv f 0 * w =
      w ^ 2 * ∫ σ in Icc (0 : ℝ) 1, (1 - σ) * iteratedDeriv 2 f (σ * w) := by
  have hconv : Convex ℝ Yint := convex_Ioo _ _
  have h0_Y : (0 : ℝ) ∈ Yint := zero_mem_Yint
  have hmap : ∀ σ ∈ Set.uIcc (0 : ℝ) 1, σ * w ∈ Yint := fun σ hσ => by
    rw [uIcc_of_le zero_le_one] at hσ
    simpa [smul_eq_mul] using hconv.smul_mem_of_zero_mem h0_Y hw hσ
  have hcd2 : ContDiffOn ℝ 2 (deriv f) Yint := by
    have h0 := hf.derivWithin isOpen_Ioo.uniqueDiffOn (by norm_num : ((2 : WithTop ℕ∞) + 1 ≤ 3))
    exact h0.congr fun x hx => (derivWithin_of_isOpen isOpen_Ioo hx).symm
  have hcd3 : ContDiffOn ℝ 1 (iteratedDeriv 2 f) Yint := by
    have h0 := hcd2.derivWithin isOpen_Ioo.uniqueDiffOn (by norm_num : ((1 : WithTop ℕ∞) + 1 ≤ 2))
    exact h0.congr fun x hx => by
      rw [iteratedDeriv_succ, iteratedDeriv_one, derivWithin_of_isOpen isOpen_Ioo hx]
  let φ : ℝ → ℝ := fun σ => f (σ * w) + (1 - σ) * w * deriv f (σ * w)
  have hφ_deriv : ∀ σ ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt φ (w ^ 2 * ((1 - σ) * iteratedDeriv 2 f (σ * w))) σ := fun σ hσ => by
    have hy := hmap σ hσ
    have hcd := hf.contDiffAt (isOpen_Ioo.mem_nhds hy)
    have hdf1 : HasDerivAt f (deriv f (σ * w)) (σ * w) := (hcd.differentiableAt (by norm_num)).hasDerivAt
    have hdf2 : HasDerivAt (deriv f) (iteratedDeriv 2 f (σ * w)) (σ * w) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      exact ((hcd2.contDiffAt (isOpen_Ioo.mem_nhds hy)).differentiableAt (by norm_num)).hasDerivAt
    have hdσ : HasDerivAt (fun s => s * w) w σ := by simpa using (hasDerivAt_id σ).mul_const w
    have h1 := HasDerivAt.comp σ hdf1 hdσ
    have h2 : HasDerivAt (fun s => (1 - s) * w) (-w) σ := by
      have := ((hasDerivAt_const σ (1 : ℝ)).sub (hasDerivAt_id σ)).mul_const w
      exact this.congr_deriv (by ring)
    have h3 := HasDerivAt.comp σ hdf2 hdσ
    exact (h1.add (h2.mul h3)).congr_deriv (by dsimp only [Function.comp_def]; ring)
  have hcont : ContinuousOn (fun σ => w ^ 2 * ((1 - σ) * iteratedDeriv 2 f (σ * w))) (Set.uIcc (0 : ℝ) 1) :=
    continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).mul
      (hcd3.continuousOn.comp (continuous_id.mul continuous_const).continuousOn fun σ hσ => hmap σ hσ))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hφ_deriv hcont.intervalIntegrable
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc] at hftc
  dsimp only [φ] at hftc
  rw [one_mul, sub_self, zero_mul, zero_mul, add_zero, hf0, sub_zero, zero_add,
    one_mul, mul_comm w (deriv f 0)] at hftc
  exact hftc.symm

/-- On `[0, Sw_ell c^{-1/6}]`, `J₀(q₀(ell₂), Y(u)) - 1 ∈ 𝒮^{10}(C c^{-4/3})` and
`J₀(q₀(ell₂), Y(u)) - J₀(q₀(ell₁), Y(u)) ∈ 𝒮^{10}(C c^{-7/6} (ell₂ - ell₁))`. -/
theorem win_J0_sub_one_and_diff {K4 Sw_ell : ℝ} (hK4 : 1 ≤ K4) (hSw : 1 ≤ Sw_ell) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 32 ^ 4 ≤ c₀ ∧ ∀ {ε c α ell1 ell2 : ℝ},
      (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      c ^ (-(1 / 4 : ℝ)) ≤ pbTauLim → K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 →
      |α| ≤ c ^ (-(1 / 2 : ℝ)) →
      0 ≤ ell1 → ell1 ≤ ell2 → ell2 ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) →
      let S := concreteBoxS K4 ε c
      let τ₁ := c ^ (-(1 / 4 : ℝ))
      let J0 := fun (ell u : ℝ) => ((Jfun S.V fctH (τ₁ ^ 2) ((ell, 0, α), fctInnerY c u) - 1 : ℝ) : ℂ)
      FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C * c ^ (-(4 / 3 : ℝ))) (J0 ell2) ∧
      FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C * c ^ (-(7 / 6 : ℝ)) * (ell2 - ell1))
        (fun u => J0 ell2 u - J0 ell1 u) := by
  obtain ⟨r_star, B_Jrs, δH, hr_pos, _, hδH_pos, _, _, hr_cR, hB_Jrs0, hSrs_all⟩ :=
    r_rs_chart_exist pbM_nonneg (by norm_num : (0 : ℝ) ≤ 2) pbC0_nonneg
  have hr2_pos : 0 < r_star ^ 2 := sq_pos_of_pos hr_pos
  let Y_Q : Set ℝ := Ioo (-(1 / 10 : ℝ)) 1
  let bw_Q : ℝ := 2 ^ 13 * 1 * ((Nat.factorial 13 : ℝ) * 1)
  let C_comp_Q : ℝ := (Nat.factorial 13 : ℝ) * (max 1 (max 1 bw_Q)) ^ 13
  let B_Q1 : ℝ := 2 ^ 13 * 2 * C_comp_Q * B_Jrs
  let B_Q : ℝ := (Nat.factorial 8 : ℝ) * B_Q1
  let B_D1 : ℝ := (Nat.factorial 8 : ℝ) * (C_comp_Q * B_Jrs)
  let C_Q_sym : ℝ := 100 ^ 8 * ((Nat.factorial 8 : ℝ) * B_Q)
  let C_D1_sym : ℝ := 100 ^ 8 * ((Nat.factorial 8 : ℝ) * B_D1)
  let C_d : ℝ := B_Jrs * (Sw_ell / r_star ^ 2 + 1 / r_star ^ 2)
  let C_w : ℝ := 2 / r_star ^ 2
  let C_J0 : ℝ := C_d * C_w + 2 ^ 8 * (2 ^ 8 * C_w * C_w) * C_Q_sym
  let C_J0_d : ℝ := 2 ^ 8 * C_w * (C_D1_sym / r_star ^ 2)
  let C_tot : ℝ := max C_J0 C_J0_d
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      (160000 : ℝ) ≤ c ∧ (30 * pbC0 + 1) ^ 2 ≤ c ∧
      (161 / r_star ^ 2) ^ 2 ≤ c ∧ 2 / r_star ^ 2 ≤ c ∧
      c ^ (-(1 / 2 : ℝ)) < δH / 6 ∧
      (Sw_ell / r_star ^ 2 + 1) * c ^ (-(2 / 3 : ℝ)) < 1 / 20 ∧
      Sw_ell * c ^ (-(1 / 6 : ℝ)) < 27 / 10 := by
    refine Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
      (Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
        (Eventually.and ?_ (Eventually.and ?_ ?_)))))
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually (Iio_mem_nhds (by positivity))
    · have h0 : Tendsto (fun c : ℝ => (Sw_ell / r_star ^ 2 + 1) * c ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul
          (Sw_ell / r_star ^ 2 + 1)
      exact h0.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 20))
    · have h0 : Tendsto (fun c : ℝ => Sw_ell * c ^ (-(1 / 6 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).const_mul Sw_ell
      exact h0.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 27 / 10))
  obtain ⟨c_ev, hc_ev⟩ := eventually_atTop.mp hc_ev
  refine ⟨C_tot, max (32 ^ 4) c_ev, by positivity, le_max_left _ _,
    fun {ε c α ell1 ell2} hε hc hτ_lim hK4t hα hell1 h12 hell2 => ?_⟩
  obtain ⟨hc160000, hc_C0, hc_r1, hc_r2, hτ1_δH, hprs_small, hSw_4⟩ :=
    hc_ev c ((le_max_right _ _).trans hc)
  have hc32 : (32 : ℝ) ^ 4 ≤ c := (le_max_left _ _).trans hc
  have hc100 : (100 : ℝ) ≤ c := le_trans (by norm_num) hc32
  have hc0 : 0 < c := by linarith only [hc100]
  have hc1 : 1 ≤ c := by linarith only [hc100]
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  have hvalid : concreteBoxValid K4 ε c := ⟨hK4, hε, hc0, hτ_lim, hK4t⟩
  set T := concreteBoxT K4 ε c
  set S := concreteBoxS K4 ε c
  obtain ⟨hTM, hTmt, _, hSΩ, hSℓ, hSr, hSε, _, _, _⟩ := concreteBox_spec hvalid
  set τ₁ : ℝ := c ^ (-(1 / 4 : ℝ))
  have hτ₁_pos : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hτ₁_sq : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
    dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hτ₁_4 : τ₁ ^ 4 = c⁻¹ := by
    dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num [Real.rpow_neg_one]
  have hc_half : 161 / r_star ^ 2 ≤ c ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le hc_r1
  have hc_neg_half : c ^ (-(1 / 2 : ℝ)) ≤ r_star ^ 2 / 161 := by
    rw [Real.rpow_neg hc0.le, inv_le_comm₀ (Real.rpow_pos_of_pos hc0 _) (by positivity)]
    simpa [inv_div] using hc_half
  have hsub30 : Ioo (-(1 / 30 : ℝ)) (1 / 30) ⊆ Ioo (-1 : ℝ) 6 := fun x hx =>
    ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
  have jc_30 : ∀ {g : ℝ → ℝ}, JC 18 (Ioo (-1 : ℝ) 6) g pbM → JC 18 (Ioo (-(1 / 30 : ℝ)) (1 / 30)) g pbM :=
    fun {g} hg => ⟨hg.1.mono hsub30, fun i hi x hx => by
      rw [iteratedFDerivWithin_of_isOpen (n := i) isOpen_Ioo hx,
        ← iteratedFDerivWithin_of_isOpen (n := i) isOpen_Ioo (hsub30 hx)]
      exact hg.2 i hi x (hsub30 hx)⟩
  obtain ⟨S_rs, hSrs_Ω, hSrs_ℓ, hSrs_r, h15rs, hJrs_jc, hJrs_0, hJrs_d0⟩ :=
    hSrs_all (jc_30 (by rw [← hTM, ← hTmt]; exact T.jc_mt)) (jc_30 (by rw [← hTM]; exact T.jc_θt))
  let J_rs : (ℝ × ℝ) × ℝ → ℝ := Jfun S_rs.V fctH (r_star ^ 2)
  have hO_rs : IsOpen (fctOmegaRs ×ˢ Yint) := isOpen_fctOmegaRs.prod isOpen_Ioo
  have hUd_rs : UniqueDiffOn ℝ (fctOmegaRs ×ˢ Yint) := hO_rs.uniqueDiffOn
  let lam : ℝ := τ₁ ^ 2 / r_star ^ 2
  have hlam_pos : 0 < lam := div_pos (sq_pos_of_pos hτ₁_pos) hr2_pos
  have hlam_16 : lam ≤ 1 / 6 := by
    have h1 : τ₁ ^ 2 ≤ r_star ^ 2 / 161 := hτ₁_sq ▸ hc_neg_half
    dsimp only [lam]; rw [div_le_iff₀ hr2_pos]; linarith
  have hlam_le_c : lam ≤ (1 / r_star ^ 2) * c ^ (-(1 / 2 : ℝ)) := by
    dsimp only [lam]; rw [hτ₁_sq]; ring_nf; rfl
  have hlam_div_le : lam ≤ c ^ (-(1 / 2 : ℝ)) / r_star ^ 2 := by
    dsimp only [lam]; rw [hτ₁_sq]
  have hSε_bd : 15 * S.ε ≤ 1 / 2 := by
    have h1 : 30 * pbC0 + 1 ≤ c ^ (1 / 2 : ℝ) := by rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le hc_C0
    have hpos : (0 : ℝ) < 30 * pbC0 + 1 := by linarith only [pbC0_nonneg]
    rw [hSε, hτ₁_sq, Real.rpow_neg hc0.le]
    have h2 : pbC0 * (c ^ (1 / 2 : ℝ))⁻¹ ≤ 1 / 30 := by
      calc pbC0 * (c ^ (1 / 2 : ℝ))⁻¹ ≤ pbC0 * (30 * pbC0 + 1)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ hpos h1) pbC0_nonneg
        _ ≤ 1 / 30 := by rw [← div_eq_mul_inv, div_le_div_iff₀ hpos (by norm_num)]; linarith only
    linarith only [h2]
  have hα_om : |α| < 2 * τ₁ ^ 2 := by
    rw [hτ₁_sq]; linarith only [hα, Real.rpow_pos_of_pos hc0 (-(1 / 2 : ℝ))]
  have hp_mem_of : ∀ {ell : ℝ}, 0 ≤ ell → ell ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) →
      (ell, 0, α) ∈ S.Ω := fun {ell} hell0 hell_ub => by
    rw [hSΩ]
    exact ⟨⟨by linarith only [hell0], by linarith only [hell_ub, hSw_4]⟩,
      ⟨by norm_num, by norm_num⟩, by simpa [abs_lt] using hα_om⟩
  have hp_rs_of : ∀ {ell : ℝ}, 0 ≤ ell → ell ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) →
      (lam * ell, τ₁ ^ 4 / r_star ^ 2) ∈ fctOmegaRs ∧
      ‖((lam * ell, τ₁ ^ 4 / r_star ^ 2) : ℝ × ℝ)‖ ≤ (Sw_ell / r_star ^ 2 + 1 / r_star ^ 2) * c ^ (-(2 / 3 : ℝ)) := by
    intro ell hell0 hell_ub
    have hc1_23 : c ^ (-1 : ℝ) ≤ c ^ (-(2 / 3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have htau4_le : τ₁ ^ 4 / r_star ^ 2 ≤ (1 / r_star ^ 2) * c ^ (-(2 / 3 : ℝ)) := by
      rw [hτ₁_4, ← Real.rpow_neg_one]; calc c ^ (-1 : ℝ) / r_star ^ 2 = (1 / r_star ^ 2) * c ^ (-1 : ℝ) := by ring
        _ ≤ (1 / r_star ^ 2) * c ^ (-(2 / 3 : ℝ)) := by gcongr
    have hc4_lt : τ₁ ^ 4 / r_star ^ 2 < 1 := by
      have h1 : 1 / r_star ^ 2 ≤ Sw_ell / r_star ^ 2 + 1 :=
        (div_le_div_of_nonneg_right hSw hr2_pos.le).trans (le_add_of_nonneg_right zero_le_one)
      have hc23_nn : 0 ≤ c ^ (-(2 / 3 : ℝ)) := by positivity
      calc τ₁ ^ 4 / r_star ^ 2 ≤ (Sw_ell / r_star ^ 2 + 1) * c ^ (-(2 / 3 : ℝ)) :=
            htau4_le.trans (mul_le_mul_of_nonneg_right h1 hc23_nn)
        _ < 1 / 20 := hprs_small
        _ < 1 := by norm_num
    have hlam_ell_le : lam * ell ≤ (Sw_ell / r_star ^ 2) * c ^ (-(2 / 3 : ℝ)) := by
      have hc12_16 : c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 6 : ℝ)) = c ^ (-(2 / 3 : ℝ)) := by
        rw [← Real.rpow_add hc0]; norm_num
      calc lam * ell ≤ (1 / r_star ^ 2 * c ^ (-(1 / 2 : ℝ))) * (Sw_ell * c ^ (-(1 / 6 : ℝ))) :=
            mul_le_mul hlam_le_c hell_ub hell0 (by positivity)
        _ = (Sw_ell / r_star ^ 2) * (c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 6 : ℝ))) := by ring
        _ = _ := by rw [hc12_16]
    have hlam_ell_lt : lam * ell < 1 / 20 := by
      have : (Sw_ell / r_star ^ 2) * c ^ (-(2 / 3 : ℝ)) ≤ (Sw_ell / r_star ^ 2 + 1) * c ^ (-(2 / 3 : ℝ)) := by
        gcongr; linarith
      exact (hlam_ell_le.trans this).trans_lt hprs_small
    have hnorm : ‖((lam * ell, τ₁ ^ 4 / r_star ^ 2) : ℝ × ℝ)‖ ≤
        (Sw_ell / r_star ^ 2 + 1 / r_star ^ 2) * c ^ (-(2 / 3 : ℝ)) := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hlam_pos.le hell0), abs_of_pos (div_pos (pow_pos hτ₁_pos 4) hr2_pos)]
      refine max_le (hlam_ell_le.trans (mul_le_mul_of_nonneg_right (by linarith [show (0 : ℝ) ≤ 1 / r_star ^ 2 by positivity]) (by positivity)))
        (htau4_le.trans (mul_le_mul_of_nonneg_right (by linarith [show (0 : ℝ) ≤ Sw_ell / r_star ^ 2 by positivity]) (by positivity)))
    exact ⟨⟨⟨by linarith [mul_nonneg hlam_pos.le hell0], hlam_ell_lt⟩,
      ⟨by linarith [div_pos (pow_pos hτ₁_pos 4) hr2_pos], hc4_lt⟩⟩, hnorm⟩
  have hR_small_of : ∀ {ell : ℝ}, 0 ≤ ell → ell ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) →
      ∀ z ∈ Ioo (-1 : ℝ) 6, |lam⁻¹ * S.R ((ell, 0, α), z)| < 1 / 50 := by
    intro ell hell0 hell_ub z hz
    have hp_mem := hp_mem_of hell0 hell_ub
    have hReq := S.out.2.2.2.2.2.1 ((ell, 0, α), z) ⟨hp_mem, hz⟩
    have hBmem := (S.out.2.1 _ hp_mem).1
    have hd_abs := abs_le.mp (S.d_dev hp_mem)
    have hd_lo : (92 / 100 : ℝ) ≤ S.d (ell, 0, α) := by linarith only [hd_abs.1, dStar_bounds.1]
    have hd_hi : S.d (ell, 0, α) ≤ 95 / 100 := by linarith only [hd_abs.2, dStar_bounds.2]
    have hz6 : |z| ≤ 6 := by rw [abs_le]; constructor <;> linarith only [hz.1, hz.2]
    have hzB7 : |z - S.B (ell, 0, α)| ≤ 7 := by rw [abs_le]; constructor <;> linarith only [hz.1, hz.2, hBmem.1, hBmem.2]
    have hR50 : |S.R ((ell, 0, α), z)| ≤ 1 / 50 := hReq.1.le
    let coef := S.d (ell, 0, α) ^ 2 + S.d (ell, 0, α) * z * S.R ((ell, 0, α), z) +
      1 / 3 * z * (z - S.B (ell, 0, α)) * S.R ((ell, 0, α), z) ^ 2
    have h1 : |S.d (ell, 0, α) * z * S.R ((ell, 0, α), z)| ≤ (95 / 100) * 6 * (1 / 50) := by
      rw [abs_mul, abs_mul, abs_of_pos (by linarith only [hd_lo])]
      exact mul_le_mul (mul_le_mul hd_hi hz6 (abs_nonneg z) (by positivity)) hR50 (abs_nonneg _) (by positivity)
    have h2 : |1 / 3 * z * (z - S.B (ell, 0, α)) * S.R ((ell, 0, α), z) ^ 2| ≤
        (1 / 3 : ℝ) * 6 * 7 * (1 / 50) ^ 2 := by
      rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)]
      have hh : (1 / 3 : ℝ) * |z| * |z - S.B (ell, 0, α)| ≤ (1 / 3 : ℝ) * 6 * 7 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hz6 (by norm_num)) hzB7 (abs_nonneg _) (by positivity)
      exact mul_le_mul hh (pow_le_pow_left₀ (abs_nonneg _) hR50 2) (sq_nonneg _) (by positivity)
    have hcoef_ge : (1 / 2 : ℝ) ≤ coef := by
      have hdsq : (92 / 100 : ℝ) ^ 2 ≤ S.d (ell, 0, α) ^ 2 := by nlinarith only [hd_lo]
      dsimp only [coef]; linarith only [hdsq, (abs_le.mp h1).1, (abs_le.mp h2).1]
    have hhad_bd : |hadH S.r S.B ((ell, 0, α), z)| ≤ S.ε := by
      unfold hadH
      have hO : IsOpen (S.Ω ×ˢ Ioo (-1 : ℝ) 6) := S.hΩ.prod isOpen_Ioo
      have h17 := (S.hr.succ_fderiv hO).clm_apply_const hO.uniqueDiffOn ((0 : ℝ × ℝ × ℝ), (1 : ℝ))
      have h_int_bd : ∀ σ ∈ Icc (0 : ℝ) 1,
          ‖(1 - σ) * fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1))
            ((ell, 0, α), S.B (ell, 0, α) + σ * (z - S.B (ell, 0, α))) (0, 1)‖ ≤ S.ε := by
        intro σ hσ
        have hqσ : ((ell, 0, α), S.B (ell, 0, α) + σ * (z - S.B (ell, 0, α))) ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6 :=
          ⟨hp_mem, by simpa [smul_eq_mul] using (convex_Ioo (-1 : ℝ) 6).add_smul_sub_mem hBmem hz hσ⟩
        have hbd := h17.2 1 (by norm_num) _ hqσ
        rw [norm_iteratedFDerivWithin_one _ (hO.uniqueDiffOn _ hqσ), fderivWithin_of_isOpen hO hqσ] at hbd
        have hbd' : ‖fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1))
            ((ell, 0, α), S.B (ell, 0, α) + σ * (z - S.B (ell, 0, α)))‖ ≤ S.ε := by
          simpa [Prod.norm_def] using hbd
        have hfd : ‖fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1))
            ((ell, 0, α), S.B (ell, 0, α) + σ * (z - S.B (ell, 0, α))) ((0 : ℝ × ℝ × ℝ), (1 : ℝ))‖ ≤ S.ε :=
          ((fderiv ℝ _ _).le_opNorm _).trans (by rw [show ‖((0 : ℝ × ℝ × ℝ), (1 : ℝ))‖ = 1 by simp [Prod.norm_def], mul_one]; exact hbd')
        have h1σ : ‖(1 - σ : ℝ)‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (by linarith only [hσ.2])]; linarith only [hσ.1]
        rw [norm_mul]; exact (mul_le_mul h1σ hfd (norm_nonneg _) zero_le_one).trans_eq (one_mul S.ε)
      have hint_le := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume)
        (show volume (Icc (0 : ℝ) 1) < ⊤ by simp) h_int_bd
      simpa [Real.norm_eq_abs, Real.volume_Icc] using hint_le
    have hR_le : |S.R ((ell, 0, α), z)| ≤ 2 * S.ε := by
      have hReq2 := hReq.2; dsimp only at hReq2
      have heq : S.R ((ell, 0, α), z) * coef = -hadH S.r S.B ((ell, 0, α), z) := by
        dsimp only [coef]; exact eq_neg_of_add_eq_zero_right hReq2
      have hab : |S.R ((ell, 0, α), z)| * |coef| = |hadH S.r S.B ((ell, 0, α), z)| := by
        rw [← abs_mul, heq, abs_neg]
      rw [abs_of_pos (lt_of_lt_of_le (by norm_num) hcoef_ge)] at hab
      calc |S.R ((ell, 0, α), z)| = 2 * (1 / 2 * |S.R ((ell, 0, α), z)|) := by ring
        _ ≤ 2 * (|S.R ((ell, 0, α), z)| * coef) := by
            have := mul_le_mul_of_nonneg_right hcoef_ge (abs_nonneg (S.R ((ell, 0, α), z))); linarith only [this]
        _ = 2 * |hadH S.r S.B ((ell, 0, α), z)| := by rw [hab]
        _ ≤ 2 * S.ε := by gcongr
    rw [abs_mul, abs_of_pos (inv_pos.mpr hlam_pos)]
    calc lam⁻¹ * |S.R ((ell, 0, α), z)| ≤ lam⁻¹ * (2 * S.ε) := by gcongr
      _ = 2 * pbC0 * r_star ^ 2 := by dsimp only [lam]; rw [hSε, inv_div]; field_simp [pow_ne_zero 2 hτ₁_pos.ne']
      _ < 1 / 50 := hr_cR
  -- `JC` setup for `Jrs_d`, `Jrs_dd`, `Q_rs`, `D1_rs`
  have hJrs_d14 : JC 14 (fctOmegaRs ×ˢ Yint) (fun q => fderiv ℝ J_rs q (0, 1)) B_Jrs :=
    JC.deriv_snd hO_rs hJrs_jc
  let Jrs_d : (ℝ × ℝ) × ℝ → ℝ := fun q => fderiv ℝ J_rs q (0, 1)
  let Jrs_dd : (ℝ × ℝ) × ℝ → ℝ := fun q => fderiv ℝ Jrs_d q (0, 1)
  have hJrs_dd_jc : JC 13 (fctOmegaRs ×ˢ Yint) Jrs_dd B_Jrs := JC.deriv_snd hO_rs hJrs_d14
  have hO_Q : IsOpen (fctOmegaRs ×ˢ Y_Q) := isOpen_fctOmegaRs.prod isOpen_Ioo
  have hUd_Q : UniqueDiffOn ℝ (fctOmegaRs ×ˢ Y_Q) := hO_Q.uniqueDiffOn
  have hUd_Q3 : UniqueDiffOn ℝ ((fctOmegaRs ×ˢ Y_Q) ×ˢ Icc (0 : ℝ) 1) :=
    hUd_Q.prod (uniqueDiffOn_Icc zero_lt_one)
  have hσ_jc : JC 13 ((fctOmegaRs ×ˢ Y_Q) ×ˢ Icc (0 : ℝ) 1) (fun x : ((ℝ × ℝ) × ℝ) × ℝ => x.2) 1 :=
    JC.snd hUd_Q3 le_rfl fun x hx => by rw [abs_le]; constructor <;> linarith only [hx.2.1, hx.2.2]
  have hw0_jc : JC 13 (fctOmegaRs ×ˢ Y_Q) (fun q : (ℝ × ℝ) × ℝ => q.2) 1 :=
    JC.snd hUd_Q le_rfl fun q hq => by rw [abs_le]; constructor <;> linarith only [hq.2.1, hq.2.2]
  have hw_jc : JC 13 ((fctOmegaRs ×ˢ Y_Q) ×ˢ Icc (0 : ℝ) 1)
      (fun x : ((ℝ × ℝ) × ℝ) × ℝ => x.1.2) ((Nat.factorial 13 : ℝ) * 1) :=
    JC.comp_clm hUd_Q3 hUd_Q (ContinuousLinearMap.fst ℝ ((ℝ × ℝ) × ℝ) ℝ) (norm_fst_le_one _ _)
      (by norm_num : (0 : ℝ) ≤ 1) hw0_jc fun x hx => hx.1
  let L_p : (((ℝ × ℝ) × ℝ) × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).comp (ContinuousLinearMap.fst ℝ ((ℝ × ℝ) × ℝ) ℝ)
  have hLp_n : ‖L_p‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    have h1 := norm_fst_le_one (ℝ × ℝ) ℝ
    have h2 := norm_fst_le_one ((ℝ × ℝ) × ℝ) ℝ
    nlinarith only [h1, h2, norm_nonneg (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ),
      norm_nonneg (ContinuousLinearMap.fst ℝ ((ℝ × ℝ) × ℝ) ℝ)])
  have hmul_σw : JC 13 ((fctOmegaRs ×ˢ Y_Q) ×ˢ Icc (0 : ℝ) 1)
      (fun x : ((ℝ × ℝ) × ℝ) × ℝ => x.2 * x.1.2) bw_Q :=
    (JC.mul hUd_Q3 zero_le_one (by positivity) hσ_jc hw_jc).mono (le_of_eq (by dsimp only [bw_Q]))
  have hLp_u : ∀ i, 1 ≤ i → i ≤ 13 → ∀ y ∈ ((fctOmegaRs ×ˢ Y_Q) ×ˢ Icc (0 : ℝ) 1),
      ‖iteratedFDerivWithin ℝ i (fun x : ((ℝ × ℝ) × ℝ) × ℝ => L_p x)
        ((fctOmegaRs ×ˢ Y_Q) ×ˢ Icc (0 : ℝ) 1) y‖ ≤ 1 :=
    fun i hi _ y hy => (norm_iteratedFDerivWithin_clm_le hUd_Q3 L_p hi hy).trans hLp_n
  have hmap_sw : MapsTo (fun x : ((ℝ × ℝ) × ℝ) × ℝ => (L_p x, x.2 * x.1.2))
      ((fctOmegaRs ×ˢ Y_Q) ×ˢ Icc (0 : ℝ) 1) (fctOmegaRs ×ˢ Yint) := fun x hx => by
    have hq2 : x.1.2 ∈ Ioo (-(1 / 10 : ℝ)) 1 := hx.1.2
    exact ⟨hx.1.1, ⟨by nlinarith only [hx.2.1, hx.2.2, hq2.1, hq2.2],
      by nlinarith only [hx.2.1, hx.2.2, hq2.1, hq2.2]⟩⟩
  have hQ_comp := JC.comp_pair hUd_Q3 hUd_rs (g := Jrs_dd)
    (u := fun x => L_p x) (w := fun x => x.2 * x.1.2) (b1 := 1) (b2 := bw_Q)
    hB_Jrs0 hJrs_dd_jc L_p.contDiff.contDiffOn hmul_σw.1 hLp_u
    (fun i _ hi y hy => hmul_σw.2 i hi y hy) hmap_sw
  have h1mσ : JC 13 ((fctOmegaRs ×ˢ Y_Q) ×ˢ Icc (0 : ℝ) 1)
      (fun x : ((ℝ × ℝ) × ℝ) × ℝ => 1 - x.2) 2 :=
    ((JC.const hUd_Q3 (1 : ℝ)).sub hUd_Q3 hσ_jc).mono (by norm_num)
  have hQ_integrand : JC 13 ((fctOmegaRs ×ˢ Y_Q) ×ˢ Icc (0 : ℝ) 1)
      (fun x : ((ℝ × ℝ) × ℝ) × ℝ => (1 - x.2) * Jrs_dd (x.1.1, x.2 * x.1.2)) B_Q1 :=
    (JC.mul hUd_Q3 (by norm_num : (0 : ℝ) ≤ 2) (by positivity) h1mσ hQ_comp).mono (le_of_eq (by dsimp only [B_Q1, C_comp_Q]; ring))
  let Q_rs : (ℝ × ℝ) × ℝ → ℝ := fun q => ∫ σ in Icc (0 : ℝ) 1, (1 - σ) * Jrs_dd (q.1, σ * q.2)
  have hQ_rs_jc : JC 13 (fctOmegaRs ×ˢ Y_Q) Q_rs B_Q1 :=
    JC.integral01 hO_Q (f := fun q σ => (1 - σ) * Jrs_dd (q.1, σ * q.2)) hQ_integrand
  have hD1_comp := JC.comp_pair hUd_Q3 hUd_rs (g := Jrs_d)
    (u := fun x => L_p x) (w := fun x => x.2 * x.1.2) (b1 := 1) (b2 := bw_Q)
    hB_Jrs0 (hJrs_d14.mono_order (by norm_num)) L_p.contDiff.contDiffOn hmul_σw.1 hLp_u
    (fun i _ hi y hy => hmul_σw.2 i hi y hy) hmap_sw
  let D1_rs : (ℝ × ℝ) × ℝ → ℝ := fun q => ∫ σ in Icc (0 : ℝ) 1, Jrs_d (q.1, σ * q.2)
  have hD1_rs_jc : JC 13 (fctOmegaRs ×ˢ Y_Q) D1_rs (C_comp_Q * B_Jrs) :=
    JC.integral01 hO_Q (f := fun q σ => Jrs_d (q.1, σ * q.2))
      (hD1_comp.mono (le_of_eq (by dsimp only [C_comp_Q]; ring)))
  let w_fn : ℝ → ℝ := fun u => lam * fctInnerY c u
  have hw_sym : FctSymClsOn (Icc 0 (fctUc c)) 8 2 (C_w * c ^ (-(2 / 3 : ℝ))) (fun u => ((w_fn u : ℝ) : ℂ)) := by
    let k_w : ℝ := lam * 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ))
    have hsc := (u_sq_sym_win hc0).const_mul hDu (k_w : ℂ)
    have hkw_nn : 0 ≤ k_w := by dsimp only [k_w]; positivity
    have hle : ‖(k_w : ℂ)‖ * 2 ≤ C_w * c ^ (-(2 / 3 : ℝ)) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hkw_nn]
      have h243 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
      have hc_eq : c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 6 : ℝ)) = c ^ (-(2 / 3 : ℝ)) := by
        rw [← Real.rpow_add hc0]; norm_num
      calc k_w * 2 ≤ (1 / r_star ^ 2 * c ^ (-(1 / 2 : ℝ))) * 1 * c ^ (-(1 / 6 : ℝ)) * 2 := by
            dsimp only [k_w]; gcongr
        _ = C_w * (c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 6 : ℝ))) := by dsimp only [C_w]; ring
        _ = C_w * c ^ (-(2 / 3 : ℝ)) := by rw [hc_eq]
    refine (hsc.mono_B Icc_subset_Ici_self hle).congr hDu fun u _ => ?_
    dsimp only [k_w, w_fn, fctInnerY]; push_cast; ring
  have hell2_nn : 0 ≤ ell2 := hell1.trans h12
  obtain ⟨hp_rs1_mem, _⟩ := hp_rs_of hell1 (h12.trans hell2)
  obtain ⟨hp_rs2_mem, hp_rs2_norm⟩ := hp_rs_of hell2_nn hell2
  let p_rs1 : ℝ × ℝ := (lam * ell1, τ₁ ^ 4 / r_star ^ 2)
  let p_rs2 : ℝ × ℝ := (lam * ell2, τ₁ ^ 4 / r_star ^ 2)
  have hUd_YQ : UniqueDiffOn ℝ Y_Q := isOpen_Ioo.uniqueDiffOn
  -- Part A: `J0 ell2 ∈ 𝒮^8_{10}(C_tot c^{-4/3})`
  have hJ0_ell2 : FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C_tot * c ^ (-(4 / 3 : ℝ)))
      (fun u => ((Jfun S.V fctH (τ₁ ^ 2) ((ell2, 0, α), fctInnerY c u) - 1 : ℝ) : ℂ)) := by
    let F_der : ℝ × ℝ → ℝ := fun p => fderiv ℝ J_rs (p, 0) (0, 1)
    have hF_diff : ∀ p ∈ fctOmegaRs, HasFDerivWithinAt F_der
        ((fderiv ℝ (fun q => fderiv ℝ J_rs q (0, 1)) (p, 0)).comp (ContinuousLinearMap.inl ℝ (ℝ × ℝ) ℝ))
        fctOmegaRs p := fun p hp => by
      have h1 := ((hJrs_d14.1.contDiffAt (hO_rs.mem_nhds (show ((p, (0 : ℝ)) : (ℝ × ℝ) × ℝ) ∈ fctOmegaRs ×ˢ Yint from ⟨hp, zero_mem_Yint⟩))).differentiableAt (by norm_num)).hasFDerivAt
      have h2 : HasFDerivAt (fun x : ℝ × ℝ => (x, (0 : ℝ))) (ContinuousLinearMap.inl ℝ (ℝ × ℝ) ℝ) p :=
        (hasFDerivAt_id p).prodMk (hasFDerivAt_const 0 p)
      exact (h1.comp p h2).hasFDerivWithinAt
    have hF_bd : ∀ p ∈ fctOmegaRs,
        ‖(fderiv ℝ (fun q => fderiv ℝ J_rs q (0, 1)) (p, 0)).comp (ContinuousLinearMap.inl ℝ (ℝ × ℝ) ℝ)‖ ≤ B_Jrs := fun p hp => by
      have hq0 : (p, (0 : ℝ)) ∈ fctOmegaRs ×ˢ Yint := ⟨hp, zero_mem_Yint⟩
      have hb := hJrs_d14.2 1 (by norm_num) _ hq0
      rw [norm_iteratedFDerivWithin_one _ (hUd_rs _ hq0), fderivWithin_of_isOpen hO_rs hq0] at hb
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul hb (ContinuousLinearMap.norm_inl_le_one ℝ (ℝ × ℝ) ℝ) (norm_nonneg _) hB_Jrs0).trans_eq (mul_one _))
    have hp00_mem : ((0 : ℝ), (0 : ℝ)) ∈ fctOmegaRs := ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
    have hF_der_eq : ∀ p ∈ fctOmegaRs, deriv (fun w => J_rs (p, w)) 0 = F_der p := fun p hp => by
      have h1 := ((hJrs_jc.1.contDiffAt (hO_rs.mem_nhds (show ((p, (0 : ℝ)) : (ℝ × ℝ) × ℝ) ∈ fctOmegaRs ×ˢ Yint from ⟨hp, zero_mem_Yint⟩))).differentiableAt (by norm_num)).hasFDerivAt
      exact (h1.comp_hasDerivAt 0 (by simpa using (hasDerivAt_const (0 : ℝ) p).prodMk (hasDerivAt_id (0 : ℝ)))).deriv
    have hF00 : F_der (0, 0) = 0 := by rw [← hF_der_eq (0, 0) hp00_mem]; exact hJrs_d0
    have hmv_der := (convex_Ioo (-(1 / 20 : ℝ)) (1 / 20)).prod (convex_Ioo (-1 : ℝ) 1) |>.norm_image_sub_le_of_norm_hasFDerivWithin_le
      hF_diff hF_bd hp00_mem hp_rs2_mem
    have hder_prs_bd : |deriv (fun w => J_rs (p_rs2, w)) 0| ≤ C_d * c ^ (-(2 / 3 : ℝ)) := by
      rw [hF_der_eq p_rs2 hp_rs2_mem]
      have h1 : ‖F_der p_rs2‖ ≤ B_Jrs * ‖p_rs2‖ := by
        rw [hF00, sub_zero, show p_rs2 - ((0 : ℝ), (0 : ℝ)) = p_rs2 from sub_zero p_rs2] at hmv_der
        exact hmv_der
      rw [Real.norm_eq_abs] at h1
      calc |F_der p_rs2| ≤ B_Jrs * ((Sw_ell / r_star ^ 2 + 1 / r_star ^ 2) * c ^ (-(2 / 3 : ℝ))) :=
            h1.trans (mul_le_mul_of_nonneg_left hp_rs2_norm hB_Jrs0)
        _ = C_d * c ^ (-(2 / 3 : ℝ)) := by dsimp only [C_d]; ring
    have hQ_p_jc : JC 8 Y_Q (fun w => Q_rs (p_rs2, w)) B_Q := by
      have hcomp8 := JC.comp_pair (k := 8) hUd_YQ hUd_Q (g := Q_rs)
        (u := fun _ : ℝ => p_rs2) (w := fun t : ℝ => t) (b1 := 1) (b2 := 1)
        (by positivity) (hQ_rs_jc.mono_order (by norm_num)) contDiffOn_const contDiffOn_id
        (fun j hj1 _ t ht => by
          simp [iteratedFDerivWithin_eq_iteratedFDeriv hUd_YQ contDiffAt_const ht,
            iteratedFDeriv_const_of_ne (by omega : j ≠ 0) p_rs2])
        (fun j hj1 _ t ht => by change ‖iteratedFDerivWithin ℝ j (id : ℝ → ℝ) Y_Q t‖ ≤ 1; exact norm_iteratedFDerivWithin_id_le hUd_YQ hj1 ht)
        (fun _ ht => ⟨hp_rs2_mem, ht⟩)
      refine hcomp8.mono (le_of_eq ?_)
      have hmax1 : max (1 : ℝ) (max 1 1) = 1 := by norm_num
      rw [hmax1, one_pow, mul_one]
    have hQ_w_sym := win_Q_w_sym_of_jc hr2_pos (by positivity) hc100 hc_neg_half hlam_pos hlam_div_le hQ_p_jc
    have hlin_sym : FctSymClsOn (Icc 0 (fctUc c)) 8 10 ((C_d * C_w) * c ^ (-(4 / 3 : ℝ)))
        (fun u => ((deriv (fun w => J_rs (p_rs2, w)) 0 * w_fn u : ℝ) : ℂ)) := by
      let d_lin : ℝ := deriv (fun w => J_rs (p_rs2, w)) 0
      have hsc := hw_sym.const_mul hDu (d_lin : ℂ)
      have hle : ‖(d_lin : ℂ)‖ * (C_w * c ^ (-(2 / 3 : ℝ))) ≤ (C_d * C_w) * c ^ (-(4 / 3 : ℝ)) := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        have hcexp : c ^ (-(2 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) = c ^ (-(4 / 3 : ℝ)) := by
          rw [← Real.rpow_add hc0]; congr 1; norm_num
        calc |d_lin| * (C_w * c ^ (-(2 / 3 : ℝ)))
            ≤ (C_d * c ^ (-(2 / 3 : ℝ))) * (C_w * c ^ (-(2 / 3 : ℝ))) := mul_le_mul_of_nonneg_right hder_prs_bd (by positivity)
          _ = C_d * C_w * c ^ (-(4 / 3 : ℝ)) := by rw [← hcexp]; ring
      refine ((hsc.mono_B Icc_subset_Ici_self hle).mono_p Icc_subset_Ici_self (by positivity)
        (by norm_num)).congr hDu fun u _ => by dsimp only [d_lin]; push_cast; rfl
    have hquad_sym : FctSymClsOn (Icc 0 (fctUc c)) 8 10 ((2 ^ 8 * (2 ^ 8 * C_w * C_w) * C_Q_sym) * c ^ (-(4 / 3 : ℝ)))
        (fun u => ((w_fn u ^ 2 * Q_rs (p_rs2, w_fn u) : ℝ) : ℂ)) := by
      have hw2 := hw_sym.mul Icc_subset_Ici_self hDu hw_sym
      have hcexp : c ^ (-(2 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) = c ^ (-(4 / 3 : ℝ)) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      have hw2_bd : 2 ^ 8 * (C_w * c ^ (-(2 / 3 : ℝ))) * (C_w * c ^ (-(2 / 3 : ℝ))) =
          2 ^ 8 * C_w * C_w * c ^ (-(4 / 3 : ℝ)) := by rw [← hcexp]; ring
      have hmul := (hw2.mono_B Icc_subset_Ici_self hw2_bd.le).mul Icc_subset_Ici_self hDu hQ_w_sym
      refine ((hmul.mono_B Icc_subset_Ici_self (le_of_eq (by ring))).mono_p Icc_subset_Ici_self (by positivity)
        (by norm_num)).congr hDu fun u _ => by push_cast; ring
    have hC_le_tot : (C_d * C_w + 2 ^ 8 * (2 ^ 8 * C_w * C_w) * C_Q_sym) * c ^ (-(4 / 3 : ℝ)) ≤
        C_tot * c ^ (-(4 / 3 : ℝ)) := by
      have hJ0_le : C_J0 ≤ C_tot := le_max_left _ _
      exact mul_le_mul_of_nonneg_right hJ0_le (by positivity)
    refine ((hlin_sym.add hDu hquad_sym).mono_B Icc_subset_Ici_self
      ((le_of_eq (by ring)).trans hC_le_tot)).congr hDu fun u hu => ?_
    have hY_mem : fctInnerY c u ∈ Icc (0 : ℝ) 3.5 := fctInnerY_mem_35 hc1 hu
    have hscale := Jfun_scale_eq (c := c) hr_pos hSrs_Ω hSrs_ℓ hSrs_r h15rs hτ₁_pos hTmt rfl hSΩ hSℓ hSr
      (hp_mem_of hell2_nn hell2) hlam_pos hlam_16 hp_rs2_mem (hR_small_of hell2_nn hell2)
      (fctInnerY c u) hY_mem
    have hJrs_w_cd : ContDiffOn ℝ 3 (fun w => J_rs (p_rs2, w)) Yint :=
      (hJrs_jc.1.of_le (by norm_num)).comp (contDiffOn_const.prodMk contDiffOn_id) fun w hw => ⟨hp_rs2_mem, hw⟩
    have hwnn : 0 ≤ w_fn u := mul_nonneg hlam_pos.le hY_mem.1
    have hw_YQ : w_fn u ∈ Y_Q := ⟨by linarith only [hwnn], by
      have hy35 : fctInnerY c u ≤ 3.5 := hY_mem.2
      have hY0 : 0 ≤ fctInnerY c u := hY_mem.1
      dsimp only [w_fn]
      nlinarith only [hy35, hY0, hlam_16, hlam_pos]⟩
    have hw_int : w_fn u ∈ Yint := ⟨by linarith only [hw_YQ.1], by linarith only [hw_YQ.2]⟩
    have hhad := hadamard_second_order_win (hJrs_w_cd.sub contDiffOn_const)
      (by dsimp only [J_rs]; rw [hJrs_0 p_rs2 hp_rs2_mem, sub_self]) hw_int
    have hderiv_sub : deriv (fun w => J_rs (p_rs2, w) - 1) 0 = deriv (fun w => J_rs (p_rs2, w)) 0 := deriv_sub_const _
    have h2_sub : ∀ x : ℝ, iteratedDeriv 2 (fun t => J_rs (p_rs2, t) - 1) x = iteratedDeriv 2 (fun t => J_rs (p_rs2, t)) x := fun x => by
      have h1 : deriv (fun t => J_rs (p_rs2, t) - 1) = deriv (fun t => J_rs (p_rs2, t)) := funext fun t => deriv_sub_const _
      rw [iteratedDeriv_succ', h1, ← iteratedDeriv_succ']
    have hJrs_dd_eq : ∀ y ∈ Yint, iteratedDeriv 2 (fun t => J_rs (p_rs2, t)) y = Jrs_dd (p_rs2, y) := fun y hy => by
      have hev1 : deriv (fun t => J_rs (p_rs2, t)) =ᶠ[𝓝 y] fun t => Jrs_d (p_rs2, t) := by
        filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
        have hf1 := ((hJrs_jc.1.contDiffAt (hO_rs.mem_nhds
          (show ((p_rs2, t) : (ℝ × ℝ) × ℝ) ∈ fctOmegaRs ×ˢ Yint from ⟨hp_rs2_mem, ht⟩))).differentiableAt (by norm_num)).hasFDerivAt
        exact (hf1.comp_hasDerivAt t (by simpa using (hasDerivAt_const t p_rs2).prodMk (hasDerivAt_id t))).deriv
      have hdd : HasDerivAt (fun t => Jrs_d (p_rs2, t)) (Jrs_dd (p_rs2, y)) y := by
        have hf2 := ((hJrs_d14.1.contDiffAt (hO_rs.mem_nhds
          (show ((p_rs2, y) : (ℝ × ℝ) × ℝ) ∈ fctOmegaRs ×ˢ Yint from ⟨hp_rs2_mem, hy⟩))).differentiableAt (by norm_num)).hasFDerivAt
        exact hf2.comp_hasDerivAt y (by simpa using (hasDerivAt_const y p_rs2).prodMk (hasDerivAt_id y))
      rw [iteratedDeriv_succ, iteratedDeriv_one, hev1.deriv_eq, hdd.deriv]
    have hint_sub : ∫ σ in Icc (0 : ℝ) 1, (1 - σ) * iteratedDeriv 2 (fun t => J_rs (p_rs2, t) - 1) (σ * w_fn u) =
        Q_rs (p_rs2, w_fn u) := by
      refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
      rw [h2_sub (σ * w_fn u)]
      have hσw_int : σ * w_fn u ∈ Yint := by
        simpa [smul_eq_mul] using (convex_Ioo _ _).smul_mem_of_zero_mem zero_mem_Yint hw_int hσ
      rw [hJrs_dd_eq _ hσw_int]
    rw [hscale]
    change ((J_rs (p_rs2, w_fn u) - 1 : ℝ) : ℂ) = _
    have heq_sub : J_rs (p_rs2, w_fn u) - 1 =
        deriv (fun w => J_rs (p_rs2, w)) 0 * w_fn u + w_fn u ^ 2 * Q_rs (p_rs2, w_fn u) := by
      rw [hderiv_sub, hint_sub] at hhad; linarith only [hhad]
    rw [heq_sub]; push_cast; ring
  -- Part B: `J0 ell2 u - J0 ell1 u ∈ 𝒮^8_{10}(C_tot c^{-7/6} (ell2 - ell1))`
  have hJ0_diff : FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C_tot * c ^ (-(7 / 6 : ℝ)) * (ell2 - ell1))
      (fun u => ((Jfun S.V fctH (τ₁ ^ 2) ((ell2, 0, α), fctInnerY c u) - 1 : ℝ) : ℂ) -
        ((Jfun S.V fctH (τ₁ ^ 2) ((ell1, 0, α), fctInnerY c u) - 1 : ℝ) : ℂ)) := by
    let D_diff : ℝ → ℝ := fun w => D1_rs (p_rs2, w) - D1_rs (p_rs1, w)
    have hD1_dir : JC 12 (fctOmegaRs ×ˢ Y_Q) (fun q => fderiv ℝ D1_rs q (((1 : ℝ), (0 : ℝ)), (0 : ℝ))) (C_comp_Q * B_Jrs) := by
      have hn : ‖(((1 : ℝ), (0 : ℝ)), (0 : ℝ))‖ = 1 := by simp [Prod.norm_def]
      have h0 := (hD1_rs_jc.succ_fderiv hO_Q).clm_apply_const hUd_Q (((1 : ℝ), (0 : ℝ)), (0 : ℝ))
      rwa [hn, one_mul] at h0
    let v_p : ℝ × ℝ := (lam * (ell2 - ell1), 0)
    have hseg_rs : ∀ t ∈ Icc (0 : ℝ) 1, p_rs1 + t • v_p ∈ fctOmegaRs := fun t ht => by
      have hcv : Convex ℝ fctOmegaRs := (convex_Ioo (-(1 / 20 : ℝ)) (1 / 20)).prod (convex_Ioo (-1 : ℝ) 1)
      have hmem := hcv.add_smul_sub_mem hp_rs1_mem hp_rs2_mem ht
      rw [show p_rs2 - p_rs1 = v_p by
        exact Prod.ext (by dsimp only [p_rs1, p_rs2, v_p]; simp only [Prod.fst_sub]; ring)
          (by dsimp only [p_rs1, p_rs2, v_p]; simp only [Prod.snd_sub, sub_self])] at hmem
      exact hmem
    have hD_diff_jc : JC 8 Y_Q D_diff (B_D1 * (lam * (ell2 - ell1))) := by
      have hD_cd : ContDiffOn ℝ 8 D_diff Y_Q :=
        ((hD1_rs_jc.1.of_le (by norm_num)).comp (contDiffOn_const.prodMk contDiffOn_id)
          (fun w hw => ⟨hp_rs2_mem, hw⟩)).sub
        ((hD1_rs_jc.1.of_le (by norm_num)).comp (contDiffOn_const.prodMk contDiffOn_id)
          (fun w hw => ⟨hp_rs1_mem, hw⟩))
      refine ⟨hD_cd, fun k hk w hw => ?_⟩
      rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
        iteratedDerivWithin_of_isOpen isOpen_Ioo hw, Real.norm_eq_abs]
      have hcd1 : ContDiffAt ℝ k (fun s => D1_rs (p_rs2, s)) w :=
        ((hD1_rs_jc.1.comp (contDiffOn_const.prodMk contDiffOn_id) fun s hs => ⟨hp_rs2_mem, hs⟩).contDiffAt
          (isOpen_Ioo.mem_nhds hw)).of_le (by exact_mod_cast (by omega : k ≤ 13))
      have hcd2 : ContDiffAt ℝ k (fun s => D1_rs (p_rs1, s)) w :=
        ((hD1_rs_jc.1.comp (contDiffOn_const.prodMk contDiffOn_id) fun s hs => ⟨hp_rs1_mem, hs⟩).contDiffAt
          (isOpen_Ioo.mem_nhds hw)).of_le (by exact_mod_cast (by omega : k ≤ 13))
      change |iteratedDeriv k (fun s => D1_rs (p_rs2, s) - D1_rs (p_rs1, s)) w| ≤ _
      rw [show (fun s => D1_rs (p_rs2, s) - D1_rs (p_rs1, s)) =
          (fun s => D1_rs (p_rs2, s)) - (fun s => D1_rs (p_rs1, s)) from rfl, iteratedDeriv_sub hcd1 hcd2]
      let φ : ℝ → ℝ := fun t => iteratedDeriv k (fun s => D1_rs (p_rs1 + t • v_p, s)) w
      have hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt φ
          (iteratedDeriv k (fun s => fderiv ℝ D1_rs (p_rs1 + t • v_p, s) (v_p, 0)) w) (Icc 0 1) t := fun t ht => by
        have hD_k2 : ContDiffOn ℝ (k + 2) D1_rs (fctOmegaRs ×ˢ Y_Q) :=
          hD1_rs_jc.1.of_le (by exact_mod_cast (by omega : k + 2 ≤ 13))
        exact (hasDerivAt_iteratedDeriv_path hO_Q p_rs1 v_p w k D1_rs hD_k2 t ⟨hseg_rs t ht, hw⟩).hasDerivWithinAt
      have hbd : ∀ t ∈ Icc (0 : ℝ) 1,
          ‖iteratedDeriv k (fun s => fderiv ℝ D1_rs (p_rs1 + t • v_p, s) (v_p, 0)) w‖ ≤
            B_D1 * (lam * (ell2 - ell1)) := fun t ht => by
        have hp_t := hseg_rs t ht
        have hsm : (v_p, (0 : ℝ)) = (lam * (ell2 - ell1)) • (((1 : ℝ), (0 : ℝ)), (0 : ℝ)) := by
          ext <;> simp [v_p]
        have hfun : (fun s => fderiv ℝ D1_rs (p_rs1 + t • v_p, s) (v_p, 0)) =
            fun s => (lam * (ell2 - ell1)) * fderiv ℝ D1_rs (p_rs1 + t • v_p, s) (((1 : ℝ), (0 : ℝ)), (0 : ℝ)) := by
          ext s; rw [hsm, map_smul, smul_eq_mul]
        rw [hfun, iteratedDeriv_const_mul_field]
        have hslice := JC.comp_pair (k := 8) hUd_YQ hUd_Q
          (g := fun q => fderiv ℝ D1_rs q (((1 : ℝ), (0 : ℝ)), (0 : ℝ)))
          (u := fun _ : ℝ => p_rs1 + t • v_p) (w := fun s : ℝ => s) (b1 := 1) (b2 := 1)
          (by positivity) (hD1_dir.mono_order (by norm_num)) contDiffOn_const contDiffOn_id
          (fun j hj1 _ s hs => by
            simp [iteratedFDerivWithin_eq_iteratedFDeriv hUd_YQ contDiffAt_const hs,
              iteratedFDeriv_const_of_ne (by omega : j ≠ 0) (p_rs1 + t • v_p)])
          (fun j hj1 _ s hs => by
            change ‖iteratedFDerivWithin ℝ j (id : ℝ → ℝ) Y_Q s‖ ≤ 1
            exact norm_iteratedFDerivWithin_id_le hUd_YQ hj1 hs)
          (fun _ hs => ⟨hp_t, hs⟩)
        have hbd_k := hslice.2 k hk w hw
        rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
          iteratedDerivWithin_of_isOpen isOpen_Ioo hw, Real.norm_eq_abs] at hbd_k
        have hmax1 : max (1 : ℝ) (max 1 1) = 1 := by norm_num
        rw [hmax1, one_pow, mul_one] at hbd_k
        have hbd_k' : |iteratedDeriv k (fun s => fderiv ℝ D1_rs (p_rs1 + t • v_p, s) (((1 : ℝ), (0 : ℝ)), (0 : ℝ))) w| ≤ B_D1 :=
          hbd_k.trans_eq rfl
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg hlam_pos.le (sub_nonneg.mpr h12))]
        exact (mul_le_mul_of_nonneg_left hbd_k' (mul_nonneg hlam_pos.le (sub_nonneg.mpr h12))).trans_eq (mul_comm _ _)
      have hmv := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd
        (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
      have hφ1 : φ 1 = iteratedDeriv k (fun s => D1_rs (p_rs2, s)) w := by
        dsimp only [φ]; rw [one_smul, show p_rs1 + v_p = p_rs2 by ext <;> simp [p_rs1, p_rs2, v_p]; ring]
      have hφ0 : φ 0 = iteratedDeriv k (fun s => D1_rs (p_rs1, s)) w := by
        dsimp only [φ]; rw [zero_smul, add_zero]
      simpa [Real.norm_eq_abs, hφ1, hφ0, sub_zero, mul_one] using hmv
    have hD_w_sym := win_Q_w_sym_of_jc hr2_pos (mul_nonneg (by positivity) (mul_nonneg hlam_pos.le (sub_nonneg.mpr h12)))
      hc100 hc_neg_half hlam_pos hlam_div_le hD_diff_jc
    have hprod := hw_sym.mul Icc_subset_Ici_self hDu hD_w_sym
    have hbd_eq : 2 ^ 8 * (C_w * c ^ (-(2 / 3 : ℝ))) *
        (100 ^ 8 * ((Nat.factorial 8 : ℝ) * (B_D1 * (lam * (ell2 - ell1))))) ≤
        C_tot * c ^ (-(7 / 6 : ℝ)) * (ell2 - ell1) := by
      have hc_eq : c ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 2 : ℝ)) = c ^ (-(7 / 6 : ℝ)) := by
        rw [← Real.rpow_add hc0]; norm_num
      have hlam_nn : 0 ≤ lam := hlam_pos.le
      have hell_nn : 0 ≤ ell2 - ell1 := sub_nonneg.mpr h12
      calc 2 ^ 8 * (C_w * c ^ (-(2 / 3 : ℝ))) * (100 ^ 8 * ((Nat.factorial 8 : ℝ) * (B_D1 * (lam * (ell2 - ell1)))))
          ≤ 2 ^ 8 * (C_w * c ^ (-(2 / 3 : ℝ))) *
              (100 ^ 8 * ((Nat.factorial 8 : ℝ) * (B_D1 * ((1 / r_star ^ 2 * c ^ (-(1 / 2 : ℝ))) * (ell2 - ell1))))) := by
            gcongr
        _ = C_J0_d * (c ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 2 : ℝ))) * (ell2 - ell1) := by
            dsimp only [C_J0_d, C_D1_sym]; ring
        _ = C_J0_d * c ^ (-(7 / 6 : ℝ)) * (ell2 - ell1) := by rw [hc_eq]
        _ ≤ C_tot * c ^ (-(7 / 6 : ℝ)) * (ell2 - ell1) := by
            have : C_J0_d ≤ C_tot := le_max_right _ _
            gcongr
    refine ((hprod.mono_B Icc_subset_Ici_self hbd_eq).mono_p Icc_subset_Ici_self (by positivity)
      (by norm_num : (2 : ℝ) + 0 ≤ 10)).congr hDu fun u hu => ?_
    have hY_mem : fctInnerY c u ∈ Icc (0 : ℝ) 3.5 := fctInnerY_mem_35 hc1 hu
    have hscale2 := Jfun_scale_eq (c := c) hr_pos hSrs_Ω hSrs_ℓ hSrs_r h15rs hτ₁_pos hTmt rfl hSΩ hSℓ hSr
      (hp_mem_of hell2_nn hell2) hlam_pos hlam_16 hp_rs2_mem (hR_small_of hell2_nn hell2)
      (fctInnerY c u) hY_mem
    have hscale1 := Jfun_scale_eq (c := c) hr_pos hSrs_Ω hSrs_ℓ hSrs_r h15rs hτ₁_pos hTmt rfl hSΩ hSℓ hSr
      (hp_mem_of hell1 (h12.trans hell2)) hlam_pos hlam_16 hp_rs1_mem (hR_small_of hell1 (h12.trans hell2))
      (fctInnerY c u) hY_mem
    have hwnn : 0 ≤ w_fn u := mul_nonneg hlam_pos.le hY_mem.1
    have hw_YQ : w_fn u ∈ Y_Q := ⟨by linarith only [hwnn], by
      have hy35 : fctInnerY c u ≤ 3.5 := hY_mem.2
      have hY0 : 0 ≤ fctInnerY c u := hY_mem.1
      dsimp only [w_fn]
      nlinarith only [hy35, hY0, hlam_16, hlam_pos]⟩
    have hw_int : w_fn u ∈ Yint := ⟨by linarith only [hw_YQ.1], by linarith only [hw_YQ.2]⟩
    have hJrs_w : ∀ {p : ℝ × ℝ}, p ∈ fctOmegaRs → ContDiffOn ℝ 2 (fun w => J_rs (p, w)) Yint := fun {p} hp =>
      (hJrs_jc.1.of_le (by norm_num)).comp (contDiffOn_const.prodMk contDiffOn_id) fun w hw => ⟨hp, hw⟩
    have hhad2 := hadamard_first_order ((hJrs_w hp_rs2_mem).sub contDiffOn_const)
      (by dsimp only [J_rs]; rw [hJrs_0 p_rs2 hp_rs2_mem, sub_self]) hw_int
    have hhad1 := hadamard_first_order ((hJrs_w hp_rs1_mem).sub contDiffOn_const)
      (by dsimp only [J_rs]; rw [hJrs_0 p_rs1 hp_rs1_mem, sub_self]) hw_int
    have hder_eq : ∀ {p : ℝ × ℝ}, p ∈ fctOmegaRs →
        ∫ σ in Icc (0 : ℝ) 1, deriv (fun w => J_rs (p, w) - 1) (σ * w_fn u) = D1_rs (p, w_fn u) := fun {p} hp => by
      refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
      rw [deriv_sub_const]
      have hσw_int : σ * w_fn u ∈ Yint := by
        simpa [smul_eq_mul] using (convex_Ioo _ _).smul_mem_of_zero_mem zero_mem_Yint hw_int hσ
      have hf1 := ((hJrs_jc.1.contDiffAt (hO_rs.mem_nhds
        (show ((p, σ * w_fn u) : (ℝ × ℝ) × ℝ) ∈ fctOmegaRs ×ˢ Yint from ⟨hp, hσw_int⟩))).differentiableAt (by norm_num)).hasFDerivAt
      exact (hf1.comp_hasDerivAt (σ * w_fn u)
        (by simpa using (hasDerivAt_const (σ * w_fn u) p).prodMk (hasDerivAt_id (σ * w_fn u)))).deriv
    rw [hscale2, hscale1]
    change ((J_rs (p_rs2, w_fn u) - 1 : ℝ) : ℂ) - ((J_rs (p_rs1, w_fn u) - 1 : ℝ) : ℂ) = _
    rw [hhad2, hhad1, hder_eq hp_rs2_mem, hder_eq hp_rs1_mem]
    dsimp only [D_diff]; push_cast; ring
  exact ⟨hJ0_ell2, hJ0_diff⟩

/-- info: 'FormalResearch.SignUncertainty.win_dJ_comp_Y_sym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_dJ_comp_Y_sym

/-- info: 'FormalResearch.SignUncertainty.win_Q_w_sym_of_jc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_Q_w_sym_of_jc

/-- info: 'FormalResearch.SignUncertainty.win_J0_sub_one_and_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_J0_sub_one_and_diff

end FormalResearch.SignUncertainty
