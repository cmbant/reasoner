/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpWinJ1
public import FormalResearch.SignUncertainty.FctInnerVJets

/-!
# Window `fctS` parameter shift and `T_L - T_{L_1}` composition helpers (`fct:warp-win`)

Leaf helper module for `FctWarpWinInner.lean`:
* `win_fctS_shift`: `‖fctS b κ - fctS a κ‖ ≤ C B |b - a|` for `κ ∈ 𝒮^8_p(B)` (`0 ≤ p ≤ 13`, `|a|, |b| ≤ M`).
* `win_g_Y_sym_0`: `JC 8 [0, 3.6] g B_g → FctSymClsOn [0, U_c] 8 0 (C B_g) (fun u => g (Y(u)))`.
* `win_V_diff_sym`: `V_{L2}(Y(u)) - V_{L1}(Y(u)) ∈ 𝒮^8_0(C (L2 - L1))` and `T_{L2}(u) - T_{L1}(u) ∈ 𝒮^8_1(C c^{-1/3} (L2 - L1))`.
* `win_comp_T_diff_jc`: `g(T_2 u) - g(T_1 u) ∈ 𝒮^8_1(C C_{g'} c^{-1/3} D)` for smooth `g` on `(-R, R)`.

Class: proved.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped Real ContDiff BigOperators
open FormalResearch.CohnElkies FormalResearch.Special FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD FormalResearch.SignUncertainty.FctMoment
open FormalResearch.SignUncertainty.FctSymA

namespace FormalResearch.SignUncertainty

/-! ### 1. Parameter shift of `fctS` (`win_fctS_shift`) -/

private lemma win_fctSEps_hasDerivAt {ε p B : ℝ} (hε : 0 < ε) (hp0 : 0 ≤ p)
    {κ : ℝ → ℂ} (hκ : FctSymCls 8 p B κ) (w : ℝ) :
    HasDerivAt (fun w' : ℝ => fctSEps w' ε κ)
      (-Complex.I * fctSEps w ε (fun u => (u : ℂ) * κ u)) w := by
  have hB0 : 0 ≤ B := by
    have h0 := hκ.2 0 (by norm_num) 0 le_rfl
    rw [iteratedDerivWithin_zero, Nat.cast_zero, sub_zero, add_zero, Real.one_rpow, mul_one] at h0
    exact (norm_nonneg (κ 0)).trans h0
  set F : ℝ → ℝ → ℂ := fun w' u => fctRho u * Complex.exp (fctW w' ε u) * κ u with hF
  set F' : ℝ → ℝ → ℂ := fun w' u =>
    fctRho u * (Complex.exp (fctW w' ε u) * (-(Complex.I * (u : ℂ)))) * κ u with hF'
  set μ : Measure ℝ := volume.restrict (Ioi 0)
  have hκ_bd : ∀ u : ℝ, 0 < u → ‖κ u‖ ≤ B * (1 + u) ^ p := fun u hu => by
    have h0 := hκ.2 0 (by norm_num) u hu.le
    rw [iteratedDerivWithin_zero, Nat.cast_zero, sub_zero] at h0
    exact h0
  have hint_fn : ∀ (a : ℝ), -1 < a → IntegrableOn (fun x : ℝ => x ^ a * Real.exp (-ε * x ^ 2)) (Ioi 0) :=
    fun a ha => integrableOn_rpow_mul_exp_neg_mul_sq hε ha
  let hdom_fn : ℝ → ℝ := fun x =>
    B * 2 ^ p * (x ^ (-(1 / 2 : ℝ)) * Real.exp (-ε * x ^ 2) + x ^ (p - 1 / 2) * Real.exp (-ε * x ^ 2))
  let hdom_u_fn : ℝ → ℝ := fun x =>
    B * 2 ^ p * (x ^ (1 / 2 : ℝ) * Real.exp (-ε * x ^ 2) + x ^ (p + 1 / 2) * Real.exp (-ε * x ^ 2))
  have h1p_le : ∀ u : ℝ, 0 < u → (1 + u) ^ p ≤ 2 ^ p * (1 + u ^ p) := fun u hu => by
    by_cases hu1 : u ≤ 1
    · calc (1 + u) ^ p ≤ (1 + 1) ^ p := Real.rpow_le_rpow (by positivity) (by linarith) hp0
        _ = 2 ^ p * 1 := by norm_num
        _ ≤ 2 ^ p * (1 + u ^ p) := by gcongr; exact le_add_of_nonneg_right (by positivity)
    · have hu1' : 1 ≤ u := le_of_not_ge hu1
      calc (1 + u) ^ p ≤ (u + u) ^ p := Real.rpow_le_rpow (by positivity) (by linarith) hp0
        _ = 2 ^ p * u ^ p := by rw [← two_mul, Real.mul_rpow (by norm_num) hu.le]
        _ ≤ 2 ^ p * (1 + u ^ p) := by gcongr; linarith
  have hdom0 : Integrable hdom_fn μ := by
    dsimp only [hdom_fn]
    have hi1 := (hint_fn (-(1 / 2 : ℝ)) (by norm_num)).add (hint_fn (p - 1 / 2) (by linarith))
    convert hi1.const_mul (B * 2 ^ p) using 1
  have hdom1 : Integrable hdom_u_fn μ := by
    dsimp only [hdom_u_fn]
    have hi1 := (hint_fn (1 / 2 : ℝ) (by norm_num)).add (hint_fn (p + 1 / 2) (by linarith))
    convert hi1.const_mul (B * 2 ^ p) using 1
  have hcontF : ∀ w' : ℝ, ContinuousOn (F w') (Ioi 0) := fun w' =>
    (((contDiffOn_fctRho 0).continuousOn).mul (continuous_fctW w' ε).cexp.continuousOn).mul
      (hκ.1.continuousOn.mono Ioi_subset_Ici_self)
  have hcontF' : ∀ w' : ℝ, ContinuousOn (F' w') (Ioi 0) := fun w' =>
    (((contDiffOn_fctRho 0).continuousOn).mul
      (((continuous_fctW w' ε).cexp).mul (by fun_prop : Continuous fun u : ℝ => -(Complex.I * (u : ℂ)))).continuousOn).mul
      (hκ.1.continuousOn.mono Ioi_subset_Ici_self)
  have hmeasF : ∀ w' : ℝ, AEStronglyMeasurable (F w') μ := fun w' => (hcontF w').aestronglyMeasurable measurableSet_Ioi
  have hmeasF' : ∀ w' : ℝ, AEStronglyMeasurable (F' w') μ := fun w' => (hcontF' w').aestronglyMeasurable measurableSet_Ioi
  have hnormF_le : ∀ w' u : ℝ, 0 < u → ‖F w' u‖ ≤ hdom_fn u := fun w' u hu => by
    dsimp only [F, hdom_fn]
    rw [norm_mul, norm_mul, norm_fctRho hu, norm_exp_fctW]
    have hmul_e : u ^ (-(1 / 2 : ℝ)) * Real.exp (-(ε * u ^ 2)) * ‖κ u‖ ≤
        u ^ (-(1 / 2 : ℝ)) * Real.exp (-ε * u ^ 2) * (B * (2 ^ p * (1 + u ^ p))) := by
      rw [show -(ε * u ^ 2) = -ε * u ^ 2 by ring]
      exact mul_le_mul_of_nonneg_left ((hκ_bd u hu).trans (mul_le_mul_of_nonneg_left (h1p_le u hu) hB0)) (by positivity)
    refine hmul_e.trans_eq ?_
    have hp_eq : u ^ (-(1 / 2 : ℝ)) * u ^ p = u ^ (p - 1 / 2) := by
      rw [← Real.rpow_add hu]; congr 1; ring
    calc u ^ (-(1 / 2 : ℝ)) * Real.exp (-ε * u ^ 2) * (B * (2 ^ p * (1 + u ^ p)))
        = B * 2 ^ p * (u ^ (-(1 / 2 : ℝ)) * Real.exp (-ε * u ^ 2) +
            (u ^ (-(1 / 2 : ℝ)) * u ^ p) * Real.exp (-ε * u ^ 2)) := by ring
      _ = _ := by rw [hp_eq]
  have hnormF'_le : ∀ w' u : ℝ, 0 < u → ‖F' w' u‖ ≤ hdom_u_fn u := fun w' u hu => by
    dsimp only [F', hdom_u_fn]
    rw [norm_mul, norm_mul, norm_mul, norm_fctRho hu, norm_exp_fctW, norm_neg, norm_mul,
      Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hu.le]
    have hmul_e : u ^ (-(1 / 2 : ℝ)) * (Real.exp (-(ε * u ^ 2)) * u) * ‖κ u‖ ≤
        u ^ (-(1 / 2 : ℝ)) * (Real.exp (-ε * u ^ 2) * u) * (B * (2 ^ p * (1 + u ^ p))) := by
      rw [show -(ε * u ^ 2) = -ε * u ^ 2 by ring]
      exact mul_le_mul_of_nonneg_left ((hκ_bd u hu).trans (mul_le_mul_of_nonneg_left (h1p_le u hu) hB0)) (by positivity)
    refine hmul_e.trans_eq ?_
    have hu12 : u ^ (-(1 / 2 : ℝ)) * u = u ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add_one hu.ne']; congr 1; norm_num
    have hup12' : u ^ (1 / 2 : ℝ) * u ^ p = u ^ (p + 1 / 2) := by
      rw [← Real.rpow_add hu]; congr 1; ring
    calc u ^ (-(1 / 2 : ℝ)) * (Real.exp (-ε * u ^ 2) * u) * (B * (2 ^ p * (1 + u ^ p)))
        = B * 2 ^ p * ((u ^ (-(1 / 2 : ℝ)) * u) * Real.exp (-ε * u ^ 2) +
            (u ^ (-(1 / 2 : ℝ)) * u) * u ^ p * Real.exp (-ε * u ^ 2)) := by ring
      _ = _ := by rw [hu12, hup12']
  have hFint : Integrable (F w) μ :=
    Integrable.mono' hdom0 (hmeasF w) ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun u hu => hnormF_le w u hu))
  obtain ⟨_, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := F') (x₀ := w)
    (bound := hdom_u_fn) (s := univ) univ_mem (Eventually.of_forall hmeasF) hFint (hmeasF' w)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu w' _ => hnormF'_le w' u hu))
    hdom1
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu w' _ =>
      (((hasDerivAt_fctW_û w' ε u).cexp).const_mul (fctRho u)).mul_const (κ u)))
  have e1 : (fun w' : ℝ => fctSEps w' ε κ) = fun w' =>
      Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) * ∫ u, F w' u ∂μ := funext fun w' => fctSEps_eq w' ε κ
  have e2 : -Complex.I * fctSEps w ε (fun u => (u : ℂ) * κ u) =
      Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) * ∫ u, F' w u ∂μ := by
    rw [fctSEps_eq]
    have hF'eq : ∀ u : ℝ, F' w u = -Complex.I * (fctRho u * Complex.exp (fctW w ε u) * ((u : ℂ) * κ u)) := by
      intro u; dsimp only [F']; ring
    simp_rw [hF'eq, integral_const_mul]; ring
  rw [e1, e2]
  exact hd.const_mul _

/-- Uniform shift bound for `fctS`: `‖fctS b κ - fctS a κ‖ ≤ C * B * |b - a|`
when `|a|, |b| ≤ M` (`M > 0`), `κ ∈ 𝒮^8_p(B)`, `0 ≤ p ≤ 22`. -/
theorem win_fctS_shift {M p : ℝ} (hM : 0 < M) (hp0 : 0 ≤ p) (hp22 : p ≤ 22) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b B : ℝ} {κ : ℝ → ℂ},
      |a| ≤ M → |b| ≤ M → 0 ≤ B → FctSymCls 8 p B κ →
      ‖fctS b κ - fctS a κ‖ ≤ C * B * |b - a| := by
  obtain ⟨C_u, hCu0, hCu⟩ := FctSymA.fctInnerSymbolsA_unif M 8 (p + 1) hM (by norm_num) (by push_cast; linarith)
  obtain ⟨_, _, hLim⟩ := FctSymA.fctInnerSymbolsA M 8 p hM (by norm_num) (by push_cast; linarith)
  refine ⟨C_u * 2 ^ 8, by positivity, fun {a b B κ} ha hb hB0 hκ => ?_⟩
  have hDi := uniqueDiffOn_Ici (0 : ℝ)
  have huκ : FctSymCls 8 (p + 1) (2 ^ 8 * B) (fun u => (u : ℂ) * κ u) :=
    (((id_symCls 8).mul Subset.rfl hDi hκ).mono_B Subset.rfl (le_of_eq (by ring))).mono_p
      Subset.rfl (by linarith) (le_of_eq (add_comm 1 p))
  have h_eps : ∀ ε ∈ Ioo (0 : ℝ) 1, ‖fctSEps b ε κ - fctSEps a ε κ‖ ≤ C_u * 2 ^ 8 * B * |b - a| := by
    intro ε hε
    have hder : ∀ w ∈ uIcc a b, HasDerivWithinAt (fun w' => fctSEps w' ε κ)
        (-Complex.I * fctSEps w ε (fun u => (u : ℂ) * κ u)) (uIcc a b) w := fun w _ =>
      (win_fctSEps_hasDerivAt hε.1 hp0 hκ w).hasDerivWithinAt
    have hbd : ∀ w ∈ uIcc a b,
        ‖-Complex.I * fctSEps w ε (fun u => (u : ℂ) * κ u)‖ ≤ C_u * (2 ^ 8 * B) := fun w hw => by
      have hwM : |w| ≤ M := by
        rcases mem_uIcc.mp hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [abs_le] <;>
          constructor <;> linarith only [h1, h2, abs_le.mp ha, abs_le.mp hb]
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
      exact hCu w (2 ^ 8 * B) _ hwM (by positivity) huκ ε hε
    have hmv := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd
      left_mem_uIcc right_mem_uIcc
    rw [Real.norm_eq_abs] at hmv
    calc ‖fctSEps b ε κ - fctSEps a ε κ‖
        ≤ C_u * (2 ^ 8 * B) * |b - a| := hmv
      _ = C_u * 2 ^ 8 * B * |b - a| := by ring
  obtain ⟨La, hLa⟩ := (hLim a B κ ha hB0 hκ).1
  obtain ⟨Lb, hLb⟩ := (hLim b B κ hb hB0 hκ).1
  have hta : Tendsto (fun ε : ℝ => fctSEps a ε κ) (𝓝[>] 0) (𝓝 (fctS a κ)) := by
    rw [hLa.fctS_eq]; exact hLa
  have htb : Tendsto (fun ε : ℝ => fctSEps b ε κ) (𝓝[>] 0) (𝓝 (fctS b κ)) := by
    rw [hLb.fctS_eq]; exact hLb
  have htn : Tendsto (fun ε : ℝ => ‖fctSEps b ε κ - fctSEps a ε κ‖) (𝓝[>] 0) (𝓝 ‖fctS b κ - fctS a κ‖) :=
    (htb.sub hta).norm
  have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT zero_lt_one
  exact le_of_tendsto htn (mem_of_superset hmem h_eps)

/-! ### 2. Weight-0 composition with `fctInnerY c` (`win_g_Y_sym_0`) -/

private lemma win_fctInnerY_deriv_bounds {c : ℝ} (hc : 1 ≤ c) :
    ContDiffOn ℝ 8 (fctInnerY c) (Icc 0 (fctUc c)) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ 8 → ∀ u ∈ Icc 0 (fctUc c),
      |iteratedDerivWithin j (fctInnerY c) (Icc 0 (fctUc c)) u| ≤
        8 * c ^ (-(1 / 12 : ℝ)) * (1 + u) ^ ((1 : ℝ) - j)) := by
  have hc0 : 0 < c := by linarith
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu : UniqueDiffOn ℝ (Icc 0 (fctUc c)) := uniqueDiffOn_Icc hUc0
  have hcd : ContDiff ℝ 8 (fctInnerY c) := by unfold fctInnerY; fun_prop
  refine ⟨hcd.contDiffOn, fun j hj1 hj8 u hu => ?_⟩
  set κ : ℝ := 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ))
  have hκ0 : 0 ≤ κ := by positivity
  have hκ_le : κ ≤ c ^ (-(1 / 6 : ℝ)) := by
    have h2 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    calc κ = (2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) := rfl
      _ ≤ 1 * c ^ (-(1 / 6 : ℝ)) := by gcongr
      _ = c ^ (-(1 / 6 : ℝ)) := one_mul _
  have h1u0 : 0 < 1 + u := by linarith [hu.1]
  have h1u_le : 1 + u ≤ 4 * c ^ ((1 : ℝ) / 12) := by
    have := one_add_fctUc_le hc; linarith [hu.2]
  have hit : iteratedDerivWithin j (fctInnerY c) (Icc 0 (fctUc c)) u = iteratedDeriv j (fctInnerY c) u :=
    iteratedDerivWithin_eq_iteratedDeriv hDu (hcd.contDiffAt.of_le (by exact_mod_cast hj8)) hu
  rw [hit]
  have hYeq : fctInnerY c = fun x => κ * x ^ 2 := rfl
  rcases (by omega : j = 1 ∨ j = 2 ∨ 3 ≤ j) with rfl | rfl | hj3
  · have hd1 : iteratedDeriv 1 (fun x => κ * x ^ 2) u = 2 * κ * u := by
      rw [iteratedDeriv_one, ((hasDerivAt_pow 2 u).const_mul κ).deriv]; ring
    rw [hYeq, hd1, abs_mul, abs_mul, abs_of_pos zero_lt_two, abs_of_nonneg hκ0, abs_of_nonneg hu.1]
    have h_1j : (1 + u) ^ ((1 : ℝ) - (1 : ℕ)) = 1 := by norm_num
    rw [h_1j, mul_one]
    have hu4 : u ≤ 4 * c ^ ((1 : ℝ) / 12) := by linarith [hu.1]
    have hu0 : 0 ≤ u := hu.1
    calc 2 * κ * u ≤ 2 * c ^ (-(1 / 6 : ℝ)) * (4 * c ^ ((1 : ℝ) / 12)) := by gcongr
      _ = 8 * (c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 12)) := by ring
      _ = 8 * c ^ (-(1 / 12 : ℝ)) := by rw [← Real.rpow_add hc0]; congr 1; norm_num
  · have hd2 : iteratedDeriv 2 (fun x => κ * x ^ 2) u = 2 * κ := by
      have hfn : (iteratedDeriv 1 fun x => κ * x ^ 2) = fun x => 2 * κ * x := by
        ext x; rw [iteratedDeriv_one, ((hasDerivAt_pow 2 x).const_mul κ).deriv]; ring
      rw [iteratedDeriv_succ, hfn]
      simpa only [id_eq, mul_one] using ((hasDerivAt_id u).const_mul (2 * κ)).deriv
    rw [hYeq, hd2, abs_mul, abs_of_pos zero_lt_two, abs_of_nonneg hκ0]
    have h_1j : (1 + u) ^ ((1 : ℝ) - (2 : ℕ)) = (1 + u)⁻¹ := by
      rw [show (1 : ℝ) - ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    rw [h_1j]
    have h1 : 2 * κ * (1 + u) ≤ 8 * c ^ (-(1 / 12 : ℝ)) := by
      calc 2 * κ * (1 + u) ≤ 2 * c ^ (-(1 / 6 : ℝ)) * (4 * c ^ ((1 : ℝ) / 12)) := by gcongr
        _ = 8 * (c ^ (-(1 / 6 : ℝ)) * c ^ ((1 : ℝ) / 12)) := by ring
        _ = 8 * c ^ (-(1 / 12 : ℝ)) := by rw [← Real.rpow_add hc0]; congr 1; norm_num
    calc 2 * κ = (2 * κ * (1 + u)) * (1 + u)⁻¹ := by field_simp [h1u0.ne']
      _ ≤ 8 * c ^ (-(1 / 12 : ℝ)) * (1 + u)⁻¹ := by gcongr
  · have hd3 : iteratedDeriv j (fun x => κ * x ^ 2) u = 0 := by
      have hfn2 : (iteratedDeriv 2 fun x => κ * x ^ 2) = fun _ => 2 * κ := by
        ext x
        have hfn : (iteratedDeriv 1 fun x => κ * x ^ 2) = fun x => 2 * κ * x := by
          ext z; rw [iteratedDeriv_one, ((hasDerivAt_pow 2 z).const_mul κ).deriv]; ring
        rw [iteratedDeriv_succ, hfn]
        simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul (2 * κ)).deriv
      have hsplit : j = (j - 2) + 2 := by omega
      rw [hsplit, ← iteratedDeriv_iteratedDeriv_eq, hfn2, iteratedDeriv_const,
        show (if j - 2 = 0 then 2 * κ else 0) = 0 by simp only [show j - 2 ≠ 0 by omega, ↓reduceIte]]
    rw [hYeq, hd3, abs_zero]
    positivity

lemma win_g_Y_sym_0 {c B_g : ℝ} (hc1 : 1 ≤ c) (hBg0 : 0 ≤ B_g)
    {g : ℝ → ℝ} (hg : JC 8 (Icc (0 : ℝ) 3.5) g B_g) :
    FctSymClsOn (Icc 0 (fctUc c)) 8 0 ((Nat.factorial 8 : ℝ) * 32 ^ 8 * B_g)
      (fun u => ((g (fctInnerY c u) : ℝ) : ℂ)) := by
  have hc0 : 0 < c := by linarith only [hc1]
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  obtain ⟨hYcd, hYd⟩ := win_fctInnerY_deriv_bounds hc1
  have hDu35 : UniqueDiffOn ℝ (Icc (0 : ℝ) 3.5) := uniqueDiffOn_Icc (by norm_num)
  have hg_cd : ContDiffOn ℝ 8 (fun y : ℝ => ((g y : ℝ) : ℂ)) (Icc (0 : ℝ) 3.5) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hg.1
  have hg_bd : ∀ i ≤ 8, ∀ y ∈ Icc (0 : ℝ) 3.5,
      ‖iteratedDerivWithin i (fun y : ℝ => ((g y : ℝ) : ℂ)) (Icc (0 : ℝ) 3.5) y‖ ≤ B_g := fun i hi y hy => by
    rw [iteratedDerivWithin_ofReal_cast hDu35 hg.1 hi y hy, Complex.norm_real]
    have hb := hg.2 i hi y hy
    rwa [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin] at hb
  have hmaps : MapsTo (fctInnerY c) (Icc 0 (fctUc c)) (Icc (0 : ℝ) 3.5) := fun u hu =>
    fctInnerY_mem_35 hc1 hu
  have hBfM : 8 * c ^ (-(1 / 12 : ℝ)) * (1 + fctUc c) ≤ 32 := by
    have h1 := one_add_fctUc_le hc1
    have hc0_eq : c ^ (-(1 / 12 : ℝ)) * c ^ ((1 : ℝ) / 12) = 1 := by
      rw [← Real.rpow_add hc0]; norm_num
    calc 8 * c ^ (-(1 / 12 : ℝ)) * (1 + fctUc c)
        ≤ 8 * c ^ (-(1 / 12 : ℝ)) * (4 * c ^ ((1 : ℝ) / 12)) := by gcongr
      _ = 32 * (c ^ (-(1 / 12 : ℝ)) * c ^ ((1 : ℝ) / 12)) := by ring
      _ = 32 := by rw [hc0_eq, mul_one]
  have hsym := FctSymClsOn.comp_T_zero hUc0 (by norm_num : (1 : ℝ) ≤ 32) hDu35 hg_cd
    hBg0 hg_bd hYcd hmaps (by positivity) hBfM hYd
  exact hsym.mono_B Icc_subset_Ici_self (le_of_eq (by ring))

/-! ### 3. `V_2(Y(u)) - V_1(Y(u))` and `T_2(u) - T_1(u)` (`win_V_diff_sym`) -/

theorem win_V_diff_sym {K4 Sw_ell : ℝ} (hK4 : 1 ≤ K4) (_hSw : 1 ≤ Sw_ell) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 32 ^ 4 ≤ c₀ ∧ ∀ {ε c α L_lo L_hi : ℝ},
      (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      c ^ (-(1 / 4 : ℝ)) ≤ pbTauLim → K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 →
      |α| ≤ c ^ (-(1 / 2 : ℝ)) →
      0 ≤ concreteEll1 ε c L_lo → L_lo ≤ L_hi →
      concreteEll1 ε c L_hi ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) →
      let S := concreteBoxS K4 ε c
      let ell1 := concreteEll1 ε c L_lo
      let ell2 := concreteEll1 ε c L_hi
      let V1 : ℝ → ℝ := fun Y => S.V ((ell1, 1, α), Y)
      let V2 : ℝ → ℝ := fun Y => S.V ((ell2, 1, α), Y)
      FctSymClsOn (Icc 0 (fctUc c)) 8 0 (C * (L_hi - L_lo))
        (fun u => ((V2 (fctInnerY c u) - V1 (fctInnerY c u) : ℝ) : ℂ)) ∧
      FctSymClsOn (Icc 0 (fctUc c)) 8 1 (C * c ^ (-(1 / 3 : ℝ)) * (L_hi - L_lo))
        (fun u => ((fctInnerT c V2 u - fctInnerT c V1 u : ℝ) : ℂ)) := by
  let C_Y : ℝ := (Nat.factorial 8 : ℝ) * 32 ^ 8 * ((Nat.factorial 8 : ℝ) * pbcV * pbC0)
  let C_T : ℝ := 2 ^ 8 * ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * C_Y)
  let C_tot : ℝ := max C_Y C_T
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      (32 : ℝ) ^ 4 ≤ c ∧ (160000 : ℝ) ≤ c ∧ Sw_ell * c ^ (-(1 / 6 : ℝ)) < 27 / 10 := by
    refine Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _) ?_)
    have h0 : Tendsto (fun c : ℝ => Sw_ell * c ^ (-(1 / 6 : ℝ))) atTop (𝓝 0) := by
      simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).const_mul Sw_ell
    exact h0.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 27 / 10))
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  refine ⟨C_tot, max (32 ^ 4) c₀, by have := pbcV_nonneg; have := pbC0_nonneg; positivity, le_max_left _ _,
    fun {ε c α L_lo L_hi} hε hc hτ_lim hK4t hα hell1 h12 hell2 => ?_⟩
  obtain ⟨hc32, _, hSw_lt⟩ := hc₀ c ((le_max_right _ _).trans hc)
  have hc100 : (100 : ℝ) ≤ c := le_trans (by norm_num) hc32
  have hc0 : 0 < c := by linarith only [hc100]
  have hc1 : 1 ≤ c := by linarith only [hc100]
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  have hvalid : concreteBoxValid K4 ε c := ⟨hK4, hε, hc0, hτ_lim, hK4t⟩
  set S := concreteBoxS K4 ε c
  obtain ⟨_, _, _, hSΩ, _, _, hSε, hcV_eq, _, _⟩ := concreteBox_spec hvalid
  set τ₁ : ℝ := c ^ (-(1 / 4 : ℝ))
  have hτ₁_pos : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hτ₁_sq : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
    dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hα_om : |α| < 2 * τ₁ ^ 2 := by
    rw [hτ₁_sq]; linarith only [hα, Real.rpow_pos_of_pos hc0 (-(1 / 2 : ℝ))]
  set ell1 := concreteEll1 ε c L_lo
  set ell2 := concreteEll1 ε c L_hi
  have hell_le : ell1 ≤ ell2 := by
    dsimp only [ell1, ell2, concreteEll1]; gcongr
  have hell_diff : ell2 - ell1 = c ^ (1 / 2 : ℝ) * (L_hi - L_lo) := by
    dsimp only [ell1, ell2, concreteEll1]
    have hdenom : (c ^ (-(1 / 4 : ℝ))) ^ 2 = (c ^ (1 / 2 : ℝ))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le, ← Real.rpow_neg hc0.le]; congr 1; norm_num
    rw [hdenom, div_inv_eq_mul, div_inv_eq_mul]; ring
  have hO_S : IsOpen (S.Ω ×ˢ Yint) := S.hΩ.prod isOpen_Ioo
  have hV0_jc : JC 16 (S.Ω ×ˢ Yint) (fun y => S.V y - dStar⁻¹) (pbcV * pbC0 * c ^ (-(1 / 2 : ℝ))) := by
    have h1 := S.out.2.2.2.2.2.2.2.2.2.1
    rw [hcV_eq, hSε, hτ₁_sq] at h1
    exact h1.mono (le_of_eq (by ring))
  have hV_cd : ContDiffOn ℝ 16 S.V (S.Ω ×ˢ Yint) := by
    have heq : S.V = fun y => (S.V y - dStar⁻¹) + dStar⁻¹ := funext fun y => by ring
    rw [heq]; exact hV0_jc.1.add contDiffOn_const
  let dir : (ℝ × ℝ × ℝ) × ℝ := (((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0 : ℝ))
  have hdir_n : ‖dir‖ = 1 := by simp [dir, Prod.norm_def]
  have hV0_dir := ((hV0_jc.succ_fderiv hO_S).clm_apply_const hO_S.uniqueDiffOn dir).mono
    (le_of_eq (by rw [hdir_n, one_mul]))
  have hp_mem_seg : ∀ t ∈ Icc (0 : ℝ) 1, (ell1 + t * (ell2 - ell1), (1 : ℝ), α) ∈ S.Ω := fun t ht => by
    have hlo : 0 ≤ ell1 + t * (ell2 - ell1) := by nlinarith only [hell1, hell_le, ht.1]
    have hhi : ell1 + t * (ell2 - ell1) ≤ Sw_ell * c ^ (-(1 / 6 : ℝ)) := by nlinarith only [hell2, hell_le, ht.1, ht.2]
    rw [hSΩ]
    exact ⟨⟨by linarith only [hlo], by linarith only [hhi, hSw_lt]⟩,
      ⟨by norm_num, by norm_num⟩, abs_lt.mp hα_om⟩
  have hVdiff_jc : JC 8 (Icc (0 : ℝ) 3.5) (fun Y => S.V ((ell2, 1, α), Y) - S.V ((ell1, 1, α), Y))
      ((Nat.factorial 8 : ℝ) * pbcV * pbC0 * (L_hi - L_lo)) := by
    have hsub35 : Icc (0 : ℝ) 3.5 ⊆ Yint := fun y hy => ⟨by linarith only [hy.1], by linarith only [hy.2]⟩
    have hp2_mem : (ell2, (1 : ℝ), α) ∈ S.Ω := by simpa using hp_mem_seg 1 (right_mem_Icc.mpr zero_le_one)
    have hp1_mem : (ell1, (1 : ℝ), α) ∈ S.Ω := by simpa using hp_mem_seg 0 (left_mem_Icc.mpr zero_le_one)
    have hcd2 : ContDiffOn ℝ 8 (fun Y => S.V ((ell2, 1, α), Y)) Yint :=
      (hV_cd.of_le (by norm_num)).comp (contDiffOn_const.prodMk contDiffOn_id) fun y hy => ⟨hp2_mem, hy⟩
    have hcd1 : ContDiffOn ℝ 8 (fun Y => S.V ((ell1, 1, α), Y)) Yint :=
      (hV_cd.of_le (by norm_num)).comp (contDiffOn_const.prodMk contDiffOn_id) fun y hy => ⟨hp1_mem, hy⟩
    refine ⟨(hcd2.sub hcd1).mono hsub35, fun k hk Y hY => ?_⟩
    have hYint : Y ∈ Yint := hsub35 hY
    have hDu35 : UniqueDiffOn ℝ (Icc (0 : ℝ) 3.5) := uniqueDiffOn_Icc (by norm_num)
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      iteratedDerivWithin_eq_iteratedDeriv hDu35 (((hcd2.sub hcd1).contDiffAt (isOpen_Ioo.mem_nhds hYint)).of_le
        (by exact_mod_cast hk)) hY, Real.norm_eq_abs]
    have hk8 : ((k : ℕ∞) : WithTop ℕ∞) ≤ 8 := by
      rw [show (8 : WithTop ℕ∞) = (((8 : ℕ) : ℕ∞) : WithTop ℕ∞) by rfl]; exact_mod_cast hk
    rw [show (fun s => S.V ((ell2, 1, α), s) - S.V ((ell1, 1, α), s)) =
        (fun s => S.V ((ell2, 1, α), s)) - (fun s => S.V ((ell1, 1, α), s)) from rfl,
      iteratedDeriv_sub ((hcd2.contDiffAt (isOpen_Ioo.mem_nhds hYint)).of_le hk8)
        ((hcd1.contDiffAt (isOpen_Ioo.mem_nhds hYint)).of_le hk8)]
    let v : ℝ × ℝ × ℝ := (ell2 - ell1, 0, 0)
    let p1 : ℝ × ℝ × ℝ := (ell1, 1, α)
    let φ : ℝ → ℝ := fun t => iteratedDeriv k (fun s => S.V (p1 + t • v, s)) Y
    have hVk2 : ContDiffOn ℝ (k + 2) S.V (S.Ω ×ˢ Yint) :=
      hV_cd.of_le (by exact_mod_cast (by omega : k + 2 ≤ 16))
    have hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt φ
        (iteratedDeriv k (fun s => fderiv ℝ S.V (p1 + t • v, s) (v, 0)) Y) (Icc (0 : ℝ) 1) t := fun t ht => by
      have hp_t : p1 + t • v ∈ S.Ω := by
        rw [show p1 + t • v = (ell1 + t * (ell2 - ell1), 1, α) by ext <;> simp [p1, v]]
        exact hp_mem_seg t ht
      exact (hasDerivAt_iteratedDeriv_path hO_S p1 v Y k S.V hVk2 t ⟨hp_t, hYint⟩).hasDerivWithinAt
    have hbd : ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedDeriv k (fun s => fderiv ℝ S.V (p1 + t • v, s) (v, 0)) Y‖ ≤
          (Nat.factorial 8 : ℝ) * pbcV * pbC0 * (L_hi - L_lo) := fun t ht => by
      have hp_t : p1 + t • v ∈ S.Ω := by
        rw [show p1 + t • v = (ell1 + t * (ell2 - ell1), 1, α) by ext <;> simp [p1, v]]
        exact hp_mem_seg t ht
      have hv_eq : (v, (0 : ℝ)) = (ell2 - ell1) • dir := by ext <;> simp [v, dir]
      have hfn : (fun s => fderiv ℝ S.V (p1 + t • v, s) (v, 0)) =
          fun s => (ell2 - ell1) * fderiv ℝ (fun y => S.V y - dStar⁻¹) (p1 + t • v, s) dir := by
        ext s
        rw [hv_eq, map_smul, smul_eq_mul, fderiv_sub_const]
      rw [hfn, iteratedDeriv_const_mul_field, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr hell_le)]
      have hUd_Y : UniqueDiffOn ℝ Yint := isOpen_Ioo.uniqueDiffOn
      have hV0_8 : JC 8 (S.Ω ×ˢ Yint) (fun q => fderiv ℝ (fun y => S.V y - dStar⁻¹) q dir)
          (pbcV * pbC0 * c ^ (-(1 / 2 : ℝ))) := hV0_dir.mono_order (by norm_num : 8 ≤ 15)
      have hs_jc := JC.comp_pair (k := 8) hUd_Y hO_S.uniqueDiffOn
        (g := fun q => fderiv ℝ (fun y => S.V y - dStar⁻¹) q dir)
        (u := fun _ : ℝ => p1 + t • v) (w := fun s : ℝ => s) (b1 := 1) (b2 := 1)
        (by have := pbcV_nonneg; have := pbC0_nonneg; positivity)
        hV0_8 contDiffOn_const contDiffOn_id
        (fun j hj1 _ s hs => by
          simp [iteratedFDerivWithin_eq_iteratedFDeriv hUd_Y contDiffAt_const hs,
            iteratedFDeriv_const_of_ne (by omega : j ≠ 0) (p1 + t • v)])
        (fun j hj1 _ s hs => by
          change ‖iteratedFDerivWithin ℝ j (id : ℝ → ℝ) Yint s‖ ≤ 1
          exact norm_iteratedFDerivWithin_id_le hUd_Y hj1 hs)
        (fun _ hs => ⟨hp_t, hs⟩)
      have hbd_deriv : |iteratedDeriv k (fun s => fderiv ℝ (fun y => S.V y - dStar⁻¹) (p1 + t • v, s) dir) Y| ≤
          (Nat.factorial 8 : ℝ) * pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) := by
        have hk8 := hs_jc.2 k hk Y hYint
        rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
          iteratedDerivWithin_of_isOpen isOpen_Ioo hYint, Real.norm_eq_abs] at hk8
        have hmax1 : max (1 : ℝ) (max 1 1) = 1 := by norm_num
        rw [hmax1, one_pow, mul_one] at hk8
        exact hk8.trans_eq (by ring)
      calc (ell2 - ell1) * |iteratedDeriv k (fun s => fderiv ℝ (fun y => S.V y - dStar⁻¹) (p1 + t • v, s) dir) Y|
          ≤ (ell2 - ell1) * ((Nat.factorial 8 : ℝ) * pbcV * pbC0 * c ^ (-(1 / 2 : ℝ))) := by gcongr
        _ = (c ^ (1 / 2 : ℝ) * c ^ (-(1 / 2 : ℝ))) * ((Nat.factorial 8 : ℝ) * pbcV * pbC0 * (L_hi - L_lo)) := by
            rw [hell_diff]; ring
        _ = (Nat.factorial 8 : ℝ) * pbcV * pbC0 * (L_hi - L_lo) := by
            rw [← Real.rpow_add hc0, add_neg_cancel, Real.rpow_zero, one_mul]
    have hmv := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd
      (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
    have hp2_eq : p1 + (1 : ℝ) • v = (ell2, 1, α) := by ext <;> simp [p1, v]
    have hφ1 : φ 1 = iteratedDeriv k (fun s => S.V ((ell2, 1, α), s)) Y := by dsimp only [φ]; rw [hp2_eq]
    have hφ0 : φ 0 = iteratedDeriv k (fun s => S.V ((ell1, 1, α), s)) Y := by dsimp only [φ]; rw [zero_smul, add_zero]
    simpa [Real.norm_eq_abs, hφ1, hφ0, sub_zero, mul_one] using hmv
  have hV_sym := (win_g_Y_sym_0 hc1
    (by have := pbcV_nonneg; have := pbC0_nonneg; have := sub_nonneg.mpr h12; positivity) hVdiff_jc).mono_B
    Icc_subset_Ici_self (by
      have : C_Y ≤ C_tot := le_max_left _ _
      calc (Nat.factorial 8 : ℝ) * 32 ^ 8 * ((Nat.factorial 8 : ℝ) * pbcV * pbC0 * (L_hi - L_lo))
          = C_Y * (L_hi - L_lo) := by dsimp only [C_Y]; ring
        _ ≤ C_tot * (L_hi - L_lo) := mul_le_mul_of_nonneg_right this (sub_nonneg.mpr h12))
  have hT_sym : FctSymClsOn (Icc 0 (fctUc c)) 8 1 (C_tot * c ^ (-(1 / 3 : ℝ)) * (L_hi - L_lo))
      (fun u => ((fctInnerT c (fun Y => S.V ((ell2, 1, α), Y)) u -
        fctInnerT c (fun Y => S.V ((ell1, 1, α), Y)) u : ℝ) : ℂ)) := by
    have hY_sym : FctSymClsOn (Icc 0 (fctUc c)) 8 0 (C_Y * (L_hi - L_lo))
        (fun u => ((S.V ((ell2, 1, α), fctInnerY c u) - S.V ((ell1, 1, α), fctInnerY c u) : ℝ) : ℂ)) :=
      (win_g_Y_sym_0 hc1
        (by have := pbcV_nonneg; have := pbC0_nonneg; have := sub_nonneg.mpr h12; positivity) hVdiff_jc).mono_B
        Icc_subset_Ici_self (le_of_eq (by dsimp only [C_Y]; ring))
    have hid : FctSymClsOn (Icc 0 (fctUc c)) 8 1 1 (fun u : ℝ => (u : ℂ)) :=
      (id_symCls 8).mono_set Icc_subset_Ici_self hDu (uniqueDiffOn_Ici 0)
    have hprod := (hid.mul Icc_subset_Ici_self hDu hY_sym).const_mul hDu
      (((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ)
    have hnorm : ‖(((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ)‖ =
        (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hprodB : FctSymClsOn (Icc 0 (fctUc c)) 8 (1 + 0) (C_tot * c ^ (-(1 / 3 : ℝ)) * (L_hi - L_lo))
        (fun u => (((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) *
          ((u : ℂ) * ((S.V ((ell2, 1, α), fctInnerY c u) - S.V ((ell1, 1, α), fctInnerY c u) : ℝ) : ℂ))) :=
      hprod.mono_B Icc_subset_Ici_self (by
        rw [hnorm]; have : C_T ≤ C_tot := le_max_right _ _
        calc (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * (2 ^ 8 * 1 * (C_Y * (L_hi - L_lo)))
            = C_T * c ^ (-(1 / 3 : ℝ)) * (L_hi - L_lo) := by dsimp only [C_T]; ring
          _ ≤ C_tot * c ^ (-(1 / 3 : ℝ)) * (L_hi - L_lo) := by gcongr)
    refine (hprodB.mono_p Icc_subset_Ici_self
      (by have := pbcV_nonneg; have := pbC0_nonneg; have := sub_nonneg.mpr h12; positivity)
      (by norm_num : (1 : ℝ) + 0 ≤ 1)).congr hDu fun u _ => ?_
    dsimp only [fctInnerT, fctInnerY]; push_cast; ring
  exact ⟨hV_sym, hT_sym⟩

/-! ### 4. Difference composition `g(T_2 u) - g(T_1 u)` (`win_comp_T_diff_jc`) -/

private lemma re_iteratedDeriv (r : ℕ) {f : ℝ → ℂ} {O : Set ℝ} (hO : IsOpen O)
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

private lemma im_iteratedDeriv (r : ℕ) {f : ℝ → ℂ} {O : Set ℝ} (hO : IsOpen O)
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

private lemma fctVJets_convex {K c s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {V1 V2 : ℝ → ℝ} (h1 : FctVJets K c V1) (h2 : FctVJets K c V2) :
    FctVJets K c (fun Y => (1 - s) * V1 Y + s * V2 Y) := by
  have hDu36 := uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 3.6)
  refine ⟨(contDiffOn_const.mul h1.1).add (contDiffOn_const.mul h2.1), fun j hj Y hY => ?_⟩
  have h1s : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
  have hs0 : 0 ≤ s := hs.1
  have hj14 : ((j : ℕ∞) : WithTop ℕ∞) ≤ 14 := by
    rw [show (14 : WithTop ℕ∞) = (((14 : ℕ) : ℕ∞) : WithTop ℕ∞) by rfl]; exact_mod_cast hj
  have hd1 : ContDiffOn ℝ j (fun Y => V1 Y - (12 / π ^ 2) ^ (1 / 3 : ℝ)) (Icc 0 3.6) :=
    (h1.1.of_le hj14).sub contDiffOn_const
  have hd2 : ContDiffOn ℝ j (fun Y => V2 Y - (12 / π ^ 2) ^ (1 / 3 : ℝ)) (Icc 0 3.6) :=
    (h2.1.of_le hj14).sub contDiffOn_const
  have heq : EqOn (fun Y => (1 - s) * V1 Y + s * V2 Y - (12 / π ^ 2) ^ (1 / 3 : ℝ))
      (fun Y => (1 - s) * (V1 Y - (12 / π ^ 2) ^ (1 / 3 : ℝ)) +
        s * (V2 Y - (12 / π ^ 2) ^ (1 / 3 : ℝ))) (Icc 0 3.6) := fun z _ => by ring
  rw [iteratedDerivWithin_congr heq hY]
  change |iteratedDerivWithin j
      ((fun Y => (1 - s) * (V1 Y - (12 / π ^ 2) ^ (1 / 3 : ℝ))) +
        (fun Y => s * (V2 Y - (12 / π ^ 2) ^ (1 / 3 : ℝ)))) (Icc 0 3.6) Y| ≤ _
  rw [iteratedDerivWithin_add hY hDu36
      ((contDiffOn_const.mul hd1).contDiffWithinAt hY)
      ((contDiffOn_const.mul hd2).contDiffWithinAt hY),
    iteratedDerivWithin_const_mul (n := j) (c := 1 - s) hY hDu36 (hd1.contDiffWithinAt hY),
    iteratedDerivWithin_const_mul (n := j) (c := s) hY hDu36 (hd2.contDiffWithinAt hY)]
  have hb1 := h1.2 j hj Y hY
  have hb2 := h2.2 j hj Y hY
  calc |(1 - s) * iteratedDerivWithin j (fun Y => V1 Y - (12 / π ^ 2) ^ (1 / 3 : ℝ)) (Icc 0 3.6) Y +
        s * iteratedDerivWithin j (fun Y => V2 Y - (12 / π ^ 2) ^ (1 / 3 : ℝ)) (Icc 0 3.6) Y|
      ≤ (1 - s) * |iteratedDerivWithin j (fun Y => V1 Y - (12 / π ^ 2) ^ (1 / 3 : ℝ)) (Icc 0 3.6) Y| +
        s * |iteratedDerivWithin j (fun Y => V2 Y - (12 / π ^ 2) ^ (1 / 3 : ℝ)) (Icc 0 3.6) Y| := by
        simpa [abs_mul, abs_of_nonneg h1s, abs_of_nonneg hs0] using abs_add_le
          ((1 - s) * _) (s * _)
    _ ≤ (1 - s) * (K * c ^ (-(1 / 2 : ℝ))) + s * (K * c ^ (-(1 / 2 : ℝ))) := by gcongr
    _ = K * c ^ (-(1 / 2 : ℝ)) := by ring

theorem win_comp_T_diff_jc {K : ℝ} (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c R B_g D : ℝ},
      (10000 : ℝ) ≤ c → K * c ^ (-(1 / 2 : ℝ)) ≤ 0.001 → 3 * fctTau1 c ≤ R →
      0 ≤ B_g → 0 ≤ D →
      ∀ {V1 V2 : ℝ → ℝ},
        ContDiffOn ℝ 10 V1 Yint → ContDiffOn ℝ 10 V2 Yint →
        FctVJets K c V1 → FctVJets K c V2 →
        (∀ y ∈ Yint, 0 ≤ V1 y ∧ V1 y ≤ 1.1) →
        (∀ y ∈ Yint, 0 ≤ V2 y ∧ V2 y ≤ 1.1) →
        FctSymClsOn (Icc 0 (fctUc c)) 8 1 (D * c ^ (-(1 / 3 : ℝ)))
          (fun u => ((fctInnerT c V2 u - fctInnerT c V1 u : ℝ) : ℂ)) →
        ∀ {g : ℝ → ℂ}, ContDiffOn ℝ 10 g (Ioo (-R) R) → JC 8 (Ioo (-R) R) (deriv g) B_g →
          FctSymClsOn (Icc 0 (fctUc c)) 8 1 (C * B_g * D * c ^ (-(1 / 3 : ℝ)))
            (fun u => g (fctInnerT c V2 u) - g (fctInnerT c V1 u)) := by
  obtain ⟨B_T, hBT1, hBT⟩ := fctInnerT_sym_bounds hK
  let M_m : ℝ := max 1 (4 * B_T)
  let C_g : ℝ := (Nat.factorial 8 : ℝ) * M_m ^ 8
  let C_fin : ℝ := 2 ^ 8 * C_g
  refine ⟨C_fin, by positivity, fun {c R B_g D} hc10000 hη hR hBg0 hD0
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
      (1 - s) * fctInnerT c V1 u + s * fctInnerT c V2 u ∈ Ioo (-R) R := fun s hs u hu => by
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
    have htot : |(1 - s) * fctInnerT c V1 u + s * fctInnerT c V2 u| ≤ 1.2 * (2.06 * fctTau1 c) := by
      calc |(1 - s) * fctInnerT c V1 u + s * fctInnerT c V2 u|
          ≤ |1 - s| * |fctInnerT c V1 u| + |s| * |fctInnerT c V2 u| := by
            simpa [abs_mul] using abs_add_le ((1 - s) * fctInnerT c V1 u) (s * fctInnerT c V2 u)
        _ ≤ |1 - s| * (2.06 * fctTau1 c) + |s| * (2.06 * fctTau1 c) := by gcongr
        _ = (|1 - s| + |s|) * (2.06 * fctTau1 c) := by ring
        _ ≤ 1.2 * (2.06 * fctTau1 c) := by gcongr
    have hlt : 1.2 * (2.06 * fctTau1 c) < 3 * fctTau1 c := by nlinarith only [hτ_pos]
    exact abs_lt.mp (lt_of_le_of_lt htot (lt_of_lt_of_le hlt hR))
  have hT1_cd : ContDiffOn ℝ 10 (fctInnerT c V1) O_u := by
    have hYc : ContDiff ℝ 10 (fctInnerY c) := by unfold fctInnerY; fun_prop
    exact ((contDiff_const.mul contDiff_id).contDiffOn).mul (hV1_cd.comp hYc.contDiffOn fun u hu => hOu_Y u hu)
  have hT2_cd : ContDiffOn ℝ 10 (fctInnerT c V2) O_u := by
    have hYc : ContDiff ℝ 10 (fctInnerY c) := by unfold fctInnerY; fun_prop
    exact ((contDiff_const.mul contDiff_id).contDiffOn).mul (hV2_cd.comp hYc.contDiffOn fun u hu => hOu_Y u hu)
  have hg1_cd : ContDiffOn ℝ 10 (fun u => g (fctInnerT c V1 u)) O_u :=
    hg_cd.comp hT1_cd fun u hu => by simpa using hT_map_R 0 ⟨by norm_num, by norm_num⟩ u hu
  have hg2_cd : ContDiffOn ℝ 10 (fun u => g (fctInnerT c V2 u)) O_u :=
    hg_cd.comp hT2_cd fun u hu => by simpa using hT_map_R 1 ⟨by norm_num, by norm_num⟩ u hu
  refine ⟨(hg2_cd.sub hg1_cd |>.of_le (by norm_num)).mono hIcc_Ou, fun r hr u₀ hu₀ => ?_⟩
  have hk10 : ((r : ℕ∞) : WithTop ℕ∞) ≤ 10 := by
    rw [show (10 : WithTop ℕ∞) = (((10 : ℕ) : ℕ∞) : WithTop ℕ∞) by rfl]; exact_mod_cast (by omega : r ≤ 10)
  rw [iteratedDerivWithin_eq_iteratedDeriv hDu
    (((hg2_cd.sub hg1_cd).contDiffAt (hOu_open.mem_nhds (hIcc_Ou hu₀))).of_le hk10) hu₀]
  rw [show (fun u => g (fctInnerT c V2 u) - g (fctInnerT c V1 u)) =
      (fun u => g (fctInnerT c V2 u)) - (fun u => g (fctInnerT c V1 u)) from rfl,
    iteratedDeriv_sub ((hg2_cd.contDiffAt (hOu_open.mem_nhds (hIcc_Ou hu₀))).of_le hk10)
      ((hg1_cd.contDiffAt (hOu_open.mem_nhds (hIcc_Ou hu₀))).of_le hk10)]
  let H : ℝ × ℝ → ℂ := fun q => g ((1 - q.1) * fctInnerT c V1 q.2 + q.1 * fctInnerT c V2 q.2)
  have hO_prod : IsOpen (Ioo (-0.1 : ℝ) 1.1 ×ˢ O_u) := isOpen_Ioo.prod hOu_open
  have hH_cd : ContDiffOn ℝ 10 H (Ioo (-0.1 : ℝ) 1.1 ×ˢ O_u) := by
    have harg : ContDiffOn ℝ 10 (fun q : ℝ × ℝ => (1 - q.1) * fctInnerT c V1 q.2 + q.1 * fctInnerT c V2 q.2)
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
        (deriv g ((1 - s) * fctInnerT c V1 u + s * fctInnerT c V2 u) *
          ((fctInnerT c V2 u - fctInnerT c V1 u : ℝ) : ℂ)).re ∧
      fderiv ℝ (fun q => (H q).im) (s, u) (1, 0) =
        (deriv g ((1 - s) * fctInnerT c V1 u + s * fctInnerT c V2 u) *
          ((fctInnerT c V2 u - fctInnerT c V1 u : ℝ) : ℂ)).im := by
    intro s hs u hu
    have hs_mem : s ∈ Ioo (-0.1 : ℝ) 1.1 := ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
    have hT_z := hT_map_R s hs_mem u hu
    have hdg : HasDerivAt g (deriv g ((1 - s) * fctInnerT c V1 u + s * fctInnerT c V2 u))
        ((1 - s) * fctInnerT c V1 u + s * fctInnerT c V2 u) :=
      ((hg_cd.contDiffAt (isOpen_Ioo.mem_nhds hT_z)).differentiableAt (by norm_num)).hasDerivAt
    have hlin : HasDerivAt (fun t : ℝ => (1 - t) * fctInnerT c V1 u + t * fctInnerT c V2 u)
        (fctInnerT c V2 u - fctInnerT c V1 u) s := by
      have := (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).mul_const (fctInnerT c V1 u)).add
        ((hasDerivAt_id s).mul_const (fctInnerT c V2 u))
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
        (deriv g ((1 - s) * fctInnerT c V1 u + s * fctInnerT c V2 u) *
          ((fctInnerT c V2 u - fctInnerT c V1 u : ℝ) : ℂ)) 0 := by
      have hc2 : HasDerivAt (fun t : ℝ => s + t * 1) 1 0 :=
        ((hasDerivAt_const 0 s).add ((hasDerivAt_id 0).mul_const 1)).congr_deriv (by ring)
      have hHc0 : HasDerivAt (fun t => g ((1 - t) * fctInnerT c V1 u + t * fctInnerT c V2 u))
          ((fctInnerT c V2 u - fctInnerT c V1 u) • deriv g ((1 - s) * fctInnerT c V1 u + s * fctInnerT c V2 u))
          (s + 0 * 1) := by
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
      (iteratedDeriv r (fun u => deriv g ((1 - s) * fctInnerT c V1 u + s * fctInnerT c V2 u) *
        ((fctInnerT c V2 u - fctInnerT c V1 u : ℝ) : ℂ)) u₀) (Icc (0 : ℝ) 1) s := fun s hs => by
    have hs_mem : s ∈ Ioo (-0.1 : ℝ) 1.1 := ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
    have hpr := hpath_re s ⟨by simpa using hs_mem, hIcc_Ou hu₀⟩
    have hpi := hpath_im s ⟨by simpa using hs_mem, hIcc_Ou hu₀⟩
    have hHr_u : ∀ t : ℝ, t ∈ Ioo (-0.1 : ℝ) 1.1 → ContDiffOn ℝ r (fun u => H (t, u)) O_u := fun t ht =>
      (hH_cd.of_le hk10).comp (contDiffOn_const.prodMk contDiffOn_id) fun u hu => ⟨ht, hu⟩
    have hre_eq : (fun t => iteratedDeriv r (fun u => (H (0 + t • 1, u)).re) u₀) =ᶠ[𝓝 s]
        fun t => (φ t).re := by
      filter_upwards [isOpen_Ioo.mem_nhds hs_mem] with t ht
      rw [zero_add, smul_eq_mul, mul_one]
      exact re_iteratedDeriv r hOu_open (hHr_u t ht) (hIcc_Ou hu₀)
    have him_eq : (fun t => iteratedDeriv r (fun u => (H (0 + t • 1, u)).im) u₀) =ᶠ[𝓝 s]
        fun t => (φ t).im := by
      filter_upwards [isOpen_Ioo.mem_nhds hs_mem] with t ht
      rw [zero_add, smul_eq_mul, mul_one]
      exact im_iteratedDeriv r hOu_open (hHr_u t ht) (hIcc_Ou hu₀)
    have hd_cd : ContDiffOn ℝ r (fun u => deriv g ((1 - s) * fctInnerT c V1 u + s * fctInnerT c V2 u) *
        ((fctInnerT c V2 u - fctInnerT c V1 u : ℝ) : ℂ)) O_u := by
      have hg' : ContDiffOn ℝ 9 (deriv g) (Ioo (-R) R) := by
        have h0 := hg_cd.derivWithin isOpen_Ioo.uniqueDiffOn (by norm_num : ((9 : WithTop ℕ∞) + 1 ≤ 10))
        exact h0.congr fun x hx => (derivWithin_of_isOpen isOpen_Ioo hx).symm
      have harg_u : ContDiffOn ℝ 10 (fun u => (1 - s) * fctInnerT c V1 u + s * fctInnerT c V2 u) O_u :=
        (contDiffOn_const.mul hT1_cd).add (contDiffOn_const.mul hT2_cd)
      exact ((hg'.of_le (by norm_cast; omega)).comp (harg_u.of_le (by norm_cast; omega))
        fun u hu => hT_map_R s hs_mem u hu).mul
        (Complex.ofRealCLM.contDiff.comp_contDiffOn ((hT2_cd.sub hT1_cd).of_le (by norm_cast; omega)))
    have hval_re : iteratedDeriv r (fun u => fderiv ℝ (fun q => (H q).re) (0 + s • 1, u) (1, 0)) u₀ =
        (iteratedDeriv r (fun u => deriv g ((1 - s) * fctInnerT c V1 u + s * fctInnerT c V2 u) *
          ((fctInnerT c V2 u - fctInnerT c V1 u : ℝ) : ℂ)) u₀).re := by
      rw [← re_iteratedDeriv r hOu_open hd_cd (hIcc_Ou hu₀)]
      refine Filter.EventuallyEq.iteratedDeriv_eq r ?_
      filter_upwards [hOu_open.mem_nhds (hIcc_Ou hu₀)] with u hu
      rw [zero_add, smul_eq_mul, mul_one]
      exact (hfderiv_H s hs u hu).1
    have hval_im : iteratedDeriv r (fun u => fderiv ℝ (fun q => (H q).im) (0 + s • 1, u) (1, 0)) u₀ =
        (iteratedDeriv r (fun u => deriv g ((1 - s) * fctInnerT c V1 u + s * fctInnerT c V2 u) *
          ((fctInnerT c V2 u - fctInnerT c V1 u : ℝ) : ℂ)) u₀).im := by
      rw [← im_iteratedDeriv r hOu_open hd_cd (hIcc_Ou hu₀)]
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
      ‖iteratedDeriv r (fun u => deriv g ((1 - s) * fctInnerT c V1 u + s * fctInnerT c V2 u) *
        ((fctInnerT c V2 u - fctInnerT c V1 u : ℝ) : ℂ)) u₀‖ ≤
        C_fin * B_g * D * c ^ (-(1 / 3 : ℝ)) * (1 + u₀) ^ ((1 : ℝ) - r) := fun s hs => by
    let V_s : ℝ → ℝ := fun Y => (1 - s) * V1 Y + s * V2 Y
    have hVs_j := fctVJets_convex hs hV1_j hV2_j
    obtain ⟨hTs_cd, _, hTs_deriv, _⟩ := hBT hc1 hη hVs_j
    have hTs_eq : ∀ u : ℝ, (1 - s) * fctInnerT c V1 u + s * fctInnerT c V2 u = fctInnerT c V_s u := fun u => by
      dsimp only [fctInnerT, V_s]; ring
    have hs_mem : s ∈ Ioo (-0.1 : ℝ) 1.1 := ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
    have hTs_maps : MapsTo (fctInnerT c V_s) (Icc 0 (fctUc c)) (Ioo (-R) R) := fun u hu => by
      rw [← hTs_eq u]; exact hT_map_R s hs_mem u (hIcc_Ou hu)
    have hBfM : B_T * c ^ (-(1 / 3 : ℝ)) * (1 + fctUc c) ≤ M_m := by
      have h1 := one_add_fctUc_le hc1
      have hc14 : c ^ (-(1 / 3 : ℝ)) * c ^ ((1 : ℝ) / 12) = c ^ (-(1 / 4 : ℝ)) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      have hle1 : c ^ (-(1 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
      calc B_T * c ^ (-(1 / 3 : ℝ)) * (1 + fctUc c)
          ≤ B_T * c ^ (-(1 / 3 : ℝ)) * (4 * c ^ ((1 : ℝ) / 12)) := by gcongr
        _ = 4 * B_T * (c ^ (-(1 / 3 : ℝ)) * c ^ ((1 : ℝ) / 12)) := by ring
        _ ≤ 4 * B_T * 1 := by rw [hc14]; gcongr
        _ ≤ M_m := by rw [mul_one]; exact le_max_right _ _
    have hdg_sym := FctSymClsOn.comp_T_zero hUc0 (le_max_left _ _ : 1 ≤ M_m) isOpen_Ioo.uniqueDiffOn
      (hg_jc.1.mono (by rfl) |>.of_le (by norm_num)) hBg0
      (fun i hi t ht => by
        have := hg_jc.2 i hi t ht
        rwa [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin] at this)
      hTs_cd hTs_maps (by positivity) hBfM (fun j hj1 hj8 u hu => hTs_deriv j hj1 hj8 u hu)
    have hdg_sym' : FctSymClsOn (Icc 0 (fctUc c)) 8 0 (C_g * B_g)
        (fun u => deriv g ((1 - s) * fctInnerT c V1 u + s * fctInnerT c V2 u)) :=
      (hdg_sym.mono_B Icc_subset_Ici_self (le_of_eq (by dsimp only [C_g]; ring))).congr hDu
        fun u _ => by dsimp only [Function.comp_apply]; rw [hTs_eq u]
    have hprod : FctSymClsOn (Icc 0 (fctUc c)) 8 (0 + 1) (C_fin * B_g * D * c ^ (-(1 / 3 : ℝ)))
        (fun u => deriv g ((1 - s) * fctInnerT c V1 u + s * fctInnerT c V2 u) *
          ((fctInnerT c V2 u - fctInnerT c V1 u : ℝ) : ℂ)) :=
      (hdg_sym'.mul Icc_subset_Ici_self hDu hT_diff).mono_B Icc_subset_Ici_self
        (le_of_eq (by dsimp only [C_fin]; ring))
    have hprod1 := hprod.mono_p Icc_subset_Ici_self (by positivity) (by norm_num : (0 : ℝ) + 1 ≤ 1)
    have hb_u0 : ‖iteratedDerivWithin r (fun u => deriv g ((1 - s) * fctInnerT c V1 u + s * fctInnerT c V2 u) *
          ((fctInnerT c V2 u - fctInnerT c V1 u : ℝ) : ℂ)) (Icc 0 (fctUc c)) u₀‖ ≤
        C_fin * B_g * D * c ^ (-(1 / 3 : ℝ)) * (1 + u₀) ^ ((1 : ℝ) - r) :=
      hprod1.2 r hr u₀ hu₀
    have hg'_cd : ContDiffOn ℝ r (fun u => deriv g ((1 - s) * fctInnerT c V1 u + s * fctInnerT c V2 u) *
        ((fctInnerT c V2 u - fctInnerT c V1 u : ℝ) : ℂ)) O_u := by
      have hg9 : ContDiffOn ℝ 9 (deriv g) (Ioo (-R) R) := by
        have h0 := hg_cd.derivWithin isOpen_Ioo.uniqueDiffOn (by norm_num : ((9 : WithTop ℕ∞) + 1 ≤ 10))
        exact h0.congr fun x hx => (derivWithin_of_isOpen isOpen_Ioo hx).symm
      have harg_u : ContDiffOn ℝ 10 (fun u => (1 - s) * fctInnerT c V1 u + s * fctInnerT c V2 u) O_u :=
        (contDiffOn_const.mul hT1_cd).add (contDiffOn_const.mul hT2_cd)
      exact ((hg9.of_le (by norm_cast; omega)).comp (harg_u.of_le (by norm_cast; omega))
        fun u hu => hT_map_R s hs_mem u hu).mul
        (Complex.ofRealCLM.contDiff.comp_contDiffOn ((hT2_cd.sub hT1_cd).of_le (by norm_cast; omega)))
    rwa [iteratedDerivWithin_eq_iteratedDeriv hDu (hg'_cd.contDiffAt (hOu_open.mem_nhds (hIcc_Ou hu₀))) hu₀] at hb_u0
  have hmv := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd
    (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
  have hφ1 : φ 1 = iteratedDeriv r (fun u => g (fctInnerT c V2 u)) u₀ := by
    dsimp only [φ, H]; congr 1; ext u; simp
  have hφ0 : φ 0 = iteratedDeriv r (fun u => g (fctInnerT c V1 u)) u₀ := by
    dsimp only [φ, H]; congr 1; ext u; simp
  simpa [Real.norm_eq_abs, hφ1, hφ0, sub_zero, mul_one] using hmv

/-- info: 'FormalResearch.SignUncertainty.win_fctS_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_fctS_shift

/-- info: 'FormalResearch.SignUncertainty.win_g_Y_sym_0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_g_Y_sym_0

/-- info: 'FormalResearch.SignUncertainty.win_V_diff_sym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_V_diff_sym

/-- info: 'FormalResearch.SignUncertainty.win_comp_T_diff_jc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_comp_T_diff_jc

end FormalResearch.SignUncertainty
