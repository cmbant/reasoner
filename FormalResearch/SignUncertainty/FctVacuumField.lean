/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctVacuumBudget
public import FormalResearch.SignUncertainty.FctPhiKill
public import FormalResearch.SignUncertainty.CtBoasBlocks

/-!
# `hvac` of `physical_budget_field`: the uniform vacuum integral from the named displays (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:physical-budget` (proof parts (a)-(c)).

**Proved** (`vacuum_integral_field`): exactly the hypothesis `hvac` of `FctSym.physical_budget_field`,
`∃ A c₀, ∀ ε c, (ε = ±1) → c₀ ≤ c → ∫ χ(L/3δ) γ(L̃) (O − F) ≤ A c^{-3/4}`, for the physical envelope `O = I_osc^{warp}` (`physOsc`,
`Φ = vacPhi = φ_kill(i τ₀(·); c^{-1/12})`), from the named displays `VacDisp` (`FctVacuumBudget`).  Proved here and not assumed: measurability and the
size bound `‖φ_kill(iτ₀(u); a)‖ ≤ K min(1,(u/a²)⁴)` (`vacPhi_norm_le`: `fct:phikill` (1), `τ₀(L) ≤ 1.105 √L`), `κ ≤ a^{24}`, and the
passage `a = c^{-1/12}`, `c ≥ c₀`.

Remaining hypotheses (fields of `VacDisp`, each a display of `fct:comp-D`/`fct:phikill` for the instantiated datum): `(fct:Dstar-inner)`
consequences (`hDin`, `hDmid`, `hDfar`), `(fct:cos-pen)` (`hDint`, `hCfl`, `hcos`, `hin`), `(fct:bump-1L)` (`hb1`), `(fct:bump-2L)` (`hb2`),
the finite-part cancellation of `(fct:bump-1L)` with `fct:phikill` (3) in the `L`-variable (`hcancel`), and the size/positivity facts of the datum.
For the concrete datum all of them except the size facts, measurability and positivity of `P` and `hDin`, `hDmid`, `hDfar` are proved in
`FctVacuumCancel` (`fct_vac_cancel` = `hcancel`) and `FctVacuumConcrete` (`vacDisp_concrete`, `vacuum_integral_concrete`).

Class: proved under the explicit hypotheses `hO` (the definition of `O` on the support of the cutoff) and `hdisp`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctPhiKill

/-- `Φ(u) = φ_kill(i τ₀(u); a)`. -/
noncomputable def vacPhi (a u : ℝ) : ℂ := phiKill a (((tau0 u : ℝ) : ℂ) * Complex.I)

lemma tau0_monotone : Monotone tau0 := by
  intro L L' h
  by_cases hL : 0 < L
  · exact tau0_mono hL h
  · have h0 : tau0 L = 0 := by simp [tau0, hL]
    rw [h0]
    by_cases hL' : 0 < L'
    · exact (tau0_pos hL').le
    · simp [tau0, hL']

lemma tau0_measurable : Measurable tau0 := tau0_monotone.measurable

lemma vacPhi_measurable {a : ℝ} (ha : 0 < a) : Measurable (vacPhi a) := by
  have hcont : Continuous (fun t : ℝ => phiKill a ((t : ℂ) * Complex.I)) := by
    refine (differentiableOn_phiPQ 8 8 a).continuousOn.comp_continuous
      (Complex.continuous_ofReal.mul continuous_const) fun t => ?_
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, mul_one, sub_self, Complex.neg_re] at hre
    linarith
  exact hcont.measurable.comp tau0_measurable

/-- `‖φ_kill(i τ₀(u); a)‖ ≤ K min(1, (u/a²)⁴)` for `0 < a ≤ 1`, `u > 0` (`fct:phikill` (1) and `τ₀(L) ≤ 1.105 √L` on `L ≤ 0.002`). -/
lemma vacPhi_norm_le : ∃ K : ℝ, 1 ≤ K ∧ ∀ {a u : ℝ}, 0 < a → a ≤ 1 → 0 < u →
    ‖vacPhi a u‖ ≤ K * min 1 ((u / a ^ 2) ^ 4) := by
  obtain ⟨C, hC0, hC⟩ := norm_phiPQ_le 8 8
  refine ⟨C * 10 ^ 11 + 1, by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 10) 11], fun {a u} ha ha1 hu => ?_⟩
  have hτ := tau0_pos hu
  have hz : ‖((tau0 u : ℝ) : ℂ) * Complex.I‖ = tau0 u := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
  have h1 : ‖vacPhi a u‖ ≤ C * min ((tau0 u / a) ^ 8) 1 := by
    have := hC (a := a) (z := ((tau0 u : ℝ) : ℂ) * Complex.I) ha (by simp)
    rwa [hz] at this
  have hK1 : 0 ≤ C * 10 ^ 11 + 1 := by positivity
  by_cases hu2 : u ≤ 0.002
  · obtain ⟨-, hb, -⟩ := tau0_bounds hu hu2
    have hx : 0 ≤ u / a ^ 2 := by positivity
    have h2 : (tau0 u / a) ^ 8 ≤ 3 * (u / a ^ 2) ^ 4 := by
      have : (tau0 u / a) ^ 8 ≤ (1.105 * Real.sqrt u / a) ^ 8 := by gcongr
      refine this.trans ?_
      have e : (1.105 * Real.sqrt u / a) ^ 8 = 1.105 ^ 8 * (u / a ^ 2) ^ 4 := by
        rw [div_pow, mul_pow]
        have : (Real.sqrt u) ^ 8 = u ^ 4 := by
          rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, Real.sq_sqrt hu.le]
        rw [this]; field_simp
      rw [e]; gcongr; norm_num
    have h3 : min ((tau0 u / a) ^ 8) 1 ≤ 3 * min 1 ((u / a ^ 2) ^ 4) := by
      rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3)]
      refine le_min ?_ ?_
      · exact (min_le_right _ _).trans (by norm_num)
      · exact (min_le_left _ _).trans h2
    calc ‖vacPhi a u‖ ≤ C * min ((tau0 u / a) ^ 8) 1 := h1
      _ ≤ C * (3 * min 1 ((u / a ^ 2) ^ 4)) := by gcongr
      _ ≤ (C * 10 ^ 11 + 1) * min 1 ((u / a ^ 2) ^ 4) := by
        have hm : 0 ≤ min 1 ((u / a ^ 2) ^ 4) := le_min zero_le_one (by positivity)
        nlinarith [mul_nonneg hC0 hm]
  · have hu3 : (0.002 : ℝ) < u := not_le.mp hu2
    have hx : (0.002 : ℝ) ≤ u / a ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : a ^ 2 ≤ 1 := pow_le_one₀ ha.le ha1
      nlinarith
    have hx4 : (0.002 : ℝ) ^ 4 ≤ (u / a ^ 2) ^ 4 := pow_le_pow_left₀ (by norm_num) hx 4
    have hmin : (0.002 : ℝ) ^ 4 ≤ min 1 ((u / a ^ 2) ^ 4) := le_min (by norm_num) hx4
    calc ‖vacPhi a u‖ ≤ C * min ((tau0 u / a) ^ 8) 1 := h1
      _ ≤ C * 1 := by gcongr; exact min_le_right _ _
      _ ≤ (C * 10 ^ 11 + 1) * min 1 ((u / a ^ 2) ^ 4) := by
        have : (1 : ℝ) ≤ 10 ^ 11 * min 1 ((u / a ^ 2) ^ 4) := by
          have : (10 : ℝ) ^ 11 * (0.002 : ℝ) ^ 4 ≥ 1 := by norm_num
          nlinarith
        have hm : 0 ≤ min 1 ((u / a ^ 2) ^ 4) := le_min zero_le_one (by positivity)
        nlinarith [mul_nonneg hC0 hm]


/-- `VacDisp` is monotone in the dominating constant `K`. -/
lemma VacDisp.mono {K K' a0 a1 a δ s L1 α Cfl I0 : ℝ} {P : ℝ → ℝ} {Φ : ℝ → ℂ} (D : VacDisp K a0 a1 a δ s L1 α Cfl I0 P Φ)
    (h : K ≤ K') : VacDisp K' a0 a1 a δ s L1 α Cfl I0 P Φ := by
  have hK0 : 0 ≤ K := by linarith [D.hK]
  have ha := D.ha
  have hf : ∀ {x y : ℝ}, 0 ≤ y → x ≤ K * y → x ≤ K' * y := fun hy hx => hx.trans (mul_le_mul_of_nonneg_right h hy)
  have ha' : ∀ n : ℕ, 0 ≤ a ^ n := fun n => by positivity
  have hai : ∀ n : ℕ, 0 ≤ (a⁻¹) ^ n := fun n => by have := D.ha; positivity
  refine ⟨D.hK.trans h, D.ha0, D.hKa0.trans h, D.hKa1.trans h, D.hKf.trans h, D.ha, D.ha1, D.hδ0, D.hδ1,
    hf (ha' 12) D.hs, hf (ha' 8) D.hL1, hf (ha' 8) D.hα, D.hPm, D.hP0, ?_, ?_, ?_, D.hDint, D.hCfl, ?_, ?_, D.hI0.trans h, ?_, ?_, ?_⟩
  · intro u hu
    exact hf (Real.sqrt_nonneg u) (D.hDin u hu)
  · intro u hu
    have hu0 : 0 < u := by
      have : 0 < 3 * δ := lt_of_lt_of_le (mul_pos D.ha0 (pow_pos ha 6)) (by nlinarith [D.hδ0, mul_pos D.ha0 (pow_pos ha 6)])
      linarith [hu.1]
    have := D.hDmid u hu
    calc |vacD P u| ≤ K * a ^ 6 * u ^ (-(3 / 2 : ℝ)) := this
      _ ≤ K' * a ^ 6 * u ^ (-(3 / 2 : ℝ)) := by gcongr
  · intro u hu
    have hu0 : 0 < u := by
      have : 0 < 144 * δ := lt_of_lt_of_le (mul_pos D.ha0 (pow_pos ha 6)) (by nlinarith [D.hδ0, mul_pos D.ha0 (pow_pos ha 6)])
      linarith
    exact hf (Real.rpow_nonneg hu0.le _) (D.hDfar u hu)
  · exact D.hcos.trans (mul_le_mul_of_nonneg_right h (ha' 9))
  · exact D.hin.trans (mul_le_mul_of_nonneg_right h (add_nonneg (ha' 9) (mul_nonneg (abs_nonneg _) (ha' 3))))
  · exact D.hb1.trans (mul_le_mul_of_nonneg_right h (add_nonneg (ha' 3) (mul_nonneg (abs_nonneg _) (hai 3))))
  · exact D.hb2.trans (mul_le_mul_of_nonneg_right h (add_nonneg (hai 3) (mul_nonneg (abs_nonneg _) (hai 9))))
  · exact D.hcancel.trans (mul_le_mul_of_nonneg_right h
      (add_nonneg (add_nonneg (ha' 3) (mul_nonneg (abs_nonneg _) (hai 3))) (ha' 8)))

/-- **`hvac` of `physical_budget_field`** (`fct:physical-budget` proof, parts (a)-(c)): the uniform vacuum integral
`∫ χ(L/3δ) γ(L̃)(O − F) dL ≤ A c^{-3/4}` for the physical envelope `O = I_osc^{warp}` (`physOsc`, with `Φ = φ_kill(iτ₀(·); c^{-1/12})`),
from the named displays `VacDisp` of `fct:comp-D` (1), (2) and `fct:phikill` (3) at `a = c^{-1/12}`.  `O` is only used on the support
`L ≥ 3δ/2` of the cutoff (`hO`). -/
theorem vacuum_integral_field {χ : ℝ → ℝ} (hχ : IsCutoff χ) (δf sf L1f : ℝ → ℝ → ℝ) (Of Pf : ℝ → ℝ → ℝ → ℝ)
    (αf Cflf I0f : ℝ → ℝ → ℝ)
    (hO : ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → ∀ x : ℝ, 3 / 2 * δf ε c ≤ x →
      Of ε c x = physOsc (Pf ε c) (vacPhi (c ^ (-(1 / 12 : ℝ)))) (sf ε c) (L1f ε c) x)
    (hdisp : ∃ K a0 a1 c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      VacDisp K a0 a1 (c ^ (-(1 / 12 : ℝ))) (δf ε c) (sf ε c) (L1f ε c) (αf ε c) (Cflf ε c) (I0f ε c) (Pf ε c)
        (vacPhi (c ^ (-(1 / 12 : ℝ))))) :
    ∃ A c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      (∫ x, χ (x / (3 * δf ε c)) * physGamma c (sf ε c) x * (Of ε c x - physF (sf ε c) (L1f ε c) x)) ≤
        A * c ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨cO, hO⟩ := hO
  obtain ⟨K, a0, a1, cD, hD⟩ := hdisp
  obtain ⟨Kφ, hKφ1, hΦ⟩ := vacPhi_norm_le
  have hK1 : 1 ≤ K := (hD 1 (max cD 1) (Or.inl rfl) (le_max_left _ _)).hK
  set K' : ℝ := max K (Kφ ^ 2) with hK'
  have hKK' : K ≤ K' := le_max_left _ _
  have hK'1 : 1 ≤ K' := hK1.trans hKK'
  have hφK' : Kφ ^ 2 ≤ K' := le_max_right _ _
  have hφ2 : Kφ ≤ Kφ ^ 2 := by nlinarith
  set M : ℝ := 10 * K' ^ 3 with hM
  have hM1 : 1 ≤ M := by nlinarith [pow_pos (by linarith : (0 : ℝ) < K') 3, one_le_pow₀ hK'1 (n := 3)]
  refine ⟨VacHyp.AM K' + 57 * K' ^ 5 + ABR K', max (max cD cO) (max 1 (M ^ 6)), fun ε c hε hc => ?_⟩
  have hcD : cD ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hc)
  have hcO : cO ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
  have hc1 : 1 ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hcM : M ^ 6 ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
  have hc0 : 0 < c := by linarith
  set a : ℝ := c ^ (-(1 / 12 : ℝ)) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hc0 _
  have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
  have hpow : ∀ n : ℕ, a ^ n = c ^ (-((n : ℝ) / 12)) := by
    intro n
    rw [ha_def, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; congr 1; ring
  have hc12 : c⁻¹ = a ^ 12 := by
    rw [hpow 12]; norm_num [Real.rpow_neg_one]
  have hsm : 10 * K' ^ 3 * a ^ 2 ≤ 1 := by
    have h1 : (a ^ 2 * M) ^ 6 ≤ 1 := by
      have e : (a ^ 2 * M) ^ 6 = c⁻¹ * M ^ 6 := by rw [hc12]; ring
      rw [e, inv_mul_le_iff₀ hc0]; linarith
    have h2 : a ^ 2 * M ≤ 1 := by
      by_contra hlt
      have := one_lt_pow₀ (not_le.mp hlt) (by norm_num : (6 : ℕ) ≠ 0)
      linarith
    nlinarith
  have D := (hD ε c hε hcD).mono hKK'
  have hΦre : ∀ u, 0 < u → |(vacPhi a u).re| ≤ K' * min 1 ((u / a ^ 2) ^ 4) := by
    intro u hu
    have hm : 0 ≤ min 1 ((u / a ^ 2) ^ 4) := le_min zero_le_one (by positivity)
    calc |(vacPhi a u).re| ≤ ‖vacPhi a u‖ := Complex.abs_re_le_norm _
      _ ≤ Kφ * min 1 ((u / a ^ 2) ^ 4) := hΦ ha ha1 hu
      _ ≤ K' * min 1 ((u / a ^ 2) ^ 4) := mul_le_mul_of_nonneg_right (hφ2.trans hφK') hm
  have hΦim : ∀ u, 0 < u → (vacPhi a u).im ^ 2 ≤ K' * min 1 ((u / a ^ 2) ^ 4) := by
    intro u hu
    have hm : 0 ≤ min 1 ((u / a ^ 2) ^ 4) := le_min zero_le_one (by positivity)
    have hm1 : min 1 ((u / a ^ 2) ^ 4) ≤ 1 := min_le_left _ _
    have h1 : |(vacPhi a u).im| ≤ Kφ * min 1 ((u / a ^ 2) ^ 4) := (Complex.abs_im_le_norm _).trans (hΦ ha ha1 hu)
    calc (vacPhi a u).im ^ 2 = |(vacPhi a u).im| ^ 2 := (sq_abs _).symm
      _ ≤ (Kφ * min 1 ((u / a ^ 2) ^ 4)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = Kφ ^ 2 * (min 1 ((u / a ^ 2) ^ 4) * min 1 ((u / a ^ 2) ^ 4)) := by ring
      _ ≤ Kφ ^ 2 * (min 1 ((u / a ^ 2) ^ 4) * 1) := by gcongr
      _ ≤ K' * min 1 ((u / a ^ 2) ^ 4) := by
        rw [mul_one]
        nlinarith [mul_le_mul_of_nonneg_right hφK' hm]
  have V := VacHyp.of_disp (c := c) D hc12 hsm (vacPhi_measurable ha) hΦre hΦim
  have hcore := vac_core (c := c) hχ V rfl
  have h9 : a ^ 9 = c ^ (-(3 / 4 : ℝ)) := by rw [hpow 9]; norm_num
  have hcongr : (∫ x, χ (x / (3 * δf ε c)) * physGamma c (sf ε c) x * (Of ε c x - physF (sf ε c) (L1f ε c) x)) =
      ∫ x, χ (x / (3 * δf ε c)) * physGamma c (sf ε c) x *
        (physOsc (Pf ε c) (vacPhi a) (sf ε c) (L1f ε c) x - physF (sf ε c) (L1f ε c) x) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    by_cases hx : 3 / 2 * δf ε c ≤ x
    · rw [hO ε c hε hcO x hx]
    · have hδ := V.hδpos
      have hz : χ (x / (3 * δf ε c)) = 0 := by
        apply hχ.zero
        rw [div_le_iff₀ (by positivity)]
        linarith [not_le.mp hx]
      rw [hz]; simp
  rw [hcongr, ← h9]
  exact hcore

/-- info: 'FormalResearch.SignUncertainty.FctSym.vacuum_integral_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vacuum_integral_field

/-- info: 'FormalResearch.SignUncertainty.FctSym.vacPhi_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vacPhi_norm_le

end FormalResearch.SignUncertainty.FctSym
