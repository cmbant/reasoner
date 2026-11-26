/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctVacuumCancel
public import FormalResearch.SignUncertainty.FctVacuumPointwise

/-!
# `VacDisp` for the concrete datum: the comp-D displays of `fct:physical-budget` discharged (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:physical-budget` (a)-(d), with Lemma `fct:comp-D` (2) and `fct:phikill` (3).

For the concrete datum `P = vacP` (`I_osc^{DH₀}(1 + Δ_curv ∘ τ₀)`, so `vacD P = D_*`), `Φ = vacPhi a = φ_kill(iτ₀(·); a)`, `a³ = τ₁`, `δ = m(τ₁)`,
`Cfl = stripCfl`, `I0 = stripFp1`, **proved here** (`vacDisp_concrete`) from `fct_comp_D_part2` and `fct_vac_cancel`: the fields `hK`, `ha0`, `hKa0`, `hKa1`,
`hKf`, `ha`, `ha1`, `hδ0`, `hδ1` (`m(t) ≍ t²`), `hDint`, `hCfl`, `hcos`, `hin`, `hI0`, `hb1`, `hb2`, `hcancel` of `VacDisp`.

`vacDisp_concrete` takes the structure `VacPointwise` (pointwise bounds of `(fct:Dstar-inner)` on `D_*`, measurability and nonnegativity of `P`) and the three size
bounds of the physical datum (`|s| ≲ a¹²`, `|L₁| ≲ a⁸`, `|α| ≲ a⁸`) as hypotheses; `VacPointwise` is **proved** for the concrete datum in `FctVacuumPointwise`
(`vacPointwise_concrete`), so `vacuum_integral_concrete` assumes only the size bounds (`hsize`, facts about the physical datum) and the definition of `O` (`hO`).

Class: proved; the only hypotheses of `vacuum_integral_concrete` are the size bounds `hsize` and the identification `hO` of `O` on the support of the cutoff.
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.CohnElkies FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCompD
  FormalResearch.SignUncertainty.FctPhiKill FormalResearch.SignUncertainty.FctMoment

/-- **`VacDisp` for the concrete datum.**  For every `K4 ≥ 1` there is `K ≥ 1` such that, for `c`, `α`, `τ₁ = c^{-1/4} ≤ τ₀`, `a³ = τ₁`, and any `K'`
dominating the size bounds `|s| ≤ K' a¹²`, `|L₁| ≤ K' a⁸`, `|α| ≤ K' a⁸` and `VacPointwise K' a (m τ₁) (vacP …)`, the structure
`VacDisp (max K K') a₀ a₁ a (m τ₁) s L₁ α C_fl f.p.₁ (vacP …) (vacPhi a)` holds. -/
theorem vacDisp_concrete (kind : StripKernelChoice) :
    ∃ τ₀ > 0, τ₀ ≤ 1 / 100 ∧ ∃ a0 a1 : ℝ, 0 < a0 ∧ ∀ K4 : ℝ, 1 ≤ K4 → ∃ K : ℝ, 1 ≤ K ∧
      ∀ {c α τ₁ a s L1 K' : ℝ}, 0 < c → 0 < τ₁ → τ₁ ≤ τ₀ → τ₁ ^ 4 * c = 1 → |α| ≤ τ₁ ^ 2 → 0 < a → a ^ 3 = τ₁ →
        |s| ≤ K' * a ^ 12 → |L1| ≤ K' * a ^ 8 → |α| ≤ K' * a ^ 8 →
        VacPointwise K' a (uctM τ₁) (vacP kind K4 c α τ₁) →
        VacDisp (max K K') a0 a1 a (uctM τ₁) s L1 α (stripCfl kind) (stripFp1 kind) (vacP kind K4 c α τ₁) (vacPhi a) := by
  obtain ⟨τ2, hτ2, hτ2_100, h2⟩ := fct_comp_D_part2 kind
  obtain ⟨τC, hτC, hτC100, hC⟩ := fct_vac_cancel kind
  obtain ⟨cm, hcm, hcm_bd⟩ := uct_m_lower_small
  obtain ⟨Cu, hCu, hCu_bd⟩ := uct_m_upper_small
  refine ⟨min τ2 τC, lt_min hτ2 hτC, (min_le_left _ _).trans hτ2_100, cm, Cu, hcm, fun K4 hK4 => ?_⟩
  obtain ⟨C2, hC20, hC2⟩ := h2 K4 hK4
  obtain ⟨CC, hCC0, hCC⟩ := hC K4 hK4
  have hcminv : 0 < cm⁻¹ := inv_pos.mpr hcm
  set K : ℝ := 1 + C2 + CC + |stripFp1 kind| + |uctAlphaFl| + cm⁻¹ + Cu with hKdef
  have hK1 : 1 ≤ K := by
    have := abs_nonneg (stripFp1 kind); have := abs_nonneg uctAlphaFl; rw [hKdef]; linarith
  refine ⟨K, hK1, fun {c α τ₁ a s L1 K'} hc hτ₁ hτ₁_le hc_eq hα_le ha ha3 hs hL1 hα V => ?_⟩
  have hτ₁_2 : τ₁ ≤ τ2 := hτ₁_le.trans (min_le_left _ _)
  have hτ₁_C : τ₁ ≤ τC := hτ₁_le.trans (min_le_right _ _)
  have hτ₁_100 : τ₁ ≤ 1 / 100 := hτ₁_2.trans hτ2_100
  have ha1 : a ≤ 1 := by
    by_contra h
    have h1 : 1 < a := not_le.mp h
    have : 1 < a ^ 3 := one_lt_pow₀ h1 (by norm_num)
    linarith
  set KK : ℝ := max K K' with hKKdef
  have hKK : K ≤ KK := le_max_left _ _
  have hK'K : K' ≤ KK := le_max_right _ _
  have hK0 : 0 ≤ K := by linarith
  have hKK1 : 1 ≤ KK := hK1.trans hKK
  have habs : 0 ≤ |stripFp1 kind| := abs_nonneg _
  have habs2 : 0 ≤ |uctAlphaFl| := abs_nonneg _
  have hC2K : C2 ≤ KK := hKK.trans' (by rw [hKdef]; linarith)
  have hCCK : CC ≤ KK := hKK.trans' (by rw [hKdef]; linarith)
  have hI0K : |stripFp1 kind| ≤ KK := hKK.trans' (by rw [hKdef]; linarith)
  have hflK : |uctAlphaFl| ≤ KK := hKK.trans' (by rw [hKdef]; linarith)
  have hcmK : cm⁻¹ ≤ KK := hKK.trans' (by rw [hKdef]; linarith)
  have hCuK : Cu ≤ KK := hKK.trans' (by rw [hKdef]; linarith)
  have ha0 : 0 < a := ha
  have hτ_eq : τ₁ = a ^ 3 := ha3.symm
  have hinv : τ₁⁻¹ = (a⁻¹) ^ 3 := by rw [← ha3, inv_pow]
  have hα_a : |α| ≤ a ^ 6 := by rw [show a ^ 6 = τ₁ ^ 2 by rw [← ha3]; ring]; exact hα_le
  obtain ⟨_, _, _, hDint, hcos, _, _, hin, _, _, hb1, _, hb2⟩ := hC2 hc hτ₁ hτ₁_2 hc_eq hα_le
  have hcancel := hCC hc hτ₁ hτ₁_C hc_eq hα_le ha ha3
  have hτ18 : τ₁ ≤ 1 / 8 := by linarith
  obtain ⟨hm1, -⟩ := hcm_bd τ₁ ⟨hτ₁, hτ18⟩
  have hm2 := hCu_bd τ₁ ⟨hτ₁, hτ18⟩
  have hVP := V.mono hK'K (uctM_pos hτ₁).le
  have e3 : τ₁ ^ 3 = a ^ 9 := by rw [← ha3]; ring
  have hτ2a : τ₁ ^ 2 = a ^ 6 := by rw [← ha3]; ring
  have hCfl : stripCfl kind ≤ 0 := by
    cases kind
    · exact le_rfl
    · show -(π / 2) * uctAlphaOsc ≤ 0
      have := uctAlphaOsc_nonneg
      nlinarith [Real.pi_pos]
  have hz : ∀ {x y : ℝ}, 0 ≤ y → x ≤ C2 * y → x ≤ KK * y := fun hy h => kmono hy h hC2K
  refine ⟨hKK1, hcm, hcmK, hCuK, hflK, ha, ha1, ?_, ?_, kmono (by positivity) hs hK'K, kmono (by positivity) hL1 hK'K,
    kmono (by positivity) hα hK'K, hVP.hPm, hVP.hP0, hVP.hDin, hVP.hDmid, hVP.hDfar, hDint, hCfl, ?_, ?_, hI0K, ?_, ?_, ?_⟩
  · rw [← hτ2a]; exact hm1
  · rw [← hτ2a]; exact hm2
  · refine hz (by positivity) (hcos.trans_eq ?_)
    rw [e3]
  · refine hz (by positivity) (hin.trans_eq ?_)
    rw [show τ₁ ^ 3 + |α| * τ₁ = a ^ 9 + |α| * a ^ 3 by rw [← ha3]; ring]
  · refine hz (by positivity) (hb1.trans_eq ?_)
    rw [hinv, ← ha3]
  · refine hz (by positivity) (hb2.trans_eq ?_)
    have e : τ₁ ^ (-3 : ℤ) = (a⁻¹) ^ 9 := by
      rw [← ha3, show (-3 : ℤ) = -((3 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast, ← pow_mul,
        show 3 * 3 = 9 from rfl, inv_pow]
    rw [zpow_neg_one, hinv, e]
  · exact kmono (by positivity) hcancel hCCK

/-- **`hvac` for the concrete datum** (`fct:physical-budget` parts (a)-(d)): the uniform vacuum integral
`∫ χ(L/3δ_L) γ(L̃)(O − F) dL ≤ A c^{-3/4}` for `O = I_osc^{warp}` built from the concrete datum `P = vacP` (`δ_L = m(c^{-1/4})`,
`Φ = φ_kill(iτ₀(·); c^{-1/12})`, `C_fl = stripCfl`, `I₀ = stripFp1`), with the `fct:comp-D` (2) displays `(fct:cos-pen)`, `(fct:bump-1L)`, `(fct:bump-2L)`
and the finite-part cancellation of `fct:phikill` (3) now *proved* (not part of the hypotheses).  The hypotheses left are the size bounds of the
datum `(s, L₁, α)` (`hsize`) and the definition of `O` on the support of the cutoff (`hO`); the pointwise facts `VacPointwise` (pointwise `(fct:Dstar-inner)`
bounds, `P ≥ 0`, measurability) are now proved (`vacPointwise_concrete`). -/
theorem vacuum_integral_concrete {χ : ℝ → ℝ} (hχ : IsCutoff χ) (kind : StripKernelChoice) {K4 : ℝ} (hK4 : 1 ≤ K4)
    (sf L1f αf : ℝ → ℝ → ℝ) (Of : ℝ → ℝ → ℝ → ℝ)
    (hO : ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → ∀ x : ℝ, 3 / 2 * uctM (c ^ (-(1 / 4 : ℝ))) ≤ x →
      Of ε c x = physOsc (vacP kind K4 c (αf ε c) (c ^ (-(1 / 4 : ℝ)))) (vacPhi (c ^ (-(1 / 12 : ℝ)))) (sf ε c) (L1f ε c) x)
    (hsize : ∃ K c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      |sf ε c| ≤ K * (c ^ (-(1 / 12 : ℝ))) ^ 12 ∧ |L1f ε c| ≤ K * (c ^ (-(1 / 12 : ℝ))) ^ 8 ∧
        |αf ε c| ≤ K * (c ^ (-(1 / 12 : ℝ))) ^ 8)
    :
    ∃ A c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      (∫ x, χ (x / (3 * uctM (c ^ (-(1 / 4 : ℝ))))) * physGamma c (sf ε c) x *
        (Of ε c x - physF (sf ε c) (L1f ε c) x)) ≤ A * c ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨τ₀, hτ₀, hτ₀100, a0, a1, ha0, hK⟩ := vacDisp_concrete kind
  obtain ⟨K, hK1, hKd⟩ := hK K4 hK4
  obtain ⟨Ks, cs, hs⟩ := hsize
  obtain ⟨Kp, τp, hτp, hKp1, hp⟩ := vacPointwise_concrete kind K4 hK4
  set K' : ℝ := max Ks Kp with hK'def
  have hKsK' : Ks ≤ K' := le_max_left _ _
  have hKpK' : Kp ≤ K' := le_max_right _ _
  set M : ℝ := max K' 1 with hMdef
  have hM1 : 1 ≤ M := le_max_right _ _
  have hK'M : K' ≤ M := le_max_left _ _
  have hM0 : 0 < M := by linarith
  refine vacuum_integral_field hχ (fun _ c => uctM (c ^ (-(1 / 4 : ℝ)))) sf L1f Of
    (fun ε c => vacP kind K4 c (αf ε c) (c ^ (-(1 / 4 : ℝ)))) αf (fun _ _ => stripCfl kind) (fun _ _ => stripFp1 kind) hO
    ⟨max K K', a0, a1, max (max cs (τp⁻¹ ^ 4)) (max (τ₀⁻¹ ^ 4) (M ^ 6)), fun ε c hε hc => ?_⟩
  have hcs : cs ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hcp : τp⁻¹ ^ 4 ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hcτ : τ₀⁻¹ ^ 4 ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hcM : M ^ 6 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hcτ
  set a : ℝ := c ^ (-(1 / 12 : ℝ)) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hc0 _
  have hpow : ∀ n : ℕ, a ^ n = c ^ (-((n : ℝ) / 12)) := by
    intro n; rw [ha_def, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; congr 1; ring
  have hc12 : c⁻¹ = a ^ 12 := by rw [hpow 12]; norm_num [Real.rpow_neg_one]
  have ha3 : a ^ 3 = c ^ (-(1 / 4 : ℝ)) := by rw [hpow 3]; norm_num
  set τ₁ : ℝ := c ^ (-(1 / 4 : ℝ)) with hτ₁_def
  have hτ₁ : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hτ4 : τ₁ ^ 4 = c⁻¹ := by
    rw [← ha3, ← pow_mul, show 3 * 4 = 12 from rfl, ← hc12]
  have hc_eq : τ₁ ^ 4 * c = 1 := by rw [hτ4]; field_simp
  have hτ₁_le : τ₁ ≤ τ₀ := by
    have h4 : τ₁ ^ 4 ≤ τ₀ ^ 4 := by
      rw [hτ4, inv_le_comm₀ hc0 (by positivity)]
      simpa [inv_pow] using hcτ
    exact le_of_pow_le_pow_left₀ (by norm_num) hτ₀.le h4
  have hsm : M * a ^ 2 ≤ 1 := by
    have h1 : (a ^ 2 * M) ^ 6 ≤ 1 := by
      have e : (a ^ 2 * M) ^ 6 = c⁻¹ * M ^ 6 := by rw [hc12]; ring
      rw [e, inv_mul_le_iff₀ hc0]; linarith
    have h2 : a ^ 2 * M ≤ 1 := by
      by_contra hlt
      have := one_lt_pow₀ (not_le.mp hlt) (by norm_num : (6 : ℕ) ≠ 0)
      linarith
    nlinarith
  have hτ₁_leP : τ₁ ≤ τp := by
    have h4 : τ₁ ^ 4 ≤ τp ^ 4 := by
      rw [hτ4, inv_le_comm₀ hc0 (by positivity)]
      simpa [inv_pow] using hcp
    exact le_of_pow_le_pow_left₀ (by norm_num) hτp.le h4
  obtain ⟨hs1, hL1, hα⟩ := hs ε c hε hcs
  have hα_le : |αf ε c| ≤ τ₁ ^ 2 := by
    calc |αf ε c| ≤ Ks * a ^ 8 := hα
      _ ≤ M * a ^ 8 := mul_le_mul_of_nonneg_right (hKsK'.trans hK'M) (by positivity)
      _ = (M * a ^ 2) * a ^ 6 := by ring
      _ ≤ 1 * a ^ 6 := mul_le_mul_of_nonneg_right hsm (by positivity)
      _ = τ₁ ^ 2 := by rw [← ha3]; ring
  exact hKd hc0 hτ₁ hτ₁_le hc_eq hα_le ha ha3 (kmono (by positivity) hs1 hKsK') (kmono (by positivity) hL1 hKsK')
    (kmono (by positivity) hα hKsK') ((hp hc0 hτ₁ hτ₁_leP hc_eq hα_le ha ha3).mono hKpK' (uctM_pos hτ₁).le)

/-- info: 'FormalResearch.SignUncertainty.FctSym.vacDisp_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vacDisp_concrete

/-- info: 'FormalResearch.SignUncertainty.FctSym.vacuum_integral_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vacuum_integral_concrete

end FormalResearch.SignUncertainty.FctSym
