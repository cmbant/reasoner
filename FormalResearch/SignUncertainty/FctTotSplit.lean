/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctMainHankelDefs
public import FormalResearch.SignUncertainty.UctPosFloor
public import FormalResearch.SignUncertainty.UctBumpMain
public import FormalResearch.SignUncertainty.UctBumpRefl

/-!
# Linear decomposition of `admissF c (ctWtot ...)` and exact matches for `ctWfl`, `ctWbump` (Step 2)

For `c ≥ 2` and `ξ > 0` (`Δ = c ξ`), defines the normalised density

`normDensity W c ξ = (c^{1/3} / (2π)) * Re ∫ K₀(iτ, ξ) W(iτ) dτ`

and proves:
* `normDensity_eq_admissF`: `normDensity W c ξ = c^{1/3} ξ ρ₀(cξ) f_W(cξ)` for `StripAdmissData (1/2) W`;
* `nonneg_admissF_iff_normDensity`: `0 ≤ f_W(cξ) ↔ 0 ≤ normDensity W c ξ`;
* `normDensity_ctWtot`: linear split over `ctWwarp`, `ctWg1`, `ctWfl`, `ctWbump`;
* `normDensity_ctWbump`: exact identity `normDensity (ctWbump B ε c) c ξ = Re(bumpHmain c B ξ + ε bumpHrefl c B ξ)`;
* `normDensity_ctWfl_floor`: exact match to `uct_pos_floor_lift`, yielding `Kfl ≥ 1` and the floor lower bound
  `0 ≤ normDensity (ctWfl Kfl ε c) c ξ` everywhere on `-U ≤ hbS c ξ`, and `≥ (cfl / 2) (1 + max (hbS c ξ) 0)^{-3/2}`.

Class: proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real
open FormalResearch.CohnElkies

namespace FormalResearch.SignUncertainty

/-- The normalised density `h_norm[W](L) = (c^{1/3} / 2π) Re ∫ K₀(iτ, ξ) W(iτ) dτ` (`ξ = e^L / π²`). -/
noncomputable def normDensity (W : ℂ → ℂ) (c ξ : ℝ) : ℝ :=
  (c ^ (1 / 3 : ℝ) / (2 * Real.pi)) *
    (∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * W ((τ : ℂ) * Complex.I)).re

section Basic

lemma admiss_edge0_integrable {W : ℂ → ℂ} {c ξ : ℝ} (hc : 1 ≤ c) (hξ : 0 < ξ)
    (hW : StripAdmissFullData (1 / 2) W) :
    Integrable (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * W ((τ : ℂ) * Complex.I)) := by
  have h := admiss_vert_integrable_of_W1 hc (by norm_num : (0 : ℝ) < 3 / 2) hW.toStripM1.toStripW1
    (σ := 0) le_rfl one_pos hξ
  simpa using h

lemma normDensity_eq_admissF {W : ℂ → ℂ} {c ξ : ℝ} (hc : 2 ≤ c) (hξ : 0 < ξ)
    (hW : StripAdmissData (1 / 2) W) :
    normDensity W c ξ = c ^ (1 / 3 : ℝ) * ξ * (hankelRho0 c (c * ξ) * admissF c W (c * ξ)) := by
  have hv := (uct_admiss hc (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hW).2.2.2.2.2.1 ξ hξ 0 le_rfl one_pos
  have hv' := congrArg Complex.re hv
  simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] at hv'
  have hpt : (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * W ((τ : ℂ) * Complex.I)) =
      fun τ : ℝ => mellinK0 c (Complex.I * (τ : ℂ)) ξ * W (Complex.I * (τ : ℂ)) := by
    funext τ; rw [mul_comm (τ : ℂ) Complex.I]
  unfold normDensity
  rw [hpt, hv']
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hξ0 : ξ ≠ 0 := hξ.ne'
  field_simp

lemma nonneg_admissF_iff_normDensity {W : ℂ → ℂ} {c ξ : ℝ} (hc : 2 ≤ c) (hξ : 0 < ξ)
    (hW : StripAdmissData (1 / 2) W) :
    0 ≤ admissF c W (c * ξ) ↔ 0 ≤ normDensity W c ξ := by
  rw [normDensity_eq_admissF hc hξ hW]
  have hc0 : 0 < c := by linarith
  have hΔ : 0 < c * ξ := mul_pos hc0 hξ
  have hr : 0 < hankelRho0 c (c * ξ) := by
    unfold hankelRho0
    have := Real.Gamma_pos_of_pos hc0
    have := Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi) c
    have := Real.rpow_pos_of_pos hΔ (c - 1)
    positivity
  have hpref : 0 < c ^ (1 / 3 : ℝ) * ξ * hankelRho0 c (c * ξ) := by
    have := Real.rpow_pos_of_pos hc0 (1 / 3 : ℝ)
    positivity
  have e : c ^ (1 / 3 : ℝ) * ξ * (hankelRho0 c (c * ξ) * admissF c W (c * ξ)) =
      (c ^ (1 / 3 : ℝ) * ξ * hankelRho0 c (c * ξ)) * admissF c W (c * ξ) := by ring
  rw [e]
  exact ⟨fun h => mul_nonneg hpref.le h, fun h => nonneg_of_mul_nonneg_right h hpref⟩

lemma normDensity_add {W1 W2 : ℂ → ℂ} {c ξ : ℝ} (hc : 1 ≤ c) (hξ : 0 < ξ)
    (h1 : StripAdmissFullData (1 / 2) W1) (h2 : StripAdmissFullData (1 / 2) W2) :
    normDensity (fun ζ => W1 ζ + W2 ζ) c ξ = normDensity W1 c ξ + normDensity W2 c ξ := by
  have i1 := admiss_edge0_integrable hc hξ h1
  have i2 := admiss_edge0_integrable hc hξ h2
  unfold normDensity
  have hpt : (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * (W1 ((τ : ℂ) * Complex.I) + W2 ((τ : ℂ) * Complex.I))) =
      fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * W1 ((τ : ℂ) * Complex.I) +
        mellinK0 c ((τ : ℂ) * Complex.I) ξ * W2 ((τ : ℂ) * Complex.I) := by
    funext τ; ring
  rw [hpt, integral_add i1 i2, Complex.add_re]
  ring

lemma normDensity_smul_real (a : ℝ) (W : ℂ → ℂ) (c ξ : ℝ) :
    normDensity (fun ζ => (a : ℂ) * W ζ) c ξ = a * normDensity W c ξ := by
  unfold normDensity
  have hpt : (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * ((a : ℂ) * W ((τ : ℂ) * Complex.I))) =
      fun τ : ℝ => (a : ℂ) * (mellinK0 c ((τ : ℂ) * Complex.I) ξ * W ((τ : ℂ) * Complex.I)) := by
    funext τ; ring
  rw [hpt, integral_const_mul, Complex.re_ofReal_mul]
  ring

lemma normDensity_ctWtot (PhiHat D : ℝ → ℝ → ℂ → ℂ) (B : ℝ → ℝ → ℝ → ℝ → ℝ) {ε c Kfl K0 K1 Kd ξ : ℝ}
    (hc : 1 ≤ c) (hξ : 0 < ξ)
    (hwarp : StripAdmissFullData (1 / 2) (ctWwarp PhiHat D ε c))
    (hg : StripAdmissFullData (1 / 2) (ctWg1 ε c))
    (hfl : StripAdmissFullData (1 / 2) (ctWfl Kfl ε c))
    (hb : StripAdmissFullData (1 / 2) (ctWbump (B ε c K1) ε c)) :
    normDensity (ctWtot PhiHat D B ε c Kfl K0 K1 Kd) c ξ =
      normDensity (ctWwarp PhiHat D ε c) c ξ -
        Kd * c ^ (-(13 / 12 : ℝ)) * normDensity (ctWg1 ε c) c ξ +
        K0 * c ^ (-(4 / 3 : ℝ)) * normDensity (ctWfl Kfl ε c) c ξ +
        normDensity (ctWbump (B ε c K1) ε c) c ξ := by
  have hg' := hg.smul_real (-(Kd * c ^ (-(13 / 12 : ℝ))))
  have hfl' := hfl.smul_real (K0 * c ^ (-(4 / 3 : ℝ)))
  have h12 := hwarp.add hg'
  have h123 := h12.add hfl'
  have hcongr : ctWtot PhiHat D B ε c Kfl K0 K1 Kd = fun ζ =>
      ((ctWwarp PhiHat D ε c ζ + ((-(Kd * c ^ (-(13 / 12 : ℝ))) : ℝ) : ℂ) * ctWg1 ε c ζ) +
        ((K0 * c ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * ctWfl Kfl ε c ζ) + ctWbump (B ε c K1) ε c ζ := by
    funext ζ
    unfold ctWtot
    push_cast
    ring
  rw [hcongr, normDensity_add hc hξ h123 hb, normDensity_add hc hξ h12 hfl', normDensity_add hc hξ hwarp hg',
    normDensity_smul_real, normDensity_smul_real]
  ring

end Basic

section BumpMatch

lemma bumpDW_edge_integrable {B : ℝ → ℝ} {δ M α β c ξ : ℝ} {K : ℕ → ℝ}
    (hc : 1 ≤ c) (hδ0 : 0 < δ) (hδ1 : 3 / 2 * δ ≤ 1) (hβ : 3 / 2 ≤ β) (hM : 0 ≤ M) (hξ : 0 < ξ)
    (hB : BumpProfile (3 / 2) δ M α β K B) :
    Integrable (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B ((τ : ℂ) * Complex.I)) := by
  have hc0 : 0 < c := by linarith
  have h := bump_stripAdmissFull (b := 3 / 2) (by norm_num) hβ K hδ0 (by linarith) hδ1 hM hc0 hB
  exact admiss_edge0_integrable hc hξ h

lemma normDensity_ctWbump {B : ℝ → ℝ} {δ M α β c ε ξ : ℝ} {K : ℕ → ℝ}
    (hc : 1 ≤ c) (hδ0 : 0 < δ) (hδ1 : 3 / 2 * δ ≤ 1) (hβ : 3 / 2 ≤ β) (hM : 0 ≤ M) (hξ : 0 < ξ)
    (hB : BumpProfile (3 / 2) δ M α β K B) :
    normDensity (ctWbump B ε c) c ξ = (bumpHmain c B ξ + (ε : ℂ) * bumpHrefl c B ξ).re := by
  have hc0 : 0 < c := by linarith
  have h1 := bumpDW_edge_integrable hc hδ0 hδ1 hβ hM hξ hB
  have hadm := (bump_stripAdmissFull (b := 3 / 2) (by norm_num) hβ K hδ0 (by linarith) hδ1 hM hc0 hB).reflect
  have h2 : Integrable (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B (1 - (τ : ℂ) * Complex.I)) :=
    admiss_edge0_integrable hc hξ hadm
  have h2' := h2.const_mul (ε : ℂ)
  have hcongr : (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * ctWbump B ε c ((τ : ℂ) * Complex.I)) =
      fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B ((τ : ℂ) * Complex.I) +
        (ε : ℂ) * (mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B (1 - (τ : ℂ) * Complex.I)) := by
    funext τ; unfold ctWbump; ring
  unfold normDensity bumpHmain bumpHrefl
  rw [hcongr, integral_add h1 h2', integral_const_mul]
  have e : ((c ^ (1 / 3 : ℝ) / (2 * Real.pi) : ℝ) : ℂ) *
      ((∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B ((τ : ℂ) * Complex.I)) +
        (ε : ℂ) * ∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B (1 - (τ : ℂ) * Complex.I)) =
      ((c ^ (1 / 3 : ℝ) / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B ((τ : ℂ) * Complex.I)) +
      (ε : ℂ) * (((c ^ (1 / 3 : ℝ) / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B (1 - (τ : ℂ) * Complex.I)) := by ring
  have hre := congrArg Complex.re e
  simpa only [Complex.re_ofReal_mul] using hre

end BumpMatch

section FloorMatch

private lemma admissPhi_ctWfl_eq {K ε c : ℝ} (hc : 0 < c) :
    admissPhi c (ctWfl K ε c) = liftPhi (liftSymbol uctSpos (ceBeta1 * K * liftEps c / 2) 4) c ε := by
  funext z
  unfold admissPhi admissG liftPhi liftS ctWfl
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have e1 : (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - z / (c : ℂ))) = ((c : ℂ) - z) / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) := by
    have hsplit : c = c ^ (1 / 3 : ℝ) * c ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_add hc]; norm_num
    have h13 : ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.rpow_pos_of_pos hc _).ne'
    have h23 : ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.rpow_pos_of_pos hc _).ne'
    have hsplitC : (c : ℂ) = ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) := by
      exact_mod_cast hsplit
    rw [eq_div_iff h23]
    calc (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - z / (c : ℂ))) * ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ)
        = (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ)) * (1 - z / (c : ℂ)) := by ring
      _ = (c : ℂ) * (1 - z / (c : ℂ)) := by rw [← hsplitC]
      _ = (c : ℂ) - z := by field_simp
  have e2 : (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (z / (c : ℂ))) = z / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) := by
    have hsplit : c = c ^ (1 / 3 : ℝ) * c ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_add hc]; norm_num
    have h23 : ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.rpow_pos_of_pos hc _).ne'
    have hsplitC : (c : ℂ) = ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) := by
      exact_mod_cast hsplit
    rw [eq_div_iff h23]
    calc (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (z / (c : ℂ))) * ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ)
        = (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ)) * (z / (c : ℂ)) := by ring
      _ = (c : ℂ) * (z / (c : ℂ)) := by rw [← hsplitC]
      _ = z := by field_simp
  have e3 : 1 - (1 - z / (c : ℂ)) = z / (c : ℂ) := by ring
  rw [e3, e1, e2]

theorem normDensity_ctWfl_eq_iMain_iDual {K ε c ξ : ℝ} (hK : 0 < K) (hc : 8 ≤ c) (hξ : 0 < ξ)
    (hε : ε = 1 ∨ ε = -1) :
    normDensity (ctWfl K ε c) c ξ =
      ξ * (iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ +
        (ε : ℂ) * iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ).re := by
  have hc0 : 0 < c := by linarith
  have hc2 : 2 ≤ c := by linarith
  have hadm := (ctWfl_stripAdmissFull hK ε hc).toStripAdmissData
  rw [normDensity_eq_admissF hc2 hξ hadm]
  have hFL : admissF c (ctWfl K ε c) (c * ξ) =
      liftFun (liftPhi (liftSymbol uctSpos (ceBeta1 * K * liftEps c / 2) 4) c ε) (c / 2) (c * ξ) := by
    have hpos : c * ξ ≠ 0 := (mul_pos hc0 hξ).ne'
    simp only [admissF, hpos, ↓reduceIte, admissLift, admissPhi_ctWfl_eq hc0]
  rw [hFL]
  have hX := hasU2_uctSpos
  have hδ : 0 ≤ ceBeta1 * K * liftEps c / 2 := by
    have := ceBeta1_pos; have := liftEps_pos hc0; positivity
  have hrepr := lift_edge_repr hX hδ 4 (by linarith : (3 / 2 : ℝ) < c) hε hξ
  have hre := congrArg Complex.re hrepr
  simp only [Complex.ofReal_re] at hre
  rw [← hre]
  ring

/-- Floor parameter `K_* ≥ 1` and universal positivity/floor bounds for `normDensity (ctWfl K_* ε c) c ξ`,
uniform on `hbS c ξ ≥ -U` (any `U ≥ 1`), from `uct_pos_floor_lift`. -/
theorem normDensity_ctWfl_floor :
    ∃ Kfl : ℝ, 1 ≤ Kfl ∧ ∀ U : ℝ, 1 ≤ U → ∃ cfl c₀ : ℝ, 0 < cfl ∧ 8 ≤ c₀ ∧
      ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → ∀ ξ : ℝ, 0 < ξ → -U ≤ hbS c ξ →
        (1 / 2 * cfl * (1 + max (hbS c ξ) 0) ^ (-(3 / 2 : ℝ)) ≤ normDensity (ctWfl Kfl ε c) c ξ ∧
          0 ≤ normDensity (ctWfl Kfl ε c) c ξ) := by
  obtain ⟨Kst, hKst, _, _, hfl⟩ := uct_pos_floor_lift
  refine ⟨Kst, hKst, fun U hU => ?_⟩
  obtain ⟨cfl, hcfl, hflK⟩ := hfl U hU
  obtain ⟨c₀, hc₀⟩ := hflK Kst le_rfl
  refine ⟨cfl, max c₀ 8, hcfl, le_max_right _ _, fun ε c hε hc ξ hξ hUξ => ?_⟩
  obtain ⟨f, _, hrep, hlb, _⟩ := hc₀ c ((le_max_left _ _).trans hc) ε hε
  have hm := normDensity_ctWfl_eq_iMain_iDual (by linarith : 0 < Kst) ((le_max_right _ _).trans hc) hξ hε
  have hre := congrArg Complex.re (hrep ξ hξ)
  simp only [Complex.ofReal_re] at hre
  have heq : normDensity (ctWfl Kst ε c) c ξ = ξ * (c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * f (c * ξ)) := by
    rw [hm, ← hre]
  have hlow := hlb ξ hξ hUξ
  rw [← heq] at hlow
  have hnn : 0 ≤ 1 / 2 * cfl * (1 + max (hbS c ξ) 0) ^ (-(3 / 2 : ℝ)) := by
    have : 0 ≤ 1 + max (hbS c ξ) 0 := by linarith [le_max_right (hbS c ξ) 0]
    positivity
  exact ⟨hlow, hnn.trans hlow⟩

end FloorMatch

/-- info: 'FormalResearch.SignUncertainty.normDensity_ctWtot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normDensity_ctWtot

/-- info: 'FormalResearch.SignUncertainty.normDensity_ctWbump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normDensity_ctWbump

/-- info: 'FormalResearch.SignUncertainty.normDensity_ctWfl_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normDensity_ctWfl_floor

end FormalResearch.SignUncertainty
