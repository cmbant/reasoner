module

public import FormalResearch.SignUncertainty.Headlines
public import FormalResearch.SignUncertainty.HankelWindow
public import FormalResearch.SignUncertainty.HankelChartSecond
public import FormalResearch.SignUncertainty.HankelQuantC1Feasible

/-!
# `hb_thresholds_lower` (`thm:hb-thresholds` lower half at `(P, Q) = (1, 0)`; M5-S7)

For `c` large and either eigenvalue, every feasible threshold satisfies
`T ≥ c/π² + A c^{1/3} - C`, `A = |a₁|/β₁` (`hb_thresholds_lower : HbThresholdsLower`).

Proof (`TE.4` in the form of a direct expansion): normalise `M[f] = 1`.  If `T ≥ cξ(a₁)` the second-order
expansion `hankelXi_lower` at `x = a₁` finishes.  Otherwise `hankel_quantC1_of_feasible` gives the level `u_T`
(`cξ(u_T) = T`, `a₁ < u_T`, `QuantC1B2Holds`), `hankelBootHB` (with the window hypothesis `hankel_yv_at`) gives a
`BootstrapHBInstance`, `teb_bootstrap_hb` gives `c^{1/3}(u_T - a₁) ≤ K₀`, and `hankelXi_lower` at `x = u_T` gives
`T ≥ c/π² + A c^{1/3} - K₀/β₁ - 13`.  The constants are Lean constants (`K₀ = tebK0HB P 0`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap FormalResearch.ModularBootstrap.ConcreteBootstrap

/-- Normalisation: a feasible `f` is a positive multiple of a feasible `g` with `M[g] = 1`. -/
lemma hankel_feasible_normalize {c ε T : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelFeasible c ε T f) :
    ∃ g : ℝ → ℝ, IsHankelFeasible c ε T g ∧ hankelMass c g = 1 := by
  obtain ⟨Δ0, hΔ0, hne⟩ := hf.nonzero
  have hm : 0 < hankelMass c f :=
    hankelMass_pos_of_continuousOn hc hf.cont hf.int ⟨Δ0, hΔ0, hne⟩
  set m := hankelMass c f with hmdef
  have hmi : 0 < m⁻¹ := inv_pos.2 hm
  refine ⟨fun Δ => m⁻¹ * f Δ, ?_, ?_⟩
  · refine ⟨hf.toIsHankelEigenfn.smul m⁻¹, ?_, ?_, ?_⟩
    · exact ⟨Δ0, hΔ0, mul_ne_zero hmi.ne' hne⟩
    · have := hf.origin_sign
      show ε * (m⁻¹ * f 0) ≤ 0
      nlinarith [mul_nonneg hmi.le (neg_nonneg.2 this)]
    · intro Δ hΔ
      exact mul_nonneg hmi.le (hf.tail_nonneg Δ hΔ)
  · rw [hankelMass_smul, abs_of_pos hmi, inv_mul_cancel₀ hm.ne']

/-- `4 r_c r_∞ ≤ 1` for large `c`. -/
lemma hankel_small_eventually : ∀ᶠ c : ℝ in atTop, 4 * langerRadius c * hankelRinf c ≤ 1 := by
  have h := hankelRinf_delta_tendsto.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [h, eventually_gt_atTop 0] with c hc hc0
  have hL := langerRadius_pos hc0
  have h1 : hankelRinf c ≤ |hankelRinf c| := le_abs_self _
  have h2 : 4 * langerRadius c * hankelRinf c ≤ 4 * langerRadius c * |hankelRinf c| :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith [abs_nonneg (hankelRinf c)]

set_option maxHeartbeats 1000000 in
/-- **`hb_thresholds_lower`** (`thm:hb-thresholds` = `u1cl:multilevel`, lower half, `(P, Q) = (1, 0)`; proved):
exactly the skeleton statement `HbThresholdsLower` of `Headlines.lean` (one level, both eigenvalues `ε = ±1`, all real
`c ≥ c₀`, every feasible `T`, no extra hypothesis).  `C = 13 + |K₀|/β₁` and `c₀ = max (10¹⁴, c₁, c₂, tebC2 P)` are
Lean constants independent of `c`, `ε`, `T`, `f` (`K₀ = tebK0HB P 0 ≥ 1`, `P = hankelBootParams hankelWindowC _`;
`c₁` from `hankel_quantC1_of_feasible`, `c₂` from `hankel_small_eventually`).
Inputs: `hankel_quantC1_of_feasible` (type (I) compactness, S5), `hankelBootHB` with `hankel_yv_at` (S6a/S6b) and
`teb_bootstrap_hb` (`TE.2(4)`); the hypothesis `4 r_c r_∞ ≤ 1` of `hankelBootHB` is discharged by
`hankel_small_eventually` (from `hankelRinf_delta_tendsto`), and `-3 ≤ u_T ≤ 0` by `hankelBoot_uT_range`.
**Not used:** `teb_mellin_o1_lower` (`TE.4`) and `RadialCompactness`: no a-priori Airy window for `T` is needed because
`hankel_quantC1_of_feasible` covers every `T < cξ(a₁)`, and the inversion of the chart is `hankelXi_lower`. -/
theorem hb_thresholds_lower : HbThresholdsLower := by
  set P := hankelBootParams hankelWindowC one_le_hankelWindowC with hP
  obtain ⟨c₁, hc₁, hquant⟩ := hankel_quantC1_of_feasible
  obtain ⟨c₂, hc₂⟩ := Filter.eventually_atTop.1 hankel_small_eventually
  set K0 := tebK0HB P 0 with hK0
  have hβ := hankelBeta1_pos
  refine ⟨13 + |K0| / hankelBeta1, max (max (max 1e14 c₁) c₂) (tebC2 P), ?_⟩
  intro c hc ε hε T f hf
  have hc14 : 1e14 ≤ c := ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hc
  have hc1 : c₁ ≤ c := (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hc
  have hc2' : c₂ ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hcT : tebC2 P ≤ c := (le_max_right _ _).trans hc
  have hc0 : 0 < c := by linarith
  have hc3 : 3e6 ≤ c := by linarith
  obtain ⟨g, hg, hgm⟩ := hankel_feasible_normalize hc0 hf
  have hA : airyOrderCoeff = -airyZero 1 / hankelBeta1 := by
    unfold airyOrderCoeff; rw [abs_of_neg (airyZero_neg 1)]
  have ha := airyZero_one
  by_cases hcase : c * hankelXi c (airyZero 1) ≤ T
  · have hlow := hankelXi_lower hc3 (x := airyZero 1) (by rw [abs_of_neg (airyZero_neg 1)]; linarith [ha.1])
    have e : -(airyZero 1) * c ^ (1 / 3 : ℝ) / hankelBeta1 = airyOrderCoeff * c ^ (1 / 3 : ℝ) := by
      rw [hA]; ring
    have hnn : 0 ≤ |K0| / hankelBeta1 := by positivity
    have : c / π ^ 2 - airyZero 1 * c ^ (1 / 3 : ℝ) / hankelBeta1 - 13 ≤ T := hlow.trans hcase
    have e2 : airyZero 1 * c ^ (1 / 3 : ℝ) / hankelBeta1 = -(airyOrderCoeff * c ^ (1 / 3 : ℝ)) := by
      rw [hA]; ring
    rw [e2] at this
    linarith
  · push Not at hcase
    obtain ⟨u_T, ha1, huR, hT, hB2⟩ := hquant c ε T g hc1 hg hε hgm (by
      exact_mod_cast hcase)
    obtain ⟨hu0, hu3⟩ := hankelBoot_uT_range ha1 hB2
    have hc12 : (3 * π) ^ (12 : ℕ) ≤ c := by
      have : 3 * π ≤ 10 := by linarith [Real.pi_lt_d2]
      have h2 : (3 * π) ^ (12 : ℕ) ≤ (10 : ℝ) ^ 12 := pow_le_pow_left₀ (by positivity) this 12
      linarith
    have h48 : 48 ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by
      obtain ⟨t, ht14, hct, hk4, hK8, -⟩ := hankel_window_cnum hc14
      rw [hK8]
      have : (14 : ℝ) ^ 8 ≤ t ^ 8 := pow_le_pow_left₀ (by norm_num) ht14 8
      norm_num at this ⊢
      linarith
    have hsm := hc₂ c hc2'
    let I := hankelBootHB one_le_hankelWindowC hankel_yv_at (c := c) hc14 hc3 hc12 h48 hg hε hgm hT ha1 hB2 hsm
    obtain ⟨hL, hIc, hIx⟩ := I.2
    have hcI : tebC2 P ≤ I.1.c := by rw [hIc]; exact hcT
    have hboot := (teb_bootstrap_hb P I.1 hcI).2 hL
    have hK : c ^ (1 / 3 : ℝ) * (u_T - airyZero 1) ≤ K0 := by
      have := hboot.2
      rw [hIc, hIx] at this
      exact this
    have hlow := hankelXi_lower hc3 (x := u_T) (by
      rw [abs_le]; constructor <;> linarith [ha.1])
    have hTe : c * hankelXi c u_T = T := hT
    have hk0 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    have h1 : u_T * c ^ (1 / 3 : ℝ) ≤ airyZero 1 * c ^ (1 / 3 : ℝ) + K0 := by linarith
    have h2 : u_T * c ^ (1 / 3 : ℝ) / hankelBeta1 ≤
        (airyZero 1 * c ^ (1 / 3 : ℝ) + K0) / hankelBeta1 := by gcongr
    have h3 : (airyZero 1 * c ^ (1 / 3 : ℝ) + K0) / hankelBeta1 =
        airyZero 1 * c ^ (1 / 3 : ℝ) / hankelBeta1 + K0 / hankelBeta1 := by ring
    have h4 : K0 / hankelBeta1 ≤ |K0| / hankelBeta1 := by gcongr; exact le_abs_self K0
    have e2 : airyZero 1 * c ^ (1 / 3 : ℝ) / hankelBeta1 = -(airyOrderCoeff * c ^ (1 / 3 : ℝ)) := by
      rw [hA]; ring
    rw [e2] at h3
    linarith

/-- info: 'FormalResearch.SignUncertainty.hb_thresholds_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hb_thresholds_lower

/-- info: 'FormalResearch.SignUncertainty.hankel_feasible_normalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_feasible_normalize

/-- info: 'FormalResearch.SignUncertainty.hankel_small_eventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_small_eventually

end FormalResearch.SignUncertainty
