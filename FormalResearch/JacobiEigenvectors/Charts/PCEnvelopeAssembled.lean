module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.PCActual
public import FormalResearch.JacobiEigenvectors.Charts.PCPositive
public import FormalResearch.JacobiEigenvectors.Charts.PCEnergyWell
public import FormalResearch.JacobiEigenvectors.Charts.PCEnergyAiryEnv
public import FormalResearch.JacobiEigenvectors.Charts.PCEnvWellFar
public import FormalResearch.JacobiEigenvectors.Charts.PCEnvCompact
public import FormalResearch.JacobiEigenvectors.Charts.PCEnvBar
public import FormalResearch.JacobiEigenvectors.Charts.PCMolv
public import FormalResearch.JacobiEigenvectors.Charts.PCBeyond

/-!
# Paper J, Layer 4: Assembling `PCEnvelopeFacts` and `ParabolicCylinderFacts` for `pcU, pcV`

This module assembles all banked Layer-4 envelope results for the actual parabolic-cylinder
functions `pcU, pcV` unconditionally into `PCEnvelopeFacts pcU pcV cPC CPC` (`pcEnvelopeFacts`)
and `ParabolicCylinderFacts pcU pcV cPC CPC` (`parabolicCylinderFacts`).

## What is proved here
* `pc_env_well`: `env_well` for all `a ≤ 0` and `0 ≤ z` with a single absolute constant, combining
  `env_well_on_Icc_U_V` (`Charts/PCEnergyWell.lean`), `env_well_on_airy_U_V` (`Charts/PCEnergyAiryEnv.lean`),
  `env_well_far_U_V` (`Charts/PCEnvWellFar.lean`) for `a ≤ -4`, and `pc_env_well_compact` (`Charts/PCEnvCompact.lean`)
  for `-4 < a ≤ 0`.
* `pc_env_bar`: `env_bar` for all `a > 0` and all `z : ℝ` with a single absolute constant, combining
  `pc_env_bar_ge_one` (`Charts/PCEnvBar.lean`) and `pc_env_bar_compact` (`Charts/PCEnvCompact.lean`).
* `pc_molv_well`, `pc_molv_bar`: two-sided `Molv` bounds from `Charts/PCMolv.lean`.
* `pc_beyond`: both conjuncts of `beyond` for `z ≥ 2 * sqrt(max(-a, 0))`, combining
  `pcU_beyond_deriv_abs` (`Charts/PCBeyond.lean`) with `pc_molv_well` / `pc_molv_bar`.
* `pcEnvelopeFacts`, `parabolicCylinderFacts`: full unconditional assembly (`V_growth` is not
  needed by `PCEnvelopeFacts` or Layers 2–3; far-region `pcV` growth is proved in `Charts/PCVFarGrowth.lean`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Set Real

private lemma ewell_pos (a z : ℝ) : 0 < Ewell a z := by
  unfold Ewell
  split_ifs
  · exact Real.exp_pos _
  · exact one_pos

private lemma ebar_pos (a z : ℝ) : 0 < Ebar a z := by
  unfold Ebar
  exact Real.exp_pos _

private lemma wwell_pos (a z : ℝ) : 0 < Wwell a z := by
  unfold Wwell
  split_ifs
  · exact ewell_pos a z
  · exact inv_pos.mpr (ewell_pos a |z|)

/-- **`env_well` for `pcU, pcV` for all `a ≤ 0`, `z ≥ 0` with one absolute constant.**
Combines the three-zone estimates for `a ≤ -4` (`PCEnergyWell`, `PCEnergyAiryEnv`, `PCEnvWellFar`)
with the compact-parameter estimate for `-4 < a ≤ 0` (`PCEnvCompact`). -/
theorem pc_env_well : ∃ C : ℝ, 0 < C ∧ ∀ a ≤ 0, ∀ z, 0 ≤ z →
    Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) ≤
      C * Ewell a z * Mbal a z ∧
    Real.sqrt (vt pcV a z ^ 2 + (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z) ≤
      C * (Ewell a z)⁻¹ * Mbal a z := by
  obtain ⟨C1, hC1_pos, hC1⟩ := pc_env_well_compact
  refine ⟨max C1 (Real.exp 54), lt_of_lt_of_le (Real.exp_pos 54) (le_max_right _ _),
    fun a ha0 z hz0 => ?_⟩
  have hE_nn : 0 ≤ Ewell a z := (ewell_pos a z).le
  have hEi_nn : 0 ≤ (Ewell a z)⁻¹ := inv_nonneg.mpr hE_nn
  have hM_nn : 0 ≤ Mbal a z := (Mbal_pos a z).le
  have hEM_nn : 0 ≤ Ewell a z * Mbal a z := mul_nonneg hE_nn hM_nn
  have hEiM_nn : 0 ≤ (Ewell a z)⁻¹ * Mbal a z := mul_nonneg hEi_nn hM_nn
  rcases lt_or_ge (-4) a with ha_gt | ha_le
  · obtain ⟨hU, hV⟩ := hC1 a ha_gt ha0 z hz0
    have hle : C1 ≤ max C1 (Real.exp 54) := le_max_left _ _
    exact ⟨hU.trans (by rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hle hEM_nn),
      hV.trans (by rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hle hEiM_nn)⟩
  · have h54 : Real.exp 54 ≤ max C1 (Real.exp 54) := le_max_right _ _
    rcases le_or_gt z (z1Well a) with hz1 | hz1
    · obtain ⟨⟨_, hU⟩, ⟨_, hV⟩⟩ := env_well_on_Icc_U_V ha_le hz0 hz1
      have h117 : (117 : ℝ) / 50 ≤ Real.exp 54 := by
        linarith [Real.add_one_le_exp (54 : ℝ)]
      have hle : (117 : ℝ) / 50 ≤ max C1 (Real.exp 54) := h117.trans h54
      exact ⟨hU.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hle hEM_nn),
        hV.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hle hEiM_nn)⟩
    · rcases le_or_gt z (z2Airy a) with hz2 | hz2
      · obtain ⟨⟨_, hU⟩, ⟨_, hV⟩⟩ := env_well_on_airy_U_V ha_le hz1.le hz2
        have h14 : Real.exp 14 ≤ Real.exp 54 := Real.exp_le_exp.mpr (by norm_num)
        have hle : Real.exp 14 ≤ max C1 (Real.exp 54) := h14.trans h54
        exact ⟨hU.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hle hEM_nn),
          hV.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hle hEiM_nn)⟩
      · obtain ⟨⟨_, hU⟩, ⟨_, hV⟩⟩ := env_well_far_U_V ha_le hz2.le
        exact ⟨hU.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_right h54 hEM_nn),
          hV.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_right h54 hEiM_nn)⟩

/-- **`env_bar` for `pcU` for all `a > 0`, `z : ℝ` with one absolute constant.**
Combines `pc_env_bar_ge_one` (`a ≥ 1`, `PCEnvBar`) and `pc_env_bar_compact` (`0 < a < 1`, `PCEnvCompact`). -/
theorem pc_env_bar : ∃ C : ℝ, 0 < C ∧ ∀ a, 0 < a → ∀ z,
    Real.sqrt ((kappaBal a * pcU a z) ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) ≤
      C * Ebar a z * Mbal a z ∧
    Real.sqrt ((kappaBal a * pcU a (-z)) ^ 2 + (kappaBal a * deriv (fun w => pcU a (-w)) z) ^ 2 / k2 a z) ≤
      C * (Ebar a z)⁻¹ * Mbal a z := by
  obtain ⟨C1, hC1_pos, hC1⟩ := pc_env_bar_ge_one
  obtain ⟨C2, hC2_pos, hC2⟩ := pc_env_bar_compact
  refine ⟨max C1 C2, lt_of_lt_of_le hC1_pos (le_max_left _ _), fun a ha z => ?_⟩
  have hE_nn : 0 ≤ Ebar a z := (ebar_pos a z).le
  have hEi_nn : 0 ≤ (Ebar a z)⁻¹ := inv_nonneg.mpr hE_nn
  have hM_nn : 0 ≤ Mbal a z := (Mbal_pos a z).le
  have hEM_nn : 0 ≤ Ebar a z * Mbal a z := mul_nonneg hE_nn hM_nn
  have hEiM_nn : 0 ≤ (Ebar a z)⁻¹ * Mbal a z := mul_nonneg hEi_nn hM_nn
  rcases lt_or_ge a 1 with ha1 | ha1
  · obtain ⟨h1, h2⟩ := hC2 a ha ha1 z
    have hle : C2 ≤ max C1 C2 := le_max_right _ _
    exact ⟨h1.trans (by rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hle hEM_nn),
      h2.trans (by rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hle hEiM_nn)⟩
  · obtain ⟨h1, h2⟩ := hC1 a ha1 z
    have hle : C1 ≤ max C1 C2 := le_max_left _ _
    exact ⟨h1.trans (by rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hle hEM_nn),
      h2.trans (by rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hle hEiM_nn)⟩

/-- **`molv_well` for `pcU, pcV` for all `a ≤ 0`, `z : ℝ`.**
Derived from `pc_env_well` via `molv_well_of_env_well` (`Charts/PCMolv.lean`). -/
theorem pc_molv_well : ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ a ≤ 0, ∀ z,
    c * (kappaBal a)⁻¹ * Wwell a z * Mbal a z ≤ Molv pcU pcV a z ∧
    Molv pcU pcV a z ≤ C * (kappaBal a)⁻¹ * Wwell a z * Mbal a z := by
  obtain ⟨C_w, hC_w_pos, h_well⟩ := pc_env_well
  let c := 1 / (C_w * Real.sqrt (Real.pi / 2))
  let C := Real.sqrt ((1 + Real.sqrt (2 / Real.pi)) ^ 2 + 2 / Real.pi) * C_w
  have hc_pos : 0 < c := by dsimp [c]; positivity
  have hC_pos : 0 < C := by dsimp [C]; positivity
  have h_mw := molv_well_of_env_well hC_w_pos h_well
  refine ⟨min c C, C, lt_min hc_pos hC_pos, min_le_right _ _, fun a ha z => ?_⟩
  obtain ⟨hlb, hub⟩ := h_mw a ha z
  have hcoeff : 0 ≤ (kappaBal a)⁻¹ * Wwell a z * Mbal a z :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr (kappaBal_pos a).le) (wwell_pos a z).le) (Mbal_pos a z).le
  refine ⟨?_, hub⟩
  calc min c C * (kappaBal a)⁻¹ * Wwell a z * Mbal a z
      = min c C * ((kappaBal a)⁻¹ * Wwell a z * Mbal a z) := by ring
    _ ≤ c * ((kappaBal a)⁻¹ * Wwell a z * Mbal a z) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hcoeff
    _ = c * (kappaBal a)⁻¹ * Wwell a z * Mbal a z := by ring
    _ ≤ Molv pcU pcV a z := hlb

/-- **`molv_bar` for `pcU, pcV` for all `a > 0`, `z : ℝ`.**
Derived from `pc_env_bar` via `molv_bar_of_env_bar` (`Charts/PCMolv.lean`). -/
theorem pc_molv_bar : ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ a, 0 < a → ∀ z,
    c * (kappaBal a)⁻¹ * Ebar a z * Mbal a z ≤ Molv pcU pcV a z ∧
    Molv pcU pcV a z ≤ C * (kappaBal a)⁻¹ * Ebar a z * Mbal a z := by
  obtain ⟨C_b, hC_b_pos, h_bar⟩ := pc_env_bar
  let c := 1 / C_b
  have hc_pos : 0 < c := by dsimp [c]; positivity
  have h_mb := molv_bar_of_env_bar hC_b_pos h_bar
  refine ⟨min c C_b, C_b, lt_min hc_pos hC_b_pos, min_le_right _ _, fun a ha z => ?_⟩
  obtain ⟨hlb, hub⟩ := h_mb a ha z
  have hcoeff : 0 ≤ (kappaBal a)⁻¹ * Ebar a z * Mbal a z :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr (kappaBal_pos a).le) (ebar_pos a z).le) (Mbal_pos a z).le
  refine ⟨?_, hub⟩
  calc min c C_b * (kappaBal a)⁻¹ * Ebar a z * Mbal a z
      = min c C_b * ((kappaBal a)⁻¹ * Ebar a z * Mbal a z) := by ring
    _ ≤ c * ((kappaBal a)⁻¹ * Ebar a z * Mbal a z) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hcoeff
    _ = c * (kappaBal a)⁻¹ * Ebar a z * Mbal a z := by ring
    _ ≤ Molv pcU pcV a z := hlb

/-- **`beyond` second conjunct derived from `molv_well`, `molv_bar`, and `pcU_beyond_deriv_abs`.**
Holds for any `c > 0` that is a valid lower constant for both `molv_well` and `molv_bar`. -/
theorem pc_beyond_of_molv {c : ℝ}
    (hmw : ∀ a ≤ 0, ∀ z, c * (kappaBal a)⁻¹ * Wwell a z * Mbal a z ≤ Molv pcU pcV a z)
    (hmb : ∀ a, 0 < a → ∀ z, c * (kappaBal a)⁻¹ * Ebar a z * Mbal a z ≤ Molv pcU pcV a z) :
    ∀ a z, 2 * Real.sqrt (max (-a) 0) ≤ z →
      |deriv (pcU a) z| ≤ 4 * Real.sqrt (k2 a z) * |pcU a z| ∧
      c / Real.sqrt 17 * Erec a z * Mbal a z ≤ |kappaBal a * pcU a z| := by
  intro a z hz
  have hderiv := pcU_beyond_deriv_abs a z hz
  refine ⟨hderiv, ?_⟩
  have hz0 : 0 ≤ z := le_trans (by positivity) hz
  have hk_pos : 0 < k2 a z := k2_pos a z
  have hκ_pos : 0 < kappaBal a := kappaBal_pos a
  -- Step 1: `Molv pcU pcV a z = sqrt (U^2 + U'^2 / k2)` since `0 ≤ z`
  have hMolv_eq : Molv pcU pcV a z = Real.sqrt (pcU a z ^ 2 + deriv (pcU a) z ^ 2 / k2 a z) := by
    unfold Molv
    exact ite_eq_left_iff.mpr (fun h => absurd (Or.inl hz0) h)
  -- Step 2: `Molv pcU pcV a z ≤ sqrt 17 * |pcU a z|` from `|U'| ≤ 4 sqrt(k2) |U|`
  have hsq : deriv (pcU a) z ^ 2 ≤ (4 * Real.sqrt (k2 a z) * |pcU a z|) ^ 2 := by
    rw [← sq_abs (deriv (pcU a) z)]
    exact sq_le_sq' (by linarith [abs_nonneg (deriv (pcU a) z), hderiv]) hderiv
  have hsq' : deriv (pcU a) z ^ 2 / k2 a z ≤ 16 * pcU a z ^ 2 := by
    have h4 : (4 * Real.sqrt (k2 a z) * |pcU a z|) ^ 2 = 16 * k2 a z * pcU a z ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hk_pos.le, sq_abs]
      norm_num
    rw [h4] at hsq
    rw [div_le_iff₀ hk_pos]
    linarith
  have hMolv_le : Molv pcU pcV a z ≤ Real.sqrt 17 * |pcU a z| := by
    rw [hMolv_eq]
    calc Real.sqrt (pcU a z ^ 2 + deriv (pcU a) z ^ 2 / k2 a z)
        ≤ Real.sqrt (17 * pcU a z ^ 2) := Real.sqrt_le_sqrt (by linarith)
      _ = Real.sqrt 17 * |pcU a z| := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq_eq_abs]
  -- Step 3: `c * (kappaBal a)⁻¹ * Erec a z * Mbal a z ≤ Molv pcU pcV a z`
  have hMolv_lb : c * (kappaBal a)⁻¹ * Erec a z * Mbal a z ≤ Molv pcU pcV a z := by
    rcases le_or_gt a 0 with ha | ha
    · have hW : Wwell a z = Ewell a z := ite_eq_left_iff.mpr (fun h => absurd hz0 h)
      have hE : Erec a z = Ewell a z := by
        unfold Erec
        rw [ite_eq_left_iff.mpr (fun h => absurd ha h), abs_of_nonneg hz0]
      rw [hE, ← hW]
      exact hmw a ha z
    · have hE : Erec a z = Ebar a z := ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr ha))
      rw [hE]
      exact hmb a ha z
  -- Step 4: Multiply by `kappaBal a > 0` and divide by `sqrt 17 > 0`
  have hmul : c * Erec a z * Mbal a z ≤ Real.sqrt 17 * |kappaBal a * pcU a z| := by
    have h1 := mul_le_mul_of_nonneg_left (hMolv_lb.trans hMolv_le) hκ_pos.le
    have hLHS : kappaBal a * (c * (kappaBal a)⁻¹ * Erec a z * Mbal a z) = c * Erec a z * Mbal a z := by
      field_simp [hκ_pos.ne']
    have hRHS : kappaBal a * (Real.sqrt 17 * |pcU a z|) = Real.sqrt 17 * |kappaBal a * pcU a z| := by
      rw [abs_mul, abs_of_pos hκ_pos]
      ring
    rwa [hLHS, hRHS] at h1
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
  linarith

/-- **`beyond` for `pcU` for all `z ≥ 2 * sqrt(max(-a, 0))` with an existential constant `c > 0`.**
Combines `pcU_beyond_deriv_abs` (`Charts/PCBeyond.lean`) with `pc_molv_well` and `pc_molv_bar`. -/
theorem pc_beyond : ∃ c : ℝ, 0 < c ∧ ∀ a z, 2 * Real.sqrt (max (-a) 0) ≤ z →
    |deriv (pcU a) z| ≤ 4 * Real.sqrt (k2 a z) * |pcU a z| ∧
    c / Real.sqrt 17 * Erec a z * Mbal a z ≤ |kappaBal a * pcU a z| := by
  obtain ⟨c1, _, hc1_pos, _, hmw⟩ := pc_molv_well
  obtain ⟨c2, _, hc2_pos, _, hmb⟩ := pc_molv_bar
  refine ⟨min c1 c2, lt_min hc1_pos hc2_pos, pc_beyond_of_molv (fun a ha z => ?_) (fun a ha z => ?_)⟩
  · have hcoeff : 0 ≤ (kappaBal a)⁻¹ * Wwell a z * Mbal a z :=
      mul_nonneg (mul_nonneg (inv_nonneg.mpr (kappaBal_pos a).le) (wwell_pos a z).le) (Mbal_pos a z).le
    calc min c1 c2 * (kappaBal a)⁻¹ * Wwell a z * Mbal a z
        = min c1 c2 * ((kappaBal a)⁻¹ * Wwell a z * Mbal a z) := by ring
      _ ≤ c1 * ((kappaBal a)⁻¹ * Wwell a z * Mbal a z) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hcoeff
      _ = c1 * (kappaBal a)⁻¹ * Wwell a z * Mbal a z := by ring
      _ ≤ Molv pcU pcV a z := (hmw a ha z).1
  · have hcoeff : 0 ≤ (kappaBal a)⁻¹ * Ebar a z * Mbal a z :=
      mul_nonneg (mul_nonneg (inv_nonneg.mpr (kappaBal_pos a).le) (ebar_pos a z).le) (Mbal_pos a z).le
    calc min c1 c2 * (kappaBal a)⁻¹ * Ebar a z * Mbal a z
        = min c1 c2 * ((kappaBal a)⁻¹ * Ebar a z * Mbal a z) := by ring
      _ ≤ c2 * ((kappaBal a)⁻¹ * Ebar a z * Mbal a z) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hcoeff
      _ = c2 * (kappaBal a)⁻¹ * Ebar a z * Mbal a z := by ring
      _ ≤ Molv pcU pcV a z := (hmb a ha z).1

/-- **Unconditional `PCEnvelopeFacts` for the actual `pcU, pcV`.**
Assembles `pc_env_well`, `pc_env_bar`, `pc_molv_well`, `pc_molv_bar`, `pcU_pos_beyond`, and `pc_beyond_of_molv`
for a single universal pair `(cPC, CPC)` with `0 < cPC ≤ CPC`. -/
theorem pcEnvelopeFacts :
    ∃ cPC CPC : ℝ, PCEnvelopeFacts pcU pcV cPC CPC := by
  obtain ⟨C_w, hC_w_pos, h_well⟩ := pc_env_well
  obtain ⟨C_b, hC_b_pos, h_bar⟩ := pc_env_bar
  have h_molv_well := molv_well_of_env_well hC_w_pos h_well
  have h_molv_bar := molv_bar_of_env_bar hC_b_pos h_bar
  let c_mw : ℝ := 1 / (C_w * Real.sqrt (Real.pi / 2))
  let C_mw : ℝ := Real.sqrt ((1 + Real.sqrt (2 / Real.pi)) ^ 2 + 2 / Real.pi) * C_w
  let c_mb : ℝ := 1 / C_b
  let C_mb : ℝ := C_b
  have hc_mw_pos : 0 < c_mw := by dsimp [c_mw]; positivity
  have hc_mb_pos : 0 < c_mb := by dsimp [c_mb]; positivity
  let cPC : ℝ := min 1 (min c_mw c_mb)
  let CPC : ℝ := max 1 (max (max C_w C_b) (max C_mw C_mb))
  have hcPC_pos : 0 < cPC := lt_min one_pos (lt_min hc_mw_pos hc_mb_pos)
  have hcPC_le : cPC ≤ CPC := (min_le_left _ _).trans (le_max_left _ _)
  have hCw_le : C_w ≤ CPC :=
    (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hCb_le : C_b ≤ CPC :=
    (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hCmw_le : C_mw ≤ CPC :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCmb_le : C_mb ≤ CPC :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hc_mw_ge : cPC ≤ c_mw := (min_le_right _ _).trans (min_le_left _ _)
  have hc_mb_ge : cPC ≤ c_mb := (min_le_right _ _).trans (min_le_right _ _)
  have h_molv_well_c : ∀ a ≤ 0, ∀ z,
      cPC * (kappaBal a)⁻¹ * Wwell a z * Mbal a z ≤ Molv pcU pcV a z ∧
      Molv pcU pcV a z ≤ CPC * (kappaBal a)⁻¹ * Wwell a z * Mbal a z := by
    intro a ha z
    obtain ⟨hlb, hub⟩ := h_molv_well a ha z
    have hcoeff : 0 ≤ (kappaBal a)⁻¹ * Wwell a z * Mbal a z :=
      mul_nonneg (mul_nonneg (inv_nonneg.mpr (kappaBal_pos a).le) (wwell_pos a z).le) (Mbal_pos a z).le
    refine ⟨?_, ?_⟩
    · calc cPC * (kappaBal a)⁻¹ * Wwell a z * Mbal a z
          = cPC * ((kappaBal a)⁻¹ * Wwell a z * Mbal a z) := by ring
        _ ≤ c_mw * ((kappaBal a)⁻¹ * Wwell a z * Mbal a z) :=
            mul_le_mul_of_nonneg_right hc_mw_ge hcoeff
        _ = c_mw * (kappaBal a)⁻¹ * Wwell a z * Mbal a z := by ring
        _ ≤ Molv pcU pcV a z := hlb
    · calc Molv pcU pcV a z
          ≤ C_mw * (kappaBal a)⁻¹ * Wwell a z * Mbal a z := hub
        _ = C_mw * ((kappaBal a)⁻¹ * Wwell a z * Mbal a z) := by ring
        _ ≤ CPC * ((kappaBal a)⁻¹ * Wwell a z * Mbal a z) :=
            mul_le_mul_of_nonneg_right hCmw_le hcoeff
        _ = CPC * (kappaBal a)⁻¹ * Wwell a z * Mbal a z := by ring
  have h_molv_bar_c : ∀ a, 0 < a → ∀ z,
      cPC * (kappaBal a)⁻¹ * Ebar a z * Mbal a z ≤ Molv pcU pcV a z ∧
      Molv pcU pcV a z ≤ CPC * (kappaBal a)⁻¹ * Ebar a z * Mbal a z := by
    intro a ha z
    obtain ⟨hlb, hub⟩ := h_molv_bar a ha z
    have hcoeff : 0 ≤ (kappaBal a)⁻¹ * Ebar a z * Mbal a z :=
      mul_nonneg (mul_nonneg (inv_nonneg.mpr (kappaBal_pos a).le) (ebar_pos a z).le) (Mbal_pos a z).le
    refine ⟨?_, ?_⟩
    · calc cPC * (kappaBal a)⁻¹ * Ebar a z * Mbal a z
          = cPC * ((kappaBal a)⁻¹ * Ebar a z * Mbal a z) := by ring
        _ ≤ c_mb * ((kappaBal a)⁻¹ * Ebar a z * Mbal a z) :=
            mul_le_mul_of_nonneg_right hc_mb_ge hcoeff
        _ = c_mb * (kappaBal a)⁻¹ * Ebar a z * Mbal a z := by ring
        _ ≤ Molv pcU pcV a z := hlb
    · calc Molv pcU pcV a z
          ≤ C_mb * (kappaBal a)⁻¹ * Ebar a z * Mbal a z := hub
        _ = C_mb * ((kappaBal a)⁻¹ * Ebar a z * Mbal a z) := by ring
        _ ≤ CPC * ((kappaBal a)⁻¹ * Ebar a z * Mbal a z) :=
            mul_le_mul_of_nonneg_right hCmb_le hcoeff
        _ = CPC * (kappaBal a)⁻¹ * Ebar a z * Mbal a z := by ring
  refine ⟨cPC, CPC, ?_⟩
  refine
    { cPC_pos := hcPC_pos
      cPC_le := hcPC_le
      env_well := fun a ha z hz => by
        obtain ⟨hU, hV_env⟩ := h_well a ha z hz
        have hEM : 0 ≤ Ewell a z * Mbal a z := mul_nonneg (ewell_pos a z).le (Mbal_pos a z).le
        have hEiM : 0 ≤ (Ewell a z)⁻¹ * Mbal a z :=
          mul_nonneg (inv_nonneg.mpr (ewell_pos a z).le) (Mbal_pos a z).le
        exact ⟨hU.trans (by rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hCw_le hEM),
          hV_env.trans (by rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hCw_le hEiM)⟩
      env_bar := fun a ha z => by
        obtain ⟨h1, h2⟩ := h_bar a ha z
        have hEM : 0 ≤ Ebar a z * Mbal a z := mul_nonneg (ebar_pos a z).le (Mbal_pos a z).le
        have hEiM : 0 ≤ (Ebar a z)⁻¹ * Mbal a z :=
          mul_nonneg (inv_nonneg.mpr (ebar_pos a z).le) (Mbal_pos a z).le
        exact ⟨h1.trans (by rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hCb_le hEM),
          h2.trans (by rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hCb_le hEiM)⟩
      molv_well := h_molv_well_c
      molv_bar := h_molv_bar_c
      U_pos := pcU_pos_beyond
      beyond := pc_beyond_of_molv (fun a ha z => (h_molv_well_c a ha z).1)
        (fun a ha z => (h_molv_bar_c a ha z).1) }

/-- **Unconditional `ParabolicCylinderFacts` for the actual `pcU, pcV`.**
Combines `pcEnvelopeFacts` with `ParabolicCylinderFacts.ofEnvelope` (`Charts/PCActual.lean`). -/
theorem parabolicCylinderFacts :
    ∃ cPC CPC : ℝ, ParabolicCylinderFacts pcU pcV cPC CPC := by
  obtain ⟨cPC, CPC, he⟩ := pcEnvelopeFacts
  exact ⟨cPC, CPC, ParabolicCylinderFacts.ofEnvelope he⟩

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pc_env_well' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pc_env_well

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pc_env_bar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pc_env_bar

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pc_molv_well' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pc_molv_well

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pc_molv_bar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pc_molv_bar

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pc_beyond_of_molv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pc_beyond_of_molv

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pc_beyond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pc_beyond

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pcEnvelopeFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pcEnvelopeFacts

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.parabolicCylinderFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parabolicCylinderFacts

end FormalResearch.JacobiEigenvectors.Charts
