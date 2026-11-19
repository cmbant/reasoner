module

public import Mathlib
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenReal
public import FormalResearch.JacobiEigenvectors.Charts.PCEnvWellFar
public import FormalResearch.JacobiEigenvectors.Charts.PCEnvBar

/-!
# Paper J, Layer 4 (phase B2, E5): `env_well` on `(-4, 0]` and `env_bar` on `(0, 1)`

Proves the two remaining parameter ranges of `PCEnvelopeFacts` for the actual functions `pcU, pcV`:

* **(A) `pc_env_well_compact`**: `env_well` (both `pcU` and `pcV` conjuncts) for `-4 ≤ a ≤ 0` and
  all `z ≥ 0`, with an absolute constant `C`.
* **(B) `pc_env_bar_compact`**: `env_bar` (both `pcU(a, z)` and `pcU(a, -z)` conjuncts) for
  `0 < a ≤ 1` and all `z : ℝ`, with an absolute constant `C`.

Method:
1. Compactness on `[-4, 0] × [0, 10]` and `[0, 1] × [-10, 10]` using `pcSmoothFacts`, `cont_pcUD`,
   `cont_pcVD`, continuity of `kappaBal` on `[-4, 0]` and of `kappaBalPos` on `[0, 1]`, and
   non-vanishing of `(U, U')` and `(V, V')` from `pc_wronsk`.
2. Tail `pcU` for `|a| ≤ 4`, `z ≥ 10`: `LiouvilleGreen.exists_solution_exp_of_pos` on `(9, ∞)`
   with `p(t) = t^2 / 4 + a ≥ t^2 / 8` and `∫_x^∞ |errorDensity| ≤ 3 / 50`, normalised at `z = 10`.
3. Tail `pcV` (`-4 ≤ a ≤ 0`, `z ≥ 10`) via `(vt / ut)' = 1 / ut^2`, and tail `pcU(a, -x)`
   (`0 < a ≤ 1`, `x ≥ 10`) via `parabolicCylinderU_wronskian_neg`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open MeasureTheory Set Real Filter Topology intervalIntegral

/-! ### Section 1: Continuity and compactness bounds on the boxes -/

/-- Continuous extension of `kappaBal` to `a ≥ 0`. -/
def kappaBalPos (a : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(1 : ℝ) / 4) * Real.sqrt (Real.Gamma (1 / 2 + a))

lemma kappaBal_eq_kappaBalPos {a : ℝ} (ha : 0 < a) : kappaBal a = kappaBalPos a := by
  unfold kappaBal kappaBalPos
  rw [ite_eq_right_iff.mpr (fun h => absurd ha (not_lt.mpr h))]

lemma kappaBalPos_pos {a : ℝ} (ha : 0 ≤ a) : 0 < kappaBalPos a := by
  unfold kappaBalPos
  have hpi : 0 < 2 * Real.pi := by positivity
  have hG : 0 < Real.Gamma (1 / 2 + a) := Real.Gamma_pos_of_pos (by linarith)
  positivity

lemma continuous_k2 : Continuous (fun p : ℝ × ℝ => k2 p.1 p.2) := by
  unfold k2
  refine Continuous.max (Continuous.abs (by fun_prop)) ?_
  exact ((continuous_abs.comp continuous_fst).max continuous_const).rpow_const fun p =>
    Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _)))

lemma continuousOn_Gamma_pos : ContinuousOn Real.Gamma (Ioi 0) := by
  intro x hx
  have hx0 : 0 < x := hx
  exact (Real.differentiableAt_Gamma fun m =>
    ne_of_gt (by linarith [Nat.cast_nonneg (α := ℝ) m])).continuousAt.continuousWithinAt

lemma continuousOn_kappaBal_well : ContinuousOn kappaBal (Icc (-4 : ℝ) 0) := by
  have hcont : ContinuousOn (fun a : ℝ => (Real.Gamma (1 / 2 - a)) ^ (-(1 : ℝ) / 2)) (Icc (-4 : ℝ) 0) := by
    refine ContinuousOn.rpow_const ?_ fun a ha => ?_
    · exact continuousOn_Gamma_pos.comp (by fun_prop) fun a ha => by
        simp only [mem_Icc] at ha
        simp only [mem_Ioi]
        linarith
    · left
      simp only [mem_Icc] at ha
      exact (Real.Gamma_pos_of_pos (by linarith)).ne'
  refine hcont.congr fun a ha => ?_
  simp only [mem_Icc] at ha
  unfold kappaBal
  rw [ite_eq_left_iff.mpr fun h => absurd ha.2 h]

lemma continuousOn_kappaBalPos : ContinuousOn kappaBalPos (Icc (0 : ℝ) 1) := by
  unfold kappaBalPos
  refine continuousOn_const.mul (ContinuousOn.sqrt ?_)
  exact continuousOn_Gamma_pos.comp (by fun_prop) fun a ha => by
    simp only [mem_Icc] at ha
    simp only [mem_Ioi]
    linarith

lemma eu_pos (a z : ℝ) :
    0 < Real.sqrt (pcU a z ^ 2 + pcUD a z ^ 2 / k2 a z) := by
  refine Real.sqrt_pos.mpr ?_
  have hk := k2_pos a z
  have hwr := pc_wronsk a z
  rw [deriv_pcU, deriv_pcV] at hwr
  by_contra hle
  push Not at hle
  have h1 : pcU a z ^ 2 + pcUD a z ^ 2 / k2 a z = 0 :=
    le_antisymm hle (add_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) hk.le))
  have h2 : pcU a z ^ 2 = 0 :=
    le_antisymm (by linarith [div_nonneg (sq_nonneg (pcUD a z)) hk.le]) (sq_nonneg _)
  have h3 : pcUD a z ^ 2 / k2 a z = 0 := by linarith
  have hU0 : pcU a z = 0 := sq_eq_zero_iff.mp h2
  have hUD0 : pcUD a z = 0 := sq_eq_zero_iff.mp (div_eq_zero_iff.mp h3 |>.resolve_right hk.ne')
  rw [hU0, hUD0, zero_mul, zero_mul, sub_zero] at hwr
  have hpi : 0 < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.mpr (by positivity)
  linarith

lemma ev_pos (a z : ℝ) :
    0 < Real.sqrt (pcV a z ^ 2 + pcVD a z ^ 2 / k2 a z) := by
  refine Real.sqrt_pos.mpr ?_
  have hk := k2_pos a z
  have hwr := pc_wronsk a z
  rw [deriv_pcU, deriv_pcV] at hwr
  by_contra hle
  push Not at hle
  have h1 : pcV a z ^ 2 + pcVD a z ^ 2 / k2 a z = 0 :=
    le_antisymm hle (add_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) hk.le))
  have h2 : pcV a z ^ 2 = 0 :=
    le_antisymm (by linarith [div_nonneg (sq_nonneg (pcVD a z)) hk.le]) (sq_nonneg _)
  have h3 : pcVD a z ^ 2 / k2 a z = 0 := by linarith
  have hV0 : pcV a z = 0 := sq_eq_zero_iff.mp h2
  have hVD0 : pcVD a z = 0 := sq_eq_zero_iff.mp (div_eq_zero_iff.mp h3 |>.resolve_right hk.ne')
  rw [hV0, hVD0, mul_zero, mul_zero, sub_zero] at hwr
  have hpi : 0 < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.mpr (by positivity)
  linarith

lemma Ewell_box_bounds {a z : ℝ} (_ha : -4 ≤ a) (_ha0 : a ≤ 0) (hz0 : 0 ≤ z) (hz10 : z ≤ 10) :
    Real.exp (-50) ≤ Ewell a z ∧ Ewell a z ≤ 1 := by
  unfold Ewell
  split_ifs with hlt
  · constructor
    · refine Real.exp_le_exp.mpr (neg_le_neg ?_)
      have h0 : 0 ≤ 2 * Real.sqrt |a| := by positivity
      have hint : ∫ t in (2 * Real.sqrt |a|)..z, Real.sqrt (t ^ 2 / 4 - |a|) ≤
          ∫ t in (2 * Real.sqrt |a|)..z, (5 : ℝ) := by
        refine intervalIntegral.integral_mono_on hlt.le ?_ intervalIntegrable_const fun t ht => ?_
        · exact (Real.continuous_sqrt.comp (by continuity)).intervalIntegrable _ _
        · have ht0 : 0 ≤ t := h0.trans ht.1
          have hle : t ^ 2 / 4 - |a| ≤ (5 : ℝ) ^ 2 := by
            have h1 : t ^ 2 ≤ 100 := by nlinarith [ht.2]
            have h2 : 0 ≤ |a| := abs_nonneg a
            linarith
          have hsq : Real.sqrt (t ^ 2 / 4 - |a|) ≤ Real.sqrt ((5 : ℝ) ^ 2) :=
            Real.sqrt_le_sqrt hle
          rwa [Real.sqrt_sq (by norm_num)] at hsq
      have hconst : ∫ t in (2 * Real.sqrt |a|)..z, (5 : ℝ) = (z - 2 * Real.sqrt |a|) * 5 :=
        intervalIntegral.integral_const _
      linarith
    · refine Real.exp_le_one_iff.mpr (neg_nonpos.mpr ?_)
      exact intervalIntegral.integral_nonneg hlt.le fun t _ => Real.sqrt_nonneg _
  · exact ⟨(Real.exp_le_one_iff.mpr (by norm_num)), le_rfl⟩

lemma Ebar_box_bounds {a z : ℝ} (_ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hzlo : -10 ≤ z) (hzhi : z ≤ 10) :
    Real.exp (-60) ≤ Ebar a z ∧ Ebar a z ≤ Real.exp 60 := by
  unfold Ebar
  have hbd : |∫ t in (0 : ℝ)..z, Real.sqrt (t ^ 2 / 4 + a)| ≤ 60 := by
    have hle : ∀ t ∈ uIoc (0 : ℝ) z, ‖Real.sqrt (t ^ 2 / 4 + a)‖ ≤ 6 := fun t ht => by
      have ht' := uIoc_subset_uIcc ht
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      have ht_abs : |t| ≤ 10 := by
        rw [abs_le]
        rcases mem_uIcc.mp ht' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
      have ht2 : t ^ 2 ≤ 100 := by nlinarith [abs_le.mp ht_abs]
      have hsq : t ^ 2 / 4 + a ≤ 6 ^ 2 := by linarith
      calc Real.sqrt (t ^ 2 / 4 + a) ≤ Real.sqrt (6 ^ 2) := Real.sqrt_le_sqrt hsq
        _ = 6 := Real.sqrt_sq (by norm_num)
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const hle
    rw [Real.norm_eq_abs, sub_zero] at hint
    have habs : |z| ≤ 10 := abs_le.mpr ⟨hzlo, hzhi⟩
    nlinarith
  obtain ⟨h1, h2⟩ := abs_le.mp hbd
  exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr (by linarith)⟩

lemma Mbal_box_bounds {a z : ℝ} (ha : |a| ≤ 4) (hz : |z| ≤ 10) :
    (29 : ℝ) ^ (-(1 : ℝ) / 4) ≤ Mbal a z ∧ Mbal a z ≤ 1 := by
  have hk_lo : 1 ≤ k2 a z := by
    unfold k2
    refine le_trans ?_ (le_max_right _ _)
    exact Real.one_le_rpow (le_max_right _ _) (by norm_num)
  have hk_hi : k2 a z ≤ 29 := by
    unfold k2
    refine max_le ?_ ?_
    · have hz2 : z ^ 2 ≤ 100 := by nlinarith [abs_le.mp hz]
      have h1 : |z ^ 2 / 4 + a| ≤ z ^ 2 / 4 + |a| := by
        calc |z ^ 2 / 4 + a| ≤ |z ^ 2 / 4| + |a| := abs_add_le _ _
          _ = z ^ 2 / 4 + |a| := by rw [abs_of_nonneg (by positivity)]
      linarith
    · have hm : max |a| 1 ≤ 4 := max_le ha (by norm_num)
      calc max |a| 1 ^ ((1 : ℝ) / 3) ≤ 4 ^ ((1 : ℝ) / 3) :=
            Real.rpow_le_rpow (by positivity) hm (by norm_num)
        _ ≤ 4 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 4 := Real.rpow_one 4
        _ ≤ 29 := by norm_num
  unfold Mbal
  constructor
  · exact Real.rpow_le_rpow_of_nonpos (k2_pos a z) hk_hi (by norm_num)
  · calc k2 a z ^ (-(1 : ℝ) / 4) ≤ 1 ^ (-(1 : ℝ) / 4) :=
          Real.rpow_le_rpow_of_nonpos zero_lt_one hk_lo (by norm_num)
      _ = 1 := Real.one_rpow _

theorem compact_box_well :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ a, -4 ≤ a → a ≤ 0 → ∀ z, 0 ≤ z → z ≤ 10 →
        (c * Ewell a z * Mbal a z ≤
            Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) ∧
          Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) ≤
            C * Ewell a z * Mbal a z) ∧
        (c * (Ewell a z)⁻¹ * Mbal a z ≤
            Real.sqrt (vt pcV a z ^ 2 + (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z) ∧
          Real.sqrt (vt pcV a z ^ 2 + (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z) ≤
            C * (Ewell a z)⁻¹ * Mbal a z) := by
  let S : Set (ℝ × ℝ) := Icc (-4 : ℝ) 0 ×ˢ Icc (0 : ℝ) 10
  have hS_compact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hS_ne : S.Nonempty := ⟨(0, 0), ⟨by norm_num, le_rfl⟩, ⟨le_rfl, by norm_num⟩⟩
  let fU : ℝ × ℝ → ℝ := fun p =>
    kappaBal p.1 * Real.sqrt (pcU p.1 p.2 ^ 2 + pcUD p.1 p.2 ^ 2 / k2 p.1 p.2)
  let fV : ℝ × ℝ → ℝ := fun p =>
    Real.sqrt (π / 2) * (kappaBal p.1)⁻¹ * Real.sqrt (pcV p.1 p.2 ^ 2 + pcVD p.1 p.2 ^ 2 / k2 p.1 p.2)
  have hcont_pcUD : Continuous (fun p : ℝ × ℝ => pcUD p.1 p.2) := by
    simpa only [← deriv_pcU] using cont_pcUD
  have hcont_pcVD : Continuous (fun p : ℝ × ℝ => pcVD p.1 p.2) := by
    simpa only [← deriv_pcV] using cont_pcVD
  have hfU_cont : ContinuousOn fU S := by
    refine (continuousOn_kappaBal_well.comp continuousOn_fst fun p hp => hp.1).mul ?_
    refine ContinuousOn.sqrt (ContinuousOn.add ?_ (ContinuousOn.div ?_ continuous_k2.continuousOn ?_))
    · exact (pcSmoothFacts.cont_U.pow 2).continuousOn
    · exact (hcont_pcUD.pow 2).continuousOn
    · intro p _; exact (k2_pos p.1 p.2).ne'
  have hfV_cont : ContinuousOn fV S := by
    refine (continuousOn_const.mul (ContinuousOn.inv₀
      (continuousOn_kappaBal_well.comp continuousOn_fst fun p hp => hp.1)
      fun p _ => (kappaBal_pos p.1).ne')).mul ?_
    refine ContinuousOn.sqrt (ContinuousOn.add ?_ (ContinuousOn.div ?_ continuous_k2.continuousOn ?_))
    · exact (pcSmoothFacts.cont_V.pow 2).continuousOn
    · exact (hcont_pcVD.pow 2).continuousOn
    · intro p _; exact (k2_pos p.1 p.2).ne'
  obtain ⟨pU_min, hpU_minS, hpU_min⟩ := hS_compact.exists_isMinOn hS_ne hfU_cont
  obtain ⟨pU_max, hpU_maxS, hpU_max⟩ := hS_compact.exists_isMaxOn hS_ne hfU_cont
  obtain ⟨pV_min, hpV_minS, hpV_min⟩ := hS_compact.exists_isMinOn hS_ne hfV_cont
  obtain ⟨pV_max, hpV_maxS, hpV_max⟩ := hS_compact.exists_isMaxOn hS_ne hfV_cont
  have hfU_pos : ∀ p, 0 < fU p := fun p => mul_pos (kappaBal_pos p.1) (eu_pos p.1 p.2)
  have hfV_pos : ∀ p, 0 < fV p := fun p =>
    mul_pos (mul_pos (Real.sqrt_pos.mpr (by positivity)) (inv_pos.mpr (kappaBal_pos p.1))) (ev_pos p.1 p.2)
  let c0 := min (fU pU_min) (fV pV_min)
  let C0 := max (fU pU_max) (fV pV_max)
  have hc0_pos : 0 < c0 := lt_min (hfU_pos pU_min) (hfV_pos pV_min)
  have hc0_le_C0 : c0 ≤ C0 :=
    le_trans (min_le_left _ _) (le_trans (hpU_max hpU_minS) (le_max_left _ _))
  refine ⟨c0 * Real.exp (-50), C0 * Real.exp 50 * 29 ^ ((1 : ℝ) / 4), by positivity, ?_, ?_⟩
  · have h1 : Real.exp (-50) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have h2 : (1 : ℝ) ≤ Real.exp 50 := Real.one_le_exp (by norm_num)
    have h3 : (1 : ℝ) ≤ (29 : ℝ) ^ ((1 : ℝ) / 4) := Real.one_le_rpow (by norm_num) (by norm_num)
    have h4 : c0 * Real.exp (-50) ≤ c0 := mul_le_of_le_one_right hc0_pos.le h1
    have h5 : C0 ≤ C0 * Real.exp 50 * 29 ^ ((1 : ℝ) / 4) := by
      have hC0 : 0 ≤ C0 := le_trans hc0_pos.le hc0_le_C0
      calc C0 = C0 * 1 * 1 := by ring
        _ ≤ C0 * Real.exp 50 * 29 ^ ((1 : ℝ) / 4) := by gcongr
    linarith
  · intro a ha4 ha0 z hz0 hz10
    have hpS : (a, z) ∈ S := ⟨⟨ha4, ha0⟩, ⟨hz0, hz10⟩⟩
    have ha_abs : |a| ≤ 4 := abs_le.mpr ⟨ha4, by linarith⟩
    have hz_abs : |z| ≤ 10 := abs_le.mpr ⟨by linarith, hz10⟩
    obtain ⟨hE_lo, hE_hi⟩ := Ewell_box_bounds ha4 ha0 hz0 hz10
    obtain ⟨hM_lo, hM_hi⟩ := Mbal_box_bounds ha_abs hz_abs
    have hE_pos : 0 < Ewell a z := lt_of_lt_of_le (Real.exp_pos _) hE_lo
    have hM_pos : 0 < Mbal a z := Mbal_pos a z
    have hEM_le : Ewell a z * Mbal a z ≤ 1 := by
      calc Ewell a z * Mbal a z ≤ 1 * 1 := mul_le_mul hE_hi hM_hi hM_pos.le (by norm_num)
        _ = 1 := one_mul 1
    have h29_neg_nonneg : 0 ≤ (29 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg (by norm_num) _
    have h29_pos_nonneg : 0 ≤ (29 : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by norm_num) _
    have hEM_ge : Real.exp (-50) * (29 : ℝ) ^ (-(1 : ℝ) / 4) ≤ Ewell a z * Mbal a z :=
      mul_le_mul hE_lo hM_lo h29_neg_nonneg hE_pos.le
    have hEinvM_le : (Ewell a z)⁻¹ * Mbal a z ≤ Real.exp 50 := by
      have hinv : (Ewell a z)⁻¹ ≤ Real.exp 50 := by
        rw [inv_le_iff_one_le_mul₀' hE_pos]
        calc (1 : ℝ) = Real.exp 50 * Real.exp (-50) := by rw [← Real.exp_add]; norm_num
          _ ≤ Real.exp 50 * Ewell a z := mul_le_mul_of_nonneg_left hE_lo (Real.exp_pos _).le
          _ = Ewell a z * Real.exp 50 := mul_comm _ _
      calc (Ewell a z)⁻¹ * Mbal a z ≤ Real.exp 50 * 1 :=
            mul_le_mul hinv hM_hi hM_pos.le (Real.exp_pos _).le
        _ = Real.exp 50 := mul_one _
    have hEinvM_ge : (29 : ℝ) ^ (-(1 : ℝ) / 4) ≤ (Ewell a z)⁻¹ * Mbal a z := by
      have hinv : 1 ≤ (Ewell a z)⁻¹ := (one_le_inv₀ hE_pos).mpr hE_hi
      calc (29 : ℝ) ^ (-(1 : ℝ) / 4) = 1 * (29 : ℝ) ^ (-(1 : ℝ) / 4) := (one_mul _).symm
        _ ≤ (Ewell a z)⁻¹ * Mbal a z := mul_le_mul hinv hM_lo h29_neg_nonneg (by linarith)
    have hfU_eq : Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) = fU (a, z) := by
      have hκ := (kappaBal_pos a).le
      unfold fU ut
      rw [deriv_pcU, ← Real.sqrt_sq hκ, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hκ]
      congr 1; ring
    have hfV_eq : Real.sqrt (vt pcV a z ^ 2 + (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z) = fV (a, z) := by
      have hc : 0 ≤ Real.sqrt (π / 2) * (kappaBal a)⁻¹ :=
        mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (kappaBal_pos a).le)
      unfold fV vt
      rw [deriv_pcV, ← Real.sqrt_sq hc, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]
      congr 1; ring
    have hinv_prod : (29 : ℝ) ^ ((1 : ℝ) / 4) * (29 : ℝ) ^ (-(1 : ℝ) / 4) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; norm_num
    have hexp_prod : Real.exp 50 * Real.exp (-50) = 1 := by
      rw [← Real.exp_add]; norm_num
    have hexp_prod' : Real.exp (-50) * Real.exp 50 = 1 := by rw [mul_comm, hexp_prod]
    have hC0_pos : 0 ≤ C0 := le_trans hc0_pos.le hc0_le_C0
    constructor
    · rw [hfU_eq]
      constructor
      · calc c0 * Real.exp (-50) * Ewell a z * Mbal a z
            = (c0 * Real.exp (-50)) * (Ewell a z * Mbal a z) := by ring
          _ ≤ (c0 * Real.exp (-50)) * 1 :=
              mul_le_mul_of_nonneg_left hEM_le (mul_nonneg hc0_pos.le (Real.exp_pos _).le)
          _ ≤ c0 * 1 := by
              have hexp1 : Real.exp (-50) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
              nlinarith
          _ = c0 := mul_one c0
          _ ≤ fU pU_min := min_le_left _ _
          _ ≤ fU (a, z) := hpU_min hpS
      · calc fU (a, z) ≤ fU pU_max := hpU_max hpS
          _ ≤ C0 := le_max_left _ _
          _ = C0 * (Real.exp 50 * Real.exp (-50)) * ((29 : ℝ) ^ ((1 : ℝ) / 4) * (29 : ℝ) ^ (-(1 : ℝ) / 4)) := by
              rw [hexp_prod, hinv_prod, mul_one, mul_one]
          _ = (C0 * Real.exp 50 * 29 ^ ((1 : ℝ) / 4)) * (Real.exp (-50) * (29 : ℝ) ^ (-(1 : ℝ) / 4)) := by ring
          _ ≤ (C0 * Real.exp 50 * 29 ^ ((1 : ℝ) / 4)) * (Ewell a z * Mbal a z) :=
              mul_le_mul_of_nonneg_left hEM_ge (mul_nonneg (mul_nonneg hC0_pos (Real.exp_pos _).le) h29_pos_nonneg)
          _ = C0 * Real.exp 50 * 29 ^ ((1 : ℝ) / 4) * Ewell a z * Mbal a z := by ring
    · rw [hfV_eq]
      constructor
      · calc c0 * Real.exp (-50) * (Ewell a z)⁻¹ * Mbal a z
            = c0 * (Real.exp (-50) * ((Ewell a z)⁻¹ * Mbal a z)) := by ring
          _ ≤ c0 * (Real.exp (-50) * Real.exp 50) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEinvM_le (Real.exp_pos _).le) hc0_pos.le
          _ = c0 := by rw [hexp_prod', mul_one]
          _ ≤ fV pV_min := min_le_right _ _
          _ ≤ fV (a, z) := hpV_min hpS
      · calc fV (a, z) ≤ fV pV_max := hpV_max hpS
          _ ≤ C0 := le_max_right _ _
          _ = C0 * 1 * ((29 : ℝ) ^ ((1 : ℝ) / 4) * (29 : ℝ) ^ (-(1 : ℝ) / 4)) := by
              rw [hinv_prod, mul_one, mul_one]
          _ ≤ C0 * Real.exp 50 * ((29 : ℝ) ^ ((1 : ℝ) / 4) * (29 : ℝ) ^ (-(1 : ℝ) / 4)) := by
              have h1 : (1 : ℝ) ≤ Real.exp 50 := Real.one_le_exp (by norm_num)
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC0_pos)
                (mul_nonneg h29_pos_nonneg h29_neg_nonneg)
          _ = (C0 * Real.exp 50 * 29 ^ ((1 : ℝ) / 4)) * (29 : ℝ) ^ (-(1 : ℝ) / 4) := by ring
          _ ≤ (C0 * Real.exp 50 * 29 ^ ((1 : ℝ) / 4)) * ((Ewell a z)⁻¹ * Mbal a z) :=
              mul_le_mul_of_nonneg_left hEinvM_ge (mul_nonneg (mul_nonneg hC0_pos (Real.exp_pos _).le) h29_pos_nonneg)
          _ = C0 * Real.exp 50 * 29 ^ ((1 : ℝ) / 4) * (Ewell a z)⁻¹ * Mbal a z := by ring

theorem compact_box_bar :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ a, 0 ≤ a → a ≤ 1 → ∀ z, -10 ≤ z → z ≤ 10 →
        c * Ebar a z * Mbal a z ≤
            Real.sqrt ((kappaBalPos a * pcU a z) ^ 2 + (kappaBalPos a * deriv (pcU a) z) ^ 2 / k2 a z) ∧
          Real.sqrt ((kappaBalPos a * pcU a z) ^ 2 + (kappaBalPos a * deriv (pcU a) z) ^ 2 / k2 a z) ≤
            C * Ebar a z * Mbal a z := by
  let S : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (-10 : ℝ) 10
  have hS_compact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hS_ne : S.Nonempty := ⟨(0, 0), ⟨le_rfl, zero_le_one⟩, ⟨by norm_num, by norm_num⟩⟩
  let gU : ℝ × ℝ → ℝ := fun p =>
    kappaBalPos p.1 * Real.sqrt (pcU p.1 p.2 ^ 2 + pcUD p.1 p.2 ^ 2 / k2 p.1 p.2)
  have hcont_pcUD : Continuous (fun p : ℝ × ℝ => pcUD p.1 p.2) := by
    simpa only [← deriv_pcU] using cont_pcUD
  have hgU_cont : ContinuousOn gU S := by
    refine (continuousOn_kappaBalPos.comp continuousOn_fst fun p hp => hp.1).mul ?_
    refine ContinuousOn.sqrt (ContinuousOn.add ?_ (ContinuousOn.div ?_ continuous_k2.continuousOn ?_))
    · exact (pcSmoothFacts.cont_U.pow 2).continuousOn
    · exact (hcont_pcUD.pow 2).continuousOn
    · intro p _; exact (k2_pos p.1 p.2).ne'
  obtain ⟨p_min, hp_minS, hp_min⟩ := hS_compact.exists_isMinOn hS_ne hgU_cont
  obtain ⟨p_max, hp_maxS, hp_max⟩ := hS_compact.exists_isMaxOn hS_ne hgU_cont
  have hgU_pos : ∀ p ∈ S, 0 < gU p := fun p hp =>
    mul_pos (kappaBalPos_pos hp.1.1) (eu_pos p.1 p.2)
  let c0 := gU p_min
  let C0 := gU p_max
  have hc0_pos : 0 < c0 := hgU_pos p_min hp_minS
  have hc0_le_C0 : c0 ≤ C0 := hp_max hp_minS
  refine ⟨c0 * Real.exp (-60), C0 * Real.exp 60 * 29 ^ ((1 : ℝ) / 4), by positivity, ?_, ?_⟩
  · have h1 : Real.exp (-60) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have h2 : (1 : ℝ) ≤ Real.exp 60 := Real.one_le_exp (by norm_num)
    have h3 : (1 : ℝ) ≤ (29 : ℝ) ^ ((1 : ℝ) / 4) := Real.one_le_rpow (by norm_num) (by norm_num)
    have h4 : c0 * Real.exp (-60) ≤ c0 := mul_le_of_le_one_right hc0_pos.le h1
    have h5 : C0 ≤ C0 * Real.exp 60 * 29 ^ ((1 : ℝ) / 4) := by
      have hC0 : 0 ≤ C0 := le_trans hc0_pos.le hc0_le_C0
      calc C0 = C0 * 1 * 1 := by ring
        _ ≤ C0 * Real.exp 60 * 29 ^ ((1 : ℝ) / 4) := by gcongr
    linarith
  · intro a ha0 ha1 z hzlo hzhi
    have hpS : (a, z) ∈ S := ⟨⟨ha0, ha1⟩, ⟨hzlo, hzhi⟩⟩
    have ha_abs : |a| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hz_abs : |z| ≤ 10 := abs_le.mpr ⟨hzlo, hzhi⟩
    obtain ⟨hE_lo, hE_hi⟩ := Ebar_box_bounds ha0 ha1 hzlo hzhi
    obtain ⟨hM_lo, hM_hi⟩ := Mbal_box_bounds ha_abs hz_abs
    have hEM_le : Ebar a z * Mbal a z ≤ Real.exp 60 := by
      calc Ebar a z * Mbal a z ≤ Real.exp 60 * 1 :=
            mul_le_mul hE_hi hM_hi (Mbal_pos a z).le (by positivity)
        _ = Real.exp 60 := mul_one _
    have h29_neg_nonneg : 0 ≤ (29 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg (by norm_num) _
    have h29_pos_nonneg : 0 ≤ (29 : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by norm_num) _
    have hEM_ge : Real.exp (-60) * (29 : ℝ) ^ (-(1 : ℝ) / 4) ≤ Ebar a z * Mbal a z :=
      mul_le_mul hE_lo hM_lo h29_neg_nonneg (Real.exp_pos _).le
    have hgU_eq : Real.sqrt ((kappaBalPos a * pcU a z) ^ 2 +
        (kappaBalPos a * deriv (pcU a) z) ^ 2 / k2 a z) = gU (a, z) := by
      have hκ := (kappaBalPos_pos ha0).le
      unfold gU
      rw [deriv_pcU, ← Real.sqrt_sq hκ, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hκ]
      congr 1; ring
    have hinv_prod : (29 : ℝ) ^ ((1 : ℝ) / 4) * (29 : ℝ) ^ (-(1 : ℝ) / 4) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; norm_num
    have hexp_prod : Real.exp 60 * Real.exp (-60) = 1 := by
      rw [← Real.exp_add]; norm_num
    have hexp_prod' : Real.exp (-60) * Real.exp 60 = 1 := by rw [mul_comm, hexp_prod]
    rw [hgU_eq]
    constructor
    · calc c0 * Real.exp (-60) * Ebar a z * Mbal a z
          = c0 * (Real.exp (-60) * (Ebar a z * Mbal a z)) := by ring
        _ ≤ c0 * (Real.exp (-60) * Real.exp 60) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEM_le (Real.exp_pos _).le) hc0_pos.le
        _ = c0 := by rw [hexp_prod', mul_one]
        _ ≤ gU (a, z) := hp_min hpS
    · calc gU (a, z) ≤ C0 := hp_max hpS
        _ = C0 * (Real.exp 60 * Real.exp (-60)) * ((29 : ℝ) ^ ((1 : ℝ) / 4) * (29 : ℝ) ^ (-(1 : ℝ) / 4)) := by
            rw [hexp_prod, hinv_prod, mul_one, mul_one]
        _ = (C0 * Real.exp 60 * 29 ^ ((1 : ℝ) / 4)) * (Real.exp (-60) * (29 : ℝ) ^ (-(1 : ℝ) / 4)) := by ring
        _ ≤ (C0 * Real.exp 60 * 29 ^ ((1 : ℝ) / 4)) * (Ebar a z * Mbal a z) :=
            mul_le_mul_of_nonneg_left hEM_ge (mul_nonneg (mul_nonneg (le_trans hc0_pos.le hc0_le_C0) (Real.exp_pos _).le) h29_pos_nonneg)
        _ = C0 * Real.exp 60 * 29 ^ ((1 : ℝ) / 4) * Ebar a z * Mbal a z := by ring

/-! ### Section 2: Tail `pcU` for `|a| ≤ 4` and `z ≥ 10` -/

lemma p_compact_ge {a t : ℝ} (ha : |a| ≤ 4) (ht : 9 ≤ t) :
    t ^ 2 / 8 ≤ t ^ 2 / 4 + a ∧ 10 ≤ t ^ 2 / 4 + a := by
  have ha_lo : -4 ≤ a := (abs_le.mp ha).1
  have ht2 : 81 ≤ t ^ 2 := by nlinarith
  constructor <;> linarith

lemma p_compact_pos {a t : ℝ} (ha : |a| ≤ 4) (ht : 9 ≤ t) : 0 < t ^ 2 / 4 + a := by
  linarith [(p_compact_ge ha ht).2]

lemma k2_compact_eq {a z : ℝ} (ha : |a| ≤ 4) (hz : 10 ≤ z) : k2 a z = z ^ 2 / 4 + a := by
  have hp : 10 ≤ z ^ 2 / 4 + a := (p_compact_ge ha (by linarith)).2
  have hmax : max |a| 1 ^ ((1 : ℝ) / 3) ≤ 4 := by
    have hm : max |a| 1 ≤ 4 := max_le ha (by norm_num)
    calc max |a| 1 ^ ((1 : ℝ) / 3) ≤ 4 ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (by positivity) hm (by norm_num)
      _ ≤ 4 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := Real.rpow_one 4
  unfold k2
  rw [abs_of_nonneg (by linarith)]
  exact max_eq_left (by linarith)

lemma Mbal_compact_eq {a z : ℝ} (ha : |a| ≤ 4) (hz : 10 ≤ z) :
    Mbal a z = (z ^ 2 / 4 + a) ^ (-(1 / 4) : ℝ) := by
  unfold Mbal
  rw [k2_compact_eq ha hz]
  norm_num

lemma errorDensity_compact (a t : ℝ) (ha : |a| ≤ 4) (ht : 9 ≤ t) :
    LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a) (fun s => s / 2)
        (fun _ => 1 / 2) (fun _ => 0) t =
      (3 / 16 * (t ^ 2 / 4 + a) - 5 / 16 * a) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ) := by
  have hp : 0 < t ^ 2 / 4 + a := p_compact_pos ha ht
  unfold LiouvilleGreen.errorDensity
  have h1 : (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) =
      (t ^ 2 / 4 + a) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ) := by
    rw [← Real.rpow_one_add' hp.le (by norm_num)]
    norm_num
  rw [h1]
  ring

lemma abs_errorDensity_compact_le {a t : ℝ} (ha : |a| ≤ 4) (ht : 9 ≤ t) :
    |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a) (fun s => s / 2)
        (fun _ => 1 / 2) (fun _ => 0) t| ≤ 12 * t ^ (-3 : ℝ) := by
  have hp_ge := p_compact_ge ha ht
  have hp : 0 < t ^ 2 / 4 + a := by linarith [hp_ge.2]
  have ht0 : 0 < t := by linarith
  have hab : |3 / 16 * (t ^ 2 / 4 + a) - 5 / 16 * a| ≤ 1 / 2 * (t ^ 2 / 4 + a) := by
    obtain ⟨ha1, ha2⟩ := abs_le.mp ha
    rw [abs_le]
    constructor <;> linarith [hp_ge.2]
  have h1 : (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) =
      (t ^ 2 / 4 + a) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ) := by
    rw [← Real.rpow_one_add' hp.le (by norm_num)]
    norm_num
  have hed : |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a) (fun s => s / 2)
      (fun _ => 1 / 2) (fun _ => 0) t| ≤ 1 / 2 * (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) := by
    rw [errorDensity_compact a t ha ht, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hp _)]
    calc |3 / 16 * (t ^ 2 / 4 + a) - 5 / 16 * a| * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ)
        ≤ (1 / 2 * (t ^ 2 / 4 + a)) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ) := by gcongr
      _ = 1 / 2 * ((t ^ 2 / 4 + a) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ)) := by ring
      _ = 1 / 2 * (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) := by rw [← h1]
  have hrpow : (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) ≤ (t ^ 2 / 8) ^ (-(3 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hp_ge.1 (by norm_num)
  have h8 : (t ^ 2 / 8) ^ (-(3 / 2) : ℝ) = (8 : ℝ) ^ ((3 / 2) : ℝ) * t ^ (-3 : ℝ) := by
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    rw [Real.div_rpow ht2 (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8),
      div_inv_eq_mul, ← Real.rpow_natCast t 2, ← Real.rpow_mul ht0.le]
    have hmul : ((2 : ℕ) : ℝ) * -(3 / 2) = -3 := by norm_num
    rw [hmul]
    ring
  have h8_le : (8 : ℝ) ^ ((3 / 2) : ℝ) ≤ 24 := by
    have hsq : ((8 : ℝ) ^ ((3 / 2) : ℝ)) ^ 2 ≤ 24 ^ 2 := by
      rw [← Real.rpow_natCast ((8 : ℝ) ^ ((3 / 2) : ℝ)) 2, ← Real.rpow_mul (by norm_num)]
      norm_num
    exact (sq_le_sq₀ (by positivity) (by norm_num)).mp hsq
  calc |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a) (fun s => s / 2)
        (fun _ => 1 / 2) (fun _ => 0) t|
      ≤ 1 / 2 * (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) := hed
    _ ≤ 1 / 2 * (t ^ 2 / 8) ^ (-(3 / 2) : ℝ) := by gcongr
    _ = 1 / 2 * ((8 : ℝ) ^ ((3 / 2) : ℝ) * t ^ (-3 : ℝ)) := by rw [h8]
    _ ≤ 1 / 2 * (24 * t ^ (-3 : ℝ)) := by gcongr
    _ = 12 * t ^ (-3 : ℝ) := by ring

lemma integrableOn_abs_errorDensity_compact {a c : ℝ} (ha : |a| ≤ 4) (hc : 9 < c) :
    IntegrableOn (fun t => |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a)
      (fun s => s / 2) (fun _ => 1 / 2) (fun _ => 0) t|) (Ioi c) := by
  have hc0 : 0 < c := by linarith
  have hmaj : IntegrableOn (fun t : ℝ => 12 * t ^ (-3 : ℝ)) (Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hc0).const_mul 12
  have hcont : ContinuousOn (fun t => |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a)
      (fun s => s / 2) (fun _ => 1 / 2) (fun _ => 0) t|) (Ioi c) := by
    refine ContinuousOn.abs ?_
    refine ContinuousOn.congr (f := fun t => (3 / 16 * (t ^ 2 / 4 + a) - 5 / 16 * a) *
        (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ)) ?_ ?_
    · refine ContinuousOn.mul (by fun_prop) (ContinuousOn.rpow_const (by fun_prop) fun t ht => ?_)
      exact Or.inl (p_compact_pos ha (lt_trans hc (Set.mem_Ioi.mp ht)).le).ne'
    · intro t ht
      exact errorDensity_compact a t ha (lt_trans hc (Set.mem_Ioi.mp ht)).le
  refine hmaj.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_of_nonneg (abs_nonneg _)]
  exact abs_errorDensity_compact_le ha (lt_trans hc ht).le

lemma integral_abs_errorDensity_compact_le {a x : ℝ} (ha : |a| ≤ 4) (hx : 10 ≤ x) :
    ∫ t in Ioi x, |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a)
      (fun s => s / 2) (fun _ => 1 / 2) (fun _ => 0) t| ≤ 3 / 50 := by
  have hx9 : 9 < x := by linarith
  have hx0 : 0 < x := by linarith
  have h_ed := integrableOn_abs_errorDensity_compact ha hx9
  have h_maj : IntegrableOn (fun t : ℝ => 12 * t ^ (-3 : ℝ)) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hx0).const_mul 12
  have hle : ∫ t in Ioi x, |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a)
        (fun s => s / 2) (fun _ => 1 / 2) (fun _ => 0) t| ≤
      ∫ t in Ioi x, 12 * t ^ (-3 : ℝ) := by
    refine setIntegral_mono_on h_ed h_maj measurableSet_Ioi fun t ht => ?_
    exact abs_errorDensity_compact_le ha (by linarith [Set.mem_Ioi.mp ht])
  have hanti : ∀ t : ℝ, x ≤ t → HasDerivAt (fun s : ℝ => -6 * s ^ (-2 : ℝ)) (12 * t ^ (-3 : ℝ)) t :=
    fun t ht => by
      have ht0 : t ≠ 0 := by linarith
      refine ((Real.hasDerivAt_rpow_const (p := (-2 : ℝ)) (Or.inl ht0)).const_mul (-6)).congr_deriv ?_
      rw [show (-2 : ℝ) - 1 = -3 by norm_num]
      ring
  have htend : Tendsto (fun s : ℝ => -6 * s ^ (-2 : ℝ)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun s : ℝ => s ^ (-2 : ℝ)) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    simpa [mul_zero] using h0.const_mul (-6)
  have hint_eq : ∫ t in Ioi x, 12 * t ^ (-3 : ℝ) = 0 - (-6 * x ^ (-2 : ℝ)) :=
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun t ht => hanti t ht) h_maj htend
  have hx2 : x ^ (-2 : ℝ) ≤ (100 : ℝ)⁻¹ := by
    have h1 : (100 : ℝ) ≤ x ^ 2 := by nlinarith
    have h2 : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
      rw [← Real.rpow_natCast x 2, ← Real.rpow_neg (by positivity)]
      norm_num
    rw [h2]
    exact inv_anti₀ (by norm_num) h1
  calc ∫ t in Ioi x, |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a)
        (fun s => s / 2) (fun _ => 1 / 2) (fun _ => 0) t|
      ≤ ∫ t in Ioi x, 12 * t ^ (-3 : ℝ) := hle
    _ = 6 * x ^ (-2 : ℝ) := by linarith [hint_eq]
    _ ≤ 6 * (100 : ℝ)⁻¹ := by gcongr
    _ = 3 / 50 := by norm_num

lemma pcU_compact_far_lg {a : ℝ} (ha : |a| ≤ 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ z, 10 ≤ z →
      (1 / 2 * (Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) * Mbal a z) ≤ pcU a z / c ∧
        pcU a z / c ≤ 5 / 4 * (Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) * Mbal a z)) ∧
      |deriv (pcU a) z / c| ≤
        2 * Real.sqrt (k2 a z) * (Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) * Mbal a z) := by
  let a0 : ℝ := 9
  let p : ℝ → ℝ := fun t => t ^ 2 / 4 + a
  let p' : ℝ → ℝ := fun t => t / 2
  let p'' : ℝ → ℝ := fun _ => 1 / 2
  let g : ℝ → ℝ := fun _ => 0
  let ξ : ℝ → ℝ := fun t => ∫ s in (10 : ℝ)..t, Real.sqrt (p s)
  have hp_pos : ∀ x, a0 < x → 0 < p x := fun x hx => p_compact_pos ha hx.le
  have hp' : ∀ x, a0 < x → HasDerivAt p (p' x) x := fun x _ => by
    refine (((hasDerivAt_pow 2 x).div_const 4).add_const a).congr_deriv ?_
    ring
  have hp'' : ∀ x, a0 < x → HasDerivAt p' (p'' x) x := fun x _ => by
    simpa [p', p''] using (hasDerivAt_id x).div_const 2
  have hξ_deriv : ∀ x : ℝ, HasDerivAt ξ (Real.sqrt (p x)) x := fun x => by
    have hcont : Continuous (fun s => Real.sqrt (p s)) :=
      Real.continuous_sqrt.comp (by continuity)
    exact intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 10 x) (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  obtain ⟨ε, ε', w', hLG⟩ := LiouvilleGreen.exists_solution_exp_of_pos (a := a0) (u := 1)
    one_pos hp_pos hp' hp'' continuousOn_const continuousOn_const (fun x _ => hξ_deriv x)
    (fun c hc => integrableOn_abs_errorDensity_compact ha hc)
  let w : ℝ → ℝ := fun y => p y ^ (-(1 / 4) : ℝ) * Real.exp (-ξ y) * (1 + ε y)
  have hw_deriv : ∀ x, a0 < x → HasDerivAt w (w' x) x := fun x hx => by
    simpa [w, one_mul] using (hLG x hx).2.1
  have hw'_deriv : ∀ x, a0 < x → HasDerivAt w' (p x * w x) x := fun x hx => by
    simpa [w, g, one_mul] using (hLG x hx).2.2.1
  have hε_bd : ∀ x, 10 ≤ x → |ε x| < 1 / 4 := fun x hx => by
    have hx_a0 : a0 < x := by linarith
    have h1 := (hLG x hx_a0).2.2.2.1
    have hV := integral_abs_errorDensity_compact_le ha hx
    have hV' : (∫ t in Ioi x, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1) ≤ 5 / 96 := by
      linarith
    have hexp : Real.exp ((∫ t in Ioi x, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1)) < 5 / 4 :=
      lt_of_le_of_lt (Real.exp_le_exp.mpr hV') exp_five_ninetysixths_lt
    linarith
  have hw_pos : ∀ x, 10 ≤ x → 0 < w x := fun x hx => by
    have h1 : 0 < 1 + ε x := by linarith [(abs_lt.mp (hε_bd x hx)).1]
    have h2 : 0 < p x ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos (hp_pos x (by linarith)) _
    have h3 : 0 < Real.exp (-ξ x) := Real.exp_pos _
    positivity
  have hw'_eq : ∀ x, a0 < x →
      w' x = p x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) *
        ((-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x) + ε' x) := by
    intro x hx
    have hpx := hp_pos x hx
    have hA : HasDerivAt (fun y => p y ^ (-(1 / 4) : ℝ))
        (p x ^ (-(1 / 4) : ℝ) * (-(1 / 4) * (x / 2) / p x)) x := by
      refine ((hp' x hx).rpow_const (p := -(1 / 4)) (Or.inl hpx.ne')).congr_deriv ?_
      have hsub : p x ^ (-(1 / 4) - 1 : ℝ) = p x ^ (-(1 / 4) : ℝ) * (p x)⁻¹ := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hpx]; norm_num
      rw [hsub]; simp only [p']; ring
    have hE : HasDerivAt (fun y => Real.exp (-ξ y)) (Real.exp (-ξ x) * (-Real.sqrt (p x))) x := by
      simpa using (hξ_deriv x).neg.exp
    have hAE : HasDerivAt (fun y => p y ^ (-(1 / 4) : ℝ) * Real.exp (-ξ y))
        (p x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) * (-(1 / 4) * (x / 2) / p x - Real.sqrt (p x))) x := by
      refine (hA.mul hE).congr_deriv ?_; ring
    have hfull : HasDerivAt w
        (p x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) *
          ((-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x) + ε' x)) x := by
      have h1ε : HasDerivAt (fun y => 1 + ε y) (ε' x) x :=
        ((hasDerivAt_const x 1).add (hLG x hx).1).congr_deriv (by ring)
      refine (hAE.mul h1ε).congr_deriv ?_; ring
    exact (hw_deriv x hx).unique hfull
  let W : ℝ → ℝ := fun x => pcU a x * w' x - pcUD a x * w x
  have hW_deriv : ∀ x, a0 < x → HasDerivAt W 0 x := fun x hx => by
    have hU := hasDerivAt_pcU a x
    have hUD : HasDerivAt (pcUD a) (p x * pcU a x) x := by
      simpa [p] using hasDerivAt_pcUD a x
    refine ((hU.mul (hw'_deriv x hx)).sub (hUD.mul (hw_deriv x hx))).congr_deriv ?_
    ring
  have hW_const : ∀ x, a0 < x → W x = W 10 := fun x hx =>
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun y hy => (hW_deriv y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hW_deriv y hy).deriv) hx (by norm_num)
  have hξ_nonneg : ∀ x : ℝ, 10 ≤ x → 0 ≤ ξ x := fun x hx =>
    intervalIntegral.integral_nonneg hx (fun t _ => Real.sqrt_nonneg _)
  have hw_bd : ∀ x : ℝ, 10 ≤ x → |w x| ≤ 2 := fun x hx => by
    have hpx : 1 ≤ p x := by dsimp [p]; linarith [(p_compact_ge ha (by linarith)).2]
    have hp14 : p x ^ (-(1 / 4) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hpx (by norm_num)
    have hexp : Real.exp (-ξ x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hξ_nonneg x hx])
    have h1ε : |1 + ε x| ≤ 2 := by
      have := abs_lt.mp (hε_bd x hx)
      rw [abs_le]; constructor <;> linarith
    rw [show w x = p x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) * (1 + ε x) from rfl,
      abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hp_pos x (by linarith)) _),
      abs_of_pos (Real.exp_pos _)]
    calc p x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) * |1 + ε x| ≤ 1 * 1 * 2 := by gcongr
      _ = 2 := by ring
  have hw'_bd : ∀ x : ℝ, 10 ≤ x → |w' x| ≤ 2 * (1 + x) := fun x hx => by
    have hx_a0 : a0 < x := by linarith
    rw [hw'_eq x hx_a0]
    have hp_ge := p_compact_ge ha (by linarith : 9 ≤ x)
    have hpx_pos : 0 < p x := by dsimp [p]; linarith [hp_ge.2]
    have hp14 : p x ^ (-(1 / 4) : ℝ) ≤ 1 := by
      dsimp [p]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hp_ge.2]) (by norm_num)
    have hexp : Real.exp (-ξ x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hξ_nonneg x hx])
    have hsqp : Real.sqrt (p x) ≤ x := by
      have ha_hi : a ≤ 4 := (abs_le.mp ha).2
      have hle : p x ≤ x ^ 2 := by dsimp [p]; nlinarith
      calc Real.sqrt (p x) ≤ Real.sqrt (x ^ 2) := Real.sqrt_le_sqrt hle
        _ = x := Real.sqrt_sq (by linarith)
    have hp_frac : |-(1 / 4) * (x / 2) / p x| ≤ 1 / 8 * Real.sqrt (p x) := by
      have hdiv : x / p x ≤ Real.sqrt (p x) := by
        rw [div_le_iff₀ hpx_pos]
        have hsq3 : 1 ≤ Real.sqrt (p x) := by
          rw [← Real.sqrt_one]; dsimp [p]; exact Real.sqrt_le_sqrt (by linarith [hp_ge.2])
        have hx8 : x ≤ p x := by
          have : 10 * x / 8 ≤ x ^ 2 / 8 := by nlinarith
          dsimp [p]; linarith [hp_ge.1]
        nlinarith
      rw [abs_div, abs_of_pos hpx_pos, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x / 2)]
      norm_num
      have : 1 / 4 * (x / 2) / p x = 1 / 8 * (x / p x) := by ring
      linarith
    have h1ε : |1 + ε x| ≤ 5 / 4 := by
      have := abs_lt.mp (hε_bd x hx)
      rw [abs_le]; constructor <;> linarith
    have hε' : |ε' x| ≤ 1 / 2 * Real.sqrt (p x) := by
      have h2 := (hLG x hx_a0).2.2.2.2
      have hV := integral_abs_errorDensity_compact_le ha hx
      have hV' : (∫ t in Ioi x, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1) ≤ 5 / 96 := by
        linarith
      have hexp2 : Real.exp ((∫ t in Ioi x, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1)) - 1 ≤ 1 / 4 := by
        linarith [Real.exp_le_exp.mpr hV', exp_five_ninetysixths_lt]
      calc |ε' x| ≤ 2 * 1 * Real.sqrt (p x) *
            (Real.exp ((∫ t in Ioi x, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1)) - 1) := h2
        _ ≤ 2 * 1 * Real.sqrt (p x) * (1 / 4) := by gcongr
        _ = 1 / 2 * Real.sqrt (p x) := by ring
    have hterm : |(-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x) + ε' x| ≤ 2 * (1 + x) := by
      have hsub : |-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)| ≤ 9 / 8 * x := by
        calc |-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)|
            ≤ |-(1 / 4) * (x / 2) / p x| + |Real.sqrt (p x)| := abs_sub _ _
          _ ≤ 1 / 8 * Real.sqrt (p x) + Real.sqrt (p x) := by
              rw [abs_of_nonneg (Real.sqrt_nonneg _)]; linarith
          _ = 9 / 8 * Real.sqrt (p x) := by ring
          _ ≤ 9 / 8 * x := by gcongr
      calc |(-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x) + ε' x|
          ≤ |(-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x)| + |ε' x| := abs_add_le _ _
        _ = |-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)| * |1 + ε x| + |ε' x| := by rw [abs_mul]
        _ ≤ (9 / 8 * x) * (5 / 4) + 1 / 2 * x := by
            have hε'_x : |ε' x| ≤ 1 / 2 * x := le_trans hε' (by gcongr)
            gcongr
        _ ≤ 2 * (1 + x) := by linarith
    rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hpx_pos _), abs_of_pos (Real.exp_pos _)]
    calc p x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) *
          |(-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x) + ε' x|
        ≤ 1 * 1 * (2 * (1 + x)) := by gcongr
      _ = 2 * (1 + x) := by ring
  have hW_tendsto : Tendsto W atTop (𝓝 0) := by
    have ht1 : Tendsto (fun x : ℝ => pcU a x * w' x) atTop (𝓝 0) := by
      have hlin : Tendsto (fun x : ℝ => 2 * |(1 + x) * pcU a x|) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_pcU_mul_linear_all a).abs.const_mul 2
      rw [tendsto_zero_iff_abs_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun x => abs_nonneg _) ?_ hlin
      filter_upwards [eventually_ge_atTop (10 : ℝ)] with x hx
      dsimp only [Function.comp_apply]
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + x)]
      calc |pcU a x| * |w' x| ≤ |pcU a x| * (2 * (1 + x)) := by gcongr; exact hw'_bd x hx
        _ = 2 * ((1 + x) * |pcU a x|) := by ring
    have ht2 : Tendsto (fun x : ℝ => pcUD a x * w x) atTop (𝓝 0) := by
      have hlin : Tendsto (fun x : ℝ => 2 * |pcUD a x|) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_pcUD_all a).abs.const_mul 2
      rw [tendsto_zero_iff_abs_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun x => abs_nonneg _) ?_ hlin
      filter_upwards [eventually_ge_atTop (10 : ℝ)] with x hx
      dsimp only [Function.comp_apply]
      rw [abs_mul]
      calc |pcUD a x| * |w x| ≤ |pcUD a x| * 2 := by gcongr; exact hw_bd x hx
        _ = 2 * |pcUD a x| := by ring
    simpa [W] using ht1.sub ht2
  have hW_zero : ∀ x, 10 ≤ x → W x = 0 := by
    have hW10 : W 10 = 0 := by
      have hconst : Tendsto W atTop (𝓝 (W 10)) :=
        tendsto_const_nhds.congr' (by
          filter_upwards [eventually_gt_atTop (10 : ℝ)] with x hx
          exact (hW_const x (by linarith)).symm)
      exact tendsto_nhds_unique hconst hW_tendsto
    intro x hx
    rw [hW_const x (by linarith), hW10]
  have hdiv_deriv : ∀ x, 10 ≤ x → HasDerivAt (fun y => pcU a y / w y) 0 x := fun x hx => by
    have h := (hasDerivAt_pcU a x).div (hw_deriv x (by linarith)) (hw_pos x hx).ne'
    refine h.congr_deriv ?_
    have hW0 := hW_zero x hx
    dsimp [W] at hW0
    have e : pcUD a x * w x - pcU a x * w' x = 0 := by linarith
    rw [e, zero_div]
  let c : ℝ := pcU a 11 / w 11
  have hpcU_gt : ∀ z, 10 < z → pcU a z = c * w z := fun z hz => by
    have hconst : pcU a z / w z = c :=
      isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        (fun y hy => (hdiv_deriv y (le_of_lt hy)).differentiableAt.differentiableWithinAt)
        (fun y hy => (hdiv_deriv y (le_of_lt hy)).deriv) hz (Set.mem_Ioi.mpr (by norm_num))
    exact (div_eq_iff (hw_pos z hz.le).ne').mp hconst
  have hpcU_eq : ∀ z, 10 ≤ z → pcU a z = c * w z := fun z hz => by
    rcases eq_or_lt_of_le hz with rfl | hgt
    · have hL : Tendsto (pcU a) (𝓝[>] (10 : ℝ)) (𝓝 (pcU a 10)) :=
        (hasDerivAt_pcU a 10).continuousAt.continuousWithinAt
      have hR : Tendsto (fun y => c * w y) (𝓝[>] (10 : ℝ)) (𝓝 (c * w 10)) :=
        ((hw_deriv 10 (by norm_num)).continuousAt.const_mul c).continuousWithinAt
      refine tendsto_nhds_unique (hL.congr' ?_) hR
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hpcU_gt y hy
    · exact hpcU_gt z hgt
  have hpcUD_eq : ∀ z, 10 ≤ z → deriv (pcU a) z = c * w' z := fun z hz => by
    have hgt : ∀ y, 10 < y → deriv (pcU a) y = c * w' y := fun y hy => by
      have hU' : HasDerivAt (pcU a) (c * w' y) y := by
        refine ((hw_deriv y (by linarith)).const_mul c).congr_of_eventuallyEq ?_
        filter_upwards [Ioi_mem_nhds hy] with t ht
        exact hpcU_gt t ht
      exact hU'.deriv
    rcases eq_or_lt_of_le hz with rfl | hgt_z
    · have hL : Tendsto (deriv (pcU a)) (𝓝[>] (10 : ℝ)) (𝓝 (deriv (pcU a) 10)) := by
        rw [deriv_pcU]
        exact (hasDerivAt_pcUD a 10).continuousAt.continuousWithinAt
      have hR : Tendsto (fun y => c * w' y) (𝓝[>] (10 : ℝ)) (𝓝 (c * w' 10)) :=
        ((hw'_deriv 10 (by norm_num)).continuousAt.const_mul c).continuousWithinAt
      refine tendsto_nhds_unique (hL.congr' ?_) hR
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hgt y hy
    · exact hgt z hgt_z
  have hc_pos : 0 < c := by
    have hturn : 2 * Real.sqrt (max (-a) 0) ≤ 10 := by
      have hm : max (-a) 0 ≤ 4 := max_le (by linarith [(abs_le.mp ha).1]) (by norm_num)
      calc 2 * Real.sqrt (max (-a) 0) ≤ 2 * Real.sqrt 4 := by gcongr
        _ = 4 := by norm_num
        _ ≤ 10 := by norm_num
    have hUpos := pcU_pos_beyond a 10 hturn
    rw [hpcU_eq 10 le_rfl] at hUpos
    exact pos_of_mul_pos_left hUpos (hw_pos 10 le_rfl).le
  refine ⟨c, hc_pos, fun z hz => ?_⟩
  have hz_a0 : a0 < z := by linarith
  have hM : Mbal a z = p z ^ (-(1 / 4) : ℝ) := Mbal_compact_eq ha hz
  have hk : k2 a z = p z := k2_compact_eq ha hz
  have hp_ge := p_compact_ge ha (by linarith : 9 ≤ z)
  have hpx_pos : 0 < p z := by dsimp [p]; linarith [hp_ge.2]
  constructor
  · rw [hpcU_eq z hz, mul_div_cancel_left₀ _ hc_pos.ne']
    have hε := abs_lt.mp (hε_bd z hz)
    have hME_nonneg : 0 ≤ Real.exp (-ξ z) * Mbal a z :=
      mul_nonneg (Real.exp_pos _).le (Mbal_pos a z).le
    have hw_eq : w z = Real.exp (-ξ z) * Mbal a z * (1 + ε z) := by
      dsimp [w]; rw [hM]; ring
    rw [hw_eq]
    constructor
    · calc 1 / 2 * (Real.exp (-ξ z) * Mbal a z)
          ≤ (3 / 4) * (Real.exp (-ξ z) * Mbal a z) := by nlinarith
        _ ≤ (1 + ε z) * (Real.exp (-ξ z) * Mbal a z) := by
            gcongr; linarith
        _ = Real.exp (-ξ z) * Mbal a z * (1 + ε z) := by ring
    · calc Real.exp (-ξ z) * Mbal a z * (1 + ε z)
          = (1 + ε z) * (Real.exp (-ξ z) * Mbal a z) := by ring
        _ ≤ (5 / 4) * (Real.exp (-ξ z) * Mbal a z) := by
            gcongr; linarith
  · rw [hpcUD_eq z hz, mul_div_cancel_left₀ _ hc_pos.ne', hw'_eq z hz_a0, hM, hk]
    have hp_frac : |-(1 / 4) * (z / 2) / p z| ≤ 1 / 8 * Real.sqrt (p z) := by
      have hdiv : z / p z ≤ Real.sqrt (p z) := by
        rw [div_le_iff₀ hpx_pos]
        have hsq3 : 1 ≤ Real.sqrt (p z) := by
          rw [← Real.sqrt_one]; dsimp [p]; exact Real.sqrt_le_sqrt (by linarith [hp_ge.2])
        have hz8 : z ≤ p z := by
          have : 10 * z / 8 ≤ z ^ 2 / 8 := by nlinarith
          dsimp [p]; linarith [hp_ge.1]
        nlinarith
      rw [abs_div, abs_of_pos hpx_pos, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ z / 2)]
      norm_num
      have : 1 / 4 * (z / 2) / p z = 1 / 8 * (z / p z) := by ring
      linarith
    have h1ε : |1 + ε z| ≤ 5 / 4 := by
      have := abs_lt.mp (hε_bd z hz)
      rw [abs_le]; constructor <;> linarith
    have hε' : |ε' z| ≤ 1 / 2 * Real.sqrt (p z) := by
      have h2 := (hLG z hz_a0).2.2.2.2
      have hV := integral_abs_errorDensity_compact_le ha hz
      have hV' : (∫ t in Ioi z, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1) ≤ 5 / 96 := by
        linarith
      have hexp2 : Real.exp ((∫ t in Ioi z, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1)) - 1 ≤ 1 / 4 := by
        linarith [Real.exp_le_exp.mpr hV', exp_five_ninetysixths_lt]
      calc |ε' z| ≤ 2 * 1 * Real.sqrt (p z) *
            (Real.exp ((∫ t in Ioi z, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1)) - 1) := h2
        _ ≤ 2 * 1 * Real.sqrt (p z) * (1 / 4) := by gcongr
        _ = 1 / 2 * Real.sqrt (p z) := by ring
    have hterm : |(-(1 / 4) * (z / 2) / p z - Real.sqrt (p z)) * (1 + ε z) + ε' z| ≤
        2 * Real.sqrt (p z) := by
      have hsub : |-(1 / 4) * (z / 2) / p z - Real.sqrt (p z)| ≤ 9 / 8 * Real.sqrt (p z) := by
        calc |-(1 / 4) * (z / 2) / p z - Real.sqrt (p z)|
            ≤ |-(1 / 4) * (z / 2) / p z| + |Real.sqrt (p z)| := abs_sub _ _
          _ ≤ 1 / 8 * Real.sqrt (p z) + Real.sqrt (p z) := by
              rw [abs_of_nonneg (Real.sqrt_nonneg _)]; linarith
          _ = 9 / 8 * Real.sqrt (p z) := by ring
      calc |(-(1 / 4) * (z / 2) / p z - Real.sqrt (p z)) * (1 + ε z) + ε' z|
          ≤ |(-(1 / 4) * (z / 2) / p z - Real.sqrt (p z)) * (1 + ε z)| + |ε' z| := abs_add_le _ _
        _ = |-(1 / 4) * (z / 2) / p z - Real.sqrt (p z)| * |1 + ε z| + |ε' z| := by rw [abs_mul]
        _ ≤ (9 / 8 * Real.sqrt (p z)) * (5 / 4) + 1 / 2 * Real.sqrt (p z) := by gcongr
        _ ≤ 2 * Real.sqrt (p z) := by linarith [Real.sqrt_nonneg (p z)]
    rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hpx_pos _), abs_of_pos (Real.exp_pos _)]
    calc p z ^ (-(1 / 4) : ℝ) * Real.exp (-ξ z) *
          |(-(1 / 4) * (z / 2) / p z - Real.sqrt (p z)) * (1 + ε z) + ε' z|
        ≤ p z ^ (-(1 / 4) : ℝ) * Real.exp (-ξ z) * (2 * Real.sqrt (p z)) := by gcongr
      _ = 2 * Real.sqrt (p z) * (Real.exp (-ξ z) * p z ^ (-(1 / 4) : ℝ)) := by ring

/-! ### Section 3: Normalised tail `pcU`, tail `pcV`, and tail `pcU(a, -z)` -/

lemma Ewell_compact_far_eq {a z : ℝ} (ha : -4 ≤ a) (ha0 : a ≤ 0) (hz : 10 ≤ z) :
    Ewell a z = Ewell a 10 * Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) := by
  have h4 : 2 * Real.sqrt |a| < 10 := by
    have ha_abs : |a| ≤ 4 := abs_le.mpr ⟨ha, by linarith⟩
    calc 2 * Real.sqrt |a| ≤ 2 * Real.sqrt 4 := by gcongr
      _ = 4 := by norm_num
      _ < 10 := by norm_num
  have hz_lt : 2 * Real.sqrt |a| < z := lt_of_lt_of_le h4 hz
  unfold Ewell
  simp only [hz_lt, h4, ↓reduceIte]
  have hsub : ∀ s : ℝ, s ^ 2 / 4 - |a| = s ^ 2 / 4 + a := fun s => by
    rw [abs_of_nonpos ha0]; ring
  simp_rw [hsub]
  have hcont : Continuous (fun s : ℝ => Real.sqrt (s ^ 2 / 4 + a)) :=
    Real.continuous_sqrt.comp (by continuity)
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (a := 2 * Real.sqrt |a|) (b := 10) (c := z) (μ := volume)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  rw [← hadd, neg_add, Real.exp_add]

lemma Ebar_compact_far_eq {a z : ℝ} :
    Ebar a z = Ebar a 10 * Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) := by
  unfold Ebar
  have hcont : Continuous (fun s : ℝ => Real.sqrt (s ^ 2 / 4 + a)) :=
    Real.continuous_sqrt.comp (by continuity)
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (a := (0 : ℝ)) (b := 10) (c := z) (μ := volume)
    (hcont.intervalIntegrable 0 10) (hcont.intervalIntegrable 10 z)
  rw [← hadd, neg_add, Real.exp_add]

lemma tail_U_well :
    ∃ cU CU : ℝ, 0 < cU ∧ cU ≤ CU ∧
      ∀ a, -4 ≤ a → a ≤ 0 → ∀ z, 10 ≤ z →
        (cU * (Ewell a z * Mbal a z) ≤ ut pcU a z ∧
          ut pcU a z ≤ CU * (Ewell a z * Mbal a z)) ∧
        |kappaBal a * deriv (pcU a) z| ≤ CU * Real.sqrt (k2 a z) * (Ewell a z * Mbal a z) ∧
        Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) ≤
          3 * CU * (Ewell a z * Mbal a z) := by
  obtain ⟨c_box, C_box, hc_box, hle_box, hbox⟩ := compact_box_well
  refine ⟨c_box / 6, 4 * C_box, by positivity, by linarith, fun a ha4 ha0 z hz => ?_⟩
  have ha_abs : |a| ≤ 4 := abs_le.mpr ⟨ha4, by linarith⟩
  obtain ⟨c, hc_pos, hlg⟩ := pcU_compact_far_lg ha_abs
  have hκ := kappaBal_pos a
  have hE10_pos : 0 < Ewell a 10 :=
    lt_of_lt_of_le (Real.exp_pos _) (Ewell_box_bounds ha4 ha0 (by norm_num) le_rfl).1
  have hM10_pos : 0 < Mbal a 10 := Mbal_pos a 10
  have hk10_pos : 0 < k2 a 10 := k2_pos a 10
  -- Normalise `kappaBal a * c` at `z = 10`
  have hlg10 := hlg 10 le_rfl
  simp only [intervalIntegral.integral_same, neg_zero, Real.exp_zero, one_mul] at hlg10
  have hbox10 := (hbox a ha4 ha0 10 (by norm_num) le_rfl).1
  have hscale10 : Real.sqrt (ut pcU a 10 ^ 2 + (kappaBal a * deriv (pcU a) 10) ^ 2 / k2 a 10) =
      (kappaBal a * c) * Real.sqrt ((pcU a 10 / c) ^ 2 + (deriv (pcU a) 10 / c) ^ 2 / k2 a 10) := by
    have hkc : 0 ≤ kappaBal a * c := mul_nonneg hκ.le hc_pos.le
    unfold ut
    rw [← Real.sqrt_sq hkc, ← Real.sqrt_mul (sq_nonneg _)]
    congr 1; field_simp [hc_pos.ne']
  have hnorm_lo : 1 / 2 * Mbal a 10 ≤
      Real.sqrt ((pcU a 10 / c) ^ 2 + (deriv (pcU a) 10 / c) ^ 2 / k2 a 10) := by
    calc 1 / 2 * Mbal a 10 ≤ pcU a 10 / c := hlg10.1.1
      _ ≤ |pcU a 10 / c| := le_abs_self _
      _ = Real.sqrt ((pcU a 10 / c) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((pcU a 10 / c) ^ 2 + (deriv (pcU a) 10 / c) ^ 2 / k2 a 10) :=
          Real.sqrt_le_sqrt (le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hk10_pos.le))
  have hnorm_hi : Real.sqrt ((pcU a 10 / c) ^ 2 + (deriv (pcU a) 10 / c) ^ 2 / k2 a 10) ≤
      3 * Mbal a 10 := by
    have h1 : (pcU a 10 / c) ^ 2 ≤ (5 / 4 * Mbal a 10) ^ 2 :=
      pow_le_pow_left₀ (by linarith [hlg10.1.1]) hlg10.1.2 2
    have h2 : (deriv (pcU a) 10 / c) ^ 2 / k2 a 10 ≤ (2 * Mbal a 10) ^ 2 := by
      have hsq : (deriv (pcU a) 10 / c) ^ 2 ≤ (2 * Real.sqrt (k2 a 10) * Mbal a 10) ^ 2 := by
        rw [← sq_abs (deriv (pcU a) 10 / c)]
        exact pow_le_pow_left₀ (abs_nonneg _) hlg10.2 2
      calc (deriv (pcU a) 10 / c) ^ 2 / k2 a 10
          ≤ (2 * Real.sqrt (k2 a 10) * Mbal a 10) ^ 2 / k2 a 10 :=
            div_le_div_of_nonneg_right hsq hk10_pos.le
        _ = 4 * (Real.sqrt (k2 a 10) ^ 2) * Mbal a 10 ^ 2 / k2 a 10 := by ring
        _ = 4 * k2 a 10 * Mbal a 10 ^ 2 / k2 a 10 := by rw [Real.sq_sqrt hk10_pos.le]
        _ = (2 * Mbal a 10) ^ 2 := by field_simp [hk10_pos.ne']; ring
    have hsum : (pcU a 10 / c) ^ 2 + (deriv (pcU a) 10 / c) ^ 2 / k2 a 10 ≤ (3 * Mbal a 10) ^ 2 := by
      linarith [sq_nonneg (Mbal a 10)]
    calc Real.sqrt ((pcU a 10 / c) ^ 2 + (deriv (pcU a) 10 / c) ^ 2 / k2 a 10)
        ≤ Real.sqrt ((3 * Mbal a 10) ^ 2) := Real.sqrt_le_sqrt hsum
      _ = 3 * Mbal a 10 := Real.sqrt_sq (by positivity)
  have hkc_lo : c_box / 3 * Ewell a 10 ≤ kappaBal a * c := by
    have h1 : c_box * Ewell a 10 * Mbal a 10 ≤ (kappaBal a * c) * (3 * Mbal a 10) :=
      hbox10.1.trans (hscale10 ▸ mul_le_mul_of_nonneg_left hnorm_hi (mul_nonneg hκ.le hc_pos.le))
    have h2 : (c_box / 3 * Ewell a 10) * (3 * Mbal a 10) ≤ (kappaBal a * c) * (3 * Mbal a 10) := by
      linarith
    exact le_of_mul_le_mul_right h2 (by positivity)
  have hkc_hi : kappaBal a * c ≤ 2 * C_box * Ewell a 10 := by
    have h1 : (kappaBal a * c) * (1 / 2 * Mbal a 10) ≤ C_box * Ewell a 10 * Mbal a 10 :=
      (hscale10 ▸ mul_le_mul_of_nonneg_left hnorm_lo (mul_nonneg hκ.le hc_pos.le)).trans hbox10.2
    have h2 : (kappaBal a * c) * (1 / 2 * Mbal a 10) ≤ (2 * C_box * Ewell a 10) * (1 / 2 * Mbal a 10) := by
      linarith
    exact le_of_mul_le_mul_right h2 (by positivity)
  -- Now evaluate at `z ≥ 10`
  have hlgz := hlg z hz
  have hEz : Ewell a z = Ewell a 10 * Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) :=
    Ewell_compact_far_eq ha4 ha0 hz
  have hM_pos : 0 < Mbal a z := Mbal_pos a z
  have hk_pos : 0 < k2 a z := k2_pos a z
  have hexp_pos : 0 < Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) := Real.exp_pos _
  have hut_eq : ut pcU a z = (kappaBal a * c) * (pcU a z / c) := by
    unfold ut; field_simp [hc_pos.ne']
  have hud_eq : |kappaBal a * deriv (pcU a) z| = (kappaBal a * c) * |deriv (pcU a) z / c| := by
    rw [show kappaBal a * deriv (pcU a) z = (kappaBal a * c) * (deriv (pcU a) z / c) by
          field_simp [hc_pos.ne'],
        abs_mul, abs_of_pos (mul_pos hκ hc_pos)]
  have hut_lo : c_box / 6 * (Ewell a z * Mbal a z) ≤ ut pcU a z := by
    rw [hut_eq, hEz]
    calc c_box / 6 * (Ewell a 10 * Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) * Mbal a z)
        = (c_box / 3 * Ewell a 10) * (1 / 2 * (Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) * Mbal a z)) := by ring
      _ ≤ (kappaBal a * c) * (pcU a z / c) :=
          mul_le_mul hkc_lo hlgz.1.1 (by positivity) (mul_nonneg hκ.le hc_pos.le)
  have hut_hi : ut pcU a z ≤ 4 * C_box * (Ewell a z * Mbal a z) := by
    rw [hut_eq, hEz]
    calc (kappaBal a * c) * (pcU a z / c)
        ≤ (2 * C_box * Ewell a 10) * (5 / 4 * (Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) * Mbal a z)) :=
          mul_le_mul hkc_hi hlgz.1.2 (by linarith [hlgz.1.1]) (mul_nonneg (mul_nonneg (by positivity) (by linarith [hc_box, hle_box])) hE10_pos.le)
      _ = 5 / 2 * C_box * (Ewell a 10 * Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) * Mbal a z) := by ring
      _ ≤ 4 * C_box * (Ewell a 10 * Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) * Mbal a z) := by
          have hEM : 0 ≤ Ewell a 10 * Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) * Mbal a z :=
            mul_nonneg (mul_nonneg hE10_pos.le hexp_pos.le) hM_pos.le
          nlinarith
  have hud_hi : |kappaBal a * deriv (pcU a) z| ≤ 4 * C_box * Real.sqrt (k2 a z) * (Ewell a z * Mbal a z) := by
    rw [hud_eq, hEz]
    calc (kappaBal a * c) * |deriv (pcU a) z / c|
        ≤ (2 * C_box * Ewell a 10) * (2 * Real.sqrt (k2 a z) *
            (Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) * Mbal a z)) :=
          mul_le_mul hkc_hi hlgz.2 (abs_nonneg _) (mul_nonneg (mul_nonneg (by positivity) (by linarith [hc_box, hle_box])) hE10_pos.le)
      _ = 4 * C_box * Real.sqrt (k2 a z) *
            (Ewell a 10 * Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) * Mbal a z) := by ring
  refine ⟨⟨hut_lo, hut_hi⟩, hud_hi, ?_⟩
  have hut_nn : 0 ≤ ut pcU a z := by
    have hEM : 0 ≤ Ewell a z * Mbal a z :=
      mul_nonneg (by rw [hEz]; exact mul_nonneg hE10_pos.le hexp_pos.le) hM_pos.le
    exact le_trans (mul_nonneg (by positivity) hEM) hut_lo
  have hsum : ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z ≤
      (3 * (4 * C_box) * (Ewell a z * Mbal a z)) ^ 2 := by
    have h1 : ut pcU a z ^ 2 ≤ (4 * C_box * (Ewell a z * Mbal a z)) ^ 2 := by
      rw [← sq_abs (ut pcU a z), abs_of_nonneg hut_nn]
      exact pow_le_pow_left₀ hut_nn hut_hi 2
    have h2 : (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z ≤
        (4 * C_box * (Ewell a z * Mbal a z)) ^ 2 := by
      have hsq : (kappaBal a * deriv (pcU a) z) ^ 2 ≤
          (4 * C_box * Real.sqrt (k2 a z) * (Ewell a z * Mbal a z)) ^ 2 := by
        rw [← sq_abs (kappaBal a * deriv (pcU a) z)]
        exact pow_le_pow_left₀ (abs_nonneg _) hud_hi 2
      calc (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z
          ≤ (4 * C_box * Real.sqrt (k2 a z) * (Ewell a z * Mbal a z)) ^ 2 / k2 a z :=
            div_le_div_of_nonneg_right hsq hk_pos.le
        _ = (4 * C_box * (Ewell a z * Mbal a z)) ^ 2 * Real.sqrt (k2 a z) ^ 2 / k2 a z := by ring
        _ = (4 * C_box * (Ewell a z * Mbal a z)) ^ 2 * k2 a z / k2 a z := by rw [Real.sq_sqrt hk_pos.le]
        _ = (4 * C_box * (Ewell a z * Mbal a z)) ^ 2 := mul_div_cancel_right₀ _ hk_pos.ne'
    have hle : 2 * (4 * C_box * (Ewell a z * Mbal a z)) ^ 2 ≤ (3 * (4 * C_box) * (Ewell a z * Mbal a z)) ^ 2 := by
      have hsq : 0 ≤ (4 * C_box * (Ewell a z * Mbal a z)) ^ 2 := sq_nonneg _
      nlinarith
    linarith
  calc Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z)
      ≤ Real.sqrt ((3 * (4 * C_box) * (Ewell a z * Mbal a z)) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = 3 * (4 * C_box) * (Ewell a z * Mbal a z) :=
        Real.sqrt_sq (mul_nonneg (mul_nonneg (by norm_num) (by linarith [hc_box, hle_box]))
          (mul_nonneg (by rw [hEz]; exact mul_nonneg hE10_pos.le hexp_pos.le) hM_pos.le))

lemma tail_U_bar :
    ∃ cB CB : ℝ, 0 < cB ∧ cB ≤ CB ∧
      ∀ a, 0 ≤ a → a ≤ 1 → ∀ z, 10 ≤ z →
        (cB * (Ebar a z * Mbal a z) ≤ kappaBalPos a * pcU a z ∧
          kappaBalPos a * pcU a z ≤ CB * (Ebar a z * Mbal a z)) ∧
        |kappaBalPos a * deriv (pcU a) z| ≤ CB * Real.sqrt (k2 a z) * (Ebar a z * Mbal a z) ∧
        Real.sqrt ((kappaBalPos a * pcU a z) ^ 2 + (kappaBalPos a * deriv (pcU a) z) ^ 2 / k2 a z) ≤
          3 * CB * (Ebar a z * Mbal a z) := by
  obtain ⟨c_box, C_box, hc_box, hle_box, hbox⟩ := compact_box_bar
  refine ⟨c_box / 6, 4 * C_box, by positivity, by linarith, fun a ha0 ha1 z hz => ?_⟩
  have ha_abs : |a| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨c, hc_pos, hlg⟩ := pcU_compact_far_lg ha_abs
  have hκ := kappaBalPos_pos ha0
  have hE10_pos : 0 < Ebar a 10 :=
    lt_of_lt_of_le (Real.exp_pos _) (Ebar_box_bounds ha0 ha1 (by norm_num) le_rfl).1
  have hM10_pos : 0 < Mbal a 10 := Mbal_pos a 10
  have hk10_pos : 0 < k2 a 10 := k2_pos a 10
  have hlg10 := hlg 10 le_rfl
  simp only [intervalIntegral.integral_same, neg_zero, Real.exp_zero, one_mul] at hlg10
  have hbox10 := hbox a ha0 ha1 10 (by norm_num) le_rfl
  have hscale10 : Real.sqrt ((kappaBalPos a * pcU a 10) ^ 2 +
      (kappaBalPos a * deriv (pcU a) 10) ^ 2 / k2 a 10) =
      (kappaBalPos a * c) * Real.sqrt ((pcU a 10 / c) ^ 2 + (deriv (pcU a) 10 / c) ^ 2 / k2 a 10) := by
    have hkc : 0 ≤ kappaBalPos a * c := mul_nonneg hκ.le hc_pos.le
    rw [← Real.sqrt_sq hkc, ← Real.sqrt_mul (sq_nonneg _)]
    congr 1; field_simp [hc_pos.ne']
  have hnorm_lo : 1 / 2 * Mbal a 10 ≤
      Real.sqrt ((pcU a 10 / c) ^ 2 + (deriv (pcU a) 10 / c) ^ 2 / k2 a 10) := by
    calc 1 / 2 * Mbal a 10 ≤ pcU a 10 / c := hlg10.1.1
      _ ≤ |pcU a 10 / c| := le_abs_self _
      _ = Real.sqrt ((pcU a 10 / c) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((pcU a 10 / c) ^ 2 + (deriv (pcU a) 10 / c) ^ 2 / k2 a 10) :=
          Real.sqrt_le_sqrt (le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hk10_pos.le))
  have hnorm_hi : Real.sqrt ((pcU a 10 / c) ^ 2 + (deriv (pcU a) 10 / c) ^ 2 / k2 a 10) ≤
      3 * Mbal a 10 := by
    have h1 : (pcU a 10 / c) ^ 2 ≤ (5 / 4 * Mbal a 10) ^ 2 :=
      pow_le_pow_left₀ (by linarith [hlg10.1.1]) hlg10.1.2 2
    have h2 : (deriv (pcU a) 10 / c) ^ 2 / k2 a 10 ≤ (2 * Mbal a 10) ^ 2 := by
      have hsq : (deriv (pcU a) 10 / c) ^ 2 ≤ (2 * Real.sqrt (k2 a 10) * Mbal a 10) ^ 2 := by
        rw [← sq_abs (deriv (pcU a) 10 / c)]
        exact pow_le_pow_left₀ (abs_nonneg _) hlg10.2 2
      calc (deriv (pcU a) 10 / c) ^ 2 / k2 a 10
          ≤ (2 * Real.sqrt (k2 a 10) * Mbal a 10) ^ 2 / k2 a 10 :=
            div_le_div_of_nonneg_right hsq hk10_pos.le
        _ = 4 * (Real.sqrt (k2 a 10) ^ 2) * Mbal a 10 ^ 2 / k2 a 10 := by ring
        _ = 4 * k2 a 10 * Mbal a 10 ^ 2 / k2 a 10 := by rw [Real.sq_sqrt hk10_pos.le]
        _ = (2 * Mbal a 10) ^ 2 := by field_simp [hk10_pos.ne']; ring
    have hsum : (pcU a 10 / c) ^ 2 + (deriv (pcU a) 10 / c) ^ 2 / k2 a 10 ≤ (3 * Mbal a 10) ^ 2 := by
      linarith [sq_nonneg (Mbal a 10)]
    calc Real.sqrt ((pcU a 10 / c) ^ 2 + (deriv (pcU a) 10 / c) ^ 2 / k2 a 10)
        ≤ Real.sqrt ((3 * Mbal a 10) ^ 2) := Real.sqrt_le_sqrt hsum
      _ = 3 * Mbal a 10 := Real.sqrt_sq (by positivity)
  have hkc_lo : c_box / 3 * Ebar a 10 ≤ kappaBalPos a * c := by
    have h1 : c_box * Ebar a 10 * Mbal a 10 ≤ (kappaBalPos a * c) * (3 * Mbal a 10) :=
      hbox10.1.trans (hscale10 ▸ mul_le_mul_of_nonneg_left hnorm_hi (mul_nonneg hκ.le hc_pos.le))
    have h2 : (c_box / 3 * Ebar a 10) * (3 * Mbal a 10) ≤ (kappaBalPos a * c) * (3 * Mbal a 10) := by
      linarith
    exact le_of_mul_le_mul_right h2 (by positivity)
  have hkc_hi : kappaBalPos a * c ≤ 2 * C_box * Ebar a 10 := by
    have h1 : (kappaBalPos a * c) * (1 / 2 * Mbal a 10) ≤ C_box * Ebar a 10 * Mbal a 10 :=
      (hscale10 ▸ mul_le_mul_of_nonneg_left hnorm_lo (mul_nonneg hκ.le hc_pos.le)).trans hbox10.2
    have h2 : (kappaBalPos a * c) * (1 / 2 * Mbal a 10) ≤ (2 * C_box * Ebar a 10) * (1 / 2 * Mbal a 10) := by
      linarith
    exact le_of_mul_le_mul_right h2 (by positivity)
  have hlgz := hlg z hz
  have hEz : Ebar a z = Ebar a 10 * Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) :=
    Ebar_compact_far_eq
  have hM_pos : 0 < Mbal a z := Mbal_pos a z
  have hk_pos : 0 < k2 a z := k2_pos a z
  have hexp_pos : 0 < Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) := Real.exp_pos _
  have hut_eq : kappaBalPos a * pcU a z = (kappaBalPos a * c) * (pcU a z / c) := by
    field_simp [hc_pos.ne']
  have hud_eq : |kappaBalPos a * deriv (pcU a) z| = (kappaBalPos a * c) * |deriv (pcU a) z / c| := by
    rw [show kappaBalPos a * deriv (pcU a) z = (kappaBalPos a * c) * (deriv (pcU a) z / c) by
          field_simp [hc_pos.ne'],
        abs_mul, abs_of_pos (mul_pos hκ hc_pos)]
  have hut_lo : c_box / 6 * (Ebar a z * Mbal a z) ≤ kappaBalPos a * pcU a z := by
    rw [hut_eq, hEz]
    calc c_box / 6 * (Ebar a 10 * Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) * Mbal a z)
        = (c_box / 3 * Ebar a 10) * (1 / 2 * (Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) * Mbal a z)) := by ring
      _ ≤ (kappaBalPos a * c) * (pcU a z / c) :=
          mul_le_mul hkc_lo hlgz.1.1 (by positivity) (mul_nonneg hκ.le hc_pos.le)
  have hut_hi : kappaBalPos a * pcU a z ≤ 4 * C_box * (Ebar a z * Mbal a z) := by
    rw [hut_eq, hEz]
    calc (kappaBalPos a * c) * (pcU a z / c)
        ≤ (2 * C_box * Ebar a 10) * (5 / 4 * (Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) * Mbal a z)) :=
          mul_le_mul hkc_hi hlgz.1.2 (by linarith [hlgz.1.1]) (mul_nonneg (mul_nonneg (by positivity) (by linarith [hc_box, hle_box])) hE10_pos.le)
      _ = 5 / 2 * C_box * (Ebar a 10 * Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) * Mbal a z) := by ring
      _ ≤ 4 * C_box * (Ebar a 10 * Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) * Mbal a z) := by
          have hEM : 0 ≤ Ebar a 10 * Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) * Mbal a z :=
            mul_nonneg (mul_nonneg hE10_pos.le hexp_pos.le) hM_pos.le
          nlinarith
  have hud_hi : |kappaBalPos a * deriv (pcU a) z| ≤ 4 * C_box * Real.sqrt (k2 a z) * (Ebar a z * Mbal a z) := by
    rw [hud_eq, hEz]
    calc (kappaBalPos a * c) * |deriv (pcU a) z / c|
        ≤ (2 * C_box * Ebar a 10) * (2 * Real.sqrt (k2 a z) *
            (Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) * Mbal a z)) :=
          mul_le_mul hkc_hi hlgz.2 (abs_nonneg _) (mul_nonneg (mul_nonneg (by positivity) (by linarith [hc_box, hle_box])) hE10_pos.le)
      _ = 4 * C_box * Real.sqrt (k2 a z) *
            (Ebar a 10 * Real.exp (-(∫ s in (10 : ℝ)..z, Real.sqrt (s ^ 2 / 4 + a))) * Mbal a z) := by ring
  refine ⟨⟨hut_lo, hut_hi⟩, hud_hi, ?_⟩
  have hut_nn : 0 ≤ kappaBalPos a * pcU a z := by
    have hEM : 0 ≤ Ebar a z * Mbal a z :=
      mul_nonneg (by rw [hEz]; exact mul_nonneg hE10_pos.le hexp_pos.le) hM_pos.le
    exact le_trans (mul_nonneg (by positivity) hEM) hut_lo
  have hsum : (kappaBalPos a * pcU a z) ^ 2 + (kappaBalPos a * deriv (pcU a) z) ^ 2 / k2 a z ≤
      (3 * (4 * C_box) * (Ebar a z * Mbal a z)) ^ 2 := by
    have h1 : (kappaBalPos a * pcU a z) ^ 2 ≤ (4 * C_box * (Ebar a z * Mbal a z)) ^ 2 := by
      rw [← sq_abs (kappaBalPos a * pcU a z), abs_of_nonneg hut_nn]
      exact pow_le_pow_left₀ hut_nn hut_hi 2
    have h2 : (kappaBalPos a * deriv (pcU a) z) ^ 2 / k2 a z ≤
        (4 * C_box * (Ebar a z * Mbal a z)) ^ 2 := by
      have hsq : (kappaBalPos a * deriv (pcU a) z) ^ 2 ≤
          (4 * C_box * Real.sqrt (k2 a z) * (Ebar a z * Mbal a z)) ^ 2 := by
        rw [← sq_abs (kappaBalPos a * deriv (pcU a) z)]
        exact pow_le_pow_left₀ (abs_nonneg _) hud_hi 2
      calc (kappaBalPos a * deriv (pcU a) z) ^ 2 / k2 a z
          ≤ (4 * C_box * Real.sqrt (k2 a z) * (Ebar a z * Mbal a z)) ^ 2 / k2 a z :=
            div_le_div_of_nonneg_right hsq hk_pos.le
        _ = (4 * C_box * (Ebar a z * Mbal a z)) ^ 2 * Real.sqrt (k2 a z) ^ 2 / k2 a z := by ring
        _ = (4 * C_box * (Ebar a z * Mbal a z)) ^ 2 * k2 a z / k2 a z := by rw [Real.sq_sqrt hk_pos.le]
        _ = (4 * C_box * (Ebar a z * Mbal a z)) ^ 2 := mul_div_cancel_right₀ _ hk_pos.ne'
    have hle : 2 * (4 * C_box * (Ebar a z * Mbal a z)) ^ 2 ≤ (3 * (4 * C_box) * (Ebar a z * Mbal a z)) ^ 2 := by
      have hsq : 0 ≤ (4 * C_box * (Ebar a z * Mbal a z)) ^ 2 := sq_nonneg _
      nlinarith
    linarith
  calc Real.sqrt ((kappaBalPos a * pcU a z) ^ 2 + (kappaBalPos a * deriv (pcU a) z) ^ 2 / k2 a z)
      ≤ Real.sqrt ((3 * (4 * C_box) * (Ebar a z * Mbal a z)) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = 3 * (4 * C_box) * (Ebar a z * Mbal a z) :=
        Real.sqrt_sq (mul_nonneg (mul_nonneg (by norm_num) (by linarith [hc_box, hle_box]))
          (mul_nonneg (by rw [hEz]; exact mul_nonneg hE10_pos.le hexp_pos.le) hM_pos.le))

lemma ut_neg_wronsk {a : ℝ} (ha : 0 ≤ a) (z : ℝ) :
    (kappaBalPos a * pcU a z) * (kappaBalPos a * deriv (fun w => pcU a (-w)) z) -
      (kappaBalPos a * deriv (pcU a) z) * (kappaBalPos a * pcU a (-z)) = 1 := by
  have hwr := congrArg Complex.re (DLMF.Confluent.parabolicCylinderU_wronskian_neg (a : ℂ) (z : ℂ))
  have hderiv_c : deriv (fun w : ℂ => DLMF.Confluent.parabolicCylinderU (a : ℂ) (-w)) (z : ℂ) =
      -DLMF.Confluent.parabolicCylinderUDeriv (a : ℂ) (-z) := by
    have h := (DLMF.Confluent.hasDerivAt_parabolicCylinderU_neg (a : ℂ) (z : ℂ)).deriv
    exact h
  have hderiv_r : deriv (fun w : ℝ => pcU a (-w)) z = -pcUD a (-z) := by
    have h : HasDerivAt (fun w : ℝ => pcU a (-w)) (pcUD a (-z) * (-1)) z :=
      (hasDerivAt_pcU a (-z)).comp z (hasDerivAt_neg z)
    rw [h.deriv]; ring
  rw [hderiv_c, DLMF.Confluent.deriv_parabolicCylinderU] at hwr
  have hpcU_neg : DLMF.Confluent.parabolicCylinderU (a : ℂ) (-(z : ℂ)) = (pcU a (-z) : ℂ) := by
    simpa using pcU_ofReal a (-z)
  have hpcUD_neg : (DLMF.Confluent.parabolicCylinderUDeriv (a : ℂ) (-(z : ℂ))).re = pcUD a (-z) := by
    simp [pcUD]
  have hG : Complex.Gamma (1 / 2 + (a : ℂ)) = ((Real.Gamma (1 / 2 + a) : ℝ) : ℂ) := by
    have : (1 / 2 + (a : ℂ)) = (((1 / 2 + a : ℝ) : ℂ)) := by push_cast; ring
    rw [this, Complex.Gamma_ofReal]
  rw [hG] at hwr
  have hre : ((Real.sqrt (2 * Real.pi) : ℂ) / ((Real.Gamma (1 / 2 + a) : ℝ) : ℂ)).re =
      Real.sqrt (2 * Real.pi) / Real.Gamma (1 / 2 + a) := by
    rw [← Complex.ofReal_div, Complex.ofReal_re]
  rw [hre] at hwr
  have hlhs : ((DLMF.Confluent.parabolicCylinderU (a : ℂ) (z : ℂ) *
      -DLMF.Confluent.parabolicCylinderUDeriv (a : ℂ) (-(z : ℂ)) -
      DLMF.Confluent.parabolicCylinderUDeriv (a : ℂ) (z : ℂ) *
        DLMF.Confluent.parabolicCylinderU (a : ℂ) (-(z : ℂ))).re) =
      pcU a z * (-pcUD a (-z)) - pcUD a z * pcU a (-z) := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.neg_im]
    have h1 : (DLMF.Confluent.parabolicCylinderU (a : ℂ) (z : ℂ)).im = 0 := by
      have := pcU_ofReal a z
      rw [this, Complex.ofReal_im]
    have h2 : (DLMF.Confluent.parabolicCylinderU (a : ℂ) (-(z : ℂ))).im = 0 := by
      rw [hpcU_neg, Complex.ofReal_im]
    rw [h1, h2]
    simp [pcU, pcUD]
  rw [hlhs] at hwr
  have hwr_r : pcU a z * deriv (fun w => pcU a (-w)) z - deriv (pcU a) z * pcU a (-z) =
      Real.sqrt (2 * Real.pi) / Real.Gamma (1 / 2 + a) := by
    rw [hderiv_r, deriv_pcU]; exact hwr
  have hκ2 : kappaBalPos a ^ 2 = Real.Gamma (1 / 2 + a) / Real.sqrt (2 * Real.pi) := by
    unfold kappaBalPos
    have hG_pos : 0 < Real.Gamma (1 / 2 + a) := Real.Gamma_pos_of_pos (by linarith)
    have h2pi_pos : 0 < 2 * Real.pi := by positivity
    rw [mul_pow, Real.sq_sqrt hG_pos.le, ← Real.rpow_natCast ((2 * Real.pi) ^ (-(1 : ℝ) / 4)) 2,
      ← Real.rpow_mul h2pi_pos.le]
    have hhalf : (-(1 : ℝ) / 4) * ((2 : ℕ) : ℝ) = -(1 / 2) := by norm_num
    rw [hhalf, Real.rpow_neg h2pi_pos.le, ← Real.sqrt_eq_rpow]
    ring
  calc (kappaBalPos a * pcU a z) * (kappaBalPos a * deriv (fun w => pcU a (-w)) z) -
        (kappaBalPos a * deriv (pcU a) z) * (kappaBalPos a * pcU a (-z))
      = kappaBalPos a ^ 2 * (pcU a z * deriv (fun w => pcU a (-w)) z - deriv (pcU a) z * pcU a (-z)) := by ring
    _ = (Real.Gamma (1 / 2 + a) / Real.sqrt (2 * Real.pi)) * (Real.sqrt (2 * Real.pi) / Real.Gamma (1 / 2 + a)) := by
        rw [hκ2, hwr_r]
    _ = 1 := by
        have hG_ne : Real.Gamma (1 / 2 + a) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
        have hpi_ne : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
        field_simp

lemma tail_dominant_of_wronsk {a z E10 c_f C_f C_10 : ℝ}
    (ha : |a| ≤ 4) (hz : 10 ≤ z)
    (hE10 : 0 < E10) (hc_f : 0 < c_f) (hC_f : 0 < C_f) (hC_10 : 0 ≤ C_10)
    {f f' g g' E : ℝ → ℝ}
    (hE : ∀ t, 10 ≤ t → E t = E10 * Real.exp (-(∫ s in (10 : ℝ)..t, Real.sqrt (s ^ 2 / 4 + a))))
    (hf_deriv : ∀ t, HasDerivAt f (f' t) t)
    (hg_deriv : ∀ t, HasDerivAt g (g' t) t)
    (hf_cont : Continuous f)
    (hwr : ∀ t, f t * g' t - f' t * g t = 1)
    (hf_bd : ∀ t, 10 ≤ t → c_f * (E t * Mbal a t) ≤ f t ∧ f t ≤ C_f * (E t * Mbal a t))
    (hf'_bd : ∀ t, 10 ≤ t → |f' t| ≤ C_f * Real.sqrt (k2 a t) * (E t * Mbal a t))
    (hg10_bd : |g 10| ≤ C_10 * (E 10)⁻¹ * Mbal a 10) :
    Real.sqrt (g z ^ 2 + g' z ^ 2 / k2 a z) ≤
      Real.sqrt 2 * (1 / c_f + (C_f + C_f ^ 2 / c_f) * (C_10 / c_f + 1 / (2 * c_f ^ 2))) *
        ((E z)⁻¹ * Mbal a z) := by
  let ξ : ℝ → ℝ := fun t => ∫ s in (10 : ℝ)..t, Real.sqrt (s ^ 2 / 4 + a)
  have hE_pos : ∀ t, 10 ≤ t → 0 < E t := fun t ht => by
    rw [hE t ht]; exact mul_pos hE10 (Real.exp_pos _)
  have hf_pos : ∀ t, 10 ≤ t → 0 < f t := fun t ht =>
    lt_of_lt_of_le (mul_pos hc_f (mul_pos (hE_pos t ht) (Mbal_pos a t))) (hf_bd t ht).1
  have hderiv_quo : ∀ t, 10 ≤ t → HasDerivAt (fun s => g s / f s) ((f t)⁻¹ ^ 2) t := fun t ht => by
    refine ((hg_deriv t).div (hf_deriv t) (hf_pos t ht).ne').congr_deriv ?_
    have hwr' : g' t * f t - g t * f' t = 1 := by linarith [hwr t]
    rw [hwr', inv_pow, one_div]
  have hcont_quo : ContinuousOn (fun t => (f t)⁻¹ ^ 2) (Icc 10 z) :=
    ContinuousOn.pow (ContinuousOn.inv₀ hf_cont.continuousOn fun t ht => (hf_pos t ht.1).ne') 2
  have hint_eq : g z / f z - g 10 / f 10 = ∫ t in (10 : ℝ)..z, (f t)⁻¹ ^ 2 :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hderiv_quo t (Set.mem_Icc.mp (by simpa [hz] using ht)).1)
      (hcont_quo.intervalIntegrable_of_Icc hz)).symm
  have hξ_deriv : ∀ t : ℝ, HasDerivAt ξ (Real.sqrt (t ^ 2 / 4 + a)) t := fun t => by
    have hcont : Continuous (fun s => Real.sqrt (s ^ 2 / 4 + a)) :=
      Real.continuous_sqrt.comp (by continuity)
    exact intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 10 t) (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  have hanti_deriv : ∀ t : ℝ,
      HasDerivAt (fun s => 1 / 2 * (E10⁻¹ ^ 2 * Real.exp (2 * ξ s)))
        ((E10⁻¹ * Real.exp (ξ t)) ^ 2 * Real.sqrt (t ^ 2 / 4 + a)) t := fun t => by
    refine ((((hξ_deriv t).const_mul 2).exp.const_mul (E10⁻¹ ^ 2)).const_mul (1 / 2)).congr_deriv ?_
    have h2 : Real.exp (2 * ξ t) = Real.exp (ξ t) ^ 2 := by
      rw [sq, ← Real.exp_add, two_mul]
    rw [h2]; ring
  have hint_ub : ∫ t in (10 : ℝ)..z, (f t)⁻¹ ^ 2 ≤ 1 / (2 * c_f ^ 2) * (E z)⁻¹ ^ 2 := by
    have hcont_rhs : ContinuousOn (fun t : ℝ =>
        c_f⁻¹ ^ 2 * ((E10⁻¹ * Real.exp (ξ t)) ^ 2 * Real.sqrt (t ^ 2 / 4 + a))) (Icc 10 z) := by
      refine continuousOn_const.mul (ContinuousOn.mul ?_ (ContinuousOn.sqrt (by fun_prop)))
      exact Continuous.continuousOn ((continuous_const.mul (Real.continuous_exp.comp
        (intervalIntegral.continuous_primitive (fun a' b' =>
          (Real.continuous_sqrt.comp (by continuity : Continuous (fun s : ℝ => s ^ 2 / 4 + a))).intervalIntegrable a' b') _))).pow 2)
    have hmono : ∫ t in (10 : ℝ)..z, (f t)⁻¹ ^ 2 ≤
        ∫ t in (10 : ℝ)..z, c_f⁻¹ ^ 2 * ((E10⁻¹ * Real.exp (ξ t)) ^ 2 * Real.sqrt (t ^ 2 / 4 + a)) := by
      refine intervalIntegral.integral_mono_on hz (hcont_quo.intervalIntegrable_of_Icc hz)
        (hcont_rhs.intervalIntegrable_of_Icc hz) fun t ht => ?_
      have hlb := (hf_bd t ht.1).1
      have hEt := hE t ht.1
      have hMt := Mbal_compact_eq ha ht.1
      have hp_pos : 0 < t ^ 2 / 4 + a := p_compact_pos ha (by linarith [ht.1])
      have hinv : (f t)⁻¹ ≤ c_f⁻¹ * (E t)⁻¹ * (Mbal a t)⁻¹ := by
        rw [inv_le_iff_one_le_mul₀' (hf_pos t ht.1)]
        calc (1 : ℝ) = (c_f⁻¹ * c_f) * ((E t)⁻¹ * E t) * ((Mbal a t)⁻¹ * Mbal a t) := by
              rw [inv_mul_cancel₀ hc_f.ne', inv_mul_cancel₀ (hE_pos t ht.1).ne',
                inv_mul_cancel₀ (Mbal_pos a t).ne']; ring
          _ = (c_f⁻¹ * (E t)⁻¹ * (Mbal a t)⁻¹) * (c_f * (E t * Mbal a t)) := by ring
          _ ≤ (c_f⁻¹ * (E t)⁻¹ * (Mbal a t)⁻¹) * f t :=
              mul_le_mul_of_nonneg_left hlb (mul_nonneg (mul_nonneg (inv_nonneg.mpr hc_f.le)
                (inv_nonneg.mpr (hE_pos t ht.1).le)) (inv_nonneg.mpr (Mbal_pos a t).le))
          _ = f t * (c_f⁻¹ * (E t)⁻¹ * (Mbal a t)⁻¹) := mul_comm _ _
      have hsq : (f t)⁻¹ ^ 2 ≤ c_f⁻¹ ^ 2 * (E t)⁻¹ ^ 2 * (Mbal a t)⁻¹ ^ 2 := by
        calc (f t)⁻¹ ^ 2 ≤ (c_f⁻¹ * (E t)⁻¹ * (Mbal a t)⁻¹) ^ 2 :=
              pow_le_pow_left₀ (inv_nonneg.mpr (hf_pos t ht.1).le) hinv 2
          _ = c_f⁻¹ ^ 2 * (E t)⁻¹ ^ 2 * (Mbal a t)⁻¹ ^ 2 := by ring
      have hEinv : (E t)⁻¹ = E10⁻¹ * Real.exp (ξ t) := by
        rw [hEt, mul_inv, ← Real.exp_neg, neg_neg]
      have hM2 : (Mbal a t)⁻¹ ^ 2 = Real.sqrt (t ^ 2 / 4 + a) := by
        rw [hMt, ← Real.rpow_neg hp_pos.le, neg_neg, Real.sqrt_eq_rpow,
          ← Real.rpow_natCast, ← Real.rpow_mul hp_pos.le]
        norm_num
      rw [hEinv, hM2] at hsq
      linarith
    have hanti_int : ∫ t in (10 : ℝ)..z, (E10⁻¹ * Real.exp (ξ t)) ^ 2 * Real.sqrt (t ^ 2 / 4 + a) =
        1 / 2 * (E10⁻¹ ^ 2 * Real.exp (2 * ξ z)) - 1 / 2 * (E10⁻¹ ^ 2 * Real.exp (2 * ξ 10)) := by
      have hcont_anti : Continuous (fun t : ℝ => (E10⁻¹ * Real.exp (ξ t)) ^ 2 * Real.sqrt (t ^ 2 / 4 + a)) :=
        ((continuous_const.mul (Real.continuous_exp.comp
          (intervalIntegral.continuous_primitive (fun a' b' =>
            (Real.continuous_sqrt.comp (by continuity : Continuous (fun s : ℝ => s ^ 2 / 4 + a))).intervalIntegrable a' b') _))).pow 2).mul
          (Real.continuous_sqrt.comp (by continuity))
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hanti_deriv t)
        (hcont_anti.intervalIntegrable 10 z)
    have hEz_sq : (E z)⁻¹ ^ 2 = E10⁻¹ ^ 2 * Real.exp (2 * ξ z) := by
      rw [hE z hz, mul_inv, ← Real.exp_neg, neg_neg, mul_pow, sq (Real.exp (ξ z)), ← Real.exp_add, ← two_mul]
    calc ∫ t in (10 : ℝ)..z, (f t)⁻¹ ^ 2
        ≤ ∫ t in (10 : ℝ)..z, c_f⁻¹ ^ 2 * ((E10⁻¹ * Real.exp (ξ t)) ^ 2 * Real.sqrt (t ^ 2 / 4 + a)) := hmono
      _ = c_f⁻¹ ^ 2 * ∫ t in (10 : ℝ)..z, (E10⁻¹ * Real.exp (ξ t)) ^ 2 * Real.sqrt (t ^ 2 / 4 + a) :=
          intervalIntegral.integral_const_mul _ _
      _ = c_f⁻¹ ^ 2 * (1 / 2 * (E10⁻¹ ^ 2 * Real.exp (2 * ξ z)) -
            1 / 2 * (E10⁻¹ ^ 2 * Real.exp (2 * ξ 10))) := by rw [hanti_int]
      _ ≤ c_f⁻¹ ^ 2 * (1 / 2 * (E10⁻¹ ^ 2 * Real.exp (2 * ξ z))) := by
          gcongr; linarith [mul_pos (sq_pos_of_pos (inv_pos.mpr hE10)) (Real.exp_pos (2 * ξ 10))]
      _ = 1 / (2 * c_f ^ 2) * (E z)⁻¹ ^ 2 := by rw [hEz_sq]; ring
  have hE10_le_Ez : (E 10)⁻¹ ≤ (E z)⁻¹ := by
    have hξ_nonneg : 0 ≤ ξ z := intervalIntegral.integral_nonneg hz (fun t _ => Real.sqrt_nonneg _)
    have hEz_le : E z ≤ E 10 := by
      rw [hE z hz, hE 10 le_rfl]
      simp only [intervalIntegral.integral_same, neg_zero, Real.exp_zero, mul_one]
      exact mul_le_of_le_one_right hE10.le (Real.exp_le_one_iff.mpr (by linarith))
    exact inv_anti₀ (hE_pos z hz) hEz_le
  have hquo10 : |g 10 / f 10| ≤ C_10 / c_f * (E z)⁻¹ ^ 2 := by
    have hlb10 := (hf_bd 10 le_rfl).1
    have hM10 : 0 < Mbal a 10 := Mbal_pos a 10
    have hE10' : 0 < E 10 := hE_pos 10 le_rfl
    rw [abs_div, abs_of_pos (hf_pos 10 le_rfl)]
    calc |g 10| / f 10 ≤ (C_10 * (E 10)⁻¹ * Mbal a 10) / (c_f * (E 10 * Mbal a 10)) :=
          div_le_div₀ (by positivity) hg10_bd (by positivity) hlb10
      _ = C_10 / c_f * (E 10)⁻¹ ^ 2 := by field_simp [hE10'.ne', hM10.ne', hc_f.ne']
      _ ≤ C_10 / c_f * (E z)⁻¹ ^ 2 := by gcongr
  have hquo_z : |g z / f z| ≤ (C_10 / c_f + 1 / (2 * c_f ^ 2)) * (E z)⁻¹ ^ 2 := by
    have heq : g z / f z = g 10 / f 10 + ∫ t in (10 : ℝ)..z, (f t)⁻¹ ^ 2 := by linarith [hint_eq]
    have hint_nn : 0 ≤ ∫ t in (10 : ℝ)..z, (f t)⁻¹ ^ 2 :=
      intervalIntegral.integral_nonneg hz (fun t _ => sq_nonneg _)
    calc |g z / f z| ≤ |g 10 / f 10| + |∫ t in (10 : ℝ)..z, (f t)⁻¹ ^ 2| := by
          rw [heq]; exact abs_add_le _ _
      _ = |g 10 / f 10| + ∫ t in (10 : ℝ)..z, (f t)⁻¹ ^ 2 := by rw [abs_of_nonneg hint_nn]
      _ ≤ C_10 / c_f * (E z)⁻¹ ^ 2 + 1 / (2 * c_f ^ 2) * (E z)⁻¹ ^ 2 := add_le_add hquo10 hint_ub
      _ = (C_10 / c_f + 1 / (2 * c_f ^ 2)) * (E z)⁻¹ ^ 2 := by ring
  have hg_bd : |g z| ≤ C_f * (C_10 / c_f + 1 / (2 * c_f ^ 2)) * ((E z)⁻¹ * Mbal a z) := by
    have hfz := hf_pos z hz
    have hub := (hf_bd z hz).2
    have hEz' := hE_pos z hz
    calc |g z| = |g z / f z| * f z := by rw [abs_div, abs_of_pos hfz, div_mul_cancel₀ _ hfz.ne']
      _ ≤ ((C_10 / c_f + 1 / (2 * c_f ^ 2)) * (E z)⁻¹ ^ 2) * (C_f * (E z * Mbal a z)) :=
          mul_le_mul hquo_z hub hfz.le (mul_nonneg (add_nonneg (div_nonneg hC_10 hc_f.le) (by positivity)) (sq_nonneg _))
      _ = C_f * (C_10 / c_f + 1 / (2 * c_f ^ 2)) * ((E z)⁻¹ * Mbal a z) := by
          field_simp [hEz'.ne']
  have hk_pos : 0 < k2 a z := k2_pos a z
  have hM_pos : 0 < Mbal a z := Mbal_pos a z
  have hEz' := hE_pos z hz
  have hM_inv : (Mbal a z)⁻¹ = Real.sqrt (k2 a z) * Mbal a z := by
    have hsq : Mbal a z ^ 2 = (Real.sqrt (k2 a z))⁻¹ := Mbal_sq a z
    have h1 : Mbal a z * Mbal a z = (Real.sqrt (k2 a z))⁻¹ := by simpa [sq] using hsq
    have h2 : Mbal a z * (Real.sqrt (k2 a z) * Mbal a z) = 1 := by
      calc Mbal a z * (Real.sqrt (k2 a z) * Mbal a z) = Real.sqrt (k2 a z) * (Mbal a z * Mbal a z) := by ring
        _ = Real.sqrt (k2 a z) * (Real.sqrt (k2 a z))⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel₀ (Real.sqrt_pos.mpr hk_pos).ne'
    exact inv_eq_of_mul_eq_one_right h2
  have hg'_bd : |g' z| ≤ (1 / c_f + C_f ^ 2 / c_f * (C_10 / c_f + 1 / (2 * c_f ^ 2))) *
      Real.sqrt (k2 a z) * ((E z)⁻¹ * Mbal a z) := by
    have hfz := hf_pos z hz
    have hlb := (hf_bd z hz).1
    have hgeq : g' z = (1 + f' z * g z) / f z := by
      have h := hwr z
      field_simp [hfz.ne']
      linarith
    have h1_div : 1 / f z ≤ 1 / c_f * Real.sqrt (k2 a z) * ((E z)⁻¹ * Mbal a z) := by
      calc 1 / f z ≤ 1 / (c_f * (E z * Mbal a z)) := one_div_le_one_div_of_le (by positivity) hlb
        _ = 1 / c_f * (Mbal a z)⁻¹ * (E z)⁻¹ := by ring
        _ = 1 / c_f * Real.sqrt (k2 a z) * ((E z)⁻¹ * Mbal a z) := by rw [hM_inv]; ring
    have h2_div : |f' z| * |g z| / f z ≤
        C_f ^ 2 / c_f * (C_10 / c_f + 1 / (2 * c_f ^ 2)) * Real.sqrt (k2 a z) * ((E z)⁻¹ * Mbal a z) := by
      have hprod : |f' z| * |g z| ≤
          (C_f * Real.sqrt (k2 a z) * (E z * Mbal a z)) *
            (C_f * (C_10 / c_f + 1 / (2 * c_f ^ 2)) * ((E z)⁻¹ * Mbal a z)) :=
        mul_le_mul (hf'_bd z hz) hg_bd (abs_nonneg _) (by positivity)
      calc |f' z| * |g z| / f z
          ≤ ((C_f * Real.sqrt (k2 a z) * (E z * Mbal a z)) *
              (C_f * (C_10 / c_f + 1 / (2 * c_f ^ 2)) * ((E z)⁻¹ * Mbal a z))) /
              (c_f * (E z * Mbal a z)) :=
            div_le_div₀ (by positivity) hprod (by positivity) hlb
        _ = C_f ^ 2 / c_f * (C_10 / c_f + 1 / (2 * c_f ^ 2)) * Real.sqrt (k2 a z) * ((E z)⁻¹ * Mbal a z) := by
            field_simp [hEz'.ne', hM_pos.ne', hc_f.ne']
    calc |g' z| = |1 + f' z * g z| / f z := by rw [hgeq, abs_div, abs_of_pos hfz]
      _ ≤ (1 + |f' z| * |g z|) / f z := by
          gcongr
          calc |1 + f' z * g z| ≤ |1| + |f' z * g z| := abs_add_le _ _
            _ = 1 + |f' z| * |g z| := by rw [abs_one, abs_mul]
      _ = 1 / f z + |f' z| * |g z| / f z := add_div _ _ _
      _ ≤ 1 / c_f * Real.sqrt (k2 a z) * ((E z)⁻¹ * Mbal a z) +
            C_f ^ 2 / c_f * (C_10 / c_f + 1 / (2 * c_f ^ 2)) * Real.sqrt (k2 a z) * ((E z)⁻¹ * Mbal a z) :=
          add_le_add h1_div h2_div
      _ = (1 / c_f + C_f ^ 2 / c_f * (C_10 / c_f + 1 / (2 * c_f ^ 2))) *
            Real.sqrt (k2 a z) * ((E z)⁻¹ * Mbal a z) := by ring
  let K := 1 / c_f + (C_f + C_f ^ 2 / c_f) * (C_10 / c_f + 1 / (2 * c_f ^ 2))
  have hg_K : |g z| ≤ K * ((E z)⁻¹ * Mbal a z) := by
    have h1 : C_f * (C_10 / c_f + 1 / (2 * c_f ^ 2)) ≤ K := by
      dsimp [K]
      have : 0 ≤ 1 / c_f + C_f ^ 2 / c_f * (C_10 / c_f + 1 / (2 * c_f ^ 2)) := by
        refine add_nonneg (by positivity) (mul_nonneg (by positivity) (add_nonneg (div_nonneg hC_10 hc_f.le) (by positivity)))
      linarith
    exact hg_bd.trans (mul_le_mul_of_nonneg_right h1 (mul_nonneg (inv_nonneg.mpr hEz'.le) hM_pos.le))
  have hg'_K : |g' z| ≤ K * Real.sqrt (k2 a z) * ((E z)⁻¹ * Mbal a z) := by
    have h1 : 1 / c_f + C_f ^ 2 / c_f * (C_10 / c_f + 1 / (2 * c_f ^ 2)) ≤ K := by
      dsimp [K]
      have : 0 ≤ C_f * (C_10 / c_f + 1 / (2 * c_f ^ 2)) :=
        mul_nonneg hC_f.le (add_nonneg (div_nonneg hC_10 hc_f.le) (by positivity))
      linarith
    exact hg'_bd.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _))
      (mul_nonneg (inv_nonneg.mpr hEz'.le) hM_pos.le))
  have hK_nn : 0 ≤ K := le_trans (div_nonneg (abs_nonneg (g z)) (mul_nonneg (inv_nonneg.mpr hEz'.le) hM_pos.le))
    ((div_le_iff₀ (mul_pos (inv_pos.mpr hEz') hM_pos)).mpr hg_K)
  have hsum : g z ^ 2 + g' z ^ 2 / k2 a z ≤ (Real.sqrt 2 * K * ((E z)⁻¹ * Mbal a z)) ^ 2 := by
    have h1 : g z ^ 2 ≤ (K * ((E z)⁻¹ * Mbal a z)) ^ 2 := by
      rw [← sq_abs (g z)]
      exact pow_le_pow_left₀ (abs_nonneg _) hg_K 2
    have h2 : g' z ^ 2 / k2 a z ≤ (K * ((E z)⁻¹ * Mbal a z)) ^ 2 := by
      have hsq : g' z ^ 2 ≤ (K * Real.sqrt (k2 a z) * ((E z)⁻¹ * Mbal a z)) ^ 2 := by
        rw [← sq_abs (g' z)]
        exact pow_le_pow_left₀ (abs_nonneg _) hg'_K 2
      calc g' z ^ 2 / k2 a z ≤ (K * Real.sqrt (k2 a z) * ((E z)⁻¹ * Mbal a z)) ^ 2 / k2 a z :=
            div_le_div_of_nonneg_right hsq hk_pos.le
        _ = (K * ((E z)⁻¹ * Mbal a z)) ^ 2 * Real.sqrt (k2 a z) ^ 2 / k2 a z := by ring
        _ = (K * ((E z)⁻¹ * Mbal a z)) ^ 2 * k2 a z / k2 a z := by rw [Real.sq_sqrt hk_pos.le]
        _ = (K * ((E z)⁻¹ * Mbal a z)) ^ 2 := mul_div_cancel_right₀ _ hk_pos.ne'
    calc g z ^ 2 + g' z ^ 2 / k2 a z
        ≤ (K * ((E z)⁻¹ * Mbal a z)) ^ 2 + (K * ((E z)⁻¹ * Mbal a z)) ^ 2 := add_le_add h1 h2
      _ = 2 * (K * ((E z)⁻¹ * Mbal a z)) ^ 2 := by ring
      _ = Real.sqrt 2 ^ 2 * (K * ((E z)⁻¹ * Mbal a z)) ^ 2 := by rw [Real.sq_sqrt (by norm_num)]
      _ = (Real.sqrt 2 * K * ((E z)⁻¹ * Mbal a z)) ^ 2 := by ring
  calc Real.sqrt (g z ^ 2 + g' z ^ 2 / k2 a z)
      ≤ Real.sqrt ((Real.sqrt 2 * K * ((E z)⁻¹ * Mbal a z)) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 2 * K * ((E z)⁻¹ * Mbal a z) :=
        Real.sqrt_sq (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hK_nn)
          (mul_nonneg (inv_nonneg.mpr hEz'.le) hM_pos.le))

/-! ### Section 4: Assembly of `(A)` and `(B)` -/

/-- **(A) `env_well` on the compact parameter range `[-4, 0]`**: both the `pcU` and `pcV`
envelopes of `PCEnvelopeFacts.env_well` hold for all `-4 < a ≤ 0` and `0 ≤ z` with an
absolute constant `C` independent of `a` and `z`. -/
theorem pc_env_well_compact :
    ∃ C : ℝ, 0 < C ∧ ∀ a, -4 < a → a ≤ 0 → ∀ z, 0 ≤ z →
      Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) ≤
        C * Ewell a z * Mbal a z ∧
      Real.sqrt (vt pcV a z ^ 2 + (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z) ≤
        C * (Ewell a z)⁻¹ * Mbal a z := by
  obtain ⟨c_box, C_box, hc_box, hle_box, hbox⟩ := compact_box_well
  obtain ⟨c_U, C_U, hc_U, hle_U, htailU⟩ := tail_U_well
  let K_V := Real.sqrt 2 * (1 / c_U + (C_U + C_U ^ 2 / c_U) * (C_box / c_U + 1 / (2 * c_U ^ 2)))
  refine ⟨max C_box (max (3 * C_U) K_V), lt_of_lt_of_le (lt_of_lt_of_le hc_box hle_box) (le_max_left _ _),
    fun a ha4 ha0 z hz0 => ?_⟩
  rcases le_or_gt z 10 with hz10 | hz10
  · obtain ⟨h1, h2⟩ := hbox a ha4.le ha0 z hz0 hz10
    have hle : C_box ≤ max C_box (max (3 * C_U) K_V) := le_max_left _ _
    have hEM1 : 0 ≤ Ewell a z * Mbal a z :=
      mul_nonneg (lt_of_lt_of_le (Real.exp_pos _) (Ewell_box_bounds ha4.le ha0 hz0 hz10).1).le (Mbal_pos a z).le
    have hEM2 : 0 ≤ (Ewell a z)⁻¹ * Mbal a z :=
      mul_nonneg (inv_nonneg.mpr (lt_of_lt_of_le (Real.exp_pos _) (Ewell_box_bounds ha4.le ha0 hz0 hz10).1).le) (Mbal_pos a z).le
    exact ⟨h1.2.trans (by nlinarith), h2.2.trans (by nlinarith)⟩
  · have hU := htailU a ha4.le ha0 z hz10.le
    have ha_abs : |a| ≤ 4 := abs_le.mpr ⟨ha4.le, by linarith⟩
    have hE10 : 0 < Ewell a 10 :=
      lt_of_lt_of_le (Real.exp_pos _) (Ewell_box_bounds ha4.le ha0 (by norm_num) le_rfl).1
    have hV10 : |vt pcV a 10| ≤ C_box * (Ewell a 10)⁻¹ * Mbal a 10 := by
      have hbox10 := (hbox a ha4.le ha0 10 (by norm_num) le_rfl).2.2
      calc |vt pcV a 10| = Real.sqrt (vt pcV a 10 ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (vt pcV a 10 ^ 2 +
              (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (pcV a) 10) ^ 2 / k2 a 10) :=
            Real.sqrt_le_sqrt (le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (k2_pos a 10).le))
        _ ≤ C_box * (Ewell a 10)⁻¹ * Mbal a 10 := hbox10
    have hV_tail := tail_dominant_of_wronsk ha_abs hz10.le hE10 hc_U (lt_of_lt_of_le hc_U hle_U)
      (le_trans hc_box.le hle_box)
      (f := ut pcU a) (f' := fun t => kappaBal a * deriv (pcU a) t)
      (g := vt pcV a) (g' := fun t => Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (pcV a) t)
      (E := Ewell a)
      (fun t ht => Ewell_compact_far_eq ha4.le ha0 ht)
      (fun t => by rw [deriv_pcU]; exact (hasDerivAt_pcU a t).const_mul _)
      (fun t => by rw [deriv_pcV]; exact (hasDerivAt_pcV a t).const_mul _)
      ((pcSmoothFacts.cont_U.comp (continuous_const.prodMk continuous_id)).const_mul _)
      (fun t => ut_vt_wronsk a t)
      (fun t ht => (htailU a ha4.le ha0 t ht).1)
      (fun t ht => (htailU a ha4.le ha0 t ht).2.1)
      hV10
    have hEz : 0 ≤ Ewell a z := by
      rw [Ewell_compact_far_eq ha4.le ha0 hz10.le]
      exact mul_nonneg hE10.le (Real.exp_pos _).le
    have hMz : 0 ≤ Mbal a z := (Mbal_pos a z).le
    have hle1 : 3 * C_U ≤ max C_box (max (3 * C_U) K_V) := le_trans (le_max_left _ _) (le_max_right _ _)
    have hle2 : K_V ≤ max C_box (max (3 * C_U) K_V) := le_trans (le_max_right _ _) (le_max_right _ _)
    constructor
    · calc Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z)
          ≤ 3 * C_U * (Ewell a z * Mbal a z) := hU.2.2
        _ ≤ max C_box (max (3 * C_U) K_V) * (Ewell a z * Mbal a z) :=
            mul_le_mul_of_nonneg_right hle1 (mul_nonneg hEz hMz)
        _ = max C_box (max (3 * C_U) K_V) * Ewell a z * Mbal a z := by ring
    · calc Real.sqrt (vt pcV a z ^ 2 + (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z)
          ≤ K_V * ((Ewell a z)⁻¹ * Mbal a z) := hV_tail
        _ ≤ max C_box (max (3 * C_U) K_V) * ((Ewell a z)⁻¹ * Mbal a z) :=
            mul_le_mul_of_nonneg_right hle2 (mul_nonneg (inv_nonneg.mpr hEz) hMz)
        _ = max C_box (max (3 * C_U) K_V) * (Ewell a z)⁻¹ * Mbal a z := by ring

lemma pc_env_bar_first_compact :
    ∃ C : ℝ, 0 < C ∧ ∀ a, 0 < a → a < 1 → ∀ z,
      Real.sqrt ((kappaBal a * pcU a z) ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) ≤
        C * Ebar a z * Mbal a z := by
  obtain ⟨c_box, C_box, hc_box, hle_box, hbox⟩ := compact_box_bar
  obtain ⟨c_B, C_B, hc_B, hle_B, htailB⟩ := tail_U_bar
  let K_neg := Real.sqrt 2 * (1 / c_B + (C_B + C_B ^ 2 / c_B) * (C_box / c_B + 1 / (2 * c_B ^ 2)))
  refine ⟨max C_box (max (3 * C_B) K_neg), lt_of_lt_of_le (lt_of_lt_of_le hc_box hle_box) (le_max_left _ _),
    fun a ha0 ha1 z => ?_⟩
  rw [kappaBal_eq_kappaBalPos ha0]
  by_cases hz_box : -10 ≤ z ∧ z ≤ 10
  · have h1 := (hbox a ha0.le ha1.le z hz_box.1 hz_box.2).2
    have hle : C_box ≤ max C_box (max (3 * C_B) K_neg) := le_max_left _ _
    have hEM : 0 ≤ Ebar a z * Mbal a z :=
      mul_nonneg (lt_of_lt_of_le (Real.exp_pos _) (Ebar_box_bounds ha0.le ha1.le hz_box.1 hz_box.2).1).le
        (Mbal_pos a z).le
    exact h1.trans (by nlinarith)
  · rcases lt_or_ge 10 z with hz_pos | hz_le10
    · have hB := (htailB a ha0.le ha1.le z hz_pos.le).2.2
      have hle : 3 * C_B ≤ max C_box (max (3 * C_B) K_neg) :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      have hEz : 0 ≤ Ebar a z := by unfold Ebar; exact (Real.exp_pos _).le
      have hMz : 0 ≤ Mbal a z := (Mbal_pos a z).le
      calc Real.sqrt ((kappaBalPos a * pcU a z) ^ 2 + (kappaBalPos a * deriv (pcU a) z) ^ 2 / k2 a z)
          ≤ 3 * C_B * (Ebar a z * Mbal a z) := hB
        _ ≤ max C_box (max (3 * C_B) K_neg) * (Ebar a z * Mbal a z) :=
            mul_le_mul_of_nonneg_right hle (mul_nonneg hEz hMz)
        _ = max C_box (max (3 * C_B) K_neg) * Ebar a z * Mbal a z := by ring
    · have hx : 10 ≤ -z := by
        by_contra hlt
        push Not at hlt
        exact hz_box ⟨by linarith, hz_le10⟩
      set x := -z with hx_def
      have ha_abs : |a| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hE10 : 0 < Ebar a 10 := by unfold Ebar; exact Real.exp_pos _
      have hg10 : |kappaBalPos a * pcU a (-10)| ≤ C_box * (Ebar a 10)⁻¹ * Mbal a 10 := by
        have hbox_neg10 := (hbox a ha0.le ha1.le (-10) le_rfl (by norm_num)).2
        have hEneg : Ebar a (-10) = (Ebar a 10)⁻¹ := Ebar_neg a 10
        have hMneg : Mbal a (-10) = Mbal a 10 := Mbal_neg a 10
        rw [hEneg, hMneg] at hbox_neg10
        calc |kappaBalPos a * pcU a (-10)| = Real.sqrt ((kappaBalPos a * pcU a (-10)) ^ 2) :=
              (Real.sqrt_sq_eq_abs _).symm
          _ ≤ Real.sqrt ((kappaBalPos a * pcU a (-10)) ^ 2 +
                (kappaBalPos a * deriv (pcU a) (-10)) ^ 2 / k2 a (-10)) :=
              Real.sqrt_le_sqrt (le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (k2_pos a (-10)).le))
          _ ≤ C_box * (Ebar a 10)⁻¹ * Mbal a 10 := hbox_neg10
      have h_tail := tail_dominant_of_wronsk ha_abs hx hE10 hc_B (lt_of_lt_of_le hc_B hle_B)
        (le_trans hc_box.le hle_box)
        (f := fun t => kappaBalPos a * pcU a t)
        (f' := fun t => kappaBalPos a * deriv (pcU a) t)
        (g := fun t => kappaBalPos a * pcU a (-t))
        (g' := fun t => kappaBalPos a * deriv (fun w => pcU a (-w)) t)
        (E := Ebar a)
        (fun _ _ => Ebar_compact_far_eq)
        (fun t => by rw [deriv_pcU]; exact (hasDerivAt_pcU a t).const_mul _)
        (fun t => by
          have h : HasDerivAt (fun w => pcU a (-w)) (pcUD a (-t) * (-1)) t :=
            (hasDerivAt_pcU a (-t)).comp t (hasDerivAt_neg t)
          rw [h.deriv]
          exact h.const_mul _)
        ((pcSmoothFacts.cont_U.comp (continuous_const.prodMk continuous_id)).const_mul _)
        (fun t => ut_neg_wronsk ha0.le t)
        (fun t ht => (htailB a ha0.le ha1.le t ht).1)
        (fun t ht => (htailB a ha0.le ha1.le t ht).2.1)
        hg10
      have hderiv_neg : deriv (fun w => pcU a (-w)) x = -deriv (pcU a) (-x) := by
        have h : HasDerivAt (fun w => pcU a (-w)) (pcUD a (-x) * (-1)) x :=
          (hasDerivAt_pcU a (-x)).comp x (hasDerivAt_neg x)
        rw [h.deriv, deriv_pcU]; ring
      have hz_eq : -x = z := by rw [hx_def, neg_neg]
      rw [hderiv_neg, hz_eq] at h_tail
      have hsq_eq : (kappaBalPos a * -deriv (pcU a) z) ^ 2 = (kappaBalPos a * deriv (pcU a) z) ^ 2 := by
        ring
      have hE_eq : (Ebar a x)⁻¹ = Ebar a z := by
        rw [← Ebar_neg a x, hz_eq]
      have hM_eq : Mbal a x = Mbal a z := by
        rw [← Mbal_neg a x, hz_eq]
      have hk_eq : k2 a x = k2 a z := by
        rw [← k2_neg a x, hz_eq]
      rw [hsq_eq, hk_eq, hE_eq, hM_eq] at h_tail
      have hle : K_neg ≤ max C_box (max (3 * C_B) K_neg) :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      have hEz : 0 ≤ Ebar a z := by unfold Ebar; exact (Real.exp_pos _).le
      have hMz : 0 ≤ Mbal a z := (Mbal_pos a z).le
      calc Real.sqrt ((kappaBalPos a * pcU a z) ^ 2 + (kappaBalPos a * deriv (pcU a) z) ^ 2 / k2 a z)
          ≤ K_neg * (Ebar a z * Mbal a z) := h_tail
        _ ≤ max C_box (max (3 * C_B) K_neg) * (Ebar a z * Mbal a z) :=
            mul_le_mul_of_nonneg_right hle (mul_nonneg hEz hMz)
        _ = max C_box (max (3 * C_B) K_neg) * Ebar a z * Mbal a z := by ring

/-- **(B) `env_bar` on the compact parameter range `(0, 1)`**: both the `pcU(a, z)` and
`pcU(a, -z)` envelopes of `PCEnvelopeFacts.env_bar` hold for all `0 < a < 1` and all `z : ℝ`
with an absolute constant `C` independent of `a` and `z`. -/
theorem pc_env_bar_compact :
    ∃ C : ℝ, 0 < C ∧ ∀ a, 0 < a → a < 1 → ∀ z,
      Real.sqrt ((kappaBal a * pcU a z) ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) ≤
        C * Ebar a z * Mbal a z ∧
      Real.sqrt ((kappaBal a * pcU a (-z)) ^ 2 +
          (kappaBal a * deriv (fun w => pcU a (-w)) z) ^ 2 / k2 a z) ≤
        C * (Ebar a z)⁻¹ * Mbal a z := by
  obtain ⟨C, hC, hfirst⟩ := pc_env_bar_first_compact
  refine ⟨C, hC, fun a ha0 ha1 z => ⟨hfirst a ha0 ha1 z, ?_⟩⟩
  have hneg : deriv (fun w => pcU a (-w)) z = -deriv (pcU a) (-z) := by
    have h : HasDerivAt (fun w : ℝ => pcU a (-w)) (pcUD a (-z) * (-1)) z :=
      (hasDerivAt_pcU a (-z)).comp z (hasDerivAt_neg z)
    rw [h.deriv, deriv_pcU]
    ring
  rw [hneg, ← Ebar_neg a z, ← k2_neg a z, ← Mbal_neg a z]
  have hsq : (kappaBal a * -deriv (pcU a) (-z)) ^ 2 = (kappaBal a * deriv (pcU a) (-z)) ^ 2 := by
    ring
  rw [hsq]
  exact hfirst a ha0 ha1 (-z)

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pc_env_well_compact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.pc_env_well_compact

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pc_env_bar_compact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.pc_env_bar_compact

end FormalResearch.JacobiEigenvectors.Charts
