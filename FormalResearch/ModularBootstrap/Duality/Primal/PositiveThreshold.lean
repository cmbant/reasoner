module

public import FormalResearch.ModularBootstrap.Duality.Primal.StripLimit
public import FormalResearch.ModularBootstrap.Duality.ConstrainedThreshold

/-!
# Positivity of `T_V` from the fixed-charge strip bound (`dsl:strip-fixed`(b))

The half-mass argument: a feasible `g` with `M[g] > 0`, `g_vac > 0`, `g ≥ 0` on `[T, ∞)` has negative
mass `∫ g_- V > M[g]/2`, supported in `(0, T]`, while `‖g‖_∞ ≤ C M[g]` (strip bound on the real axis)
and `∫_0^T V ≤ B T`; so `T ≥ 1/(2 C B)`.  Hence `0 < T_V`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Complex
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeight

open Crossing WeightAxioms

variable {prob : FixedWeightProblem} {cTilde : ℝ}

/-- `‖g‖_∞ ≤ C M[g]` on `[0, ∞)` (the strip bound on the real axis). -/
lemma testClass_sup_le (S : FixedChargeStrip prob cTilde) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ g : ℝ → ℝ, TestClass prob (cTilde / 12) g → ∀ t : ℝ, 0 ≤ t →
      |g t| ≤ C * prob.cardyNorm (cTilde / 12) g := by
  obtain ⟨C, hC⟩ := S.bound
  refine ⟨max C 0, le_max_right _ _, fun g hg t ht => ?_⟩
  have h1 := hC g hg (stripCoord cTilde t : ℂ) (by simp)
  rw [hankel_ofReal_testClass S.hc_pos hg, stripCoord_sq S.hc_pos ht, Complex.norm_real,
    Real.norm_eq_abs] at h1
  have hM : 0 ≤ prob.cardyNorm (cTilde / 12) g :=
    prob.cardyNorm_nonneg (by linarith [S.hc]) g
  exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hM)

/-- A strictly feasible test has positive Cardy norm. -/
lemma cardyNorm_pos_of_vac_pos (hc : 12 * prob.totalShift ≤ cTilde) {g : ℝ → ℝ}
    (_hg : TestClass prob (cTilde / 12) g) (hv : 0 < prob.gVac (cTilde / 12) g) :
    0 < prob.cardyNorm (cTilde / 12) g := by
  have ha : prob.totalShift ≤ cTilde / 12 := by linarith
  by_contra hM
  have hM0 : prob.cardyNorm (cTilde / 12) g = 0 :=
    le_antisymm (not_lt.1 hM) (prob.cardyNorm_nonneg ha g)
  have h1 : |∫ t in Ioi (0 : ℝ), g t * prob.cardyV (cTilde / 12) t| ≤
      ∫ t in Ioi (0 : ℝ), |g t| * prob.cardyV (cTilde / 12) t := by
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [abs_mul, abs_of_nonneg (prob.cardyV_nonneg ha (le_of_lt ht))]
  have h2 : ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (cTilde / 12) t = 0 := by
    have : |∫ t in Ioi (0 : ℝ), g t * prob.cardyV (cTilde / 12) t| ≤ 0 := by
      have := h1; rw [show (∫ t in Ioi (0 : ℝ), |g t| * prob.cardyV (cTilde / 12) t) = 0 from hM0] at this
      exact this
    exact abs_nonpos_iff.1 this
  have : prob.gVac (cTilde / 12) g = 0 := by
    unfold FixedWeightProblem.gVac; rw [h2]; ring
  linarith

/-- **Half-mass argument** (`dsl:strip-fixed`(b)): there is `T₀ > 0` such that every strictly feasible
gap `T` satisfies `T ≥ T₀`. -/
theorem feasible_gap_lower_bound (S : FixedChargeStrip prob cTilde) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, 0 < T → ∀ g, prob.IsFeasible (cTilde / 12) T g → T₀ ≤ T := by
  classical
  have ha : prob.totalShift ≤ cTilde / 12 := by linarith [S.hc]
  obtain ⟨C, hC0, hC⟩ := testClass_sup_le S
  have hVc := continuous_cardyV prob (cTilde / 12)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hVc.continuousOn
  set B' : ℝ := max B 1 with hB'
  have hB'pos : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hVB : ∀ t ∈ Icc (0 : ℝ) 1, prob.cardyV (cTilde / 12) t ≤ B' := fun t ht => by
    have := hB t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (prob.cardyV_nonneg ha ht.1)] at this
    exact this.trans (le_max_left _ _)
  set T₀ : ℝ := min 1 (1 / (4 * (C + 1) * B')) with hT₀
  have hT₀pos : 0 < T₀ := lt_min one_pos (by positivity)
  refine ⟨T₀, hT₀pos, fun T hT g hg => ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨htc, hvac, hnn⟩ := hg
  have hT1 : T < 1 := lt_of_lt_of_le hlt (min_le_left _ _)
  have hTT : T < 1 / (4 * (C + 1) * B') := lt_of_lt_of_le hlt (min_le_right _ _)
  set M := prob.cardyNorm (cTilde / 12) g with hMdef
  have hMpos : 0 < M := cardyNorm_pos_of_vac_pos S.hc htc hvac
  set V := prob.cardyV (cTilde / 12) with hV
  have hV0 : ∀ t, 0 ≤ t → 0 ≤ V t := fun t ht => prob.cardyV_nonneg ha ht
  have hint : IntegrableOn (fun t => |g t| * V t) (Ioi 0) := htc.int_cardy
  have hint2 : IntegrableOn (fun t => g t * V t) (Ioi 0) := by
    refine hint.mono' ?_ ?_
    · exact (htc.cont.mono Ioi_subset_Ici_self |>.mul (hVc.continuousOn)).aestronglyMeasurable
        measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hV0 t (le_of_lt ht))]
  -- negative part
  set gm : ℝ → ℝ := fun t => (|g t| - g t) / 2 with hgm
  have hgm_int : IntegrableOn (fun t => gm t * V t) (Ioi 0) := by
    refine hint.mono' ?_ ?_
    · exact ((((htc.cont.mono Ioi_subset_Ici_self).abs.sub (htc.cont.mono Ioi_subset_Ici_self)).div_const 2).mul
        hVc.continuousOn).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      have h0 := hV0 t (le_of_lt ht)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
      refine mul_le_mul_of_nonneg_right ?_ h0
      have hg0 := neg_abs_le (g t)
      have hg1 := le_abs_self (g t)
      have hg2 : 0 ≤ (|g t| - g t) / 2 := by linarith
      rw [abs_of_nonneg hg2]
      linarith [abs_nonneg (g t)]
  have hrel : M = (∫ t in Ioi (0 : ℝ), g t * V t) + 2 * ∫ t in Ioi (0 : ℝ), gm t * V t := by
    rw [← integral_const_mul, ← integral_add hint2 (hgm_int.const_mul 2)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    ring
  have hvneg : ∫ t in Ioi (0 : ℝ), g t * V t < 0 := by
    have : prob.gVac (cTilde / 12) g = -2 * π * ∫ t in Ioi (0 : ℝ), g t * V t := rfl
    nlinarith [Real.pi_pos]
  -- the negative mass lives on `(0, T]` and is small
  have hN : ∫ t in Ioi (0 : ℝ), gm t * V t ≤ C * M * B' * T := by
    rw [← Ioc_union_Ioi_eq_Ioi hT.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hgm_int.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi le_rfl)))
      (hgm_int.mono_set (Ioi_subset_Ioi hT.le))]
    have hzero : ∫ t in Ioi T, gm t * V t = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
      have := hnn t (le_of_lt ht)
      have e : gm t = (|g t| - g t) / 2 := rfl
      rw [e, abs_of_nonneg this]; ring
    rw [hzero, add_zero]
    have hb : ∀ t ∈ Ioc (0 : ℝ) T, gm t * V t ≤ C * M * B' := fun t ht => by
      have h1 : gm t ≤ C * M := by
        have := hC g htc t ht.1.le
        refine le_trans ?_ this
        have e : gm t = (|g t| - g t) / 2 := rfl
        rw [e]
        linarith [neg_abs_le (g t), le_abs_self (g t), abs_nonneg (g t)]
      have h2 : V t ≤ B' := hVB t ⟨ht.1.le, ht.2.trans hT1.le⟩
      have hgm0 : 0 ≤ gm t := by
        have e : gm t = (|g t| - g t) / 2 := rfl
        rw [e]; linarith [le_abs_self (g t)]
      exact mul_le_mul h1 h2 (hV0 t ht.1.le) (by positivity)
    calc ∫ t in Ioc (0 : ℝ) T, gm t * V t ≤ ∫ _t in Ioc (0 : ℝ) T, C * M * B' :=
          setIntegral_mono_on (hgm_int.mono_set Ioc_subset_Ioi_self) (integrableOn_const (by simp))
            measurableSet_Ioc hb
      _ = C * M * B' * T := by
          rw [setIntegral_const, Real.volume_real_Ioc_of_le hT.le]; simp [mul_comm]
  -- contradiction
  have h1 : M / 2 < ∫ t in Ioi (0 : ℝ), gm t * V t := by linarith
  have h2 : C * M * B' * T < M / 2 := by
    have : T * (4 * (C + 1) * B') < 1 := by
      have := (lt_div_iff₀ (by positivity : 0 < 4 * (C + 1) * B')).1 hTT; exact this
    nlinarith [mul_pos hMpos hB'pos, mul_nonneg hC0 hMpos.le, mul_pos hMpos hT]
  linarith

/-- **`0 < T_V`** (`dsl:strip-fixed`(b)) from the fixed-charge strip bound. -/
theorem T_V_pos_of_strip (S : FixedChargeStrip prob cTilde) : 0 < prob.T_V cTilde := by
  obtain ⟨T₀, hT₀, hlow⟩ := feasible_gap_lower_bound S
  have hne := prob.feasible_nonempty S.hc
  refine lt_of_lt_of_le hT₀ (le_csInf hne fun T hT => ?_)
  obtain ⟨hT0, g, hg⟩ := hT
  exact hlow T hT0 g hg

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.T_V_pos_of_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.T_V_pos_of_strip

end FormalResearch.ModularBootstrap.FixedWeight
