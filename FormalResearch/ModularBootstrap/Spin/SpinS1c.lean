module

public import FormalResearch.ModularBootstrap.Spin.SpinS1b
public import FormalResearch.ModularBootstrap.Spin.Assembly
public import FormalResearch.ModularBootstrap.Bessel.IntegralRep

/-!
# Proof of `SpinS1c` (Theorem S1 (c)) and unconditional `spinS3` (`spinnotes:S3`)

Proves:
- `spinTestClassJ_radialLift`: for `a ≥ 2`, the radial lift of any spinless test
  `g ∈ TestClass virasoroProblem a` lies in the `J`-finite continuous-spin class
  `SpinTestClassJ a (spinRadialLift g)`.
- `spinS1c : SpinS1c`: for `c ≥ 40`,
  `Δ_Z(c) ≤ Δ_L(c) ≤ Δ_spin(c) ≤ Δ_best(c - 1)`.
- `spinS3 : SpinS3`: unconditional continuous-spin large-`c` slope (`spinnotes:S3`),
  assembled as `spinS3_of_S1 spinS1b spinS1c`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Bessel

/-! ### Section 1: Asymptotic dominance of `I_0(4π √(a t))` by `virasoroProblem.cardyV a t` -/

private lemma spin_besselI0_lower_bound {w δ : ℝ} (hw : 0 ≤ w) (hδ0 : 0 ≤ δ) (hδ : δ ≤ π) :
    (δ / π) * Real.exp (w * Real.cos δ) ≤ besselI 0 w := by
  change (δ / π) * Real.exp (w * Real.cos δ) ≤ besselI0 w
  rw [besselI0_integral]
  have hsplit : ∫ θ in (0 : ℝ)..π, Real.exp (w * Real.cos θ) =
      (∫ θ in (0 : ℝ)..δ, Real.exp (w * Real.cos θ)) +
      (∫ θ in δ..π, Real.exp (w * Real.cos θ)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (Continuous.intervalIntegrable (by fun_prop) 0 δ)
      (Continuous.intervalIntegrable (by fun_prop) δ π)).symm
  have htail : 0 ≤ ∫ θ in δ..π, Real.exp (w * Real.cos θ) :=
    intervalIntegral.integral_nonneg hδ fun θ _ => (Real.exp_pos _).le
  have hhead : δ * Real.exp (w * Real.cos δ) ≤ ∫ θ in (0 : ℝ)..δ, Real.exp (w * Real.cos θ) := by
    have hconst : ∫ _θ in (0 : ℝ)..δ, Real.exp (w * Real.cos δ) = δ * Real.exp (w * Real.cos δ) := by
      simp [intervalIntegral.integral_const]
    rw [← hconst]
    refine intervalIntegral.integral_mono_on hδ0
      (Continuous.intervalIntegrable (by fun_prop) 0 δ)
      (Continuous.intervalIntegrable (by fun_prop) 0 δ) fun θ hθ => ?_
    refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hw)
    exact Real.antitoneOn_cos ⟨hθ.1, hθ.2.trans hδ⟩ ⟨hδ0, hδ⟩ hθ.2
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le

private lemma kernelK_one_eq_besselI0' {α t : ℝ} (hα : 0 ≤ α) (ht : 0 ≤ t) :
    kernelK 1 α t = besselI 0 (4 * π * Real.sqrt (α * t)) := by
  unfold kernelK kernelKTerm besselI besselS besselTerm
  simp only [Nat.sub_self, pow_zero, one_mul, add_zero, Nat.add_sub_cancel]
  refine tsum_congr fun k => ?_
  have hsq : (4 * π * Real.sqrt (α * t)) ^ 2 / 4 = 4 * π ^ 2 * α * t := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hα ht)]
    ring
  rw [hsq]

private lemma spin_besselI0_le_two_cardyV_eventually {a : ℝ} (ha : 2 ≤ a) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ {t : ℝ}, T₀ ≤ t →
      besselI 0 (4 * π * Real.sqrt (a * t)) ≤ 2 * virasoroProblem.cardyV a t := by
  have ha_pos : (0 : ℝ) < a := by linarith
  have ha1_pos : (0 : ℝ) < a - 1 := by linarith
  have hr_lt1 : Real.sqrt ((a - 1) / a) < 1 := by
    rw [Real.sqrt_lt' one_pos, one_pow]
    exact (div_lt_one ha_pos).mpr (by linarith)
  have hr_pos : 0 < Real.sqrt ((a - 1) / a) := Real.sqrt_pos.mpr (div_pos ha1_pos ha_pos)
  let c : ℝ := (1 + Real.sqrt ((a - 1) / a)) / 2
  have hc_gt_r : Real.sqrt ((a - 1) / a) < c := by dsimp [c]; linarith
  have hc_lt1 : c < 1 := by dsimp [c]; linarith
  have hc_pos : 0 < c := by dsimp [c]; linarith
  let δ : ℝ := Real.arccos c
  have hcos_δ : Real.cos δ = c := Real.cos_arccos (by linarith) hc_lt1.le
  have hδ_pos : 0 < δ := by
    have hnn : 0 ≤ δ := Real.arccos_nonneg c
    rcases eq_or_lt_of_le hnn with h0 | hpos
    · exfalso
      have : c = 1 := by rw [← hcos_δ, ← h0, Real.cos_zero]
      linarith
    · exact hpos
  have hδ_le_pi : δ ≤ π := Real.arccos_le_pi c
  have hsqrt_ar : Real.sqrt a * Real.sqrt ((a - 1) / a) = Real.sqrt (a - 1) := by
    rw [← Real.sqrt_mul ha_pos.le, mul_div_cancel₀ _ ha_pos.ne']
  let η : ℝ := 4 * π * (Real.sqrt a * c - Real.sqrt (a - 1))
  have hη_pos : 0 < η := by
    have h1 : Real.sqrt (a - 1) < Real.sqrt a * c := by
      rw [← hsqrt_ar]
      exact mul_lt_mul_of_pos_left hc_gt_r (Real.sqrt_pos.mpr ha_pos)
    dsimp [η]
    have : 0 < Real.sqrt a * c - Real.sqrt (a - 1) := sub_pos.mpr h1
    positivity
  let M : ℝ := max 1 (Real.log (4 * π / δ) / η)
  have hM_ge1 : 1 ≤ M := le_max_left _ _
  refine ⟨M ^ 2, by nlinarith, fun {t} ht => ?_⟩
  have ht_nn : 0 ≤ t := by nlinarith
  have hsqrt_t_ge : M ≤ Real.sqrt t := by
    rw [← Real.sqrt_sq (by linarith : 0 ≤ M)]
    exact Real.sqrt_le_sqrt ht
  have hlog_le : Real.log (4 * π / δ) ≤ η * Real.sqrt t := by
    have h1 : Real.log (4 * π / δ) / η ≤ Real.sqrt t := (le_max_right _ _).trans hsqrt_t_ge
    linarith [(div_le_iff₀ hη_pos).mp h1]
  have h4pi_le : 4 * π / δ ≤ Real.exp (η * Real.sqrt t) := by
    have h := Real.exp_le_exp.mpr hlog_le
    rwa [Real.exp_log (by positivity : 0 < 4 * π / δ)] at h
  have hI_a1 : besselI 0 (4 * π * Real.sqrt ((a - 1) * t)) ≤
      Real.exp (4 * π * Real.sqrt (a - 1) * Real.sqrt t) := by
    rw [Real.sqrt_mul ha1_pos.le t, ← mul_assoc]
    exact besselI0_le_exp (by positivity)
  have hI_a : (δ / π) * Real.exp (4 * π * Real.sqrt a * c * Real.sqrt t) ≤
      besselI 0 (4 * π * Real.sqrt (a * t)) := by
    have hlb := spin_besselI0_lower_bound (w := 4 * π * Real.sqrt (a * t)) (by positivity)
      hδ_pos.le hδ_le_pi
    rw [hcos_δ] at hlb
    have harg : 4 * π * Real.sqrt (a * t) * c = 4 * π * Real.sqrt a * c * Real.sqrt t := by
      rw [Real.sqrt_mul ha_pos.le t]; ring
    rwa [harg] at hlb
  have hexp_ratio : 4 * Real.exp (4 * π * Real.sqrt (a - 1) * Real.sqrt t) ≤
      (δ / π) * Real.exp (4 * π * Real.sqrt a * c * Real.sqrt t) := by
    have hsplit_exp : Real.exp (4 * π * Real.sqrt a * c * Real.sqrt t) =
        Real.exp (η * Real.sqrt t) * Real.exp (4 * π * Real.sqrt (a - 1) * Real.sqrt t) := by
      rw [← Real.exp_add]
      congr 1; dsimp [η]; ring
    rw [hsplit_exp, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have hmul := mul_le_mul_of_nonneg_left h4pi_le (by positivity : 0 ≤ δ / π)
    have hcancel : (δ / π) * (4 * π / δ) = 4 := by
      field_simp [Real.pi_pos.ne', hδ_pos.ne']
    linarith
  have hI_a2_nn : 0 ≤ besselI 0 (4 * π * Real.sqrt ((a - 2) * t)) :=
    besselI_nonneg 0 (by positivity)
  have hV : virasoroProblem.cardyV a t =
      besselI 0 (4 * π * Real.sqrt (a * t)) -
        2 * besselI 0 (4 * π * Real.sqrt ((a - 1) * t)) +
        besselI 0 (4 * π * Real.sqrt ((a - 2) * t)) := by
    rw [virasoro_cardyV_eq, kernelK_one_eq_besselI0' (by linarith) ht_nn,
      kernelK_one_eq_besselI0' (by linarith) ht_nn,
      kernelK_one_eq_besselI0' (by linarith) ht_nn]
  linarith

/-! ### Section 2: `J`-finiteness of radial lifts -/

/-- For `a ≥ 2`, the radial lift of any spinless test `g ∈ TestClass virasoroProblem a` lies in
the `J`-finite continuous-spin class `SpinTestClassJ a`. -/
theorem spinTestClassJ_radialLift {a : ℝ} (ha : 2 ≤ a) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) :
    SpinTestClassJ a (spinRadialLift g) where
  base := (spinTestClass_radialLift_iff ha g).mp hg
  int_J := by
    have heq : (fun p : ℝ × ℝ => |spinRadialLift g p| *
        Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2)) =
        fun p => |g ((p.1 ^ 2 + p.2 ^ 2) / 2)| *
          (Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2)) := by
      ext p; simp only [spinRadialLift]; ring
    rw [heq]
    have hW_cont : Continuous (fun p : ℝ × ℝ =>
        Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2)) := by
      fun_prop
    have hW_nn : ∀ p : ℝ × ℝ,
        0 ≤ Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2) :=
      fun p => mul_nonneg (Real.cosh_pos _).le (Real.cosh_pos _).le
    have hW₀_eq : EqOn (fun t : ℝ => 2 * π * besselI 0 (4 * π * Real.sqrt (a * t)))
        (fun t : ℝ => 2 * π * kernelK 1 a t) (Ici 0) := fun t ht => by
      dsimp only
      rw [kernelK_one_eq_besselI0' (by linarith) (mem_Ici.mp ht)]
    have hK_cont : Continuous (fun t : ℝ => 2 * π * kernelK 1 a t) :=
      continuous_const.mul (continuous_kernelK 1 a)
    have hW₀_cont_Ici : ContinuousOn (fun t : ℝ => 2 * π * besselI 0 (4 * π * Real.sqrt (a * t))) (Ici 0) :=
      hK_cont.continuousOn.congr fun t ht => hW₀_eq ht
    have hW₀_cont : ContinuousOn (fun t : ℝ => 2 * π * besselI 0 (4 * π * Real.sqrt (a * t))) (Ioi 0) :=
      hW₀_cont_Ici.mono Ioi_subset_Ici_self
    refine (spin_polar_integrable_iff hg.cont.abs (fun _ _ => abs_nonneg _)
      hW_cont hW_nn hW₀_cont (fun {t} ht => spin_cosh_integral_zero (by linarith) ht.le)).mpr ?_
    obtain ⟨T₀, hT₀_ge1, hdom⟩ := spin_besselI0_le_two_cardyV_eventually ha
    have hsplit : Ioi (0 : ℝ) ⊆ Ioc 0 T₀ ∪ Ioi T₀ := fun t ht => by
      rcases le_or_gt t T₀ with hle | hgt
      · exact Or.inl ⟨mem_Ioi.mp ht, hle⟩
      · exact Or.inr hgt
    refine (IntegrableOn.union ?_ ?_).mono_set hsplit
    · have hcont_Icc : ContinuousOn
          (fun t : ℝ => |g t| * (2 * π * besselI 0 (4 * π * Real.sqrt (a * t)))) (Icc 0 T₀) :=
        (hg.cont.abs.mono Icc_subset_Ici_self).mul (hW₀_cont_Ici.mono Icc_subset_Ici_self)
      exact hcont_Icc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · have hdom_int : IntegrableOn (fun t : ℝ => (4 * π) * (|g t| * virasoroProblem.cardyV a t)) (Ioi T₀) :=
        IntegrableOn.mono_set (hg.int_cardy.const_mul (4 * π)) (Ioi_subset_Ioi (by linarith))
      refine hdom_int.mono' ?_ ?_
      · exact ((hg.cont.abs.mono (Ioi_subset_Ici (by linarith))).mul
          (hW₀_cont.mono (Ioi_subset_Ioi (by linarith)))).aestronglyMeasurable measurableSet_Ioi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht_ge : T₀ ≤ t := (mem_Ioi.mp ht).le
        have hI_nn : 0 ≤ besselI 0 (4 * π * Real.sqrt (a * t)) := besselI_nonneg 0 (by positivity)
        rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) hI_nn))]
        have hle := hdom ht_ge
        calc |g t| * (2 * π * besselI 0 (4 * π * Real.sqrt (a * t)))
            ≤ |g t| * (2 * π * (2 * virasoroProblem.cardyV a t)) := by gcongr
          _ = 4 * π * (|g t| * virasoroProblem.cardyV a t) := by ring

/-! ### Section 3: Theorem S1 (c) and unconditional Theorem S3 -/

/-- **Theorem S1 (c)** (`spinnotes:S1`): for `c ≥ 40`,
`Δ_Z(c) ≤ Δ_L(c) ≤ Δ_spin(c) ≤ Δ_best(c - 1)`. -/
theorem spinS1c : SpinS1c := by
  intro c hc
  let a : ℝ := (c - 1) / 12
  have ha : 2 ≤ a := by dsimp [a]; linarith
  have hc_shift : 12 * virasoroProblem.totalShift ≤ c - 1 := by
    rw [virasoroProblem_totalShift]; linarith
  have hne_spinless : {T : ℝ | 0 < T ∧ ∃ g, virasoroProblem.IsFeasible a T g}.Nonempty :=
    virasoroProblem.feasible_nonempty hc_shift
  have hlift : ∀ {T : ℝ} {g : ℝ → ℝ}, virasoroProblem.IsFeasible a T g →
      SpinIsFeasible (SpinTestClassJ a) liouvilleCone a T (spinRadialLift g) := by
    intro T g ⟨hg, hvac, hpos⟩
    refine ⟨spinTestClassJ_radialLift ha hg, ?_, ?_⟩
    · rw [(spinM2_and_phiVac_radialLift ha hg).2]; exact hvac
    · intro p ⟨hp1, hp2, hsum⟩
      rw [spinEvalT_radialLift g hp1 hp2]
      exact hpos (p.1 + p.2) hsum
  have hsub_J : {T : ℝ | 0 < T ∧ ∃ g, virasoroProblem.IsFeasible a T g} ⊆
      {T : ℝ | 0 < T ∧ ∃ Φ, SpinIsFeasible (SpinTestClassJ a) liouvilleCone a T Φ} := by
    rintro T ⟨hT, g, hg⟩
    exact ⟨hT, spinRadialLift g, hlift hg⟩
  have hne_J : {T : ℝ | 0 < T ∧ ∃ Φ, SpinIsFeasible (SpinTestClassJ a) liouvilleCone a T Φ}.Nonempty :=
    hne_spinless.mono hsub_J
  have hne_base : {T : ℝ | 0 < T ∧ ∃ Φ, SpinIsFeasible (SpinTestClass a) liouvilleCone a T Φ}.Nonempty :=
    hne_J.mono (by rintro T ⟨hT, Φ, hC, hvac, hpos⟩; exact ⟨hT, Φ, hC.base, hvac, hpos⟩)
  refine ⟨spinDeltaInt_le_spinDeltaL c hne_base, spinDeltaL_le_spinDeltaSpin c hne_J, ?_⟩
  unfold spinDeltaSpin FixedWeightProblem.Delta_best spinThrInf FixedWeightProblem.T_V
  have hinf : sInf {T : ℝ | 0 < T ∧ ∃ Φ, SpinIsFeasible (SpinTestClassJ a) liouvilleCone a T Φ} ≤
      sInf {T : ℝ | 0 < T ∧ ∃ g, virasoroProblem.IsFeasible a T g} :=
    csInf_le_csInf ⟨0, fun T hT => hT.1.le⟩ hne_spinless hsub_J
  linarith

/-- **Theorem S3** (`spinnotes:S3`, unconditional): there exist universal constants `C₀ > 0`
and `c₀ ≥ 40` such that for all `c ≥ c₀`,
`Δ_L(c) ≤ (c - 1) / 12 - C₀ c^{1/3} (log c)^{2/3}`. -/
theorem spinS3 : SpinS3 :=
  spinS3_of_S1 spinS1b spinS1c

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinTestClassJ_radialLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinTestClassJ_radialLift

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS1c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS1c

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS3

end FormalResearch.ModularBootstrap.Spin
