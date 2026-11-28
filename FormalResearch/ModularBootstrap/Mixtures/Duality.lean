module

public import FormalResearch.ModularBootstrap.Mixtures.Primal
public import FormalResearch.ModularBootstrap.Mixtures.DualityLP

/-!
# Duality, primal attainment, and LP convergence for common sources and mixtures (`pmix:duality`)

Source: `CFT/modular_bootstrap/paper/positive_mixtures.tex`, Proposition PM.8 (`pmix:duality`).

Establishes at large charge `c̃ ≥ c₀`:
- `T_weak_pos_of_common`, `T_weak_le_T_V_of_common`: `0 < T_weak(c̃) ≤ T_V(c̃) < ∞`.
- `pmix_duality_common`: for any `CommonSource`, full `dsl:strip-fixed`, `ds:M`, `ds:E` (a)–(c),
  `ds:primal` (a)–(d), and `ds:LP` (i)–(iii).
- `pmix_duality_mixture`: for any `MixtureData`, rebasing (`MixtureData.rebase`) produces a
  `CommonSource` with `min_i r'_i = 0`, transferring all conclusions (including `0 < T_{weak,mix}
  ≤ T_{mix} < ∞`, arbitrary closed-support separation, constrained/unconstrained strong duality,
  reserve separation, primal attainment, and finite-derivative LP convergence) directly to
  `M.toSource` at charge `c̃` when `c₀ ≤ c̃ - 12 * M.rmin`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality
open FormalResearch.ModularBootstrap.FixedWeight
open FormalResearch.ModularBootstrap.LP
open FormalResearch.ModularBootstrap.WeightAxioms

/-! ### Weak-threshold positivity and comparison for `CommonSource` -/

private lemma cardyNorm_pos_of_exists_ne_zero_src {src : ShiftSource} {Fl : FloorData src} {a : ℝ}
    (hAt : Fl.At a) {g : ℝ → ℝ} (hg : TestClass src a g) (hne : ∃ t : ℝ, 0 ≤ t ∧ g t ≠ 0) :
    0 < src.cardyNorm a g := by
  obtain ⟨t₀, ht₀, hgt₀⟩ := hne
  have hpos_pt : ∃ t₁ : ℝ, 0 < t₁ ∧ g t₁ ≠ 0 := by
    rcases ht₀.eq_or_lt with rfl | hpos
    · have hcont0 : ContinuousWithinAt g (Ici 0) 0 := hg.cont 0 (le_rfl : (0 : ℝ) ∈ Ici 0)
      obtain ⟨δ, hδ, hmem⟩ := Metric.continuousWithinAt_iff.1 hcont0 (|g 0| / 2)
        (half_pos (abs_pos.2 hgt₀))
      refine ⟨δ / 2, half_pos hδ, fun hz => ?_⟩
      have h1 := hmem (x := δ / 2) (mem_Ici.mpr (half_pos hδ).le) (by
        rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]; linarith)
      simp only [hz, Real.dist_eq, zero_sub, abs_neg] at h1
      have hpos_abs : 0 < |g 0| := abs_pos.2 hgt₀
      linarith
    · exact ⟨t₀, hpos, hgt₀⟩
  obtain ⟨t₁, ht₁, hg1⟩ := hpos_pt
  have hV1_pos : 0 < src.cardyV a t₁ := hAt.pos_V ht₁
  have hcont_at : ContinuousAt (fun t => |g t| * src.cardyV a t) t₁ :=
    ((hg.cont.abs).continuousAt (Ici_mem_nhds ht₁)).mul (src.continuous_cardyV a).continuousAt
  have hev : ∀ᶠ t in 𝓝 t₁, 0 < |g t| * src.cardyV a t :=
    hcont_at.eventually (Ioi_mem_nhds (mul_pos (abs_pos.2 hg1) hV1_pos))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hev.and (Ioi_mem_nhds ht₁))
  have hIoo_sub : Ioo (t₁ - ε) (t₁ + ε) ⊆
      Function.support (fun t => |g t| * src.cardyV a t) ∩ Ioi 0 := fun t ht => by
    have hd : dist t t₁ < ε := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]
    exact ⟨(hball hd).1.ne', (hball hd).2⟩
  have hpos_v : 0 < volume (Ioo (t₁ - ε) (t₁ + ε)) := by
    rw [Real.volume_Ioo]; simp; linarith
  have hnonneg_f : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ |g t| * src.cardyV a t := fun t ht =>
    mul_nonneg (abs_nonneg _) (hAt.nonneg_V (le_of_lt ht))
  unfold ShiftSource.cardyNorm
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hnonneg_f)) hg.int_cardy]
  exact lt_of_lt_of_le hpos_v (measure_mono hIoo_sub)

private lemma isWeaklyFeasible_of_isFeasible {src : ShiftSource} {a T : ℝ}
    {g : ℝ → ℝ} (hg : src.IsFeasible a T g) :
    src.IsWeaklyFeasible a T g := by
  refine ⟨hg.1, ?_, hg.2.1.le, hg.2.2⟩
  by_contra hall
  push Not at hall
  have h0 : (fun t => g t * src.cardyV a t) =ᵐ[volume.restrict (Ioi 0)] 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp [hall t (mem_Ioi.1 ht).le]
  have hv0 : src.gVac a g = 0 := by
    unfold ShiftSource.gVac
    rw [integral_congr_ae h0]; simp
  have := hg.2.1
  linarith

/-- Every `CommonSource` at large charge satisfies `T_weak ≤ T_V` (with a nonempty feasible set). -/
lemma T_weak_le_T_V_of_common (C : CommonSource) {cTilde : ℝ} (hc : 12 * C.a₀ ≤ cTilde) :
    C.src.T_weak cTilde ≤ C.src.T_V cTilde := by
  have hAt : C.F.At (cTilde / 12) := C.at_ (by linarith)
  obtain ⟨β₀, S₀⟩ := SourceDualSetupCore.exists_of_common C hc one_pos
  obtain ⟨-, T, hT, ⟨g, hg⟩, -⟩ := T_V_lt_top_of_core S₀
  have hne : {T : ℝ | 0 < T ∧ ∃ g, C.src.IsFeasible (cTilde / 12) T g}.Nonempty := ⟨T, hT, g, hg⟩
  refine csInf_le_csInf ⟨0, fun _ h => h.1.le⟩ hne ?_
  intro τ ⟨hτ, g', hg'⟩
  exact ⟨hτ, g', isWeaklyFeasible_of_isFeasible hg'⟩

/-- **Strict positivity of the weak threshold** (`0 < T_weak(c̃)`) for `CommonSource` at every
`12 C.a₀ ≤ c̃`. -/
theorem T_weak_pos_of_common (C : CommonSource) {cTilde : ℝ} (hc : 12 * C.a₀ ≤ cTilde) :
    0 < C.src.T_weak cTilde := by
  have hAt : C.F.At (cTilde / 12) := C.at_ (by linarith)
  obtain ⟨β₀, S₀⟩ := SourceDualSetupCore.exists_of_common C hc one_pos
  have hTw_nn : 0 ≤ C.src.T_weak cTilde :=
    le_csInf (by
      obtain ⟨-, T, hT, ⟨g, hg⟩, -⟩ := T_V_lt_top_of_core S₀
      exact ⟨T, hT, g, isWeaklyFeasible_of_isFeasible hg⟩) (fun _ h => h.1.le)
  by_contra hle0
  have hTw0 : C.src.T_weak cTilde = 0 := le_antisymm (not_lt.1 hle0) hTw_nn
  have hne : {T : ℝ | 0 < T ∧ ∃ g, C.src.IsWeaklyFeasible (cTilde / 12) T g}.Nonempty := by
    obtain ⟨-, T, hT, ⟨g, hg⟩, -⟩ := T_V_lt_top_of_core S₀
    exact ⟨T, hT, g, isWeaklyFeasible_of_isFeasible hg⟩
  have hmem : ∀ n : ℕ, ∃ τ : ℝ, 0 < τ ∧ τ < 1 / ((n : ℝ) + 1) ∧
      ∃ g, C.src.IsWeaklyFeasible (cTilde / 12) τ g := fun n => by
    have hlt : C.src.T_weak cTilde < 1 / ((n : ℝ) + 1) := by rw [hTw0]; positivity
    obtain ⟨τ, hτmem, hτlt⟩ := exists_lt_of_csInf_lt hne hlt
    exact ⟨τ, hτmem.1, hτlt, hτmem.2⟩
  choose τ hτpos hτlt g0 hg0 using hmem
  let g : ℕ → ℝ → ℝ := fun n t => (C.src.cardyNorm (cTilde / 12) (g0 n))⁻¹ * g0 n t
  have htc : ∀ n, TestClass C.src (cTilde / 12) (g n) := fun n =>
    testClass_smul_src _ (hg0 n).1
  have hM1 : ∀ n, C.src.cardyNorm (cTilde / 12) (g n) = 1 := fun n => by
    have hMp := cardyNorm_pos_of_exists_ne_zero_src hAt (hg0 n).1 (hg0 n).2.1
    rw [cardyNorm_smul_of_nonneg_src _ (inv_nonneg.2 hMp.le), inv_mul_cancel₀ hMp.ne']
  have hv : ∀ n, ∫ t in Ioi (0 : ℝ), g n t * C.src.cardyV (cTilde / 12) t ≤ 0 := fun n => by
    have hMp := cardyNorm_pos_of_exists_ne_zero_src hAt (hg0 n).1 (hg0 n).2.1
    have hvac_p : 0 ≤ C.src.gVac (cTilde / 12) (g n) := by
      dsimp [g]; rw [gVac_smul_src]; exact mul_nonneg (inv_nonneg.2 hMp.le) (hg0 n).2.2.1
    change 0 ≤ -2 * π * ∫ t in Ioi (0 : ℝ), g n t * C.src.cardyV (cTilde / 12) t at hvac_p
    nlinarith [Real.pi_pos]
  have hneg1 : ∀ n, ∀ t ≥ (1 : ℝ), 0 ≤ g n t := fun n t ht => by
    have hMp := cardyNorm_pos_of_exists_ne_zero_src hAt (hg0 n).1 (hg0 n).2.1
    have hle1 : τ n ≤ t := by
      have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
        div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by positivity)
      linarith [hτlt n]
    exact mul_nonneg (inv_nonneg.2 hMp.le) ((hg0 n).2.2.2 t hle1)
  obtain ⟨φ, gs, hφ, hgstc, -, hunif, -, hgs_vac, ⟨t₀, ht₀, hgt₀⟩, -, -, -⟩ :=
    exists_primal_limit_src C hc htc hM1 hv zero_le_one hneg1
  have hgs_nn : ∀ t : ℝ, 0 < t → 0 ≤ gs t := fun t ht => by
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt ht
    have hpt : Tendsto (fun k => g (φ k) t) atTop (𝓝 (gs t)) :=
      (hunif t).tendsto_at ⟨ht.le, le_rfl⟩
    refine ge_of_tendsto hpt (eventually_atTop.2 ⟨N, fun k hk => ?_⟩)
    have hkN : (N : ℝ) + 1 ≤ (φ k : ℝ) + 1 := by
      have : N ≤ φ k := hk.trans (hφ.id_le k)
      exact_mod_cast Nat.add_le_add_right this 1
    have hτ_le : τ (φ k) ≤ t := by
      have h1 : 1 / ((φ k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) hkN
      linarith [hτlt (φ k), h1, hN]
    have hMp := cardyNorm_pos_of_exists_ne_zero_src hAt (hg0 (φ k)).1 (hg0 (φ k)).2.1
    exact mul_nonneg (inv_nonneg.2 hMp.le) ((hg0 (φ k)).2.2.2 t hτ_le)
  have hpos_pt : ∃ t₁ : ℝ, 0 < t₁ ∧ gs t₁ ≠ 0 := by
    rcases ht₀.eq_or_lt with rfl | hpos
    · have hcont0 : ContinuousWithinAt gs (Ici 0) 0 := hgstc.cont 0 (le_rfl : (0 : ℝ) ∈ Ici 0)
      obtain ⟨δ, hδ, hmem⟩ := Metric.continuousWithinAt_iff.1 hcont0 (|gs 0| / 2)
        (half_pos (abs_pos.2 hgt₀))
      refine ⟨δ / 2, half_pos hδ, fun hz => ?_⟩
      have h1 := hmem (x := δ / 2) (mem_Ici.mpr (half_pos hδ).le) (by
        rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]; linarith)
      simp only [hz, Real.dist_eq, zero_sub, abs_neg] at h1
      have hpos_abs : 0 < |gs 0| := abs_pos.2 hgt₀
      linarith
    · exact ⟨t₀, hpos, hgt₀⟩
  obtain ⟨t₁, ht₁, hgs1⟩ := hpos_pt
  have hint_pos : 0 < ∫ t in Ioi (0 : ℝ), gs t * C.src.cardyV (cTilde / 12) t := by
    have hcont_f : ContinuousOn (fun t => gs t * C.src.cardyV (cTilde / 12) t) (Ioi 0) :=
      (hgstc.cont.mono Ioi_subset_Ici_self).mul (C.src.continuous_cardyV (cTilde / 12)).continuousOn
    have hnonneg_f : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ gs t * C.src.cardyV (cTilde / 12) t := fun t ht =>
      mul_nonneg (hgs_nn t ht) (hAt.nonneg_V (le_of_lt ht))
    have hgs1_pos' : 0 < gs t₁ := lt_of_le_of_ne (hgs_nn t₁ ht₁) hgs1.symm
    have hV1_pos : 0 < C.src.cardyV (cTilde / 12) t₁ := hAt.pos_V ht₁
    have hgV_hint : IntegrableOn (fun t => gs t * C.src.cardyV (cTilde / 12) t) (Ioi 0) := by
      refine hgstc.int_cardy.mono' (hcont_f.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hAt.nonneg_V ht.le)]
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hnonneg_f)) hgV_hint]
    have hcont_at : ContinuousAt (fun t => gs t * C.src.cardyV (cTilde / 12) t) t₁ :=
      (hgstc.cont.continuousAt (Ici_mem_nhds ht₁)).mul
        (C.src.continuous_cardyV (cTilde / 12)).continuousAt
    have hev : ∀ᶠ t in 𝓝 t₁, 0 < gs t * C.src.cardyV (cTilde / 12) t :=
      hcont_at.eventually (Ioi_mem_nhds (mul_pos hgs1_pos' hV1_pos))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hev.and (Ioi_mem_nhds ht₁))
    have hIoo_sub : Ioo (t₁ - ε) (t₁ + ε) ⊆
        Function.support (fun t => gs t * C.src.cardyV (cTilde / 12) t) ∩ Ioi 0 := fun t ht => by
      have hd : dist t t₁ < ε := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]
      exact ⟨(hball hd).1.ne', (hball hd).2⟩
    have hpos_v : 0 < volume (Ioo (t₁ - ε) (t₁ + ε)) := by
      rw [Real.volume_Ioo]; simp; linarith
    exact lt_of_lt_of_le hpos_v (measure_mono hIoo_sub)
  have hv_neg : C.src.gVac (cTilde / 12) gs < 0 := by
    unfold ShiftSource.gVac
    nlinarith [Real.pi_pos]
  linarith

/-! ### Full `pmix:duality` package for `CommonSource` and `MixtureData` -/

/-- Bundled conclusion of Proposition PM.8 (`pmix:duality`) for a `ShiftSource` with floor `Fl`
at charge `c̃`: combines `dsl:strip-fixed`, `ds:M`, `0 < T_weak ≤ T_V < ∞`, `ds:E` (a)–(c),
`ds:primal` (a)–(d), and `ds:LP` (i)–(iii). -/
structure DualityBundleS (C : CommonSource) (cTilde : ℝ) where
  at_ : C.F.At (cTilde / 12)
  strip_bound : ∃ K : ℝ, 0 < K ∧ ∀ {g : ℝ → ℝ}, TestClass C.src (cTilde / 12) g →
    (∫ t in Ioi (0 : ℝ), |g t| * kernelK C.src.w (cTilde / 12) t ≤
      K * C.src.cardyNorm (cTilde / 12) g) ∧
    ContinuousOn (hankelContinuationW C.src.w cTilde g) {b : ℂ | |b.im| ≤ 1 / 2} ∧
    DifferentiableOn ℂ (hankelContinuationW C.src.w cTilde g) {b : ℂ | |b.im| < 1 / 2} ∧
    (∀ {b : ℂ}, |b.im| ≤ 1 / 2 →
      ‖hankelContinuationW C.src.w cTilde g b‖ ≤ 2 * π * K * C.src.cardyNorm (cTilde / 12) g)
  tail : ∀ ε > 0, ∃ R : ℝ, ∀ t ≥ R, t ^ (C.src.w - 1) ≤ ε * C.src.cardyV (cTilde / 12) t
  core : ∃ β₀ : ℝ, SourceDualSetupCore C.src cTilde β₀ 1
  T_weak_pos : 0 < C.src.T_weak cTilde
  T_weak_le_T_V : C.src.T_weak cTilde ≤ C.src.T_V cTilde
  T_V_pos : 0 < C.src.T_V cTilde
  feasible_nonempty : ∃ T : ℝ, 0 < T ∧ ∃ g, C.src.IsFeasible (cTilde / 12) T g
  /-- `ds:E`(b) for compact `F ⊂ (0, ∞)`. -/
  duality_E_b : ∀ {F : Set ℝ}, IsCompact F → F ⊆ Ioi 0 →
    (C.src.T_V cTilde ≤ constrainedThresholdS C.src cTilde F ∧
      (constrainedGapsS C.src cTilde F).Nonempty) ∧
    (0 < constrainedThresholdS C.src cTilde F ∧
      ∃ meas : SourceCrossingMeasure C.src (cTilde / 12),
        meas.ν (F ∪ Ici (constrainedThresholdS C.src cTilde F))ᶜ = 0) ∧
    (IsGreatest {τ : ℝ | 0 < τ ∧ ∃ meas : SourceCrossingMeasure C.src (cTilde / 12),
        meas.ν (F ∪ Ici τ)ᶜ = 0} (constrainedThresholdS C.src cTilde F)) ∧
    (∀ τ : ℝ, 0 < τ → τ < constrainedThresholdS C.src cTilde F →
      ∃ meas : SourceCrossingMeasure C.src (cTilde / 12), meas.ν (F ∪ Ici τ)ᶜ = 0)
  /-- `ds:E`(b) for `F = ∅` (unconstrained optimum). -/
  duality_E_b_empty :
    constrainedThresholdS C.src cTilde ∅ = C.src.T_V cTilde ∧
    (∃ meas : SourceCrossingMeasure C.src (cTilde / 12),
      meas.ν (Ici (C.src.T_V cTilde))ᶜ = 0) ∧
    IsGreatest {τ : ℝ | 0 < τ ∧ ∃ meas : SourceCrossingMeasure C.src (cTilde / 12),
      meas.ν (Ici τ)ᶜ = 0} (C.src.T_V cTilde)
  /-- `ds:LP`(i) and (iii) for `C.src`. -/
  duality_LP_iii :
    thrInfS C.src (cTilde / 12) ∅ = ENNReal.ofReal (C.src.T_V cTilde) ∧
    Tendsto (fun N => thrNS C.src (cTilde / 12) ∅ N) atTop
      (𝓝 (ENNReal.ofReal (C.src.T_V cTilde))) ∧
    (⨅ P : ℕ, thrNS C.src (cTilde / 12) ∅ (2 * P + 1)) = ENNReal.ofReal (C.src.T_V cTilde) ∧
    IsGreatest {τ : ℝ | 0 < τ ∧ ∃ meas : SourceCrossingMeasure C.src (cTilde / 12),
      meas.ν (Ici τ)ᶜ = 0} (C.src.T_V cTilde)

/-- **Proposition PM.8 (`pmix:duality`) for any `CommonSource`**: unconditionally for every
`12 C.a₀ ≤ c̃`, every `CommonSource` enjoys `dsl:strip-fixed`, `ds:M`, `0 < T_weak ≤ T_V < ∞`,
and all conclusions of `ds:E`, `ds:primal`, and `ds:LP`. -/
theorem pmix_duality_common (C : CommonSource) {cTilde : ℝ} (hc : 12 * C.a₀ ≤ cTilde) :
    Nonempty (DualityBundleS C cTilde) := by
  have hAt : C.F.At (cTilde / 12) := C.at_ (by linarith)
  have hTV := T_V_pos_of_common C hc
  have hTw := T_weak_pos_of_common C hc
  have hle := T_weak_le_T_V_of_common C hc
  obtain ⟨β₀, S₀⟩ := SourceDualSetupCore.exists_of_common C hc one_pos
  obtain ⟨-, T, hT, ⟨g, hg⟩, -⟩ := T_V_lt_top_of_core S₀
  exact ⟨{
    at_ := hAt
    strip_bound := (dsl_strip_fixed_a_of_floorAt C.F).2 hAt
    tail := tail_of_floorAt hAt
    core := ⟨β₀, S₀⟩
    T_weak_pos := hTw
    T_weak_le_T_V := hle
    T_V_pos := hTV
    feasible_nonempty := ⟨T, hT, g, hg⟩
    duality_E_b := fun hFc hF => theorem_E_b_compact_src hAt hFc hF hTV
    duality_E_b_empty := theorem_E_b_compact_empty_src hAt hTV
    duality_LP_iii := ds_LP_iii_src hAt hTV }⟩

/-- Transport a crossing measure across rebasing `M.rebase` ↔ `M`. -/
def crossingMeasure_of_rebase (M : MixtureData) {cTilde : ℝ}
    (meas : SourceCrossingMeasure M.rebase.toSource (cTilde / 12 - M.rmin)) :
    SourceCrossingMeasure M.toSource (cTilde / 12) where
  ν := meas.ν
  supp_nonneg := meas.supp_nonneg
  finite_laplace := meas.finite_laplace
  crossing {β} hβ := by
    have heq1 : (fun t => thermalDiff M.toSource.w β t) =
        fun t => thermalDiff M.rebase.toSource.w β t := by
      simp [M.rebase_toSource_w]
    have heq2 : ∀ t, M.toSource.cardyDensity (cTilde / 12) t =
        M.rebase.toSource.cardyDensity (cTilde / 12 - M.rmin) t := fun t =>
      (M.rebase_cardyDensity (cTilde / 12) t).symm
    simp_rw [heq1, heq2]
    exact meas.crossing hβ

/-- Transport a crossing measure in the reverse direction `M` → `M.rebase`. -/
def rebase_crossingMeasure (M : MixtureData) {cTilde : ℝ}
    (meas : SourceCrossingMeasure M.toSource (cTilde / 12)) :
    SourceCrossingMeasure M.rebase.toSource (cTilde / 12 - M.rmin) where
  ν := meas.ν
  supp_nonneg := meas.supp_nonneg
  finite_laplace := meas.finite_laplace
  crossing {β} hβ := by
    have heq1 : (fun t => thermalDiff M.rebase.toSource.w β t) =
        fun t => thermalDiff M.toSource.w β t := by
      simp [M.rebase_toSource_w]
    have heq2 : ∀ t, M.rebase.toSource.cardyDensity (cTilde / 12 - M.rmin) t =
        M.toSource.cardyDensity (cTilde / 12) t := fun t =>
      M.rebase_cardyDensity (cTilde / 12) t
    simp_rw [heq1, heq2]
    exact meas.crossing hβ

/-- **Proposition PM.8 (`pmix:duality`) for a positive mixture `M : MixtureData`**:
rebasing to `min_i r'_i = 0` yields a `CommonSource` (`M.rebase.commonSource hi₀`), giving at all
rebased charges `c̃ - 12 r_min ≥ c₀`:
1. the full `DualityBundleS` (plus `theorem_E_a_src`, `theorem_E_c_reserve_src`,
   `theorem_primal_src`, `ds_LP_i_src`, `ds_LP_ii_src`) for `M.rebase.commonSource hi₀` at
   `c̃ - 12 r_min`; and
2. on the un-rebased mixture `M.toSource` at charge `c̃`:
   `0 < T_weak(c̃) ≤ T_V(c̃) < ∞`, existence of an attaining crossing measure at `[T_V(c̃), ∞)`,
   and constrained crossing attainment & LP limit equivalence via `M.rebase_T_V` /
   `crossingMeasure_of_rebase`. -/
theorem pmix_duality_mixture (M : MixtureData) :
    ∃ (i₀ : Fin M.s) (hi₀ : M.rebase.r i₀ = 0),
      ∀ {cTilde : ℝ}, 12 * (M.rebase.commonSource hi₀).a₀ ≤ cTilde - 12 * M.rmin →
        Nonempty (DualityBundleS (M.rebase.commonSource hi₀) (cTilde - 12 * M.rmin)) ∧
        0 < M.toSource.T_weak cTilde ∧
        M.toSource.T_weak cTilde ≤ M.toSource.T_V cTilde ∧
        (∃ T : ℝ, 0 < T ∧ ∃ g, M.toSource.IsFeasible (cTilde / 12) T g) ∧
        IsGreatest {τ : ℝ | 0 < τ ∧ ∃ meas : SourceCrossingMeasure M.toSource (cTilde / 12),
          meas.ν (Ici τ)ᶜ = 0} (M.toSource.T_V cTilde) := by
  obtain ⟨i₀, hi₀⟩ := M.rebase_exists_zero
  let C := M.rebase.commonSource hi₀
  refine ⟨i₀, hi₀, fun {cTilde} hc => ?_⟩
  obtain ⟨B⟩ := pmix_duality_common C hc
  have hTw : M.rebase.toSource.T_weak (cTilde - 12 * M.rmin) = M.toSource.T_weak cTilde :=
    M.rebase_T_weak cTilde
  have hTV : M.rebase.toSource.T_V (cTilde - 12 * M.rmin) = M.toSource.T_V cTilde :=
    M.rebase_T_V cTilde
  have hpos_w : 0 < M.toSource.T_weak cTilde := hTw ▸ B.T_weak_pos
  have hle_wv : M.toSource.T_weak cTilde ≤ M.toSource.T_V cTilde := by
    rw [← hTw, ← hTV]; exact B.T_weak_le_T_V
  obtain ⟨T, hT, g, hg⟩ := B.feasible_nonempty
  have hg' : M.toSource.IsFeasible (cTilde / 12) T g := by
    have hch : (cTilde - 12 * M.rmin) / 12 = cTilde / 12 - M.rmin := M.rebase_charge cTilde
    rw [hch] at hg
    exact (M.rebase_isFeasible_iff (a := cTilde / 12) (T := T) (g := g)).1 hg
  obtain ⟨-, ⟨meas, hm⟩, hmax⟩ := B.duality_E_b_empty
  have hm' : ∀ {τ : ℝ}, (∃ m : SourceCrossingMeasure M.rebase.toSource ((cTilde - 12 * M.rmin) / 12),
      m.ν (Ici τ)ᶜ = 0) ↔
      ∃ m : SourceCrossingMeasure M.toSource (cTilde / 12), m.ν (Ici τ)ᶜ = 0 := by
    intro τ
    rw [M.rebase_charge cTilde]
    exact ⟨fun ⟨m, h⟩ => ⟨crossingMeasure_of_rebase M m, h⟩,
      fun ⟨m, h⟩ => ⟨rebase_crossingMeasure M m, h⟩⟩
  refine ⟨⟨B⟩, hpos_w, hle_wv, ⟨T, hT, g, hg'⟩, ?_⟩
  refine ⟨⟨B.T_V_pos.trans_eq hTV, ?_⟩, fun τ hτ => ?_⟩
  · rw [← hTV]; exact (hm' (τ := M.rebase.toSource.T_V (cTilde - 12 * M.rmin))).1 ⟨meas, hm⟩
  · rw [← hTV]
    exact hmax.2 ⟨hτ.1, (hm' (τ := τ)).2 hτ.2⟩

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.T_weak_pos_of_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.T_weak_pos_of_common

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_duality_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.pmix_duality_common

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_duality_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.pmix_duality_mixture

end FormalResearch.ModularBootstrap.Mixtures
