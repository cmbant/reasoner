module

public import FormalResearch.ModularBootstrap.FixedWeightTip.BlowupAndRigidity
public import FormalResearch.ModularBootstrap.TwoLevel.PinnedRigidity

/-!
# Theorem 2.1: the two-level leading-order theorem (`virasoro_two_level.tex`, `gt:2.1`)

At every integer `(w, Q)` (`prob : FixedWeightProblem`).  Let `c'_j → ∞` along a countably generated
filter `p`, `g_j` weakly feasible (`g_vac ≥ 0`, `g_j ≥ 0` on `[τ_j, ∞)`, `τ_j = leastThreshold g_j`),
and suppose `g_j(t_*(c_j)) ≥ 0` at `t_*(c_j) = ξ̄ c_j' + A₁ c_j'^{1/3} + o(c_j'^{1/3})`, `A₁ < A_opt`.

* `concrete_two_level_theorem`: `A_2^*(A₁) ≤ liminf (τ_j - ξ̄ c_j')/c_j'^{1/3}` (in `EReal`);
* `concrete_two_level_eventually`: the eventual `ε` form;
* `concrete_two_level_equality`: if `(τ_j - ξ̄ c_j')/c_j'^{1/3} → A_2^*(A₁)` along `p`
  (equality along a subsequence is the instance `ι = ℕ`, `p = atTop`), then
  `Φ_j → c · g_α(-β ·)` locally uniformly and in `L¹` (`c > 0` fixed by `‖Φ‖₁ = 1`),
  `s₁ → -z₂/β` and the vacuum part `γ → 0`.

The proofs use only Proposition T (through `blowupFamilyPackage_of_concrete_tests_general`),
the Clark two-node theorem `clark_two_node_uncertainty`/`clark_two_node_equality`, and Scheffé.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.ModularBootstrap.FixedWeightTip
open Crossing PoissonJensen WeightAxioms TipFront FixedWeight
open FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.Analysis

/-- The `s`-coordinate `(√(3 t/c') - ξ_*)/ε` of the point `t` in the blow-up window. -/
noncomputable def pinPoint (c' t : ℝ) : ℝ := (Real.sqrt (3 * t / c') - xiStar) / tipEps c'

lemma three_mul_div_eq {c' t : ℝ} (hc' : 0 < c') :
    3 * t / c' = xiStar ^ 2 + 3 * ((t - xiBar * c') / c' ^ (1 / 3 : ℝ)) * tipEps c' := by
  have hp13 : 0 < c' ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc' _
  have hce : c' * tipEps c' = c' ^ (1 / 3 : ℝ) := by
    unfold tipEps
    calc c' * c' ^ (-(2 / 3 : ℝ)) = c' ^ (1 : ℝ) * c' ^ (-(2 / 3 : ℝ)) := by rw [Real.rpow_one]
      _ = c' ^ (1 + -(2 / 3 : ℝ)) := (Real.rpow_add hc' _ _).symm
      _ = c' ^ (1 / 3 : ℝ) := by norm_num
  unfold xiBar
  rw [← hce]
  have hε := (tipEps_pos hc').ne'
  field_simp
  ring

lemma tendsto_pinPoint {ι : Type*} {p : Filter ι} {c' ts : ι → ℝ} (hc' : Tendsto c' p atTop)
    {A : ℝ}
    (hts : Tendsto (fun n => (ts n - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ)) p (nhds A)) :
    Tendsto (fun n => pinPoint (c' n) (ts n)) p (nhds (3 * A / (2 * xiStar))) := by
  have he : Tendsto (fun n => tipEps (c' n)) p (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc'
  have hr : Tendsto (fun n => xiStar ^ 2 + 3 * ((ts n - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ)) *
      tipEps (c' n)) p (nhds (xiStar ^ 2)) := by
    simpa using tendsto_const_nhds.add ((hts.const_mul 3).mul he)
  have hx : Tendsto (fun n => Real.sqrt (3 * ts n / c' n)) p (nhds xiStar) := by
    have h1 : Tendsto (fun n => Real.sqrt (xiStar ^ 2 + 3 * ((ts n - xiBar * c' n) /
        (c' n) ^ (1 / 3 : ℝ)) * tipEps (c' n))) p (nhds (Real.sqrt (xiStar ^ 2))) :=
      (Real.continuous_sqrt.tendsto _).comp hr
    rw [Real.sqrt_sq xiStar_pos.le] at h1
    refine h1.congr' ?_
    filter_upwards [hc'.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
    rw [three_mul_div_eq hn]
  have hpos : ∀ᶠ n in p, 0 < xiStar ^ 2 + 3 * ((ts n - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ)) *
      tipEps (c' n) := hr.eventually (eventually_gt_nhds (by have := xiStar_pos; positivity))
  have hlim : Tendsto (fun n => 3 * ((ts n - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ)) /
      (Real.sqrt (3 * ts n / c' n) + xiStar)) p (nhds (3 * A / (xiStar + xiStar))) :=
    (hts.const_mul 3).div (hx.add tendsto_const_nhds) (by have := xiStar_pos; positivity)
  rw [show xiStar + xiStar = 2 * xiStar by ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [hc'.eventually (eventually_gt_atTop (0 : ℝ)), hpos] with n hn hrn
  have hε := tipEps_pos hn
  have hsq : Real.sqrt (3 * ts n / c' n) ^ 2 = xiStar ^ 2 + 3 * ((ts n - xiBar * c' n) /
      (c' n) ^ (1 / 3 : ℝ)) * tipEps (c' n) := by
    rw [Real.sq_sqrt (by rw [three_mul_div_eq hn]; exact hrn.le), three_mul_div_eq hn]
  have hxpos : 0 < Real.sqrt (3 * ts n / c' n) + xiStar := by
    have := xiStar_pos; positivity
  unfold pinPoint
  rw [div_eq_div_iff hxpos.ne' hε.ne']
  nlinarith [hsq]

lemma pinPoint_nonneg_rescale (prob : FixedWeightProblem) {c' ts T : ℝ} {g : ℝ → ℝ}
    (hc'0 : 0 < c') (hsh : prob.totalShift ≤ c' / 12) (hwf : prob.IsWeaklyFeasible (c' / 12) T g)
    (hts : 0 ≤ ts) (hg : 0 ≤ g ts) :
    0 ≤ (tipRescaleW prob c' g ((pinPoint c' ts : ℝ) : ℂ)).re := by
  have hε : 0 < tipEps c' := tipEps_pos hc'0
  have hb : tipBReal c' (pinPoint c' ts) = Real.sqrt (3 * ts / c') := by
    unfold tipBReal pinPoint
    field_simp
    ring
  have ht : tipTReal c' (pinPoint c' ts) = ts := by
    unfold tipTReal
    rw [hb, Real.sq_sqrt (by positivity)]
    field_simp
  have hM := cardyNorm_pos_of_nonzero_general prob hsh hwf.1 hwf.2.1
  rw [tipRescaleW_real_on_real hc'0 hwf.1, Complex.ofReal_re, ht, hb]
  exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hε.le (by positivity))
    (Real.sqrt_nonneg _)) (prob.cardyV_nonneg hsh hts)) hg) hM.le

/-- The pinned family satisfies the hypotheses of the abstract two-level theorems. -/
lemma concrete_pin_data (prob : FixedWeightProblem)
    {ι : Type*} {p : Filter ι} {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (g : ι → ℝ → ℝ)
    (hg : ∀ᶠ n in p, ∃ T : ℝ, prob.IsWeaklyFeasible (c' n / 12) T (g n))
    {A₁ : ℝ} (hA₁ : A₁ < Aopt) (tstar : ι → ℝ)
    (hts : Tendsto (fun n => (tstar n - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ)) p (nhds A₁))
    (hpin : ∀ᶠ n in p, 0 ≤ g n (tstar n)) :
    airyZero 1 < -A₁ / cStar ∧
    Tendsto (fun n => pinPoint (c' n) (tstar n)) p (nhds (-(-A₁ / cStar) / betaTip)) ∧
    ∀ᶠ n in p, 0 ≤ ((blowupFamilyPackage_of_concrete_tests_general prob hc' g hg).Φ n
      ((pinPoint (c' n) (tstar n) : ℝ) : ℂ)).re := by
  refine ⟨mem_gap_one_of_lt_Aopt hA₁, ?_, ?_⟩
  · have h := tendsto_pinPoint hc' hts
    have hlim : 3 * A₁ / (2 * xiStar) = -(-A₁ / cStar) / betaTip := by
      unfold cStar
      field_simp [betaTip_pos.ne', xiStar_pos.ne']
    rwa [hlim] at h
  · have hpos : ∀ᶠ n in p, 0 < xiStar ^ 2 + 3 * ((tstar n - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ)) *
        tipEps (c' n) := by
      have he : Tendsto (fun n => tipEps (c' n)) p (nhds 0) :=
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc'
      have hr : Tendsto (fun n => xiStar ^ 2 + 3 * ((tstar n - xiBar * c' n) /
          (c' n) ^ (1 / 3 : ℝ)) * tipEps (c' n)) p (nhds (xiStar ^ 2)) := by
        simpa using tendsto_const_nhds.add ((hts.const_mul 3).mul he)
      exact hr.eventually (eventually_gt_nhds (by have := xiStar_pos; positivity))
    filter_upwards [hc'.eventually (eventually_ge_atTop (max 1 (24 * prob.totalShift))), hg, hpin,
      hpos] with n hc'n ⟨T, hwf⟩ hgn hrn
    have hc'0 : 0 < c' n := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans hc'n)
    have hsh : prob.totalShift ≤ c' n / 12 := by
      have := (le_max_right 1 _).trans hc'n
      linarith [prob.totalShift_nonneg]
    have hts0 : 0 ≤ tstar n := by
      have h3 : 0 < 3 * tstar n / c' n := by rw [three_mul_div_eq hc'0]; exact hrn
      have := (div_pos_iff_of_pos_right hc'0).mp h3
      linarith
    exact pinPoint_nonneg_rescale prob hc'0 hsh hwf hts0 hgn

/-- **Theorem 2.1** (`virasoro_two_level.tex`, `gt:2.1`), eventual form: for every `ε > 0`,
eventually `A_2^*(A₁) - ε ≤ (τ_j - ξ̄ c_j')/c_j'^{1/3}`. -/
theorem concrete_two_level_eventually (prob : FixedWeightProblem)
    {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (g : ι → ℝ → ℝ)
    (hg : ∀ᶠ n in p, ∃ T : ℝ, prob.IsWeaklyFeasible (c' n / 12) T (g n))
    {A₁ : ℝ} (hA₁ : A₁ < Aopt) (tstar : ι → ℝ)
    (hts : Tendsto (fun n => (tstar n - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ)) p (nhds A₁))
    (hpin : ∀ᶠ n in p, 0 ≤ g n (tstar n)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in p, A2star A₁ - ε ≤ (leastThreshold (g n) - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ) := by
  obtain ⟨hu₁, hσ, hpin'⟩ := concrete_pin_data prob hc' g hg hA₁ tstar hts hpin
  exact twoLevel_eventually (blowupFamilyPackage_of_concrete_tests_general prob hc' g hg) hu₁ hσ
    hpin' ε hε

/-- **Theorem 2.1** (`virasoro_two_level.tex`, `gt:2.1`): with the first level pinned
(`g_j(t_*) ≥ 0` at `t_* = ξ̄ c' + A₁ c'^{1/3} + o(c'^{1/3})`, `A₁ < A_opt`), every weakly feasible
family has `A_2^*(A₁) ≤ liminf (τ_j - ξ̄ c_j')/c_j'^{1/3}`, where `τ_j = leastThreshold g_j` and
`A_2^*(A₁) = c_* |z₂(α(-A₁/c_*))|` (`A2star`). -/
theorem concrete_two_level_theorem (prob : FixedWeightProblem)
    {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (g : ι → ℝ → ℝ)
    (hg : ∀ᶠ n in p, ∃ T : ℝ, prob.IsWeaklyFeasible (c' n / 12) T (g n))
    {A₁ : ℝ} (hA₁ : A₁ < Aopt) (tstar : ι → ℝ)
    (hts : Tendsto (fun n => (tstar n - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ)) p (nhds A₁))
    (hpin : ∀ᶠ n in p, 0 ≤ g n (tstar n)) :
    (A2star A₁ : EReal) ≤
      Filter.liminf (fun n =>
        (((leastThreshold (g n) - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ) : ℝ) : EReal)) p := by
  obtain ⟨hu₁, hσ, hpin'⟩ := concrete_pin_data prob hc' g hg hA₁ tstar hts hpin
  exact twoLevel_liminf (blowupFamilyPackage_of_concrete_tests_general prob hc' g hg) hu₁ hσ hpin'

/-- **Theorem 2.1, equality case** (`virasoro_two_level.tex`, `gt:2.1`): if moreover
`(τ_j - ξ̄ c_j')/c_j'^{1/3} → A_2^*(A₁)` along `p`, then `Φ_j → c · g_α(-β ·)` locally uniformly and
in `L¹` (`α = α(-A₁/c_*)`, `c > 0` fixed by `‖c · g_α(-β ·)‖₁ = 1`), `s₁ → -z₂/β`, `γ → 0`. -/
theorem concrete_two_level_equality (prob : FixedWeightProblem)
    {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (g : ι → ℝ → ℝ)
    (hg : ∀ᶠ n in p, ∃ T : ℝ, prob.IsWeaklyFeasible (c' n / 12) T (g n))
    {A₁ : ℝ} (hA₁ : A₁ < Aopt) (tstar : ι → ℝ)
    (hts : Tendsto (fun n => (tstar n - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ)) p (nhds A₁))
    (hpin : ∀ᶠ n in p, 0 ≤ g n (tstar n))
    (hEq : Tendsto (fun n => (leastThreshold (g n) - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ)) p
      (nhds (A2star A₁))) :
    let R := rigidityFamilyPackage_of_concrete_tests_general prob hc' g hg
    let α := clarkAngle (-A₁ / cStar)
    ∃ c : ℝ, 0 < c ∧ (∫ s : ℝ, ‖clarkProfile α c (s : ℂ)‖ = 1) ∧
      Tendsto R.s₁ p (nhds (-clarkNode α 2 / betaTip)) ∧
      TendstoLocallyUniformlyOn R.Φ (clarkProfile α c) p univ ∧
      Tendsto R.γ p (nhds 0) ∧
      Tendsto (fun n => ∫ s : ℝ, ‖phiExt R n s - clarkProfile α c (s : ℂ)‖) p (nhds 0) ∧
      Tendsto (fun n => ∫ s in Ioi (-xiStar * (R.c' n) ^ (2 / 3 : ℝ)),
        ‖R.Φ n (s : ℂ) - clarkProfile α c (s : ℂ)‖) p (nhds 0) := by
  obtain ⟨hu₁, hσ, hpin'⟩ := concrete_pin_data prob hc' g hg hA₁ tstar hts hpin
  exact twoLevel_rigidity (rigidityFamilyPackage_of_concrete_tests_general prob hc' g hg) hu₁ hσ
    hpin' hEq

/-- **Theorem 2.1, equality along a subsequence** (`virasoro_two_level.tex`, `gt:2.1`): the instance
`ι = ℕ`, `p = atTop` of `concrete_two_level_equality` for a subsequence `ns → p` along which
`(τ_j - ξ̄ c_j')/c_j'^{1/3} → A_2^*(A₁)`. -/
theorem concrete_two_level_equality_subseq (prob : FixedWeightProblem)
    {ι : Type*} {p : Filter ι}
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (g : ι → ℝ → ℝ)
    (hg : ∀ᶠ n in p, ∃ T : ℝ, prob.IsWeaklyFeasible (c' n / 12) T (g n))
    {A₁ : ℝ} (hA₁ : A₁ < Aopt) (tstar : ι → ℝ)
    (hts : Tendsto (fun n => (tstar n - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ)) p (nhds A₁))
    (hpin : ∀ᶠ n in p, 0 ≤ g n (tstar n))
    (ns : ℕ → ι) (hns : Tendsto ns atTop p)
    (hEq : Tendsto (fun k => (leastThreshold (g (ns k)) - xiBar * c' (ns k)) /
      (c' (ns k)) ^ (1 / 3 : ℝ)) atTop (nhds (A2star A₁))) :
    ∃ c : ℝ, 0 < c ∧
      (∫ s : ℝ, ‖clarkProfile (clarkAngle (-A₁ / cStar)) c (s : ℂ)‖ = 1) ∧
      TendstoLocallyUniformlyOn (fun k => tipRescaleW prob (c' (ns k)) (g (ns k)))
        (clarkProfile (clarkAngle (-A₁ / cStar)) c) atTop univ ∧
      Tendsto (fun k => ∫ s in Ioi (-xiStar * (c' (ns k)) ^ (2 / 3 : ℝ)),
        ‖tipRescaleW prob (c' (ns k)) (g (ns k)) (s : ℂ) -
          clarkProfile (clarkAngle (-A₁ / cStar)) c (s : ℂ)‖) atTop (nhds 0) := by
  obtain ⟨c, hc, hn, -, hΦ, -, -, hL1⟩ := concrete_two_level_equality prob (hc'.comp hns)
    (fun k => g (ns k)) (hns.eventually hg) hA₁ (fun k => tstar (ns k)) (hts.comp hns)
    (hns.eventually hpin) hEq
  exact ⟨c, hc, hn, hΦ, hL1⟩

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.concrete_two_level_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms concrete_two_level_theorem

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.concrete_two_level_eventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms concrete_two_level_eventually

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.concrete_two_level_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms concrete_two_level_equality

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.concrete_two_level_equality_subseq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms concrete_two_level_equality_subseq

end FormalResearch.ModularBootstrap.TwoLevel
