module

public import FormalResearch.ModularBootstrap.TwoLevel.SoftEdgeCrossingCorollary
public import FormalResearch.ModularBootstrap.TwoLevel.SoftEdgeA2StarLipschitz

/-!
# Offset form of Corollary SE.8 (`se:3.3` in `soft_edge_two_level_stability.tex`)

Proves the `L_J (e_n)_-` offset form of `se:3.3` via `se_crossing_corollary` and
`A2star_lipschitzOn`:

* `se_crossing_corollary_offset`: for any compact `J ⊆ (-∞, A_opt)`, there exist `n_J, D_J, L_J`
  with `0 ≤ L_J` such that for `n ≥ n_J`, `A₁ ∈ J`, and any offset `e : ℝ` whose shifted parameter
  `A_{1,n} := A₁ + e * n^{-1/3}` stays in `J`, writing `t₁ = levelTime A₁ n + e`, for every
  `T ≤ levelTime (A2star A₁) n - D_J - L_J * max (-e) 0` there is an admissible crossing measure
  supported in `{t₁} ∪ [T, ∞)` with strictly positive mass at `t₁`.
* `se_crossing_corollary_offset_bounded`: removing the hypothesis `A_{1,n} ∈ J` whenever
  `|e| ≤ R_off`, by passing to an enlarged compact interval inside `(-∞, A_opt)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality

/-- **Corollary SE.8, offset form (`se:3.3`)**: when `t₁ = levelTime A₁ n + e` with `A₁ ∈ J` and
`A₁ + e * n^{-1/3} ∈ J`, any `T ≤ levelTime (A2star A₁) n - D_J - L_J * max (-e) 0` admits a
positive crossing measure on `{t₁} ∪ [T, ∞)` with `ν {t₁} > 0`. -/
theorem se_crossing_corollary_offset (prob : FixedWeightProblem) {J : Set ℝ} (hJ : IsCompact J)
    (hJsub : J ⊆ Iio Aopt) :
    ∃ n_J D_J L_J : ℝ, 0 < n_J ∧ 0 ≤ L_J ∧
      ∀ n : ℝ, n_J ≤ n → ∀ A₁ ∈ J, ∀ e : ℝ, A₁ + e * n ^ (-(1 / 3 : ℝ)) ∈ J →
        let t₁ := levelTime A₁ n + e
        ∀ T : ℝ, T ≤ levelTime (A2star A₁) n - D_J - L_J * max (-e) 0 →
          ∃ meas : AdmissibleCrossingMeasure prob (n / 12),
            meas.ν ({t₁} ∪ Ici T)ᶜ = 0 ∧ 0 < meas.ν {t₁} ∧
            Integrable (wStar (n / 12) (1 / 2)) meas.ν ∧
            ∫ t, wStar (n / 12) (1 / 2) t ∂meas.ν ≤ FixedWeight.dualC0 prob (n / 12) (1 / 2) := by
  obtain ⟨n₀, D_J, hcor⟩ := se_crossing_corollary prob hJ hJsub
  obtain ⟨L_J, hLJ_nn, hLip⟩ := A2star_lipschitzOn hJ hJsub
  refine ⟨max n₀ 1, D_J, L_J, lt_of_lt_of_le zero_lt_one (le_max_right _ _), hLJ_nn,
    fun n hn A₁ hA₁ e hA₁n T hT => ?_⟩
  have hn_pos : 0 < n := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hn)
  have hn₀ : n₀ ≤ n := (le_max_left _ _).trans hn
  let A₁n : ℝ := A₁ + e * n ^ (-(1 / 3 : ℝ))
  have ht₁_eq : levelTime A₁n n = levelTime A₁ n + e := by
    have hprod : n ^ (-(1 / 3 : ℝ)) * n ^ ((1 : ℝ) / 3) = 1 := by
      rw [← Real.rpow_add hn_pos]; norm_num
    dsimp [levelTime, A₁n]
    calc xiBar * n + (A₁ + e * n ^ (-(1 / 3 : ℝ))) * n ^ ((1 : ℝ) / 3)
        = xiBar * n + A₁ * n ^ ((1 : ℝ) / 3) +
            e * (n ^ (-(1 / 3 : ℝ)) * n ^ ((1 : ℝ) / 3)) := by ring
      _ = xiBar * n + A₁ * n ^ ((1 : ℝ) / 3) + e := by rw [hprod, mul_one]
  have hT_adj : T ≤ levelTime (A2star A₁n) n - D_J := by
    have hnp : 0 < n ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hn_pos _
    have hA_diff : A2star A₁ - A2star A₁n ≤ L_J * max (-e) 0 * n ^ (-(1 / 3 : ℝ)) := by
      rcases le_total 0 e with he | he
      · have hle : A₁ ≤ A₁n := by
          dsimp [A₁n]
          linarith [mul_nonneg he (Real.rpow_nonneg hn_pos.le (-(1 / 3 : ℝ)))]
        have hm : A2star A₁ ≤ A2star A₁n :=
          (A2star_strictMonoOn.le_iff_le (hJsub hA₁) (hJsub hA₁n)).2 hle
        have h_rhs : 0 ≤ L_J * max (-e) 0 * n ^ (-(1 / 3 : ℝ)) := by
          exact mul_nonneg (mul_nonneg hLJ_nn (le_max_right _ _)) (Real.rpow_nonneg hn_pos.le _)
        linarith
      · have h1 : A2star A₁ - A2star A₁n ≤ |A2star A₁ - A2star A₁n| := le_abs_self _
        have h2 := hLip A₁ hA₁ A₁n hA₁n
        have h3 : |A₁ - A₁n| = (-e) * n ^ (-(1 / 3 : ℝ)) := by
          have heq : A₁ - A₁n = -(e * n ^ (-(1 / 3 : ℝ))) := by dsimp [A₁n]; ring
          rw [heq, abs_neg, abs_mul, abs_of_nonpos he,
            abs_of_pos (Real.rpow_pos_of_pos hn_pos _)]
        have h4 : max (-e) 0 = -e := max_eq_left (neg_nonneg.mpr he)
        rw [h3, ← mul_assoc] at h2
        rw [h4]; linarith only [h1, h2]
    have h_lvl : levelTime (A2star A₁) n - L_J * max (-e) 0 ≤ levelTime (A2star A₁n) n := by
      have hm := mul_le_mul_of_nonneg_right hA_diff hnp.le
      have hprod : n ^ (-(1 / 3 : ℝ)) * n ^ ((1 : ℝ) / 3) = 1 := by
        rw [← Real.rpow_add hn_pos]; norm_num
      have h_rhs : L_J * max (-e) 0 * n ^ (-(1 / 3 : ℝ)) * n ^ ((1 : ℝ) / 3) = L_J * max (-e) 0 := by
        calc L_J * max (-e) 0 * n ^ (-(1 / 3 : ℝ)) * n ^ ((1 : ℝ) / 3)
            = L_J * max (-e) 0 * (n ^ (-(1 / 3 : ℝ)) * n ^ ((1 : ℝ) / 3)) := by ring
          _ = L_J * max (-e) 0 := by rw [hprod, mul_one]
      rw [h_rhs, sub_mul] at hm
      dsimp [levelTime]
      linarith
    linarith
  simpa [ht₁_eq] using hcor n hn₀ A₁n hA₁n T hT_adj

/-- **Corollary SE.8, bounded-offset form (`se:3.3`)**: for compact `J ⊆ (-∞, A_opt)` and
`R_off ≥ 0`, no separate membership check for `A₁ + e * n^{-1/3}` is needed once `|e| ≤ R_off`. -/
theorem se_crossing_corollary_offset_bounded (prob : FixedWeightProblem) {R_off : ℝ}
    (hR : 0 ≤ R_off) {J : Set ℝ} (hJ : IsCompact J) (hJsub : J ⊆ Iio Aopt) :
    ∃ n_J D_J L_J : ℝ, 0 < n_J ∧ 0 ≤ L_J ∧
      ∀ n : ℝ, n_J ≤ n → ∀ A₁ ∈ J, ∀ e : ℝ, |e| ≤ R_off →
        let t₁ := levelTime A₁ n + e
        ∀ T : ℝ, T ≤ levelTime (A2star A₁) n - D_J - L_J * max (-e) 0 →
          ∃ meas : AdmissibleCrossingMeasure prob (n / 12),
            meas.ν ({t₁} ∪ Ici T)ᶜ = 0 ∧ 0 < meas.ν {t₁} ∧
            Integrable (wStar (n / 12) (1 / 2)) meas.ν ∧
            ∫ t, wStar (n / 12) (1 / 2) t ∂meas.ν ≤ FixedWeight.dualC0 prob (n / 12) (1 / 2) := by
  rcases J.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 0, 0, zero_lt_one, le_rfl, fun _ _ A₁ hA₁ => absurd hA₁ (Set.notMem_empty A₁)⟩
  obtain ⟨hi, hhiJ, hhi⟩ := hJ.exists_isMaxOn hne continuous_id.continuousOn
  obtain ⟨lo, _, hlo⟩ := hJ.exists_isMinOn hne continuous_id.continuousOn
  let δ : ℝ := (Aopt - hi) / 2
  have hδ_pos : 0 < δ := half_pos (sub_pos.mpr (hJsub hhiJ))
  let J' : Set ℝ := Icc (lo - 1) (hi + δ)
  have hJ' : IsCompact J' := isCompact_Icc
  have hJ'sub : J' ⊆ Iio Aopt := fun x hx => by
    have hiA : hi < Aopt := hJsub hhiJ
    have hlt : hi + δ < Aopt := by dsimp [δ]; linarith only [hiA]
    exact lt_of_le_of_lt hx.2 hlt
  obtain ⟨n₀, D_J, L_J, hn₀_pos, hLJ_nn, hcor⟩ :=
    se_crossing_corollary_offset prob hJ' hJ'sub
  let m₀ : ℝ := min 1 δ
  have hm₀_pos : 0 < m₀ := lt_min zero_lt_one hδ_pos
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).eventually_le_const
      (show (0 : ℝ) < m₀ / (R_off + 1) by positivity))
  refine ⟨max n₀ (max n₁ 1), D_J, L_J, lt_of_lt_of_le hn₀_pos (le_max_left _ _), hLJ_nn,
    fun n hn A₁ hA₁ e he T hT => ?_⟩
  have hn_pos : 0 < n := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hn₀ : n₀ ≤ n := (le_max_left _ _).trans hn
  have hn₁' : n₁ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hstep : |e * n ^ (-(1 / 3 : ℝ))| ≤ m₀ := by
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hn_pos _)]
    have h1 := hn₁ n hn₁'
    have h2 : |e| * n ^ (-(1 / 3 : ℝ)) ≤ R_off * (m₀ / (R_off + 1)) :=
      mul_le_mul he h1 (Real.rpow_nonneg hn_pos.le _) hR
    have h3 : R_off * (m₀ / (R_off + 1)) = (R_off / (R_off + 1)) * m₀ := by ring
    have h4 : R_off / (R_off + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
    nlinarith
  have hloA : lo ≤ A₁ := hlo hA₁
  have hhiA : A₁ ≤ hi := hhi hA₁
  have hA₁_mem' : A₁ ∈ J' := ⟨by linarith, by linarith⟩
  have hA₁n_mem' : A₁ + e * n ^ (-(1 / 3 : ℝ)) ∈ J' := by
    obtain ⟨h_neg, h_pos⟩ := abs_le.mp hstep
    have hm1 : m₀ ≤ 1 := min_le_left _ _
    have hmδ : m₀ ≤ δ := min_le_right _ _
    exact ⟨by linarith, by linarith⟩
  exact hcor n hn₀ A₁ hA₁_mem' e hA₁n_mem' T hT

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.se_crossing_corollary_offset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms se_crossing_corollary_offset

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.se_crossing_corollary_offset_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms se_crossing_corollary_offset_bounded

end FormalResearch.ModularBootstrap.TwoLevel
