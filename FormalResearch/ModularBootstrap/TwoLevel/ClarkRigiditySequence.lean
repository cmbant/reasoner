module

public import FormalResearch.ModularBootstrap.TwoLevel.ExclusionChart
public import FormalResearch.ModularBootstrap.Upper.Rigidity.Wiring

/-!
# Two-level crossing sequences (setting of Theorem 2.6, `virasoro_two_level.tex`, `gt:2.6`)

* `TwoLevelSequence prob A₁`: admissible crossing measures `ν_j` at `c_j → ∞` with support in
  `{t₁^{(j)}} ∪ [τ_j, ∞)`, `t₁^{(j)} = ξ̄ c_j + A₁ c_j^{1/3} + o(c_j^{1/3})`,
  `τ_j ≥ ξ̄ c_j + (A₂*(A₁) - o(1)) c_j^{1/3}` (`lowest`: `ν_j` vanishes below `t₁^{(j)}`).
* `TwoLevelSequence.toCrossingSequence`: it is a `CrossingSequence` with gap `t₁^{(j)}`, so Property `sr:P`
  (`designPropertyP_prob`, `displacedPropertyP_prob`) and `designPropertyP_twoZero` apply to its spectral measures
  `μ_j = S.μS j`.
* `spectral_gap_null`: `μ_j` vanishes on `(u(τ_j), u(t₁^{(j)}))`, hence lives on
  `{s₁^{(j)}} ∪ (-∞, s₂^{(j)}]` with `s₁^{(j)} = u(t₁^{(j)}) → u₁ = -A₁/c_*` (`tendsto_uAiry_t₁`) and
  `s₂^{(j)} = u(τ_j)`, `s₂^{(j)} ≤ z₂ + ε` eventually, `z₂ = -A₂*(A₁)/c_*` (`eventually_uAiry_τ_le`).

All results are proved unconditionally.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.Duality
open FormalResearch.ModularBootstrap.Upper.Rigidity

/-- Crossing measures with support in `{t₁} ∪ [τ, ∞)` at `c_j → ∞` (setting of `gt:2.6`). -/
structure TwoLevelSequence (prob : FixedWeightProblem) (A₁ : ℝ) where
  c : ℕ → ℝ
  meas : ∀ j, AdmissibleCrossingMeasure prob (c j / 12)
  t₁ : ℕ → ℝ
  τ : ℕ → ℝ
  tendsto_c : Tendsto c atTop atTop
  c_pos : ∀ j, 0 < c j
  shift_le : ∀ j, prob.totalShift ≤ c j / 12
  t₁_pos : ∀ j, 0 < t₁ j
  lowest : ∀ j, (meas j).ν (Iio (t₁ j)) = 0
  supp : ∀ j, (meas j).ν ({t₁ j} ∪ Ici (τ j))ᶜ = 0
  t₁_asymp : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, |t₁ j - levelTime A₁ (c j)| ≤ ε * (c j) ^ ((1 : ℝ) / 3)
  τ_lower : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, levelTime (A2star A₁ - ε) (c j) ≤ τ j

namespace TwoLevelSequence

variable {prob : FixedWeightProblem} {A₁ : ℝ} (S : TwoLevelSequence prob A₁)

/-- The two-level sequence as a `CrossingSequence` with gap `t₁^{(j)}`. -/
def toCrossingSequence : CrossingSequence prob where
  c := S.c
  τ := S.t₁
  meas := S.meas
  tendsto_c := S.tendsto_c
  c_pos := S.c_pos
  shift_le := S.shift_le
  τ_pos := S.t₁_pos
  atGap := S.lowest

/-- The spectral measures `μ_j`. -/
noncomputable def μ (j : ℕ) : Measure ℝ := S.toCrossingSequence.μS j

instance (j : ℕ) : IsLocallyFiniteMeasure (S.μ j) := S.toCrossingSequence.isLocallyFinite j

/-- `μ_j` lives on `u ≤ u(t₁^{(j)})`. -/
lemma μ_Ioi_null (j : ℕ) : S.μ j (Ioi (uAiry (S.c j) (S.t₁ j))) = 0 :=
  S.toCrossingSequence.supp j

/-- **The gap of the support**: `μ_j` vanishes on `(u(τ_j), u(t₁^{(j)}))`. -/
theorem spectral_gap_null (j : ℕ) :
    S.μ j (Ioo (uAiry (S.c j) (S.τ j)) (uAiry (S.c j) (S.t₁ j))) = 0 := by
  have hc := S.c_pos j
  unfold μ CrossingSequence.μS spectralMeasure
  change ((((S.meas j).ν.restrict (Ioi 0)).withDensity (spectralDensity prob (S.c j))).map
    (uAiry (S.c j))) _ = 0
  rw [Measure.map_apply (continuous_uAiry _).measurable measurableSet_Ioo]
  refine withDensity_absolutelyContinuous _ _ ?_
  have hsub : uAiry (S.c j) ⁻¹' Ioo (uAiry (S.c j) (S.τ j)) (uAiry (S.c j) (S.t₁ j)) ⊆
      ({S.t₁ j} ∪ Ici (S.τ j))ᶜ := fun t ht => by
    obtain ⟨h1, h2⟩ := ht
    have ha : S.t₁ j < t := by
      by_contra h
      exact absurd (uAiry_antitone hc (not_lt.1 h)) (not_le.2 h2)
    have hb : t < S.τ j := by
      by_contra h
      exact absurd (uAiry_antitone hc (not_lt.1 h)) (not_le.2 h1)
    rintro (h | h)
    · exact ha.ne' h
    · exact absurd (mem_Ici.1 h) (not_le.2 hb)
  refine le_antisymm ?_ bot_le
  calc ((S.meas j).ν.restrict (Ioi 0)) _ ≤ (S.meas j).ν _ := Measure.restrict_le_self _
    _ ≤ (S.meas j).ν ({S.t₁ j} ∪ Ici (S.τ j))ᶜ := measure_mono hsub
    _ = 0 := S.supp j

/-- `s₁^{(j)} = u(t₁^{(j)}) → u₁ = -A₁/c_*`. -/
theorem tendsto_uAiry_t₁ : Tendsto (fun j => uAiry (S.c j) (S.t₁ j)) atTop (𝓝 (-A₁ / cStar)) := by
  have hcs := cStar_pos
  rw [tendsto_order]
  constructor
  · intro a ha
    set ε : ℝ := (-A₁ / cStar - a) * cStar / 2 with hε
    have hε0 : 0 < ε := by
      have : 0 < -A₁ / cStar - a := by linarith
      positivity
    have hlim := (tendsto_uAiry_levelTime (A₁ + ε)).comp S.tendsto_c
    have h1 : ∀ᶠ j in atTop, a < uAiry (S.c j) (levelTime (A₁ + ε) (S.c j)) := by
      refine hlim.eventually (lt_mem_nhds ?_)
      have : -(A₁ + ε) / cStar = -A₁ / cStar - ε / cStar := by field_simp; ring
      rw [this, hε]
      have : (-A₁ / cStar - a) * cStar / 2 / cStar = (-A₁ / cStar - a) / 2 := by field_simp
      rw [this]; linarith
    have h2 := S.t₁_asymp (ε / 2) (by positivity)
    filter_upwards [h1, h2, S.tendsto_c.eventually_gt_atTop 0] with j hj1 hj2 hc0
    have hp : 0 < (S.c j) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc0 _
    have hle : S.t₁ j ≤ levelTime (A₁ + ε) (S.c j) := by
      have := (abs_le.1 hj2).2
      have e : levelTime (A₁ + ε) (S.c j) - levelTime A₁ (S.c j) = ε * (S.c j) ^ ((1 : ℝ) / 3) := by
        rw [levelTime_sub]; ring
      nlinarith
    exact lt_of_lt_of_le hj1 (uAiry_antitone hc0 hle)
  · intro b hb
    set ε : ℝ := (b - -A₁ / cStar) * cStar / 2 with hε
    have hε0 : 0 < ε := by
      have : 0 < b - -A₁ / cStar := by linarith
      positivity
    have hlim := (tendsto_uAiry_levelTime (A₁ - ε)).comp S.tendsto_c
    have h1 : ∀ᶠ j in atTop, uAiry (S.c j) (levelTime (A₁ - ε) (S.c j)) < b := by
      refine hlim.eventually (gt_mem_nhds ?_)
      have : -(A₁ - ε) / cStar = -A₁ / cStar + ε / cStar := by field_simp; ring
      rw [this, hε]
      have : (b - -A₁ / cStar) * cStar / 2 / cStar = (b - -A₁ / cStar) / 2 := by field_simp
      rw [this]; linarith
    have h2 := S.t₁_asymp (ε / 2) (by positivity)
    filter_upwards [h1, h2, S.tendsto_c.eventually_gt_atTop 0] with j hj1 hj2 hc0
    have hp : 0 < (S.c j) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc0 _
    have hle : levelTime (A₁ - ε) (S.c j) ≤ S.t₁ j := by
      have := (abs_le.1 hj2).1
      have e : levelTime A₁ (S.c j) - levelTime (A₁ - ε) (S.c j) = ε * (S.c j) ^ ((1 : ℝ) / 3) := by
        rw [levelTime_sub]; ring
      nlinarith
    exact lt_of_le_of_lt (uAiry_antitone hc0 hle) hj1

/-- `u(τ_j) ≤ z₂ + ε` eventually, `z₂ = -A₂*(A₁)/c_*`. -/
theorem eventually_uAiry_τ_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, uAiry (S.c j) (S.τ j) ≤ -A2star A₁ / cStar + ε := by
  have hcs := cStar_pos
  set δ : ℝ := ε * cStar / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hlim := (tendsto_uAiry_levelTime (A2star A₁ - δ)).comp S.tendsto_c
  have h1 : ∀ᶠ j in atTop, uAiry (S.c j) (levelTime (A2star A₁ - δ) (S.c j)) <
      -A2star A₁ / cStar + ε := by
    refine hlim.eventually (gt_mem_nhds ?_)
    have : -(A2star A₁ - δ) / cStar = -A2star A₁ / cStar + δ / cStar := by field_simp; ring
    rw [this, hδ]
    have : ε * cStar / 2 / cStar = ε / 2 := by field_simp
    rw [this]; linarith
  filter_upwards [h1, S.τ_lower δ hδ0, S.tendsto_c.eventually_gt_atTop 0] with j hj1 hj2 hc0
  exact (uAiry_antitone hc0 hj2).trans hj1.le

end TwoLevelSequence

/-- `A₂*(A₁) = -c_* z₂(α(-A₁/c_*))`. -/
lemma A2star_eq_neg_cStar_mul {A₁ : ℝ} (hA : A₁ < Aopt) :
    A2star A₁ = -(cStar * clarkNode (clarkAngle (-A₁ / cStar)) 2) := by
  have hz : clarkNode (clarkAngle (-A₁ / cStar)) 2 < 0 := by
    have := airyZero_two_lt_clarkNode_two (mem_gap_one_of_lt_Aopt hA)
    exact this.2.trans (airyZero_neg 1)
  unfold A2star
  rw [abs_of_neg hz]; ring

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.TwoLevelSequence.tendsto_uAiry_t₁' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoLevelSequence.tendsto_uAiry_t₁

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.TwoLevelSequence.spectral_gap_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoLevelSequence.spectral_gap_null

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.TwoLevelSequence.eventually_uAiry_τ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoLevelSequence.eventually_uAiry_τ_le

end FormalResearch.ModularBootstrap.TwoLevel
