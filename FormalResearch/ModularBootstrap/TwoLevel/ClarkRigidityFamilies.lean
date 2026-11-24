module

public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityAtomic

/-!
# Weights from families of ideal windows (`virasoro_two_level.tex`, `gt:2.6`, Steps 4 and 5)

Abstract node-level statements.  Let `ν` be a locally finite measure carried by the nodes `z_i`, with reference weights
`w_i > 0`, and put `x_i = ν{z_i}/w_i`.  For a family of ideal windows `G_K ≥ 0` on `(-∞, q_K]` with the ideal
inequality `IdealIneq ν B G_K q_K V_K`, node values `τ^K_i = G_K(z_i) w_i` and `Σ_i τ^K_i = V_K`:

* `weight_le_one_of_family`: if `τ^K_j > 0`, `τ^K_i ≥ 0` for `i ≠ j` and `(V_K - τ^K_j)/τ^K_j → 0` then `x_j ≤ 1`;
* `weight_ge_one_of_family`: if all `x_i ≤ 1`, `τ^K_j < 0` and `Σ_i max(τ^K_i, 0)/(-τ^K_j) → 0` then `x_j ≥ 1`.

All results are proved unconditionally.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.ModularBootstrap.Upper.Rigidity

/-- The atomic inequality in the normalised form `Σ_i x_i τ_i ≤ V`. -/
lemma atomic_ineq_normalised {z w : ℕ → ℝ} (hw : ∀ i, 0 < w i) (hz : Tendsto z atTop atBot)
    (hanti : StrictAnti z) {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] (hconc : ν (Set.range z)ᶜ = 0)
    {B : ℝ} (hzB : ∀ i, z i ≤ B) {G : ℝ → ℝ} (hG : Continuous G) {q V : ℝ}
    (hnonneg : ∀ u, u ≤ q → 0 ≤ G u) (hI : IdealIneq ν B G q V) {τ : ℕ → ℝ}
    (hτG : ∀ i, τ i = G (z i) * w i) :
    Summable (fun i => (ν {z i}).toReal / w i * τ i) ∧ ∑' i, (ν {z i}).toReal / w i * τ i ≤ V := by
  obtain ⟨hs, hle⟩ := atomic_ineq_of_ideal hz hanti hconc hzB hG hnonneg hI
  have e : ∀ i, (ν {z i}).toReal / w i * τ i = G (z i) * (ν {z i}).toReal := fun i => by
    rw [hτG i]; field_simp [(hw i).ne']
  simp_rw [e]
  exact ⟨hs, hle⟩

theorem weight_le_one_of_family {z w : ℕ → ℝ} (hw : ∀ i, 0 < w i) (hz : Tendsto z atTop atBot)
    (hanti : StrictAnti z) {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] (hconc : ν (Set.range z)ᶜ = 0)
    {B : ℝ} (hzB : ∀ i, z i ≤ B) {G : ℕ → ℝ → ℝ} (hGc : ∀ K, Continuous (G K)) {q V : ℕ → ℝ}
    (hnonneg : ∀ K u, u ≤ q K → 0 ≤ G K u) (hI : ∀ᶠ K in atTop, IdealIneq ν B (G K) (q K) (V K))
    {τ : ℕ → ℕ → ℝ} (hτ : ∀ᶠ K in atTop, HasSum (τ K) (V K))
    (hτG : ∀ᶠ K in atTop, ∀ i, τ K i = G K (z i) * w i) {j : ℕ}
    (hpos : ∀ᶠ K in atTop, 0 < τ K j) (hnn : ∀ᶠ K in atTop, ∀ i, i ≠ j → 0 ≤ τ K i)
    (hlim : Tendsto (fun K => (V K - τ K j) / τ K j) atTop (𝓝 0)) :
    (ν {z j}).toReal ≤ w j := by
  set x : ℕ → ℝ := fun i => (ν {z i}).toReal / w i with hx
  have hx0 : ∀ i, 0 ≤ x i := fun i => div_nonneg ENNReal.toReal_nonneg (hw i).le
  have hev : ∀ᶠ K in atTop, x j - 1 ≤ (V K - τ K j) / τ K j := by
    filter_upwards [hI, hτ, hτG, hpos, hnn] with K hIK hτK hτGK hposK hnnK
    obtain ⟨hs, hle⟩ := atomic_ineq_normalised hw hz hanti hconc hzB (hGc K) (hnonneg K) hIK hτGK
    have := weight_le_one_of_ratio (x := x) hx0 hτK hs hle hnnK
    rw [le_div_iff₀ hposK]; exact this
  have h1 : x j - 1 ≤ 0 := ge_of_tendsto hlim hev
  have h2 : x j ≤ 1 := by linarith
  have h3 : (ν {z j}).toReal = x j * w j := by rw [hx]; field_simp [(hw j).ne']
  rw [h3]
  nlinarith [hw j]

theorem weight_ge_one_of_family {z w : ℕ → ℝ} (hw : ∀ i, 0 < w i) (hz : Tendsto z atTop atBot)
    (hanti : StrictAnti z) {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] (hconc : ν (Set.range z)ᶜ = 0)
    (hxle : ∀ i, (ν {z i}).toReal ≤ w i) {B : ℝ} (hzB : ∀ i, z i ≤ B) {G : ℕ → ℝ → ℝ}
    (hGc : ∀ K, Continuous (G K)) {q V : ℕ → ℝ} (hnonneg : ∀ K u, u ≤ q K → 0 ≤ G K u)
    (hI : ∀ᶠ K in atTop, IdealIneq ν B (G K) (q K) (V K)) {τ : ℕ → ℕ → ℝ}
    (hτ : ∀ᶠ K in atTop, HasSum (τ K) (V K)) (hτG : ∀ᶠ K in atTop, ∀ i, τ K i = G K (z i) * w i)
    {j : ℕ} (hneg : ∀ᶠ K in atTop, τ K j < 0)
    (hlim : Tendsto (fun K => (∑' i, max (τ K i) 0) / (-τ K j)) atTop (𝓝 0)) :
    w j ≤ (ν {z j}).toReal := by
  set x : ℕ → ℝ := fun i => (ν {z i}).toReal / w i with hx
  have hx0 : ∀ i, 0 ≤ x i ∧ x i ≤ 1 := fun i =>
    ⟨div_nonneg ENNReal.toReal_nonneg (hw i).le, (div_le_one (hw i)).2 (hxle i)⟩
  have hev : ∀ᶠ K in atTop, 1 - x j ≤ (∑' i, max (τ K i) 0) / (-τ K j) := by
    filter_upwards [hI, hτ, hτG, hneg] with K hIK hτK hτGK hnegK
    obtain ⟨hs, hle⟩ := atomic_ineq_normalised hw hz hanti hconc hzB (hGc K) (hnonneg K) hIK hτGK
    have := weight_ge_one_of_ratio (x := x) (j := j) hx0 hτK hs hle
    rw [le_div_iff₀ (by linarith)]; exact this
  have h1 : 1 - x j ≤ 0 := ge_of_tendsto hlim hev
  have h3 : (ν {z j}).toReal = x j * w j := by rw [hx]; field_simp [(hw j).ne']
  rw [h3]
  nlinarith [hw j]

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.weight_le_one_of_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms weight_le_one_of_family

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.weight_ge_one_of_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms weight_ge_one_of_family

end FormalResearch.ModularBootstrap.TwoLevel
