module

public import FormalResearch.ModularBootstrap.Upper.Rigidity.Concentration

/-!
# Theorem `Σ`, Steps 4--6: weights of a limit measure

For a vague limit `ν` carried by the Airy zeros, `x_i = ν{a_i} Ai'(a_i)²` (`atomWeight`):

* `atomic_inequality` (Step 4, `sr:e2`): `Σ_i x_i Π_i ≤ V_𝔇` for every design test;
* `atomWeight_zero_ge` (Step 5, first half): `x_1 ≥ 1` from `Σ₀(b)` (`sigma_zero_b_eventually`);
* `atomWeight_le_one` (Step 5): `x_n ≤ 1` for all `n`;
* `atomWeight_eq_one` (Step 6): `x_n = 1` for all `n` (omitted-site designs).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.Upper.Rigidity

open FormalResearch.Special

/-- **Step 4** (`sr:e2`): `Σ_n x_n Π_n ≤ V_𝔇` for a vague limit carried by `{a_n}`. -/
theorem atomic_inequality (S : SpectralData) (hbd : LocallyBounded S.μ) {𝒰 : Ultrafilter ℕ}
    (h𝒰 : (𝒰 : Filter ℕ) ≤ atTop) {ν : Measure ℝ} [IsLocallyFiniteMeasure ν]
    (hν : IsVagueLimit 𝒰 S.μ ν) (hconc : ν (Set.range airyNode)ᶜ = 0) {D : Window}
    (T : DesignTest S.μ D) : AtomicIneq (atomWeight ν) D := by
  set x := atomWeight ν with hx
  set t : ℕ → ℝ := fun i => x i * D.pi i with ht
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ i, N₀ ≤ i → airyNode i ≤ D.uF :=
    eventually_atTop.1 (tendsto_airyNode.eventually (eventually_le_atBot D.uF))
  have ht_nonneg : ∀ i, N₀ ≤ i → 0 ≤ t i := fun i hi =>
    mul_nonneg (atomWeight_nonneg ν i) (D.pi_nonneg_of_le (hN₀ i hi))
  have hpartial : ∀ N, N₀ ≤ N → ∑ i ∈ Finset.range (N + 1), t i ≤ D.V := by
    intro N hN
    set A : ℝ := min (D.uF - 1) (airyNode N) with hA
    set B : ℝ := airyZero 1 + 1 with hB
    have hI := basic_inequality S hbd h𝒰 hν T (A := A) (B := B) (min_le_left _ _) le_rfl
    have hg : Continuous (fun u => cutoff A B u * D.W u) :=
      (cutoff_continuous A B).mul D.continuous
    have hcsg : HasCompactSupport (fun u => cutoff A B u * D.W u) :=
      HasCompactSupport.mul_cutoff A B
    rw [integral_eq_tsum_atoms hconc hg hcsg] at hI
    have hsum : Summable (fun i => (cutoff A B (airyNode i) * D.W (airyNode i)) *
        (ν {airyNode i}).toReal) := summable_of_cs hcsg _
    have hterm : ∀ i, (cutoff A B (airyNode i) * D.W (airyNode i)) * (ν {airyNode i}).toReal =
        cutoff A B (airyNode i) * t i := by
      intro i
      rw [ht, hx]
      simp only [Window.pi]
      rw [← atomWeight_mul_weight ν i]
      ring
    simp_rw [hterm] at hsum hI
    have hle : ∑ i ∈ Finset.range (N + 1), t i ≤ ∑' i, cutoff A B (airyNode i) * t i := by
      calc ∑ i ∈ Finset.range (N + 1), t i
          = ∑ i ∈ Finset.range (N + 1), cutoff A B (airyNode i) * t i := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have hi' : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            rw [cutoff_eq_one (A := A) (B := B), one_mul]
            · exact (min_le_right _ _).trans (airyNode_strictAnti.antitone hi')
            · exact (airyNode_le_airyNode_zero i).trans (by rw [hB]; linarith)
        _ ≤ ∑' i, cutoff A B (airyNode i) * t i := by
            refine Summable.sum_le_tsum _ (fun i hi => ?_) hsum
            have hi' : N₀ ≤ i := by
              have := Finset.mem_range.not.mp hi
              omega
            exact mul_nonneg (cutoff_nonneg _ _ _) (ht_nonneg i hi')
    exact hle.trans hI
  have hpartial' : ∀ m, ∑ i ∈ Finset.range (N₀ + m), t i ≤ D.V := by
    intro m
    have h1 := hpartial (N₀ + m) (Nat.le_add_right _ _)
    have h2 : ∑ i ∈ Finset.range (N₀ + m), t i ≤ ∑ i ∈ Finset.range (N₀ + m + 1), t i := by
      rw [Finset.sum_range_succ]
      linarith [ht_nonneg (N₀ + m) (Nat.le_add_right _ _)]
    linarith
  have hsum : Summable t := by
    rw [← summable_nat_add_iff N₀]
    refine summable_of_sum_range_le (c := D.V - ∑ i ∈ Finset.range N₀, t i)
      (fun i => ht_nonneg _ (Nat.le_add_left _ _)) (fun m => ?_)
    have := hpartial' m
    rw [Finset.sum_range_add] at this
    have h3 : ∑ i ∈ Finset.range m, t (i + N₀) = ∑ i ∈ Finset.range m, t (N₀ + i) :=
      Finset.sum_congr rfl fun i _ => by rw [add_comm]
    linarith
  refine ⟨hsum, ?_⟩
  refine le_of_tendsto hsum.hasSum.tendsto_sum_nat (eventually_atTop.2 ⟨N₀, fun n hn => ?_⟩)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact hpartial' m

/-- `Σ₀(b)` and concentration give `x_1 ≥ 1` (first half of Step 5). -/
theorem atomWeight_zero_ge (S : SpectralData) {𝒟 : Set Window} (hP : DesignPropertyP S.μ 𝒟)
    (F : SameSiteFamily 𝒟) {𝒰 : Ultrafilter ℕ} (h𝒰 : (𝒰 : Filter ℕ) ≤ atTop)
    {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] (hν : IsVagueLimit 𝒰 S.μ ν)
    (hconc : ν (Set.range airyNode)ᶜ = 0) : 1 ≤ atomWeight ν 0 := by
  have hg := SameSiteFamily.gap1_pos
  have hw0 := airyNodeWeight_pos 0
  set ρ : ℝ := SameSiteFamily.gap1 / 4 with hρ
  have hρ0 : 0 < ρ := by positivity
  set K : Set ℝ := Icc (airyZero 1 - ρ) (airyZero 1 + ρ) with hK
  set U : Set ℝ := Ioo (airyZero 1 - 2 * ρ) (airyZero 1 + 2 * ρ) with hU
  have hKU : K ⊆ U := fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hUsub : U ⊆ {airyNode 0} ∪ (Set.range airyNode)ᶜ := by
    intro u hu
    by_cases hr : u ∈ Set.range airyNode
    · obtain ⟨i, rfl⟩ := hr
      left
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · rfl
      · exfalso
        have h1 : airyNode i ≤ airyNode 1 := airyNode_strictAnti.antitone hi
        have h2 : airyNode 1 = airyNode 0 - SameSiteFamily.gap1 := by
          unfold SameSiteFamily.gap1; ring
        have := hu.1
        rw [← airyNode_zero] at this
        rw [hρ] at this
        linarith
    · exact Or.inr hr
  have hνU : ν U ≤ ν {airyNode 0} := by
    calc ν U ≤ ν ({airyNode 0} ∪ (Set.range airyNode)ᶜ) := measure_mono hUsub
      _ ≤ ν {airyNode 0} + ν (Set.range airyNode)ᶜ := measure_union_le _ _
      _ = ν {airyNode 0} := by rw [hconc, add_zero]
  have hfin : ν {airyNode 0} ≠ ∞ := (measure_singleton_lt_top (μ := ν)).ne
  have key : ∀ b : ℝ, b < airyNodeWeight 0 → b ≤ (ν {airyNode 0}).toReal := by
    intro b hb
    have hev := sigma_zero_b_eventually S hP F hρ0 b hb
    have hev' : ∀ᶠ j in (𝒰 : Filter ℕ), b ≤ (S.μ j K).toReal := by
      refine Filter.Eventually.filter_mono h𝒰 ?_
      filter_upwards [hev] with j hj
      exact (ENNReal.ofReal_le_iff_le_toReal (isCompact_Icc.measure_lt_top.ne)).1 hj
    have := hν.le_measure_of_eventually isCompact_Icc isOpen_Ioo hKU hev'
    have h2 : ENNReal.ofReal b ≤ ν {airyNode 0} := this.trans hνU
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 h2
  have hle : airyNodeWeight 0 ≤ (ν {airyNode 0}).toReal := by
    by_contra hcon
    push Not at hcon
    have := key ((airyNodeWeight 0 + (ν {airyNode 0}).toReal) / 2) (by linarith)
    linarith
  have hx := atomWeight_mul_weight ν 0
  have : airyNodeWeight 0 * 1 ≤ airyNodeWeight 0 * atomWeight ν 0 := by
    rw [mul_one, mul_comm, hx]; exact hle
  exact le_of_mul_le_mul_left this hw0

/-- **Step 5**: `x_n ≤ 1` for every `n` (designs with all `Π_m ≥ 0`). -/
theorem atomWeight_le_one (S : SpectralData) (hbd : LocallyBounded S.μ) {𝒟 : Set Window}
    (hP : DesignPropertyP S.μ 𝒟) (F : SameSiteFamily 𝒟) (Dis : DisplacedFamily 𝒟)
    {𝒰 : Ultrafilter ℕ} (h𝒰 : (𝒰 : Filter ℕ) ≤ atTop) {ν : Measure ℝ}
    [IsLocallyFiniteMeasure ν] (hν : IsVagueLimit 𝒰 S.μ ν)
    (hconc : ν (Set.range airyNode)ᶜ = 0) (n : ℕ) : atomWeight ν n ≤ 1 := by
  have hat : ∀ D ∈ 𝒟, AtomicIneq (atomWeight ν) D := fun D hD =>
    atomic_inequality S hbd h𝒰 hν hconc (hP D hD).some
  have hx0 := atomWeight_zero_ge S hP F h𝒰 hν hconc
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- the first site, from the designs `win k (-κ)`
    have hr := designRadius_pos
    have hr2 := designRadius_lt_two
    set κ : ℝ := designRadius / 2 with hκ
    have hκ0 : 0 < κ := by positivity
    have habs : |-κ| < designRadius := by rw [abs_neg, abs_of_pos hκ0]; linarith
    have hg := SameSiteFamily.gap1_pos
    refine upper_weight (fun i => atomWeight_nonneg ν i) (n := 0) (fun h => absurd rfl h)
      (fun k => F.win k (-κ)) (fun k => hat _ (F.mem k (-κ) habs))
      (fun k i => F.pi_win_neg_nonneg k hκ0.le i) (ω := κ / 2) (by positivity)
      (fun k => ?_) ?_
    · rw [SameSiteFamily.pi_win_zero]
      have := F.Rt_ge k
      nlinarith
    · -- rest sum is squeezed by `(1 + κ/g) E_k`
      have hrest : ∀ k, (∑' i, if i = 0 ∨ i = 0 then (0 : ℝ) else (F.win k (-κ)).pi i) =
          ∑' i, (F.win k (-κ)).pi (i + 1) := by
        intro k
        have hs := summable_ite_ne (F.win k (-κ)).summable_pi 0
        have hs' : Summable fun i => if i = 0 ∨ i = 0 then (0 : ℝ) else (F.win k (-κ)).pi i := by
          simpa using hs
        rw [hs'.tsum_eq_zero_add]
        simp
      refine squeeze_zero (fun k => ?_) (fun k => ?_)
        (by simpa using F.E_small.const_mul (1 + κ / SameSiteFamily.gap1))
      · rw [hrest]; exact tsum_nonneg fun i => F.pi_win_neg_nonneg k hκ0.le (i + 1)
      · rw [hrest]
        have h1 := SameSiteFamily.V_eq F k (-κ)
        have h2 := F.V_le_of_neg k hκ0.le
        linarith
  · refine upper_weight (fun i => atomWeight_nonneg ν i) (n := n) (fun _ => hx0)
      (fun k => Dis.win n k) (fun k => hat _ (Dis.mem n k hn)) (fun k i => Dis.pi_nonneg n k i hn)
      (ω := (Dis.pi_lower n hn).choose) (Dis.pi_lower n hn).choose_spec.1
      (Dis.pi_lower n hn).choose_spec.2 (Dis.rest_small n hn)

/-- **Step 6**: `x_n = 1` for every `n` (omitted-site designs). -/
theorem atomWeight_eq_one (S : SpectralData) (hbd : LocallyBounded S.μ) {𝒟 : Set Window}
    (hP : DesignPropertyP S.μ 𝒟) (F : SameSiteFamily 𝒟) (Dis : DisplacedFamily 𝒟)
    (Om : OmittedFamily 𝒟) {𝒰 : Ultrafilter ℕ} (h𝒰 : (𝒰 : Filter ℕ) ≤ atTop) {ν : Measure ℝ}
    [IsLocallyFiniteMeasure ν] (hν : IsVagueLimit 𝒰 S.μ ν)
    (hconc : ν (Set.range airyNode)ᶜ = 0) (n : ℕ) : atomWeight ν n = 1 := by
  have hat : ∀ D ∈ 𝒟, AtomicIneq (atomWeight ν) D := fun D hD =>
    atomic_inequality S hbd h𝒰 hν hconc (hP D hD).some
  have hle := atomWeight_le_one S hbd hP F Dis h𝒰 hν hconc
  have hge : 1 ≤ atomWeight ν n := by
    have hn : 1 ≤ n + 1 := by omega
    obtain ⟨ω, hω0, hω⟩ := Om.pi_lower (n + 1) n hn (Nat.lt_succ_self n)
    exact lower_weight (fun i => ⟨atomWeight_nonneg ν i, hle i⟩) (f := n + 1) (i₀ := n)
      (Nat.lt_succ_self n) (fun k => Om.win (n + 1) k) (fun k => hat _ (Om.mem (n + 1) k hn))
      (fun k i hi => Om.pi_neg (n + 1) k i hn hi) (fun k => Om.pi_first (n + 1) k hn)
      (fun k i hi => Om.pi_nonneg (n + 1) k i hn hi) hω0 hω (Om.tail_small (n + 1) hn)
  exact le_antisymm (hle n) hge

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.atomic_inequality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.atomic_inequality

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.atomWeight_zero_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.atomWeight_zero_ge

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.atomWeight_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.atomWeight_le_one

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.atomWeight_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.atomWeight_eq_one

end FormalResearch.ModularBootstrap.Upper.Rigidity
