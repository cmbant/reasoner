module

public import FormalResearch.ModularBootstrap.Upper.Rigidity.Families

/-!
# Weights of a limit measure on the Airy zeros (`sr:Sigma`, Steps 4--6, real-sequence level)

For a measure `ν` carried by the zeros `a_i` of `Ai`, `x_i = ν{a_i} Ai'(a_i)²`
(`atomWeight`).  The basic inequality `(I)` for an atomic `ν` reads `Σ_i x_i Π_i ≤ V` for every
design (`AtomicIneq`, `sr:e2`).  This module proves, for sequences:

* `upper_weight` (Step 5): `x_n ≤ 1` from designs with all `Π_m ≥ 0`, `Π_n ≥ ω`, small rest;
* `lower_weight` (Step 6): `x_i ≥ 1` for `i < f` from designs with omitted sites.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.Upper.Rigidity

open FormalResearch.Special

/-- The weight `x_i = ν{a_i} Ai'(a_i)²` of an atom of `ν` at the `i`-th zero. -/
noncomputable def atomWeight (ν : Measure ℝ) (i : ℕ) : ℝ :=
  (ν {airyNode i}).toReal * (airyAi' (airyNode i)) ^ 2

lemma atomWeight_nonneg (ν : Measure ℝ) (i : ℕ) : 0 ≤ atomWeight ν i :=
  mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)

lemma atomWeight_mul_weight (ν : Measure ℝ) (i : ℕ) :
    atomWeight ν i * airyNodeWeight i = (ν {airyNode i}).toReal := by
  unfold atomWeight airyNodeWeight
  have h := airyAi'_airyNode_ne i
  field_simp

/-- The atomic form of the basic inequality `(I)`: `Σ_i x_i Π_i ≤ V_𝔇` (summably). -/
def AtomicIneq (x : ℕ → ℝ) (D : Window) : Prop :=
  Summable (fun i => x i * D.pi i) ∧ ∑' i, x i * D.pi i ≤ D.V

lemma summable_ite_ne {a : ℕ → ℝ} (ha : Summable a) (i₀ : ℕ) :
    Summable fun i => if i = i₀ then (0 : ℝ) else a i := by
  convert ha.update i₀ 0 using 1
  funext i
  simp [Function.update_apply]

/-- `Σ (1 - x_i) Π_i ≥ 0` and its termwise bound: if `a_i ≤ b_i` for `i ≠ i₀` then
`-a_{i₀} ≤ Σ_{i ≠ i₀} b_i`. -/
lemma neg_le_tsum_ite {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (i₀ : ℕ)
    (hab : ∀ i, i ≠ i₀ → a i ≤ b i) (h0 : 0 ≤ ∑' i, a i) :
    -a i₀ ≤ ∑' i, if i = i₀ then 0 else b i := by
  have h1 := ha.tsum_eq_add_tsum_ite i₀
  have hsa := summable_ite_ne ha i₀
  have hsb := summable_ite_ne hb i₀
  have h2 : ∑' i, (if i = i₀ then (0 : ℝ) else a i) ≤ ∑' i, (if i = i₀ then (0 : ℝ) else b i) := by
    refine Summable.tsum_le_tsum (fun i => ?_) hsa hsb
    by_cases hi : i = i₀
    · simp [hi]
    · simpa [hi] using hab i hi
  linarith

/-- **Step 5** (`sr:Sigma`): upper bound on a weight `x_n`.  Designs `win k` with all `Π_m ≥ 0`,
`Π_n ≥ ω`, and `Σ_{m ≠ 0, n} Π_m → 0`; if `n ≠ 0` assume `x_0 ≥ 1`. -/
theorem upper_weight {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i) {n : ℕ} (hx0 : n ≠ 0 → 1 ≤ x 0)
    (win : ℕ → Window) (hat : ∀ k, AtomicIneq x (win k)) (hπ : ∀ k i, 0 ≤ (win k).pi i)
    {ω : ℝ} (hω0 : 0 < ω) (hω : ∀ k, ω ≤ (win k).pi n)
    (hr : Tendsto (fun k => ∑' i, if i = 0 ∨ i = n then 0 else (win k).pi i) atTop (𝓝 0)) :
    x n ≤ 1 := by
  have key : ∀ k, (x n - 1) * (win k).pi n ≤ ∑' i, if i = 0 ∨ i = n then 0 else (win k).pi i := by
    intro k
    obtain ⟨hs, hle⟩ := hat k
    have hpi := (win k).summable_pi
    have ha : Summable fun i => (1 - x i) * (win k).pi i := by
      have := hpi.sub hs
      refine this.congr fun i => ?_
      ring
    have h0 : 0 ≤ ∑' i, (1 - x i) * (win k).pi i := by
      have : ∑' i, (1 - x i) * (win k).pi i = (win k).V - ∑' i, x i * (win k).pi i := by
        rw [← (win k).tsum_pi, ← hpi.tsum_sub hs]
        exact tsum_congr fun i => by ring
      rw [this]; linarith
    have hb : Summable fun i => if i = 0 then (0 : ℝ) else (win k).pi i := by
      exact summable_ite_ne hpi 0
    have hab : ∀ i, i ≠ n → (1 - x i) * (win k).pi i ≤ if i = 0 then 0 else (win k).pi i := by
      intro i hi
      by_cases hi0 : i = 0
      · subst hi0
        have := hx0 (fun h => hi h.symm)
        simp only [ite_true]
        nlinarith [hπ k 0]
      · simp only [hi0, ite_false]
        nlinarith [hx i, hπ k i]
    have := neg_le_tsum_ite ha hb n hab h0
    have heq : (∑' i, if i = n then (0 : ℝ) else (if i = 0 then 0 else (win k).pi i)) =
        ∑' i, if i = 0 ∨ i = n then 0 else (win k).pi i := by
      refine tsum_congr fun i => ?_
      by_cases h1 : i = n <;> by_cases h2 : i = 0 <;> simp [h1, h2]
    rw [heq] at this
    linarith
  by_contra hcon
  push Not at hcon
  have hlim : (x n - 1) * ω ≤ 0 := by
    refine ge_of_tendsto hr (Eventually.of_forall fun k => ?_)
    calc (x n - 1) * ω ≤ (x n - 1) * (win k).pi n :=
          mul_le_mul_of_nonneg_left (hω k) (by linarith)
      _ ≤ _ := key k
  nlinarith

/-- **Step 6** (`sr:Sigma`): lower bound on the weights below the first kept site.  Assume
`0 ≤ x_i ≤ 1`, and designs `win k` with `Π_i < 0` for `i < f`, `Π_f = 0`, `Π_i ≥ 0` for `i > f`,
`-Π_{i₀} ≥ ω` eventually and `Σ_{i > f} Π_i → 0`.  Then `x_{i₀} ≥ 1`. -/
theorem lower_weight {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) {f i₀ : ℕ} (hi₀ : i₀ < f)
    (win : ℕ → Window) (hat : ∀ k, AtomicIneq x (win k))
    (hneg : ∀ k i, i < f → (win k).pi i < 0) (hfirst : ∀ k, (win k).pi f = 0)
    (hpos : ∀ k i, f < i → 0 ≤ (win k).pi i) {ω : ℝ} (hω0 : 0 < ω)
    (hω : ∀ᶠ k in atTop, ω ≤ -(win k).pi i₀)
    (hr : Tendsto (fun k => ∑' i, if f < i then (win k).pi i else 0) atTop (𝓝 0)) :
    1 ≤ x i₀ := by
  have key : ∀ k, (1 - x i₀) * (-(win k).pi i₀) ≤ ∑' i, if f < i then (win k).pi i else 0 := by
    intro k
    obtain ⟨hs, hle⟩ := hat k
    have hpi := (win k).summable_pi
    have ha : Summable fun i => (1 - x i) * (win k).pi i := by
      have := hpi.sub hs
      refine this.congr fun i => ?_
      ring
    have h0 : 0 ≤ ∑' i, (1 - x i) * (win k).pi i := by
      have : ∑' i, (1 - x i) * (win k).pi i = (win k).V - ∑' i, x i * (win k).pi i := by
        rw [← (win k).tsum_pi, ← hpi.tsum_sub hs]
        exact tsum_congr fun i => by ring
      rw [this]; linarith
    have hb : Summable fun i => if f < i then (win k).pi i else 0 := by
      convert hpi.indicator {i | f < i} using 1
      funext i
      simp [Set.indicator]
    have hab : ∀ i, i ≠ i₀ → (1 - x i) * (win k).pi i ≤ if f < i then (win k).pi i else 0 := by
      intro i hi
      rcases lt_trichotomy i f with h | h | h
      · have h1 := hneg k i h
        have h2 := (hx i).2
        have : ¬ f < i := not_lt.mpr h.le
        simp only [this, ite_false]
        nlinarith
      · subst h
        have : ¬ i < i := lt_irrefl _
        simp [hfirst k]
      · have h1 := hpos k i h
        have h2 := (hx i).1
        simp only [h, ite_true]
        nlinarith
    have := neg_le_tsum_ite ha hb i₀ hab h0
    have heq : (∑' i, if i = i₀ then (0 : ℝ) else (if f < i then (win k).pi i else 0)) =
        ∑' i, if f < i then (win k).pi i else 0 := by
      refine tsum_congr fun i => ?_
      by_cases h1 : i = i₀
      · subst h1
        have : ¬ f < i := not_lt.mpr hi₀.le
        simp [this]
      · simp [h1]
    rw [heq] at this
    linarith
  by_contra hcon
  push Not at hcon
  have hlim : (1 - x i₀) * ω ≤ 0 := by
    refine ge_of_tendsto hr ?_
    filter_upwards [hω] with k hk
    calc (1 - x i₀) * ω ≤ (1 - x i₀) * (-(win k).pi i₀) :=
          mul_le_mul_of_nonneg_left hk (by linarith)
      _ ≤ _ := key k
  nlinarith

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.upper_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.upper_weight

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.lower_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.lower_weight

end FormalResearch.ModularBootstrap.Upper.Rigidity
