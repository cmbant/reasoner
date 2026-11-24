module

public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityUp

/-!
# Lower bounds for the node weights (`virasoro_two_level.tex`, `gt:2.6`, Step 5)

`lowDatum α M` has zeros `p = z₁ + 1`, `q = z_{M+1}` and ideal double zeros at every Airy zero `a_k`, `k ≥ 3`, so
`F_M = Ai² (u - p)(u - q)/((u - a₁)²(u - a₂)²)`.  Its node values are
`τ^M_i = (z - p)(z - q)/(((z - a₁)(z - a₂))² (cot²α - z))`, `z = z_{i+1}`.  For fixed `j`:

* `τ^M_j < 0` and `|τ^M_j| ≥ c > 0` for `M ≥ j + 1`;
* `τ^M_i ≤ 0` for `i ≤ M`, and `0 ≤ τ^M_i ≤ 2/i²` for `i > M ≥ M₀`.

Hence `Σ_i max(τ^M_i, 0)/|τ^M_j| ≤ (1/c) Σ_{i > M} 2/i² → 0` (`low_family`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty
open FormalResearch.ModularBootstrap.Upper.Rigidity

/-- The datum with zeros `z₁ + 1`, `z_{M+1}` and sites at the Airy zeros `a_k`, `3 ≤ k ≤ M`. -/
noncomputable def lowDatum (α : ℝ) (M : ℕ) : IdealDatum :=
  ⟨clarkNode α 1 + 1, clarkNode α (M + 1), M, fun k => airyZero k⟩

lemma lowDatum_adm (α : ℝ) {M : ℕ} (hM : 2 ≤ M) : (lowDatum α M).Adm := by
  have hz1 : clarkNode α 2 < clarkNode α 1 := clarkNode_lt_of_lt le_rfl (by norm_num) α
  have hzM : clarkNode α (M + 1) < clarkNode α 2 :=
    clarkNode_lt_of_lt (n := 2) (m := M + 1) (by norm_num) (by omega) α
  refine ⟨?_, ?_, hM, ?_, ?_, ?_⟩
  · show clarkNode α (M + 1) < clarkNode α 1 + 1; linarith
  · show clarkNode α (M + 1) < 0; linarith [clarkNode_two_lt_zero α]
  · intro k _ _; exact airyZero_neg k
  · intro j k hj3 _ hk3 _ h
    exact airyZero_inj (by omega) (by omega) h
  · intro k hk3 hkM j hj h
    have := airyZero_inj (by omega) (by omega) h
    omega

lemma tau_low (α : ℝ) {M : ℕ} (hM : 2 ≤ M) (i : ℕ) :
    (lowDatum α M).tau α i =
      (cNode α i - (clarkNode α 1 + 1)) * (cNode α i - clarkNode α (M + 1)) /
        (((cNode α i - airyZero 1) * (cNode α i - airyZero 2)) ^ 2 * (cotC α ^ 2 - cNode α i)) := by
  have hD := windowDr_split M hM (cNode α i)
  have hP : ∏ k ∈ Finset.Icc 3 M, (cNode α i - airyZero k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k hk =>
      sub_ne_zero.mpr (clarkNode_ne_airyZero α (n := i + 1) (by omega) (by have := (Finset.mem_Icc.mp hk).1; omega))
  have h1 : cNode α i - airyZero 1 ≠ 0 := sub_ne_zero.mpr (clarkNode_ne_airyZero α (n := i + 1) (by omega) le_rfl)
  have h2 : cNode α i - airyZero 2 ≠ 0 :=
    sub_ne_zero.mpr (clarkNode_ne_airyZero α (n := i + 1) (by omega) (by norm_num))
  unfold IdealDatum.tau
  have hNr : (lowDatum α M).Nr (cNode α i) = (cNode α i - (clarkNode α 1 + 1)) * (cNode α i - clarkNode α (M + 1)) *
      (∏ k ∈ Finset.Icc 3 M, (cNode α i - airyZero k)) ^ 2 := by
    show (cNode α i - (clarkNode α 1 + 1)) * (cNode α i - clarkNode α (M + 1)) *
      ∏ k ∈ Finset.Icc 3 M, (cNode α i - airyZero k) ^ 2 = _
    rw [Finset.prod_pow]
  have hK : (lowDatum α M).K = M := rfl
  rw [hNr, hK, hD]
  field_simp

lemma low_term_aux {X P Q A1 A2 c I : ℝ} (hI : 0 < I) (hX : 0 < X) (hP0 : 0 ≤ P) (hP : P ≤ 2 * X)
    (hQ : Q ≤ X) (hA1 : X / 2 ≤ A1) (hA2 : X / 2 ≤ A2) (hc : 0 ≤ c)
    (hI3 : I ^ 2 * 16 ≤ X ^ 3) : P * Q / ((A1 * A2) ^ 2 * (c + X)) ≤ 2 / I ^ 2 := by
  have hA1p : 0 < A1 := by linarith
  have hA2p : 0 < A2 := by linarith
  have hden : 0 < (A1 * A2) ^ 2 * (c + X) := by positivity
  rw [div_le_div_iff₀ hden (by positivity)]
  have h1 : P * Q ≤ 2 * X ^ 2 := by nlinarith
  have h2 : P * Q * I ^ 2 ≤ 2 * X ^ 2 * I ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg I)
  have h3 : 2 * X ^ 2 * I ^ 2 ≤ 2 * X ^ 2 * (X ^ 3 / 16) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
  have h4 : X ^ 2 / 4 ≤ A1 * A2 := by
    have := mul_le_mul hA1 hA2 (by positivity) hA1p.le
    nlinarith
  have h5 : (X ^ 2 / 4) ^ 2 ≤ (A1 * A2) ^ 2 := pow_le_pow_left₀ (by positivity) h4 2
  have h6 : (X ^ 2 / 4) ^ 2 * X ≤ (A1 * A2) ^ 2 * (c + X) :=
    mul_le_mul h5 (by linarith) hX.le (by positivity)
  nlinarith

lemma tau_low_nonpos (α : ℝ) {M : ℕ} (hM : 2 ≤ M) {i : ℕ} (hi : i ≤ M) :
    (lowDatum α M).tau α i ≤ 0 := by
  rw [tau_low α hM i]
  have hz1 : cNode α i ≤ clarkNode α 1 := by
    have := (cNode_strictAnti α).antitone (Nat.zero_le i); simpa [cNode] using this
  have hq : clarkNode α (M + 1) ≤ cNode α i := by
    have := (cNode_strictAnti α).antitone hi; simpa [cNode] using this
  have hc := cot_sq_sub_pos α (n := i + 1) (by omega)
  refine div_nonpos_of_nonpos_of_nonneg ?_ (by unfold cNode at *; positivity)
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

/-- The eventual summable majorant: `0 ≤ τ^M_i ≤ 2/i²` for `i > M ≥ N₀`. -/
lemma tau_low_tail (α : ℝ) : ∃ N₀ : ℕ, ∀ M, N₀ ≤ M → ∀ i, M < i →
    0 ≤ (lowDatum α M).tau α i ∧ (lowDatum α M).tau α i ≤ 2 / (i : ℝ) ^ 2 := by
  obtain ⟨k0, h⟩ := exists_clark_nodeHyp α
  set X₀ : ℝ := max (|clarkNode α 1| + 1) (2 * (|airyZero 1| + |airyZero 2|)) with hX₀
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 ((tendsto_cNode α).eventually (eventually_le_atBot (-X₀)))
  refine ⟨max N₁ 2, fun M hM i hi => ?_⟩
  have hM2 : 2 ≤ M := (le_max_right _ _).trans hM
  have hiM : N₁ ≤ i := by have := (le_max_left N₁ 2).trans hM; omega
  have hi2 : 2 ≤ i := by omega
  rw [tau_low α hM2 i]
  set z := cNode α i with hz
  have hzX : z ≤ -X₀ := hN₁ i hiM
  have hX0pos : 0 < X₀ := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hzneg : z < 0 := by linarith
  have hq : z < clarkNode α (M + 1) := by
    have := clarkNode_lt_of_lt (n := M + 1) (m := i + 1) (by omega) (by omega) α
    simpa [hz, cNode] using this
  have hq0 : clarkNode α (M + 1) < 0 := clarkNode_neg_of_two_le α (by omega)
  have hc := cot_sq_sub_pos α (n := i + 1) (by omega)
  have hcot : 0 ≤ cotC α ^ 2 := sq_nonneg _
  have h1 : |clarkNode α 1| + 1 ≤ -z := by linarith [le_max_left (|clarkNode α 1| + 1) (2 * (|airyZero 1| + |airyZero 2|))]
  have h2 : 2 * (|airyZero 1| + |airyZero 2|) ≤ -z := by
    linarith [le_max_right (|clarkNode α 1| + 1) (2 * (|airyZero 1| + |airyZero 2|))]
  have ha1 : airyZero 1 < 0 := airyZero_neg 1
  have ha2 : airyZero 2 < 0 := airyZero_neg 2
  have habs1 : |airyZero 1| = -airyZero 1 := abs_of_neg ha1
  have habs2 : |airyZero 2| = -airyZero 2 := abs_of_neg ha2
  have hz1abs := neg_abs_le (clarkNode α 1)
  have hz1abs' := le_abs_self (clarkNode α 1)
  -- cube bound
  have hcube : (i : ℝ) ^ 2 * 16 ≤ (-z) ^ 3 := by
    have hlt : cNode α i < airyZero i := by
      have := cNode_lt_airyNode α (i - 1)
      unfold airyNode at this
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ i)] at this
    have hp : 16 * (i : ℝ) ^ 2 ≤ (-airyZero i) ^ 3 := h.cube_lo i hi2
    have hpos : 0 < -airyZero i := h.pos i (by omega)
    have h3 : -airyZero i ≤ -z := by linarith
    have h4 : (-airyZero i) ^ 3 ≤ (-z) ^ 3 := pow_le_pow_left₀ hpos.le h3 3
    nlinarith
  have hI : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
  have hbase := low_term_aux (X := -z) (P := clarkNode α 1 + 1 - z) (Q := clarkNode α (M + 1) - z)
    (A1 := airyZero 1 - z) (A2 := airyZero 2 - z) (c := cotC α ^ 2) hI (by linarith)
    (by linarith [(cNode_strictAnti α).antitone (Nat.zero_le i), show cNode α 0 = clarkNode α 1 from rfl])
    (by linarith) (by linarith) (by linarith) (by linarith) hcot hcube
  have e : (z - (clarkNode α 1 + 1)) * (z - clarkNode α (M + 1)) /
      (((z - airyZero 1) * (z - airyZero 2)) ^ 2 * (cotC α ^ 2 - z)) =
      (clarkNode α 1 + 1 - z) * (clarkNode α (M + 1) - z) /
        (((airyZero 1 - z) * (airyZero 2 - z)) ^ 2 * (cotC α ^ 2 + -z)) := by
    have e1 : (z - airyZero 1) * (z - airyZero 2) = (airyZero 1 - z) * (airyZero 2 - z) := by ring
    have e2 : cotC α ^ 2 - z = cotC α ^ 2 + -z := by ring
    have e3 : (z - (clarkNode α 1 + 1)) * (z - clarkNode α (M + 1)) =
        (clarkNode α 1 + 1 - z) * (clarkNode α (M + 1) - z) := by ring
    rw [e1, e2, e3]
  rw [e]
  refine ⟨?_, hbase⟩
  refine div_nonneg (mul_nonneg ?_ ?_) (mul_nonneg (sq_nonneg _) (by linarith))
  · have := (cNode_strictAnti α).antitone (Nat.zero_le i)
    have h0 : cNode α 0 = clarkNode α 1 := rfl
    linarith
  · linarith

lemma tau_low_neg (α : ℝ) (j : ℕ) : ∃ c : ℝ, 0 < c ∧ ∀ M, j + 1 ≤ M → 2 ≤ M →
    (lowDatum α M).tau α j ≤ -c := by
  set z := cNode α j with hz
  have hn : 1 ≤ j + 1 := by omega
  have hc := cot_sq_sub_pos α (n := j + 1) hn
  have hz' : cotC α ^ 2 - z > 0 := hc
  have h1 : z - airyZero 1 ≠ 0 := sub_ne_zero.mpr (clarkNode_ne_airyZero α (n := j + 1) hn le_rfl)
  have h2 : z - airyZero 2 ≠ 0 := sub_ne_zero.mpr (clarkNode_ne_airyZero α (n := j + 1) hn (by norm_num))
  have hden : 0 < ((z - airyZero 1) * (z - airyZero 2)) ^ 2 * (cotC α ^ 2 - z) := by
    have : 0 < ((z - airyZero 1) * (z - airyZero 2)) ^ 2 := by positivity
    positivity
  have hd : 0 < z - cNode α (j + 1) := by
    have := (cNode_strictAnti α) (Nat.lt_succ_self j); linarith
  refine ⟨(z - cNode α (j + 1)) / (((z - airyZero 1) * (z - airyZero 2)) ^ 2 * (cotC α ^ 2 - z)),
    by positivity, fun M hM hM2 => ?_⟩
  rw [tau_low α hM2 j, ← hz]
  have hz1 : z ≤ clarkNode α 1 := by
    have := (cNode_strictAnti α).antitone (Nat.zero_le j); simpa [hz, cNode] using this
  have hq : clarkNode α (M + 1) ≤ cNode α (j + 1) := by
    have := (cNode_strictAnti α).antitone (show j + 1 ≤ M by omega); simpa [cNode] using this
  rw [← neg_div, div_le_div_iff_of_pos_right hden]
  have h3 : 1 ≤ clarkNode α 1 + 1 - z := by linarith
  have h4 : z - cNode α (j + 1) ≤ z - clarkNode α (M + 1) := by linarith
  have h5 := mul_le_mul h3 h4 hd.le (by linarith)
  nlinarith

lemma tendsto_tail_sum :
    Tendsto (fun M : ℕ => ∑' i : ℕ, (fun k : ℕ => 2 / (k : ℝ) ^ 2) (i + (M + 1))) atTop (𝓝 0) :=
  (tendsto_sum_nat_add (fun k : ℕ => 2 / (k : ℝ) ^ 2)).comp (tendsto_add_atTop_nat 1)

lemma summable_two_div_sq : Summable (fun k : ℕ => 2 / (k : ℝ) ^ 2) := by
  have := (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2)).mul_left 2
  refine this.congr fun k => ?_
  ring

lemma summable_max_tau {α : ℝ} (hα : Real.sin α ≠ 0) {M : ℕ} (hM2 : 2 ≤ M) :
    Summable (fun i => max ((lowDatum α M).tau α i) 0) := by
  have hV := (lowDatum α M).hasSum_tau hα (show 2 ≤ (lowDatum α M).K from hM2)
  refine Summable.of_norm_bounded hV.summable.abs fun i => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  rcases le_total 0 ((lowDatum α M).tau α i) with h | h
  · rw [max_eq_left h, abs_of_nonneg h]
  · rw [max_eq_right h]; exact abs_nonneg _

lemma low_tsum_le {α : ℝ} (hα : Real.sin α ≠ 0) {N₀ : ℕ}
    (hN₀ : ∀ M, N₀ ≤ M → ∀ i, M < i →
      0 ≤ (lowDatum α M).tau α i ∧ (lowDatum α M).tau α i ≤ 2 / (i : ℝ) ^ 2)
    {M : ℕ} (hM : N₀ ≤ M) (hM2 : 2 ≤ M) :
    0 ≤ ∑' i, max ((lowDatum α M).tau α i) 0 ∧
      ∑' i, max ((lowDatum α M).tau α i) 0 ≤
        ∑' i : ℕ, (fun k : ℕ => 2 / (k : ℝ) ^ 2) (i + (M + 1)) := by
  have hsum := summable_max_tau hα hM2
  have hsplit := hsum.sum_add_tsum_nat_add (M + 1)
  have hzero : ∑ i ∈ Finset.range (M + 1), max ((lowDatum α M).tau α i) 0 = 0 :=
    Finset.sum_eq_zero fun i hi => max_eq_right
      (tau_low_nonpos α hM2 (by have := Finset.mem_range.1 hi; omega))
  rw [hzero, zero_add] at hsplit
  refine ⟨tsum_nonneg fun i => le_max_right _ _, ?_⟩
  have hle : ∀ i : ℕ, max ((lowDatum α M).tau α (i + (M + 1))) 0 ≤
      2 / (((i + (M + 1) : ℕ) : ℝ)) ^ 2 := by
    intro i
    obtain ⟨h1, h2⟩ := hN₀ M hM (i + (M + 1)) (by omega)
    rw [max_eq_left h1]; exact h2
  have hg : Summable (fun i : ℕ => 2 / (((i + (M + 1) : ℕ) : ℝ)) ^ 2) :=
    (summable_nat_add_iff (f := fun k : ℕ => 2 / (k : ℝ) ^ 2) (M + 1)).2 summable_two_div_sq
  have hf : Summable (fun i : ℕ => max ((lowDatum α M).tau α (i + (M + 1))) 0) :=
    (summable_nat_add_iff (f := fun i => max ((lowDatum α M).tau α i) 0) (M + 1)).2 hsum
  have := hf.tsum_le_tsum hle hg
  rw [hsplit] at this
  exact this

theorem low_family {α : ℝ} (hα : Real.sin α ≠ 0) (j : ℕ) :
    (∀ᶠ M in atTop, (lowDatum α M).tau α j < 0) ∧
    Tendsto (fun M : ℕ => (∑' i, max ((lowDatum α M).tau α i) 0) / (-(lowDatum α M).tau α j))
      atTop (𝓝 0) := by
  obtain ⟨c, hc, hneg⟩ := tau_low_neg α j
  obtain ⟨N₀, hN₀⟩ := tau_low_tail α
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℕ, j + 1 ≤ K₀ ∧ 2 ≤ K₀ ∧ N₀ ≤ K₀ :=
    ⟨max (max (j + 1) 2) N₀, by omega, by omega, by omega⟩
  have hneg' : ∀ M, K₀ ≤ M → (lowDatum α M).tau α j ≤ -c := fun M hM =>
    hneg M (by omega) (by omega)
  refine ⟨eventually_atTop.2 ⟨K₀, fun M hM => by linarith [hneg' M hM]⟩, ?_⟩
  have hbound : ∀ M, K₀ ≤ M →
      0 ≤ (∑' i, max ((lowDatum α M).tau α i) 0) / (-(lowDatum α M).tau α j) ∧
      (∑' i, max ((lowDatum α M).tau α i) 0) / (-(lowDatum α M).tau α j) ≤
        (1 / c) * ∑' i : ℕ, (fun k : ℕ => 2 / (k : ℝ) ^ 2) (i + (M + 1)) := by
    intro M hM
    obtain ⟨hS0, hS⟩ := low_tsum_le hα hN₀ (M := M) (by omega) (by omega)
    have hτ := hneg' M hM
    refine ⟨div_nonneg hS0 (by linarith), ?_⟩
    calc _ ≤ (∑' i : ℕ, (fun k : ℕ => 2 / (k : ℝ) ^ 2) (i + (M + 1))) / c :=
          div_le_div₀ (hS0.trans hS) hS hc (by linarith)
      _ = _ := by rw [one_div, inv_mul_eq_div]
  have hup : Tendsto (fun M : ℕ => (1 / c) *
      ∑' i : ℕ, (fun k : ℕ => 2 / (k : ℝ) ^ 2) (i + (M + 1))) atTop (𝓝 0) := by
    simpa using tendsto_tail_sum.const_mul (1 / c)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (eventually_atTop.2 ⟨K₀, fun M hM => (hbound M hM).1⟩)
    (eventually_atTop.2 ⟨K₀, fun M hM => (hbound M hM).2⟩)

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.low_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms low_family

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.lowDatum_adm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lowDatum_adm

end FormalResearch.ModularBootstrap.TwoLevel
