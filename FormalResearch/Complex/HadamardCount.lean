module

public import FormalResearch.Complex.HadamardListing
public import FormalResearch.Complex.HadamardProduct

/-!
# Zeros of an entire function of finite order: Jensen counting and convergence exponent
(Hadamard factorization, milestone H2)

Statement formalised (Hadamard 1893; Boas, *Entire functions*, Thm 2.5.1; Titchmarsh, *The theory of functions*, 8.1):
if `f` is entire, `f 0 ≠ 0` and `‖f z‖ ≤ C exp (C ‖z‖^σ)`, then the number of zeros (with multiplicity) in the disc
`‖z‖ ≤ r` is `O(r^σ)` (`Hadamard.Listing.ncard_le_mul_rpow`, from Mathlib's Jensen inequality
`AnalyticOnNhd.sum_divisor_le`), hence `Σ ‖a_i‖^{-s} < ∞` for every `s > σ`
(`Hadamard.Listing.summable_rpow`, `Hadamard.Listing.canonData`).  All **proved**.
-/

@[expose] public section

open Complex Filter Topology Finset Metric
open scoped BigOperators Classical

namespace FormalResearch.Hadamard

variable {ι : Type*}

/-- `f` has growth of order at most `σ`: `‖f z‖ ≤ C exp (C ‖z‖^σ)`. -/
def GrowthBound (f : ℂ → ℂ) (σ : ℝ) : Prop := ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C * Real.exp (C * ‖z‖ ^ σ)

lemma GrowthBound.exists_ge_one {f : ℂ → ℂ} {σ : ℝ} (h : GrowthBound f σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z, ‖f z‖ ≤ C * Real.exp (C * ‖z‖ ^ σ) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 1, le_max_right _ _, fun z => ?_⟩
  have hx : 0 ≤ ‖z‖ ^ σ := Real.rpow_nonneg (norm_nonneg _) _
  calc ‖f z‖ ≤ C * Real.exp (C * ‖z‖ ^ σ) := hC z
    _ ≤ max C 1 * Real.exp (C * ‖z‖ ^ σ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max C 1 * Real.exp (max C 1 * ‖z‖ ^ σ) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hx

section count

variable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {a : ι → ℂ} (L : Listing f a)
  {C σ : ℝ} (hC : 1 ≤ C) (hb : ∀ z, ‖f z‖ ≤ C * Real.exp (C * ‖z‖ ^ σ))
include hf h0 L hC hb

/-- Jensen: the number of zeros in `‖z‖ ≤ r` is at most `(log C + C (2r)^σ + |log ‖f 0‖|) / log 2`. -/
lemma Listing.ncard_le (r : ℝ) (hr : 0 < r) :
    (Set.ncard {i | ‖a i‖ ≤ r} : ℝ) ≤
      (Real.log C + C * (2 * r) ^ σ + |Real.log ‖f 0‖|) / Real.log 2 := by
  have hfin : {i | a i ∈ closedBall (0 : ℂ) r}.Finite := by
    refine (L.finite_idx hf h0 r).subset fun i hi => ?_
    simpa using hi
  have hcard := L.ncard_idx_eq_finsum_divisor hf h0 (closedBall (0 : ℂ) r) hfin
  set M : ℝ := C * Real.exp (C * (2 * r) ^ σ) with hM
  have hM1 : 1 ≤ M := by
    have : 1 ≤ Real.exp (C * (2 * r) ^ σ) := by
      apply Real.one_le_exp
      exact mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _)
    nlinarith
  have han : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |2 * r|) := fun w _ => hf.analyticAt w
  have hjen := han.sum_divisor_le (c := 0) (r := r) (R := 2 * r) (M := M)
    (by rw [abs_pos]; exact hr.ne') (by rw [abs_of_pos hr, abs_of_pos (by linarith)]; linarith)
    hM1 h0 (fun z hz => by
      have hz' : ‖z‖ = 2 * r := by
        simpa [abs_of_pos (by linarith : 0 < 2 * r)] using hz
      rw [hM, ← hz']
      exact hb z)
  have hlog2 : Real.log (2 * r / r) = Real.log 2 := by
    congr 1; field_simp
  rw [abs_of_pos hr, hlog2] at hjen
  have h1 : ((Set.ncard {i | ‖a i‖ ≤ r} : ℕ) : ℝ) = (((∑ᶠ u, MeromorphicOn.divisor f
      (closedBall (0 : ℂ) r) u : ℤ)) : ℝ) := by
    have : (Set.ncard {i | a i ∈ closedBall (0 : ℂ) r} : ℤ) = _ := hcard
    have h2 : {i | a i ∈ closedBall (0 : ℂ) r} = {i | ‖a i‖ ≤ r} := by ext i; simp
    rw [h2] at this
    rw [← this]; norm_cast
  rw [h1]
  refine hjen.trans ?_
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine div_le_div_of_nonneg_right ?_ hlog2pos.le
  have hf0 : 0 < ‖f 0‖ := norm_pos_iff.mpr h0
  have hMpos : 0 < M := by linarith
  rw [Real.log_div hMpos.ne' hf0.ne', hM, Real.log_mul (by linarith) (Real.exp_pos _).ne',
    Real.log_exp]
  have := neg_abs_le (Real.log ‖f 0‖)
  linarith

/-- Counting bound `n(r) ≤ K r^σ` for `r ≥ 1`. -/
lemma Listing.ncard_le_mul_rpow (hσ : 0 ≤ σ) {r : ℝ} (hr : 1 ≤ r) :
    (Set.ncard {i | ‖a i‖ ≤ r} : ℝ) ≤
      ((Real.log C + C * 2 ^ σ + |Real.log ‖f 0‖|) / Real.log 2) * r ^ σ := by
  refine (Listing.ncard_le hf h0 L hC hb r (by linarith)).trans ?_
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hrσ : 1 ≤ r ^ σ := Real.one_le_rpow hr hσ
  rw [div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ hlog2pos.le
  rw [Real.mul_rpow (by norm_num) (by linarith)]
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have habs : 0 ≤ |Real.log ‖f 0‖| := abs_nonneg _
  have hpos : 0 ≤ C * 2 ^ σ := by positivity
  nlinarith

end count

/-! ### Dyadic summation -/

lemma two_pow_rpow_comm (j : ℕ) (z : ℝ) : ((2 : ℝ) ^ j) ^ z = ((2 : ℝ) ^ z) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num), mul_comm]

/-- One dyadic block: the elements with `2^j ≤ ‖a i‖ < 2^{j+1}` contribute at most `K 2^σ q^j`. -/
lemma block_sum_le {a : ι → ℂ} {K σ s : ℝ} (hσ : 0 ≤ σ) (hs : σ < s)
    (hfin : ∀ R : ℝ, {i | ‖a i‖ ≤ R}.Finite)
    (hcount : ∀ r : ℝ, 1 ≤ r → (Set.ncard {i | ‖a i‖ ≤ r} : ℝ) ≤ K * r ^ σ)
    (u : Finset ι) (j : ℕ) :
    ∑ i ∈ u with Nat.log 2 ⌊‖a i‖⌋₊ = j,
        (if 1 ≤ ‖a i‖ then (‖a i‖ ^ s)⁻¹ else 0)
      ≤ K * 2 ^ σ * (((2 : ℝ) ^ (σ - s)) ^ j) := by
  rw [← Finset.sum_filter]
  set B : Finset ι := (u.filter fun i => Nat.log 2 ⌊‖a i‖⌋₊ = j).filter fun i => 1 ≤ ‖a i‖ with hB
  have hmem : ∀ i ∈ B, (2 : ℝ) ^ j ≤ ‖a i‖ ∧ ‖a i‖ < (2 : ℝ) ^ (j + 1) := by
    intro i hi
    simp only [hB, Finset.mem_filter] at hi
    obtain ⟨⟨_, hij⟩, h1⟩ := hi
    have hfl : 1 ≤ ⌊‖a i‖⌋₊ := Nat.le_floor (by simpa using h1)
    constructor
    · have := Nat.pow_log_le_self 2 (x := ⌊‖a i‖⌋₊) (by omega)
      rw [hij] at this
      calc (2 : ℝ) ^ j = ((2 ^ j : ℕ) : ℝ) := by push_cast; rfl
        _ ≤ (⌊‖a i‖⌋₊ : ℝ) := by exact_mod_cast this
        _ ≤ ‖a i‖ := Nat.floor_le (norm_nonneg _)
    · have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) ⌊‖a i‖⌋₊
      rw [hij] at this
      have h2 : ⌊‖a i‖⌋₊ + 1 ≤ 2 ^ (j + 1) := this
      calc ‖a i‖ < (⌊‖a i‖⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        _ ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast h2
        _ = (2 : ℝ) ^ (j + 1) := by push_cast; rfl
  have hterm : ∀ i ∈ B, (‖a i‖ ^ s)⁻¹ ≤ (((2 : ℝ) ^ j) ^ s)⁻¹ := by
    intro i hi
    have := (hmem i hi).1
    have hpos : 0 < ((2 : ℝ) ^ j) := by positivity
    exact inv_anti₀ (by positivity) (Real.rpow_le_rpow hpos.le this (by linarith))
  have hcardB : (B.card : ℝ) ≤ K * ((2 : ℝ) ^ (j + 1)) ^ σ := by
    have hsub : (↑B : Set ι) ⊆ {i | ‖a i‖ ≤ (2 : ℝ) ^ (j + 1)} := fun i hi => (hmem i hi).2.le
    have h1 : B.card ≤ Set.ncard {i | ‖a i‖ ≤ (2 : ℝ) ^ (j + 1)} := by
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hsub (hfin _)
    calc (B.card : ℝ) ≤ (Set.ncard {i | ‖a i‖ ≤ (2 : ℝ) ^ (j + 1)} : ℝ) := by exact_mod_cast h1
      _ ≤ _ := hcount _ (one_le_pow₀ (by norm_num))
  calc ∑ i ∈ B, (‖a i‖ ^ s)⁻¹ ≤ ∑ i ∈ B, (((2 : ℝ) ^ j) ^ s)⁻¹ := Finset.sum_le_sum hterm
    _ = (B.card : ℝ) * (((2 : ℝ) ^ j) ^ s)⁻¹ := by simp
    _ ≤ (K * ((2 : ℝ) ^ (j + 1)) ^ σ) * (((2 : ℝ) ^ j) ^ s)⁻¹ :=
        mul_le_mul_of_nonneg_right hcardB (by positivity)
    _ = K * 2 ^ σ * (((2 : ℝ) ^ (σ - s)) ^ j) := by
        rw [← two_pow_rpow_comm, Real.rpow_sub (by norm_num), pow_succ,
          Real.mul_rpow (by positivity) (by norm_num)]
        have h2 : ((2 : ℝ) ^ j) ^ s ≠ 0 := by positivity
        field_simp

/-- Convergence exponent from a counting bound: `n(r) ≤ K r^σ` for `r ≥ 1` gives `Σ ‖a_i‖^{-s} < ∞` for `s > σ`. -/
theorem summable_rpow_of_count {a : ι → ℂ} {K σ s : ℝ} (hK : 0 ≤ K) (hσ : 0 ≤ σ) (hs : σ < s)
    (hfin : ∀ R : ℝ, {i | ‖a i‖ ≤ R}.Finite)
    (hcount : ∀ r : ℝ, 1 ≤ r → (Set.ncard {i | ‖a i‖ ≤ r} : ℝ) ≤ K * r ^ σ) :
    Summable fun i => (‖a i‖ ^ s)⁻¹ := by
  set G : ι → ℝ := fun i => if 1 ≤ ‖a i‖ then (‖a i‖ ^ s)⁻¹ else 0 with hG
  have hq0 : 0 ≤ (2 : ℝ) ^ (σ - s) := by positivity
  have hq1 : (2 : ℝ) ^ (σ - s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hGnn : 0 ≤ G := fun i => by
    simp only [hG, Pi.zero_apply]; split_ifs <;> positivity
  have hGs : Summable G := by
    refine summable_of_sum_le (c := K * 2 ^ σ * (1 - (2 : ℝ) ^ (σ - s))⁻¹) hGnn fun u => ?_
    set kk : ι → ℕ := fun i => Nat.log 2 ⌊‖a i‖⌋₊ with hkk
    have hmaps : ∀ i ∈ u, kk i ∈ Finset.range (u.sup kk + 1) := fun i hi =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := kk) hi))
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have hgeo : HasSum (fun j : ℕ => K * 2 ^ σ * (((2 : ℝ) ^ (σ - s)) ^ j))
        (K * 2 ^ σ * (1 - (2 : ℝ) ^ (σ - s))⁻¹) :=
      (hasSum_geometric_of_lt_one hq0 hq1).mul_left _
    calc ∑ j ∈ Finset.range (u.sup kk + 1), ∑ i ∈ u with kk i = j, G i
        ≤ ∑ j ∈ Finset.range (u.sup kk + 1), K * 2 ^ σ * (((2 : ℝ) ^ (σ - s)) ^ j) :=
          Finset.sum_le_sum fun j _ => block_sum_le hσ hs hfin hcount u j
      _ ≤ _ := sum_le_hasSum _ (fun j _ => by positivity) hgeo
  refine Summable.of_norm_bounded_eventually hGs ?_
  have hev : ∀ᶠ i in cofinite, 1 ≤ ‖a i‖ := by
    rw [Filter.eventually_cofinite]
    refine (hfin 1).subset fun i hi => ?_
    simp only [Set.mem_ofPred_eq, not_le] at hi ⊢
    exact hi.le
  filter_upwards [hev] with i hi
  simp only [hG, hi, ↓reduceIte]
  rw [Real.norm_of_nonneg (by positivity)]

section summable

variable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {a : ι → ℂ} (L : Listing f a)
  {C σ : ℝ} (hC : 1 ≤ C) (hb : ∀ z, ‖f z‖ ≤ C * Real.exp (C * ‖z‖ ^ σ))
include hf h0 L hC hb

/-- **Convergence exponent (H2).** `Σ ‖a_i‖^{-s} < ∞` for every `s > σ`. -/
theorem Listing.summable_rpow (hσ : 0 ≤ σ) {s : ℝ} (hs : σ < s) :
    Summable fun i => (‖a i‖ ^ s)⁻¹ := by
  refine summable_rpow_of_count ?_ hσ hs (L.finite_idx hf h0) fun r hr =>
    Listing.ncard_le_mul_rpow hf h0 L hC hb hσ hr
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : 0 ≤ C * 2 ^ σ := by positivity
  positivity

/-- The canonical-product hypothesis for the genus `p` with `σ < p + 1`. -/
theorem Listing.canonData (hσ : 0 ≤ σ) {p : ℕ} (hp : σ < p + 1) : CanonData p a := by
  refine ⟨L.ne_zero, ?_⟩
  have := Listing.summable_rpow hf h0 L hC hb hσ (s := ((p + 1 : ℕ) : ℝ)) (by push_cast; exact hp)
  simp only [Real.rpow_natCast] at this
  exact this

end summable

end FormalResearch.Hadamard

/-- info: 'FormalResearch.Hadamard.Listing.ncard_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.Listing.ncard_le

/-- info: 'FormalResearch.Hadamard.Listing.summable_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.Listing.summable_rpow

/-- info: 'FormalResearch.Hadamard.Listing.canonData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.Listing.canonData

/-- info: 'FormalResearch.Hadamard.summable_rpow_of_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.summable_rpow_of_count
