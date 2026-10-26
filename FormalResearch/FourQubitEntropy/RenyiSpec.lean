import FormalResearch.FourQubitEntropy.Renyi

/-!
# Rényi entropies of a probability vector

General facts used by the Rényi corollaries of the paper:

* `renyiSpec_le_logb_card`, `renyiSpec_eq_iff`: `H_q(λ) ≤ log₂ n` for every `q > 0`, `q ≠ 1`, with
  equality iff `λ` is uniform (used in `prop:fqe-renyi-rank-two`);
* `sum_rpow_le_sum_rpow`, `sum_rpow_lt_sum_rpow`: order monotonicity of `H_q` for `q > 1`, weak and
  strict (`cor:fqe-renyi-two-up`, `prop:fqe-renyi-crossing`).
-/

open scoped ComplexConjugate Matrix ComplexOrder

namespace FormalResearch.FourQubitEntropy

open Real

/-- The Rényi-`q` entropy in bits of a probability vector: `log₂(Σ λᵢ^q)/(1-q)`. -/
noncomputable def renyiSpec {ι : Type*} [Fintype ι] (q : ℝ) (l : ι → ℝ) : ℝ :=
  Real.logb 2 (∑ i, l i ^ q) / (1 - q)

theorem renyiCut_eq_renyiSpec (q : ℝ) {R : Mat4} (hR : R.IsHermitian) :
    renyiCut q hR = renyiSpec q hR.eigenvalues := rfl

section Spectrum

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem card_rpow_eq (q : ℝ) : (Fintype.card ι : ℝ) ^ (1 - q) = Fintype.card ι * (1 / (Fintype.card ι : ℝ)) ^ q := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [Real.rpow_sub hn, Real.rpow_one, one_div, Real.inv_rpow hn.le, div_eq_mul_inv]

/-- Jensen with uniform weights, both directions: for `q > 0`, `q ≠ 1` the sum `Σ λᵢ^q` is at
most (`q < 1`) resp. at least (`q > 1`) `n^{1-q}`, with equality iff `λ` is uniform. -/
theorem sum_rpow_vs_card {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) {l : ι → ℝ} (hl : ∀ i, 0 ≤ l i)
    (hs : ∑ i, l i = 1) :
    (q < 1 → ∑ i, l i ^ q ≤ (Fintype.card ι : ℝ) ^ (1 - q)) ∧
    (1 < q → (Fintype.card ι : ℝ) ^ (1 - q) ≤ ∑ i, l i ^ q) ∧
    (∑ i, l i ^ q = (Fintype.card ι : ℝ) ^ (1 - q) ↔ ∀ i, l i = 1 / (Fintype.card ι : ℝ)) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  have hw : ∀ i ∈ (Finset.univ : Finset ι), 0 < 1 / n := fun i _ => by positivity
  have hw1 : ∑ _i : ι, 1 / n = 1 := by
    simp [hn_def]
  have hmean : ∑ i, (1 / n) • l i = 1 / n := by
    simp only [smul_eq_mul, ← Finset.mul_sum, hs, mul_one]
  have hmem : ∀ i ∈ (Finset.univ : Finset ι), l i ∈ Set.Ici (0 : ℝ) := fun i _ => hl i
  have hsum_q : ∑ i, (1 / n) • (l i ^ q) = (1 / n) * ∑ i, l i ^ q := by
    simp only [smul_eq_mul, ← Finset.mul_sum]
  have key_unif : (∀ i, l i = 1 / n) → ∑ i, l i ^ q = n ^ (1 - q) := by
    intro h
    simp only [h]
    rw [Finset.sum_const, Finset.card_univ, card_rpow_eq, nsmul_eq_mul]
  have e1 : n ^ (1 - q) = n * (1 / n) ^ q := card_rpow_eq q
  rcases lt_or_gt_of_ne hq1 with hlt | hgt
  · have hc := strictConcaveOn_rpow hq0 hlt
    have hle := hc.concaveOn.le_map_sum (t := Finset.univ) (w := fun _ => 1 / n) (p := l)
      (fun i _ => (hw i (Finset.mem_univ i)).le) hw1 hmem
    simp only [hmean, hsum_q] at hle
    have hiff := hc.map_sum_eq_iff (t := Finset.univ) (w := fun _ => 1 / n) (p := l) hw hw1 hmem
    simp only [hmean, hsum_q] at hiff
    refine ⟨fun _ => ?_, fun h => absurd h (by linarith), ?_⟩
    · rw [e1]
      have : n * ((1 / n) * ∑ i, l i ^ q) ≤ n * (1 / n) ^ q := by
        have h' : (1 / n) * ∑ i, l i ^ q ≤ (1 / n) ^ q := hle
        exact mul_le_mul_of_nonneg_left h' hn.le
      have e2 : n * ((1 / n) * ∑ i, l i ^ q) = ∑ i, l i ^ q := by field_simp
      linarith
    · constructor
      · intro h
        have h2 : (1 / n) ^ q = (1 / n) * ∑ i, l i ^ q := by
          rw [e1] at h
          have : n * (1 / n) ^ q = n * ((1 / n) * ∑ i, l i ^ q) := by
            rw [← h]; field_simp
          exact mul_left_cancel₀ hn.ne' this
        have := hiff.1 h2
        intro i
        exact this i (Finset.mem_univ i)
      · intro h; exact key_unif h
  · have hc := strictConvexOn_rpow hgt
    have hle := hc.convexOn.map_sum_le (t := Finset.univ) (w := fun _ => 1 / n) (p := l)
      (fun i _ => (hw i (Finset.mem_univ i)).le) hw1 hmem
    simp only [hmean, hsum_q] at hle
    have hiff := hc.map_sum_eq_iff (t := Finset.univ) (w := fun _ => 1 / n) (p := l) hw hw1 hmem
    simp only [hmean, hsum_q] at hiff
    refine ⟨fun h => absurd h (by linarith), fun _ => ?_, ?_⟩
    · rw [e1]
      have : n * (1 / n) ^ q ≤ n * ((1 / n) * ∑ i, l i ^ q) := by
        have h' : (1 / n) ^ q ≤ (1 / n) * ∑ i, l i ^ q := hle
        exact mul_le_mul_of_nonneg_left h' hn.le
      have e2 : n * ((1 / n) * ∑ i, l i ^ q) = ∑ i, l i ^ q := by field_simp
      linarith
    · constructor
      · intro h
        have h2 : (1 / n) ^ q = (1 / n) * ∑ i, l i ^ q := by
          rw [e1] at h
          have : n * (1 / n) ^ q = n * ((1 / n) * ∑ i, l i ^ q) := by
            rw [← h]; field_simp
          exact mul_left_cancel₀ hn.ne' this
        have := hiff.1 h2
        intro i
        exact this i (Finset.mem_univ i)
      · intro h; exact key_unif h

omit [Nonempty ι] in
theorem sum_rpow_pos {q : ℝ} {l : ι → ℝ} (hl : ∀ i, 0 ≤ l i) (hs : ∑ i, l i = 1) :
    0 < ∑ i, l i ^ q := by
  obtain ⟨i, hi⟩ : ∃ i, 0 < l i := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have : ∑ i, l i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (h i) (hl i)
    linarith
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hi q)
    (Finset.single_le_sum (f := fun i => l i ^ q) (fun j _ => Real.rpow_nonneg (hl j) q)
      (Finset.mem_univ i))

/-- **Rényi entropy is at most `log₂ n`** for every order `q > 0`, `q ≠ 1`. -/
theorem renyiSpec_le_logb_card {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) {l : ι → ℝ} (hl : ∀ i, 0 ≤ l i)
    (hs : ∑ i, l i = 1) : renyiSpec q l ≤ Real.logb 2 (Fintype.card ι) := by
  obtain ⟨h1, h2, -⟩ := sum_rpow_vs_card hq0 hq1 hl hs
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hpos := sum_rpow_pos (q := q) hl hs
  have hlog : Real.logb 2 ((Fintype.card ι : ℝ) ^ (1 - q)) = (1 - q) * Real.logb 2 (Fintype.card ι) :=
    Real.logb_rpow_eq_mul_logb_of_pos hn
  unfold renyiSpec
  rcases lt_or_gt_of_ne hq1 with hlt | hgt
  · have := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hpos (by positivity)).2 (h1 hlt)
    rw [hlog] at this
    rw [div_le_iff₀ (by linarith)]; linarith
  · have := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity) hpos).2 (h2 hgt)
    rw [hlog] at this
    rw [div_le_iff_of_neg (by linarith)]; linarith

/-- **Equality case**: `H_q(λ) = log₂ n` iff `λ` is the uniform vector. -/
theorem renyiSpec_eq_iff {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) {l : ι → ℝ} (hl : ∀ i, 0 ≤ l i)
    (hs : ∑ i, l i = 1) :
    renyiSpec q l = Real.logb 2 (Fintype.card ι) ↔ ∀ i, l i = 1 / (Fintype.card ι : ℝ) := by
  obtain ⟨-, -, h3⟩ := sum_rpow_vs_card hq0 hq1 hl hs
  rw [← h3]
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hpos := sum_rpow_pos (q := q) hl hs
  have hlog : Real.logb 2 ((Fintype.card ι : ℝ) ^ (1 - q)) = (1 - q) * Real.logb 2 (Fintype.card ι) :=
    Real.logb_rpow_eq_mul_logb_of_pos hn
  have hq' : (1 - q) ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  unfold renyiSpec
  rw [div_eq_iff hq']
  constructor
  · intro h
    have h' : Real.logb 2 (∑ i, l i ^ q) = Real.logb 2 ((Fintype.card ι : ℝ) ^ (1 - q)) := by
      rw [hlog]; linarith
    exact Real.logb_injOn_pos (by norm_num : (1 : ℝ) < 2) (Set.mem_Ioi.2 hpos)
      (Set.mem_Ioi.2 (by positivity)) h'
  · intro h
    rw [h, hlog]; ring

end Spectrum

section Monotone

variable {ι : Type*} [Fintype ι]

theorem mul_rpow_sub_one' {x q : ℝ} (hx : 0 ≤ x) (hq : 1 < q) : x * x ^ (q - 1) = x ^ q := by
  rcases hx.eq_or_lt with h | h
  · rw [← h, Real.zero_rpow (by linarith : (0:ℝ) < q).ne']; simp
  · rw [← Real.rpow_one_add' hx (by linarith)]; ring_nf

/-- Jensen with weights `λᵢ`: `(Σ λᵢ^q)^{(q'-1)/(q-1)} ≤ Σ λᵢ^{q'}` for `1 < q ≤ q'`. -/
theorem sum_rpow_le_sum_rpow {q q' : ℝ} (hq : 1 < q) (hqq : q ≤ q') {l : ι → ℝ}
    (hl : ∀ i, 0 ≤ l i) (hs : ∑ i, l i = 1) :
    (∑ i, l i ^ q) ^ ((q' - 1) / (q - 1)) ≤ ∑ i, l i ^ q' := by
  have hr : 1 ≤ (q' - 1) / (q - 1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hc := convexOn_rpow hr
  have hmem : ∀ i ∈ (Finset.univ : Finset ι), l i ^ (q - 1) ∈ Set.Ici (0 : ℝ) :=
    fun i _ => Real.rpow_nonneg (hl i) _
  have hle := hc.map_sum_le (t := Finset.univ) (w := l) (p := fun i => l i ^ (q - 1))
    (fun i _ => hl i) hs hmem
  have e1 : ∑ i, l i • l i ^ (q - 1) = ∑ i, l i ^ q := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [smul_eq_mul]; exact mul_rpow_sub_one' (hl i) hq
  have e2 : ∑ i, l i • (l i ^ (q - 1)) ^ ((q' - 1) / (q - 1)) = ∑ i, l i ^ q' := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [smul_eq_mul]
    rw [← Real.rpow_mul (hl i)]
    have : (q - 1) * ((q' - 1) / (q - 1)) = q' - 1 := by
      have : q - 1 ≠ 0 := (sub_pos.2 hq).ne'
      field_simp
    rw [this]; exact mul_rpow_sub_one' (hl i) (by linarith)
  simp only [e1, e2] at hle
  exact hle

/-- Strict version: if all `λᵢ > 0` and `λ` is not constant, the inequality is strict for `q < q'`. -/
theorem sum_rpow_lt_sum_rpow {q q' : ℝ} (hq : 1 < q) (hqq : q < q') {l : ι → ℝ}
    (hl : ∀ i, 0 < l i) (hs : ∑ i, l i = 1) (hne : ∃ j k, l j ≠ l k) :
    (∑ i, l i ^ q) ^ ((q' - 1) / (q - 1)) < ∑ i, l i ^ q' := by
  have hr : 1 < (q' - 1) / (q - 1) := by
    rw [lt_div_iff₀ (by linarith)]; linarith
  have hc := strictConvexOn_rpow hr
  have hmem : ∀ i ∈ (Finset.univ : Finset ι), l i ^ (q - 1) ∈ Set.Ici (0 : ℝ) :=
    fun i _ => Real.rpow_nonneg (hl i).le _
  obtain ⟨j, k, hjk⟩ := hne
  have hlt := hc.map_sum_lt (t := Finset.univ) (w := l) (p := fun i => l i ^ (q - 1))
    (fun i _ => hl i) hs hmem ⟨j, Finset.mem_univ j, k, Finset.mem_univ k, by
      intro h
      have := Real.rpow_left_injOn (by linarith : q - 1 ≠ 0) (hl j).le (hl k).le h
      exact hjk this⟩
  have e1 : ∑ i, l i • l i ^ (q - 1) = ∑ i, l i ^ q := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [smul_eq_mul]; exact mul_rpow_sub_one' (hl i).le hq
  have e2 : ∑ i, l i • (l i ^ (q - 1)) ^ ((q' - 1) / (q - 1)) = ∑ i, l i ^ q' := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [smul_eq_mul]
    rw [← Real.rpow_mul (hl i).le]
    have : (q - 1) * ((q' - 1) / (q - 1)) = q' - 1 := by
      have : q - 1 ≠ 0 := (sub_pos.2 hq).ne'
      field_simp
    rw [this]; exact mul_rpow_sub_one' (hl i).le (by linarith)
  simp only [e1, e2] at hlt
  exact hlt

theorem renyiSpec_eq_neg {q : ℝ} (hq : 1 < q) (l : ι → ℝ) :
    renyiSpec q l = -Real.log (∑ i, l i ^ q) / ((q - 1) * Real.log 2) := by
  unfold renyiSpec Real.logb
  have : (1 - q) = -(q - 1) := by ring
  have h1 : q - 1 ≠ 0 := (sub_pos.2 hq).ne'
  rw [this]
  field_simp

/-- **Order monotonicity** of the Rényi entropy for `1 < q ≤ q'`. -/
theorem renyiSpec_anti {q q' : ℝ} (hq : 1 < q) (hqq : q ≤ q') {l : ι → ℝ}
    (hl : ∀ i, 0 ≤ l i) (hs : ∑ i, l i = 1) : renyiSpec q' l ≤ renyiSpec q l := by
  have hpos : 0 < ∑ i, l i ^ q := by
    have : Nonempty ι := by
      by_contra h; rw [not_nonempty_iff] at h; simp at hs
    exact sum_rpow_pos hl hs
  have hle := sum_rpow_le_sum_rpow hq hqq hl hs
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hpos _) hle
  rw [Real.log_rpow hpos] at hlog
  rw [renyiSpec_eq_neg hq, renyiSpec_eq_neg (by linarith)]
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_div_iff₀ (by have : 0 < q' - 1 := by linarith
                          positivity) (by have : 0 < q - 1 := by linarith
                                          positivity)]
  have h1 : 0 < q - 1 := by linarith
  have h2 : 0 < q' - 1 := by linarith
  have := mul_le_mul_of_nonneg_left hlog (mul_pos h1 h2).le
  have e : (q - 1) * (q' - 1) * ((q' - 1) / (q - 1) * Real.log (∑ i, l i ^ q))
      = (q' - 1) ^ 2 * Real.log (∑ i, l i ^ q) := by field_simp
  rw [e] at this
  nlinarith [this, mul_pos l2 l2, mul_pos h1 h2]

end Monotone

/-- info: 'FormalResearch.FourQubitEntropy.renyiSpec_le_logb_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms renyiSpec_le_logb_card

/-- info: 'FormalResearch.FourQubitEntropy.renyiSpec_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms renyiSpec_eq_iff

/-- info: 'FormalResearch.FourQubitEntropy.renyiSpec_anti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms renyiSpec_anti

end FormalResearch.FourQubitEntropy
