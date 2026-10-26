import FormalResearch.FourQubitEntropy.RenyiTwoUp

/-!
# Equality in the high-order Rényi purity deficit for `q > 2`

For `q > 2`, equality in `E_q(ψ) ≤ 5/3 - ⅓ log₂(2P-1)` holds exactly when two cut spectra are
`(1/4)⁴` and the third is `(1/2,1/2,0,0)` (cluster pattern) or `(1,0,0,0)` (Bell-pair-product
pattern); equality in the ceiling `E_q ≤ 5/3` holds exactly for the cluster pattern.

Paper: `cor:fqe-renyi-two-up` (renyi_above_one.tex), the clauses on `q > 2`.
-/

open scoped ComplexConjugate Matrix ComplexOrder

namespace FormalResearch.FourQubitEntropy

open Real

/-- A vector is *uniform on its support*: all its nonzero entries are equal. -/
def UniformOnSupport {ι : Type*} (l : ι → ℝ) : Prop := ∃ c, ∀ i, l i = 0 ∨ l i = c

section Support

variable {ι : Type*} [Fintype ι]

theorem sum_rpow_of_uniform {l : ι → ℝ} {c : ℝ} (hc : ∀ i, l i = 0 ∨ l i = c) (hcpos : 0 < c)
    {q : ℝ} (hq : 1 < q) : ∑ i, l i ^ q = c ^ (q - 1) * ∑ i, l i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases hc i with h | h
  · rw [h, Real.zero_rpow (by linarith : q ≠ 0)]; simp
  · rw [h, Real.rpow_sub_one hcpos.ne']; field_simp

theorem renyiSpec_uniform {l : ι → ℝ} {c : ℝ} (hc : ∀ i, l i = 0 ∨ l i = c) (hcpos : 0 < c)
    (hs : ∑ i, l i = 1) {q : ℝ} (hq : 1 < q) : renyiSpec q l = -Real.logb 2 c := by
  unfold renyiSpec
  rw [sum_rpow_of_uniform hc hcpos hq, hs, mul_one, Real.logb_rpow_eq_mul_logb_of_pos hcpos]
  have : (1 - q) ≠ 0 := by linarith
  field_simp
  ring

/-- For `q > 2`, `H_q(λ) = H_2(λ)` iff `λ` is uniform on its support. -/
theorem renyiSpec_eq_two_iff_uniform {q : ℝ} (hq : 2 < q) {l : ι → ℝ} (hl : ∀ i, 0 ≤ l i)
    (hs : ∑ i, l i = 1) : renyiSpec q l = renyiSpec 2 l ↔ UniformOnSupport l := by
  have hq1 : 1 < q := by linarith
  constructor
  · intro heq
    classical
    have e2 : ∑ i, l i ^ (2 : ℝ) = ∑ i, l i ^ 2 := by simp
    have hpos2 : 0 < ∑ i, l i ^ 2 := by
      have : Nonempty ι := by
        by_contra h; rw [not_nonempty_iff] at h; simp at hs
      rw [← e2]; exact sum_rpow_pos hl hs
    have hposq : 0 < ∑ i, l i ^ q := by
      have : Nonempty ι := by
        by_contra h; rw [not_nonempty_iff] at h; simp at hs
      exact sum_rpow_pos hl hs
    have hkey : (∑ i, l i ^ 2) ^ (q - 1) = ∑ i, l i ^ q := by
      rw [renyiSpec_eq_neg hq1, renyiSpec_eq_neg (by norm_num : (1 : ℝ) < 2), e2] at heq
      have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h1 : 0 < q - 1 := by linarith
      have this : Real.log (∑ i, l i ^ q) = (q - 1) * Real.log (∑ i, l i ^ 2) := by
        have h' := heq
        norm_num at h'
        field_simp at h'
        linarith
      rw [← Real.log_rpow hpos2] at this
      exact (Real.log_injOn_pos (Set.mem_Ioi.2 (Real.rpow_pos_of_pos hpos2 _)) (Set.mem_Ioi.2 hposq)
        this.symm)
    -- strict Jensen on the support
    set T : Finset ι := Finset.univ.filter (fun i => l i ≠ 0) with hT
    have hTpos : ∀ i ∈ T, 0 < l i := by
      intro i hi
      rw [hT, Finset.mem_filter] at hi
      exact lt_of_le_of_ne (hl i) (Ne.symm hi.2)
    have hsumT : ∀ f : ι → ℝ, (∀ i, l i = 0 → f i = 0) → ∑ i ∈ T, f i = ∑ i, f i := by
      intro f hf
      refine Finset.sum_subset (Finset.subset_univ _) ?_
      intro i _ hi
      apply hf
      by_contra h
      exact hi (by rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩)
    have hw1 : ∑ i ∈ T, l i = 1 := by rw [hsumT l (fun i h => h), hs]
    have hmem : ∀ i ∈ T, l i ∈ Set.Ici (0 : ℝ) := fun i _ => hl i
    have hc := strictConvexOn_rpow (by linarith : 1 < q - 1)
    have hiff := hc.map_sum_eq_iff (t := T) (w := l) (p := l) hTpos hw1 hmem
    have e1 : ∑ i ∈ T, l i • l i = ∑ i, l i ^ 2 := by
      simp only [smul_eq_mul]
      rw [hsumT (fun i => l i * l i) (fun i h => by simp [h])]
      simp [sq]
    have e3 : ∑ i ∈ T, l i • (l i) ^ (q - 1) = ∑ i, l i ^ q := by
      simp only [smul_eq_mul]
      rw [hsumT (fun i => l i * l i ^ (q - 1)) (fun i h => by simp [h])]
      exact Finset.sum_congr rfl fun i _ => mul_rpow_sub_one' (hl i) hq1
    simp only [e1, e3] at hiff
    have hall := hiff.1 hkey
    refine ⟨∑ i, l i ^ 2, fun i => ?_⟩
    by_cases h : l i = 0
    · left; exact h
    · right
      have hi : i ∈ T := by rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩
      exact hall i hi
  · rintro ⟨c, hc⟩
    obtain ⟨i, hi⟩ : ∃ i, l i ≠ 0 := by
      by_contra h
      push Not at h
      have : ∑ i, l i = 0 := Finset.sum_eq_zero fun i _ => h i
      linarith
    have hcpos : 0 < c := by
      rcases hc i with h | h
      · exact absurd h hi
      · rw [← h]; exact lt_of_le_of_ne (hl i) (Ne.symm hi)
    rw [renyiSpec_uniform hc hcpos hs hq1, renyiSpec_uniform hc hcpos hs (by norm_num : (1 : ℝ) < 2)]

end Support


/-! ### The third cut -/

theorem sum_sq_of_uniform {l : Fin 2 × Fin 2 → ℝ} {c : ℝ} (hc : ∀ i, l i = 0 ∨ l i = c)
    (hs : ∑ i, l i = 1) : ∑ i, l i ^ 2 = c := by
  have : ∀ i, l i ^ 2 = c * l i := by
    intro i; rcases hc i with h | h <;> rw [h] <;> ring
  simp only [this, ← Finset.mul_sum, hs, mul_one]

/-- A probability vector on four points that is uniform on its support and has `Σ λ² ≥ 1/2` is
`(1/2, 1/2, 0, 0)` or `(1, 0, 0, 0)` up to ordering. -/
theorem rankTwo_of_uniform {l : Fin 2 × Fin 2 → ℝ} (hl : IsProb l) (hu : UniformOnSupport l)
    (hp : 1 / 2 ≤ ∑ i, l i ^ 2) : RankTwoSpec l (1 / 2) ∨ RankTwoSpec l 1 := by
  classical
  obtain ⟨c, hc⟩ := hu
  have hcsq := sum_sq_of_uniform hc hl.2
  have hc12 : 1 / 2 ≤ c := by linarith
  set S : Finset (Fin 2 × Fin 2) := Finset.univ.filter (fun i => l i ≠ 0) with hS
  have hmemS : ∀ i, i ∈ S ↔ l i ≠ 0 := by
    intro i; rw [hS, Finset.mem_filter]; simp
  have hlS : ∀ i ∈ S, l i = c := by
    intro i hi
    rcases hc i with h | h
    · exact absurd h ((hmemS i).1 hi)
    · exact h
  have hsum : ∑ i, l i = S.card * c := by
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by
      by_contra h; exact hi ((hmemS i).2 h))]
    rw [Finset.sum_congr rfl hlS]; simp
  have hn : (S.card : ℝ) * c = 1 := by rw [← hsum]; exact hl.2
  have hnle : S.card ≤ 2 := by
    by_contra h
    push Not at h
    have : (3 : ℝ) ≤ S.card := by exact_mod_cast h
    nlinarith
  have hn0 : S.card ≠ 0 := by
    intro h; rw [h] at hn; simp at hn
  have hout : ∀ j, j ∉ S → l j = 0 := by
    intro j hj; by_contra h; exact hj ((hmemS j).2 h)
  interval_cases hcard : S.card
  · exact absurd rfl hn0
  · right
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 hcard
    have hli : l i = 1 := by
      have : i ∈ S := by rw [hi]; simp
      rw [hlS i this]; simpa using hn
    obtain ⟨k, hk⟩ : ∃ k : Fin 2 × Fin 2, k ≠ i := by
      by_cases h : i = (0, 0)
      · exact ⟨(0, 1), by rw [h]; decide⟩
      · exact ⟨(0, 0), fun h' => h h'.symm⟩
    refine ⟨i, k, hk.symm, hli, ?_, ?_⟩
    · rw [hout k (by rw [hi]; simpa using hk)]; norm_num
    · intro j hj1 hj2
      exact hout j (by rw [hi]; simpa using hj1)
  · left
    obtain ⟨i, k, hik, hik2⟩ := Finset.card_eq_two.1 hcard
    have hc2 : c = 1 / 2 := by push_cast at hn; linarith
    refine ⟨i, k, hik, ?_, ?_, ?_⟩
    · rw [hlS i (by rw [hik2]; simp), hc2]
    · rw [hlS k (by rw [hik2]; simp), hc2]; norm_num
    · intro j hj1 hj2
      exact hout j (by rw [hik2]; simp; exact ⟨hj1, hj2⟩)


/-! ### Equality for `q > 2`: spectrum level -/

/-- The spectrum `(1/4)⁴`. -/
def UniformFour (l : Fin 2 × Fin 2 → ℝ) : Prop := ∀ i, l i = 1 / 4

/-- The three-cut pattern: two cuts uniform-four, the third rank two with spectrum `(a, 1-a, 0, 0)`. -/
def TwoUpPattern (a : ℝ) (l₂ l₃ l₄ : Fin 2 × Fin 2 → ℝ) : Prop :=
  (UniformFour l₂ ∧ UniformFour l₃ ∧ RankTwoSpec l₄ a) ∨
  (UniformFour l₂ ∧ UniformFour l₄ ∧ RankTwoSpec l₃ a) ∨
  (UniformFour l₃ ∧ UniformFour l₄ ∧ RankTwoSpec l₂ a)

theorem sum_sq_uniformFour {l : Fin 2 × Fin 2 → ℝ} (h : UniformFour l) : ∑ i, l i ^ 2 = 1 / 4 := by
  simp [h _, Fin.sum_univ_two, Fintype.sum_prod_type]; norm_num

theorem RankTwoSpec.sum_sq {l : Fin 2 × Fin 2 → ℝ} {a : ℝ} (h : RankTwoSpec l a) :
    ∑ i, l i ^ 2 = a ^ 2 + (1 - a) ^ 2 := by
  have := h.sum_rpow (q := 2) (by norm_num)
  simpa [Real.rpow_two] using this

/-- Attainment: a rank-two cut with `a ∈ {1/2, 1}` and two uniform-four cuts attain the bound. -/
theorem two_up_attain {q a : ℝ} (hq : 2 < q) (ha : a = 1 / 2 ∨ a = 1)
    {la lb lc : Fin 2 × Fin 2 → ℝ} (hb : IsProb lb) (hc : IsProb lc) (hub : UniformFour lb)
    (huc : UniformFour lc) (hra : RankTwoSpec la a) {P : ℝ}
    (hP : P = ∑ i, la i ^ 2 + ∑ i, lb i ^ 2 + ∑ i, lc i ^ 2) :
    (renyiSpec q la + renyiSpec q lb + renyiSpec q lc) / 3 = 5 / 3 - Real.logb 2 (2 * P - 1) / 3 := by
  obtain ⟨-, c2⟩ := renyi_rank_two_core (q := q) (a := a) (by linarith) (by linarith) hb hc hra
  have hmain := c2.2 ⟨hub, huc⟩
  rw [hmain]
  rw [hP, hra.sum_sq, sum_sq_uniformFour hub, sum_sq_uniformFour huc]
  rcases ha with rfl | rfl
  · rw [renyiBin_half (by linarith) (by linarith)]
    norm_num
  · rw [renyiBin_one (by linarith)]
    rw [show 2 * ((1 : ℝ) ^ 2 + (1 - 1) ^ 2 + 1 / 4 + 1 / 4) - 1 = 2 by norm_num,
      Real.logb_self_eq_one (by norm_num)]
    norm_num

/-- **Equality in the high-order purity deficit for `q > 2`** (spectrum level): for three probability
vectors with `P ≥ 1`, equality holds iff two spectra are `(1/4)⁴` and the third is `(1/2,1/2,0,0)` or
`(1,0,0,0)`. -/
theorem two_up_eq_gt {q : ℝ} (hq : 2 < q) {l₂ l₃ l₄ : Fin 2 × Fin 2 → ℝ} (h₂ : IsProb l₂)
    (h₃ : IsProb l₃) (h₄ : IsProb l₄) (hP : 1 ≤ ∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2) :
    (renyiSpec q l₂ + renyiSpec q l₃ + renyiSpec q l₄) / 3 =
        5 / 3 - Real.logb 2 (2 * (∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2) - 1) / 3 ↔
      TwoUpPattern (1 / 2) l₂ l₃ l₄ ∨ TwoUpPattern 1 l₂ l₃ l₄ := by
  have hq1 : (1 : ℝ) < 2 := by norm_num
  constructor
  · intro heq
    have m2 := renyiSpec_anti hq1 hq.le h₂.1 h₂.2
    have m3 := renyiSpec_anti hq1 hq.le h₃.1 h₃.2
    have m4 := renyiSpec_anti hq1 hq.le h₄.1 h₄.2
    obtain ⟨core, coreiff⟩ := two_up_core_two h₂ h₃ h₄
    have e2 : (renyiSpec 2 l₂ + renyiSpec 2 l₃ + renyiSpec 2 l₄) / 3 =
        5 / 3 - Real.logb 2 (2 * (∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2) - 1) / 3 := by
      linarith
    have two := coreiff.1 e2
    have u2 := (renyiSpec_eq_two_iff_uniform hq h₂.1 h₂.2).1 (by linarith)
    have u3 := (renyiSpec_eq_two_iff_uniform hq h₃.1 h₃.2).1 (by linarith)
    have u4 := (renyiSpec_eq_two_iff_uniform hq h₄.1 h₄.2).1 (by linarith)
    rcases two with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · have sa := sum_sq_uniformFour a
      have sb := sum_sq_uniformFour b
      rcases rankTwo_of_uniform h₄ u4 (by linarith) with r | r
      · exact Or.inl (Or.inl ⟨a, b, r⟩)
      · exact Or.inr (Or.inl ⟨a, b, r⟩)
    · have sa := sum_sq_uniformFour a
      have sb := sum_sq_uniformFour b
      rcases rankTwo_of_uniform h₃ u3 (by linarith) with r | r
      · exact Or.inl (Or.inr (Or.inl ⟨a, b, r⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨a, b, r⟩))
    · have sa := sum_sq_uniformFour a
      have sb := sum_sq_uniformFour b
      rcases rankTwo_of_uniform h₂ u2 (by linarith) with r | r
      · exact Or.inl (Or.inr (Or.inr ⟨a, b, r⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨a, b, r⟩))
  · rintro ((⟨a, b, r⟩ | ⟨a, b, r⟩ | ⟨a, b, r⟩) | (⟨a, b, r⟩ | ⟨a, b, r⟩ | ⟨a, b, r⟩))
    · have := two_up_attain hq (Or.inl rfl) h₂ h₃ a b r
        (P := ∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2) (by ring)
      linarith
    · have := two_up_attain hq (Or.inl rfl) h₂ h₄ a b r
        (P := ∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2) (by ring)
      linarith
    · have := two_up_attain hq (Or.inl rfl) h₃ h₄ a b r
        (P := ∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2) (by ring)
      linarith
    · have := two_up_attain hq (Or.inr rfl) h₂ h₃ a b r
        (P := ∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2) (by ring)
      linarith
    · have := two_up_attain hq (Or.inr rfl) h₂ h₄ a b r
        (P := ∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2) (by ring)
      linarith
    · have := two_up_attain hq (Or.inr rfl) h₃ h₄ a b r
        (P := ∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2) (by ring)
      linarith

theorem TwoUpPattern.sum_sq {a : ℝ} {l₂ l₃ l₄ : Fin 2 × Fin 2 → ℝ} (h : TwoUpPattern a l₂ l₃ l₄) :
    ∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2 = 1 / 2 + (a ^ 2 + (1 - a) ^ 2) := by
  rcases h with ⟨u, v, r⟩ | ⟨u, v, r⟩ | ⟨u, v, r⟩
  · rw [sum_sq_uniformFour u, sum_sq_uniformFour v, r.sum_sq]; ring
  · rw [sum_sq_uniformFour u, sum_sq_uniformFour v, r.sum_sq]; ring
  · rw [sum_sq_uniformFour u, sum_sq_uniformFour v, r.sum_sq]; ring

/-- **Ceiling equality for `q > 2`** (spectrum level): `E_q = 5/3` iff two spectra are `(1/4)⁴` and
the third is `(1/2, 1/2, 0, 0)` (cluster pattern). -/
theorem two_up_ceiling_gt {q : ℝ} (hq : 2 < q) {l₂ l₃ l₄ : Fin 2 × Fin 2 → ℝ} (h₂ : IsProb l₂)
    (h₃ : IsProb l₃) (h₄ : IsProb l₄) (hP : 1 ≤ ∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2) :
    (renyiSpec q l₂ + renyiSpec q l₃ + renyiSpec q l₄) / 3 = 5 / 3 ↔ TwoUpPattern (1 / 2) l₂ l₃ l₄ := by
  have hq1 : (1 : ℝ) < 2 := by norm_num
  have heqiff := two_up_eq_gt hq h₂ h₃ h₄ hP
  constructor
  · intro heq
    have m2 := renyiSpec_anti hq1 hq.le h₂.1 h₂.2
    have m3 := renyiSpec_anti hq1 hq.le h₃.1 h₃.2
    have m4 := renyiSpec_anti hq1 hq.le h₄.1 h₄.2
    obtain ⟨core, -⟩ := two_up_core_two h₂ h₃ h₄
    have hnn : 0 ≤ Real.logb 2 (2 * (∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2) - 1) :=
      Real.logb_nonneg (by norm_num) (by linarith)
    have hlog : Real.logb 2 (2 * (∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2) - 1) = 0 := by
      linarith
    have hP1 : ∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2 = 1 := by
      have h' : 2 * (∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2) - 1 = 1 := by
        have := (Real.logb_eq_iff_rpow_eq (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
          (by linarith : 0 < 2 * (∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2) - 1)).1 hlog
        simpa using this.symm
      linarith
    have : (renyiSpec q l₂ + renyiSpec q l₃ + renyiSpec q l₄) / 3 =
        5 / 3 - Real.logb 2 (2 * (∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2) - 1) / 3 := by
      rw [hlog]; linarith
    rcases heqiff.1 this with h | h
    · exact h
    · have := h.sum_sq
      norm_num at this
      linarith
  · intro h
    have hP1 := h.sum_sq
    have := heqiff.2 (Or.inl h)
    rw [this]
    have : 2 * (∑ i, l₂ i ^ 2 + ∑ i, l₃ i ^ 2 + ∑ i, l₄ i ^ 2) - 1 = 1 := by rw [hP1]; norm_num
    rw [this]; simp

/-! ### The theorem for four-qubit vectors -/

/-- **Equality in `cor:fqe-renyi-two-up` for `q > 2`**: equality in the first bound holds iff two of
the three balanced cut spectra are `(1/4)⁴` and the third is `(1/2,1/2,0,0)` or `(1,0,0,0)`. -/
theorem renyi_two_up_eq_gt {q : ℝ} (hq : 2 < q) {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    meanRenyi q ψ = 5 / 3 - Real.logb 2 (2 * purity ψ - 1) / 3 ↔
      TwoUpPattern (1 / 2) (red12_herm ψ).eigenvalues (red13_herm ψ).eigenvalues
        (red14_herm ψ).eigenvalues ∨
      TwoUpPattern 1 (red12_herm ψ).eigenvalues (red13_herm ψ).eigenvalues
        (red14_herm ψ).eigenvalues := by
  have hP := purity_ge ψ
  rw [hψ] at hP
  have hP1 : 1 ≤ purity ψ := by nlinarith
  rw [purity_eq_sum_sq] at hP1 ⊢
  exact two_up_eq_gt hq (isProb12 hψ) (isProb13 hψ) (isProb14 hψ) hP1

/-- **Ceiling equality for `q > 2`** (`cor:fqe-renyi-two-up`): `E_q(ψ) = 5/3` iff the balanced cut
spectra are `(1/2,1/2,0,0), (1/4)⁴, (1/4)⁴` up to ordering of the cuts. -/
theorem renyi_two_up_ceiling_gt {q : ℝ} (hq : 2 < q) {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    meanRenyi q ψ = 5 / 3 ↔
      TwoUpPattern (1 / 2) (red12_herm ψ).eigenvalues (red13_herm ψ).eigenvalues
        (red14_herm ψ).eigenvalues := by
  have hP := purity_ge ψ
  rw [hψ] at hP
  have hP1 : 1 ≤ purity ψ := by nlinarith
  rw [purity_eq_sum_sq] at hP1
  exact two_up_ceiling_gt hq (isProb12 hψ) (isProb13 hψ) (isProb14 hψ) hP1

/-- info: 'FormalResearch.FourQubitEntropy.renyiSpec_eq_two_iff_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms renyiSpec_eq_two_iff_uniform

/-- info: 'FormalResearch.FourQubitEntropy.two_up_eq_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_up_eq_gt

/-- info: 'FormalResearch.FourQubitEntropy.two_up_ceiling_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_up_ceiling_gt

/-- info: 'FormalResearch.FourQubitEntropy.renyi_two_up_eq_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms renyi_two_up_eq_gt

/-- info: 'FormalResearch.FourQubitEntropy.renyi_two_up_ceiling_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms renyi_two_up_ceiling_gt

end FormalResearch.FourQubitEntropy
