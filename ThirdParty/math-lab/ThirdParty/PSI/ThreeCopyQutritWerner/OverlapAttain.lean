module

public import ThreeCopyQutritWerner.Overlap

@[expose] public section


/-!
# The overlap bound is attained

Manuscript proof of Corollary 2.2: a product state attains the overlap bound `1/2`.
Discarding the three copies and preparing `|00⟩` is a trace-preserving
separable operation (Kraus pairs `|0⟩⟨a| ⊗ |0⟩⟨b|` over all basis pairs `(a, b)`); on a
unit-trace input its output is `|00⟩⟨00|`, whose overlap with `Φ = (|00⟩ + |11⟩)/√2` is `1/2`.
-/

noncomputable section

namespace ThreeCopyQutritWerner

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The matrix unit `|0⟩⟨a|` from an arbitrary finite type to one qubit. -/
def prepZero {ι : Type*} [DecidableEq ι] (a : ι) : Matrix (Fin 2) ι ℂ :=
  Matrix.of fun i p => if i = 0 then (if p = a then 1 else 0) else 0

theorem sum_star_prepZero_mul {ι : Type*} [DecidableEq ι] (a p p' : ι) :
    ∑ i : Fin 2, star (prepZero a i p') * prepZero a i p =
      (if p' = a then 1 else 0) * (if p = a then 1 else 0) := by
  simp only [prepZero, Matrix.of_apply, Fin.sum_univ_two]
  by_cases h1 : p' = a <;> by_cases h2 : p = a <;> simp [h1, h2]

theorem sum_indicator_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (p p' : ι) :
    ∑ a : ι, (if p' = a then (1 : ℂ) else 0) * (if p = a then 1 else 0) =
      if p = p' then 1 else 0 := by
  rw [Finset.sum_eq_single p']
  · by_cases h : p = p' <;> simp [h]
  · intro a _ ha
    simp [Ne.symm ha]
  · intro h
    exact absurd (Finset.mem_univ p') h

/-- The enumeration of basis pairs `(a, b)` used to index the Kraus pairs. -/
def discardPair (k : Fin (Fintype.card ((m × m × m) × (n × n × n)))) :
    (m × m × m) × (n × n × n) :=
  (Fintype.equivFin ((m × m × m) × (n × n × n))).symm k

theorem sum_discardPair (f : (m × m × m) × (n × n × n) → ℂ) :
    ∑ k, f (discardPair k) = ∑ w, f w :=
  (Fintype.equivFin ((m × m × m) × (n × n × n))).symm.sum_comp f

/-- Kraus pairs `|0⟩⟨a| ⊗ |0⟩⟨b|`, indexed by `Fin K` through an enumeration of the pairs. -/
def discardKraus :
    (Fin (Fintype.card ((m × m × m) × (n × n × n))) → Matrix (Fin 2) (m × m × m) ℂ) ×
      (Fin (Fintype.card ((m × m × m) × (n × n × n))) → Matrix (Fin 2) (n × n × n) ℂ) :=
  (fun k => prepZero (discardPair k).1, fun k => prepZero (discardPair k).2)

/-- The discard-and-prepare operation is trace preserving. -/
theorem discardKraus_tp (u v : (m × m × m) × (n × n × n)) :
    ∑ k, (∑ i : Fin 2, star ((discardKraus (m := m) (n := n)).1 k i v.1) *
        (discardKraus (m := m) (n := n)).1 k i u.1) *
      (∑ j : Fin 2, star ((discardKraus (m := m) (n := n)).2 k j v.2) *
        (discardKraus (m := m) (n := n)).2 k j u.2) = if u = v then 1 else 0 := by
  have h : ∀ k, (∑ i : Fin 2, star ((discardKraus (m := m) (n := n)).1 k i v.1) *
        (discardKraus (m := m) (n := n)).1 k i u.1) *
      (∑ j : Fin 2, star ((discardKraus (m := m) (n := n)).2 k j v.2) *
        (discardKraus (m := m) (n := n)).2 k j u.2) =
      ((if v.1 = (discardPair k).1 then 1 else 0) * (if u.1 = (discardPair k).1 then 1 else 0)) *
        ((if v.2 = (discardPair k).2 then 1 else 0) * (if u.2 = (discardPair k).2 then 1 else 0)) := by
    intro k
    simp only [discardKraus]
    rw [sum_star_prepZero_mul, sum_star_prepZero_mul]
  rw [Finset.sum_congr rfl fun k _ => h k]
  rw [sum_discardPair (fun w : (m × m × m) × (n × n × n) =>
    ((if v.1 = w.1 then (1 : ℂ) else 0) * (if u.1 = w.1 then 1 else 0)) *
      ((if v.2 = w.2 then 1 else 0) * (if u.2 = w.2 then 1 else 0)))]
  rw [Fintype.sum_prod_type]
  have hfac : (∑ a : m × m × m, ∑ b : n × n × n,
      ((if v.1 = a then (1 : ℂ) else 0) * (if u.1 = a then 1 else 0)) *
        ((if v.2 = b then 1 else 0) * (if u.2 = b then 1 else 0))) =
      (∑ a : m × m × m, (if v.1 = a then (1 : ℂ) else 0) * (if u.1 = a then 1 else 0)) *
        (∑ b : n × n × n, (if v.2 = b then (1 : ℂ) else 0) * (if u.2 = b then 1 else 0)) :=
    (Finset.sum_mul_sum _ _ _ _).symm
  rw [hfac, sum_indicator_mul, sum_indicator_mul]
  by_cases h1 : u.1 = v.1 <;> by_cases h2 : u.2 = v.2
  · have huv : u = v := Prod.ext h1 h2
    simp [h1, h2, huv]
  · have huv : u ≠ v := fun h => h2 (congrArg Prod.snd h)
    simp [h2, huv]
  · have huv : u ≠ v := fun h => h1 (congrArg Prod.fst h)
    simp [h1, huv]
  · have huv : u ≠ v := fun h => h1 (congrArg Prod.fst h)
    simp [h1, huv]

/-- Entries of the output of discard-and-prepare: `Tr(ρ^{⊗3}) |00⟩⟨00|`. -/
theorem sepOutput_discardKraus_apply (ρ : Matrix (m × n) (m × n) ℂ) (x y : Fin 2 × Fin 2) :
    sepOutput (discardKraus (m := m) (n := n)).1 (discardKraus (m := m) (n := n)).2 ρ x y =
      (if x = (0, 0) then 1 else 0) * (if y = (0, 0) then 1 else 0) * (tripleCopy ρ).trace := by
  have hk : ∀ k, localFilter ((discardKraus (m := m) (n := n)).1 k)
      ((discardKraus (m := m) (n := n)).2 k) (tripleCopy ρ) x y =
      (if x = (0, 0) then 1 else 0) * (if y = (0, 0) then 1 else 0) *
        tripleCopy ρ (discardPair k) (discardPair k) := by
    intro k
    simp only [localFilter, discardKraus, prepZero, Matrix.of_apply]
    obtain ⟨x₁, x₂⟩ := x
    obtain ⟨y₁, y₂⟩ := y
    by_cases hx : x₁ = 0 ∧ x₂ = 0
    · by_cases hy : y₁ = 0 ∧ y₂ = 0
      · obtain ⟨rfl, rfl⟩ := hx
        obtain ⟨rfl, rfl⟩ := hy
        rw [Finset.sum_eq_single (discardPair k)]
        · rw [Finset.sum_eq_single (discardPair k)]
          · simp
          · intro q _ hq
            have : ¬ (q.1 = (discardPair k).1 ∧ q.2 = (discardPair k).2) := fun h => hq (Prod.ext h.1 h.2)
            by_cases h1 : q.1 = (discardPair k).1
            · simp [h1, show q.2 ≠ (discardPair k).2 from fun h2 => this ⟨h1, h2⟩]
            · simp [h1]
          · intro h
            exact absurd (Finset.mem_univ _) h
        · intro p _ hp
          have : ¬ (p.1 = (discardPair k).1 ∧ p.2 = (discardPair k).2) := fun h => hp (Prod.ext h.1 h.2)
          apply Finset.sum_eq_zero
          intro q _
          by_cases h1 : p.1 = (discardPair k).1
          · simp [h1, show p.2 ≠ (discardPair k).2 from fun h2 => this ⟨h1, h2⟩]
          · simp [h1]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · have hy' : ¬ ((y₁, y₂) = ((0 : Fin 2), (0 : Fin 2))) := by
          intro h
          exact hy ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
        rw [if_neg hy', mul_zero, zero_mul]
        apply Finset.sum_eq_zero
        intro p _
        apply Finset.sum_eq_zero
        intro q _
        by_cases h1 : y₁ = 0
        · have h2 : y₂ ≠ 0 := fun h2 => hy ⟨h1, h2⟩
          simp [h2]
        · simp [h1]
    · have hx' : ¬ ((x₁, x₂) = ((0 : Fin 2), (0 : Fin 2))) := by
        intro h
        exact hx ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      rw [if_neg hx', zero_mul, zero_mul]
      apply Finset.sum_eq_zero
      intro p _
      apply Finset.sum_eq_zero
      intro q _
      by_cases h1 : x₁ = 0
      · have h2 : x₂ ≠ 0 := fun h2 => hx ⟨h1, h2⟩
        simp [h2]
      · simp [h1]
  unfold sepOutput
  rw [Matrix.sum_apply, Finset.sum_congr rfl fun k _ => hk k, ← Finset.mul_sum,
    sum_discardPair (fun w => tripleCopy ρ w w)]
  rfl

/-- Corollary 2.2, attainment of the overlap bound: discard-and-prepare is a trace-preserving
separable operation whose output has overlap exactly `1/2` with `Φ` when `Tr ρ = 1`. -/
theorem maxEntOverlap_sepOutput_discardKraus (ρ : Matrix (m × n) (m × n) ℂ)
    (hρ : ρ.trace = 1) :
    maxEntOverlap (sepOutput (discardKraus (m := m) (n := n)).1
      (discardKraus (m := m) (n := n)).2 ρ) = 1 / 2 := by
  have ht : (tripleCopy ρ).trace = 1 := by rw [trace_tripleCopy, hρ, one_pow]
  unfold maxEntOverlap expectation
  simp only [sepOutput_discardKraus_apply, ht, mul_one, omegaVec₂, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  norm_num

/-- At `d = 3` for every `-1 ≤ α ≤ 1`: some trace-preserving separable operation on three
copies of `ρ_{3,α}` has overlap exactly `1/2` with the maximally entangled two-qubit state. -/
theorem werner_three_exists_maxEntOverlap_eq_half {α : ℝ} (h1 : α ≤ 1) :
    ∃ (K : ℕ) (A : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
      (B : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ),
      (∀ u v : (Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3),
        ∑ k, (∑ i : Fin 2, star (A k i v.1) * A k i u.1) *
          (∑ j : Fin 2, star (B k j v.2) * B k j u.2) = if u = v then 1 else 0) ∧
      maxEntOverlap (sepOutput A B (werner 3 α)) = 1 / 2 :=
  ⟨_, (discardKraus (m := Fin 3) (n := Fin 3)).1, (discardKraus (m := Fin 3) (n := Fin 3)).2,
    discardKraus_tp, maxEntOverlap_sepOutput_discardKraus _
      (trace_werner 3 α (by norm_num) (by intro h; norm_num at h; linarith))⟩

end ThreeCopyQutritWerner

end
