module

public import FormalResearch.Wigner.ThreeJOrth

/-!
# Completeness of the `3j` symbol in the rank (DLMF 34.3.16)

Fix `j₂ j₃ M` and put `a = 2j₂`, `b = 2j₃`, `P = j₂+j₃+M`, `Q = j₂+j₃-M` (natural numbers).  The
admissible ranks are `L = j₂+j₃-t`, `0 ≤ t ≤ min(a,b,P,Q)`, and the admissible projections are
`m = j₂-k`, `max(0,P-b) ≤ k ≤ min(a,P)`; both families have `n = min(a,b,P,Q)+1` elements.  The matrix
`A_{L,m} = √(2L+1) (L j₂ j₃; M m -M-m)` is therefore square, and by `threeJ_orthogonality` it has
orthonormal rows, hence orthonormal columns:
`∑_L (2L+1)(L j₂ j₃; M m -M-m)(L j₂ j₃; M m' -M-m') = δ_{mm'}` (`threeJ_completeness`).
-/

@[expose] public section

namespace FormalResearch.Wigner

section
variable {j₂ j₃ M : ℚ} {a b P Q : ℕ}

/-- The number of admissible ranks (equivalently of admissible projections). -/
def nrk (a b P Q : ℕ) : ℕ := min (min a b) (min P Q) + 1

lemma ladm_of_nat (ha : 2 * j₂ = a) (hb : 2 * j₃ = b) (hP : j₂ + j₃ + M = P)
    (hQ : j₂ + j₃ - M = Q) {t : ℕ} (h : t ≤ min (min a b) (min P Q)) :
    LAdm j₂ j₃ M (j₂ + j₃ - t) := by
  have ta : t ≤ a := le_trans h (le_trans (min_le_left _ _) (min_le_left _ _))
  have tb : t ≤ b := le_trans h (le_trans (min_le_left _ _) (min_le_right _ _))
  have tP : t ≤ P := le_trans h (le_trans (min_le_right _ _) (min_le_left _ _))
  have tQ : t ≤ Q := le_trans h (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨⟨⟨a - t, ?_⟩, ⟨b - t, ?_⟩, ⟨t, ?_⟩⟩, ⟨P - t, ?_⟩, ⟨Q - t, ?_⟩⟩
  · push_cast [Nat.cast_sub ta]; linarith
  · push_cast [Nat.cast_sub tb]; linarith
  · ring
  · push_cast [Nat.cast_sub tP]; linarith
  · push_cast [Nat.cast_sub tQ]; linarith

lemma madm_of_nat (ha : 2 * j₂ = a) (hb : 2 * j₃ = b) (hP : j₂ + j₃ + M = P)
    {k : ℕ} (hk : k ≤ a) (hkP : k ≤ P) (hPb : P ≤ b + k) : MAdm j₂ j₃ M (j₂ - k) := by
  refine ⟨⟨a - k, ?_⟩, ⟨k, ?_⟩, ⟨b + k - P, ?_⟩, ⟨P - k, ?_⟩⟩
  · push_cast [Nat.cast_sub hk]; linarith
  · ring
  · push_cast [Nat.cast_sub hPb]; linarith
  · push_cast [Nat.cast_sub hkP]; linarith

lemma madm_imp (ha : 2 * j₂ = a) (hb : 2 * j₃ = b) (hP : j₂ + j₃ + M = P) {m : ℚ}
    (h : MAdm j₂ j₃ M m) : ∃ k : ℕ, m = j₂ - k ∧ k ≤ a ∧ k ≤ P ∧ P ≤ b + k := by
  obtain ⟨⟨c1, hc1⟩, ⟨k, hk⟩, ⟨c3, hc3⟩, ⟨c4, hc4⟩⟩ := h
  refine ⟨k, by linarith, ?_, ?_, ?_⟩
  · have : (k : ℚ) ≤ a := by
      have : (0 : ℚ) ≤ c1 := by positivity
      linarith
    exact_mod_cast this
  · have : (k : ℚ) ≤ P := by
      have : (0 : ℚ) ≤ c4 := by positivity
      linarith
    exact_mod_cast this
  · have : (P : ℚ) ≤ b + k := by
      have : (0 : ℚ) ≤ c3 := by positivity
      linarith
    exact_mod_cast this

/-- First admissible rank and projection. -/
def Lbot (j₂ j₃ : ℚ) (n : ℕ) : ℚ := j₂ + j₃ - ((n : ℚ) - 1)

def mbot (j₂ : ℚ) (a P : ℕ) : ℚ := j₂ - (min a P : ℕ)

/-- The projection lattice `m₀ + j`, `j < n`, covers every admissible projection. -/
lemma mlat_cover (ha : 2 * j₂ = a) (hb : 2 * j₃ = b) (hP : j₂ + j₃ + M = P) (hQ : j₂ + j₃ - M = Q)
    {m : ℚ} (h : MAdm j₂ j₃ M m) :
    ∃ j : ℕ, j < nrk a b P Q ∧ m = mbot j₂ a P + j := by
  obtain ⟨k, hm, hka, hkP, hPb⟩ := madm_imp ha hb hP h
  have hPQ : P + Q = a + b := by
    have : ((P + Q : ℕ) : ℚ) = ((a + b : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  refine ⟨min a P - k, ?_, ?_⟩
  · unfold nrk; omega
  · unfold mbot
    have : k ≤ min a P := le_min hka hkP
    push_cast [Nat.cast_sub this]
    rw [hm]; ring

lemma mlat_adm (ha : 2 * j₂ = a) (hb : 2 * j₃ = b) (hP : j₂ + j₃ + M = P) (hQ : j₂ + j₃ - M = Q)
    {j : ℕ} (hj : j < nrk a b P Q) : MAdm j₂ j₃ M (mbot j₂ a P + j) := by
  have hPQ : P + Q = a + b := by
    have : ((P + Q : ℕ) : ℚ) = ((a + b : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  unfold nrk at hj
  have hjm : j ≤ min a P := by omega
  have := madm_of_nat ha hb hP (k := min a P - j) (by omega) (by omega) (by omega)
  convert this using 1
  unfold mbot
  push_cast [Nat.cast_sub hjm]
  ring

lemma rlat_adm (ha : 2 * j₂ = a) (hb : 2 * j₃ = b) (hP : j₂ + j₃ + M = P) (hQ : j₂ + j₃ - M = Q)
    {i : ℕ} (hi : i < nrk a b P Q) : LAdm j₂ j₃ M (Lbot j₂ j₃ (nrk a b P Q) + i) := by
  unfold nrk at hi
  have h1 := ladm_of_nat ha hb hP hQ (t := min (min a b) (min P Q) - i) (by omega)
  convert h1 using 1
  unfold Lbot nrk
  have : i ≤ min (min a b) (min P Q) := by omega
  push_cast [Nat.cast_sub this]
  ring

/-- The `m`-lattice sum over the admissible projections is `∑_{j<n} f (m₀ + j)`. -/
lemma msum_eq_range (ha : 2 * j₂ = a) (hb : 2 * j₃ = b) (hP : j₂ + j₃ + M = P)
    (hQ : j₂ + j₃ - M = Q) {f : ℚ → ℝ} (hf : ∀ m, f m ≠ 0 → MAdm j₂ j₃ M m) :
    msum j₂ f = ∑ j ∈ Finset.range (nrk a b P Q), f (mbot j₂ a P + j) := by
  have hPQ : P + Q = a + b := by
    have : ((P + Q : ℕ) : ℚ) = ((a + b : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  unfold msum
  have hsupp : (Function.support fun k : ℕ => f (j₂ - k)) ⊆
      ↑((Finset.range (nrk a b P Q)).image (fun j : ℕ => min a P - j)) := by
    intro k hk
    simp only [Function.mem_support, ne_eq] at hk
    obtain ⟨k', hk', hka, hkP, hPb⟩ := madm_imp ha hb hP (hf _ hk)
    have : k' = k := by
      have : (k' : ℚ) = k := by linarith
      exact_mod_cast this
    subst this
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    refine ⟨min a P - k', ?_, ?_⟩
    · unfold nrk; omega
    · omega
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < nrk a b P Q := Finset.mem_range.mp hj
    have hjm : j ≤ min a P := by unfold nrk at hj'; omega
    congr 1
    unfold mbot
    push_cast [Nat.cast_sub hjm]
    ring
  · intro j hj l hl h
    have hj' : j < nrk a b P Q := Finset.mem_range.mp hj
    have hl' : l < nrk a b P Q := Finset.mem_range.mp hl
    unfold nrk at hj' hl'
    simp only at h
    omega

/-- **Orthogonality on the explicit lattices**: for `i, i' < n`,
`∑_{j<n} tt(L_i, m_j) tt(L_{i'}, m_j) = δ_{ii'}/(2L_i+1)`. -/
lemma tt_orth_range (ha : 2 * j₂ = a) (hb : 2 * j₃ = b) (hP : j₂ + j₃ + M = P)
    (hQ : j₂ + j₃ - M = Q) {i i' : ℕ} (hi : i < nrk a b P Q) (hi' : i' < nrk a b P Q) :
    ∑ j ∈ Finset.range (nrk a b P Q),
        tt j₂ j₃ M (Lbot j₂ j₃ (nrk a b P Q) + i) (mbot j₂ a P + j) *
          tt j₂ j₃ M (Lbot j₂ j₃ (nrk a b P Q) + i') (mbot j₂ a P + j) =
      if i = i' then 1 / (2 * ((Lbot j₂ j₃ (nrk a b P Q) + i : ℚ) : ℝ) + 1) else 0 := by
  have hL := rlat_adm ha hb hP hQ hi
  have hL' := rlat_adm ha hb hP hQ hi'
  have hmain := threeJ_orthogonality j₂ j₃ M _ _ hL.1 hL.2.1 hL.2.2 hL'.1 hL'.2.1 hL'.2.2
  have hOA : ∑ᶠ k : ℕ, threeJ (Lbot j₂ j₃ (nrk a b P Q) + i) j₂ j₃ M (j₂ - k) (-M - (j₂ - k)) *
        threeJ (Lbot j₂ j₃ (nrk a b P Q) + i') j₂ j₃ M (j₂ - k) (-M - (j₂ - k)) =
      msum j₂ (fun m => tt j₂ j₃ M (Lbot j₂ j₃ (nrk a b P Q) + i) m *
        tt j₂ j₃ M (Lbot j₂ j₃ (nrk a b P Q) + i') m) := rfl
  rw [hOA, msum_eq_range ha hb hP hQ] at hmain
  · rw [hmain]
    have : (Lbot j₂ j₃ (nrk a b P Q) + i = Lbot j₂ j₃ (nrk a b P Q) + i') ↔ i = i' := by
      constructor
      · intro h; have : (i : ℚ) = i' := by linarith
        exact_mod_cast this
      · intro h; rw [h]
    simp only [this]
  · intro m hm
    by_contra hnot
    apply hm
    rw [tt_eq_zero_of_not_madm _ hnot]; ring

/-- A square real matrix with orthonormal rows has orthonormal columns. -/
lemma cols_of_rows (n : ℕ) (A : Fin n → Fin n → ℝ)
    (h : ∀ i i' : Fin n, ∑ k : Fin n, A i k * A i' k = if i = i' then 1 else 0)
    (k k' : Fin n) : ∑ i : Fin n, A i k * A i k' = if k = k' then 1 else 0 := by
  have h1 : (Matrix.of A) * (Matrix.of A).transpose = 1 := by
    ext i i'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    exact h i i'
  have h2 : (Matrix.of A).transpose * (Matrix.of A) = 1 := mul_eq_one_comm.mp h1
  have := congrFun (congrFun h2 k) k'
  simpa [Matrix.mul_apply, Matrix.one_apply] using this

/-- **Completeness of the `3j` symbol (DLMF 34.3.16).**  With `a = 2j₂`, `b = 2j₃`,
`P = j₂+j₃+M`, `Q = j₂+j₃-M` natural numbers, `n = min(a,b,P,Q)+1` is both the number of admissible
ranks `L = L₀ + i` and of admissible projections `m = m₀ + j`, and for `j, j' < n`
`∑_{i<n} (2L_i+1) (L_i j₂ j₃; M m_j -M-m_j)(L_i j₂ j₃; M m_{j'} -M-m_{j'}) = δ_{jj'}`. -/
theorem threeJ_completeness (ha : 2 * j₂ = a) (hb : 2 * j₃ = b) (hP : j₂ + j₃ + M = P)
    (hQ : j₂ + j₃ - M = Q) {j j' : ℕ} (hj : j < nrk a b P Q) (hj' : j' < nrk a b P Q) :
    ∑ i ∈ Finset.range (nrk a b P Q),
        (2 * ((Lbot j₂ j₃ (nrk a b P Q) + i : ℚ) : ℝ) + 1) *
          (tt j₂ j₃ M (Lbot j₂ j₃ (nrk a b P Q) + i) (mbot j₂ a P + j) *
            tt j₂ j₃ M (Lbot j₂ j₃ (nrk a b P Q) + i) (mbot j₂ a P + j')) =
      if j = j' then 1 else 0 := by
  obtain ⟨n, hn⟩ : ∃ n, n = nrk a b P Q := ⟨_, rfl⟩
  rw [← hn] at hj hj' ⊢
  have horth : ∀ i i' : ℕ, i < n → i' < n → ∑ k ∈ Finset.range n,
      tt j₂ j₃ M (Lbot j₂ j₃ n + i) (mbot j₂ a P + k) *
        tt j₂ j₃ M (Lbot j₂ j₃ n + i') (mbot j₂ a P + k) =
      if i = i' then 1 / (2 * ((Lbot j₂ j₃ n + i : ℚ) : ℝ) + 1) else 0 := by
    intro i i' hi hi'
    rw [hn] at hi hi' ⊢
    exact tt_orth_range ha hb hP hQ hi hi'
  have hpos : ∀ i : ℕ, i < n → (0 : ℝ) < 2 * ((Lbot j₂ j₃ n + i : ℚ) : ℝ) + 1 := by
    intro i hi
    have h0 := (rlat_adm ha hb hP hQ (hn ▸ hi)).nonneg
    have h2 : (0 : ℝ) ≤ ((Lbot j₂ j₃ (nrk a b P Q) + i : ℚ) : ℝ) := by exact_mod_cast h0
    rw [← hn] at h2
    linarith
  have hrows : ∀ i i' : Fin n, ∑ k : Fin n,
      (Real.sqrt (2 * ((Lbot j₂ j₃ n + (i : ℕ) : ℚ) : ℝ) + 1) *
        tt j₂ j₃ M (Lbot j₂ j₃ n + (i : ℕ)) (mbot j₂ a P + (k : ℕ))) *
      (Real.sqrt (2 * ((Lbot j₂ j₃ n + (i' : ℕ) : ℚ) : ℝ) + 1) *
        tt j₂ j₃ M (Lbot j₂ j₃ n + (i' : ℕ)) (mbot j₂ a P + (k : ℕ))) =
      if i = i' then 1 else 0 := by
    intro i i'
    have h := horth i i' i.2 i'.2
    have e : ∑ k : Fin n, (Real.sqrt (2 * ((Lbot j₂ j₃ n + (i : ℕ) : ℚ) : ℝ) + 1) *
          tt j₂ j₃ M (Lbot j₂ j₃ n + (i : ℕ)) (mbot j₂ a P + (k : ℕ))) *
        (Real.sqrt (2 * ((Lbot j₂ j₃ n + (i' : ℕ) : ℚ) : ℝ) + 1) *
          tt j₂ j₃ M (Lbot j₂ j₃ n + (i' : ℕ)) (mbot j₂ a P + (k : ℕ))) =
        Real.sqrt (2 * ((Lbot j₂ j₃ n + (i : ℕ) : ℚ) : ℝ) + 1) *
          Real.sqrt (2 * ((Lbot j₂ j₃ n + (i' : ℕ) : ℚ) : ℝ) + 1) *
        ∑ k : Fin n, tt j₂ j₃ M (Lbot j₂ j₃ n + (i : ℕ)) (mbot j₂ a P + (k : ℕ)) *
          tt j₂ j₃ M (Lbot j₂ j₃ n + (i' : ℕ)) (mbot j₂ a P + (k : ℕ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, Fin.sum_univ_eq_sum_range (fun k : ℕ =>
        tt j₂ j₃ M (Lbot j₂ j₃ n + (i : ℕ)) (mbot j₂ a P + k) *
          tt j₂ j₃ M (Lbot j₂ j₃ n + (i' : ℕ)) (mbot j₂ a P + k)) n, h]
    by_cases hii : (i : ℕ) = i'
    · have hii' : i = i' := Fin.ext hii
      subst hii'
      simp only [ite_true]
      have := hpos i i.2
      have hs : Real.sqrt (2 * ((Lbot j₂ j₃ n + (i : ℕ) : ℚ) : ℝ) + 1) *
          Real.sqrt (2 * ((Lbot j₂ j₃ n + (i : ℕ) : ℚ) : ℝ) + 1) =
          2 * ((Lbot j₂ j₃ n + (i : ℕ) : ℚ) : ℝ) + 1 := Real.mul_self_sqrt this.le
      rw [hs]; field_simp
    · have hii' : i ≠ i' := fun h => hii (by rw [h])
      simp [hii, hii']
  have key := cols_of_rows n (fun i k => Real.sqrt (2 * ((Lbot j₂ j₃ n + (i : ℕ) : ℚ) : ℝ) + 1) *
        tt j₂ j₃ M (Lbot j₂ j₃ n + (i : ℕ)) (mbot j₂ a P + (k : ℕ))) hrows ⟨j, hj⟩ ⟨j', hj'⟩
  have e2 : ∑ i : Fin n, (Real.sqrt (2 * ((Lbot j₂ j₃ n + (i : ℕ) : ℚ) : ℝ) + 1) *
        tt j₂ j₃ M (Lbot j₂ j₃ n + (i : ℕ)) (mbot j₂ a P + j)) *
      (Real.sqrt (2 * ((Lbot j₂ j₃ n + (i : ℕ) : ℚ) : ℝ) + 1) *
        tt j₂ j₃ M (Lbot j₂ j₃ n + (i : ℕ)) (mbot j₂ a P + j')) =
      ∑ i ∈ Finset.range n, (2 * ((Lbot j₂ j₃ n + i : ℚ) : ℝ) + 1) *
          (tt j₂ j₃ M (Lbot j₂ j₃ n + i) (mbot j₂ a P + j) *
            tt j₂ j₃ M (Lbot j₂ j₃ n + i) (mbot j₂ a P + j')) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => (2 * ((Lbot j₂ j₃ n + i : ℚ) : ℝ) + 1) *
          (tt j₂ j₃ M (Lbot j₂ j₃ n + i) (mbot j₂ a P + j) *
            tt j₂ j₃ M (Lbot j₂ j₃ n + i) (mbot j₂ a P + j')))]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hpos i i.2
    have hs : Real.sqrt (2 * ((Lbot j₂ j₃ n + (i : ℕ) : ℚ) : ℝ) + 1) *
          Real.sqrt (2 * ((Lbot j₂ j₃ n + (i : ℕ) : ℚ) : ℝ) + 1) =
          2 * ((Lbot j₂ j₃ n + (i : ℕ) : ℚ) : ℝ) + 1 := Real.mul_self_sqrt this.le
    linear_combination
      (tt j₂ j₃ M (Lbot j₂ j₃ n + (i : ℕ)) (mbot j₂ a P + j) *
        tt j₂ j₃ M (Lbot j₂ j₃ n + (i : ℕ)) (mbot j₂ a P + j')) * hs
  rw [← e2, key]
  by_cases hjj : j = j'
  · subst hjj; simp
  · have : (⟨j, hj⟩ : Fin n) ≠ ⟨j', hj'⟩ := fun h => hjj (by simpa using h)
    simp [hjj, this]

/-- info: 'FormalResearch.Wigner.threeJ_completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threeJ_completeness

end

end FormalResearch.Wigner
