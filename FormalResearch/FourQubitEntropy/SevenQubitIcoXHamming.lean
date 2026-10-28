import Mathlib

/-!
# Hamming-ball Schmidt rank (`thm:hamming-ball-schmidt`, HB-0) and the `(7,3,2)` case (LE-5)

`ResearchNotes/QI/seven_qubit_entanglement/hamming_ball_schmidt.tex`.

Everything is for real coefficient matrices. A pure `n`-qubit vector across a `k | m` cut (`n = k + m`) is
a matrix `M : (Fin k → Bool) → (Fin m → Bool) → ℝ`; it lies in the Hamming ball `H_{≤ r}` when
`M a b = 0` whenever `r < wt a + wt b`.

* `rank_le_cover`: the cover half of the matching/vertex-cover argument. If every nonzero entry has its
  row in `S` or its column in `T`, then `rank M ≤ |S| + |T|` (any `S`, `T`, no ball needed).
* `hamming_rank_le`: general `k, m, r`. Every matrix in `H_{≤ r}` has rank at most
  `R_{k+m,k,r} = min{2^k, min_{0≤t≤k} [∑_{i<t} C(k,i) + ∑_{j≤r-t} C(m,j)]}` (`eq:hamming-ball-rank`).
  This is the upper bound of the exact-rank statement. The matching lower bound for general `(n,k,r)`
  (König) is not formalized.
* `hammingRank_732`, `max_rank_732`: for `(n,k,r) = (7,3,2)` the formula gives `5`, the bound is attained
  (explicit LE-5 witness), so the maximal Schmidt rank of weight-`≤ 2` seven-qubit vectors across a
  `3 | 4` cut is exactly `5`.
* `witness_732`: the LE-5 state for every `0 ≤ η ≤ 1`: normalized, leakage `η_B = η` (squared weight at
  total excitation `≥ 3`), and the `3 | 4` cut has purity exactly `(1-η)²/5 + η²/3`.
* `robust_quadratic`, `robust_quadratic_ge_two_fifteenths`: the rational identities of
  `thm:low-excitation-exclusion` (the monotonicity step `robust_purity_mono` and the block
  Cauchy-Schwarz bound are in `SevenQubitIcoXBlockPurity`).
-/

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

open Finset Matrix

/-! ### Rank bound from a cover -/

theorem matrix_rank_add_le {ι κ : Type*} [Fintype ι] [Fintype κ] (A B : Matrix ι κ ℝ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have h : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_sup.2 ⟨_, ⟨x, rfl⟩, _, ⟨x, rfl⟩, by simp⟩
  calc Module.finrank ℝ (LinearMap.range (A + B).mulVecLin)
      ≤ Module.finrank ℝ (↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin)) :=
        Submodule.finrank_mono h
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

/-- If every nonzero entry has its row in `S` or its column in `T`, the rank is at most `|S| + |T|`. -/
theorem rank_le_cover {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix ι κ ℝ) (S : Finset ι) (T : Finset κ)
    (h : ∀ a b, a ∉ S → b ∉ T → M a b = 0) : M.rank ≤ S.card + T.card := by
  classical
  let DS : Matrix ι ι ℝ := diagonal fun a => if a ∈ S then 1 else 0
  let E : Matrix ι ι ℝ := diagonal fun a => if a ∈ S then 0 else 1
  let DT : Matrix κ κ ℝ := diagonal fun b => if b ∈ T then 1 else 0
  have hM : M = DS * M + E * M * DT := by
    ext a b
    simp only [DS, E, DT, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases ha : a ∈ S
    · simp [ha]
    · by_cases hb : b ∈ T
      · simp [ha, hb]
      · simp [ha, hb, h a b ha hb]
  have h1 : (DS * M).rank ≤ S.card := by
    refine (Matrix.rank_mul_le_left DS M).trans ?_
    simp only [DS, Matrix.rank_diagonal]
    rw [Fintype.card_subtype]
    simp
  have h2 : (E * M * DT).rank ≤ T.card := by
    refine (Matrix.rank_mul_le_right (E * M) DT).trans ?_
    simp only [DT, Matrix.rank_diagonal]
    rw [Fintype.card_subtype]
    simp
  calc M.rank = (DS * M + E * M * DT).rank := by rw [← hM]
    _ ≤ _ := matrix_rank_add_le _ _
    _ ≤ _ := Nat.add_le_add h1 h2

/-! ### Hamming weights and ball counts -/

/-- Hamming weight of a bit string. -/
def wt {k : ℕ} (a : Fin k → Bool) : ℕ := ∑ i, if a i = true then 1 else 0

theorem card_wt_eq (k i : ℕ) :
    (univ.filter fun a : Fin k → Bool => wt a = i).card = k.choose i := by
  have h := Finset.card_powersetCard i (univ : Finset (Fin k))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  rw [← h]
  refine Finset.card_bij (fun a _ => univ.filter fun x => a x = true) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_filter]
    exact ha
  · intro a _ a' _ hh
    funext x
    have := Finset.ext_iff.1 hh x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    cases ha : a x <;> cases ha' : a' x <;> simp_all
  · intro s hs
    rw [Finset.mem_powersetCard] at hs
    refine ⟨fun x => decide (x ∈ s), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hs.2]
      simp [wt]
    · ext x; simp

/-- `∑_{i<t} C(k,i)`: the number of strings of weight `< t`. -/
def ballCount (k t : ℕ) : ℕ := ∑ i ∈ range t, k.choose i

theorem card_wt_lt (k t : ℕ) :
    (univ.filter fun a : Fin k → Bool => wt a < t).card = ballCount k t := by
  unfold ballCount
  rw [Finset.card_eq_sum_card_fiberwise (f := wt) (t := range t)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [← card_wt_eq k i]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hi ⊢
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h ▸ hi, h⟩
  · intro a ha
    simpa using ha

/-- The cover size `∑_{i<t} C(k,i) + ∑_{j≤r-t} C(m,j)` (empty second sum for `t > r`). -/
def coverSize (k m r t : ℕ) : ℕ := ballCount k t + ballCount m (r + 1 - t)

/-- `R_{n,k,r}` of `eq:hamming-ball-rank`, with `m = n - k`. -/
def hammingRank (k m r : ℕ) : ℕ :=
  min (2 ^ k) ((range (k + 1)).inf' ⟨0, by simp⟩ (coverSize k m r))

/-- **Upper bound of `eq:hamming-ball-rank`.** Every `2^k × 2^m` real matrix supported on
`wt a + wt b ≤ r` has rank at most `R_{k+m,k,r}`. -/
theorem hamming_rank_le (k m r : ℕ) (M : Matrix (Fin k → Bool) (Fin m → Bool) ℝ)
    (h : ∀ a b, r < wt a + wt b → M a b = 0) : M.rank ≤ hammingRank k m r := by
  unfold hammingRank
  refine le_min ?_ ?_
  · calc M.rank ≤ Fintype.card (Fin k → Bool) := M.rank_le_card_height
      _ = 2 ^ k := by simp
  · refine Finset.le_inf' _ _ fun t _ => ?_
    classical
    have := rank_le_cover M (univ.filter fun a : Fin k → Bool => wt a < t)
      (univ.filter fun b : Fin m → Bool => wt b < r + 1 - t) (by
        intro a b ha hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at ha hb
        exact h a b (by omega))
    rwa [card_wt_lt, card_wt_lt] at this

/-- The formula gives `R_{7,3,2} = 5`. -/
theorem hammingRank_732 : hammingRank 3 4 2 = 5 := by
  decide +kernel

/-! ### The LE-5 witness at `(n,k,r) = (7,3,2)` -/

/-- The partner column string of each row string (`LE-5`): `000 ↦ 0011`, `001 ↦ 0001`, `010 ↦ 0010`,
`100 ↦ 0100`, `011 ↦ 0000`, `101 ↦ 1000`, `110 ↦ 0101`, `111 ↦ 1111`. -/
def pairCol (a : Fin 3 → Bool) : Fin 4 → Bool :=
  match a 0, a 1, a 2 with
  | false, false, false => ![false, false, true, true]
  | false, false, true => ![false, false, false, true]
  | false, true, false => ![false, false, true, false]
  | true, false, false => ![false, true, false, false]
  | false, true, true => ![false, false, false, false]
  | true, false, true => ![true, false, false, false]
  | true, true, false => ![false, true, false, true]
  | true, true, true => ![true, true, true, true]

/-- The five "low" rows `000, 001, 010, 100, 011` (excitation `≤ 2`), the other three are "high". -/
def isLow (a : Fin 3 → Bool) : Bool :=
  match a 0, a 1, a 2 with
  | false, false, false => true
  | false, false, true => true
  | false, true, false => true
  | true, false, false => true
  | false, true, true => true
  | _, _, _ => false

theorem pairCol_injective : Function.Injective pairCol := by
  decide +kernel

theorem low_weight : ∀ a : Fin 3 → Bool, isLow a = true → wt a + wt (pairCol a) ≤ 2 := by
  decide +kernel

theorem high_weight : ∀ a : Fin 3 → Bool, isLow a = false → 3 ≤ wt a + wt (pairCol a) := by
  decide +kernel

theorem card_isLow : (univ.filter fun a : Fin 3 → Bool => isLow a = true).card = 5 := by
  decide +kernel

theorem card_not_isLow : (univ.filter fun a : Fin 3 → Bool => ¬ isLow a = true).card = 3 := by
  decide +kernel

/-- The coefficient of the term at row `a`: `√((1-η)/5)` on low rows, `√(η/3)` on high rows. -/
noncomputable def coef (η : ℝ) (a : Fin 3 → Bool) : ℝ :=
  if isLow a = true then Real.sqrt ((1 - η) / 5) else Real.sqrt (η / 3)

/-- The `8 × 16` coefficient matrix of the LE-5 state across the `3 | 4` cut. -/
noncomputable def W (η : ℝ) (a : Fin 3 → Bool) (r : Fin 4 → Bool) : ℝ :=
  if r = pairCol a then coef η a else 0

theorem coef_sq (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) (a : Fin 3 → Bool) :
    coef η a ^ 2 = if isLow a = true then (1 - η) / 5 else η / 3 := by
  unfold coef
  split_ifs
  · exact Real.sq_sqrt (by linarith)
  · exact Real.sq_sqrt (by linarith)

/-- Distinct rows have disjoint supports, so the reduced matrix is diagonal. -/
theorem W_gram (η : ℝ) (a b : Fin 3 → Bool) :
    ∑ r, W η a r * W η b r = if a = b then coef η a ^ 2 else 0 := by
  by_cases hab : a = b
  · subst hab
    simp only [W, ite_true]
    rw [Finset.sum_eq_single (pairCol a)]
    · simp [sq]
    · intro r _ hr; simp [hr]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [hab, ite_false]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : r = pairCol a
    · have : r ≠ pairCol b := fun h => hab (pairCol_injective (hr.symm.trans h))
      simp [W, this]
    · simp [W, hr]

/-- Purity of the `3`-qubit side: `∑_{a,b} (∑_r M a r M b r)²`. -/
noncomputable def cutPurity (M : (Fin 3 → Bool) → (Fin 4 → Bool) → ℝ) : ℝ :=
  ∑ a, ∑ b, (∑ r, M a r * M b r) ^ 2

theorem sum_rows (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) (f : ℝ → ℝ) :
    ∑ a : Fin 3 → Bool, f (coef η a ^ 2) = 5 * f ((1 - η) / 5) + 3 * f (η / 3) := by
  have : ∀ a, f (coef η a ^ 2) = if isLow a = true then f ((1 - η) / 5) else f (η / 3) := by
    intro a; rw [coef_sq η h0 h1]; split_ifs <;> rfl
  simp only [this]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, card_isLow, card_not_isLow]
  simp

/-- Purity of the LE-5 state across the `3 | 4` cut. -/
theorem cutPurity_W (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    cutPurity (W η) = (1 - η) ^ 2 / 5 + η ^ 2 / 3 := by
  unfold cutPurity
  have : ∀ a b : Fin 3 → Bool, (∑ r, W η a r * W η b r) ^ 2 =
      if a = b then (coef η a ^ 2) ^ 2 else 0 := by
    intro a b; rw [W_gram]; split_ifs <;> simp
  simp only [this]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [sum_rows η h0 h1 (fun x => x ^ 2)]
  ring

/-- Normalization of the LE-5 state. -/
theorem norm_W (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    ∑ a, ∑ r, W η a r ^ 2 = 1 := by
  have : ∀ a, ∑ r, W η a r ^ 2 = coef η a ^ 2 := by
    intro a
    rw [Finset.sum_eq_single (pairCol a)]
    · simp [W]
    · intro r _ hr; simp [W, hr]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [this]
  rw [sum_rows η h0 h1 (fun x => x)]
  ring

/-- Leakage out of the weight-`≤ 2` ball: the squared weight on `wt a + wt r > 2`. -/
theorem leak_W (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    ∑ a, ∑ r, (if 2 < wt a + wt r then W η a r ^ 2 else 0) = η := by
  have : ∀ a, ∑ r, (if 2 < wt a + wt r then W η a r ^ 2 else 0) =
      if isLow a = true then 0 else coef η a ^ 2 := by
    intro a
    rw [Finset.sum_eq_single (pairCol a)]
    · by_cases ha : isLow a = true
      · have := low_weight a ha
        simp [ha, show ¬ 2 < wt a + wt (pairCol a) by omega]
      · have ha' : isLow a = false := by simpa using ha
        have := high_weight a ha'
        simp [ha, show 2 < wt a + wt (pairCol a) by omega, W]
    · intro r _ hr
      simp [W, hr]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [this]
  have h2 : ∀ a, (if isLow a = true then (0 : ℝ) else coef η a ^ 2) =
      if isLow a = true then 0 else η / 3 := by
    intro a; rw [coef_sq η h0 h1]; split_ifs <;> rfl
  simp only [h2]
  rw [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, card_not_isLow]
  simp
  ring

/-- At `η = 0` the matrix `W 0` has rank exactly `5`. -/
theorem rank_W_zero : (Matrix.of (W 0)).rank = 5 := by
  have h := Matrix.rank_self_mul_transpose (Matrix.of (W 0))
  rw [← h]
  have hd : Matrix.of (W 0) * (Matrix.of (W 0))ᵀ = Matrix.diagonal fun a => coef 0 a ^ 2 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.diagonal_apply]
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [W_gram]
  rw [hd, Matrix.rank_diagonal, Fintype.card_subtype]
  have : ∀ a : Fin 3 → Bool, (coef 0 a ^ 2 ≠ 0) ↔ isLow a = true := by
    intro a
    rw [coef_sq 0 le_rfl zero_le_one]
    split_ifs with h <;> simp [h]
  simp only [this]
  exact card_isLow

/-- **`(7,3,2)`: the maximal Schmidt rank is exactly `5`.** Every weight-`≤ 2` matrix has rank `≤ 5`
and the LE-5 matrix attains `5`. -/
theorem max_rank_732 :
    (∀ M : Matrix (Fin 3 → Bool) (Fin 4 → Bool) ℝ, (∀ a b, 2 < wt a + wt b → M a b = 0) →
      M.rank ≤ 5) ∧
    (∃ M : Matrix (Fin 3 → Bool) (Fin 4 → Bool) ℝ,
      (∀ a b, 2 < wt a + wt b → M a b = 0) ∧ M.rank = 5) := by
  refine ⟨fun M h => ?_, ⟨Matrix.of (W 0), ?_, rank_W_zero⟩⟩
  · have := hamming_rank_le 3 4 2 M h
    rwa [hammingRank_732] at this
  · intro a b hab
    simp only [Matrix.of_apply, W]
    split_ifs with hb
    · subst hb
      by_cases ha : isLow a = true
      · exact absurd hab (by have := low_weight a ha; omega)
      · simp [coef, ha]
    · rfl

/-! ### The LE-5 state as a seven-qubit tensor -/

/-- Hamming weight of a seven-qubit string. -/
abbrev wt7 (s : Fin 7 → Bool) : ℕ := wt s

/-- The LE-5 state `Z η`: coefficient `W η a r` on the string with sites `0,1,2` equal to `a` and sites
`3..6` equal to `r`. -/
noncomputable def Z (η : ℝ) (s : Fin 7 → Bool) : ℝ :=
  W η (fun i => s (Fin.castAdd 4 i)) (fun j => s (Fin.natAdd 3 j))

theorem wt_append (a : Fin 3 → Bool) (r : Fin 4 → Bool) :
    wt (Fin.append a r) = wt a + wt r := by
  unfold wt
  rw [Fin.sum_univ_add]
  simp

theorem Z_append (η : ℝ) (a : Fin 3 → Bool) (r : Fin 4 → Bool) :
    Z η (Fin.append a r) = W η a r := by
  simp [Z]

/-- Sums over seven-qubit strings are sums over the `3 | 4` cut. -/
theorem sum_bitstring (F : (Fin 7 → Bool) → ℝ) :
    ∑ s, F s = ∑ a : Fin 3 → Bool, ∑ r : Fin 4 → Bool, F (Fin.append a r) := by
  rw [← Finset.sum_product']
  exact (Fintype.sum_equiv (Fin.appendEquiv 3 4) (fun p => F (Fin.append p.1 p.2)) F
    (fun p => rfl)).symm

/-- **LE-5 (`prop:low-excitation-cutwise-sharp`).** For every `0 ≤ η ≤ 1` (in particular `0 ≤ η ≤ 3/8`)
the seven-qubit vector `Z η` is normalized, has weight `> 2` leakage `η_B = η`, and the `3 | 4` cut
(first three vs last four sites) has purity exactly `(1-η)²/5 + η²/3`. -/
theorem witness_732 (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    ∑ s, Z η s ^ 2 = 1 ∧
    ∑ s, (if 2 < wt7 s then Z η s ^ 2 else 0) = η ∧
    ∑ a : Fin 3 → Bool, ∑ b : Fin 3 → Bool,
      (∑ r : Fin 4 → Bool, Z η (Fin.append a r) * Z η (Fin.append b r)) ^ 2 =
        (1 - η) ^ 2 / 5 + η ^ 2 / 3 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [sum_bitstring]
    simpa only [Z_append] using norm_W η h0 h1
  · rw [sum_bitstring]
    simp only [Z_append, wt7, wt_append]
    exact leak_W η h0 h1
  · have := cutPurity_W η h0 h1
    unfold cutPurity at this
    simpa only [Z_append] using this

/-! ### The rational constants of `thm:low-excitation-exclusion` -/

/-- `(1-η)²/5 + η²/3 = 1/8 + (8/15)(η - 3/8)²`. -/
theorem robust_quadratic (η : ℝ) :
    (1 - η) ^ 2 / 5 + η ^ 2 / 3 = 1 / 8 + 8 / 15 * (η - 3 / 8) ^ 2 := by
  ring

/-- `η ≤ 1/4` forces the bound `≥ 2/15`. -/
theorem robust_quadratic_ge_two_fifteenths (η : ℝ) (h1 : η ≤ 1 / 4) :
    2 / 15 ≤ (1 - η) ^ 2 / 5 + η ^ 2 / 3 := by
  rw [robust_quadratic]
  nlinarith

/-- The value at `η = 1/4` is exactly `2/15`. -/
theorem robust_quadratic_quarter : (1 - 1 / 4 : ℝ) ^ 2 / 5 + (1 / 4 : ℝ) ^ 2 / 3 = 2 / 15 := by
  norm_num

end FormalResearch.FourQubitEntropy.SevenQubitIco
