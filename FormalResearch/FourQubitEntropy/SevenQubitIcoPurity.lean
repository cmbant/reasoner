import FormalResearch.FourQubitEntropy.SevenQubitIcoState

/-!
# Purities of the seven-qubit icosahedral family on every cut

For every `k`-subset of the seven sites (`k = 3` and `k = 2`) this derives the purity of the reduced
state of `icosahedralState alpha beta` from the state tensor alone, as an integer-coefficient
polynomial in `alpha`, `beta`. A cut is a bijection of the seven sites onto `Fin k ⊕ Fin l`; the
reduced matrix entry is `∑_r ψ(a, r) ψ(b, r)` as in `SevenQubitIcoState`.

The results (`thm:ico` of `icosahedral_state.tex`):

* every `3`-cut has purity `114 α⁴ + 12 α²β² + 2 β⁴` if it avoids the special site `0` and
  `146 α⁴ + 4 α²β² + 2 β⁴` if it contains it (the odd terms vanish);
* the mean over the 35 three-cuts is `(4470 α⁴ + 300 α²β² + 70 β⁴)/35`, which on the family
  (`α² = (1-2x)/30`, `β² = x`) equals `121/917 + (1048/525)(x - 37/524)²`, so `x = 37/524` is the unique
  minimiser and `π₃ = 121/917` there;
* the pair purities are those listed for `thm:ico`.

The eigenvalues of the reduced matrices, and hence entropies, are not treated here.
-/

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

open Finset

/-- A cut of the seven sites: each site goes to the `k`-qubit side or to the `l`-qubit complement. -/
abbrev Cut (k l : ℕ) := Fin 7 → Fin k ⊕ Fin l

/-- The basis string whose site `i` carries the bit of the side-position `cut i`. -/
def encode {k l : ℕ} (cut : Cut k l) (a : Fin k → Bool) (r : Fin l → Bool) : BitString :=
  fun i => Sum.elim a r (cut i)

/-- Integer Gram entry of two coefficient tables across a cut. -/
def gram {k l : ℕ} (cut : Cut k l) (f g : BitString → ℤ) (a b : Fin k → Bool) : ℤ :=
  ∑ r : Fin l → Bool, f (encode cut a r) * g (encode cut b r)

/-- Reduced density-matrix entry of `icosahedralState alpha beta` on the `k`-qubit side of a cut. -/
def entry {k l : ℕ} (cut : Cut k l) (alpha beta : ℝ) (a b : Fin k → Bool) : ℝ :=
  ∑ r : Fin l → Bool,
    icosahedralState alpha beta (encode cut a r) * icosahedralState alpha beta (encode cut b r)

/-- Purity `tr ρ²` of the `k`-qubit reduced state across a cut (the entries are real). -/
def purity {k l : ℕ} (cut : Cut k l) (alpha beta : ℝ) : ℝ :=
  ∑ a : Fin k → Bool, ∑ b : Fin k → Bool, entry cut alpha beta a b ^ 2

/-- The `αα`, `αβ + βα` and `ββ` Gram matrices of a cut. -/
def gramP {k l : ℕ} (cut : Cut k l) (a b : Fin k → Bool) : ℤ := gram cut alphaCoefficient alphaCoefficient a b
def gramQ {k l : ℕ} (cut : Cut k l) (a b : Fin k → Bool) : ℤ :=
  gram cut alphaCoefficient betaCoefficient a b + gram cut betaCoefficient alphaCoefficient a b
def gramR {k l : ℕ} (cut : Cut k l) (a b : Fin k → Bool) : ℤ := gram cut betaCoefficient betaCoefficient a b

/-- Integer coefficients of the purity polynomial `c40 α⁴ + c31 α³β + c22 α²β² + c13 αβ³ + c04 β⁴`. -/
structure PurityCoeffs where
  c40 : ℤ
  c31 : ℤ
  c22 : ℤ
  c13 : ℤ
  c04 : ℤ
  deriving DecidableEq

def purityCoeffs {k l : ℕ} (cut : Cut k l) : PurityCoeffs where
  c40 := ∑ a, ∑ b, gramP cut a b ^ 2
  c31 := ∑ a, ∑ b, 2 * (gramP cut a b * gramQ cut a b)
  c22 := ∑ a, ∑ b, (gramQ cut a b ^ 2 + 2 * (gramP cut a b * gramR cut a b))
  c13 := ∑ a, ∑ b, 2 * (gramQ cut a b * gramR cut a b)
  c04 := ∑ a, ∑ b, gramR cut a b ^ 2

theorem entry_expand {k l : ℕ} (cut : Cut k l) (alpha beta : ℝ) (a b : Fin k → Bool) :
    entry cut alpha beta a b =
      alpha ^ 2 * gramP cut a b + alpha * beta * gramQ cut a b + beta ^ 2 * gramR cut a b := by
  unfold entry gramP gramQ gramR gram
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  simp only [icosahedralState]
  ring

theorem purity_expand {k l : ℕ} (cut : Cut k l) (alpha beta : ℝ) :
    purity cut alpha beta =
      (purityCoeffs cut).c40 * alpha ^ 4 + (purityCoeffs cut).c31 * (alpha ^ 3 * beta) +
        (purityCoeffs cut).c22 * (alpha ^ 2 * beta ^ 2) +
        (purityCoeffs cut).c13 * (alpha * beta ^ 3) + (purityCoeffs cut).c04 * beta ^ 4 := by
  unfold purity
  simp only [purityCoeffs, entry_expand]
  push_cast
  simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring


/-! ### The cuts -/

/-- Number of `true` bits of `m`. -/
def weight (m : Fin 7 → Bool) : ℕ := (Finset.univ.filter fun i => m i = true).card

/-- Number of sites before `i` whose mask bit is `v`. -/
def countBefore (m : Fin 7 → Bool) (v : Bool) (i : Fin 7) : ℕ :=
  ((List.finRange 7).filter (fun j => decide (j.val < i.val) && m j == v)).length

/-- The cut sending the sites with mask bit `true` (in increasing order) to the `k`-qubit side and the
others to the complement. -/
def maskCut (k l : ℕ) [NeZero k] [NeZero l] (m : Fin 7 → Bool) : Cut k l :=
  fun i => if m i then Sum.inl (Fin.ofNat k (countBefore m true i))
    else Sum.inr (Fin.ofNat l (countBefore m false i))

/-- Each mask of weight 3 (resp. 2) gives a genuine cut: every site lands on exactly one position. -/
theorem maskCut_bijective_three :
    ∀ m : Fin 7 → Bool, weight m = 3 → Function.Bijective (maskCut 3 4 m) := by
  decide +kernel

theorem maskCut_bijective_two :
    ∀ m : Fin 7 → Bool, weight m = 2 → Function.Bijective (maskCut 2 5 m) := by
  decide +kernel

/-- The 35 three-qubit cuts. The special site is site `0`. -/
def tripleMasks : Finset (Fin 7 → Bool) := Finset.univ.filter fun m => weight m = 3

/-- The 21 two-qubit cuts. -/
def pairMasks : Finset (Fin 7 → Bool) := Finset.univ.filter fun m => weight m = 2

theorem tripleMasks_card : tripleMasks.card = 35 := by decide +kernel
theorem tripleMasks_containing_card : (tripleMasks.filter fun m => m 0 = true).card = 15 := by
  decide +kernel
theorem tripleMasks_avoiding_card : (tripleMasks.filter fun m => ¬ m 0 = true).card = 20 := by
  decide +kernel
theorem pairMasks_card : pairMasks.card = 21 := by decide +kernel
theorem pairMasks_containing_card : (pairMasks.filter fun m => m 0 = true).card = 6 := by
  decide +kernel
theorem pairMasks_avoiding_card : (pairMasks.filter fun m => ¬ m 0 = true).card = 15 := by
  decide +kernel

/-! ### Purity coefficients of every cut -/

theorem triple_coeffs : ∀ m : Fin 7 → Bool, weight m = 3 →
    purityCoeffs (maskCut 3 4 m) =
      if m 0 = true then ⟨146, 0, 4, 0, 2⟩ else ⟨114, 0, 12, 0, 2⟩ := by
  decide +kernel

theorem pair_coeffs : ∀ m : Fin 7 → Bool, weight m = 2 →
    purityCoeffs (maskCut 2 5 m) =
      if m 0 = true then ⟨250, 0, 20, 0, 2⟩ else ⟨226, 0, 28, 0, 2⟩ := by
  decide +kernel

theorem tripleCut_purity (m : Fin 7 → Bool) (hm : weight m = 3) (alpha beta : ℝ) :
    purity (maskCut 3 4 m) alpha beta =
      if m 0 = true then 146 * alpha ^ 4 + 4 * (alpha ^ 2 * beta ^ 2) + 2 * beta ^ 4
      else 114 * alpha ^ 4 + 12 * (alpha ^ 2 * beta ^ 2) + 2 * beta ^ 4 := by
  rw [purity_expand, triple_coeffs m hm]
  by_cases h : m 0 = true <;> simp [h]

theorem pairCut_purity (m : Fin 7 → Bool) (hm : weight m = 2) (alpha beta : ℝ) :
    purity (maskCut 2 5 m) alpha beta =
      if m 0 = true then 250 * alpha ^ 4 + 20 * (alpha ^ 2 * beta ^ 2) + 2 * beta ^ 4
      else 226 * alpha ^ 4 + 28 * (alpha ^ 2 * beta ^ 2) + 2 * beta ^ 4 := by
  rw [purity_expand, pair_coeffs m hm]
  by_cases h : m 0 = true <;> simp [h]

/-- Mean purity over the 35 three-qubit cuts. -/
noncomputable def meanTriplePurity (alpha beta : ℝ) : ℝ :=
  (∑ m ∈ tripleMasks, purity (maskCut 3 4 m) alpha beta) / 35

theorem meanTriplePurity_eq (alpha beta : ℝ) :
    meanTriplePurity alpha beta =
      (4470 * alpha ^ 4 + 300 * (alpha ^ 2 * beta ^ 2) + 70 * beta ^ 4) / 35 := by
  unfold meanTriplePurity
  have hs : ∀ m ∈ tripleMasks, purity (maskCut 3 4 m) alpha beta =
      if m 0 = true then 146 * alpha ^ 4 + 4 * (alpha ^ 2 * beta ^ 2) + 2 * beta ^ 4
      else 114 * alpha ^ 4 + 12 * (alpha ^ 2 * beta ^ 2) + 2 * beta ^ 4 :=
    fun m hm => tripleCut_purity m (Finset.mem_filter.1 hm).2 alpha beta
  rw [Finset.sum_congr rfl hs,
    Finset.sum_ite, Finset.sum_const, Finset.sum_const, tripleMasks_containing_card,
    tripleMasks_avoiding_card]
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-! ### On the family `α² = (1-2x)/30`, `β² = x` -/

theorem meanTriplePurity_family (x alpha beta : ℝ) (hα : alpha ^ 2 = u x) (hβ : beta ^ 2 = x) :
    meanTriplePurity alpha beta = 121 / 917 + 1048 / 525 * (x - 37 / 524) ^ 2 := by
  rw [meanTriplePurity_eq, show alpha ^ 4 = (alpha ^ 2) ^ 2 by ring,
    show beta ^ 4 = (beta ^ 2) ^ 2 by ring, hα, hβ]
  unfold u
  ring

/-- Within the family the mean three-body purity is at least `121/917`. -/
theorem meanTriplePurity_ge (x alpha beta : ℝ) (hα : alpha ^ 2 = u x) (hβ : beta ^ 2 = x) :
    121 / 917 ≤ meanTriplePurity alpha beta := by
  rw [meanTriplePurity_family x alpha beta hα hβ]
  nlinarith [sq_nonneg (x - 37 / 524)]

/-- Equality holds exactly at `x = 37/524`. -/
theorem meanTriplePurity_eq_min_iff (x alpha beta : ℝ) (hα : alpha ^ 2 = u x) (hβ : beta ^ 2 = x) :
    meanTriplePurity alpha beta = 121 / 917 ↔ x = 37 / 524 := by
  rw [meanTriplePurity_family x alpha beta hα hβ]
  constructor
  · intro h
    have : (x - 37 / 524) ^ 2 = 0 := by nlinarith [sq_nonneg (x - 37 / 524)]
    have := pow_eq_zero_iff (two_ne_zero) |>.1 this
    linarith
  · intro h
    rw [h]
    ring

/-- At `x = 37/524` (`α² = 15/524`, `β² = 37/524`) the three-qubit marginals avoiding the special
site have purity `4381/34322` and those containing it `2363/17161`. -/
theorem tripleCut_purity_ico (m : Fin 7 → Bool) (hm : weight m = 3) (alpha beta : ℝ)
    (hα : alpha ^ 2 = u (37 / 524)) (hβ : beta ^ 2 = 37 / 524) :
    purity (maskCut 3 4 m) alpha beta = if m 0 = true then 2363 / 17161 else 4381 / 34322 := by
  rw [tripleCut_purity m hm, show alpha ^ 4 = (alpha ^ 2) ^ 2 by ring,
    show beta ^ 4 = (beta ^ 2) ^ 2 by ring, hα, hβ]
  unfold u
  split_ifs <;> norm_num

/-- At `x = 37/524` the pair purities are `8641/34322` (pairs avoiding the special site) and
`8761/34322` (pairs containing it). -/
theorem pairCut_purity_ico (m : Fin 7 → Bool) (hm : weight m = 2) (alpha beta : ℝ)
    (hα : alpha ^ 2 = u (37 / 524)) (hβ : beta ^ 2 = 37 / 524) :
    purity (maskCut 2 5 m) alpha beta = if m 0 = true then 8761 / 34322 else 8641 / 34322 := by
  rw [pairCut_purity m hm, show alpha ^ 4 = (alpha ^ 2) ^ 2 by ring,
    show beta ^ 4 = (beta ^ 2) ^ 2 by ring, hα, hβ]
  unfold u
  split_ifs <;> norm_num

end FormalResearch.FourQubitEntropy.SevenQubitIco
