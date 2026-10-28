import Mathlib

/-!
# Unique Rains equality faces at `n = 7, 13, 19, 20` (`prop:rains-faces`, EF-7/13/19/20)

`ResearchNotes/QI/seven_qubit_entanglement/shadow_equality_geometry.tex`, `prop:rains-faces`;
checker `code/verify_rains_equality_faces.py` (log `verification/verify_rains_equality_faces.txt`).

For each `n ∈ {7, 13, 19, 20}` the active zero Pauli weights `A_j = 0` (`j ∈ zA`) and zero Rains
shadow coefficients `S_i = 0` (`i ∈ zS`) coming from the exact lower-bound certificates, together with
`A_0 = 1` and the pure-state complementary-purity equations `a_s = a_{n-s}` (`s < ⌈n/2⌉`), form the
linear system `Face n zA zS A` (definition above; `a_{s,j} = C(n-j,s-j)/(2^s C(n,s))`, shadow
transform `S_i = 2^{-n} ∑_j K_{i,j} A_j` with the Krawtchouk-type numbers `shadowNum`). The inputs
`zA`, `zS` are taken from the paper's certificates (not re-derived here).

Proved here (exact, over `ℚ`, for each `n`, with the face data produced by the checker):

* `faceN_unique`: every `A : ℕ → ℚ` satisfying `Face n zA zS A` has `A_j = tgtN j` for all `j ≤ n`
  (this is the rank statement: the selected `n+1` rows have an explicit integer left inverse `L`, with
  `L M = dd · 1` checked by `decide +kernel`);
* `faceN_target`: the profile `tgtN` itself satisfies all the constraints (so the system is consistent);
* `faceN_sum`, `faceN_obj`, `faceN_shadow`, `faceN_shadow_sum`, `faceN_nonneg`: `∑ A_j = 2^n`, the
  Rains LP objective `a_{⌊n/2⌋}(A) = 1/8, 25/1408, 93/38896, 1193/739024`, the reconstructed shadow
  vector `S = shN` (values listed in `shLitN` and `shN_values`, equal to the paper's/checker's
  tables), `∑ S_i = 2^n`, and nonnegativity of all `A_j` and `S_i`;
* `rains_face7_no_integral_shadow`, `rains_face13_no_integral_shadow`: no `A` satisfying the face
  system has all shadow coefficients integers (`S_1 = 7/4` at `n = 7`, `S_3 = 39/4` at `n = 13`). The
  paper's remark that stabilizer states have integer shadow coefficients is **not** formalized; the
  integrality is the hypothesis `hS`, so this is the arithmetic half of "the Rains bound cannot be
  attained by a stabilizer state" at `n = 7, 13`.

Not proved here: that these `zA`, `zS` are what the dual certificates force at equality, the claims
about `n = 20` Type I additive `F₄` codes (`s`-extremal enumerators), and existence of any state or
code with the putative profile (the paper asserts none). `ℕ → ℚ` functions are only constrained on
`0 … n`.
-/

namespace FormalResearch.FourQubitEntropy.SevenQubitRains

open Finset

/-! ### Definitions -/

/-- `a_{s,j}^{(n)} = C(n-j, s-j) / (2^s C(n,s))` for `j ≤ s ≤ n` and `0` otherwise. -/
def aCoef (n s j : ℕ) : ℚ :=
  if j ≤ s ∧ s ≤ n then (Nat.choose (n - j) (s - j) : ℚ) / (2 ^ s * Nat.choose n s) else 0

/-- `2^n` times the shadow-transform coefficient. -/
def shadowNum (n i j : ℕ) : ℤ :=
  ∑ u ∈ range (n + 1), if u ≤ i then
    (Nat.choose (n - j) u : ℤ) * 3 ^ u * Nat.choose j (i - u) * (-1) ^ (j + i + u) else 0

/-- `S_i = ∑_j shadowCoef n i j * A_j`. -/
def shadowCoef (n i j : ℕ) : ℚ := (shadowNum n i j : ℚ) / 2 ^ n

/-- Constraints of an equality face: `A_0 = 1`, the listed Pauli weights vanish, the pure-state
complementary-purity equations `a_s = a_{n-s}` hold for `s < ⌈n/2⌉`, and the listed Rains shadow
coefficients vanish. -/
def Face (n : ℕ) (zA zS : List ℕ) (A : ℕ → ℚ) : Prop :=
  A 0 = 1 ∧ (∀ j ∈ zA, A j = 0) ∧
  (∀ s < (n + 1) / 2, ∑ j ∈ range (n + 1), (aCoef n s j - aCoef n (n - s) j) * A j = 0) ∧
  (∀ i ∈ zS, ∑ j ∈ range (n + 1), shadowCoef n i j * A j = 0)

/-! ### Integer forms of the constraint rows -/

/-- `2^n C(n,s) (a_{s,j} - a_{n-s,j})`. -/
def pNum (n s j : ℕ) : ℤ :=
  (if j ≤ s then 2 ^ (n - s) * (Nat.choose (n - j) (s - j) : ℤ) else 0) -
  (if j ≤ n - s then 2 ^ s * (Nat.choose (n - j) (n - s - j) : ℤ) else 0)

/-- `2^{⌊n/2⌋} C(n,⌊n/2⌋) a_{⌊n/2⌋,j}`. -/
def objNum (n j : ℕ) : ℤ := if j ≤ n / 2 then (Nat.choose (n - j) (n / 2 - j) : ℤ) else 0

theorem coefP_eq (n s j : ℕ) (hs : s ≤ n) :
    aCoef n s j - aCoef n (n - s) j = (pNum n s j : ℚ) / (2 ^ n * Nat.choose n s) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = s + k := ⟨n - s, by omega⟩
  have hpos : (0 : ℚ) < Nat.choose (s + k) s := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_right s k)
  have hc : (Nat.choose (s + k) k : ℚ) = Nat.choose (s + k) s := by
    rw [Nat.choose_symm_add]
  have e : s + k - s = k := by omega
  have hp2 : (2 : ℚ) ^ (s + k) = 2 ^ s * 2 ^ k := pow_add _ _ _
  simp only [aCoef, pNum, e, hc, hp2]
  by_cases h1 : j ≤ s <;> by_cases h2 : j ≤ k <;> simp [h1, h2] <;> field_simp

theorem aCoef_half (n j : ℕ) :
    aCoef n (n / 2) j = (objNum n j : ℚ) / (2 ^ (n / 2) * Nat.choose n (n / 2)) := by
  have : n / 2 ≤ n := Nat.div_le_self _ _
  by_cases h : j ≤ n / 2 <;> simp [aCoef, objNum, h, this]

/-- Row identity for the purity equations. -/
theorem sum_P (n s : ℕ) (hs : s ≤ n) (A : ℕ → ℚ) :
    ∑ j ∈ range (n + 1), (aCoef n s j - aCoef n (n - s) j) * A j =
      (∑ j ∈ range (n + 1), (pNum n s j : ℚ) * A j) / (2 ^ n * Nat.choose n s) := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coefP_eq n s j hs, div_mul_eq_mul_div]

theorem sum_S (n i : ℕ) (A : ℕ → ℚ) :
    ∑ j ∈ range (n + 1), shadowCoef n i j * A j =
      (∑ j ∈ range (n + 1), (shadowNum n i j : ℚ) * A j) / 2 ^ n := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [shadowCoef, div_mul_eq_mul_div]

theorem sum_obj (n : ℕ) (A : ℕ → ℚ) :
    ∑ j ∈ range (n + 1), aCoef n (n / 2) j * A j =
      (∑ j ∈ range (n + 1), (objNum n j : ℚ) * A j) / (2 ^ (n / 2) * Nat.choose n (n / 2)) := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [aCoef_half, div_mul_eq_mul_div]

/-! ### Generic uniqueness certificate and target verification -/

/-- Row of the constraint matrix: type `0` is the unit row `e_k`, type `1` the purity row `P_k`,
type `2` the shadow row `S_k`. -/
def rowI (n t k j : ℕ) : ℤ :=
  if t = 0 then (if j = k then 1 else 0) else if t = 1 then pNum n k j else shadowNum n k j

/-- A rational left inverse `L M = dd · 1` of the selected rows forces `dd · A = L · rhs`. -/
theorem unique_of_cert (n : ℕ) (spec : ℕ → ℕ × ℕ) (L : ℕ → ℕ → ℤ) (dd : ℤ)
    (hLM : ∀ j < n + 1, ∀ i < n + 1,
      ∑ k ∈ range (n + 1), L j k * rowI n (spec k).1 (spec k).2 i = if j = i then dd else 0)
    (A : ℕ → ℚ) (rhs : ℕ → ℤ)
    (hrow : ∀ k < n + 1,
      ∑ i ∈ range (n + 1), (rowI n (spec k).1 (spec k).2 i : ℚ) * A i = (rhs k : ℚ)) :
    ∀ j < n + 1, (dd : ℚ) * A j = ((∑ k ∈ range (n + 1), L j k * rhs k : ℤ) : ℚ) := by
  intro j hj
  push_cast
  symm
  calc (∑ k ∈ range (n + 1), (L j k : ℚ) * (rhs k : ℚ))
      = ∑ k ∈ range (n + 1), (L j k : ℚ) *
          ∑ i ∈ range (n + 1), (rowI n (spec k).1 (spec k).2 i : ℚ) * A i := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [hrow k (Finset.mem_range.1 hk)]
    _ = ∑ i ∈ range (n + 1),
          (∑ k ∈ range (n + 1), (L j k : ℚ) * (rowI n (spec k).1 (spec k).2 i : ℚ)) * A i := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = ∑ i ∈ range (n + 1), (if j = i then (dd : ℚ) else 0) * A i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have := hLM j hj i (Finset.mem_range.1 hi)
        have h2 : (∑ k ∈ range (n + 1), (L j k : ℚ) * (rowI n (spec k).1 (spec k).2 i : ℚ)) =
            if j = i then (dd : ℚ) else 0 := by
          have := congrArg (fun z : ℤ => (z : ℚ)) this
          simpa [apply_ite] using this
        rw [h2]
    _ = (dd : ℚ) * A j := by
        simp [ite_mul, Finset.sum_ite_eq, Finset.mem_range, hj]

/-- Every row of the selected list is a row of the face, with right-hand side `1` for `A_0 = 1`
and `0` otherwise. -/
theorem face_rows (n : ℕ) (zA zS : List ℕ) (A : ℕ → ℚ) (h : Face n zA zS A)
    (spec : ℕ → ℕ × ℕ)
    (hspec : ∀ k < n + 1, spec k = (0, 0) ∨
      ((spec k).1 = 0 ∧ (spec k).2 ∈ zA ∧ 0 < (spec k).2 ∧ (spec k).2 ≤ n) ∨
      ((spec k).1 = 1 ∧ (spec k).2 < (n + 1) / 2) ∨
      ((spec k).1 = 2 ∧ (spec k).2 ∈ zS ∧ (spec k).2 ≤ n)) :
    ∀ k < n + 1, ∑ i ∈ range (n + 1), (rowI n (spec k).1 (spec k).2 i : ℚ) * A i =
      ((if (spec k).1 = 0 ∧ (spec k).2 = 0 then 1 else 0 : ℤ) : ℚ) := by
  obtain ⟨h0, hz, hp, hs⟩ := h
  intro k hk
  rcases hspec k hk with hk0 | ⟨ht, hm, hpos, hle⟩ | ⟨ht, hlt⟩ | ⟨ht, hm, hle⟩
  · rw [hk0]
    simp [rowI, h0]
  · have hne : (spec k).2 ≠ 0 := by omega
    simp [rowI, ht, hne, Finset.mem_range, Nat.lt_succ_of_le hle, hz _ hm]
  · have h1 : (spec k).1 ≠ 0 := by omega
    have hs' : (spec k).2 ≤ n := by omega
    have := hp (spec k).2 hlt
    rw [sum_P n _ hs'] at this
    have hD : (2 : ℚ) ^ n * Nat.choose n (spec k).2 ≠ 0 := by
      have : (0 : ℚ) < Nat.choose n (spec k).2 := by exact_mod_cast Nat.choose_pos hs'
      positivity
    simpa [rowI, h1, ht, hD] using this
  · have h1 : (spec k).1 ≠ 0 := by omega
    have h2 : (spec k).1 ≠ 1 := by omega
    have := hs _ hm
    rw [sum_S] at this
    simpa [rowI, h1, h2] using this

theorem face_target_of_checks (n : ℕ) (zA zS : List ℕ) (l : List ℤ)
    (h0 : l.getD 0 0 = 1) (hz : ∀ j ∈ zA, l.getD j 0 = 0)
    (hp : ∀ s < (n + 1) / 2, ∑ j ∈ range (n + 1), pNum n s j * l.getD j 0 = 0)
    (hs : ∀ i ∈ zS, ∑ j ∈ range (n + 1), shadowNum n i j * l.getD j 0 = 0) :
    Face n zA zS (fun j => ((l.getD j 0 : ℤ) : ℚ)) := by
  refine ⟨?_, fun j hj => ?_, fun s hs' => ?_, fun i hi => ?_⟩
  · show ((l.getD 0 0 : ℤ) : ℚ) = 1
    rw [h0]; norm_num
  · show ((l.getD j 0 : ℤ) : ℚ) = 0
    rw [hz j hj]; norm_num
  · rw [sum_P n s (by omega)]
    have : (∑ j ∈ range (n + 1), (pNum n s j : ℚ) * ((l.getD j 0 : ℤ) : ℚ)) = 0 := by
      have := congrArg (fun z : ℤ => (z : ℚ)) (hp s hs')
      simpa using this
    rw [this]; simp
  · rw [sum_S]
    have : (∑ j ∈ range (n + 1), (shadowNum n i j : ℚ) * ((l.getD j 0 : ℤ) : ℚ)) = 0 := by
      have := congrArg (fun z : ℤ => (z : ℚ)) (hs i hi)
      simpa using this
    rw [this]; simp

/-! ### `n = 7` -/

/-- Pauli weights forced to vanish at `n = 7`. -/
def zA7 : List ℕ := [1, 2, 3]
/-- Rains shadow coefficients forced to vanish at `n = 7`. -/
def zS7 : List ℕ := [0, 2]
/-- The unique equality profile `(A_0, …, A_7)` at `n = 7`. -/
def tgtL7 : List ℤ := [1, 0, 0, 0, 35, 42, 28, 22]
def tgt7 (j : ℕ) : ℚ := ((tgtL7.getD j 0 : ℤ) : ℚ)
/-- `2^7 S_i` for the reconstructed Rains shadow vector. -/
def shNum7 : List ℤ := [0, 224, 0, 1120, 0, 11424, 0, 3616]
def sh7 (i : ℕ) : ℚ := ((shNum7.getD i 0 : ℤ) : ℚ) / 2 ^ 7
/-- The shadow vector as stated in the paper. -/
def shLit7 : List ℚ := [(0 : ℚ), (7/4 : ℚ), (0 : ℚ), (35/4 : ℚ), (0 : ℚ), (357/4 : ℚ), (0 : ℚ), (113/4 : ℚ)]
/-- Selected independent rows (type, index) for the uniqueness certificate. -/
def spec7 : List (ℕ × ℕ) := [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3)]
/-- Integer left inverse of the selected rows: `L M = dd · 1`. -/
def Ltab7 : List (List ℤ) := [
    [8, 0, 0, 0, 0, 0, 0, 0],
    [0, 8, 0, 0, 0, 0, 0, 0],
    [0, 0, 8, 0, 0, 0, 0, 0],
    [0, 0, 0, 8, 0, 0, 0, 0],
    [280, 80, 0, -16, 0, 0, 0, -1],
    [336, 24, -16, 0, 0, 0, -2, 3],
    [224, -80, -8, 16, 0, -4, 4, -3],
    [176, -32, 16, -8, -8, 4, -2, 1]]
def dd7 : ℤ := 8

theorem face7_target : Face 7 zA7 zS7 (tgt7) :=
  face_target_of_checks 7 zA7 zS7 tgtL7 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem face7_unique (A : ℕ → ℚ) (h : Face 7 zA7 zS7 A) : ∀ j ≤ 7, A j = tgt7 j := by
  have hrows := face_rows 7 zA7 zS7 A h (fun k => spec7.getD k (0, 0)) (by decide +kernel)
  have hc := unique_of_cert 7 (fun k => spec7.getD k (0, 0))
    (fun j k => (Ltab7.getD j []).getD k 0) dd7 (by decide +kernel) A _ hrows
  have hcol : ∀ j < 7 + 1, ∑ k ∈ range (7 + 1), (Ltab7.getD j []).getD k 0 *
      (if (spec7.getD k (0, 0)).1 = 0 ∧ (spec7.getD k (0, 0)).2 = 0 then 1 else 0 : ℤ) =
      dd7 * tgtL7.getD j 0 := by decide +kernel
  intro j hj
  have e := hc j (by omega)
  rw [hcol j (by omega)] at e
  have hd : (dd7 : ℚ) ≠ 0 := by unfold dd7; norm_num
  exact mul_left_cancel₀ hd (e.trans (by push_cast; rfl))

theorem face7_sum : ∑ j ∈ range (7 + 1), tgt7 j = 2 ^ 7 := by
  have h : (∑ j ∈ range (7 + 1), tgtL7.getD j 0 : ℤ) = 2 ^ 7 := by decide +kernel
  have := congrArg (fun z : ℤ => (z : ℚ)) h
  simp only [Int.cast_sum, Int.cast_pow, Int.cast_ofNat] at this
  simpa only [tgt7] using this

theorem face7_obj : ∑ j ∈ range (7 + 1), aCoef 7 (7 / 2) j * tgt7 j = 1/8 := by
  rw [sum_obj]
  have h : (∑ j ∈ range (7 + 1), objNum 7 j * tgtL7.getD j 0 : ℤ) = 35 := by decide +kernel
  have hc : Nat.choose 7 (7 / 2) = 35 := by decide +kernel
  have h2 := congrArg (fun z : ℤ => (z : ℚ)) h
  simp only [Int.cast_sum, Int.cast_mul] at h2
  simp only [tgt7]
  rw [h2, hc]
  norm_num

theorem face7_shadow (i : ℕ) (hi : i ≤ 7) :
    ∑ j ∈ range (7 + 1), shadowCoef 7 i j * tgt7 j = sh7 i := by
  rw [sum_S]
  have h : ∀ i < 7 + 1, (∑ j ∈ range (7 + 1), shadowNum 7 i j * tgtL7.getD j 0 : ℤ) =
      shNum7.getD i 0 := by decide +kernel
  have h2 := congrArg (fun z : ℤ => (z : ℚ)) (h i (by omega))
  simp only [Int.cast_sum, Int.cast_mul] at h2
  simp only [tgt7, sh7]
  rw [h2]

theorem sh7_values : (List.range (7 + 1)).map sh7 = shLit7 := by
  norm_num [sh7, shNum7, shLit7, List.range_succ]

theorem face7_nonneg : (∀ j ≤ 7, 0 ≤ tgt7 j) ∧ (∀ i ≤ 7, 0 ≤ sh7 i) := by
  have h1 : ∀ j < 7 + 1, 0 ≤ tgtL7.getD j 0 := by decide +kernel
  have h2 : ∀ i < 7 + 1, 0 ≤ shNum7.getD i 0 := by decide +kernel
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · have := h1 j (by omega)
    simp only [tgt7]; exact_mod_cast this
  · have := h2 i (by omega)
    simp only [sh7]; positivity

theorem face7_shadow_sum : ∑ i ∈ range (7 + 1), sh7 i = 2 ^ 7 := by
  have h : (∑ i ∈ range (7 + 1), shNum7.getD i 0 : ℤ) = 2 ^ 14 := by decide +kernel
  have h2 := congrArg (fun z : ℤ => (z : ℚ)) h
  simp only [Int.cast_sum] at h2
  simp only [sh7]
  rw [← Finset.sum_div, h2]
  norm_num [pow_mul]

/-! ### `n = 13` -/

/-- Pauli weights forced to vanish at `n = 13`. -/
def zA13 : List ℕ := [1, 2, 3, 4, 5]
/-- Rains shadow coefficients forced to vanish at `n = 13`. -/
def zS13 : List ℕ := [0, 1, 2, 6, 10]
/-- The unique equality profile `(A_0, …, A_13)` at `n = 13`. -/
def tgtL13 : List ℤ := [1, 0, 0, 0, 0, 0, 234, 546, 819, 1690, 2262, 1638, 780, 222]
def tgt13 (j : ℕ) : ℚ := ((tgtL13.getD j 0 : ℤ) : ℚ)
/-- `2^13 S_i` for the reconstructed Rains shadow vector. -/
def shNum13 : List ℤ := [0, 0, 0, 79872, 0, 239616, 0, 8466432, 0, 26890240, 0, 28514304, 0, 2918400]
def sh13 (i : ℕ) : ℚ := ((shNum13.getD i 0 : ℤ) : ℚ) / 2 ^ 13
/-- The shadow vector as stated in the paper. -/
def shLit13 : List ℚ := [(0 : ℚ), (0 : ℚ), (0 : ℚ), (39/4 : ℚ), (0 : ℚ), (117/4 : ℚ), (0 : ℚ), (2067/2 : ℚ), (0 : ℚ), (6565/2 : ℚ), (0 : ℚ), (13923/4 : ℚ), (0 : ℚ), (1425/4 : ℚ)]
/-- Selected independent rows (type, index) for the uniqueness certificate. -/
def spec13 : List (ℕ × ℕ) := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1)]
/-- Integer left inverse of the selected rows: `L M = dd · 1`. -/
def Ltab13 : List (List ℤ) := [
    [256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 256, 0, 0, 0, 0, 0, 0, 0, 0],
    [59904, 25088, 8192, 1536, -512, -512, 13, -11, 9, -7, 5, -3, 1, 1],
    [139776, 43520, 9728, 0, -512, -512, -65, 55, -45, 35, -25, 15, -9, -5],
    [209664, 23040, -10752, -4608, 0, 1536, 117, -99, 81, -63, 45, -35, 33, 9],
    [432640, 29440, -12800, -2560, 1536, 0, -65, 55, -45, 35, -41, 55, -65, -5],
    [579072, 9728, -4352, 4608, 512, -1536, -65, 55, -45, 3, 39, -65, 75, -5],
    [419328, -59904, -3584, 3840, -1536, 512, 117, -99, 17, 33, -51, 53, -51, 9],
    [199680, -57856, 6656, -1536, -256, 512, -65, -73, 83, -61, 39, -25, 19, -5],
    [56832, -13312, 6656, -1536, 512, -256, -243, 117, -55, 25, -11, 5, -3, 1]]
def dd13 : ℤ := 256

theorem face13_target : Face 13 zA13 zS13 (tgt13) :=
  face_target_of_checks 13 zA13 zS13 tgtL13 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem face13_unique (A : ℕ → ℚ) (h : Face 13 zA13 zS13 A) : ∀ j ≤ 13, A j = tgt13 j := by
  have hrows := face_rows 13 zA13 zS13 A h (fun k => spec13.getD k (0, 0)) (by decide +kernel)
  have hc := unique_of_cert 13 (fun k => spec13.getD k (0, 0))
    (fun j k => (Ltab13.getD j []).getD k 0) dd13 (by decide +kernel) A _ hrows
  have hcol : ∀ j < 13 + 1, ∑ k ∈ range (13 + 1), (Ltab13.getD j []).getD k 0 *
      (if (spec13.getD k (0, 0)).1 = 0 ∧ (spec13.getD k (0, 0)).2 = 0 then 1 else 0 : ℤ) =
      dd13 * tgtL13.getD j 0 := by decide +kernel
  intro j hj
  have e := hc j (by omega)
  rw [hcol j (by omega)] at e
  have hd : (dd13 : ℚ) ≠ 0 := by unfold dd13; norm_num
  exact mul_left_cancel₀ hd (e.trans (by push_cast; rfl))

theorem face13_sum : ∑ j ∈ range (13 + 1), tgt13 j = 2 ^ 13 := by
  have h : (∑ j ∈ range (13 + 1), tgtL13.getD j 0 : ℤ) = 2 ^ 13 := by decide +kernel
  have := congrArg (fun z : ℤ => (z : ℚ)) h
  simp only [Int.cast_sum, Int.cast_pow, Int.cast_ofNat] at this
  simpa only [tgt13] using this

theorem face13_obj : ∑ j ∈ range (13 + 1), aCoef 13 (13 / 2) j * tgt13 j = 25/1408 := by
  rw [sum_obj]
  have h : (∑ j ∈ range (13 + 1), objNum 13 j * tgtL13.getD j 0 : ℤ) = 1950 := by decide +kernel
  have hc : Nat.choose 13 (13 / 2) = 1716 := by decide +kernel
  have h2 := congrArg (fun z : ℤ => (z : ℚ)) h
  simp only [Int.cast_sum, Int.cast_mul] at h2
  simp only [tgt13]
  rw [h2, hc]
  norm_num

theorem face13_shadow (i : ℕ) (hi : i ≤ 13) :
    ∑ j ∈ range (13 + 1), shadowCoef 13 i j * tgt13 j = sh13 i := by
  rw [sum_S]
  have h : ∀ i < 13 + 1, (∑ j ∈ range (13 + 1), shadowNum 13 i j * tgtL13.getD j 0 : ℤ) =
      shNum13.getD i 0 := by decide +kernel
  have h2 := congrArg (fun z : ℤ => (z : ℚ)) (h i (by omega))
  simp only [Int.cast_sum, Int.cast_mul] at h2
  simp only [tgt13, sh13]
  rw [h2]

theorem sh13_values : (List.range (13 + 1)).map sh13 = shLit13 := by
  norm_num [sh13, shNum13, shLit13, List.range_succ]

theorem face13_nonneg : (∀ j ≤ 13, 0 ≤ tgt13 j) ∧ (∀ i ≤ 13, 0 ≤ sh13 i) := by
  have h1 : ∀ j < 13 + 1, 0 ≤ tgtL13.getD j 0 := by decide +kernel
  have h2 : ∀ i < 13 + 1, 0 ≤ shNum13.getD i 0 := by decide +kernel
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · have := h1 j (by omega)
    simp only [tgt13]; exact_mod_cast this
  · have := h2 i (by omega)
    simp only [sh13]; positivity

theorem face13_shadow_sum : ∑ i ∈ range (13 + 1), sh13 i = 2 ^ 13 := by
  have h : (∑ i ∈ range (13 + 1), shNum13.getD i 0 : ℤ) = 2 ^ 26 := by decide +kernel
  have h2 := congrArg (fun z : ℤ => (z : ℚ)) h
  simp only [Int.cast_sum] at h2
  simp only [sh13]
  rw [← Finset.sum_div, h2]
  norm_num [pow_mul]

/-! ### `n = 19` -/

/-- Pauli weights forced to vanish at `n = 19`. -/
def zA19 : List ℕ := [1, 2, 3, 4, 5, 6, 7]
/-- Rains shadow coefficients forced to vanish at `n = 19`. -/
def zS19 : List ℕ := [0, 1, 2, 3, 4, 8, 12, 16]
/-- The unique equality profile `(A_0, …, A_19)` at `n = 19`. -/
def tgtL19 : List ℤ := [1, 0, 0, 0, 0, 0, 0, 0, 1482, 4408, 8208, 24168, 55176, 82992, 102144, 106704, 81453, 41496, 13680, 2376]
def tgt19 (j : ℕ) : ℚ := ((tgtL19.getD j 0 : ℤ) : ℚ)
/-- `2^19 S_i` for the reconstructed Rains shadow vector. -/
def shNum19 : List ℤ := [0, 0, 0, 0, 0, 29884416, 0, 29884416, 0, 4293394432, 0, 25491406848, 0, 88069373952, 0, 110064304128, 0, 44677201920, 0, 2222456832]
def sh19 (i : ℕ) : ℚ := ((shNum19.getD i 0 : ℤ) : ℚ) / 2 ^ 19
/-- The shadow vector as stated in the paper. -/
def shLit19 : List ℚ := [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (57 : ℚ), (0 : ℚ), (57 : ℚ), (0 : ℚ), (8189 : ℚ), (0 : ℚ), (48621 : ℚ), (0 : ℚ), (167979 : ℚ), (0 : ℚ), (209931 : ℚ), (0 : ℚ), (85215 : ℚ), (0 : ℚ), (4239 : ℚ)]
/-- Selected independent rows (type, index) for the uniqueness certificate. -/
def spec19 : List (ℕ × ℕ) := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 1), (2, 3)]
/-- Integer left inverse of the selected rows: `L M = dd · 1`. -/
def Ltab19 : List (List ℤ) := [
    [16384, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 16384, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 16384, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 16384, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 16384, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 16384, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 16384, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 16384, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [24281088, 11403264, 4718592, 1703936, 409600, 32768, -65536, -32768, 1140, -816, 560, -364, 220, -120, 56, -20, 4, 0, 9, 1],
    [72220672, 28475392, 10092544, 2621440, 557056, -114688, -32768, -65536, -5852, 4216, -2920, 1924, -1188, 672, -336, 140, -44, 8, -53, -5],
    [134479872, 33161216, 2523136, -2228224, -1572864, -163840, 81920, 163840, 9196, -6800, 4880, -3380, 2244, -1416, 840, -460, 220, -96, 127, 7],
    [395968512, 84148224, 6160384, -3768320, -1736704, 0, 163840, 81920, 1596, -408, -440, 988, -1276, 1344, -1232, 980, -692, 504, -171, 5],
    [904003584, 164364288, 17301504, 262144, 1622016, 327680, 0, -327680, -17784, 11424, -6560, 3016, -616, -816, 1456, -1608, 1576, -1536, 186, -22],
    [1359740928, 123863040, -16515072, -3670016, 1376256, 573440, -327680, 0, 9576, -5712, 2800, -728, -616, 1344, -1824, 2296, -2744, 3024, -210, 14],
    [1673527296, -786432, -47579136, -4456448, 131072, -327680, -81920, 327680, 15960, -11424, 7840, -5096, 3080, -2192, 2320, -2968, 3640, -4032, 126, 14],
    [1748238336, -88080384, -21233664, 6946816, 720896, -917504, 327680, -81920, -18696, 12240, -7280, 3640, -2168, 2176, -2720, 3240, -3560, 3696, 138, -22],
    [1334525952, -144310272, 9437184, 8519680, -999424, 163840, 65536, -163840, -1596, 2448, -2960, 1124, 972, -2264, 2712, -2660, 2452, -2304, -339, 5],
    [679870464, -137674752, 16908288, -1048576, -1409024, 573440, -163840, 65536, 12084, -9384, 3064, 788, -2228, 2336, -1936, 1468, -1116, 936, 279, 7],
    [224133120, -63832064, 13582336, -3801088, 393216, -32768, -16384, 32768, -6916, -3024, 4432, -3492, 2292, -1384, 808, -476, 300, -224, -109, -5],
    [38928384, -10747904, 4587520, -1097728, 491520, -131072, 32768, -16384, -15092, 7240, -3416, 1580, -716, 320, -144, 68, -36, 24, 17, 1]]
def dd19 : ℤ := 16384

theorem face19_target : Face 19 zA19 zS19 (tgt19) :=
  face_target_of_checks 19 zA19 zS19 tgtL19 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem face19_unique (A : ℕ → ℚ) (h : Face 19 zA19 zS19 A) : ∀ j ≤ 19, A j = tgt19 j := by
  have hrows := face_rows 19 zA19 zS19 A h (fun k => spec19.getD k (0, 0)) (by decide +kernel)
  have hc := unique_of_cert 19 (fun k => spec19.getD k (0, 0))
    (fun j k => (Ltab19.getD j []).getD k 0) dd19 (by decide +kernel) A _ hrows
  have hcol : ∀ j < 19 + 1, ∑ k ∈ range (19 + 1), (Ltab19.getD j []).getD k 0 *
      (if (spec19.getD k (0, 0)).1 = 0 ∧ (spec19.getD k (0, 0)).2 = 0 then 1 else 0 : ℤ) =
      dd19 * tgtL19.getD j 0 := by decide +kernel
  intro j hj
  have e := hc j (by omega)
  rw [hcol j (by omega)] at e
  have hd : (dd19 : ℚ) ≠ 0 := by unfold dd19; norm_num
  exact mul_left_cancel₀ hd (e.trans (by push_cast; rfl))

theorem face19_sum : ∑ j ∈ range (19 + 1), tgt19 j = 2 ^ 19 := by
  have h : (∑ j ∈ range (19 + 1), tgtL19.getD j 0 : ℤ) = 2 ^ 19 := by decide +kernel
  have := congrArg (fun z : ℤ => (z : ℚ)) h
  simp only [Int.cast_sum, Int.cast_pow, Int.cast_ofNat] at this
  simpa only [tgt19] using this

theorem face19_obj : ∑ j ∈ range (19 + 1), aCoef 19 (19 / 2) j * tgt19 j = 93/38896 := by
  rw [sum_obj]
  have h : (∑ j ∈ range (19 + 1), objNum 19 j * tgtL19.getD j 0 : ℤ) = 113088 := by decide +kernel
  have hc : Nat.choose 19 (19 / 2) = 92378 := by decide +kernel
  have h2 := congrArg (fun z : ℤ => (z : ℚ)) h
  simp only [Int.cast_sum, Int.cast_mul] at h2
  simp only [tgt19]
  rw [h2, hc]
  norm_num

theorem face19_shadow (i : ℕ) (hi : i ≤ 19) :
    ∑ j ∈ range (19 + 1), shadowCoef 19 i j * tgt19 j = sh19 i := by
  rw [sum_S]
  have h : ∀ i < 19 + 1, (∑ j ∈ range (19 + 1), shadowNum 19 i j * tgtL19.getD j 0 : ℤ) =
      shNum19.getD i 0 := by decide +kernel
  have h2 := congrArg (fun z : ℤ => (z : ℚ)) (h i (by omega))
  simp only [Int.cast_sum, Int.cast_mul] at h2
  simp only [tgt19, sh19]
  rw [h2]

theorem sh19_values : (List.range (19 + 1)).map sh19 = shLit19 := by
  norm_num [sh19, shNum19, shLit19, List.range_succ]

theorem face19_nonneg : (∀ j ≤ 19, 0 ≤ tgt19 j) ∧ (∀ i ≤ 19, 0 ≤ sh19 i) := by
  have h1 : ∀ j < 19 + 1, 0 ≤ tgtL19.getD j 0 := by decide +kernel
  have h2 : ∀ i < 19 + 1, 0 ≤ shNum19.getD i 0 := by decide +kernel
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · have := h1 j (by omega)
    simp only [tgt19]; exact_mod_cast this
  · have := h2 i (by omega)
    simp only [sh19]; positivity

theorem face19_shadow_sum : ∑ i ∈ range (19 + 1), sh19 i = 2 ^ 19 := by
  have h : (∑ i ∈ range (19 + 1), shNum19.getD i 0 : ℤ) = 2 ^ 38 := by decide +kernel
  have h2 := congrArg (fun z : ℤ => (z : ℚ)) h
  simp only [Int.cast_sum] at h2
  simp only [sh19]
  rw [← Finset.sum_div, h2]
  norm_num [pow_mul]

/-! ### `n = 20` -/

/-- Pauli weights forced to vanish at `n = 20`. -/
def zA20 : List ℕ := [1, 2, 3, 4, 5, 6, 7]
/-- Rains shadow coefficients forced to vanish at `n = 20`. -/
def zS20 : List ℕ := [0, 2, 4]
/-- The unique equality profile `(A_0, …, A_20)` at `n = 20`. -/
def tgtL20 : List ℤ := [1, 0, 0, 0, 0, 0, 0, 0, 990, 4160, 9552, 25920, 65820, 120960, 174240, 210048, 200745, 141120, 69520, 22080, 3420]
def tgt20 (j : ℕ) : ℚ := ((tgtL20.getD j 0 : ℤ) : ℚ)
/-- `2^20 S_i` for the reconstructed Rains shadow vector. -/
def shNum20 : List ℤ := [0, 0, 0, 0, 0, 0, 125829120, 0, 1132462080, 0, 23580377088, 0, 130484797440, 0, 374844948480, 0, 414103633920, 0, 148520304640, 0, 6719275008]
def sh20 (i : ℕ) : ℚ := ((shNum20.getD i 0 : ℤ) : ℚ) / 2 ^ 20
/-- The shadow vector as stated in the paper. -/
def shLit20 : List ℚ := [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (120 : ℚ), (0 : ℚ), (1080 : ℚ), (0 : ℚ), (22488 : ℚ), (0 : ℚ), (124440 : ℚ), (0 : ℚ), (357480 : ℚ), (0 : ℚ), (394920 : ℚ), (0 : ℚ), (141640 : ℚ), (0 : ℚ), (6408 : ℚ)]
/-- Selected independent rows (type, index) for the uniqueness certificate. -/
def spec20 : List (ℕ × ℕ) := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 2), (2, 4)]
/-- Integer left inverse of the selected rows: `L M = dd · 1`. -/
def Ltab20 : List (List ℤ) := [
    [65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [64880640, 32243712, 13369344, 5505024, 1310720, 327680, -196608, -65536, 6600, -4320, 2688, -1568, 840, -400, 160, -48, 8, 0, 45, 9, 1],
    [272629760, 113377280, 46137344, 13107200, 4194304, -327680, 0, -393216, -28000, 18576, -11776, 7056, -3936, 2000, -896, 336, -96, 16, -260, -44, -4],
    [625999872, 200802304, 45744128, 4718592, -3145728, -917504, -196608, 393216, 24464, -17776, 12608, -8688, 5776, -3664, 2176, -1168, 528, -176, 714, 74, 2],
    [1698693120, 423100416, 46137344, -11403264, -12582912, -655360, 0, 983040, 48160, -26576, 12160, -3280, -1504, 3440, -3584, 2800, -1760, 816, -1620, -44, 12],
    [4313579520, 886308864, 107741184, -13893632, -131072, -327680, 1638400, -983040, -75720, 43344, -21312, 7312, 696, -4480, 5536, -5088, 3832, -2064, 3795, 15, -17],
    [7927234560, 1127743488, 25165824, -22020096, 8388608, 3604480, 0, -1310720, -50880, 34464, -23040, 15520, -10944, 8480, -7424, 6688, -5312, 2976, -7560, -24, -8],
    [11418992640, 714080256, -221773824, -34603008, 2097152, 3932160, -2949120, 1310720, 131040, -79968, 45696, -24416, 12768, -7840, 6144, -5152, 3808, -2016, 11340, -84, 28],
    [13765705728, -78643200, -276824064, 1572864, 8388608, -4980736, 0, 983040, -1728, -3744, 5376, -4256, 1344, 480, -512, -288, 832, -672, -13128, 264, -8],
    [13156024320, -824967168, -104595456, 57409536, 4456448, -5570560, 2555904, -983040, -108360, 67776, -38400, 17920, -8392, 6000, -6176, 6160, -5000, 2784, 12195, -201, -17],
    [9248440320, -1190854656, 62914560, 42467328, -12582912, 2949120, 0, -393216, 37920, -16944, 3072, -2864, 6688, -9200, 9344, -7792, 5408, -2736, -8820, -60, 12],
    [4556062720, -940048384, 134021120, -12058624, -7340032, 3276800, -1114112, 393216, 46480, -36144, 11328, 3664, -9072, 9200, -7296, 5040, -3056, 1424, 4490, 170, 2],
    [1447034880, -394788864, 96468992, -23789568, 4194304, -655360, 0, 65536, -38240, -5776, 14208, -12176, 8352, -5200, 3072, -1744, 928, -400, -1380, -92, -4],
    [224133120, -68419584, 25427968, -7077888, 2686976, -720896, 196608, -65536, -57272, 27088, -12608, 5776, -2616, 1184, -544, 256, -120, 48, 189, 17, 1]]
def dd20 : ℤ := 65536

theorem face20_target : Face 20 zA20 zS20 (tgt20) :=
  face_target_of_checks 20 zA20 zS20 tgtL20 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem face20_unique (A : ℕ → ℚ) (h : Face 20 zA20 zS20 A) : ∀ j ≤ 20, A j = tgt20 j := by
  have hrows := face_rows 20 zA20 zS20 A h (fun k => spec20.getD k (0, 0)) (by decide +kernel)
  have hc := unique_of_cert 20 (fun k => spec20.getD k (0, 0))
    (fun j k => (Ltab20.getD j []).getD k 0) dd20 (by decide +kernel) A _ hrows
  have hcol : ∀ j < 20 + 1, ∑ k ∈ range (20 + 1), (Ltab20.getD j []).getD k 0 *
      (if (spec20.getD k (0, 0)).1 = 0 ∧ (spec20.getD k (0, 0)).2 = 0 then 1 else 0 : ℤ) =
      dd20 * tgtL20.getD j 0 := by decide +kernel
  intro j hj
  have e := hc j (by omega)
  rw [hcol j (by omega)] at e
  have hd : (dd20 : ℚ) ≠ 0 := by unfold dd20; norm_num
  exact mul_left_cancel₀ hd (e.trans (by push_cast; rfl))

theorem face20_sum : ∑ j ∈ range (20 + 1), tgt20 j = 2 ^ 20 := by
  have h : (∑ j ∈ range (20 + 1), tgtL20.getD j 0 : ℤ) = 2 ^ 20 := by decide +kernel
  have := congrArg (fun z : ℤ => (z : ℚ)) h
  simp only [Int.cast_sum, Int.cast_pow, Int.cast_ofNat] at this
  simpa only [tgt20] using this

theorem face20_obj : ∑ j ∈ range (20 + 1), aCoef 20 (20 / 2) j * tgt20 j = 1193/739024 := by
  rw [sum_obj]
  have h : (∑ j ∈ range (20 + 1), objNum 20 j * tgtL20.getD j 0 : ℤ) = 305408 := by decide +kernel
  have hc : Nat.choose 20 (20 / 2) = 184756 := by decide +kernel
  have h2 := congrArg (fun z : ℤ => (z : ℚ)) h
  simp only [Int.cast_sum, Int.cast_mul] at h2
  simp only [tgt20]
  rw [h2, hc]
  norm_num

theorem face20_shadow (i : ℕ) (hi : i ≤ 20) :
    ∑ j ∈ range (20 + 1), shadowCoef 20 i j * tgt20 j = sh20 i := by
  rw [sum_S]
  have h : ∀ i < 20 + 1, (∑ j ∈ range (20 + 1), shadowNum 20 i j * tgtL20.getD j 0 : ℤ) =
      shNum20.getD i 0 := by decide +kernel
  have h2 := congrArg (fun z : ℤ => (z : ℚ)) (h i (by omega))
  simp only [Int.cast_sum, Int.cast_mul] at h2
  simp only [tgt20, sh20]
  rw [h2]

theorem sh20_values : (List.range (20 + 1)).map sh20 = shLit20 := by
  norm_num [sh20, shNum20, shLit20, List.range_succ]

theorem face20_nonneg : (∀ j ≤ 20, 0 ≤ tgt20 j) ∧ (∀ i ≤ 20, 0 ≤ sh20 i) := by
  have h1 : ∀ j < 20 + 1, 0 ≤ tgtL20.getD j 0 := by decide +kernel
  have h2 : ∀ i < 20 + 1, 0 ≤ shNum20.getD i 0 := by decide +kernel
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · have := h1 j (by omega)
    simp only [tgt20]; exact_mod_cast this
  · have := h2 i (by omega)
    simp only [sh20]; positivity

theorem face20_shadow_sum : ∑ i ∈ range (20 + 1), sh20 i = 2 ^ 20 := by
  have h : (∑ i ∈ range (20 + 1), shNum20.getD i 0 : ℤ) = 2 ^ 40 := by decide +kernel
  have h2 := congrArg (fun z : ℤ => (z : ℚ)) h
  simp only [Int.cast_sum] at h2
  simp only [sh20]
  rw [← Finset.sum_div, h2]
  norm_num [pow_mul]

/-! ### Non-integrality of the shadow at `n = 7, 13` -/

theorem sh7_one : sh7 1 = 7 / 4 := by norm_num [sh7, shNum7]

theorem sh13_three : sh13 3 = 39 / 4 := by norm_num [sh13, shNum13]

/-- At `n = 7` the unique equality profile has `S_1 = 7/4`, so its shadow coefficients are not all
integers: a state attaining the Rains bound `1/8` whose shadow coefficients are integers (e.g. a
stabilizer state, a fact not formalized here) cannot exist. -/
theorem rains_face7_no_integral_shadow (A : ℕ → ℚ) (h : Face 7 zA7 zS7 A)
    (hS : ∀ i ≤ 7, ∃ z : ℤ, ∑ j ∈ range (7 + 1), shadowCoef 7 i j * A j = z) : False := by
  have hu := face7_unique A h
  obtain ⟨z, hz⟩ := hS 1 (by norm_num)
  have : ∑ j ∈ range (7 + 1), shadowCoef 7 1 j * A j =
      ∑ j ∈ range (7 + 1), shadowCoef 7 1 j * tgt7 j :=
    Finset.sum_congr rfl fun j hj => by rw [hu j (by simp at hj; omega)]
  rw [this, face7_shadow 1 (by norm_num), sh7_one] at hz
  have h4 : (7 : ℚ) = 4 * z := by linarith
  have h5 : (7 : ℤ) = 4 * z := by exact_mod_cast h4
  omega

/-- At `n = 13` the unique equality profile has `S_3 = 39/4`. -/
theorem rains_face13_no_integral_shadow (A : ℕ → ℚ) (h : Face 13 zA13 zS13 A)
    (hS : ∀ i ≤ 13, ∃ z : ℤ, ∑ j ∈ range (13 + 1), shadowCoef 13 i j * A j = z) : False := by
  have hu := face13_unique A h
  obtain ⟨z, hz⟩ := hS 3 (by norm_num)
  have : ∑ j ∈ range (13 + 1), shadowCoef 13 3 j * A j =
      ∑ j ∈ range (13 + 1), shadowCoef 13 3 j * tgt13 j :=
    Finset.sum_congr rfl fun j hj => by rw [hu j (by simp at hj; omega)]
  rw [this, face13_shadow 3 (by norm_num), sh13_three] at hz
  have h4 : (39 : ℚ) = 4 * z := by linarith
  have h5 : (39 : ℤ) = 4 * z := by exact_mod_cast h4
  omega

end FormalResearch.FourQubitEntropy.SevenQubitRains
