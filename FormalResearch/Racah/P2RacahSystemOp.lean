module

public import FormalResearch.Racah.P2RacahSystemLattice
public import FormalResearch.Racah.P2RacahLatticeEnd

/-!
# The Hamiltonian `H_R` on `ℓ²(𝒞, ω)` as a concrete real matrix (Weyl P2, `thm:6jfiniteRacah`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `eq:RacahHamiltonian`, `eq:RacahDetailedBalance`.

The physical lattice `𝒞 = {c_min, ..., c_max}` is indexed by `i : Fin (D+1)`, `c_i = c_min + i`, where
`D = c_max - c_min` (`RacahSystem`: the paper's integrality conventions and `D + 1 = |𝒞|`; such a `D`
exists exactly when the lattice is non-empty, `RacahSystem.exists`).  The weight is
`ω_i = (2c_i+1)/(2AB)` (`wgtR`), and

`(H_R q)_i = -a⁺_{c_i} q_{i+1} + b_{c_i} q_i - a⁻_{c_i} q_{i-1}` (`HR`, the absent boundary terms
omitted, `b_c = -κ_R/2` at a physical endpoint `c = 0`, `bRow`).

## Results

* `RacahSystem.exists`, `RacahSystem.A_pos`, `RacahSystem.B_pos`: non-emptiness gives `D`, and `A, B > 0`.
* `HR_mulVec`: the row formula; `HR_selfadjoint_entries`: `ω_i H_{ij} = ω_j H_{ji}` (detailed balance,
  `eq:RacahDetailedBalance`); `HR_selfadjoint`: `⟨x, H y⟩_ω = ⟨H x, y⟩_ω`;
  `HR_symmetrised_isHermitian`: `D^{1/2} H D^{-1/2}` is a real symmetric (Hermitian) matrix.
-/

@[expose] public section

namespace FormalResearch.Racah.SixJ

open FormalResearch.Wigner

/-- The paper's integrality conventions together with `D + 1 = |𝒞|`, i.e. `D = c_max - c_min`
(`eq:cminRacah`-`eq:Racahdimension`). -/
structure RacahSystem (a b m n : ℚ) (D : ℕ) : Prop where
  labels : RacahLabels a b m n
  dim : (D : ℚ) = cMax a b m n - cMin a b m n

/-- `c_min ≤ c_max` forces `A, B ≥ 1/2` (`f_1 ≥ f_0 ≥ 0`, `f_1 = 2 min(A,B) - 1`). -/
lemma AB_pos {a b m n : ℚ} (hne : cMin a b m n ≤ cMax a b m n) :
    (0 : ℝ) < wA a n ∧ (0 : ℝ) < wB b m := by
  have h := cMax_sub_cMin a b m n
  have h1 := fMax_centered a b m n
  have h0 : 0 ≤ fMin m n := le_max_of_le_left (abs_nonneg _)
  have h2 : (1 : ℚ) / 2 ≤ min (a + (n + 1) / 2) (b + (m + 1) / 2) := by linarith
  have hA : (1 : ℚ) / 2 ≤ a + (n + 1) / 2 := le_trans h2 (min_le_left _ _)
  have hB : (1 : ℚ) / 2 ≤ b + (m + 1) / 2 := le_trans h2 (min_le_right _ _)
  have hA' := (Rat.cast_le (K := ℝ)).2 hA
  have hB' := (Rat.cast_le (K := ℝ)).2 hB
  push_cast at hA' hB'
  unfold wA wB
  constructor <;> linarith

lemma cMin_nonneg (a b m n : ℚ) : 0 ≤ cMin a b m n := le_max_of_le_left (abs_nonneg _)

/-- A non-empty lattice with the paper's integrality conventions has an integer dimension. -/
theorem RacahSystem.exists {a b m n : ℚ} (hl : RacahLabels a b m n)
    (hne : cMin a b m n ≤ cMax a b m n) : ∃ D : ℕ, RacahSystem a b m n D := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩, ⟨s, hs⟩⟩ := id hl
  have e1 := two_cMin hp hq hs
  have e2 := two_cMax hp hq hr hs
  obtain ⟨Z, hZ⟩ : ∃ Z : ℤ, Z = min (p + q) (p + q + 2 * r - 2 * s) -
      max |p - q| |q - p + 2 * s| := ⟨_, rfl⟩
  have hZ0 : 0 ≤ Z := by
    have h1 : 2 * cMin a b m n ≤ 2 * cMax a b m n := by linarith
    rw [e1, e2] at h1
    have h2 := Int.cast_le.1 h1
    omega
  have hZe : 2 ∣ Z := by
    rw [hZ]; simp only [abs_eq_max_neg]; omega
  obtain ⟨z, hz⟩ := hZe
  have hzq : (Z : ℚ) = 2 * z := by exact_mod_cast hz
  refine ⟨z.toNat, hl, ?_⟩
  have h3 : ((z.toNat : ℤ) : ℚ) = (z : ℚ) := by exact_mod_cast Int.toNat_of_nonneg (by omega)
  have h4 : (Z : ℚ) = (((min (p + q) (p + q + 2 * r - 2 * s) : ℤ) : ℚ)) -
      (((max |p - q| |q - p + 2 * s| : ℤ) : ℚ)) := by rw [hZ]; push_cast; rfl
  have h5 : 2 * (cMax a b m n - cMin a b m n) = Z := by
    rw [mul_sub, e1, e2, h4]
  push_cast at h3
  linarith

/-! ### The matrix `H_R` -/

/-- The lattice point `c_i = c_min + i`. -/
def cPt (a b m n : ℚ) {D : ℕ} (i : Fin (D + 1)) : ℚ := cMin a b m n + (i : ℕ)

/-- The rank `f_j = f_0 + j`. -/
def fPt (m n : ℚ) {D : ℕ} (j : Fin (D + 1)) : ℚ := fMin m n + (j : ℕ)

/-- The lattice weight `ω_i = (2c_i+1)/(2AB)` (`eq:Racahweightcell`). -/
noncomputable def wgtR (a b m n : ℚ) {D : ℕ} (i : Fin (D + 1)) : ℝ :=
  omegaW (wA a n) (wB b m) (cPt a b m n i)

/-- The diagonal coefficient: `b_c` (`eq:Racahdiag`), and `b_0 = -κ_R/2` at a physical endpoint
`c = 0` (`eq:Racahdiagzero`). -/
noncomputable def bRow (A B m n c : ℝ) : ℝ :=
  if c = 0 then bDiagZero A B m n else bDiag A B m n c

/-- The superdiagonal part `(i, i+1) ↦ -a⁺_{c_i}`. -/
noncomputable def HRup (a b m n : ℚ) (D : ℕ) : Matrix (Fin (D + 1)) (Fin (D + 1)) ℝ :=
  fun i j => if (j : ℕ) = (i : ℕ) + 1 then -(aPlus a b m n (cPt a b m n i)) else 0

/-- The subdiagonal part `(i, i-1) ↦ -a⁻_{c_i}`. -/
noncomputable def HRlo (a b m n : ℚ) (D : ℕ) : Matrix (Fin (D + 1)) (Fin (D + 1)) ℝ :=
  fun i j => if (j : ℕ) + 1 = (i : ℕ) then -(aMinus a b m n (cPt a b m n i)) else 0

/-- The diagonal part `i ↦ b_{c_i}`. -/
noncomputable def HRdiag (a b m n : ℚ) (D : ℕ) : Matrix (Fin (D + 1)) (Fin (D + 1)) ℝ :=
  Matrix.diagonal fun i => bRow (wA a n) (wB b m) m n (cPt a b m n i)

/-- **`eq:RacahHamiltonian`**: `(H_R q)_c = -a_c⁺ q_{c+1} + b_c q_c - a_c⁻ q_{c-1}` on the physical
lattice `{c_min, ..., c_max}` indexed by `Fin (D+1)`, absent boundary terms omitted. -/
noncomputable def HR (a b m n : ℚ) (D : ℕ) : Matrix (Fin (D + 1)) (Fin (D + 1)) ℝ :=
  HRup a b m n D + HRlo a b m n D + HRdiag a b m n D

lemma sum_ite_succ {D : ℕ} (k : ℕ) (X : ℝ) (q : Fin (D + 1) → ℝ) :
    ∑ j : Fin (D + 1), (if (j : ℕ) = k then X else 0) * q j =
      if h : k < D + 1 then X * q ⟨k, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨k, h⟩ : Fin (D + 1))]
    · simp
    · intro j _ hj
      have : (j : ℕ) ≠ k := fun e => hj (Fin.ext e)
      simp [this]
    · simp
  · apply Finset.sum_eq_zero
    intro j _
    have : (j : ℕ) ≠ k := by have := j.2; omega
    simp [this]

lemma sum_ite_pred {D : ℕ} (i : Fin (D + 1)) (X : ℝ) (q : Fin (D + 1) → ℝ) :
    ∑ j : Fin (D + 1), (if (j : ℕ) + 1 = (i : ℕ) then X else 0) * q j =
      if h : 0 < (i : ℕ) then X * q ⟨(i : ℕ) - 1, by omega⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨(i : ℕ) - 1, by omega⟩ : Fin (D + 1))]
    · have : (i : ℕ) - 1 + 1 = (i : ℕ) := by omega
      simp [this]
    · intro j _ hj
      have : (j : ℕ) + 1 ≠ (i : ℕ) := by
        intro e; apply hj; apply Fin.ext; simp only; omega
      simp [this]
    · simp
  · apply Finset.sum_eq_zero
    intro j _
    have : (j : ℕ) + 1 ≠ (i : ℕ) := by omega
    simp [this]

/-- The row formula of `H_R` acting on an arbitrary vector (zero outside the lattice). -/
theorem HR_mulVec (a b m n : ℚ) (D : ℕ) (q : Fin (D + 1) → ℝ) (i : Fin (D + 1)) :
    (HR a b m n D).mulVec q i =
      -(aPlus a b m n (cPt a b m n i) *
          (if h : (i : ℕ) + 1 < D + 1 then q ⟨(i : ℕ) + 1, h⟩ else 0)) +
        bRow (wA a n) (wB b m) m n (cPt a b m n i) * q i -
        aMinus a b m n (cPt a b m n i) *
          (if h : 0 < (i : ℕ) then q ⟨(i : ℕ) - 1, by omega⟩ else 0) := by
  have hup : (HRup a b m n D).mulVec q i = -(aPlus a b m n (cPt a b m n i) *
      (if h : (i : ℕ) + 1 < D + 1 then q ⟨(i : ℕ) + 1, h⟩ else 0)) := by
    unfold Matrix.mulVec dotProduct HRup
    rw [sum_ite_succ]
    split_ifs <;> simp
  have hlo : (HRlo a b m n D).mulVec q i = -(aMinus a b m n (cPt a b m n i) *
      (if h : 0 < (i : ℕ) then q ⟨(i : ℕ) - 1, by omega⟩ else 0)) := by
    unfold Matrix.mulVec dotProduct HRlo
    rw [sum_ite_pred]
    split_ifs <;> simp
  have hdi : (HRdiag a b m n D).mulVec q i =
      bRow (wA a n) (wB b m) m n (cPt a b m n i) * q i := by
    unfold HRdiag
    rw [Matrix.mulVec_diagonal]
  unfold HR
  rw [Matrix.add_mulVec, Matrix.add_mulVec]
  simp only [Pi.add_apply]
  rw [hup, hlo, hdi]
  ring

/-! ### Self-adjointness (detailed balance) -/

lemma RacahSystem.hne {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) :
    cMin a b m n ≤ cMax a b m n := by
  have := h.dim
  have : (0 : ℚ) ≤ D := by positivity
  linarith

lemma cPt_cast_succ {a b m n : ℚ} {D : ℕ} (i j : Fin (D + 1)) (h : (j : ℕ) = (i : ℕ) + 1) :
    ((cPt a b m n j : ℚ) : ℝ) = ((cPt a b m n i : ℚ) : ℝ) + 1 := by
  unfold cPt
  rw [h]
  push_cast
  ring

lemma cPt_nonneg (a b m n : ℚ) {D : ℕ} (i : Fin (D + 1)) : (0 : ℝ) ≤ ((cPt a b m n i : ℚ) : ℝ) := by
  have h1 : (0 : ℚ) ≤ cPt a b m n i := by
    unfold cPt
    have := cMin_nonneg a b m n
    positivity
  exact_mod_cast h1

/-- `wgtR i > 0`. -/
lemma wgtR_pos {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (i : Fin (D + 1)) :
    0 < wgtR a b m n i := by
  obtain ⟨hA, hB⟩ := AB_pos h.hne
  have hc := cPt_nonneg a b m n i
  unfold wgtR omegaW
  positivity

/-- `ω_i (H_R)_{i,i+1} = ω_{i+1} (H_R)_{i+1,i}`: **`eq:RacahDetailedBalance`**. -/
lemma HR_balance_succ {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (i j : Fin (D + 1))
    (hj : (j : ℕ) = (i : ℕ) + 1) :
    wgtR a b m n i * HR a b m n D i j = wgtR a b m n j * HR a b m n D j i := by
  obtain ⟨hA, hB⟩ := AB_pos h.hne
  have hc := cPt_nonneg a b m n i
  have e1 : HR a b m n D i j = -(aPlus a b m n (cPt a b m n i)) := by
    simp [HR, HRup, HRlo, HRdiag, hj, Fin.ext_iff]
    omega
  have e2 : HR a b m n D j i = -(aMinus a b m n (cPt a b m n j)) := by
    simp [HR, HRup, HRlo, HRdiag, hj, Fin.ext_iff]
    omega
  rw [e1, e2]
  unfold wgtR
  rw [cPt_cast_succ i j hj]
  have h1 := omegaW_aPlus a b m n (wA a n) (wB b m) _ hA.ne' hB.ne' hc
  have h2 := omegaW_succ_aMinus a b m n (wA a n) (wB b m) _ hA.ne' hB.ne' hc
  rw [mul_neg, mul_neg, h1, h2]

/-- `ω_i (H_R)_{ij} = ω_j (H_R)_{ji}` for all `i, j` (self-adjointness in `ℓ²(𝒞, ω)`). -/
theorem HR_selfadjoint_entries {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D)
    (i j : Fin (D + 1)) :
    wgtR a b m n i * HR a b m n D i j = wgtR a b m n j * HR a b m n D j i := by
  by_cases h1 : (j : ℕ) = (i : ℕ) + 1
  · exact HR_balance_succ h i j h1
  by_cases h2 : (i : ℕ) = (j : ℕ) + 1
  · exact (HR_balance_succ h j i h2).symm
  by_cases h3 : i = j
  · subst h3; rfl
  have h3' : (i : ℕ) ≠ (j : ℕ) := fun e => h3 (Fin.ext e)
  have n1 : ¬ (j : ℕ) = (i : ℕ) + 1 := h1
  have n2 : ¬ (j : ℕ) + 1 = (i : ℕ) := fun e => h2 e.symm
  have n3 : ¬ (i : ℕ) = (j : ℕ) := h3'
  have m1 : ¬ (i : ℕ) = (j : ℕ) + 1 := h2
  have m2 : ¬ (i : ℕ) + 1 = (j : ℕ) := fun e => h1 e.symm
  have m3 : ¬ (j : ℕ) = (i : ℕ) := fun e => h3' e.symm
  have e1 : HR a b m n D i j = 0 := by
    simp [HR, HRup, HRlo, HRdiag, Fin.ext_iff, n1, n2, n3]
  have e2 : HR a b m n D j i = 0 := by
    simp [HR, HRup, HRlo, HRdiag, Fin.ext_iff, m1, m2, m3]
  rw [e1, e2]; ring

/-- The weighted inner product on `ℓ²(𝒞, ω)`. -/
noncomputable def ipR (a b m n : ℚ) {D : ℕ} (x y : Fin (D + 1) → ℝ) : ℝ :=
  ∑ i, wgtR a b m n i * (x i * y i)

/-- **Self-adjointness of `H_R` in `ℓ²(𝒞, ω)`**: `⟨x, H y⟩_ω = ⟨H x, y⟩_ω`. -/
theorem HR_selfadjoint {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D)
    (x y : Fin (D + 1) → ℝ) :
    ipR a b m n x ((HR a b m n D).mulVec y) = ipR a b m n ((HR a b m n D).mulVec x) y := by
  unfold ipR Matrix.mulVec dotProduct
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  have := HR_selfadjoint_entries h i k
  calc wgtR a b m n i * (x i * (HR a b m n D i k * y k))
      = (wgtR a b m n i * HR a b m n D i k) * (x i * y k) := by ring
    _ = (wgtR a b m n k * HR a b m n D k i) * (x i * y k) := by rw [this]
    _ = wgtR a b m n k * (HR a b m n D k i * x i * y k) := by ring

/-- The symmetrised matrix `D^{1/2} H_R D^{-1/2}` (`D = diag ω`). -/
noncomputable def HRsym (a b m n : ℚ) (D : ℕ) : Matrix (Fin (D + 1)) (Fin (D + 1)) ℝ :=
  fun i j => Real.sqrt (wgtR a b m n i) * HR a b m n D i j * (Real.sqrt (wgtR a b m n j))⁻¹

/-- `D^{1/2} H_R D^{-1/2}` is a real symmetric matrix. -/
theorem HRsym_isSymm {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) :
    (HRsym a b m n D).IsSymm := by
  ext i j
  have hi := wgtR_pos h i
  have hj := wgtR_pos h j
  have := HR_selfadjoint_entries h i j
  have hsi := Real.sqrt_pos.2 hi
  have hsj := Real.sqrt_pos.2 hj
  have e1 := Real.mul_self_sqrt hi.le
  have e2 := Real.mul_self_sqrt hj.le
  simp only [HRsym, Matrix.transpose_apply]
  field_simp
  rw [Real.sq_sqrt hi.le, Real.sq_sqrt hj.le]
  linarith [this]

/-- `D^{1/2} H_R D^{-1/2}` is Hermitian. -/
theorem HRsym_isHermitian {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) :
    (HRsym a b m n D).IsHermitian := by
  have := HRsym_isSymm h
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact this

/-- info: 'FormalResearch.Racah.SixJ.HR_selfadjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HR_selfadjoint

/-- info: 'FormalResearch.Racah.SixJ.RacahSystem.exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RacahSystem.exists

/-- info: 'FormalResearch.Racah.SixJ.HR_selfadjoint_entries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HR_selfadjoint_entries

/-- info: 'FormalResearch.Racah.SixJ.HRsym_isSymm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HRsym_isSymm

/-- info: 'FormalResearch.Racah.SixJ.HR_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HR_mulVec

end FormalResearch.Racah.SixJ
