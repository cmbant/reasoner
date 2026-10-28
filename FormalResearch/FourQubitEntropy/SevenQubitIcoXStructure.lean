import FormalResearch.FourQubitEntropy.SevenQubitIcoSpectrum

/-!
# Structure of the icosahedral state (`eq:ico`, `thm:ico` remarks)

`ResearchNotes/QI/seven_qubit_entanglement/icosahedral_state.tex`.

* `alphaCoefficient_eq_pairs`, `betaCoefficient_eq`, `icosahedralState_eq_ico`: the coefficient tensors
  of `SevenQubitIcoState` are exactly the two sums of `eq:ico`:
  `ψ_x = |0⟩_s (α ∑_{i<j} s_{ij} |e_i+e_j⟩ + β |111111⟩) + |1⟩_s (β |000000⟩ - α ∑_{i<j} s_{ij}
  |111111 - e_i - e_j⟩)`, where `s_{ij} = -1` on the edges of the pentagon `1-3-2-4-5-1` of the six
  ordinary qubits `0..5` and `+1` otherwise.
* `pair_two_negative_triangles`, `negative_triangle_count`, `twoGraph_aut_card`: the signs form the
  regular two-graph: every pair lies in exactly two negative triangles (`10` negative triangles in all)
  and the group of permutations of the six axes preserving the negative triangles has order `60`.
* `support_alpha_card`, `support_beta_card`: `30` and `2` nonzero integer amplitudes.
* `tripleCut_spectrum_ico`: the spectra of the three-qubit marginals of `Ψico` quoted after `thm:ico`:
  `(41/262)², (15/131)⁶` on the `20` cuts avoiding `s`, `(30/131), (15/131)⁵, (13/131)²` on the `15`
  cuts containing it.
-/

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

open Finset

/-! ### The signs `s_{ij}` and the strings of `eq:ico` -/

/-- The pentagon `1-3-2-4-5-1` on the six ordinary qubits `0, …, 5`. -/
def pentEdge (i j : Fin 6) : Bool :=
  decide ((i.val = 1 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 1) ∨ (i.val = 3 ∧ j.val = 2) ∨
    (i.val = 2 ∧ j.val = 3) ∨ (i.val = 2 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 2) ∨
    (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4) ∨ (i.val = 5 ∧ j.val = 1) ∨
    (i.val = 1 ∧ j.val = 5))

/-- `s_{ij} = -1` on pentagon edges, `+1` otherwise. -/
def sgn (i j : Fin 6) : ℤ := if pentEdge i j then -1 else 1

/-- The string `|0⟩_s |e_i + e_j⟩`. -/
def pairString (i j : Fin 6) : BitString :=
  Fin.cons (α := fun _ => Bool) false (fun l => decide (l = i ∨ l = j))

/-- The string `|1⟩_s |111111 - e_i - e_j⟩`. -/
def copairString (i j : Fin 6) : BitString :=
  Fin.cons (α := fun _ => Bool) true (fun l => !decide (l = i ∨ l = j))

/-- `|0⟩_s |111111⟩`. -/
def allOnesString : BitString := Fin.cons (α := fun _ => Bool) false (fun _ => true)

/-- `|1⟩_s |000000⟩`. -/
def allZerosString : BitString := Fin.cons (α := fun _ => Bool) true (fun _ => false)

/-- `eq:ico`, `α`-part. -/
theorem alphaCoefficient_eq_pairs : ∀ z : BitString,
    alphaCoefficient z = ∑ i : Fin 6, ∑ j : Fin 6, if i < j then
      sgn i j * ((if z = pairString i j then 1 else 0) - (if z = copairString i j then 1 else 0))
      else 0 := by
  decide +kernel

/-- `eq:ico`, `β`-part. -/
theorem betaCoefficient_eq : ∀ z : BitString,
    betaCoefficient z = (if z = allOnesString then 1 else 0) + (if z = allZerosString then 1 else 0) := by
  decide +kernel

/-- The state `ψ_x` of `eq:ico`, written as in the paper. -/
theorem icosahedralState_eq_ico (alpha beta : ℝ) (z : BitString) :
    icosahedralState alpha beta z =
      alpha * (∑ i : Fin 6, ∑ j : Fin 6, if i < j then
        (sgn i j : ℝ) * ((if z = pairString i j then 1 else 0) -
          (if z = copairString i j then 1 else 0)) else 0) +
      beta * ((if z = allOnesString then 1 else 0) + (if z = allZerosString then 1 else 0)) := by
  have hA := alphaCoefficient_eq_pairs z
  have hB := betaCoefficient_eq z
  unfold icosahedralState
  have hA' : (alphaCoefficient z : ℝ) = ∑ i : Fin 6, ∑ j : Fin 6, if i < j then
        (sgn i j : ℝ) * ((if z = pairString i j then 1 else 0) -
          (if z = copairString i j then 1 else 0)) else 0 := by
    rw [hA]; push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hB' : (betaCoefficient z : ℝ) =
      (if z = allOnesString then 1 else 0) + (if z = allZerosString then 1 else 0) := by
    rw [hB]; push_cast; split_ifs <;> simp
  rw [hA', hB']

/-! ### The regular two-graph -/

/-- A triangle is negative when its three signs multiply to `-1`. -/
def negTri (i j k : Fin 6) : Bool := decide (sgn i j * sgn j k * sgn i k = -1)

/-- Every pair of axes lies in exactly two negative triangles. -/
theorem pair_two_negative_triangles : ∀ i j : Fin 6, i ≠ j →
    (univ.filter fun k : Fin 6 => k ≠ i ∧ k ≠ j ∧ negTri i j k = true).card = 2 := by
  decide +kernel

/-- There are ten negative triangles. -/
theorem negative_triangle_count :
    (univ.filter fun t : Fin 6 × Fin 6 × Fin 6 =>
      t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ negTri t.1 t.2.1 t.2.2 = true).card = 10 := by
  decide +kernel

/-- The permutations of the six axes preserving the negative triangles. -/
def twoGraphAut : Finset (Equiv.Perm (Fin 6)) :=
  univ.filter fun σ => ∀ i j k : Fin 6, negTri (σ i) (σ j) (σ k) = negTri i j k

/-- The symmetry group of the two-graph has order `60` (it is `A₅ ≅ PSL(2,5)`). -/
theorem twoGraph_aut_card : twoGraphAut.card = 60 := by
  decide +kernel

/-! ### Support -/

theorem support_alpha_card : (univ.filter fun z : BitString => alphaCoefficient z ≠ 0).card = 30 := by
  decide +kernel

theorem support_beta_card : (univ.filter fun z : BitString => betaCoefficient z ≠ 0).card = 2 := by
  decide +kernel

/-- For `α, β ≠ 0` the state `ψ_x` has exactly `32` nonzero amplitudes. -/
theorem support_card (alpha beta : ℝ) (hα : alpha ≠ 0) (hβ : beta ≠ 0) :
    (univ.filter fun z : BitString => icosahedralState alpha beta z ≠ 0).card = 32 := by
  have hdisj : ∀ z : BitString, alphaCoefficient z ≠ 0 → betaCoefficient z = 0 := by
    decide +kernel
  have : (univ.filter fun z : BitString => icosahedralState alpha beta z ≠ 0) =
      (univ.filter fun z : BitString => alphaCoefficient z ≠ 0) ∪
        (univ.filter fun z : BitString => betaCoefficient z ≠ 0) := by
    ext z
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · intro h
      by_contra hc
      push Not at hc
      apply h
      simp [icosahedralState, hc.1, hc.2]
    · rintro (h | h)
      · have := hdisj z h
        simp [icosahedralState, this, h, hα]
      · have hA : alphaCoefficient z = 0 := by
          by_contra hA; exact h (hdisj z hA)
        simp [icosahedralState, hA, h, hβ]
  rw [this, Finset.card_union_of_disjoint, support_alpha_card, support_beta_card]
  rw [Finset.disjoint_filter]
  intro z _ hz hz'
  exact hz' (hdisj z hz)

/-! ### Spectra at `Ψico` -/

/-- The spectra of the three-qubit marginals of `Ψico`, quoted after `thm:ico`: for every function `g`,
`∑ g(eigenvalue)` is `6 g(15/131) + 2 g(41/262)` on the `20` cuts avoiding the special site and
`g(30/131) + 5 g(15/131) + 2 g(13/131)` on the `15` containing it. -/
theorem tripleCut_spectrum_ico (m : Fin 7 → Bool) (hm : weight m = 3) (alpha beta : ℝ)
    (hα : alpha ^ 2 = u (37 / 524)) (hβ : beta ^ 2 = 37 / 524) (g : ℝ → ℝ) :
    ∑ i, g ((redMat_isHermitian (maskCut 3 4 m) alpha beta).eigenvalues i) =
      if m 0 = true then 5 * g (15 / 131) + g (30 / 131) + 2 * g (13 / 131)
      else 6 * g (15 / 131) + 2 * g (41 / 262) := by
  have e1 : 4 * alpha ^ 2 = 15 / 131 := by rw [hα]; unfold u; norm_num
  have e2 : 8 * alpha ^ 2 = 30 / 131 := by rw [hα]; unfold u; norm_num
  have e3 : 3 * alpha ^ 2 + beta ^ 2 = 41 / 262 := by rw [hα, hβ]; unfold u; norm_num
  have e4 : alpha ^ 2 + beta ^ 2 = 13 / 131 := by rw [hα, hβ]; unfold u; norm_num
  rw [tripleCut_spectrum m hm, e1, e2, e3, e4]

end FormalResearch.FourQubitEntropy.SevenQubitIco
