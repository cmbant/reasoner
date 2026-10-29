import Mathlib

/-!
# Seven-qubit stabilizer states: the witness `19/140` and a conditional reduction of `prop:stab7`

`ResearchNotes/QI/seven_qubit_entanglement/icosahedral_state.tex`, `prop:stab7`: every seven-qubit
stabilizer state has `π₃ ≥ 19/140`, hence the seven-qubit minimum `121/917` is not attained by a
stabilizer state. The paper's proof is analytic: `280 π₃ = 35 + 15A₁ + 5A₂ + A₃` and the Rains shadow
identity `4 S₁ = 7 + A₁ + A₂ - A₃`, with the weight and shadow coefficients `A_w, S_w` nonnegative
integers for a stabilizer state; GS-4 (`verify_balanced_purity_lp_graph_states.py`) checks the two
identities and an explicit seven-vertex graph state with `π₃ = 19/140`. The earlier proof by an
exhaustive evaluation of `π₃` on all `2^21` seven-vertex graph states is no longer part of the paper.

**Status: partly formalized; the proposition itself is not.** The Pauli-enumerator and shadow-integrality
argument is not formalized, nor is the Clifford-to-graph-state normal form, and the `2^21`-graph sweep is
not run in Lean (a `decide +kernel` sweep of `2^21` graphs times `35` cuts is far beyond a routine build).
What is proved here:

* the data model: a graph on seven vertices is a `21`-bit number (lexicographic edge order, as in
  the verifier); `cutRank g T` is the `GF(2)` rank of the `3 × 4` off-diagonal block for a 3-subset
  `T` (computed as `log₂` of the size of the row span), and for a graph state
  `π₃(g) = (1/35) ∑_T 2^{-cutRank}` (`pi3`), a standard formula that is *recalled, not proved* here;
* `pi3_empty`, `pi3_complete`, `pi3_witness`: exact values at the empty graph (`1`), the complete graph
  (`1/2`) and the Fano/wheel witness graph `0x00cf17` of SE-1 (`19/140`, with rank profile `3 × 2,
  32 × 3`), by `decide +kernel`; this is the sharpness half of GS-4;
* `stab7_of_enumeration`, `stab7_not_attained`: the conditional reduction. IF the statement
  `∀ g < 2^21, 19/140 ≤ π₃(g)` (the content of the former exhaustive sweep, which the analytic proof
  of the paper now replaces) holds (taken as a hypothesis, not proved in Lean), THEN no seven-vertex
  graph state attains `121/917`, and likewise for any value `v < 19/140`. The arithmetic
  `121/917 < 19/140` is `ico_lt_stab`.
-/

namespace FormalResearch.FourQubitEntropy.SevenQubitStab7

open Finset

/-- Index of the edge `{i, j}` (`i < j`) in the lexicographic order `(0,1), (0,2), …, (5,6)`. -/
def edgeIdx (i j : ℕ) : ℕ := 6 * i - i * (i - 1) / 2 + (j - i - 1)

/-- Adjacency of `i` and `j` in the graph coded by the `21`-bit number `g`. -/
def adj (g i j : ℕ) : Bool :=
  if i = j then false else if i < j then g.testBit (edgeIdx i j) else g.testBit (edgeIdx j i)

/-- Row of vertex `i` restricted to the complement of the cut `{a, b, c}`, as a bit mask. -/
def rowMask (g a b c i : ℕ) : ℕ :=
  ((List.range 7).filter (fun j => j ≠ a ∧ j ≠ b ∧ j ≠ c)).foldl
    (fun acc j => if adj g i j then acc ||| (1 <<< j) else acc) 0

/-- `GF(2)` rank of three row vectors: `log₂` of the number of distinct vectors in their span. -/
def rank3 (x y z : ℕ) : ℕ :=
  Nat.log2 ([0, x, y, z, x ^^^ y, x ^^^ z, y ^^^ z, x ^^^ y ^^^ z].dedup.length)

/-- Rank of the `3 × 4` block of the cut `{a, b, c} | rest`; this is the entanglement entropy
(in bits) of the graph state across the cut. -/
def cutRank (g a b c : ℕ) : ℕ := rank3 (rowMask g a b c a) (rowMask g a b c b) (rowMask g a b c c)

/-- The `35` three-element subsets of `{0, …, 6}`. -/
def triples : List (ℕ × ℕ × ℕ) :=
  ((List.range 7).flatMap fun a => (List.range 7).flatMap fun b => (List.range 7).filterMap fun c =>
    if a < b ∧ b < c then some (a, b, c) else none)

/-- `∑_T 8 · 2^{-cutRank} = ∑_T 2^{3 - cutRank}` (integer, since `cutRank ≤ 3`). -/
def tot (g : ℕ) : ℕ := (triples.map fun t => 2 ^ (3 - cutRank g t.1 t.2.1 t.2.2)).sum

/-- Mean balanced `3|4` purity `π₃` of the graph state `g`: `tot / (8 · 35)`. -/
def pi3 (g : ℕ) : ℚ := tot g / 280

theorem triples_length : triples.length = 35 := by decide +kernel

theorem pi3_empty : pi3 0 = 1 := by
  have : tot 0 = 280 := by decide +kernel
  unfold pi3
  rw [this]; norm_num

theorem pi3_complete : pi3 (2 ^ 21 - 1) = 1 / 2 := by
  have : tot (2 ^ 21 - 1) = 140 := by decide +kernel
  unfold pi3
  rw [this]; norm_num

/-- The SE-1 witness: Fano/wheel graph (`graph_bits = 0x00cf17`). -/
def witnessGraph : ℕ := 0x00cf17

theorem pi3_witness : pi3 witnessGraph = 19 / 140 := by
  have : tot witnessGraph = 38 := by decide +kernel
  unfold pi3
  rw [this]; norm_num

/-- Cut-rank profile of the witness: `3` cuts of rank `2` and `32` of rank `3`. -/
theorem witness_profile :
    (triples.filter fun t => cutRank witnessGraph t.1 t.2.1 t.2.2 = 2).length = 3 ∧
    (triples.filter fun t => cutRank witnessGraph t.1 t.2.1 t.2.2 = 3).length = 32 := by
  constructor <;> decide +kernel

theorem ico_lt_stab : (121 : ℚ) / 917 < 19 / 140 := by norm_num

/-- `prop:stab7` modulo the former enumeration (hypothesis `hGS4`, not proved in Lean) and the graph-state normal form:
if every seven-vertex graph state has `π₃ ≥ 19/140`, then no graph state attains any value below
`19/140`, in particular not `121/917`. -/
theorem stab7_of_enumeration (hGS4 : ∀ g < 2 ^ 21, (19 : ℚ) / 140 ≤ pi3 g) :
    ∀ g < 2 ^ 21, pi3 g ≠ 121 / 917 := by
  intro g hg h
  have := hGS4 g hg
  rw [h] at this
  exact absurd this (not_le.2 ico_lt_stab)

theorem stab7_not_attained (hGS4 : ∀ g < 2 ^ 21, (19 : ℚ) / 140 ≤ pi3 g) (v : ℚ)
    (hv : v < 19 / 140) : ∀ g < 2 ^ 21, pi3 g ≠ v := by
  intro g hg h
  have := hGS4 g hg
  rw [h] at this
  exact absurd this (not_le.2 hv)

end FormalResearch.FourQubitEntropy.SevenQubitStab7
