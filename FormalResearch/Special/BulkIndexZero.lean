module

public import FormalResearch.Special.BulkIndexHahn

/-!
# Bulk index, part 4: the Bohr-Sommerfeld integer equals the number of nodes to the right, and the index from the left

Conditional composition for the actual `3j` chain (integer lattice, `τ = +1`, `0 < x < 1`), `N = kmin + m + 1`,
`kmin = max |M| |σ| ≥ 1`, node `x = x_n`, `n ≤ m`, `u_i = Ŷ_{kmin+i}` (`bixU`), `q_i = (kmin + i + 1/2)/N`.

**Right-end count** (`BixRightCount`, an explicit hypothesis, NOT proved): at some bulk site `i_R` with `|cos θ| > t₀`, the
number of nodes in the bonds `i_R, …, m-1` is `⌊Φ(q_{i_R})/(π h) + 1/4⌋`.  This is the node count of the region `[b, N)`
(Airy window around `q_*`, none beyond `q_*`); see the module docstring of `BulkIndexRight` for what is missing.

* **`bix_hahn_zero_index`**: under `BixRightCount`, for every bulk site `i ≤ i_R` with `|cos θ_i| > t₀`:
  the nodes at or to the right of `i` number `⌊Φ(q_i)/(π h) + 1/4⌋`, and (with `cho_hahn_nodes`, total `m - n`) the nodes strictly
  to the left of `i` number `(m - n) - ⌊Φ(q_i)/(π h) + 1/4⌋`.
* **`bix_bs_lattice`**: if the bond `(i, i+1)` carries a node and both sites are definite, with `R = ⌊Φ(q_i)/(π h) + 1/4⌋`
  then `Φ(q_{i+1})/h < π (R - 1/4) ≤ Φ(q_i)/h`: the Bohr-Sommerfeld point of the bond is the `R`-th, `R` = the number of nodes at or to the
  right of the bond (no offset: the integer `m` of `hahn_chain_bulk_zeros` is `R`, `bix_bs_unique`).

**Claim class: proved under the explicit hypothesis `BixRightCount`** (`proved` for the pure lemmas).  **Not formalised:** the discharge of
`BixRightCount`, `τ = -1`, half-integer lattice, Racah chains.
-/

@[expose] public section

open Finset Real FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

/-- **The right-end count (hypothesis).**  The bonds `i_R, …, m-1` of the `3j` chain carry `⌊Φ(q_{i_R})/(π h) + 1/4⌋` nodes. -/
def BixRightCount (M σ N : ℤ) (x : ℚ) (iR m : ℕ) : Prop :=
  ((∑ j ∈ Ico iR m, bix_c (bixU M σ N x) j : ℕ) : ℤ) =
    ⌊bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (bixQ N (max |M| |σ| + (iR : ℤ))) / (π * (1 / (N : ℝ))) + 1 / 4⌋

/-- A node bond between two definite sites: the `R`-th Bohr-Sommerfeld point lies in the bond. -/
theorem bix_bs_lattice {L L' : ℝ} {R : ℤ} (hR : ⌊L / π + 1 / 4⌋ = R)
    (hR' : ⌊L' / π + 1 / 4⌋ = R - 1) : L' < π * ((R : ℝ) - 1 / 4) ∧ π * ((R : ℝ) - 1 / 4) ≤ L := by
  have hπ := Real.pi_pos
  have h1 := Int.floor_le (L / π + 1 / 4)
  have h2 := Int.lt_floor_add_one (L' / π + 1 / 4)
  rw [hR] at h1
  rw [hR'] at h2
  push_cast at h2
  constructor
  · have : L' / π < (R : ℝ) - 1 / 4 := by linarith
    rwa [div_lt_iff₀ hπ, mul_comm] at this
  · have : (R : ℝ) - 1 / 4 ≤ L / π := by linarith
    rwa [le_div_iff₀ hπ, mul_comm] at this

/-- Uniqueness: any integer in the `c`-widened bond window is `R`, as soon as the bond is shorter than `π - 2c`. -/
theorem bix_bs_unique {L L' c : ℝ} {R m' : ℤ} (hc : 0 ≤ c) (hlen : L - L' + 2 * c < π)
    (h1 : L' < π * ((R : ℝ) - 1 / 4)) (h2 : π * ((R : ℝ) - 1 / 4) ≤ L)
    (hm1 : L' - c ≤ π * ((m' : ℝ) - 1 / 4)) (hm2 : π * ((m' : ℝ) - 1 / 4) ≤ L + c) : m' = R := by
  have hπ := Real.pi_pos
  have a1 : π * ((m' : ℝ) - R) < π := by nlinarith
  have a2 : -π < π * ((m' : ℝ) - R) := by nlinarith
  have b1 : (m' : ℝ) - R < 1 := by
    by_contra h; push Not at h; nlinarith
  have b2 : -1 < (m' : ℝ) - R := by
    by_contra h; push Not at h; nlinarith
  have c1 : m' - R < 1 := by exact_mod_cast b1
  have c2 : -1 < m' - R := by exact_mod_cast b2
  omega

theorem bix_site_le_m {N k : ℤ} {b : ℝ} {x : ℝ} (hb : b < √(1 - x ^ 2)) (hN : 0 < N) (h : bixQ N k ≤ b) : k < N := by
  have hq : √(1 - x ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]; nlinarith [sq_nonneg x]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold bixQ at h
  have : ((k : ℝ) + 1 / 2) * (1 / (N : ℝ)) < 1 := by linarith
  rw [← div_eq_mul_one_div, div_lt_one hN'] at this
  have : (k : ℝ) < N := by linarith
  exact_mod_cast this

/-- **The zero index of the `3j` chain in the bulk, conditional on the right-end count.** -/
theorem bix_hahn_zero_index (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hb : b < √(1 - (x : ℝ) ^ 2)) :
    ∃ t₀ ε : ℝ, 0 < t₀ ∧ 0 < ε ∧
      ∀ (m n : ℕ), 1 ≤ max |M| |σ| → n ≤ m → xLat (M : ℚ) (σ : ℚ) ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℚ) n = x →
        1 / ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℝ) ≤ ε → ∀ i iR : ℕ, i ≤ iR →
          a ≤ bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (i : ℤ)) →
          bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (iR : ℤ)) ≤ b →
          t₀ < |Real.cos (bixTheta (x : ℝ) (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (i : ℤ)))| →
          t₀ < |Real.cos (bixTheta (x : ℝ) (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (iR : ℤ)))| →
          BixRightCount M σ (max |M| |σ| + (m : ℤ) + 1) x iR m →
          ((∑ j ∈ Ico i m, bix_c (bixU M σ (max |M| |σ| + (m : ℤ) + 1) x) j : ℕ) : ℤ) =
              ⌊bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (i : ℤ))) /
                (π * (1 / ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℝ))) + 1 / 4⌋ ∧
            ((∑ j ∈ range i, bix_c (bixU M σ (max |M| |σ| + (m : ℤ) + 1) x) j : ℕ) : ℤ) =
              ((m : ℤ) - n) -
              ⌊bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (i : ℤ))) /
                (π * (1 / ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℝ))) + 1 / 4⌋ := by
  obtain ⟨η, ε, hη0, hη1, hε, H⟩ := bix_hahn_window M σ x hx0 hx1 a b ha hab hb
  refine ⟨Real.sin η, ε, Real.sin_pos_of_pos_of_lt_pi hη0 (by linarith [Real.pi_pos]), hε, ?_⟩
  intro m n hlo hnm hxn hNε i iR hi hlo' hhi hd1 hd2 hR
  set N : ℤ := max |M| |σ| + (m : ℤ) + 1 with hNdef
  have hkpos : 0 ≤ max |M| |σ| := le_trans (abs_nonneg M) (le_max_left _ _)
  have hNmax : max |M| |σ| < N := by omega
  have hnlt : (n : ℤ) < N - max |M| |σ| := by omega
  have hNpos : 0 < N := by omega
  obtain ⟨s, A, W⟩ := H N n ⟨hNmax, hnlt, hxn⟩ hNε i iR hi hlo' hhi
  have hiRm : iR ≤ m := by
    have := bix_site_le_m hb hNpos hhi
    omega
  have hT : cho_nodal (bixU M σ N x) m = m - n := by
    have := cho_hahn_nodes (M := M) (σ := σ) (N := N) hlo (m := m) hNdef (n := n) hnm
    rw [hxn] at this
    exact this
  have hRc : ((∑ j ∈ Ico iR m, bix_c (bixU M σ N x) j : ℕ) : ℤ) = bixN (bixTheta (x : ℝ) N (max |M| |σ| + (iR : ℤ))) := by
    unfold BixRightCount at hR
    rw [hR]
    have hh : (0 : ℝ) < 1 / (N : ℝ) := by
      have : (0 : ℝ) < N := by exact_mod_cast hNpos
      positivity
    unfold bixTheta
    rw [bixN_theta _ _ hh]
  have hDi : BixDef (fun i : ℕ => bixTheta (x : ℝ) N (max |M| |σ| + (i : ℤ))) η i := bix_def_iff.2 hd1
  have hDR : BixDef (fun i : ℕ => bixTheta (x : ℝ) N (max |M| |σ| + (i : ℤ))) η iR := bix_def_iff.2 hd2
  have hh : (0 : ℝ) < 1 / (N : ℝ) := by
    have : (0 : ℝ) < N := by exact_mod_cast hNpos
    positivity
  have e1 := bix_count_right W (k := i) (kR := iR) (m := m) le_rfl hi le_rfl hiRm hDi hDR hRc
  have e2 := bix_count_left W (k := i) (kR := iR) (m := m) (T := m - n) le_rfl hi le_rfl hiRm hDi hDR hRc hT
  have hnn : ((m - n : ℕ) : ℤ) = (m : ℤ) - n := by omega
  refine ⟨?_, ?_⟩
  · rw [e1]; unfold bixTheta; rw [bixN_theta _ _ hh]
  · rw [e2, hnn]; unfold bixTheta; rw [bixN_theta _ _ hh]

/-- info: 'FormalResearch.Special.bix_hahn_zero_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bix_hahn_zero_index

/-- info: 'FormalResearch.Special.bix_bs_lattice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bix_bs_lattice

/-- info: 'FormalResearch.Special.bix_bs_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bix_bs_unique

/-- **`hahn_chain_bulk_zero_index`, conditional on the right-end count.**  For a node bond `(i, i+1)` of the bulk (`u_i u_{i+1} < 0`,
both sites definite) the number `R` of nodes in the bonds `i, …, m-1` satisfies
`Φ(q_{i+1})/h < π (R - 1/4) ≤ Φ(q_i)/h` (the Bohr-Sommerfeld integer of `hahn_chain_bulk_zeros` is `R`, no offset) and the nodes strictly to
the left of the bond number `(m - n) - R`, so the bond carries the node of index `(m - n) - R + 1` from the left. -/
theorem bix_hahn_bs_index (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hb : b < √(1 - (x : ℝ) ^ 2)) :
    ∃ t₀ ε : ℝ, 0 < t₀ ∧ 0 < ε ∧
      ∀ (m n : ℕ), 1 ≤ max |M| |σ| → n ≤ m → xLat (M : ℚ) (σ : ℚ) ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℚ) n = x →
        1 / ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℝ) ≤ ε → ∀ i iR : ℕ, i + 1 ≤ iR →
          a ≤ bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (i : ℤ)) →
          bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (iR : ℤ)) ≤ b →
          t₀ < |Real.cos (bixTheta (x : ℝ) (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (i : ℤ)))| →
          t₀ < |Real.cos (bixTheta (x : ℝ) (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + ((i + 1 : ℕ) : ℤ)))| →
          t₀ < |Real.cos (bixTheta (x : ℝ) (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (iR : ℤ)))| →
          BixRightCount M σ (max |M| |σ| + (m : ℤ) + 1) x iR m →
          bixU M σ (max |M| |σ| + (m : ℤ) + 1) x i * bixU M σ (max |M| |σ| + (m : ℤ) + 1) x (i + 1) < 0 →
          ∃ R : ℕ, (∑ j ∈ Ico i m, bix_c (bixU M σ (max |M| |σ| + (m : ℤ) + 1) x) j) = R ∧
            ((∑ j ∈ range i, bix_c (bixU M σ (max |M| |σ| + (m : ℤ) + 1) x) j : ℕ) : ℤ) = ((m : ℤ) - n) - R ∧
            bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + ((i + 1 : ℕ) : ℤ))) /
                (1 / ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℝ)) < π * ((R : ℝ) - 1 / 4) ∧
            π * ((R : ℝ) - 1 / 4) ≤ bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (i : ℤ))) /
                (1 / ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℝ)) := by
  obtain ⟨t₀, ε, ht, hε, H⟩ := bix_hahn_zero_index M σ x hx0 hx1 a b ha hab hb
  refine ⟨t₀, ε, ht, hε, ?_⟩
  intro m n hlo hnm hxn hNε i iR hiR hlo' hhi hd1 hd2 hd3 hR hnode
  set N : ℤ := max |M| |σ| + (m : ℤ) + 1 with hNdef
  have hkpos : 0 ≤ max |M| |σ| := le_trans (abs_nonneg M) (le_max_left _ _)
  have hNpos : 0 < N := by omega
  have hiRm : iR ≤ m := by
    have := bix_site_le_m hb hNpos hhi
    omega
  have hlo2 : a ≤ bixQ N (max |M| |σ| + ((i + 1 : ℕ) : ℤ)) :=
    hlo'.trans (bixQ_mono hNpos (by push_cast; omega))
  obtain ⟨A1, A2⟩ := H m n hlo hnm hxn hNε i iR (by omega) hlo' hhi hd1 hd3 hR
  obtain ⟨B1, B2⟩ := H m n hlo hnm hxn hNε (i + 1) iR hiR hlo2 hhi hd2 hd3 hR
  have hne : bixU M σ N x i ≠ 0 := by
    intro h; rw [h] at hnode; simp at hnode
  have hc : bix_c (bixU M σ N x) i = 1 := by
    unfold bix_c; simp [hne, hnode]
  have hsplit : ∑ j ∈ Ico i m, bix_c (bixU M σ N x) j = bix_c (bixU M σ N x) i + ∑ j ∈ Ico (i + 1) m, bix_c (bixU M σ N x) j :=
    Finset.sum_eq_sum_Ico_succ_bot (by omega) _
  have hh : (0 : ℝ) < 1 / (N : ℝ) := by
    have : (0 : ℝ) < N := by exact_mod_cast hNpos
    positivity
  refine ⟨∑ j ∈ Ico i m, bix_c (bixU M σ N x) j, rfl, ?_, ?_⟩
  · rw [A2, A1]
  · have := bix_bs_lattice (L := bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (bixQ N (max |M| |σ| + (i : ℤ))) / (1 / (N : ℝ)))
      (L' := bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (bixQ N (max |M| |σ| + ((i + 1 : ℕ) : ℤ))) / (1 / (N : ℝ)))
      (R := ((∑ j ∈ Ico i m, bix_c (bixU M σ N x) j : ℕ) : ℤ)) (by
        rw [A1]; congr 1; rw [hNdef]; field_simp) (by
        have : ((∑ j ∈ Ico (i + 1) m, bix_c (bixU M σ N x) j : ℕ) : ℤ) = ((∑ j ∈ Ico i m, bix_c (bixU M σ N x) j : ℕ) : ℤ) - 1 := by
          rw [hsplit, hc]; push_cast; ring
        rw [← this, B1]; congr 1; rw [hNdef]; field_simp)
    simpa using this

/-- info: 'FormalResearch.Special.bix_hahn_bs_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bix_hahn_bs_index

end FormalResearch.Special
