module

public import FormalResearch.Special.RacahWindowPhys
public import FormalResearch.Special.RacahWindowZero
public import FormalResearch.Special.RacahWindowNodesNeg
public import FormalResearch.Special.BulkIndexZero

/-!
# Racah window, part 10: the zero index of the twisted integer `6j` chain (`τ = -1`)

The mirror of `RacahWindowZero`: composition of the right count `bix_racah_rightcount_neg` (`RacahWindowPhys`) with the total node count `rw_chain_nodes_neg` (`RacahWindowNodesNeg`: the twisted chain
`Y_k = (-1)^k Ŷ_k` at `c = c_min + l` has `D' - l` nodes).

* **`racah_chain_zero_index_neg`**: at a definite bulk site `i₀` (`q ∈ [a', b']`, `|cos θ| > 1/2`) the nodes in the bonds `i₀, …, D' - 1` number `⌊Φ(q_{i₀})/(π h) + 1/4⌋`, and the
  nodes strictly to the left (bonds `0, …, i₀ - 1`) number `(D' - l) - ⌊Φ(q_{i₀})/(π h) + 1/4⌋`, `l = c - c_min`.
* **`racah_chain_bs_index_neg`**: for a node bond `(i₀, i₀+1)` of the bulk (`Y Y' < 0`, both sites definite) the number `R` of nodes at or to the right of the bond satisfies
  `Φ(q_{i₀+1})/h < π (R - 1/4) ≤ Φ(q_{i₀})/h`, and the bond carries the node of index `(D' - l) - R + 1` from the left.

**Claim class: proved** (axiom guards pinned; `1 ≤ kmin`, integer data, `τ = -1`).  **Not formalised:** half-integer lattice, `kmin = 0`; resonant sites `|cos θ| ≤ 1/2`.
-/

@[expose] public section

open Finset FormalResearch.Racah FormalResearch.Racah.SixJ FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

/-- **The zero index of the twisted integer `6j` chain** (`τ = -1`): see the module docstring. -/
theorem racah_chain_zero_index_neg (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : 0 < (α - β * x) * (β - α * x)) (m n : ℤ) :
    ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < racahQs α β x → ∃ ε : ℝ, 0 < ε ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x → 1 ≤ max |m| |n| →
        ∀ i₀ : ℕ, a' ≤ rwQ (1 / 2) h (max |m| |n| + (i₀ : ℤ)) → rwQ (1 / 2) h (max |m| |n| + (i₀ : ℤ)) ≤ b' →
          1 / 2 < |Real.cos (rwTheta (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (1 / 2) h (max |m| |n| + (i₀ : ℤ)))| →
          i₀ < D' ∧ ((∑ j ∈ Ico i₀ D', bix_c (fun s : ℕ => rwY (fun j => (-1 : ℝ) ^ j) a b c m n (max |m| |n| + (s : ℤ))) j : ℕ) : ℤ) =
              ⌊bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (rwQ (1 / 2) h (max |m| |n| + (i₀ : ℤ))) / (π * h) + 1 / 4⌋ ∧
            ((∑ j ∈ range i₀, bix_c (fun s : ℕ => rwY (fun j => (-1 : ℝ) ^ j) a b c m n (max |m| |n| + (s : ℤ))) j : ℕ) : ℤ) =
              ((D' : ℤ) - ((i : ℕ) : ℤ)) -
              ⌊bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (rwQ (1 / 2) h (max |m| |n| + (i₀ : ℤ))) / (π * h) + 1 / 4⌋ := by
  intro a' b' ha hab hb
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_neg hα hβ hx1 hx2 hprod
  obtain ⟨ε1, hε1, H⟩ := bix_racah_rightcount_neg α β x hα hβ hx1 hx2 hprod m n a' b' ha hab hb
  set qs : ℝ := racahQs α β x with hqsdef
  have hqa : qs < 2 * α := by
    have : qs ^ 2 < 4 * α ^ 2 := by
      have h1 : 1 / (4 * α ^ 2) * qs ^ 2 < 1 := by linarith
      rw [one_div_mul_eq_div, div_lt_one (by positivity)] at h1; exact h1
    nlinarith [sq_nonneg (qs - 2 * α), sq_nonneg (qs + 2 * α)]
  have hqb : qs < 2 * β := by
    have : qs ^ 2 < 4 * β ^ 2 := by
      have h1 : 1 / (4 * β ^ 2) * qs ^ 2 < 1 := by linarith
      rw [one_div_mul_eq_div, div_lt_one (by positivity)] at h1; exact h1
    nlinarith [sq_nonneg (qs - 2 * β), sq_nonneg (qs + 2 * β)]
  have hδq : 0 < min (2 * α) (2 * β) - qs := by
    have := lt_min hqa hqb; linarith
  refine ⟨min ε1 (2 * (min (2 * α) (2 * β) - qs)), lt_min hε1 (by linarith), ?_⟩
  intro a b c D' hsys i hc h hh hhε hAh hBh hx hlo i₀ haR hRb hcos
  have hK : 0 ≤ max |m| |n| := le_trans (abs_nonneg m) (le_max_left _ _)
  have hD := rw_D_eq a b m n hsys
  have hiRD : i₀ < D' := by
    by_contra hcon
    push Not at hcon
    have h1 : rwQ (1 / 2) h (max |m| |n| + (D' : ℤ)) ≤ rwQ (1 / 2) h (max |m| |n| + (i₀ : ℤ)) :=
      rwQ_mono hh (by omega)
    have h2 := rw_top_site hα hβ a b m n hsys hAh hBh hh hqa hqb (hhε.trans (min_le_right _ _))
    have h3 : rwQ (1 / 2) h (max |m| |n| + (i₀ : ℤ)) ≥ qs := le_trans h2 h1
    have h4 : rwQ (1 / 2) h (max |m| |n| + (i₀ : ℤ)) < qs := lt_of_le_of_lt hRb hb
    linarith
  have hR := H a b c D' hsys i hc h hh (hhε.trans (min_le_left _ _)) hAh hBh hx hlo i₀ haR hRb hcos
  refine ⟨hiRD, hR, ?_⟩
  have hT := rw_chain_nodes_neg (c := c) hsys i hc hh hlo
  rw [bix_nodal_eq_sum] at hT
  have hs := sum_range_add_sum_Ico (bix_c (fun s : ℕ => rwY (fun j => (-1 : ℝ) ^ j) a b c m n (max |m| |n| + (s : ℤ)))) hiRD.le
  rw [hT] at hs
  have : ((∑ j ∈ range i₀, bix_c (fun s : ℕ => rwY (fun j => (-1 : ℝ) ^ j) a b c m n (max |m| |n| + (s : ℤ))) j : ℕ) : ℤ) +
      ((∑ j ∈ Ico i₀ D', bix_c (fun s : ℕ => rwY (fun j => (-1 : ℝ) ^ j) a b c m n (max |m| |n| + (s : ℤ))) j : ℕ) : ℤ) = (D' : ℤ) - ((i : ℕ) : ℤ) := by
    have hiD : (i : ℕ) ≤ D' := by have := i.2; omega
    have h3 := congrArg (Nat.cast : ℕ → ℤ) hs
    rw [Nat.cast_sub hiD] at h3
    push_cast at h3 ⊢
    linarith
  linarith

/-- info: 'FormalResearch.Special.racah_chain_zero_index_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.racah_chain_zero_index_neg

/-- **The Bohr-Sommerfeld integer of a node bond and the index from the left, twisted integer `6j` chain** (`τ = -1`): see the module docstring. -/
theorem racah_chain_bs_index_neg (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : 0 < (α - β * x) * (β - α * x)) (m n : ℤ) :
    ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < racahQs α β x → ∃ ε : ℝ, 0 < ε ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x → 1 ≤ max |m| |n| →
        ∀ i₀ : ℕ, a' ≤ rwQ (1 / 2) h (max |m| |n| + (i₀ : ℤ)) → rwQ (1 / 2) h (max |m| |n| + ((i₀ + 1 : ℕ) : ℤ)) ≤ b' →
          1 / 2 < |Real.cos (rwTheta (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (1 / 2) h (max |m| |n| + (i₀ : ℤ)))| →
          1 / 2 < |Real.cos (rwTheta (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (1 / 2) h (max |m| |n| + ((i₀ + 1 : ℕ) : ℤ)))| →
          rwY (fun j => (-1 : ℝ) ^ j) a b c m n (max |m| |n| + (i₀ : ℤ)) * rwY (fun j => (-1 : ℝ) ^ j) a b c m n (max |m| |n| + ((i₀ + 1 : ℕ) : ℤ)) < 0 →
          ∃ R : ℕ, (∑ j ∈ Ico i₀ D', bix_c (fun s : ℕ => rwY (fun j => (-1 : ℝ) ^ j) a b c m n (max |m| |n| + (s : ℤ))) j) = R ∧
            ((∑ j ∈ range i₀, bix_c (fun s : ℕ => rwY (fun j => (-1 : ℝ) ^ j) a b c m n (max |m| |n| + (s : ℤ))) j : ℕ) : ℤ) = ((D' : ℤ) - ((i : ℕ) : ℤ)) - R ∧
            bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (rwQ (1 / 2) h (max |m| |n| + ((i₀ + 1 : ℕ) : ℤ))) / h <
              π * ((R : ℝ) - 1 / 4) ∧
            π * ((R : ℝ) - 1 / 4) ≤
              bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (rwQ (1 / 2) h (max |m| |n| + (i₀ : ℤ))) / h := by
  intro a' b' ha hab hb
  obtain ⟨ε, hε, H⟩ := racah_chain_zero_index_neg α β x hα hβ hx1 hx2 hprod m n a' b' ha hab hb
  refine ⟨ε, hε, ?_⟩
  intro a b c D' hsys i hc h hh hhε hAh hBh hx hlo i₀ haR hRb hd1 hd2 hnode
  set K : ℤ := max |m| |n| with hKdef
  have hK : 0 ≤ K := le_trans (abs_nonneg m) (le_max_left _ _)
  have hD := rw_D_eq a b m n hsys
  have hle : rwQ (1 / 2) h (K + (i₀ : ℤ)) ≤ rwQ (1 / 2) h (K + ((i₀ + 1 : ℕ) : ℤ)) := rwQ_mono hh (by push_cast; omega)
  obtain ⟨hi0, A1, A2⟩ := H a b c D' hsys i hc h hh hhε hAh hBh hx hlo i₀ haR (hle.trans hRb) hd1
  have hlo2 : a' ≤ rwQ (1 / 2) h (K + ((i₀ + 1 : ℕ) : ℤ)) := haR.trans hle
  obtain ⟨hi1, B1, B2⟩ := H a b c D' hsys i hc h hh hhε hAh hBh hx hlo (i₀ + 1) hlo2 hRb hd2
  set u : ℕ → ℝ := fun s : ℕ => rwY (fun j => (-1 : ℝ) ^ j) a b c m n (K + (s : ℤ)) with hu
  have hne : u i₀ ≠ 0 := by
    intro h0
    have : u i₀ * u (i₀ + 1) = 0 := by rw [h0, zero_mul]
    have h3 : rwY (fun j => (-1 : ℝ) ^ j) a b c m n (K + (i₀ : ℤ)) * rwY (fun j => (-1 : ℝ) ^ j) a b c m n (K + ((i₀ + 1 : ℕ) : ℤ)) = 0 := this
    linarith
  have hc1 : bix_c u i₀ = 1 := by
    unfold bix_c
    have : u i₀ * u (i₀ + 1) < 0 := hnode
    simp [hne, this]
  have hsplit : ∑ j ∈ Ico i₀ D', bix_c u j = bix_c u i₀ + ∑ j ∈ Ico (i₀ + 1) D', bix_c u j :=
    Finset.sum_eq_sum_Ico_succ_bot hi0 _
  have hcnt : ((∑ j ∈ Ico (i₀ + 1) D', bix_c u j : ℕ) : ℤ) = ((∑ j ∈ Ico i₀ D', bix_c u j : ℕ) : ℤ) - 1 := by
    rw [hsplit, hc1]; push_cast; ring
  refine ⟨∑ j ∈ Ico i₀ D', bix_c u j, rfl, ?_, ?_⟩
  · rw [A2, A1]
  · have := bix_bs_lattice (L := bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (rwQ (1 / 2) h (K + (i₀ : ℤ))) / h)
      (L' := bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (rwQ (1 / 2) h (K + ((i₀ + 1 : ℕ) : ℤ))) / h)
      (R := ((∑ j ∈ Ico i₀ D', bix_c u j : ℕ) : ℤ)) (by
        rw [A1, rw_floor_eq]) (by
        rw [← hcnt, B1, rw_floor_eq])
    simpa using this

/-- info: 'FormalResearch.Special.racah_chain_bs_index_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.racah_chain_bs_index_neg

end FormalResearch.Special
