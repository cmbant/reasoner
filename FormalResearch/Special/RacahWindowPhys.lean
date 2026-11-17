module

public import FormalResearch.Special.RacahWindowIndex

/-!
# Racah window, part 7: the two physical integer chains

`rwn_chain_window_count`, `rwn_chain_rightcount` (`RacahWindowIndex`) specialised to the data `RwData.pos` and `RwData.neg`.

* `racah_chain_window_count`, `bix_racah_rightcount`: the untwisted chain `Ŷ_k = racah6jY` (`τ = +1`, `(α - β x)(β - α x) < 0`), with turn `q_* = racahQs α β x`; the literal threshold
  `1/2 < |cos θ_{iR}|`, no existential threshold.
* `racah_chain_window_count_neg`, `bix_racah_rightcount_neg`: the twisted chain `Y_k = (-1)^k Ŷ_k` (`τ = -1`, `(α - β x)(β - α x) > 0`), written with `rwY (fun j => (-1) ^ j)`.

**Claim class: proved** (axiom guards pinned).  Numerics: see `RacahWindowIndex`.  **Not formalised:** the half-integer lattice, `kmin = 0`, uniformity of `ε` in `(α, β, x, m, n)`,
resonant sites `|cos θ| ≤ 1/2`.
-/

@[expose] public section

open Finset Set FormalResearch.Racah FormalResearch.Racah.SixJ FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

/-- **Right count of the untwisted integer `6j` chain** (`τ = +1`): the bonds `iR, …, D' - 1` carry exactly `⌊Φ(q_{iR})/(π h) + 1/4⌋` nodes of `s ↦ racah6jY (kmin + s)`. -/
theorem bix_racah_rightcount (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : (α - β * x) * (β - α * x) < 0) (m n : ℤ) :
    ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < racahQs α β x → ∃ ε : ℝ, 0 < ε ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x → 1 ≤ max |m| |n| →
        ∀ iR : ℕ, a' ≤ rwQ (1 / 2) h (max |m| |n| + (iR : ℤ)) → rwQ (1 / 2) h (max |m| |n| + (iR : ℤ)) ≤ b' →
          1 / 2 < |Real.cos (rwTheta (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (racahQs α β x) (1 / 2) h (max |m| |n| + (iR : ℤ)))| →
          ((∑ j ∈ Ico iR D', bix_c (fun s : ℕ => racah6jY a b c m n (max |m| |n| + (s : ℤ))) j : ℕ) : ℤ) =
            ⌊bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (racahQs α β x) (rwQ (1 / 2) h (max |m| |n| + (iR : ℤ))) / (π * h) + 1 / 4⌋ := by
  intro a' b' ha hab hb
  obtain ⟨ε, hε, H⟩ := rwn_chain_rightcount (RwData.pos hα hβ hx1 hx2 hprod m n) a' b' ha hab hb
  refine ⟨ε, hε, ?_⟩
  intro a b c D' hsys i hc h hh hhε hAh hBh hx hlo iR haR hRb hcos
  have := H a b c D' hsys i hc h hh hhε hAh hBh hx hlo iR haR hRb hcos
  simpa [rwY] using this

/-- info: 'FormalResearch.Special.bix_racah_rightcount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bix_racah_rightcount

/-- **Window, bulk and tail count of the untwisted integer `6j` chain** (`τ = +1`), for a last site `i₁ ≤ D'` beyond the turn. -/
theorem racah_chain_window_count (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : (α - β * x) * (β - α * x) < 0) (m n : ℤ) :
    ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < racahQs α β x → ∃ ε : ℝ, 0 < ε ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x → 1 ≤ max |m| |n| →
        ∀ i₁ iR : ℕ, iR ≤ i₁ → i₁ ≤ D' →
          a' ≤ rwQ (1 / 2) h (max |m| |n| + (iR : ℤ)) → rwQ (1 / 2) h (max |m| |n| + (iR : ℤ)) ≤ b' →
          racahQs α β x ≤ rwQ (1 / 2) h (max |m| |n| + (i₁ : ℤ)) →
          1 / 2 < |Real.cos (rwTheta (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (racahQs α β x) (1 / 2) h (max |m| |n| + (iR : ℤ)))| →
          ((∑ j ∈ Ico iR i₁, bix_c (fun s : ℕ => racah6jY a b c m n (max |m| |n| + (s : ℤ))) j : ℕ) : ℤ) =
            ⌊bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (racahQs α β x) (rwQ (1 / 2) h (max |m| |n| + (iR : ℤ))) / (π * h) + 1 / 4⌋ := by
  intro a' b' ha hab hb
  obtain ⟨ε, hε, H⟩ := rwn_chain_window_count (RwData.pos hα hβ hx1 hx2 hprod m n) a' b' ha hab hb
  refine ⟨ε, hε, ?_⟩
  intro a b c D' hsys i hc h hh hhε hAh hBh hx hlo i₁ iR hiR hi1 haR hRb hq1 hcos
  have := H a b c D' hsys i hc h hh hhε hAh hBh hx hlo i₁ iR hiR hi1 haR hRb hq1 hcos
  simpa [rwY] using this

/-- info: 'FormalResearch.Special.racah_chain_window_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.racah_chain_window_count

/-- **Right count of the twisted integer `6j` chain** `Y_k = (-1)^k Ŷ_k` (`τ = -1`). -/
theorem bix_racah_rightcount_neg (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : 0 < (α - β * x) * (β - α * x)) (m n : ℤ) :
    ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < racahQs α β x → ∃ ε : ℝ, 0 < ε ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x → 1 ≤ max |m| |n| →
        ∀ iR : ℕ, a' ≤ rwQ (1 / 2) h (max |m| |n| + (iR : ℤ)) → rwQ (1 / 2) h (max |m| |n| + (iR : ℤ)) ≤ b' →
          1 / 2 < |Real.cos (rwTheta (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (1 / 2) h (max |m| |n| + (iR : ℤ)))| →
          ((∑ j ∈ Ico iR D', bix_c (fun s : ℕ => rwY (fun j => (-1 : ℝ) ^ j) a b c m n (max |m| |n| + (s : ℤ))) j : ℕ) : ℤ) =
            ⌊bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (rwQ (1 / 2) h (max |m| |n| + (iR : ℤ))) / (π * h) + 1 / 4⌋ :=
  rwn_chain_rightcount (RwData.neg hα hβ hx1 hx2 hprod m n)

/-- info: 'FormalResearch.Special.bix_racah_rightcount_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bix_racah_rightcount_neg

/-- **Window, bulk and tail count of the twisted integer `6j` chain** (`τ = -1`). -/
theorem racah_chain_window_count_neg (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : 0 < (α - β * x) * (β - α * x)) (m n : ℤ) :
    ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < racahQs α β x → ∃ ε : ℝ, 0 < ε ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x → 1 ≤ max |m| |n| →
        ∀ i₁ iR : ℕ, iR ≤ i₁ → i₁ ≤ D' →
          a' ≤ rwQ (1 / 2) h (max |m| |n| + (iR : ℤ)) → rwQ (1 / 2) h (max |m| |n| + (iR : ℤ)) ≤ b' →
          racahQs α β x ≤ rwQ (1 / 2) h (max |m| |n| + (i₁ : ℤ)) →
          1 / 2 < |Real.cos (rwTheta (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (1 / 2) h (max |m| |n| + (iR : ℤ)))| →
          ((∑ j ∈ Ico iR i₁, bix_c (fun s : ℕ => rwY (fun j => (-1 : ℝ) ^ j) a b c m n (max |m| |n| + (s : ℤ))) j : ℕ) : ℤ) =
            ⌊bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (rwQ (1 / 2) h (max |m| |n| + (iR : ℤ))) / (π * h) + 1 / 4⌋ :=
  rwn_chain_window_count (RwData.neg hα hβ hx1 hx2 hprod m n)

/-- info: 'FormalResearch.Special.racah_chain_window_count_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.racah_chain_window_count_neg

end FormalResearch.Special
