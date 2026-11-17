module

public import FormalResearch.Special.RacahWindowChain
public import FormalResearch.Special.BulkIndexHahn

/-!
# Racah window, part 4: the bulk node count of the `6j` chain (integer data, `τ = +1`)

The Racah counterpart of `bix_hahn_window`, `bix_hahn_count` (`BulkIndexHahn`) and `bwn_bulk_count` (`BulkWindowIndex`), for the centred Racah data of `RwGeo`:

* `rwn_eta`: on `[0, b']`, `b' < q_*`, there is `η ∈ (0, π/6)` with the phase step `(Φ(q) - Φ(q + h))/h ∈ (2η, π - 2η)` (`RwGeo.phase_step`: `arccos u ∈ [arccos hi, arccos lo] ⊂ (0, π/2)`);
* `rwn_bulk_count_of_form` (abstract in the chain): if `Y_k = s A(q_k) cos(Φ(q_k)/h - π/4) + O(sin η A(q_k))` at the lattice sites `q_k = (k + θ) h ∈ [a', b']` (`s = ±1`, `A = bkAmp`), then for definite sites
  `i₁ ≤ i₂` (`|cos θ| > 1/2`, `sin η < 1/2`) the nodes of `s ↦ Y_{K+s}` in the bonds `i₁, …, i₂ - 1` number `⌊Φ(q_{i₁})/(π h) + 1/4⌋ - ⌊Φ(q_{i₂})/(π h) + 1/4⌋` (`bix_count`, `BulkIndexCount`);
* **`rwn_racah_bulk`**: the same for the integer `6j` chain, with the form supplied by `racah_chain_bulk_explicit`.

**Claim class: proved** (axiom guards pinned).  **Not formalised:** `τ = -1`, the half-integer lattice (the same proof with `racah_chain_bulk_explicit_neg`, `_half`, and the `τ = -1` phase steps).
-/

@[expose] public section

open Finset Set FormalResearch.Racah FormalResearch.Racah.SixJ FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

namespace RwGeo

variable {P Q x qs : ℝ}

lemma rkS_pos (G : RwGeo P Q x qs) : 0 < rkS P Q x :=
  (bkr_geom G.hP G.hQ (by norm_num) G.hqs (by linarith [G.hx.2]) G.hα G.hβ G.hturn).2

lemma amp_pos (G : RwGeo P Q x qs) {q : ℝ} (hq0 : 0 ≤ q) (hq : q < qs) : 0 < bkAmp P Q x qs q := by
  have h1 : 0 < rkS P Q x * (qs ^ 2 - q ^ 2) := mul_pos G.rkS_pos (by nlinarith)
  unfold bkAmp
  have := Real.sqrt_pos.2 (Real.sqrt_pos.2 h1)
  positivity

/-- A uniform margin `η ∈ (0, π/6)` for the phase steps on `[0, b']`. -/
lemma eta (G : RwGeo P Q x qs) {b' : ℝ} (hb0 : 0 ≤ b') (hb : b' < qs) :
    ∃ η : ℝ, 0 < η ∧ η < π / 6 ∧ ∀ q h : ℝ, 0 ≤ q → 0 < h → q + h ≤ b' →
      2 * η < (bkPhase P Q 1 x qs q - bkPhase P Q 1 x qs (q + h)) / h ∧
      (bkPhase P Q 1 x qs q - bkPhase P Q 1 x qs (q + h)) / h + 2 * η < π := by
  obtain ⟨lo, hi, hlo, hhi, H⟩ := G.u_bounds hb0 hb
  have hδ1 : 0 < Real.arccos hi := Real.arccos_pos.2 hhi
  have hhi0 : 0 < hi := lt_of_lt_of_le hlo (le_trans (H 0 ⟨le_rfl, hb0⟩).1 (H 0 ⟨le_rfl, hb0⟩).2)
  have hδ1' : Real.arccos hi < π / 2 := Real.arccos_lt_pi_div_two.2 hhi0
  have hδ2 : Real.arccos lo < π / 2 := Real.arccos_lt_pi_div_two.2 hlo
  refine ⟨Real.arccos hi / 3, by positivity, by linarith, ?_⟩
  intro q h hq hh hqh
  have hstep := G.phase_step H hb.le hq (by linarith : q ≤ q + h) hqh
  have e : q + h - q = h := by ring
  rw [e] at hstep
  obtain ⟨s1, s2⟩ := hstep
  constructor
  · have : Real.arccos hi ≤ (bkPhase P Q 1 x qs q - bkPhase P Q 1 x qs (q + h)) / h := by
      rw [le_div_iff₀ hh]; linarith
    linarith
  · have : (bkPhase P Q 1 x qs q - bkPhase P Q 1 x qs (q + h)) / h ≤ Real.arccos lo := by
      rw [div_le_iff₀ hh]; linarith
    linarith [Real.pi_pos]

end RwGeo

/-- **Bulk node count of a chain in amplitude-phase form** (see the module docstring). -/
theorem rwn_bulk_count_of_form {P Q x qs θ h a' b' η s : ℝ} (G : RwGeo P Q x qs) (hh : 0 < h) (hθ : 0 ≤ θ)
    (hb : b' < qs) (hη0 : 0 < η) (hη1 : η < π / 6)
    (hstep : ∀ q h' : ℝ, 0 ≤ q → 0 < h' → q + h' ≤ b' →
      2 * η < (bkPhase P Q 1 x qs q - bkPhase P Q 1 x qs (q + h')) / h' ∧
      (bkPhase P Q 1 x qs q - bkPhase P Q 1 x qs (q + h')) / h' + 2 * η < π)
    (hs : s = 1 ∨ s = -1) (Yc : ℤ → ℝ) (K : ℤ) (hK : 0 ≤ K)
    (Hform : ∀ k : ℤ, a' ≤ rwQ θ h k → rwQ θ h k ≤ b' →
      |Yc k - s * bkAmp P Q x qs (rwQ θ h k) * Real.cos (bkPhase P Q 1 x qs (rwQ θ h k) / h - π / 4)| ≤
        Real.sin η * bkAmp P Q x qs (rwQ θ h k))
    (i₁ i₂ : ℕ) (hi : i₁ ≤ i₂) (hlo : a' ≤ rwQ θ h (K + (i₁ : ℤ))) (hhi : rwQ θ h (K + (i₂ : ℤ)) ≤ b')
    (hd1 : 1 / 2 < |Real.cos (rwTheta P Q x qs θ h (K + (i₁ : ℤ)))|)
    (hd2 : 1 / 2 < |Real.cos (rwTheta P Q x qs θ h (K + (i₂ : ℤ)))|) :
    ((∑ j ∈ Ico i₁ i₂, bix_c (fun s : ℕ => Yc (K + (s : ℤ))) j : ℕ) : ℤ) =
      ⌊bkPhase P Q 1 x qs (rwQ θ h (K + (i₁ : ℤ))) / (π * h) + 1 / 4⌋ -
        ⌊bkPhase P Q 1 x qs (rwQ θ h (K + (i₂ : ℤ))) / (π * h) + 1 / 4⌋ := by
  have hsin : Real.sin η < 1 / 2 := by
    rw [← Real.sin_pi_div_six]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hη1
  have hin : ∀ j : ℕ, i₁ ≤ j → j ≤ i₂ → a' ≤ rwQ θ h (K + (j : ℤ)) ∧ rwQ θ h (K + (j : ℤ)) ≤ b' := by
    intro j h1 h2
    exact ⟨hlo.trans (rwQ_mono hh (by omega)), (rwQ_mono hh (by omega)).trans hhi⟩
  have hq0 : ∀ j : ℕ, 0 ≤ rwQ θ h (K + (j : ℤ)) := by
    intro j
    unfold rwQ
    have : (0 : ℝ) ≤ ((K + (j : ℤ) : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ K + (j : ℤ))
    positivity
  have W : BixWin (fun s : ℕ => Yc (K + (s : ℤ))) (fun j : ℕ => rwTheta P Q x qs θ h (K + (j : ℤ)))
      (fun j : ℕ => bkAmp P Q x qs (rwQ θ h (K + (j : ℤ)))) s η i₁ i₂ := by
    refine ⟨hs, hη0, by linarith [Real.pi_pos], ?_, ?_, ?_⟩
    · intro j h1 h2
      obtain ⟨l, u⟩ := hin j h1 h2
      exact G.amp_pos (hq0 j) (lt_of_le_of_lt u hb)
    · intro j h1 h2
      obtain ⟨l, u⟩ := hin j h1 h2
      exact Hform _ l u
    · intro j h1 h2
      obtain ⟨l, u⟩ := hin j h1 (by omega)
      obtain ⟨l', u'⟩ := hin (j + 1) (by omega) h2
      have e : K + ((j + 1 : ℕ) : ℤ) = K + (j : ℤ) + 1 := by push_cast; ring
      have hq1 : rwQ θ h (K + ((j + 1 : ℕ) : ℤ)) = rwQ θ h (K + (j : ℤ)) + h := by
        rw [e, rwQ_succ]
      rw [hq1] at u'
      have hst := hstep (rwQ θ h (K + (j : ℤ))) h (hq0 j) hh u'
      have hdiff : rwTheta P Q x qs θ h (K + (j : ℤ)) - rwTheta P Q x qs θ h (K + ((j + 1 : ℕ) : ℤ)) =
          (bkPhase P Q 1 x qs (rwQ θ h (K + (j : ℤ))) - bkPhase P Q 1 x qs (rwQ θ h (K + (j : ℤ)) + h)) / h := by
        unfold rwTheta; rw [hq1]; ring
      rw [hdiff]
      exact hst
  have key := bix_count W (i₂ - i₁) i₁ le_rfl (by omega) (bix_def_iff.2 (hsin.trans hd1))
    (by rw [Nat.add_sub_cancel' hi]; exact bix_def_iff.2 (hsin.trans hd2))
  rw [Nat.add_sub_cancel' hi] at key
  rw [key]
  unfold rwTheta
  rw [bixN_theta _ _ hh, bixN_theta _ _ hh]

/-- info: 'FormalResearch.Special.rwn_bulk_count_of_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rwn_bulk_count_of_form

/-- **Bulk node count of the physical integer `6j` chain** (`τ = +1`): for `[a', b'] ⊂ (0, q_*)` there is `ε > 0` such that for every finite Racah system with `A h = α`, `B h = β`,
`cos = x`, `h ≤ ε`, and every pair of definite bulk sites `i₁ ≤ i₂` (`q ∈ [a', b']`, `|cos θ| > 1/2`), the nodes of `s ↦ Ŷ_{K+s}` in the bonds `i₁, …, i₂ - 1` number
`⌊Φ(q_{i₁})/(π h) + 1/4⌋ - ⌊Φ(q_{i₂})/(π h) + 1/4⌋`. -/
theorem rwn_racah_bulk (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : (α - β * x) * (β - α * x) < 0) (m n : ℤ) :
    ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < racahQs α β x → ∃ ε : ℝ, 0 < ε ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
        ∀ i₁ i₂ : ℕ, i₁ ≤ i₂ → a' ≤ rwQ (1 / 2) h (max |m| |n| + (i₁ : ℤ)) → rwQ (1 / 2) h (max |m| |n| + (i₂ : ℤ)) ≤ b' →
          1 / 2 < |Real.cos (rwTheta (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x (racahQs α β x) (1 / 2) h (max |m| |n| + (i₁ : ℤ)))| →
          1 / 2 < |Real.cos (rwTheta (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x (racahQs α β x) (1 / 2) h (max |m| |n| + (i₂ : ℤ)))| →
          ((∑ j ∈ Ico i₁ i₂, bix_c (fun s : ℕ => racah6jY a b c m n (max |m| |n| + (s : ℤ))) j : ℕ) : ℤ) =
            ⌊bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (racahQs α β x) (rwQ (1 / 2) h (max |m| |n| + (i₁ : ℤ))) / (π * h) + 1 / 4⌋ -
            ⌊bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (racahQs α β x) (rwQ (1 / 2) h (max |m| |n| + (i₂ : ℤ))) / (π * h) + 1 / 4⌋ := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_pos hα hβ hx1 hx2 hprod
  have G : RwGeo (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x (racahQs α β x) :=
    ⟨by positivity, by positivity, hqs, hαq, hβq, hturn, ⟨hx1, hx2⟩⟩
  intro a' b' ha hab hb
  obtain ⟨η, hη0, hη1, hstep⟩ := G.eta (by linarith) hb
  have ht : 0 < Real.sin η := Real.sin_pos_of_pos_of_lt_pi hη0 (by linarith [Real.pi_pos])
  obtain ⟨ε, hε, H⟩ := racah_chain_bulk_explicit α β x hα hβ hx1 hx2 hprod m n a' b' ha hab hb (Real.sin η) ht
  refine ⟨ε, hε, ?_⟩
  intro a b c D' hsys i hc h hh hεh hAh hBh hx i₁ i₂ hi hlo hhi hd1 hd2
  obtain ⟨s, hs, Hs⟩ := H a b c D' hsys i hc h hh hεh hAh hBh hx
  have hK : 0 ≤ max |m| |n| := le_trans (abs_nonneg m) (le_max_left _ _)
  exact rwn_bulk_count_of_form (θ := 1 / 2) (a' := a') (b' := b') G hh (by norm_num) hb hη0 hη1 hstep hs
    (racah6jY a b c m n) (max |m| |n|) hK (fun k hl hu => Hs k hl hu) i₁ i₂ hi hlo hhi hd1 hd2

/-- info: 'FormalResearch.Special.rwn_racah_bulk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rwn_racah_bulk

end FormalResearch.Special
