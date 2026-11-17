module

public import FormalResearch.Special.BulkWindowHahn
public import FormalResearch.Special.BulkIndexRight
public import FormalResearch.Special.BulkIndexZero

/-!
# Bulk window, part 7: the node count of the Airy window, unconditionally, and the zero index of the `3j` chain

Junction of the Airy-window count (`bwn_hahn_window`, `BulkWindowHahn`) with the bulk count (`bix_hahn_count` of `BulkIndexHahn`, here `bwn_bulk_count` with the margin
`sin η < 1/2` made explicit) and the tail (`bix_hahn_tail`, no nodes beyond `q_*`):

* `bwn_theta_step`, `bwn_exists_good`: the phase `θ_j = Φ(q_j)/h - π/4` decreases by a step in `[δ₁, δ₂]`, `δ₂ = arccos x < π/2`, on `[0, b]`, `b < q_*`, hence in
  `[q_* - ρ, q_* - ρ/2]` there is a site with `|cos θ| > 1/2` (it comes within `π/4` of a multiple of `π`).
* `bwn_junction` (abstract, index bookkeeping): window count from the overlap site + bulk count from `iR` to it + tail beyond the window give the count from `iR`.
* **`hahn_chain_window_count`**: for `[a, b] ⊂ (0, q_*)` there are `t₀ = 1/2` and `ε > 0` with: at every lattice node `h = 1/N ≤ ε` (`N = kmin + m + 1`, `kmin = max |M| |σ| ≥ 1`,
  `n ≤ m`, `x_n = x`), for every bulk site `iR` (`q ∈ [a, b]`, `|cos θ| > 1/2`) and `iR ≤ i₁ ≤ m` with `q_{i₁} ≥ q_*`, the nodes in the bonds `iR, …, i₁ - 1` number exactly
  `⌊Φ(q_{iR})/(π h) + 1/4⌋`.
* **`bix_hahn_rightcount`**: `BixRightCount` (the hypothesis of `bix_hahn_zero_index`) holds at every such site: the right-end count is a theorem.
* **`hahn_chain_zero_index`**, **`hahn_chain_bs_index`**: `bix_hahn_zero_index`, `bix_hahn_bs_index` without the hypothesis `BixRightCount`.

**Claim class: proved** (axiom guards pinned).  Numerics (mpmath, 40 digits, exact `3j` symbols; `BulkIndexHahn` docstring): `R_k = ⌊Φ/(π h) + 1/4⌋` at all non-resonant bulk sites of 8 chains.
**Not formalised:** `τ = -1`, the half-integer lattice and the Racah chains (the same proof with the corresponding window theorems `hahn_chain_kappa_sharp_neg`, `_half`, ...);
constants uniform in `x` or `(M, σ)`; resonant sites `|cos θ| ≤ 1/2` (the count there is `⌊·⌋` or `⌊·⌋ - 1`; not needed for the index of a node bond with definite ends);
the left edge `q → 0` (not needed: the index from the left is `(m - n) - R` from the total node count).
-/

@[expose] public section

open Finset Set FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special


/-- The phase step of the lattice: `δ₁ ≤ θ_j - θ_{j+1} ≤ δ₂` for sites with `0 ≤ q_j`, `q_{j+1} ≤ b < q_*`. -/
lemma bwn_theta_step {x b : ℝ} {N k : ℤ} (hN : 0 < N) (hx0 : 0 < x) (hx1 : x < 1) (hb : b < √(1 - x ^ 2))
    (hq : 0 ≤ bixQ N k) (hq' : bixQ N (k + 1) ≤ b) :
    Real.arccos (x / √(1 - b ^ 2)) ≤ bixTheta x N k - bixTheta x N (k + 1) ∧
      bixTheta x N k - bixTheta x N (k + 1) ≤ Real.arccos x := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  have h1 := bixQ_succ N k
  have hstep := bix_phase_step (x := x) (b := b) (q := bixQ N k) (q' := bixQ N (k + 1)) hx0 hx1 hb hq
    (by rw [h1]; linarith) hq'
  rw [h1] at hstep
  have e : bixQ N k + 1 / (N : ℝ) - bixQ N k = 1 / (N : ℝ) := by ring
  rw [e] at hstep
  have hdiff : bixTheta x N k - bixTheta x N (k + 1) =
      (bkPhase 1 0 1 x (√(1 - x ^ 2)) (bixQ N k) - bkPhase 1 0 1 x (√(1 - x ^ 2)) (bixQ N k + 1 / (N : ℝ))) / (1 / (N : ℝ)) := by
    unfold bixTheta; rw [h1]; ring
  rw [hdiff]
  constructor
  · rw [le_div_iff₀ hh]; exact hstep.1
  · rw [div_le_iff₀ hh]; exact hstep.2


/-- **A definite site in the overlap.**  For `N` large there is a lattice site with `q ∈ [q_* - ρ, q_* - ρ/2]` and `|cos θ| > 1/2`
(the phase decreases by a step in `[δ₁, δ₂]`, `δ₂ < π/2`, so it comes within `π/4` of a multiple of `π`). -/
lemma bwn_exists_good (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) {ρ : ℝ} (hρ : 0 < ρ)
    (hρq : ρ ≤ √(1 - (x : ℝ) ^ 2) / 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℤ, max |M| |σ| < N → 1 / (N : ℝ) ≤ ε →
      ∃ j : ℕ, √(1 - (x : ℝ) ^ 2) - ρ ≤ bixQ N (max |M| |σ| + (j : ℤ)) ∧
        bixQ N (max |M| |σ| + (j : ℤ)) ≤ √(1 - (x : ℝ) ^ 2) - ρ / 2 ∧
        1 / 2 < |Real.cos (bixTheta (x : ℝ) N (max |M| |σ| + (j : ℤ)))| := by
  classical
  have hx0' : (0 : ℝ) < x := by exact_mod_cast hx0
  have hx1' : (x : ℝ) < 1 := by exact_mod_cast hx1
  set qs : ℝ := √(1 - (x : ℝ) ^ 2) with hqs
  have hqspos : 0 < qs := Real.sqrt_pos.2 (by nlinarith)
  set K : ℤ := max |M| |σ| with hK
  have hK0 : 0 ≤ K := le_trans (abs_nonneg M) (le_max_left _ _)
  have hK0' : (0 : ℝ) ≤ K := by exact_mod_cast hK0
  set b2 : ℝ := qs - ρ / 2 with hb2
  have hb2pos : 0 ≤ b2 := by rw [hb2]; linarith
  have hb2q : b2 < qs := by rw [hb2]; linarith
  have hδ1 : 0 < Real.arccos (x / √(1 - b2 ^ 2)) := Real.arccos_pos.2 (bix_lt_one hb2pos hb2q)
  have hδ2 : Real.arccos (x : ℝ) < π / 2 := Real.arccos_lt_pi_div_two.2 hx0'
  set δ1 : ℝ := Real.arccos (x / √(1 - b2 ^ 2)) with hδ1def
  set δ2 : ℝ := Real.arccos (x : ℝ) with hδ2def
  set L : ℕ := ⌈π / δ1⌉₊ + 1 with hLdef
  have hL : π ≤ (L : ℝ) * δ1 := by
    have h1 : π / δ1 ≤ ⌈π / δ1⌉₊ := Nat.le_ceil _
    have h2 : (⌈π / δ1⌉₊ : ℝ) ≤ L := by rw [hLdef]; push_cast; linarith
    have := (div_le_iff₀ hδ1).1 (h1.trans h2)
    linarith
  have hKp : (0 : ℝ) < (K : ℝ) + 1 := by linarith
  refine ⟨min (ρ / (2 * ((L : ℝ) + 2))) (qs / (2 * ((K : ℝ) + 1))), lt_min (by positivity) (by positivity), ?_⟩
  intro N hN hNε
  have hNpos : 0 < N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hh : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  set h : ℝ := 1 / (N : ℝ) with hhdef
  have hh1 : ((L : ℝ) + 2) * h ≤ ρ / 2 := by
    have := (hNε.trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hh2 : ((K : ℝ) + 1) * h ≤ qs / 2 := by
    have := (hNε.trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  set g : ℕ → ℝ := fun j => bixQ N (K + (j : ℤ)) with hg
  set θ : ℕ → ℝ := fun j => bixTheta (x : ℝ) N (K + (j : ℤ)) with hθ
  have hg0 : ∀ j : ℕ, 0 ≤ g j := by
    intro j; simp only [hg, bixQ]
    have : (0 : ℝ) ≤ ((K + (j : ℤ) : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ K + (j : ℤ))
    positivity
  have hgs : ∀ j : ℕ, g (j + 1) = g j + h := by
    intro j
    have e : K + ((j + 1 : ℕ) : ℤ) = K + (j : ℤ) + 1 := by push_cast; ring
    simp only [hg]; rw [e, bixQ_succ]
  have hgt : ∀ t j : ℕ, g (j + t) = g j + t * h := by
    intro t; induction t with
    | zero => intro j; simp
    | succ t ih => intro j; rw [← add_assoc, hgs, ih]; push_cast; ring
  -- first site above `q_* - ρ`
  have hex : ∃ j : ℕ, qs - ρ ≤ g j := by
    refine ⟨⌈qs * N⌉₊, ?_⟩
    have h1 : qs * N ≤ (⌈qs * N⌉₊ : ℝ) := Nat.le_ceil _
    simp only [hg, bixQ]
    push_cast
    have : (⌈qs * N⌉₊ : ℝ) * (1 / (N : ℝ)) ≤ ((K : ℝ) + (⌈qs * N⌉₊ : ℝ) + 1 / 2) * (1 / (N : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ hh.le; linarith
    have h3 : qs * N * (1 / (N : ℝ)) ≤ (⌈qs * N⌉₊ : ℝ) * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_right h1 hh.le
    have h4 : qs * N * (1 / (N : ℝ)) = qs := by field_simp
    linarith
  set j0 := Nat.find hex with hj0
  have hj0s : qs - ρ ≤ g j0 := Nat.find_spec hex
  have hj0pos : j0 ≠ 0 := by
    intro h0
    rw [h0] at hj0s
    have : g 0 = ((K : ℝ) + 1 / 2) * h := by simp [hg, bixQ, hhdef]
    rw [this] at hj0s
    nlinarith
  obtain ⟨j1, hj1⟩ : ∃ j1, j0 = j1 + 1 := ⟨j0 - 1, by omega⟩
  have hj1lt : g j1 < qs - ρ := by
    have := Nat.find_min hex (show j1 < j0 by omega)
    push Not at this; exact this
  have hj0up : g j0 < qs - ρ + h := by rw [hj1, hgs]; linarith
  have hsites : ∀ t : ℕ, t ≤ L → g (j0 + t) ≤ b2 := by
    intro t ht
    rw [hgt]
    have : (t : ℝ) ≤ L := by exact_mod_cast ht
    have : (t : ℝ) * h ≤ L * h := mul_le_mul_of_nonneg_right this hh.le
    rw [hb2]; nlinarith
  have hstep : ∀ t : ℕ, t < L → δ1 ≤ θ (j0 + t) - θ (j0 + t + 1) ∧ θ (j0 + t) - θ (j0 + t + 1) ≤ δ2 := by
    intro t ht
    have e : K + ((j0 + t + 1 : ℕ) : ℤ) = K + ((j0 + t : ℕ) : ℤ) + 1 := by push_cast; ring
    have h2 := hsites (t + 1) (by omega)
    have h3 : bixQ N (K + ((j0 + t : ℕ) : ℤ) + 1) ≤ b2 := by
      rw [← e]; simpa [hg, add_assoc] using h2
    have := bwn_theta_step (x := (x : ℝ)) (b := b2) (N := N) (k := K + ((j0 + t : ℕ) : ℤ)) hNpos hx0' hx1' hb2q (hg0 (j0 + t)) h3
    simp only [hθ, e]
    exact this
  have hθt : ∀ t : ℕ, t ≤ L → θ (j0 + t) ≤ θ j0 - t * δ1 := by
    intro t; induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      have h1 := ih (by omega)
      have h2 := (hstep t (by omega)).1
      push_cast
      have : j0 + (t + 1) = j0 + t + 1 := by ring
      rw [this]; linarith
  set ℓ : ℤ := ⌊θ j0 / π⌋ with hℓ
  have hℓ1 : (ℓ : ℝ) * π ≤ θ j0 := by
    have := Int.floor_le (θ j0 / π)
    rw [le_div_iff₀ Real.pi_pos] at this; linarith
  have hℓ2 : θ j0 < ((ℓ : ℝ) + 1) * π := by
    have := Int.lt_floor_add_one (θ j0 / π)
    rw [div_lt_iff₀ Real.pi_pos] at this; linarith
  have hPex : ∃ t : ℕ, θ (j0 + t) ≤ ℓ * π + π / 4 := by
    refine ⟨L, ?_⟩
    have := hθt L le_rfl
    nlinarith [Real.pi_pos]
  set tt := Nat.find hPex with htt
  have htts : θ (j0 + tt) ≤ ℓ * π + π / 4 := Nat.find_spec hPex
  have httL : tt ≤ L := Nat.find_min' hPex (by
    have := hθt L le_rfl
    nlinarith [Real.pi_pos])
  have hlow : (ℓ : ℝ) * π - π / 4 < θ (j0 + tt) := by
    rcases Nat.eq_zero_or_pos tt with h0 | hpos
    · rw [h0]; simp only [add_zero]; linarith [Real.pi_pos]
    · obtain ⟨s, hs⟩ : ∃ s, tt = s + 1 := ⟨tt - 1, by omega⟩
      have hmin := Nat.find_min hPex (show s < tt by omega)
      push Not at hmin
      have h2 := (hstep s (by omega)).2
      rw [hs, ← add_assoc]
      linarith
  refine ⟨j0 + tt, ?_, ?_, ?_⟩
  · have : g j0 ≤ g (j0 + tt) := by
      rw [hgt]; have : (0 : ℝ) ≤ tt * h := by positivity
      linarith
    exact hj0s.trans this
  · have := hsites tt httL
    rw [hb2] at this; exact this
  · have hφ : |θ (j0 + tt) - ℓ * π| ≤ π / 4 := by
      rw [abs_le]; constructor <;> linarith [Real.pi_pos]
    have e1 : Real.cos (θ (j0 + tt) - ℓ * π) = (-1) ^ ℓ * Real.cos (θ (j0 + tt)) := Real.cos_sub_int_mul_pi _ _
    have e2 : |Real.cos (θ (j0 + tt))| = |Real.cos (θ (j0 + tt) - ℓ * π)| := by
      rw [e1, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
    have e3 : Real.cos (π / 4) ≤ Real.cos |θ (j0 + tt) - ℓ * π| :=
      Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hφ
    rw [Real.cos_abs] at e3
    have e4 : Real.cos (π / 4) = √2 / 2 := Real.cos_pi_div_four
    have e5 : (1 : ℝ) < √2 := by
      rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have e6 : 0 ≤ Real.cos (θ (j0 + tt) - ℓ * π) := by linarith
    show 1 / 2 < |Real.cos (θ (j0 + tt))|
    rw [e2, abs_of_nonneg e6]
    linarith


/-- The abstract junction of the Airy-window count with the bulk count and the tail. -/
lemma bwn_junction {c : ℕ → ℕ} {Q : ℕ → ℝ} {F : ℕ → ℤ} {good : ℕ → Prop} {qs ρ a b2 h : ℝ} {iw m iR i1 : ℕ}
    (hh : 0 < h) (hQs : ∀ i, Q (i + 1) = Q i + h) (_hwin1 : qs ≤ Q iw) (hwin2 : Q iw < qs + h)
    (Hwin : ∀ i, qs - ρ ≤ Q i → Q i ≤ b2 → good i → i < iw ∧ ((∑ j ∈ Ico i iw, c j : ℕ) : ℤ) = F i)
    (Hbulk : ∀ i₁ i₂, i₁ ≤ i₂ → a ≤ Q i₁ → Q i₂ ≤ b2 → good i₁ → good i₂ →
      ((∑ j ∈ Ico i₁ i₂, c j : ℕ) : ℤ) = F i₁ - F i₂)
    (Htail : ∑ j ∈ Ico iw m, c j = 0) (Hex : ∃ j, qs - ρ ≤ Q j ∧ Q j ≤ b2 ∧ good j)
    (_hiR : iR ≤ i1) (hi1m : i1 ≤ m) (haR : a ≤ Q iR) (hRb : Q iR ≤ b2) (hq1 : qs ≤ Q i1) (hgood : good iR) :
    ((∑ j ∈ Ico iR i1, c j : ℕ) : ℤ) = F iR := by
  have hQd : ∀ d i : ℕ, Q (i + d) = Q i + d * h := by
    intro d; induction d with
    | zero => intro i; simp
    | succ d ih => intro i; rw [← add_assoc, hQs, ih]; push_cast; ring
  have hmono : ∀ i j : ℕ, i ≤ j → Q i ≤ Q j := by
    intro i j hij
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    rw [hQd]; have : (0 : ℝ) ≤ d * h := by positivity
    linarith
  have hiw : iw ≤ i1 := by
    by_contra hc
    push Not at hc
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hc
    have h1 := hQd (d + 1) i1
    have : i1 + (d + 1) = iw := by omega
    rw [this] at h1
    have : (0 : ℝ) ≤ d * h := by positivity
    push_cast at h1
    linarith
  have hsumR : ((∑ j ∈ Ico iR iw, c j : ℕ) : ℤ) = F iR := by
    by_cases hA : qs - ρ ≤ Q iR
    · exact (Hwin iR hA hRb hgood).2
    · push Not at hA
      obtain ⟨j', hj1, hj2, hj3⟩ := Hex
      have hRj : iR ≤ j' := by
        by_contra hc; push Not at hc
        have := hmono j' iR hc.le
        linarith
      obtain ⟨hjw, hjsum⟩ := Hwin j' hj1 hj2 hj3
      have hb := Hbulk iR j' hRj haR hj2 hgood hj3
      have hsplit : ∑ j ∈ Ico iR iw, c j = ∑ j ∈ Ico iR j', c j + ∑ j ∈ Ico j' iw, c j :=
        (Finset.sum_Ico_consecutive _ hRj hjw.le).symm
      rw [hsplit]; push_cast at hb hjsum ⊢
      rw [hb, hjsum]; ring
  have hiRw : iR ≤ iw := by
    by_contra hc; push Not at hc
    by_cases hA : qs - ρ ≤ Q iR
    · have := (Hwin iR hA hRb hgood).1; omega
    · push Not at hA
      obtain ⟨j', hj1, hj2, hj3⟩ := Hex
      have hRj : iR ≤ j' := by
        by_contra hc'; push Not at hc'
        have := hmono j' iR hc'.le
        linarith
      have := (Hwin j' hj1 hj2 hj3).1; omega
  have hsplit : ∑ j ∈ Ico iR i1, c j = ∑ j ∈ Ico iR iw, c j + ∑ j ∈ Ico iw i1, c j :=
    (Finset.sum_Ico_consecutive _ hiRw hiw).symm
  have hz : ∑ j ∈ Ico iw i1, c j = 0 := by
    have := Finset.sum_le_sum_of_subset (f := c) (show Finset.Ico iw i1 ⊆ Finset.Ico iw m from
      Finset.Ico_subset_Ico le_rfl hi1m)
    omega
  rw [hsplit, hz]; push_cast; rw [add_zero]; exact_mod_cast hsumR

/-- Bulk count with the margin `sin η < 1/2` made explicit (`bix_hahn_count`, with threshold `1/2`). -/
theorem bwn_bulk_count (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hb : b < √(1 - (x : ℝ) ^ 2)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (N : ℤ) (n : ℕ), max |M| |σ| < N ∧ (n : ℤ) < N - max |M| |σ| ∧ xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x →
        1 / (N : ℝ) ≤ ε → ∀ i₁ i₂ : ℕ, i₁ ≤ i₂ → a ≤ bixQ N (max |M| |σ| + (i₁ : ℤ)) →
          bixQ N (max |M| |σ| + (i₂ : ℤ)) ≤ b →
          1 / 2 < |Real.cos (bixTheta (x : ℝ) N (max |M| |σ| + (i₁ : ℤ)))| →
          1 / 2 < |Real.cos (bixTheta (x : ℝ) N (max |M| |σ| + (i₂ : ℤ)))| →
          ((∑ j ∈ Ico i₁ i₂, bix_c (bixU M σ N x) j : ℕ) : ℤ) =
            ⌊bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (bixQ N (max |M| |σ| + (i₁ : ℤ))) / (π * (1 / (N : ℝ))) + 1 / 4⌋ -
            ⌊bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (bixQ N (max |M| |σ| + (i₂ : ℤ))) / (π * (1 / (N : ℝ))) + 1 / 4⌋ := by
  obtain ⟨η, ε, hη0, hη1, hε, H⟩ := bix_hahn_window M σ x hx0 hx1 a b ha hab hb
  have hsin : Real.sin η < 1 / 2 := by
    rw [← Real.sin_pi_div_six]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hη1
  refine ⟨ε, hε, ?_⟩
  intro N n hnode hNε i₁ i₂ hi hlo hhi hd1 hd2
  obtain ⟨hN, hn, hxn⟩ := hnode
  have hNpos : 0 < N := lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  obtain ⟨s, A, W⟩ := H N n ⟨hN, hn, hxn⟩ hNε i₁ i₂ hi hlo hhi
  have key := bix_count W (i₂ - i₁) i₁ le_rfl (by omega) (bix_def_iff.2 (hsin.trans hd1))
    (by rw [Nat.add_sub_cancel' hi]; exact bix_def_iff.2 (hsin.trans hd2))
  rw [Nat.add_sub_cancel' hi] at key
  rw [key]
  have hh : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  unfold bixTheta
  rw [bixN_theta _ _ hh, bixN_theta _ _ hh]


/-- **The node count of the Airy window, unconditionally** (the last gap of the zero index of the integer `3j` chain, `τ = +1`).
For `[a, b] ⊂ (0, q_*)` there are `t₀ = 1/2` and `ε > 0` such that at every lattice node with `h = 1/N ≤ ε` (`N = kmin + m + 1`, `kmin = max |M| |σ| ≥ 1`,
`n ≤ m`, `x_n = x`), for every site `iR` with `q ∈ [a, b]` and `|cos θ_{iR}| > 1/2` and every `i₁ ≥ iR`, `i₁ ≤ m` with `q_{i₁} ≥ q_*`, the nodes in the bonds
`iR, …, i₁ - 1` number `⌊Φ(q_{iR})/(π h) + 1/4⌋`. -/
theorem hahn_chain_window_count (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∀ a b : ℝ, 0 < a → a < b → b < √(1 - (x : ℝ) ^ 2) → ∃ ε : ℝ, 0 < ε ∧
      ∀ (m n : ℕ), 1 ≤ max |M| |σ| → n ≤ m → xLat (M : ℚ) (σ : ℚ) ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℚ) n = x →
        1 / ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℝ) ≤ ε → ∀ i₁ iR : ℕ, iR ≤ i₁ → i₁ ≤ m →
          a ≤ bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (iR : ℤ)) →
          bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (iR : ℤ)) ≤ b →
          √(1 - (x : ℝ) ^ 2) ≤ bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (i₁ : ℤ)) →
          1 / 2 < |Real.cos (bixTheta (x : ℝ) (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (iR : ℤ)))| →
          ((∑ j ∈ Ico iR i₁, bix_c (bixU M σ (max |M| |σ| + (m : ℤ) + 1) x) j : ℕ) : ℤ) =
            ⌊bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (iR : ℤ))) /
              (π * (1 / ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℝ))) + 1 / 4⌋ := by
  intro a b ha hab hb
  have hx0' : (0 : ℝ) < x := by exact_mod_cast hx0
  have hx1' : (x : ℝ) < 1 := by exact_mod_cast hx1
  obtain ⟨ρ, hρ, hρq, Hw⟩ := bwn_hahn_window M σ x hx0 hx1
  set qs : ℝ := √(1 - (x : ℝ) ^ 2) with hqs
  set b2 : ℝ := max b (qs - ρ / 2) with hb2
  have hb2q : b2 < qs := max_lt hb (by linarith)
  have hbb2 : b ≤ b2 := le_max_left _ _
  have hab2 : a < b2 := lt_of_lt_of_le hab hbb2
  obtain ⟨εw, hεw, Hw'⟩ := Hw b2 (by linarith) hb2q
  obtain ⟨εb, hεb, Hb⟩ := bwn_bulk_count M σ x hx0 hx1 a b2 ha hab2 hb2q
  obtain ⟨εt, hεt, Ht⟩ := bix_hahn_tail M σ x hx0 hx1
  obtain ⟨εg, hεg, Hg⟩ := bwn_exists_good M σ x hx0 hx1 hρ hρq
  refine ⟨min εw (min εb (min εt εg)), lt_min hεw (lt_min hεb (lt_min hεt hεg)), ?_⟩
  intro m n hlo hnm hxn hNε i₁ iR hiR him haR hRb hq1 hcos
  set K : ℤ := max |M| |σ| with hK
  set N : ℤ := K + (m : ℤ) + 1 with hN
  have hK0 : 0 ≤ K := le_trans (abs_nonneg M) (le_max_left _ _)
  have hnode : K < N ∧ (n : ℤ) < N - K ∧ xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x :=
    ⟨by omega, by omega, hxn⟩
  have hNpos : 0 < N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hh : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  have hNεw : 1 / (N : ℝ) ≤ εw := hNε.trans (min_le_left _ _)
  have hNεb : 1 / (N : ℝ) ≤ εb := hNε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hNεt : 1 / (N : ℝ) ≤ εt := hNε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hNεg : 1 / (N : ℝ) ≤ εg := hNε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨iw, hiw1, hiw2, Hwin⟩ := Hw' N n hnode hNεw
  have Htail := Ht m n hlo hnm hxn hNεt iw hiw1
  obtain ⟨j, hj1, hj2, hj3⟩ := Hg N hnode.1 hNεg
  refine bwn_junction (c := bix_c (bixU M σ N x)) (Q := fun i : ℕ => bixQ N (K + (i : ℤ)))
    (F := fun i : ℕ => ⌊bkPhase 1 0 1 (x : ℝ) qs (bixQ N (K + (i : ℤ))) / (π * (1 / (N : ℝ))) + 1 / 4⌋)
    (good := fun i : ℕ => 1 / 2 < |Real.cos (bixTheta (x : ℝ) N (K + (i : ℤ)))|) (qs := qs) (ρ := ρ) (a := a) (b2 := b2)
    (h := 1 / (N : ℝ)) (iw := iw) (m := m) hh ?_ hiw1 hiw2 ?_ ?_ Htail ⟨j, hj1, hj2.trans (le_max_right _ _), hj3⟩ hiR him haR (hRb.trans hbb2) hq1 hcos
  · intro i
    have e : K + ((i + 1 : ℕ) : ℤ) = K + (i : ℤ) + 1 := by push_cast; ring
    simp only [e]; exact bixQ_succ N _
  · intro i h1 h2 h3
    exact Hwin i h1 h2 (by linarith [h3])
  · intro i₁' i₂' hi h1 h2 h3 h4
    exact Hb N n hnode hNεb i₁' i₂' hi h1 h2 h3 h4

/-- info: 'FormalResearch.Special.hahn_chain_window_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_window_count


/-- **`BixRightCount` is a theorem** (the hypothesis of `bix_hahn_zero_index`, `bix_hahn_bs_index`): at every bulk site `iR` with `q ∈ [a, b]` and
`|cos θ_{iR}| > t₀`, the bonds `iR, …, m - 1` carry `⌊Φ(q_{iR})/(π h) + 1/4⌋` nodes. -/
theorem bix_hahn_rightcount (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hb : b < √(1 - (x : ℝ) ^ 2)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (m n : ℕ), 1 ≤ max |M| |σ| → n ≤ m → xLat (M : ℚ) (σ : ℚ) ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℚ) n = x →
        1 / ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℝ) ≤ ε → ∀ iR : ℕ,
          a ≤ bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (iR : ℤ)) →
          bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (iR : ℤ)) ≤ b →
          1 / 2 < |Real.cos (bixTheta (x : ℝ) (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (iR : ℤ)))| →
          BixRightCount M σ (max |M| |σ| + (m : ℤ) + 1) x iR m := by
  have hx0' : (0 : ℝ) < x := by exact_mod_cast hx0
  have hx1' : (x : ℝ) < 1 := by exact_mod_cast hx1
  obtain ⟨ε1, hε1, H⟩ := hahn_chain_window_count M σ x hx0 hx1 a b ha hab hb
  have hqs1 : √(1 - (x : ℝ) ^ 2) < 1 := by
    rw [Real.sqrt_lt' one_pos]; nlinarith
  refine ⟨min ε1 (1 - √(1 - (x : ℝ) ^ 2)), lt_min hε1 (by linarith), ?_⟩
  intro m n hlo hnm hxn hNε iR haR hRb hcos
  set N : ℤ := max |M| |σ| + (m : ℤ) + 1 with hN
  have hK0 : 0 ≤ max |M| |σ| := le_trans (abs_nonneg M) (le_max_left _ _)
  have hNpos : 0 < N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hiRm : iR ≤ m := by
    have := bix_site_le_m hb hNpos hRb
    omega
  have hqm : √(1 - (x : ℝ) ^ 2) ≤ bixQ N (max |M| |σ| + (m : ℤ)) := by
    have hh : 1 / (N : ℝ) ≤ 1 - √(1 - (x : ℝ) ^ 2) := hNε.trans (min_le_right _ _)
    have e : bixQ N (max |M| |σ| + (m : ℤ)) = 1 - 1 / (2 * (N : ℝ)) := by
      unfold bixQ
      have : ((max |M| |σ| + (m : ℤ) : ℤ) : ℝ) = (N : ℝ) - 1 := by
        rw [hN]; push_cast; ring
      rw [this]; field_simp; ring
    rw [e]
    have : 1 / (2 * (N : ℝ)) = 1 / (N : ℝ) / 2 := by field_simp
    rw [this]; linarith
  have hcount := H m n hlo hnm hxn (hNε.trans (min_le_left _ _)) m iR hiRm le_rfl haR hRb hqm hcos
  exact hcount

/-- **The zero index of the integer `3j` chain, unconditional** (`bix_hahn_zero_index` with `BixRightCount` proved). -/
theorem hahn_chain_zero_index (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hb : b < √(1 - (x : ℝ) ^ 2)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (m n : ℕ), 1 ≤ max |M| |σ| → n ≤ m → xLat (M : ℚ) (σ : ℚ) ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℚ) n = x →
        1 / ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℝ) ≤ ε → ∀ i iR : ℕ, i ≤ iR →
          a ≤ bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (i : ℤ)) →
          bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (iR : ℤ)) ≤ b →
          1 / 2 < |Real.cos (bixTheta (x : ℝ) (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (i : ℤ)))| →
          1 / 2 < |Real.cos (bixTheta (x : ℝ) (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (iR : ℤ)))| →
          ((∑ j ∈ Ico i m, bix_c (bixU M σ (max |M| |σ| + (m : ℤ) + 1) x) j : ℕ) : ℤ) =
              ⌊bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (i : ℤ))) /
                (π * (1 / ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℝ))) + 1 / 4⌋ ∧
            ((∑ j ∈ range i, bix_c (bixU M σ (max |M| |σ| + (m : ℤ) + 1) x) j : ℕ) : ℤ) =
              ((m : ℤ) - n) -
              ⌊bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (i : ℤ))) /
                (π * (1 / ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℝ))) + 1 / 4⌋ := by
  obtain ⟨ε1, hε1, H1⟩ := bix_hahn_zero_index M σ x hx0 hx1 a b ha hab hb
  obtain ⟨ε2, hε2, H2⟩ := bix_hahn_rightcount M σ x hx0 hx1 a b ha hab hb
  refine ⟨min ε1 ε2, lt_min hε1 hε2, ?_⟩
  intro m n hlo hnm hxn hNε i iR hi haI hRb hc1 hc2
  set N : ℤ := max |M| |σ| + (m : ℤ) + 1 with hN
  have hK0 : 0 ≤ max |M| |σ| := le_trans (abs_nonneg M) (le_max_left _ _)
  have hNpos : 0 < N := by omega
  have haR : a ≤ bixQ N (max |M| |σ| + (iR : ℤ)) := haI.trans (bixQ_mono hNpos (by omega))
  have hR := H2 m n hlo hnm hxn (hNε.trans (min_le_right _ _)) iR haR hRb hc2
  exact H1 m n hlo hnm hxn (hNε.trans (min_le_left _ _)) i iR hi haI hRb hc1
    hc2 hR

/-- **The Bohr-Sommerfeld integer of a node bond and the index from the left, unconditional** (`bix_hahn_bs_index` with `BixRightCount` proved). -/
theorem hahn_chain_bs_index (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hb : b < √(1 - (x : ℝ) ^ 2)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (m n : ℕ), 1 ≤ max |M| |σ| → n ≤ m → xLat (M : ℚ) (σ : ℚ) ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℚ) n = x →
        1 / ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℝ) ≤ ε → ∀ i iR : ℕ, i + 1 ≤ iR →
          a ≤ bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (i : ℤ)) →
          bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (iR : ℤ)) ≤ b →
          1 / 2 < |Real.cos (bixTheta (x : ℝ) (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (i : ℤ)))| →
          1 / 2 < |Real.cos (bixTheta (x : ℝ) (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + ((i + 1 : ℕ) : ℤ)))| →
          1 / 2 < |Real.cos (bixTheta (x : ℝ) (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (iR : ℤ)))| →
          bixU M σ (max |M| |σ| + (m : ℤ) + 1) x i * bixU M σ (max |M| |σ| + (m : ℤ) + 1) x (i + 1) < 0 →
          ∃ R : ℕ, (∑ j ∈ Ico i m, bix_c (bixU M σ (max |M| |σ| + (m : ℤ) + 1) x) j) = R ∧
            ((∑ j ∈ range i, bix_c (bixU M σ (max |M| |σ| + (m : ℤ) + 1) x) j : ℕ) : ℤ) = ((m : ℤ) - n) - R ∧
            bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + ((i + 1 : ℕ) : ℤ))) /
                (1 / ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℝ)) < π * ((R : ℝ) - 1 / 4) ∧
            π * ((R : ℝ) - 1 / 4) ≤ bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (i : ℤ))) /
                (1 / ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℝ)) := by
  obtain ⟨ε1, hε1, H1⟩ := bix_hahn_bs_index M σ x hx0 hx1 a b ha hab hb
  obtain ⟨ε2, hε2, H2⟩ := bix_hahn_rightcount M σ x hx0 hx1 a b ha hab hb
  refine ⟨min ε1 ε2, lt_min hε1 hε2, ?_⟩
  intro m n hlo hnm hxn hNε i iR hi haI hRb hc1 hc2 hc3 hnode
  set N : ℤ := max |M| |σ| + (m : ℤ) + 1 with hN
  have hK0 : 0 ≤ max |M| |σ| := le_trans (abs_nonneg M) (le_max_left _ _)
  have hNpos : 0 < N := by omega
  have haR : a ≤ bixQ N (max |M| |σ| + (iR : ℤ)) := haI.trans (bixQ_mono hNpos (by omega))
  have hR := H2 m n hlo hnm hxn (hNε.trans (min_le_right _ _)) iR haR hRb hc3
  exact H1 m n hlo hnm hxn (hNε.trans (min_le_left _ _)) i iR hi haI hRb hc1
    hc2 hc3 hR hnode

/-- info: 'FormalResearch.Special.hahn_chain_bs_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_bs_index

/-- info: 'FormalResearch.Special.bix_hahn_rightcount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bix_hahn_rightcount

/-- info: 'FormalResearch.Special.hahn_chain_zero_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_zero_index

end FormalResearch.Special
