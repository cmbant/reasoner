module

public import FormalResearch.Special.RacahWindowBulk
public import FormalResearch.Special.RacahWindowTail
public import FormalResearch.Special.BulkWindowIndex

/-!
# Racah window, part 6: the right count of the integer `6j` chain (`τ = ±1`)

Junction of the Airy-window count (`rwn_racah_window`, `RacahWindowChain`), the bulk count (`rwn_racah_bulk`, `RacahWindowBulk`) and the tail (`rwn_racah_tail`, `RacahWindowTail`),
exactly as `hahn_chain_window_count` (`BulkWindowIndex`) does for the `3j` chain; the abstract junction `bwn_junction` is reused.  All theorems are for the chain `Y = u Ŷ` of `RwData`
(`u ≡ 1`, `τ = +1`; `u_k = (-1)^k`, `τ = -1`); `RwData.pos`, `RwData.neg` supply the data of the two physical chains.

* `rwn_theta_step`, `rwn_exists_good`: the phase `θ_j = Φ(q_j)/h - π/4` decreases by a step in `[arccos hi, arccos lo]`, `arccos lo < π/2` near the turn (`u > 0` there:
  `RwGeo.near_turn_pos`), hence in `[q_* - ρ, q_* - ρ/2]` there is a site with `|cos θ| > 1/2`.
* **`rwn_chain_window_count`**: for `[a', b'] ⊂ (0, q_*)` there is `ε > 0` such that for every finite Racah system with `A h = α`, `B h = β`, `cos = x`, `h ≤ ε`, `kmin = max |m| |n| ≥ 1`,
  every bulk site `iR` (`q ∈ [a', b']`, `|cos θ_{iR}| > 1/2`: the literal threshold, no existential `t₀`) and every `iR ≤ i₁ ≤ D'` with `q_{i₁} ≥ q_*` (`D' = kmax - kmin`),
  the nodes of `s ↦ Y_{kmin+s}` in the bonds `iR, …, i₁ - 1` number exactly `⌊Φ(q_{iR})/(π h) + 1/4⌋`.
* **`rwn_chain_rightcount`**: with `i₁ = D'` (the last site): the nodes in the bonds `iR, …, D' - 1` number `⌊Φ(q_{iR})/(π h) + 1/4⌋`.  This identifies the Bohr-Sommerfeld integer of
  `racah_chain_bulk_zeros(_neg)` with the number of nodes at or to the right of the site.
* `racah_chain_window_count`, `bix_racah_rightcount`: the untwisted chain `Ŷ` (`τ = +1`) in the form without `u`.

Numerics (mpmath, 40 digits, exact `6j` symbols from the Racah sum, throw-away script, numerical evidence only): integer `τ = +1` chains `(m, n)` and `(A, B, C) = k(2, 3, 3/2)`,
`k = 5, 11, 25, 51` (`m = n = 1`); `k(3, 2, 3/2)`, `k = 31, 61, 101` (`m = n = 1`); `k(2, 3, 3/2)` with `(m, n) = (3, 1)`, `(-1, 1)`, `k = 31, 61`; and twisted `τ = -1` chains `(-1)^k Ŷ_k` with
`(A, B, C) = k(2, 2, 3/2)`, `k = 11, 25, 51`, and `k(2, 3, 5/2)`, `k = 31, 61` (`m = n = 1`); `h = 2/A` (`α = 2`): at every site with `0.15 q_* ≤ q_k < 0.97 q_*` and `|cos(Φ/h - π/4)| > 1/2`
(about 1000 sites `τ = +1`, 370 sites `τ = -1`) the number `R_k` of nodes in the bonds `j ≥ k` equals `⌊Φ(q_k)/(π h) + 1/4⌋` (offset `0`; the offsets `±1` fail at every such site, negative control),
and the total number of nodes of the chain is `c - c_min` (`τ = +1`) resp. `D' - (c - c_min)` (`τ = -1`).

**Claim class: proved** (axiom guards pinned).  The total node count and the zero index from the left are `RacahWindowNodes`, `RacahWindowZero`.  **Not formalised:** the half-integer lattice,
`kmin = 0`; uniformity of `ε` in `(α, β, x, m, n)`; resonant sites `|cos θ| ≤ 1/2`.
-/

@[expose] public section

open Finset Set FormalResearch.Racah FormalResearch.Racah.SixJ FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

/-- The phase step of the lattice: `arccos hi ≤ θ_k - θ_{k+1} ≤ arccos lo` for sites with `0 ≤ q_k`, `q_{k+1} ≤ b`. -/
lemma rwn_theta_step {P Q τ x qs θ h lo hi : ℝ} (G : RwGeo P Q τ x qs)
    (k : ℤ) (hlohi : ∀ t ∈ Set.Icc (rwQ θ h k) (rwQ θ h (k + 1)), lo ≤ hrU P Q τ x t ∧ hrU P Q τ x t ≤ hi)
    (hh : 0 < h) (hq : 0 ≤ rwQ θ h k) (hq' : rwQ θ h (k + 1) ≤ qs) :
    Real.arccos hi ≤ rwTheta P Q τ x qs θ h k - rwTheta P Q τ x qs θ h (k + 1) ∧
      rwTheta P Q τ x qs θ h k - rwTheta P Q τ x qs θ h (k + 1) ≤ Real.arccos lo := by
  have h1 := rwQ_succ θ h k
  have hstep := G.phase_step hlohi hq (by rw [h1]; linarith) hq'
  rw [h1] at hstep
  have e : rwQ θ h k + h - rwQ θ h k = h := by ring
  rw [e] at hstep
  have hdiff : rwTheta P Q τ x qs θ h k - rwTheta P Q τ x qs θ h (k + 1) =
      (bkPhase P Q τ x qs (rwQ θ h k) - bkPhase P Q τ x qs (rwQ θ h k + h)) / h := by
    unfold rwTheta; rw [h1]; ring
  rw [hdiff]
  constructor
  · rw [le_div_iff₀ hh]; linarith [hstep.1]
  · rw [div_le_iff₀ hh]; linarith [hstep.2]

/-- **A definite site in the overlap.**  For small `h` there is a lattice site with `q ∈ [q_* - ρ, q_* - ρ/2]` and `|cos θ| > 1/2`. -/
lemma rwn_exists_good {P Q τ x qs θ : ℝ} (G : RwGeo P Q τ x qs) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) {ρ : ℝ} (hρ : 0 < ρ) (hρq : ρ ≤ qs / 2)
    (hρu : ∀ t, qs - ρ ≤ t → t ≤ qs → 0 < hrU P Q τ x t) (K : ℤ) (hK : 0 ≤ K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ, 0 < h → h ≤ ε →
      ∃ j : ℕ, qs - ρ ≤ rwQ θ h (K + (j : ℤ)) ∧ rwQ θ h (K + (j : ℤ)) ≤ qs - ρ / 2 ∧
        1 / 2 < |Real.cos (rwTheta P Q τ x qs θ h (K + (j : ℤ)))| := by
  classical
  have hqs := G.hqs
  have hK0' : (0 : ℝ) ≤ K := by exact_mod_cast hK
  set b2 : ℝ := qs - ρ / 2 with hb2
  have hb2pos : 0 ≤ b2 := by rw [hb2]; linarith
  have hb2q : b2 < qs := by rw [hb2]; linarith
  have hcb : qs - ρ ≤ b2 := by rw [hb2]; linarith
  obtain ⟨lo, hi, ⟨t1, ht1, ht1e⟩, hhi, Hu⟩ := G.u_bounds_Icc (by linarith) hcb hb2q
  have hlo : 0 < lo := by rw [ht1e]; exact hρu t1 ht1.1 (ht1.2.trans hb2q.le)
  have hδ1 : 0 < Real.arccos hi := Real.arccos_pos.2 hhi
  have hδ2 : Real.arccos lo < π / 2 := Real.arccos_lt_pi_div_two.2 hlo
  set δ1 : ℝ := Real.arccos hi with hδ1def
  set δ2 : ℝ := Real.arccos lo with hδ2def
  set L : ℕ := ⌈π / δ1⌉₊ + 1 with hLdef
  have hL : π ≤ (L : ℝ) * δ1 := by
    have h1 : π / δ1 ≤ ⌈π / δ1⌉₊ := Nat.le_ceil _
    have h2 : (⌈π / δ1⌉₊ : ℝ) ≤ L := by rw [hLdef]; push_cast; linarith
    have := (div_le_iff₀ hδ1).1 (h1.trans h2)
    linarith
  have hKp : (0 : ℝ) < (K : ℝ) + 2 := by linarith
  refine ⟨min (ρ / (2 * ((L : ℝ) + 2))) (qs / (2 * ((K : ℝ) + 2))), lt_min (by positivity) (by positivity), ?_⟩
  intro h hh hhε
  have hh1 : ((L : ℝ) + 2) * h ≤ ρ / 2 := by
    have := (hhε.trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hh2 : ((K : ℝ) + 2) * h ≤ qs / 2 := by
    have := (hhε.trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  set g : ℕ → ℝ := fun j => rwQ θ h (K + (j : ℤ)) with hg
  set θs : ℕ → ℝ := fun j => rwTheta P Q τ x qs θ h (K + (j : ℤ)) with hθs
  have hg0 : ∀ j : ℕ, 0 ≤ g j := by
    intro j; simp only [hg, rwQ]
    have : (0 : ℝ) ≤ ((K + (j : ℤ) : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ K + (j : ℤ))
    positivity
  have hgs : ∀ j : ℕ, g (j + 1) = g j + h := by
    intro j
    have e : K + ((j + 1 : ℕ) : ℤ) = K + (j : ℤ) + 1 := by push_cast; ring
    simp only [hg]; rw [e, rwQ_succ]
  have hgt : ∀ t j : ℕ, g (j + t) = g j + t * h := by
    intro t; induction t with
    | zero => intro j; simp
    | succ t ih => intro j; rw [← add_assoc, hgs, ih]; push_cast; ring
  have hex : ∃ j : ℕ, qs - ρ ≤ g j := by
    refine ⟨⌈qs / h⌉₊, ?_⟩
    have h1 : qs / h ≤ (⌈qs / h⌉₊ : ℝ) := Nat.le_ceil _
    simp only [hg, rwQ]
    push_cast
    have h3 : qs ≤ (⌈qs / h⌉₊ : ℝ) * h := by
      have := mul_le_mul_of_nonneg_right h1 hh.le
      rwa [div_mul_cancel₀ _ hh.ne'] at this
    have : (⌈qs / h⌉₊ : ℝ) * h ≤ ((K : ℝ) + (⌈qs / h⌉₊ : ℝ) + θ) * h := by
      apply mul_le_mul_of_nonneg_right _ hh.le; linarith
    linarith
  set j0 := Nat.find hex with hj0
  have hj0s : qs - ρ ≤ g j0 := Nat.find_spec hex
  have hj0pos : j0 ≠ 0 := by
    intro h0
    rw [h0] at hj0s
    have : g 0 = ((K : ℝ) + θ) * h := by simp [hg, rwQ]
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
  have hstep : ∀ t : ℕ, t < L → δ1 ≤ θs (j0 + t) - θs (j0 + t + 1) ∧ θs (j0 + t) - θs (j0 + t + 1) ≤ δ2 := by
    intro t ht
    have e : K + ((j0 + t + 1 : ℕ) : ℤ) = K + ((j0 + t : ℕ) : ℤ) + 1 := by push_cast; ring
    have h2 := hsites (t + 1) (by omega)
    have h3 : rwQ θ h (K + ((j0 + t : ℕ) : ℤ) + 1) ≤ b2 := by
      rw [← e]; simpa [hg, add_assoc] using h2
    have h4 : qs - ρ ≤ rwQ θ h (K + ((j0 + t : ℕ) : ℤ)) := by
      have : g (j0 + t) = g j0 + t * h := hgt t j0
      have h5 : 0 ≤ (t : ℝ) * h := by positivity
      have : g j0 ≤ g (j0 + t) := by linarith
      exact hj0s.trans this
    have := rwn_theta_step (θ := θ) (h := h) G (K + ((j0 + t : ℕ) : ℤ))
      (fun s hs => Hu s ⟨h4.trans hs.1, hs.2.trans h3⟩) hh (hg0 (j0 + t)) (h3.trans hb2q.le)
    simp only [hθs, e]
    exact this
  have hθt : ∀ t : ℕ, t ≤ L → θs (j0 + t) ≤ θs j0 - t * δ1 := by
    intro t; induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      have h1 := ih (by omega)
      have h2 := (hstep t (by omega)).1
      push_cast
      have : j0 + (t + 1) = j0 + t + 1 := by ring
      rw [this]; linarith
  set ℓ : ℤ := ⌊θs j0 / π⌋ with hℓ
  have hℓ1 : (ℓ : ℝ) * π ≤ θs j0 := by
    have := Int.floor_le (θs j0 / π)
    rw [le_div_iff₀ Real.pi_pos] at this; linarith
  have hℓ2 : θs j0 < ((ℓ : ℝ) + 1) * π := by
    have := Int.lt_floor_add_one (θs j0 / π)
    rw [div_lt_iff₀ Real.pi_pos] at this; linarith
  have hPex : ∃ t : ℕ, θs (j0 + t) ≤ ℓ * π + π / 4 := by
    refine ⟨L, ?_⟩
    have := hθt L le_rfl
    nlinarith [Real.pi_pos]
  set tt := Nat.find hPex with htt
  have htts : θs (j0 + tt) ≤ ℓ * π + π / 4 := Nat.find_spec hPex
  have httL : tt ≤ L := Nat.find_min' hPex (by
    have := hθt L le_rfl
    nlinarith [Real.pi_pos])
  have hlow : (ℓ : ℝ) * π - π / 4 < θs (j0 + tt) := by
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
  · have hφ : |θs (j0 + tt) - ℓ * π| ≤ π / 4 := by
      rw [abs_le]; constructor <;> linarith [Real.pi_pos]
    have e1 : Real.cos (θs (j0 + tt) - ℓ * π) = (-1) ^ ℓ * Real.cos (θs (j0 + tt)) := Real.cos_sub_int_mul_pi _ _
    have e2 : |Real.cos (θs (j0 + tt))| = |Real.cos (θs (j0 + tt) - ℓ * π)| := by
      rw [e1, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
    have e3 : Real.cos (π / 4) ≤ Real.cos |θs (j0 + tt) - ℓ * π| :=
      Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hφ
    rw [Real.cos_abs] at e3
    have e4 : Real.cos (π / 4) = √2 / 2 := Real.cos_pi_div_four
    have e5 : (1 : ℝ) < √2 := by
      rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have e6 : 0 ≤ Real.cos (θs (j0 + tt) - ℓ * π) := by linarith
    show 1 / 2 < |Real.cos (θs (j0 + tt))|
    rw [e2, abs_of_nonneg e6]
    linarith


/-- **The node count of the Airy window, bulk and tail of the integer `6j` chain** (`τ = ±1`; the Racah counterpart of `hahn_chain_window_count`): see the module docstring.
The threshold is the literal `1/2 < |cos θ_{iR}|`. -/
theorem rwn_chain_window_count {α β x τ qs : ℝ} {m n : ℤ} {u : ℤ → ℝ} (D : RwData α β x τ qs m n u) :
    ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < qs → ∃ ε : ℝ, 0 < ε ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x → 1 ≤ max |m| |n| →
        ∀ i₁ iR : ℕ, iR ≤ i₁ → i₁ ≤ D' →
          a' ≤ rwQ (1 / 2) h (max |m| |n| + (iR : ℤ)) → rwQ (1 / 2) h (max |m| |n| + (iR : ℤ)) ≤ b' →
          qs ≤ rwQ (1 / 2) h (max |m| |n| + (i₁ : ℤ)) →
          1 / 2 < |Real.cos (rwTheta (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x qs (1 / 2) h (max |m| |n| + (iR : ℤ)))| →
          ((∑ j ∈ Ico iR i₁, bix_c (fun s : ℕ => rwY u a b c m n (max |m| |n| + (s : ℤ))) j : ℕ) : ℤ) =
            ⌊bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x qs (rwQ (1 / 2) h (max |m| |n| + (iR : ℤ))) / (π * h) + 1 / 4⌋ := by
  intro a' b' ha hab hb
  have G := D.geo
  have hqs := D.hqs
  obtain ⟨ρ0, hρ0, hρq0, Hw⟩ := rwn_racah_window D
  obtain ⟨ρu, hρu0, -, hρu⟩ := G.near_turn_pos
  set ρ : ℝ := min ρ0 ρu with hρdef
  have hρ : 0 < ρ := lt_min hρ0 hρu0
  have hρq : ρ ≤ qs / 2 := (min_le_left _ _).trans hρq0
  have hρu' : ∀ t, qs - ρ ≤ t → t ≤ qs → 0 < hrU (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x t :=
    fun t h1 h2 => hρu t (by linarith [min_le_right ρ0 ρu]) h2
  set b2 : ℝ := max b' (qs - ρ / 2) with hb2
  have hb2q : b2 < qs := max_lt hb (by linarith)
  have hbb2 : b' ≤ b2 := le_max_left _ _
  have hab2 : a' < b2 := lt_of_lt_of_le hab hbb2
  obtain ⟨εw, hεw, Hw'⟩ := Hw b2 (by linarith) hb2q
  obtain ⟨εb, hεb, Hb⟩ := rwn_racah_bulk D a' b2 ha hab2 hb2q
  obtain ⟨εt, hεt, Ht⟩ := rwn_racah_tail D
  have hK : 0 ≤ max |m| |n| := le_trans (abs_nonneg m) (le_max_left _ _)
  obtain ⟨εg, hεg, Hg⟩ := rwn_exists_good (θ := 1 / 2) G (by norm_num) (by norm_num) hρ hρq hρu' (max |m| |n|) hK
  refine ⟨min εw (min εb (min εt εg)), lt_min hεw (lt_min hεb (lt_min hεt hεg)), ?_⟩
  intro a b c D' hsys i hc h hh hhε hAh hBh hx hlo i₁ iR hiR hi1D haR hRb hq1 hcos
  set K : ℤ := max |m| |n| with hKdef
  have hhεw : h ≤ εw := hhε.trans (min_le_left _ _)
  have hhεb : h ≤ εb := hhε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhεt : h ≤ εt := hhε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hhεg : h ≤ εg := hhε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨iw, hiw1, hiw2, Hwin⟩ := Hw' a b c D' hsys i hc h hh hhεw hAh hBh hx
  have Htail := Ht a b c D' hsys i hc h hh hhεt hAh hBh hx hlo iw hiw1
  obtain ⟨j, hj1, hj2, hj3⟩ := Hg h hh hhεg
  refine bwn_junction (c := bix_c (fun s : ℕ => rwY u a b c m n (K + (s : ℤ))))
    (Q := fun i : ℕ => rwQ (1 / 2) h (K + (i : ℤ)))
    (F := fun i : ℕ => ⌊bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x qs (rwQ (1 / 2) h (K + (i : ℤ))) / (π * h) + 1 / 4⌋)
    (good := fun i : ℕ => 1 / 2 < |Real.cos (rwTheta (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x qs (1 / 2) h (K + (i : ℤ)))|)
    (qs := qs) (ρ := ρ) (a := a') (b2 := b2) (h := h) (iw := iw) (m := D') hh ?_ hiw1 hiw2 ?_ ?_ Htail
    ⟨j, hj1, hj2.trans (le_max_right _ _), hj3⟩ hiR hi1D haR (hRb.trans hbb2) hq1 hcos
  · intro i
    have e : K + ((i + 1 : ℕ) : ℤ) = K + (i : ℤ) + 1 := by push_cast; ring
    simp only [e]; exact rwQ_succ _ _ _
  · intro i h1 h2 h3
    exact Hwin i (by linarith [min_le_left ρ0 ρu]) h2 (by linarith [h3])
  · intro i₁' i₂' hi h1 h2 h3 h4
    exact Hb a b c D' hsys i hc h hh hhεb hAh hBh hx i₁' i₂' hi h1 h2 h3 h4

/-- info: 'FormalResearch.Special.rwn_chain_window_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rwn_chain_window_count


/-- The last site of the chain is beyond the turn: `q_* ≤ (kmax + 1/2) h` for `h ≤ 2(min(2α, 2β) - q_*)`. -/
lemma rw_top_site {α β h qs : ℝ} (hα : 0 < α) (hβ : 0 < β) (a b m n : ℤ) {D' : ℕ}
    (hsys : RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D')
    (hAh : wA (a : ℚ) (n : ℚ) * h = α) (hBh : wB (b : ℚ) (m : ℚ) * h = β) (hh : 0 < h)
    (hqa : qs < 2 * α) (hqb : qs < 2 * β) (hε : h ≤ 2 * (min (2 * α) (2 * β) - qs)) :
    qs ≤ rwQ (1 / 2) h (max |m| |n| + (D' : ℤ)) := by
  have hD := rw_D_eq a b m n hsys
  have e : max |m| |n| + (D' : ℤ) = min (2 * b + m) (2 * a + n) := by omega
  rw [e]
  unfold rwQ
  have hma : min (2 * α) (2 * β) ≤ 2 * α := min_le_left _ _
  have hmb : min (2 * α) (2 * β) ≤ 2 * β := min_le_right _ _
  rcases min_choice (2 * b + m) (2 * a + n) with hc' | hc'
  · rw [hc']
    have : ((2 * b + m : ℤ) : ℝ) + 1 = 2 * wB (b : ℚ) (m : ℚ) := by unfold wB; push_cast; ring
    have h2 : (((2 * b + m : ℤ) : ℝ) + 1 / 2) * h = 2 * β - h / 2 := by
      have : (((2 * b + m : ℤ) : ℝ) + 1 / 2) = 2 * wB (b : ℚ) (m : ℚ) - 1 / 2 := by unfold wB; push_cast; ring
      rw [this, sub_mul, mul_assoc, hBh]; ring
    rw [h2]; linarith
  · rw [hc']
    have h2 : (((2 * a + n : ℤ) : ℝ) + 1 / 2) * h = 2 * α - h / 2 := by
      have : (((2 * a + n : ℤ) : ℝ) + 1 / 2) = 2 * wA (a : ℚ) (n : ℚ) - 1 / 2 := by unfold wA; push_cast; ring
      rw [this, sub_mul, mul_assoc, hAh]; ring
    rw [h2]; linarith

/-- **`BixRightCount`-style right count of the integer `6j` chain** (`τ = ±1`): at every bulk site `iR` (`q ∈ [a', b']`, `|cos θ_{iR}| > 1/2`) the bonds `iR, …, D' - 1` carry
exactly `⌊Φ(q_{iR})/(π h) + 1/4⌋` nodes of `s ↦ Y_{kmin+s}`. -/
theorem rwn_chain_rightcount {α β x τ qs : ℝ} {m n : ℤ} {u : ℤ → ℝ} (D : RwData α β x τ qs m n u) :
    ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < qs → ∃ ε : ℝ, 0 < ε ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x → 1 ≤ max |m| |n| →
        ∀ iR : ℕ, a' ≤ rwQ (1 / 2) h (max |m| |n| + (iR : ℤ)) → rwQ (1 / 2) h (max |m| |n| + (iR : ℤ)) ≤ b' →
          1 / 2 < |Real.cos (rwTheta (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x qs (1 / 2) h (max |m| |n| + (iR : ℤ)))| →
          ((∑ j ∈ Ico iR D', bix_c (fun s : ℕ => rwY u a b c m n (max |m| |n| + (s : ℤ))) j : ℕ) : ℤ) =
            ⌊bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x qs (rwQ (1 / 2) h (max |m| |n| + (iR : ℤ))) / (π * h) + 1 / 4⌋ := by
  intro a' b' ha hab hb
  have hα := D.hα
  have hβ := D.hβ
  have hqs := D.hqs
  have hαq := D.hαq
  have hβq := D.hβq
  obtain ⟨ε1, hε1, H⟩ := rwn_chain_window_count D a' b' ha hab hb
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
  intro a b c D' hsys i hc h hh hhε hAh hBh hx hlo iR haR hRb hcos
  have hK : 0 ≤ max |m| |n| := le_trans (abs_nonneg m) (le_max_left _ _)
  have hiRD : iR ≤ D' := by
    by_contra hcon
    push Not at hcon
    have h1 : rwQ (1 / 2) h (max |m| |n| + (D' : ℤ)) ≤ rwQ (1 / 2) h (max |m| |n| + (iR : ℤ)) :=
      rwQ_mono hh (by omega)
    have h2 := rw_top_site hα hβ a b m n hsys hAh hBh hh hqa hqb (hhε.trans (min_le_right _ _))
    have h3 : rwQ (1 / 2) h (max |m| |n| + (iR : ℤ)) ≥ qs := le_trans h2 h1
    have h4 : rwQ (1 / 2) h (max |m| |n| + (iR : ℤ)) < qs := lt_of_le_of_lt hRb hb
    linarith
  exact H a b c D' hsys i hc h hh (hhε.trans (min_le_left _ _)) hAh hBh hx hlo D' iR hiRD le_rfl haR hRb
    (rw_top_site hα hβ a b m n hsys hAh hBh hh hqa hqb (hhε.trans (min_le_right _ _))) hcos

/-- info: 'FormalResearch.Special.rwn_chain_rightcount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rwn_chain_rightcount

end FormalResearch.Special
