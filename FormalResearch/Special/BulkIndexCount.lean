module

public import FormalResearch.Special.BulkIndexPhase
public import FormalResearch.Special.ChainOscNodal

/-!
# Bulk index, part 2: sign changes of a sequence in amplitude-phase form equal the drop of `⌊θ/π + 1/2⌋`

Abstract counting theorem.  Let `u : ℕ → ℝ` be a sequence with an amplitude-phase approximation
`|u_j - s A_j cos θ_j| ≤ (sin η) A_j` (`s = ±1`, `A_j > 0`, `0 < η < π/2`) on the sites `k₀ ≤ j ≤ k₁`, whose phase decreases
by a step in `(2η, π - 2η)` from site to site.  Call a site *definite* if `sin η < sin (bixPhi θ_j)`, i.e. `|cos θ_j| > sin η`;
there the sign of `u_j` is the sign of `s cos θ_j`, namely `s (-1)^{bixN θ_j}`.

* `bix_c u j`: the contribution of the bond `(j, j+1)` to the nodal count of `ChainOscNodal.cho_nodal` (a sign change
  `u_j u_{j+1} < 0`, plus an interior zero `u_j = 0`, `0 < j`); `bix_nodal_eq_sum`: `cho_nodal u m = ∑_{j<m} bix_c u j`.
* **`bix_count`**: for definite sites `k ≤ k'` in `[k₀, k₁]` the number of nodes in the bonds `k, …, k'-1` is exactly
  `⌊θ_k/π + 1/2⌋ - ⌊θ_{k'}/π + 1/2⌋`.  In particular every site that is not definite is isolated (`bix_not_consecutive`) and
  the count never depends on the value of `u` at such a site (it may be positive, zero or negative).
* **`bix_count_right`** (the composition with an assumed right-end count): if the nodes in the bonds `k_R, …, m-1` are
  `⌊θ_{k_R}/π + 1/2⌋` for a definite site `k_R ≤ k₁`, then for every definite `k ≤ k_R` the nodes in the bonds `k, …, m-1`
  are `⌊θ_k/π + 1/2⌋`.

**Claim class: proved** (elementary: floors, signs and induction on the site index).  Not formalised: that the amplitude-phase
hypothesis holds (that is `BulkIndexHahn`) and the right-end count (an explicit hypothesis of `bix_count_right`).
-/

@[expose] public section

open Finset Real

namespace FormalResearch.Special

/-- The contribution of the bond `(j, j+1)` to the node count (`cho_nodal` counts `u_j u_{j+1} < 0` and interior zeros). -/
noncomputable def bix_c (u : ℕ → ℝ) (j : ℕ) : ℕ :=
  (if u j * u (j + 1) < 0 then 1 else 0) + (if 0 < j ∧ u j = 0 then 1 else 0)

theorem bix_nodal_eq_sum (u : ℕ → ℝ) (m : ℕ) : cho_nodal u m = ∑ j ∈ range m, bix_c u j := by
  induction m with
  | zero => simp [cho_nodal_zero]
  | succ m ih => rw [cho_nodal_succ, sum_range_succ, ih]; unfold bix_c; ring

/-- Sites where the amplitude-phase form decides the sign of `u`: `sin η < sin (bixPhi θ_j)` (i.e. `sin η < |cos θ_j|`). -/
def BixDef (θ : ℕ → ℝ) (η : ℝ) (j : ℕ) : Prop := Real.sin η < Real.sin (bixPhi (θ j))

/-- The hypotheses on a window `[k₀, k₁]`: amplitude-phase form with tolerance `sin η`, and phase steps in `(2η, π - 2η)`. -/
structure BixWin (u θ A : ℕ → ℝ) (s η : ℝ) (k₀ k₁ : ℕ) : Prop where
  hs : s = 1 ∨ s = -1
  hη0 : 0 < η
  hη1 : η < π / 2
  hA : ∀ j, k₀ ≤ j → j ≤ k₁ → 0 < A j
  hY : ∀ j, k₀ ≤ j → j ≤ k₁ → |u j - s * A j * Real.cos (θ j)| ≤ Real.sin η * A j
  hd : ∀ j, k₀ ≤ j → j < k₁ → 2 * η < θ j - θ (j + 1) ∧ θ j - θ (j + 1) + 2 * η < π

namespace BixWin

variable {u θ A : ℕ → ℝ} {s η : ℝ} {k₀ k₁ : ℕ}

/-- At a definite site `ε s u_j > 0` with `ε = (-1)^{bixN θ_j}`. -/
theorem sign_pos (W : BixWin u θ A s η k₀ k₁) {j : ℕ} (h0 : k₀ ≤ j) (h1 : j ≤ k₁) (hD : BixDef θ η j) :
    0 < (-1 : ℝ) ^ (bixN (θ j)) * s * u j := by
  have hA := W.hA j h0 h1
  have hY := W.hY j h0 h1
  set ε : ℝ := (-1 : ℝ) ^ (bixN (θ j)) with hε
  have hεε : ε * ε = 1 := bix_neg_one_zpow_sq _
  have hss : s * s = 1 := by rcases W.hs with h | h <;> rw [h] <;> norm_num
  have hc : Real.cos (θ j) = ε * Real.sin (bixPhi (θ j)) := bix_cos_eq _
  have e : ε * s * u j - A j * Real.sin (bixPhi (θ j)) = ε * s * (u j - s * A j * Real.cos (θ j)) := by
    rw [hc]; linear_combination (A j * Real.sin (bixPhi (θ j)) * s * s) * hεε + (A j * Real.sin (bixPhi (θ j))) * hss
  have habs : |ε * s * (u j - s * A j * Real.cos (θ j))| = |u j - s * A j * Real.cos (θ j)| := by
    rw [abs_mul, abs_mul]
    have h1 : |ε| = 1 := by
      have : |ε| * |ε| = 1 := by rw [← abs_mul, hεε]; simp
      nlinarith [abs_nonneg ε]
    have h2 : |s| = 1 := by
      have : |s| * |s| = 1 := by rw [← abs_mul, hss]; simp
      nlinarith [abs_nonneg s]
    rw [h1, h2]; ring
  have : |ε * s * u j - A j * Real.sin (bixPhi (θ j))| ≤ Real.sin η * A j := by rw [e, habs]; exact hY
  have := (abs_le.1 this).1
  unfold BixDef at hD
  nlinarith

end BixWin

section Count

variable {u θ A : ℕ → ℝ} {s η : ℝ} {k₀ k₁ : ℕ}

theorem bix_not_def_range (W : BixWin u θ A s η k₀ k₁) {j : ℕ} (h : ¬ BixDef θ η j) :
    bixPhi (θ j) ≤ η ∨ π - η ≤ bixPhi (θ j) := by
  unfold BixDef at h
  exact bix_sin_le W.hη0 (not_lt.1 h)

/-- Two consecutive sites of a window are never both indefinite. -/
theorem bix_not_consecutive (W : BixWin u θ A s η k₀ k₁) {j : ℕ} (h0 : k₀ ≤ j) (h1 : j < k₁) :
    BixDef θ η j ∨ BixDef θ η (j + 1) := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨d1, d2⟩ := W.hd j h0 h1
  exact (bix_pair W.hη0 d1 d2).2 ⟨bix_not_def_range W hc.1, bix_not_def_range W hc.2⟩

theorem bix_prod_aux (ε ε' s a b : ℝ) (hε : ε * ε = 1) (hε' : ε' * ε' = 1) (hs : s * s = 1)
    (z : 0 < ε * s * a) (z' : 0 < ε' * s * b) : (ε = ε' → 0 < a * b) ∧ (ε = -ε' → a * b < 0) := by
  have h : (ε * ε') * ((ε * s * a) * (ε' * s * b)) = a * b := by
    have : (ε * ε') * ((ε * s * a) * (ε' * s * b)) = (ε * ε) * (ε' * ε') * (s * s) * (a * b) := by ring
    rw [this, hε, hε', hs]; ring
  have hp := mul_pos z z'
  constructor
  · intro e; subst e; rw [← h, hε]; linarith
  · intro e
    have : ε * ε' = -1 := by rw [e]; nlinarith
    rw [← h, this]; linarith

theorem bix_sq_s (hs : s = 1 ∨ s = -1) : s * s = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num

/-- Signs at two definite sites whose integer parts agree, resp. differ by one. -/
theorem bix_prod_signs (W : BixWin u θ A s η k₀ k₁) {i j : ℕ} (hi0 : k₀ ≤ i) (hi1 : i ≤ k₁) (hj0 : k₀ ≤ j)
    (hj1 : j ≤ k₁) (hi : BixDef θ η i) (hj : BixDef θ η j) :
    (bixN (θ i) = bixN (θ j) → 0 < u i * u j) ∧ (bixN (θ i) = bixN (θ j) + 1 → u i * u j < 0) := by
  have := bix_prod_aux ((-1 : ℝ) ^ (bixN (θ i))) ((-1 : ℝ) ^ (bixN (θ j))) s (u i) (u j)
    (bix_neg_one_zpow_sq _) (bix_neg_one_zpow_sq _) (bix_sq_s W.hs) (W.sign_pos hi0 hi1 hi) (W.sign_pos hj0 hj1 hj)
  refine ⟨fun h => this.1 (by rw [h]), fun h => this.2 ?_⟩
  rw [h, zpow_add_one₀ (by norm_num)]; ring

/-- One bond between two definite sites contributes the drop of `bixN`. -/
theorem bix_step1 (W : BixWin u θ A s η k₀ k₁) {j : ℕ} (h0 : k₀ ≤ j) (h1 : j < k₁) (hj : BixDef θ η j)
    (hj' : BixDef θ η (j + 1)) : (bix_c u j : ℤ) = bixN (θ j) - bixN (θ (j + 1)) := by
  obtain ⟨d1, d2⟩ := W.hd j h0 h1
  have hfl := (bix_pair W.hη0 d1 d2).1
  have z1 := W.sign_pos h0 h1.le hj
  have hs := bix_prod_signs W h0 h1.le (j := j + 1) (by omega) h1 hj hj'
  have hne : u j ≠ 0 := by
    intro h; rw [h] at z1; simp at z1
  unfold bix_c
  rcases hfl with h | h
  · have : 0 < u j * u (j + 1) := hs.1 (by omega)
    simp [hne, this.not_gt, h]
  · have : u j * u (j + 1) < 0 := hs.2 (by omega)
    simp [hne, this, h]

theorem bix_sign3 (a b c : ℝ) (ha : a ≠ 0) (hac : a * c < 0) :
    ((if a * b < 0 then 1 else 0) + ((if b * c < 0 then 1 else 0) + (if b = 0 then 1 else 0)) : ℕ) = 1 := by
  rcases lt_trichotomy b 0 with hb | hb | hb
  · rcases lt_or_gt_of_ne ha with ha' | ha'
    · have : 0 < c := by nlinarith
      have h1 : ¬ a * b < 0 := by nlinarith
      have h2 : b * c < 0 := by nlinarith
      simp [h1, h2, hb.ne]
    · have : c < 0 := by nlinarith
      have h1 : a * b < 0 := by nlinarith
      have h2 : ¬ b * c < 0 := by nlinarith
      simp [h1, h2, hb.ne]
  · subst hb; simp
  · rcases lt_or_gt_of_ne ha with ha' | ha'
    · have : 0 < c := by nlinarith
      have h1 : a * b < 0 := by nlinarith
      have h2 : ¬ b * c < 0 := by nlinarith
      simp [h1, h2, hb.ne']
    · have : c < 0 := by nlinarith
      have h1 : ¬ a * b < 0 := by nlinarith
      have h2 : b * c < 0 := by nlinarith
      simp [h1, h2, hb.ne']

/-- Two bonds around an indefinite site contribute exactly the drop of `bixN`. -/
theorem bix_step2 (W : BixWin u θ A s η k₀ k₁) {j : ℕ} (h0 : k₀ ≤ j) (h2 : j + 1 < k₁) (hj : BixDef θ η j)
    (hm : ¬ BixDef θ η (j + 1)) (hj' : BixDef θ η (j + 2)) :
    (bix_c u j : ℤ) + bix_c u (j + 1) = bixN (θ j) - bixN (θ (j + 2)) := by
  obtain ⟨d1, d1'⟩ := W.hd j h0 (by omega)
  obtain ⟨d2, d2'⟩ := W.hd (j + 1) (by omega) h2
  have hn : bixN (θ j) - bixN (θ (j + 2)) = 1 :=
    bix_triple W.hη0 d1 d1' d2 d2' (bix_not_def_range W hm)
  rw [hn]
  have z1 := W.sign_pos h0 (by omega) hj
  have z2 := W.sign_pos (j := j + 2) (by omega) h2 hj'
  have hac : u j * u (j + 2) < 0 := (bix_prod_signs W h0 (by omega) (j := j + 2) (by omega) h2 hj hj').2 (by omega)
  have hne : u j ≠ 0 := by intro h; rw [h] at z1; simp at z1
  have := bix_sign3 (u j) (u (j + 1)) (u (j + 2)) hne hac
  unfold bix_c
  have hj1 : 0 < j + 1 := by omega
  simp only [hne, and_false, ite_false, add_zero, hj1, true_and]
  exact_mod_cast this

/-- **Sign changes equal the drop of `⌊θ/π + 1/2⌋`.**  For definite sites `k ≤ k'` of the window, the number of nodes in the
bonds `k, …, k'-1` is `⌊θ_k/π + 1/2⌋ - ⌊θ_{k'}/π + 1/2⌋`. -/
theorem bix_count (W : BixWin u θ A s η k₀ k₁) :
    ∀ d k : ℕ, k₀ ≤ k → k + d ≤ k₁ → BixDef θ η k → BixDef θ η (k + d) →
      ((∑ j ∈ Ico k (k + d), bix_c u j : ℕ) : ℤ) = bixN (θ k) - bixN (θ (k + d)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro k h0 h1 hk hkd
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · have hcase : BixDef θ η (k + d - 1) ∨ (d ≥ 2 ∧ ¬ BixDef θ η (k + d - 1)) := by
        by_cases hD : BixDef θ η (k + d - 1)
        · exact Or.inl hD
        · refine Or.inr ⟨?_, hD⟩
          by_contra hlt
          have : d = 1 := by omega
          subst this
          exact hD (by simpa using hk)
      rcases hcase with hD | ⟨hd2, hD⟩
      · have ih' := ih (d - 1) (by omega) k h0 (by omega) hk (by
          have : k + (d - 1) = k + d - 1 := by omega
          rw [this]; exact hD)
        have e : k + d = (k + (d - 1)) + 1 := by omega
        have step := bix_step1 W (j := k + (d - 1)) (by omega) (by omega) (by
          have : k + (d - 1) = k + d - 1 := by omega
          rw [this]; exact hD) (by rw [← e]; exact hkd)
        rw [e, sum_Ico_succ_top (by omega)]
        push_cast at ih' ⊢
        rw [ih' , step]
        have : k + (d - 1) + 1 = k + d := by omega
        rw [this] at *
        ring
      · have hD' : BixDef θ η (k + (d - 2)) := by
          have hb := bix_not_consecutive W (j := k + (d - 2)) (by omega) (by omega)
          have : k + (d - 2) + 1 = k + d - 1 := by omega
          rw [this] at hb
          exact hb.resolve_right hD
        have ih' := ih (d - 2) (by omega) k h0 (by omega) hk hD'
        have e : k + d = (k + (d - 2)) + 2 := by omega
        have hm : ¬ BixDef θ η (k + (d - 2) + 1) := by
          have : k + (d - 2) + 1 = k + d - 1 := by omega
          rw [this]; exact hD
        have step := bix_step2 W (j := k + (d - 2)) (by omega) (by omega) hD' hm (by rw [← e]; exact hkd)
        have hsum : ∑ j ∈ Ico k (k + d), bix_c u j =
            ∑ j ∈ Ico k (k + (d - 2)), bix_c u j + bix_c u (k + (d - 2)) + bix_c u (k + (d - 2) + 1) := by
          rw [e, sum_Ico_succ_top (by omega), sum_Ico_succ_top (by omega)]
        rw [hsum]
        push_cast at ih' ⊢
        have : k + (d - 2) + 2 = k + d := by omega
        rw [this] at step
        linarith

/-- **Composition with a right-end count.**  If the bonds `k_R, …, m-1` carry `⌊θ_{k_R}/π + 1/2⌋` nodes at a definite site
`k_R ≤ k₁`, then the bonds `k, …, m-1` carry `⌊θ_k/π + 1/2⌋` nodes at every definite site `k ≤ k_R` of the window. -/
theorem bix_count_right (W : BixWin u θ A s η k₀ k₁) {k kR m : ℕ} (hk0 : k₀ ≤ k) (hkR : k ≤ kR) (hR1 : kR ≤ k₁)
    (hRm : kR ≤ m) (hk : BixDef θ η k) (hR : BixDef θ η kR)
    (hcnt : ((∑ j ∈ Ico kR m, bix_c u j : ℕ) : ℤ) = bixN (θ kR)) :
    ((∑ j ∈ Ico k m, bix_c u j : ℕ) : ℤ) = bixN (θ k) := by
  have h := bix_count W (kR - k) k hk0 (by omega) hk (by rw [Nat.add_sub_cancel' hkR]; exact hR)
  rw [Nat.add_sub_cancel' hkR] at h
  rw [← sum_Ico_consecutive _ hkR hRm]
  push_cast at h hcnt ⊢
  linarith

/-- **Index from the left.**  If the whole sequence `u_0, …, u_m` has `T` nodes (`∑_{j<m} bix_c u j = T`, e.g.
`cho_hahn_nodes`), and the right-end count of `bix_count_right` holds, then the bonds `0, …, k-1` carry
`T - ⌊θ_k/π + 1/2⌋` nodes at every definite site `k ≤ k_R`. -/
theorem bix_count_left (W : BixWin u θ A s η k₀ k₁) {k kR m T : ℕ} (hk0 : k₀ ≤ k) (hkR : k ≤ kR) (hR1 : kR ≤ k₁)
    (hRm : kR ≤ m) (hk : BixDef θ η k) (hR : BixDef θ η kR)
    (hcnt : ((∑ j ∈ Ico kR m, bix_c u j : ℕ) : ℤ) = bixN (θ kR)) (hT : cho_nodal u m = T) :
    ((∑ j ∈ range k, bix_c u j : ℕ) : ℤ) = (T : ℤ) - bixN (θ k) := by
  have h := bix_count_right W hk0 hkR hR1 hRm hk hR hcnt
  rw [bix_nodal_eq_sum] at hT
  have hs := sum_range_add_sum_Ico (bix_c u) (show k ≤ m by omega)
  rw [hT] at hs
  push_cast at h hs ⊢
  have : ((∑ j ∈ range k, bix_c u j : ℕ) : ℤ) + ((∑ j ∈ Ico k m, bix_c u j : ℕ) : ℤ) = (T : ℤ) := by exact_mod_cast hs
  push_cast at this
  linarith

end Count

end FormalResearch.Special

/-- info: 'FormalResearch.Special.bix_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bix_count

/-- info: 'FormalResearch.Special.bix_count_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bix_count_right

/-- info: 'FormalResearch.Special.bix_count_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bix_count_left