module

public import FormalResearch.Special.DiscreteLgSmooth
public import FormalResearch.Special.DiscreteAiryLimitHahn

/-!
# Bulk Liouville-Green layer for the Hahn / Racah chains

Instance of `dlg_bulk_smooth` for the closed-form Hahn/Racah coefficients `hrAk`, `hrCk` of `DiscreteAiryLimitHahn` (lattice `q_k = (k + 1/2) δ³`, `h = δ³`).
The input is the `O(h²)` closeness of the closed forms to the smooth data `A = hrA1`, `u = hrU` (`hr_perturb`), valid on a window `[c, d]` with `3d ≤ 5c` (the
`r ≤ q_*/4` hypothesis of `hr_perturb` with `q_* = (c+d)/2`), together with the oscillatory regularity hypothesis `hreg` (`1 - Pq² > 0`, `1 - Qq² > 0`, `|u(q)| < 1`
on an open neighbourhood of the window).  Conclusion: every exact solution of the Hahn/Racah rows on a lattice window of macroscopic length `≤ L` inside `[c, d]`
is `R w(q_k) [cos(Θ(q_k)/δ³ - φ₀) + O(δ³)]`, `R ≍ |Y_m| + |Y_{m+1}|`.

**Claim class: proved.**  **Not formalised here:** the Hahn/Racah chain data needed to feed the *matching* `dlg_airy_match` (chart relations at the sites near a turn) -- that
is the Langer-chart link to `DaiFull` and `hahn_chain_kappa`; the value of `κ`.
-/

@[expose] public section

open Set FormalResearch.DiscreteAiry

namespace FormalResearch.Special

lemma dlgh_etilde_pos {P Q q : ℝ} (hint : 0 < (1 - P * q ^ 2) * (1 - Q * q ^ 2)) : 0 < Racah.P3.etilde P Q (q ^ 2) := by
  have := hrA_pos hint
  unfold hrA1 at this
  linarith

lemma dlgh_u_diff {P Q : ℝ} (τ x : ℝ) {U0 : Set ℝ}
    (hreg : ∀ q ∈ U0, 0 < (1 - P * q ^ 2) * (1 - Q * q ^ 2)) : ContDiffOn ℝ 2 (hrU P Q τ x) U0 := by
  intro q hq
  have hint := hreg q hq
  have hnum : ContDiffAt ℝ 2 (fun y : ℝ => τ * (x - Real.sqrt (P * Q) * y ^ 2)) q := by fun_prop
  exact (hnum.div (etilde_contDiffAt 2 hint) (dlgh_etilde_pos hint).ne').contDiffWithinAt

/-- **Bulk Liouville-Green theorem for the Hahn/Racah chains.**  See the module docstring. -/
theorem dlg_bulk_hahn {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x : ℝ) (hτ : τ ^ 2 = 1) {c0 d0 c d : ℝ}
    (hc0 : 0 < c0) (hc0c : c0 < c) (hcd : c < d) (hdd0 : d < d0) (hr : 3 * d ≤ 5 * c)
    (hreg : ∀ q ∈ Icc c0 d0, 0 < 1 - P * q ^ 2 ∧ 0 < 1 - Q * q ^ 2 ∧ |hrU P Q τ x q| < 1) (L : ℝ) (hL : 0 ≤ L) :
    ∃ (θ w Θ : ℝ → ℝ) (δ0 C : ℝ), 0 < δ0 ∧ 0 < C ∧ (∀ t ∈ Icc c d, Real.cos (θ t) = hrU P Q τ x t) ∧
      ∀ (δ : ℝ) (Y : ℤ → ℝ) (J N m : ℤ), 0 < δ → δ ≤ δ0 → J ≤ m → m ≤ N → ((N - J : ℤ) : ℝ) * δ ^ 3 ≤ L →
        (∀ k ∈ Finset.Icc J (N + 1), dlgQ (δ ^ 3 / 2) (δ ^ 3) k ∈ Icc c d) →
        (∀ k ∈ Finset.Icc (J + 1) N, jac (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) Y k = 0) →
        ∃ R φ0 : ℝ, 0 ≤ R ∧
          (∀ k ∈ Finset.Icc J (N + 1), |Y k - R * w (dlgQ (δ ^ 3 / 2) (δ ^ 3) k) *
              Real.cos (dlgP Θ (δ ^ 3 / 2) (δ ^ 3) k - φ0)| ≤ C * δ ^ 3 * R * w (dlgQ (δ ^ 3 / 2) (δ ^ 3) k)) ∧
          R ≤ C * (|Y m| + |Y (m + 1)|) ∧ |Y m| + |Y (m + 1)| ≤ C * R := by
  set qs : ℝ := (c + d) / 2 with hqs
  set r : ℝ := (d - c) / 2 with hr_
  have hqs0 : 0 < qs := by rw [hqs]; linarith
  have hreg' : ∀ q ∈ Ioo c0 d0, 0 < (1 - P * q ^ 2) * (1 - Q * q ^ 2) := fun q hq =>
    mul_pos (hreg q (Ioo_subset_Icc_self hq)).1 (hreg q (Ioo_subset_Icc_self hq)).2.1
  have hA : ContDiffOn ℝ 2 (hrA1 P Q) (Ioo c0 d0) := fun q hq =>
    (hrA_contDiffAt 2 (hreg' q hq)).contDiffWithinAt
  have hu := dlgh_u_diff τ x hreg'
  have hsub : Icc ((c0 + c) / 2) ((d + d0) / 2) ⊆ Ioo c0 d0 := fun q hq => ⟨by linarith [hq.1], by linarith [hq.2]⟩
  obtain ⟨θ, w, Θ, h0, C, hh0, hh01, hC, hcos, H⟩ := dlg_bulk_smooth (isOpen_Ioo (a := c0) (b := d0))
    (c := (c0 + c) / 2) (d := (d + d0) / 2) (by linarith) hsub hA hu
    (fun q hq => hrA_pos (hreg' q hq)) (fun q hq => (hreg q (Ioo_subset_Icc_self hq)).2.2)
    (hrE P Q a b qs) L (hrE_nonneg P Q a b qs) hL
  have hM1 : 1 ≤ hrM a b := le_max_left _ _
  have hMpos : 0 < 4 * hrM a b := by linarith
  refine ⟨θ, w, Θ, min (min 1 (3 * qs / (4 * hrM a b))) h0, C, lt_min (lt_min one_pos (by positivity)) hh0, hC,
    fun t ht => hcos t ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
  intro δ Y J N m hδ hδ0 hJm hmN hlen hwin hY
  have hδ1 : δ ≤ 1 := (hδ0.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hδM : δ ≤ 3 * qs / (4 * hrM a b) := (hδ0.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hδh : δ ≤ h0 := hδ0.trans (min_le_right _ _)
  have h3δ : δ ^ 3 ≤ δ := by
    have h1 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
    calc δ ^ 3 = δ * δ ^ 2 := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left h1 hδ.le
      _ = δ := mul_one _
  have hwin' : ∀ k ∈ Finset.Icc J (N + 1), dalQ (δ ^ 3 / 2) δ k ∈ Icc (qs - r) (qs + r) := by
    intro k hk
    have := hwin k hk
    have e : dalQ (δ ^ 3 / 2) δ k = dlgQ (δ ^ 3 / 2) (δ ^ 3) k := rfl
    rw [e]
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hdom : ∀ q ∈ Icc (qs - r) (qs + r), 0 < 1 - P * q ^ 2 ∧ 0 < 1 - Q * q ^ 2 := fun q hq => by
    have := hreg q ⟨by linarith [hq.1], by linarith [hq.2]⟩
    exact ⟨this.1, this.2.1⟩
  obtain ⟨hpa, hpc⟩ := hr_perturb hP hQ a b τ x qs hqs0 hτ (r := r) (r0 := r) (δ := δ) (J := J) (N := N)
    (by rw [hqs, hr_]; linarith) le_rfl hdom hδ hδ1 hδM hwin'
  have e6 : (δ ^ 3) ^ 2 = δ ^ 6 := by ring
  refine H (δ ^ 3 / 2) (δ ^ 3) (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) Y J N m (by positivity)
    (h3δ.trans hδh) hJm hmN hlen (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_) hY
  · have := hwin k hk
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · rw [e6]; exact hpa k hk
  · rw [e6]; exact hpc k hk

/-- info: 'FormalResearch.Special.dlg_bulk_hahn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dlg_bulk_hahn

end FormalResearch.Special
