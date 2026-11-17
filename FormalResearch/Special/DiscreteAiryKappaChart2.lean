module

public import FormalResearch.Special.DiscreteAiryKappaChart

/-!
# The Airy window with the full chart data exported (plan K1, order-sharp `κ`)

`kc_turn` / `kc_hahn_full` (`DiscreteAiryKappaChart`) export `g ≤ g_max` and `X_k ≤ 1/4` for `k ≤ m + 1`.  The order-sharp estimates of
`|κ|` (`DiscreteAiryKappaOrder*`) also need the *lower* bound `g ≥ g_min > 0`, the lattice gaps `c₁ δ ≤ X_{k+1} - X_k ≤ c₂ δ` on the whole
window and `0 ≤ X_m ≤ c₂ δ` (all produced by the same proofs through `dao_lattice` and `dal_turn_data`, but not previously exported).  This
module reads them off `kc_turn_full` (`DiscreteAiryKappaChart`, which also carries the Lipschitz bound on `g` used by the Hermite chain) for `kc2_turn`, and
repeats the closed-form `3j` / `6j` reduction of `kc_hahn_full` for `kc2_hahn_full` (the constants `g_min, c₁, c₂` are independent of `δ`).

**Claim class: proved** (`kc2_turn` is a projection of `kc_turn_full`; `kc2_hahn_full` is the proof of `kc_hahn_full` with the extra conjuncts).
-/

@[expose] public section

open Finset FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **`discrete_airy_full` with the chart data**: the same statement as `discrete_airy_full` (`DiscreteAiryPhysTurn`) with, in
addition, a uniform bound `gmax` on the Langer amplitude on the window `[J, N+1]` and `X_k ≤ 1/4` for `k ≤ m+1` (the data of the
chart are not exported by `discrete_airy_full`, whose radius `r` is existential). -/
theorem kc2_turn {u A : ℝ → ℝ} {c0 : ℝ} (hu : ContDiffAt ℝ 3 u c0) (h1 : u c0 = 1)
    (h2 : 0 < deriv u c0) (hA : ContDiffAt ℝ 2 A c0) (hA0 : 0 < A c0) {r0 : ℝ} (hr0 : 0 < r0)
    (E : ℝ) (hE : 0 ≤ E) :
    ∃ (r δ0 C Cmu ξ0 gmax gmin c1 c2 : ℝ), 0 < r ∧ r ≤ r0 ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧
      0 < gmin ∧ gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧
      ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ0 → ∃ J m N : ℤ, J < N ∧ J ≤ m ∧ m ≤ N ∧
        (∀ k ∈ Finset.Icc J (N + 1), dalQ q₀ δ k ∈ Set.Icc (c0 - r) (c0 + r)) ∧
        c0 - r ≤ dalQ q₀ δ J ∧ dalQ q₀ δ J < c0 - r + δ ^ 3 ∧ c0 ≤ dalQ q₀ δ m ∧
        dalQ q₀ δ m < c0 + δ ^ 3 ∧ c0 + r / 4 ≤ dalQ q₀ δ N ∧ dalQ q₀ δ (N + 1) ≤ c0 + r / 2 ∧
        (∀ k ∈ Finset.Icc J (N + 1), |langerAmp u A c0 (dalQ q₀ δ k)| ≤ gmax) ∧
        (∀ k ∈ Finset.Icc J (m + 1), turnX u c0 q₀ δ k ≤ 1 / 4) ∧
        (∀ k ∈ Finset.Icc J (N + 1), gmin ≤ langerAmp u A c0 (dalQ q₀ δ k)) ∧
        (∀ k ∈ Finset.Icc J N, c1 * δ ≤ turnX u c0 q₀ δ (k + 1) - turnX u c0 q₀ δ k ∧
          turnX u c0 q₀ δ (k + 1) - turnX u c0 q₀ δ k ≤ c2 * δ) ∧
        (0 ≤ turnX u c0 q₀ δ m ∧ turnX u c0 q₀ δ m ≤ c2 * δ) ∧
        c1 * (r / 4) / δ ^ 2 ≤ turnX u c0 q₀ δ N ∧
        ∀ a c : ℤ → ℝ,
          (∀ k ∈ Finset.Icc (J + 1) (N + 1), |a k - A (dalQ q₀ δ k - δ ^ 3 / 2)| ≤ E * δ ^ 6) →
          (∀ k ∈ Finset.Icc (J + 1) N, |c k - 2 * A (dalQ q₀ δ k) * u (dalQ q₀ δ k)| ≤ E * δ ^ 6) →
          DaiFull a c (turnX u c0 q₀ δ) (fun k => langerAmp u A c0 (dalQ q₀ δ k)) J m N δ C Cmu ξ0 := by
  obtain ⟨r, δ0, C, Cmu, ξ0, gmax, gmin, c1, c2, Lg, hr, hrr0, hδ0, hδ01, hC, hCmu, hξ0, hgmax, hgmin, hgg, hc1, hc12, -, H⟩ :=
    kc_turn_full hu h1 h2 hA hA0 hr0 E hE
  refine ⟨r, δ0, C, Cmu, ξ0, gmax, gmin, c1, c2, hr, hrr0, hδ0, hδ01, hC, hCmu, hξ0, hgmax, hgmin, hgg, hc1, hc12,
    fun δ q₀ hδ hδδ0 => ?_⟩
  obtain ⟨J, m, N, hJN, hJm, hmN, hwin, h3, h4, h5, h6, h7, h8, hg, hX, hgl, hgap, hX0, hXN, -, -, Hc⟩ := H δ q₀ hδ hδδ0
  exact ⟨J, m, N, hJN, hJm, hmN, hwin, h3, h4, h5, h6, h7, h8, hg, hX, hgl, hgap, hX0, hXN, Hc⟩

/-- info: 'FormalResearch.Special.kc2_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kc2_turn

/-- **`discrete_airy_hahn_racah_full` with the chart data** (`g ≤ g_max` on the window, `X_k ≤ 1/4` for `k ≤ m+1`). -/
theorem kc2_hahn_full {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs)
    (hτ : τ ^ 2 = 1) (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    (hturn : Phi P Q τ x (qs ^ 2) = 0) :
    ∃ (r δ0 C Cmu ξ0 gmax gmin c1 c2 : ℝ), 0 < r ∧ r ≤ qs / 4 ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧
      0 < gmin ∧ gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∃ J m N : ℤ, 1 ≤ J ∧ J < N ∧ J ≤ m ∧ m ≤ N ∧
        (∀ k ∈ Finset.Icc J (N + 1), |((k : ℝ) + 1 / 2) * δ ^ 3 - qs| ≤ r) ∧
        qs - r ≤ ((J : ℝ) + 1 / 2) * δ ^ 3 ∧ ((J : ℝ) + 1 / 2) * δ ^ 3 < qs - r + δ ^ 3 ∧
        qs ≤ ((m : ℝ) + 1 / 2) * δ ^ 3 ∧ ((m : ℝ) + 1 / 2) * δ ^ 3 < qs + δ ^ 3 ∧
        qs + r / 4 ≤ ((N : ℝ) + 1 / 2) * δ ^ 3 ∧ ((N : ℝ) + 1 + 1 / 2) * δ ^ 3 ≤ qs + r / 2 ∧
        (∀ k ∈ Finset.Icc J (N + 1), |langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3 / 2) δ k)| ≤ gmax) ∧
        (∀ k ∈ Finset.Icc J (m + 1), turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ k ≤ 1 / 4) ∧
        (∀ k ∈ Finset.Icc J (N + 1), gmin ≤ langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3 / 2) δ k)) ∧
        (∀ k ∈ Finset.Icc J N, c1 * δ ≤ turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ (k + 1) - turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ k ∧
          turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ (k + 1) - turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ k ≤ c2 * δ) ∧
        (0 ≤ turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ m ∧ turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ m ≤ c2 * δ) ∧
        c1 * (r / 4) / δ ^ 2 ≤ turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ N ∧
        DaiFull (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ)
          (fun k => langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3 / 2) δ k)) J m N δ C Cmu ξ0 := by
  obtain ⟨r0, hr0, hr0q, hdom⟩ := hr_dom hqs hα hβ
  have hint : 0 < (1 - P * qs ^ 2) * (1 - Q * qs ^ 2) := mul_pos hα hβ
  obtain ⟨r, δ0', C, Cmu, ξ0, gmax, gmin, c1, c2, hr, hrr0, hδ0', hδ01, hC, hCmu, hξ0, hgmax, hgmin, hgg, hc1, hc12, H⟩ :=
    kc2_turn (hrU_contDiffAt τ x 3 hint) (hrU_turn hint hturn)
      (hrU_deriv_pos hqs hκ hα hβ hturn) (hrA_contDiffAt 2 hint) (hrA_pos hint) hr0 (hrE P Q a b qs)
      (hrE_nonneg P Q a b qs)
  have hM0 : 0 < hrM a b := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hδip : 0 < min 1 (min (3 * qs / (4 * hrM a b)) (qs / 2)) :=
    lt_min one_pos (lt_min (by positivity) (by positivity))
  refine ⟨r, min δ0' (min 1 (min (3 * qs / (4 * hrM a b)) (qs / 2))), C, Cmu, ξ0, gmax, gmin, c1, c2, hr,
    hrr0.trans hr0q, lt_min hδ0' hδip, (min_le_left _ _).trans hδ01, hC, hCmu, hξ0, hgmax, hgmin, hgg, hc1, hc12, ?_⟩
  intro δ hδ hδδ0
  have hδ1' : δ ≤ δ0' := hδδ0.trans (min_le_left _ _)
  have hδi' := hδδ0.trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := hδi'.trans (min_le_left _ _)
  have hδM : δ ≤ 3 * qs / (4 * hrM a b) := hδi'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδq : δ ≤ qs / 2 := hδi'.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h3δ : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2]
  obtain ⟨J, m, N, hJN, hJm, hmN, hwin, hqJ, hqJc, hqm1, hqm2, hqN, hqN1, hg, hXm, hgl, hgap, hX0m, hXN, Hc⟩ := H δ (δ ^ 3 / 2) hδ hδ1'
  have hr4 : r ≤ qs / 4 := hrr0.trans hr0q
  obtain ⟨hpa, hpc⟩ := hr_perturb hP hQ a b τ x qs hqs hτ hr4 hrr0 hdom hδ hδ1 hδM hwin
  have e2 : ∀ k : ℤ, dalQ (δ ^ 3 / 2) δ k = ((k : ℝ) + 1 / 2) * δ ^ 3 := fun k => by unfold dalQ; ring
  refine ⟨J, m, N, hr_J_pos hr4 hδ (h3δ.trans hδq) (by omega) hwin, hJN, hJm, hmN, fun k hk => ?_,
    by rw [← e2]; exact hqJ, by rw [← e2]; exact hqJc, by rw [← e2]; exact hqm1, by rw [← e2]; exact hqm2,
    by rw [← e2]; exact hqN, by have := hqN1; rw [show ((N : ℝ) + 1 + 1 / 2) * δ ^ 3 = dalQ (δ ^ 3 / 2) δ (N + 1) by
      unfold dalQ; push_cast; ring]; exact this, hg, hXm, hgl, hgap, hX0m, hXN, Hc _ _ hpa hpc⟩
  have h1 := hwin k hk
  rw [e2] at h1
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2]

/-- info: 'FormalResearch.Special.kc2_hahn_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kc2_hahn_full

end FormalResearch.Special
