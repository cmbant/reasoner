module

public import FormalResearch.Special.DiscreteLgSmooth
public import FormalResearch.Special.DiscreteAiryLimitHahn

/-!
# Bulk Liouville-Green layer for the Hahn / Racah chains

Instance of `dlg_bulk_smooth` for the closed-form Hahn/Racah coefficients `hrAk`, `hrCk` of `DiscreteAiryLimitHahn` (lattice `q_k = (k + 1/2) δ³`, `h = δ³`).
The input is the `O(h²)` closeness of the closed forms to the smooth data `A = hrA1`, `u = hrU`, obtained by applying `hr_perturb` *site by site* (with `q_* = q_k`,
`r = δ³`), so that the window `[c, d]` is arbitrary (`0 < c < d`; no `3d ≤ 5c` restriction), together with the oscillatory regularity hypothesis `hreg` (`1 - Pq² > 0`, `1 - Qq² > 0`, `|u(q)| < 1`
on an open neighbourhood of the window).  Conclusion: every exact solution of the Hahn/Racah rows on a lattice window of macroscopic length `≤ L` inside `[c, d]`
is `R w(q_k) [cos(Θ(q_k)/δ³ - φ₀) + O(δ³)]`, `R ≍ |Y_m| + |Y_{m+1}|`.

**Claim class: proved.**  **Not formalised here:** the Hahn/Racah chain data needed to feed the *matching* `dlg_airy_match` (chart relations at the sites near a turn) -- that
is the Langer-chart link to `DaiFull` and `hahn_chain_kappa`; the value of `κ`.
-/

@[expose] public section

open Set FormalResearch.DiscreteAiry
open scoped Real

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

lemma dlgh_hrE_anti {P Q : ℝ} (a b : ℝ) {c q : ℝ} (hc : 0 < c) (hcq : c ≤ q) :
    hrE P Q a b q ≤ hrE P Q a b c := by
  unfold hrE
  have hq : 0 < q := hc.trans_le hcq
  have hcq2 : c ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hc.le hcq 2
  have hX : 0 ≤ 2 * (a ^ 2 + b ^ 2 + 1 / 3) := by positivity
  have hY : 0 ≤ 4 * |a * b| := by positivity
  have t1 : 2 * (a ^ 2 + b ^ 2 + 1 / 3) / q ^ 2 ≤ 2 * (a ^ 2 + b ^ 2 + 1 / 3) / c ^ 2 :=
    div_le_div_of_nonneg_left hX (by positivity) hcq2
  have t2 : 4 * |a * b| / q ^ 2 ≤ 4 * |a * b| / c ^ 2 := div_le_div_of_nonneg_left hY (by positivity) hcq2
  exact max_le_max t1 (by linarith)

/-- **Closeness of the closed forms to the smooth data on an arbitrary window `[c, d]`**, by applying `hr_perturb` at each site (`q_* = q_k`, `r = δ³`):
`|a_k - A(q_k - h/2)| ≤ E h²`, `|c_k - 2 A(q_k) u(q_k)| ≤ E h²` with `E = hrE(c)` independent of the window length. -/
theorem dlgh_close {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x : ℝ) (hτ : τ ^ 2 = 1) {c0 d0 c d δ : ℝ} {J N : ℤ}
    (hc0 : 0 < c0) (hc0c : c0 < c)
    (hreg : ∀ q ∈ Icc c0 d0, 0 < 1 - P * q ^ 2 ∧ 0 < 1 - Q * q ^ 2) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδM : δ ≤ 3 * c / (4 * hrM a b)) (hδc : δ ^ 3 ≤ c - c0) (hδd : δ ^ 3 ≤ d0 - d) (hδq : δ ^ 3 ≤ c / 4)
    (hwin : ∀ k ∈ Finset.Icc J (N + 1), dalQ (δ ^ 3 / 2) δ k ∈ Icc c d) :
    (∀ k ∈ Finset.Icc (J + 1) (N + 1),
      |hrAk P Q a b (δ ^ 3) k - hrA1 P Q (dalQ (δ ^ 3 / 2) δ k - δ ^ 3 / 2)| ≤ hrE P Q a b c * δ ^ 6) ∧
    (∀ k ∈ Finset.Icc (J + 1) N,
      |hrCk P Q τ x a b (δ ^ 3) k - 2 * hrA1 P Q (dalQ (δ ^ 3 / 2) δ k) * hrU P Q τ x (dalQ (δ ^ 3 / 2) δ k)| ≤
        hrE P Q a b c * δ ^ 6) := by
  have hc : 0 < c := hc0.trans hc0c
  have hM1 : 1 ≤ hrM a b := le_max_left _ _
  have hh3 : 0 < δ ^ 3 := by positivity
  have e : ∀ j : ℤ, dalQ (δ ^ 3 / 2) δ (j + 1) = dalQ (δ ^ 3 / 2) δ j + δ ^ 3 := fun j => by unfold dalQ; push_cast; ring
  -- the common hypotheses of `hr_perturb` at the site `k`
  have key : ∀ k : ℤ, dalQ (δ ^ 3 / 2) δ k ∈ Icc c d → ∀ N' : ℤ, (N' = k - 1 ∨ N' = k) →
      (∀ j ∈ Finset.Icc (k - 1) (N' + 1), dalQ (δ ^ 3 / 2) δ j ∈ Icc c d) →
      (∀ k' ∈ Finset.Icc (k - 1 + 1) (N' + 1),
        |hrAk P Q a b (δ ^ 3) k' - hrA1 P Q (dalQ (δ ^ 3 / 2) δ k' - δ ^ 3 / 2)| ≤ hrE P Q a b c * δ ^ 6) ∧
      (∀ k' ∈ Finset.Icc (k - 1 + 1) N',
        |hrCk P Q τ x a b (δ ^ 3) k' - 2 * hrA1 P Q (dalQ (δ ^ 3 / 2) δ k') * hrU P Q τ x (dalQ (δ ^ 3 / 2) δ k')| ≤
          hrE P Q a b c * δ ^ 6) := by
    intro k hk N' hN' hw
    have hqk : c ≤ dalQ (δ ^ 3 / 2) δ k := hk.1
    have hqk' := hk.2
    have hqs : 0 < dalQ (δ ^ 3 / 2) δ k := hc.trans_le hqk
    have hdom : ∀ q ∈ Icc (dalQ (δ ^ 3 / 2) δ k - δ ^ 3) (dalQ (δ ^ 3 / 2) δ k + δ ^ 3),
        0 < 1 - P * q ^ 2 ∧ 0 < 1 - Q * q ^ 2 := fun q hq =>
      hreg q ⟨by linarith [hq.1], by linarith [hq.2]⟩
    have hwin' : ∀ j ∈ Finset.Icc (k - 1) (N' + 1), dalQ (δ ^ 3 / 2) δ j ∈
        Icc (dalQ (δ ^ 3 / 2) δ k - δ ^ 3) (dalQ (δ ^ 3 / 2) δ k + δ ^ 3) := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      have hjk : j = k - 1 ∨ j = k ∨ j = k + 1 := by omega
      have e1 : dalQ (δ ^ 3 / 2) δ k = dalQ (δ ^ 3 / 2) δ (k - 1) + δ ^ 3 := by
        have := e (k - 1); rw [show k - 1 + 1 = k by ring] at this; exact this
      have e2 : dalQ (δ ^ 3 / 2) δ (k + 1) = dalQ (δ ^ 3 / 2) δ k + δ ^ 3 := e k
      rcases hjk with h | h | h <;> subst h <;> constructor <;> linarith
    obtain ⟨hpa, hpc⟩ := hr_perturb hP hQ a b τ x _ hqs hτ (r := δ ^ 3) (r0 := δ ^ 3) (δ := δ) (J := k - 1) (N := N')
      (by linarith) le_rfl hdom hδ hδ1
      (hδM.trans (by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_le_mul_of_nonneg_right hqk (by positivity : (0 : ℝ) ≤ 3 * (4 * hrM a b))
        nlinarith)) hwin'
    have hE := dlgh_hrE_anti (P := P) (Q := Q) a b hc hqk
    exact ⟨fun k' hk' => (hpa k' hk').trans (mul_le_mul_of_nonneg_right hE (by positivity)),
      fun k' hk' => (hpc k' hk').trans (mul_le_mul_of_nonneg_right hE (by positivity))⟩
  constructor
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have hk0 := hwin k (by rw [Finset.mem_Icc]; omega)
    have := (key k hk0 (k - 1) (Or.inl rfl) (fun j hj => hwin j (by rw [Finset.mem_Icc] at hj ⊢; omega))).1
      k (by rw [Finset.mem_Icc]; omega)
    exact this
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have hk0 := hwin k (by rw [Finset.mem_Icc]; omega)
    exact (key k hk0 k (Or.inr rfl) (fun j hj => hwin j (by rw [Finset.mem_Icc] at hj ⊢; omega))).2 k
      (by rw [Finset.mem_Icc]; omega)

/-- **Bulk Liouville-Green theorem for the Hahn/Racah chains.**  See the module docstring.  `θ = arccos hrU`, `w = dlgsW hrA1 hrU`,
`Θ = dlgsPhase hrU c₁` with `c₁ = (c₀ + c)/2`. -/
theorem dlg_bulk_hahn {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x : ℝ) (hτ : τ ^ 2 = 1) {c0 d0 c d : ℝ}
    (hc0 : 0 < c0) (hc0c : c0 < c) (hcd : c < d) (hdd0 : d < d0)
    (hreg : ∀ q ∈ Icc c0 d0, 0 < 1 - P * q ^ 2 ∧ 0 < 1 - Q * q ^ 2 ∧ |hrU P Q τ x q| < 1) :
    ∃ δ0 C : ℝ, 0 < δ0 ∧ 0 < C ∧
      ∀ (δ : ℝ) (Y : ℤ → ℝ) (J N m : ℤ), 0 < δ → δ ≤ δ0 → J ≤ m → m ≤ N →
        (∀ k ∈ Finset.Icc J (N + 1), dlgQ (δ ^ 3 / 2) (δ ^ 3) k ∈ Icc c d) →
        (∀ k ∈ Finset.Icc (J + 1) N, jac (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) Y k = 0) →
        ∃ R φ0 : ℝ, 0 ≤ R ∧
          (∀ k ∈ Finset.Icc J (N + 1), |Y k - R * dlgsW (hrA1 P Q) (hrU P Q τ x) (dlgQ (δ ^ 3 / 2) (δ ^ 3) k) *
              Real.cos (dlgP (dlgsPhase (hrU P Q τ x) ((c0 + c) / 2)) (δ ^ 3 / 2) (δ ^ 3) k - φ0)| ≤
            C * δ ^ 3 * R * dlgsW (hrA1 P Q) (hrU P Q τ x) (dlgQ (δ ^ 3 / 2) (δ ^ 3) k)) ∧
          R ≤ C * (|Y m| + |Y (m + 1)|) ∧ |Y m| + |Y (m + 1)| ≤ C * R := by
  have hreg' : ∀ q ∈ Ioo c0 d0, 0 < (1 - P * q ^ 2) * (1 - Q * q ^ 2) := fun q hq =>
    mul_pos (hreg q (Ioo_subset_Icc_self hq)).1 (hreg q (Ioo_subset_Icc_self hq)).2.1
  have hA : ContDiffOn ℝ 2 (hrA1 P Q) (Ioo c0 d0) := fun q hq =>
    (hrA_contDiffAt 2 (hreg' q hq)).contDiffWithinAt
  have hu := dlgh_u_diff τ x hreg'
  have hsub : Icc ((c0 + c) / 2) ((d + d0) / 2) ⊆ Ioo c0 d0 := fun q hq => ⟨by linarith [hq.1], by linarith [hq.2]⟩
  obtain ⟨h0, C, hh0, hh01, hC, H⟩ := dlg_bulk_smooth (isOpen_Ioo (a := c0) (b := d0))
    (c := (c0 + c) / 2) (d := (d + d0) / 2) (by linarith) hsub hA hu
    (fun q hq => hrA_pos (hreg' q hq)) (fun q hq => (hreg q (Ioo_subset_Icc_self hq)).2.2)
    (hrE P Q a b c) (d - c) (hrE_nonneg P Q a b c) (by linarith)
  have hM1 : 1 ≤ hrM a b := le_max_left _ _
  have hc : 0 < c := hc0.trans hc0c
  have hρ : 0 < min (min (min 1 (3 * c / (4 * hrM a b))) (min (c - c0) (d0 - d))) (min (c / 4) h0) :=
    lt_min (lt_min (lt_min one_pos (by positivity)) (lt_min (by linarith) (by linarith))) (lt_min (by positivity) hh0)
  refine ⟨_, C, hρ, hC, ?_⟩
  intro δ Y J N m hδ hδ0 hJm hmN hwin hY
  have hδ1 : δ ≤ 1 := by
    refine hδ0.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hδM : δ ≤ 3 * c / (4 * hrM a b) :=
    hδ0.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hδc' : δ ≤ c - c0 := hδ0.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδd' : δ ≤ d0 - d := hδ0.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hδq' : δ ≤ c / 4 := hδ0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδh : δ ≤ h0 := hδ0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h3δ : δ ^ 3 ≤ δ := by
    have h1 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
    calc δ ^ 3 = δ * δ ^ 2 := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left h1 hδ.le
      _ = δ := mul_one _
  obtain ⟨hpa, hpc⟩ := dlgh_close hP hQ a b τ x hτ (c0 := c0) (d0 := d0) (c := c) (d := d) (J := J) (N := N) hc0 hc0c
    (fun q hq => ⟨(hreg q hq).1, (hreg q hq).2.1⟩) hδ hδ1 hδM (h3δ.trans hδc') (h3δ.trans hδd') (h3δ.trans hδq') hwin
  have e6 : (δ ^ 3) ^ 2 = δ ^ 6 := by ring
  have hlen : ((N - J : ℤ) : ℝ) * δ ^ 3 ≤ d - c := by
    have h1 := hwin J (by rw [Finset.mem_Icc]; omega)
    have h2 := hwin (N + 1) (by rw [Finset.mem_Icc]; omega)
    have e : dalQ (δ ^ 3 / 2) δ (N + 1) = dalQ (δ ^ 3 / 2) δ J + ((N + 1 - J : ℤ) : ℝ) * δ ^ 3 := by
      unfold dalQ; push_cast; ring
    have h3 : ((N + 1 - J : ℤ) : ℝ) * δ ^ 3 ≤ d - c := by
      have : dalQ (δ ^ 3 / 2) δ (N + 1) ≤ d := h2.2
      have : c ≤ dalQ (δ ^ 3 / 2) δ J := h1.1
      linarith
    have h4 : ((N - J : ℤ) : ℝ) = ((N + 1 - J : ℤ) : ℝ) - 1 := by push_cast; ring
    rw [h4]; nlinarith [pow_pos hδ 3]
  refine H (δ ^ 3 / 2) (δ ^ 3) (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) Y J N m (by positivity)
    (h3δ.trans hδh) hJm hmN hlen (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_) hY
  · have := hwin k hk
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · rw [e6]; exact hpa k hk
  · rw [e6]; exact hpc k hk

/-- info: 'FormalResearch.Special.dlgh_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dlgh_close

/-- info: 'FormalResearch.Special.dlg_bulk_hahn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dlg_bulk_hahn

/-- The window hypotheses of the smooth LG theorems for the Hahn/Racah chains: sites in the smooth domain, window length, and the two closeness statements in the
`E h²` form (`h = δ³`). -/
lemma dlgh_inputs {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x : ℝ) (hτ : τ ^ 2 = 1) {c0 d0 c d δ : ℝ} {J N : ℤ}
    (hJN : J ≤ N) (hc0 : 0 < c0) (hc0c : c0 < c) (hdd0 : d < d0)
    (hreg : ∀ q ∈ Icc c0 d0, 0 < 1 - P * q ^ 2 ∧ 0 < 1 - Q * q ^ 2) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδM : δ ≤ 3 * c / (4 * hrM a b)) (hδc : δ ≤ c - c0) (hδd : δ ≤ d0 - d) (hδq : δ ≤ c / 4)
    (hwin : ∀ k ∈ Finset.Icc J (N + 1), dlgQ (δ ^ 3 / 2) (δ ^ 3) k ∈ Icc c d) :
    (∀ k ∈ Finset.Icc J (N + 1), dlgQ (δ ^ 3 / 2) (δ ^ 3) k ∈ Ioo ((c0 + c) / 2) ((d + d0) / 2)) ∧
      ((N - J : ℤ) : ℝ) * δ ^ 3 ≤ d - c ∧
      (∀ k ∈ Finset.Icc (J + 1) (N + 1),
        |hrAk P Q a b (δ ^ 3) k - hrA1 P Q (dlgQ (δ ^ 3 / 2) (δ ^ 3) k - δ ^ 3 / 2)| ≤ hrE P Q a b c * (δ ^ 3) ^ 2) ∧
      (∀ k ∈ Finset.Icc (J + 1) N,
        |hrCk P Q τ x a b (δ ^ 3) k - 2 * hrA1 P Q (dlgQ (δ ^ 3 / 2) (δ ^ 3) k) * hrU P Q τ x (dlgQ (δ ^ 3 / 2) (δ ^ 3) k)| ≤
          hrE P Q a b c * (δ ^ 3) ^ 2) := by
  have h3δ : δ ^ 3 ≤ δ := by
    have h1 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
    calc δ ^ 3 = δ * δ ^ 2 := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left h1 hδ.le
      _ = δ := mul_one _
  obtain ⟨hpa, hpc⟩ := dlgh_close hP hQ a b τ x hτ (c0 := c0) (d0 := d0) (c := c) (d := d) (J := J) (N := N) hc0 hc0c
    hreg hδ hδ1 hδM (h3δ.trans hδc) (h3δ.trans hδd) (h3δ.trans hδq) hwin
  have e6 : (δ ^ 3) ^ 2 = δ ^ 6 := by ring
  refine ⟨fun k hk => ?_, ?_, fun k hk => ?_, fun k hk => ?_⟩
  · have := hwin k hk
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · have h1 := hwin J (by rw [Finset.mem_Icc]; omega)
    have h2 := hwin (N + 1) (by rw [Finset.mem_Icc]; omega)
    have e : dlgQ (δ ^ 3 / 2) (δ ^ 3) (N + 1) = dlgQ (δ ^ 3 / 2) (δ ^ 3) J + ((N + 1 - J : ℤ) : ℝ) * δ ^ 3 := by
      unfold dlgQ; push_cast; ring
    have h3 : ((N + 1 - J : ℤ) : ℝ) * δ ^ 3 ≤ d - c := by
      have : dlgQ (δ ^ 3 / 2) (δ ^ 3) (N + 1) ≤ d := h2.2
      have : c ≤ dlgQ (δ ^ 3 / 2) (δ ^ 3) J := h1.1
      linarith
    have h4 : ((N - J : ℤ) : ℝ) = ((N + 1 - J : ℤ) : ℝ) - 1 := by push_cast; ring
    rw [h4]; nlinarith [pow_pos hδ 3]
  · rw [e6]; exact hpa k hk
  · rw [e6]; exact hpc k hk

/-- **Airy matching for the Hahn/Racah chains**: `dlg_airy_match_smooth` for the closed-form coefficients on an arbitrary window `[c, d]`.  Given the
Airy-chart datum `DlgAiryAt` at two sites `m, m+1` of the window (`Θ = dlgsPhase hrU c₁`, `c₁ = (c₀ + c)/2`), every exact solution is
`Y_k = h^{1/6} π^{-1/2} w_k (κ cos χ_k + μ sin χ_k) + O(h^{1/6} h (|κ|+|μ|) w_k)`, `χ_k = Θ_k/h - Θ*/h + π/4`, `h = δ³`, on the whole window. -/
theorem dlg_airy_match_hahn {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x : ℝ) (hτ : τ ^ 2 = 1) {c0 d0 c d : ℝ}
    (hc0 : 0 < c0) (hc0c : c0 < c) (hcd : c < d) (hdd0 : d < d0)
    (hreg : ∀ q ∈ Icc c0 d0, 0 < 1 - P * q ^ 2 ∧ 0 < 1 - Q * q ^ 2 ∧ |hrU P Q τ x q| < 1) :
    ∃ δ0 C : ℝ, 0 < δ0 ∧ 0 < C ∧
      ∀ (δ : ℝ) (Y : ℤ → ℝ) (J N m : ℤ) (κ μ Ts Φmin gmin Ca : ℝ), 0 < Φmin → 0 < gmin → 0 ≤ Ca →
        0 < δ → δ ≤ δ0 → J ≤ m → m ≤ N →
        (∀ k ∈ Finset.Icc J (N + 1), dlgQ (δ ^ 3 / 2) (δ ^ 3) k ∈ Icc c d) →
        (∀ k ∈ Finset.Icc (J + 1) N, jac (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) Y k = 0) →
        DlgAiryAt κ μ Y (dlgsW (hrA1 P Q) (hrU P Q τ x)) (dlgsPhase (hrU P Q τ x) ((c0 + c) / 2)) (δ ^ 3 / 2) (δ ^ 3)
          Ts Φmin gmin Ca m →
        DlgAiryAt κ μ Y (dlgsW (hrA1 P Q) (hrU P Q τ x)) (dlgsPhase (hrU P Q τ x) ((c0 + c) / 2)) (δ ^ 3 / 2) (δ ^ 3)
          Ts Φmin gmin Ca (m + 1) →
        ∀ k ∈ Finset.Icc J (N + 1),
          |Y k - (δ ^ 3) ^ (1 / 6 : ℝ) * (1 / √π) * dlgsW (hrA1 P Q) (hrU P Q τ x) (dlgQ (δ ^ 3 / 2) (δ ^ 3) k) *
              (κ * Real.cos (dlgP (dlgsPhase (hrU P Q τ x) ((c0 + c) / 2)) (δ ^ 3 / 2) (δ ^ 3) k - Ts / δ ^ 3 + π / 4) +
                μ * Real.sin (dlgP (dlgsPhase (hrU P Q τ x) ((c0 + c) / 2)) (δ ^ 3 / 2) (δ ^ 3) k - Ts / δ ^ 3 + π / 4))| ≤
            C * (2 + (1 / (12 * Φmin) + Ca / gmin)) * ((|κ| + |μ|) * ((δ ^ 3) ^ (1 / 6 : ℝ) * δ ^ 3)) *
              dlgsW (hrA1 P Q) (hrU P Q τ x) (dlgQ (δ ^ 3 / 2) (δ ^ 3) k) := by
  have hreg' : ∀ q ∈ Ioo c0 d0, 0 < (1 - P * q ^ 2) * (1 - Q * q ^ 2) := fun q hq =>
    mul_pos (hreg q (Ioo_subset_Icc_self hq)).1 (hreg q (Ioo_subset_Icc_self hq)).2.1
  have hA : ContDiffOn ℝ 2 (hrA1 P Q) (Ioo c0 d0) := fun q hq =>
    (hrA_contDiffAt 2 (hreg' q hq)).contDiffWithinAt
  have hu := dlgh_u_diff τ x hreg'
  have hsub : Icc ((c0 + c) / 2) ((d + d0) / 2) ⊆ Ioo c0 d0 := fun q hq => ⟨by linarith [hq.1], by linarith [hq.2]⟩
  obtain ⟨h0, C, hh0, hh01, hC, H⟩ := dlg_airy_match_smooth (isOpen_Ioo (a := c0) (b := d0))
    (c := (c0 + c) / 2) (d := (d + d0) / 2) (by linarith) hsub hA hu
    (fun q hq => hrA_pos (hreg' q hq)) (fun q hq => (hreg q (Ioo_subset_Icc_self hq)).2.2)
    (hrE P Q a b c) (d - c) (hrE_nonneg P Q a b c) (by linarith)
  have hM1 : 1 ≤ hrM a b := le_max_left _ _
  have hc : 0 < c := hc0.trans hc0c
  have hρ : 0 < min (min (min 1 (3 * c / (4 * hrM a b))) (min (c - c0) (d0 - d))) (min (c / 4) h0) :=
    lt_min (lt_min (lt_min one_pos (by positivity)) (lt_min (by linarith) (by linarith))) (lt_min (by positivity) hh0)
  refine ⟨_, C, hρ, hC, ?_⟩
  intro δ Y J N m κ μ Ts Φmin gmin Ca hΦ hg hCa hδ hδ0 hJm hmN hwin hY S0 S1
  have hδ1 : δ ≤ 1 := hδ0.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hδM : δ ≤ 3 * c / (4 * hrM a b) :=
    hδ0.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hδc' : δ ≤ c - c0 := hδ0.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδd' : δ ≤ d0 - d := hδ0.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hδq' : δ ≤ c / 4 := hδ0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδh : δ ≤ h0 := hδ0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h3δ : δ ^ 3 ≤ δ := by
    have h1 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
    calc δ ^ 3 = δ * δ ^ 2 := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left h1 hδ.le
      _ = δ := mul_one _
  obtain ⟨hU, hlen, hpa, hpc⟩ := dlgh_inputs hP hQ a b τ x hτ (by omega) hc0 hc0c hdd0
    (fun q hq => ⟨(hreg q hq).1, (hreg q hq).2.1⟩) hδ hδ1 hδM hδc' hδd' hδq' hwin
  exact H (δ ^ 3 / 2) (δ ^ 3) (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) Y J N m κ μ Ts Φmin gmin Ca hΦ hg hCa
    (by positivity) (h3δ.trans hδh) hJm hmN hlen hU hpa hpc hY S0 S1

/-- info: 'FormalResearch.Special.dlg_airy_match_hahn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dlg_airy_match_hahn

end FormalResearch.Special
