module

public import FormalResearch.Special.DiscreteAirySecondFinal
public import FormalResearch.Special.DiscreteAirySecondQ1
public import FormalResearch.Special.DiscreteAiryOscLattice
public import FormalResearch.Special.DiscreteAiryLimitData
public import FormalResearch.Special.AiryRecessiveSums

/-!
# Second-order Airy parametrix, part 16: the simple-turn statement (Q5b)

`airy2_dai_full` (`DiscreteAirySecondFinal`) takes the lattice-window facts as hypotheses.  Here they are derived at a simple turn
`ζ(c₀) = 0`, `ζ' > 0`: on the window `[c₀ - r, c₀ + r]` inside the open set `U` of the data, for the shifted argument
`X̂_k = ζ(q_k)/δ² + δ⁴ q₁(q_k)/g(q_k)` (a perturbation of size `δ⁴ B_max` of `X_k = ζ(q_k)/δ²`):

* `a2t_window`: indices `J < m₀ ≤ N`, `q_J ∈ [c₀ - r, c₀ - r + δ³)`, `q_{m₀} ∈ [c₀, c₀ + 2δ³)`, `q_N ≥ c₀ + r/4`, `q_{N+1} ≤ c₀ + r/2`,
  gaps `(s₁/2) δ ≤ X̂_{k+1} - X̂_k ≤ (2 s₂ + s₁) δ`, `|X̂_k| ≤ M/δ²`, `0 ≤ X̂_{m₀} ≤ (2 s₂ + s₁) δ` (base site `m₀ ∈ {m, m+1}`: the
  first site with `X̂ ≥ 0`), `ξ₀/δ³ ≤ ξ(X̂_N)`.
* `airy2_turn_conclusion`: **the second-order bracket at a simple turn** for data `(ζ, A, A₂, g, q₁, c₂)` satisfying the
  amplitude relation and the `q₁`-residual equation on `U`: there are `δ₀, r`-independent constants `C, Q, C_μ, ξ₀` such that for
  `δ ≤ δ₀`, every `q₀` and all coefficients within `E δ⁹` of the exact second-order ones, `DaiFullR` holds with error rate `δ⁶ = h²`
  on the whole oscillatory side `[c₀ - r, c₀]` plus the bulk to `c₀ + r/4`.  The Casoratian constant `Q` does not depend on `E`.
* `airy2_turn_full`: the same with `q₁` **constructed** (`airy2_q1_exists`) on a ball, from `ζ ∈ C⁷`, `A, g ∈ C⁶`, `A₂, c₂ ∈ C⁴`.

**Claim class: proved.**  This is the abstract statement; the Hahn/Racah instances (coefficient closeness `E δ⁹`, i.e. `S4`) are not
formalised here.
-/

@[expose] public section

open Finset Metric FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- `ξ(a/δ²) = (2/3) (√a)³ / δ³` for `a > 0`. -/
lemma a2t_xi {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    2 / 3 * (√a) ^ 3 / δ ^ 3 = airyXi (a / δ ^ 2) := by
  rw [airyXi_eq_sqrt_pow, max_eq_left (by positivity), Real.sqrt_div ha.le, Real.sqrt_sq hδ.le]
  field_simp

/-- `δ⁴ B ≤ s δ / 4` and `δ⁶ B ≤ s'`-type estimates from `δ B ≤ s/4`. -/
lemma a2t_eps {δ Bm s : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 0 ≤ Bm) (h : δ * Bm ≤ s / 4) :
    δ ^ 4 * Bm ≤ s * δ / 4 := by
  have h3 : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le (by linarith)
  have : δ ^ 4 * Bm = δ * (δ ^ 3 * Bm) := by ring
  have h4 : δ ^ 3 * Bm ≤ δ * Bm := by
    have h33 : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2]
    exact mul_le_mul_of_nonneg_right h33 hB
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left (h4.trans h) hδ.le]

/-- The perturbation of `X` by `δ⁴ B`, in terms of `dalX`. -/
lemma a2t_dalX {ζ : ℝ → ℝ} {q₀ δ : ℝ} (hδ : 0 < δ) (k : ℤ) :
    dalX ζ q₀ δ k = ζ (dalQ q₀ δ k) / δ ^ 2 := by
  unfold dalX
  rw [dal_rpow_cube hδ]
  field_simp

/-- **Perturbing a lattice window.**  If `X̂` is within `ε` of `X` and `X` has the window facts, then `X̂` has them (with the base site
`m₀ ∈ {m, m+1}`), after enlarging the gap constants. -/
lemma a2t_perturb {X Xh : ℤ → ℝ} {J m N : ℤ} {δ s1 s2 r Zm ε : ℝ} (hδ : 0 < δ) (hs1 : 0 < s1) (hs12 : s1 ≤ s2)
    (hr : 0 < r) (hJm : J ≤ m) (hmN : m < N)
    (hgap : ∀ k ∈ Icc J N, s1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ s2 * δ)
    (hXabs : ∀ k ∈ Icc J (N + 1), |X k| ≤ Zm / δ ^ 2) (hX0 : 0 ≤ X m) (hX1 : X m ≤ s2 * δ)
    (hXN : s1 * (r / 4) / δ ^ 2 ≤ X N) (hε : ∀ k ∈ Icc J (N + 1), |Xh k - X k| ≤ ε)
    (hε1 : ε ≤ s1 * δ / 4) (hε2 : ε ≤ s1 * r / 8 / δ ^ 2) :
    ∃ m0 : ℤ, J ≤ m0 ∧ m0 ≤ N ∧ (m0 = m ∨ m0 = m + 1) ∧
      (∀ k ∈ Icc J N, s1 / 2 * δ ≤ Xh (k + 1) - Xh k ∧ Xh (k + 1) - Xh k ≤ (2 * s2 + s1) * δ) ∧
      (∀ k ∈ Icc J (N + 1), |Xh k| ≤ (Zm + s1 * r) / δ ^ 2) ∧ 0 ≤ Xh m0 ∧ Xh m0 ≤ (2 * s2 + s1) * δ ∧
      s1 * r / 8 / δ ^ 2 ≤ Xh N := by
  have hJ : ∀ k ∈ Icc J N, k ∈ Icc J (N + 1) := fun k hk => by rw [mem_Icc] at hk ⊢; omega
  have hJ1 : ∀ k ∈ Icc J N, k + 1 ∈ Icc J (N + 1) := fun k hk => by rw [mem_Icc] at hk ⊢; omega
  have hgapX : ∀ k ∈ Icc J N, s1 / 2 * δ ≤ Xh (k + 1) - Xh k ∧ Xh (k + 1) - Xh k ≤ (2 * s2 + s1) * δ := by
    intro k hk
    have h1 := abs_le.1 (hε k (hJ k hk))
    have h2 := abs_le.1 (hε (k + 1) (hJ1 k hk))
    have h3 := hgap k hk
    have hs2 : 0 < s2 * δ := by have := hs1.trans_le hs12; positivity
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  have hm : m ∈ Icc J N := mem_Icc.2 ⟨hJm, hmN.le⟩
  have hmε := abs_le.1 (hε m (hJ m hm))
  have hmgap := hgap m hm
  have hm1ε := abs_le.1 (hε (m + 1) (hJ1 m hm))
  have hsδ : 0 < s1 * δ := by positivity
  have hs2δ : s1 * δ ≤ s2 * δ := mul_le_mul_of_nonneg_right hs12 hδ.le
  have hXabsX : ∀ k ∈ Icc J (N + 1), |Xh k| ≤ (Zm + s1 * r) / δ ^ 2 := by
    intro k hk
    have h1 := hε k hk
    have h2 := hXabs k hk
    have h3 : |Xh k| ≤ |X k| + ε := by
      calc |Xh k| = |(Xh k - X k) + X k| := by ring_nf
        _ ≤ |Xh k - X k| + |X k| := abs_add_le _ _
        _ ≤ ε + |X k| := by linarith
        _ = |X k| + ε := by ring
    have h4 : s1 * r / 8 / δ ^ 2 ≤ s1 * r / δ ^ 2 :=
      div_le_div_of_nonneg_right (by nlinarith [mul_pos hs1 hr]) (by positivity)
    have h5 : (Zm + s1 * r) / δ ^ 2 = Zm / δ ^ 2 + s1 * r / δ ^ 2 := by ring
    rw [h5]
    linarith
  have hNN : Xh N ≥ s1 * r / 8 / δ ^ 2 := by
    have h1 := abs_le.1 (hε N (mem_Icc.2 ⟨by omega, by omega⟩))
    have e : s1 * (r / 4) / δ ^ 2 = 2 * (s1 * r / 8 / δ ^ 2) := by ring
    linarith [h1.1]
  by_cases h0 : 0 ≤ Xh m
  · refine ⟨m, hJm, hmN.le, Or.inl rfl, hgapX, hXabsX, h0, ?_, hNN⟩
    nlinarith [hmε.2, hmgap]
  · refine ⟨m + 1, by omega, by omega, Or.inr rfl, hgapX, hXabsX, ?_, ?_, hNN⟩
    · nlinarith [hmε.1, hm1ε.1, hmgap.1, hX0, hε1]
    · nlinarith [hm1ε.2, hmgap.2, hX1, hε1]

/-- **The shifted lattice window at a simple turn.** -/
lemma a2t_window {ζ g q1 : ℝ → ℝ} {c0 r s1 s2 Bm Zm : ℝ} (hr : 0 < r) (hs1 : 0 < s1) (hs12 : s1 ≤ s2)
    (hz0 : ζ c0 = 0)
    (hd : ∀ q ∈ Set.Icc (c0 - r) (c0 + r), HasDerivAt ζ (deriv ζ q) q ∧ s1 ≤ deriv ζ q ∧ deriv ζ q ≤ s2)
    (hB0 : 0 ≤ Bm) (hB : ∀ q ∈ Set.Icc (c0 - r) (c0 + r), |q1 q / g q| ≤ Bm)
    (hZ : ∀ q ∈ Set.Icc (c0 - r) (c0 + r), |ζ q| ≤ Zm) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 ∧ ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ0 → ∃ J m0 N : ℤ, J < N ∧ J ≤ m0 ∧ m0 ≤ N ∧
      (∀ k ∈ Icc J (N + 1), dalQ q₀ δ k ∈ Set.Icc (c0 - r) (c0 + r)) ∧
      c0 - r ≤ dalQ q₀ δ J ∧ dalQ q₀ δ J < c0 - r + δ ^ 3 ∧ c0 ≤ dalQ q₀ δ m0 ∧ dalQ q₀ δ m0 < c0 + 2 * δ ^ 3 ∧
      c0 + r / 4 ≤ dalQ q₀ δ N ∧ dalQ q₀ δ (N + 1) ≤ c0 + r / 2 ∧
      (∀ k ∈ Icc J N, s1 / 2 * δ ≤ a2Xh ζ g q1 δ (dalQ q₀ δ (k + 1)) - a2Xh ζ g q1 δ (dalQ q₀ δ k) ∧
        a2Xh ζ g q1 δ (dalQ q₀ δ (k + 1)) - a2Xh ζ g q1 δ (dalQ q₀ δ k) ≤ (2 * s2 + s1) * δ) ∧
      (∀ k ∈ Icc J (N + 1), |a2Xh ζ g q1 δ (dalQ q₀ δ k)| ≤ (Zm + s1 * r) / δ ^ 2) ∧
      0 ≤ a2Xh ζ g q1 δ (dalQ q₀ δ m0) ∧ a2Xh ζ g q1 δ (dalQ q₀ δ m0) ≤ (2 * s2 + s1) * δ ∧
      2 / 3 * (√(s1 * r / 8)) ^ 3 / δ ^ 3 ≤ airyXi (a2Xh ζ g q1 δ (dalQ q₀ δ N)) := by
  obtain ⟨δL, hδL, hδL1, HL⟩ := dao_lattice hr hs1 hs12 hz0 hd
  have hsr : 0 < s1 * r / 8 := by positivity
  refine ⟨min δL (min (r / 8) (min (s1 / (4 * (Bm + 1))) (s1 * r / (8 * (Bm + 1))))), ?_,
    (min_le_left _ _).trans hδL1, ?_⟩
  · exact lt_min hδL (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  intro δ q₀ hδ hδ0
  have hδL' : δ ≤ δL := hδ0.trans (min_le_left _ _)
  have hδr : δ ≤ r / 8 := hδ0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδs : δ ≤ s1 / (4 * (Bm + 1)) :=
    hδ0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδsr : δ ≤ s1 * r / (8 * (Bm + 1)) :=
    hδ0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hδ1 : δ ≤ 1 := hδL'.trans hδL1
  obtain ⟨J, m, N, hJm, hmN, hwin, hqJ1, hqJ2, hqm1, hqm2, hqN, hqN1, hgap, hXabs, hX0, hX1, hXN⟩ :=
    HL δ q₀ hδ hδL'
  have h3 : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2]
  have h3r : δ ^ 3 ≤ r / 8 := h3.trans hδr
  -- `m < N`
  have hmN' : m < N := by
    rcases lt_or_eq_of_le hmN with h | h
    · exact h
    · subst h; linarith
  have hdX : ∀ k, dalX ζ q₀ δ k = ζ (dalQ q₀ δ k) / δ ^ 2 := fun k => a2t_dalX hδ k
  have hB1 : δ * Bm ≤ s1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at hδs
    nlinarith [hδs]
  have hε1 : δ ^ 4 * Bm ≤ s1 * δ / 4 := a2t_eps hδ hδ1 hB0 hB1
  have hε2 : δ ^ 4 * Bm ≤ s1 * r / 8 / δ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at hδsr
    have h6 : δ ^ 6 ≤ δ := by
      have : δ ^ 5 ≤ 1 := pow_le_one₀ hδ.le hδ1
      nlinarith
    have : δ ^ 4 * Bm * δ ^ 2 = δ ^ 6 * Bm := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_right h6 hB0]
  have hpert : ∀ k ∈ Icc J (N + 1), |a2Xh ζ g q1 δ (dalQ q₀ δ k) - dalX ζ q₀ δ k| ≤ δ ^ 4 * Bm := by
    intro k hk
    have e : a2Xh ζ g q1 δ (dalQ q₀ δ k) - dalX ζ q₀ δ k = δ ^ 4 * (q1 (dalQ q₀ δ k) / g (dalQ q₀ δ k)) := by
      rw [hdX]; unfold a2Xh; ring
    rw [e, abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left (hB _ (hwin k hk)) (by positivity)
  have hXa : ∀ k ∈ Icc J (N + 1), |dalX ζ q₀ δ k| ≤ Zm / δ ^ 2 := by
    intro k hk
    rw [hdX, abs_div, abs_of_pos (by positivity : 0 < δ ^ 2)]
    exact div_le_div_of_nonneg_right (hZ _ (hwin k hk)) (by positivity)
  have hXN' : s1 * (r / 4) / δ ^ 2 ≤ dalX ζ q₀ δ N := by
    have : s1 * (r / 4) / δ ^ 2 = s1 * (r / 4) / δ ^ 2 := rfl
    exact hXN
  obtain ⟨m0, hJm0, hm0N, hm0, hgapX, hXabsX, hX0X, hX1X, hNN⟩ :=
    a2t_perturb (X := dalX ζ q₀ δ) (Xh := fun k => a2Xh ζ g q1 δ (dalQ q₀ δ k)) (δ := δ) (s1 := s1) (s2 := s2)
      (r := r) (Zm := Zm) (ε := δ ^ 4 * Bm) hδ hs1 hs12 hr hJm hmN' hgap hXa hX0 (by simpa using hX1) hXN' hpert hε1 hε2
  refine ⟨J, m0, N, by omega, hJm0, hm0N, hwin, hqJ1, hqJ2, ?_, ?_, hqN, hqN1, hgapX, hXabsX, hX0X, hX1X, ?_⟩
  · rcases hm0 with rfl | rfl
    · exact hqm1
    · have : dalQ q₀ δ (m + 1) = dalQ q₀ δ m + δ ^ 3 := by unfold dalQ; push_cast; ring
      rw [this]; linarith
  · rcases hm0 with rfl | rfl
    · linarith
    · have : dalQ q₀ δ (m + 1) = dalQ q₀ δ m + δ ^ 3 := by unfold dalQ; push_cast; ring
      rw [this]; linarith
  · rw [a2t_xi hsr hδ]
    exact airyXi_mono hNN

end FormalResearch.Special
