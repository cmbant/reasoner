module

public import FormalResearch.Special.DiscreteAirySecondFinal
public import FormalResearch.Special.DiscreteAirySecondQ1
public import FormalResearch.Special.DiscreteAiryOscLattice
public import FormalResearch.Special.DiscreteAiryLimitData
public import FormalResearch.Special.DiscreteAiryLimitFields
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
  amplitude relation and the `q₁`-residual equation on `U`: there are constants `δ₀, C, Q, C_μ, ξ₀` (depending on the data, `r` and `E` only) such that for
  `δ ≤ δ₀`, every `q₀` and all coefficients within `E δ⁹` of the exact second-order ones, `DaiFullR` holds with error rate `δ⁶ = h²`
  on the whole oscillatory side `[c₀ - r, c₀]` plus the bulk to `c₀ + r/4`.  The Casoratian constant `Q` does not depend on `E`.
* `airy2_turn_full`: the same with `q₁` **constructed** (`airy2_q1_exists`) on a ball, from `ζ ∈ C⁷`, `A, g ∈ C⁶`, `A₂, c₂ ∈ C⁴`.

**Claim class: proved.**  This is the abstract statement; the Hahn/Racah instances (coefficient closeness `E δ⁹`, i.e. `S4`) are not
formalised here.

The error order is `δ⁶ = h²` in the Olver weights, i.e. the bracket `Ai(t) + N^{-4/3} B Ai'(t) + O(N^{-2})` of
`thm:general-rank-airy-second` in `Weyl/P3/paper/weyl_midpoint_semiclassics.tex` (`B = q₁/g`, `h^{4/3} = δ⁴`); the sharper `O(h³)`
remainder `𝔯_N` of `thm:general-rank-airy` (ii) (residual `O(h⁴)`, amplitude `p₂` with `2 p₂/g + 𝔧 = 0`) is **not** formalised, since `p`
is taken as `ζ q₁²/(2g)` (`a2p`), which differs from `p₂` at order `h²`, inside the `δ⁶` error.  Numerical evidence only (independent
`mpmath` check, no committed verifier): for a smooth model chain `a_k = A(q_k - h/2)`, `c_k = 2 A u(q_k)` the exact recessive solution
fits `g Ai(X̂)` with error `≈ 0.004 δ⁶` for `h = 10⁻² … 3·10⁻⁴` (first order `g Ai(X)`: `≈ 0.002 δ³`).

**Not formalised:** `S4` (second-order coefficient closeness for the Hahn/Racah chains and the chain wiring); a global `q₁` on the
window (`airy2_q1_exists` is local on a ball `B(c₀, ρ)`, window `[c₀ - ρ/2, c₀ + ρ/2]`); the route from `c = 2 A u + h² c₂` to second-order
Langer-form data `(ζ, A, A₂, g, c₂)` (needs `u ∈ C⁷`); the `h²` phase / Darboux normalisation `κ`.  The `P3` external input (canonical
`Ai/Bi` basis of Geronimo–Bruno–Van Assche, connection by matching) is **not** replaced by this result.
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

/-- **Uniform window bounds** for the data of a simple turn. -/
lemma a2t_bounds {U : Set ℝ} {ζ A A2 g q1 cq : ℝ → ℝ} {c0 r : ℝ} (hr : 0 < r) (hU : IsOpen U)
    (hsub : Set.Icc (c0 - r) (c0 + r) ⊆ U) (hζ : ContDiffOn ℝ 4 ζ U) (hA : ContDiffOn ℝ 3 A U)
    (hA2 : ContDiffOn ℝ 1 A2 U) (hg : ContDiffOn ℝ 3 g U) (hq1 : ContDiffOn ℝ 3 q1 U)
    (hcq : ContinuousOn cq U) (hzpos : ∀ q ∈ U, 0 < deriv ζ q) (hApos : ∀ q ∈ U, 0 < A q)
    (hgpos : ∀ q ∈ U, 0 < g q) :
    ∃ s1 s2 gmin gmax Amin Amax Bm Zm A2m Cm : ℝ, 0 < s1 ∧ s1 ≤ s2 ∧ 0 < gmin ∧ gmin ≤ gmax ∧ 0 < Amin ∧
      Amin ≤ Amax ∧ 0 ≤ Bm ∧ 0 ≤ A2m ∧ 0 ≤ Cm ∧
      (∀ q ∈ Set.Icc (c0 - r) (c0 + r), HasDerivAt ζ (deriv ζ q) q ∧ s1 ≤ deriv ζ q ∧ deriv ζ q ≤ s2) ∧
      (∀ q ∈ Set.Icc (c0 - r) (c0 + r), |ζ q| ≤ Zm) ∧
      (∀ q ∈ Set.Icc (c0 - r) (c0 + r), gmin ≤ g q ∧ g q ≤ gmax) ∧
      (∀ q ∈ Set.Icc (c0 - r) (c0 + r), Amin ≤ A q ∧ A q ≤ Amax) ∧
      (∀ q ∈ Set.Icc (c0 - r) (c0 + r), |q1 q / g q| ≤ Bm) ∧
      (∀ q ∈ Set.Icc (c0 - r) (c0 + r), |A2 q| ≤ A2m) ∧
      (∀ q ∈ Set.Icc (c0 - r) (c0 + r), ∀ h : ℝ, |h| ≤ 1 → |a2c ζ A cq q h| ≤ Cm) := by
  have hle : c0 - r ≤ c0 + r := by linarith
  have hdζ : ContinuousOn (deriv ζ) U := hζ.continuousOn_deriv_of_isOpen hU (by norm_num)
  obtain ⟨s1, s2, hs1, hs12, hsb⟩ := dal_pos_bounds hle (hdζ.mono hsub) (fun x hx => hzpos x (hsub hx))
  obtain ⟨gmin, gmax, hg1, hg12, hgb⟩ := dal_pos_bounds hle (hg.continuousOn.mono hsub) (fun x hx => hgpos x (hsub hx))
  obtain ⟨Amin, Amax, hA1, hA12, hAb⟩ := dal_pos_bounds hle (hA.continuousOn.mono hsub) (fun x hx => hApos x (hsub hx))
  have hBc : ContinuousOn (fun q => q1 q / g q) (Set.Icc (c0 - r) (c0 + r)) :=
    (hq1.continuousOn.mono hsub).div (hg.continuousOn.mono hsub) (fun x hx => (hgpos x (hsub hx)).ne')
  obtain ⟨Bm0, hBm0⟩ := isCompact_Icc.exists_bound_of_continuousOn hBc
  obtain ⟨Zm0, hZm0⟩ := isCompact_Icc.exists_bound_of_continuousOn (hζ.continuousOn.mono hsub)
  obtain ⟨A2m0, hA2m0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hA2.continuousOn).mono hsub)
  obtain ⟨cqm0, hcqm0⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcq.mono hsub)
  have hZm : ∀ q ∈ Set.Icc (c0 - r) (c0 + r), |ζ q| ≤ max Zm0 0 := fun q hq => by
    have := hZm0 q hq; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  obtain ⟨Mc, hMc0, hMc⟩ := apuc_bound (max Zm0 0 * s2 ^ 2)
  have hCh : ∀ q ∈ Set.Icc (c0 - r) (c0 + r), |langerCosh (ζ q * deriv ζ q ^ 2)| ≤ Mc := by
    intro q hq
    have hw : |ζ q * deriv ζ q ^ 2| ≤ max Zm0 0 * s2 ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg (deriv ζ q))]
      have h1 := (hsb q hq)
      have h2 : deriv ζ q ^ 2 ≤ s2 ^ 2 := by
        have := hs1.le.trans h1.1
        exact pow_le_pow_left₀ this h1.2 2
      exact mul_le_mul (hZm q hq) h2 (sq_nonneg _) (le_max_right _ _)
    exact (hMc _ hw).1
  refine ⟨s1, s2, gmin, gmax, Amin, Amax, max Bm0 0, max Zm0 0, max A2m0 0, 2 * Amax * Mc + max cqm0 0, hs1, hs12,
    hg1, hg12, hA1, hA12, le_max_right _ _, le_max_right _ _,
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hA1.le.trans hA12)) hMc0) (le_max_right _ _), ?_, hZm, hgb, hAb, ?_, ?_, ?_⟩
  · intro q hq
    exact ⟨((hζ.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds (hsub hq))).hasDerivAt,
      (hsb q hq).1, (hsb q hq).2⟩
  · intro q hq
    have := hBm0 q hq; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  · intro q hq
    have := hA2m0 q hq; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  · intro q hq h hh
    have hc := hcqm0 q hq
    rw [Real.norm_eq_abs] at hc
    have hA0 : 0 ≤ A q := (hA1.trans_le (hAb q hq).1).le
    unfold a2c
    have h2 : |h ^ 2 * cq q| ≤ max cqm0 0 := by
      rw [abs_mul, abs_pow]
      have : |h| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) hh
      exact (mul_le_of_le_one_left (abs_nonneg _) this).trans (hc.trans (le_max_left _ _))
    have h1 : |2 * A q * langerCosh (ζ q * deriv ζ q ^ 2)| ≤ 2 * Amax * Mc := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hA0]
      have := mul_le_mul (hAb q hq).2 (hCh q hq) (abs_nonneg _) (hA1.trans_le (hA12)).le
      nlinarith [this]
    exact (abs_add_le _ _).trans (by linarith)

/-- Bounds for a coefficient within `E δ⁹` of the exact second-order one. -/
lemma a2t_acoef {a Aq A2q Amin Amax A2m E δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hE : 0 ≤ E)
    (ha : |a - (Aq + (δ ^ 3) ^ 2 * A2q)| ≤ E * δ ^ 9) (hAq : Amin ≤ Aq ∧ Aq ≤ Amax) (hA2 : |A2q| ≤ A2m) :
    Amin - δ * (A2m + E) ≤ a ∧ a ≤ Amax + A2m + E := by
  have hA20 : 0 ≤ A2m := (abs_nonneg _).trans hA2
  have h6 : δ ^ 6 ≤ δ := by
    have : δ ^ 5 ≤ 1 := pow_le_one₀ hδ.le hδ1
    nlinarith
  have h6' : δ ^ 6 ≤ 1 := h6.trans hδ1
  have h9 : δ ^ 9 ≤ δ ^ 6 := pow_le_pow_of_le_one hδ.le hδ1 (by norm_num)
  have e : (δ ^ 3) ^ 2 = δ ^ 6 := by ring
  rw [e] at ha
  have hb := abs_le.1 ha
  have hp : |δ ^ 6 * A2q| ≤ δ ^ 6 * A2m := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left hA2 (by positivity)
  have hp' := abs_le.1 hp
  have hE9 : E * δ ^ 9 ≤ E * δ := mul_le_mul_of_nonneg_left (h9.trans h6) hE
  have hEu : E * δ ^ 9 ≤ E := mul_le_of_le_one_right hE (h9.trans h6')
  have hA2d : δ ^ 6 * A2m ≤ δ * A2m := mul_le_mul_of_nonneg_right h6 hA20
  have hA2u : δ ^ 6 * A2m ≤ A2m := mul_le_of_le_one_left hA20 h6'
  constructor <;> nlinarith [hb.1, hb.2, hp'.1, hp'.2]

lemma a2t_small6 {Cl δ : ℝ} (hCl : 0 ≤ Cl) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h : δ ≤ 1 / (4 * (Cl + 1))) : Cl * δ ^ 6 ≤ 1 / 4 := by
  rw [le_div_iff₀ (by positivity)] at h
  have h3 : δ ^ 6 ≤ δ := by
    have : δ ^ 5 ≤ 1 := pow_le_one₀ hδ.le hδ1
    nlinarith [pow_pos hδ 5]
  nlinarith [mul_le_mul_of_nonneg_left h3 hCl]

/-- `|c| ≤ C_m + E` from closeness to a bounded exact coefficient. -/
lemma a2t_cbound {c ac Cm E δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hE : 0 ≤ E) (h : |c - ac| ≤ E * δ ^ 9)
    (hac : |ac| ≤ Cm) : |c| ≤ Cm + E := by
  have h9 : E * δ ^ 9 ≤ E := mul_le_of_le_one_right hE (pow_le_one₀ hδ.le hδ1)
  calc |c| = |(c - ac) + ac| := by ring_nf
    _ ≤ |c - ac| + |ac| := abs_add_le _ _
    _ ≤ Cm + E := by linarith

/-- The conclusion of `airy2_turn_conclusion`: constants `δ₀, C, Q, C_μ, ξ₀` and, for every `δ ≤ δ₀` and `q₀`, window indices
`J < N`, `J ≤ m₀ ≤ N` with the stated lattice position and, for all coefficients within `E δ⁹` of the exact second-order ones,
`DaiFullR` at the rate `δ⁶ = h²` for `X̂_k = ζ(q_k)/δ² + δ⁴ q₁(q_k)/g(q_k)` and `g_k = g(q_k)`. -/
def A2TurnConclusion (ζ A A2 g q1 cq : ℝ → ℝ) (c0 r E : ℝ) : Prop :=
    ∃ δ0 C Q Cmu ξ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 ∧ 0 < Q ∧ 0 < Cmu ∧ 0 < ξ0 ∧
      ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ0 → ∃ J m0 N : ℤ, J < N ∧ J ≤ m0 ∧ m0 ≤ N ∧
        (∀ k ∈ Icc J (N + 1), dalQ q₀ δ k ∈ Set.Icc (c0 - r) (c0 + r)) ∧
        c0 - r ≤ dalQ q₀ δ J ∧ dalQ q₀ δ J < c0 - r + δ ^ 3 ∧ c0 ≤ dalQ q₀ δ m0 ∧
        dalQ q₀ δ m0 < c0 + 2 * δ ^ 3 ∧ c0 + r / 4 ≤ dalQ q₀ δ N ∧ dalQ q₀ δ (N + 1) ≤ c0 + r / 2 ∧
        ∀ a c : ℤ → ℝ,
          (∀ k ∈ Icc (J + 1) (N + 1), |a k - (A (dalQ q₀ δ k - δ ^ 3 / 2) +
            (δ ^ 3) ^ 2 * A2 (dalQ q₀ δ k - δ ^ 3 / 2))| ≤ E * δ ^ 9) →
          (∀ k ∈ Icc (J + 1) N, |c k - a2c ζ A cq (dalQ q₀ δ k) (δ ^ 3)| ≤ E * δ ^ 9) →
          DaiFullR a c (fun k => a2Xh ζ g q1 δ (dalQ q₀ δ k)) (fun k => g (dalQ q₀ δ k)) J m0 N δ (δ ^ 6) C Q Cmu
            ξ0

/-- **The second-order bracket at a simple turn (Q5b).**  See the module docstring. -/
theorem airy2_turn_conclusion {U : Set ℝ} {ζ A A2 g q1 cq : ℝ → ℝ} {c0 r : ℝ} (hr : 0 < r) (hU : IsOpen U)
    (hsub : Set.Icc (c0 - r) (c0 + r) ⊆ U) (hζ : ContDiffOn ℝ 4 ζ U) (hA : ContDiffOn ℝ 3 A U)
    (hA2 : ContDiffOn ℝ 1 A2 U) (hg : ContDiffOn ℝ 3 g U) (hq1c : ContDiffOn ℝ 3 q1 U)
    (hcq : ContinuousOn cq U) (hz0 : ζ c0 = 0) (hzpos : ∀ q ∈ U, 0 < deriv ζ q) (hApos : ∀ q ∈ U, 0 < A q)
    (hgpos : ∀ q ∈ U, 0 < g q)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1)
    (hq1 : ∀ q ∈ U, a2Res ζ A A2 g q1 cq q = 0) (E : ℝ) (hE : 0 ≤ E) :
    A2TurnConclusion ζ A A2 g q1 cq c0 r E := by
  unfold A2TurnConclusion
  obtain ⟨s1, s2, gmin, gmax, Amin, Amax, Bm, Zm, A2m, Cm, hs1, hs12, hgmin, hgmm, hAmin, hAmm, hBm, hA2m, hCm,
    hd, hZ, hgb, hAb, hB, hA2b, hCb⟩ := a2t_bounds hr hU hsub hζ hA hA2 hg hq1c hcq hzpos hApos hgpos
  obtain ⟨δW, hδW, hδW1, HW⟩ := a2t_window hr hs1 hs12 hz0 hd hBm hB hZ
  obtain ⟨K0, δK, hK0, hδK, hδK1, HK⟩ := airy2_dai_full hU hζ hA hA2 hg hq1c hcq hrel hq1 isCompact_Icc hsub E hE
  set cL : ℝ := s1 / 2 with hcL
  set cU : ℝ := 2 * s2 + s1 with hcU
  set M : ℝ := Zm + s1 * r with hM
  set ca : ℝ := Amin / 2 with hca
  set Aa : ℝ := Amax + A2m + E with hAa
  set Cd : ℝ := Cm + E with hCd
  have hZm0 : 0 ≤ Zm := (abs_nonneg _).trans (hZ c0 ⟨by linarith, by linarith⟩)
  have hcLp : 0 < cL := by positivity
  have hcUp : 0 < cU := by have := hs1.trans_le hs12; positivity
  have hM0 : 0 ≤ M := by positivity
  have hcap : 0 < ca := by positivity
  have hgm0 : 0 ≤ gmax := hgmin.le.trans hgmm
  have hLam0 : 0 ≤ a2Lam K0 E gmax cL cU M ca gmin := by
    unfold a2Lam a2K1 a2Cn
    have := Real.sqrt_nonneg (2 + M)
    positivity
  have hQp : 0 < a2Q cL ca gmin := by unfold a2Q; positivity
  have hCmup : 0 < a2Cmu cL ca gmin gmax Aa := by
    unfold a2Cmu
    have : 0 < Aa := by rw [hAa]; have := hAmin.trans_le hAmm; positivity
    have hgmaxp : 0 < gmax := hgmin.trans_le hgmm
    positivity
  have hξ : 0 < 2 / 3 * (√(s1 * r / 8)) ^ 3 := by
    have : 0 < √(s1 * r / 8) := Real.sqrt_pos.2 (by positivity)
    positivity
  refine ⟨min δW (min δK (min (1 / (4 * (a2Lam K0 E gmax cL cU M ca gmin + 1)))
    (min (Amin / (2 * (A2m + E + 1))) (1 / (8 * cU))))),
    a2Ce K0 E gmax cL cU M ca gmin Aa Cd, a2Q cL ca gmin, a2Cmu cL ca gmin gmax Aa, 2 / 3 * (√(s1 * r / 8)) ^ 3,
    lt_min hδW (lt_min hδK (lt_min (by positivity) (lt_min (by positivity) (by positivity)))),
    (min_le_left _ _).trans hδW1, hQp, hCmup, hξ, ?_⟩
  intro δ q₀ hδ hδ0
  have hδW' : δ ≤ δW := hδ0.trans (min_le_left _ _)
  have hδK' : δ ≤ δK := hδ0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδL : δ ≤ 1 / (4 * (a2Lam K0 E gmax cL cU M ca gmin + 1)) :=
    hδ0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδA : δ ≤ Amin / (2 * (A2m + E + 1)) :=
    hδ0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hδc : δ ≤ 1 / (8 * cU) :=
    hδ0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hδ1 : δ ≤ 1 := hδW'.trans hδW1
  obtain ⟨J, m0, N, hJN, hJm0, hm0N, hwin, hqJ1, hqJ2, hqm1, hqm2, hqN, hqN1, hgap, hXabs, hX0, hX1, hxi⟩ :=
    HW δ q₀ hδ hδW'
  refine ⟨J, m0, N, hJN, hJm0, hm0N, hwin, hqJ1, hqJ2, hqm1, hqm2, hqN, hqN1, ?_⟩
  intro a c ha hc
  have hcUδ : cU * δ ≤ 1 / 8 := by
    rw [le_div_iff₀ (by positivity)] at hδc
    nlinarith only [hδc]
  have hmid := dal_mid (q₀ := q₀) (δ := δ) (c0 := c0) (r := r) hwin hδ
  have hAδ : δ * (A2m + E) ≤ Amin / 2 := by
    rw [le_div_iff₀ (by positivity)] at hδA
    nlinarith only [hδA, hδ]
  have hac : ∀ k ∈ Icc (J + 1) (N + 1), Amin / 2 ≤ a k ∧ a k ≤ Aa := by
    intro k hk
    have := a2t_acoef hδ hδ1 hE (ha k hk) (hAb _ (hmid k hk)) (hA2b _ (hmid k hk))
    constructor <;> linarith [this.1, this.2]
  have hNmem : N ∈ Icc (J + 1) (N + 1) := mem_Icc.2 ⟨by omega, by omega⟩
  have hN1mem : N + 1 ∈ Icc (J + 1) (N + 1) := mem_Icc.2 ⟨by omega, by omega⟩
  have hcN : |c N| ≤ Cd := by
    have hNc : N ∈ Icc (J + 1) N := mem_Icc.2 ⟨by omega, le_rfl⟩
    have h2 := hCb _ (hwin N (mem_Icc.2 ⟨by omega, by omega⟩)) (δ ^ 3)
      (by rw [abs_of_pos (by positivity)]; nlinarith only [pow_pos hδ 2, pow_pos hδ 3, hδ1, hδ])
    rw [hCd]
    exact a2t_cbound hδ hδ1 hE (hc N hNc) h2
  have hsmall : a2Lam K0 E gmax cL cU M ca gmin * δ ^ 6 ≤ 1 / 4 := a2t_small6 hLam0 hδ hδ1 hδL
  exact HK δ q₀ a c J m0 N cL cU gmin gmax ca M Aa Cd _ hδ (hδ0.trans ((min_le_right _ _).trans (min_le_left _ _)))
    hJN hJm0 hm0N hwin hcLp (by linarith only [hcUδ]) hM0 hcUp.le hgap hXabs hgmin
    (fun k hk => hgb _ (hwin k hk)) hcap (fun k hk => (hac k hk).1) ha hc hX0 hX1 hcUδ (hac N hNmem).2
    (hac (N + 1) hN1mem).2 hcN hxi hsmall

/-- info: 'FormalResearch.Special.airy2_turn_conclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy2_turn_conclusion

/-- **The second-order bracket at a simple turn, with `q₁` constructed.**  For smooth data on a ball `B(c₀, ρ)` (`ζ ∈ C⁷`,
`A, g ∈ C⁶`, `A₂, c₂ ∈ C⁴`, `ζ(c₀) = 0`, `ζ' > 0`, `A, g > 0`, amplitude relation) there is a regular `q₁ ∈ C³(B)` solving the
`q₁`-residual equation (`airy2_q1_exists`) and the conclusion `A2TurnConclusion` holds on `[c₀ - ρ/2, c₀ + ρ/2]`: error `δ⁶ = h²` in the
Olver weights on the whole window, Casoratian `≥ δ/Q` unchanged. -/
theorem airy2_turn_full {c0 ρ : ℝ} {ζ A A2 g cq : ℝ → ℝ} (hρ : 0 < ρ)
    (hζ : ContDiffOn ℝ 7 ζ (ball c0 ρ)) (hA : ContDiffOn ℝ 6 A (ball c0 ρ))
    (hA2 : ContDiffOn ℝ 4 A2 (ball c0 ρ)) (hg : ContDiffOn ℝ 6 g (ball c0 ρ))
    (hcq : ContDiffOn ℝ 4 cq (ball c0 ρ)) (hz0 : ζ c0 = 0)
    (hzpos : ∀ q ∈ ball c0 ρ, 0 < deriv ζ q) (hApos : ∀ q ∈ ball c0 ρ, 0 < A q)
    (hgpos : ∀ q ∈ ball c0 ρ, 0 < g q)
    (hrel : ∀ q ∈ ball c0 ρ,
      g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1)
    (E : ℝ) (hE : 0 ≤ E) :
    ∃ q1 : ℝ → ℝ, ContDiffOn ℝ 3 q1 (ball c0 ρ) ∧ (∀ q ∈ ball c0 ρ, a2Res ζ A A2 g q1 cq q = 0) ∧
      A2TurnConclusion ζ A A2 g q1 cq c0 (ρ / 2) E := by
  obtain ⟨q1, hq1c, hq1⟩ := airy2_q1_exists hρ hζ hA hA2 hg hcq hz0 hzpos hApos hrel
  refine ⟨q1, hq1c, hq1, ?_⟩
  have hsub : Set.Icc (c0 - ρ / 2) (c0 + ρ / 2) ⊆ ball c0 ρ := fun x hx => by
    rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2]
  exact airy2_turn_conclusion (by positivity) isOpen_ball hsub (hζ.of_le (by norm_num)) (hA.of_le (by norm_num))
    (hA2.of_le (by norm_num)) (hg.of_le (by norm_num)) (hq1c) hcq.continuousOn hz0 hzpos hApos hgpos hrel hq1 E hE

/-- info: 'FormalResearch.Special.airy2_turn_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy2_turn_full

end FormalResearch.Special
