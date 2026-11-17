module

public import FormalResearch.Special.DiscreteAirySecondShiftLattice
public import FormalResearch.Special.DiscreteAirySecondAbstract

/-!
# Second-order Airy parametrix, part 13: wiring into the abstract `O(h²)` bracket (Q5)

The explicit constants of `dai_full_rate` (`DiscreteAirySecondAbstract`) are named (`a2Cn`, `a2K1`, `a2Lam`, `a2Ce`, `a2Q`,
`a2Cmu`).  `airy2_dai_full` plugs the shifted-form row defects (`airy2_shifted_defect_Ai/Bi`, defect `K δ⁹ w`) into `dai_full_rate`
at `n = 1`: for smooth data `(ζ, A, A₂, g, q₁, c₂)` with the amplitude relation `hrel` and the `q₁`-residual equation `hq1`,
lattice `q_k = q₀ + k δ³`, parametrix pair `(g_k Ai(X̂_k), g_k Bi(X̂_k))`, `X̂_k = ζ(q_k)/δ² + δ⁴ q₁(q_k)/g(q_k)`, and coefficients
within `E δ⁹` of the exact second-order ones `a₀(k) = (A + δ⁶ A₂)(q_k - δ³/2)`, `c₀(k) = 2 A Ch(ζ ζ'²) + δ⁶ c₂` at `q_k` the
conclusion `DaiFullR` holds with error rate `ρ = δ⁶ = h²` in the Olver weights on the whole window, and Casoratian `≥ δ/Q`
(unchanged).  The lattice-window facts (gaps of `X̂`, `|X̂| ≤ M/δ²`, base site, amplitude/coefficient bounds) are **hypotheses**
here; their derivation at a simple turn is in `DiscreteAirySecondTurn`.  **Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- `C_n = (6/5) e^{c₂ √(1+M)}`. -/
noncomputable def a2Cn (cU M : ℝ) : ℝ := 6 / 5 * Real.exp (cU * √(1 + M))
/-- `K₁ = K₀ + E · 450 g_max (2 C_n + 1)`. -/
noncomputable def a2K1 (K0 E gmax cU M : ℝ) : ℝ := K0 + E * (450 * gmax * (2 * a2Cn cU M + 1))
/-- `Λ₁ = 475 g_max K₁ (8 √(2+M)/c₁)/(c_a g_min² c₁/(8π))` (the smallness constant: `Λ₁ δ^{3+3n} ≤ 1/4`). -/
noncomputable def a2Lam (K0 E gmax cL cU M ca gmin : ℝ) : ℝ :=
  475 * gmax * a2K1 K0 E gmax cU M * (8 * √(2 + M) / cL) / (ca * gmin ^ 2 * cL / (8 * Real.pi))
/-- The error constant `Ce`. -/
noncomputable def a2Ce (K0 E gmax cL cU M ca gmin Aa Cd : ℝ) : ℝ :=
  7200 * gmax * a2Lam K0 E gmax cL cU M ca gmin +
    a2Cn cU M * (Cd * (7200 * gmax * a2Lam K0 E gmax cL cU M ca gmin) +
      Aa * (7200 * gmax * a2Lam K0 E gmax cL cU M ca gmin) * a2Cn cU M + a2K1 K0 E gmax cU M) / ca
/-- The Casoratian constant `Q = 4π/(c_a g_min² c₁)`. -/
noncomputable def a2Q (cL ca gmin : ℝ) : ℝ := 4 * Real.pi / (ca * gmin ^ 2 * cL)
/-- The coefficient `Cmu`. -/
noncomputable def a2Cmu (cL ca gmin gmax Aa : ℝ) : ℝ := 50 * gmax * Aa * a2Q cL ca gmin

/-- `dai_full_rate` at `n = 1` with named constants. -/
theorem dai_full_rate_one {X g a c a0 c0 : ℤ → ℝ} {J m0 N : ℤ}
    {δ cL cU gmin gmax ca K0 E M Aa Cd ξ0 : ℝ}
    (hJN : J < N) (hJm : J ≤ m0) (hmN : m0 ≤ N) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc1 : 0 < cL) (hc2δ : cU * δ ≤ 1)
    (hM : 0 ≤ M) (hc2 : 0 ≤ cU)
    (hgap : ∀ k ∈ Icc J N, cL * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ cU * δ)
    (hXabs : ∀ k ∈ Icc J (N + 1), |X k| ≤ M / δ ^ 2)
    (hgmin : 0 < gmin) (hgb : ∀ k ∈ Icc J (N + 1), gmin ≤ g k ∧ g k ≤ gmax)
    (hca : 0 < ca) (halow : ∀ k ∈ Icc (J + 1) (N + 1), ca ≤ a k) (hK0 : 0 ≤ K0) (hE : 0 ≤ E)
    (ha : ∀ k ∈ Icc (J + 1) (N + 1), |a k - a0 k| ≤ E * δ ^ 9)
    (hc : ∀ k ∈ Icc (J + 1) N, |c k - c0 k| ≤ E * δ ^ 9)
    (hdA : ∀ k ∈ Icc (J + 1) N, |jac a0 c0 (daoPhi g X) k| ≤ K0 * δ ^ 9 * airyWt (X k))
    (hdB : ∀ k ∈ Icc (J + 1) N, |jac a0 c0 (daoPsi g X) k| ≤ K0 * δ ^ 9 * airyBiWt (X k))
    (hX0 : 0 ≤ X m0) (hX1 : X m0 ≤ cU * δ) (hc8 : cU * δ ≤ 1 / 8)
    (haN : a N ≤ Aa) (haN1 : a (N + 1) ≤ Aa) (hcN : |c N| ≤ Cd) (hxi : ξ0 / δ ^ 3 ≤ airyXi (X N))
    (hsmall : a2Lam K0 E gmax cL cU M ca gmin * δ ^ 6 ≤ 1 / 4) :
    DaiFullR a c X g J m0 N δ (δ ^ 6) (a2Ce K0 E gmax cL cU M ca gmin Aa Cd) (a2Q cL ca gmin)
      (a2Cmu cL ca gmin gmax Aa) ξ0 := by
  have := dai_full_rate (X := X) (g := g) (a := a) (c := c) (a0 := a0) (c0 := c0) (J := J) (m0 := m0) (N := N)
    (δ := δ) (c1 := cL) (c2 := cU) (gmin := gmin) (gmax := gmax) (ca := ca) (K0 := K0) (E := E) (M := M)
    (Aa := Aa) (Cd := Cd) (ξ0 := ξ0) 1 hJN hJm hmN hδ hδ1 hc1 hc2δ hM hc2 hgap hXabs hgmin hgb hca halow hK0 hE
    (by simpa using ha) (by simpa using hc) (by simpa using hdA) (by simpa using hdB) hX0 hX1 hc8 haN haN1 hcN hxi
    (by simpa [a2Lam, a2K1, a2Cn] using hsmall)
  simpa [a2Ce, a2Lam, a2K1, a2Cn, a2Q, a2Cmu] using this

/-- **Q5: the second-order abstract bracket for smooth data (window facts as hypotheses).**  There are `K₀, δ₀` (depending on the
data only) such that for `δ ≤ δ₀`, every lattice window `[J, N+1]` inside `Jw`, and all coefficients within `E δ⁹` of the exact
second-order ones, `DaiFullR` holds at the rate `δ⁶ = h²` with the explicit constants `a2Ce, a2Q, a2Cmu`. -/
theorem airy2_dai_full {U Jw : Set ℝ} {ζ A A2 g q1 c2 : ℝ → ℝ} (hU : IsOpen U) (hζ : ContDiffOn ℝ 4 ζ U)
    (hA : ContDiffOn ℝ 3 A U) (hA2 : ContDiffOn ℝ 1 A2 U) (hg : ContDiffOn ℝ 3 g U)
    (hq1c : ContDiffOn ℝ 3 q1 U) (hc2 : ContinuousOn c2 U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1)
    (hq1 : ∀ q ∈ U, a2Res ζ A A2 g q1 c2 q = 0) (hJ : IsCompact Jw) (hJU : Jw ⊆ U) (E : ℝ) (hE : 0 ≤ E) :
    ∃ K0 δ0 : ℝ, 0 < K0 ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧
      ∀ (δ q₀ : ℝ) (a c : ℤ → ℝ) (J m0 N : ℤ) (cL cU gmin gmax ca M Aa Cd ξ0 : ℝ), 0 < δ → δ ≤ δ0 →
        J < N → J ≤ m0 → m0 ≤ N → (∀ k ∈ Icc J (N + 1), dalQ q₀ δ k ∈ Jw) → 0 < cL → cU * δ ≤ 1 → 0 ≤ M →
        0 ≤ cU →
        (∀ k ∈ Icc J N, cL * δ ≤ a2Xh ζ g q1 δ (dalQ q₀ δ (k + 1)) - a2Xh ζ g q1 δ (dalQ q₀ δ k) ∧
          a2Xh ζ g q1 δ (dalQ q₀ δ (k + 1)) - a2Xh ζ g q1 δ (dalQ q₀ δ k) ≤ cU * δ) →
        (∀ k ∈ Icc J (N + 1), |a2Xh ζ g q1 δ (dalQ q₀ δ k)| ≤ M / δ ^ 2) → 0 < gmin →
        (∀ k ∈ Icc J (N + 1), gmin ≤ g (dalQ q₀ δ k) ∧ g (dalQ q₀ δ k) ≤ gmax) → 0 < ca →
        (∀ k ∈ Icc (J + 1) (N + 1), ca ≤ a k) →
        (∀ k ∈ Icc (J + 1) (N + 1), |a k - (A (dalQ q₀ δ k - δ ^ 3 / 2) +
          (δ ^ 3) ^ 2 * A2 (dalQ q₀ δ k - δ ^ 3 / 2))| ≤ E * δ ^ 9) →
        (∀ k ∈ Icc (J + 1) N, |c k - a2c ζ A c2 (dalQ q₀ δ k) (δ ^ 3)| ≤ E * δ ^ 9) →
        0 ≤ a2Xh ζ g q1 δ (dalQ q₀ δ m0) → a2Xh ζ g q1 δ (dalQ q₀ δ m0) ≤ cU * δ → cU * δ ≤ 1 / 8 →
        a N ≤ Aa → a (N + 1) ≤ Aa → |c N| ≤ Cd →
        ξ0 / δ ^ 3 ≤ airyXi (a2Xh ζ g q1 δ (dalQ q₀ δ N)) →
        a2Lam K0 E gmax cL cU M ca gmin * δ ^ 6 ≤ 1 / 4 →
        DaiFullR a c (fun k => a2Xh ζ g q1 δ (dalQ q₀ δ k)) (fun k => g (dalQ q₀ δ k)) J m0 N δ (δ ^ 6)
          (a2Ce K0 E gmax cL cU M ca gmin Aa Cd) (a2Q cL ca gmin) (a2Cmu cL ca gmin gmax Aa) ξ0 := by
  obtain ⟨KA, δA, hKA, hδA, hδA1, HA⟩ := airy2_shifted_defect_Ai hU hζ hA hA2 hg hq1c hc2 hrel hq1 hJ hJU
  obtain ⟨KB, δB, hKB, hδB, hδB1, HB⟩ := airy2_shifted_defect_Bi hU hζ hA hA2 hg hq1c hc2 hrel hq1 hJ hJU
  refine ⟨max KA KB, min δA δB, lt_max_of_lt_left hKA, lt_min hδA hδB, (min_le_left _ _).trans hδA1,
    fun δ q₀ a c J m0 N cL cU gmin gmax ca M Aa Cd ξ0 hδ hδδ hJN hJm hmN hwin hcL hcU1 hM hcU hgap hXabs hgmin
      hgb hca halow ha hc hX0 hX1 hc8 haN haN1 hcN hxi hsmall => ?_⟩
  have hδ1 : δ ≤ 1 := hδδ.trans ((min_le_left _ _).trans hδA1)
  have hmemJ : ∀ k ∈ Icc (J + 1) N, k ∈ Icc J (N + 1) := fun k hk => by
    rw [mem_Icc] at hk ⊢; omega
  refine dai_full_rate_one (X := fun k => a2Xh ζ g q1 δ (dalQ q₀ δ k)) (g := fun k => g (dalQ q₀ δ k)) (a := a)
    (c := c) (a0 := fun j => A (dalQ q₀ δ j - δ ^ 3 / 2) + (δ ^ 3) ^ 2 * A2 (dalQ q₀ δ j - δ ^ 3 / 2))
    (c0 := fun j => a2c ζ A c2 (dalQ q₀ δ j) (δ ^ 3)) hJN hJm hmN hδ hδ1 hcL hcU1 hM hcU hgap hXabs hgmin hgb hca
    halow (lt_max_of_lt_left hKA).le hE ha hc ?_ ?_ hX0 hX1 hc8 haN haN1 hcN hxi hsmall
  · intro k hk
    have := (HA δ q₀ hδ (hδδ.trans (min_le_left _ _)) k (hwin k (hmemJ k hk)))
    refine this.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      (airyWt_pos _).le)
  · intro k hk
    have := (HB δ q₀ hδ (hδδ.trans (min_le_right _ _)) k (hwin k (hmemJ k hk)))
    refine this.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
      (airyBiWt_pos _).le)

/-- info: 'FormalResearch.Special.airy2_dai_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy2_dai_full

end FormalResearch.Special
