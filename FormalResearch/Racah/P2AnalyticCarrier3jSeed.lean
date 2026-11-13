module

public import FormalResearch.Racah.P2AnalyticCarrier3jDef
public import FormalResearch.Racah.P2HahnChambers
public import FormalResearch.Racah.P2HahnL1
public import FormalResearch.Racah.P2ThreeJSym
public import FormalResearch.Racah.P2ThreeJRegge
public import FormalResearch.Racah.P2ThreeJSystem

/-!
# The starts of the square-root-free `3j` carrier in every chamber (Weyl P2)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, proof of `lem:sqrtfreecarrier`
("it suffices to check the starts"), `eq:3jseed`, and the chamber reductions before it.

For `α = |M-σ|`, `β = |M+σ|` natural and `(M, σ, N, μ)` on the physical lattice
(`Lat4`: the four numbers `j_±±m_±` are naturals), at the minimal rank `L₀ = max(|M|,|σ|)`:
`Φ_{L₀}^{M,σ} = seed3 M σ · √(𝔠_α(u₋,h) 𝔠_β(u₊,h)) / √(𝔠_{α+β+1}(1,h))`,
`u_∓ = (1∓x)/2`, `h = 1/N`, `x = 2μ/N` (`Phi3j_carrier_start`).  The extremal chamber `M = L₀`
is `Phi3j_seed`; the others follow from `Phi3j_regge` and `Phi3j_neg_M` (the signs combine to
`seed3`).  For `M = σ = 0` the row `L = 1` (`Phi3j_L1_M0`) gives the second scalar start
`P̃_1 = 1 - 2τ` (`Phi3j_carrier_start_one`).
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner

/-- Physical lattice at the point `(M, σ, N, μ)`: `j_- ± m_-` and `j_+ ± m_+` are natural numbers
(the four conditions of `lat_adm`). -/
def Lat4 (M σ N μ : ℚ) : Prop :=
  IsNat (jMinus N σ + mMinus M μ) ∧ IsNat (jPlus N σ - mPlus M μ) ∧
    IsNat (jMinus N σ - mMinus M μ) ∧ IsNat (jPlus N σ + mPlus M μ)

/-- The Regge exchange `(M, σ) ↦ (-σ, -M)` permutes the four lattice numbers. -/
lemma Lat4.regge {M σ N μ : ℚ} (h : Lat4 M σ N μ) : Lat4 (-σ) (-M) N μ := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩⟩ := h
  unfold Lat4 jMinus jPlus mMinus mPlus at *
  exact ⟨⟨b, by linarith⟩, ⟨a, by linarith⟩, ⟨c, by linarith⟩, ⟨d, by linarith⟩⟩

/-- The sign symmetry `(M, μ) ↦ (-M, -μ)` permutes the four lattice numbers. -/
lemma Lat4.negM {M σ N μ : ℚ} (h : Lat4 M σ N μ) : Lat4 (-M) σ N (-μ) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩⟩ := h
  unfold Lat4 jMinus jPlus mMinus mPlus at *
  exact ⟨⟨c, by linarith⟩, ⟨d, by linarith⟩, ⟨a, by linarith⟩, ⟨b, by linarith⟩⟩

lemma seed3_eq {M σ : ℚ} {α β : ℕ} (hα : |M - σ| = α) (hβ : |M + σ| = β) :
    seed3 M σ = (if σ ≤ M then (-1 : ℝ) ^ α else 1) *
      Real.sqrt (((α + β).factorial : ℝ) / ((α.factorial : ℝ) * (β.factorial : ℝ))) := by
  have h1 : pPlus3 M σ = α := by unfold pPlus3; rw [hα]; exact Nat.floor_natCast α
  have h2 : pMinus3 M σ = β := by unfold pMinus3; rw [hβ]; exact Nat.floor_natCast β
  unfold seed3
  rw [h1, h2]

/-- The Regge exchange does not change the start. -/
lemma seed3_regge (M σ : ℚ) : seed3 (-σ) (-M) = seed3 M σ := by
  have h1 : pPlus3 (-σ) (-M) = pPlus3 M σ := by
    unfold pPlus3; rw [show -σ - -M = -(σ - M) by ring, abs_neg, abs_sub_comm]
  have h2 : pMinus3 (-σ) (-M) = pMinus3 M σ := by
    unfold pMinus3; rw [show -σ + -M = -(M + σ) by ring, abs_neg]
  unfold seed3
  rw [h1, h2]
  have : (-M ≤ -σ) ↔ (σ ≤ M) := neg_le_neg_iff
  simp only [this]

lemma max_regge (M σ : ℚ) : max |(-σ)| |(-M)| = max |M| |σ| := by
  rw [abs_neg, abs_neg, max_comm]

/-- Chamber `|σ| ≤ M` (extremal `M = L₀`): `eq:3jseed` (`Phi3j_seed`). -/
theorem carrier_start_A (M σ N μ : ℚ) (α β : ℕ) (hA : |σ| ≤ M) (hα : |M - σ| = α)
    (hβ : |M + σ| = β) (hlat : Lat4 M σ N μ) :
    Phi3j M M σ N μ = seed3 M σ *
      (Real.sqrt (Cprod α ((1 - 2 * (μ : ℝ) / N) / 2) (1 / N) *
          Cprod β ((1 + 2 * (μ : ℝ) / N) / 2) (1 / N)) /
        Real.sqrt (Cprod (α + β + 1) 1 (1 / N))) := by
  have h1 : M - σ = α := by
    rw [← hα]; exact (abs_of_nonneg (by linarith [le_abs_self σ])).symm
  have h2 : M + σ = β := by
    rw [← hβ]; exact (abs_of_nonneg (by linarith [neg_abs_le σ])).symm
  obtain ⟨a, ha⟩ := hlat.1
  obtain ⟨c, hc⟩ := hlat.2.2.2
  have hc0 : σ ≤ M := (le_abs_self σ).trans hA
  rw [Phi3j_seed M σ N μ β α a c h2 h1 ha hc, seed3_eq hα hβ]
  simp only [hc0, ↓reduceIte]
  rw [h1, sgn_natCast, Nat.add_comm β α,
    mul_comm (Cprod β _ _), mul_comm (β.factorial : ℝ)]
  ring

/-- Chamber `M < 0`, `|σ| ≤ -M` (`M = -L₀`): the sign symmetry `Phi3j_neg_M` reduces to
`carrier_start_A` for `(-M, σ)` at `-μ`. -/
theorem carrier_start_C (M σ N μ : ℚ) (α β : ℕ) (hA : |σ| ≤ -M) (hα : |M - σ| = α)
    (hβ : |M + σ| = β) (hlat : Lat4 M σ N μ) :
    Phi3j (-M) M σ N μ = seed3 M σ *
      (Real.sqrt (Cprod α ((1 - 2 * (μ : ℝ) / N) / 2) (1 / N) *
          Cprod β ((1 + 2 * (μ : ℝ) / N) / 2) (1 / N)) /
        Real.sqrt (Cprod (α + β + 1) 1 (1 / N))) := by
  have hσ1 : σ ≤ -M := (le_abs_self σ).trans hA
  have hσ2 : M ≤ σ := by linarith [neg_abs_le σ]
  have h1 : σ - M = α := by
    rw [← hα, abs_sub_comm]; exact (abs_of_nonneg (by linarith)).symm
  have h2 : -M - σ = β := by
    rw [← hβ, ← abs_neg]; rw [show -(M + σ) = -M - σ by ring]
    exact (abs_of_nonneg (by linarith)).symm
  -- integrality hypotheses of `Phi3j_neg_M`
  obtain ⟨a, ha⟩ := hlat.1
  obtain ⟨b, hb⟩ := hlat.2.1
  obtain ⟨c, hc⟩ := hlat.2.2.1
  obtain ⟨d, hd⟩ := hlat.2.2.2
  have hneg := Phi3j_neg_M (-M) (-M) σ N (-μ)
    ⟨((α + β : ℕ) : ℤ), by push_cast; linarith⟩
    ⟨((b + d : ℕ) : ℤ), by
      unfold jPlus mPlus at *; push_cast; linarith⟩
    ⟨(β : ℤ), by push_cast; linarith⟩
    ⟨(b : ℤ), by unfold jPlus mPlus at *; push_cast; linarith⟩
  rw [neg_neg, neg_neg] at hneg
  have hA' : |σ| ≤ -M := hA
  have hα' : |(-M) - σ| = β := by
    rw [show -M - σ = -(M + σ) by ring, abs_neg]; exact hβ
  have hβ' : |(-M) + σ| = α := by
    rw [show -M + σ = -(M - σ) by ring, abs_neg]; exact hα
  have hseed := carrier_start_A (-M) σ N (-μ) β α hA' hα' hβ' hlat.negM
  rw [hneg, hseed, seed3_eq hα hβ, seed3_eq hα' hβ']
  have hsg : sgn (-M - σ) = (-1 : ℝ) ^ β := by rw [h2, sgn_natCast]
  rw [hsg]
  have hσM : σ ≤ M → α = 0 := by
    intro h
    have h0 : σ = M := le_antisymm h hσ2
    have : (α : ℚ) = 0 := by rw [← h1, h0]; simp
    exact_mod_cast this
  have hif : (if σ ≤ M then (-1 : ℝ) ^ α else 1) = 1 := by
    split_ifs with h
    · rw [hσM h]; simp
    · rfl
  simp only [hσ1, ↓reduceIte]
  rw [hif]
  have e3 : β + α = α + β := Nat.add_comm _ _
  simp only [e3]
  have e1 : (1 - 2 * ((-μ : ℚ) : ℝ) / N) / 2 = (1 + 2 * (μ : ℝ) / N) / 2 := by
    push_cast; ring
  have e2 : (1 + 2 * ((-μ : ℚ) : ℝ) / N) / 2 = (1 - 2 * (μ : ℝ) / N) / 2 := by
    push_cast; ring
  rw [e1, e2, mul_comm (Cprod β _ _) (Cprod α _ _), mul_comm (β.factorial : ℝ)]
  have hsq : ((-1 : ℝ) ^ β) * ((-1 : ℝ) ^ β) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination
    (Real.sqrt (((α + β).factorial : ℝ) / ((α.factorial : ℝ) * (β.factorial : ℝ))) *
      (Real.sqrt (Cprod α ((1 - 2 * (μ : ℝ) / N) / 2) (1 / N) *
          Cprod β ((1 + 2 * (μ : ℝ) / N) / 2) (1 / N)) /
        Real.sqrt (Cprod (α + β + 1) 1 (1 / N)))) * hsq

/-- Chamber `σ ≤ -|M|` (`|M| ≤ -σ`): Regge exchange to `carrier_start_A`. -/
theorem carrier_start_D (M σ N μ : ℚ) (α β : ℕ) (hA : |M| ≤ -σ) (hα : |M - σ| = α)
    (hβ : |M + σ| = β) (hlat : Lat4 M σ N μ) :
    Phi3j (-σ) M σ N μ = seed3 M σ *
      (Real.sqrt (Cprod α ((1 - 2 * (μ : ℝ) / N) / 2) (1 / N) *
          Cprod β ((1 + 2 * (μ : ℝ) / N) / 2) (1 / N)) /
        Real.sqrt (Cprod (α + β + 1) 1 (1 / N))) := by
  have hα' : |(-σ) - (-M)| = α := by rw [show -σ - -M = M - σ by ring]; exact hα
  have hβ' : |(-σ) + (-M)| = β := by
    rw [show -σ + -M = -(M + σ) by ring, abs_neg]; exact hβ
  rw [Phi3j_regge (-σ) M σ N μ,
    carrier_start_A (-σ) (-M) N μ α β (by rwa [abs_neg]) hα' hβ' hlat.regge, seed3_regge]

/-- Chamber `σ ≥ |M|`, `σ > 0`: Regge exchange to `carrier_start_C`. -/
theorem carrier_start_B (M σ N μ : ℚ) (α β : ℕ) (hA : |M| ≤ σ) (hα : |M - σ| = α)
    (hβ : |M + σ| = β) (hlat : Lat4 M σ N μ) :
    Phi3j σ M σ N μ = seed3 M σ *
      (Real.sqrt (Cprod α ((1 - 2 * (μ : ℝ) / N) / 2) (1 / N) *
          Cprod β ((1 + 2 * (μ : ℝ) / N) / 2) (1 / N)) /
        Real.sqrt (Cprod (α + β + 1) 1 (1 / N))) := by
  have hα' : |(-σ) - (-M)| = α := by rw [show -σ - -M = M - σ by ring]; exact hα
  have hβ' : |(-σ) + (-M)| = β := by
    rw [show -σ + -M = -(M + σ) by ring, abs_neg]; exact hβ
  have := carrier_start_C (-σ) (-M) N μ α β (by rwa [abs_neg, neg_neg]) hα' hβ' hlat.regge
  rw [neg_neg] at this
  rw [Phi3j_regge σ M σ N μ, this, seed3_regge]

/-- **Starts of `lem:sqrtfreecarrier`, every chamber.**  At the minimal rank `L₀ = max(|M|,|σ|)`
and a physical lattice point (`Lat4`), with `α = |M-σ|`, `β = |M+σ|` natural,
`Φ_{L₀}^{M,σ} = seed3 M σ · √(𝔠_α((1-x)/2,h) 𝔠_β((1+x)/2,h)) / √(𝔠_{α+β+1}(1,h))`
(`h = 1/N`, `x = 2μ/N`; `α+β+1 = 2L₀+1`). -/
theorem Phi3j_carrier_start (M σ N μ : ℚ) (α β : ℕ) (hα : |M - σ| = α) (hβ : |M + σ| = β)
    (hlat : Lat4 M σ N μ) :
    Phi3j (max |M| |σ|) M σ N μ = seed3 M σ *
      (Real.sqrt (Cprod α ((1 - 2 * (μ : ℝ) / N) / 2) (1 / N) *
          Cprod β ((1 + 2 * (μ : ℝ) / N) / 2) (1 / N)) /
        Real.sqrt (Cprod (α + β + 1) 1 (1 / N))) := by
  by_cases hA : |σ| ≤ M
  · have hM0 : 0 ≤ M := (abs_nonneg σ).trans hA
    rw [show max |M| |σ| = M by rw [abs_of_nonneg hM0]; exact max_eq_left hA]
    exact carrier_start_A M σ N μ α β hA hα hβ hlat
  by_cases hC : |σ| ≤ -M
  · have hM0 : M < 0 := by
      by_contra hc
      rw [not_lt] at hc
      exact hA (by have := abs_nonneg σ; linarith)
    rw [show max |M| |σ| = -M by rw [abs_of_neg hM0]; exact max_eq_left hC]
    exact carrier_start_C M σ N μ α β hC hα hβ hlat
  rw [not_le] at hA hC
  by_cases hD : |M| ≤ -σ
  · have hσ0 : σ ≤ 0 := by have := abs_nonneg M; linarith
    rw [show max |M| |σ| = -σ by rw [abs_of_nonpos hσ0]; exact max_eq_right hD]
    exact carrier_start_D M σ N μ α β hD hα hβ hlat
  · rw [not_le] at hD
    have hσ0 : 0 < σ := by
      by_contra hc
      rw [not_lt] at hc
      have : |M| ≤ -σ := by
        rcases le_or_gt 0 M with hm | hm
        · rw [abs_of_nonneg hm]; linarith [abs_of_nonpos hc]
        · rw [abs_of_neg hm]; linarith [abs_of_nonpos hc]
      linarith
    have hMσ : |M| ≤ σ := by
      rcases le_or_gt 0 M with hm | hm
      · rw [abs_of_nonneg hm]; linarith [abs_of_pos hσ0]
      · rw [abs_of_neg hm]; linarith [abs_of_pos hσ0]
    rw [show max |M| |σ| = σ by rw [abs_of_pos hσ0]; exact max_eq_right hMσ]
    exact carrier_start_B M σ N μ α β hMσ hα hβ hlat

/-- **Second scalar start** (`M = σ = 0`, rank `L = 1`): `Φ_1^{0,0} = x/√(1-h²)`, i.e.
`P̃_1 = 1 - 2τ` with `τ = (1-x)/2` (`𝔠_3(1,h) = 1 - h²`).  Needs `N ≥ 2` (rank `1 ≤ N-1`). -/
theorem Phi3j_carrier_start_one (N μ : ℚ) (hlat : Lat4 0 0 N μ) (hN : 2 ≤ N) :
    Phi3j 1 0 0 N μ = (1 - 2 * ((1 - 2 * (μ : ℝ) / N) / 2)) *
      (Real.sqrt (Cprod 0 ((1 - 2 * (μ : ℝ) / N) / 2) (1 / N) *
          Cprod 0 ((1 + 2 * (μ : ℝ) / N) / 2) (1 / N)) /
        Real.sqrt (Cprod (0 + 0 + 2 + 1) 1 (1 / N))) := by
  obtain ⟨b, hb⟩ := hlat.2.1
  obtain ⟨d, hd⟩ := hlat.2.2.2
  have hDq : N - 1 = ((b + d : ℕ) : ℚ) := by
    unfold jPlus mPlus at *; push_cast; linarith
  have hD1 : 1 ≤ b + d := by
    have : (1 : ℚ) ≤ ((b + d : ℕ) : ℚ) := by rw [← hDq]; linarith
    exact_mod_cast this
  have hL1 := Phi3j_L1_M0 N μ (b + d) d hDq hd (by omega) hD1
  rw [hL1]
  have hNr : (N : ℝ) = ((b : ℝ) + d) + 1 := by
    have : N = ((b + d : ℕ) : ℚ) + 1 := by linarith
    rw [this]; push_cast; ring
  have hμr : (μ : ℝ) = ((b : ℝ) + d) / 2 - d := by
    have : μ = ((b + d : ℕ) : ℚ) / 2 - d := by
      unfold jPlus mPlus at hd
      have hDq' : N - 1 = (b : ℚ) + d := by exact_mod_cast hDq
      push_cast; linarith
    rw [this]; push_cast; ring
  have hC3 : Cprod (0 + 0 + 2 + 1) 1 (1 / (N : ℝ)) = 1 - 1 / (N : ℝ) ^ 2 := by
    rw [show (0 + 0 + 2 + 1 : ℕ) = 1 + 2 by norm_num, Cprod_succ_succ, Cprod_one]
    push_cast
    ring
  rw [hC3, Cprod_zero, Cprod_zero]
  have hD : (0 : ℝ) < (b : ℝ) + d := by
    have : (1 : ℝ) ≤ ((b + d : ℕ) : ℝ) := by exact_mod_cast hD1
    push_cast at this; linarith
  have hNpos : (0 : ℝ) < N := by rw [hNr]; linarith
  have hsq : 1 - 1 / (N : ℝ) ^ 2 = (((b + d : ℕ) : ℝ) * (((b + d : ℕ) : ℝ) + 2)) / (N : ℝ) ^ 2 := by
    rw [hNr]; push_cast; field_simp; ring
  rw [hsq, Real.sqrt_div (by positivity), Real.sqrt_sq hNpos.le, mul_one, Real.sqrt_one]
  have hq : 0 < Real.sqrt (((b + d : ℕ) : ℝ) * (((b + d : ℕ) : ℝ) + 2)) :=
    Real.sqrt_pos.mpr (by push_cast; positivity)
  rw [hμr, hNr]
  push_cast
  field_simp
  ring

/-- info: 'FormalResearch.Racah.Phi3j_carrier_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_carrier_start

/-- info: 'FormalResearch.Racah.Phi3j_carrier_start_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_carrier_start_one

end FormalResearch.Racah
