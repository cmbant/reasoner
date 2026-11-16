module

public import FormalResearch.Racah.P2SeedLogAllOrder
public import FormalResearch.Racah.P2ThreeJSeed
public import FormalResearch.Racah.P2AnalyticLeading
public import FormalResearch.Asymptotics.Examples

/-!
# `eq:3jseedlogallorder` for the physical `3j` kernel (Weyl P2, `app:3j-allorder`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, appendix `app:3j-allorder`,
`eq:3jseedlogallorder` and the sentence after it.

Notation: `M, σ ∈ ℚ` with `α = M-σ` and `β = M+σ` natural numbers (the extremal chamber
`M ≥ |σ|`, `M = L₀`), `N, μ` on the physical lattice (`a = j_-+m_-` and `c = j_++m_+` natural),
`x = 2μ/N`, `t = N⁻²`.

## Results

* `Phi3j_eq_wignerSmallDx_mul_seedRatio`: `Φ_M^{Mσ}(x;1/N) = d^M_{Mσ}(x) · seedRatio α β x (N⁻²)`,
  so `Φ/d = seedRatio` (`Phi3j_div_wignerSmallDx`, `d ≠ 0` on `(-1,1)`); the identification of
  `eq:3jseed` with the `d`-function value `d^M_{Mσ} = ε √((2M)!/(α!β!)) √(u₋^α u₊^β)`
  (`wignerSmallDx_extremal`).
* `Phi3j_log_hasSum`: **at every physical lattice point**
  `log(Φ_M^{Mσ}/d^M_{Mσ}) = ∑_{r≥1} ℓ_r(x) N^{-2r}` converges and equals the left side
  (`seedEll` is the paper's `ℓ_r`; `S_{2r}(p) = 2B_{2r+1}((p+1)/2)/(2r+1)` in
  `FormalResearch.Asymptotics.centeredPowerSum_even_eq_bernoulliFun`).  All convergence
  hypotheses of `P2SeedLogAllOrder` hold automatically on the lattice.
* `Phi3j_log_hasUniformExpansionOn` and `Phi3j_ratio_hasUniformExpansionOn`: as `N → ∞` on the
  physical grid, uniformly for `x` in a compact `K ⊆ (-1,1)`, `log(Φ/d)` has the expansion
  `∑ ℓ_r(x) N^{-2r}` and `Φ/d` has the expansion `∑ κ_r(x) N^{-2r}`, `κ_r = [t^r] exp(∑ ℓ_s t^s)`.

Not covered: this is the seed (extremal rank `L = M`, `k = 0`) statement only.  It is not shown
here that the local-calculus functions `ψ_{2r}` of `prop:localcalculus(b)` equal `κ_r`: the abstract
`eq:3jpsi2r` is `local_calculus_start` (`P2LocalCalculusLeftNormal`), but its instance at the seed row,
`ψ_{2r} = κ_r - 𝒥(𝖡_{2r})d/d`, is not shown here.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Asymptotics FormalResearch.Wigner Finset Filter Topology Set

/-- Wigner's extremal value in the variable `x = cos θ`:
`d^M_{Mσ}(arccos x) = (-1)^α √((α+β)!/(α!β!)) √(u₋^α u₊^β)` for `α = M-σ`, `β = M+σ` natural,
`x ∈ [-1,1]`. -/
theorem wignerSmallDx_extremal (M σ : ℚ) (α β : ℕ) (hα : M - σ = α) (hβ : M + σ = β) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    wignerSmallDx M M σ x = (-1 : ℝ) ^ α * Real.sqrt (((α + β).factorial : ℝ) /
      ((α.factorial : ℝ) * β.factorial)) *
        Real.sqrt (((1 - x) / 2) ^ α * ((1 + x) / 2) ^ β) := by
  have hα' : |M - σ| = α := by rw [hα]; exact abs_of_nonneg (Nat.cast_nonneg α)
  have hβ' : |M + σ| = β := by rw [hβ]; exact abs_of_nonneg (Nat.cast_nonneg β)
  have hσM : σ ≤ M := by have : (0 : ℚ) ≤ α := Nat.cast_nonneg α; linarith
  have hM0 : 0 ≤ M := by
    have : (0 : ℚ) ≤ α := Nat.cast_nonneg α; have : (0 : ℚ) ≤ β := Nat.cast_nonneg β; linarith
  have hmax : max |M| |σ| + ((0 : ℕ) : ℚ) = M := by
    rw [Nat.cast_zero, add_zero, abs_of_nonneg hM0]
    exact max_eq_left (abs_le.mpr ⟨by linarith [(Nat.cast_nonneg β : (0 : ℚ) ≤ β)], hσM⟩)
  have h := wignerSmallD_eq_signE3 M σ α β hα' hβ' 0 (Real.arccos x)
  rw [hmax] at h
  unfold wignerSmallDx
  rw [h, wignerJacobiForm_arccos α β 0 hx]
  simp [signE3, hσM, wignerJacobiNorm, FormalResearch.Special.jacobi_zero]
  ring

private lemma lattice_rel (M σ N μ : ℚ) (α β a c : ℕ) (hα : M - σ = α) (hβ : M + σ = β)
    (ha : jMinus N σ + mMinus M μ = a) (hc : jPlus N σ + mPlus M μ = c) :
    (N : ℝ) = a + c + 1 + ((α : ℝ) + β) / 2 ∧ (N : ℝ) + 2 * μ = 2 * a + β + 1 ∧
      (N : ℝ) - 2 * μ = 2 * c + α + 1 := by
  have e1 : N = (a : ℚ) + c + 1 + M := by unfold jMinus jPlus mMinus mPlus at *; linarith
  have e2 : N + 2 * μ = 2 * a + β + 1 := by unfold jMinus jPlus mMinus mPlus at *; linarith
  have e3 : N - 2 * μ = 2 * c + α + 1 := by unfold jMinus jPlus mMinus mPlus at *; linarith
  have e4 : M = ((α : ℚ) + β) / 2 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (Rat.cast : ℚ → ℝ) e1
    rw [e4] at this
    push_cast at this; linarith
  · have := congrArg (Rat.cast : ℚ → ℝ) e2
    push_cast at this; linarith
  · have := congrArg (Rat.cast : ℚ → ℝ) e3
    push_cast at this; linarith

/-- On the physical lattice all convergence hypotheses of `seedRatio_log_hasSum` hold. -/
theorem seedOK_of_lattice (M σ N μ : ℚ) (α β a c : ℕ) (hα : M - σ = α) (hβ : M + σ = β)
    (ha : jMinus N σ + mMinus M μ = a) (hc : jPlus N σ + mPlus M μ = c) :
    SeedOK α β (2 * (μ : ℝ) / N) (1 / (N : ℝ) ^ 2) := by
  obtain ⟨hN, k1, k2⟩ := lattice_rel M σ N μ α β a c hα hβ ha hc
  have hNpos : (0 : ℝ) < N := by
    rw [hN]; positivity
  have hu1 : (1 - 2 * (μ : ℝ) / N) / 2 = (2 * c + α + 1) / (2 * N) := by
    field_simp; linarith
  have hu2 : (1 + 2 * (μ : ℝ) / N) / 2 = (2 * a + β + 1) / (2 * N) := by
    field_simp; linarith
  have hα0 : (0 : ℝ) ≤ α := Nat.cast_nonneg α
  have hβ0 : (0 : ℝ) ≤ β := Nat.cast_nonneg β
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  refine ⟨?_, ?_, by positivity, ?_, ?_, ?_⟩
  · rw [hu1]; positivity
  · rw [hu2]; positivity
  · rw [hu1]
    have key : (α : ℝ) ^ 2 ≤ (2 * c + α + 1) ^ 2 := by nlinarith
    calc (α : ℝ) ^ 2 * (1 / (N : ℝ) ^ 2) ≤ (2 * c + α + 1) ^ 2 * (1 / (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right key (by positivity)
      _ = 4 * (((2 * c + α + 1) / (2 * N)) ^ 2) := by field_simp; ring
  · rw [hu2]
    have key : (β : ℝ) ^ 2 ≤ (2 * a + β + 1) ^ 2 := by nlinarith
    calc (β : ℝ) ^ 2 * (1 / (N : ℝ) ^ 2) ≤ (2 * a + β + 1) ^ 2 * (1 / (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right key (by positivity)
      _ = 4 * (((2 * a + β + 1) / (2 * N)) ^ 2) := by field_simp; ring
  · have hcast : ((α + β + 1 : ℕ) : ℝ) = α + β + 1 := by push_cast; ring
    rw [hcast]
    have key : ((α : ℝ) + β + 1) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by nlinarith
    calc ((α : ℝ) + β + 1) ^ 2 * (1 / (N : ℝ) ^ 2) ≤ 4 * (N : ℝ) ^ 2 * (1 / (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right key (by positivity)
      _ = 4 * 1 ^ 2 := by field_simp

private lemma mem_Icc_of_seedOK {α β : ℕ} {x t : ℝ} (h : SeedOK α β x t) :
    x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [h.hp], by linarith [h.hm]⟩

/-- **`Φ_M^{Mσ}(x; 1/N) = d^M_{Mσ}(x) · seedRatio α β x N⁻²`** on the physical lattice
(`α = M-σ`, `β = M+σ` natural, `x = 2μ/N`): `eq:3jseed` against Wigner's extremal value. -/
theorem Phi3j_eq_wignerSmallDx_mul_seedRatio (M σ N μ : ℚ) (α β a c : ℕ) (hα : M - σ = α)
    (hβ : M + σ = β) (ha : jMinus N σ + mMinus M μ = a) (hc : jPlus N σ + mPlus M μ = c) :
    Phi3j M M σ N μ = wignerSmallDx M M σ (2 * (μ : ℝ) / N) *
      seedRatio α β (2 * (μ : ℝ) / N) (1 / (N : ℝ) ^ 2) := by
  have hok := seedOK_of_lattice M σ N μ α β a c hα hβ ha hc
  rw [wignerSmallDx_extremal M σ α β hα hβ (mem_Icc_of_seedOK hok),
    Phi3j_seed M σ N μ β α a c hβ hα ha hc, hα, sgn_natCast]
  have ht : (1 / (N : ℝ)) ^ 2 = 1 / (N : ℝ) ^ 2 := by rw [one_div_pow]
  rw [Cprod_eq_Ct, Cprod_eq_Ct, Cprod_eq_Ct, ht]
  unfold seedRatio
  have hU : 0 < Real.sqrt (((1 - 2 * (μ : ℝ) / N) / 2) ^ α * ((1 + 2 * (μ : ℝ) / N) / 2) ^ β) :=
    Real.sqrt_pos.2 (mul_pos (pow_pos hok.hm _) (pow_pos hok.hp _))
  rw [add_comm β α, mul_comm (β.factorial : ℝ), mul_comm (Ct β _ _)]
  field_simp

/-- `d^M_{Mσ}(x) ≠ 0` for `x ∈ (-1,1)`. -/
theorem wignerSmallDx_extremal_ne_zero (M σ : ℚ) (α β : ℕ) (hα : M - σ = α) (hβ : M + σ = β)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : wignerSmallDx M M σ x ≠ 0 := by
  rw [wignerSmallDx_extremal M σ α β hα hβ ⟨hx.1.le, hx.2.le⟩]
  have h1 : 0 < (1 - x) / 2 := by linarith [hx.2]
  have h2 : 0 < (1 + x) / 2 := by linarith [hx.1]
  have h3 : 0 < Real.sqrt (((α + β).factorial : ℝ) / ((α.factorial : ℝ) * β.factorial)) :=
    Real.sqrt_pos.2 (by positivity)
  have h4 : 0 < Real.sqrt (((1 - x) / 2) ^ α * ((1 + x) / 2) ^ β) :=
    Real.sqrt_pos.2 (mul_pos (pow_pos h1 _) (pow_pos h2 _))
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) h3.ne') h4.ne'

/-- `Φ_M^{Mσ}/d^M_{Mσ} = seedRatio α β x N⁻²` on the physical lattice. -/
theorem Phi3j_div_wignerSmallDx (M σ N μ : ℚ) (α β a c : ℕ) (hα : M - σ = α)
    (hβ : M + σ = β) (ha : jMinus N σ + mMinus M μ = a) (hc : jPlus N σ + mPlus M μ = c) :
    Phi3j M M σ N μ / wignerSmallDx M M σ (2 * (μ : ℝ) / N) =
      seedRatio α β (2 * (μ : ℝ) / N) (1 / (N : ℝ) ^ 2) := by
  have hok := seedOK_of_lattice M σ N μ α β a c hα hβ ha hc
  have hx := mem_Icc_of_seedOK hok
  have hne : wignerSmallDx M M σ (2 * (μ : ℝ) / N) ≠ 0 :=
    wignerSmallDx_extremal_ne_zero M σ α β hα hβ
      ⟨by linarith [hok.hp], by linarith [hok.hm]⟩
  rw [Phi3j_eq_wignerSmallDx_mul_seedRatio M σ N μ α β a c hα hβ ha hc]
  field_simp

/-- **`eq:3jseedlogallorder` at every physical lattice point (exact, convergent).**
`log (Φ_M^{Mσ}/d^M_{Mσ}) = ∑_{r≥1} ℓ_r(x) N^{-2r}`, `x = 2μ/N`, with the paper's
`ℓ_r = (1/4r)[S_{2r}(2M+1) - S_{2r}(M+σ)/u₊^{2r} - S_{2r}(M-σ)/u₋^{2r}]` (`seedEll α β r x`,
`α = M-σ`, `β = M+σ`, `2M+1 = α+β+1`). -/
theorem Phi3j_log_hasSum (M σ N μ : ℚ) (α β a c : ℕ) (hα : M - σ = α)
    (hβ : M + σ = β) (ha : jMinus N σ + mMinus M μ = a) (hc : jPlus N σ + mPlus M μ = c) :
    HasSum (fun r : ℕ => seedEll α β r (2 * (μ : ℝ) / N) * (1 / (N : ℝ) ^ 2) ^ r)
      (Real.log (Phi3j M M σ N μ / wignerSmallDx M M σ (2 * (μ : ℝ) / N))) := by
  rw [Phi3j_div_wignerSmallDx M σ N μ α β a c hα hβ ha hc]
  exact seedRatio_log_hasSum (seedOK_of_lattice M σ N μ α β a c hα hβ ha hc)

/-! ### Asymptotics along the physical grid -/

theorem tendsto_eps3j_nonneg : Tendsto eps3j atN (𝓝[≥] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_eps3j, Eventually.of_forall fun q => by
    simp only [eps3j, Set.mem_Ici]; positivity⟩

section Grid

variable (M σ : ℚ) (α β : ℕ) (hα : M - σ = α) (hβ : M + σ = β)
include hα hβ

theorem grid_ratio_eq {p : ℝ × (ℚ × ℚ)} (hp : p ∈ phys3jGrid M σ) :
    Phi3j M M σ p.2.1 p.2.2 / wignerSmallDx M M σ p.1 = seedRatio α β p.1 (eps3j p.2) := by
  obtain ⟨-, hlat, hx⟩ := hp
  obtain ⟨a, ha⟩ := hlat.1
  obtain ⟨c, hc⟩ := hlat.2.2.2
  rw [hx]
  exact Phi3j_div_wignerSmallDx M σ p.2.1 p.2.2 α β a c hα hβ ha hc

/-- **`eq:3jseedlogallorder` as an asymptotic statement on the physical grid.**  For a compact
`K ⊆ (-1,1)`, as `N → ∞` on the physical lattice,
`log(Φ_M^{Mσ}/d^M_{Mσ})(x) = ∑_{r≥1} ℓ_r(x) N^{-2r}` to every order, uniformly for `x ∈ K`. -/
theorem Phi3j_log_hasUniformExpansionOn {K : Set ℝ} (hK : IsCompact K)
    (hKI : K ⊆ Ioo (-1 : ℝ) 1) :
    HasUniformExpansionOn (phys3jGrid M σ)
      (fun x q => Real.log (Phi3j M M σ q.1 q.2 / wignerSmallDx M M σ x)) (seedEll α β)
      eps3j atN K := by
  have h1 := ((seedRatio_log_hasUniformExpansion_compact α β hK hKI).comp_index
    tendsto_eps3j_nonneg).on (phys3jGrid M σ)
  refine HasExpansionAlong.congr_left h1 ?_
  have hS : ∀ᶠ p in 𝓟 (phys3jGrid M σ) ⊓ (𝓟 K ×ˢ atN), p ∈ phys3jGrid M σ :=
    Filter.Eventually.filter_mono inf_le_left (eventually_principal.2 fun _ h => h)
  filter_upwards [hS] with p hp
  rw [grid_ratio_eq M σ α β hα hβ hp]

/-- **The ratio `Φ_M^{Mσ}/d^M_{Mσ}` has the expansion `∑ κ_r(x) N^{-2r}`**, `κ_r(x) = [t^r]
exp(∑_{s≥1} ℓ_s(x) t^s)` (`expCoeff`), on the physical grid, uniformly for `x ∈ K`. -/
theorem Phi3j_ratio_hasUniformExpansionOn {K : Set ℝ} (hK : IsCompact K)
    (hKI : K ⊆ Ioo (-1 : ℝ) 1) :
    HasUniformExpansionOn (phys3jGrid M σ)
      (fun x q => Phi3j M M σ q.1 q.2 / wignerSmallDx M M σ x)
      (expCoeff (seedEll α β)) eps3j atN K := by
  have h1 := ((seedRatio_hasUniformExpansion_compact α β hK hKI).comp_index
    tendsto_eps3j_nonneg).on (phys3jGrid M σ)
  refine HasExpansionAlong.congr_left h1 ?_
  have hS : ∀ᶠ p in 𝓟 (phys3jGrid M σ) ⊓ (𝓟 K ×ˢ atN), p ∈ phys3jGrid M σ :=
    Filter.Eventually.filter_mono inf_le_left (eventually_principal.2 fun _ h => h)
  filter_upwards [hS] with p hp
  rw [grid_ratio_eq M σ α β hα hβ hp]

end Grid

/-- info: 'FormalResearch.Racah.wignerSmallDx_extremal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallDx_extremal

/-- info: 'FormalResearch.Racah.Phi3j_eq_wignerSmallDx_mul_seedRatio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_eq_wignerSmallDx_mul_seedRatio

/-- info: 'FormalResearch.Racah.Phi3j_div_wignerSmallDx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_div_wignerSmallDx

/-- info: 'FormalResearch.Racah.Phi3j_log_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_log_hasSum

/-- info: 'FormalResearch.Racah.Phi3j_log_hasUniformExpansionOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_log_hasUniformExpansionOn

/-- info: 'FormalResearch.Racah.Phi3j_ratio_hasUniformExpansionOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_ratio_hasUniformExpansionOn

end FormalResearch.Racah
