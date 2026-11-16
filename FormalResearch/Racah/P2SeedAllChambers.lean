module

public import FormalResearch.Racah.P2SeedMultiplierLink
public import FormalResearch.Racah.P2AnalyticCarrier3jSeed

/-!
# `eq:3jseedlogallorder` in every chamber (Weyl P2, `app:3j-allorder`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `app:3j-allorder` (`eq:3jseedlogallorder`, and the
sentence on Regge and transposition covariance), `eq:3jcarrierstart`.

`P2SeedLogAllOrderPhys` treats the extremal chamber `M ≥ |σ|` (`α = M-σ`, `β = M+σ`).  Here the same
exact statements are proved in **every chamber**, for `α = |M-σ|`, `β = |M+σ|` natural, `L₀ = max(|M|,|σ|)`
(`2L₀ = α + β`), at every physical lattice point (`Lat4`): the source is `Phi3j_carrier_start`
(`P2AnalyticCarrier3jSeed`), which already contains the Regge and `M ↦ -M` covariance of the start
(`Phi3j_regge`, `Phi3j_neg_M`, with the signs combining to `seed3`), so no further covariance argument is
needed: in every chamber

`Φ_{L₀}^{Mσ}(x;1/N) = d^{L₀}_{Mσ}(x) · seedRatio α β x N⁻²`, `x = 2μ/N`

with the same function `seedRatio` (and ℓ_r = `seedEll α β r`) as in the extremal chamber; the chamber
enters only through `α = |M-σ|`, `β = |M+σ|` (so for `σ > M` the roles are `α = σ-M`, `β = M+σ`; for `M < -|σ|`,
`α = σ-M`, `β = -M-σ`; for `σ < -|M|`, `α = M-σ`, `β = -M-σ`), and the sign of `d` is the exact sign `seed3`
of the Wigner function (`dZero3_eq_wignerD`).

* `seedOK_of_lattice_all`: all convergence hypotheses of `seedRatio_log_hasSum` hold at every lattice point
  (`N ± 2μ ≥ 1 + β, 1 + α`, hence `x ∈ (-1,1)` and `α + β + 1 < 2N`).
* `Phi3j_eq_wignerSmallDx_mul_seedRatio_all`, `Phi3j_div_wignerSmallDx_all`: the exact identity and the quotient.
* `Phi3j_log_hasSum_all`: `log(Φ_{L₀}^{Mσ}/d^{L₀}_{Mσ}) = ∑_{r≥1} ℓ_r(x) N^{-2r}` exactly (convergent) at every
  lattice point, every chamber.
* `Phi3j_log_hasUniformExpansionOn_all`, `Phi3j_ratio_hasUniformExpansionOn_all`: the expansions on the physical
  grid, uniformly on compact `K ⊆ (-1,1)`; `κ_r = expCoeff (seedEll α β) r`.

Not covered here: the operator statement `(𝒢_r d_{L₀}) = κ_r d_{L₀}` outside `M ≥ |σ|`.  The proof in
`P2SeedMultiplierLink` needs the density of the physical lattice of `(M,σ)` in `x` (`exists_grid_point`), which is
proved there only for `M ≥ |σ|`; it is obtained in every chamber in `P2SeedRational` (`link3_zero_all`) not by
transporting the density but by the exact sign scalings `f3even_negMσ`, `f3even_swap`, `f3even_regge` of the
extremal-chamber statement.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Asymptotics FormalResearch.Wigner Finset Filter Topology Set

section AllChambers

variable {M σ N μ : ℚ} {α β : ℕ}

/-- On the lattice: `N - 2μ ≥ 1 + |M-σ|` and `N + 2μ ≥ 1 + |M+σ|`. -/
theorem lat_bounds (hα : |M - σ| = α) (hβ : |M + σ| = β) (hlat : Lat4 M σ N μ) :
    (α : ℚ) + 1 ≤ N - 2 * μ ∧ (β : ℚ) + 1 ≤ N + 2 * μ := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩⟩ := hlat
  simp only [jMinus, jPlus, mMinus, mPlus] at ha hb hc hd
  have a0 : (0 : ℚ) ≤ a := Nat.cast_nonneg a
  have b0 : (0 : ℚ) ≤ b := Nat.cast_nonneg b
  have c0 : (0 : ℚ) ≤ c := Nat.cast_nonneg c
  have d0 : (0 : ℚ) ≤ d := Nat.cast_nonneg d
  constructor
  · rcases abs_cases (M - σ) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h] at hα; linarith
    · rw [h] at hα; linarith
  · rcases abs_cases (M + σ) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h] at hβ; linarith
    · rw [h] at hβ; linarith

/-- On the physical lattice of any chamber all convergence hypotheses of `seedRatio_log_hasSum` hold. -/
theorem seedOK_of_lattice_all (hα : |M - σ| = α) (hβ : |M + σ| = β) (hlat : Lat4 M σ N μ) :
    SeedOK α β (2 * (μ : ℝ) / N) (1 / (N : ℝ) ^ 2) := by
  obtain ⟨h1, h2⟩ := lat_bounds hα hβ hlat
  have h1' : (α : ℝ) + 1 ≤ (N : ℝ) - 2 * μ := by exact_mod_cast h1
  have h2' : (β : ℝ) + 1 ≤ (N : ℝ) + 2 * μ := by exact_mod_cast h2
  have hα0 : (0 : ℝ) ≤ α := Nat.cast_nonneg α
  have hβ0 : (0 : ℝ) ≤ β := Nat.cast_nonneg β
  have hNpos : (0 : ℝ) < N := by linarith
  have hu1 : (1 - 2 * (μ : ℝ) / N) / 2 = ((N : ℝ) - 2 * μ) / (2 * N) := by field_simp
  have hu2 : (1 + 2 * (μ : ℝ) / N) / 2 = ((N : ℝ) + 2 * μ) / (2 * N) := by field_simp
  refine ⟨?_, ?_, by positivity, ?_, ?_, ?_⟩
  · rw [hu1]; apply div_pos <;> linarith
  · rw [hu2]; apply div_pos <;> linarith
  · rw [hu1]
    have key : (α : ℝ) ^ 2 ≤ ((N : ℝ) - 2 * μ) ^ 2 := by nlinarith
    calc (α : ℝ) ^ 2 * (1 / (N : ℝ) ^ 2) ≤ ((N : ℝ) - 2 * μ) ^ 2 * (1 / (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right key (by positivity)
      _ = 4 * ((((N : ℝ) - 2 * μ) / (2 * N)) ^ 2) := by field_simp; ring
  · rw [hu2]
    have key : (β : ℝ) ^ 2 ≤ ((N : ℝ) + 2 * μ) ^ 2 := by nlinarith
    calc (β : ℝ) ^ 2 * (1 / (N : ℝ) ^ 2) ≤ ((N : ℝ) + 2 * μ) ^ 2 * (1 / (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right key (by positivity)
      _ = 4 * ((((N : ℝ) + 2 * μ) / (2 * N)) ^ 2) := by field_simp; ring
  · have hcast : ((α + β + 1 : ℕ) : ℝ) = α + β + 1 := by push_cast; ring
    rw [hcast]
    have key : ((α : ℝ) + β + 1) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by nlinarith
    calc ((α : ℝ) + β + 1) ^ 2 * (1 / (N : ℝ) ^ 2) ≤ 4 * (N : ℝ) ^ 2 * (1 / (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right key (by positivity)
      _ = 4 * 1 ^ 2 := by field_simp

private lemma mem_Ioo_of_seedOK {x t : ℝ} (h : SeedOK α β x t) : x ∈ Ioo (-1 : ℝ) 1 :=
  ⟨by linarith [h.hp], by linarith [h.hm]⟩

/-- `d^{L₀}_{Mσ}(x) = seed3 · √(u₋^α u₊^β)` in every chamber, `x ∈ [-1,1]`. -/
theorem wignerSmallDx_L0_eq (hα : |M - σ| = α) (hβ : |M + σ| = β) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    wignerSmallDx (max |M| |σ|) M σ x =
      seed3 M σ * Real.sqrt (((1 - x) / 2) ^ α * ((1 + x) / 2) ^ β) := by
  have h := dZero3_eq_wignerD M σ α β hα hβ hx 0
  rw [dZero3_zero] at h
  have e1 : pPlus3 M σ = α := by unfold pPlus3; rw [hα]; exact Nat.floor_natCast α
  have e2 : pMinus3 M σ = β := by unfold pMinus3; rw [hβ]; exact Nat.floor_natCast β
  rw [e1, e2] at h
  simpa using h.symm

/-- **`Φ_{L₀}^{Mσ}(x;1/N) = d^{L₀}_{Mσ}(x) · seedRatio α β x N⁻²` on the physical lattice, every chamber**
(`α = |M-σ|`, `β = |M+σ|` natural, `x = 2μ/N`). -/
theorem Phi3j_eq_wignerSmallDx_mul_seedRatio_all (hα : |M - σ| = α) (hβ : |M + σ| = β)
    (hlat : Lat4 M σ N μ) :
    Phi3j (max |M| |σ|) M σ N μ = wignerSmallDx (max |M| |σ|) M σ (2 * (μ : ℝ) / N) *
      seedRatio α β (2 * (μ : ℝ) / N) (1 / (N : ℝ) ^ 2) := by
  have hok := seedOK_of_lattice_all hα hβ hlat
  have hx := mem_Ioo_of_seedOK hok
  rw [wignerSmallDx_L0_eq hα hβ ⟨hx.1.le, hx.2.le⟩, Phi3j_carrier_start M σ N μ α β hα hβ hlat]
  have ht : (1 / (N : ℝ)) ^ 2 = 1 / (N : ℝ) ^ 2 := by rw [one_div_pow]
  rw [Cprod_eq_Ct, Cprod_eq_Ct, Cprod_eq_Ct, ht]
  unfold seedRatio
  have hU : 0 < Real.sqrt (((1 - 2 * (μ : ℝ) / N) / 2) ^ α * ((1 + 2 * (μ : ℝ) / N) / 2) ^ β) :=
    Real.sqrt_pos.2 (mul_pos (pow_pos hok.hm _) (pow_pos hok.hp _))
  field_simp

/-- `d^{L₀}_{Mσ}(x) ≠ 0` for `x ∈ (-1,1)`, every chamber. -/
theorem wignerSmallDx_L0_ne_zero (hα : |M - σ| = α) (hβ : |M + σ| = β) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) : wignerSmallDx (max |M| |σ|) M σ x ≠ 0 := by
  rw [wignerSmallDx_L0_eq hα hβ ⟨hx.1.le, hx.2.le⟩]
  have h1 : 0 < (1 - x) / 2 := by linarith [hx.2]
  have h2 : 0 < (1 + x) / 2 := by linarith [hx.1]
  exact mul_ne_zero (LocalCalculus.Fun.seed3_ne_zero M σ)
    (Real.sqrt_ne_zero'.mpr (mul_pos (pow_pos h1 _) (pow_pos h2 _)))

/-- `Φ_{L₀}^{Mσ}/d^{L₀}_{Mσ} = seedRatio α β x N⁻²` on the physical lattice, every chamber. -/
theorem Phi3j_div_wignerSmallDx_all (hα : |M - σ| = α) (hβ : |M + σ| = β) (hlat : Lat4 M σ N μ) :
    Phi3j (max |M| |σ|) M σ N μ / wignerSmallDx (max |M| |σ|) M σ (2 * (μ : ℝ) / N) =
      seedRatio α β (2 * (μ : ℝ) / N) (1 / (N : ℝ) ^ 2) := by
  have hx := mem_Ioo_of_seedOK (seedOK_of_lattice_all hα hβ hlat)
  have hne := wignerSmallDx_L0_ne_zero hα hβ hx
  rw [Phi3j_eq_wignerSmallDx_mul_seedRatio_all hα hβ hlat]
  field_simp

/-- **`eq:3jseedlogallorder` in every chamber, exact at every physical lattice point.**
`log (Φ_{L₀}^{Mσ}/d^{L₀}_{Mσ}) = ∑_{r≥1} ℓ_r(x) N^{-2r}`, `x = 2μ/N`, `ℓ_r = seedEll α β r`,
`α = |M-σ|`, `β = |M+σ|`. -/
theorem Phi3j_log_hasSum_all (hα : |M - σ| = α) (hβ : |M + σ| = β) (hlat : Lat4 M σ N μ) :
    HasSum (fun r : ℕ => seedEll α β r (2 * (μ : ℝ) / N) * (1 / (N : ℝ) ^ 2) ^ r)
      (Real.log (Phi3j (max |M| |σ|) M σ N μ /
        wignerSmallDx (max |M| |σ|) M σ (2 * (μ : ℝ) / N))) := by
  rw [Phi3j_div_wignerSmallDx_all hα hβ hlat]
  exact seedRatio_log_hasSum (seedOK_of_lattice_all hα hβ hlat)

section Grid

variable (M σ) (α β) (hα : |M - σ| = α) (hβ : |M + σ| = β)
include hα hβ

theorem grid_ratio_eq_all {p : ℝ × (ℚ × ℚ)} (hp : p ∈ phys3jGrid M σ) :
    Phi3j (max |M| |σ|) M σ p.2.1 p.2.2 / wignerSmallDx (max |M| |σ|) M σ p.1 =
      seedRatio α β p.1 (eps3j p.2) := by
  obtain ⟨-, hlat, hx⟩ := hp
  rw [hx]
  exact Phi3j_div_wignerSmallDx_all hα hβ hlat

/-- **`eq:3jseedlogallorder`, every chamber, as an asymptotic statement on the physical grid**: for a
compact `K ⊆ (-1,1)`, `log(Φ_{L₀}^{Mσ}/d^{L₀}_{Mσ})(x) = ∑_{r≥1} ℓ_r(x) N^{-2r}` to every order as
`N → ∞`, uniformly in `x ∈ K`. -/
theorem Phi3j_log_hasUniformExpansionOn_all {K : Set ℝ} (hK : IsCompact K)
    (hKI : K ⊆ Ioo (-1 : ℝ) 1) :
    HasUniformExpansionOn (phys3jGrid M σ)
      (fun x q => Real.log (Phi3j (max |M| |σ|) M σ q.1 q.2 /
        wignerSmallDx (max |M| |σ|) M σ x)) (seedEll α β) eps3j atN K := by
  have h1 := ((seedRatio_log_hasUniformExpansion_compact α β hK hKI).comp_index
    tendsto_eps3j_nonneg).on (phys3jGrid M σ)
  refine HasExpansionAlong.congr_left h1 ?_
  have hS : ∀ᶠ p in 𝓟 (phys3jGrid M σ) ⊓ (𝓟 K ×ˢ atN), p ∈ phys3jGrid M σ :=
    Filter.Eventually.filter_mono inf_le_left (eventually_principal.2 fun _ h => h)
  filter_upwards [hS] with p hp
  rw [grid_ratio_eq_all M σ α β hα hβ hp]

/-- **The ratio `Φ_{L₀}^{Mσ}/d^{L₀}_{Mσ}` has the expansion `∑ κ_r(x) N^{-2r}`, every chamber**,
`κ_r = expCoeff (seedEll α β) r`, `α = |M-σ|`, `β = |M+σ|`, on the physical grid, uniformly on compact
`K ⊆ (-1,1)`. -/
theorem Phi3j_ratio_hasUniformExpansionOn_all {K : Set ℝ} (hK : IsCompact K)
    (hKI : K ⊆ Ioo (-1 : ℝ) 1) :
    HasUniformExpansionOn (phys3jGrid M σ)
      (fun x q => Phi3j (max |M| |σ|) M σ q.1 q.2 / wignerSmallDx (max |M| |σ|) M σ x)
      (expCoeff (seedEll α β)) eps3j atN K := by
  have h1 := ((seedRatio_hasUniformExpansion_compact α β hK hKI).comp_index
    tendsto_eps3j_nonneg).on (phys3jGrid M σ)
  refine HasExpansionAlong.congr_left h1 ?_
  have hS : ∀ᶠ p in 𝓟 (phys3jGrid M σ) ⊓ (𝓟 K ×ˢ atN), p ∈ phys3jGrid M σ :=
    Filter.Eventually.filter_mono inf_le_left (eventually_principal.2 fun _ h => h)
  filter_upwards [hS] with p hp
  rw [grid_ratio_eq_all M σ α β hα hβ hp]

end Grid

end AllChambers

/-- info: 'FormalResearch.Racah.seedOK_of_lattice_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedOK_of_lattice_all

/-- info: 'FormalResearch.Racah.Phi3j_eq_wignerSmallDx_mul_seedRatio_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_eq_wignerSmallDx_mul_seedRatio_all

/-- info: 'FormalResearch.Racah.Phi3j_div_wignerSmallDx_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_div_wignerSmallDx_all

/-- info: 'FormalResearch.Racah.Phi3j_log_hasSum_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_log_hasSum_all

/-- info: 'FormalResearch.Racah.Phi3j_log_hasUniformExpansionOn_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_log_hasUniformExpansionOn_all

/-- info: 'FormalResearch.Racah.Phi3j_ratio_hasUniformExpansionOn_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_ratio_hasUniformExpansionOn_all

end FormalResearch.Racah
