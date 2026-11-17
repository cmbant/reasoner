module

public import FormalResearch.Special.RacahKappaBandD
public import FormalResearch.Special.RacahKappaHBandD

/-!
# Window-first bulk and band predicates for the Hahn / centred Racah chains

`rk_bulk` (`RacahKappaBulk`) and `rk_bulk_band` (`RacahKappaBandD`) each *produce* an Airy window `(J, m, N, κ, μ)`, so a statement about the amplitude `κ` (`rk_kappa_sharp_abs`) cannot be put
together with the Liouville-Green bulk form of the same chain: the two windows are different existential witnesses, and the radius cap `r ≤ ρ/2` that the bulk form needs is not exported.  This layer
restates both in the *window-first* form "for **every** window `RkWinAtG` of the exported constants, the bulk form (resp. the band mass) holds with that `κ, μ`".  The two predicates below are
the conclusions, on the lattice `q_k = q₀ + k δ³` (`q₀ = δ³/2` integer chains, `q₀ = δ³` half-integer chains).

**Claim class: definitions.**  Theorems: `BulkKappaWin`, `BulkKappaWinH`.
-/

@[expose] public section

open Finset Set FormalResearch.Racah.P3 FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

/-- The Liouville-Green bulk form of `Y` with the Airy coefficients `κ, μ`: for every lattice site `q_k = q₀ + kδ³ ∈ [c, q_* - η]`,
`Y_k = h^{1/6} π^{-1/2} w(q_k) (κ cos χ_k + μ sin χ_k) + O(C h^{7/6}(|κ|+|μ|) w(q_k))`, `h = δ³`, `χ_k = Θ(q_k)/h - Θ_*/h + π/4`, `Θ = ∫_{(c₀+c)/2}^· arccos u`. -/
def BkBulkAt (q₀ P Q τ x qs c0 c η δ C : ℝ) (Y : ℤ → ℝ) (κ μ : ℝ) : Prop :=
  ∀ k : ℤ, c ≤ dlgQ q₀ (δ ^ 3) k → dlgQ q₀ (δ ^ 3) k ≤ qs - η →
    |Y k - (δ ^ 3) ^ (1 / 6 : ℝ) * (1 / √π) * dlgsW (hrA1 P Q) (hrU P Q τ x) (dlgQ q₀ (δ ^ 3) k) *
        (κ * Real.cos (dlgP (dlgsPhase (hrU P Q τ x) ((c0 + c) / 2)) q₀ (δ ^ 3) k -
            (∫ s in (c0 + c) / 2..qs, Real.arccos (hrU P Q τ x s)) / δ ^ 3 + π / 4) +
          μ * Real.sin (dlgP (dlgsPhase (hrU P Q τ x) ((c0 + c) / 2)) q₀ (δ ^ 3) k -
            (∫ s in (c0 + c) / 2..qs, Real.arccos (hrU P Q τ x s)) / δ ^ 3 + π / 4))| ≤
      C * ((|κ| + |μ|) * ((δ ^ 3) ^ (1 / 6 : ℝ) * δ ^ 3)) * dlgsW (hrA1 P Q) (hrU P Q τ x) (dlgQ q₀ (δ ^ 3) k)

/-- The band mass of `Y` in units of the Gauss weight `M` (`M δ³ √s = 1`): for every band `kc ≤ k < jz` of the lattice `q_k = (k + θ)δ³`
(`q_{kc-1} < c ≤ q_{kc}`, `q_{jz-1} ≤ q_* - η < q_{jz}`), `T M (1 - a_B - θ₀ δ³) ≤ Σ_{kc ≤ k < jz} Y_k² ≤ T M (1 + θ₀ δ³)`, `T = (κ² + μ²) δ/2`, `a_B = c/q_* + 2√(η/q_*)`. -/
def BkBandAt (θ : ℝ) (P Q x qs c η δ θ0 : ℝ) (Y : ℤ → ℝ) (κ μ : ℝ) : Prop :=
  ∀ (kc jz : ℤ) (M : ℝ), c ≤ ((kc : ℝ) + θ) * δ ^ 3 → ((kc : ℝ) + θ - 1) * δ ^ 3 < c →
    qs - η < ((jz : ℝ) + θ) * δ ^ 3 → ((jz : ℝ) + θ - 1) * δ ^ 3 ≤ qs - η →
    M * δ ^ 3 * Real.sqrt (rkS P Q x) = 1 →
      (κ ^ 2 + μ ^ 2) * δ / 2 * M * (1 - (c / qs + 2 * √(η / qs)) - θ0 * δ ^ 3) ≤ ∑ k ∈ Finset.Ico kc jz, Y k ^ 2 ∧
      ∑ k ∈ Finset.Ico kc jz, Y k ^ 2 ≤ (κ ^ 2 + μ ^ 2) * δ / 2 * M * (1 + θ0 * δ ^ 3)

/-- **The three conclusions of the abstract sharp theorem for a family** `Fam` of chains (`h`, `Y`, Gauss weight `M`), with one set of constants (`cs = 1/√s + 1`, `s = rkS P Q x`):
(window) every member with `h ≤ δ_A³` has an Airy window `RkWinAtG θ (q₀ δ)` with `Y_max = cs/δ³`;
(sharp) for every `τ' > 0` there is `ε₁` such that for every member with `h ≤ ε₁` **every** such window has `|κ² δ - 2| ≤ τ'`;
(bulk) for every bulk window `[c, q_* - η]` there are `δ₀, C` such that for every member with `h ≤ δ₀³` **every** such window satisfies `BkBulkAt` with its own `κ, μ`. -/
def BkOut (θ : ℝ) (q₀ : ℝ → ℝ) (P Q τ x qs : ℝ) (Fam : ℝ → (ℤ → ℝ) → ℝ → Prop)
    (r Cmu ξ0 gmax gmin c1 c2 CA δA : ℝ) : Prop :=
  (∀ (h : ℝ) (Y : ℤ → ℝ) (M : ℝ), Fam h Y M → 0 < h → h ≤ δA ^ 3 →
    ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = h ∧ ∃ (J m N : ℤ) (κ μ : ℝ),
      RkWinAtG θ (q₀ δ) P Q τ x qs Y ((1 / Real.sqrt (rkS P Q x) + 1) / δ ^ 3) r CA Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ) ∧
  (∀ τ' : ℝ, 0 < τ' → ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ (h : ℝ) (Y : ℤ → ℝ) (M : ℝ), Fam h Y M → 0 < h → h ≤ ε1 →
    ∀ (δ : ℝ) (J m N : ℤ) (κ μ : ℝ), 0 < δ → δ ^ 3 = h →
      RkWinAtG θ (q₀ δ) P Q τ x qs Y ((1 / Real.sqrt (rkS P Q x) + 1) / δ ^ 3) r CA Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ →
        |κ ^ 2 * δ - 2| ≤ τ') ∧
  (∀ c0 : ℝ, 0 < c0 → c0 < qs / 2 → ∀ η : ℝ, 0 < η → η ≤ r / 2 → ∀ c : ℝ, c0 < c → c < qs - r → ∃ δ0 C : ℝ, 0 < δ0 ∧ 0 < C ∧
    ∀ (h : ℝ) (Y : ℤ → ℝ) (M : ℝ), Fam h Y M → 0 < h → h ≤ δ0 ^ 3 →
      ∀ (δ : ℝ) (J m N : ℤ) (κ μ : ℝ), 0 < δ → δ ^ 3 = h →
        RkWinAtG θ (q₀ δ) P Q τ x qs Y ((1 / Real.sqrt (rkS P Q x) + 1) / δ ^ 3) r CA Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ →
          BkBulkAt (q₀ δ) P Q τ x qs c0 c η δ C Y κ μ)

end FormalResearch.Special
