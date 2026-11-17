module

public import FormalResearch.Special.BulkKappaExplicit
public import FormalResearch.Special.BulkKappaHahnH

/-!
# `κ² δ → 2` and the explicit bulk form for the actual `3j` chain (integer and half-integer data, `τ = ±1`)

Instances of the abstract theorems `bk_sharp_abs`, `bk_sharp_absH` (`BulkKappaSharp`) and `bk_explicit_of_out` (`BulkKappaExplicit`) for the family of `3j` chains at the lattice nodes
(`bk_hahn_int`, `bk_hahn_half`, `BulkKappaHahn`, `BulkKappaHahnH`), all for the geometric data `P = 1, Q = 0, s = 1`, `q_* = √(1 - x²)`:

| chain | lattice | `h` | window | turn type |
|---|---|---|---|---|
| `hahn3jY M σ N x` | `q_k = (k+½)h` | `1/N` | `RkWinAt` | `τ = +1`, `0 < x < 1` (`hahn_chain_kappa_sharp_win`, `hahn_chain_bulk_explicit`) |
| `(-1)^k hahn3jY M σ N x k` | `q_k = (k+½)h` | `1/N` | `RkWinAt` | `τ = -1`, `-1 < x < 0` (`hahn_chain_kappa_sharp_neg`, `hahn_chain_bulk_explicit_neg`) |
| `hahn3jYH M σ N x` | `q_k = (k+1)h` | `1/(N+½)` | `RkWinAtH` | `τ = +1` (`hahn_chain_kappa_sharp_half`, `hahn_chain_bulk_explicit_half`) |
| `(-1)^k hahn3jYH M σ N x k` | `q_k = (k+1)h` | `1/(N+½)` | `RkWinAtH` | `τ = -1` (`hahn_chain_kappa_sharp_half_neg`, `hahn_chain_bulk_explicit_half_neg`) |

**`κ² δ → 2`** (`hahn_chain_kappa_sharp_*`): for every `τ' > 0` there is `ε₁` such that at every lattice node with `h ≤ ε₁` the Airy window `(J, m, N', κ, μ)` of the chain (positions, chart data, pointwise matching
`Ŷ = κ g Ai + μ g Bi + O(δ³ ...)`, `|μ| ≤ C_μ (2/δ³) e^{-ξ₀/δ³}/δ`) satisfies `|κ² δ - 2| ≤ τ'`, `δ³ = h`: `|κ| = √2 N^{1/6}(1 + o(1))`.  For `τ = +1`, integer data this is the window form of
`hahn_chain_kappa_sharp` (`DiscreteAiryKappaSharpFinal`); the other three are new (the half-integer `3j` chain, and the `τ = -1` branch, the twisted chain `(-1)^k Ŷ_k`).

**Explicit bulk theorem** (`hahn_chain_bulk_explicit_*`): for every compact `[a, b] ⊂ (0, q_*)` and `t > 0` there is `ε` such that at every node with `h ≤ ε` there is a sign `s = ±1` with, for every site `q_k ∈ [a, b]`,
`|Y_k - s A(q_k) cos(Φ(q_k)/h - π/4)| ≤ t A(q_k)`, `A(q) = (2/√π)(q_*² - q²)^{-1/4}`, `Φ(q) = ∫_q^{q_*} arccos(|x|/√(1-t²)) dt` (`bkAmp`, `bkPhase`; `hrU 1 0 τ x t = τ x/√(1-t²) = |x|/√(1-t²)`).

**Claim class: proved.**  Numerics (mpmath, exact chain by backward recursion, `N = 800`, `(M, σ, x) = (0,0,1/2), (1,0,1/2)`): `Y_k / (A cos(Φ/h - π/4)) = 1 ± 10⁻³` at sites `0.15 q_* N ≤ k ≤ 0.85 q_* N`, `s = +1` in the natural gauge (numerical evidence only).
**Not formalised:** the sign `s` (equivalently the sign of `κ`; `κ` is an Airy-window coefficient and the lemma pins only `κ²`), the dependence of `ε₁, ε` on `x, M, σ` (constants existential; no uniformity in `x`), a rate in `τ'`, mixed
parities `(M+½, σ)`, the hard edges `x → 0, 1`.
-/

@[expose] public section

open Finset FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

lemma bkh_cs (x : ℝ) : (1 / Real.sqrt (rkS 1 0 x) + 1) = 2 := by
  have : rkS 1 0 x = 1 := by simp [rkS]
  rw [this, Real.sqrt_one]; norm_num

lemma bkh_turn_id {x : ℝ} (hx1 : |x| < 1) :
    1 - x ^ 2 = rkS 1 0 x * √(1 - x ^ 2) ^ 2 := by
  have hx : -1 < x ∧ x < 1 := abs_lt.1 hx1
  have h1 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have : rkS 1 0 x = 1 := by simp [rkS]
  rw [this, one_mul, Real.sq_sqrt h1.le]

/-- **`κ² δ → 2` for the integer `3j` chain: window form** (generic twist). -/
theorem bk_hahn_int_sharp (M σ : ℤ) (x : ℚ) (τ : ℝ) (u : ℤ → ℝ) (hxτ : (τ = 1 ∧ 0 < (x : ℝ)) ∨ (τ = -1 ∧ (x : ℝ) < 0))
    (hx1 : |(x : ℝ)| < 1) (hu : ∀ k, u k ^ 2 = 1)
    (hrowsAll : ∀ N : ℤ, 0 < N → ∀ k : ℤ, 1 ≤ k →
      jac (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ)))
        (hrCk 1 0 τ (x : ℝ) (M : ℝ) (σ : ℝ) (1 / (N : ℝ)))
        (fun j => u j * hahn3jY M σ N x j) k = 0) :
    ∃ (r Cmu ξ0 gmax gmin c1 c2 CA : ℝ), 0 < r ∧ r ≤ √(1 - (x : ℝ) ^ 2) / 4 ∧ 0 < CA ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧
      0 < gmin ∧ gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧
      ∀ τ' : ℝ, 0 < τ' → ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ (N : ℤ) (n : ℕ) (Y : ℤ → ℝ), max |M| |σ| < N ∧ (n : ℤ) < N - max |M| |σ| ∧ xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x →
        Y = (fun j => u j * hahn3jY M σ N x j) → 1 / (N : ℝ) ≤ ε1 →
        ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = 1 / (N : ℝ) ∧ ∃ (J m N' : ℤ) (κ μ : ℝ),
          RkWinAt 1 0 τ (x : ℝ) (√(1 - (x : ℝ) ^ 2)) Y (2 / δ ^ 3) r CA Cmu ξ0 gmin gmax c1 c2 δ J m N' κ μ ∧ |κ ^ 2 * δ - 2| ≤ τ' := by
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, δA, hm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hmpos, Hwin, Hsharp, -⟩ :=
    bk_hahn_int M σ x τ u hxτ hx1 hu hrowsAll
  refine ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ?_⟩
  intro τ' hτ'
  obtain ⟨ε1, hε1, HS⟩ := Hsharp τ' hτ'
  refine ⟨min ε1 (min hm (δA ^ 3)), lt_min hε1 (lt_min hmpos (by positivity)), ?_⟩
  intro N n Y hnode hY hNε
  obtain ⟨hN, hn, hxn⟩ := hnode
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
  have hε1' : 1 / (N : ℝ) ≤ ε1 := hNε.trans (min_le_left _ _)
  have hhm : 1 / (N : ℝ) ≤ hm := hNε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhA : 1 / (N : ℝ) ≤ δA ^ 3 := hNε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmem : bkFamHahn M σ x u hm (1 / (N : ℝ)) Y (N : ℝ) := ⟨by positivity, hhm, N, n, hN, hn, hxn, rfl, hY, rfl⟩
  obtain ⟨δ, hδ, hδ3, J, m, N', κ, μ, hW⟩ := Hwin _ _ _ hmem (by positivity) hhA
  refine ⟨δ, hδ, hδ3, J, m, N', κ, μ, ?_, HS _ _ _ hmem (by positivity) hε1' δ J m N' κ μ hδ hδ3 hW⟩
  rw [bkh_cs] at hW
  exact hW

/-- **Explicit bulk theorem for the integer `3j` chain** (generic twist; see the module docstring). -/
theorem bk_hahn_int_bulk (M σ : ℤ) (x : ℚ) (τ : ℝ) (u : ℤ → ℝ) (hxτ : (τ = 1 ∧ 0 < (x : ℝ)) ∨ (τ = -1 ∧ (x : ℝ) < 0))
    (hx1 : |(x : ℝ)| < 1) (hu : ∀ k, u k ^ 2 = 1)
    (hrowsAll : ∀ N : ℤ, 0 < N → ∀ k : ℤ, 1 ≤ k →
      jac (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ)))
        (hrCk 1 0 τ (x : ℝ) (M : ℝ) (σ : ℝ) (1 / (N : ℝ)))
        (fun j => u j * hahn3jY M σ N x j) k = 0) :
    ∀ a b : ℝ, 0 < a → a < b → b < √(1 - (x : ℝ) ^ 2) → ∀ t : ℝ, 0 < t → ∃ ε : ℝ, 0 < ε ∧
      ∀ (N : ℤ) (n : ℕ) (Y : ℤ → ℝ), max |M| |σ| < N ∧ (n : ℤ) < N - max |M| |σ| ∧ xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x →
        Y = (fun j => u j * hahn3jY M σ N x j) → 1 / (N : ℝ) ≤ ε →
        ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ k : ℤ, a ≤ ((k : ℝ) + 1 / 2) * (1 / (N : ℝ)) → ((k : ℝ) + 1 / 2) * (1 / (N : ℝ)) ≤ b →
          |Y k - s * bkAmp 1 0 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1 / 2) * (1 / (N : ℝ))) *
              Real.cos (bkPhase 1 0 τ (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1 / 2) * (1 / (N : ℝ))) / (1 / (N : ℝ)) - π / 4)| ≤
            t * bkAmp 1 0 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1 / 2) * (1 / (N : ℝ))) := by
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, δA, hm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hmpos, Hout⟩ :=
    bk_hahn_int M σ x τ u hxτ hx1 hu hrowsAll
  obtain ⟨hqs, hτ, hκ, hα, hβ, hturn⟩ := bkh_geom hxτ hx1
  have hS1 : rkS 1 0 (x : ℝ) = 1 := by simp [rkS]
  have hS : 0 < rkS 1 0 (x : ℝ) := by rw [hS1]; norm_num
  have hE := bk_explicit_of_out (zero_le_one : (0 : ℝ) ≤ 1) (le_rfl : (0 : ℝ) ≤ 0) hτ (bkh_turn_id hx1) hS hqs hα hβ
    (θ := 1 / 2) (q₀ := fun δ => δ ^ 3 / 2) (fun δ k => by unfold dlgQ; ring) h1 h2 h4 h5 Hout h11
  intro a b ha hab hbq t ht
  obtain ⟨ε, hε, HE⟩ := hE a b ha hab hbq t ht
  refine ⟨min ε hm, lt_min hε hmpos, ?_⟩
  intro N n Y hnode hY hNε
  obtain ⟨hN, hn, hxn⟩ := hnode
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
  have hmem : bkFamHahn M σ x u hm (1 / (N : ℝ)) Y (N : ℝ) :=
    ⟨by positivity, hNε.trans (min_le_right _ _), N, n, hN, hn, hxn, rfl, hY, rfl⟩
  obtain ⟨δ, -, -, s, hs, H⟩ := HE _ _ _ hmem (by positivity) (hNε.trans (min_le_left _ _))
  exact ⟨s, hs, H⟩

/-- **`κ² δ → 2` for the half-integer `3j` chain: window form** (generic twist). -/
theorem bk_hahn_half_sharp (M σ : ℤ) (x : ℚ) (τ : ℝ) (u : ℤ → ℝ) (hxτ : (τ = 1 ∧ 0 < (x : ℝ)) ∨ (τ = -1 ∧ (x : ℝ) < 0))
    (hx1 : |(x : ℝ)| < 1) (hu : ∀ k, u k ^ 2 = 1)
    (hrowsAll : ∀ N : ℤ, 0 ≤ N → ∀ k : ℤ, 1 ≤ k →
      jac (hrAkH 1 0 ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) (1 / ((N : ℝ) + 1 / 2)))
        (hrCkH 1 0 τ (x : ℝ) ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) (1 / ((N : ℝ) + 1 / 2)))
        (fun j => u j * hahn3jYH M σ N x j) k = 0) :
    ∃ (r Cmu ξ0 gmax gmin c1 c2 CA : ℝ), 0 < r ∧ r ≤ √(1 - (x : ℝ) ^ 2) / 4 ∧ 0 < CA ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧
      0 < gmin ∧ gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧
      ∀ τ' : ℝ, 0 < τ' → ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ (N : ℤ) (n : ℕ) (Y : ℤ → ℝ), halfLo M σ < N ∧ (n : ℤ) < N - halfLo M σ ∧ xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n = x →
        Y = (fun j => u j * hahn3jYH M σ N x j) → 1 / ((N : ℝ) + 1 / 2) ≤ ε1 →
        ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = 1 / ((N : ℝ) + 1 / 2) ∧ ∃ (J m N' : ℤ) (κ μ : ℝ),
          RkWinAtH 1 0 τ (x : ℝ) (√(1 - (x : ℝ) ^ 2)) Y (2 / δ ^ 3) r CA Cmu ξ0 gmin gmax c1 c2 δ J m N' κ μ ∧ |κ ^ 2 * δ - 2| ≤ τ' := by
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, δA, hm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hmpos, Hwin, Hsharp, -⟩ :=
    bk_hahn_half M σ x τ u hxτ hx1 hu hrowsAll
  refine ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ?_⟩
  intro τ' hτ'
  obtain ⟨ε1, hε1, HS⟩ := Hsharp τ' hτ'
  refine ⟨min ε1 (min hm (δA ^ 3)), lt_min hε1 (lt_min hmpos (by positivity)), ?_⟩
  intro N n Y hnode hY hNε
  obtain ⟨hN, hn, hxn⟩ := hnode
  have hNpos : (0 : ℝ) < ((N : ℝ) + 1 / 2) := by have h0 : (0 : ℝ) ≤ N := (by exact_mod_cast (le_trans (halfLo_nonneg M σ) hN.le)); linarith
  have hε1' : 1 / ((N : ℝ) + 1 / 2) ≤ ε1 := hNε.trans (min_le_left _ _)
  have hhm : 1 / ((N : ℝ) + 1 / 2) ≤ hm := hNε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhA : 1 / ((N : ℝ) + 1 / 2) ≤ δA ^ 3 := hNε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmem : bkFamHahnH M σ x u hm (1 / ((N : ℝ) + 1 / 2)) Y ((N : ℝ) + 1 / 2) := ⟨by positivity, hhm, N, n, hN, hn, hxn, rfl, hY, rfl⟩
  obtain ⟨δ, hδ, hδ3, J, m, N', κ, μ, hW⟩ := Hwin _ _ _ hmem (by positivity) hhA
  refine ⟨δ, hδ, hδ3, J, m, N', κ, μ, ?_, HS _ _ _ hmem (by positivity) hε1' δ J m N' κ μ hδ hδ3 hW⟩
  rw [bkh_cs] at hW
  exact hW

/-- **Explicit bulk theorem for the half-integer `3j` chain** (generic twist; see the module docstring). -/
theorem bk_hahn_half_bulk (M σ : ℤ) (x : ℚ) (τ : ℝ) (u : ℤ → ℝ) (hxτ : (τ = 1 ∧ 0 < (x : ℝ)) ∨ (τ = -1 ∧ (x : ℝ) < 0))
    (hx1 : |(x : ℝ)| < 1) (hu : ∀ k, u k ^ 2 = 1)
    (hrowsAll : ∀ N : ℤ, 0 ≤ N → ∀ k : ℤ, 1 ≤ k →
      jac (hrAkH 1 0 ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) (1 / ((N : ℝ) + 1 / 2)))
        (hrCkH 1 0 τ (x : ℝ) ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) (1 / ((N : ℝ) + 1 / 2)))
        (fun j => u j * hahn3jYH M σ N x j) k = 0) :
    ∀ a b : ℝ, 0 < a → a < b → b < √(1 - (x : ℝ) ^ 2) → ∀ t : ℝ, 0 < t → ∃ ε : ℝ, 0 < ε ∧
      ∀ (N : ℤ) (n : ℕ) (Y : ℤ → ℝ), halfLo M σ < N ∧ (n : ℤ) < N - halfLo M σ ∧ xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n = x →
        Y = (fun j => u j * hahn3jYH M σ N x j) → 1 / ((N : ℝ) + 1 / 2) ≤ ε →
        ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ k : ℤ, a ≤ ((k : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2)) → ((k : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2)) ≤ b →
          |Y k - s * bkAmp 1 0 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2))) *
              Real.cos (bkPhase 1 0 τ (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2))) / (1 / ((N : ℝ) + 1 / 2)) - π / 4)| ≤
            t * bkAmp 1 0 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2))) := by
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, δA, hm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hmpos, Hout⟩ :=
    bk_hahn_half M σ x τ u hxτ hx1 hu hrowsAll
  obtain ⟨hqs, hτ, hκ, hα, hβ, hturn⟩ := bkh_geom hxτ hx1
  have hS1 : rkS 1 0 (x : ℝ) = 1 := by simp [rkS]
  have hS : 0 < rkS 1 0 (x : ℝ) := by rw [hS1]; norm_num
  have hE := bk_explicit_of_out (zero_le_one : (0 : ℝ) ≤ 1) (le_rfl : (0 : ℝ) ≤ 0) hτ (bkh_turn_id hx1) hS hqs hα hβ
    (θ := 1) (q₀ := fun δ => δ ^ 3) (fun δ k => by unfold dlgQ; ring) h1 h2 h4 h5 Hout h11
  intro a b ha hab hbq t ht
  obtain ⟨ε, hε, HE⟩ := hE a b ha hab hbq t ht
  refine ⟨min ε hm, lt_min hε hmpos, ?_⟩
  intro N n Y hnode hY hNε
  obtain ⟨hN, hn, hxn⟩ := hnode
  have hNpos : (0 : ℝ) < ((N : ℝ) + 1 / 2) := by have h0 : (0 : ℝ) ≤ N := (by exact_mod_cast (le_trans (halfLo_nonneg M σ) hN.le)); linarith
  have hmem : bkFamHahnH M σ x u hm (1 / ((N : ℝ) + 1 / 2)) Y ((N : ℝ) + 1 / 2) :=
    ⟨by positivity, hNε.trans (min_le_right _ _), N, n, hN, hn, hxn, rfl, hY, rfl⟩
  obtain ⟨δ, -, -, s, hs, H⟩ := HE _ _ _ hmem (by positivity) (hNε.trans (min_le_left _ _))
  exact ⟨s, hs, H⟩

lemma bkh_neg_sq (j : ℤ) : ((-1 : ℝ) ^ j) ^ 2 = 1 := by
  have h1 : |(-1 : ℝ) ^ j| = 1 := by simp [abs_zpow]
  rw [← sq_abs, h1]; norm_num

lemma bkh_rows_int_pos (M σ : ℤ) (x : ℚ) (N : ℤ) (hN : 0 < N) (k : ℤ) (hk : 1 ≤ k) :
    jac (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (hrCk 1 0 1 (x : ℝ) (M : ℝ) (σ : ℝ) (1 / (N : ℝ)))
      (fun j => (fun _ : ℤ => (1 : ℝ)) j * hahn3jY M σ N x j) k = 0 := by
  have e : (fun j => (fun _ : ℤ => (1 : ℝ)) j * hahn3jY M σ N x j) = hahn3jY M σ N x := by
    funext j; simp
  rw [e]; exact hahn_class_chain M σ N x hN k hk

lemma bkh_rows_int_neg (M σ : ℤ) (x : ℚ) (N : ℤ) (hN : 0 < N) (k : ℤ) (hk : 1 ≤ k) :
    jac (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (hrCk 1 0 (-1) (x : ℝ) (M : ℝ) (σ : ℝ) (1 / (N : ℝ)))
      (fun j => (fun j : ℤ => (-1 : ℝ) ^ j) j * hahn3jY M σ N x j) k = 0 :=
  hahn_class_chain_neg M σ N x hN k hk

lemma bkh_rows_half_pos (M σ : ℤ) (x : ℚ) (N : ℤ) (hN : 0 ≤ N) (k : ℤ) (hk : 1 ≤ k) :
    jac (hrAkH 1 0 ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) (1 / ((N : ℝ) + 1 / 2)))
      (hrCkH 1 0 1 (x : ℝ) ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) (1 / ((N : ℝ) + 1 / 2)))
      (fun j => (fun _ : ℤ => (1 : ℝ)) j * hahn3jYH M σ N x j) k = 0 := by
  have e : (fun j => (fun _ : ℤ => (1 : ℝ)) j * hahn3jYH M σ N x j) = hahn3jYH M σ N x := by
    funext j; simp
  rw [e]; exact hahn_class_chain_half M σ N x hN k hk

lemma bkh_rows_half_neg (M σ : ℤ) (x : ℚ) (N : ℤ) (hN : 0 ≤ N) (k : ℤ) (hk : 1 ≤ k) :
    jac (hrAkH 1 0 ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) (1 / ((N : ℝ) + 1 / 2)))
      (hrCkH 1 0 (-1) (x : ℝ) ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) (1 / ((N : ℝ) + 1 / 2)))
      (fun j => (fun j : ℤ => (-1 : ℝ) ^ j) j * hahn3jYH M σ N x j) k = 0 := by
  have h := jac_twist_zero (hahn_class_chain_half M σ N x hN k hk)
  convert h using 2
  ext j
  unfold hrCkH; ring

/-- **`κ² δ → 2` for the integer `3j` chain, `τ = +1`** (window form; see the module docstring). -/
theorem hahn_chain_kappa_sharp_win (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ (r Cmu ξ0 gmax gmin c1 c2 CA : ℝ), 0 < r ∧ r ≤ √(1 - (x : ℝ) ^ 2) / 4 ∧ 0 < CA ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧
      0 < gmin ∧ gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧
      ∀ τ' : ℝ, 0 < τ' → ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ (N : ℤ) (n : ℕ), max |M| |σ| < N ∧ (n : ℤ) < N - max |M| |σ| ∧ xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x → 1 / (N : ℝ) ≤ ε1 →
        ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = 1 / (N : ℝ) ∧ ∃ (J m N' : ℤ) (κ μ : ℝ),
          RkWinAt 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (hahn3jY M σ N x) (2 / δ ^ 3) r CA Cmu ξ0 gmin gmax c1 c2 δ J m N' κ μ ∧
            |κ ^ 2 * δ - 2| ≤ τ' := by
  have hx : |(x : ℝ)| < 1 := abs_lt.2 ⟨by have h0 : (0 : ℝ) < x := (by exact_mod_cast hx0); linarith, by exact_mod_cast hx1⟩
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, H⟩ :=
    bk_hahn_int_sharp M σ x 1 (fun _ => 1) (Or.inl ⟨rfl, by exact_mod_cast hx0⟩) hx (fun _ => by norm_num) (bkh_rows_int_pos M σ x)
  refine ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, fun τ' hτ' => ?_⟩
  obtain ⟨ε1, hε1, H1⟩ := H τ' hτ'
  exact ⟨ε1, hε1, fun N n hnode hNε => H1 N n _ hnode (by funext j; simp) hNε⟩

/-- **Explicit bulk theorem for the integer `3j` chain, `τ = +1`** (see the module docstring). -/
theorem hahn_chain_bulk_explicit (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∀ a b : ℝ, 0 < a → a < b → b < √(1 - (x : ℝ) ^ 2) → ∀ t : ℝ, 0 < t → ∃ ε : ℝ, 0 < ε ∧
      ∀ (N : ℤ) (n : ℕ), max |M| |σ| < N ∧ (n : ℤ) < N - max |M| |σ| ∧ xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x → 1 / (N : ℝ) ≤ ε →
        ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ k : ℤ, a ≤ ((k : ℝ) + 1 / 2) * (1 / (N : ℝ)) → ((k : ℝ) + 1 / 2) * (1 / (N : ℝ)) ≤ b →
          |hahn3jY M σ N x k - s * bkAmp 1 0 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1 / 2) * (1 / (N : ℝ))) *
              Real.cos (bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1 / 2) * (1 / (N : ℝ))) / (1 / (N : ℝ)) - π / 4)| ≤
            t * bkAmp 1 0 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1 / 2) * (1 / (N : ℝ))) := by
  have hx : |(x : ℝ)| < 1 := abs_lt.2 ⟨by have h0 : (0 : ℝ) < x := (by exact_mod_cast hx0); linarith, by exact_mod_cast hx1⟩
  intro a b ha hab hbq t ht
  obtain ⟨ε, hε, H⟩ := bk_hahn_int_bulk M σ x 1 (fun _ => 1) (Or.inl ⟨rfl, by exact_mod_cast hx0⟩) hx (fun _ => by norm_num) (bkh_rows_int_pos M σ x) a b ha hab hbq t ht
  exact ⟨ε, hε, fun N n hnode hNε => H N n _ hnode (by funext j; simp) hNε⟩

/-- **`κ² δ → 2` for the twisted integer `3j` chain `(-1)^k Ŷ_k`, `τ = -1`** (window form; see the module docstring). -/
theorem hahn_chain_kappa_sharp_neg (M σ : ℤ) (x : ℚ) (hx0 : x < 0) (hx1 : -1 < x) :
    ∃ (r Cmu ξ0 gmax gmin c1 c2 CA : ℝ), 0 < r ∧ r ≤ √(1 - (x : ℝ) ^ 2) / 4 ∧ 0 < CA ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧
      0 < gmin ∧ gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧
      ∀ τ' : ℝ, 0 < τ' → ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ (N : ℤ) (n : ℕ), max |M| |σ| < N ∧ (n : ℤ) < N - max |M| |σ| ∧ xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x → 1 / (N : ℝ) ≤ ε1 →
        ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = 1 / (N : ℝ) ∧ ∃ (J m N' : ℤ) (κ μ : ℝ),
          RkWinAt 1 0 (-1) (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (fun j => (-1 : ℝ) ^ j * hahn3jY M σ N x j) (2 / δ ^ 3) r CA Cmu ξ0 gmin gmax c1 c2 δ J m N' κ μ ∧
            |κ ^ 2 * δ - 2| ≤ τ' := by
  have hx : |(x : ℝ)| < 1 := abs_lt.2 ⟨by exact_mod_cast hx1, by have h0 : (x : ℝ) < 0 := (by exact_mod_cast hx0); linarith⟩
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, H⟩ :=
    bk_hahn_int_sharp M σ x (-1) (fun j => (-1 : ℝ) ^ j) (Or.inr ⟨rfl, by exact_mod_cast hx0⟩) hx bkh_neg_sq (bkh_rows_int_neg M σ x)
  refine ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, fun τ' hτ' => ?_⟩
  obtain ⟨ε1, hε1, H1⟩ := H τ' hτ'
  exact ⟨ε1, hε1, fun N n hnode hNε => H1 N n _ hnode rfl hNε⟩

/-- **Explicit bulk theorem for the twisted integer `3j` chain `(-1)^k Ŷ_k`, `τ = -1`** (see the module docstring). -/
theorem hahn_chain_bulk_explicit_neg (M σ : ℤ) (x : ℚ) (hx0 : x < 0) (hx1 : -1 < x) :
    ∀ a b : ℝ, 0 < a → a < b → b < √(1 - (x : ℝ) ^ 2) → ∀ t : ℝ, 0 < t → ∃ ε : ℝ, 0 < ε ∧
      ∀ (N : ℤ) (n : ℕ), max |M| |σ| < N ∧ (n : ℤ) < N - max |M| |σ| ∧ xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x → 1 / (N : ℝ) ≤ ε →
        ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ k : ℤ, a ≤ ((k : ℝ) + 1 / 2) * (1 / (N : ℝ)) → ((k : ℝ) + 1 / 2) * (1 / (N : ℝ)) ≤ b →
          |(-1 : ℝ) ^ k * hahn3jY M σ N x k - s * bkAmp 1 0 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1 / 2) * (1 / (N : ℝ))) *
              Real.cos (bkPhase 1 0 (-1) (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1 / 2) * (1 / (N : ℝ))) / (1 / (N : ℝ)) - π / 4)| ≤
            t * bkAmp 1 0 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1 / 2) * (1 / (N : ℝ))) := by
  have hx : |(x : ℝ)| < 1 := abs_lt.2 ⟨by exact_mod_cast hx1, by have h0 : (x : ℝ) < 0 := (by exact_mod_cast hx0); linarith⟩
  intro a b ha hab hbq t ht
  obtain ⟨ε, hε, H⟩ := bk_hahn_int_bulk M σ x (-1) (fun j => (-1 : ℝ) ^ j) (Or.inr ⟨rfl, by exact_mod_cast hx0⟩) hx bkh_neg_sq (bkh_rows_int_neg M σ x) a b ha hab hbq t ht
  exact ⟨ε, hε, fun N n hnode hNε => H N n _ hnode rfl hNε⟩

/-- **`κ² δ → 2` for the half-integer `3j` chain, `τ = +1`** (window form; see the module docstring). -/
theorem hahn_chain_kappa_sharp_half (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ (r Cmu ξ0 gmax gmin c1 c2 CA : ℝ), 0 < r ∧ r ≤ √(1 - (x : ℝ) ^ 2) / 4 ∧ 0 < CA ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧
      0 < gmin ∧ gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧
      ∀ τ' : ℝ, 0 < τ' → ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ (N : ℤ) (n : ℕ), halfLo M σ < N ∧ (n : ℤ) < N - halfLo M σ ∧ xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n = x → 1 / ((N : ℝ) + 1 / 2) ≤ ε1 →
        ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = 1 / ((N : ℝ) + 1 / 2) ∧ ∃ (J m N' : ℤ) (κ μ : ℝ),
          RkWinAtH 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (hahn3jYH M σ N x) (2 / δ ^ 3) r CA Cmu ξ0 gmin gmax c1 c2 δ J m N' κ μ ∧
            |κ ^ 2 * δ - 2| ≤ τ' := by
  have hx : |(x : ℝ)| < 1 := abs_lt.2 ⟨by have h0 : (0 : ℝ) < x := (by exact_mod_cast hx0); linarith, by exact_mod_cast hx1⟩
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, H⟩ :=
    bk_hahn_half_sharp M σ x 1 (fun _ => 1) (Or.inl ⟨rfl, by exact_mod_cast hx0⟩) hx (fun _ => by norm_num) (bkh_rows_half_pos M σ x)
  refine ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, fun τ' hτ' => ?_⟩
  obtain ⟨ε1, hε1, H1⟩ := H τ' hτ'
  exact ⟨ε1, hε1, fun N n hnode hNε => H1 N n _ hnode (by funext j; simp) hNε⟩

/-- **Explicit bulk theorem for the half-integer `3j` chain, `τ = +1`** (see the module docstring). -/
theorem hahn_chain_bulk_explicit_half (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∀ a b : ℝ, 0 < a → a < b → b < √(1 - (x : ℝ) ^ 2) → ∀ t : ℝ, 0 < t → ∃ ε : ℝ, 0 < ε ∧
      ∀ (N : ℤ) (n : ℕ), halfLo M σ < N ∧ (n : ℤ) < N - halfLo M σ ∧ xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n = x → 1 / ((N : ℝ) + 1 / 2) ≤ ε →
        ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ k : ℤ, a ≤ ((k : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2)) → ((k : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2)) ≤ b →
          |hahn3jYH M σ N x k - s * bkAmp 1 0 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2))) *
              Real.cos (bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2))) / (1 / ((N : ℝ) + 1 / 2)) - π / 4)| ≤
            t * bkAmp 1 0 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2))) := by
  have hx : |(x : ℝ)| < 1 := abs_lt.2 ⟨by have h0 : (0 : ℝ) < x := (by exact_mod_cast hx0); linarith, by exact_mod_cast hx1⟩
  intro a b ha hab hbq t ht
  obtain ⟨ε, hε, H⟩ := bk_hahn_half_bulk M σ x 1 (fun _ => 1) (Or.inl ⟨rfl, by exact_mod_cast hx0⟩) hx (fun _ => by norm_num) (bkh_rows_half_pos M σ x) a b ha hab hbq t ht
  exact ⟨ε, hε, fun N n hnode hNε => H N n _ hnode (by funext j; simp) hNε⟩

/-- **`κ² δ → 2` for the twisted half-integer `3j` chain `(-1)^k Ŷ_k`, `τ = -1`** (window form; see the module docstring). -/
theorem hahn_chain_kappa_sharp_half_neg (M σ : ℤ) (x : ℚ) (hx0 : x < 0) (hx1 : -1 < x) :
    ∃ (r Cmu ξ0 gmax gmin c1 c2 CA : ℝ), 0 < r ∧ r ≤ √(1 - (x : ℝ) ^ 2) / 4 ∧ 0 < CA ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧
      0 < gmin ∧ gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧
      ∀ τ' : ℝ, 0 < τ' → ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ (N : ℤ) (n : ℕ), halfLo M σ < N ∧ (n : ℤ) < N - halfLo M σ ∧ xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n = x → 1 / ((N : ℝ) + 1 / 2) ≤ ε1 →
        ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = 1 / ((N : ℝ) + 1 / 2) ∧ ∃ (J m N' : ℤ) (κ μ : ℝ),
          RkWinAtH 1 0 (-1) (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (fun j => (-1 : ℝ) ^ j * hahn3jYH M σ N x j) (2 / δ ^ 3) r CA Cmu ξ0 gmin gmax c1 c2 δ J m N' κ μ ∧
            |κ ^ 2 * δ - 2| ≤ τ' := by
  have hx : |(x : ℝ)| < 1 := abs_lt.2 ⟨by exact_mod_cast hx1, by have h0 : (x : ℝ) < 0 := (by exact_mod_cast hx0); linarith⟩
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, H⟩ :=
    bk_hahn_half_sharp M σ x (-1) (fun j => (-1 : ℝ) ^ j) (Or.inr ⟨rfl, by exact_mod_cast hx0⟩) hx bkh_neg_sq (bkh_rows_half_neg M σ x)
  refine ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, fun τ' hτ' => ?_⟩
  obtain ⟨ε1, hε1, H1⟩ := H τ' hτ'
  exact ⟨ε1, hε1, fun N n hnode hNε => H1 N n _ hnode rfl hNε⟩

/-- **Explicit bulk theorem for the twisted half-integer `3j` chain `(-1)^k Ŷ_k`, `τ = -1`** (see the module docstring). -/
theorem hahn_chain_bulk_explicit_half_neg (M σ : ℤ) (x : ℚ) (hx0 : x < 0) (hx1 : -1 < x) :
    ∀ a b : ℝ, 0 < a → a < b → b < √(1 - (x : ℝ) ^ 2) → ∀ t : ℝ, 0 < t → ∃ ε : ℝ, 0 < ε ∧
      ∀ (N : ℤ) (n : ℕ), halfLo M σ < N ∧ (n : ℤ) < N - halfLo M σ ∧ xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n = x → 1 / ((N : ℝ) + 1 / 2) ≤ ε →
        ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ k : ℤ, a ≤ ((k : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2)) → ((k : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2)) ≤ b →
          |(-1 : ℝ) ^ k * hahn3jYH M σ N x k - s * bkAmp 1 0 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2))) *
              Real.cos (bkPhase 1 0 (-1) (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2))) / (1 / ((N : ℝ) + 1 / 2)) - π / 4)| ≤
            t * bkAmp 1 0 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2))) := by
  have hx : |(x : ℝ)| < 1 := abs_lt.2 ⟨by exact_mod_cast hx1, by have h0 : (x : ℝ) < 0 := (by exact_mod_cast hx0); linarith⟩
  intro a b ha hab hbq t ht
  obtain ⟨ε, hε, H⟩ := bk_hahn_half_bulk M σ x (-1) (fun j => (-1 : ℝ) ^ j) (Or.inr ⟨rfl, by exact_mod_cast hx0⟩) hx bkh_neg_sq (bkh_rows_half_neg M σ x) a b ha hab hbq t ht
  exact ⟨ε, hε, fun N n hnode hNε => H N n _ hnode rfl hNε⟩

/-- info: 'FormalResearch.Special.hahn_chain_kappa_sharp_win' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_kappa_sharp_win

/-- info: 'FormalResearch.Special.hahn_chain_bulk_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_bulk_explicit

/-- info: 'FormalResearch.Special.hahn_chain_kappa_sharp_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_kappa_sharp_neg

/-- info: 'FormalResearch.Special.hahn_chain_bulk_explicit_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_bulk_explicit_neg

/-- info: 'FormalResearch.Special.hahn_chain_kappa_sharp_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_kappa_sharp_half

/-- info: 'FormalResearch.Special.hahn_chain_bulk_explicit_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_bulk_explicit_half

/-- info: 'FormalResearch.Special.hahn_chain_kappa_sharp_half_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_kappa_sharp_half_neg

/-- info: 'FormalResearch.Special.hahn_chain_bulk_explicit_half_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_bulk_explicit_half_neg

end FormalResearch.Special
