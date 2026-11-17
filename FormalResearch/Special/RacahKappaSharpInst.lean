module

public import FormalResearch.Special.RacahKappaRacah

/-!
# `κ² δ → 2` for the actual Wigner `6j` chain (integer data)

`racah_chain_kappa_sharp` (`τ = +1`, natural gauge) and `racah_chain_kappa_sharp_neg` (`τ = -1`, the twisted chain `(-1)^k Ŷ_k`): for the geometric data of `racah_chain_airy_full_pos/_neg`, the window amplitude `κ` of the Langer
matching (`RkWinAt`) satisfies `|κ² δ - 2| ≤ τ'` for every `τ' > 0` once `h = δ³ ≤ ε₁(τ')`.  This is the Racah analogue of `hahn_chain_kappa_sharp`.

**Claim class: proved** (integer data, `m, n` fixed; `κ` is the window amplitude, its sign is not asserted; half-integer data is in `RacahKappaHSharpInst`).

**Quantifiers.**  `(α, β, x, m, n)` are fixed first (`α, β > 0`, `|x| < 1`, `τ = +1` iff `(α - βx)(β - αx) < 0`); then the window constants `r, C_μ, ξ₀, g_min, g_max, c₁, c₂, C_A, c_s` are chosen
(depending on `(α, β, x, m, n)` only); then, for every `τ' > 0`, `ε₁ = ε₁(τ'; α, β, x, m, n) > 0`; the conclusion holds for **every** finite Racah system `(a, b, c, D')` with `A h = α`, `B h = β`,
`cos = x` (these three equalities are exact hypotheses) and every `0 < h ≤ ε₁`: `ε₁` does not depend on the system or on `h`.  `κ` is pinned to the chain: it is the Airy coefficient of the actual Wigner `6j` solution
`Y = racah6jY a b c m n` (resp. `(-1)^k Y_k`; Gauss-weight normalisation `Σ Y² = 4AB/(2C)`) on a window of `≥ 2` lattice sites (`Y_k = κ g Ai(X_k) + μ g Bi(X_k) + O(δ³ ...)` with `|μ| ≤ C_μ Y_max e^{-ξ₀/h}/δ`), so it
is determined up to a relative `O(δ³)`.  The hypotheses are satisfiable along sequences with `h → 0`, e.g. (exact, scaling by odd `s`) `x = 1/5`, `(2A, 2B, 2C) = s (7, 60, 59)`, `(m, n) = (1, 0)`, `τ = +1`, and
`x = 1/2`, `A = B = C`, `m = n = 0`, `τ = -1`.

**Numerical evidence (not part of the proof; mpmath, 60 digits; chain from the closed-form rows by backward recursion from the hard edge with Gauss normalisation, rows and normalisation checked against the Racah formula;
Langer chart `X = ζ/δ²`, `g = (|ζ|/(|u²-1| A²))^{1/4}`, least-squares `κ` on the sites with `X ∈ [-3, 1/2]`).**  `|κ²δ - 2| ≤ 3·10⁻³` at `h = 1/150` and `≤ 10⁻⁴` at `h = 1/2400`, both `τ`,
`(m, n) ∈ {(1, 0), (2, -1), (0, 0)}`, `α = 1`, `β/α ∈ {1, 1.3, 2, 60/7}`.

**Not formalised.**  (i) The sign of `κ` (equivalently the `O(1)` phase of the Airy window, `(-1)^{#nodes}`).  (ii) Uniformity of `ε₁` and of the constants in `(α, β, x, m, n)`.  (iii) `x` only approximately
(`|cos - x| = O(h)`) and `A h = α` only approximately: the exact equalities are hypotheses.  (iv) Mixed-parity labels.  (v) `q`-Racah.
-/

@[expose] public section

open FormalResearch.Racah FormalResearch.Racah.SixJ FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **Sharp amplitude for the `6j` chain, `τ = +1`.** -/
theorem racah_chain_kappa_sharp (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : (α - β * x) * (β - α * x) < 0) (m n : ℤ) :
    ∃ (r Cmu ξ0 gmax gmin c1 c2 CA cs : ℝ), 0 < r ∧ r ≤ racahQs α β x / 4 ∧ 0 < CA ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧
      0 < gmin ∧ gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧ 0 ≤ cs ∧
      ∀ τ' : ℝ, 0 < τ' → ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ (a b c : ℤ) (D' : ℕ),
        RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → h ≤ ε1 →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
        ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = h ∧ ∃ (J m' N : ℤ) (κ μ : ℝ),
          RkWinAt (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (racahQs α β x) (racah6jY a b c m n) (cs / δ ^ 3) r CA Cmu ξ0
            gmin gmax c1 c2 δ J m' N κ μ ∧ |κ ^ 2 * δ - 2| ≤ τ' := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_pos hα hβ hx1 hx2 hprod
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, cs, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, H⟩ :=
    rk_racah_sharp_gen α β x 1 (racahQs α β x) m n hα hβ hqs (by norm_num) hκ hαq hβq hturn (fun _ => 1) (fun _ => by norm_num)
      (by
        intro a b c D' hsys i hc h hh hAh hBh hx k hk
        obtain ⟨hA, hB, -⟩ := rd_pos hα hβ a b c m n i hc hh hAh hBh
        have := racah_class_chain a b c m n h hh hA hB k hk
        rw [hAh, hBh, hx] at this
        have e : (fun j => (fun _ : ℤ => (1 : ℝ)) j * racah6jY a b c m n j) = racah6jY a b c m n := by
          funext j; simp
        rw [e]
        exact this)
  refine ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, cs, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_⟩
  intro τ' hτ'
  obtain ⟨ε1, hε1, H'⟩ := H τ' hτ'
  refine ⟨ε1, hε1, ?_⟩
  intro a b c D' hsys i hc h hh hhε hAh hBh hx
  obtain ⟨δ, hδ, hδ3, J, m', N, κ, μ, hW, hk⟩ := H' a b c D' hsys i hc h hh hhε hAh hBh hx
  refine ⟨δ, hδ, hδ3, J, m', N, κ, μ, ?_, hk⟩
  simpa only [one_mul] using hW

/-- **Sharp amplitude for the `6j` chain, `τ = -1`** (the twisted chain `(-1)^k Ŷ_k`). -/
theorem racah_chain_kappa_sharp_neg (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : 0 < (α - β * x) * (β - α * x)) (m n : ℤ) :
    ∃ (r Cmu ξ0 gmax gmin c1 c2 CA cs : ℝ), 0 < r ∧ r ≤ racahQs α β x / 4 ∧ 0 < CA ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧
      0 < gmin ∧ gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧ 0 ≤ cs ∧
      ∀ τ' : ℝ, 0 < τ' → ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ (a b c : ℤ) (D' : ℕ),
        RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → h ≤ ε1 →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
        ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = h ∧ ∃ (J m' N : ℤ) (κ μ : ℝ),
          RkWinAt (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (fun j => (-1 : ℝ) ^ j * racah6jY a b c m n j)
            (cs / δ ^ 3) r CA Cmu ξ0 gmin gmax c1 c2 δ J m' N κ μ ∧ |κ ^ 2 * δ - 2| ≤ τ' := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_neg hα hβ hx1 hx2 hprod
  exact rk_racah_sharp_gen α β x (-1) (racahQs α β x) m n hα hβ hqs (by norm_num) hκ hαq hβq hturn (fun j => (-1 : ℝ) ^ j)
    (fun j => by
      have h1 : |(-1 : ℝ) ^ j| = 1 := by simp [abs_zpow]
      rw [← sq_abs, h1]; norm_num)
    (by
      intro a b c D' hsys i hc h hh hAh hBh hx k hk
      obtain ⟨hA, hB, -⟩ := rd_pos hα hβ a b c m n i hc hh hAh hBh
      have := racah_class_chain_neg a b c m n h hh hA hB k hk
      rw [hAh, hBh, hx] at this
      exact this)

/-- info: 'FormalResearch.Special.racah_chain_kappa_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.racah_chain_kappa_sharp

/-- info: 'FormalResearch.Special.racah_chain_kappa_sharp_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.racah_chain_kappa_sharp_neg

end FormalResearch.Special
