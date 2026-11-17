module

public import FormalResearch.Special.RacahKappaHRacah

/-!
# `κ² δ → 2` for the actual half-integer Wigner `6j` chain

`racah_chain_kappa_sharp_half` (`τ = +1`, natural gauge) and `racah_chain_kappa_sharp_half_neg` (`τ = -1`, the twisted chain `(-1)^k Ŷ_k`): for the geometric data of `racah_chain_airy_geom_half_pos/_neg`, the window amplitude `κ` of the Langer
matching on the shifted lattice (`RkWinAtH`) satisfies `|κ² δ - 2| ≤ τ'` for every `τ' > 0` once `h = δ³ ≤ ε₁(τ')`.  Half-integer analogue of `racah_chain_kappa_sharp`.

**Claim class: proved** (`m, n` fixed integers labelling `m + ½`, `n + ½`; `κ` is the window amplitude, its sign is not asserted; mixed parities are not covered).

**Quantifiers.**  As in `RacahKappaSharpInst`: `(α, β, x, m, n)` fixed first, then the window constants (depending on these only), then for each `τ' > 0` an `ε₁(τ'; α, β, x, m, n)` that works for every finite half-integer Racah system
with the exact equalities `A h = α`, `B h = β`, `cos = x` (here `A = a + (n + 3/2)/2`, `B = b + (m + 3/2)/2`, `C = c + ½`) and every `0 < h ≤ ε₁`.  `κ` is the Airy coefficient of the actual chain `racah6jYH` (rank `f = k + ½`,
site `q_k = (k + 1) h`, versus `(k + ½) h` for integer data), pinned by the window as in the integer case.  Satisfiable with `h → 0`, e.g. (exact, scaling by `s ≡ 1 (mod 4)`) `x = 11/21`, `(4A, 4B, 2C) = s (3, 7, 3)`, `m = n = 0`,
`τ = +1`, and `x = 7/25`, `A = B`, `(4A, 2C) = s (5, 3)`, `m = n = 0`, `s ≡ 3 (mod 4)`, `τ = -1`.

**Numerical evidence (not part of the proof; as in `RacahKappaSharpInst`, half-integer chain checked against the Racah formula at `m' = m + ½`).**  `|κ²δ - 2| ≤ 3·10⁻³` at `h = 1/150` and `≤ 10⁻⁴` at `h = 1/2400`, both `τ`;
using the integer lattice `(k + ½) h` instead of `(k + 1) h` in the chart gives a visibly wrong fit (relative residual `0.1` instead of `10⁻⁴`).

**Not formalised.**  (i) The sign of `κ`.  (ii) Uniformity in `(α, β, x, m, n)`.  (iii) `x`, `A h`, `B h` only approximately equal to the fixed data.  (iv) Mixed-parity labels (half-integer `a, b, c` with integer `m, n`, etc.).
(v) The Hahn half-integer `κ` is not done here; it is `hahn_chain_kappa_sharp_half`, `_half_neg` (`BulkKappaHahnInst`, window form).
-/

@[expose] public section

open FormalResearch.Racah FormalResearch.Racah.SixJ FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **Sharp amplitude for the half-integer `6j` chain, `τ = +1`.** -/
theorem racah_chain_kappa_sharp_half (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : (α - β * x) * (β - α * x) < 0) (m n : ℤ) :
    ∃ (r Cmu ξ0 gmax gmin c1 c2 CA cs : ℝ), 0 < r ∧ r ≤ racahQs α β x / 4 ∧ 0 < CA ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧
      0 < gmin ∧ gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧ 0 ≤ cs ∧
      ∀ τ' : ℝ, 0 < τ' → ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ (a b c : ℤ) (D' : ℕ),
        RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i → ∀ h : ℝ, 0 < h → h ≤ ε1 →
        wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α → wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = β →
        cosA (wA (a : ℚ) ((n : ℚ) + 1 / 2)) (wB (b : ℚ) ((m : ℚ) + 1 / 2)) (wC (c : ℚ)) = x →
        ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = h ∧ ∃ (J m' N : ℤ) (κ μ : ℝ),
          RkWinAtH (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (racahQs α β x) (racah6jYH a b c m n) (cs / δ ^ 3) r CA Cmu ξ0
            gmin gmax c1 c2 δ J m' N κ μ ∧ |κ ^ 2 * δ - 2| ≤ τ' := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_pos hα hβ hx1 hx2 hprod
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, cs, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, H⟩ :=
    rk_racah_sharp_genH α β x 1 (racahQs α β x) m n hα hβ hqs (by norm_num) hκ hαq hβq hturn (fun _ => 1) (fun _ => by norm_num)
      (by
        intro a b c D' hsys i hc h hh hAh hBh hx k hk
        obtain ⟨hA, hB, -⟩ := rdH_pos hα hβ a b c m n i hc hh hAh hBh
        have := racah_class_chain_half a b c m n h hh hA hB k hk
        rw [hAh, hBh, hx] at this
        have e : (fun j => (fun _ : ℤ => (1 : ℝ)) j * racah6jYH a b c m n j) = racah6jYH a b c m n := by
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

/-- **Sharp amplitude for the half-integer `6j` chain, `τ = -1`** (the twisted chain `(-1)^k Ŷ_k`). -/
theorem racah_chain_kappa_sharp_half_neg (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : 0 < (α - β * x) * (β - α * x)) (m n : ℤ) :
    ∃ (r Cmu ξ0 gmax gmin c1 c2 CA cs : ℝ), 0 < r ∧ r ≤ racahQs α β x / 4 ∧ 0 < CA ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧
      0 < gmin ∧ gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧ 0 ≤ cs ∧
      ∀ τ' : ℝ, 0 < τ' → ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ (a b c : ℤ) (D' : ℕ),
        RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i → ∀ h : ℝ, 0 < h → h ≤ ε1 →
        wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α → wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = β →
        cosA (wA (a : ℚ) ((n : ℚ) + 1 / 2)) (wB (b : ℚ) ((m : ℚ) + 1 / 2)) (wC (c : ℚ)) = x →
        ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = h ∧ ∃ (J m' N : ℤ) (κ μ : ℝ),
          RkWinAtH (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (fun j => (-1 : ℝ) ^ j * racah6jYH a b c m n j)
            (cs / δ ^ 3) r CA Cmu ξ0 gmin gmax c1 c2 δ J m' N κ μ ∧ |κ ^ 2 * δ - 2| ≤ τ' := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_neg hα hβ hx1 hx2 hprod
  exact rk_racah_sharp_genH α β x (-1) (racahQs α β x) m n hα hβ hqs (by norm_num) hκ hαq hβq hturn (fun j => (-1 : ℝ) ^ j)
    (fun j => by
      have h1 : |(-1 : ℝ) ^ j| = 1 := by simp [abs_zpow]
      rw [← sq_abs, h1]; norm_num)
    (by
      intro a b c D' hsys i hc h hh hAh hBh hx k hk
      obtain ⟨hA, hB, -⟩ := rdH_pos hα hβ a b c m n i hc hh hAh hBh
      have := racah_class_chain_half_neg a b c m n h hh hA hB k hk
      rw [hAh, hBh, hx] at this
      exact this)

/-- info: 'FormalResearch.Special.racah_chain_kappa_sharp_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.racah_chain_kappa_sharp_half

/-- info: 'FormalResearch.Special.racah_chain_kappa_sharp_half_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.racah_chain_kappa_sharp_half_neg

end FormalResearch.Special
