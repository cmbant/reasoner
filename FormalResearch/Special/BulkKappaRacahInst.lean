module

public import FormalResearch.Special.BulkKappaRacah
public import FormalResearch.Special.BulkKappaHahnInst

/-!
# Explicit bulk form and zero localisation for the actual Wigner `6j` chain (integer and half-integer data, `τ = ±1`)

Instances of `bk_explicit_of_out` and `bk_zeros_of_out` for the `6j` families of `BulkKappaRacah`, for the geometric data of `racah_chain_kappa_sharp(_neg)`, `racah_chain_kappa_sharp_half(_neg)` (`RacahKappaSharpInst`,
`RacahKappaHSharpInst`): `α, β > 0`, `|x| < 1`, `(α - βx)(β - αx) < 0` (`τ = +1`) or `> 0` (`τ = -1`, twisted chain `(-1)^k Ŷ_k`), `P = 1/(4α²)`, `Q = 1/(4β²)`, `q_* = racahQs α β x`, and every finite Racah system with
`A h = α`, `B h = β`, `cos = x`.  For every compact `[a', b'] ⊂ (0, q_*)` and `t > 0` there is `ε` such that every such chain with `h ≤ ε` has a sign `s = ±1` with

`|Y_k - s A(q_k) cos(Φ(q_k)/h - π/4)| ≤ t A(q_k)`,  `A(q) = (2/√π)(s_R (q_*² - q²))^{-1/4}`,  `s_R = rkS P Q x = γ²/(4α²β²)` (`rk_racah_s`),  `Φ(q) = ∫_q^{q_*} arccos(hrU P Q τ x t) dt`,

for every site `q_k ∈ [a', b']` (`q_k = (k+½)h` integer data, `(k+1)h` half-integer data); and every sign change `Y_k Y_{k+1} ≤ 0` in the window has an integer `m` with
`Φ(q_{k+1})/h - C₀ h ≤ π(m - ¼) ≤ Φ(q_k)/h + C₀ h` (Bohr-Sommerfeld lattice up to `O(h)`).  This is the `6j` counterpart of `BulkKappaHahnInst`, `BulkKappaHahnZeros`.

Numerics (numerical evidence only; mpmath with the exact `6j` symbols from the Racah sum, `Σ_f Ŷ_f² = 4AB/(2C)` checked at small size; throw-away script, not committed; `(A, B, C) = k (A₀, B₀, C₀)`, `h = 1/k`, `k = 201, 801, 3201`):
the maximum over the sites `0.15 q_* ≤ q_k ≤ 0.85 q_*` of `|Ŷ_k - s A(q_k) cos(Φ(q_k)/h - π/4)| / A(q_k)` is, for the integer chains `m = n = 1` with `(A₀, B₀, C₀) = (2, 3, 3/2)` (`τ = +1`) and `(2, 2, 3/2)` (`τ = -1`, twisted),
`4.4e-3, 1.1e-3, 2.7e-4` and `4.3e-3, 1.1e-3, 2.8e-4`, and for the half-integer chains `m = n = 0` with `(11/4, 19/4, 7/2)` (`τ = +1`) and `(11/4, 11/4, 5/2)` (`τ = -1`, twisted), `1.3e-3, 3.3e-4, 8.4e-5` and
`1.4e-3, 3.6e-4` (`k = 201, 801`); in every case every sign change `Ŷ_kŶ_{k+1} ≤ 0` has a Bohr-Sommerfeld point `π(m' - ¼)` inside `[Φ(q_{k+1})/h, Φ(q_k)/h]`.

**Claim class: proved.**  **Not formalised:** the sign `s`, uniformity of `ε, C₀` in the data, the converse count of the zeros, the conversion of the phase window into `q`, mixed parities.
-/

@[expose] public section

open Finset FormalResearch.Racah FormalResearch.Racah.SixJ FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

/-- The turn identity and positivity of `s_R` for the centred Racah data (generic). -/
lemma bkr_geom {P Q τ x qs : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hτ : τ ^ 2 = 1) (hqs : 0 < qs) (hκ : 0 < 1 - τ * x)
    (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2) (hturn : Phi P Q τ x (qs ^ 2) = 0) :
    1 - x ^ 2 = rkS P Q x * qs ^ 2 ∧ 0 < rkS P Q x := by
  have hs := rk_turn_id hP hQ hτ hα hβ hturn
  have hx2 := rk_abs_x_lt hP hQ hτ hqs hα hβ hκ hturn
  refine ⟨hs, ?_⟩
  have : 0 < rkS P Q x * qs ^ 2 := by rw [← hs]; linarith
  by_contra hc; push Not at hc
  nlinarith only [this, mul_nonneg (neg_nonneg.2 hc) (sq_nonneg qs)]

/-- **Explicit bulk theorem for the integer `6j` chain** (generic twist; see the module docstring). -/
theorem bk_racah_int_bulk (α β x τ qs : ℝ) (m n : ℤ) (hα : 0 < α) (hβ : 0 < β) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
    (hκ : 0 < 1 - τ * x) (hαq : 0 < 1 - 1 / (4 * α ^ 2) * qs ^ 2) (hβq : 0 < 1 - 1 / (4 * β ^ 2) * qs ^ 2)
    (hturn : Phi (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x (qs ^ 2) = 0) (u : ℤ → ℝ) (hu : ∀ k, u k ^ 2 = 1)
    (hrowsAll : ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
      (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → wA (a : ℚ) (n : ℚ) * h = α →
      wB (b : ℚ) (m : ℚ) * h = β → cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
      ∀ k : ℤ, 1 ≤ k → jac (hrAk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (m : ℝ) (n : ℝ) h)
        (hrCk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x (m : ℝ) (n : ℝ) h) (fun j => u j * racah6jY a b c m n j) k = 0) :
    ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < qs → ∀ t : ℝ, 0 < t → ∃ ε : ℝ, 0 < ε ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
        ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ k : ℤ, a' ≤ ((k : ℝ) + 1 / 2) * h → ((k : ℝ) + 1 / 2) * h ≤ b' →
          |(fun j => u j * racah6jY a b c m n j) k - s * bkAmp (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x qs (((k : ℝ) + 1 / 2) * h) *
              Real.cos (bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x qs (((k : ℝ) + 1 / 2) * h) / h - π / 4)| ≤
            t * bkAmp (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x qs (((k : ℝ) + 1 / 2) * h) := by
  have hP : (0 : ℝ) ≤ 1 / (4 * α ^ 2) := by positivity
  have hQ : (0 : ℝ) ≤ 1 / (4 * β ^ 2) := by positivity
  obtain ⟨hs, hspos⟩ := bkr_geom hP hQ hτ hqs hκ hαq hβq hturn
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, δA, hm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hmpos, Hout⟩ :=
    bk_racah_int α β x τ qs m n hα hβ hqs hτ hκ hαq hβq hturn u hu hrowsAll
  have hE := bk_explicit_of_out hP hQ hτ hs hspos hqs hαq hβq
    (θ := 1 / 2) (q₀ := fun δ => δ ^ 3 / 2) (fun δ k => by unfold dlgQ; ring) h1 h2 h4 h5 Hout h11
  intro a' b' ha hab hbq t ht
  obtain ⟨ε, hε, HE⟩ := hE a' b' ha hab hbq t ht
  refine ⟨min ε hm, lt_min hε hmpos, ?_⟩
  intro a b c D' hsys i hc h hh hhε hAh hBh hx
  obtain ⟨δ, -, -, s, hs1, H⟩ := HE h _ _ ⟨hh, hhε.trans (min_le_right _ _), a, b, c, D', hsys, i, hc, hAh, hBh, hx, rfl, rfl⟩ hh
    (hhε.trans (min_le_left _ _))
  exact ⟨s, hs1, H⟩

/-- **Bulk zero localisation for the integer `6j` chain** (generic twist; see the module docstring). -/
theorem bk_racah_int_zeros (α β x τ qs : ℝ) (m n : ℤ) (hα : 0 < α) (hβ : 0 < β) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
    (hκ : 0 < 1 - τ * x) (hαq : 0 < 1 - 1 / (4 * α ^ 2) * qs ^ 2) (hβq : 0 < 1 - 1 / (4 * β ^ 2) * qs ^ 2)
    (hturn : Phi (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x (qs ^ 2) = 0) (u : ℤ → ℝ) (hu : ∀ k, u k ^ 2 = 1)
    (hrowsAll : ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
      (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → wA (a : ℚ) (n : ℚ) * h = α →
      wB (b : ℚ) (m : ℚ) * h = β → cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
      ∀ k : ℤ, 1 ≤ k → jac (hrAk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (m : ℝ) (n : ℝ) h)
        (hrCk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x (m : ℝ) (n : ℝ) h) (fun j => u j * racah6jY a b c m n j) k = 0) :
    ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < qs → ∃ ε C0 : ℝ, 0 < ε ∧ 0 < C0 ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
        ∀ k : ℤ, a' ≤ ((k : ℝ) + 1 / 2) * h → ((k : ℝ) + 1 + 1 / 2) * h ≤ b' →
          (fun j => u j * racah6jY a b c m n j) k * (fun j => u j * racah6jY a b c m n j) (k + 1) ≤ 0 →
          ∃ m' : ℤ, bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x qs (((k : ℝ) + 1 + 1 / 2) * h) / h - C0 * h ≤ π * ((m' : ℝ) - 1 / 4) ∧
            π * ((m' : ℝ) - 1 / 4) ≤ bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x qs (((k : ℝ) + 1 / 2) * h) / h + C0 * h := by
  have hP : (0 : ℝ) ≤ 1 / (4 * α ^ 2) := by positivity
  have hQ : (0 : ℝ) ≤ 1 / (4 * β ^ 2) := by positivity
  obtain ⟨hs, hspos⟩ := bkr_geom hP hQ hτ hqs hκ hαq hβq hturn
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, δA, hm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hmpos, Hout⟩ :=
    bk_racah_int α β x τ qs m n hα hβ hqs hτ hκ hαq hβq hturn u hu hrowsAll
  have hE := bk_zeros_of_out hP hQ hτ hs hspos hqs hαq hβq
    (θ := 1 / 2) (q₀ := fun δ => δ ^ 3 / 2) (fun δ k => by unfold dlgQ; ring) h1 h2 h4 h5 Hout h11
  intro a' b' ha hab hbq
  obtain ⟨ε, C0, hε, hC0, HE⟩ := hE a' b' ha hab hbq
  refine ⟨min ε hm, C0, lt_min hε hmpos, hC0, ?_⟩
  intro a b c D' hsys i hc h hh hhε hAh hBh hx
  exact HE h _ _ ⟨hh, hhε.trans (min_le_right _ _), a, b, c, D', hsys, i, hc, hAh, hBh, hx, rfl, rfl⟩ hh
    (hhε.trans (min_le_left _ _))

/-- **Explicit bulk theorem for the half-integer `6j` chain** (generic twist; see the module docstring). -/
theorem bk_racah_half_bulk (α β x τ qs : ℝ) (m n : ℤ) (hα : 0 < α) (hβ : 0 < β) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
    (hκ : 0 < 1 - τ * x) (hαq : 0 < 1 - 1 / (4 * α ^ 2) * qs ^ 2) (hβq : 0 < 1 - 1 / (4 * β ^ 2) * qs ^ 2)
    (hturn : Phi (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x (qs ^ 2) = 0) (u : ℤ → ℝ) (hu : ∀ k, u k ^ 2 = 1)
    (hrowsAll : ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D' → ∀ i : Fin (D' + 1),
      (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i → ∀ h : ℝ, 0 < h → wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α →
      wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = β → cosA (wA (a : ℚ) ((n : ℚ) + 1 / 2)) (wB (b : ℚ) ((m : ℚ) + 1 / 2)) (wC (c : ℚ)) = x →
      ∀ k : ℤ, 1 ≤ k → jac (hrAkH (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) h)
        (hrCkH (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) h) (fun j => u j * racah6jYH a b c m n j) k = 0) :
    ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < qs → ∀ t : ℝ, 0 < t → ∃ ε : ℝ, 0 < ε ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α → wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = β →
        cosA (wA (a : ℚ) ((n : ℚ) + 1 / 2)) (wB (b : ℚ) ((m : ℚ) + 1 / 2)) (wC (c : ℚ)) = x →
        ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ k : ℤ, a' ≤ ((k : ℝ) + 1) * h → ((k : ℝ) + 1) * h ≤ b' →
          |(fun j => u j * racah6jYH a b c m n j) k - s * bkAmp (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x qs (((k : ℝ) + 1) * h) *
              Real.cos (bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x qs (((k : ℝ) + 1) * h) / h - π / 4)| ≤
            t * bkAmp (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x qs (((k : ℝ) + 1) * h) := by
  have hP : (0 : ℝ) ≤ 1 / (4 * α ^ 2) := by positivity
  have hQ : (0 : ℝ) ≤ 1 / (4 * β ^ 2) := by positivity
  obtain ⟨hs, hspos⟩ := bkr_geom hP hQ hτ hqs hκ hαq hβq hturn
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, δA, hm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hmpos, Hout⟩ :=
    bk_racah_half α β x τ qs m n hα hβ hqs hτ hκ hαq hβq hturn u hu hrowsAll
  have hE := bk_explicit_of_out hP hQ hτ hs hspos hqs hαq hβq
    (θ := 1) (q₀ := fun δ => δ ^ 3) (fun δ k => by unfold dlgQ; ring) h1 h2 h4 h5 Hout h11
  intro a' b' ha hab hbq t ht
  obtain ⟨ε, hε, HE⟩ := hE a' b' ha hab hbq t ht
  refine ⟨min ε hm, lt_min hε hmpos, ?_⟩
  intro a b c D' hsys i hc h hh hhε hAh hBh hx
  obtain ⟨δ, -, -, s, hs1, H⟩ := HE h _ _ ⟨hh, hhε.trans (min_le_right _ _), a, b, c, D', hsys, i, hc, hAh, hBh, hx, rfl, rfl⟩ hh
    (hhε.trans (min_le_left _ _))
  exact ⟨s, hs1, H⟩

/-- **Bulk zero localisation for the half-integer `6j` chain** (generic twist; see the module docstring). -/
theorem bk_racah_half_zeros (α β x τ qs : ℝ) (m n : ℤ) (hα : 0 < α) (hβ : 0 < β) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
    (hκ : 0 < 1 - τ * x) (hαq : 0 < 1 - 1 / (4 * α ^ 2) * qs ^ 2) (hβq : 0 < 1 - 1 / (4 * β ^ 2) * qs ^ 2)
    (hturn : Phi (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x (qs ^ 2) = 0) (u : ℤ → ℝ) (hu : ∀ k, u k ^ 2 = 1)
    (hrowsAll : ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D' → ∀ i : Fin (D' + 1),
      (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i → ∀ h : ℝ, 0 < h → wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α →
      wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = β → cosA (wA (a : ℚ) ((n : ℚ) + 1 / 2)) (wB (b : ℚ) ((m : ℚ) + 1 / 2)) (wC (c : ℚ)) = x →
      ∀ k : ℤ, 1 ≤ k → jac (hrAkH (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) h)
        (hrCkH (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) h) (fun j => u j * racah6jYH a b c m n j) k = 0) :
    ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < qs → ∃ ε C0 : ℝ, 0 < ε ∧ 0 < C0 ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α → wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = β →
        cosA (wA (a : ℚ) ((n : ℚ) + 1 / 2)) (wB (b : ℚ) ((m : ℚ) + 1 / 2)) (wC (c : ℚ)) = x →
        ∀ k : ℤ, a' ≤ ((k : ℝ) + 1) * h → ((k : ℝ) + 1 + 1) * h ≤ b' →
          (fun j => u j * racah6jYH a b c m n j) k * (fun j => u j * racah6jYH a b c m n j) (k + 1) ≤ 0 →
          ∃ m' : ℤ, bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x qs (((k : ℝ) + 1 + 1) * h) / h - C0 * h ≤ π * ((m' : ℝ) - 1 / 4) ∧
            π * ((m' : ℝ) - 1 / 4) ≤ bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x qs (((k : ℝ) + 1) * h) / h + C0 * h := by
  have hP : (0 : ℝ) ≤ 1 / (4 * α ^ 2) := by positivity
  have hQ : (0 : ℝ) ≤ 1 / (4 * β ^ 2) := by positivity
  obtain ⟨hs, hspos⟩ := bkr_geom hP hQ hτ hqs hκ hαq hβq hturn
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, δA, hm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hmpos, Hout⟩ :=
    bk_racah_half α β x τ qs m n hα hβ hqs hτ hκ hαq hβq hturn u hu hrowsAll
  have hE := bk_zeros_of_out hP hQ hτ hs hspos hqs hαq hβq
    (θ := 1) (q₀ := fun δ => δ ^ 3) (fun δ k => by unfold dlgQ; ring) h1 h2 h4 h5 Hout h11
  intro a' b' ha hab hbq
  obtain ⟨ε, C0, hε, hC0, HE⟩ := hE a' b' ha hab hbq
  refine ⟨min ε hm, C0, lt_min hε hmpos, hC0, ?_⟩
  intro a b c D' hsys i hc h hh hhε hAh hBh hx
  exact HE h _ _ ⟨hh, hhε.trans (min_le_right _ _), a, b, c, D', hsys, i, hc, hAh, hBh, hx, rfl, rfl⟩ hh
    (hhε.trans (min_le_left _ _))

lemma bkr_rows_int_pos {α β x : ℝ} (hα : 0 < α) (hβ : 0 < β) (m n : ℤ) :
    ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
      (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → wA (a : ℚ) (n : ℚ) * h = α →
      wB (b : ℚ) (m : ℚ) * h = β → cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
      ∀ k : ℤ, 1 ≤ k → jac (hrAk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (m : ℝ) (n : ℝ) h)
        (hrCk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (m : ℝ) (n : ℝ) h)
        (fun j => (fun _ : ℤ => (1 : ℝ)) j * racah6jY a b c m n j) k = 0 := by
  intro a b c D' hsys i hc h hh hAh hBh hx k hk
  obtain ⟨hA, hB, -⟩ := rd_pos hα hβ a b c m n i hc hh hAh hBh
  have := racah_class_chain a b c m n h hh hA hB k hk
  rw [hAh, hBh, hx] at this
  have e : (fun j => (fun _ : ℤ => (1 : ℝ)) j * racah6jY a b c m n j) = racah6jY a b c m n := by funext j; simp
  rw [e]; exact this

lemma bkr_rows_int_neg {α β x : ℝ} (hα : 0 < α) (hβ : 0 < β) (m n : ℤ) :
    ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
      (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → wA (a : ℚ) (n : ℚ) * h = α →
      wB (b : ℚ) (m : ℚ) * h = β → cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
      ∀ k : ℤ, 1 ≤ k → jac (hrAk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (m : ℝ) (n : ℝ) h)
        (hrCk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (m : ℝ) (n : ℝ) h)
        (fun j => (fun j : ℤ => (-1 : ℝ) ^ j) j * racah6jY a b c m n j) k = 0 := by
  intro a b c D' hsys i hc h hh hAh hBh hx k hk
  obtain ⟨hA, hB, -⟩ := rd_pos hα hβ a b c m n i hc hh hAh hBh
  have := racah_class_chain_neg a b c m n h hh hA hB k hk
  rw [hAh, hBh, hx] at this
  exact this

lemma bkr_rows_half_pos {α β x : ℝ} (hα : 0 < α) (hβ : 0 < β) (m n : ℤ) :
    ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D' → ∀ i : Fin (D' + 1),
      (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i → ∀ h : ℝ, 0 < h →
      wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α → wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = β →
      cosA (wA (a : ℚ) ((n : ℚ) + 1 / 2)) (wB (b : ℚ) ((m : ℚ) + 1 / 2)) (wC (c : ℚ)) = x →
      ∀ k : ℤ, 1 ≤ k → jac (hrAkH (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) h)
        (hrCkH (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) h)
        (fun j => (fun _ : ℤ => (1 : ℝ)) j * racah6jYH a b c m n j) k = 0 := by
  intro a b c D' hsys i hc h hh hAh hBh hx k hk
  obtain ⟨hA, hB, -⟩ := rdH_pos hα hβ a b c m n i hc hh hAh hBh
  have := racah_class_chain_half a b c m n h hh hA hB k hk
  rw [hAh, hBh, hx] at this
  have e : (fun j => (fun _ : ℤ => (1 : ℝ)) j * racah6jYH a b c m n j) = racah6jYH a b c m n := by funext j; simp
  rw [e]; exact this

lemma bkr_rows_half_neg {α β x : ℝ} (hα : 0 < α) (hβ : 0 < β) (m n : ℤ) :
    ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D' → ∀ i : Fin (D' + 1),
      (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i → ∀ h : ℝ, 0 < h →
      wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α → wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = β →
      cosA (wA (a : ℚ) ((n : ℚ) + 1 / 2)) (wB (b : ℚ) ((m : ℚ) + 1 / 2)) (wC (c : ℚ)) = x →
      ∀ k : ℤ, 1 ≤ k → jac (hrAkH (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) h)
        (hrCkH (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) h)
        (fun j => (fun j : ℤ => (-1 : ℝ) ^ j) j * racah6jYH a b c m n j) k = 0 := by
  intro a b c D' hsys i hc h hh hAh hBh hx k hk
  obtain ⟨hA, hB, -⟩ := rdH_pos hα hβ a b c m n i hc hh hAh hBh
  have := racah_class_chain_half_neg a b c m n h hh hA hB k hk
  rw [hAh, hBh, hx] at this
  exact this

/-- **Explicit bulk theorem for the integer `6j` chain, `τ = +1`** (see the module docstring). -/
theorem racah_chain_bulk_explicit (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : (α - β * x) * (β - α * x) < 0) (m n : ℤ) :
    ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < racahQs α β x → ∀ t : ℝ, 0 < t → ∃ ε : ℝ, 0 < ε ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
        ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ k : ℤ, a' ≤ ((k : ℝ) + 1 / 2) * h → ((k : ℝ) + 1 / 2) * h ≤ b' →
          |racah6jY a b c m n k - s * bkAmp (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x (racahQs α β x) (((k : ℝ) + 1 / 2) * h) *
              Real.cos (bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (racahQs α β x) (((k : ℝ) + 1 / 2) * h) / h - π / 4)| ≤
            t * bkAmp (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x (racahQs α β x) (((k : ℝ) + 1 / 2) * h) := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_pos hα hβ hx1 hx2 hprod
  intro a' b' ha hab hbq t ht
  obtain ⟨ε, hε, H⟩ := bk_racah_int_bulk α β x 1 (racahQs α β x) m n hα hβ hqs (by norm_num) hκ hαq hβq hturn (fun _ => 1) (fun _ => by norm_num)
    (bkr_rows_int_pos hα hβ m n) a' b' ha hab hbq t ht
  refine ⟨ε, hε, fun a b c D' hs i hc h hh hεh hA hB hx => ?_⟩
  simpa only [one_mul] using H a b c D' hs i hc h hh hεh hA hB hx

/-- **Bulk zero localisation for the integer `6j` chain, `τ = +1`** (see the module docstring). -/
theorem racah_chain_bulk_zeros (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : (α - β * x) * (β - α * x) < 0) (m n : ℤ) :
    ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < racahQs α β x → ∃ ε C0 : ℝ, 0 < ε ∧ 0 < C0 ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
        ∀ k : ℤ, a' ≤ ((k : ℝ) + 1 / 2) * h → ((k : ℝ) + 1 + 1 / 2) * h ≤ b' → racah6jY a b c m n k * racah6jY a b c m n (k + 1) ≤ 0 →
          ∃ m' : ℤ, bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (racahQs α β x) (((k : ℝ) + 1 + 1 / 2) * h) / h - C0 * h ≤
              π * ((m' : ℝ) - 1 / 4) ∧
            π * ((m' : ℝ) - 1 / 4) ≤ bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (racahQs α β x) (((k : ℝ) + 1 / 2) * h) / h +
              C0 * h := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_pos hα hβ hx1 hx2 hprod
  intro a' b' ha hab hbq
  obtain ⟨ε, C0, hε, hC0, H⟩ := bk_racah_int_zeros α β x 1 (racahQs α β x) m n hα hβ hqs (by norm_num) hκ hαq hβq hturn (fun _ => 1) (fun _ => by norm_num)
    (bkr_rows_int_pos hα hβ m n) a' b' ha hab hbq
  refine ⟨ε, C0, hε, hC0, fun a b c D' hs i hc h hh hεh hA hB hx => ?_⟩
  simpa only [one_mul] using H a b c D' hs i hc h hh hεh hA hB hx

/-- **Explicit bulk theorem for the twisted integer `6j` chain `(-1)^k Ŷ_k`, `τ = -1`** (see the module docstring). -/
theorem racah_chain_bulk_explicit_neg (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : 0 < (α - β * x) * (β - α * x)) (m n : ℤ) :
    ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < racahQs α β x → ∀ t : ℝ, 0 < t → ∃ ε : ℝ, 0 < ε ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
        ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ k : ℤ, a' ≤ ((k : ℝ) + 1 / 2) * h → ((k : ℝ) + 1 / 2) * h ≤ b' →
          |((-1 : ℝ) ^ k * racah6jY a b c m n k) - s * bkAmp (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x (racahQs α β x) (((k : ℝ) + 1 / 2) * h) *
              Real.cos (bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (((k : ℝ) + 1 / 2) * h) / h - π / 4)| ≤
            t * bkAmp (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x (racahQs α β x) (((k : ℝ) + 1 / 2) * h) := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_neg hα hβ hx1 hx2 hprod
  intro a' b' ha hab hbq t ht
  obtain ⟨ε, hε, H⟩ := bk_racah_int_bulk α β x (-1) (racahQs α β x) m n hα hβ hqs (by norm_num) hκ hαq hβq hturn (fun j => (-1 : ℝ) ^ j) bkh_neg_sq
    (bkr_rows_int_neg hα hβ m n) a' b' ha hab hbq t ht
  exact ⟨ε, hε, H⟩

/-- **Bulk zero localisation for the twisted integer `6j` chain `(-1)^k Ŷ_k`, `τ = -1`** (see the module docstring). -/
theorem racah_chain_bulk_zeros_neg (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : 0 < (α - β * x) * (β - α * x)) (m n : ℤ) :
    ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < racahQs α β x → ∃ ε C0 : ℝ, 0 < ε ∧ 0 < C0 ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x →
        ∀ k : ℤ, a' ≤ ((k : ℝ) + 1 / 2) * h → ((k : ℝ) + 1 + 1 / 2) * h ≤ b' → ((-1 : ℝ) ^ k * racah6jY a b c m n k) * ((-1 : ℝ) ^ (k + 1) * racah6jY a b c m n (k + 1)) ≤ 0 →
          ∃ m' : ℤ, bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (((k : ℝ) + 1 + 1 / 2) * h) / h - C0 * h ≤
              π * ((m' : ℝ) - 1 / 4) ∧
            π * ((m' : ℝ) - 1 / 4) ≤ bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (((k : ℝ) + 1 / 2) * h) / h +
              C0 * h := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_neg hα hβ hx1 hx2 hprod
  intro a' b' ha hab hbq
  obtain ⟨ε, C0, hε, hC0, H⟩ := bk_racah_int_zeros α β x (-1) (racahQs α β x) m n hα hβ hqs (by norm_num) hκ hαq hβq hturn (fun j => (-1 : ℝ) ^ j) bkh_neg_sq
    (bkr_rows_int_neg hα hβ m n) a' b' ha hab hbq
  exact ⟨ε, C0, hε, hC0, H⟩

/-- **Explicit bulk theorem for the half-integer `6j` chain, `τ = +1`** (see the module docstring). -/
theorem racah_chain_bulk_explicit_half (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : (α - β * x) * (β - α * x) < 0) (m n : ℤ) :
    ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < racahQs α β x → ∀ t : ℝ, 0 < t → ∃ ε : ℝ, 0 < ε ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α → wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = β →
        cosA (wA (a : ℚ) ((n : ℚ) + 1 / 2)) (wB (b : ℚ) ((m : ℚ) + 1 / 2)) (wC (c : ℚ)) = x →
        ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ k : ℤ, a' ≤ ((k : ℝ) + 1) * h → ((k : ℝ) + 1) * h ≤ b' →
          |racah6jYH a b c m n k - s * bkAmp (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x (racahQs α β x) (((k : ℝ) + 1) * h) *
              Real.cos (bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (racahQs α β x) (((k : ℝ) + 1) * h) / h - π / 4)| ≤
            t * bkAmp (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x (racahQs α β x) (((k : ℝ) + 1) * h) := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_pos hα hβ hx1 hx2 hprod
  intro a' b' ha hab hbq t ht
  obtain ⟨ε, hε, H⟩ := bk_racah_half_bulk α β x 1 (racahQs α β x) m n hα hβ hqs (by norm_num) hκ hαq hβq hturn (fun _ => 1) (fun _ => by norm_num)
    (bkr_rows_half_pos hα hβ m n) a' b' ha hab hbq t ht
  refine ⟨ε, hε, fun a b c D' hs i hc h hh hεh hA hB hx => ?_⟩
  simpa only [one_mul] using H a b c D' hs i hc h hh hεh hA hB hx

/-- **Bulk zero localisation for the half-integer `6j` chain, `τ = +1`** (see the module docstring). -/
theorem racah_chain_bulk_zeros_half (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : (α - β * x) * (β - α * x) < 0) (m n : ℤ) :
    ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < racahQs α β x → ∃ ε C0 : ℝ, 0 < ε ∧ 0 < C0 ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α → wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = β →
        cosA (wA (a : ℚ) ((n : ℚ) + 1 / 2)) (wB (b : ℚ) ((m : ℚ) + 1 / 2)) (wC (c : ℚ)) = x →
        ∀ k : ℤ, a' ≤ ((k : ℝ) + 1) * h → ((k : ℝ) + 1 + 1) * h ≤ b' → racah6jYH a b c m n k * racah6jYH a b c m n (k + 1) ≤ 0 →
          ∃ m' : ℤ, bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (racahQs α β x) (((k : ℝ) + 1 + 1) * h) / h - C0 * h ≤
              π * ((m' : ℝ) - 1 / 4) ∧
            π * ((m' : ℝ) - 1 / 4) ≤ bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (racahQs α β x) (((k : ℝ) + 1) * h) / h +
              C0 * h := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_pos hα hβ hx1 hx2 hprod
  intro a' b' ha hab hbq
  obtain ⟨ε, C0, hε, hC0, H⟩ := bk_racah_half_zeros α β x 1 (racahQs α β x) m n hα hβ hqs (by norm_num) hκ hαq hβq hturn (fun _ => 1) (fun _ => by norm_num)
    (bkr_rows_half_pos hα hβ m n) a' b' ha hab hbq
  refine ⟨ε, C0, hε, hC0, fun a b c D' hs i hc h hh hεh hA hB hx => ?_⟩
  simpa only [one_mul] using H a b c D' hs i hc h hh hεh hA hB hx

/-- **Explicit bulk theorem for the twisted half-integer `6j` chain `(-1)^k Ŷ_k`, `τ = -1`** (see the module docstring). -/
theorem racah_chain_bulk_explicit_half_neg (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : 0 < (α - β * x) * (β - α * x)) (m n : ℤ) :
    ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < racahQs α β x → ∀ t : ℝ, 0 < t → ∃ ε : ℝ, 0 < ε ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α → wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = β →
        cosA (wA (a : ℚ) ((n : ℚ) + 1 / 2)) (wB (b : ℚ) ((m : ℚ) + 1 / 2)) (wC (c : ℚ)) = x →
        ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ k : ℤ, a' ≤ ((k : ℝ) + 1) * h → ((k : ℝ) + 1) * h ≤ b' →
          |((-1 : ℝ) ^ k * racah6jYH a b c m n k) - s * bkAmp (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x (racahQs α β x) (((k : ℝ) + 1) * h) *
              Real.cos (bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (((k : ℝ) + 1) * h) / h - π / 4)| ≤
            t * bkAmp (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x (racahQs α β x) (((k : ℝ) + 1) * h) := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_neg hα hβ hx1 hx2 hprod
  intro a' b' ha hab hbq t ht
  obtain ⟨ε, hε, H⟩ := bk_racah_half_bulk α β x (-1) (racahQs α β x) m n hα hβ hqs (by norm_num) hκ hαq hβq hturn (fun j => (-1 : ℝ) ^ j) bkh_neg_sq
    (bkr_rows_half_neg hα hβ m n) a' b' ha hab hbq t ht
  exact ⟨ε, hε, H⟩

/-- **Bulk zero localisation for the twisted half-integer `6j` chain `(-1)^k Ŷ_k`, `τ = -1`** (see the module docstring). -/
theorem racah_chain_bulk_zeros_half_neg (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : 0 < (α - β * x) * (β - α * x)) (m n : ℤ) :
    ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < racahQs α β x → ∃ ε C0 : ℝ, 0 < ε ∧ 0 < C0 ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α → wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = β →
        cosA (wA (a : ℚ) ((n : ℚ) + 1 / 2)) (wB (b : ℚ) ((m : ℚ) + 1 / 2)) (wC (c : ℚ)) = x →
        ∀ k : ℤ, a' ≤ ((k : ℝ) + 1) * h → ((k : ℝ) + 1 + 1) * h ≤ b' → ((-1 : ℝ) ^ k * racah6jYH a b c m n k) * ((-1 : ℝ) ^ (k + 1) * racah6jYH a b c m n (k + 1)) ≤ 0 →
          ∃ m' : ℤ, bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (((k : ℝ) + 1 + 1) * h) / h - C0 * h ≤
              π * ((m' : ℝ) - 1 / 4) ∧
            π * ((m' : ℝ) - 1 / 4) ≤ bkPhase (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x) (((k : ℝ) + 1) * h) / h +
              C0 * h := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_neg hα hβ hx1 hx2 hprod
  intro a' b' ha hab hbq
  obtain ⟨ε, C0, hε, hC0, H⟩ := bk_racah_half_zeros α β x (-1) (racahQs α β x) m n hα hβ hqs (by norm_num) hκ hαq hβq hturn (fun j => (-1 : ℝ) ^ j) bkh_neg_sq
    (bkr_rows_half_neg hα hβ m n) a' b' ha hab hbq
  exact ⟨ε, C0, hε, hC0, H⟩

/-- info: 'FormalResearch.Special.racah_chain_bulk_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.racah_chain_bulk_explicit

/-- info: 'FormalResearch.Special.racah_chain_bulk_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.racah_chain_bulk_zeros

/-- info: 'FormalResearch.Special.racah_chain_bulk_explicit_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.racah_chain_bulk_explicit_neg

/-- info: 'FormalResearch.Special.racah_chain_bulk_zeros_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.racah_chain_bulk_zeros_neg

/-- info: 'FormalResearch.Special.racah_chain_bulk_explicit_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.racah_chain_bulk_explicit_half

/-- info: 'FormalResearch.Special.racah_chain_bulk_zeros_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.racah_chain_bulk_zeros_half

/-- info: 'FormalResearch.Special.racah_chain_bulk_explicit_half_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.racah_chain_bulk_explicit_half_neg

/-- info: 'FormalResearch.Special.racah_chain_bulk_zeros_half_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.racah_chain_bulk_zeros_half_neg

/-- info: 'FormalResearch.Special.bk_racah_int_bulk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bk_racah_int_bulk

/-- info: 'FormalResearch.Special.bk_racah_int_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bk_racah_int_zeros

/-- info: 'FormalResearch.Special.bk_racah_half_bulk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bk_racah_half_bulk

/-- info: 'FormalResearch.Special.bk_racah_half_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bk_racah_half_zeros

end FormalResearch.Special
