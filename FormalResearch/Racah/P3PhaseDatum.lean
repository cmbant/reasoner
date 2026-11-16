module

public import FormalResearch.Racah.P2AnalyticNLO3j
public import FormalResearch.Racah.P2AnalyticNLO6j

/-!
# The fixed-rank datum `c(x) = -J₂(0,x)` for the Hahn and Racah chains (Weyl P3)

Source: `Weyl/P3/paper/weyl_midpoint_semiclassics_appendices.tex`, proof of
`cor:3j-phase-exactness` and `cor:6j-phase-exactness` (the paragraph "the fixed-rank datum"), as
used in `weyl_midpoint_semiclassics.tex` (`thm:general-phase-exactness`, `cor:3j-phase-exactness`,
`cor:6j-phase-exactness`, `rem:flux-gauss`).  The statement `c(x) = -J₂(0,x)` is `δ_fl = 0`.

## What is formalised

The paper's argument: the `t = h²` coefficient of the natural-gauge exact chain solution `Ŷ_k` and that
of the second-order pullback `Û^{[2]}_k` differ by `c(x) d̂_k`; `Û^{[2]}_k` has `t`-coefficient
`√(2k+1) 𝒬_{2,k} d_k`, so `c(x) d_k = (t-coefficient of Y_k) - 𝒬_{2,k} d_k`; the `t`-coefficient of `Y_k` is
the exact coefficient of Paper II (`thm:3jNLO` for Hahn, `thm:6jclosedcorrection` for Racah), already
formalised in `P2AnalyticNLO3j` / `P2AnalyticNLO6j`; and the two coefficients differ by `-J₂(0,x)`.

* **Definitions copied from the paper** (explicit, with their label): `rho20` (`eq:general-rho20`),
  `J20` (`eq:phase-exactness-J20`), `Q2` (the operator `𝒬_{2,k}` of the proof of
  `prop:general-fixed-rank-contact`, with `κ = k + 1/2`, `s = 1-x²`, `∂_θ = -√s ∂_x`), in the notation
  `(ε₁, β₁, β₂, λ₁, χ)` of the class data (`eq:class-first-coefficients`, `eq:class-small-q`).
  The Hahn data are `eq:hahn-class-data` (`ε₁ = 1/2`, `β₁ = β₂ = 0`, `χ = x/2`, `λ₁ = 0`); the Racah data
  are `eq:racah-class-data` (`ε₁ = (α⁻²+β⁻²)/8`, `β₁ = 1/(4αβ)`, `β₂ = (1/2-m²-n²)/(8αβ)`,
  `χ₆ = x(α⁻²+β⁻²)/8 - 1/(4αβ)`, `λ₁ = 0`).
* `hahn_datum` (`cor:3j-phase-exactness`): for `x ∈ (-1,1)` and all `L, M, σ`,
  `nloF2 L M σ x = 𝒬_{2}[d] - J₂(0,x) d`, `d = d^L_{Mσ}(arccos x)`.
  `Phi3j_datum_expansion` puts this on the exact lattice `3j`: the `N⁻²` coefficient of
  `Φ_L^{M,σ}(x;1/N)` (`Phi3j_nlo_expansion`) is `𝒬_2[d] + c d` with `c = -J₂(0,x)`.
* `racah_datum` (`cor:6j-phase-exactness`): for `x ∈ (-1,1)`, all `f, m, n` and all `(ρ, w)`
  (`ρ = (α⁻²+β⁻²)/8`, `w = 1/(αβ)`; the identity is linear in `(ρ, w)`), the closed form
  `G_{f,2} = P_f d' + Q_f d` (`nlo6G`) equals `𝒬_2[d] - J₂(0,x) d`.
  `a6_datum` and `Phi6_datum_expansion` apply it to the exact `t`-coefficient and to the exact `6j` symbol.

## Not formalised

* The *derivation* of `𝒬_{2,k}`, `ρ₂(0,x)` and `J₂(0,x)` from the Darboux/WKB expansion of the pullback
  (`eq:generic-second-weyl-density`, `lem:pullback-flux`) is not formalised: `rho20`, `J20`, `Q2` are
  definitions copied from the paper, so what is proved is the **algebraic datum identity** between the
  P2 coefficient and these definitions.  Likewise the identification of the pullback `t`-coefficient with
  `𝒬_{2,k} d_k` (`prop:general-fixed-rank-contact`), the contact identity itself, and everything about
  the phase-exact pullback `Û^{[3]} = (1 + h²α) Û^{[2]}` and its `O(N⁻³)` bound are not formalised.
* The natural-gauge factor `√(2k+1)` is common to all three terms and is omitted.
* The statements are for the Hahn and centered Racah chains only (the quantum `6j` value `δ_fl = -1/12`
  and the general-chain `δ_fl` are not formalised).
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Racah.SixJ Set

/-! ### Definitions copied from the paper -/

/-- `ρ₂(0,x)` of `eq:general-rho20` (`prop:general-fixed-rank-contact`), with `(a,b)` the offsets,
`(ε₁, β₁, β₂, λ₁)` the first coefficients of the class data, and `s = 1-x²`:
`ρ₂(0,x) = [ε₁(9x - x³ - 8(a²+b²)x + 4abx² + 12ab) + β₁(8(a²+b²) - 16abx - 2x² - 6)
 + 12(β₂+λ₁x)(1-x²)] / (12 s^{3/2})`. -/
noncomputable def rho20 (a b ε₁ β₁ β₂ lam₁ x : ℝ) : ℝ :=
  (ε₁ * (9 * x - x ^ 3 - 8 * (a ^ 2 + b ^ 2) * x + 4 * (a * b) * x ^ 2 + 12 * (a * b)) +
      β₁ * (8 * (a ^ 2 + b ^ 2) - 16 * (a * b) * x - 2 * x ^ 2 - 6) +
      12 * (β₂ + lam₁ * x) * (1 - x ^ 2)) /
    (12 * ((1 - x ^ 2) * Real.sqrt (1 - x ^ 2)))

/-- `J₂(0,x)` of `eq:phase-exactness-J20`. -/
noncomputable def J20 (a b ε₁ β₁ β₂ lam₁ x : ℝ) : ℝ :=
  -(ε₁ * ((8 * (a ^ 2 + b ^ 2) - 5) * x ^ 2 + 4 * (a * b) * x * (x ^ 2 - 5) - 3) +
        8 * β₁ * ((1 - a ^ 2 - b ^ 2) * x + a * b * (1 + x ^ 2)) -
        12 * β₂ * x * (1 - x ^ 2)) /
      (24 * (1 - x ^ 2) ^ 2) + lam₁ / (2 * (1 - x ^ 2))

/-- The first-order operator `𝒬_{2,k}` of the proof of `prop:general-fixed-rank-contact` applied to a
function with value `d` and `x`-derivative `dp` (`κ = k + 1/2`, `s = 1-x²`):
`𝒬_{2,k} d = (κ²χ/3 - √s ρ₂) d' + [κ²((ε₁ - xβ₁)/2 - xχ/6)/s + xρ₂/(2√s)] d`. -/
noncomputable def Q2 (a b κ ε₁ β₁ β₂ lam₁ χ x d dp : ℝ) : ℝ :=
  (κ ^ 2 * χ / 3 - Real.sqrt (1 - x ^ 2) * rho20 a b ε₁ β₁ β₂ lam₁ x) * dp +
    (κ ^ 2 * ((ε₁ - x * β₁) / 2 - x * χ / 6) / (1 - x ^ 2) +
        x * rho20 a b ε₁ β₁ β₂ lam₁ x / (2 * Real.sqrt (1 - x ^ 2))) * d

/-! ### Algebra: removing the square roots -/

lemma sqrt_aux1 (N s r : ℝ) (hr : 0 < r) (hsq : r * r = s) :
    r * (N / (12 * (s * r))) = N / (12 * s) := by
  subst hsq; field_simp

lemma sqrt_aux2 (N s r : ℝ) (hr : 0 < r) (hsq : r * r = s) :
    N / (12 * (s * r)) / r = N / (12 * s ^ 2) := by
  subst hsq; field_simp

lemma sqrt_mul_rho20 (a b ε₁ β₁ β₂ lam₁ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Real.sqrt (1 - x ^ 2) * rho20 a b ε₁ β₁ β₂ lam₁ x =
      (ε₁ * (9 * x - x ^ 3 - 8 * (a ^ 2 + b ^ 2) * x + 4 * (a * b) * x ^ 2 + 12 * (a * b)) +
        β₁ * (8 * (a ^ 2 + b ^ 2) - 16 * (a * b) * x - 2 * x ^ 2 - 6) +
        12 * (β₂ + lam₁ * x) * (1 - x ^ 2)) / (12 * (1 - x ^ 2)) := by
  have hs : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  exact sqrt_aux1 _ _ _ (Real.sqrt_pos.2 hs) (Real.mul_self_sqrt hs.le)

lemma rho20_div_sqrt (a b ε₁ β₁ β₂ lam₁ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    rho20 a b ε₁ β₁ β₂ lam₁ x / Real.sqrt (1 - x ^ 2) =
      (ε₁ * (9 * x - x ^ 3 - 8 * (a ^ 2 + b ^ 2) * x + 4 * (a * b) * x ^ 2 + 12 * (a * b)) +
        β₁ * (8 * (a ^ 2 + b ^ 2) - 16 * (a * b) * x - 2 * x ^ 2 - 6) +
        12 * (β₂ + lam₁ * x) * (1 - x ^ 2)) / (12 * (1 - x ^ 2) ^ 2) := by
  have hs : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  exact sqrt_aux2 _ _ _ (Real.sqrt_pos.2 hs) (Real.mul_self_sqrt hs.le)

/-- `𝒬_{2,k}` as a rational expression in `x` (no square roots) for `x ∈ (-1,1)`. -/
lemma Q2_eq (a b κ ε₁ β₁ β₂ lam₁ χ d dp : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Q2 a b κ ε₁ β₁ β₂ lam₁ χ x d dp =
      (κ ^ 2 * χ / 3 -
          (ε₁ * (9 * x - x ^ 3 - 8 * (a ^ 2 + b ^ 2) * x + 4 * (a * b) * x ^ 2 + 12 * (a * b)) +
            β₁ * (8 * (a ^ 2 + b ^ 2) - 16 * (a * b) * x - 2 * x ^ 2 - 6) +
            12 * (β₂ + lam₁ * x) * (1 - x ^ 2)) / (12 * (1 - x ^ 2))) * dp +
        (κ ^ 2 * ((ε₁ - x * β₁) / 2 - x * χ / 6) / (1 - x ^ 2) +
          x / 2 *
            ((ε₁ * (9 * x - x ^ 3 - 8 * (a ^ 2 + b ^ 2) * x + 4 * (a * b) * x ^ 2 + 12 * (a * b)) +
              β₁ * (8 * (a ^ 2 + b ^ 2) - 16 * (a * b) * x - 2 * x ^ 2 - 6) +
              12 * (β₂ + lam₁ * x) * (1 - x ^ 2)) / (12 * (1 - x ^ 2) ^ 2))) * d := by
  unfold Q2
  have h1 := sqrt_mul_rho20 a b ε₁ β₁ β₂ lam₁ hx
  have h2 := rho20_div_sqrt a b ε₁ β₁ β₂ lam₁ hx
  have e : x * rho20 a b ε₁ β₁ β₂ lam₁ x / (2 * Real.sqrt (1 - x ^ 2)) =
      x / 2 * (rho20 a b ε₁ β₁ β₂ lam₁ x / Real.sqrt (1 - x ^ 2)) := by ring
  rw [h1, e, h2]

/-! ### Hahn (`cor:3j-phase-exactness`) -/

/-- **`cor:3j-phase-exactness`, fixed-rank datum** (algebraic identity, proved): with the Hahn class data
`eq:hahn-class-data` (`ε₁ = 1/2`, `β₁ = β₂ = λ₁ = 0`, `χ = x/2`), `κ² = L(L+1) + 1/4` and offsets
`(a,b) = (M,σ)`, the P2 coefficient `(A₂ d' + B₂ d)/(12(x²-1))` of `thm:3jNLO` equals
`𝒬_{2,L}[d] - J₂(0,x) d`, for every value pair `(d, d')`; i.e. the datum is `c(x) = -J₂(0,x)`.  The
definitions `rho20`, `J20`, `Q2` are the paper's; their derivation from the Darboux expansion is not
formalised. -/
theorem hahn_datum_alg (L M σ : ℚ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (d dp : ℝ) :
    (nloA2 L M σ x * dp + nloB2 L M σ x * d) / (12 * (x ^ 2 - 1)) =
      Q2 M σ ((L : ℝ) + 1 / 2) (1 / 2) 0 0 0 (x / 2) x d dp -
        J20 M σ (1 / 2) 0 0 0 x * d := by
  have hs : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  have hs' : x ^ 2 - 1 ≠ 0 := fun h => hs (by linarith)
  rw [Q2_eq _ _ _ _ _ _ _ _ _ _ hx]
  unfold nloA2 nloB2 J20
  field_simp
  ring

/-- **`cor:3j-phase-exactness`, fixed-rank datum for the exact `3j` coefficient** (proved):
`f_2 = (A₂ d' + B₂ d)/(12(x²-1)) = 𝒬_{2,L} d - J₂(0,x) d`, `d = d^L_{Mσ}(arccos x)`, `x ∈ (-1,1)`. -/
theorem hahn_datum (L M σ : ℚ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    nloF2 L M σ x =
      Q2 M σ ((L : ℝ) + 1 / 2) (1 / 2) 0 0 0 (x / 2) x (wignerSmallDx L M σ x)
          (deriv (wignerSmallDx L M σ) x) -
        J20 M σ (1 / 2) 0 0 0 x * wignerSmallDx L M σ x :=
  hahn_datum_alg L M σ hx _ _

/-- **`cor:3j-phase-exactness` on the exact lattice `3j`** (proved, from `Phi3j_nlo_expansion` and
`hahn_datum`): uniformly on compact `K ⊆ (-1,1)`, with `x = 2μ/N`, `d = d^L_{Mσ}(arccos x)`,
`|Φ_L^{M,σ}(x;1/N) - d - N⁻²(𝒬_{2,L} d - J₂(0,x) d)| ≤ C N⁻⁴`: the fixed-rank datum of the
exact `3j` solution is `c(x) = -J₂(0,x)`.  (Natural-gauge factor `√(2L+1)` omitted.) -/
theorem Phi3j_datum_expansion (M σ L : ℚ) (k : ℕ) (hL : L = max |M| |σ| + k) {K : Set ℝ}
    (hK : IsCompact K) (hKI : K ⊆ Ioo (-1 : ℝ) 1) :
    ∃ C N₀ : ℝ, ∀ N μ : ℚ, SpecAdm M σ N → Lat4 M σ N μ → N₀ ≤ (N : ℝ) →
      2 * (μ : ℝ) / N ∈ K →
      |Phi3j L M σ N μ - wignerSmallDx L M σ (2 * (μ : ℝ) / N) -
          (Q2 M σ ((L : ℝ) + 1 / 2) (1 / 2) 0 0 0 ((2 * (μ : ℝ) / N) / 2) (2 * (μ : ℝ) / N)
              (wignerSmallDx L M σ (2 * (μ : ℝ) / N))
              (deriv (wignerSmallDx L M σ) (2 * (μ : ℝ) / N)) -
            J20 M σ (1 / 2) 0 0 0 (2 * (μ : ℝ) / N) *
              wignerSmallDx L M σ (2 * (μ : ℝ) / N)) / (N : ℝ) ^ 2| ≤ C / (N : ℝ) ^ 4 := by
  obtain ⟨C, N₀, h⟩ := Phi3j_nlo_expansion M σ L k hL hK hKI
  refine ⟨C, N₀, fun N μ hA hlat hN hxK => ?_⟩
  have key := h N μ hA hlat hN hxK
  have hd := hahn_datum L M σ (hKI hxK)
  unfold nloF2 at hd
  rw [← hd]
  exact key

/-! ### Racah (`cor:6j-phase-exactness`) -/

/-- **`cor:6j-phase-exactness`, fixed-rank datum** (algebraic identity, proved): with the Racah class
data `eq:racah-class-data` in the shape-homogeneous variables `ρ = (α⁻²+β⁻²)/8`, `w = 1/(αβ)`
(`ε₁ = ρ`, `β₁ = w/4`, `β₂ = (1/2-m²-n²)w/8`, `χ₆ = ρx - w/4`, `λ₁ = 0`), offsets `(a,b) = (m,n)` and
`κ = f + 1/2`, the P2 closed form `G_{f,2} = P_f d' + Q_f d` of `thm:6jclosedcorrection`
(`nlo6G`) equals `𝒬_{2,f}[d] - J₂(0,x) d` for every `(d, d')`, `(ρ, w)` real and `x ∈ (-1,1)`;
i.e. the datum is `c(x) = -J₂(0,x)`.  (`rho20`, `J20`, `Q2` are definitions copied from the paper.) -/
theorem racah_datum (f m n ρ w : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (d dp : ℝ) :
    nlo6G (f * (f + 1)) (m ^ 2 + n ^ 2) (m * n) ρ w x d dp =
      Q2 m n (f + 1 / 2) ρ (w / 4) ((1 / 2 - m ^ 2 - n ^ 2) * w / 8) 0 (ρ * x - w / 4) x d dp -
        J20 m n ρ (w / 4) ((1 / 2 - m ^ 2 - n ^ 2) * w / 8) 0 x * d := by
  have hs : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [Q2_eq _ _ _ _ _ _ _ _ _ _ hx]
  unfold nlo6G nlo6P nlo6Q J20
  field_simp
  ring

/-- **`cor:6j-phase-exactness` for the exact `t`-coefficient of the `6j` germ** (proved, from
`a6_one_closed`): for a strict-triangle shape `(α,β,γ)` and `f ± m`, `f ± n` natural,
`a_{f,1} = 𝒬_{2,f} d - J₂(0,x) d` with the Racah data of `eq:racah-class-data`
(`ε₁ = (α⁻²+β⁻²)/8`, `β₁ = 1/(4αβ)`, `β₂ = (1/2-m²-n²)/(8αβ)`, `χ₆ = x(α⁻²+β⁻²)/8 - 1/(4αβ)`),
`x = cosA α β γ`, `d = d^f_{nm}(arccos x)`. -/
theorem a6_datum (f m n : ℚ) (n1 : IsNat (f + m)) (n2 : IsNat (f - m)) (n3 : IsNat (f + n))
    (n4 : IsNat (f - n)) {α β γ : ℝ} (hz : (α, β, γ) ∈ StrictTri) :
    a6 f m n 1 (α, β, γ) =
      Q2 m n ((f : ℝ) + 1 / 2) (((α ^ 2)⁻¹ + (β ^ 2)⁻¹) / 8) (1 / (α * β) / 4)
          ((1 / 2 - (m : ℝ) ^ 2 - (n : ℝ) ^ 2) * (1 / (α * β)) / 8) 0
          ((((α ^ 2)⁻¹ + (β ^ 2)⁻¹) / 8) * cosA α β γ - 1 / (α * β) / 4) (cosA α β γ)
          (wignerSmallDx f n m (cosA α β γ)) (deriv (wignerSmallDx f n m) (cosA α β γ)) -
        J20 m n (((α ^ 2)⁻¹ + (β ^ 2)⁻¹) / 8) (1 / (α * β) / 4)
            ((1 / 2 - (m : ℝ) ^ 2 - (n : ℝ) ^ 2) * (1 / (α * β)) / 8) 0 (cosA α β γ) *
          wignerSmallDx f n m (cosA α β γ) := by
  rw [a6_one_closed f m n n1 n2 n3 n4 hz]
  exact racah_datum _ _ _ _ _ (nlo6_cosA_mem_Ioo hz) _ _

/-- **`cor:6j-phase-exactness` on the exact `6j` symbol** (proved, from `Phi6_nlo_expansion` and
`racah_datum`): on a compact set `K` of strict-triangle shapes, for every physical admissible point with
`S = A+B+C ≥ S₀` and normalised shape in `K`, with `A = wA a n`, `B = wB b m`, `C = wC c`,
`x = cosA A B C`, `d = d^f_{nm}(arccos x)`,
`|Φ_f - d - (𝒬_{2,f} d - J₂(0,x) d)| ≤ C S⁻⁴`, where `𝒬_{2,f}` and `J₂(0,x)` carry the Racah data
of `eq:racah-class-data` at `(α,β) = (A,B)` (the `t = N⁻²` bookkeeping is absorbed into the scale,
`A = Nα`): the fixed-rank datum of the exact `6j` solution is `c(x) = -J₂(0,x)`. -/
theorem Phi6_datum_expansion (f m n : ℚ) {K : Set Shape6} (hK : IsCompact K)
    (hKS : K ⊆ StrictTri) :
    ∃ C S₀ : ℝ, ∀ a b c : ℚ, IsTri f (b + m) b → IsTri f a (a + n) → IsTri c a b →
      IsTri c (b + m) (a + n) → S₀ ≤ wA a n + wB b m + wC c →
      (wA a n / (wA a n + wB b m + wC c), wB b m / (wA a n + wB b m + wC c),
        wC c / (wA a n + wB b m + wC c)) ∈ K →
      |Phi6 a b c f m n - wignerSmallDx f n m (cosA (wA a n) (wB b m) (wC c)) -
          (Q2 m n ((f : ℝ) + 1 / 2) (((wA a n ^ 2)⁻¹ + (wB b m ^ 2)⁻¹) / 8)
              (1 / (wA a n * wB b m) / 4)
              ((1 / 2 - (m : ℝ) ^ 2 - (n : ℝ) ^ 2) * (1 / (wA a n * wB b m)) / 8) 0
              ((((wA a n ^ 2)⁻¹ + (wB b m ^ 2)⁻¹) / 8) * cosA (wA a n) (wB b m) (wC c) -
                1 / (wA a n * wB b m) / 4)
              (cosA (wA a n) (wB b m) (wC c))
              (wignerSmallDx f n m (cosA (wA a n) (wB b m) (wC c)))
              (deriv (wignerSmallDx f n m) (cosA (wA a n) (wB b m) (wC c))) -
            J20 m n (((wA a n ^ 2)⁻¹ + (wB b m ^ 2)⁻¹) / 8) (1 / (wA a n * wB b m) / 4)
                ((1 / 2 - (m : ℝ) ^ 2 - (n : ℝ) ^ 2) * (1 / (wA a n * wB b m)) / 8) 0
                (cosA (wA a n) (wB b m) (wC c)) *
              wignerSmallDx f n m (cosA (wA a n) (wB b m) (wC c)))| ≤
        C / (wA a n + wB b m + wC c) ^ 4 := by
  obtain ⟨C, S₀, h⟩ := Phi6_nlo_expansion f m n hK hKS
  refine ⟨C, S₀, fun a b c h1 h2 h3 h4 hS0 hz => ?_⟩
  have key := h a b c h1 h2 h3 h4 hS0 hz
  obtain ⟨hA, hB, hC, hSpos⟩ := physical_scale_pos h1 h2 h3
  have hst := strictTri_shape hSpos (hKS hz)
  have hxI := nlo6_cosA_mem_Ioo hst
  have hd := racah_datum f m n (((wA a n ^ 2)⁻¹ + (wB b m ^ 2)⁻¹) / 8) (1 / (wA a n * wB b m))
    hxI (wignerSmallDx f n m (cosA (wA a n) (wB b m) (wC c)))
    (deriv (wignerSmallDx f n m) (cosA (wA a n) (wB b m) (wC c)))
  unfold G6closed at key
  rw [hd] at key
  exact key

/-! ### Axiom checks -/

/-- info: 'FormalResearch.Racah.hahn_datum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_datum

/-- info: 'FormalResearch.Racah.Phi3j_datum_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_datum_expansion

/-- info: 'FormalResearch.Racah.racah_datum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_datum

/-- info: 'FormalResearch.Racah.a6_datum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms a6_datum

/-- info: 'FormalResearch.Racah.Phi6_datum_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_datum_expansion

end FormalResearch.Racah
