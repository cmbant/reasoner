module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic

/-!
# The Racah turning curve is the flat-tetrahedron locus (Weyl P3, `lem:racah-cayley-menger`)

Source: `Weyl/P3/paper/weyl_midpoint_semiclassics.tex`, `lem:racah-cayley-menger` /
`eq:racah-cayley-menger`, and its proof in `weyl_midpoint_semiclassics_appendices.tex`
("Proof of Lemma `lem:racah-cayley-menger`", with the two remarks following it: relation to the volume,
equilateral family).  The principal Weyl tetrahedron has edge array `(A,B,C;B,A,F)`, `A = Nα`,
`B = Nβ`, `C = Nγ`, `F = Nρ`.

## What is formalised (exact, all real parameters)

* `cmMat`, `cmDet`: the `5×5` Cayley--Menger matrix of a tetrahedron with the six edges
  `d₁₂, d₂₃, d₁₃, d₃₄, d₁₄, d₂₄` and its determinant (`Matrix.det`, no hypotheses on the edges).
* `cmDet_racah` (`eq:racah-cayley-menger`, polynomial form): for arbitrary reals `N, α, β, γ, ρ`,
  `det CM(Nα,Nβ,Nγ;Nβ,Nα,Nρ) = 2N⁶ρ²(4α²β² - (α²+β²-γ²)² - γ²ρ²)`.
* `heron` (Heron's formula): `4α²β² - (α²+β²-γ²)² = 16 s(s-α)(s-β)(s-γ)`, `s = (α+β+γ)/2`.
  `T²` is represented by `heronT2 α β γ := s(s-α)(s-β)(s-γ)` (the area is `√(heronT2)`; no
  geometric definition of the area is used).
* `cmDet_racah_T`: `det CM = 2N⁶ρ²(16T² - γ²ρ²)`.
* `D6lin`, `D6adiab` (`eq:D6adiabatic`, with `x = (α²+β²-γ²)/(2αβ)`): the two forms of `D_6`;
  `D6adiab_eq_D6lin` (for `α, β ≠ 0`) proves they agree, and `cmDet_racah_D6`:
  `det CM = 8N⁶ρ²α²β² D_6(ρ)`.
* `volume_formula` : the route of the paper's proof, `288 𝒱² = det CM` for
  `𝒱 = F r_A r_B sin ω / 6`, with `r_A² = N²(α²-ρ²/4)`, `r_B² = N²(β²-ρ²/4)`, `sin²ω = D_6/η²`
  (stated for `η² ≠ 0`, as an identity of squares).
* `cmDet_pos_iff`, `cmDet_eq_zero_iff`, `cmDet_neg_iff`: the sign trichotomy
  `sign det CM = sign D_6` for `N, α, β, ρ ≠ 0` (the prefactor is `> 0`).
* `faces_admissible`: **a point the paper's proof does not verify**: `D_6 > 0` with `α, β, γ > 0`
  already forces `ρ < 2α`, `ρ < 2β`, so the two faces `(A,A,F)`, `(B,B,F)` of the tetrahedron satisfy
  the triangle inequality (the other two faces are the `(α,β,γ)` triangle); hence
  `D_6 > 0` alone is the Euclidean condition.
* `volume_sq`, `volume_sq_le`, `volume_sq_max_iff` (the volume remark): `det CM/288 =
  N⁶γ²ρ²(ρ⋆²-ρ²)/144` with `ρ⋆² = 16T²/γ²` (`γ ≠ 0`), and the maximum of `ρ²(ρ⋆²-ρ²)` is `ρ⋆⁴/4`,
  attained exactly at `ρ² = ρ⋆²/2`.
* `cmRacah_homog`: `det CM` is homogeneous of degree 6 in `N`.
* `cmDet_equilateral`: `det CM = 2N⁶L²ρ²(3L²-ρ²)` for `α = β = γ = L`.

## Not formalised

The geometric content (`det CM = 288 𝒱²` for an actual Euclidean tetrahedron, the existence
criterion "a tetrahedron with prescribed edges exists in `ℝ³` iff `det CM ≥ 0` and the faces are
admissible", the Schläfli/dihedral-angle machinery) is formalised in `FormalResearch.EuclTet`
(`EuclTet.Gram`, `EuclTet.Dichotomy`, `EuclTet.Schlafli`, `EuclTet.RacahBridge`).  Not formalised
anywhere: `ω = Θ_F` and `𝒱 = F r_A r_B sin ω/6` as statements about points, and the irrationality
remark (`√3`) beyond `cmDet_equilateral`.  This module is the *algebra* only.
-/

@[expose] public section

namespace FormalResearch.Racah.P3

/-- The `5×5` Cayley--Menger matrix of a tetrahedron with edges
`d₁₂ = a, d₂₃ = b, d₁₃ = c, d₃₄ = d, d₁₄ = e, d₂₄ = f` (vertices `1,2,3,4`). -/
def cmMat (a b c d e f : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 1, 1, 1, 1;
     1, 0, a ^ 2, c ^ 2, e ^ 2;
     1, a ^ 2, 0, b ^ 2, f ^ 2;
     1, c ^ 2, b ^ 2, 0, d ^ 2;
     1, e ^ 2, f ^ 2, d ^ 2, 0]

/-- The Cayley--Menger determinant. -/
def cmDet (a b c d e f : ℝ) : ℝ := (cmMat a b c d e f).det

/-- The principal Weyl tetrahedron `(A,B,C;B,A,F)` with `A = Nα`, `B = Nβ`, `C = Nγ`, `F = Nρ`:
edges `d₁₂ = A`, `d₂₃ = B`, `d₁₃ = C`, `d₃₄ = B`, `d₁₄ = A`, `d₂₄ = F`. -/
def cmRacah (N α β γ ρ : ℝ) : ℝ := cmDet (N * α) (N * β) (N * γ) (N * β) (N * α) (N * ρ)

/-- **`eq:racah-cayley-menger`, polynomial form.**  For all real `N, α, β, γ, ρ`,
`det CM = 2N⁶ρ²(4α²β² - (α²+β²-γ²)² - γ²ρ²)`. -/
theorem cmDet_racah_poly (N α β γ ρ : ℝ) :
    cmRacah N α β γ ρ =
      2 * N ^ 6 * ρ ^ 2 * (4 * α ^ 2 * β ^ 2 - (α ^ 2 + β ^ 2 - γ ^ 2) ^ 2 - γ ^ 2 * ρ ^ 2) := by
  simp [cmRacah, cmDet, cmMat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- **Heron's formula**, in the form used by the proof: `4α²β² - (α²+β²-γ²)² = 16 s(s-α)(s-β)(s-γ)`
with `s = (α+β+γ)/2`. -/
noncomputable def heronT2 (α β γ : ℝ) : ℝ :=
  ((α + β + γ) / 2) * ((α + β + γ) / 2 - α) * ((α + β + γ) / 2 - β) * ((α + β + γ) / 2 - γ)

theorem heron (α β γ : ℝ) :
    4 * α ^ 2 * β ^ 2 - (α ^ 2 + β ^ 2 - γ ^ 2) ^ 2 = 16 * heronT2 α β γ := by
  unfold heronT2; ring

/-- **`eq:racah-cayley-menger`, second equality**: `det CM = 2N⁶ρ²(16T² - γ²ρ²)`, `T² = heronT2`. -/
theorem cmDet_racah_T (N α β γ ρ : ℝ) :
    cmRacah N α β γ ρ = 2 * N ^ 6 * ρ ^ 2 * (16 * heronT2 α β γ - γ ^ 2 * ρ ^ 2) := by
  rw [cmDet_racah_poly, ← heron]

/-- `x = cos θ = (α²+β²-γ²)/(2αβ)` (law of cosines, `2αβx = α²+β²-γ²`). -/
noncomputable def cosθ (α β γ : ℝ) : ℝ := (α ^ 2 + β ^ 2 - γ ^ 2) / (2 * α * β)

/-- `η(ρ)² = (1-ρ²/4α²)(1-ρ²/4β²)` (`eq:6jsymbol`). -/
noncomputable def eta2 (α β ρ : ℝ) : ℝ := (1 - ρ ^ 2 / (4 * α ^ 2)) * (1 - ρ ^ 2 / (4 * β ^ 2))

/-- `D₆(ρ) = η² - (x - ρ²/(4αβ))²` (`eq:D6adiabatic`, first form). -/
noncomputable def D6adiab (α β γ ρ : ℝ) : ℝ :=
  eta2 α β ρ - (cosθ α β γ - ρ ^ 2 / (4 * α * β)) ^ 2

/-- `D₆(ρ) = sin²θ - γ²ρ²/(4α²β²)` (`eq:D6adiabatic`, second form), `sin²θ = 1 - x²`. -/
noncomputable def D6lin (α β γ ρ : ℝ) : ℝ :=
  (1 - cosθ α β γ ^ 2) - γ ^ 2 * ρ ^ 2 / (4 * α ^ 2 * β ^ 2)

/-- The two forms of `D₆` of `eq:D6adiabatic` agree (the paper's "exact simplification"). -/
theorem D6adiab_eq_D6lin {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (γ ρ : ℝ) :
    D6adiab α β γ ρ = D6lin α β γ ρ := by
  unfold D6adiab D6lin eta2 cosθ
  field_simp
  ring

theorem D6lin_eq {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (γ ρ : ℝ) :
    D6lin α β γ ρ =
      (4 * α ^ 2 * β ^ 2 - (α ^ 2 + β ^ 2 - γ ^ 2) ^ 2 - γ ^ 2 * ρ ^ 2) / (4 * α ^ 2 * β ^ 2) := by
  unfold D6lin cosθ
  field_simp
  ring

/-- **`eq:racah-cayley-menger`, first equality**: `det CM = 8N⁶ρ²α²β² D₆(ρ)` (both forms of `D₆`). -/
theorem cmDet_racah_D6 {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (N γ ρ : ℝ) :
    cmRacah N α β γ ρ = 8 * N ^ 6 * ρ ^ 2 * α ^ 2 * β ^ 2 * D6lin α β γ ρ ∧
    cmRacah N α β γ ρ = 8 * N ^ 6 * ρ ^ 2 * α ^ 2 * β ^ 2 * D6adiab α β γ ρ := by
  have h : cmRacah N α β γ ρ = 8 * N ^ 6 * ρ ^ 2 * α ^ 2 * β ^ 2 * D6lin α β γ ρ := by
    rw [cmDet_racah_poly, D6lin_eq hα hβ]
    field_simp
    ring
  exact ⟨h, by rw [D6adiab_eq_D6lin hα hβ]; exact h⟩

/-- The route of the paper's proof: `288 𝒱² = det CM` for `𝒱 = F r_A r_B sin ω / 6`, with
`F = Nρ`, `r_A² = N²α²(1-ρ²/4α²)`, `r_B² = N²β²(1-ρ²/4β²)` and `sin²ω = D₆/η²` (from
`cos ω = (x-b)/η`, `b = ρ²/4αβ`).  Stated for the squares (no square roots, no geometry), `η² ≠ 0`. -/
theorem volume_formula {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (N γ ρ : ℝ)
    (hη : eta2 α β ρ ≠ 0) :
    288 * (((N * ρ) ^ 2 * (N ^ 2 * α ^ 2 * (1 - ρ ^ 2 / (4 * α ^ 2))) *
        (N ^ 2 * β ^ 2 * (1 - ρ ^ 2 / (4 * β ^ 2))) * (D6adiab α β γ ρ / eta2 α β ρ)) / 36) =
      cmRacah N α β γ ρ := by
  rw [(cmDet_racah_D6 hα hβ N γ ρ).2]
  have h1 : eta2 α β ρ * (D6adiab α β γ ρ / eta2 α β ρ) = D6adiab α β γ ρ := by
    field_simp
  have h2 : (N * ρ) ^ 2 * (N ^ 2 * α ^ 2 * (1 - ρ ^ 2 / (4 * α ^ 2))) *
        (N ^ 2 * β ^ 2 * (1 - ρ ^ 2 / (4 * β ^ 2))) * (D6adiab α β γ ρ / eta2 α β ρ) =
      (N * ρ) ^ 2 * (N ^ 2 * α ^ 2 * (N ^ 2 * β ^ 2)) *
        (eta2 α β ρ * (D6adiab α β γ ρ / eta2 α β ρ)) := by
    unfold eta2; ring
  rw [h2, h1]; ring

/-- **Sign trichotomy** (`N, α, β, ρ ≠ 0`): `sign det CM = sign D₆`. -/
theorem cmDet_pos_iff {N α β : ℝ} (hN : N ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0) {ρ : ℝ} (hρ : ρ ≠ 0)
    (γ : ℝ) : 0 < cmRacah N α β γ ρ ↔ 0 < D6lin α β γ ρ := by
  rw [(cmDet_racah_D6 hα hβ N γ ρ).1]
  have : 0 < 8 * N ^ 6 * ρ ^ 2 * α ^ 2 * β ^ 2 := by positivity
  exact mul_pos_iff_of_pos_left this

theorem cmDet_eq_zero_iff {N α β : ℝ} (hN : N ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0) {ρ : ℝ}
    (hρ : ρ ≠ 0) (γ : ℝ) : cmRacah N α β γ ρ = 0 ↔ D6lin α β γ ρ = 0 := by
  rw [(cmDet_racah_D6 hα hβ N γ ρ).1]
  have : 8 * N ^ 6 * ρ ^ 2 * α ^ 2 * β ^ 2 ≠ 0 := by positivity
  simp [this]

theorem cmDet_neg_iff {N α β : ℝ} (hN : N ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0) {ρ : ℝ} (hρ : ρ ≠ 0)
    (γ : ℝ) : cmRacah N α β γ ρ < 0 ↔ D6lin α β γ ρ < 0 := by
  rw [(cmDet_racah_D6 hα hβ N γ ρ).1]
  have : 0 < 8 * N ^ 6 * ρ ^ 2 * α ^ 2 * β ^ 2 := by positivity
  constructor
  · intro h
    by_contra hD
    nlinarith [mul_nonneg this.le (not_lt.1 hD)]
  · intro h
    exact mul_neg_of_pos_of_neg this h

/-- **Face admissibility** (a point the paper's proof uses without proof).  With `α, β, γ > 0`,
`D₆ > 0` already forces `ρ² < 4α²` and `ρ² < 4β²`: the faces `(A,A,F)` and `(B,B,F)` of the
tetrahedron satisfy the triangle inequality (the other two faces are the `(α,β,γ)` triangle).
The inequalities are `4α²γ² - [4α²β²-(α²+β²-γ²)²] = (α²-β²+γ²)² ≥ 0` and the symmetric one. -/
theorem faces_admissible {α β γ ρ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hD : 0 < D6lin α β γ ρ) : ρ ^ 2 < 4 * α ^ 2 ∧ ρ ^ 2 < 4 * β ^ 2 := by
  rw [D6lin_eq hα.ne' hβ.ne'] at hD
  have hP : 0 < 4 * α ^ 2 * β ^ 2 - (α ^ 2 + β ^ 2 - γ ^ 2) ^ 2 - γ ^ 2 * ρ ^ 2 := by
    have := (div_pos_iff_of_pos_right (by positivity : (0:ℝ) < 4 * α ^ 2 * β ^ 2)).1 hD
    exact this
  have hγ2 : 0 < γ ^ 2 := by positivity
  constructor
  · by_contra h
    have h := not_lt.1 h
    nlinarith [sq_nonneg (α ^ 2 - β ^ 2 + γ ^ 2), mul_le_mul_of_nonneg_left h hγ2.le]
  · by_contra h
    have h := not_lt.1 h
    nlinarith [sq_nonneg (β ^ 2 - α ^ 2 + γ ^ 2), mul_le_mul_of_nonneg_left h hγ2.le]

/-- **Volume remark**: `𝒱² = det CM / 288 = N⁶γ²ρ²(ρ⋆² - ρ²)/144` with `ρ⋆² = 16T²/γ²`
(`γ ≠ 0`). -/
theorem volume_sq {γ : ℝ} (hγ : γ ≠ 0) (N α β ρ : ℝ) :
    cmRacah N α β γ ρ / 288 =
      N ^ 6 * γ ^ 2 / 144 * (ρ ^ 2 * (16 * heronT2 α β γ / γ ^ 2 - ρ ^ 2)) := by
  rw [cmDet_racah_T]
  field_simp
  ring

/-- The maximum of `ρ²(ρ⋆² - ρ²)` is `ρ⋆⁴/4`, attained exactly at `ρ² = ρ⋆²/2`
(the volume is maximal at `ρ = ρ⋆/√2`). -/
theorem volume_sq_le (c ρ : ℝ) : ρ ^ 2 * (c - ρ ^ 2) ≤ (c / 2) ^ 2 := by
  nlinarith [sq_nonneg (ρ ^ 2 - c / 2)]

theorem volume_sq_max_iff (c ρ : ℝ) :
    ρ ^ 2 * (c - ρ ^ 2) = (c / 2) ^ 2 ↔ ρ ^ 2 = c / 2 := by
  constructor
  · intro h
    have : (ρ ^ 2 - c / 2) ^ 2 = 0 := by nlinarith
    nlinarith [pow_eq_zero_iff (two_ne_zero) |>.1 this]
  · intro h; rw [h]; ring

/-- **Equilateral family** `α = β = γ = L`: `det CM = 2N⁶L²ρ²(3L² - ρ²)`. -/
theorem cmDet_equilateral (N L ρ : ℝ) :
    cmRacah N L L L ρ = 2 * N ^ 6 * L ^ 2 * ρ ^ 2 * (3 * L ^ 2 - ρ ^ 2) := by
  rw [cmDet_racah_poly]; ring

/-- Homogeneity of degree 6 in the dilation parameter. -/
theorem cmRacah_homog (N α β γ ρ : ℝ) :
    cmRacah N α β γ ρ = N ^ 6 * cmRacah 1 α β γ ρ := by
  rw [cmDet_racah_poly, cmDet_racah_poly]; ring

/-- info: 'FormalResearch.Racah.P3.cmDet_racah_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cmDet_racah_poly

/-- info: 'FormalResearch.Racah.P3.cmDet_racah_D6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cmDet_racah_D6

/-- info: 'FormalResearch.Racah.P3.cmDet_racah_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cmDet_racah_T

/-- info: 'FormalResearch.Racah.P3.faces_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms faces_admissible

/-- info: 'FormalResearch.Racah.P3.volume_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms volume_formula

end FormalResearch.Racah.P3
