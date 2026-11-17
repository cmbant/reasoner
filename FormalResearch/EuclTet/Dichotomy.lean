module

public import Mathlib
public import FormalResearch.EuclTet.Schlafli

/-!
# Lorentzian dichotomy and wall angles, from the Cayley--Menger cofactors

Sources: Weyl/P5 `cayley_menger_trichotomy.tex`, `thm:dichotomy` (`eq:flat-edge-dichotomy`,
`eq:flat-edge-forbidden`: `det CM >0 / =0 / <0` iff `|cos θ_e| <1 / =1 / >1` for all six edges),
`cor:combinatorial` (at a wall point with strict faces every dihedral cosine is `±1`), `eq:gramcos`
(the dihedral cosine in vertex-Gram form), and Blumenthal's realisation criterion
(`eq:cm`, Blumenthal 1953).  Everything is a statement about the six squared edge lengths
`x_{ij}` (no points), through the Cayley--Menger cofactors `C_{ij}` of `FormalResearch.EuclTet.Cofactor`.

Setting.  `FacesStrict x` says `x_e > 0` and `C_{ii} < 0` for the four faces (the strict triangle
inequalities, Hypothesis `hyp:faces`); `det CM` has no sign condition.  `cosX x i j =
C_{ij}/√(C_{ii}C_{jj})` is the (possibly continued) cosine of the dihedral angle at the edge shared by
the faces opposite `i` and `j`; `oppX x i j` is the squared length of that edge.

## What is formalised (exact, proved; no numerics)

* `cof_jacobi_pair`: `C_ii C_jj - C_ij² = 2 · oppX i j · det CM` for every pair `i ≠ j`
  (uniform form of `cof_jacobi01 … 23`).
* `abs_cosX_lt_one_iff`, `abs_cosX_eq_one_iff`, `one_lt_abs_cosX_iff`
  (**`thm:dichotomy`**): under `FacesStrict`, for each of the six edges, `|cos| < 1 ⇔ det CM > 0`,
  `|cos| = 1 ⇔ det CM = 0`, `|cos| > 1 ⇔ det CM < 0`; `six_edges_trichotomy`: hence either all six edges
  have `|cos| < 1`, or all six `= 1`, or all six `> 1` (a mixed configuration is impossible).
* `thetaX_eq_zero_iff_cof_pos`, `thetaX_eq_pi_iff_cof_neg`, `thetaX_eq_zero_or_pi_of_wall`
  (**`cor:combinatorial`**): at `det CM = 0` with strict faces, `θ_ij ∈ {0, π}`, with `θ_ij = 0 ⇔ C_ij > 0`.
* `cosX_eq_gram_*` (**`eq:gramcos`**): for the three edges at the vertex `0`, `cosX` is the
  vertex-Gram expression `(G_uu G_vw - G_uv G_uw)/√((G_uu G_vv - G_uv²)(G_uu G_ww - G_uw²))`
  with `G = gramX x` (`cof23_eq_gram`, … are the polynomial identities behind it).
* `posSemidef_gramX_of_blumenthal`, `exists_points_of_blumenthal`, `blumenthal_iff`
  (**Blumenthal's criterion**, full form): six numbers `x_e ≥ 0` are the squared distances of four points of
  `ℝ³` iff `det CM ≥ 0` and the four faces satisfy the triangle inequalities (`C_ii ≤ 0`).  Only the three faces
  through the vertex `0` are needed for the converse.  The proof of positive semidefiniteness of the
  `3×3` Gram matrix from its principal minors is `posSemidef_fin3_of_minors` (via the characteristic
  polynomial `det (G - μ) = det G - μ ∑ m₂ + μ² tr G - μ³`).

## Not formalised

* The statement of `thm:dichotomy` in the paper is for admissible `6j` tuples; only the CM geometry
  (`FacesStrict`) is used here.  Hyperbolic (boost) edges for `|cos| > 1` are not interpreted.
* Blumenthal's criterion for general `n`; the identification of the realised points with a tetrahedron
  of positive volume is `Gram`.
-/

@[expose] public section

namespace FormalResearch.EuclTet

open Matrix Real

/-- Strict faces (Hypothesis `hyp:faces`): positive squared edges and `C_ii < 0` for the four faces. -/
structure FacesStrict (x01 x02 x03 x12 x13 x23 : ℝ) : Prop where
  x01_pos : 0 < x01
  x02_pos : 0 < x02
  x03_pos : 0 < x03
  x12_pos : 0 < x12
  x13_pos : 0 < x13
  x23_pos : 0 < x23
  c00_neg : cof00 x01 x02 x03 x12 x13 x23 < 0
  c11_neg : cof11 x01 x02 x03 x12 x13 x23 < 0
  c22_neg : cof22 x01 x02 x03 x12 x13 x23 < 0
  c33_neg : cof33 x01 x02 x03 x12 x13 x23 < 0

theorem FacesStrict.of_nondeg {x01 x02 x03 x12 x13 x23 : ℝ} (h : Nondeg x01 x02 x03 x12 x13 x23) :
    FacesStrict x01 x02 x03 x12 x13 x23 :=
  ⟨h.x01_pos, h.x02_pos, h.x03_pos, h.x12_pos, h.x13_pos, h.x23_pos, h.c00_neg, h.c11_neg,
    h.c22_neg, h.c33_neg⟩

theorem FacesStrict.cofM_diag_neg {x01 x02 x03 x12 x13 x23 : ℝ}
    (h : FacesStrict x01 x02 x03 x12 x13 x23) (i : Fin 4) :
    cofM x01 x02 x03 x12 x13 x23 i i < 0 := by
  fin_cases i
  · exact h.c00_neg
  · exact h.c11_neg
  · exact h.c22_neg
  · exact h.c33_neg

/-- The squared length of the edge shared by the faces opposite the vertices `i ≠ j`
(the edge `kl` with `{i,j,k,l} = {0,1,2,3}`). -/
def oppX (x01 x02 x03 x12 x13 x23 : ℝ) (i j : Fin 4) : ℝ :=
  ![![0, x23, x13, x12], ![x23, 0, x03, x02], ![x13, x03, 0, x01], ![x12, x02, x01, 0]] i j

/-- The (possibly continued) dihedral cosine `C_ij / √(C_ii C_jj)`. -/
noncomputable def cosX (x01 x02 x03 x12 x13 x23 : ℝ) (i j : Fin 4) : ℝ :=
  cofM x01 x02 x03 x12 x13 x23 i j /
    √(cofM x01 x02 x03 x12 x13 x23 i i * cofM x01 x02 x03 x12 x13 x23 j j)

theorem thetaX_eq_arccos_cosX (x01 x02 x03 x12 x13 x23 : ℝ) (i j : Fin 4) :
    thetaX x01 x02 x03 x12 x13 x23 i j = arccos (cosX x01 x02 x03 x12 x13 x23 i j) := rfl

/-- **Jacobi's identity, uniform form**: `C_ii C_jj - C_ij² = 2 x_{kl} det CM` for `i ≠ j`. -/
theorem cof_jacobi_pair (x01 x02 x03 x12 x13 x23 : ℝ) (i j : Fin 4) (hij : i ≠ j) :
    cofM x01 x02 x03 x12 x13 x23 i i * cofM x01 x02 x03 x12 x13 x23 j j
      - cofM x01 x02 x03 x12 x13 x23 i j ^ 2
      = 2 * oppX x01 x02 x03 x12 x13 x23 i j * cmDet2 x01 x02 x03 x12 x13 x23 := by
  have h01 := cof_jacobi01 x01 x02 x03 x12 x13 x23
  have h02 := cof_jacobi02 x01 x02 x03 x12 x13 x23
  have h03 := cof_jacobi03 x01 x02 x03 x12 x13 x23
  have h12 := cof_jacobi12 x01 x02 x03 x12 x13 x23
  have h13 := cof_jacobi13 x01 x02 x03 x12 x13 x23
  have h23 := cof_jacobi23 x01 x02 x03 x12 x13 x23
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | (simp [cofM, oppX]; linarith)

theorem oppX_pos {x01 x02 x03 x12 x13 x23 : ℝ} (h : FacesStrict x01 x02 x03 x12 x13 x23)
    (i j : Fin 4) (hij : i ≠ j) : 0 < oppX x01 x02 x03 x12 x13 x23 i j := by
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | (simp [oppX]; linarith [h.x01_pos, h.x02_pos, h.x03_pos, h.x12_pos, h.x13_pos, h.x23_pos])

section Generic

theorem sq_div_sqrt_mul {a b c : ℝ} (hab : 0 < a * b) : (c / √(a * b)) ^ 2 = c ^ 2 / (a * b) := by
  rw [div_pow, Real.sq_sqrt hab.le]

theorem abs_div_sqrt_lt_one_iff {a b c : ℝ} (hab : 0 < a * b) :
    |c / √(a * b)| < 1 ↔ 0 < a * b - c ^ 2 := by
  rw [← sq_lt_one_iff_abs_lt_one, sq_div_sqrt_mul hab, div_lt_one hab]
  constructor <;> intro h <;> linarith

theorem abs_div_sqrt_eq_one_iff {a b c : ℝ} (hab : 0 < a * b) :
    |c / √(a * b)| = 1 ↔ a * b - c ^ 2 = 0 := by
  have h1 : |c / √(a * b)| = 1 ↔ (c / √(a * b)) ^ 2 = 1 := by
    rw [← sq_abs]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).symm
  rw [h1, sq_div_sqrt_mul hab, div_eq_one_iff_eq hab.ne']
  constructor <;> intro h <;> linarith

theorem one_lt_abs_div_sqrt_iff {a b c : ℝ} (hab : 0 < a * b) :
    1 < |c / √(a * b)| ↔ a * b - c ^ 2 < 0 := by
  rw [← one_lt_sq_iff_one_lt_abs, sq_div_sqrt_mul hab, one_lt_div hab]
  constructor <;> intro h <;> linarith

end Generic

section Dichotomy

variable {x01 x02 x03 x12 x13 x23 : ℝ}

theorem cof_diag_mul_pos (h : FacesStrict x01 x02 x03 x12 x13 x23) (i j : Fin 4) :
    0 < cofM x01 x02 x03 x12 x13 x23 i i * cofM x01 x02 x03 x12 x13 x23 j j :=
  mul_pos_of_neg_of_neg (h.cofM_diag_neg i) (h.cofM_diag_neg j)

/-- **`thm:dichotomy`, nondegenerate side**: `|cos θ_ij| < 1 ⇔ det CM > 0`. -/
theorem abs_cosX_lt_one_iff (h : FacesStrict x01 x02 x03 x12 x13 x23) (i j : Fin 4) (hij : i ≠ j) :
    |cosX x01 x02 x03 x12 x13 x23 i j| < 1 ↔ 0 < cmDet2 x01 x02 x03 x12 x13 x23 := by
  unfold cosX
  rw [abs_div_sqrt_lt_one_iff (cof_diag_mul_pos h i j), cof_jacobi_pair _ _ _ _ _ _ i j hij]
  have := oppX_pos h i j hij
  constructor <;> intro hh <;> nlinarith

/-- **`thm:dichotomy`, wall**: `|cos θ_ij| = 1 ⇔ det CM = 0`. -/
theorem abs_cosX_eq_one_iff (h : FacesStrict x01 x02 x03 x12 x13 x23) (i j : Fin 4) (hij : i ≠ j) :
    |cosX x01 x02 x03 x12 x13 x23 i j| = 1 ↔ cmDet2 x01 x02 x03 x12 x13 x23 = 0 := by
  unfold cosX
  rw [abs_div_sqrt_eq_one_iff (cof_diag_mul_pos h i j), cof_jacobi_pair _ _ _ _ _ _ i j hij]
  have := oppX_pos h i j hij
  constructor
  · intro hh
    rcases mul_eq_zero.mp hh with h0 | h0
    · linarith
    · exact h0
  · intro hh; rw [hh]; ring

/-- **`thm:dichotomy`, forbidden side**: `|cos θ_ij| > 1 ⇔ det CM < 0`. -/
theorem one_lt_abs_cosX_iff (h : FacesStrict x01 x02 x03 x12 x13 x23) (i j : Fin 4) (hij : i ≠ j) :
    1 < |cosX x01 x02 x03 x12 x13 x23 i j| ↔ cmDet2 x01 x02 x03 x12 x13 x23 < 0 := by
  unfold cosX
  rw [one_lt_abs_div_sqrt_iff (cof_diag_mul_pos h i j), cof_jacobi_pair _ _ _ _ _ _ i j hij]
  have := oppX_pos h i j hij
  constructor <;> intro hh <;> nlinarith

/-- **`thm:dichotomy`** (`eq:flat-edge-dichotomy`, `eq:flat-edge-forbidden`): with strict faces, either
all six edges have `|cos| < 1` (`det CM > 0`), or all six `|cos| = 1` (`det CM = 0`), or all six
`|cos| > 1` (`det CM < 0`); no mixed configuration occurs. -/
theorem six_edges_trichotomy (h : FacesStrict x01 x02 x03 x12 x13 x23) :
    ((∀ i j : Fin 4, i ≠ j → |cosX x01 x02 x03 x12 x13 x23 i j| < 1) ∧
        0 < cmDet2 x01 x02 x03 x12 x13 x23) ∨
    ((∀ i j : Fin 4, i ≠ j → |cosX x01 x02 x03 x12 x13 x23 i j| = 1) ∧
        cmDet2 x01 x02 x03 x12 x13 x23 = 0) ∨
    ((∀ i j : Fin 4, i ≠ j → 1 < |cosX x01 x02 x03 x12 x13 x23 i j|) ∧
        cmDet2 x01 x02 x03 x12 x13 x23 < 0) := by
  rcases lt_trichotomy (cmDet2 x01 x02 x03 x12 x13 x23) 0 with hD | hD | hD
  · exact Or.inr (Or.inr ⟨fun i j hij => (one_lt_abs_cosX_iff h i j hij).mpr hD, hD⟩)
  · exact Or.inr (Or.inl ⟨fun i j hij => (abs_cosX_eq_one_iff h i j hij).mpr hD, hD⟩)
  · exact Or.inl ⟨fun i j hij => (abs_cosX_lt_one_iff h i j hij).mpr hD, hD⟩

theorem cof_ne_zero_of_wall (h : FacesStrict x01 x02 x03 x12 x13 x23)
    (hD : cmDet2 x01 x02 x03 x12 x13 x23 = 0) (i j : Fin 4) (hij : i ≠ j) :
    cofM x01 x02 x03 x12 x13 x23 i j ≠ 0 := by
  intro h0
  have := cof_jacobi_pair x01 x02 x03 x12 x13 x23 i j hij
  rw [h0, hD] at this
  have := cof_diag_mul_pos h i j
  nlinarith

/-- On the wall, `cos θ_ij = 1 ⇔ C_ij > 0`. -/
theorem cosX_eq_one_iff_of_wall (h : FacesStrict x01 x02 x03 x12 x13 x23)
    (hD : cmDet2 x01 x02 x03 x12 x13 x23 = 0) (i j : Fin 4) (hij : i ≠ j) :
    cosX x01 x02 x03 x12 x13 x23 i j = 1 ↔ 0 < cofM x01 x02 x03 x12 x13 x23 i j := by
  have hab := cof_diag_mul_pos h i j
  have hs : 0 < √(cofM x01 x02 x03 x12 x13 x23 i i * cofM x01 x02 x03 x12 x13 x23 j j) :=
    Real.sqrt_pos.mpr hab
  have habs := (abs_cosX_eq_one_iff h i j hij).mpr hD
  have hne := cof_ne_zero_of_wall h hD i j hij
  unfold cosX at habs ⊢
  constructor
  · intro h1
    have : 0 < cofM x01 x02 x03 x12 x13 x23 i j / √(cofM x01 x02 x03 x12 x13 x23 i i *
        cofM x01 x02 x03 x12 x13 x23 j j) := by rw [h1]; norm_num
    exact (div_pos_iff_of_pos_right hs).mp this
  · intro hc
    have : 0 < cofM x01 x02 x03 x12 x13 x23 i j / √(cofM x01 x02 x03 x12 x13 x23 i i *
        cofM x01 x02 x03 x12 x13 x23 j j) := div_pos hc hs
    rwa [abs_of_pos this] at habs

/-- On the wall, `cos θ_ij = -1 ⇔ C_ij < 0`. -/
theorem cosX_eq_neg_one_iff_of_wall (h : FacesStrict x01 x02 x03 x12 x13 x23)
    (hD : cmDet2 x01 x02 x03 x12 x13 x23 = 0) (i j : Fin 4) (hij : i ≠ j) :
    cosX x01 x02 x03 x12 x13 x23 i j = -1 ↔ cofM x01 x02 x03 x12 x13 x23 i j < 0 := by
  have hab := cof_diag_mul_pos h i j
  have hs : 0 < √(cofM x01 x02 x03 x12 x13 x23 i i * cofM x01 x02 x03 x12 x13 x23 j j) :=
    Real.sqrt_pos.mpr hab
  have habs := (abs_cosX_eq_one_iff h i j hij).mpr hD
  unfold cosX at habs ⊢
  constructor
  · intro h1
    have : cofM x01 x02 x03 x12 x13 x23 i j / √(cofM x01 x02 x03 x12 x13 x23 i i *
        cofM x01 x02 x03 x12 x13 x23 j j) < 0 := by rw [h1]; norm_num
    by_contra hc
    exact absurd (div_nonneg (not_lt.mp hc) hs.le) (not_le.mpr this)
  · intro hc
    have : cofM x01 x02 x03 x12 x13 x23 i j / √(cofM x01 x02 x03 x12 x13 x23 i i *
        cofM x01 x02 x03 x12 x13 x23 j j) < 0 := div_neg_of_neg_of_pos hc hs
    rw [abs_of_neg this] at habs
    linarith

/-- **`cor:combinatorial`**: at a wall point with strict faces, `θ_ij = 0 ⇔ C_ij > 0`. -/
theorem thetaX_eq_zero_iff_cof_pos (h : FacesStrict x01 x02 x03 x12 x13 x23)
    (hD : cmDet2 x01 x02 x03 x12 x13 x23 = 0) (i j : Fin 4) (hij : i ≠ j) :
    thetaX x01 x02 x03 x12 x13 x23 i j = 0 ↔ 0 < cofM x01 x02 x03 x12 x13 x23 i j := by
  rw [thetaX_eq_arccos_cosX, Real.arccos_eq_zero, ← cosX_eq_one_iff_of_wall h hD i j hij]
  have := (abs_cosX_eq_one_iff h i j hij).mpr hD
  constructor
  · intro h1
    have h2 := (abs_le.mp this.le).2
    linarith
  · intro h1; exact h1.ge

/-- **`cor:combinatorial`**: at a wall point with strict faces, `θ_ij = π ⇔ C_ij < 0`. -/
theorem thetaX_eq_pi_iff_cof_neg (h : FacesStrict x01 x02 x03 x12 x13 x23)
    (hD : cmDet2 x01 x02 x03 x12 x13 x23 = 0) (i j : Fin 4) (hij : i ≠ j) :
    thetaX x01 x02 x03 x12 x13 x23 i j = Real.pi ↔ cofM x01 x02 x03 x12 x13 x23 i j < 0 := by
  rw [thetaX_eq_arccos_cosX, Real.arccos_eq_pi, ← cosX_eq_neg_one_iff_of_wall h hD i j hij]
  have := (abs_cosX_eq_one_iff h i j hij).mpr hD
  constructor
  · intro h1
    have h2 := (abs_le.mp this.le).1
    linarith
  · intro h1; exact h1.le

/-- **`cor:combinatorial`**: at a wall point with strict faces every interior dihedral angle is `0` or
`π` (the caustic angle data are combinatorial). -/
theorem thetaX_eq_zero_or_pi_of_wall (h : FacesStrict x01 x02 x03 x12 x13 x23)
    (hD : cmDet2 x01 x02 x03 x12 x13 x23 = 0) (i j : Fin 4) (hij : i ≠ j) :
    thetaX x01 x02 x03 x12 x13 x23 i j = 0 ∨ thetaX x01 x02 x03 x12 x13 x23 i j = Real.pi := by
  have hne := cof_ne_zero_of_wall h hD i j hij
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact Or.inr ((thetaX_eq_pi_iff_cof_neg h hD i j hij).mpr hlt)
  · exact Or.inl ((thetaX_eq_zero_iff_cof_pos h hD i j hij).mpr hgt)

end Dichotomy

section GramCos

/-- Gram form of the cofactors at the vertex `0` (`G = gramX x`, indices `0,1,2` are the edges
`01, 02, 03`): `C₂₃ = 4 (G₀₀G₁₂ - G₀₁G₀₂)`, the numerator of `eq:gramcos` for the edge `01`. -/
theorem cof23_eq_gram (x01 x02 x03 x12 x13 x23 : ℝ) :
    cof23 x01 x02 x03 x12 x13 x23 = 4 * (gramX x01 x02 x03 x12 x13 x23 0 0 *
      gramX x01 x02 x03 x12 x13 x23 1 2 - gramX x01 x02 x03 x12 x13 x23 0 1 *
      gramX x01 x02 x03 x12 x13 x23 0 2) := by
  simp [gramX, cof23]; ring

theorem cof13_eq_gram (x01 x02 x03 x12 x13 x23 : ℝ) :
    cof13 x01 x02 x03 x12 x13 x23 = 4 * (gramX x01 x02 x03 x12 x13 x23 1 1 *
      gramX x01 x02 x03 x12 x13 x23 0 2 - gramX x01 x02 x03 x12 x13 x23 0 1 *
      gramX x01 x02 x03 x12 x13 x23 1 2) := by
  simp [gramX, cof13]; ring

theorem cof12_eq_gram (x01 x02 x03 x12 x13 x23 : ℝ) :
    cof12 x01 x02 x03 x12 x13 x23 = 4 * (gramX x01 x02 x03 x12 x13 x23 2 2 *
      gramX x01 x02 x03 x12 x13 x23 0 1 - gramX x01 x02 x03 x12 x13 x23 0 2 *
      gramX x01 x02 x03 x12 x13 x23 1 2) := by
  simp [gramX, cof12]; ring

/-- The face minors: `C₁₁ = -4 (G₀₀... )`; the face opposite the vertex `j+1`... (see the three
lemmas): `C₃₃ = -4 (G₀₀G₁₁ - G₀₁²)`. -/
theorem cof33_eq_gram (x01 x02 x03 x12 x13 x23 : ℝ) :
    cof33 x01 x02 x03 x12 x13 x23 = -4 * (gramX x01 x02 x03 x12 x13 x23 0 0 *
      gramX x01 x02 x03 x12 x13 x23 1 1 - gramX x01 x02 x03 x12 x13 x23 0 1 ^ 2) := by
  simp [gramX, cof33]; ring

theorem cof22_eq_gram (x01 x02 x03 x12 x13 x23 : ℝ) :
    cof22 x01 x02 x03 x12 x13 x23 = -4 * (gramX x01 x02 x03 x12 x13 x23 0 0 *
      gramX x01 x02 x03 x12 x13 x23 2 2 - gramX x01 x02 x03 x12 x13 x23 0 2 ^ 2) := by
  simp [gramX, cof22]; ring

theorem cof11_eq_gram (x01 x02 x03 x12 x13 x23 : ℝ) :
    cof11 x01 x02 x03 x12 x13 x23 = -4 * (gramX x01 x02 x03 x12 x13 x23 1 1 *
      gramX x01 x02 x03 x12 x13 x23 2 2 - gramX x01 x02 x03 x12 x13 x23 1 2 ^ 2) := by
  simp [gramX, cof11]; ring

theorem four_div_sqrt_aux (N A B : ℝ) : 4 * N / √((-4 * B) * (-4 * A)) = N / √(A * B) := by
  have h16 : (-4 * B) * (-4 * A) = 16 * (A * B) := by ring
  have hs16 : √(16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [h16, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16), hs16,
    mul_div_mul_left _ _ (by norm_num : (4 : ℝ) ≠ 0)]

/-- **`eq:gramcos`** for the edge `01` (faces `2`, `3`): the interior dihedral cosine in vertex-Gram form,
`(G_uuG_vw - G_uvG_uw)/√((G_uuG_vv - G_uv²)(G_uuG_ww - G_uw²))` with `u,v,w = 0,1,2`
(edges `01,02,03`). -/
theorem cosX_eq_gram_23 (x01 x02 x03 x12 x13 x23 : ℝ) :
    cosX x01 x02 x03 x12 x13 x23 2 3 =
      (gramX x01 x02 x03 x12 x13 x23 0 0 * gramX x01 x02 x03 x12 x13 x23 1 2 -
          gramX x01 x02 x03 x12 x13 x23 0 1 * gramX x01 x02 x03 x12 x13 x23 0 2) /
        √((gramX x01 x02 x03 x12 x13 x23 0 0 * gramX x01 x02 x03 x12 x13 x23 1 1 -
            gramX x01 x02 x03 x12 x13 x23 0 1 ^ 2) *
          (gramX x01 x02 x03 x12 x13 x23 0 0 * gramX x01 x02 x03 x12 x13 x23 2 2 -
            gramX x01 x02 x03 x12 x13 x23 0 2 ^ 2)) := by
  have e23 : cofM x01 x02 x03 x12 x13 x23 2 3 = cof23 x01 x02 x03 x12 x13 x23 := by simp [cofM]
  have e22 : cofM x01 x02 x03 x12 x13 x23 2 2 = cof22 x01 x02 x03 x12 x13 x23 := by simp [cofM]
  have e33 : cofM x01 x02 x03 x12 x13 x23 3 3 = cof33 x01 x02 x03 x12 x13 x23 := by simp [cofM]
  unfold cosX
  rw [e23, e22, e33, cof23_eq_gram, cof22_eq_gram, cof33_eq_gram]
  exact four_div_sqrt_aux _ _ _

/-- **`eq:gramcos`** for the edge `02` (faces `1`, `3`), `u,v,w = 1,0,2`. -/
theorem cosX_eq_gram_13 (x01 x02 x03 x12 x13 x23 : ℝ) :
    cosX x01 x02 x03 x12 x13 x23 1 3 =
      (gramX x01 x02 x03 x12 x13 x23 1 1 * gramX x01 x02 x03 x12 x13 x23 0 2 -
          gramX x01 x02 x03 x12 x13 x23 0 1 * gramX x01 x02 x03 x12 x13 x23 1 2) /
        √((gramX x01 x02 x03 x12 x13 x23 0 0 * gramX x01 x02 x03 x12 x13 x23 1 1 -
            gramX x01 x02 x03 x12 x13 x23 0 1 ^ 2) *
          (gramX x01 x02 x03 x12 x13 x23 1 1 * gramX x01 x02 x03 x12 x13 x23 2 2 -
            gramX x01 x02 x03 x12 x13 x23 1 2 ^ 2)) := by
  have e13 : cofM x01 x02 x03 x12 x13 x23 1 3 = cof13 x01 x02 x03 x12 x13 x23 := by simp [cofM]
  have e11 : cofM x01 x02 x03 x12 x13 x23 1 1 = cof11 x01 x02 x03 x12 x13 x23 := by simp [cofM]
  have e33 : cofM x01 x02 x03 x12 x13 x23 3 3 = cof33 x01 x02 x03 x12 x13 x23 := by simp [cofM]
  unfold cosX
  rw [e13, e11, e33, cof13_eq_gram, cof11_eq_gram, cof33_eq_gram]
  exact four_div_sqrt_aux _ _ _

/-- **`eq:gramcos`** for the edge `03` (faces `1`, `2`), `u,v,w = 2,0,1`. -/
theorem cosX_eq_gram_12 (x01 x02 x03 x12 x13 x23 : ℝ) :
    cosX x01 x02 x03 x12 x13 x23 1 2 =
      (gramX x01 x02 x03 x12 x13 x23 2 2 * gramX x01 x02 x03 x12 x13 x23 0 1 -
          gramX x01 x02 x03 x12 x13 x23 0 2 * gramX x01 x02 x03 x12 x13 x23 1 2) /
        √((gramX x01 x02 x03 x12 x13 x23 0 0 * gramX x01 x02 x03 x12 x13 x23 2 2 -
            gramX x01 x02 x03 x12 x13 x23 0 2 ^ 2) *
          (gramX x01 x02 x03 x12 x13 x23 1 1 * gramX x01 x02 x03 x12 x13 x23 2 2 -
            gramX x01 x02 x03 x12 x13 x23 1 2 ^ 2)) := by
  have e12 : cofM x01 x02 x03 x12 x13 x23 1 2 = cof12 x01 x02 x03 x12 x13 x23 := by simp [cofM]
  have e11 : cofM x01 x02 x03 x12 x13 x23 1 1 = cof11 x01 x02 x03 x12 x13 x23 := by simp [cofM]
  have e22 : cofM x01 x02 x03 x12 x13 x23 2 2 = cof22 x01 x02 x03 x12 x13 x23 := by simp [cofM]
  unfold cosX
  rw [e12, e11, e22, cof12_eq_gram, cof11_eq_gram, cof22_eq_gram]
  exact four_div_sqrt_aux _ _ _

end GramCos

section Blumenthal

/-- The characteristic polynomial of a `3×3` matrix in terms of principal minors:
`det (G - μ) = det G - μ (m₀₁ + m₀₂ + m₁₂) + μ² tr G - μ³`. -/
theorem det_sub_smul_one_fin3 (G : Matrix (Fin 3) (Fin 3) ℝ) (μ : ℝ) :
    (G - μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det =
      G.det - μ * ((G 0 0 * G 1 1 - G 0 1 * G 1 0) + (G 0 0 * G 2 2 - G 0 2 * G 2 0) +
        (G 1 1 * G 2 2 - G 1 2 * G 2 1)) + μ ^ 2 * (G 0 0 + G 1 1 + G 2 2) - μ ^ 3 := by
  simp [Matrix.det_fin_three]
  ring

/-- **Positive semidefiniteness of a real symmetric `3×3` matrix from its principal minors**
(the direction of Sylvester's criterion needed for Blumenthal): the diagonal entries, the three
`2×2` principal minors and the determinant are all `≥ 0`.  Proof: an eigenvalue `μ < 0` would give
`0 = det (G - μ) = det G - μ ∑ m₂ + μ² tr G - μ³ > 0`. -/
theorem posSemidef_fin3_of_minors (G : Matrix (Fin 3) (Fin 3) ℝ) (hs : ∀ i j, G i j = G j i)
    (h0 : 0 ≤ G 0 0) (h1 : 0 ≤ G 1 1) (h2 : 0 ≤ G 2 2)
    (m01 : 0 ≤ G 0 0 * G 1 1 - G 0 1 ^ 2) (m02 : 0 ≤ G 0 0 * G 2 2 - G 0 2 ^ 2)
    (m12 : 0 ≤ G 1 1 * G 2 2 - G 1 2 ^ 2) (hd : 0 ≤ G.det) : G.PosSemidef := by
  have hH : G.IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, hs i j]
  rw [hH.posSemidef_iff_eigenvalues_nonneg]
  intro j
  by_contra hneg
  have hμ : hH.eigenvalues j < 0 := not_le.mp hneg
  set μ := hH.eigenvalues j with hμdef
  have hv : (⇑(hH.eigenvectorBasis j) : Fin 3 → ℝ) ≠ 0 := by
    intro h
    have := (hH.eigenvectorBasis.orthonormal.ne_zero j)
    apply this
    ext i
    simpa using congrFun h i
  have hker : (G - μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ ⇑(hH.eigenvectorBasis j) = 0 := by
    rw [Matrix.sub_mulVec, hH.mulVec_eigenvectorBasis, Matrix.smul_mulVec, Matrix.one_mulVec,
      ← hμdef]
    exact sub_self _
  have hdet : (G - μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hv, hker⟩
  rw [det_sub_smul_one_fin3, hs 1 0, hs 2 0, hs 2 1] at hdet
  have e1 : G 0 0 * G 1 1 - G 0 1 * G 0 1 = G 0 0 * G 1 1 - G 0 1 ^ 2 := by ring
  have e2 : G 0 0 * G 2 2 - G 0 2 * G 0 2 = G 0 0 * G 2 2 - G 0 2 ^ 2 := by ring
  have e3 : G 1 1 * G 2 2 - G 1 2 * G 1 2 = G 1 1 * G 2 2 - G 1 2 ^ 2 := by ring
  rw [e1, e2, e3] at hdet
  have t1 : 0 ≤ -μ * ((G 0 0 * G 1 1 - G 0 1 ^ 2) + (G 0 0 * G 2 2 - G 0 2 ^ 2) +
      (G 1 1 * G 2 2 - G 1 2 ^ 2)) := by
    apply mul_nonneg (by linarith); linarith
  have t2 : 0 ≤ μ ^ 2 * (G 0 0 + G 1 1 + G 2 2) := by positivity
  have t3 : 0 < -μ ^ 3 := by nlinarith [sq_nonneg μ, mul_pos_of_neg_of_neg hμ hμ]
  nlinarith

end Blumenthal

section BlumenthalGram

variable {x01 x02 x03 x12 x13 x23 : ℝ}

theorem gramX_symm (x01 x02 x03 x12 x13 x23 : ℝ) (i j : Fin 3) :
    gramX x01 x02 x03 x12 x13 x23 i j = gramX x01 x02 x03 x12 x13 x23 j i := by
  fin_cases i <;> fin_cases j <;> simp [gramX]

/-- **Blumenthal, Gram form of the converse**: nonnegative squared edges at the vertex `0`, the three
triangle inequalities of the faces through `0` (`C_ii ≤ 0`) and `det CM ≥ 0` make `gramX x` positive
semidefinite. -/
theorem posSemidef_gramX_of_blumenthal (hx01 : 0 ≤ x01) (hx02 : 0 ≤ x02) (hx03 : 0 ≤ x03)
    (h1 : cof11 x01 x02 x03 x12 x13 x23 ≤ 0) (h2 : cof22 x01 x02 x03 x12 x13 x23 ≤ 0)
    (h3 : cof33 x01 x02 x03 x12 x13 x23 ≤ 0) (hD : 0 ≤ cmDet2 x01 x02 x03 x12 x13 x23) :
    (gramX x01 x02 x03 x12 x13 x23).PosSemidef := by
  apply posSemidef_fin3_of_minors _ (gramX_symm x01 x02 x03 x12 x13 x23)
  · simpa [gramX] using hx01
  · simpa [gramX] using hx02
  · simpa [gramX] using hx03
  · have := cof33_eq_gram x01 x02 x03 x12 x13 x23
    linarith
  · have := cof22_eq_gram x01 x02 x03 x12 x13 x23
    linarith
  · have := cof11_eq_gram x01 x02 x03 x12 x13 x23
    linarith
  · have := cmDet2_eq_eight_det_gramX x01 x02 x03 x12 x13 x23
    linarith

/-- **Blumenthal's realisation theorem** (`eq:cm`, converse): six numbers `x_e ≥ 0` with `det CM ≥ 0`
and the triangle inequalities `C_ii ≤ 0` on the faces through the vertex `0` are the squared
distances of four points of `ℝ³`. -/
theorem exists_points_of_blumenthal (hx01 : 0 ≤ x01) (hx02 : 0 ≤ x02) (hx03 : 0 ≤ x03)
    (h1 : cof11 x01 x02 x03 x12 x13 x23 ≤ 0) (h2 : cof22 x01 x02 x03 x12 x13 x23 ≤ 0)
    (h3 : cof33 x01 x02 x03 x12 x13 x23 ≤ 0) (hD : 0 ≤ cmDet2 x01 x02 x03 x12 x13 x23) :
    ∃ p : Fin 4 → R3, sqd p 0 1 = x01 ∧ sqd p 0 2 = x02 ∧ sqd p 0 3 = x03 ∧
      sqd p 1 2 = x12 ∧ sqd p 1 3 = x13 ∧ sqd p 2 3 = x23 :=
  exists_points_of_posSemidef_gramX
    (posSemidef_gramX_of_blumenthal hx01 hx02 hx03 h1 h2 h3 hD)

/-- **Blumenthal's criterion for four points** (full form): six numbers `x_e ≥ 0` are the squared
distances of four points of `ℝ³` if and only if `det CM ≥ 0` and the four faces satisfy the triangle
inequalities (`C_ii ≤ 0`, i.e. Heron's expression is `≥ 0`). -/
theorem blumenthal_iff {x01 x02 x03 x12 x13 x23 : ℝ} :
    (0 ≤ x01 ∧ 0 ≤ x02 ∧ 0 ≤ x03 ∧ 0 ≤ x12 ∧ 0 ≤ x13 ∧ 0 ≤ x23 ∧
      cof00 x01 x02 x03 x12 x13 x23 ≤ 0 ∧ cof11 x01 x02 x03 x12 x13 x23 ≤ 0 ∧
      cof22 x01 x02 x03 x12 x13 x23 ≤ 0 ∧ cof33 x01 x02 x03 x12 x13 x23 ≤ 0 ∧
      0 ≤ cmDet2 x01 x02 x03 x12 x13 x23) ↔
    ∃ p : Fin 4 → R3, sqd p 0 1 = x01 ∧ sqd p 0 2 = x02 ∧ sqd p 0 3 = x03 ∧
      sqd p 1 2 = x12 ∧ sqd p 1 3 = x13 ∧ sqd p 2 3 = x23 := by
  constructor
  · rintro ⟨a, b, c, _, _, _, _, h1, h2, h3, hD⟩
    exact exists_points_of_blumenthal a b c h1 h2 h3 hD
  · rintro ⟨p, e01, e02, e03, e12, e13, e23⟩
    subst e01 e02 e03 e12 e13 e23
    have hc : ∀ i : Fin 4, cofP p i i ≤ 0 := fun i => by
      have := norm_sq_areaVec p i
      nlinarith [sq_nonneg ‖areaVec p i‖]
    refine ⟨by unfold sqd; positivity, by unfold sqd; positivity, by unfold sqd; positivity,
      by unfold sqd; positivity, by unfold sqd; positivity, by unfold sqd; positivity,
      ?_, ?_, ?_, ?_, cmPts_nonneg p⟩
    · simpa [cofP, cofM] using hc 0
    · simpa [cofP, cofM] using hc 1
    · simpa [cofP, cofM] using hc 2
    · simpa [cofP, cofM] using hc 3

end BlumenthalGram

/-- info: 'FormalResearch.EuclTet.cof_jacobi_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cof_jacobi_pair

/-- info: 'FormalResearch.EuclTet.abs_cosX_lt_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abs_cosX_lt_one_iff

/-- info: 'FormalResearch.EuclTet.abs_cosX_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abs_cosX_eq_one_iff

/-- info: 'FormalResearch.EuclTet.one_lt_abs_cosX_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_lt_abs_cosX_iff

/-- info: 'FormalResearch.EuclTet.six_edges_trichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms six_edges_trichotomy

/-- info: 'FormalResearch.EuclTet.thetaX_eq_zero_iff_cof_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thetaX_eq_zero_iff_cof_pos

/-- info: 'FormalResearch.EuclTet.thetaX_eq_pi_iff_cof_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thetaX_eq_pi_iff_cof_neg

/-- info: 'FormalResearch.EuclTet.thetaX_eq_zero_or_pi_of_wall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thetaX_eq_zero_or_pi_of_wall

/-- info: 'FormalResearch.EuclTet.cosX_eq_gram_23' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cosX_eq_gram_23

/-- info: 'FormalResearch.EuclTet.cosX_eq_gram_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cosX_eq_gram_13

/-- info: 'FormalResearch.EuclTet.cosX_eq_gram_12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cosX_eq_gram_12

/-- info: 'FormalResearch.EuclTet.posSemidef_fin3_of_minors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms posSemidef_fin3_of_minors

/-- info: 'FormalResearch.EuclTet.posSemidef_gramX_of_blumenthal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms posSemidef_gramX_of_blumenthal

/-- info: 'FormalResearch.EuclTet.exists_points_of_blumenthal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_points_of_blumenthal

/-- info: 'FormalResearch.EuclTet.blumenthal_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms blumenthal_iff

end FormalResearch.EuclTet
