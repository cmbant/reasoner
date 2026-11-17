module

public import Mathlib
public import FormalResearch.EuclTet.Dichotomy

/-!
# The Racah turning curve is the flat-tetrahedron locus: the geometric half of `lem:racah-cayley-menger`

Source: Weyl/P3 `lem:racah-cayley-menger` (`eq:racah-cayley-menger`) and the remark "Geometric check for genuine
tetrahedra" of its proof (appendix): for the principal Weyl tetrahedron `(A,B,C;B,A,F)` with
`A = Nα`, `B = Nβ`, `C = Nγ`, `F = Nρ`, `D₆ > 0` is the nondegenerate Euclidean tetrahedron, `D₆ = 0` the flat
one, and for `D₆ < 0` the six lengths are not those of any Euclidean tetrahedron; `288 𝒱² = 8N⁶ρ²α²β²D₆`.

The algebraic identity (`det CM = 8N⁶ρ²α²β²D₆`, both forms, sign trichotomy, `faces_admissible`) is
`FormalResearch.Racah.P3CayleyMenger`; this module combines it with `FormalResearch.EuclTet.Gram`
(`det CM = 288 V²` for points of `ℝ³`) and Blumenthal's criterion of `FormalResearch.EuclTet.Dichotomy`.

Vertices `0,1,2,3` of the tetrahedron are the paper's `1,2,3,4`: `|p₀p₁| = A`, `|p₁p₂| = B`, `|p₀p₂| = C`,
`|p₂p₃| = B`, `|p₀p₃| = A`, `|p₁p₃| = F`.

## What is formalised (exact, proved)

* `RacahDist p N α β γ ρ`: the six distance conditions.
* `racah_exists_points_of_D6_nonneg` (**existence**): for `N, α, β, γ, ρ > 0` with `D₆ ≥ 0` there are four points of
  `ℝ³` with these distances.  The four faces are shown to satisfy the triangle inequalities directly from
  `D₆ ≥ 0` (the `(α,β,γ)` faces from `16T² ≥ γ²ρ²`, the faces `(A,A,F)`, `(B,B,F)` from `ρ² ≤ 4α², 4β²`).
* `racah_no_points_of_D6_neg` (**non-existence**): for `D₆ < 0` no four points of `ℝ³` have these distances
  (`det CM = 288 V² ≥ 0`).  `racah_exists_points_iff`: existence `⇔ D₆ ≥ 0`.
* `racah_tetVol_sq` (**`288 𝒱² = 8N⁶ρ²α²β²D₆`**): for every realisation, `𝒱² = N⁶ρ²α²β² D₆/36`, with `𝒱 = tetVol`;
  `racah_tetVol_pos_iff`, `racah_tetVol_eq_zero_iff`: `𝒱 > 0 ⇔ D₆ > 0` (nondegenerate), `𝒱 = 0 ⇔ D₆ = 0` (flat).

## Not formalised

* `𝒱 = F r_A r_B sin ω/6` with the geometric `ω` (the dihedral angle `Θ_F`) as a statement about the points
  (`P3CayleyMenger.volume_formula` is the identity of squares); the identification of `tetVol` with the Lebesgue
  measure of the convex hull.
-/

@[expose] public section

namespace FormalResearch.EuclTet

open FormalResearch.Racah.P3

/-- The six distance conditions of the principal Weyl tetrahedron `(A,B,C;B,A,F)` on the points `p₀..p₃`. -/
def RacahDist (p : Fin 4 → R3) (N α β γ ρ : ℝ) : Prop :=
  dist (p 0) (p 1) = N * α ∧ dist (p 0) (p 2) = N * γ ∧ dist (p 0) (p 3) = N * α ∧
    dist (p 1) (p 2) = N * β ∧ dist (p 1) (p 3) = N * ρ ∧ dist (p 2) (p 3) = N * β

theorem cmPts_eq_cmRacah {p : Fin 4 → R3} {N α β γ ρ : ℝ} (h : RacahDist p N α β γ ρ) :
    cmPts p = cmRacah N α β γ ρ := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := h
  unfold cmPts cmRacah
  rw [cmDet_eq_cmDet2, sqd_eq_dist_sq, sqd_eq_dist_sq, sqd_eq_dist_sq, sqd_eq_dist_sq,
    sqd_eq_dist_sq, sqd_eq_dist_sq, h01, h02, h03, h12, h13, h23]

/-- **`288 𝒱² = 8N⁶ρ²α²β²D₆`** for every realisation of the principal Weyl tetrahedron. -/
theorem racah_tetVol_sq {p : Fin 4 → R3} {N α β γ ρ : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0)
    (h : RacahDist p N α β γ ρ) :
    288 * tetVol p ^ 2 = 8 * N ^ 6 * ρ ^ 2 * α ^ 2 * β ^ 2 * D6lin α β γ ρ := by
  rw [← cmPts_eq_288_tetVol_sq, cmPts_eq_cmRacah h]
  exact (cmDet_racah_D6 hα hβ N γ ρ).1

theorem racah_tetVol_pos_iff {p : Fin 4 → R3} {N α β γ ρ : ℝ} (hN : N ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hρ : ρ ≠ 0) (h : RacahDist p N α β γ ρ) : 0 < tetVol p ↔ 0 < D6lin α β γ ρ := by
  rw [tetVol_pos_iff, cmPts_eq_cmRacah h]
  exact cmDet_pos_iff hN hα hβ hρ γ

theorem racah_tetVol_eq_zero_iff {p : Fin 4 → R3} {N α β γ ρ : ℝ} (hN : N ≠ 0) (hα : α ≠ 0)
    (hβ : β ≠ 0) (hρ : ρ ≠ 0) (h : RacahDist p N α β γ ρ) :
    tetVol p = 0 ↔ D6lin α β γ ρ = 0 := by
  have h0 : 0 ≤ tetVol p := by unfold tetVol; positivity
  have hD6 : 0 ≤ D6lin α β γ ρ ∨ D6lin α β γ ρ < 0 := le_or_gt _ _
  constructor
  · intro hv
    have := racah_tetVol_sq hα hβ h
    rw [hv] at this
    have hpos : 0 < 8 * N ^ 6 * ρ ^ 2 * α ^ 2 * β ^ 2 := by positivity
    have : D6lin α β γ ρ = 0 := by
      rcases mul_eq_zero.mp (by linarith : 8 * N ^ 6 * ρ ^ 2 * α ^ 2 * β ^ 2 * D6lin α β γ ρ = 0)
        with h1 | h1
      · exact absurd h1 hpos.ne'
      · exact h1
    exact this
  · intro hD
    by_contra hne
    have := (racah_tetVol_pos_iff hN hα hβ hρ h).mp (lt_of_le_of_ne h0 (Ne.symm hne))
    linarith

/-- **Non-existence for `D₆ < 0`**: the six lengths are not those of any Euclidean tetrahedron. -/
theorem racah_no_points_of_D6_neg {N α β γ ρ : ℝ} (hN : N ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hρ : ρ ≠ 0) (hD : D6lin α β γ ρ < 0) : ¬ ∃ p : Fin 4 → R3, RacahDist p N α β γ ρ := by
  rintro ⟨p, hp⟩
  have h1 := cmPts_nonneg p
  rw [cmPts_eq_cmRacah hp] at h1
  have := (cmDet_neg_iff hN hα hβ hρ γ).mpr hD
  linarith

/-- **Existence for `D₆ ≥ 0`** (Blumenthal): for positive `N, α, β, γ, ρ` with `D₆ ≥ 0` the six lengths of
the principal Weyl tetrahedron are realised by four points of `ℝ³`. -/
theorem racah_exists_points_of_D6_nonneg {N α β γ ρ : ℝ} (hN : 0 < N) (hα : 0 < α) (hβ : 0 < β)
    (hγ : 0 < γ) (hρ : 0 < ρ) (hD : 0 ≤ D6lin α β γ ρ) :
    ∃ p : Fin 4 → R3, RacahDist p N α β γ ρ := by
  have hP : 0 ≤ 4 * α ^ 2 * β ^ 2 - (α ^ 2 + β ^ 2 - γ ^ 2) ^ 2 - γ ^ 2 * ρ ^ 2 := by
    rw [D6lin_eq hα.ne' hβ.ne'] at hD
    exact (div_nonneg_iff.mp hD).elim (fun h => h.1) (fun h => by
      have : (0 : ℝ) < 4 * α ^ 2 * β ^ 2 := by positivity
      linarith [h.2])
  have hγ2 : 0 < γ ^ 2 := by positivity
  have hρα : ρ ^ 2 ≤ 4 * α ^ 2 := by
    by_contra h
    have h := lt_of_not_ge h
    nlinarith [sq_nonneg (α ^ 2 - β ^ 2 + γ ^ 2), mul_lt_mul_of_pos_left h hγ2]
  have hρβ : ρ ^ 2 ≤ 4 * β ^ 2 := by
    by_contra h
    have h := lt_of_not_ge h
    nlinarith [sq_nonneg (β ^ 2 - α ^ 2 + γ ^ 2), mul_lt_mul_of_pos_left h hγ2]
  have hN4 : 0 < N ^ 4 := by positivity
  have hdet : 0 ≤ cmRacah N α β γ ρ := by
    rw [cmDet_racah_poly]; positivity
  have hX := cmDet_eq_cmDet2 (N * α) (N * β) (N * γ) (N * β) (N * α) (N * ρ)
  obtain ⟨p, e01, e02, e03, e12, e13, e23⟩ := exists_points_of_blumenthal
    (x01 := (N * α) ^ 2) (x02 := (N * γ) ^ 2) (x03 := (N * α) ^ 2) (x12 := (N * β) ^ 2)
    (x13 := (N * ρ) ^ 2) (x23 := (N * β) ^ 2) (by positivity) (by positivity) (by positivity)
    (by
      rw [cof11_eq_heron]
      nlinarith [mul_nonneg hN4.le (mul_nonneg (sq_nonneg ρ) (sub_nonneg.mpr hρβ)),
        mul_nonneg hN4.le hP])
    (by
      rw [cof22_eq_heron]
      nlinarith [mul_nonneg hN4.le (mul_nonneg (sq_nonneg ρ) (sub_nonneg.mpr hρα))])
    (by
      rw [cof33_eq_heron]
      nlinarith [mul_nonneg hN4.le hP, mul_nonneg hN4.le (mul_nonneg hγ2.le (sq_nonneg ρ))])
    (by rw [← hX]; exact hdet)
  refine ⟨p, ?_⟩
  have key : ∀ i j : Fin 4, ∀ r : ℝ, 0 ≤ r → sqd p i j = r ^ 2 → dist (p i) (p j) = r := by
    intro i j r hr h
    rw [sqd_eq_dist_sq] at h
    exact (sq_eq_sq₀ dist_nonneg hr).mp h
  exact ⟨key 0 1 _ (by positivity) e01, key 0 2 _ (by positivity) e02, key 0 3 _ (by positivity) e03,
    key 1 2 _ (by positivity) e12, key 1 3 _ (by positivity) e13, key 2 3 _ (by positivity) e23⟩

/-- **The Racah turning curve is the flat-tetrahedron locus** (`lem:racah-cayley-menger`, geometric
half): for positive `N, α, β, γ, ρ`, the principal Weyl tetrahedron exists in `ℝ³` iff `D₆ ≥ 0`. -/
theorem racah_exists_points_iff {N α β γ ρ : ℝ} (hN : 0 < N) (hα : 0 < α) (hβ : 0 < β)
    (hγ : 0 < γ) (hρ : 0 < ρ) :
    (∃ p : Fin 4 → R3, RacahDist p N α β γ ρ) ↔ 0 ≤ D6lin α β γ ρ := by
  constructor
  · intro h
    by_contra hneg
    exact racah_no_points_of_D6_neg hN.ne' hα.ne' hβ.ne' hρ.ne' (lt_of_not_ge hneg) h
  · exact racah_exists_points_of_D6_nonneg hN hα hβ hγ hρ

/-- info: 'FormalResearch.EuclTet.racah_exists_points_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_exists_points_iff

/-- info: 'FormalResearch.EuclTet.racah_tetVol_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_tetVol_sq

/-- info: 'FormalResearch.EuclTet.racah_tetVol_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_tetVol_pos_iff

/-- info: 'FormalResearch.EuclTet.racah_tetVol_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_tetVol_eq_zero_iff

/-- info: 'FormalResearch.EuclTet.racah_no_points_of_D6_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_no_points_of_D6_neg

end FormalResearch.EuclTet
