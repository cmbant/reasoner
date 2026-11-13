module

public import FormalResearch.Racah.P2RacahPolyOrth

/-!
# The ground-state transform is the Racah difference operator (Weyl P2,
`eq:RacahGroundTransform`, `eq:RacahPolyEigenvalue`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, subsection *Explicit physical Racah-polynomial
realization*.  Canonical sector `|n| ≤ m`.

* `groundTransform`: `(ℒ_R p)(c) = Φ_m(c)^{-1} ((H_R - m(m+1))(Φ_m p))(c)` on `ℓ(𝒞)`.
* `groundTransform_eq`: for every sequence `p`, `ℒ_R p (c_i) = B(i)(p(i+1)-p(i)) + D(i)(p(i-1)-p(i))`,
  the standard Racah difference operator with the physical parameters (`physRacahB`, `physRacahD`;
  absent boundary terms have zero coefficient).
* `groundTransform_physR`: `ℒ_R ℛ_r = r(r+2m+1) ℛ_r` (`eq:RacahPolyEigenvalue`), `0 ≤ r ≤ D`.
-/

@[expose] public section

namespace FormalResearch.Racah.SixJ

open FormalResearch.Wigner FormalResearch.Racah.RacahPoly

/-- `(ℒ_R p)(c_i) = Φ_m(c_i)^{-1} ((H_R - m(m+1))(Φ_m p))(c_i)` (`eq:RacahGroundTransform`),
`p : Fin (D+1) → ℝ` a function on the lattice. -/
noncomputable def groundTransform (a b m n : ℚ) (D : ℕ) (p : Fin (D + 1) → ℝ) (i : Fin (D + 1)) : ℝ :=
  (Phi6 a b (cPt a b m n i) m m n)⁻¹ *
    ((HR a b m n D).mulVec (fun j => Phi6 a b (cPt a b m n j) m m n * p j) i -
      (m : ℝ) * ((m : ℝ) + 1) * (Phi6 a b (cPt a b m n i) m m n * p i))

/-- **`eq:RacahGroundTransform`: `ℒ_R` is exactly the standard Racah difference operator.**  For
every sequence `P : ℕ → ℝ` (values at `y = c - c_min`),
`(ℒ_R P)(y) = B(y)(P(y+1)-P(y)) + D(y)(P(y-1)-P(y))` with the physical Racah coefficients
`B = physRacahB`, `D = physRacahD` of the parameters `eq:physicalRacahParameters`. -/
theorem groundTransform_eq {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (hcan : |n| ≤ m)
    (P : ℕ → ℝ) (i : Fin (D + 1)) :
    groundTransform a b m n D (fun j => P j) i =
      physRacahB a b m n D (i : ℕ) * (P ((i : ℕ) + 1) - P i) +
        physRacahD a b m n D (i : ℕ) * (P ((i : ℕ) - 1) - P i) := by
  have hm := mem_rank h hcan 0 (Nat.zero_le _)
  simp only [Nat.cast_zero, add_zero] at hm
  have hy : (i : ℕ) ≤ D := by omega
  have hc := mem_lattice h i hy
  have P0 : 0 < Phi6 a b (cMin a b m n + (i : ℕ)) m m n :=
    Phi6_seed_pos _ _ _ _ _ hm.1 hm.2 hc.1 hc.2
  have hP := offPlus h hcan i hy
  have hM := offMinus h hcan i hy
  have eq0 := row_rank h hcan 0 i (Nat.zero_le _) hy
  simp only [Nat.cast_zero, add_zero] at eq0
  have hH := HR_mulVec a b m n D (fun j => Phi6 a b (cPt a b m n j) m m n * P j) i
  unfold groundTransform
  rw [hH]
  have hcP : cPt a b m n i = cMin a b m n + ((i : ℕ) : ℚ) := rfl
  -- the neighbours
  have hup : aPlus a b m n (cPt a b m n i) *
      (if hh : (i : ℕ) + 1 < D + 1 then
        Phi6 a b (cPt a b m n ⟨(i : ℕ) + 1, hh⟩) m m n * P ((i : ℕ) + 1) else 0) =
      -physRacahB a b m n D (i : ℕ) * Phi6 a b (cMin a b m n + (i : ℕ)) m m n * P ((i : ℕ) + 1) := by
    split_ifs with hh
    · have e : cPt a b m n (⟨(i : ℕ) + 1, hh⟩ : Fin (D + 1)) = cMin a b m n + (i : ℕ) + 1 := by
        unfold cPt; push_cast; ring
      rw [e, hcP]
      have := hP
      linear_combination (P ((i : ℕ) + 1)) * this
    · have hiD : (i : ℕ) = D := by omega
      have hz : aPlus a b m n (cPt a b m n i) = 0 := by
        have hc' : cMin a b m n + ((i : ℕ) : ℚ) = cMax a b m n := by
          rw [hiD, h.dim]; ring
        rw [hcP, hc']; unfold aPlus; rw [edgeA_cMax_succ]; simp
      have hB : physRacahB a b m n D ((i : ℕ) : ℝ) = 0 := by rw [hiD]; exact physRacahB_top a b m n D
      rw [hz, hB]; ring
  have hlo : aMinus a b m n (cPt a b m n i) *
      (if hh : 0 < (i : ℕ) then
        Phi6 a b (cPt a b m n ⟨(i : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.2⟩) m m n * P ((i : ℕ) - 1) else 0) =
      -physRacahD a b m n D (i : ℕ) * Phi6 a b (cMin a b m n + (i : ℕ)) m m n * P ((i : ℕ) - 1) := by
    split_ifs with hh
    · have e : cPt a b m n (⟨(i : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.2⟩ : Fin (D + 1)) =
          cMin a b m n + (i : ℕ) - 1 := by
        unfold cPt; rw [Nat.cast_sub hh]; push_cast; ring
      rw [e, hcP]
      have := hM
      linear_combination (P ((i : ℕ) - 1)) * this
    · have h0 : (i : ℕ) = 0 := by omega
      have hz : aMinus a b m n (cPt a b m n i) = 0 := by
        have hc' : cMin a b m n + ((i : ℕ) : ℚ) = cMin a b m n := by rw [h0]; simp
        rw [hcP, hc']; unfold aMinus; rw [edgeA_cMin]; simp
      rw [hz, h0]; simp [physRacahD_zero]
  rw [hup, hlo]
  have hcR : cPt a b m n i = cMin a b m n + ((i : ℕ) : ℚ) := rfl
  rw [hcR] at *
  -- diagonal: from the rank-m row
  have hdiag : bRow (wA a n) (wB b m) m n ((cMin a b m n + ((i : ℕ) : ℚ) : ℚ) : ℝ) *
        Phi6 a b (cMin a b m n + (i : ℕ)) m m n -
      (m : ℝ) * ((m : ℝ) + 1) * Phi6 a b (cMin a b m n + (i : ℕ)) m m n =
      -physRacahB a b m n D (i : ℕ) * Phi6 a b (cMin a b m n + (i : ℕ)) m m n -
        physRacahD a b m n D (i : ℕ) * Phi6 a b (cMin a b m n + (i : ℕ)) m m n := by
    have e0 : (m : ℝ) * ((m : ℝ) + 1) * Phi6 a b (cMin a b m n + (i : ℕ)) m m n =
        -(aPlus a b m n ((cMin a b m n + (i : ℕ) : ℚ) : ℝ) *
            Phi6 a b (cMin a b m n + (i : ℕ) + 1) m m n) +
          bRow (wA a n) (wB b m) m n ((cMin a b m n + (i : ℕ) : ℚ) : ℝ) *
            Phi6 a b (cMin a b m n + (i : ℕ)) m m n -
          aMinus a b m n ((cMin a b m n + (i : ℕ) : ℚ) : ℝ) *
            Phi6 a b (cMin a b m n + (i : ℕ) - 1) m m n := by
      simpa using eq0
    linear_combination -e0 + hP + hM
  rw [inv_mul_eq_iff_eq_mul₀ P0.ne']
  linear_combination (P i) * hdiag

/-- info: 'FormalResearch.Racah.SixJ.groundTransform_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms groundTransform_eq

/-- **`eq:RacahPolyEigenvalue`**: `ℒ_R ℛ_r = r(r+2m+1) ℛ_r` for `0 ≤ r ≤ D`.  Literal (`ℛ_r` is
`physR`, `ℒ_R` is `groundTransform`, i.e. `Φ_m^{-1}(H_R - m(m+1))Φ_m`). -/
theorem groundTransform_physR {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (hcan : |n| ≤ m)
    (r : ℕ) (hr : r ≤ D) (i : Fin (D + 1)) :
    groundTransform a b m n D (fun j => physR a b m n r j) i =
      (r : ℝ) * (r + 2 * m + 1) * physR a b m n r i := by
  rw [groundTransform_eq h hcan (physR a b m n r) i]
  have := ppR_row h hcan r i hr (by omega)
  unfold physR
  linear_combination
    (Real.sqrt ((2 * ((m : ℝ) + r) + 1) / (2 * (m : ℝ) + 1))) * this

/-- info: 'FormalResearch.Racah.SixJ.groundTransform_physR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms groundTransform_physR

end FormalResearch.Racah.SixJ
