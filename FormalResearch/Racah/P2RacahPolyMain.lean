module

public import FormalResearch.Racah.P2RacahPolyRatio

/-!
# The physical Racah polynomials (Weyl P2, `eq:physicalRacahPolynomial`-`eq:physicalRacahPolyOrth`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, subsection *Explicit physical Racah-polynomial
realization*.
-/

@[expose] public section

namespace FormalResearch.Racah.SixJ

open FormalResearch.Wigner FormalResearch.Racah.RacahPoly

/-- The ratio `Φ_{m+r}(c_min+y)/Φ_m(c_min+y)` along the lattice (`eq:physicalRacahPolynomial` before
the normalisation factor). -/
noncomputable def ppR (a b m n : ℚ) (r y : ℕ) : ℝ :=
  Phi6 a b (cMin a b m n + y) (m + r) m n / Phi6 a b (cMin a b m n + y) m m n

lemma row_rank {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (hcan : |n| ≤ m) (r y : ℕ)
    (hr : r ≤ D) (hy : y ≤ D) :
    ((m : ℝ) + r) * ((m : ℝ) + r + 1) * Phi6 a b (cMin a b m n + y) (m + r) m n =
      -(aPlus a b m n ((cMin a b m n + y : ℚ) : ℝ) * Phi6 a b (cMin a b m n + y + 1) (m + r) m n) +
        bRow (wA a n) (wB b m) m n ((cMin a b m n + y : ℚ) : ℝ) *
          Phi6 a b (cMin a b m n + y) (m + r) m n -
        aMinus a b m n ((cMin a b m n + y : ℚ) : ℝ) * Phi6 a b (cMin a b m n + y - 1) (m + r) m n := by
  have := Phi6_row h ⟨y, by omega⟩ ⟨r, by omega⟩
  simp only [cPt, fPt, fMin_eq_of_canonical hcan] at this
  push_cast at this ⊢
  exact this

/-- **The recurrence of the ratios**: `r(r+2m+1) p_r(y) = B(y)(p_r(y+1)-p_r(y)) + D(y)(p_r(y-1)-p_r(y))`
for the physical Racah coefficients, `p_r(y) = Φ_{m+r}(c_min+y)/Φ_m(c_min+y)`. -/
theorem ppR_row {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (hcan : |n| ≤ m) (r y : ℕ)
    (hr : r ≤ D) (hy : y ≤ D) :
    physRacahB a b m n D y * (ppR a b m n r (y + 1) - ppR a b m n r y) +
        physRacahD a b m n D y * (ppR a b m n r (y - 1) - ppR a b m n r y) =
      (r : ℝ) * (r + 2 * m + 1) * ppR a b m n r y := by
  have hm := mem_rank h hcan 0 (Nat.zero_le _)
  simp only [Nat.cast_zero, add_zero] at hm
  have hc := mem_lattice h y hy
  have P0 : 0 < Phi6 a b (cMin a b m n + y) m m n := Phi6_seed_pos _ _ _ _ _ hm.1 hm.2 hc.1 hc.2
  have eq1 := row_rank h hcan r y hr hy
  have eq0 := row_rank h hcan 0 y (Nat.zero_le _) hy
  simp only [Nat.cast_zero, add_zero] at eq0
  have hP := offPlus h hcan y hy
  have hM := offMinus h hcan y hy
  set u := Phi6 a b (cMin a b m n + y) m m n with hu
  set v := Phi6 a b (cMin a b m n + y) (m + r) m n with hv
  set p := ppR a b m n r y with hp
  have hvp : v = p * u := by
    rw [hp]; unfold ppR; rw [div_mul_cancel₀ _ P0.ne']
  -- upper neighbour
  have hPv : aPlus a b m n ((cMin a b m n + y : ℚ) : ℝ) *
      Phi6 a b (cMin a b m n + y + 1) (m + r) m n =
      -physRacahB a b m n D y * u * ppR a b m n r (y + 1) := by
    rcases hy.lt_or_eq with hlt | heq
    · have hc' := mem_lattice h (y + 1) (by omega)
      push_cast at hc'
      have P1 : 0 < Phi6 a b (cMin a b m n + y + 1) m m n :=
        Phi6_seed_pos _ _ _ _ _ hm.1 hm.2 (by simpa [add_assoc] using hc'.1)
          (by simpa [add_assoc] using hc'.2)
      have e : ppR a b m n r (y + 1) =
          Phi6 a b (cMin a b m n + y + 1) (m + r) m n / Phi6 a b (cMin a b m n + y + 1) m m n := by
        unfold ppR; push_cast; rw [add_assoc]
      rw [e]
      field_simp
      linear_combination (Phi6 a b (cMin a b m n + y + 1) (m + r) m n) * hP
    · have hz : aPlus a b m n ((cMin a b m n + y : ℚ) : ℝ) = 0 := by
        have hc : cMin a b m n + (y : ℚ) = cMax a b m n := by
          rw [heq, h.dim]; ring
        rw [hc]; unfold aPlus; rw [edgeA_cMax_succ]; simp
      have hB : physRacahB a b m n D (y : ℝ) = 0 := by rw [heq]; exact physRacahB_top a b m n D
      rw [hz, hB]; ring
  -- lower neighbour
  have hMv : aMinus a b m n ((cMin a b m n + y : ℚ) : ℝ) *
      Phi6 a b (cMin a b m n + y - 1) (m + r) m n =
      -physRacahD a b m n D y * u * ppR a b m n r (y - 1) := by
    rcases Nat.eq_zero_or_pos y with h0 | hpos
    · have hz : aMinus a b m n ((cMin a b m n + y : ℚ) : ℝ) = 0 := by
        have hc : cMin a b m n + (y : ℚ) = cMin a b m n := by rw [h0]; simp
        rw [hc]; unfold aMinus; rw [edgeA_cMin]; simp
      have hD0 : physRacahD a b m n D (y : ℝ) = 0 := by rw [h0]; simpa using physRacahD_zero a b m n D
      rw [hz, hD0]; ring
    · have hc' := mem_lattice h (y - 1) (by omega)
      have e0 : (((y - 1 : ℕ) : ℚ)) = (y : ℚ) - 1 := by rw [Nat.cast_sub hpos]; simp
      rw [e0] at hc'
      have P1 : 0 < Phi6 a b (cMin a b m n + y - 1) m m n :=
        Phi6_seed_pos _ _ _ _ _ hm.1 hm.2 (by simpa [add_sub_assoc] using hc'.1)
          (by simpa [add_sub_assoc] using hc'.2)
      have e : ppR a b m n r (y - 1) =
          Phi6 a b (cMin a b m n + y - 1) (m + r) m n / Phi6 a b (cMin a b m n + y - 1) m m n := by
        unfold ppR; rw [e0, add_sub_assoc]
      rw [e]
      field_simp
      linear_combination (Phi6 a b (cMin a b m n + y - 1) (m + r) m n) * hM
  have hDe : ((m : ℝ) + r) * ((m : ℝ) + r + 1) - (m : ℝ) * ((m : ℝ) + 1) =
      (r : ℝ) * (r + 2 * m + 1) := by ring
  -- combine
  have key : u * (physRacahB a b m n D y * (ppR a b m n r (y + 1) - p) +
        physRacahD a b m n D y * (ppR a b m n r (y - 1) - p) -
        (r : ℝ) * (r + 2 * m + 1) * p) = 0 := by
    linear_combination hPv + hMv - p * hP - p * hM - eq1 + p * eq0 +
      (((m : ℝ) + r) * ((m : ℝ) + r + 1) -
        bRow (wA a n) (wB b m) m n ((cMin a b m n + y : ℚ) : ℝ)) * hvp
  rcases mul_eq_zero.1 key with h0 | h0
  · exact absurd h0 P0.ne'
  · linarith

/-- info: 'FormalResearch.Racah.SixJ.ppR_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppR_row

end FormalResearch.Racah.SixJ
