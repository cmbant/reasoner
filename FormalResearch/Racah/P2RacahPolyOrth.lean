module

public import FormalResearch.Racah.P2RacahPolyIdent
public import FormalResearch.Racah.P2RacahSystem

/-!
# The physical Racah polynomials: weight, explicit form, orthonormality (Weyl P2,
`eq:physicalRacahweight`-`eq:physicalRacahPolyOrth`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, subsection *Explicit physical Racah-polynomial
realization*.  Canonical sector `|n| ≤ m`, lattice `c_i = c_min + i`, `0 ≤ i ≤ D = c_max - c_min`.

* `physPi`: `π_c = ω_c (2m+1)/2 · Φ_m(c)²`; `physPi_eq`: `= (2c+1)(2m+1)/(4AB) 𝒮_m(A,B,c+1/2)`;
  `physPi_pos`.
* `physR`: `ℛ_r(c) = √((2(m+r)+1)/(2m+1)) Φ_{m+r}(c)/Φ_m(c)`.
* `physR_eq`: `ℛ_r(c_min+y) = ℛ_r(c_min) Q^R_r(y)` (`eq:physicalRacahExplicit`).
* `physR_orthonormal`: `∑_c π_c ℛ_r(c) ℛ_s(c) = δ_{rs}` (`eq:physicalRacahPolyOrth`);
  `physPi_sum`: `∑_c π_c = 1`.
-/

@[expose] public section

namespace FormalResearch.Racah.SixJ

open FormalResearch.Wigner FormalResearch.Racah.RacahPoly

/-- The physical Racah weight `π_c = ω_c (2m+1)/2 · Φ_m(c)²` at `c = c_i` (`eq:physicalRacahweight`). -/
noncomputable def physPi (a b m n : ℚ) {D : ℕ} (i : Fin (D + 1)) : ℝ :=
  wgtR a b m n i * (((2 * (m : ℝ) + 1) / 2) * Phi6 a b (cPt a b m n i) m m n ^ 2)

/-- The normalised physical Racah coefficients (`eq:physicalRacahPolynomial`) at `c = c_min + y`. -/
noncomputable def physR (a b m n : ℚ) (r y : ℕ) : ℝ :=
  Real.sqrt ((2 * ((m : ℝ) + r) + 1) / (2 * (m : ℝ) + 1)) * ppR a b m n r y

/-- `ℛ_r(c) = ℛ_r(c_min) Q^R_r(c - c_min)`: **`eq:physicalRacahExplicit`**, with
`Q^R_r` the terminating Racah polynomial of `eq:physicalRacah4F3`.  Literal. -/
theorem physR_eq {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (hcan : |n| ≤ m) (r y : ℕ)
    (hr : r ≤ D) (hy : y ≤ D) :
    physR a b m n r y = physR a b m n r 0 * physQ a b m n D r (y : ℝ) := by
  unfold physR
  rw [ppR_eq_racahPoly h hcan r y hr hy]
  ring

/-- `π_c = (2c+1)(2m+1)/(4AB) · 𝒮_m(A,B,c+1/2)`: the second form in `eq:physicalRacahweight`. -/
theorem physPi_eq {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (hcan : |n| ≤ m)
    (i : Fin (D + 1)) :
    physPi a b m n i =
      (2 * ((cPt a b m n i : ℚ) : ℝ) + 1) * (2 * (m : ℝ) + 1) / (4 * wA a n * wB b m) *
        seedS m n (wA a n) (wB b m) (wC (cPt a b m n i)) := by
  have hm := mem_rank h hcan 0 (Nat.zero_le _)
  simp only [Nat.cast_zero, add_zero] at hm
  have hc := mem_lattice h i (by omega)
  obtain ⟨hA, hB⟩ := AB_pos h.hne
  have := (Phi6_seed_sq a b (cPt a b m n i) m n hm.1 hm.2 hc.1 hc.2).2
  unfold physPi wgtR omegaW
  rw [this]
  field_simp
  ring

/-- `π_c > 0` on the physical lattice. -/
theorem physPi_pos {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (hcan : |n| ≤ m)
    (i : Fin (D + 1)) : 0 < physPi a b m n i := by
  have hm := mem_rank h hcan 0 (Nat.zero_le _)
  simp only [Nat.cast_zero, add_zero] at hm
  have hc := mem_lattice h i (by omega)
  have hP := Phi6_seed_pos a b (cPt a b m n i) m n hm.1 hm.2 hc.1 hc.2
  have hm0 : (0 : ℝ) ≤ m := by
    have := (abs_le.1 hcan); have h0 : (0 : ℚ) ≤ m := le_trans (abs_nonneg _) hcan
    exact_mod_cast h0
  unfold physPi
  have := wgtR_pos h i
  positivity

/-- **`eq:physicalRacahPolyOrth`**: `∑_c π_c ℛ_r(c) ℛ_s(c) = δ_{rs}`, `0 ≤ r, s ≤ D`.  Literal (the sum
over the physical lattice `𝒞 = {c_min + i}`, `ℛ_r(c_i) = physR r i`). -/
theorem physR_orthonormal {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (hcan : |n| ≤ m)
    (r s : Fin (D + 1)) :
    ∑ i : Fin (D + 1), physPi a b m n i * (physR a b m n r i * physR a b m n s i) =
      if r = s then 1 else 0 := by
  have hm := mem_rank h hcan 0 (Nat.zero_le _)
  simp only [Nat.cast_zero, add_zero] at hm
  have hm0 : (0 : ℝ) ≤ m := by
    have h0 : (0 : ℚ) ≤ m := le_trans (abs_nonneg _) hcan
    exact_mod_cast h0
  have h2m : (0 : ℝ) < 2 * m + 1 := by linarith
  have orth := Phi6_orthogonality_fin h r s
  have hf : ∀ j : Fin (D + 1), (fPt m n j : ℝ) = m + (j : ℕ) := by
    intro j; unfold fPt; rw [fMin_eq_of_canonical hcan]; push_cast; ring
  set qr := Real.sqrt ((2 * ((m : ℝ) + (r : ℕ)) + 1) / (2 * (m : ℝ) + 1)) with hqr
  set qs := Real.sqrt ((2 * ((m : ℝ) + (s : ℕ)) + 1) / (2 * (m : ℝ) + 1)) with hqs
  have hpt : ∀ i : Fin (D + 1), physPi a b m n i * (physR a b m n r i * physR a b m n s i) =
      (qr * qs * ((2 * (m : ℝ) + 1) / 2)) *
        (wgtR a b m n i * (Phi6 a b (cPt a b m n i) (fPt m n r) m n *
          Phi6 a b (cPt a b m n i) (fPt m n s) m n)) := by
    intro i
    have hc := mem_lattice h i (by omega)
    have hP := Phi6_seed_pos a b (cPt a b m n i) m n hm.1 hm.2 hc.1 hc.2
    have e1 : ppR a b m n r i = Phi6 a b (cPt a b m n i) (fPt m n r) m n /
        Phi6 a b (cPt a b m n i) m m n := by
      unfold ppR cPt fPt; rw [fMin_eq_of_canonical hcan]
    have e2 : ppR a b m n s i = Phi6 a b (cPt a b m n i) (fPt m n s) m n /
        Phi6 a b (cPt a b m n i) m m n := by
      unfold ppR cPt fPt; rw [fMin_eq_of_canonical hcan]
    unfold physPi physR
    rw [e1, e2, hqr, hqs]
    field_simp
  simp only [hpt]
  rw [← Finset.mul_sum]
  unfold wgtR
  rw [orth]
  by_cases hrs : r = s
  · subst hrs
    simp only [if_true]
    have hq : qr * qr = (2 * ((m : ℝ) + (r : ℕ)) + 1) / (2 * (m : ℝ) + 1) :=
      Real.mul_self_sqrt (by positivity)
    rw [hf r, hq]
    have : (0 : ℝ) < 2 * ((m : ℝ) + (r : ℕ)) + 1 := by
      have := (Nat.cast_nonneg (r : ℕ) : (0 : ℝ) ≤ (r : ℕ)); linarith
    field_simp
  · simp [hrs]

/-- `∑_c π_c = 1` (the weight is a probability distribution; `ℛ_0 = 1`). -/
theorem physPi_sum {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (hcan : |n| ≤ m) :
    ∑ i : Fin (D + 1), physPi a b m n i = 1 := by
  have := physR_orthonormal h hcan 0 0
  have hm0 : (0 : ℝ) ≤ m := by
    have h0 : (0 : ℚ) ≤ m := le_trans (abs_nonneg _) hcan
    exact_mod_cast h0
  have hm := mem_rank h hcan 0 (Nat.zero_le _)
  simp only [Nat.cast_zero, add_zero] at hm
  have hR : ∀ i : Fin (D + 1), physR a b m n 0 i = 1 := by
    intro i
    have hc := mem_lattice h i (by omega)
    have hP := Phi6_seed_pos a b (cMin a b m n + (i : ℕ)) m n hm.1 hm.2 hc.1 hc.2
    have h2m : (0 : ℝ) < 2 * m + 1 := by linarith
    simp only [physR, ppR, Nat.cast_zero, add_zero]
    rw [div_self hP.ne', mul_one, div_self h2m.ne', Real.sqrt_one]
  simpa [hR] using this

/-- info: 'FormalResearch.Racah.SixJ.physR_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physR_eq

/-- info: 'FormalResearch.Racah.SixJ.physPi_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physPi_eq

/-- info: 'FormalResearch.Racah.SixJ.physPi_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physPi_pos

/-- info: 'FormalResearch.Racah.SixJ.physR_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physR_orthonormal

/-- info: 'FormalResearch.Racah.SixJ.physPi_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physPi_sum

end FormalResearch.Racah.SixJ
