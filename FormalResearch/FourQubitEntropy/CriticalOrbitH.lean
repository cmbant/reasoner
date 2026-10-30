import FormalResearch.FourQubitEntropy.CriticalOrbitPr

/-!
# Critical-orbit stability: the 32 representatives `𝓗` and their overlaps

For `η ∈ 𝓗` (`η_i = 1/√2`, `η_j = ε_j i/√6`, `j ≠ i`; index `a = 8 i + n`, `n` encoding `ε`),
`6 |⟨η, v⟩|² = Aq + 2 √3 Cq` (`qH`).  The coordinate swaps, sign flips and `H₊`, `H₋` map the pairs
`(Aq, Cq)` of the 32 representatives among themselves (the tables `tau*`, checked per case by
`ring`), which is the closure `𝓗 -> 𝓗` used in the symmetry reduction of
`critical_orbit_stability.tex`.
-/

set_option linter.unusedSimpArgs false

namespace FormalResearch.FourQubitEntropy.CO
open PaperECritical

/-- The four coordinates `v₀₀, v₀₁, v₁₀, v₁₁` as a vector indexed by `Fin 4`. -/
def coord (v : V) : Fin 4 → ℂ := ![v (0, 0), v (0, 1), v (1, 0), v (1, 1)]

/-- The sign vectors of `𝓗`: for `a = 8 i + n`, `ε_i = 0` and `ε_j = ±1` (bits of `n`) for `j ≠ i`. -/
def epsOf : Fin 32 → Fin 4 → ℝ :=
  ![![0, 1, 1, 1],
    ![0, -1, 1, 1],
    ![0, 1, -1, 1],
    ![0, -1, -1, 1],
    ![0, 1, 1, -1],
    ![0, -1, 1, -1],
    ![0, 1, -1, -1],
    ![0, -1, -1, -1],
    ![1, 0, 1, 1],
    ![-1, 0, 1, 1],
    ![1, 0, -1, 1],
    ![-1, 0, -1, 1],
    ![1, 0, 1, -1],
    ![-1, 0, 1, -1],
    ![1, 0, -1, -1],
    ![-1, 0, -1, -1],
    ![1, 1, 0, 1],
    ![-1, 1, 0, 1],
    ![1, -1, 0, 1],
    ![-1, -1, 0, 1],
    ![1, 1, 0, -1],
    ![-1, 1, 0, -1],
    ![1, -1, 0, -1],
    ![-1, -1, 0, -1],
    ![1, 1, 1, 0],
    ![-1, 1, 1, 0],
    ![1, -1, 1, 0],
    ![-1, -1, 1, 0],
    ![1, 1, -1, 0],
    ![-1, 1, -1, 0],
    ![1, -1, -1, 0],
    ![-1, -1, -1, 0]]

/-- The distinguished coordinate `i` of `a = 8 i + n`. -/
def idxI (a : Fin 32) : Fin 4 := ⟨a.val / 8, by omega⟩

/-- `∑_j ε_j Re v_j`. -/
noncomputable def Sx (a : Fin 32) (v : V) : ℝ := ∑ j, epsOf a j * (coord v j).re
/-- `∑_j ε_j Im v_j`. -/
noncomputable def Sy (a : Fin 32) (v : V) : ℝ := ∑ j, epsOf a j * (coord v j).im

/-- `6 |⟨η, v⟩|² = Aq + 2 √3 Cq` for `η = (1/√2) e_i + (i/√6) ε`. -/
noncomputable def Aq (a : Fin 32) (v : V) : ℝ :=
  3 * Complex.normSq (coord v (idxI a)) + Sx a v ^ 2 + Sy a v ^ 2

/-- The cross term of `6 |⟨η, v⟩|²`. -/
noncomputable def Cq (a : Fin 32) (v : V) : ℝ :=
  (coord v (idxI a)).re * Sy a v - (coord v (idxI a)).im * Sx a v

/-- The overlap `|⟨η_a, v⟩|²` with the `a`-th representative of `𝓗`. -/
noncomputable def qH (a : Fin 32) (v : V) : ℝ := (Aq a v + 2 * Real.sqrt 3 * Cq a v) / 6

set_option maxHeartbeats 8000000 in
theorem close_wp (v : V) (a : Fin 32) :
    Aq a (wp v) = Aq (![17, 29, 5, 12, 11, 2, 26, 22, 18, 30, 13, 4, 3, 10, 25, 21, 23, 0, 8, 31, 24, 15, 7, 16, 20, 14, 6, 28, 27, 1, 9, 19] a) v ∧
    Cq a (wp v) = Cq (![17, 29, 5, 12, 11, 2, 26, 22, 18, 30, 13, 4, 3, 10, 25, 21, 23, 0, 8, 31, 24, 15, 7, 16, 20, 14, 6, 28, 27, 1, 9, 19] a) v := by
  fin_cases a <;> simp [Aq, Cq, Sx, Sy, coord, epsOf, idxI, wp, wm, swapV, flipV, Equiv.swap_apply_def, Fin.sum_univ_four,
    Complex.normSq_apply] <;> refine ⟨?_, ?_⟩ <;> ring

set_option maxHeartbeats 8000000 in
theorem close_wm (v : V) (a : Fin 32) :
    Aq a (wm v) = Aq (![7, 14, 22, 25, 30, 17, 9, 0, 15, 6, 21, 26, 29, 18, 1, 8, 23, 5, 13, 28, 27, 10, 2, 16, 31, 3, 11, 20, 19, 12, 4, 24] a) v ∧
    Cq a (wm v) = Cq (![7, 14, 22, 25, 30, 17, 9, 0, 15, 6, 21, 26, 29, 18, 1, 8, 23, 5, 13, 28, 27, 10, 2, 16, 31, 3, 11, 20, 19, 12, 4, 24] a) v := by
  fin_cases a <;> simp [Aq, Cq, Sx, Sy, coord, epsOf, idxI, wp, wm, swapV, flipV, Equiv.swap_apply_def, Fin.sum_univ_four,
    Complex.normSq_apply] <;> refine ⟨?_, ?_⟩ <;> ring

set_option maxHeartbeats 8000000 in
theorem close_swap1 (v : V) (a : Fin 32) :
    Aq a (swapV (0, 0) (0, 1) v) = Aq (![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 16, 18, 17, 19, 20, 22, 21, 23, 24, 26, 25, 27, 28, 30, 29, 31] a) v ∧
    Cq a (swapV (0, 0) (0, 1) v) = Cq (![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 16, 18, 17, 19, 20, 22, 21, 23, 24, 26, 25, 27, 28, 30, 29, 31] a) v := by
  fin_cases a <;> simp [Aq, Cq, Sx, Sy, coord, epsOf, idxI, wp, wm, swapV, flipV, Equiv.swap_apply_def, Fin.sum_univ_four,
    Complex.normSq_apply] <;> refine ⟨?_, ?_⟩ <;> ring

set_option maxHeartbeats 8000000 in
theorem close_swap2 (v : V) (a : Fin 32) :
    Aq a (swapV (0, 0) (1, 0) v) = Aq (![16, 18, 17, 19, 20, 22, 21, 23, 8, 10, 9, 11, 12, 14, 13, 15, 0, 2, 1, 3, 4, 6, 5, 7, 24, 28, 26, 30, 25, 29, 27, 31] a) v ∧
    Cq a (swapV (0, 0) (1, 0) v) = Cq (![16, 18, 17, 19, 20, 22, 21, 23, 8, 10, 9, 11, 12, 14, 13, 15, 0, 2, 1, 3, 4, 6, 5, 7, 24, 28, 26, 30, 25, 29, 27, 31] a) v := by
  fin_cases a <;> simp [Aq, Cq, Sx, Sy, coord, epsOf, idxI, wp, wm, swapV, flipV, Equiv.swap_apply_def, Fin.sum_univ_four,
    Complex.normSq_apply] <;> refine ⟨?_, ?_⟩ <;> ring

set_option maxHeartbeats 8000000 in
theorem close_swap3 (v : V) (a : Fin 32) :
    Aq a (swapV (0, 0) (1, 1) v) = Aq (![24, 26, 28, 30, 25, 27, 29, 31, 8, 12, 10, 14, 9, 13, 11, 15, 16, 20, 18, 22, 17, 21, 19, 23, 0, 4, 1, 5, 2, 6, 3, 7] a) v ∧
    Cq a (swapV (0, 0) (1, 1) v) = Cq (![24, 26, 28, 30, 25, 27, 29, 31, 8, 12, 10, 14, 9, 13, 11, 15, 16, 20, 18, 22, 17, 21, 19, 23, 0, 4, 1, 5, 2, 6, 3, 7] a) v := by
  fin_cases a <;> simp [Aq, Cq, Sx, Sy, coord, epsOf, idxI, wp, wm, swapV, flipV, Equiv.swap_apply_def, Fin.sum_univ_four,
    Complex.normSq_apply] <;> refine ⟨?_, ?_⟩ <;> ring

set_option maxHeartbeats 8000000 in
theorem close_flip1 (v : V) (a : Fin 32) :
    Aq a (flipV (0, 1) v) = Aq (![1, 0, 3, 2, 5, 4, 7, 6, 15, 14, 13, 12, 11, 10, 9, 8, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29] a) v ∧
    Cq a (flipV (0, 1) v) = Cq (![1, 0, 3, 2, 5, 4, 7, 6, 15, 14, 13, 12, 11, 10, 9, 8, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29] a) v := by
  fin_cases a <;> simp [Aq, Cq, Sx, Sy, coord, epsOf, idxI, wp, wm, swapV, flipV, Equiv.swap_apply_def, Fin.sum_univ_four,
    Complex.normSq_apply] <;> refine ⟨?_, ?_⟩ <;> ring

set_option maxHeartbeats 8000000 in
theorem close_flip2 (v : V) (a : Fin 32) :
    Aq a (flipV (1, 0) v) = Aq (![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 23, 22, 21, 20, 19, 18, 17, 16, 28, 29, 30, 31, 24, 25, 26, 27] a) v ∧
    Cq a (flipV (1, 0) v) = Cq (![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 23, 22, 21, 20, 19, 18, 17, 16, 28, 29, 30, 31, 24, 25, 26, 27] a) v := by
  fin_cases a <;> simp [Aq, Cq, Sx, Sy, coord, epsOf, idxI, wp, wm, swapV, flipV, Equiv.swap_apply_def, Fin.sum_univ_four,
    Complex.normSq_apply] <;> refine ⟨?_, ?_⟩ <;> ring

set_option maxHeartbeats 8000000 in
theorem close_flip3 (v : V) (a : Fin 32) :
    Aq a (flipV (1, 1) v) = Aq (![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 31, 30, 29, 28, 27, 26, 25, 24] a) v ∧
    Cq a (flipV (1, 1) v) = Cq (![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 31, 30, 29, 28, 27, 26, 25, 24] a) v := by
  fin_cases a <;> simp [Aq, Cq, Sx, Sy, coord, epsOf, idxI, wp, wm, swapV, flipV, Equiv.swap_apply_def, Fin.sum_univ_four,
    Complex.normSq_apply] <;> refine ⟨?_, ?_⟩ <;> ring


theorem coord_smul (c : ℂ) (v : V) (j : Fin 4) : coord (smulV c v) j = c * coord v j := by
  fin_cases j <;> simp [coord, smulV]

theorem Sx_smul (c : ℂ) (v : V) (a : Fin 32) :
    Sx a (smulV c v) = c.re * Sx a v - c.im * Sy a v := by
  simp only [Sx, Sy, coord_smul, Complex.mul_re, Fin.sum_univ_four]; ring

theorem Sy_smul (c : ℂ) (v : V) (a : Fin 32) :
    Sy a (smulV c v) = c.re * Sy a v + c.im * Sx a v := by
  simp only [Sx, Sy, coord_smul, Complex.mul_im, Fin.sum_univ_four]; ring

theorem Aq_smul {c : ℂ} (hc : Complex.normSq c = 1) (v : V) (a : Fin 32) :
    Aq a (smulV c v) = Aq a v := by
  have h : c.re * c.re + c.im * c.im = 1 := by rw [Complex.normSq_apply] at hc; exact hc
  simp only [Aq, coord_smul, Complex.normSq_mul, hc, Sx_smul, Sy_smul]
  linear_combination (Sx a v ^ 2 + Sy a v ^ 2) * h

theorem Cq_smul {c : ℂ} (hc : Complex.normSq c = 1) (v : V) (a : Fin 32) :
    Cq a (smulV c v) = Cq a v := by
  have h : c.re * c.re + c.im * c.im = 1 := by rw [Complex.normSq_apply] at hc; exact hc
  simp only [Cq, coord_smul, Complex.mul_re, Complex.mul_im, Sx_smul, Sy_smul]
  linear_combination (((coord v (idxI a)).re * Sy a v - (coord v (idxI a)).im * Sx a v)) * h

end FormalResearch.FourQubitEntropy.CO
