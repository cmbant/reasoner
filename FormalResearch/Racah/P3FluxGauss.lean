module

public import FormalResearch.Racah.P2ThreeJSystem
public import FormalResearch.Racah.P2RacahSystemSpec

/-!
# The exact Gauss-weight identity `λ² w = 2` for the `3j` and `6j` chains (Weyl P3, `rem:flux-gauss`)

Source: `Weyl/P3/paper/weyl_midpoint_semiclassics.tex`, `rem:flux-gauss` (the paragraph beginning
"The weight identity holds exactly for `3j` (`λ_j² = N`, `w_j = 2/N`) and `6j`
(`λ_j² = 4AB/(2C)`, `w_j = C/(AB)`)").  The natural gauge of the paper is `Ŷ_k = √(2k+1) Φ_k`, so the
column norm is `λ_j² = ∑_k Ŷ_k(x_j)² = ∑_k (2k+1) Φ_k(x_j)²`.

## Results (all `N`, all admissible labels; exact identities, no asymptotics)

* `gaussWeight_3j`: for an admissible `3j` system (`SpecAdm`, `0 < N`, `K = N - max(|M|,|σ|)` lattice
  points) and every lattice node `x_n = xLat M σ N n` (`n < K`),
  `λ² := ∑_{L} (2L+1) Φ_L(x_n)² = N` and `λ² w = 2`, with `w = x_{n+1} - x_n = 2/N` the node gap.
  `xLat_centred_gap` records that the centred gap `(x_{n+1} - x_{n-1})/2` is the same number `2/N`.
* `gaussWeight_6j`: for a finite Racah system (`RacahSystem a b m n D`) and every physical `c = c_i`,
  `λ² := ∑_f (2f+1) Φ_f(c)² = 4AB/(2C)` (`C = c + 1/2`, `A = wA a n`, `B = wB b m`) and `λ² w = 2`
  with `w = ω_c = (2c+1)/(2AB) = C/(AB)`.

Which object is which for `6j`.  `omegaW A B c` is the paper's *cell width*
`ω_c = x̂(c) - x̂(c+1)`, `x̂(s) = (A²+B²-s²)/(2AB)` (`omegaW_eq_cell_width`, `eq:Racahcellwidth`), and it is
the paper's `w = C/(AB)`.  The nodes themselves are `x_c = x̂(c + 1/2) = cosA A B (wC c)`; the *centred*
node gap `(x_{c-1} - x_{c+1})/2` of these nodes is the same number (`omegaW_eq_centred_gap`).  Both are
statements about the real-variable lattice coordinate; for `3j` the gap is the spacing of the grid of
`eq:physicalgrid`.

## Not formalised

The semiclassical step of `rem:flux-gauss` (that the physical flux satisfies
`J_phys(x_j) = λ_j² w_j (1 + O(h³))/4` across the forbidden zone, hence `δ_fl = 0` intrinsically, for a
general chain in the class) is stated in the paper as *open* and is not formalised; neither is the
quantum `6j` deformed identity, nor the verifier's control showing that a truncated chain violates the
identity.  Only the finite exact identity `λ² w = 2`, a corollary of the P2 completeness relations
`Phi_disccomplete` (`eq:3jdisccomplete`) and `Phi6_completeness` (`eq:RacahPhiCompleteness`), is proved.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner

/-! ### `3j` -/

/-- The natural-gauge column norm of the `3j` chain at the node `x_n`:
`λ_n² = ∑_{i<K} (2L_i+1) Φ_{L_i}(x_n)²`, `L_i = max(|M|,|σ|) + i`, with `Ŷ_L = √(2L+1) Φ_L`. -/
noncomputable def lambdaSq3j (M σ N : ℚ) (K n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range K,
    (2 * ((max |M| |σ| + i : ℚ) : ℝ) + 1) *
      PhiX (max |M| |σ| + i) M σ N (xLat M σ N n) ^ 2

/-- **`rem:flux-gauss`, `3j` half** (exact): `λ_n² = N` and `λ_n² w_n = 2`, where the node gap is
`w_n = x_{n+1} - x_n = 2/N`.  For an admissible system, every lattice node `n < K`. -/
theorem gaussWeight_3j {M σ N : ℚ} (hA : SpecAdm M σ N) (hN : 0 < N) {K : ℕ}
    (hK : (K : ℚ) = N - max |M| |σ|) {n : ℕ} (hn : n < K) :
    lambdaSq3j M σ N K n = N ∧
      lambdaSq3j M σ N K n * ((xLat M σ N (n + 1) - xLat M σ N n : ℚ) : ℝ) = 2 := by
  have hc := Phi_disccomplete hA hN hK hn hn
  simp only [↓reduceIte] at hc
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hl : lambdaSq3j M σ N K n = N := by
    unfold lambdaSq3j
    have : ∑ i ∈ Finset.range K, (2 * ((max |M| |σ| + i : ℚ) : ℝ) + 1) *
        PhiX (max |M| |σ| + i) M σ N (xLat M σ N n) ^ 2 = (N : ℝ) := by
      field_simp at hc
      simpa [sq] using hc
    exact this
  refine ⟨hl, ?_⟩
  rw [hl, xLat_succ]
  push_cast
  field_simp
  ring

/-- The centred node gap of the `3j` grid, `(x_{n+1} - x_{n-1})/2 = 2/N` (`n ≥ 1`): the same number as
the one-sided gap used in `gaussWeight_3j`. -/
theorem xLat_centred_gap (M σ N : ℚ) {n : ℕ} (hn : 1 ≤ n) :
    (xLat M σ N (n + 1) - xLat M σ N (n - 1)) / 2 = 2 / N := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, xLat_succ, xLat_succ]
  ring

/-! ### `6j` -/

namespace SixJ

/-- The centred node gap of the `6j` nodes `x_c = cosA A B (c + 1/2)`:
`(x_{c-1} - x_{c+1})/2 = ω_c = (2c+1)/(2AB)`; so the cell width `omegaW` (`eq:Racahcellwidth`) is
also the centred gap, equal to `C/(AB)` with `C = c + 1/2`. -/
theorem omegaW_eq_centred_gap (A B c : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) :
    omegaW A B c = (cosA A B (c - 1 / 2) - cosA A B (c + 3 / 2)) / 2 := by
  unfold omegaW cosA
  field_simp
  ring

/-- `ω_c = C/(AB)` with `C = c + 1/2` (`wC`), the form in which `rem:flux-gauss` states the `6j` weight. -/
theorem omegaW_eq_C_div (A B : ℝ) (c : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) :
    omegaW A B (c : ℝ) = wC c / (A * B) := by
  unfold omegaW wC
  field_simp

/-- The natural-gauge column norm of the `6j` chain at `c = c_i`:
`λ_i² = ∑_j (2f_j+1) Φ_{f_j}(c_i)²`, with `Ŷ_f = √(2f+1) Φ_f`. -/
noncomputable def lambdaSq6j (a b m n : ℚ) {D : ℕ} (i : Fin (D + 1)) : ℝ :=
  ∑ j : Fin (D + 1), (2 * (fPt m n j : ℝ) + 1) *
    Phi6 a b (cPt a b m n i) (fPt m n j) m n ^ 2

/-- **`rem:flux-gauss`, `6j` half** (exact): for a finite Racah system and every physical `c = c_i`,
with `A = wA a n`, `B = wB b m`, `C = wC c_i = c_i + 1/2`,
`λ² = 4AB/(2C)` and `λ² w = 2` for `w = ω_c = C/(AB) = x̂(c) - x̂(c+1)` (the cell width,
`omegaW_eq_cell_width`, equal to the centred node gap, `omegaW_eq_centred_gap`). -/
theorem gaussWeight_6j {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (i : Fin (D + 1)) :
    lambdaSq6j a b m n i = 4 * wA a n * wB b m / (2 * wC (cPt a b m n i)) ∧
      lambdaSq6j a b m n i * (wC (cPt a b m n i) / (wA a n * wB b m)) = 2 ∧
      lambdaSq6j a b m n i * wgtR a b m n i = 2 ∧
      wgtR a b m n i = cosA (wA a n) (wB b m) (cPt a b m n i) -
        cosA (wA a n) (wB b m) (((cPt a b m n i : ℚ) : ℝ) + 1) := by
  obtain ⟨hA, hB⟩ := AB_pos h.hne
  have hw := wgtR_pos h i
  have hc := Phi6_completeness h i i
  simp only [↓reduceIte] at hc
  have hl : lambdaSq6j a b m n i = 2 * (wgtR a b m n i)⁻¹ := by
    rw [← hc, Finset.mul_sum]
    unfold lambdaSq6j
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hwC : wgtR a b m n i = wC (cPt a b m n i) / (wA a n * wB b m) := by
    unfold wgtR
    exact omegaW_eq_C_div _ _ _ hA.ne' hB.ne'
  have hCpos : 0 < wC (cPt a b m n i) := by
    have := cPt_nonneg a b m n i
    unfold wC; positivity
  have h3 : lambdaSq6j a b m n i * wgtR a b m n i = 2 := by
    rw [hl]; field_simp
  refine ⟨?_, by rw [← hwC]; exact h3, h3, ?_⟩
  · rw [hl, hwC]
    field_simp
    norm_num
  · unfold wgtR
    exact omegaW_eq_cell_width _ _ _ hA.ne' hB.ne'

end SixJ

/-! ### Axiom checks -/

/-- info: 'FormalResearch.Racah.gaussWeight_3j' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gaussWeight_3j

/-- info: 'FormalResearch.Racah.SixJ.gaussWeight_6j' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixJ.gaussWeight_6j

end FormalResearch.Racah
