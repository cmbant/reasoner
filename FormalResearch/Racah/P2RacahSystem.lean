module

public import FormalResearch.Racah.P2RacahSystemSpec

/-!
# Exact finite self-adjoint Racah-Wigner system (Weyl P2, `thm:6jfiniteRacah`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, section *Exact finite Racah spectral system on
the physical `c`-lattice* (`sec:6jcspectral`), `thm:6jfiniteRacah`.

`RacahSystem a b m n D` records the paper's integrality conventions (`2a, 2b, 2m, m-n ∈ ℤ`) and
`D = c_max - c_min` (so that `D + 1 = |𝒞|`); `RacahSystem.exists` shows that such a `D` exists iff the
physical `c`-lattice is non-empty.  The lattice is indexed by `i : Fin (D+1)`, `c_i = c_min + i`, and the
`f`-range by `j : Fin (D+1)`, `f_j = f_0 + j` (same cardinality, `eq:Racahdimension`).

## Dictionary (paper -> Lean)

| paper | Lean |
|---|---|
| `𝒞`, `{f_0..f_1}` | `physC a b m n`, `physF a b m n` |
| `H_R`, `eq:RacahHamiltonian` | `HR a b m n D` (matrix on `Fin (D+1)`) |
| `ω_c` | `wgtR a b m n i` |
| `Φ_f(c)` | `Phi6 a b c f m n` |
| `v_f` | `vR a b m n j` |
| `f(f+1)` | `lamR m n j` |

## Contents of `thm:6jfiniteRacah` (all proved here, no hypothesis beyond `RacahSystem`)

1. the physical lattices are `{c_min, ..., c_max}` and `{f_0, ..., f_1}` (`mem_physC_iff`,
   `mem_physF_iff`; `eq:Racahdimension` in `cMax_sub_cMin`);
2. `H_R` is self-adjoint in `ℓ²(𝒞, ω)` by detailed balance (`HR_selfadjoint_entries`,
   `HR_selfadjoint`, `HRsym_isSymm`);
3. `H_R v_f = f(f+1) v_f` (`vR_eigen`), `⟨v_f, v_g⟩_ω = δ_{fg}` (`vR_orthonormal`), i.e.
   `eq:RacahPhiOrthogonality` (`Phi6_orthogonality`, `Phi6_orthogonality_fin`);
4. `eq:RacahPhiCompleteness` (`Phi6_completeness`);
5. `spec H_R = {f(f+1)}` and each eigenvalue is simple (`HR_spectrum`, `HR_eigenspace`, `HR_charpoly`).

`thm_6jfiniteRacah` collects all of it in one statement.
-/

@[expose] public section

namespace FormalResearch.Racah.SixJ

open FormalResearch.Wigner

/-- `eq:RacahPhiOrthogonality`, indexed form: `∑_{i} ω_{c_i} Φ_{f_j}(c_i) Φ_{f_l}(c_i)
= 2/(2f_j+1) δ_{jl}`. -/
theorem Phi6_orthogonality_fin {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D)
    (j l : Fin (D + 1)) :
    ∑ i : Fin (D + 1), omegaW (wA a n) (wB b m) (cPt a b m n i) *
        (Phi6 a b (cPt a b m n i) (fPt m n j) m n * Phi6 a b (cPt a b m n i) (fPt m n l) m n) =
      if j = l then 2 / (2 * (fPt m n j : ℝ) + 1) else 0 := by
  rw [sum_fin_eq_finsum h (fun c => omegaW (wA a n) (wB b m) c *
    (Phi6 a b c (fPt m n j) m n * Phi6 a b c (fPt m n l) m n)),
    Phi6_orthogonality (fPt_mem h j) (fPt_mem h l)]
  by_cases hjl : j = l
  · subst hjl; simp
  · have : fPt m n j ≠ fPt m n l := fun e => hjl (fPt_injective m n e)
    simp [hjl, this]

/-- **`thm:6jfiniteRacah`** (Exact finite self-adjoint Racah-Wigner system).
For `a, b, m, n` with the paper's integrality conventions and a non-empty physical lattice
(`D + 1 = c_max - c_min + 1`): (1) the physical lattices; (2) detailed balance
`ω_c (H_R)_{c,c'} = ω_{c'} (H_R)_{c',c}`, i.e. self-adjointness of `H_R` in `ℓ²(𝒞, ω)`;
(3) the orthonormal eigenbasis `v_f = √((2f+1)/2) Φ_f`, `H_R v_f = f(f+1) v_f`; (4) the exact
discrete orthogonality `eq:RacahPhiOrthogonality` and completeness `eq:RacahPhiCompleteness`;
(5) `spec H_R = {f(f+1) : f_0 ≤ f ≤ f_1}`, each eigenvalue simple (also as the characteristic
polynomial). -/
theorem thm_6jfiniteRacah {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) :
    (∀ c : ℚ, c ∈ physC a b m n ↔ ∃ i : ℕ, i ≤ D ∧ c = cMin a b m n + i) ∧
    (∀ f : ℚ, f ∈ physF a b m n ↔ ∃ j : ℕ, j ≤ D ∧ f = fMin m n + j) ∧
    (∀ i j : Fin (D + 1),
      wgtR a b m n i * HR a b m n D i j = wgtR a b m n j * HR a b m n D j i) ∧
    (∀ j : Fin (D + 1), (HR a b m n D).mulVec (vR a b m n j) = lamR m n j • vR a b m n j) ∧
    (∀ j l : Fin (D + 1), ipR a b m n (vR a b m n j) (vR a b m n l) = if j = l then 1 else 0) ∧
    (∀ j l : Fin (D + 1),
      ∑ i : Fin (D + 1), wgtR a b m n i *
          (Phi6 a b (cPt a b m n i) (fPt m n j) m n * Phi6 a b (cPt a b m n i) (fPt m n l) m n) =
        if j = l then 2 / (2 * (fPt m n j : ℝ) + 1) else 0) ∧
    (∀ i i' : Fin (D + 1),
      ∑ j : Fin (D + 1), ((2 * (fPt m n j : ℝ) + 1) / 2) *
          (Phi6 a b (cPt a b m n i) (fPt m n j) m n * Phi6 a b (cPt a b m n i') (fPt m n j) m n) =
        if i = i' then (wgtR a b m n i)⁻¹ else 0) ∧
    (∀ μ : ℝ, (∃ q : Fin (D + 1) → ℝ, q ≠ 0 ∧ (HR a b m n D).mulVec q = μ • q) ↔
      ∃ j : Fin (D + 1), μ = lamR m n j) ∧
    (∀ (j : Fin (D + 1)) (q : Fin (D + 1) → ℝ),
      (HR a b m n D).mulVec q = lamR m n j • q → ∃ t : ℝ, q = t • vR a b m n j) ∧
    (HR a b m n D).charpoly = ∏ j : Fin (D + 1), (Polynomial.X - Polynomial.C (lamR m n j)) := by
  refine ⟨?_, ?_, HR_selfadjoint_entries h, vR_eigen h, vR_orthonormal h, ?_, Phi6_completeness h,
    HR_spectrum h, HR_eigenspace h, HR_charpoly h⟩
  · intro c
    rw [mem_physC_iff h.labels]
    have := h.dim
    constructor
    · rintro ⟨i, hi, hc⟩
      exact ⟨i, by exact_mod_cast (show (i : ℚ) ≤ D by linarith), hc⟩
    · rintro ⟨i, hi, hc⟩
      exact ⟨i, by have : (i : ℚ) ≤ D := by exact_mod_cast hi
                   linarith, hc⟩
  · intro f
    rw [mem_physF_iff h.labels]
    have := h.dim
    have h3 := cMax_sub_cMin a b m n
    constructor
    · rintro ⟨i, hi, hc⟩
      exact ⟨i, by exact_mod_cast (show (i : ℚ) ≤ D by linarith), hc⟩
    · rintro ⟨i, hi, hc⟩
      exact ⟨i, by have : (i : ℚ) ≤ D := by exact_mod_cast hi
                   linarith, hc⟩
  · exact Phi6_orthogonality_fin h

/-- info: 'FormalResearch.Racah.SixJ.thm_6jfiniteRacah' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thm_6jfiniteRacah

/-- Non-vacuity: `a = 3, b = 2, m = n = 0` gives `𝒞 = {1, ..., 5}`, `D = 4`. -/
theorem racahSystem_example : RacahSystem (3 : ℚ) 2 0 0 4 := by
  refine ⟨⟨⟨6, by norm_num⟩, ⟨4, by norm_num⟩, ⟨0, by norm_num⟩, ⟨0, by norm_num⟩⟩, ?_⟩
  unfold cMax cMin
  norm_num [max_def, min_def, abs_of_nonneg]

/-- Non-vacuity, half-integer labels: `a = 5/2, b = 3/2, m = 1, n = 0`, `D = 3`. -/
theorem racahSystem_example_half : RacahSystem (5 / 2 : ℚ) (3 / 2) 1 0 3 := by
  refine ⟨⟨⟨5, by norm_num⟩, ⟨3, by norm_num⟩, ⟨2, by norm_num⟩, ⟨1, by norm_num⟩⟩, ?_⟩
  unfold cMax cMin
  norm_num [max_def, min_def]

end FormalResearch.Racah.SixJ
