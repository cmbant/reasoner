import FormalResearch.FourQubitEntropy.SevenQubitIcoSpectrum

/-!
# Spectra of the two-qubit (pair) marginals of the seven-qubit icosahedral family

Companion of `SevenQubitIcoCert` / `SevenQubitIcoSpectrum` (the 35 three-qubit cuts) for the 21
two-qubit cuts of `icosahedralState alpha beta` (`thm:ico` of `icosahedral_state.tex`; the paper
states the pair *purities* there, item 3, and this file proves the pair *spectra*, which the paper
does not state, from which those purities are recovered).

For every one of the 21 pair cuts the integer Gram matrices `P`, `Q`, `R` (of `αα`, `αβ+βα`, `ββ`)
are checked in the kernel to be `Q = 0` and `P`, `R` diagonal. So every pair marginal is a
*diagonal* matrix, and its spectrum is its diagonal:

* pairs avoiding the special site `0` (15 of them): `8α²` (twice) and `7α²+β²` (twice);
* pairs containing it (6 of them): `10α²` (twice) and `5α²+β²` (twice).

Spectra are stated as `∑ g(eigenvalue)` for every function `g`, i.e. as multisets.
Consequences proved here: the mean pair von Neumann entropy (nats, `meanPairEntropy`) over the 21
cuts, its value on the family `α² = (1-2x)/30`, `β² = x`, the eigenvalues at `x = 37/524`, and the
pair purities `pairCut_purity` re-derived from the spectra (`∑ λ² = purity`).

What is proved: all statements below, for all real `alpha beta` (exact kernel certificates plus the
spectral-theorem argument for diagonal Hermitian matrices). Not proved here: any extremality
statement for the mean pair entropy (the paper makes none).
-/

open Matrix

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

/-! ### Integer certificates for every pair cut -/

abbrev Pair := Fin 2 → Bool

/-- Pair cuts avoiding the special site: `Q = 0`, `P = diag(7,8,8,7)`, `R = diag(1,0,0,1)`
(indexed by the two bits `a 0`, `a 1`; the diagonal value depends on whether they agree). -/
def PairAvoidCert (cut : Cut 2 5) : Prop :=
  ∀ a b : Pair, gramQ cut a b = 0 ∧
    gramP cut a b = (if a = b then (if a 0 = a 1 then 7 else 8) else 0) ∧
    gramR cut a b = (if a = b then (if a 0 = a 1 then 1 else 0) else 0)

/-- Pair cuts containing the special site: `Q = 0`, `P = diag(10,5,5,10)`, `R = diag(0,1,1,0)`. -/
def PairContainCert (cut : Cut 2 5) : Prop :=
  ∀ a b : Pair, gramQ cut a b = 0 ∧
    gramP cut a b = (if a = b then (if a 0 = a 1 then 10 else 5) else 0) ∧
    gramR cut a b = (if a = b then (if a 0 = a 1 then 0 else 1) else 0)

instance (cut : Cut 2 5) : Decidable (PairAvoidCert cut) := by unfold PairAvoidCert; infer_instance
instance (cut : Cut 2 5) : Decidable (PairContainCert cut) := by unfold PairContainCert; infer_instance

/-- The certificates of a mask: `PairAvoidCert` or `PairContainCert` according to the special site. -/
def PairCutCert (m : Fin 7 → Bool) : Prop :=
  weight m = 2 →
    (m 0 = true → PairContainCert (maskCut 2 5 m)) ∧ (¬ m 0 = true → PairAvoidCert (maskCut 2 5 m))

instance (m : Fin 7 → Bool) : Decidable (PairCutCert m) := by unfold PairCutCert; infer_instance

theorem pairCutCert_chunk0 : ∀ k < 16, PairCutCert (maskOfNat (16 * 0 + k)) := by decide +kernel
theorem pairCutCert_chunk1 : ∀ k < 16, PairCutCert (maskOfNat (16 * 1 + k)) := by decide +kernel
theorem pairCutCert_chunk2 : ∀ k < 16, PairCutCert (maskOfNat (16 * 2 + k)) := by decide +kernel
theorem pairCutCert_chunk3 : ∀ k < 16, PairCutCert (maskOfNat (16 * 3 + k)) := by decide +kernel
theorem pairCutCert_chunk4 : ∀ k < 16, PairCutCert (maskOfNat (16 * 4 + k)) := by decide +kernel
theorem pairCutCert_chunk5 : ∀ k < 16, PairCutCert (maskOfNat (16 * 5 + k)) := by decide +kernel
theorem pairCutCert_chunk6 : ∀ k < 16, PairCutCert (maskOfNat (16 * 6 + k)) := by decide +kernel
theorem pairCutCert_chunk7 : ∀ k < 16, PairCutCert (maskOfNat (16 * 7 + k)) := by decide +kernel

theorem pair_cuts_cert (m : Fin 7 → Bool) : PairCutCert m := by
  obtain ⟨n, hn, rfl⟩ := maskOfNat_surjective m
  obtain ⟨c, k, hk, hc, rfl⟩ : ∃ c k, k < 16 ∧ c < 8 ∧ n = 16 * c + k :=
    ⟨n / 16, n % 16, by omega, by omega, by omega⟩
  interval_cases c
  exacts [pairCutCert_chunk0 k hk, pairCutCert_chunk1 k hk, pairCutCert_chunk2 k hk,
    pairCutCert_chunk3 k hk, pairCutCert_chunk4 k hk, pairCutCert_chunk5 k hk,
    pairCutCert_chunk6 k hk, pairCutCert_chunk7 k hk]

/-! ### Spectrum of a real diagonal matrix -/

theorem sum_eigenvalues_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ)
    (ρ : Matrix ι ι ℂ) (hρ : ρ.IsHermitian) (hd : ρ = diagonal (fun i => ((d i : ℝ) : ℂ)))
    (g : ℝ → ℝ) : ∑ i, g (hρ.eigenvalues i) = ∑ i, g (d i) := by
  have hch : ρ.charpoly = ∏ i, (Polynomial.X - Polynomial.C ((d i : ℝ) : ℂ)) := by
    rw [hd]; simp [charpoly_diagonal]
  have hroots := hρ.roots_charpoly_eq_eigenvalues
  have hroots' : ρ.charpoly.roots = Multiset.map (fun i => ((d i : ℝ) : ℂ)) Finset.univ.val := by
    rw [hch, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hm := hroots.symm.trans hroots'
  have h3 := congrArg (fun m : Multiset ℂ => (m.map (fun z : ℂ => g z.re)).sum) hm
  simp only [Multiset.map_map] at h3
  have e1 : ((fun z : ℂ => g z.re) ∘ (RCLike.ofReal ∘ hρ.eigenvalues)) =
      fun i => g (hρ.eigenvalues i) := by
    funext i; simp
  have e2 : ((fun z : ℂ => g z.re) ∘ (fun i => ((d i : ℝ) : ℂ))) = fun i => g (d i) := by
    funext i; simp
  rw [e1, e2] at h3
  exact h3

/-! ### The pair reduced matrices -/

/-- The reduced density matrix of a two-qubit cut, as a complex matrix. -/
noncomputable def redMat2 (cut : Cut 2 5) (alpha beta : ℝ) : Matrix Pair Pair ℂ :=
  Matrix.of fun a b => ((entry cut alpha beta a b : ℝ) : ℂ)

theorem redMat2_isHermitian (cut : Cut 2 5) (alpha beta : ℝ) :
    (redMat2 cut alpha beta).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, redMat2, entry_symm cut alpha beta i j]

/-- Von Neumann entropy (in nats) of the reduced state of a two-qubit cut. -/
noncomputable def pairCutEntropy (cut : Cut 2 5) (alpha beta : ℝ) : ℝ :=
  ∑ i, Real.negMulLog ((redMat2_isHermitian cut alpha beta).eigenvalues i)

/-- A pair marginal with prescribed diagonal values on the equal / unequal bit patterns has spectrum
`g(e) + g(e) + g(n) + g(n)` for `e` on the two bit patterns with `a 0 = a 1` and `n` on the others. -/
theorem sum_eigenvalues_pair_diag (ρ : Matrix Pair Pair ℂ) (hρ : ρ.IsHermitian) (e n : ℝ)
    (hd : ρ = diagonal (fun a : Pair => (((if a 0 = a 1 then e else n : ℝ)) : ℂ))) (g : ℝ → ℝ) :
    ∑ i, g (hρ.eigenvalues i) = 2 * g e + 2 * g n := by
  rw [sum_eigenvalues_diagonal _ ρ hρ hd g]
  have hU : (Finset.univ : Finset Pair) =
      {![false, false], ![false, true], ![true, false], ![true, true]} := by decide +kernel
  rw [hU]
  rw [Finset.sum_insert (by decide +kernel), Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel), Finset.sum_singleton]
  simp
  ring

theorem redMat2_eq_diagonal (cut : Cut 2 5) (alpha beta : ℝ) (pe pn re rn : ℤ)
    (hQ : ∀ a b : Pair, gramQ cut a b = 0)
    (hP : ∀ a b : Pair, gramP cut a b = if a = b then (if a 0 = a 1 then pe else pn) else 0)
    (hR : ∀ a b : Pair, gramR cut a b = if a = b then (if a 0 = a 1 then re else rn) else 0) :
    redMat2 cut alpha beta = diagonal (fun a : Pair =>
      (((if a 0 = a 1 then alpha ^ 2 * pe + beta ^ 2 * re else alpha ^ 2 * pn + beta ^ 2 * rn : ℝ)) : ℂ)) := by
  ext a b
  simp only [redMat2, Matrix.of_apply, entry_expand, hQ, hP, hR]
  by_cases h : a = b
  · subst h
    by_cases h2 : a 0 = a 1 <;> simp [h2]
  · simp [h]

/-! ### Spectrum on each kind of pair cut -/

theorem spectrum_pair_avoiding (cut : Cut 2 5) (h : PairAvoidCert cut) (alpha beta : ℝ) (g : ℝ → ℝ) :
    ∑ i, g ((redMat2_isHermitian cut alpha beta).eigenvalues i) =
      2 * g (7 * alpha ^ 2 + beta ^ 2) + 2 * g (8 * alpha ^ 2) := by
  have hd := redMat2_eq_diagonal cut alpha beta 7 8 1 0 (fun a b => (h a b).1)
    (fun a b => (h a b).2.1) (fun a b => (h a b).2.2)
  rw [sum_eigenvalues_pair_diag _ (redMat2_isHermitian cut alpha beta) _ _ hd g]
  push_cast
  ring_nf

theorem spectrum_pair_containing (cut : Cut 2 5) (h : PairContainCert cut) (alpha beta : ℝ)
    (g : ℝ → ℝ) :
    ∑ i, g ((redMat2_isHermitian cut alpha beta).eigenvalues i) =
      2 * g (10 * alpha ^ 2) + 2 * g (5 * alpha ^ 2 + beta ^ 2) := by
  have hd := redMat2_eq_diagonal cut alpha beta 10 5 0 1 (fun a b => (h a b).1)
    (fun a b => (h a b).2.1) (fun a b => (h a b).2.2)
  rw [sum_eigenvalues_pair_diag _ (redMat2_isHermitian cut alpha beta) _ _ hd g]
  push_cast
  ring_nf

/-! ### Every pair cut -/

/-- The spectrum of the reduced matrix of every two-qubit cut: for each function `g`,
`∑ g(eigenvalue)` is `2 g(8α²) + 2 g(7α²+β²)` on cuts avoiding the special site `0`, and
`2 g(10α²) + 2 g(5α²+β²)` on those containing it. -/
theorem pairCut_spectrum (m : Fin 7 → Bool) (hm : weight m = 2) (alpha beta : ℝ) (g : ℝ → ℝ) :
    ∑ i, g ((redMat2_isHermitian (maskCut 2 5 m) alpha beta).eigenvalues i) =
      if m 0 = true then 2 * g (10 * alpha ^ 2) + 2 * g (5 * alpha ^ 2 + beta ^ 2)
      else 2 * g (8 * alpha ^ 2) + 2 * g (7 * alpha ^ 2 + beta ^ 2) := by
  obtain ⟨hc, ha⟩ := pair_cuts_cert m hm
  by_cases h : m 0 = true
  · simp only [h, ↓reduceIte]; exact spectrum_pair_containing _ (hc h) alpha beta g
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    rw [spectrum_pair_avoiding _ (ha h) alpha beta g]
    ring

/-- The spectra recover the pair purities `pairCut_purity`: `∑ λ² = purity`. -/
theorem pairCut_spectrum_sq_eq_purity (m : Fin 7 → Bool) (hm : weight m = 2) (alpha beta : ℝ) :
    ∑ i, ((redMat2_isHermitian (maskCut 2 5 m) alpha beta).eigenvalues i) ^ 2 =
      purity (maskCut 2 5 m) alpha beta := by
  rw [pairCut_spectrum m hm alpha beta (fun t => t ^ 2), pairCut_purity m hm]
  by_cases h : m 0 = true <;> simp [h] <;> ring

/-- The pair marginals have unit trace when `30 α² + 2 β² = 1`. -/
theorem pairCut_spectrum_sum (m : Fin 7 → Bool) (hm : weight m = 2) (alpha beta : ℝ)
    (h : 30 * alpha ^ 2 + 2 * beta ^ 2 = 1) :
    ∑ i, (redMat2_isHermitian (maskCut 2 5 m) alpha beta).eigenvalues i = 1 := by
  rw [pairCut_spectrum m hm alpha beta (fun t => t)]
  by_cases hh : m 0 = true <;> simp [hh] <;> linarith

theorem pairCut_entropy (m : Fin 7 → Bool) (hm : weight m = 2) (alpha beta : ℝ) :
    pairCutEntropy (maskCut 2 5 m) alpha beta =
      if m 0 = true then 2 * Real.negMulLog (10 * alpha ^ 2) + 2 * Real.negMulLog (5 * alpha ^ 2 + beta ^ 2)
      else 2 * Real.negMulLog (8 * alpha ^ 2) + 2 * Real.negMulLog (7 * alpha ^ 2 + beta ^ 2) :=
  pairCut_spectrum m hm alpha beta Real.negMulLog

/-- Mean von Neumann entropy (nats) over the 21 two-qubit cuts. -/
noncomputable def meanPairEntropy (alpha beta : ℝ) : ℝ :=
  (∑ m ∈ pairMasks, pairCutEntropy (maskCut 2 5 m) alpha beta) / 21

theorem meanPairEntropy_eq (alpha beta : ℝ) :
    meanPairEntropy alpha beta =
      (30 * Real.negMulLog (8 * alpha ^ 2) + 30 * Real.negMulLog (7 * alpha ^ 2 + beta ^ 2) +
        12 * Real.negMulLog (10 * alpha ^ 2) + 12 * Real.negMulLog (5 * alpha ^ 2 + beta ^ 2)) / 21 := by
  unfold meanPairEntropy
  have hs : ∀ m ∈ pairMasks, pairCutEntropy (maskCut 2 5 m) alpha beta =
      if m 0 = true then 2 * Real.negMulLog (10 * alpha ^ 2) + 2 * Real.negMulLog (5 * alpha ^ 2 + beta ^ 2)
      else 2 * Real.negMulLog (8 * alpha ^ 2) + 2 * Real.negMulLog (7 * alpha ^ 2 + beta ^ 2) :=
    fun m hm => pairCut_entropy m (Finset.mem_filter.1 hm).2 alpha beta
  rw [Finset.sum_congr rfl hs, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    pairMasks_containing_card, pairMasks_avoiding_card]
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-- On the family `α² = (1-2x)/30`, `β² = x`, with `u = (1-2x)/30`. -/
theorem meanPairEntropy_family (x alpha beta : ℝ) (hα : alpha ^ 2 = u x) (hβ : beta ^ 2 = x) :
    meanPairEntropy alpha beta =
      (30 * Real.negMulLog (8 * u x) + 30 * Real.negMulLog (7 * u x + x) +
        12 * Real.negMulLog (10 * u x) + 12 * Real.negMulLog (5 * u x + x)) / 21 := by
  rw [meanPairEntropy_eq, hα, hβ]

/-- At the icosahedral parameter `x = 37/524` (`α² = 15/524`, `β² = 37/524`) the pair spectra are
`(30/131)², (71/262)²` on the 15 pairs avoiding `0` and `(75/262)², (28/131)²` on the 6 pairs
containing it. -/
theorem pairCut_spectrum_ico (m : Fin 7 → Bool) (hm : weight m = 2) (alpha beta : ℝ)
    (hα : alpha ^ 2 = u (37 / 524)) (hβ : beta ^ 2 = 37 / 524) (g : ℝ → ℝ) :
    ∑ i, g ((redMat2_isHermitian (maskCut 2 5 m) alpha beta).eigenvalues i) =
      if m 0 = true then 2 * g (75 / 262) + 2 * g (28 / 131)
      else 2 * g (30 / 131) + 2 * g (71 / 262) := by
  rw [pairCut_spectrum m hm alpha beta g, hα, hβ]
  have e1 : 10 * u (37 / 524) = 75 / 262 := by unfold u; norm_num
  have e2 : 5 * u (37 / 524) + 37 / 524 = 28 / 131 := by unfold u; norm_num
  have e3 : 8 * u (37 / 524) = 30 / 131 := by unfold u; norm_num
  have e4 : 7 * u (37 / 524) + 37 / 524 = 71 / 262 := by unfold u; norm_num
  rw [e1, e2, e3, e4]

end FormalResearch.FourQubitEntropy.SevenQubitIco

