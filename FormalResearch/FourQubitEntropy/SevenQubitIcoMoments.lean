import FormalResearch.FourQubitEntropy.SevenQubitIcoSpectrum

/-!
# Mean marginal moments of the seven-qubit icosahedral family

Along the family `α² = u x = (1-2x)/30`, `β² = x` of `icosahedral_state.tex` (`thm:ico`), the mean
two- and three-body purities and the mean three-body third moment
`b₃ = (1/35) ∑_{|S|=3} tr ρ_S³` are

* `π₂(ψ_x) = (832x² - 112x + 163)/630`,
* `π₃(ψ_x) = (2096x² - 296x + 149)/1050` (equal to `121/917 + (1048/525)(x - 37/524)²`, see
  `meanTriplePurity_family`),
* `b₃(ψ_x) = (35008x³ + 17328x² - 3084x + 709)/31500`,

and `b₃'(37/524) = -432/120127 < 0` (item IC-6 of `icosahedral_state.tex`, `cor:ico-entropy-separation`; the Paper E §9 remark that the entropy
prefers a larger third moment and the purity minimiser is not a stationary point of `b₃`).

The cube sum is read off the proved spectra of all 35 three-qubit cuts (`tripleCut_spectrum` with
`g t = t³`); the pair mean uses the integer pair-purity coefficients of `SevenQubitIcoPurity`.
-/

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

open Finset

/-- Mean purity over the 21 two-qubit cuts. -/
noncomputable def meanPairPurity (alpha beta : ℝ) : ℝ :=
  (∑ m ∈ pairMasks, purity (maskCut 2 5 m) alpha beta) / 21

theorem meanPairPurity_eq (alpha beta : ℝ) :
    meanPairPurity alpha beta =
      (15 * (226 * alpha ^ 4 + 28 * (alpha ^ 2 * beta ^ 2) + 2 * beta ^ 4) +
        6 * (250 * alpha ^ 4 + 20 * (alpha ^ 2 * beta ^ 2) + 2 * beta ^ 4)) / 21 := by
  unfold meanPairPurity
  have hs : ∀ m ∈ pairMasks, purity (maskCut 2 5 m) alpha beta =
      if m 0 = true then 250 * alpha ^ 4 + 20 * (alpha ^ 2 * beta ^ 2) + 2 * beta ^ 4
      else 226 * alpha ^ 4 + 28 * (alpha ^ 2 * beta ^ 2) + 2 * beta ^ 4 :=
    fun m hm => pairCut_purity m (Finset.mem_filter.1 hm).2 alpha beta
  rw [Finset.sum_congr rfl hs, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    pairMasks_containing_card, pairMasks_avoiding_card]
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-- `π₂(ψ_x) = (832x² - 112x + 163)/630`. -/
theorem meanPairPurity_family (x alpha beta : ℝ) (hα : alpha ^ 2 = u x) (hβ : beta ^ 2 = x) :
    meanPairPurity alpha beta = (832 * x ^ 2 - 112 * x + 163) / 630 := by
  rw [meanPairPurity_eq, show alpha ^ 4 = (alpha ^ 2) ^ 2 by ring,
    show beta ^ 4 = (beta ^ 2) ^ 2 by ring, hα, hβ]
  unfold u
  ring

/-- `π₃(ψ_x) = (2096x² - 296x + 149)/1050`. -/
theorem meanTriplePurity_family_poly (x alpha beta : ℝ) (hα : alpha ^ 2 = u x) (hβ : beta ^ 2 = x) :
    meanTriplePurity alpha beta = (2096 * x ^ 2 - 296 * x + 149) / 1050 := by
  rw [meanTriplePurity_family x alpha beta hα hβ]
  ring

/-- Mean of `tr ρ_S³` over the 35 three-qubit cuts. -/
noncomputable def meanTripleCube (alpha beta : ℝ) : ℝ :=
  (∑ m ∈ tripleMasks,
      ∑ i, ((redMat_isHermitian (maskCut 3 4 m) alpha beta).eigenvalues i) ^ 3) / 35

theorem meanTripleCube_eq (alpha beta : ℝ) :
    meanTripleCube alpha beta =
      (20 * (6 * (4 * alpha ^ 2) ^ 3 + 2 * (3 * alpha ^ 2 + beta ^ 2) ^ 3) +
        15 * (5 * (4 * alpha ^ 2) ^ 3 + (8 * alpha ^ 2) ^ 3 + 2 * (alpha ^ 2 + beta ^ 2) ^ 3)) / 35 := by
  unfold meanTripleCube
  have hs : ∀ m ∈ tripleMasks,
      ∑ i, ((redMat_isHermitian (maskCut 3 4 m) alpha beta).eigenvalues i) ^ 3 =
      if m 0 = true then
        5 * (4 * alpha ^ 2) ^ 3 + (8 * alpha ^ 2) ^ 3 + 2 * (alpha ^ 2 + beta ^ 2) ^ 3
      else 6 * (4 * alpha ^ 2) ^ 3 + 2 * (3 * alpha ^ 2 + beta ^ 2) ^ 3 :=
    fun m hm => tripleCut_spectrum m (Finset.mem_filter.1 hm).2 alpha beta (fun t => t ^ 3)
  rw [Finset.sum_congr rfl hs, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    tripleMasks_containing_card, tripleMasks_avoiding_card]
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-- The third moment polynomial `b₃(x) = (35008x³ + 17328x² - 3084x + 709)/31500`. -/
noncomputable def b3 (x : ℝ) : ℝ := (35008 * x ^ 3 + 17328 * x ^ 2 - 3084 * x + 709) / 31500

theorem meanTripleCube_family (x alpha beta : ℝ) (hα : alpha ^ 2 = u x) (hβ : beta ^ 2 = x) :
    meanTripleCube alpha beta = b3 x := by
  rw [meanTripleCube_eq, hα, hβ]
  unfold u b3
  ring

theorem hasDerivAt_b3 (x : ℝ) :
    HasDerivAt b3 ((3 * 35008 * x ^ 2 + 2 * 17328 * x - 3084) / 31500) x := by
  have h3 := hasDerivAt_pow 3 x
  have h2 := hasDerivAt_pow 2 x
  have h1 := hasDerivAt_id x
  have h := ((((h3.const_mul (35008 : ℝ)).add (h2.const_mul (17328 : ℝ))).sub
    (h1.const_mul (3084 : ℝ))).add_const (709 : ℝ)).div_const 31500
  convert h using 1
  · funext y
    simp only [b3, Pi.add_apply, Pi.sub_apply, id]
  · push_cast
    ring

/-- `b₃'(37/524) = -432/120127 < 0`: the purity minimiser is not stationary for the third moment,
so the entropy prefers `x` below `37/524`. -/
theorem b3_deriv_ico :
    deriv b3 (37 / 524) = -432 / 120127 := by
  rw [(hasDerivAt_b3 _).deriv]
  norm_num

theorem b3_deriv_ico_neg : deriv b3 (37 / 524) < 0 := by
  rw [b3_deriv_ico]; norm_num

end FormalResearch.FourQubitEntropy.SevenQubitIco
