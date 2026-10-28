import FormalResearch.FourQubitEntropy.PaperECriticalCuts

/-!
# The critical-slice identity (Z) for the sextic `F`

For `ψ = G(v)` the three cut spectra are `|v|²`, `|H₊ v|²`, `|H₋ v|²`, so `n, P, T` of `G(v)` are
explicit, and `F = 17 n P - 12 T - 12 n³` is a sum of twelve squared moduli (`(Z)` of
`sextic_identity.tex`, proof of `prop:fqe-moment-zeros`). Proved as a polynomial identity; no
hypotheses and no `native_decide`.
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.PaperECritical
open FormalResearch.FourQubitEntropy

theorem zmat_Gv (v : Fin 2 × Fin 2 → ℂ) : zmat (Gv v) = magicB * Matrix.diagonal v * magicBᵀ := by
  unfold Gv; rw [zmat_ofZmat]

theorem Gv_n (v : Fin 2 × Fin 2 → ℂ) : normSqPsi (Gv v) = ∑ k, Complex.normSq (v k) :=
  normSqPsi_of_diag _ v (zmat_Gv v)

theorem Gv_purity (v : Fin 2 × Fin 2 → ℂ) :
    purity (Gv v) = ∑ k, Complex.normSq (v k) ^ 2 + ∑ k, Complex.normSq (wp v k) ^ 2 +
      ∑ k, Complex.normSq (wm v k) ^ 2 := by
  unfold purity
  rw [red13_eq_swap, red14_eq_swap, red12_pow_two _ v (zmat_Gv v),
    red12_pow_two _ (wp v) (zmat_swap23_Gv v), red12_pow_two _ (wm v) (zmat_swap24_Gv v)]

theorem Gv_cubic (v : Fin 2 × Fin 2 → ℂ) :
    cubicMoment (Gv v) = ∑ k, Complex.normSq (v k) ^ 3 + ∑ k, Complex.normSq (wp v k) ^ 3 +
      ∑ k, Complex.normSq (wm v k) ^ 3 := by
  unfold cubicMoment
  rw [red13_eq_swap, red14_eq_swap, red12_pow_three _ v (zmat_Gv v),
    red12_pow_three _ (wp v) (zmat_swap23_Gv v), red12_pow_three _ (wm v) (zmat_swap24_Gv v)]

/-- One summand of `(Z)`: `|v̄_i (v_j² - v_k²) + 2 v_i (p_j - p_k)|²`, `p = |v|²`. -/
noncomputable def Zterm (v : Fin 2 × Fin 2 → ℂ) (i j k : Fin 2 × Fin 2) : ℝ :=
  Complex.normSq ((starRingEnd ℂ) (v i) * (v j ^ 2 - v k ^ 2) +
    2 * v i * ((Complex.normSq (v j) : ℂ) - (Complex.normSq (v k) : ℂ)))

/-- The twelve summands of `(Z)`. -/
noncomputable def Zsum (v : Fin 2 × Fin 2 → ℂ) : ℝ :=
  Zterm v (0, 0) (0, 1) (1, 0) + Zterm v (0, 0) (0, 1) (1, 1) + Zterm v (0, 0) (1, 0) (1, 1) +
  Zterm v (0, 1) (0, 0) (1, 0) + Zterm v (0, 1) (0, 0) (1, 1) + Zterm v (0, 1) (1, 0) (1, 1) +
  Zterm v (1, 0) (0, 0) (0, 1) + Zterm v (1, 0) (0, 0) (1, 1) + Zterm v (1, 0) (0, 1) (1, 1) +
  Zterm v (1, 1) (0, 0) (0, 1) + Zterm v (1, 1) (0, 0) (1, 0) + Zterm v (1, 1) (0, 1) (1, 0)

set_option maxHeartbeats 8000000 in
/-- **Critical-slice identity (Z)** (proved): `F(G(v)) = Σ_i Σ_{j<k, j,k ≠ i}
|v̄_i (v_j² - v_k²) + 2 v_i (p_j - p_k)|²`. -/
theorem sexticF_Gv (v : Fin 2 × Fin 2 → ℂ) : sexticF (Gv v) = Zsum v := by
  unfold sexticF
  rw [Gv_n, Gv_purity, Gv_cubic]
  simp only [Zsum, Zterm, Fintype.sum_prod_type, Fin.sum_univ_two, wp, wm, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.div_ofNat_re, Complex.div_ofNat_im, pow_two,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
    Complex.im_ofNat]
  ring

end FormalResearch.FourQubitEntropy.PaperECritical
