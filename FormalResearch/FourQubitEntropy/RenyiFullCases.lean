import FormalResearch.FourQubitEntropy.RenyiFullHZ

/-!
# The cases of `thm:fqe-renyi-classical` at the lower anchor `q_s`

Paper E, proof of `thm:fqe-renyi-classical` (`sup_renyi.tex`, `sec:sup-renyi-classical-proof`):

* `caseL`: the rectangle `L` (`3/20 ≤ F ≤ 11/25`), from `RationalDual`;
* `caseC`: the capped region (`F ≥ 11/25`, `ε ≤ 1/100`, every `p_j ≤ 47/100`), from `CappedCubic`
  (`cor:fqe-capped-cluster`);
* `caseSliver`: the cluster sliver (one `p_j ≥ 47/100`), from `NearUniformDual`, `ClusterSliver`,
  `DetReduction` and the third-moment lemma.

All three give `E_{q_s} < 5/3`.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy

/-- **Band `L`**: from `RationalDual`, `E_{q_s} ≤ 5/3 - 10⁻⁵` on `3/20 ≤ F ≤ 11/25`, `20ε + 2F < 1`. -/
theorem caseL (hL : RationalDual) {l₂ l₃ l₄ : Fin 4 → ℝ} (R : RelaxTriple l₂ l₃ l₄)
    (hF1 : 3 / 20 ≤ Fm l₂ l₃ l₄) (hF2 : Fm l₂ l₃ l₄ ≤ 11 / 25)
    (hE : 20 * (Pm l₂ l₃ l₄ - 1) + 2 * Fm l₂ l₃ l₄ < 1) :
    Em qS l₂ l₃ l₄ < 5 / 3 := by
  have hP0 := R.P_ge
  have hε1 : Pm l₂ l₃ l₄ - 1 ≤ 1 / 20 := by linarith
  obtain ⟨q2, q3, q4⟩ := pur_le_of_triple R.prob₂ R.prob₃ R.prob₄ hε1
  have s2 := hL l₂ R.prob₂ (by linarith)
  have s3 := hL l₃ R.prob₃ (by linarith)
  have s4 := hL l₄ R.prob₄ (by linarith)
  have hd := dual_bound R.QK qS aL bL gL (by unfold gL; norm_num)
  have hc := ell_ge_min_corner (α := aL) (β := bL) (γ := gL) (ε₀ := 0) (ε₁ := 1 / 9)
    (F₀ := 3 / 20) (F₁ := 11 / 25) (ε := Pm l₂ l₃ l₄ - 1) (F := Fm l₂ l₃ l₄)
    (by unfold gL; norm_num) (by linarith) (by linarith) hF1 hF2
  have hW : WL = 5 / 3 + (1 / 3) * min (min (ell aL bL gL 0 (3 / 20)) (ell aL bL gL 0 (11 / 25)))
    (min (ell aL bL gL (1 / 9) (3 / 20)) (ell aL bL gL (1 / 9) (11 / 25))) := rfl
  have hEm : Em qS l₂ l₃ l₄ = (renyiSpec qS l₂ + renyiSpec qS l₃ + renyiSpec qS l₄) / 3 := rfl
  rw [hEm]
  linarith


/-! ### The capped region -/

theorem sq_sum_sorted {x y z s a : ℝ} (hz : 0 ≤ z) (hzy : z ≤ y) (hyx : y ≤ x) (hxa : x ≤ a)
    (hs : x + y + z = s) : x^2 + y^2 + z^2 ≤ a^2 + (s - a)^2 := by
  have e : a^2 + (s - a)^2 - (x^2 + y^2 + z^2) = 2 * y * z + 2 * (a - x) * (a - y - z) := by
    subst hs; ring
  have hy0 : 0 ≤ y := hz.trans hzy
  rcases le_total (y + z) a with h | h
  · nlinarith [mul_nonneg hy0 hz, mul_nonneg (sub_nonneg.2 hxa) (sub_nonneg.2 h)]
  · have h1 : (a - x) * (y + z - a) ≤ (a - y) * (y + z - a) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith [mul_nonneg hy0 (sub_nonneg.2 h), mul_nonneg (sub_nonneg.2 (hxa.trans' hyx)) (sub_nonneg.2 (hxa.trans' (hzy.trans hyx))),
      mul_nonneg hy0 hz]

theorem sq_sum_box {x y z s a : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hxa : x ≤ a) (hya : y ≤ a)
    (hza : z ≤ a) (hs : x + y + z = s) : x^2 + y^2 + z^2 ≤ a^2 + (s - a)^2 := by
  rcases le_total x y with h1 | h1 <;> rcases le_total y z with h2 | h2 <;>
    rcases le_total x z with h3 | h3
  · have := sq_sum_sorted (s := s) (a := a) hx h1 h2 hza (by linarith); linarith
  · have := sq_sum_sorted (s := s) (a := a) hx h1 h2 hza (by linarith); linarith
  · have := sq_sum_sorted (s := s) (a := a) hx h3 h2 hya (by linarith); linarith
  · have := sq_sum_sorted (s := s) (a := a) hz h3 h1 hya (by linarith); linarith
  · have := sq_sum_sorted (s := s) (a := a) hy h1 h3 hza (by linarith); linarith
  · have := sq_sum_sorted (s := s) (a := a) hy h2 h3 hxa (by linarith); linarith
  · have := sq_sum_sorted (s := s) (a := a) hz h2 h1 hxa (by linarith); linarith
  · have := sq_sum_sorted (s := s) (a := a) hz h2 h1 hxa (by linarith); linarith

/-- **`cor:fqe-capped-cluster`**: from `CappedCubic`, three spectra with `1 ≤ P ≤ 101/100`, `F ≥ 11/25`
and every `p_j ≤ 47/100` have `E_{q_s} < 5/3`. -/
theorem caseC (hC : CappedCubic) {l₂ l₃ l₄ : Fin 4 → ℝ} (R : RelaxTriple l₂ l₃ l₄)
    (hF : 11 / 25 ≤ Fm l₂ l₃ l₄) (hε : Pm l₂ l₃ l₄ - 1 ≤ 1 / 100)
    (b2 : pur l₂ ≤ 47 / 100) (b3 : pur l₃ ≤ 47 / 100) (b4 : pur l₄ ≤ 47 / 100) :
    Em qS l₂ l₃ l₄ < 5 / 3 := by
  have hP0 := R.P_ge
  have q2 := pur_ge_quarter R.prob₂
  have q3 := pur_ge_quarter R.prob₃
  have q4 := pur_ge_quarter R.prob₄
  have c2' := hC l₂ R.prob₂ b2
  have c3' := hC l₃ R.prob₃ b3
  have c4' := hC l₄ R.prob₄ b4
  have hU := sq_sum_box (x := pur l₂ - 1 / 4) (y := pur l₃ - 1 / 4) (z := pur l₄ - 1 / 4)
    (s := Pm l₂ l₃ l₄ - 3 / 4) (a := 22 / 100) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by unfold Pm; ring)
  have hEm : Em qS l₂ l₃ l₄ = (renyiSpec qS l₂ + renyiSpec qS l₃ + renyiSpec qS l₄) / 3 := rfl
  unfold Fm Tm Pm at hF
  rw [hEm]
  unfold Pm at hε hP0 hU
  have hprod : 0 ≤ (pur l₂ + pur l₃ + pur l₄ - 1) * (101 / 100 - (pur l₂ + pur l₃ + pur l₄)) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hU, hprod]

end FormalResearch.FourQubitEntropy.RenyiFull
