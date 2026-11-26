module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbConstants

/-!
# Paper J, Theorem B, L3.5c, part 15: the gauge `D_-` and the column reversal on a `ThbBlock`

Source: Paper J `app_thmB.tex`, proof of `prop:thb-inputs` (I1)--(I5): "a column in `Sigma^-` is `D_-` times such a vector for `-D_- J_h D_-`, and `D_- Psi_k` is the eigenvector of `-D_- J_h D_-` in the gauge `(.)_0 > 0`": the lower soft block is the upper soft block of
the gauge family, transported back along `U' = D U R`, `G' = D G R` (`D = diag((-1)^i)`, `R` the column reversal `k |-> N - k`).

## Proved here

* `l2_submatrix_equiv_le`, `isSchurBdd_gauge`: the `l^2` operator norm does not increase under a reindexing of the columns, hence a Schur bound survives a reindexing of the columns and a change of sign.
* `chartGauge`, `chartOk_gauge`: the chart of the gauge frame transported to the original frame: the model pair and the exterior row change sign by `(-1)^(row)` (the transfer coefficients `t_11, t_12` change sign, `alpha`, `t_11/t_12`, `kappa` do not), the hosts are
  `D host R`.
* **`ThbBlock.gauge`**: from a `ThbBlock` for `(U', G0', G1')` on the columns `cols.image rev` with `U' (rev k) = D U k`, `G' (rev k) = D G k`, a `ThbBlock` for `(U, G0, G1)` on `cols`, same constants.

## Differences from the paper

None.  **Not formalised**: nothing.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open FormalResearch.JB
open Matrix
open scoped Matrix.Norms.L2Operator

section Schur

variable {ι κ κ' : Type*} [Fintype ι] [Fintype κ] [Fintype κ'] [DecidableEq ι] [DecidableEq κ] [DecidableEq κ']

theorem l2_submatrix_equiv_le (M : Matrix ι κ ℝ) (e : κ' ≃ κ) : ‖M.submatrix id e‖ ≤ ‖M‖ := by
  rw [Matrix.l2_opNorm_def (M.submatrix id e)]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  have h := Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 (x.ofLp ∘ e.symm))
  have hx : ‖(WithLp.toLp 2 (x.ofLp ∘ e.symm) : EuclideanSpace ℝ κ)‖ = ‖x‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    exact Equiv.sum_comp e.symm (fun a => ‖x.ofLp a‖ ^ 2)
  rw [hx] at h
  convert h using 2
  ext i
  simp only [LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply, EuclideanSpace.equiv, WithLp.ofLp_toLp,
    Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id]
  show _ = (M *ᵥ (x.ofLp ∘ e.symm)) i
  simp only [Matrix.mulVec, dotProduct, Function.comp_apply]
  exact (Equiv.sum_comp e (fun a => M i a * x.ofLp (e.symm a))).symm ▸ (Finset.sum_congr rfl fun a _ => by simp)

/-- A Schur bound survives a reindexing of the columns. -/
theorem isSchurBdd_submatrix {Φ : Matrix ι κ' ℝ} {K : ℝ} (h : IsSchurBdd Φ K) (e : κ ≃ κ') :
    IsSchurBdd (Φ.submatrix id e) K := by
  refine ⟨h.1, fun Y => ?_⟩
  have e1 : (Φ.submatrix id e ⊙ Y) = (Φ ⊙ Y.submatrix id e.symm).submatrix id e := by
    ext n k; simp
  rw [e1]
  calc ‖(Φ ⊙ Y.submatrix id e.symm).submatrix id e‖ ≤ ‖Φ ⊙ Y.submatrix id e.symm‖ := l2_submatrix_equiv_le _ e
    _ ≤ K * ‖Y.submatrix id e.symm‖ := h.2 _
    _ ≤ K * ‖Y‖ := mul_le_mul_of_nonneg_left (l2_submatrix_equiv_le Y e.symm) h.1

/-- A Schur bound survives a change of sign. -/
theorem isSchurBdd_neg' {Φ : Matrix ι κ ℝ} {K : ℝ} (h : IsSchurBdd Φ K) : IsSchurBdd (Matrix.of fun n k => -Φ n k) K := by
  have := (isSchurBdd_const (ι := ι) (κ := κ) (-1)).hadamard h
  have e : (Matrix.of fun (_ : ι) (_ : κ) => (-1 : ℝ)) ⊙ Φ = Matrix.of fun n k => -Φ n k := by
    ext n k; simp
  rw [e] at this
  simpa using this

end Schur

section Gauge

variable {N R : ℕ} {cols cols' : Finset (Fin (N + 1))}

/-- The sign `(-1)^i` of the gauge `D_-`. -/
abbrev gsg (i : ℕ) : ℝ := (-1 : ℝ) ^ i

theorem gsg_sq (i : ℕ) : gsg i * gsg i = 1 := by
  unfold gsg
  rw [← mul_pow]; simp

theorem gsg_succ (i : ℕ) : gsg (i + 1) = - gsg i := by
  unfold gsg
  rw [pow_succ]; ring

theorem sq_gauge (s a u : ℝ) (hss : s * s = 1) : (s * a - u) ^ 2 = (a - s * u) ^ 2 := by
  linear_combination (a ^ 2 - u ^ 2) * hss

theorem jbL2_gsg {ι : Type*} (S : Finset ι) (s v : ι → ℝ) (hs : ∀ i, s i * s i = 1) :
    jbL2 S (fun i => s i * v i) = jbL2 S v := by
  unfold jbL2
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  linear_combination (v i) ^ 2 * hs i

/-- The row (in the sense of the sign) of the exterior row of a chart: the last row `R - 1` of an upward chart, the first row `0` of a downward one. -/
def gaugeExtRow (c : Chart (N + 1) R cols') : ℕ := c.lo + (if c.τ then R - 1 else 0)

/-- **The chart of the gauge frame, seen from the original frame**: the model pair `(y, y~)` and the exterior row are multiplied by the sign `(-1)^row`, the transfer coefficients `t_11, t_12` change sign (so that
`alpha`, `t_11/t_12`, `kappa` and the Schur data are those of `c`), the columns are relabelled by `e` (`e k = rev k`), and the hosts are `D host R`. -/
def chartGauge (e : cols ≃ cols') (c : Chart (N + 1) R cols') : Chart (N + 1) R cols where
  lo := c.lo
  lo_add := c.lo_add
  τ := c.τ
  used := c.used
  y := Matrix.of fun n k => gsg (c.lo + n.val) * c.y n (e k)
  yt := Matrix.of fun n k => gsg (c.lo + n.val) * c.yt n (e k)
  yext := fun k => -(gsg (gaugeExtRow c)) * c.yext (e k)
  ω := c.ω
  t11 := Matrix.of fun n k => -c.t11 n (e k)
  t12 := Matrix.of fun n k => -c.t12 n (e k)
  A0 := Matrix.of fun n k => c.A0 n (e k)
  A1 := Matrix.of fun n k => c.A1 n (e k)
  B0 := Matrix.of fun n k => c.B0 n (e k)
  B1 := Matrix.of fun n k => c.B1 n (e k)
  κ := Matrix.of fun n k => c.κ n (e k)
  σ0 := fun k => c.σ0 (e k)
  σ1 := fun k => c.σ1 (e k)
  P := fun k => c.P (e k)
  host0 := Matrix.of fun i j => gsg i.val * c.host0 i (Fin.rev j)
  host1 := Matrix.of fun i j => gsg i.val * c.host1 i (Fin.rev j)

theorem chartGauge_row (e : cols ≃ cols') (c : Chart (N + 1) R cols') (n : Fin R) : (chartGauge e c).row n = c.row n := rfl

theorem chartGauge_shifted (e : cols ≃ cols') (c : Chart (N + 1) R cols') (n : Fin R) (k : cols) :
    (chartGauge e c).shifted (chartGauge e c).y n k = -(gsg (c.lo + n.val)) * c.shifted c.y n (e k) := by
  unfold Chart.shifted
  cases hτ : c.τ
  · simp only [chartGauge, hτ, Bool.false_eq_true, ite_false, YshRev, Matrix.of_apply]
    by_cases hn : 0 < n.val
    · rw [dite_eq_left hn, dite_eq_left hn]
      have : c.lo + (n.val - 1) + 1 = c.lo + n.val := by omega
      have h2 := gsg_succ (c.lo + (n.val - 1))
      rw [this] at h2
      rw [show c.lo + (n.val - 1) = c.lo + (n.val - 1) from rfl]
      have h3 : gsg (c.lo + (n.val - 1)) = -gsg (c.lo + n.val) := by linarith
      simp only [Matrix.of_apply, h3]
      try ring
    · rw [dite_eq_right hn, dite_eq_right hn]
      have : gaugeExtRow c = c.lo + n.val := by
        unfold gaugeExtRow; simp only [hτ, Bool.false_eq_true, ite_false]; omega
      simp only [this]
      try ring
  · simp only [chartGauge, hτ, ite_true, Ysh, Matrix.of_apply]
    by_cases hn : n.val + 1 < R
    · rw [dite_eq_left hn, dite_eq_left hn]
      have h2 := gsg_succ (c.lo + n.val)
      simp only [Matrix.of_apply, show c.lo + (n.val + 1) = c.lo + n.val + 1 from by omega, h2]
      try ring
    · rw [dite_eq_right hn, dite_eq_right hn]
      have : gaugeExtRow c = c.lo + n.val := by
        have := n.isLt
        unfold gaugeExtRow; simp only [hτ, ite_true]; omega
      simp only [this]
      try ring

theorem chartGauge_H0 (e : cols ≃ cols') (c : Chart (N + 1) R cols') (h : ℝ) (n : Fin R) (k : cols) :
    (chartGauge e c).H0 h n k = gsg (c.lo + n.val) * c.H0 h n (e k) := by
  simp only [Chart.H0_apply, Chart.phi0_apply, chartGauge, Matrix.of_apply]
  ring

theorem chartGauge_H1 (e : cols ≃ cols') (c : Chart (N + 1) R cols') (h : ℝ) (n : Fin R) (k : cols) :
    (chartGauge e c).H1 h n k = gsg (c.lo + n.val) * c.H1 h n (e k) := by
  simp only [Chart.H1_apply, Chart.phi1_apply, chartGauge, Matrix.of_apply]
  ring

theorem chartOk_gauge {cs : OneStepConsts} {m : ℕ} {h : ℝ} {Um Um' : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (e : cols ≃ cols')
    (hev : ∀ k : cols, ((e k : cols') : Fin (N + 1)) = Fin.rev (k : Fin (N + 1)))
    (hU : ∀ i k, Um' i (Fin.rev k) = gsg i.val * Um i k) {c : Chart (N + 1) R cols'} (hc : c.Ok cs m h Um') :
    (chartGauge e c).Ok cs m h Um := by
  have hrow : ∀ n : Fin R, (((c.row n : Fin (N + 1)) : ℕ)) = c.lo + n.val := fun n => rfl
  refine
  { host0_eq := ?_, host1_eq := ?_, host0_col := ?_, host1_col := ?_, parity_A := ?_, parity_B := ?_, ω_pos := ?_, transfer := ?_,
    t12_lb := ?_, α_lb := ?_, schur_inv_α := ?_, schur_B := ?_, schur_inv_t12 := ?_, schur_t11 := ?_, schur_κ := ?_, ext_row := ?_,
    overlap_lb := ?_, overlap_ub := ?_ }
  · intro n k
    rw [chartGauge_H0]
    have h1 := hc.host0_eq n (e k)
    rw [h1]
    show _ = gsg ((c.row n : Fin (N + 1)) : ℕ) * c.host0 (c.row n) (Fin.rev k)
    rw [hrow, ← hev k]
  · intro n k
    rw [chartGauge_H1]
    have h1 := hc.host1_eq n (e k)
    rw [h1]
    show _ = gsg ((c.row n : Fin (N + 1)) : ℕ) * c.host1 (c.row n) (Fin.rev k)
    rw [hrow, ← hev k]
  · intro j
    refine le_of_eq_of_le ?_ (hc.host0_col (Fin.rev j))
    unfold jbL2; congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    show (gsg i.val * c.host0 i (Fin.rev j) - Um i j) ^ 2 = (c.host0 i (Fin.rev j) - Um' i (Fin.rev j)) ^ 2
    rw [hU i j]
    exact sq_gauge _ _ _ (gsg_sq _)
  · intro j
    refine le_of_eq_of_le ?_ (hc.host1_col (Fin.rev j))
    unfold jbL2; congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    show (gsg i.val * c.host1 i (Fin.rev j) - Um i j) ^ 2 = (c.host1 i (Fin.rev j) - Um' i (Fin.rev j)) ^ 2
    rw [hU i j]
    exact sq_gauge _ _ _ (gsg_sq _)
  · intro n k; exact hc.parity_A n (e k)
  · intro n k; exact hc.parity_B n (e k)
  · intro n; exact hc.ω_pos n
  · intro n k
    rw [chartGauge_shifted]
    have h1 := hc.transfer n (e k)
    show c.ω n * (-(gsg (c.lo + n.val)) * c.shifted c.y n (e k)) = -c.t11 n (e k) * (gsg (c.lo + n.val) * c.y n (e k)) +
      -c.t12 n (e k) * (gsg (c.lo + n.val) * c.yt n (e k))
    linear_combination (-(gsg (c.lo + n.val))) * h1
  · intro n k
    show cs.cT ≤ |-c.t12 n (e k)|
    rw [abs_neg]; exact hc.t12_lb n (e k)
  · intro n k
    have e1 : jbAlpha (chartGauge e c).A1 (chartGauge e c).B1 (chartGauge e c).t11 (chartGauge e c).t12 h n k = jbAlpha c.A1 c.B1 c.t11 c.t12 h n (e k) := by
      simp only [jbAlpha, chartGauge, Matrix.of_apply]
      rw [mul_neg, neg_div_neg_eq]
    rw [e1]; exact hc.α_lb n (e k)
  · have e1 : (Matrix.of fun n k => 1 / jbAlpha (chartGauge e c).A1 (chartGauge e c).B1 (chartGauge e c).t11 (chartGauge e c).t12 h n k) =
        (Matrix.of fun n k => 1 / jbAlpha c.A1 c.B1 c.t11 c.t12 h n k).submatrix id e := by
      ext n k
      simp only [jbAlpha, chartGauge, Matrix.of_apply, Matrix.submatrix_apply, id]
      rw [mul_neg, neg_div_neg_eq]
    rw [e1]; exact isSchurBdd_submatrix hc.schur_inv_α e
  · have e1 : (Matrix.of fun n k => (chartGauge e c).B1 n k / ((chartGauge e c).t12 n k * jbAlpha (chartGauge e c).A1 (chartGauge e c).B1 (chartGauge e c).t11 (chartGauge e c).t12 h n k)) =
        Matrix.of fun n k => -((Matrix.of fun n k => c.B1 n k / (c.t12 n k * jbAlpha c.A1 c.B1 c.t11 c.t12 h n k)).submatrix id e) n k := by
      ext n k
      simp only [jbAlpha, chartGauge, Matrix.of_apply, Matrix.submatrix_apply, id]
      rw [mul_neg, neg_div_neg_eq, neg_mul, div_neg]
    rw [e1]; exact isSchurBdd_neg' (isSchurBdd_submatrix hc.schur_B e)
  · have e1 : (Matrix.of fun n k => 1 / (chartGauge e c).t12 n k) =
        Matrix.of fun n k => -((Matrix.of fun n k => 1 / c.t12 n k).submatrix id e) n k := by
      ext n k
      simp only [chartGauge, Matrix.of_apply, Matrix.submatrix_apply, id]
      rw [one_div_neg_eq_neg_one_div]
    rw [e1]; exact isSchurBdd_neg' (isSchurBdd_submatrix hc.schur_inv_t12 e)
  · have e1 : (Matrix.of fun n k => (chartGauge e c).t11 n k / (chartGauge e c).t12 n k) =
        (Matrix.of fun n k => c.t11 n k / c.t12 n k).submatrix id e := by
      ext n k
      simp only [chartGauge, Matrix.of_apply, Matrix.submatrix_apply, id]
      rw [neg_div_neg_eq]
    rw [e1]; exact isSchurBdd_submatrix hc.schur_t11 e
  · exact isSchurBdd_submatrix hc.schur_κ e
  · intro n h1 h2
    have h3 := hc.ext_row n h1 h2
    refine le_of_eq_of_le ?_ h3
    unfold jbL2; congr 1
    rw [← Equiv.sum_comp e (fun k' => (c.ω n * c.σ1 k' * c.yext k') ^ 2)]
    refine Finset.sum_congr rfl fun k _ => ?_
    show (c.ω n * c.σ1 (e k) * (-(gsg (gaugeExtRow c)) * c.yext (e k))) ^ 2 = (c.ω n * c.σ1 (e k) * c.yext (e k)) ^ 2
    linear_combination (c.ω n * c.σ1 (e k) * c.yext (e k)) ^ 2 * gsg_sq (gaugeExtRow c)
  · intro k
    refine le_of_le_of_eq (hc.overlap_lb (e k)) ?_
    unfold jbL2; congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    show (Um' (c.row n) (e k)) ^ 2 = (Um (c.row n) k) ^ 2
    rw [hev k, hU]
    linear_combination (Um (c.row n) k) ^ 2 * gsg_sq _
  · intro k
    have h1 := hc.overlap_ub (e k)
    have hs : ∀ n : Fin R, gsg (c.lo + n.val) * gsg (c.lo + n.val) = 1 := fun n => gsg_sq _
    have ey : (fun n => (chartGauge e c).y n k) = fun n => gsg (c.lo + n.val) * c.y n (e k) := rfl
    have eyt : (fun n => (chartGauge e c).yt n k) = fun n => gsg (c.lo + n.val) * c.yt n (e k) := rfl
    have ep : (fun n => (chartGauge e c).phi1 h n k) = fun n => gsg (c.lo + n.val) * c.phi1 h n (e k) := by
      funext n
      simp only [Chart.phi1_apply, chartGauge, Matrix.of_apply]
      ring
    show jbL2 (c.P (e k)) (fun n => (chartGauge e c).y n k) + jbL2 (c.P (e k)) (fun n => (chartGauge e c).yt n k) ≤
      cs.C4 * jbL2 (c.P (e k)) (fun n => (chartGauge e c).phi1 h n k)
    rw [ey, eyt, ep, jbL2_gsg _ _ _ hs, jbL2_gsg _ _ _ hs, jbL2_gsg _ _ _ hs]
    exact h1

/-- The relabelling of the columns `k |-> rev k` between `cols` and `cols'` when `k in cols <-> rev k in cols'`. -/
def revEquiv (cols cols' : Finset (Fin (N + 1))) (h : ∀ k, k ∈ cols ↔ Fin.rev k ∈ cols') : cols ≃ cols' where
  toFun k := ⟨Fin.rev k, (h k).mp k.2⟩
  invFun k := ⟨Fin.rev k, (h (Fin.rev k)).mpr (by simpa using k.2)⟩
  left_inv k := by apply Subtype.ext; simp
  right_inv k := by apply Subtype.ext; simp

/-- **The gauge transport of a `ThbBlock`**: from a block for `(U', G0', G1')` on the columns `cols'` with `U' (rev k) = D U k`, `G' (rev k) = D G k` (`D = diag((-1)^i)`, `cols' = rev cols`) to a block for `(U, G0, G1)` on `cols`, with the same constants. -/
def ThbBlock.gauge {cs : OneStepConsts} {m : ℕ} {h : ℝ} {Um G0 G1 Um' G0' G1' : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    {Cε cε : ℝ} (hcols : ∀ k, k ∈ cols ↔ Fin.rev k ∈ cols')
    (hU : ∀ i k, Um' i (Fin.rev k) = gsg i.val * Um i k) (hG0 : ∀ i k, G0' i (Fin.rev k) = gsg i.val * G0 i k)
    (hG1 : ∀ i k, G1' i (Fin.rev k) = gsg i.val * G1 i k)
    (B : ThbBlock cs N m h Um' G0' G1' cols' Cε cε) : ThbBlock cs N m h Um G0 G1 cols Cε cε :=
  let e := revEquiv cols cols' hcols
  have hev : ∀ k : cols, ((e k : cols') : Fin (N + 1)) = Fin.rev (k : Fin (N + 1)) := fun k => rfl
  { RL := B.RL
    RR := B.RR
    chL := chartGauge e B.chL
    chR := chartGauge e B.chR
    okL := chartOk_gauge e hev hU B.okL
    okR := chartOk_gauge e hev hU B.okR
    match0L := fun n hn k => by
      have h1 := B.match0L n hn (e k)
      rw [chartGauge_H0, ← h1]
      show G0 (B.chL.row n) k = gsg (B.chL.lo + n.val) * G0' (B.chL.row n) (Fin.rev k)
      rw [hG0]
      have : ((B.chL.row n : Fin (N + 1)) : ℕ) = B.chL.lo + n.val := rfl
      rw [← mul_assoc, ← this, gsg_sq, one_mul]
    match0R := fun n hn k => by
      have h1 := B.match0R n hn (e k)
      rw [chartGauge_H0, ← h1]
      show G0 (B.chR.row n) k = gsg (B.chR.lo + n.val) * G0' (B.chR.row n) (Fin.rev k)
      rw [hG0]
      have : ((B.chR.row n : Fin (N + 1)) : ℕ) = B.chR.lo + n.val := rfl
      rw [← mul_assoc, ← this, gsg_sq, one_mul]
    match1L := fun n hn k => by
      have h1 := B.match1L n hn (e k)
      rw [chartGauge_H1, ← h1]
      show G1 (B.chL.row n) k = gsg (B.chL.lo + n.val) * G1' (B.chL.row n) (Fin.rev k)
      rw [hG1]
      have : ((B.chL.row n : Fin (N + 1)) : ℕ) = B.chL.lo + n.val := rfl
      rw [← mul_assoc, ← this, gsg_sq, one_mul]
    match1R := fun n hn k => by
      have h1 := B.match1R n hn (e k)
      rw [chartGauge_H1, ← h1]
      show G1 (B.chR.row n) k = gsg (B.chR.lo + n.val) * G1' (B.chR.row n) (Fin.rev k)
      rw [hG1]
      have : ((B.chR.row n : Fin (N + 1)) : ℕ) = B.chR.lo + n.val := rfl
      rw [← mul_assoc, ← this, gsg_sq, one_mul]
    cover := fun k hk i hi1 hi2 => by
      obtain ⟨a, b, c⟩ := B.cover (Fin.rev k) ((hcols k).mp hk) i hi1 hi2
      have habs : |gsg i.val| = 1 := by unfold gsg; rw [abs_pow]; simp
      refine ⟨?_, ?_, ?_⟩
      · rw [hG0, abs_mul, habs, one_mul] at a; exact a
      · rw [hG1, abs_mul, habs, one_mul] at b; exact b
      · rw [hU, abs_mul, habs, one_mul] at c; exact c }

end Gauge

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.l2_submatrix_equiv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.l2_submatrix_equiv_le

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.isSchurBdd_submatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.isSchurBdd_submatrix

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.chartOk_gauge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.chartOk_gauge

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.ThbBlock.gauge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.ThbBlock.gauge

end FormalResearch.JacobiEigenvectors.TheoremB

end
