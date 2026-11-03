module

public import FormalResearch.FourQubitEntropy.RenyiFullBQG
public import FormalResearch.FourQubitEntropy.RenyiFullBQCells

/-!
# Binary quartic lemma at `q_s`: `M(x(s), s) < 0` and `G'' > 0`

Combines the Riccati comparison `x ≤ U`, the monotonicity `∂M/∂ξ ≥ 0` (BQ-4) and the sign of
`M(U(s), s)` (BQ-3): `M(x,s) ≤ M(U,s) < 0` on `0 < s < 1`.
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.RenyiFull

/-- BQ-3: `(15Q)⁴ M(P/Q, s) = (q-1) s⁵ (1-s²)² K(q_s, s)` at `q = 1587/1000`. -/
theorem bqM_U_identity {s : ℝ} (hs : |s| < 1) :
    bqQn (1587 / 1000) s ^ 4 * bqM (1587 / 1000) s (bqU (1587 / 1000) s) =
      (1587 / 1000 - 1) * s ^ 5 * (1 - s ^ 2) ^ 2 * bqK s := by
  have hQ := (bqQn_pos (q := 1587 / 1000) (by norm_num) (by norm_num) hs).ne'
  unfold bqU bqM
  field_simp
  unfold bqPn bqQn bqK
  ring

theorem bqM_U_neg {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    bqM (1587 / 1000) s (bqU (1587 / 1000) s) < 0 := by
  have hs : |s| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hQ := bqQn_pos (q := 1587 / 1000) (by norm_num) (by norm_num) hs
  have hK := bqK_neg hs0.le hs1.le
  have e := bqM_U_identity hs
  have h2 : 0 < 1 - s ^ 2 := by nlinarith
  have : (1587 / 1000 - 1) * s ^ 5 * (1 - s ^ 2) ^ 2 * bqK s < 0 := by
    have : 0 < (1587 / 1000 - 1) * s ^ 5 * (1 - s ^ 2) ^ 2 := by positivity
    exact mul_neg_of_pos_of_neg this hK
  rw [← e] at this
  have h4 : 0 < bqQn (1587 / 1000) s ^ 4 := by positivity
  by_contra hcon
  push Not at hcon
  have := mul_nonneg h4.le hcon
  linarith

/-- `∂_ξ M(ξ, s)` at `q = q_s`. -/
theorem hasDerivAt_bqM_xi (s xi : ℝ) :
    HasDerivAt (fun xi => bqM (1587 / 1000) s xi) (bqdM s xi) xi := by
  have h : HasDerivAt (fun xi => bqM (1587 / 1000) s xi) (deriv (fun xi => bqM (1587 / 1000) s xi) xi) xi :=
    (by unfold bqM; fun_prop : DifferentiableAt ℝ (fun xi => bqM (1587 / 1000) s xi) xi).hasDerivAt
  refine h.congr_deriv ?_
  unfold bqM bqdM
  simp (disch := fun_prop)
  ring

/-- BQ-4 consequence: `ξ ↦ M(ξ, s)` is monotone on `[s, 1]`. -/
theorem bqM_mono {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    MonotoneOn (fun xi => bqM (1587 / 1000) s xi) (Set.Icc s 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s 1) (f' := fun xi => bqdM s xi)
  · intro xi _
    exact (hasDerivAt_bqM_xi s xi).continuousAt.continuousWithinAt
  · intro xi hxi
    exact (hasDerivAt_bqM_xi s xi).hasDerivWithinAt
  · intro xi hxi
    rw [interior_Icc] at hxi
    exact bqdM_nonneg hs0 hs1 hxi.1.le hxi.2.le

theorem bqM_x_neg {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    bqM (1587 / 1000) s (bqx (1587 / 1000) s) < 0 := by
  have h1 : (1 : ℝ) < 1587 / 1000 := by norm_num
  have h2 : (1587 / 1000 : ℝ) < 2 := by norm_num
  have hxs := bqx_gt h1 hs0 hs1
  have hxU := bqx_le_bqU h1 h2 hs0.le hs1
  have hU1 := bqU_lt_one h1 h2 hs0.le hs1
  have := bqM_mono hs0.le hs1 (Set.mem_Icc.2 ⟨hxs.le, hxU.trans hU1.le⟩)
    (Set.mem_Icc.2 ⟨hxs.le.trans hxU, hU1.le⟩) hxU
  exact lt_of_le_of_lt this (bqM_U_neg hs0 hs1)

theorem bqG2_pos {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : 0 < bqG2 (1587 / 1000) s := by
  unfold bqG2
  have h := bqM_x_neg hs0 hs1
  have h2 : 0 < 1 - s ^ 2 := by nlinarith
  have : 0 < 2 * s ^ 5 * (1 - s ^ 2) ^ 4 := by positivity
  apply div_pos _ this
  have : 0 < (1587 / 1000 : ℝ) := by norm_num
  nlinarith

end FormalResearch.FourQubitEntropy.RenyiFull
