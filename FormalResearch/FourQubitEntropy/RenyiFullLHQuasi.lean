module

public import FormalResearch.FourQubitEntropy.RenyiFullLHChain

/-!
# Quasi-convexity of the fourth-derivative numerator `J` in `y`

Paper E, `lem:fqe-large-head-curvature`: on `0 ≤ x ≤ 3/5` the quartic `J(y)` has `J'(x) ≤ 0` and
`J''' = 144 q² (q y - x) ≥ 0` on `[x, 1]`, so `J'` is convex there and starts nonpositive: `J` first
decreases and then increases, and its maximum over a subinterval of `[x, 1]` is at an endpoint.
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.RenyiFull

open Set

noncomputable def lhdJ (q x y : ℝ) : ℝ :=
  24 * q ^ 3 * y ^ 3 - 72 * q ^ 2 * x * y ^ 2 + 2 * (-8 * q ^ 3 + 36 * q * x ^ 2 + 8 * q) * y
    + (24 * q ^ 2 * x - 24 * x ^ 3 - 24 * x)

theorem hasDerivAt_lhJ (q x y : ℝ) : HasDerivAt (fun y => lhJ q x y) (lhdJ q x y) y := by
  have h : HasDerivAt (fun y => lhJ q x y) (deriv (fun y => lhJ q x y) y) y :=
    (by unfold lhJ; fun_prop : DifferentiableAt ℝ (fun y => lhJ q x y) y).hasDerivAt
  refine h.congr_deriv ?_
  unfold lhJ lhdJ
  simp (disch := fun_prop)
  ring

/-- The convexity (third divided difference) identity of the cubic `J'`. -/
theorem lhdJ_convex_identity (q x s t : ℝ) :
    (t - s) * lhdJ q x x + (s - x) * lhdJ q x t - (t - x) * lhdJ q x s =
      (s - x) * (t - s) * (t - x) * (24 * q ^ 2 * (q * (x + s + t) - 3 * x)) := by
  unfold lhdJ
  ring

/-- **Quasi-convexity of `J(·)` on `[x,1]`.** -/
theorem lhJ_quasi {q x y1 y y2 : ℝ} (hq : 1 < q) (hx0 : 0 ≤ x) (hd : lhdJ q x x ≤ 0)
    (h1 : x ≤ y1) (h12 : y1 ≤ y) (h2 : y ≤ y2) :
    lhJ q x y ≤ max (lhJ q x y1) (lhJ q x y2) := by
  by_contra hcon
  push Not at hcon
  have ha : lhJ q x y1 < lhJ q x y := lt_of_le_of_lt (le_max_left _ _) hcon
  have hb : lhJ q x y2 < lhJ q x y := lt_of_le_of_lt (le_max_right _ _) hcon
  have hy1 : y1 < y := lt_of_le_of_ne h12 (fun h => by rw [h] at ha; exact lt_irrefl _ ha)
  have hy2 : y < y2 := lt_of_le_of_ne h2 (fun h => by rw [← h] at hb; exact lt_irrefl _ hb)
  have hcont : ∀ a b : ℝ, ContinuousOn (fun y => lhJ q x y) (Icc a b) := fun a b z _ =>
    (hasDerivAt_lhJ q x z).continuousAt.continuousWithinAt
  obtain ⟨ξ1, hξ1, he1⟩ := exists_hasDerivAt_eq_slope (fun y => lhJ q x y) (fun y => lhdJ q x y) hy1
    (hcont _ _) (fun z _ => hasDerivAt_lhJ q x z)
  obtain ⟨ξ2, hξ2, he2⟩ := exists_hasDerivAt_eq_slope (fun y => lhJ q x y) (fun y => lhdJ q x y) hy2
    (hcont _ _) (fun z _ => hasDerivAt_lhJ q x z)
  have p1 : 0 < lhdJ q x ξ1 := by
    rw [he1]; exact div_pos (by linarith) (by linarith)
  have p2 : lhdJ q x ξ2 < 0 := by
    rw [he2]; exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hxξ1 : x < ξ1 := by linarith [hξ1.1]
  have hξ12 : ξ1 < ξ2 := by linarith [hξ1.2, hξ2.1]
  have hid := lhdJ_convex_identity q x ξ1 ξ2
  have hpos : 0 ≤ (ξ1 - x) * (ξ2 - ξ1) * (ξ2 - x) * (24 * q ^ 2 * (q * (x + ξ1 + ξ2) - 3 * x)) := by
    have : 0 ≤ q * (x + ξ1 + ξ2) - 3 * x := by nlinarith
    have : 0 ≤ 24 * q ^ 2 * (q * (x + ξ1 + ξ2) - 3 * x) := by positivity
    have h3 : 0 < ξ1 - x := by linarith
    have h4 : 0 < ξ2 - ξ1 := by linarith
    have h5 : 0 < ξ2 - x := by linarith
    positivity
  have hA : (ξ2 - ξ1) * lhdJ q x x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hd
  have hB : (ξ1 - x) * lhdJ q x ξ2 < 0 := mul_neg_of_pos_of_neg (by linarith) p2
  have hC : 0 < (ξ2 - x) * lhdJ q x ξ1 := mul_pos (by linarith) p1
  nlinarith

/-- The homogenisation of `J` (degree 4 in `(N, D)`). -/
noncomputable def lhJH (q x N D : ℝ) : ℝ :=
  6 * q ^ 3 * N ^ 4 - 24 * q ^ 2 * x * N ^ 3 * D + (-8 * q ^ 3 + 36 * q * x ^ 2 + 8 * q) * N ^ 2 * D ^ 2
    + (24 * q ^ 2 * x - 24 * x ^ 3 - 24 * x) * N * D ^ 3
    + (2 * q ^ 3 - 36 * q * x ^ 2 - 8 * q + 6 * x ^ 4 + 36 * x ^ 2 + 6) * D ^ 4

theorem lhJ_hom (q x N D : ℝ) (hD : D ≠ 0) : lhJ q x (N / D) * D ^ 4 = lhJH q x N D := by
  unfold lhJ lhJH
  field_simp
  ring

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.lhJ_quasi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lhJ_quasi

end FormalResearch.FourQubitEntropy.RenyiFull
