module

public import FormalResearch.ModularBootstrap.Upper.Ramped.CombBridge
public import FormalResearch.ModularBootstrap.Upper.Window.TailGeometry

/-!
# The tip-normalised Cardy/comb weight `M_wt` (`rem:cardy`, `rem:thmU` Step (5))

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`) Step (5), and `Mwt` of Proposition 1.3.  With
`K_s(x) = 𝒦_*(x) + log(2√2/π)` (`kS`, `𝒦_*(x) = langerK x ξ_*`) and
`m(x) = √x (1 - e^{-4πx})² sech²(πx/2) e^{-(3/2)K_s(x)}`,
`M_wt(x) = m(x) / (m(ξ_*) τ'(x))`.

* `kS_xiStar`: `K_s(ξ_*) = 0` (`tanh(πξ_*) = 2^{-1/2}`, `τ'(ξ_*) = 1`), hence `mwt_xiStar : M_wt(ξ_*) = 1`;
* `contDiffOn_mwt`: `M_wt` is `C¹` on `(0, ∞)`;
* `mwt_sub_one_le`: `|M_wt(x) - 1| ≤ C |x - ξ_*|` on `[ξ_*/2, ξ_* + 1/2]`;
* `abs_sub_xiStar_le_tau`: `c |x - ξ_*| ≤ |τ(x)|` on `[ξ_*/2, ∞)`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Design Upper.Window

lemma langerT_neg (w : ℝ) : langerT (-w) = langerT w := by
  by_cases hw : w = 0
  · simp [hw]
  · rw [langerT_of_ne hw, langerT_of_ne (neg_ne_zero.2 hw)]
    have : Real.tanh (π * -w / 2) = -Real.tanh (π * w / 2) := by
      rw [← Real.tanh_neg]; ring_nf
    rw [this, neg_div_neg_eq]

lemma langerK_comm (x y : ℝ) : langerK x y = langerK y x := by
  unfold langerK langerQ2
  rw [langerD_comm x y, show x - y = -(y - x) by ring, langerT_neg, add_comm x y]

/-- `K_s(x) = 𝒦_*(x) + log(2√2/π)`. -/
noncomputable def kS (x : ℝ) : ℝ := langerK x xiStar + Real.log (2 * √2 / π)

lemma contDiffOn_langerK_xiStar : ContDiffOn ℝ 1 (fun z : ℝ => langerK z xiStar) (Ioi 0) := by
  have h := contDiffOn_langerK 1 (x := xiStar) xiStar_pos
  refine h.congr fun z _ => ?_
  exact langerK_comm z xiStar

lemma kS_xiStar : kS xiStar = 0 := by
  have hxs := xiStar_pos
  unfold kS langerK
  rw [langerQ2_diag, deriv_langerTau_xiStar]
  have e : π * (xiStar + xiStar) / 2 = π * xiStar := by ring
  rw [e, Upper.Window.Tail.tanh_pi_xiStar]
  have h2 : (0 : ℝ) < √2 := Real.sqrt_pos.2 (by norm_num)
  have hpi := Real.pi_pos
  rw [← Real.log_mul (by positivity) (by positivity), ← Real.log_mul (by positivity) (by positivity)]
  rw [show π / (2 * 1) * (1 / √2) * (2 * √2 / π) = 1 by field_simp]
  simp


/-- The numerator `m(x) = √x (1 - e^{-4πx})² sech²(πx/2) e^{-(3/2)K_s(x)}` of the weight. -/
noncomputable def mUnn (x : ℝ) : ℝ :=
  √x * (1 - Real.exp (-(4 * π * x))) ^ 2 * (1 / Real.cosh (π * x / 2) ^ 2) * Real.exp (-(3 / 2) * kS x)

lemma mUnn_pos {x : ℝ} (hx : 0 < x) : 0 < mUnn x := by
  unfold mUnn
  have h : 0 < 1 - Real.exp (-(4 * π * x)) := by
    have : Real.exp (-(4 * π * x)) < 1 := by
      rw [Real.exp_lt_one_iff]; have := Real.pi_pos; nlinarith
    linarith
  have := Real.sqrt_pos.2 hx
  positivity

lemma contDiffOn_mUnn : ContDiffOn ℝ 1 mUnn (Ioi 0) := by
  have hK : ContDiffOn ℝ 1 kS (Ioi 0) :=
    contDiffOn_langerK_xiStar.add contDiffOn_const
  have h1 : ContDiffOn ℝ 1 (fun x : ℝ => √x) (Ioi 0) := fun x hx =>
    (Real.contDiffAt_sqrt (ne_of_gt hx)).contDiffWithinAt
  have h2 : ContDiffOn ℝ 1 (fun x : ℝ => (1 - Real.exp (-(4 * π * x))) ^ 2) (Ioi 0) := by
    apply ContDiff.contDiffOn; fun_prop
  have h3 : ContDiffOn ℝ 1 (fun x : ℝ => 1 / Real.cosh (π * x / 2) ^ 2) (Ioi 0) := by
    apply ContDiff.contDiffOn
    refine contDiff_const.div (by fun_prop) fun x => ?_
    have := Real.cosh_pos (π * x / 2); positivity
  have h4 : ContDiffOn ℝ 1 (fun x : ℝ => Real.exp (-(3 / 2) * kS x)) (Ioi 0) :=
    Real.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul hK)
  exact ((h1.mul h2).mul h3).mul h4

/-- The tip-normalised weight `M_wt(x) = m(x) / (m(ξ_*) τ'(x))`. -/
noncomputable def mwt (x : ℝ) : ℝ := mUnn x / (mUnn xiStar * deriv langerTau x)

lemma mwt_xiStar : mwt xiStar = 1 := by
  unfold mwt
  rw [deriv_langerTau_xiStar, mul_one, div_self (mUnn_pos xiStar_pos).ne']

lemma contDiffOn_mwt : ContDiffOn ℝ 1 mwt (Ioi 0) := by
  unfold mwt
  refine contDiffOn_mUnn.div (contDiffOn_const.mul contDiffOn_deriv_langerTau) fun x hx => ?_
  exact (mul_pos (mUnn_pos xiStar_pos) (deriv_langerTau_pos hx)).ne'

lemma exists_lipschitzOn_mwt : ∃ K : NNReal, LipschitzOnWith K mwt (langerX (1 / 2)) := by
  have hsub : langerX (1 / 2) ⊆ Ioi 0 := fun x hx => by
    have := xiStar_pos; exact lt_of_lt_of_le (by linarith) hx.1
  exact (contDiffOn_mwt.mono hsub).exists_lipschitzOnWith one_ne_zero (convex_Icc _ _)
    isCompact_Icc

/-- `|M_wt(x) - 1| ≤ C |x - ξ_*|` on the window `[ξ_*/2, ξ_* + 1/2]`. -/
theorem mwt_sub_one_le : ∃ C : ℝ, 0 < C ∧ ∀ x ∈ langerX (1 / 2), |mwt x - 1| ≤ C * |x - xiStar| := by
  obtain ⟨K, hK⟩ := exists_lipschitzOn_mwt
  have hxs := xiStar_pos
  refine ⟨K + 1, by positivity, fun x hx => ?_⟩
  have hxi : xiStar ∈ langerX (1 / 2) := ⟨by linarith, by linarith⟩
  have h := hK.dist_le_mul x hx xiStar hxi
  rw [Real.dist_eq, Real.dist_eq, mwt_xiStar] at h
  have : (0 : ℝ) ≤ |x - xiStar| := abs_nonneg _
  nlinarith

/-- `c |x - ξ_*| ≤ |τ(x)|` on `[ξ_*/2, ∞)` (`τ' ≥ c_τ`, `τ(ξ_*) = 0`). -/
theorem abs_sub_xiStar_le_tau : ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, xiStar / 2 ≤ x → c * |x - xiStar| ≤ |langerTau x| := by
  have hxs := xiStar_pos
  obtain ⟨c, hc, hcd⟩ := langerTau_deriv_ge_const_of (a := xiStar / 2) (by linarith)
  refine ⟨c, hc, fun x hx => ?_⟩
  rcases le_total xiStar x with h | h
  · have := langerTau_sub_ge (a := xiStar / 2) (c := c) (by linarith) hcd (by linarith) h
    rw [langerTau_xiStar, sub_zero] at this
    rw [abs_of_nonneg (sub_nonneg.2 h), abs_of_nonneg (by nlinarith)]
    exact this
  · have := langerTau_sub_ge (a := xiStar / 2) (c := c) (by linarith) hcd hx h
    rw [langerTau_xiStar] at this
    rw [abs_of_nonpos (sub_nonpos.2 h), abs_of_nonpos (by nlinarith)]
    linarith

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.mwt_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mwt_sub_one_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.abs_sub_xiStar_le_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abs_sub_xiStar_le_tau

end FormalResearch.ModularBootstrap.Upper.Ramped
