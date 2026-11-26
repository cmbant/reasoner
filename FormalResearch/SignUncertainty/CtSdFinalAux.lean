module

public import FormalResearch.SignUncertainty.CtSdQE
public import FormalResearch.SignUncertainty.CtCfuData

/-!
# Elementary estimates for the concrete assembly of `(ct:K-airy)` (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3.  **Proved.**
Linear lower bound for the chart, exponential-versus-polynomial decay in the parameter `lam = c^{-1/3}`,
monotonicity of the steepest-descent constant `sdC` in `|ψ|`, and the comparison `|β| ≲ |a|`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real

set_option linter.unusedSectionVars false

namespace FormalResearch.SignUncertainty.CtSd

/-- A lower derivative bound gives a linear lower bound for `T`. -/
lemma T_lower {s1' δ : ℝ} {T T1 : ℝ → ℝ} (hT : ∀ s ∈ Icc (0 : ℝ) s1', HasDerivAt T (T1 s) s)
    (hδ : ∀ s ∈ Icc (0 : ℝ) s1', δ ≤ T1 s) (hT0 : T 0 = 0) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) s1') :
    δ * s ≤ T s := by
  have hmono : MonotoneOn (fun x => T x - δ * x) (Icc 0 s1') := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 s1') ?_ ?_ ?_
    · exact fun x hx => ((hT x hx).continuousAt.sub (continuousAt_const.mul continuousAt_id)).continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ Icc 0 s1' := ⟨hx.1.le, hx.2.le⟩
      exact (((hT x hx').sub ((hasDerivAt_id x).const_mul δ)).differentiableAt).differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ Icc 0 s1' := ⟨hx.1.le, hx.2.le⟩
      have hd : HasDerivAt (fun x => T x - δ * x) (T1 x - δ * 1) x :=
        (hT x hx').sub ((hasDerivAt_id x).const_mul δ)
      rw [hd.deriv]
      have := hδ x hx'
      linarith
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) s1' := ⟨le_rfl, (hs.1.trans hs.2)⟩
  have := hmono h0 hs hs.1
  simp only [hT0, mul_zero, sub_zero] at this
  linarith

/-- `exp(-δ c) ≤ C lam⁶` when `c lam³ = 1`. -/
lemma exp_le_lam6 {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ {c lam : ℝ}, 0 < lam → c * lam ^ 3 = 1 →
    Real.exp (-(δ * c)) ≤ C * lam ^ 6 := by
  refine ⟨Nat.factorial 2 / δ ^ 2, by positivity, fun {c lam} hlam hlc => ?_⟩
  have hc : 0 < c := by
    have : 0 < lam ^ 3 := by positivity
    nlinarith
  have h1 := Real.pow_div_factorial_le_exp (δ * c) (by positivity) 2
  have h2 : Real.exp (-(δ * c)) = (Real.exp (δ * c))⁻¹ := Real.exp_neg _
  rw [h2]
  have h3 : (δ * c) ^ 2 / (Nat.factorial 2 : ℝ) ≤ Real.exp (δ * c) := h1
  have hpos : 0 < (δ * c) ^ 2 / (Nat.factorial 2 : ℝ) := by positivity
  calc (Real.exp (δ * c))⁻¹ ≤ ((δ * c) ^ 2 / (Nat.factorial 2 : ℝ))⁻¹ := inv_anti₀ hpos h3
    _ = Nat.factorial 2 / δ ^ 2 * lam ^ 6 := by
        have : lam ^ 6 = (lam ^ 3) ^ 2 := by ring
        have hl3 : lam ^ 3 = 1 / c := by field_simp; linarith
        rw [this, hl3]; field_simp

/-- Monotonicity of the steepest-descent constant in `‖ψ‖`. -/
lemma sdC_mono {CQ CE CB Cm CU Cend ρ0 q1 p1 p2 : ℝ} (hCQ : 0 ≤ CQ) (hCE : 0 ≤ CE) (hCB : 0 ≤ CB) (hCm : 0 ≤ Cm)
    (hCU : 0 ≤ CU) (hρ0 : 0 ≤ ρ0) (hq1 : 0 ≤ q1) (hp : 0 ≤ p1) (hp12 : p1 ≤ p2) :
    sdC CQ CE CB Cm CU Cend ρ0 q1 p1 ≤ sdC CQ CE CB Cm CU Cend ρ0 q1 p2 := by
  unfold sdC
  have hk := kap_pos
  have h2 : 0 ≤ p2 := hp.trans hp12
  have a1 : p1 * Cm * (CQ * (kap * CU + p1) + q1 + CQ * ρ0) ≤ p2 * Cm * (CQ * (kap * CU + p2) + q1 + CQ * ρ0) := by
    apply mul_le_mul (mul_le_mul hp12 le_rfl hCm h2) _ (by positivity) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hp12 hCQ]
  nlinarith [mul_le_mul_of_nonneg_left hp12 (mul_nonneg hCm hCQ)]

/-- `|β| ≲ |a|` and smallness of `a = AF β` near `0`. -/
lemma exists_AF_lower : ∃ δ : ℝ, 0 < δ ∧ ∀ β : ℝ, |β| < δ →
    |β| ≤ (4 / CtCfu.d0 ^ 2) * |CtCfu.AF β| := by
  have hc : ContinuousAt CtCfu.dF 0 := CtCfu.contDiffAt_dF.continuousAt
  have h0 : CtCfu.dF 0 = CtCfu.d0 := CtCfu.dF_zero
  have hd := CtCfu.d0_pos
  have hev : ∀ᶠ β in 𝓝 (0 : ℝ), CtCfu.d0 / 2 < CtCfu.dF β :=
    hc.eventually (lt_mem_nhds (by rw [h0]; linarith))
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, fun β hβ => ?_⟩
  have h1 := h (by simpa using hβ)
  have hAF : |CtCfu.AF β| = |β| * CtCfu.dF β ^ 2 := by
    unfold CtCfu.AF
    rw [show -β * CtCfu.dF β ^ 2 = -(β * CtCfu.dF β ^ 2) by ring, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg (CtCfu.dF β))]
  rw [hAF]
  have h2 : (CtCfu.d0 / 2) ^ 2 ≤ CtCfu.dF β ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) h1.le
  have : |β| ≤ 4 / CtCfu.d0 ^ 2 * (|β| * CtCfu.dF β ^ 2) := by
    have h3 : 1 ≤ 4 / CtCfu.d0 ^ 2 * CtCfu.dF β ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    nlinarith [abs_nonneg β]
  exact this

end FormalResearch.SignUncertainty.CtSd
