module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWLine
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.ArcBounds
public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapClarkArcCore

/-!
# Good-Circle Airy Quadrature at Every Fixed `(w, Q)` (`hP_le`, `hArc_cov`, `hArc_unc`)

Source: `CFT/common/two_edge_bootstrap.tex` (`teb:bootstrap`, hypotheses `hP_le`, `hArc_cov`, `hArc_unc`) and
`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Theorem `FT-L.FW` (`wone:ftlfw`), Step 3.

For the shifted test `f_{k,ℓ}(u) = Ψ̃(u + ℓ)(1 + u/R)^{k+1}` on a good circle `|u| = R`
(`CftCircleData` for the Airy zeros), the finite node sum is bounded by the real-line integral plus a covered
arc `Arc_cov` (from `YVEnvBound`, i.e. the band-feedback hypothesis) and an uncovered wedge
`Arc_unc ≤ C_unc c'^{-3/8}` (from the type-(II) envelope of `Lemma Q (2)`):

* `pNodesW`: the finite good-circle node sum;
* the pointwise bounds on the covered arc and on the uncovered wedge are in `BootstrapClarkArcCore`
  (`quad_arc_bound_core`, shared with the Clark nodes);
* `quad_arc_boundW`: `P_nodes ≤ I_line + Arc_cov + Arc_unc` (the Virasoro `virasoro_quad_arc_bound`); the
  weight-free covered-arc Gamma bound `virasoroArcCov_le` is reused.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap Crossing PoissonJensen TipFront
  ConcreteBootstrap FixedWeightTip

variable {prob : FixedWeightProblem} [Q : LemmaQData prob]

/-- Finite good-circle node sum `P_nodes` for `shiftedFunW`. -/
noncomputable def pNodesW (prob : FixedWeightProblem) (c' R ℓ : ℝ) (g : ℝ → ℝ) (k N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    (shiftedFunW prob c' R ℓ g k (airyZero n : ℂ)).re / airyAi' (airyZero n) ^ 2

/-- **Quadrature + Arc Estimate (`BootstrapCore.hP_le`, `hArc_cov`, `hArc_unc`)** from `YVEnvBound`
and Lemma Q(2): on any good circle `R` with `CftCircleData` and ratio bounds,
`P_nodes ≤ I_line + Arc_cov + Arc_unc` with `Arc_unc ≤ Q.arcUncConst * c' ^ (-(3 / 8 : ℝ))`. -/
theorem quad_arc_boundW {c' R T L' ℓ : ℝ} {N : ℕ}
    (hc' : Q.cQ ≤ c')
    (h_c12 : (3 * π) ^ (12 : ℕ) ≤ c')
    (hς_arc : Q.sigma c' * (3 * π * √R * c' ^ (-(1 / 12 : ℝ)) + 1) ≤ 1)
    (hR_10 : 10 ≤ R) (hR_ub : R + 1 ≤ Q.AC c' ^ 2)
    (hL'_nn : 0 ≤ L') (hℓ_nn : 0 ≤ ℓ) (hℓ_half : ℓ ≤ 1 / 2)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hYV : YVEnvBound (psiTilde prob c' g) c' R L')
    (hD : CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) R)
    (hRp : ∀ w : ℂ, ‖w‖ = R → 0 ≤ w.im →
      ‖(airyBiC w - I * airyAiC w) / airyAiC w‖ * airyEnv w ≤ 30 * √π)
    (hRm : ∀ w : ℂ, ‖w‖ = R → w.im ≤ 0 →
      ‖(airyBiC w + I * airyAiC w) / airyAiC w‖ * airyEnv w ≤ 30 * √π)
    {k : ℕ} (hk5 : 5 ≤ k) :
    pNodesW prob c' R ℓ g k N ≤
      (∫ x in (-R)..R, (shiftedFunW prob c' R ℓ g k (x : ℂ)).re) +
        virasoroArcCov c' R T L' ℓ g k + Q.arcUncConst * c' ^ (-(3 / 8 : ℝ)) := by
  have hR_pos : 0 < R := by linarith
  have h := quad_arc_bound_core hc' h_c12 hς_arc hR_10 hR_ub hL'_nn hℓ_nn hℓ_half hg hYV hk5
    (P := pNodesW prob c' R ℓ g k N) (μ := 1) zero_le_one (fun hf_diff B hB hBb => by
      have h_def := airy_defect_ball_split hD (by linarith : R < R + 1 / 3) hf_diff hRp hRm hB hBb
      set f := shiftedFunW prob c' R ℓ g k
      have h_sum_eq : (∑ n ∈ Finset.Icc 1 N,
          (f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2)).re =
          pNodesW prob c' R ℓ g k N := by
        unfold pNodesW
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [deriv_airyAiC_ofReal, ← Complex.ofReal_pow, Complex.div_ofReal_re]
      have h_int_eq : (∫ x in (-R)..R, f (x : ℂ)).re = ∫ x in (-R)..R, (f (x : ℂ)).re := by
        have hf_cont_R : ContinuousOn (fun x : ℝ => f (x : ℂ)) (Icc (-R) R) := by
          refine hf_diff.continuousOn.comp continuous_ofReal.continuousOn fun x hx => ?_
          rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
          exact (abs_le.mpr hx).trans_lt (by linarith)
        exact (Complex.reCLM.intervalIntegral_comp_comm
          (hf_cont_R.intervalIntegrable_of_Icc (by linarith))).symm
      have hre := (Complex.abs_re_le_norm _).trans h_def
      rw [Complex.sub_re, h_sum_eq, h_int_eq] at hre
      rw [one_mul]
      exact (abs_le.mp hre).2)
  simpa only [one_mul] using h

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.quad_arc_boundW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quad_arc_boundW

end FormalResearch.ModularBootstrap.FixedWeightBand
