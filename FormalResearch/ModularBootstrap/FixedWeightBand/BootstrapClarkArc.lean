module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapClarkArcCore
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.ClarkDiscBoundsUniform

/-!
# Good-Circle Clark Quadrature at Every Fixed `(w, Q)`: the Arc Estimate for the Nodes `z_n(α)`

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Theorem `FT-L.FW` (`wone:ftlfw`), Step 4 at the constant
Hermite-Biehler pair `(P, Q) = (cos α, -sin α)` (`wone:genlower`(2)): the quadrature
`P_{N,R}(H) = Σ_{|t_n|<R} H(t_n)/w_n^*` over the nodes `t_n = z_n(α)` of `ψ_α`, `w_n^* = K(z_n, z_n)`, against
`I_R(H)` plus the covered arc and the uncovered wedge (`wone:ftlfwquad`), with the good circles of
`gt:1.0p` uniform for `α` in a compact set avoiding `sin α = 0`.

* `pNodesClark`: the finite node sum `Σ_{n=1}^{N} Re f_{k,ℓ}(z_n(α))/K(z_n(α), z_n(α))`, the Clark version of `pNodesW`.
* `quad_arc_boundClark`: `P_nodes ≤ I_line + μ Arc_cov + μ Arc_unc`, `μ = C/(30 √π)`, `C` the ratio bound on the circle.
* `quad_arc_boundClark_uniform`: for `|sin α| ≥ σ` the radii and `μ₀ = 320/(30 σ)` depend only on `σ`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap Crossing PoissonJensen TipFront
  ConcreteBootstrap FixedWeightTip FormalResearch.SignUncertainty

variable {prob : FixedWeightProblem} [Q : LemmaQData prob]

/-- Finite good-circle node sum for the Clark nodes `z_n(α)` (`n = 1..N`) with the weights `1/K(z_n, z_n)`,
`K(z, z) = Ai'(z)² - z Ai(z)²`. -/
noncomputable def pNodesClark (prob : FixedWeightProblem) (α c' R ℓ : ℝ) (g : ℝ → ℝ) (k N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    (shiftedFunW prob c' R ℓ g k (clarkNode α n : ℂ)).re /
      (airyAi' (clarkNode α n) ^ 2 - clarkNode α n * airyAi (clarkNode α n) ^ 2)

/-- **Quadrature + arc estimate at the Clark nodes** (`wone:ftlfwquad`): on any good circle `R` of
`ψ_α = N_α` with `CftCircleData` for the nodes `z_1(α) > ⋯ > z_N(α)` and ratio bounds
`‖M/N ∓ i‖ e ≤ C` on the half circles,
`P_nodes ≤ I_line + μ Arc_cov + μ Arc_unc` with `μ = C/(30 √π)` (`μ = 1` is the Airy case `C = 30 √π`). -/
theorem quad_arc_boundClark {α c' R T L' ℓ C : ℝ} {N : ℕ} (hα : Real.sin α ≠ 0)
    (hc' : Q.cQ ≤ c')
    (h_c12 : (3 * π) ^ (12 : ℕ) ≤ c')
    (hς_arc : Q.sigma c' * (3 * π * √R * c' ^ (-(1 / 12 : ℝ)) + 1) ≤ 1)
    (hR_10 : 10 ≤ R) (hR_ub : R + 1 ≤ Q.AC c' ^ 2)
    (hL'_nn : 0 ≤ L') (hℓ_nn : 0 ≤ ℓ) (hℓ_half : ℓ ≤ 1 / 2)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hYV : YVEnvBound (psiTilde prob c' g) c' R L')
    (hD : CftCircleData (airyNC (Real.cos α) (-Real.sin α)) (fun n => (clarkNode α n : ℂ))
      (Finset.Icc 1 N) R)
    (hRp : ∀ w : ℂ, ‖w‖ = R → 0 ≤ w.im →
      ‖airyMC (Real.cos α) (-Real.sin α) w / airyNC (Real.cos α) (-Real.sin α) w - I‖ * airyEnv w ≤ C)
    (hRm : ∀ w : ℂ, ‖w‖ = R → w.im ≤ 0 →
      ‖airyMC (Real.cos α) (-Real.sin α) w / airyNC (Real.cos α) (-Real.sin α) w + I‖ * airyEnv w ≤ C)
    {k : ℕ} (hk5 : 5 ≤ k) :
    pNodesClark prob α c' R ℓ g k N ≤
      (∫ x in (-R)..R, (shiftedFunW prob c' R ℓ g k (x : ℂ)).re) +
        C / (30 * √π) * virasoroArcCov c' R T L' ℓ g k +
        C / (30 * √π) * (Q.arcUncConst * c' ^ (-(3 / 8 : ℝ))) := by
  have hQ : -Real.sin α ≠ 0 := neg_ne_zero.mpr hα
  have hR_pos : 0 < R := by linarith
  have hsp : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hC : 0 ≤ C := by
    have h := hRp (R : ℂ) (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR_pos])
      (by simp)
    exact (mul_nonneg (norm_nonneg _) (airyEnv_pos _).le).trans h
  refine quad_arc_bound_core hc' h_c12 hς_arc hR_10 hR_ub hL'_nn hℓ_nn hℓ_half hg hYV hk5
    (P := pNodesClark prob α c' R ℓ g k N) (μ := C / (30 * √π)) (by positivity) ?_
  intro hf_diff B hB hBb
  have h := clark_defect_ball_split_K (Real.cos α) (-Real.sin α) hQ hD (by linarith : R < R + 1 / 3)
    hf_diff hRp hRm hB hBb
  set f := shiftedFunW prob c' R ℓ g k
  have h_sum_eq : (∑ n ∈ Finset.Icc 1 N, f (clarkNode α n : ℂ) /
      (deriv airyAiC (clarkNode α n : ℂ) ^ 2 - (clarkNode α n : ℂ) * airyAiC (clarkNode α n : ℂ) ^ 2)).re =
      pNodesClark prob α c' R ℓ g k N := by
    unfold pNodesClark
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have e : deriv airyAiC (clarkNode α n : ℂ) ^ 2 - (clarkNode α n : ℂ) * airyAiC (clarkNode α n : ℂ) ^ 2 =
        ((airyAi' (clarkNode α n) ^ 2 - clarkNode α n * airyAi (clarkNode α n) ^ 2 : ℝ) : ℂ) := by
      rw [deriv_airyAiC_ofReal, airyAiC_ofReal]; push_cast; ring
    rw [e, Complex.div_ofReal_re]
  have h_int_eq : (∫ x in (-R)..R, f (x : ℂ)).re = ∫ x in (-R)..R, (f (x : ℂ)).re := by
    have hf_cont_R : ContinuousOn (fun x : ℝ => f (x : ℂ)) (Icc (-R) R) := by
      refine hf_diff.continuousOn.comp continuous_ofReal.continuousOn fun x hx => ?_
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact (abs_le.mpr hx).trans_lt (by linarith)
    exact (Complex.reCLM.intervalIntegral_comp_comm (hf_cont_R.intervalIntegrable_of_Icc (by linarith))).symm
  have hre := (Complex.abs_re_le_norm _).trans h
  rw [Complex.sub_re, h_sum_eq, h_int_eq] at hre
  have hmu : C / (30 * √π) * (15 * √π * R) = C / 2 * R := by
    field_simp; ring
  rw [hmu]
  exact (abs_le.mp hre).2

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.quad_arc_boundClark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quad_arc_boundClark

/-- **The Clark arc estimate with constants uniform in `α`** (`wone:genlower`(2), uniformity for `|sin α| ≥ σ`): there are
`μ₀ > 0` and `k₀` depending only on `σ` such that for every `k ≥ k₀` there is a radius `R ∈ [k, k + 1]` (the same for all
`α`, `c'`) for which, for every `α` with `|sin α| ≥ σ` and `z_1(α) < R`, the nodes `z_1(α) > ⋯ > z_N(α)` in `‖z‖ ≤ R`
satisfy `n ≤ N ↔ z_n(α) > -R` and the estimate of `quad_arc_boundClark` holds with `C/(30 √π) = μ₀`. -/
theorem quad_arc_boundClark_uniform {σ : ℝ} (hσ : 0 < σ) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∃ k₀ : ℕ, 10 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∃ R : ℝ, (k : ℝ) ≤ R ∧ R ≤ k + 1 ∧
      ∀ α : ℝ, σ ≤ |Real.sin α| → clarkNode α 1 < R →
        ∃ N : ℕ, (∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -R < clarkNode α n)) ∧
          ∀ {c' T L' ℓ : ℝ}, Q.cQ ≤ c' → (3 * π) ^ (12 : ℕ) ≤ c' →
            Q.sigma c' * (3 * π * √R * c' ^ (-(1 / 12 : ℝ)) + 1) ≤ 1 → R + 1 ≤ Q.AC c' ^ 2 →
            0 ≤ L' → 0 ≤ ℓ → ℓ ≤ 1 / 2 →
            ∀ {g : ℝ → ℝ}, prob.IsWeaklyFeasible (c' / 12) T g →
            YVEnvBound (psiTilde prob c' g) c' R L' → ∀ {k' : ℕ}, 5 ≤ k' →
            pNodesClark prob α c' R ℓ g k' N ≤
              (∫ x in (-R)..R, (shiftedFunW prob c' R ℓ g k' (x : ℂ)).re) +
                μ₀ * virasoroArcCov c' R T L' ℓ g k' + μ₀ * (Q.arcUncConst * c' ^ (-(3 / 8 : ℝ))) := by
  obtain ⟨C₀, hC₀, k₀, hk₀, h⟩ := clark_good_circle_uniform hσ
  have hsp : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  refine ⟨C₀ / (30 * √π), by positivity, k₀, hk₀, fun k hk => ?_⟩
  obtain ⟨R, hR1, hR2, hR⟩ := h k hk
  have hk10 : (10 : ℝ) ≤ k := by exact_mod_cast hk₀.trans hk
  have hR_10 : 10 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  refine ⟨R, hR1, hR2, fun α hα hR1α => ?_⟩
  have hsin : Real.sin α ≠ 0 := fun h => by rw [h, abs_zero] at hα; linarith
  have hgood : ∀ u : ℂ, ‖u‖ = R → airyNC (Real.cos α) (-Real.sin α) u ≠ 0 := by
    intro u hu h0
    have h1 := (hR α hα u hu).1
    rw [h0, norm_zero] at h1
    have : 0 < σ ^ 2 / (256 * π) * √R * airyEnv u := by
      have := airyEnv_pos u
      have : 0 < √R := Real.sqrt_pos.mpr hR0
      positivity
    linarith
  obtain ⟨N, hN, hD⟩ := clark_circleData hsin hR0 hR1α hgood
  refine ⟨N, hN, ?_⟩
  intro c' T L' ℓ hc' h_c12 hς hR_ub hL' hℓ hℓ2 g hg hYV k' hk5
  exact quad_arc_boundClark hsin hc' h_c12 hς hR_10 hR_ub hL' hℓ hℓ2 hg hYV hD
    (fun w hw hi => (hR α hα w hw).2.1 hi) (fun w hw hi => (hR α hα w hw).2.2 hi) hk5

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.quad_arc_boundClark_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quad_arc_boundClark_uniform

end FormalResearch.ModularBootstrap.FixedWeightBand
