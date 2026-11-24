module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapClarkArc
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.QuantC1Clark
public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityNodes

/-!
# Node-Sum Lower Bounds (`hP_nodes_lb_hb`, `P_theta_bound`) at the Clark Nodes

Source: `CFT/common/two_edge_bootstrap.tex` (`teb:bootstrap`(4), hypotheses `hP_nodes_lb_hb`, `P_theta_bound`) and
`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Theorem `FT-L.FW` (`wone:ftlfw`), Step 4, equations
`wone:ftlfwnodes`, `wone:ftlfwtnodes`, for the constant pair `(P, Q) = (cos α, -sin α)`, `m₀ = 2`
(`wone:genlower`(2)).

* `pnodes_lb_and_thetaClark`: for the good-circle node sum `P_nodes = pNodesClark` over the Clark nodes
  `z_n(α)` with weights `1/K_n`, `K_n = K(z_n, z_n)`, the lower bounds `hP_nodes_lb_hb` and `P_theta_bound` with the
  top-node constant `W_top ≥ 2/K_1` (`W_top = 2/K_1` in the paper) and `w_* ≤ K_2`. The nodes `n ≥ 3` carry
  `Ψ̃(z_n + ℓ) ≥ 0`, the prescribed node near `z_1` and the node `z_2` use the slope bound `C₁` of
  `QuantC1B2HoldsClark` and the `θ`-slope bound `quantC1ClarkB2_secant_lower`.

The sums use the weights `(1 + z_n/R)^{k+1}`. At the prescribed node `z_1 > 0` the factor exceeds `1`, but is at most
`exp(|z_1|/4)` for `k ≤ R/5`, `R ≥ 48`; this is absorbed into `P.C_1 ≥ C₁ exp(|z_1|/4)` (the paper's `Λ_N` is then
`2 P.C_1 (1/w_* + W_top)` with the enlarged `C_1`). Not formalised here: the choice of the good radius `R` and the
passage to `BootstrapHBInstance` (see `BootstrapClarkArc` for the quadrature estimate).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap Crossing PoissonJensen TipFront
  ConcreteBootstrap FixedWeightTip FormalResearch.SignUncertainty TwoLevel

variable {prob : FixedWeightProblem} [Q : LemmaQData prob]

/-- Mean value bound for the real part of an analytic function on a real segment inside its disc. -/
lemma re_sub_le_of_deriv_le {Ψ : ℂ → ℂ} {R_dom a b C₁ x y : ℝ}
    (hΨ : AnalyticOnNhd ℂ Ψ (closedBall (0 : ℂ) R_dom))
    (hdom : ∀ t ∈ Icc a b, |t| ≤ R_dom)
    (hder : ∀ t ∈ Icc a b, ‖deriv Ψ (t : ℂ)‖ ≤ C₁)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |(Ψ (y : ℂ)).re - (Ψ (x : ℂ)).re| ≤ C₁ * |y - x| := by
  have hd : ∀ t ∈ Icc a b,
      HasDerivAt (fun s : ℝ => (Ψ (s : ℂ)).re) ((deriv Ψ (t : ℂ)).re) t := by
    intro t ht
    have ht_ball : (t : ℂ) ∈ closedBall (0 : ℂ) R_dom := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact hdom t ht
    have hc : HasDerivAt Ψ (deriv Ψ (t : ℂ)) (t : ℂ) :=
      (hΨ (t : ℂ) ht_ball).differentiableAt.hasDerivAt
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hc.comp_ofReal
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ => (Ψ (s : ℂ)).re) (f' := fun t : ℝ => (deriv Ψ (t : ℂ)).re) (C := C₁)
    (fun t ht => (hd t ht).hasDerivWithinAt)
    (fun t ht => (Complex.abs_re_le_norm _).trans (hder t ht)) (convex_Icc a b) hx hy
  simpa only [Real.norm_eq_abs] using h

/-- A lower bound for `Re Ψ` at `y` from nonnegativity at a nearby point `ũ` and the derivative bound. -/
lemma re_lower_of_nonneg_near {Ψ : ℂ → ℂ} {R_dom z ũ y C₁ d : ℝ}
    (hΨ : AnalyticOnNhd ℂ Ψ (closedBall (0 : ℂ) R_dom))
    (hdom : ∀ t ∈ Icc (z - 1) (z + 1), |t| ≤ R_dom)
    (hder : ∀ t ∈ Icc (z - 1) (z + 1), ‖deriv Ψ (t : ℂ)‖ ≤ C₁)
    (hũ : ũ ∈ Icc (z - 1) (z + 1)) (hy : y ∈ Icc (z - 1) (z + 1)) (hd : |y - ũ| ≤ d)
    (hC₁ : 0 ≤ C₁) (hnn : 0 ≤ (Ψ (ũ : ℂ)).re) : -(C₁ * d) ≤ (Ψ (y : ℂ)).re := by
  have h := re_sub_le_of_deriv_le hΨ hdom hder hũ hy
  have h3 : C₁ * |y - ũ| ≤ C₁ * d := mul_le_mul_of_nonneg_left hd hC₁
  linarith [(abs_le.mp h).1]

/-- `u_T` lies above `z` when `T < Δ(z)`, below `A_{c'}²`, and `Δ(u_T) = T`. -/
private lemma uT_facts {c' T z : ℝ} (hc' : Q.cQ ≤ c')
    (hz_lo : -(Q.AC c' ^ 2) ≤ z) (hz_hi : z ≤ Q.AC c' ^ 2)
    (hT_A2 : virasoroDeltaChart c' (Q.AC c' ^ 2) ≤ T)
    (hT_z : T < virasoroDeltaChart c' z) :
    z < virasoroUT c' T ∧ virasoroUT c' T ≤ Q.AC c' ^ 2 ∧
      virasoroDeltaChart c' (virasoroUT c' T) = T := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have hu_mem := Q.UT_between hc'_pos hz_lo le_rfl hz_hi hT_A2 hT_z.le
  refine ⟨?_, hu_mem.1.2, hu_mem.2⟩
  by_contra hle
  have := (Q.deltaChart_strictAnti hc'_pos).antitoneOn
    ⟨hz_lo.trans hu_mem.1.1, hu_mem.1.2⟩ ⟨hz_lo, hz_hi⟩ (not_lt.mp hle)
  linarith [hu_mem.2]

omit Q in
private lemma shiftedFunW_re_real {c' R ℓ : ℝ} {g : ℝ → ℝ} {k : ℕ} (x : ℝ) :
    (shiftedFunW prob c' R ℓ g k (x : ℂ)).re =
      (1 + x / R) ^ (k + 1) * (psiTilde prob c' g ((x + ℓ : ℝ) : ℂ)).re := by
  unfold shiftedFunW
  have h1 : ((1 + (x : ℂ) / (R : ℂ)) ^ (k + 1)) = (((1 + x / R) ^ (k + 1) : ℝ) : ℂ) := by
    push_cast; ring
  rw [h1, show (x : ℂ) + (ℓ : ℂ) = ((x + ℓ : ℝ) : ℂ) by push_cast; ring,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- The nodes `z_n(α)`, `n ≥ 3`, lie below `z_3`. -/
private lemma clarkNode_le_three (α : ℝ) {n : ℕ} (hn : 3 ≤ n) : clarkNode α n ≤ clarkNode α 3 := by
  rcases hn.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (clarkNode_lt_of_lt (by norm_num) h α).le

/-- Two-node lower bound: the good-circle node sum dominates the contributions of `z₁` and `z₂`, because the
nodes `n ≥ 3` carry `Ψ̃(z_n + ℓ) ≥ 0` (`z_n + ℓ ≤ z₂ < u_T`). -/
private lemma pnodes_two_nodes_lowerClark {α c' R T ℓ : ℝ} {N : ℕ}
    (hc' : Q.cQ ≤ c') (hR_48 : 48 ≤ R) (hR_ub : R + 1 ≤ Q.AC c' ^ 2)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hT_A2 : virasoroDeltaChart c' (Q.AC c' ^ 2) ≤ T)
    (hT_z2 : T < virasoroDeltaChart c' (clarkNode α 2))
    (hN : ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -R < clarkNode α n))
    (hℓ_nn : 0 ≤ ℓ) (hℓ_gap : ℓ ≤ clarkNode α 2 - clarkNode α 3) (k : ℕ) :
    (1 + clarkNode α 1 / R) ^ (k + 1) *
        (psiTilde prob c' g ((clarkNode α 1 + ℓ : ℝ) : ℂ)).re / clarkKernel α 1 +
      (1 + clarkNode α 2 / R) ^ (k + 1) *
        (psiTilde prob c' g ((clarkNode α 2 + ℓ : ℝ) : ℂ)).re / clarkKernel α 2 ≤
      pNodesClark prob α c' R ℓ g k N := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have hR_pos : 0 < R := by linarith
  obtain ⟨ha1_lo, ha1_hi⟩ := airyZero_one
  obtain ⟨ha2_lo, ha2_hi⟩ := airyZero_two
  have hz21 : clarkNode α 2 < clarkNode α 1 := clarkNode_two_lt_one α
  have hz2_lo : airyZero 2 < clarkNode α 2 := airyZero_lt_airyClarkNode (n := 2) (by norm_num) _
  have hz1_gt : airyZero 1 < clarkNode α 1 := airyZero_lt_airyClarkNode (n := 1) le_rfl _
  have hz2_hi : clarkNode α 2 < airyZero 1 := airyClarkNode_lt_airyZero (n := 2) (by norm_num) _
  have hz2_neg : clarkNode α 2 < 0 := by linarith
  have hz2_R : -R < clarkNode α 2 := by linarith
  have hz1_R : -R < clarkNode α 1 := by linarith
  have hAC : (49 : ℝ) ≤ Q.AC c' ^ 2 := by linarith
  obtain ⟨huT_gt, huT_AC, huT_Δ⟩ := uT_facts (z := clarkNode α 2) hc' (by linarith) (by linarith)
    hT_A2 hT_z2
  have h1_mem : (1 : ℕ) ∈ Finset.Icc 1 N := by
    rw [Finset.mem_Icc]; exact ⟨le_rfl, (hN 1 le_rfl).mpr hz1_R⟩
  have h2_mem : (2 : ℕ) ∈ (Finset.Icc 1 N).erase 1 := by
    rw [Finset.mem_erase, Finset.mem_Icc]
    exact ⟨by norm_num, by norm_num, (hN 2 (by norm_num)).mpr hz2_R⟩
  have hsplit : pNodesClark prob α c' R ℓ g k N =
      (shiftedFunW prob c' R ℓ g k (clarkNode α 1 : ℂ)).re / clarkKernel α 1 +
      ((shiftedFunW prob c' R ℓ g k (clarkNode α 2 : ℂ)).re / clarkKernel α 2 +
      ∑ n ∈ ((Finset.Icc 1 N).erase 1).erase 2,
        (shiftedFunW prob c' R ℓ g k (clarkNode α n : ℂ)).re / clarkKernel α n) := by
    unfold pNodesClark
    rw [← Finset.add_sum_erase (Finset.Icc 1 N) _ h1_mem,
      ← Finset.add_sum_erase ((Finset.Icc 1 N).erase 1) _ h2_mem]
    rfl
  have htail : 0 ≤ ∑ n ∈ ((Finset.Icc 1 N).erase 1).erase 2,
      (shiftedFunW prob c' R ℓ g k (clarkNode α n : ℂ)).re / clarkKernel α n := by
    refine Finset.sum_nonneg fun n hn => ?_
    rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_Icc] at hn
    obtain ⟨hn2, hn1, hn1', hnN⟩ := hn
    have hn3 : 3 ≤ n := by omega
    have hnR : -R < clarkNode α n := (hN n hn1').mp hnN
    have hz3 := clarkNode_le_three α hn3
    have harg_le : clarkNode α n + ℓ ≤ virasoroUT c' T := by linarith
    have harg_abs : |clarkNode α n + ℓ| ≤ Q.AC c' ^ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hT_le_Δ : T ≤ virasoroDeltaChart c' (clarkNode α n + ℓ) := by
      rw [← huT_Δ]
      exact (Q.deltaChart_strictAnti hc'_pos).antitoneOn
        ⟨by linarith, by linarith⟩ ⟨by linarith, huT_AC⟩ harg_le
    have hΨ_nn : 0 ≤ (psiTilde prob c' g ((clarkNode α n + ℓ : ℝ) : ℂ)).re :=
      (Q.part3 hc' hg).1 (clarkNode α n + ℓ) harg_abs hT_le_Δ
    have hpow_nn : 0 ≤ (1 + clarkNode α n / R) ^ (k + 1) := by
      refine pow_nonneg ?_ _
      rw [show (1 : ℝ) + clarkNode α n / R = (R + clarkNode α n) / R by field_simp [hR_pos.ne'] ]
      exact div_nonneg (by linarith) hR_pos.le
    rw [shiftedFunW_re_real]
    exact div_nonneg (mul_nonneg hpow_nn hΨ_nn) (clarkKernel_pos α n).le
  rw [hsplit, shiftedFunW_re_real, shiftedFunW_re_real]
  linarith

/-- The factor `(1 + z/R)^{k+1}` at a node `z ≥ -R` is at most `exp (|z| / 4)` for `k ≤ R/5`, `R ≥ 48`. -/
private lemma pow_le_exp_quarter {z R : ℝ} {k : ℕ} (hR : 48 ≤ R) (hzR : -R ≤ z)
    (hk : (k : ℝ) ≤ R / 5) : (1 + z / R) ^ (k + 1) ≤ Real.exp (|z| / 4) := by
  have hR_pos : 0 < R := by linarith
  have hbase_nn : 0 ≤ 1 + z / R := by
    rw [show (1 : ℝ) + z / R = (R + z) / R by field_simp [hR_pos.ne'] ]
    exact div_nonneg (by linarith) hR_pos.le
  have h1 : 1 + z / R ≤ Real.exp (z / R) := by linarith [Real.add_one_le_exp (z / R)]
  have h2 : (1 + z / R) ^ (k + 1) ≤ Real.exp (z / R) ^ (k + 1) := pow_le_pow_left₀ hbase_nn h1 _
  rw [← Real.exp_nat_mul] at h2
  refine h2.trans (Real.exp_le_exp.mpr ?_)
  have hk1 : ((k + 1 : ℕ) : ℝ) ≤ R / 4 := by push_cast; linarith
  have hz_abs : z ≤ |z| := le_abs_self z
  have h3 : ((k + 1 : ℕ) : ℝ) * (z / R) ≤ ((k + 1 : ℕ) : ℝ) * (|z| / R) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hz_abs hR_pos.le) (by positivity)
  have h4 : ((k + 1 : ℕ) : ℝ) * (|z| / R) ≤ (R / 4) * (|z| / R) :=
    mul_le_mul_of_nonneg_right hk1 (by positivity)
  have h5 : (R / 4) * (|z| / R) = |z| / 4 := by field_simp
  linarith

/-- **Node-sum lower bounds at the Clark nodes** (`wone:ftlfwnodes`, `wone:ftlfwtnodes`; the hypotheses
`hP_nodes_lb_hb`, `P_theta_bound` of `BootstrapHBInstance P W_top` for the node sum `pNodesClark`, `r_∞ = 0`).

Setting: `Ψ̃ = psiTilde prob c' g` of a weakly feasible `g` with violator threshold `u_T = virasoroUT c' T`
(`T < Δ(z₂)`, `Δ(A_{c'}²) ≤ T`), `hB2 : QuantC1B2HoldsClark` for the Clark pair `cot α` with constants `(δ, κ, C₁)`,
and a prescribed point `ũ` with `|ũ - z₁| ≤ D₁ c'^{-1/3}`, `Ψ̃(ũ) ≥ 0`; `N` is the number of nodes in `|z| < R`.
The parameters satisfy `w_* ≤ K₂`, `κ_* K₂ ≤ κ w_*` (equalities in the paper), `η₀ ≤ z₂ - z₃`,
`C₁ exp(|z₁|/4) ≤ C_1` (the factor `(1 + z₁/R)^{k+1} ≤ exp(|z₁|/4)` of the prescribed node), `k₀ = 5`, and
`W_top ≥ 2/K₁` (`W_top = 2/K₁ = 2/w₁*` in the paper). Then, with `Λ_N = 2 C_1 (1/w_* + W_top)` and
`θ = min (1/2) (κ_*/(8 w_* C_1 (W_top + 1)))`,

* for `ℓ ∈ [D₁ c'^{-1/3}, min δ_* (min η₀ 1)]`, `k₀ ≤ k ≤ R/5`: `-Λ_N ℓ ≤ P_nodes(k, ℓ)`;
* `P_nodes(k₀, θ x̃) ≥ κ_*/(4 w_*) x̃`, `x̃ = u_T - z₂`, when `θ x̃` lies in that interval. -/
theorem pnodes_lb_and_thetaClark {α c' R T : ℝ} {N : ℕ} {δ κ C₁ : ℝ}
    (hc' : Q.cQ ≤ c') (hR_48 : 48 ≤ R) (hR_ub : R + 1 ≤ Q.AC c' ^ 2)
    (hz1_R : |clarkNode α 1| + 1 ≤ R)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hT_A2 : virasoroDeltaChart c' (Q.AC c' ^ 2) ≤ T)
    (hT_z2 : T < virasoroDeltaChart c' (clarkNode α 2))
    (hδ_pos : 0 < δ) (hδ_half : δ ≤ 1 / 2)
    (hB2 : QuantC1B2HoldsClark (Real.cos α / Real.sin α) δ κ C₁ (psiTilde prob c' g)
      (virasoroUT c' T))
    (hN : ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -R < clarkNode α n))
    (P : BootstrapParams) {W_top : ℝ} (hW : 2 / clarkKernel α 1 ≤ W_top)
    (hP_C1 : C₁ * Real.exp (|clarkNode α 1| / 4) ≤ P.C_1)
    (hP_w : P.w_star ≤ clarkKernel α 2) (hP_κ : P.κ_star * clarkKernel α 2 ≤ κ * P.w_star)
    (hP_η : P.η_0 ≤ clarkNode α 2 - clarkNode α 3)
    (hP_k0 : P.k_0 = 5)
    {ũ : ℝ} (hũ_near : |ũ - clarkNode α 1| ≤ P.D_1 * c' ^ (-(1 / 3 : ℝ)))
    (hũ_nn : 0 ≤ (psiTilde prob c' g (ũ : ℂ)).re) :
    (∀ k : ℕ, ∀ ℓ : ℝ, P.k_0 ≤ k → (k : ℝ) ≤ R / 5 →
      ℓ ∈ Icc (P.D_1 * c' ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
      -tebLambdaN P W_top * ℓ - P.C_α * R ^ (3 / 2 : ℝ) * 0 ≤ pNodesClark prob α c' R ℓ g k N) ∧
    ((P.k_0 : ℝ) ≤ R / 5 →
      tebThetaHB P W_top * (virasoroUT c' T - clarkNode α 2) ∈
        Icc (P.D_1 * c' ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
      (P.κ_star / (4 * P.w_star)) * (virasoroUT c' T - clarkNode α 2) -
        P.C_α * R ^ (3 / 2 : ℝ) * 0 ≤
        pNodesClark prob α c' R (tebThetaHB P W_top * (virasoroUT c' T - clarkNode α 2)) g P.k_0 N) := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have hR_pos : 0 < R := by linarith
  obtain ⟨ha1_lo, ha1_hi⟩ := airyZero_one
  obtain ⟨ha2_lo, ha2_hi⟩ := airyZero_two
  have hz21 : clarkNode α 2 < clarkNode α 1 := clarkNode_two_lt_one α
  have hz2_lo : airyZero 2 < clarkNode α 2 := airyZero_lt_airyClarkNode (n := 2) (by norm_num) _
  have hz1_gt : airyZero 1 < clarkNode α 1 := airyZero_lt_airyClarkNode (n := 1) le_rfl _
  have hz2_hi : clarkNode α 2 < airyZero 1 := airyClarkNode_lt_airyZero (n := 2) (by norm_num) _
  have hz2_neg : clarkNode α 2 < 0 := by linarith
  have hz1_R' : -R ≤ clarkNode α 1 := by linarith
  have hAC : (49 : ℝ) ≤ Q.AC c' ^ 2 := by linarith
  have hK1 := clarkKernel_pos α 1
  have hK2 := clarkKernel_pos α 2
  have hW_nn : 0 ≤ W_top := (div_nonneg two_pos.le hK1.le).trans hW
  have hder1 : ∀ x ∈ Icc (clarkNode α 1 - 1) (clarkNode α 1 + 1),
      ‖deriv (psiTilde prob c' g) (x : ℂ)‖ ≤ C₁ := hB2.deriv_le_one
  have hder2 : ∀ x ∈ Icc (clarkNode α 2 - 1) (clarkNode α 2 + 1),
      ‖deriv (psiTilde prob c' g) (x : ℂ)‖ ≤ C₁ := hB2.deriv_le_two
  have hC₁_nn : 0 ≤ C₁ :=
    (norm_nonneg _).trans (hder1 (clarkNode α 1) ⟨by linarith, by linarith⟩)
  have hE_one : 1 ≤ Real.exp (|clarkNode α 1| / 4) := Real.one_le_exp (by positivity)
  have hPC1_nn : 0 ≤ P.C_1 := P.hC1.le
  have hPC_ge : C₁ ≤ P.C_1 := (le_mul_of_one_le_right hC₁_nn hE_one).trans hP_C1
  have hw := P.hw_star
  have hκ_pos : 0 < κ :=
    (mul_pos_iff_of_pos_right hw).mp (lt_of_lt_of_le (mul_pos P.hκ_star hK2) hP_κ)
  have hΨ_an_R : AnalyticOnNhd ℂ (psiTilde prob c' g) (closedBall (0 : ℂ) (Q.AC c' ^ 2)) :=
    (Q.analytic (by linarith) hg.1).mono fun z hz => Q.closedBall_subset_psiDom hc'_pos hz
  obtain ⟨huT_gt, huT_AC, huT_Δ⟩ := uT_facts (z := clarkNode α 2) hc' (by linarith) (by linarith)
    hT_A2 hT_z2
  set u_T := virasoroUT c' T with hu_T
  have huT_nn : 0 ≤ (psiTilde prob c' g (u_T : ℂ)).re :=
    (Q.part3 hc' hg).1 u_T (abs_le.mpr ⟨by linarith, huT_AC⟩) huT_Δ.ge
  have hx_le : u_T - clarkNode α 2 ≤ min δ 1 := hB2.xtilde_le
  have hdom1 : ∀ t ∈ Icc (clarkNode α 1 - 1) (clarkNode α 1 + 1), |t| ≤ Q.AC c' ^ 2 := by
    intro t ht
    have h1 := le_abs_self (clarkNode α 1)
    have h2 := neg_abs_le (clarkNode α 1)
    exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hdom2 : ∀ t ∈ Icc (clarkNode α 2 - 1) (clarkNode α 2 + 1), |t| ≤ Q.AC c' ^ 2 := by
    intro t ht
    exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hz2_nn : 0 ≤ (psiTilde prob c' g (clarkNode α 2 : ℂ)).re :=
    (Q.part3 hc' hg).1 (clarkNode α 2) (abs_le.mpr ⟨by linarith, by linarith⟩) hT_z2.le
  -- node 1: the prescribed point
  have hnode1 : ∀ ℓ : ℝ, P.D_1 * c' ^ (-(1 / 3 : ℝ)) ≤ ℓ → ℓ ≤ 1 →
      -(C₁ * (2 * ℓ)) ≤ (psiTilde prob c' g ((clarkNode α 1 + ℓ : ℝ) : ℂ)).re := by
    intro ℓ hℓ_lo hℓ_1
    have hℓ_nn : 0 ≤ ℓ := (mul_nonneg P.hD1 (Real.rpow_nonneg hc'_pos.le _)).trans hℓ_lo
    have hu_near : |ũ - clarkNode α 1| ≤ ℓ := hũ_near.trans hℓ_lo
    refine re_lower_of_nonneg_near hΨ_an_R hdom1 hder1
      ⟨by linarith [(abs_le.mp hu_near).1], by linarith [(abs_le.mp hu_near).2]⟩
      ⟨by linarith, by linarith⟩ ?_ hC₁_nn hũ_nn
    rw [abs_le]
    constructor <;> linarith [(abs_le.mp hu_near).1, (abs_le.mp hu_near).2]
  -- node 2
  have hnode2 : ∀ ℓ : ℝ, 0 ≤ ℓ → ℓ ≤ 1 →
      -(C₁ * ℓ) ≤ (psiTilde prob c' g ((clarkNode α 2 + ℓ : ℝ) : ℂ)).re := by
    intro ℓ hℓ_nn hℓ_1
    refine re_lower_of_nonneg_near hΨ_an_R hdom2 hder2 ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ ?_ hC₁_nn hz2_nn
    rw [add_sub_cancel_left, abs_of_nonneg hℓ_nn]
  have hbase2_nn : 0 ≤ 1 + clarkNode α 2 / R := by
    rw [show (1 : ℝ) + clarkNode α 2 / R = (R + clarkNode α 2) / R by field_simp [hR_pos.ne'] ]
    exact div_nonneg (by linarith) hR_pos.le
  have hbase2_le1 : 1 + clarkNode α 2 / R ≤ 1 := by
    have : clarkNode α 2 / R ≤ 0 := div_nonpos_of_nonpos_of_nonneg hz2_neg.le hR_pos.le
    linarith
  have hbase1_nn : 0 ≤ 1 + clarkNode α 1 / R := by
    rw [show (1 : ℝ) + clarkNode α 1 / R = (R + clarkNode α 1) / R by field_simp [hR_pos.ne'] ]
    exact div_nonneg (by linarith) hR_pos.le
  have hinv1 : 1 / clarkKernel α 1 ≤ W_top / 2 := by
    have : 2 / clarkKernel α 1 = 2 * (1 / clarkKernel α 1) := by ring
    linarith
  -- the prescribed-node loss, for a shift `s ≥ 0`
  have hloss1 : ∀ s : ℝ, 0 ≤ s → 2 * C₁ * Real.exp (|clarkNode α 1| / 4) * s / clarkKernel α 1 ≤
      2 * P.C_1 * W_top * s := by
    intro s hs
    have e : 2 * C₁ * Real.exp (|clarkNode α 1| / 4) * s / clarkKernel α 1 =
        (2 * (C₁ * Real.exp (|clarkNode α 1| / 4)) * s) * (1 / clarkKernel α 1) := by ring
    rw [e]
    have h0 : 0 ≤ 2 * (C₁ * Real.exp (|clarkNode α 1| / 4)) * s := by positivity
    calc (2 * (C₁ * Real.exp (|clarkNode α 1| / 4)) * s) * (1 / clarkKernel α 1)
        ≤ (2 * (C₁ * Real.exp (|clarkNode α 1| / 4)) * s) * (W_top / 2) :=
          mul_le_mul_of_nonneg_left hinv1 h0
      _ ≤ (2 * P.C_1 * s) * (W_top / 2) := by gcongr
      _ = P.C_1 * W_top * s := by ring
      _ ≤ 2 * P.C_1 * W_top * s := by linarith [mul_nonneg (mul_nonneg hPC1_nn hW_nn) hs]
  -- the prescribed-node term, for `ℓ ≥ D₁ c'^{-1/3}`
  have hterm1 : ∀ k : ℕ, (k : ℝ) ≤ R / 5 → ∀ ℓ : ℝ, P.D_1 * c' ^ (-(1 / 3 : ℝ)) ≤ ℓ → ℓ ≤ 1 →
      -(2 * P.C_1 * W_top * ℓ) ≤ (1 + clarkNode α 1 / R) ^ (k + 1) *
        (psiTilde prob c' g ((clarkNode α 1 + ℓ : ℝ) : ℂ)).re / clarkKernel α 1 := by
    intro k hkR ℓ hℓ_lo hℓ_1
    have hℓ_nn : 0 ≤ ℓ := (mul_nonneg P.hD1 (Real.rpow_nonneg hc'_pos.le _)).trans hℓ_lo
    have hE1 := pow_le_exp_quarter (k := k) hR_48 hz1_R' hkR
    have hpow1_nn : 0 ≤ (1 + clarkNode α 1 / R) ^ (k + 1) := pow_nonneg hbase1_nn _
    have h1lb := hnode1 ℓ hℓ_lo hℓ_1
    have ht1 : -(2 * C₁ * Real.exp (|clarkNode α 1| / 4) * ℓ) ≤
        (1 + clarkNode α 1 / R) ^ (k + 1) *
          (psiTilde prob c' g ((clarkNode α 1 + ℓ : ℝ) : ℂ)).re := by
      have hm := mul_le_mul_of_nonneg_left h1lb hpow1_nn
      have h2 : 0 ≤ 2 * C₁ * ℓ := by positivity
      linarith [mul_le_mul_of_nonneg_right hE1 h2]
    have ht1' := div_le_div_of_nonneg_right ht1 hK1.le
    rw [neg_div] at ht1'
    linarith [hloss1 ℓ hℓ_nn]
  refine ⟨?_, ?_⟩
  · -- `hP_nodes_lb_hb`
    intro k ℓ _ hkR hℓ_mem
    have hℓ_nn : 0 ≤ ℓ := (mul_nonneg P.hD1 (Real.rpow_nonneg hc'_pos.le _)).trans hℓ_mem.1
    have hℓ_1 : ℓ ≤ 1 := hℓ_mem.2.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hℓ_gap : ℓ ≤ clarkNode α 2 - clarkNode α 3 :=
      hℓ_mem.2.trans (((min_le_right _ _).trans (min_le_left _ _)).trans hP_η)
    have h_main := pnodes_two_nodes_lowerClark hc' hR_48 hR_ub hg hT_A2 hT_z2 hN hℓ_nn hℓ_gap k
    have hpow2_le1 : (1 + clarkNode α 2 / R) ^ (k + 1) ≤ 1 := pow_le_one₀ hbase2_nn hbase2_le1
    have hpow2_nn : 0 ≤ (1 + clarkNode α 2 / R) ^ (k + 1) := pow_nonneg hbase2_nn _
    have h2lb := hnode2 ℓ hℓ_nn hℓ_1
    have ht2 : -(C₁ * ℓ) ≤ (1 + clarkNode α 2 / R) ^ (k + 1) *
        (psiTilde prob c' g ((clarkNode α 2 + ℓ : ℝ) : ℂ)).re := by
      have hm := mul_le_mul_of_nonneg_left h2lb hpow2_nn
      have h2 : 0 ≤ C₁ * ℓ := mul_nonneg hC₁_nn hℓ_nn
      linarith [mul_le_of_le_one_left h2 hpow2_le1]
    have ht2' : -(C₁ * ℓ) / clarkKernel α 2 ≤
        (1 + clarkNode α 2 / R) ^ (k + 1) *
          (psiTilde prob c' g ((clarkNode α 2 + ℓ : ℝ) : ℂ)).re / clarkKernel α 2 :=
      div_le_div_of_nonneg_right ht2 hK2.le
    have hinv2 : 1 / clarkKernel α 2 ≤ 1 / P.w_star := one_div_le_one_div_of_le hw hP_w
    have hA2 : C₁ * ℓ / clarkKernel α 2 ≤ 2 * P.C_1 * (1 / P.w_star) * ℓ := by
      have e : C₁ * ℓ / clarkKernel α 2 = (C₁ * ℓ) * (1 / clarkKernel α 2) := by ring
      rw [e]
      calc (C₁ * ℓ) * (1 / clarkKernel α 2) ≤ (C₁ * ℓ) * (1 / P.w_star) :=
            mul_le_mul_of_nonneg_left hinv2 (mul_nonneg hC₁_nn hℓ_nn)
        _ ≤ (P.C_1 * ℓ) * (1 / P.w_star) := by gcongr
        _ ≤ 2 * P.C_1 * (1 / P.w_star) * ℓ := by
            have : 0 ≤ P.C_1 * ℓ * (1 / P.w_star) := by positivity
            linarith
    have hΛ : tebLambdaN P W_top = 2 * P.C_1 * (1 / P.w_star + W_top) := rfl
    have e2 : -(C₁ * ℓ) / clarkKernel α 2 = -(C₁ * ℓ / clarkKernel α 2) := neg_div _ _
    have h1 := hterm1 k hkR ℓ hℓ_mem.1 hℓ_1
    rw [hΛ]
    linarith [h_main, h1, ht2', hA2, e2]
  · -- `P_theta_bound`
    intro hk0_R hℓ_mem
    set θ := tebThetaHB P W_top with hθ
    have hθ_pos : 0 < θ := tebThetaHB_pos P hW_nn
    have hθ_half : θ ≤ 1 / 2 := tebThetaHB_le_half P W_top
    set x := u_T - clarkNode α 2 with hx
    have hx_pos : 0 < x := by rw [hx]; linarith
    have hx_nn : 0 ≤ x := hx_pos.le
    have hx_1 : x ≤ 1 := hx_le.trans (min_le_right _ _)
    have hℓ_nn : 0 ≤ θ * x := mul_nonneg hθ_pos.le hx_nn
    have hℓ_1 : θ * x ≤ 1 := by
      have := mul_le_mul hθ_half hx_1 hx_nn (by norm_num)
      linarith
    have hℓ_gap : θ * x ≤ clarkNode α 2 - clarkNode α 3 :=
      hℓ_mem.2.trans (((min_le_right _ _).trans (min_le_left _ _)).trans hP_η)
    have h_main := pnodes_two_nodes_lowerClark hc' hR_48 hR_ub hg hT_A2 hT_z2 hN hℓ_nn hℓ_gap P.k_0
    have hδ_x : x ≤ δ := hx_le.trans (min_le_left _ _)
    have hsec := quantC1ClarkB2_secant_lower (R_dom := Q.AC c' ^ 2) hδ_pos hδ_half
      (by show |clarkNode α 2| + 1 ≤ Q.AC c' ^ 2; rw [abs_of_neg hz2_neg]; linarith) hΨ_an_R huT_gt huT_nn hB2 hθ_pos.le (by linarith)
    have h_psi2 : κ * x ≤ (psiTilde prob c' g ((clarkNode α 2 + θ * x : ℝ) : ℂ)).re := by
      have h1 : κ * x ≤ 2 * κ * (1 - θ) * x := by
        have := mul_nonneg (mul_nonneg hκ_pos.le hx_nn) (sub_nonneg.mpr hθ_half)
        linarith
      exact h1.trans hsec
    have h_pow2 : (1 / 2 : ℝ) ≤ (1 + clarkNode α 2 / R) ^ (P.k_0 + 1) := by
      rw [hP_k0]
      have h1 : (1 - 4.84 / 48 : ℝ) ≤ 1 + clarkNode α 2 / R := by
        have hdiv : -4.84 / 48 ≤ clarkNode α 2 / R := by
          calc -4.84 / 48 ≤ -4.84 / R := by
                rw [neg_div, neg_div, neg_le_neg_iff]
                exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hR_48
            _ ≤ clarkNode α 2 / R := div_le_div_of_nonneg_right (by linarith) hR_pos.le
        linarith
      have h2 : (1 / 2 : ℝ) ≤ (1 - 4.84 / 48 : ℝ) ^ (5 + 1) := by norm_num
      exact h2.trans (pow_le_pow_left₀ (by norm_num) h1 _)
    have hκx_nn : 0 ≤ κ * x := mul_nonneg hκ_pos.le hx_nn
    have ht2 : (1 / 2 : ℝ) * (κ * x) ≤ (1 + clarkNode α 2 / R) ^ (P.k_0 + 1) *
        (psiTilde prob c' g ((clarkNode α 2 + θ * x : ℝ) : ℂ)).re :=
      mul_le_mul h_pow2 h_psi2 hκx_nn (pow_nonneg hbase2_nn _)
    have ht2' : (1 / 2 : ℝ) * (κ * x) / clarkKernel α 2 ≤
        (1 + clarkNode α 2 / R) ^ (P.k_0 + 1) *
          (psiTilde prob c' g ((clarkNode α 2 + θ * x : ℝ) : ℂ)).re / clarkKernel α 2 :=
      div_le_div_of_nonneg_right ht2 hK2.le
    have h1 := hterm1 P.k_0 hk0_R (θ * x) hℓ_mem.1 hℓ_1
    have hκw : P.κ_star / (2 * P.w_star) ≤ κ / (2 * clarkKernel α 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith [hP_κ]
    have hhalf : (1 / 2 : ℝ) * (κ * x) / clarkKernel α 2 = κ / (2 * clarkKernel α 2) * x := by
      field_simp
    have hnodelow := hb_theta_node_lower P hW_nn
    have hfin : (P.κ_star / (4 * P.w_star)) * x ≤
        (P.κ_star / (2 * P.w_star) - 2 * P.C_1 * W_top * θ) * x :=
      mul_le_mul_of_nonneg_right hnodelow hx_nn
    have hkx : P.κ_star / (2 * P.w_star) * x ≤ κ / (2 * clarkKernel α 2) * x :=
      mul_le_mul_of_nonneg_right hκw hx_nn
    linarith [h_main, h1, ht2', hhalf, hfin, hkx]

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.pnodes_lb_and_thetaClark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pnodes_lb_and_thetaClark

/-! ### Uniformity in the first level `u₁` -/

/-- A continuous function on a compact set has a positive lower bound when it is positive. -/
private lemma exists_pos_lower_of_continuousOn {K : Set ℝ} (hK : IsCompact K) {f : ℝ → ℝ}
    (hf : ContinuousOn f K) (hpos : ∀ u ∈ K, 0 < f u) : ∃ m : ℝ, 0 < m ∧ ∀ u ∈ K, m ≤ f u := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (f := fun u => (f u)⁻¹) (hf.inv₀ fun u hu => (hpos u hu).ne')
  refine ⟨1 / (max B 1), by positivity, fun u hu => ?_⟩
  have h1 : (f u)⁻¹ ≤ max B 1 := by
    have := hB u hu
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hpos u hu))] at this
    exact this.trans (le_max_left _ _)
  have := hpos u hu
  rw [one_div, inv_le_comm₀ (by positivity) this]
  exact h1

private lemma exists_upper_of_continuousOn {K : Set ℝ} (hK : IsCompact K) {f : ℝ → ℝ}
    (hf : ContinuousOn f K) : ∃ M : ℝ, 0 < M ∧ ∀ u ∈ K, f u ≤ M := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf
  refine ⟨max B 1, by positivity, fun u hu => ?_⟩
  exact ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hB u hu)).trans (le_max_left _ _)

/-- Parameter constants for the Clark nodes, uniform for the first level `u₁ ∈ K ⊂ (a₁, ∞)`: given
`(κ, C₁) > 0`, there are `C_s, w_s, κ_s, η_s > 0`, `W_s ≥ 0` and `R_s` with, for every `u₁ ∈ K` and `α = clarkAngle u₁`
(so `z₁(α) = u₁`), `C₁ exp(|z₁|/4) ≤ C_s`, `w_s ≤ K₂`, `κ_s K₂ ≤ κ w_s`, `η_s ≤ z₂ - z₃`, `2/K₁ ≤ W_s`,
`|z₁| + 1 ≤ R_s`. -/
theorem pnodes_clark_constants_uniform {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Ioi (airyZero 1))
    {κ C₁ : ℝ} (hκ : 0 < κ) (hC₁ : 0 < C₁) :
    ∃ Cs ws κs ηs Ws Rs : ℝ, 0 < Cs ∧ 0 < ws ∧ 0 < κs ∧ 0 < ηs ∧ 0 ≤ Ws ∧
      ∀ u ∈ K, C₁ * Real.exp (|clarkNode (clarkAngle u) 1| / 4) ≤ Cs ∧
        ws ≤ clarkKernel (clarkAngle u) 2 ∧
        κs * clarkKernel (clarkAngle u) 2 ≤ κ * ws ∧
        ηs ≤ clarkNode (clarkAngle u) 2 - clarkNode (clarkAngle u) 3 ∧
        2 / clarkKernel (clarkAngle u) 1 ≤ Ws ∧ |clarkNode (clarkAngle u) 1| + 1 ≤ Rs := by
  have hcontR : ContinuousOn airyRatio K :=
    (continuousOn_airyRatio (n := 1) le_rfl).mono fun u hu => by
      rw [airyClarkGap_one]; exact hKsub hu
  have hzn : ∀ n : ℕ, 1 ≤ n → ∀ u ∈ K,
      clarkNode (clarkAngle u) n = airyClarkNode (airyRatio u) n := fun n hn u hu => by
    change airyClarkNode (Real.cos (clarkAngle u) / Real.sin (clarkAngle u)) n = _
    rw [cot_clarkAngle (hKsub hu)]
  have hcontz : ∀ n : ℕ, 1 ≤ n → ContinuousOn (fun u => airyClarkNode (airyRatio u) n) K :=
    fun n hn => (continuous_airyClarkNode hn).comp_continuousOn hcontR
  have hz1 : ∀ u ∈ K, clarkNode (clarkAngle u) 1 = u := fun u hu => by
    rw [hzn 1 le_rfl u hu]; exact airyClarkNode_airyRatio_one (hKsub hu)
  have hker : ∀ n : ℕ, 1 ≤ n → ∀ u ∈ K, clarkKernel (clarkAngle u) n =
      airyAi' (airyClarkNode (airyRatio u) n) ^ 2 -
        airyClarkNode (airyRatio u) n * airyAi (airyClarkNode (airyRatio u) n) ^ 2 := fun n hn u hu => by
    unfold clarkKernel; rw [hzn n hn u hu]
  have hcontk : ∀ n : ℕ, 1 ≤ n → ContinuousOn (fun u => clarkKernel (clarkAngle u) n) K := by
    intro n hn
    have : ContinuousOn (fun u => airyAi' (airyClarkNode (airyRatio u) n) ^ 2 -
        airyClarkNode (airyRatio u) n * airyAi (airyClarkNode (airyRatio u) n) ^ 2) K :=
      ((continuous_airyAi'.comp_continuousOn (hcontz n hn)).pow 2).sub
        ((hcontz n hn).mul ((continuous_airyAi.comp_continuousOn (hcontz n hn)).pow 2))
    exact this.congr fun u hu => hker n hn u hu
  have hgap : ∀ u ∈ K, 0 < clarkNode (clarkAngle u) 2 - clarkNode (clarkAngle u) 3 := fun u hu => by
    rw [hzn 2 (by norm_num) u hu, hzn 3 (by norm_num) u hu]
    have := airyClarkNode_succ_lt (n := 2) (by norm_num) (airyRatio u)
    linarith [this.1, this.2]
  have hcontgap : ContinuousOn (fun u => clarkNode (clarkAngle u) 2 - clarkNode (clarkAngle u) 3) K :=
    ((hcontz 2 (by norm_num)).sub (hcontz 3 (by norm_num))).congr fun u hu => by
      rw [Pi.sub_apply, hzn 2 (by norm_num) u hu, hzn 3 (by norm_num) u hu]
  obtain ⟨M, hM, hMb⟩ := exists_upper_of_continuousOn hK (continuousOn_id.abs (s := K))
  obtain ⟨m₂, hm₂, hm₂b⟩ := exists_pos_lower_of_continuousOn hK (hcontk 2 (by norm_num))
    fun u hu => clarkKernel_pos _ 2
  obtain ⟨M₂, hM₂, hM₂b⟩ := exists_upper_of_continuousOn hK (hcontk 2 (by norm_num))
  obtain ⟨m₁, hm₁, hm₁b⟩ := exists_pos_lower_of_continuousOn hK (hcontk 1 le_rfl)
    fun u hu => clarkKernel_pos _ 1
  obtain ⟨η, hη, hηb⟩ := exists_pos_lower_of_continuousOn hK hcontgap hgap
  refine ⟨C₁ * Real.exp (M / 4), m₂, κ * m₂ / M₂, η, 2 / m₁, M + 1, by positivity, hm₂, by positivity,
    hη, by positivity, fun u hu => ?_⟩
  have hu1 := hz1 u hu
  have hMu : |u| ≤ M := hMb u hu
  refine ⟨?_, hm₂b u hu, ?_, hηb u hu, ?_, ?_⟩
  · rw [hu1]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hC₁.le
  · have hK2 := hM₂b u hu
    have hK2p := clarkKernel_pos (clarkAngle u) 2
    rw [div_mul_eq_mul_div, div_le_iff₀ hM₂]
    nlinarith [mul_pos hκ hm₂]
  · exact div_le_div_of_nonneg_left two_pos.le hm₁ (hm₁b u hu)
  · rw [hu1]; linarith

/-- **`pnodes_lb_and_thetaClark` with constants uniform in the first level**: for `u₁` in a compact `K ⊂ (a₁, ∞)`, `α = clarkAngle u₁`,
and the constants `(δ, κ, C₁)` of `teb_quant_c1_clark_typeII_firstLevel` for the pair `γ = Ai'(u₁)/Ai(u₁)`, there are
parameters `(C_s, w_s, κ_s, η_s, W_s, R_s)` such that every `BootstrapParams` with `C_1 = C_s`, `w_* = w_s`, `κ_* = κ_s`,
`η₀ = η_s`, `k₀ = 5` satisfies both node bounds of `pnodes_lb_and_thetaClark` with `W_top = W_s`, for all `u₁ ∈ K` and all
radii `R ≥ max 48 R_s`. -/
theorem pnodes_lb_and_thetaClark_uniform {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Ioi (airyZero 1))
    {δ κ C₁ : ℝ} (hδ_pos : 0 < δ) (hδ_half : δ ≤ 1 / 2) (hκ : 0 < κ) (hC₁ : 0 < C₁) :
    ∃ Cs ws κs ηs Ws Rs : ℝ, 0 < Cs ∧ 0 < ws ∧ 0 < κs ∧ 0 < ηs ∧ 0 ≤ Ws ∧
      ∀ P : BootstrapParams, P.C_1 = Cs → P.w_star = ws → P.κ_star = κs → P.η_0 = ηs → P.k_0 = 5 →
      ∀ u₁ ∈ K, ∀ {c' R T : ℝ} {N : ℕ}, Q.cQ ≤ c' → 48 ≤ R → Rs ≤ R → R + 1 ≤ Q.AC c' ^ 2 →
      ∀ {g : ℝ → ℝ}, prob.IsWeaklyFeasible (c' / 12) T g →
      virasoroDeltaChart c' (Q.AC c' ^ 2) ≤ T →
      T < virasoroDeltaChart c' (clarkNode (clarkAngle u₁) 2) →
      QuantC1B2HoldsClark (airyRatio u₁) δ κ C₁ (psiTilde prob c' g) (virasoroUT c' T) →
      (∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -R < clarkNode (clarkAngle u₁) n)) →
      ∀ {ũ : ℝ}, |ũ - u₁| ≤ P.D_1 * c' ^ (-(1 / 3 : ℝ)) → 0 ≤ (psiTilde prob c' g (ũ : ℂ)).re →
      (∀ k : ℕ, ∀ ℓ : ℝ, P.k_0 ≤ k → (k : ℝ) ≤ R / 5 →
        ℓ ∈ Icc (P.D_1 * c' ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
        -tebLambdaN P Ws * ℓ - P.C_α * R ^ (3 / 2 : ℝ) * 0 ≤
          pNodesClark prob (clarkAngle u₁) c' R ℓ g k N) ∧
      ((P.k_0 : ℝ) ≤ R / 5 →
        tebThetaHB P Ws * (virasoroUT c' T - clarkNode (clarkAngle u₁) 2) ∈
          Icc (P.D_1 * c' ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
        (P.κ_star / (4 * P.w_star)) * (virasoroUT c' T - clarkNode (clarkAngle u₁) 2) -
          P.C_α * R ^ (3 / 2 : ℝ) * 0 ≤
          pNodesClark prob (clarkAngle u₁) c' R
            (tebThetaHB P Ws * (virasoroUT c' T - clarkNode (clarkAngle u₁) 2)) g P.k_0 N) := by
  obtain ⟨Cs, ws, κs, ηs, Ws, Rs, hCs, hws, hκs, hηs, hWs, h⟩ :=
    pnodes_clark_constants_uniform hK hKsub hκ hC₁
  refine ⟨Cs, ws, κs, ηs, Ws, Rs, hCs, hws, hκs, hηs, hWs, ?_⟩
  intro P hC hw hκP hη hk0 u₁ hu₁ c' R T N hc' hR48 hRs hR_ub g hg hT_A2 hT_z2 hB2 hN ũ hũ hũ_nn
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h u₁ hu₁
  have hcot : Real.cos (clarkAngle u₁) / Real.sin (clarkAngle u₁) = airyRatio u₁ :=
    cot_clarkAngle (hKsub hu₁)
  have hz1 : clarkNode (clarkAngle u₁) 1 = u₁ := (clarkAngle_spec (hKsub hu₁)).2
  refine pnodes_lb_and_thetaClark (α := clarkAngle u₁) (δ := δ) (κ := κ) (C₁ := C₁) hc' hR48 hR_ub
    (h6.trans hRs) hg hT_A2 hT_z2 hδ_pos hδ_half (by rw [hcot]; exact hB2) hN P h5
    (by rw [hC]; exact h1) (by rw [hw]; exact h2) (by rw [hw, hκP]; exact h3)
    (by rw [hη]; exact h4) hk0 (ũ := ũ) (by rwa [hz1]) hũ_nn

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.pnodes_clark_constants_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pnodes_clark_constants_uniform

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.pnodes_lb_and_thetaClark_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pnodes_lb_and_thetaClark_uniform

/-- Non-vacuity: parameters with prescribed `C_1, w_*, κ_*, η₀, k₀ = 5` exist. -/
theorem bootstrapParams_exists_clark {Cs ws κs ηs : ℝ} (hCs : 0 < Cs) (hws : 0 < ws) (hκs : 0 < κs)
    (hηs : 0 < ηs) :
    ∃ P : BootstrapParams, P.C_1 = Cs ∧ P.w_star = ws ∧ P.κ_star = κs ∧ P.η_0 = ηs ∧ P.k_0 = 5 :=
  ⟨{ b := 1, C_a := 0, C_unc := 0, C_1 := Cs, w_star := ws, κ_star := κs, C_α := 0, C_fb := 1,
     D_1 := 0, η_0 := ηs, δ_star := 1 / 2, κ := 1, C_0 := 1, C_L := 1, γ := 0, k_0 := 5,
     hb := one_pos, hCa := le_rfl, hCunc := le_rfl, hC1 := hCs, hw_star := hws, hκ_star := hκs,
     hCα := le_rfl, hCfb := le_rfl, hD1 := le_rfl, hη0 := hηs, hδ_star := by norm_num,
     hκ := one_pos, hC0 := one_pos, hCL := le_rfl, hγ := le_rfl, hk0 := by norm_num },
    rfl, rfl, rfl, rfl, rfl⟩

end FormalResearch.ModularBootstrap.FixedWeightBand
