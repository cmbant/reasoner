module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapClarkHBAux

/-!
# The `m₀ = 2` Hermite--Biehler `BootstrapHBInstance` at the Clark Nodes (Theorem `FT-L.FW`, Steps 0-4)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Theorem `FT-L.FW` (`wone:ftlfw`), Steps 0-4, and
Theorem `W1'(2)` (`wone:genlower`(2)): the constant pair `(P, Q) = (cos α, -sin α)`, `N = ψ_α`, `m₀ = 2`, `t_j = z_j(α)`;
`CFT/common/two_edge_bootstrap.tex`, Theorem `TE.2(4)` (`teb:bootstrap`).

* `bootstrapParamsForClark`: concrete `BootstrapParams` at scale `b` (`C_a = max (μ₀ C_a⁰) (C_line + 3 C₀)`,
  `C_unc = μ₀ C_unc⁰`, `C_1 = C_s`, `w_* = w_s`, `κ_* = κ_s`, `η₀ = η_s`, `δ_* = δ`, `k₀ = 5`), with `μ₀` the Clark
  arc factor, `C_s ≥ C₁ exp(|z₁|/4)` the node constant of `pnodes_lb_and_thetaClark`;
* `ClarkArcAt`, `ClarkArcData`, `clarkArcData_exists`: the good-circle quadrature at the Clark nodes
  (`quad_arc_boundClark_uniform`) in the per-`α` form consumed by the instance;
* `bootstrapHB_of_YVForClark`: the `BootstrapHBInstance P W_top` (with `(B3)`) for a violator `T < Δ(z₂(α))`,
  `α = α(u₁)`, from `YVInputAtForWThr` at the cutoff radius `A_thr = |z₂| + 1` (the level enters only through `A_thr`),
  the Clark arc data, the node bounds `pnodes_lb_and_thetaClark`, and the `TE.0'` conclusion
  `QuantC1B2HoldsClark`; `x̃ = u_T - z₂`, `ustar = z₂`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap Crossing PoissonJensen TipFront
  ConcreteBootstrap FixedWeightTip FormalResearch.SignUncertainty TwoLevel

variable {prob : FixedWeightProblem}

/-- Concrete `BootstrapParams` for the Clark pair at scale `b > 0`: the line constant `C_line` bounds `lineCaW A_thr`
at the cutoff radius in use, `μ₀` is the Clark arc factor, `(C_s, w_s, κ_s, η_s)` are the node constants. -/
noncomputable def bootstrapParamsForClark (Q : LemmaQData prob)
    (b : ℝ) (hb : 0 < b) (C_fb : ℝ) (hC_fb : 1 ≤ C_fb)
    (C_gap κ_gap : ℝ) (hκ_gap : 0 < κ_gap) (C_line μ₀ : ℝ) (hμ₀ : 0 < μ₀)
    (D_1 δ_star Cs ws κs ηs : ℝ) (hD_1 : 0 < D_1) (hδ_star : 0 < δ_star)
    (hCs : 0 < Cs) (hws : 0 < ws) (hκs : 0 < κs) (hηs : 0 < ηs) :
    BootstrapParams where
  b := b
  C_a := max (μ₀ * virasoroArcCovConst) (C_line + 3 * Q.C0)
  C_unc := μ₀ * Q.arcUncConst
  C_1 := Cs
  w_star := ws
  κ_star := κs
  C_α := 0
  C_fb := C_fb
  D_1 := D_1
  η_0 := ηs
  δ_star := δ_star
  κ := κ_gap
  C_0 := max 1 C_gap
  C_L := 4 * C_fb
  γ := 1
  k_0 := 5
  hb := hb
  hCa := le_trans (mul_nonneg hμ₀.le virasoroArcCovConst_pos.le) (le_max_left _ _)
  hCunc := mul_nonneg hμ₀.le Q.arcUncConst_pos.le
  hC1 := hCs
  hw_star := hws
  hκ_star := hκs
  hCα := le_rfl
  hCfb := hC_fb
  hD1 := hD_1.le
  hη0 := hηs
  hδ_star := hδ_star
  hκ := hκ_gap
  hC0 := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  hCL := by linarith
  hγ := zero_le_one
  hk0 := by omega

/-! ### The Clark arc data -/

variable [Q : LemmaQData prob]

/-- The covered-arc/uncovered-wedge estimate at a good circle `R` of `ψ_α` with node count `N` (`wone:ftlfwquad`):
the conclusion of `quad_arc_boundClark_uniform` for one `α`. -/
def ClarkArcAt (prob : FixedWeightProblem) [Q : LemmaQData prob] (α μ₀ R : ℝ) (N : ℕ) : Prop :=
  ∀ {c' T L' ℓ : ℝ}, Q.cQ ≤ c' → (3 * π) ^ (12 : ℕ) ≤ c' →
    Q.sigma c' * (3 * π * √R * c' ^ (-(1 / 12 : ℝ)) + 1) ≤ 1 → R + 1 ≤ Q.AC c' ^ 2 →
    0 ≤ L' → 0 ≤ ℓ → ℓ ≤ 1 / 2 →
    ∀ {g : ℝ → ℝ}, prob.IsWeaklyFeasible (c' / 12) T g →
    YVEnvBound (psiTilde prob c' g) c' R L' → ∀ {k' : ℕ}, 5 ≤ k' →
    pNodesClark prob α c' R ℓ g k' N ≤
      (∫ x in (-R)..R, (shiftedFunW prob c' R ℓ g k' (x : ℂ)).re) +
        μ₀ * virasoroArcCov c' R T L' ℓ g k' + μ₀ * (Q.arcUncConst * c' ^ (-(3 / 8 : ℝ)))

/-- Good radii `R ∈ [k, k+1]` for every `k ≥ k₀`, with the node count `N` and the arc estimate, for the Clark angle `α`. -/
def ClarkArcData (prob : FixedWeightProblem) [Q : LemmaQData prob] (α μ₀ : ℝ) (k₀ : ℕ) : Prop :=
  ∀ k : ℕ, k₀ ≤ k → ∃ R : ℝ, (k : ℝ) ≤ R ∧ R ≤ k + 1 ∧
    (clarkNode α 1 < R → ∃ N : ℕ, (∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -R < clarkNode α n)) ∧
      ClarkArcAt prob α μ₀ R N)

/-- The Clark arc data for every `α` with `|sin α| ≥ σ` (`quad_arc_boundClark_uniform`). -/
theorem clarkArcData_exists {σ : ℝ} (hσ : 0 < σ) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∃ k₀ : ℕ, 10 ≤ k₀ ∧ ∀ α : ℝ, σ ≤ |Real.sin α| → ClarkArcData prob α μ₀ k₀ := by
  obtain ⟨μ₀, hμ₀, k₀, hk₀, h⟩ := quad_arc_boundClark_uniform (prob := prob) hσ
  refine ⟨μ₀, hμ₀, k₀, hk₀, fun α hα k hk => ?_⟩
  obtain ⟨R, hR1, hR2, hR⟩ := h k hk
  refine ⟨R, hR1, hR2, fun hz1 => ?_⟩
  obtain ⟨N, hN, hN2⟩ := hR α hα hz1
  exact ⟨N, hN, hN2⟩

/-! ### The instance -/

/-- **The concrete `BootstrapHBInstance P W_top` at the Clark nodes** (`wone:ftlfw`, Steps 0-4, `m₀ = 2`,
`ustar = z₂(α)`).  For a weakly feasible `g` at `(c'/12, T)` with violator threshold `Δ(A_{c'}(b)²) < T < Δ(z₂)`,
`z₂ = z₂(α(u₁))`, `u₁ > a₁`, a prescribed point `ũ` with `|ũ - u₁| ≤ D₁ c'^{-1/3}`, `Ψ̃(ũ) ≥ 0`, the `TE.0'` conclusion
`QuantC1B2HoldsClark` (constants `δ ≤ 1/2`, `κ`, `C₁`) and `x̃ = u_T - z₂ ≤ η_s`, there is a `BootstrapHBInstance P W_top`
with `c = c'`, `x̃ = u_T - z₂` and `L ≤ C_fb (c^{1/3} (B₁ + B₂) + 1)`.  The band feedback is `YVInputAtForWThr` at the
cutoff radius `A_thr = |z₂| + 1 ∈ [virasoroAThr, secondLevelAThr]`; the node bounds are
`pnodes_lb_and_thetaClark` for `P.C_1 = C_s ≥ C₁ exp(|z₁|/4)`, `w_s ≤ K₂`, `κ_s K₂ ≤ κ w_s`, `η_s ≤ z₂ - z₃` and
`W_top ≥ 2/K₁`; the arc estimate is the `ClarkArcData` of `α`, with the radius `R ∈ [k, k+1]`,
`k = ⌈b² c'^{2/3}⌉`. -/
noncomputable def bootstrapHB_of_YVForClark
    {u₁ b C_fb c_YV C_gap κ_gap C_line μ₀ D_1 δ κ C₁ Cs ws κs ηs W_top : ℝ} {k₀ : ℕ}
    (hu₁ : airyZero 1 < u₁)
    (hC_line : lineCaW (|clarkNode (clarkAngle u₁) 2| + 1) ≤ C_line)
    (hb_pos : 0 < b) (hb_le : b ≤ Q.bV)
    (hC_fb : 1 ≤ C_fb) (hC_gap : 0 < C_gap) (hκ_gap : 0 < κ_gap) (hμ₀ : 0 < μ₀)
    (hD_1 : 0 < D_1) (hδ_pos : 0 < δ) (hδ_half : δ ≤ 1 / 2) (hκ : 0 < κ) (hC₁ : 0 < C₁)
    (hCs_pos : 0 < Cs) (hws_pos : 0 < ws) (hκs_pos : 0 < κs) (hηs_pos : 0 < ηs)
    (hYVat : YVInputAtForWThr prob (|clarkNode (clarkAngle u₁) 2| + 1) b (psiTilde prob) C_fb c_YV)
    (hCs : C₁ * Real.exp (|clarkNode (clarkAngle u₁) 1| / 4) ≤ Cs)
    (hws : ws ≤ clarkKernel (clarkAngle u₁) 2) (hκs : κs * clarkKernel (clarkAngle u₁) 2 ≤ κ * ws)
    (hηs : ηs ≤ clarkNode (clarkAngle u₁) 2 - clarkNode (clarkAngle u₁) 3)
    (hW : 2 / clarkKernel (clarkAngle u₁) 1 ≤ W_top)
    (hArc : ClarkArcData prob (clarkAngle u₁) μ₀ k₀)
    {c' T : ℝ} (hc'_Qenv : Q.cQ ≤ c') (hc'_YV : c_YV ≤ c')
    (h_c12 : (3 * π) ^ (12 : ℕ) ≤ c')
    (h_b48 : 48 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ))
    (hk₀ : (k₀ : ℝ) ≤ b ^ 2 * c' ^ (2 / 3 : ℝ))
    (hz1_b : |clarkNode (clarkAngle u₁) 1| + 1 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ))
    (hς_half : Q.sigma c' ≤ 1 / 2)
    (hς_arc : Q.sigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1) ≤ 1)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hdl_bd : deltaLobeAt prob b c' g ≤ C_gap * Real.exp (-κ_gap * c'))
    (hdl_half : deltaLobeAt prob b c' g < 1 / 2)
    (hT_A2 : virasoroDeltaChart c' (chartACAt b c' ^ 2) < T)
    (hT_z2 : T < virasoroDeltaChart c' (clarkNode (clarkAngle u₁) 2))
    (hB2 : QuantC1B2HoldsClark (airyRatio u₁) δ κ C₁ (psiTilde prob c' g) (virasoroUT c' T))
    (hx_eta : virasoroUT c' T - clarkNode (clarkAngle u₁) 2 ≤ ηs)
    {ũ : ℝ} (hũ_near : |ũ - u₁| ≤ D_1 * c' ^ (-(1 / 3 : ℝ)))
    (hũ_nn : 0 ≤ (psiTilde prob c' g (ũ : ℂ)).re) :
    let P := bootstrapParamsForClark Q b hb_pos C_fb hC_fb C_gap κ_gap hκ_gap C_line μ₀ hμ₀
      D_1 δ Cs ws κs ηs hD_1 hδ_pos hCs_pos hws_pos hκs_pos hηs_pos
    { I : BootstrapHBInstance P W_top //
      I.L ≤ P.C_fb * (I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2) + 1) ∧
      I.c = c' ∧ I.x_tilde = virasoroUT c' T - clarkNode (clarkAngle u₁) 2 } := by
  intro P
  set α := clarkAngle u₁ with hα
  have hc'_10000 : 10000 ≤ c' := Q.hcQ_10000.trans hc'_Qenv
  have hc'_pos : 0 < c' := by linarith
  have hc'_ge1 : 1 ≤ c' := by linarith
  obtain ⟨hz2_lo, hz2_hi⟩ := airyZero_two_lt_clarkNode_two hu₁
  obtain ⟨ha1_lo, ha1_hi⟩ := airyZero_one
  obtain ⟨ha2_lo, ha2_hi⟩ := airyZero_two
  have hz2_neg : clarkNode α 2 < 0 := by linarith
  have hAthr_eq : |clarkNode α 2| + 1 = -clarkNode α 2 + 1 := by rw [abs_of_neg hz2_neg]
  set A_thr : ℝ := |clarkNode α 2| + 1 with hA_thr
  have hA_thr_lo : 3 < A_thr := by rw [hAthr_eq]; linarith
  have hA_thr_hi : A_thr < 6 := by rw [hAthr_eq]; linarith
  have hA_pos : 0 < A_thr := by linarith
  obtain ⟨hlobe_AC, hdl_bd_full, hdl_half_full, hT_A2_full⟩ :=
    lobe_scale_downW hb_pos hb_le hc'_Qenv hg hdl_bd hdl_half hT_A2
  let k₁ : ℕ := ⌈b ^ 2 * c' ^ (2 / 3 : ℝ)⌉₊
  have hk₁_ge48 : 48 ≤ k₁ := by
    dsimp [k₁]
    have : (48 : ℝ) ≤ (⌈b ^ 2 * c' ^ (2 / 3 : ℝ)⌉₊ : ℝ) := h_b48.trans (Nat.le_ceil _)
    exact_mod_cast this
  have hk₀_k₁ : k₀ ≤ k₁ := by
    have : (k₀ : ℝ) ≤ (k₁ : ℝ) := hk₀.trans (Nat.le_ceil _)
    exact_mod_cast this
  have hex := hArc k₁ hk₀_k₁
  let R : ℝ := Classical.choose hex
  have hR_spec := Classical.choose_spec hex
  have hR_lb : (k₁ : ℝ) ≤ R := hR_spec.1
  have hR_le_k : R ≤ (k₁ : ℝ) + 1 := hR_spec.2.1
  have hR_48 : 48 ≤ R := (by exact_mod_cast hk₁_ge48 : (48 : ℝ) ≤ k₁).trans hR_lb
  have hR_pos : 0 < R := by linarith
  have hR_bv : b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R := (Nat.le_ceil _).trans hR_lb
  have hR_ub_ceil : R ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) + 2 := by
    have hlt := Nat.ceil_lt_add_one (by positivity : 0 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ))
    linarith
  have hR_ub_2b : R ≤ 2 * b ^ 2 * c' ^ (2 / 3 : ℝ) + 1 := by linarith
  have hR_ub_b : R + 1 ≤ chartACAt b c' ^ 2 := by
    rw [chartACAt_sq b c' hc'_pos.le]; linarith
  have hR_ub : R + 1 ≤ Q.AC c' ^ 2 := hR_ub_b.trans hlobe_AC
  have hR_thr : A_thr ≤ R := by linarith
  have hz1_R : |clarkNode α 1| + 1 ≤ R := hz1_b.trans hR_bv
  have hz1_lt_R : clarkNode α 1 < R := by linarith [le_abs_self (clarkNode α 1)]
  have hN_ex := hR_spec.2.2 hz1_lt_R
  let N : ℕ := Classical.choose hN_ex
  have hN_spec := Classical.choose_spec hN_ex
  have hN : ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -R < clarkNode α n) := hN_spec.1
  have hArcAt : ClarkArcAt prob α μ₀ R N := hN_spec.2
  have hcot : Real.cos α / Real.sin α = airyRatio u₁ := cot_clarkAngle hu₁
  have hB2' : QuantC1B2HoldsClark (Real.cos α / Real.sin α) δ κ C₁ (psiTilde prob c' g)
      (virasoroUT c' T) := by rw [hcot]; exact hB2
  have hB2_node2 : airyClarkNode (airyRatio u₁) 2 = clarkNode α 2 := airyClarkNode_airyRatio_two hu₁
  have hx_half : virasoroUT c' T - clarkNode α 2 ≤ 1 / 2 := by
    have := hB2.xtilde_le
    rw [hB2_node2] at this
    exact this.trans ((min_le_left _ _).trans hδ_half)
  have hAC4 : 4 ≤ Q.AC c' ^ 2 := by linarith
  have hz2_lo_AC : -(Q.AC c' ^ 2) ≤ clarkNode α 2 := by linarith
  have hz2_a1 : clarkNode α 2 < airyZero 1 := hz2_hi
  have hzR : |clarkNode α 2| ≤ R := by linarith
  have hzA : |clarkNode α 2| ≤ A_thr := by linarith
  have hA_AC : A_thr ≤ Q.AC c' ^ 2 := by linarith
  obtain ⟨huT_gt, huT_m1, hT_lo_m1, hT_lo_0, hT_hi_R⟩ := uT_range_of_violatorClark (R := R) hc'_Qenv
    hz2_lo_AC hz2_a1 hAC4 hT_A2_full.le hT_z2 hx_half hzR (by linarith)
  obtain ⟨-, -, -, -, hT_hi_AThr⟩ := uT_range_of_violatorClark (R := A_thr) hc'_Qenv
    hz2_lo_AC hz2_a1 hAC4 hT_A2_full.le hT_z2 hx_half hzA hA_AC
  set u_T := virasoroUT c' T
  have hB_sums := band_sums_leW_thr hA_pos hc'_Qenv hR_thr hR_ub hg hdl_half_full hT_lo_0 hT_hi_AThr
  have hB1_nn : 0 ≤ bandB1W prob c' R T g :=
    bandB1W_nonneg_thr hA_pos hc'_Qenv hR_thr (by linarith) hg hT_lo_0 hT_hi_AThr
  have hB2_nn : 0 ≤ bandB2W prob c' R g :=
    bandB2W_nonneg_thr hA_pos hc'_Qenv hR_thr (by linarith) hg hT_hi_AThr
  set B_1 := bandB1W prob c' R T g
  set B_2 := bandB2W prob c' R g
  set L := C_fb * (c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1)
  have hL_lb : 1 ≤ L := by
    have h1 : 1 ≤ c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1 := by
      have : 0 ≤ c' ^ (1 / 3 : ℝ) * (B_1 + B_2) :=
        mul_nonneg (Real.rpow_nonneg hc'_pos.le _) (by linarith)
      linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ C_fb * (c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1) := mul_le_mul hC_fb h1 zero_le_one (by linarith)
  have hL_ub : L ≤ P.C_L * c' ^ P.γ := by
    have hc13_le : c' ^ (1 / 3 : ℝ) ≤ c' := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hc'_ge1 (by norm_num : (1 / 3 : ℝ) ≤ 1)
    have h1 : c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1 ≤ 4 * c' := by
      have hB3_le : B_1 + B_2 ≤ 3 := by linarith [hB_sums.1, hB_sums.2]
      calc c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1
          ≤ c' * 3 + c' := add_le_add
              (mul_le_mul hc13_le hB3_le (by linarith) hc'_pos.le) hc'_ge1
        _ = 4 * c' := by ring
    dsimp [L, P, bootstrapParamsForClark]
    rw [Real.rpow_one]
    calc C_fb * (c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1)
        ≤ C_fb * (4 * c') := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = 4 * C_fb * c' := by ring
  have hς_arc' := Q.sigma_arc_of_scale hb_pos hc'_ge1 hR_ub_b hς_arc
  have hYV_env : YVEnvBound (psiTilde prob c' g) c' R L :=
    hYVat hc'_YV hR_thr hR_bv hR_ub_b hg hT_lo_0 hT_hi_AThr
  have hũ_near' : |ũ - clarkNode α 1| ≤ P.D_1 * c' ^ (-(1 / 3 : ℝ)) := by
    rw [(clarkAngle_spec hu₁).2]; exact hũ_near
  have hPN := pnodes_lb_and_thetaClark (α := α) (δ := δ) (κ := κ) (C₁ := C₁) hc'_Qenv hR_48 hR_ub
    hz1_R hg hT_A2_full.le hT_z2 hδ_pos hδ_half hB2' hN P hW hCs hws hκs hηs rfl hũ_near' hũ_nn
  have hW_nn : 0 ≤ W_top := (div_nonneg two_pos.le (clarkKernel_pos α 1).le).trans hW
  have hx_le_min : u_T - clarkNode α 2 ≤ min δ 1 := by
    have := hB2.xtilde_le
    rwa [hB2_node2] at this
  refine ⟨{
    c := c'
    R := R
    a := √R
    B_1 := B_1
    B_2 := B_2
    L := L
    x_tilde := u_T - clarkNode α 2
    r_inf := 0
    C_err := C_gap
    hc := by linarith
    ha_lb := by
      calc P.b * c' ^ (1 / 3 : ℝ)
          = √(b ^ 2 * c' ^ (2 / 3 : ℝ)) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hb_pos.le,
              show c' ^ (2 / 3 : ℝ) = (c' ^ (1 / 3 : ℝ)) ^ 2 by
                rw [← Real.rpow_natCast (c' ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc'_pos.le]; norm_num,
              Real.sqrt_sq (Real.rpow_nonneg hc'_pos.le _)]
            rfl
        _ ≤ √R := Real.sqrt_le_sqrt hR_bv
    ha_sq := Real.sq_sqrt hR_pos.le
    hR_ub := hR_ub_2b
    hB1 := hB1_nn
    hB2 := hB2_nn
    hL_lb := hL_lb
    hL_ub := hL_ub
    hx_pos := by linarith
    hx_ub := le_min (hx_le_min.trans (min_le_left _ _))
      (le_min hx_eta (hx_le_min.trans (min_le_right _ _)))
    hr_inf_nn := le_rfl
    hr_inf_ub := by have := P.hC0; positivity
    hC_err_nn := hC_gap.le
    hC_err_ub := le_max_right _ _
    B_1k := fun k => bandB1kW prob c' R T g k
    B_2' := fun _ => B_2
    P_nodes := fun k ℓ => pNodesClark prob α c' R ℓ g k N
    I_line := fun k ℓ => ∫ x in (-R)..R, (shiftedFunW prob c' R ℓ g k (x : ℂ)).re
    Arc_cov := fun k ℓ => μ₀ * virasoroArcCov c' R T L ℓ g k
    Arc_unc := μ₀ * (Q.arcUncConst * c' ^ (-(3 / 8 : ℝ)))
    hB1k_nn := fun k _ _ => bandB1kW_nonneg hc'_Qenv hR_pos.le (by linarith) hg hT_A2_full.le
      hT_hi_R (by linarith [huT_m1]) k
    hB2'_nn := fun _ _ _ => hB2_nn
    hB_sum := fun k _ _ => by
      have := bandB1W_le_B1k hc'_Qenv hR_pos (by linarith) hg hT_lo_0 hT_hi_R k
      linarith
    hP_le := fun k ℓ hk0 _ hℓ_mem => by
      have hℓ_nn : 0 ≤ ℓ := (mul_nonneg P.hD1 (Real.rpow_nonneg hc'_pos.le _)).trans hℓ_mem.1
      have hℓ_half : ℓ ≤ 1 / 2 :=
        hℓ_mem.2.trans ((min_le_left _ _).trans (hδ_half : P.δ_star ≤ 1 / 2))
      exact hArcAt hc'_Qenv h_c12 hς_arc' hR_ub (zero_le_one.trans hL_lb) hℓ_nn hℓ_half hg hYV_env hk0
    hArc_cov := fun k ℓ hk0 _ hℓ_mem => by
      have hℓ_pos : 0 < ℓ :=
        lt_of_lt_of_le (mul_pos hD_1 (Real.rpow_pos_of_pos hc'_pos _)) hℓ_mem.1
      have hle := virasoroArcCov_le (c' := c') (T := T)
        ((by norm_num : (10 : ℝ) ≤ 48).trans hR_48) (zero_le_one.trans hL_lb) hℓ_pos g hk0
      have hCa : μ₀ * virasoroArcCovConst ≤ P.C_a := le_max_left _ _
      calc μ₀ * virasoroArcCov c' R T L ℓ g k
          ≤ μ₀ * (virasoroArcCovConst * L * (√R)⁻¹ *
              ((2 : ℝ) ^ (k + 1) * Real.Gamma ((k : ℝ) + 1 / 2) *
                (π / (4 * ℓ * √R)) ^ ((k : ℝ) + 1 / 2))) :=
            mul_le_mul_of_nonneg_left hle hμ₀.le
        _ = (μ₀ * virasoroArcCovConst) * L * (√R)⁻¹ *
              ((2 : ℝ) ^ (k + 1) * Real.Gamma ((k : ℝ) + 1 / 2) *
                (π / (4 * ℓ * √R)) ^ ((k : ℝ) + 1 / 2)) := by ring
        _ ≤ P.C_a * L * (√R)⁻¹ *
              ((2 : ℝ) ^ (k + 1) * Real.Gamma ((k : ℝ) + 1 / 2) *
                (π / (4 * ℓ * √R)) ^ ((k : ℝ) + 1 / 2)) := by
            have hL0 : 0 ≤ L := zero_le_one.trans hL_lb
            have hGam : 0 < Real.Gamma ((k : ℝ) + 1 / 2) := Real.Gamma_pos_of_pos (by positivity)
            have hX : 0 ≤ (2 : ℝ) ^ (k + 1) * Real.Gamma ((k : ℝ) + 1 / 2) *
                (π / (4 * ℓ * √R)) ^ ((k : ℝ) + 1 / 2) := by positivity
            have hsq : 0 ≤ (√R)⁻¹ := by positivity
            gcongr
    hArc_unc := le_of_eq (by show μ₀ * (Q.arcUncConst * c' ^ (-(3 / 8 : ℝ))) =
        μ₀ * Q.arcUncConst * c' ^ (-(3 / 8 : ℝ)); ring)
    hI_line := fun k ℓ hk0 hkR hℓ_mem => by
      have hℓ_nn : 0 ≤ ℓ := (mul_nonneg P.hD1 (Real.rpow_nonneg hc'_pos.le _)).trans hℓ_mem.1
      have hℓ_half : ℓ ≤ 1 / 2 :=
        hℓ_mem.2.trans ((min_le_left _ _).trans (hδ_half : P.δ_star ≤ 1 / 2))
      have hlb := line_boundW_thr (A_thr := A_thr) (by linarith) hc'_Qenv (Q.sigma_nonneg hc'_ge1) hς_half
        (by linarith) (by linarith) hR_ub hℓ_nn hℓ_half hg hT_lo_m1 hT_hi_AThr hk0 hkR
      have hCa : lineCaW A_thr + 3 * Q.C0 ≤ P.C_a :=
        (by linarith : lineCaW A_thr + 3 * Q.C0 ≤ C_line + 3 * Q.C0).trans (le_max_right _ _)
      have h_ca_term : (lineCaW A_thr + 3 * Q.C0) * ((k : ℝ) + 1) / R ≤
          P.C_a * ((k : ℝ) + 1) / R := by gcongr
      have h_exp_le : deltaLobe prob Q.D.r_1 c' g ≤ C_gap * c' * Real.exp (-P.κ * c') := by
        have hκ_eq : P.κ = κ_gap := rfl
        rw [hκ_eq]
        calc deltaLobe prob Q.D.r_1 c' g ≤ C_gap * Real.exp (-κ_gap * c') := hdl_bd_full
          _ = 1 * (C_gap * Real.exp (-κ_gap * c')) := (one_mul _).symm
          _ ≤ c' * (C_gap * Real.exp (-κ_gap * c')) :=
              mul_le_mul_of_nonneg_right hc'_ge1 (mul_nonneg hC_gap.le (Real.exp_pos _).le)
          _ = C_gap * c' * Real.exp (-κ_gap * c') := by ring
      linarith
    hW_top := hW_nn
    hP_nodes_lb_hb := fun k ℓ hk0 hkR hℓ_mem => by
      simpa using hPN.1 k ℓ hk0 hkR hℓ_mem
    P_theta_bound := fun hk0_R hℓ_mem => by
      simpa using hPN.2 hk0_R hℓ_mem
  }, le_rfl, rfl, rfl⟩

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.clarkArcData_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clarkArcData_exists

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.bootstrapHB_of_YVForClark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bootstrapHB_of_YVForClark

end FormalResearch.ModularBootstrap.FixedWeightBand
