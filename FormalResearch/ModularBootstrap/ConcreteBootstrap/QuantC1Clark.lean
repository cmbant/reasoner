module

public import FormalResearch.ModularBootstrap.ConcreteBootstrap.QuantC1ClarkCompact
public import FormalResearch.ModularBootstrap.TwoLevel.A2StarCurve

/-!
# `TE.0'` for the Clark pairs (type II), uniform in the first level

Source: `CFT/common/two_edge_bootstrap.tex`, Proposition `TE.0'` (`teb:quant_c1_hb`) for the
constant Hermite--Biehler pairs `(P, Q) = (cos α, -sin α)`, `N = ψ_α`, `m₀ = 2`, `t_j = z_j(α)`,
in the form Step 2 of Theorem FT-L.FW (`lower_o1_two_edge.tex`, `wone:ftlfw`) uses, with
`r_∞ = 0` and `η_tr = δ_lobe`. The Clark pair is labelled by `γ = cot α`; the nodes are
`airyClarkNode γ j`. The first level `u₁ = z₁ = airyClarkNode γ 1` ranges over a compact subset
of `(a₁, ∞)` (equivalently `γ` over a compact subset of `ℝ`), which is the parametrisation of
`wone:genlower`(2) that stays compact near `α = ±π/2`.

The proof mirrors `teb_quant_c1_typeII` (sequence argument with `(c'_n, γ_n) → (∞, γ_∞)`,
Arzelà--Ascoli on `ℂ`), closing with the Clark two-node equality case instead of `airy_sign_equality`.

* `QuantC1ClarkHyp` (`QuantC1ClarkBasic`): admissible test functions, one prescribed node near `z₁`.
* `QuantC1B2HoldsClark`: the conclusion (`x̃ ≤ η₀`, `|Ψ'| ≤ C₁` at both nodes, `Ψ' ≤ -2κ_*` near
  `z₂`), analogous to `QuantC1B2Holds`.
* `teb_quant_c1_clark_typeII`: the statement, uniform for `γ` in a compact set.
* `teb_quant_c1_clark_typeII_firstLevel`: the same with `u₁` in a compact subset of `(a₁, ∞)`.
* `quantC1ClarkB2_secant_lower`: the `θ`-slope bound `Ψ(z₂ + θ x̃) ≥ 2κ_*(1 - θ) x̃`.

Constants `δ_*, κ_*, C₁` are not explicit: they are produced by the compactness argument and depend
only on `(C_0, K)` and the asymptotics `R_dom, ς, δ_lobe, ρ`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.ConcreteBootstrap

open FormalResearch.Special FormalResearch.SignUncertainty

/-! ### The conclusion -/

/-- The `(B2_HB)` conclusions of `TE.0'` at `m₀ = 2` for the Clark pair `γ`: `x̃ = u_T - z₂ ≤ η₀`
(with `η₀ = δ`), `|Ψ'| ≤ C₁` on `[z_j - 1, z_j + 1]` (`j = 1, 2`) and `Re Ψ' ≤ -2κ` on
`[z₂ - δ, z₂ + δ]`. -/
structure QuantC1B2HoldsClark (γ δ κ C₁ : ℝ) (Ψ : ℂ → ℂ) (u_T : ℝ) : Prop where
  xtilde_le : u_T - airyClarkNode γ 2 ≤ min δ 1
  deriv_le_one : ∀ x ∈ Icc (airyClarkNode γ 1 - 1) (airyClarkNode γ 1 + 1),
    ‖deriv Ψ (x : ℂ)‖ ≤ C₁
  deriv_le_two : ∀ x ∈ Icc (airyClarkNode γ 2 - 1) (airyClarkNode γ 2 + 1),
    ‖deriv Ψ (x : ℂ)‖ ≤ C₁
  slope : ∀ x ∈ Icc (airyClarkNode γ 2 - δ) (airyClarkNode γ 2 + δ),
    (deriv Ψ (x : ℂ)).re ≤ -2 * κ

/-! ### Stage 1: the violator threshold approaches `z₂` -/

/-- For every `ε > 0` and compact `K`, eventually `x̃ = u_T - z₂(γ) ≤ ε` uniformly. -/
theorem clark_uT_close {C_0 : ℝ} (hC0 : 0 < C_0)
    (R_dom ς δ_lobe ρ : ℝ → ℝ)
    (hR_lim : Tendsto R_dom atTop atTop)
    (hς_nn : ∀ᶠ c in atTop, 0 ≤ ς c) (hς_lim : Tendsto ς atTop (𝓝 0))
    (hδ_nn : ∀ᶠ c in atTop, 0 ≤ δ_lobe c) (hδ_lim : Tendsto δ_lobe atTop (𝓝 0))
    (hρ_lim : Tendsto ρ atTop (𝓝 0))
    {Kc : Set ℝ} (hK : IsCompact Kc) {ε : ℝ} (hε : 0 < ε) :
    ∃ c₁ : ℝ, 2 ≤ c₁ ∧ ∀ c' : ℝ, c₁ ≤ c' → ∀ γ ∈ Kc, ∀ (Ψ : ℂ → ℂ) (u_T ũ : ℝ),
      QuantC1ClarkHyp C_0 (R_dom c') (ς c') (δ_lobe c') (ρ c') γ Ψ u_T ũ →
      u_T - airyClarkNode γ 2 ≤ ε := by
  by_contra h_none
  push Not at h_none
  have hex : ∀ n : ℕ, ∃ c' : ℝ, max (n : ℝ) 2 ≤ c' ∧ ∃ γ ∈ Kc, ∃ (Ψ : ℂ → ℂ) (u_T ũ : ℝ),
      QuantC1ClarkHyp C_0 (R_dom c') (ς c') (δ_lobe c') (ρ c') γ Ψ u_T ũ ∧
        ε < u_T - airyClarkNode γ 2 := fun n => h_none (max (n : ℝ) 2) (le_max_right _ _)
  choose c'_seq hc'_ge γ_seq hγK Ψ_seq uT_seq ũ_seq hspec hbig using hex
  have hc'_atTop : Tendsto c'_seq atTop atTop :=
    tendsto_atTop_mono (fun n => (le_max_left (n : ℝ) 2).trans (hc'_ge n)) tendsto_natCast_atTop_atTop
  obtain ⟨θ, γlim, Φ, α, c, hθ, -, hγt, hα, hnodes, hc, hΦ, -, hunif, -⟩ :=
    clark_compactness hC0 R_dom ς δ_lobe ρ hR_lim hς_nn hς_lim hδ_nn hδ_lim hρ_lim hK hc'_atTop
      hγK hspec
  have hz12 : airyClarkNode γlim 2 < airyClarkNode γlim 1 := by
    rw [← hnodes, ← hnodes]; exact clarkNode_two_lt_one α
  set z1 := airyClarkNode γlim 1 with hz1
  set z2 := airyClarkNode γlim 2 with hz2
  set x₀ : ℝ := z2 + min ε (z1 - z2) / 2 with hx₀
  have hmin_pos : 0 < min ε (z1 - z2) := lt_min hε (by linarith)
  have hx0_gt : z2 < x₀ := by rw [hx₀]; linarith
  have hx0_lt : x₀ < z1 := by
    have := min_le_right ε (z1 - z2)
    rw [hx₀]; linarith
  have hx0_le_eps : x₀ ≤ z2 + ε / 2 := by
    have := min_le_left ε (z1 - z2)
    rw [hx₀]; linarith
  have hΦx0 : (Φ (x₀ : ℂ)).re < 0 := by
    rw [hΦ, Complex.re_ofReal_mul]
    refine mul_neg_of_pos_of_neg hc (clarkExtremal_neg_between hα ?_ ?_)
    · rw [hnodes]; exact hx0_gt
    · rw [hnodes]; exact hx0_lt
  set m : ℕ := ⌈|x₀|⌉₊ with hm
  have hx0_m : (x₀ : ℂ) ∈ closedBall (0 : ℂ) ((m : ℝ) + 1) := by
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    linarith [Nat.le_ceil |x₀|]
  have ht : Tendsto (fun k => (Ψ_seq (θ k) (x₀ : ℂ)).re) atTop (𝓝 (Φ (x₀ : ℂ)).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp ((hunif m).tendsto_at hx0_m)
  have hev_neg : ∀ᶠ k in atTop, (Ψ_seq (θ k) (x₀ : ℂ)).re < 0 := ht (Iio_mem_nhds hΦx0)
  have hz2t : Tendsto (fun k => airyClarkNode (γ_seq (θ k)) 2) atTop (𝓝 z2) :=
    ((continuous_airyClarkNode (n := 2) (by norm_num)).tendsto γlim).comp hγt
  have hev_z2 : ∀ᶠ k in atTop, z2 - ε / 2 < airyClarkNode (γ_seq (θ k)) 2 :=
    hz2t (Ioi_mem_nhds (by linarith))
  have hev_R : ∀ᶠ k in atTop, |x₀| ≤ R_dom (c'_seq (θ k)) :=
    (hR_lim.comp (hc'_atTop.comp hθ.tendsto_atTop)).eventually (eventually_ge_atTop _)
  obtain ⟨k, hk⟩ := (hev_neg.and (hev_z2.and hev_R)).exists
  obtain ⟨hk_neg, hk_z2, hk_R⟩ := hk
  have hbig' := hbig (θ k)
  have hx0_uT : x₀ ≤ uT_seq (θ k) := by linarith
  have hx0_lo : -R_dom (c'_seq (θ k)) ≤ x₀ := by linarith [neg_abs_le x₀]
  exact absurd ((hspec (θ k)).nonneg x₀ ⟨hx0_lo, hx0_uT⟩) hk_neg.not_ge

/-! ### Stage 2: uniform slope at `z₂` -/

/-- There are `δ, κ > 0` (uniform in `γ ∈ K`) with `Re Ψ' ≤ -2κ` on `[z₂ - δ, z₂ + δ]`. -/
theorem clark_slope_uniform {C_0 : ℝ} (hC0 : 0 < C_0)
    (R_dom ς δ_lobe ρ : ℝ → ℝ)
    (hR_lim : Tendsto R_dom atTop atTop)
    (hς_nn : ∀ᶠ c in atTop, 0 ≤ ς c) (hς_lim : Tendsto ς atTop (𝓝 0))
    (hδ_nn : ∀ᶠ c in atTop, 0 ≤ δ_lobe c) (hδ_lim : Tendsto δ_lobe atTop (𝓝 0))
    (hρ_lim : Tendsto ρ atTop (𝓝 0))
    {Kc : Set ℝ} (hK : IsCompact Kc) :
    ∃ δ κ : ℝ, 0 < δ ∧ 0 < κ ∧ ∃ c₁ : ℝ, 2 ≤ c₁ ∧ ∀ c' : ℝ, c₁ ≤ c' → ∀ γ ∈ Kc,
      ∀ (Ψ : ℂ → ℂ) (u_T ũ : ℝ),
      QuantC1ClarkHyp C_0 (R_dom c') (ς c') (δ_lobe c') (ρ c') γ Ψ u_T ũ →
      ∀ x : ℝ, x ∈ Icc (airyClarkNode γ 2 - δ) (airyClarkNode γ 2 + δ) →
        (deriv Ψ (x : ℂ)).re ≤ -2 * κ := by
  by_contra h_none
  push Not at h_none
  have hex : ∀ n : ℕ, ∃ c' : ℝ, max (n : ℝ) 2 ≤ c' ∧ ∃ γ ∈ Kc, ∃ (Ψ : ℂ → ℂ) (u_T ũ : ℝ),
      QuantC1ClarkHyp C_0 (R_dom c') (ς c') (δ_lobe c') (ρ c') γ Ψ u_T ũ ∧
        ∃ x : ℝ, x ∈ Icc (airyClarkNode γ 2 - 1 / ((n : ℝ) + 1)) (airyClarkNode γ 2 + 1 / ((n : ℝ) + 1)) ∧
          -2 * (1 / ((n : ℝ) + 1)) < (deriv Ψ (x : ℂ)).re := fun n =>
    h_none (1 / ((n : ℝ) + 1)) (1 / ((n : ℝ) + 1)) (by positivity) (by positivity)
      (max (n : ℝ) 2) (le_max_right _ _)
  choose c'_seq hc'_ge γ_seq hγK Ψ_seq uT_seq ũ_seq hspec x_seq hx_mem hx_slope using hex
  have hc'_atTop : Tendsto c'_seq atTop atTop :=
    tendsto_atTop_mono (fun n => (le_max_left (n : ℝ) 2).trans (hc'_ge n)) tendsto_natCast_atTop_atTop
  obtain ⟨θ, γlim, Φ, α, c, hθ, -, hγt, hα, hnodes, hc, hΦ, hΦd, hunif, hAn⟩ :=
    clark_compactness hC0 R_dom ς δ_lobe ρ hR_lim hς_nn hς_lim hδ_nn hδ_lim hρ_lim hK hc'_atTop
      hγK hspec
  set z2 := airyClarkNode γlim 2 with hz2
  have hz2t : Tendsto (fun k => airyClarkNode (γ_seq (θ k)) 2) atTop (𝓝 z2) :=
    ((continuous_airyClarkNode (n := 2) (by norm_num)).tendsto γlim).comp hγt
  have hinv : Tendsto (fun k => 1 / (((θ k : ℕ) : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => (((θ k : ℕ) : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp hθ.tendsto_atTop)
    have h2 : Tendsto (fun k => ((((θ k : ℕ) : ℝ) + 1))⁻¹) atTop (𝓝 0) := h1.inv_tendsto_atTop
    simpa [one_div] using h2
  have hdiff0 : Tendsto (fun k => x_seq (θ k) - airyClarkNode (γ_seq (θ k)) 2) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => ?_) hinv
    have := hx_mem (θ k)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [this.1, this.2]
  have hxt : Tendsto (fun k => x_seq (θ k)) atTop (𝓝 z2) := by
    simpa using hdiff0.add hz2t
  have hw : Tendsto (fun k => ((x_seq (θ k) : ℝ) : ℂ)) atTop (𝓝 ((z2 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hxt
  have hder := clark_deriv_tendsto_comp (F := Ψ_seq) hunif hAn hΦd hw
  have hder_re := Complex.continuous_re.continuousAt.tendsto.comp hder
  have hlow : Tendsto (fun k => -2 * (1 / (((θ k : ℕ) : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using hinv.const_mul (-2)
  have hge : 0 ≤ (deriv Φ ((z2 : ℝ) : ℂ)).re :=
    le_of_tendsto_of_tendsto' hlow hder_re fun k => (hx_slope (θ k)).le
  have hΦfun : Φ = fun u : ℂ => (c : ℂ) * clarkExtremal α u := funext hΦ
  have hderΦ : deriv Φ ((z2 : ℝ) : ℂ) = (c : ℂ) * deriv (clarkExtremal α) ((z2 : ℝ) : ℂ) := by
    rw [hΦfun]
    exact (((differentiable_clarkExtremal α) _).hasDerivAt.const_mul (c : ℂ)).deriv
  have hz2α : z2 = clarkNode α 2 := (hnodes 2).symm
  have hneg := clarkExtremal_deriv_two_re_neg hα
  rw [hderΦ, Complex.re_ofReal_mul, hz2α] at hge
  exact absurd hge (not_le.mpr (mul_neg_of_pos_of_neg hc hneg))

/-! ### Stage 3: derivative bound at the nodes (Cauchy estimate) -/

/-- Explicit Cauchy bound for `|Ψ'|` near the nodes, uniform in `γ ∈ K`. -/
theorem clark_deriv_bound {C_0 : ℝ} (hC0 : 0 < C_0)
    (R_dom ς : ℝ → ℝ)
    (hR_lim : Tendsto R_dom atTop atTop)
    (hς_nn : ∀ᶠ c in atTop, 0 ≤ ς c) (hς_lim : Tendsto ς atTop (𝓝 0))
    {Kc : Set ℝ} (hK : IsCompact Kc) (δ_lobe ρ : ℝ → ℝ) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ c₁ : ℝ, 2 ≤ c₁ ∧ ∀ c' : ℝ, c₁ ≤ c' → ∀ γ ∈ Kc,
      ∀ (Ψ : ℂ → ℂ) (u_T ũ : ℝ),
      QuantC1ClarkHyp C_0 (R_dom c') (ς c') (δ_lobe c') (ρ c') γ Ψ u_T ũ →
      (∀ x ∈ Icc (airyClarkNode γ 1 - 1) (airyClarkNode γ 1 + 1), ‖deriv Ψ (x : ℂ)‖ ≤ C₁) ∧
      (∀ x ∈ Icc (airyClarkNode γ 2 - 1) (airyClarkNode γ 2 + 1), ‖deriv Ψ (x : ℂ)‖ ≤ C₁) := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (continuous_airyClarkNode (n := 1) le_rfl).continuousOn
  set R₁ : ℝ := max B 0 + |airyZero 2| + 1 with hR₁
  have hR₁_nn : 0 ≤ R₁ := by positivity
  set M : ℝ := 8 * Real.exp (7 / 2) * C_0 * (1 + (R₁ + 1)) ^ (1 / 2 : ℝ) *
    Real.exp ((4 / 3 : ℝ) * (R₁ + 1) ^ (3 / 2 : ℝ)) with hM
  have hM_nn : 0 ≤ M := by positivity
  refine ⟨M + 1, by linarith, ?_⟩
  have hev : ∀ᶠ c in atTop, R₁ + 3 ≤ R_dom c ∧ 0 ≤ ς c ∧ ς c * √((R₁ + 1) + 2) ≤ 1 := by
    have h1 : ∀ᶠ c in atTop, R₁ + 3 ≤ R_dom c := hR_lim (eventually_ge_atTop _)
    have h2 : ∀ᶠ c in atTop, ς c * √((R₁ + 1) + 2) ≤ 1 := by
      have ht : Tendsto (fun c => ς c * √((R₁ + 1) + 2)) atTop (𝓝 (0 * √((R₁ + 1) + 2))) :=
        hς_lim.mul_const _
      rw [zero_mul] at ht
      exact ht (Iic_mem_nhds one_pos)
    exact h1.and (hς_nn.and h2)
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hev
  refine ⟨max c₀ 2, le_max_right _ _, fun c' hc' γ hγ Ψ u_T ũ hΨ => ?_⟩
  obtain ⟨hRc, hςc, hςs⟩ := hc₀ c' ((le_max_left _ _).trans hc')
  have hbd : ∀ u ∈ closedBall (0 : ℂ) (R₁ + 1), ‖Ψ u‖ ≤ M := fun u hu =>
    typeII_cut_bound (R₁ := R₁ + 1) (by linarith) (by linarith) hC0 hςc
      hΨ.analytic hΨ.env hςs hu
  have hAn : AnalyticOnNhd ℂ Ψ (closedBall (0 : ℂ) (R₁ + 1)) :=
    hΨ.analytic.mono (closedBall_subset_closedBall (by linarith))
  have hcau : ∀ x : ℝ, |x| ≤ R₁ → ‖deriv Ψ (x : ℂ)‖ ≤ M + 1 := fun x hx => by
    have hmem : (x : ℂ) ∈ closedBall (0 : ℂ) R₁ := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hx
    have := (typeII_cauchy_deriv_bounds hAn hM_nn hbd hmem).1
    linarith
  have hz1_bd : |airyClarkNode γ 1| ≤ max B 0 := by
    have := hB γ hγ
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hz2_bd : |airyClarkNode γ 2| ≤ |airyZero 2| := by
    have h1 := airyZero_lt_airyClarkNode (n := 2) (by norm_num) γ
    have h2 := airyClarkNode_lt_airyZero (n := 2) (by norm_num) γ
    have ha2 : airyZero 2 < 0 := airyZero_neg 2
    have ha1 : airyZero (2 - 1) < 0 := airyZero_neg 1
    rw [abs_le]
    constructor
    · rw [abs_of_neg ha2]; linarith
    · linarith [abs_nonneg (airyZero 2), neg_abs_le (airyZero 2)]
  refine ⟨fun x hx => hcau x ?_, fun x hx => hcau x ?_⟩
  · rw [abs_le] at hz1_bd ⊢
    constructor <;> linarith [hx.1, hx.2, hz1_bd.1, hz1_bd.2, abs_nonneg (airyZero 2)]
  · rw [abs_le] at hz2_bd ⊢
    constructor <;> linarith [hx.1, hx.2, hz2_bd.1, hz2_bd.2, le_max_right B 0]

/-! ### The theorem -/

/-- **Proposition `TE.0'` for the Clark pairs, type (II), uniform in the first level**
(`two_edge_bootstrap.tex`, `teb:quant_c1_hb` at `(P, Q) = (cos α, -sin α)`, `m₀ = 2`, `r_∞ = 0`;
Step 2 of `wone:ftlfw`). For every compact `K ⊂ ℝ` of Clark labels `γ = cot α` (equivalently of
first levels `z₁(γ)`), there are `δ_*, κ_*, C₁ > 0` and `c₁ ≥ 2` such that every admissible `Ψ`
(`QuantC1ClarkHyp`: type-(II) envelope, `Ψ ≥ 0` left of the violator threshold `u_T > z₂(γ)`, the
mass conditions, and `Ψ(ũ) ≥ 0` at one point `ũ` with `|ũ - z₁(γ)| ≤ ρ(c')`, `ρ → 0`) with
`c' ≥ c₁` obeys `QuantC1B2HoldsClark`. -/
theorem teb_quant_c1_clark_typeII {C_0 : ℝ} (hC0 : 0 < C_0)
    (R_dom ς δ_lobe ρ : ℝ → ℝ)
    (hR_lim : Tendsto R_dom atTop atTop)
    (hς_nn : ∀ᶠ c in atTop, 0 ≤ ς c) (hς_lim : Tendsto ς atTop (𝓝 0))
    (hδ_nn : ∀ᶠ c in atTop, 0 ≤ δ_lobe c) (hδ_lim : Tendsto δ_lobe atTop (𝓝 0))
    (hρ_lim : Tendsto ρ atTop (𝓝 0))
    {Kc : Set ℝ} (hK : IsCompact Kc) :
    ∃ δ_star κ_star C₁ : ℝ, 0 < δ_star ∧ δ_star ≤ 1 / 2 ∧ 0 < κ_star ∧ 0 < C₁ ∧
      ∃ c₁ : ℝ, 2 ≤ c₁ ∧ ∀ c' : ℝ, c₁ ≤ c' → ∀ γ ∈ Kc, ∀ (Ψ : ℂ → ℂ) (u_T ũ : ℝ),
        QuantC1ClarkHyp C_0 (R_dom c') (ς c') (δ_lobe c') (ρ c') γ Ψ u_T ũ →
        QuantC1B2HoldsClark γ δ_star κ_star C₁ Ψ u_T := by
  obtain ⟨δ, κ, hδ, hκ, c_s, hc_s, hslope⟩ :=
    clark_slope_uniform hC0 R_dom ς δ_lobe ρ hR_lim hς_nn hς_lim hδ_nn hδ_lim hρ_lim hK
  obtain ⟨C₁, hC₁, c_d, hc_d, hderiv⟩ :=
    clark_deriv_bound hC0 R_dom ς hR_lim hς_nn hς_lim hK δ_lobe ρ
  set δ_star : ℝ := min δ (1 / 2) with hδ_star
  have hδs_pos : 0 < δ_star := lt_min hδ (by norm_num)
  obtain ⟨c_u, hc_u, hclose⟩ :=
    clark_uT_close hC0 R_dom ς δ_lobe ρ hR_lim hς_nn hς_lim hδ_nn hδ_lim hρ_lim hK
      (ε := min δ_star 1) (lt_min hδs_pos one_pos)
  refine ⟨δ_star, κ, C₁, hδs_pos, min_le_right _ _, hκ, hC₁, max (max c_s c_d) c_u,
    (hc_s.trans (le_max_left _ _)).trans (le_max_left _ _), fun c' hc' γ hγ Ψ u_T ũ hΨ => ?_⟩
  have hc_s' : c_s ≤ c' := ((le_max_left _ _).trans (le_max_left _ _)).trans hc'
  have hc_d' : c_d ≤ c' := ((le_max_right _ _).trans (le_max_left _ _)).trans hc'
  have hc_u' : c_u ≤ c' := (le_max_right _ _).trans hc'
  obtain ⟨hd1, hd2⟩ := hderiv c' hc_d' γ hγ Ψ u_T ũ hΨ
  exact ⟨hclose c' hc_u' γ hγ Ψ u_T ũ hΨ, hd1, hd2, fun x hx =>
    hslope c' hc_s' γ hγ Ψ u_T ũ hΨ x
      ⟨by linarith [hx.1, min_le_left δ (1 / 2 : ℝ)], by linarith [hx.2, min_le_left δ (1 / 2 : ℝ)]⟩⟩

/-! ### The `θ`-slope bound -/

/-- From `QuantC1B2HoldsClark`, reality and nonnegativity at `u_T`, the slope bound of Step 2:
`2 κ_* (1 - θ) (u_T - z₂) ≤ Re Ψ(z₂ + θ (u_T - z₂))` for `θ ∈ [0, 1]`. -/
theorem quantC1ClarkB2_secant_lower {γ δ κ C₁ : ℝ} {Ψ : ℂ → ℂ} {u_T R_dom : ℝ}
    (hδ : 0 < δ) (hδ_half : δ ≤ 1 / 2)
    (hR : |airyClarkNode γ 2| + 1 ≤ R_dom)
    (hΨ_an : AnalyticOnNhd ℂ Ψ (closedBall (0 : ℂ) R_dom))
    (huT_gt : airyClarkNode γ 2 < u_T) (huT_pos : 0 ≤ (Ψ (u_T : ℂ)).re)
    (hB2 : QuantC1B2HoldsClark γ δ κ C₁ Ψ u_T)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    2 * κ * (1 - θ) * (u_T - airyClarkNode γ 2) ≤
      (Ψ ((airyClarkNode γ 2 + θ * (u_T - airyClarkNode γ 2) : ℝ) : ℂ)).re := by
  set a₁ : ℝ := airyClarkNode γ 2 with ha₁
  have hx_le : u_T - a₁ ≤ δ := hB2.xtilde_le.trans (min_le_left _ _)
  set x_θ : ℝ := a₁ + θ * (u_T - a₁) with hxθ
  have hx_ge_a1 : a₁ ≤ x_θ := by rw [hxθ]; nlinarith
  have hx_le_uT : x_θ ≤ u_T := by rw [hxθ]; nlinarith
  have huT_le_hi : u_T ≤ a₁ + δ := by linarith
  have hsub_band : Icc x_θ u_T ⊆ Icc (a₁ - δ) (a₁ + δ) := fun x hx =>
    ⟨by linarith [hx.1], hx.2.trans huT_le_hi⟩
  have h_in_ball : ∀ x ∈ Icc (a₁ - δ) (a₁ + δ), (x : ℂ) ∈ ball (0 : ℂ) R_dom := fun x hx => by
    have h2 : |x| ≤ |a₁| + δ := by
      have : |x - a₁| ≤ δ := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
      calc |x| = |(x - a₁) + a₁| := by ring_nf
        _ ≤ |x - a₁| + |a₁| := abs_add_le _ _
        _ ≤ |a₁| + δ := by linarith
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hderiv : ∀ x ∈ Set.uIcc x_θ u_T,
      HasDerivAt (fun t : ℝ => (Ψ (t : ℂ)).re) ((deriv Ψ (x : ℂ)).re) x := by
    intro x hx
    rw [Set.uIcc_of_le hx_le_uT] at hx
    have hx_ball := h_in_ball x (hsub_band hx)
    have hd_C := ((hΨ_an (x : ℂ) (ball_subset_closedBall hx_ball)).differentiableAt.hasDerivAt).comp_ofReal
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd_C
  have hcont_deriv : ContinuousOn (fun x : ℝ => (deriv Ψ (x : ℂ)).re) (Icc x_θ u_T) := by
    have h_an_deriv : AnalyticOnNhd ℂ (deriv Ψ) (ball (0 : ℂ) R_dom) :=
      (hΨ_an.mono ball_subset_closedBall).deriv
    refine Complex.continuous_re.comp_continuousOn ?_
    exact h_an_deriv.continuousOn.comp continuous_ofReal.continuousOn fun x hx =>
      h_in_ball x (hsub_band hx)
  have hev := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont_deriv.intervalIntegrable_of_Icc hx_le_uT)
  have hint_le : ∫ x in x_θ..u_T, (deriv Ψ (x : ℂ)).re ≤
      ∫ _ in x_θ..u_T, (-2 * κ) := by
    refine intervalIntegral.integral_mono_on hx_le_uT
      (hcont_deriv.intervalIntegrable_of_Icc hx_le_uT)
      intervalIntegrable_const fun x hx => ?_
    exact hB2.slope x (hsub_band hx)
  rw [hev, intervalIntegral.integral_const, smul_eq_mul] at hint_le
  have hdiff : u_T - x_θ = (1 - θ) * (u_T - a₁) := by rw [hxθ]; ring
  rw [hdiff] at hint_le
  linarith

/-! ### Parametrisation by the first level `u₁ ∈ K ⊂ (a₁, ∞)` -/

/-- `z₁(cot α(u₁)) = u₁` for `u₁ > a₁`, in the `γ = Ai'(u₁)/Ai(u₁)` labelling. -/
lemma airyClarkNode_airyRatio_one {u : ℝ} (hu : airyZero 1 < u) :
    airyClarkNode (airyRatio u) 1 = u :=
  airyClarkNode_ratio le_rfl (by rw [airyClarkGap_one]; exact hu)

/-- `z₂(γ(u₁)) = z₂(α(u₁))` of `TwoLevel.A2StarCurve`. -/
lemma airyClarkNode_airyRatio_two {u : ℝ} (hu : airyZero 1 < u) :
    airyClarkNode (airyRatio u) 2 = clarkNode (TwoLevel.clarkAngle u) 2 :=
  (TwoLevel.clarkNode_two_eq_airyClarkNode_ratio hu).symm

/-- **`TE.0'` for the Clark pairs, uniform for the first level in a compact subset of `(a₁, ∞)`**:
`teb_quant_c1_clark_typeII` with `γ = Ai'(u₁)/Ai(u₁)`, so that `z₁ = u₁` and
`z₂ = z₂(α(u₁))` (`airyClarkNode_airyRatio_one`, `airyClarkNode_airyRatio_two`). -/
theorem teb_quant_c1_clark_typeII_firstLevel {C_0 : ℝ} (hC0 : 0 < C_0)
    (R_dom ς δ_lobe ρ : ℝ → ℝ)
    (hR_lim : Tendsto R_dom atTop atTop)
    (hς_nn : ∀ᶠ c in atTop, 0 ≤ ς c) (hς_lim : Tendsto ς atTop (𝓝 0))
    (hδ_nn : ∀ᶠ c in atTop, 0 ≤ δ_lobe c) (hδ_lim : Tendsto δ_lobe atTop (𝓝 0))
    (hρ_lim : Tendsto ρ atTop (𝓝 0))
    {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Ioi (airyZero 1)) :
    ∃ δ_star κ_star C₁ : ℝ, 0 < δ_star ∧ δ_star ≤ 1 / 2 ∧ 0 < κ_star ∧ 0 < C₁ ∧
      ∃ c₁ : ℝ, 2 ≤ c₁ ∧ ∀ c' : ℝ, c₁ ≤ c' → ∀ u₁ ∈ K, ∀ (Ψ : ℂ → ℂ) (u_T ũ : ℝ),
        QuantC1ClarkHyp C_0 (R_dom c') (ς c') (δ_lobe c') (ρ c') (airyRatio u₁) Ψ u_T ũ →
        QuantC1B2HoldsClark (airyRatio u₁) δ_star κ_star C₁ Ψ u_T := by
  have hcont : ContinuousOn airyRatio K :=
    (continuousOn_airyRatio (n := 1) le_rfl).mono fun u hu => by
      rw [airyClarkGap_one]; exact hKsub hu
  obtain ⟨δ_star, κ_star, C₁, h1, h2, h3, h4, c₁, hc₁, h⟩ :=
    teb_quant_c1_clark_typeII hC0 R_dom ς δ_lobe ρ hR_lim hς_nn hς_lim hδ_nn hδ_lim hρ_lim
      (hK.image_of_continuousOn hcont)
  exact ⟨δ_star, κ_star, C₁, h1, h2, h3, h4, c₁, hc₁, fun c' hc' u₁ hu₁ Ψ u_T ũ hΨ =>
    h c' hc' (airyRatio u₁) (mem_image_of_mem _ hu₁) Ψ u_T ũ hΨ⟩

/-! ### Axiom audit -/

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.continuous_airyClarkNode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.ConcreteBootstrap.continuous_airyClarkNode

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.clarkNode_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.ConcreteBootstrap.clarkNode_uniform

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.clarkExtremal_deriv_two_re_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.ConcreteBootstrap.clarkExtremal_deriv_two_re_neg

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.clark_limit_extraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.ConcreteBootstrap.clark_limit_extraction

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.clark_uT_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.ConcreteBootstrap.clark_uT_close

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.clark_slope_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.ConcreteBootstrap.clark_slope_uniform

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.clark_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.ConcreteBootstrap.clark_deriv_bound

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.clark_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.ConcreteBootstrap.clark_compactness

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.teb_quant_c1_clark_typeII' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.ConcreteBootstrap.teb_quant_c1_clark_typeII

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.teb_quant_c1_clark_typeII_firstLevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.ConcreteBootstrap.teb_quant_c1_clark_typeII_firstLevel

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.quantC1ClarkB2_secant_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.ConcreteBootstrap.quantC1ClarkB2_secant_lower

end FormalResearch.ModularBootstrap.ConcreteBootstrap
