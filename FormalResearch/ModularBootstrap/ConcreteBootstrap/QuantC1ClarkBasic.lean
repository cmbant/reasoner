module

public import FormalResearch.ModularBootstrap.ConcreteBootstrap.QuantC1ClarkHelpers
public import FormalResearch.SignUncertainty.ClarkTwoNode

/-!
# Clark `TE.0'`: hypotheses, node continuity and the slope of the extremal at `z₂`

Source: `CFT/common/two_edge_bootstrap.tex`, Proposition `TE.0'` (`teb:quant_c1_hb`) for the constant
Hermite--Biehler pairs `(P, Q) = (cos α, -sin α)`, `N = ψ_α`, `m₀ = 2`, `t_j = z_j(α)`.
The Clark pair is labelled by `γ = cot α`, the nodes are `airyClarkNode γ j` (the zeros of
`Ai' - γ Ai`); `clarkNode α j = airyClarkNode (cot α) j` (`FormalResearch.SignUncertainty`).

* `QuantC1ClarkHyp`: the admissible test functions (type-(II) envelope, `(Q1)`, `(Q2_N)` with
  `r_∞ = 0`, one prescribed node at distance `≤ ρ` from `z₁`).
* `continuous_airyClarkNode`: `γ ↦ z_n(γ)` is continuous (WP-A0).
* `clarkNode_uniform`: uniform node gaps and bounds on a compact set of labels (WP-A0).
* `exists_clarkAngle_node`: every `γ` is `cot α` for some `α` with `sin α ≠ 0`.
* `clarkExtremal_deriv_two_re_neg`: `Re g_α'(z₂(α)) < 0`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.ConcreteBootstrap

open FormalResearch.Special FormalResearch.SignUncertainty

/-- Admissible test function for the Clark `TE.0'` (`r_∞ = 0`, `m₀ = 2`): `R = R_dom(c')` is the
domain radius, `ς` the type-(II) exponent, `δ` the transport defect `η_tr`, `γ = cot α` the Clark
label, `u_T = z₂ + x̃` a violator threshold (`x̃ > 0`) and `ũ` the prescribed point near `z₁`
with `ρ` the allowed offset. -/
structure QuantC1ClarkHyp (C_0 R ς δ ρ γ : ℝ) (Ψ : ℂ → ℂ) (u_T ũ : ℝ) : Prop where
  analytic : AnalyticOnNhd ℂ Ψ (closedBall (0 : ℂ) R)
  real : ∀ x ∈ Icc (-R) R, (Ψ (x : ℂ)).im = 0
  env : ∀ u ∈ closedBall (0 : ℂ) R, ¬ (u.im = 0 ∧ u.re ≤ 0) →
    ‖Ψ u‖ ≤ C_0 * airyEnv u * Real.exp (ς * (u ^ (1 / 2 : ℂ)).re) *
      ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹
  lt_uT : airyClarkNode γ 2 < u_T
  uT_le : u_T ≤ R
  nonneg : ∀ x ∈ Icc (-R) u_T, 0 ≤ (Ψ (x : ℂ)).re
  l1 : ∫ x in (-R)..R, ‖Ψ (x : ℂ)‖ ≤ 1 + δ
  tail : (1 / 2 : ℝ) - δ ≤ ∫ x in u_T..R, max 0 (-(Ψ (x : ℂ)).re)
  top : ∀ R' ∈ Icc (0 : ℝ) R, -R' ≤ u_T → ∫ x in (-R')..R, (Ψ (x : ℂ)).re ≤ δ
  node_near : |ũ - airyClarkNode γ 1| ≤ ρ
  node_nonneg : 0 ≤ (Ψ (ũ : ℂ)).re

/-- WP-A0: the Clark nodes `γ ↦ z_n(γ)` are continuous on `ℝ` (`n ≥ 1`). -/
theorem continuous_airyClarkNode {n : ℕ} (hn : 1 ≤ n) :
    Continuous (fun c : ℝ => airyClarkNode c n) := by
  have hmono : Monotone (fun c : ℝ => -airyClarkNode c n) := fun a b h =>
    neg_le_neg ((airyClarkNode_strictAnti hn).antitone h)
  have hrange : range (fun c : ℝ => -airyClarkNode c n) = (fun x : ℝ => -x) ⁻¹' airyClarkGap n := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      simpa using airyClarkNode_mem_gap hn c
    · intro hx
      have hx' : -x ∈ range (fun c : ℝ => airyClarkNode c n) := by
        rw [range_airyClarkNode hn]; exact hx
      obtain ⟨c, hc⟩ := hx'
      exact ⟨c, by simp only at hc ⊢; linarith⟩
  have hopen : IsOpen (range (fun c : ℝ => -airyClarkNode c n)) := by
    rw [hrange]; exact (isOpen_airyClarkGap n).preimage continuous_neg
  have hcont : Continuous (fun c : ℝ => -airyClarkNode c n) := by
    refine continuous_iff_continuousAt.2 fun a => ?_
    refine continuousAt_of_monotoneOn_of_image_mem_nhds (s := univ) (hmono.monotoneOn univ) univ_mem ?_
    rw [image_univ]
    exact hopen.mem_nhds ⟨a, rfl⟩
  exact hcont.neg.congr fun c => neg_neg _

/-- WP-A0: on a compact set of Clark labels the first three nodes stay a uniform positive distance
apart (`z₁ - z₂ ≥ g`, `z₂ - z₃ ≥ g`) and are uniformly bounded. -/
theorem clarkNode_uniform {Kc : Set ℝ} (hK : IsCompact Kc) :
    ∃ g B : ℝ, 0 < g ∧ ∀ γ ∈ Kc, g ≤ airyClarkNode γ 1 - airyClarkNode γ 2 ∧
      g ≤ airyClarkNode γ 2 - airyClarkNode γ 3 ∧
      |airyClarkNode γ 1| ≤ B ∧ |airyClarkNode γ 2| ≤ B ∧ |airyClarkNode γ 3| ≤ B := by
  rcases Kc.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 0, one_pos, fun γ hγ => absurd hγ (notMem_empty γ)⟩
  have h1 := continuous_airyClarkNode (n := 1) le_rfl
  have h2 := continuous_airyClarkNode (n := 2) (by norm_num)
  have h3 := continuous_airyClarkNode (n := 3) (by norm_num)
  obtain ⟨γ₁, hγ₁, hmin₁⟩ := hK.exists_isMinOn hne ((h1.sub h2).continuousOn)
  obtain ⟨γ₂, hγ₂, hmin₂⟩ := hK.exists_isMinOn hne ((h2.sub h3).continuousOn)
  have hpos₁ : 0 < airyClarkNode γ₁ 1 - airyClarkNode γ₁ 2 := by
    linarith [(airyClarkNode_succ_lt (n := 1) le_rfl γ₁).1, (airyClarkNode_succ_lt (n := 1) le_rfl γ₁).2]
  have hpos₂ : 0 < airyClarkNode γ₂ 2 - airyClarkNode γ₂ 3 := by
    linarith [(airyClarkNode_succ_lt (n := 2) (by norm_num) γ₂).1,
      (airyClarkNode_succ_lt (n := 2) (by norm_num) γ₂).2]
  obtain ⟨B₁, hB₁⟩ := hK.exists_bound_of_continuousOn h1.continuousOn
  refine ⟨min (airyClarkNode γ₁ 1 - airyClarkNode γ₁ 2) (airyClarkNode γ₂ 2 - airyClarkNode γ₂ 3),
    max B₁ 0 + |airyZero 2| + |airyZero 3|, lt_min hpos₁ hpos₂, fun γ hγ => ?_⟩
  have hz1 : |airyClarkNode γ 1| ≤ max B₁ 0 := by
    have := hB₁ γ hγ
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hz2 : |airyClarkNode γ 2| ≤ |airyZero 2| := by
    have a := airyZero_lt_airyClarkNode (n := 2) (by norm_num) γ
    have b := airyClarkNode_succ_lt (n := 1) le_rfl γ
    have ha1 := airyZero_neg 1
    have ha2 := airyZero_neg 2
    rw [abs_le]
    constructor
    · rw [abs_of_neg ha2]; linarith
    · linarith [abs_nonneg (airyZero 2), neg_abs_le (airyZero 2)]
  have hz3 : |airyClarkNode γ 3| ≤ |airyZero 3| := by
    have a := airyZero_lt_airyClarkNode (n := 3) (by norm_num) γ
    have b := airyClarkNode_succ_lt (n := 2) (by norm_num) γ
    have ha2 := airyZero_neg 2
    have ha3 := airyZero_neg 3
    rw [abs_le]
    constructor
    · rw [abs_of_neg ha3]; linarith
    · linarith [abs_nonneg (airyZero 3), neg_abs_le (airyZero 3)]
  have hm1 : airyClarkNode γ₁ 1 - airyClarkNode γ₁ 2 ≤ airyClarkNode γ 1 - airyClarkNode γ 2 :=
    hmin₁ hγ
  have hm2 : airyClarkNode γ₂ 2 - airyClarkNode γ₂ 3 ≤ airyClarkNode γ 2 - airyClarkNode γ 3 :=
    hmin₂ hγ
  refine ⟨(min_le_left _ _).trans hm1, (min_le_right _ _).trans hm2, ?_, ?_, ?_⟩
  · linarith [abs_nonneg (airyZero 2), abs_nonneg (airyZero 3)]
  · linarith [le_max_right B₁ 0, abs_nonneg (airyZero 3)]
  · linarith [le_max_right B₁ 0, abs_nonneg (airyZero 2)]

/-- The offset `D₁ c'^{-1/3}` of the prescribed node tends to `0`. -/
lemma tendsto_offset (D₁ : ℝ) :
    Tendsto (fun c' : ℝ => D₁ * c' ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
  simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul D₁

/-- Every `γ ∈ ℝ` is `cot α` for an angle `α` with `sin α ≠ 0`, and then
`clarkNode α n = airyClarkNode γ n`. -/
lemma exists_clarkAngle_node (γ : ℝ) :
    ∃ α : ℝ, Real.sin α ≠ 0 ∧ ∀ n : ℕ, clarkNode α n = airyClarkNode γ n := by
  obtain ⟨α, hα0, hαpi, hαc⟩ := airyClark_exists_angle_cot γ
  refine ⟨α, (Real.sin_pos_of_pos_of_lt_pi hα0 hαpi).ne', fun n => ?_⟩
  change airyClarkNode (Real.cos α / Real.sin α) n = _
  rw [hαc]

/-- The derivative of the Clark extremal at its second node:
`g_α'(z₂) = ψ_α'(z₂)² / (z₂ - z₁)`. -/
lemma clarkExtremal_hasDerivAt_two {α : ℝ} (hα : Real.sin α ≠ 0) :
    HasDerivAt (clarkExtremal α)
      (deriv (psiClark α) (clarkNode α 2 : ℂ) ^ 2 /
        ((clarkNode α 2 : ℂ) - (clarkNode α 1 : ℂ))) (clarkNode α 2 : ℂ) := by
  set z1 : ℂ := (clarkNode α 1 : ℂ) with hz1
  set z2 : ℂ := (clarkNode α 2 : ℂ) with hz2
  have hdiff := differentiable_psiClark α
  have hD1 : Differentiable ℂ (dslope (psiClark α) z1) :=
    EntireDiv.differentiable_dslope_entire hdiff z1
  have hD2 : Differentiable ℂ (dslope (psiClark α) z2) :=
    EntireDiv.differentiable_dslope_entire hdiff z2
  have hne : z2 ≠ z1 := by
    intro h
    have := Complex.ofReal_injective h
    linarith [clarkNode_two_lt_one α]
  have hψ1 : psiClark α z1 = 0 := clarkNode_zero hα le_rfl
  have hψ2 : psiClark α z2 = 0 := clarkNode_zero hα (by norm_num)
  have hD1z2 : dslope (psiClark α) z1 z2 = 0 := by
    rw [dslope_of_ne _ hne, slope_def_field, hψ1, hψ2]; simp
  have hD2z2 : dslope (psiClark α) z2 z2 = deriv (psiClark α) z2 := dslope_same _ _
  have hrel : (fun u : ℂ => (u - z1) * dslope (psiClark α) z1 u) = psiClark α := by
    funext u
    have := sub_smul_dslope (psiClark α) z1 u
    rw [smul_eq_mul, hψ1, sub_zero] at this
    exact this
  have hd_rel : HasDerivAt (fun u : ℂ => (u - z1) * dslope (psiClark α) z1 u)
      (1 * dslope (psiClark α) z1 z2 + (z2 - z1) * deriv (dslope (psiClark α) z1) z2) z2 :=
    ((hasDerivAt_id z2).sub_const z1).mul (hD1 z2).hasDerivAt
  rw [hrel] at hd_rel
  have hderiv_ψ : HasDerivAt (psiClark α) (deriv (psiClark α) z2) z2 := (hdiff z2).hasDerivAt
  have hD1' : deriv (dslope (psiClark α) z1) z2 = deriv (psiClark α) z2 / (z2 - z1) := by
    have := hd_rel.unique hderiv_ψ
    rw [hD1z2] at this
    have hsub : z2 - z1 ≠ 0 := sub_ne_zero.mpr hne
    field_simp
    linear_combination this
  have hprod := (hD1 z2).hasDerivAt.mul (hD2 z2).hasDerivAt
  rw [hD1z2, hD2z2, hD1', zero_mul, add_zero] at hprod
  convert hprod using 1
  · funext u; rfl
  · ring

/-- `ψ_α'` is real on the real axis. -/
lemma psiClark_deriv_im {α : ℝ} (x : ℝ) : (deriv (psiClark α) (x : ℂ)).im = 0 := by
  have hd : HasDerivAt (psiClark α) (deriv (psiClark α) (x : ℂ)) (x : ℂ) :=
    ((differentiable_psiClark α) (x : ℂ)).hasDerivAt
  have hd_real := hd.comp_ofReal
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hd_real
  have hzero : (fun y : ℝ => Complex.imCLM (psiClark α (y : ℂ))) = fun _ => (0 : ℝ) := by
    funext y
    rw [psiClark_ofReal]
    simp
  rw [Function.comp_def, hzero] at him
  exact (hasDerivAt_const x (0 : ℝ)).unique him |>.symm

/-- `Re g_α'(z₂(α)) < 0`: the Clark extremal crosses zero downward at `z₂`. -/
lemma clarkExtremal_deriv_two_re_neg {α : ℝ} (hα : Real.sin α ≠ 0) :
    (deriv (clarkExtremal α) (clarkNode α 2 : ℂ)).re < 0 := by
  rw [(clarkExtremal_hasDerivAt_two hα).deriv]
  set d := deriv (psiClark α) (clarkNode α 2 : ℂ) with hd
  have hdim : d.im = 0 := psiClark_deriv_im _
  have hdne : d ≠ 0 := clarkNode_deriv_ne_zero hα (by norm_num)
  have hdre : d.re ≠ 0 := fun h => hdne (Complex.ext h hdim)
  have hlt : clarkNode α 2 - clarkNode α 1 < 0 := by linarith [clarkNode_two_lt_one α]
  have hdc : d = (d.re : ℂ) := Complex.ext (by simp) (by simp [hdim])
  have hcast : d ^ 2 / ((clarkNode α 2 : ℂ) - (clarkNode α 1 : ℂ)) =
      ((d.re ^ 2 / (clarkNode α 2 - clarkNode α 1) : ℝ) : ℂ) := by
    rw [hdc]; push_cast; rfl
  rw [hcast, Complex.ofReal_re]
  exact div_neg_of_pos_of_neg (by positivity) hlt

end FormalResearch.ModularBootstrap.ConcreteBootstrap
