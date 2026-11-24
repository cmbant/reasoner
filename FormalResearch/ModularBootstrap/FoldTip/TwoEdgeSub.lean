module

public import FormalResearch.ModularBootstrap.FoldTip.TwoEdgeLower
public import FormalResearch.TwoEdgeBootstrap.WeakFeedback

/-!
# Proposition FT-Sub: Graded Lower Remainder with Vacuum Error and Weak Feedback

Source: `CFT/modular_bootstrap/paper/fold_tip_two_edge.tex`, Proposition FT-Sub (`fto1:sub`);
`CFT/common/two_edge_bootstrap.tex` Theorem `TE.2(5)`.

* `ft_sub_displacement`: for one violator, `K = c^{1/3} x̃ ≤ C₁'(1 + log L)`
  (`teb_weak_K_log_bound`, vacuum error `η_vac ≤ C_vac c^{-1/3}` allowed).
* `ft_sub_feedback`: with weak feedback `L ≤ C_fb(c^{1/3}(B₁ + B₂) + Υ_C)`, `L ≤ C_fb' Υ_C` and
  `K ≤ C₁'' (1 + log Υ_C)` (`teb_weak_feedback_closure`).
* `ft_sub`: every feasible threshold obeys `T ≥ ξ_* C + (|u_*|/β) C^{1/3} - C₋(1 + log Υ_C)`.
* `subViolators_nonvacuous`: the hypotheses are satisfiable.

The terminal node (Airy, Clark or Hermite--Biehler) enters through the single-`θ` terminal bound of
`BootstrapWeakCore` (`hP_theta_lb`, node constant `a_N`), the same for every violator.
-/

@[expose] public section

open scoped Real

namespace FormalResearch.ModularBootstrap.FoldTip

open FormalResearch.TwoEdgeBootstrap

/-- **Proposition FT-Sub, displacement** (first display): `K ≤ C₁'(1 + log L)`, with
`C₁' = tebCKWeak P θ a_N C_vac`. -/
theorem ft_sub_displacement (P : BootstrapParams) (W : BootstrapWeakCore P)
    (hc : tebC2 P ≤ W.c) :
    W.c ^ (1 / 3 : ℝ) * W.x_tilde ≤
      tebCKWeak P W.θ W.a_N W.C_vac * (1 + Real.log W.L) :=
  teb_weak_K_log_bound P W hc

/-- **Proposition FT-Sub, weak feedback**: `L ≤ C_fb' Υ_C` and `K ≤ C₁''(1 + log Υ_C)`. -/
theorem ft_sub_feedback (P : BootstrapParams) (W : BootstrapWeakCore P)
    (hc : tebC2 P ≤ W.c) {Upsilon : ℝ} (hU : 1 ≤ Upsilon)
    (hfb : W.L ≤ P.C_fb * (W.c ^ (1 / 3 : ℝ) * (W.B_1 + W.B_2) + Upsilon)) :
    W.L ≤ tebWeakScale (tebCStarWeak P W.C_N W.C_vac) * Upsilon ∧
      W.c ^ (1 / 3 : ℝ) * W.x_tilde ≤
        (tebCKWeak P W.θ W.a_N W.C_vac *
          (1 + Real.log (tebWeakScale (tebCStarWeak P W.C_N W.C_vac)))) *
          (1 + Real.log Upsilon) := by
  have h := teb_weak_feedback_closure P W hc hU hfb
  simpa only [mul_assoc] using h

/-- Hypotheses of Proposition FT-Sub for every violator: a vacuum-error bootstrap instance at
`c = C` with `x̃ = u - u_*`, fixed single-`θ` data `(θ, a_N, C_vac, C_N)`, and the weak feedback
with `Υ_C`. -/
def SubViolators (Ch : FoldChart) (P : BootstrapParams) (θ aN Cvac CN : ℝ) (Υ : ℝ → ℝ)
    (Feasible : ℝ → ℝ → Prop) (ustar C1 : ℝ) : Prop :=
  ∀ C : ℝ, C1 ≤ C → ∀ T u : ℝ, Ch.Violates Feasible ustar C T u →
    ∃ W : BootstrapWeakCore P, W.c = C ∧ W.x_tilde = u - ustar ∧ W.θ = θ ∧ W.a_N = aN ∧
      W.C_vac = Cvac ∧ W.C_N = CN ∧
      W.L ≤ P.C_fb * (W.c ^ (1 / 3 : ℝ) * (W.B_1 + W.B_2) + Υ C)

/-- The displacement constant `C₁''` of `ft_sub_feedback` for fixed single-`θ` data. -/
noncomputable def subK (P : BootstrapParams) (θ aN Cvac CN : ℝ) : ℝ :=
  tebCKWeak P θ aN Cvac * (1 + Real.log (tebWeakScale (tebCStarWeak P CN Cvac)))

lemma subK_nonneg (P : BootstrapParams) {θ aN Cvac CN : ℝ} (hθ : 0 < θ) (haN : 0 < aN)
    (hCvac : 0 ≤ Cvac) : 0 ≤ subK P θ aN Cvac CN := by
  have h1 : 1 ≤ tebCStarWeak P CN Cvac := le_max_left _ _
  have h2 : 1 ≤ tebWeakScale (tebCStarWeak P CN Cvac) := one_le_tebWeakScale h1
  have h3 := Real.log_nonneg h2
  have h4 := (tebCKWeak_pos P hθ haN hCvac).le
  unfold subK; positivity

/-- **Proposition FT-Sub** (`fto1:sub2`).  Under the fold hypotheses, `(B1)` with vacuum error,
the single-`θ` terminal bound and the weak feedback with `Υ_C ≥ 1` for every violator in the chart,
every feasible threshold satisfies, for `C ≥ C1 ≥ max C₀ (tebC2 P)`,
`T ≥ ξ_* C + (|u_*|/β) C^{1/3} - C₋(1 + log Υ_C)`. -/
theorem ft_sub (Ch : FoldChart) (P : BootstrapParams) {θ aN Cvac CN : ℝ} {Υ : ℝ → ℝ}
    {Feasible : ℝ → ℝ → Prop} {ustar C1 : ℝ}
    (hθ : 0 < θ) (haN : 0 < aN) (hCvac : 0 ≤ Cvac)
    (hu : ustar < 0) (hC1 : max Ch.C0 (tebC2 P) ≤ C1)
    (hΥ : ∀ C : ℝ, C1 ≤ C → 1 ≤ Υ C)
    (hU : ∀ C : ℝ, C1 ≤ C → |ustar| ≤ Ch.U C)
    (hcov : Ch.ChartCoverage Feasible ustar C1)
    (hviol : SubViolators Ch P θ aN Cvac CN Υ Feasible ustar C1) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ C : ℝ, C1 ≤ C → ∀ T : ℝ, Feasible C T →
      Ch.ξs * C + (|ustar| / Ch.β) * C ^ (1 / 3 : ℝ) - Cm * (1 + Real.log (Υ C)) ≤ T := by
  have hKs := subK_nonneg P (CN := CN) hθ haN hCvac
  have hm : 0 ≤ min P.δ_star (min P.η_0 1) :=
    le_min P.hδ_star.le (le_min P.hη0.le zero_le_one)
  refine ⟨twoEdgeKminus Ch ustar (subK P θ aN Cvac CN) (min P.δ_star (min P.η_0 1)),
    twoEdgeKminus_nonneg Ch hKs, ?_⟩
  have hlog : ∀ C : ℝ, C1 ≤ C → 1 ≤ 1 + Real.log (Υ C) := fun C hC => by
    linarith [Real.log_nonneg (hΥ C hC)]
  have hmain := Ch.lower_of_displacement
    (κ := fun C => subK P θ aN Cvac CN * (1 + Real.log (Υ C))) hu hm
    ((le_max_left _ _).trans hC1) hU
    (fun C hC => mul_nonneg hKs (by linarith [hlog C hC])) hcov (by
      intro C hC T u hv
      obtain ⟨W, hWc, hWx, hWθ, hWa, hWv, hWN, hfb⟩ := hviol C hC T u hv
      have hc : tebC2 P ≤ W.c := by rw [hWc]; exact (le_max_right _ _).trans (hC1.trans hC)
      have hU1 : 1 ≤ Υ C := hΥ C hC
      subst hWc
      have h3 := (ft_sub_feedback P W hc hU1 hfb).2
      refine ⟨by rw [← hWx]; exact W.hx_ub, ?_⟩
      rw [← hWx]
      rw [hWθ, hWa, hWv, hWN] at h3
      exact h3)
  intro C hC T hT
  have h := hmain C hC T hT
  have hE : 0 ≤ Ch.Cξ * (|ustar| + min P.δ_star (min P.η_0 1)) ^ 2 := by
    have := Ch.hCξ; positivity
  have hβ := Ch.hβ
  have hl := hlog C hC
  have hexp : twoEdgeKminus Ch ustar (subK P θ aN Cvac CN) (min P.δ_star (min P.η_0 1)) *
      (1 + Real.log (Υ C)) ≥
      subK P θ aN Cvac CN * (1 + Real.log (Υ C)) / Ch.β +
        Ch.Cξ * (|ustar| + min P.δ_star (min P.η_0 1)) ^ 2 := by
    unfold twoEdgeKminus
    have h1 : subK P θ aN Cvac CN * (1 + Real.log (Υ C)) / Ch.β =
        subK P θ aN Cvac CN / Ch.β * (1 + Real.log (Υ C)) := by ring
    rw [h1, add_mul]
    nlinarith
  linarith

/-! ### Non-vacuity -/

/-- Explicit weak-feedback bootstrap instance at `c ≥ 2` with `x̃ = c^{-2/3}`, `θ = a_N = 1/2`,
`C_vac = C_N = 1` (the witness of `bootstrapWeakCore_nonvacuous` with its parameters exposed). -/
noncomputable def weakWitness (c : ℝ) (hc : 2 ≤ c) : BootstrapWeakCore defaultBootstrapParams := by
  have hc_pos : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  let R : ℝ := c ^ (2 / 3 : ℝ)
  let a : ℝ := c ^ (1 / 3 : ℝ)
  let x_tilde : ℝ := c ^ (-(2 / 3 : ℝ))
  let η : ℝ := c ^ (-(1 / 3 : ℝ))
  have hη_pos : 0 < η := Real.rpow_pos_of_pos hc_pos _
  exact {
    c := c, R := R, a := a, B_1 := 0, B_2 := 0, L := 1
    x_tilde := x_tilde, r_inf := 0, C_err := 0, hc := hc
    ha_lb := by simp [defaultBootstrapParams, a]
    ha_sq := by
      dsimp [a, R]; rw [← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_pos.le]; norm_num
    hR_ub := by dsimp [R, defaultBootstrapParams]; linarith [Real.rpow_nonneg hc_pos.le (2 / 3 : ℝ)]
    hB1 := le_rfl, hB2 := le_rfl, hL_lb := le_rfl
    hL_ub := by simp [defaultBootstrapParams]
    hx_pos := Real.rpow_pos_of_pos hc_pos _
    hx_ub := by
      simp only [defaultBootstrapParams, min_self, x_tilde]
      rw [← Real.rpow_zero c]; exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    hr_inf_nn := le_rfl
    hr_inf_ub := by simp only [defaultBootstrapParams, one_mul, neg_mul]; positivity
    hC_err_nn := le_rfl
    hC_err_ub := by simp [defaultBootstrapParams]
    B_1k := fun _ => 0, B_2' := fun _ => 0
    P_nodes := fun k _ => η + ((k : ℝ) + 1) / R
    I_line := fun k _ => η + ((k : ℝ) + 1) / R
    Arc_cov := fun _ _ => 0, Arc_unc := 0
    hB1k_nn := fun _ _ _ => le_rfl, hB2'_nn := fun _ _ _ => le_rfl
    hB_sum := fun _ _ _ => by norm_num
    hP_le := fun _ _ _ _ _ => by ring_nf; rfl
    hArc_cov := fun k ℓ _ _ hℓ => by
      have hℓ_nn : 0 ≤ ℓ := by simpa [defaultBootstrapParams] using hℓ.1
      have ha_pos : 0 < a := Real.rpow_pos_of_pos hc_pos _
      have hgam_pos : 0 < Real.Gamma ((k : ℝ) + 1 / 2) := Real.Gamma_pos_of_pos (by positivity)
      have hpow_nn : 0 ≤ (Real.pi / (4 * ℓ * a)) ^ ((k : ℝ) + 1 / 2) :=
        Real.rpow_nonneg (by positivity) _
      simp only [defaultBootstrapParams, mul_one]; positivity
    hArc_unc := by simp only [defaultBootstrapParams, one_mul]; positivity
    C_vac := 1, η_vac := η, C_N := 1, θ := 1 / 2, a_N := 1 / 2
    hCvac := zero_le_one, hη_vac_nn := hη_pos.le, hη_vac_ub := by simp [η]
    hCN := zero_le_one, hθ_pos := by norm_num, hθ_half := le_rfl, haN_pos := by norm_num
    hI_line_vac := fun k _ _ _ _ => by
      simp only [defaultBootstrapParams, mul_zero, zero_mul, sub_zero, zero_add, one_mul, η]
      ring_nf; rfl
    hP_nodes_lb := fun k ℓ _ _ hℓ => by
      have hℓ_nn : 0 ≤ ℓ := by simpa [defaultBootstrapParams] using hℓ.1
      have hR_pos : 0 < R := Real.rpow_pos_of_pos hc_pos _
      have hp_nn : 0 ≤ η + ((k : ℝ) + 1) / R := by positivity
      dsimp [defaultBootstrapParams]
      linarith
    hP_theta_lb := fun k _ _ _ => by
      have hR_pos : 0 < R := Real.rpow_pos_of_pos hc_pos _
      have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ k by positivity]
      have h1 : (1 / 2 : ℝ) * x_tilde ≤ ((k : ℝ) + 1) / R := by
        dsimp [x_tilde, R]
        rw [Real.rpow_neg hc_pos.le, ← one_div]
        calc (1 / 2 : ℝ) * (1 / c ^ (2 / 3 : ℝ)) ≤ 1 * (1 / c ^ (2 / 3 : ℝ)) := by gcongr; norm_num
          _ ≤ ((k : ℝ) + 1) / c ^ (2 / 3 : ℝ) := by
              rw [one_mul]; exact div_le_div_of_nonneg_right hk1 hR_pos.le
      dsimp [defaultBootstrapParams]
      linarith
  }

/-- Non-vacuity for `SubViolators` and `ChartCoverage`: with the linear chart, `u_* = -1` and the
feasible set with the single violator `x̃ = C^{-2/3}` at every `C ≥ 2`, carried by `weakWitness`
(`Υ_C = 1`, `θ = a_N = 1/2`, `C_vac = C_N = 1`), all hypotheses of `ft_sub` hold. -/
theorem subViolators_nonvacuous :
    ∃ x : ℝ → ℝ, (∀ C : ℝ, 2 ≤ C → 0 < x C ∧ x C ≤ 1) ∧
      linearFoldChart.ChartCoverage (linearFeasible x) (-1) 2 ∧
      SubViolators linearFoldChart defaultBootstrapParams (1 / 2) (1 / 2) 1 1 (fun _ => 1)
        (linearFeasible x) (-1) 2 := by
  have hxb : ∀ C : ℝ, 2 ≤ C → 0 < C ^ (-(2 / 3 : ℝ)) ∧ C ^ (-(2 / 3 : ℝ)) ≤ 1 := by
    intro C hC
    exact ⟨Real.rpow_pos_of_pos (by linarith) _,
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)⟩
  refine ⟨fun C => C ^ (-(2 / 3 : ℝ)), hxb, linearFeasible_coverage hxb, ?_⟩
  intro C hC T u hv
  have hu := linearFeasible_coord (x := fun C => C ^ (-(2 / 3 : ℝ))) (by linarith) hv
  refine ⟨weakWitness C hC, rfl, by rw [hu]; simp [weakWitness], rfl, rfl, rfl, rfl, ?_⟩
  simp [weakWitness, defaultBootstrapParams]

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.ft_sub_displacement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.ft_sub_displacement

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.ft_sub_feedback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.ft_sub_feedback

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.ft_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.ft_sub

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.subViolators_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.subViolators_nonvacuous

end FormalResearch.ModularBootstrap.FoldTip
