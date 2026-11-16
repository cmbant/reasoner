module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# An Abelian theorem for improper integrals (no Airy content)

If `f : ℝ → ℝ` is continuous, `∫_0^T f → L` as `T → ∞` and `f(x) e^{-εx}` is integrable on `(0,∞)` for
every `ε > 0`, then `∫_0^∞ f(x) e^{-εx} dx → L` as `ε → 0⁺` (`tendsto_integral_mul_exp_neg_of_tendsto`).

Proof: with `F(T) = ∫_0^T f` (bounded on `[0,∞)` since convergent) integration by parts gives
`∫_0^∞ f e^{-εx} = ε ∫_0^∞ F(x) e^{-εx} dx`, the substitution `x = u/ε` turns this into
`∫_0^∞ F(u/ε) e^{-u} du`, and dominated convergence (`|F| ≤ M`, `F(u/ε) → L`) gives the limit.
This is used in `AiryIntegral` to pass from the Abel-regularised `∫ Ai(x) e^{εx} dx = e^{ε³/3} → 1`
to the improper integrals.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace FormalResearch.Special

lemma airyAbel_bdd {f : ℝ → ℝ} (hf : Continuous f) {L : ℝ}
    (hL : Tendsto (fun T => ∫ x in (0 : ℝ)..T, f x) atTop (𝓝 L)) :
    ∃ M : ℝ, ∀ x : ℝ, 0 ≤ x → |∫ t in (0 : ℝ)..x, f t| ≤ M := by
  set F : ℝ → ℝ := fun T => ∫ x in (0 : ℝ)..T, f x with hFdef
  have hFc : Continuous F := by
    have := hf.integral_hasStrictDerivAt 0
    exact continuous_iff_continuousAt.2 fun x => (this x).hasDerivAt.continuousAt
  have hev : ∀ᶠ T in atTop, |F T| ≤ |L| + 1 := by
    have h1 : ∀ᶠ T in atTop, F T ∈ Metric.ball L 1 := hL (Metric.ball_mem_nhds L one_pos)
    filter_upwards [h1] with T hT
    rw [Metric.mem_ball, Real.dist_eq] at hT
    have := abs_sub_abs_le_abs_sub (F T) L
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := |N|)).exists_bound_of_continuousOn
    hFc.continuousOn
  refine ⟨max C (|L| + 1), fun x hx => ?_⟩
  by_cases hxN : x ≤ |N|
  · exact (hC x ⟨hx, hxN⟩).trans (le_max_left _ _)
  · refine (hN x ?_).trans (le_max_right _ _)
    rw [not_le] at hxN
    exact le_trans (le_abs_self N) hxN.le

theorem tendsto_integral_mul_exp_neg_of_tendsto {f : ℝ → ℝ} (hf : Continuous f) {L : ℝ}
    (hL : Tendsto (fun T => ∫ x in (0 : ℝ)..T, f x) atTop (𝓝 L))
    (hint : ∀ ε : ℝ, 0 < ε → IntegrableOn (fun x => f x * Real.exp (-ε * x)) (Ioi 0)) :
    Tendsto (fun ε : ℝ => ∫ x in Ioi (0 : ℝ), f x * Real.exp (-ε * x)) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨M, hM⟩ := airyAbel_bdd hf hL
  set F : ℝ → ℝ := fun T => ∫ x in (0 : ℝ)..T, f x with hFdef
  have hFd : ∀ x, HasDerivAt F (f x) x := fun x => (hf.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x => (hFd x).continuousAt
  have hF0 : F 0 = 0 := by simp [hFdef]
  -- integration by parts
  have hibp : ∀ ε : ℝ, 0 < ε → ∫ x in Ioi (0 : ℝ), f x * Real.exp (-ε * x) =
      ∫ x in Ioi (0 : ℝ), F x * (ε * Real.exp (-ε * x)) := by
    intro ε hε
    have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x => -Real.exp (-ε * x)) (ε * Real.exp (-ε * x)) x := by
      intro x _
      have h1 : HasDerivAt (fun x : ℝ => -ε * x) (-ε) x := by
        simpa using (hasDerivAt_id x).const_mul (-ε)
      have := (h1.exp).neg
      convert this using 1
      ring
    have hexp_int : IntegrableOn (fun x : ℝ => Real.exp (-ε * x)) (Ioi 0) := by
      exact exp_neg_integrableOn_Ioi 0 hε
    have h1 : IntegrableOn (fun x => F x * (ε * Real.exp (-ε * x))) (Ioi 0) := by
      refine Integrable.mono' (hexp_int.const_mul (M * ε)) ?_ ?_
      · exact (hFc.mul (by fun_prop)).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (mul_pos hε (Real.exp_pos _))]
        calc |F x| * (ε * Real.exp (-ε * x)) ≤ M * (ε * Real.exp (-ε * x)) := by
              gcongr; exact hM x hx0
          _ = M * ε * Real.exp (-ε * x) := by ring
    have h2 : IntegrableOn (fun x => f x * -Real.exp (-ε * x)) (Ioi 0) := by
      have := (hint ε hε).neg
      refine this.congr_fun (fun x _ => by simp) measurableSet_Ioi
    have h0 : Tendsto (fun x => F x * -Real.exp (-ε * x)) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous fun x => F x * -Real.exp (-ε * x) := by
        refine hFc.mul ?_; fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa [hF0] using this
    have hinf : Tendsto (fun x => F x * -Real.exp (-ε * x)) atTop (𝓝 0) := by
      have hexp : Tendsto (fun x : ℝ => Real.exp (-ε * x)) atTop (𝓝 0) := by
        have : Tendsto (fun x : ℝ => -ε * x) atTop atBot :=
          tendsto_id.const_mul_atTop_of_neg (by linarith)
        exact Real.tendsto_exp_atBot.comp this
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
        (by simpa using hexp.const_mul M)
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [neg_mul]
      exact mul_le_mul_of_nonneg_right (hM x hx) (Real.exp_pos _).le
    have := integral_Ioi_mul_deriv_eq_deriv_mul (u := F) (u' := f) (v := fun x => -Real.exp (-ε * x))
      (v' := fun x => ε * Real.exp (-ε * x)) (a := 0) (a' := 0) (b' := 0)
      (fun x _ => hFd x) hv h1 h2 h0 hinf
    rw [this]
    simp [integral_neg]
  -- rescale
  have hscale : ∀ ε : ℝ, 0 < ε → ∫ x in Ioi (0 : ℝ), F x * (ε * Real.exp (-ε * x)) =
      ∫ u in Ioi (0 : ℝ), F (u / ε) * Real.exp (-u) := by
    intro ε hε
    have := integral_comp_mul_left_Ioi (fun u => F (u / ε) * Real.exp (-u)) 0 hε
    simp only [mul_zero] at this
    have e : ∀ x : ℝ, F (ε * x / ε) * Real.exp (-(ε * x)) = F x * Real.exp (-ε * x) := by
      intro x; rw [mul_div_cancel_left₀ _ hε.ne']; ring_nf
    simp_rw [e] at this
    rw [show (∫ x in Ioi (0 : ℝ), F x * (ε * Real.exp (-ε * x))) =
      ε * ∫ x in Ioi (0 : ℝ), F x * Real.exp (-ε * x) by
        rw [← integral_const_mul]; congr 1; ext x; ring]
    rw [this]
    simp [smul_eq_mul, hε.ne']
  have hdom : Tendsto (fun ε : ℝ => ∫ u in Ioi (0 : ℝ), F (u / ε) * Real.exp (-u)) (𝓝[>] 0)
      (𝓝 (∫ u in Ioi (0 : ℝ), L * Real.exp (-u))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun u => M * Real.exp (-u)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun ε => (hFc.comp (by fun_prop)).mul (by fun_prop) |>.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      gcongr
      exact hM _ (div_nonneg (le_of_lt hu) (le_of_lt hε))
    · exact (integrableOn_exp_neg_Ioi 0).const_mul M
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have h1 : Tendsto (fun ε : ℝ => u / ε) (𝓝[>] 0) atTop := by
        simpa [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hu
      exact (hL.comp h1).mul_const _
  have hlim : ∫ u in Ioi (0 : ℝ), L * Real.exp (-u) = L := by
    rw [integral_const_mul, integral_exp_neg_Ioi_zero]; ring
  rw [hlim] at hdom
  refine hdom.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [hibp ε hε, hscale ε hε]

/-- info: 'FormalResearch.Special.tendsto_integral_mul_exp_neg_of_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.tendsto_integral_mul_exp_neg_of_tendsto

end FormalResearch.Special
