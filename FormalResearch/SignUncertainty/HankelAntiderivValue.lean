module

public import FormalResearch.SignUncertainty.HankelAntiderivLimit
public import FormalResearch.SignUncertainty.HankelBesselMoments

/-!
# The value of `∫_0^∞ w^{c/2-1} φ_c(w) dw`

For `c > 1/2` the limit `L = lim_X ∫_0^X w^{c/2-1} φ_c` (`HankelAntiderivLimit`) satisfies
`(2π)^c/Γ(c) · L = 1`.  Proof: integrate the Laguerre identity `𝓗_c e^{-2πs} = e^{-2πΔ}`
(`integral_hankel_exp`) against `Δ^{c/2-1}` on `(0,X)`, swap the order (Fubini), rescale
(`hankelPrimitive`), and let `X → ∞` by dominated convergence, using only that `G_c` is bounded and
converges.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

lemma inner_scale {c : ℝ} {s X : ℝ} (hs : 0 < s) (hX : 0 ≤ X) :
    ∫ Δ in Ioc (0 : ℝ) X, Δ ^ (c / 2 - 1) * hankelPhi c (Δ * s) =
      s ^ (-(c / 2)) * hankelPrimitive c (s * X) := by
  set f : ℝ → ℝ := fun w => w ^ (c / 2 - 1) * hankelPhi c w with hf
  have h1 : ∫ Δ in Ioc (0 : ℝ) X, Δ ^ (c / 2 - 1) * hankelPhi c (Δ * s) =
      ∫ Δ in (0 : ℝ)..X, s ^ (-(c / 2 - 1)) * f (s * Δ) := by
    rw [intervalIntegral.integral_of_le hX]
    refine setIntegral_congr_fun measurableSet_Ioc fun Δ hΔ => ?_
    have hΔ0 : 0 < Δ := hΔ.1
    simp only [hf]
    rw [Real.mul_rpow hs.le hΔ0.le, mul_comm Δ s]
    have : s ^ (-(c / 2 - 1)) * s ^ (c / 2 - 1) = 1 := by
      rw [← Real.rpow_add hs]; simp
    calc Δ ^ (c / 2 - 1) * hankelPhi c (s * Δ)
        = (s ^ (-(c / 2 - 1)) * s ^ (c / 2 - 1)) * (Δ ^ (c / 2 - 1) * hankelPhi c (s * Δ)) := by
          rw [this, one_mul]
      _ = _ := by ring
  rw [h1, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left f hs.ne']
  simp only [smul_eq_mul, mul_zero]
  unfold hankelPrimitive
  rw [intervalIntegral.integral_of_le (by positivity)]
  have : s ^ (-(c / 2 - 1)) * s⁻¹ = s ^ (-(c / 2)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hs]; congr 1; ring
  rw [← mul_assoc, this]


/-- The weight `E(s) = e^{-2πs} ρ₀(s)`. -/
noncomputable def hankelExpWeight (c s : ℝ) : ℝ := Real.exp (-(2 * π * s)) * hankelRho0 c s

lemma hankelExpWeight_nonneg {c : ℝ} (hc : 0 < c) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ hankelExpWeight c s :=
  mul_nonneg (Real.exp_pos _).le (hankelRho0_nonneg hc hs)

/-- **Fubini step.** For `c > 1/2` and `X > 0`:
`∫_0^X Δ^{c/2-1} e^{-2πΔ} dΔ = ∫_0^∞ E(s) s^{-c/2} G_c(sX) ds`. -/
theorem integral_exp_eq_integral_primitive {c : ℝ} (hc : 1 / 2 < c) {X : ℝ} (hX : 0 < X) :
    ∫ Δ in Ioc (0 : ℝ) X, Δ ^ (c / 2 - 1) * Real.exp (-(2 * π * Δ)) =
      ∫ s in Ioi (0 : ℝ), hankelExpWeight c s * (s ^ (-(c / 2)) * hankelPrimitive c (s * X)) := by
  have hc0 : 0 < c := by linarith
  set F : ℝ → ℝ → ℝ := fun Δ s => Δ ^ (c / 2 - 1) * (hankelExpWeight c s * hankelPhi c (Δ * s))
    with hF
  have hE : IntegrableOn (hankelExpWeight c) (Ioi 0) := integrableOn_exp_rho0 hc0
  have hR : IntegrableOn (fun Δ : ℝ => Δ ^ (c / 2 - 1)) (Ioc 0 X) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hX.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < c / 2 - 1))
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc (0 : ℝ) X)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hg := Integrable.mul_prod (μ := volume.restrict (Ioc (0 : ℝ) X))
      (ν := volume.restrict (Ioi (0 : ℝ))) hR hE
    refine hg.mono' ?_ ?_
    · have : Measurable (Function.uncurry F) := by
        simp only [hF, hankelExpWeight, hankelRho0, Function.uncurry]
        have := (hankelPhi_continuous c).measurable
        fun_prop
      exact this.aestronglyMeasurable
    · rw [Measure.prod_restrict]
      refine (ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioi)).mpr
        (Filter.Eventually.of_forall fun p hp => ?_)
      have hΔ : 0 < p.1 := hp.1.1
      have hs : 0 < p.2 := hp.2
      simp only [Function.uncurry, hF, Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg (Real.rpow_nonneg hΔ.le _), abs_of_nonneg (hankelExpWeight_nonneg hc0 hs.le)]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (hankelExpWeight_nonneg hc0 hs.le)
        (abs_hankelPhi_le_one hc _)) (Real.rpow_nonneg hΔ.le _)
  have hswap : ∫ Δ in Ioc (0 : ℝ) X, ∫ s in Ioi (0 : ℝ), F Δ s =
      ∫ s in Ioi (0 : ℝ), ∫ Δ in Ioc (0 : ℝ) X, F Δ s := integral_integral_swap hint
  have hL : ∀ Δ ∈ Ioc (0 : ℝ) X, ∫ s in Ioi (0 : ℝ), F Δ s =
      Δ ^ (c / 2 - 1) * Real.exp (-(2 * π * Δ)) := by
    intro Δ hΔ
    simp only [hF]
    rw [integral_const_mul]
    congr 1
    exact integral_hankel_exp hc0 hΔ.1.le
  have hRr : ∀ s ∈ Ioi (0 : ℝ), ∫ Δ in Ioc (0 : ℝ) X, F Δ s =
      hankelExpWeight c s * (s ^ (-(c / 2)) * hankelPrimitive c (s * X)) := by
    intro s hs
    have hs0 : 0 < s := hs
    have : ∀ Δ : ℝ, F Δ s = hankelExpWeight c s * (Δ ^ (c / 2 - 1) * hankelPhi c (Δ * s)) := by
      intro Δ; simp only [hF]; ring
    simp_rw [this]
    rw [integral_const_mul, inner_scale hs0 hX.le]
  rw [setIntegral_congr_fun measurableSet_Ioc hL] at hswap
  rw [hswap]
  exact setIntegral_congr_fun measurableSet_Ioi hRr


/-- The primitive as an interval integral, `G_c(X) = ∫_{0..X}` (continuous in `X`). -/
noncomputable def hankelPrimitiveInt (c X : ℝ) : ℝ :=
  ∫ w in (0 : ℝ)..X, w ^ (c / 2 - 1) * hankelPhi c w

lemma continuous_hankelPrimitiveInt {c : ℝ} (hc : 0 < c) : Continuous (hankelPrimitiveInt c) :=
  intervalIntegral.continuous_primitive (fun a b => by
    exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < c / 2 - 1)).mul_continuousOn
      (hankelPhi_continuous c).continuousOn) 0

lemma hankelPrimitive_eq_int {c X : ℝ} (hX : 0 ≤ X) :
    hankelPrimitive c X = hankelPrimitiveInt c X := by
  unfold hankelPrimitive hankelPrimitiveInt
  rw [intervalIntegral.integral_of_le hX]

lemma integral_weight_eq {c : ℝ} :
    ∫ s in Ioi (0 : ℝ), hankelExpWeight c s * s ^ (-(c / 2)) =
      (2 * π) ^ c / Real.Gamma c *
        ∫ s in Ioi (0 : ℝ), s ^ (c / 2 - 1) * Real.exp (-(2 * π * s)) := by
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 < s := hs
  simp only [hankelExpWeight, hankelRho0]
  have : s ^ (c - 1) * s ^ (-(c / 2)) = s ^ (c / 2 - 1) := by
    rw [← Real.rpow_add hs0]; congr 1; ring
  calc Real.exp (-(2 * π * s)) * ((2 * π) ^ c / Real.Gamma c * s ^ (c - 1)) * s ^ (-(c / 2))
      = (2 * π) ^ c / Real.Gamma c * (Real.exp (-(2 * π * s)) * (s ^ (c - 1) * s ^ (-(c / 2)))) := by
        ring
    _ = _ := by rw [this]; ring


/-- **The value of the limit**: `(2π)^c/Γ(c) · (1/2) ∫_0^∞ w^{c/2-1} φ_{c+1} = 1` for `c > 1/2`. -/
theorem hankelPrimitive_value {c : ℝ} (hc : 1 / 2 < c) :
    (2 * π) ^ c / Real.Gamma c *
      ((1 / 2) * ∫ w in Ioi (0 : ℝ), w ^ (c / 2 - 1) * hankelPhi (c + 1) w) = 1 := by
  have hc0 : 0 < c := by linarith
  set L : ℝ := (1 / 2) * ∫ w in Ioi (0 : ℝ), w ^ (c / 2 - 1) * hankelPhi (c + 1) w with hL
  obtain ⟨M, hM⟩ := hankelPrimitive_bounded hc
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 le_rfl)
  set J1 : ℝ := ∫ s in Ioi (0 : ℝ), s ^ (c / 2 - 1) * Real.exp (-(2 * π * s)) with hJ1
  have hJ1v : J1 = (1 / (2 * π)) ^ (c / 2) * Real.Gamma (c / 2) := by
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := c / 2) (r := 2 * π) (by positivity)
      (by positivity)
    exact this
  have hJ1pos : 0 < J1 := by
    rw [hJ1v]; exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Real.Gamma_pos_of_pos (by positivity))
  have hgi : IntegrableOn (fun s : ℝ => s ^ (c / 2 - 1) * Real.exp (-(2 * π * s))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_Ioi (p := c / 2 - 1) (a := 2 * π) (by linarith)
      (by positivity)
    simpa only [neg_mul] using this
  -- left side tends to `J1`
  have hlhs : Tendsto (fun X : ℝ => ∫ Δ in Ioc (0 : ℝ) X, Δ ^ (c / 2 - 1) * Real.exp (-(2 * π * Δ)))
      atTop (𝓝 J1) := by
    have := intervalIntegral_tendsto_integral_Ioi 0 hgi tendsto_id
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
    simp only [id_eq]
    rw [intervalIntegral.integral_of_le hX]
  -- right side tends to `L * ∫ E s^{-c/2}`
  have hW : IntegrableOn (fun s : ℝ => hankelExpWeight c s * s ^ (-(c / 2))) (Ioi 0) := by
    have h : IntegrableOn (fun s : ℝ => (2 * π) ^ c / Real.Gamma c *
        (s ^ (c / 2 - 1) * Real.exp (-(2 * π * s)))) (Ioi 0) := hgi.const_mul _
    refine h.congr_fun (fun s hs => ?_) measurableSet_Ioi
    have hs0 : 0 < s := hs
    simp only [hankelExpWeight, hankelRho0]
    have : s ^ (c - 1) * s ^ (-(c / 2)) = s ^ (c / 2 - 1) := by
      rw [← Real.rpow_add hs0]; congr 1; ring
    calc (2 * π) ^ c / Real.Gamma c * (s ^ (c / 2 - 1) * Real.exp (-(2 * π * s)))
        = Real.exp (-(2 * π * s)) * ((2 * π) ^ c / Real.Gamma c * (s ^ (c - 1) * s ^ (-(c / 2)))) := by
          rw [this]; ring
      _ = _ := by ring
  have hrhs : Tendsto (fun X : ℝ => ∫ s in Ioi (0 : ℝ),
      hankelExpWeight c s * (s ^ (-(c / 2)) * hankelPrimitive c (s * X))) atTop
      (𝓝 (∫ s in Ioi (0 : ℝ), hankelExpWeight c s * (s ^ (-(c / 2)) * L))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun s => M * (hankelExpWeight c s * s ^ (-(c / 2)))) ?_ ?_ (hW.const_mul M) ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      have hcont : ContinuousOn (fun s : ℝ => hankelExpWeight c s *
          (s ^ (-(c / 2)) * hankelPrimitiveInt c (s * X))) (Ioi 0) := by
        refine ContinuousOn.mul ?_ (ContinuousOn.mul ?_ ?_)
        · exact (Real.continuous_exp.comp (by fun_prop : Continuous fun s : ℝ => -(2 * π * s))
            ).continuousOn.mul (continuousOn_hankelRho0 c)
        · exact ContinuousOn.rpow_const continuousOn_id fun s hs => Or.inl (ne_of_gt hs)
        · exact ((continuous_hankelPrimitiveInt hc0).comp (continuous_id.mul continuous_const)
            ).continuousOn
      refine (hcont.aestronglyMeasurable measurableSet_Ioi).congr ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs => ?_)
      have : (0 : ℝ) ≤ s * X := by have : (0 : ℝ) < s := hs; positivity
      simp only [hankelPrimitive_eq_int this]
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs => ?_)
      have hs0 : 0 < s := hs
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hankelExpWeight_nonneg hc0 hs0.le),
        abs_of_nonneg (Real.rpow_nonneg hs0.le _)]
      calc hankelExpWeight c s * (s ^ (-(c / 2)) * |hankelPrimitive c (s * X)|)
          ≤ hankelExpWeight c s * (s ^ (-(c / 2)) * M) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hM _ (by positivity))
              (Real.rpow_nonneg hs0.le _)) (hankelExpWeight_nonneg hc0 hs0.le)
        _ = M * (hankelExpWeight c s * s ^ (-(c / 2))) := by ring
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs => ?_)
      have hs0 : 0 < s := hs
      have hlim := (hankelPrimitive_tendsto hc).comp (tendsto_id.const_mul_atTop hs0)
      exact (hlim.const_mul (s ^ (-(c / 2)))).const_mul (hankelExpWeight c s)
  -- identify the two limits
  have hEq : ∀ᶠ X : ℝ in atTop, ∫ Δ in Ioc (0 : ℝ) X, Δ ^ (c / 2 - 1) * Real.exp (-(2 * π * Δ)) =
      ∫ s in Ioi (0 : ℝ), hankelExpWeight c s * (s ^ (-(c / 2)) * hankelPrimitive c (s * X)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    exact integral_exp_eq_integral_primitive hc hX
  have hlim := tendsto_nhds_unique (hlhs.congr' hEq) hrhs
  have hcalc : ∫ s in Ioi (0 : ℝ), hankelExpWeight c s * (s ^ (-(c / 2)) * L) =
      L * ((2 * π) ^ c / Real.Gamma c * J1) := by
    rw [← integral_weight_eq, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    ring
  rw [hcalc] at hlim
  have : J1 * (1 - (2 * π) ^ c / Real.Gamma c * L) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hJ1pos.ne'
  · linarith

/-- info: 'FormalResearch.SignUncertainty.hankelPrimitive_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelPrimitive_value

end FormalResearch.SignUncertainty
