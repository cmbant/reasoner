module

public import FormalResearch.ModularBootstrap.FiveTerm.CombProduct
public import FormalResearch.ModularBootstrap.FiveTerm.Constants

/-!
# The slit-strip comb functional `𝒥` and its defect identity (FIVE-0; `cts:Jdef`, `ctu:common-defect`)

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, eq. `cts:Jdef`, and
`constant_term_universality.tex`, Lemma ctu.2a (1).

`combJ W K F = -α_tip F'(0) - α_C + α_C ∫_0^1 [W(y) max(|F(iy)|, |F(iy) + K(y) F(e^{-iψ})|) - 1] dy/y²`
(`e^{-iψ} = conj (wPt y)`, `ψ = 2 arctan y`), with `F'(0) = slope0 F` the limit of `(F z - 1)/z` in `Ω`.

`comb_defect_identity`: for `F ∈ HAdm F c₁` and an outer-function datum `G` (`OuterDatum W K g₁ G`),
the integrand of `𝒥` is integrable on `(0,1)` (so `𝒥[F]` is the honest integral, not a junk value) and

`𝒥[F] = α_tip g₁ + α_C ∫_0^1 [max(|H(iy)|, |B_H(y)|) - Re B_H(y)] dy/y²`,   `H = F G`,

the defect identity `ctu:common-defect`; `comb_lower_bound`: `α_tip g₁ ≤ 𝒥[F]` (the lower half of
`cts:main-eq` with `c_0^* = α_tip g₁`).  `g₁` is a free real parameter (the first odd jet of `log G`), so the
results serve every `(w, Q)` (`ctu:common-functional`).  All results are proved unconditionally.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- `F'(0)` as the limit of `(F z - 1)/z` for `z → 0` in `Ω`. -/
noncomputable def slope0 (F : ℂ → ℂ) : ℂ := limUnder (𝓝[halfDisc] (0 : ℂ)) (fun z => (F z - 1) / z)

/-- The integrand of `𝒥` (`cts:Jdef`) at `y ∈ (0,1)`. -/
noncomputable def combIntegrand (W : ℝ → ℝ) (K : ℝ → ℂ) (F : ℂ → ℂ) (y : ℝ) : ℝ :=
  (W y * max ‖F (Complex.I * (y : ℂ))‖ ‖F (Complex.I * (y : ℂ)) + K y * F (starRingEnd ℂ (wPt y))‖ - 1) / y ^ 2

/-- The convex functional `𝒥` of `cts:Jdef`. -/
noncomputable def combJ (W : ℝ → ℝ) (K : ℝ → ℂ) (F : ℂ → ℂ) : ℝ :=
  -alphaTip * (slope0 F).re - alphaC + alphaC * ∫ y in Ioo (0 : ℝ) 1, combIntegrand W K F y

section

variable {F G : ℂ → ℂ} {c1 g1 : ℝ} {W : ℝ → ℝ} {K : ℝ → ℂ}

lemma neBot_nhdsWithin_halfDisc : (𝓝[halfDisc] (0 : ℂ)).NeBot := by
  refine mem_closure_iff_nhdsWithin_neBot.mp ?_
  exact mem_closure_halfDisc (by simp) (by simp)

lemma HAdm.tendsto_slope (hF : HAdm F c1) :
    Tendsto (fun z => (F z - 1) / z) (𝓝[halfDisc] (0 : ℂ)) (𝓝 (c1 : ℂ)) := by
  obtain ⟨C, r, hr, hj⟩ := hF.jet
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun z : ℂ => |C| * ‖z‖) (𝓝[halfDisc] (0 : ℂ)) (𝓝 0) := by
    have : Tendsto (fun z : ℂ => ‖z‖) (𝓝 (0 : ℂ)) (𝓝 0) := by
      simpa using (continuous_norm.tendsto (0 : ℂ))
    simpa using (this.mono_left nhdsWithin_le_nhds).const_mul |C|
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
  have hev : ∀ᶠ z in 𝓝[halfDisc] (0 : ℂ), ‖z‖ < r := by
    refine mem_nhdsWithin_of_mem_nhds ?_
    exact (continuous_norm.tendsto (0 : ℂ)).eventually (gt_mem_nhds (by simpa using hr))
  filter_upwards [hev, self_mem_nhdsWithin] with z hz hzm
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hzm; simp [halfDisc] at hzm
  have := hj z (subset_closure hzm) hz
  have e : (F z - 1) / z - c1 = (F z - 1 - c1 * z) / z := by field_simp
  rw [e, norm_div]
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  rw [div_le_iff₀ hzpos]
  calc ‖F z - 1 - c1 * z‖ ≤ C * ‖z‖ ^ 2 := this
    _ ≤ |C| * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
    _ = |C| * ‖z‖ * ‖z‖ := by ring

lemma HAdm.slope0_eq (hF : HAdm F c1) : slope0 F = c1 := by
  have := neBot_nhdsWithin_halfDisc
  exact hF.tendsto_slope.limUnder_eq

/-- The pointwise conjugation `W |F| = |H|`, `W |F + K F(e^{-iψ})| = |B_H|`. -/
lemma combIntegrand_eq (hG : OuterDatum W K g1 G) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    combIntegrand W K F y =
      (max ‖(fun z => F z * G z) (Complex.I * (y : ℂ))‖
        ‖edgeSum (fun z => F z * G z) y‖ - 1) / y ^ 2 := by
  have hW : W y = ‖G (Complex.I * (y : ℂ))‖ := (hG.modulus y hy).symm
  have hW0 : 0 ≤ W y := by rw [hW]; exact norm_nonneg _
  have h1 : edgeSum (fun z => F z * G z) y =
      G (Complex.I * (y : ℂ)) * (F (Complex.I * (y : ℂ)) + K y * F (starRingEnd ℂ (wPt y))) := by
    have hc := hG.coupling y hy
    unfold edgeSum
    calc F (Complex.I * (y : ℂ)) * G (Complex.I * (y : ℂ)) +
        wPt y * ((2 * y ^ 2 / (1 + y ^ 2) : ℝ) : ℂ) * (F (starRingEnd ℂ (wPt y)) * G (starRingEnd ℂ (wPt y)))
        = F (Complex.I * (y : ℂ)) * G (Complex.I * (y : ℂ)) +
          (G (starRingEnd ℂ (wPt y)) * wPt y * ((2 * y ^ 2 / (1 + y ^ 2) : ℝ) : ℂ)) *
            F (starRingEnd ℂ (wPt y)) := by ring
      _ = _ := by rw [← hc]; ring
  unfold combIntegrand
  rw [mul_max_of_nonneg _ _ hW0, h1, hW, norm_mul, norm_mul]
  simp only [mul_comm]

/-- **Defect identity** (`ctu:common-defect`). -/
theorem comb_defect_identity (hF : HAdm F c1) (hG : OuterDatum W K g1 G) :
    IntegrableOn (combIntegrand W K F) (Ioo (0 : ℝ) 1) ∧
    combJ W K F = alphaTip * g1 +
      alphaC * ∫ y in Ioo (0 : ℝ) 1, defectInt (fun z => F z * G z) y := by
  have hH := hF.mul_datum hG
  obtain ⟨hint, hval⟩ := halfDisc_defect_identity hH
  have hcong : ∀ y ∈ Ioo (0 : ℝ) 1, combIntegrand W K F y =
      (max ‖(fun z => F z * G z) (Complex.I * (y : ℂ))‖ ‖edgeSum (fun z => F z * G z) y‖ - 1) / y ^ 2 :=
    fun y hy => combIntegrand_eq hG hy
  refine ⟨hint.congr_fun (fun y hy => (hcong y hy).symm) measurableSet_Ioo, ?_⟩
  unfold combJ
  rw [hF.slope0_eq, setIntegral_congr_fun measurableSet_Ioo hcong, hval]
  have h2 : alphaC * (π / 2) = alphaTip := by
    rw [alphaC_eq_two_div_pi_mul_alphaTip]
    have : π ≠ 0 := Real.pi_pos.ne'
    field_simp
  simp only [Complex.ofReal_re]
  linear_combination (c1 + g1) * h2

/-- **Lower bound for the comb functional**: `α_tip g₁ ≤ 𝒥[F]` for every admissible `F`. -/
theorem comb_lower_bound (hF : HAdm F c1) (hG : OuterDatum W K g1 G) :
    alphaTip * g1 ≤ combJ W K F := by
  obtain ⟨_, h⟩ := comb_defect_identity hF hG
  rw [h]
  have : 0 ≤ ∫ y in Ioo (0 : ℝ) 1, defectInt (fun z => F z * G z) y :=
    setIntegral_nonneg measurableSet_Ioo (fun y _ => defectInt_nonneg _)
  nlinarith only [this, alphaC_pos]

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.comb_defect_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.comb_defect_identity

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.comb_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.comb_lower_bound
