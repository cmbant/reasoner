module

public import FormalResearch.ModularBootstrap.Spin.SpinD2SDQuad
public import FormalResearch.ModularBootstrap.Crossing.MehlerOddMoment

/-!
# Lemma SD-V (`sd:V`): Mehler continuity on `\overline{\mathcal A}_{\rm spin}`

Proves `spinDV : SpinDV` (`spinning_dual.tex`, Lemma SD-V) unconditionally for all `a ≥ 2`:
there exists `C_a > 0` such that for every `D_4`-invariant bounded measurable `h` (`|h| ≤ M`) and
every `Φ ∈ SpinTestClass a`:
1. `|∬ (A_r Φ) h V_1 ⊗ V_1| ≤ C_a M M_2[Φ]` uniformly for `r ∈ [1/2, 1)`;
2. `lim_{r ↑ 1} ∬ (A_r Φ) h V_1 ⊗ V_1 = ∬ Φ h V_1 ⊗ V_1`.

The proof follows `spinning_dual.tex`, Subsection 1.1, with a direct unconditional proof of the
exponential-`L^1` bound `∬ |Φ(r_L, r_R)| exp((π/3) √a |r_L|) ≤ C_a M_2[Φ]` (avoiding `SpinS24`).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal FourierTransform RealInnerProductSpace

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.LP
open FormalResearch.ModularBootstrap.Duality
open FormalResearch.ModularBootstrap.FixedWeight

/-! ### Section 1: Elementary `spinV1` bounds and exponential-`L^1` control on `SpinTestClass a` -/

private lemma cosh_sub_one_le {B : ℝ} (hB : 0 ≤ B) :
    Real.cosh B - 1 ≤ B ^ 2 / 2 * Real.exp B := by
  have h1 : 1 - B ≤ Real.exp (-B) := by
    have := Real.add_one_le_exp (-B); linarith
  have h2 : 0 ≤ 1 - Real.exp (-B) := by
    have : Real.exp (-B) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have h3 : 1 - Real.exp (-B) ≤ B := by linarith
  have hsq : (1 - Real.exp (-B)) ^ 2 ≤ B ^ 2 := by
    nlinarith
  have hexp_pos : 0 < Real.exp B := Real.exp_pos B
  have hmul : (1 - Real.exp (-B)) ^ 2 * Real.exp B ≤ B ^ 2 * Real.exp B :=
    mul_le_mul_of_nonneg_right hsq hexp_pos.le
  have hid : (1 - Real.exp (-B)) ^ 2 * Real.exp B = 2 * (Real.cosh B - 1) := by
    rw [Real.cosh_eq]
    have h1' : Real.exp (-B) * Real.exp B = 1 := by rw [← Real.exp_add]; simp
    have h2' : Real.exp (-B) ^ 2 * Real.exp B = Real.exp (-B) := by
      rw [sq, mul_assoc, h1', mul_one]
    linear_combination -2 * h1' + h2'
  linarith

private lemma spinV1_ge_four_pi_sq_mul_sq_v {a : ℝ} (ha : 2 ≤ a) (r : ℝ) :
    4 * π ^ 2 * r ^ 2 ≤ spinV1 a r := by
  have habs : spinV1 a r = spinV1 a |r| := by
    rcases le_total 0 r with hr | hr
    · rw [abs_of_nonneg hr]
    · rw [abs_of_nonpos hr, spinV1_even]
  rw [habs, spinV1_eq_mul_sinh a |r|]
  set A : ℝ := Real.sqrt a + Real.sqrt (a - 2)
  set B : ℝ := Real.sqrt a - Real.sqrt (a - 2)
  have hA_pos : 0 < A := by positivity
  have hB_pos : 0 < B := sub_pos.mpr (Real.sqrt_lt_sqrt (by linarith) (by linarith))
  have hAB : A * B = 2 := by
    dsimp [A, B]
    have h1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
    have h2 : Real.sqrt (a - 2) ^ 2 = a - 2 := Real.sq_sqrt (by linarith)
    nlinarith
  have hu : π * |r| * A ≤ Real.sinh (π * |r| * A) := Real.self_le_sinh_iff.mpr (by positivity)
  have hv : π * |r| * B ≤ Real.sinh (π * |r| * B) := Real.self_le_sinh_iff.mpr (by positivity)
  have hmul : (π * |r| * A) * (π * |r| * B) ≤
      Real.sinh (π * |r| * A) * Real.sinh (π * |r| * B) :=
    mul_le_mul hu hv (by positivity) (Real.sinh_nonneg_iff.mpr (by positivity))
  have hsq : |r| ^ 2 = r ^ 2 := sq_abs r
  calc 4 * π ^ 2 * r ^ 2 = 2 * ((π * |r| * A) * (π * |r| * B)) := by
        rw [← hsq]; linear_combination 2 * π ^ 2 * |r| ^ 2 * hAB.symm
    _ ≤ 2 * (Real.sinh (π * |r| * A) * Real.sinh (π * |r| * B)) := by linarith
    _ = 2 * Real.sinh (π * |r| * A) * Real.sinh (π * |r| * B) := by ring

private lemma spinV1_le_sq_exp {a : ℝ} (ha : 2 ≤ a) (r : ℝ) :
    spinV1 a r ≤ 2 * π ^ 2 * a * r ^ 2 * Real.exp (2 * π * Real.sqrt a * |r|) := by
  have hcosh1 : 1 ≤ Real.cosh (2 * π * Real.sqrt (a - 2) * r) := Real.one_le_cosh _
  have hV1 : spinV1 a r ≤ Real.cosh (2 * π * Real.sqrt a * |r|) - 1 := by
    unfold spinV1
    have h1 : Real.cosh (2 * π * Real.sqrt a * r) = Real.cosh (2 * π * Real.sqrt a * |r|) := by
      rcases le_total 0 r with hr | hr
      · rw [abs_of_nonneg hr]
      · rw [abs_of_nonpos hr, mul_neg, Real.cosh_neg]
    linarith
  have h2 := cosh_sub_one_le (B := 2 * π * Real.sqrt a * |r|) (by positivity)
  have hsq : (2 * π * Real.sqrt a * |r|) ^ 2 / 2 = 2 * π ^ 2 * a * r ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by linarith), sq_abs]; ring
  rw [hsq] at h2
  exact hV1.trans h2

private lemma spinV1_le_cosh {a : ℝ} (_ha : 2 ≤ a) (r : ℝ) :
    spinV1 a r ≤ Real.cosh (2 * π * Real.sqrt a * r) := by
  unfold spinV1
  linarith [Real.cosh_pos (2 * π * Real.sqrt (a - 2) * r)]

lemma spinV1_le_exp {a : ℝ} (ha : 2 ≤ a) (r : ℝ) :
    spinV1 a r ≤ Real.exp (2 * π * Real.sqrt a * |r|) := by
  refine (spinV1_le_cosh ha r).trans ?_
  rw [Real.cosh_eq]
  have h1 : Real.exp (2 * π * Real.sqrt a * r) ≤ Real.exp (2 * π * Real.sqrt a * |r|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self r) (by positivity))
  have h2 : Real.exp (-(2 * π * Real.sqrt a * r)) ≤ Real.exp (2 * π * Real.sqrt a * |r|) := by
    refine Real.exp_le_exp.mpr ?_
    have hmul : 2 * π * Real.sqrt a * (-r) ≤ 2 * π * Real.sqrt a * |r| :=
      mul_le_mul_of_nonneg_left (neg_le_abs r) (by positivity)
    linarith
  linarith

private lemma spinV1_mono_nonneg {a : ℝ} (ha : 2 ≤ a) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    spinV1 a x ≤ spinV1 a y := by
  rw [spinV1_eq_mul_sinh, spinV1_eq_mul_sinh]
  have hA : 0 ≤ Real.sqrt a + Real.sqrt (a - 2) := by positivity
  have hB : 0 ≤ Real.sqrt a - Real.sqrt (a - 2) :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have h1 : Real.sinh (π * x * (Real.sqrt a + Real.sqrt (a - 2))) ≤
      Real.sinh (π * y * (Real.sqrt a + Real.sqrt (a - 2))) :=
    Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxy Real.pi_pos.le) hA)
  have h2 : Real.sinh (π * x * (Real.sqrt a - Real.sqrt (a - 2))) ≤
      Real.sinh (π * y * (Real.sqrt a - Real.sqrt (a - 2))) :=
    Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxy Real.pi_pos.le) hB)
  have h1_nn : 0 ≤ Real.sinh (π * x * (Real.sqrt a + Real.sqrt (a - 2))) :=
    Real.sinh_nonneg_iff.mpr (by positivity)
  have h2_nn : 0 ≤ Real.sinh (π * x * (Real.sqrt a - Real.sqrt (a - 2))) :=
    Real.sinh_nonneg_iff.mpr (by positivity)
  have hmul := mul_le_mul h1 h2 h2_nn (h1_nn.trans h1)
  linarith

private lemma spinV1_scale_le {a : ℝ} (ha : 2 ≤ a) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (x : ℝ) : spinV1 a (lam * x) ≤ spinV1 a x := by
  have habs : ∀ u, spinV1 a u = spinV1 a |u| := fun u => by
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu]
    · rw [abs_of_nonpos hu, spinV1_even]
  rw [habs (lam * x), habs x, abs_mul, abs_of_nonneg h0]
  exact spinV1_mono_nonneg ha (by positivity) (mul_le_of_le_one_left (abs_nonneg x) h1)

private lemma spinV1_ge_exp_full_away' {a : ℝ} (ha : 2 ≤ a) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ r : ℝ, 1 ≤ |r| →
      c₁ * Real.exp (2 * π * Real.sqrt a * |r|) ≤ spinV1 a r := by
  set A : ℝ := Real.sqrt a + Real.sqrt (a - 2)
  set B : ℝ := Real.sqrt a - Real.sqrt (a - 2)
  have hA_pos : 0 < A := by positivity
  have hB_pos : 0 < B := sub_pos.mpr (Real.sqrt_lt_sqrt (by linarith) (by linarith))
  have hAB_sum : A + B = 2 * Real.sqrt a := by dsimp [A, B]; ring
  set δ : ℝ := 1 - Real.exp (-2 * π * B)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    have : Real.exp (-2 * π * B) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
    linarith
  refine ⟨δ ^ 2 / 2, by positivity, fun r hr => ?_⟩
  have habs : spinV1 a r = spinV1 a |r| := by
    rcases le_total 0 r with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, spinV1_even]
  rw [habs, spinV1_eq_mul_sinh a |r|]
  have hsinh_ge : ∀ t : ℝ, π * B ≤ t → (δ / 2) * Real.exp t ≤ Real.sinh t := by
    intro t ht
    rw [Real.sinh_eq]
    have h1 : Real.exp (-2 * t) ≤ Real.exp (-2 * π * B) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-t) = Real.exp (-2 * t) * Real.exp t := by
      rw [← Real.exp_add]; congr 1; ring
    have h3 : Real.exp (-t) ≤ Real.exp (-2 * π * B) * Real.exp t := by
      rw [h2]; exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos t).le
    dsimp [δ]; linarith
  have h1 : (δ / 2) * Real.exp (π * |r| * A) ≤ Real.sinh (π * |r| * A) := by
    refine hsinh_ge _ ?_
    have hBA : B ≤ A := by dsimp [A, B]; linarith [Real.sqrt_nonneg (a - 2)]
    have hpiB : π * B ≤ π * A := mul_le_mul_of_nonneg_left hBA Real.pi_pos.le
    have hpiA : π * A ≤ π * |r| * A := by
      have : π ≤ π * |r| := le_mul_of_one_le_right Real.pi_pos.le hr
      exact mul_le_mul_of_nonneg_right this hA_pos.le
    exact hpiB.trans hpiA
  have h2 : (δ / 2) * Real.exp (π * |r| * B) ≤ Real.sinh (π * |r| * B) := by
    refine hsinh_ge _ ?_
    have : π ≤ π * |r| := le_mul_of_one_le_right Real.pi_pos.le hr
    exact mul_le_mul_of_nonneg_right this hB_pos.le
  have hprod : 2 * ((δ / 2) * Real.exp (π * |r| * A)) * ((δ / 2) * Real.exp (π * |r| * B)) ≤
      2 * Real.sinh (π * |r| * A) * Real.sinh (π * |r| * B) := by
    have := mul_le_mul h1 h2 (by positivity) (Real.sinh_nonneg_iff.mpr (by positivity))
    linarith
  have hexp_prod : Real.exp (π * |r| * A) * Real.exp (π * |r| * B) =
      Real.exp (2 * π * Real.sqrt a * |r|) := by
    rw [← Real.exp_add]; congr 1; linear_combination π * |r| * hAB_sum
  calc (δ ^ 2 / 2) * Real.exp (2 * π * Real.sqrt a * |r|)
      = 2 * ((δ / 2) * Real.exp (π * |r| * A)) * ((δ / 2) * Real.exp (π * |r| * B)) := by
        rw [← hexp_prod]; ring
    _ ≤ 2 * Real.sinh (π * |r| * A) * Real.sinh (π * |r| * B) := hprod

private lemma spinV1_ge_cosh_away {a : ℝ} (ha : 2 ≤ a) :
    ∃ βa : ℝ, 0 < βa ∧ ∀ r : ℝ, 1 ≤ |r| →
      Real.cosh (2 * π * Real.sqrt a * r) ≤ βa * spinV1 a r := by
  obtain ⟨c₁, hc₁_pos, hc₁⟩ := spinV1_ge_exp_full_away' ha
  refine ⟨c₁⁻¹, inv_pos.mpr hc₁_pos, fun r hr => ?_⟩
  have hcosh : Real.cosh (2 * π * Real.sqrt a * r) ≤ Real.exp (2 * π * Real.sqrt a * |r|) := by
    rw [Real.cosh_eq]
    have h1 : Real.exp (2 * π * Real.sqrt a * r) ≤ Real.exp (2 * π * Real.sqrt a * |r|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self r) (by positivity))
    have h2 : Real.exp (-(2 * π * Real.sqrt a * r)) ≤ Real.exp (2 * π * Real.sqrt a * |r|) := by
      refine Real.exp_le_exp.mpr ?_
      have hmul : 2 * π * Real.sqrt a * (-r) ≤ 2 * π * Real.sqrt a * |r| :=
        mul_le_mul_of_nonneg_left (neg_le_abs r) (by positivity)
      linarith
    linarith
  have h2 := hc₁ r hr
  have h3 : Real.exp (2 * π * Real.sqrt a * |r|) ≤ c₁⁻¹ * spinV1 a r := by
    rw [inv_mul_eq_div, le_div_iff₀ hc₁_pos]; linarith
  exact hcosh.trans h3

private lemma integrable_exp_neg_abs_v {β : ℝ} (hβ : 0 < β) :
    Integrable (fun x : ℝ => Real.exp (-β * |x|)) := by
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-β * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hβ) 0
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (β * x)) (Iic 0) :=
    integrableOn_exp_mul_Iic hβ 0
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  refine ⟨h2.congr_fun (fun x hx => by rw [abs_of_nonpos hx]; ring_nf) measurableSet_Iic,
    h1.congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi⟩

/-- Direct unconditional exponential-`L^1` control on `SpinTestClass a` for all `a ≥ 2`:
`∬ |Φ(r_L, r_R)| exp((π / 3) √a |r_L|) dr_L dr_R ≤ C_a M_2[Φ]`. -/
theorem spinTestClass_exp_L1_le_M2 {a : ℝ} (ha : 2 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ →
      Integrable (fun p : ℝ × ℝ => |Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.1|)) ∧
      (∫ p : ℝ × ℝ, |Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.1|)) ≤
        C * spinM2 a Φ := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := spinTestClass_L1_le_M2 ha
  obtain ⟨c₁, hc₁_pos, hc₁⟩ := spinV1_ge_exp_full_away' ha
  set κ : ℝ := (1 / 3 : ℝ) * π * Real.sqrt a with hκ_def
  set β : ℝ := (3 / 4 : ℝ) * π * Real.sqrt a with hβ_def
  set δ : ℝ := β - κ with hδ_def
  have hκ_pos : 0 < κ := by rw [hκ_def]; positivity
  have hβ_pos : 0 < β := by rw [hβ_def]; positivity
  have hδ_pos : 0 < δ := by rw [hδ_def, hβ_def, hκ_def]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (by linarith : 0 < a)]
  set Iδ : ℝ := ∫ x : ℝ, Real.exp (-δ * |x|) with hIδ_def
  have hIδ_nn : 0 ≤ Iδ := integral_nonneg fun _ => (Real.exp_pos _).le
  set c₂ : ℝ := 4 * π ^ 2 * c₁ with hc₂_def
  have hc₂_pos : 0 < c₂ := by rw [hc₂_def]; positivity
  set C : ℝ := C₀ * Real.exp κ + 2 * C₀ * Iδ + c₂⁻¹ with hC_def
  have hC_pos : 0 < C := by
    rw [hC_def]
    have h1 : 0 < C₀ * Real.exp κ := by positivity
    have h2 : 0 ≤ 2 * C₀ * Iδ := by positivity
    have h3 : 0 < c₂⁻¹ := inv_pos.mpr hc₂_pos
    linarith
  refine ⟨C, hC_pos, fun {Φ} hΦ => ?_⟩
  obtain ⟨hΦ_inf, hΦ_L1⟩ := hC₀ hΦ
  -- Pointwise domination by an integrable function:
  -- `g(p) = e^κ |Φ p| + C₀ M₂ · 1_{|p.2| ≤ e^{-β|p.1|}} e^{κ|p.1|} + c₂⁻¹ |Φ p| V1(p.1) V1(p.2)`.
  let S : Set (ℝ × ℝ) := {p : ℝ × ℝ | |p.2| ≤ Real.exp (-β * |p.1|)}
  have hS_meas : MeasurableSet S :=
    measurableSet_le (continuous_abs.comp continuous_snd).measurable
      (Real.continuous_exp.comp (continuous_const.mul (continuous_abs.comp continuous_fst))).measurable
  let g1 : ℝ × ℝ → ℝ := fun p => Real.exp κ * |Φ p|
  let g2 : ℝ × ℝ → ℝ := S.indicator (fun p => C₀ * spinM2 a Φ * Real.exp (κ * |p.1|))
  let g3 : ℝ × ℝ → ℝ := fun p => c₂⁻¹ * (|Φ p| * spinV1 a p.1 * spinV1 a p.2)
  have hg1_int : Integrable g1 := hΦ.int.abs.const_mul (Real.exp κ)
  have hg3_int : Integrable g3 := hΦ.int_M2.const_mul c₂⁻¹
  have hg2_int : Integrable g2 := by
    rw [Measure.volume_eq_prod]
    have hg2_meas : AEStronglyMeasurable g2 (volume.prod volume) := by
      refine AEStronglyMeasurable.indicator ?_ hS_meas
      exact (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul (continuous_abs.comp continuous_fst)))).aestronglyMeasurable
    rw [integrable_prod_iff hg2_meas]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · have hsub : (fun y : ℝ => g2 (x, y)) =
          (Icc (-Real.exp (-β * |x|)) (Real.exp (-β * |x|))).indicator
            (fun _ => C₀ * spinM2 a Φ * Real.exp (κ * |x|)) := by
        ext y
        simp only [g2, Set.indicator, S, mem_ofPred_eq, mem_Icc, abs_le]
      rw [hsub]
      exact (integrableOn_const (hs := measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc
    · have hnorm : ∀ x : ℝ, ∫ y : ℝ, ‖g2 (x, y)‖ =
          2 * C₀ * spinM2 a Φ * Real.exp (-δ * |x|) := by
        intro x
        have hsub : (fun y : ℝ => ‖g2 (x, y)‖) =
            (Icc (-Real.exp (-β * |x|)) (Real.exp (-β * |x|))).indicator
              (fun _ => C₀ * spinM2 a Φ * Real.exp (κ * |x|)) := by
          ext y
          simp only [g2, Set.indicator, S, mem_ofPred_eq, mem_Icc, abs_le]
          split_ifs with h
          · exact Real.norm_of_nonneg (mul_nonneg (mul_nonneg hC₀_pos.le (spinM2_nonneg ha Φ))
              (Real.exp_pos _).le)
          · simp
        rw [hsub, integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
            Measure.real_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.exp_pos (-β * |x|)])]
        have hexp : Real.exp (-β * |x|) * Real.exp (κ * |x|) = Real.exp (-δ * |x|) := by
          rw [← Real.exp_add]; congr 1; rw [hδ_def]; ring
        calc (Real.exp (-β * |x|) - -Real.exp (-β * |x|)) *
              (C₀ * spinM2 a Φ * Real.exp (κ * |x|))
            = 2 * C₀ * spinM2 a Φ * (Real.exp (-β * |x|) * Real.exp (κ * |x|)) := by ring
          _ = 2 * C₀ * spinM2 a Φ * Real.exp (-δ * |x|) := by rw [hexp]
      simp_rw [hnorm]
      exact (integrable_exp_neg_abs_v hδ_pos).const_mul (2 * C₀ * spinM2 a Φ)
  have hpt : ∀ p : ℝ × ℝ,
      |Φ p| * Real.exp (κ * |p.1|) ≤ g1 p + g2 p + g3 p := by
    intro p
    have hg1_nn : 0 ≤ g1 p := by dsimp [g1]; positivity
    have hg2_nn : 0 ≤ g2 p := Set.indicator_nonneg (fun _ _ =>
      mul_nonneg (mul_nonneg hC₀_pos.le (spinM2_nonneg ha Φ)) (Real.exp_pos _).le) p
    have hg3_nn : 0 ≤ g3 p := mul_nonneg (inv_nonneg.mpr hc₂_pos.le)
      (mul_nonneg (mul_nonneg (abs_nonneg _) (spinV1_nonneg ha p.1)) (spinV1_nonneg ha p.2))
    by_cases hp1 : |p.1| ≤ 1
    · have hle : Real.exp (κ * |p.1|) ≤ Real.exp κ :=
        Real.exp_le_exp.mpr (by nlinarith)
      have : |Φ p| * Real.exp (κ * |p.1|) ≤ g1 p := by
        dsimp [g1]; rw [mul_comm]; exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
      linarith
    · push Not at hp1
      by_cases hpS : p ∈ S
      · have : |Φ p| * Real.exp (κ * |p.1|) ≤ g2 p := by
          dsimp [g2]; rw [Set.indicator_of_mem hpS]
          exact mul_le_mul_of_nonneg_right (hΦ_inf p) (Real.exp_pos _).le
        linarith
      · have hp2 : Real.exp (-β * |p.1|) < |p.2| := lt_of_not_ge hpS
        have hV1_1 : c₁ * Real.exp (2 * π * Real.sqrt a * |p.1|) ≤ spinV1 a p.1 :=
          hc₁ p.1 hp1.le
        have hV1_2 : 4 * π ^ 2 * Real.exp (-2 * β * |p.1|) ≤ spinV1 a p.2 := by
          have hsq : Real.exp (-2 * β * |p.1|) ≤ p.2 ^ 2 := by
            have h1 : Real.exp (-β * |p.1|) ^ 2 ≤ |p.2| ^ 2 :=
              pow_le_pow_left₀ (Real.exp_pos _).le hp2.le 2
            rw [sq_abs] at h1
            have h2 : Real.exp (-β * |p.1|) ^ 2 = Real.exp (-2 * β * |p.1|) := by
              rw [sq, ← Real.exp_add]; congr 1; ring
            linarith
          have := spinV1_ge_four_pi_sq_mul_sq_v ha p.2
          nlinarith [Real.pi_pos]
        have hprod : c₂ * Real.exp (κ * |p.1|) ≤ spinV1 a p.1 * spinV1 a p.2 := by
          have hexp_ge : Real.exp (κ * |p.1|) ≤
              Real.exp (2 * π * Real.sqrt a * |p.1|) * Real.exp (-2 * β * |p.1|) := by
            rw [← Real.exp_add]
            refine Real.exp_le_exp.mpr ?_
            rw [hκ_def, hβ_def]
            nlinarith [Real.pi_pos, Real.sqrt_nonneg a, abs_nonneg p.1]
          have hmul := mul_le_mul hV1_1 hV1_2 (by positivity) (spinV1_nonneg ha p.1)
          calc c₂ * Real.exp (κ * |p.1|)
              ≤ c₂ * (Real.exp (2 * π * Real.sqrt a * |p.1|) * Real.exp (-2 * β * |p.1|)) :=
                mul_le_mul_of_nonneg_left hexp_ge hc₂_pos.le
            _ = (c₁ * Real.exp (2 * π * Real.sqrt a * |p.1|)) *
                  (4 * π ^ 2 * Real.exp (-2 * β * |p.1|)) := by rw [hc₂_def]; ring
            _ ≤ spinV1 a p.1 * spinV1 a p.2 := hmul
        have : |Φ p| * Real.exp (κ * |p.1|) ≤ g3 p := by
          dsimp [g3]
          have hmul := mul_le_mul_of_nonneg_left hprod (abs_nonneg (Φ p))
          have hdiv : c₂⁻¹ * (|Φ p| * (c₂ * Real.exp (κ * |p.1|))) ≤
              c₂⁻¹ * (|Φ p| * (spinV1 a p.1 * spinV1 a p.2)) :=
            mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hc₂_pos.le)
          have hcancel : c₂⁻¹ * (|Φ p| * (c₂ * Real.exp (κ * |p.1|))) =
              |Φ p| * Real.exp (κ * |p.1|) := by
            field_simp [hc₂_pos.ne']
          linarith [show |Φ p| * (spinV1 a p.1 * spinV1 a p.2) =
            |Φ p| * spinV1 a p.1 * spinV1 a p.2 by ring]
        linarith
  have hmeas_f : AEStronglyMeasurable
      (fun p : ℝ × ℝ => |Φ p| * Real.exp (κ * |p.1|)) volume :=
    ((continuous_abs.comp hΦ.cont).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_abs.comp continuous_fst)))).aestronglyMeasurable
  have hint_f : Integrable (fun p : ℝ × ℝ => |Φ p| * Real.exp (κ * |p.1|)) := by
    refine ((hg1_int.add hg2_int).add hg3_int).mono' hmeas_f (Eventually.of_forall fun p => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)]
    exact hpt p
  refine ⟨hint_f, ?_⟩
  have hint_g1 : ∫ p : ℝ × ℝ, g1 p ≤ C₀ * Real.exp κ * spinM2 a Φ := by
    dsimp [g1]; rw [integral_const_mul]
    nlinarith [Real.exp_pos κ]
  have hint_g2 : ∫ p : ℝ × ℝ, g2 p = 2 * C₀ * Iδ * spinM2 a Φ := by
    rw [Measure.volume_eq_prod, integral_prod _ (by rwa [← Measure.volume_eq_prod])]
    have hslice : ∀ x : ℝ, ∫ y : ℝ, g2 (x, y) = 2 * C₀ * spinM2 a Φ * Real.exp (-δ * |x|) := by
      intro x
      have hsub : (fun y : ℝ => g2 (x, y)) =
          (Icc (-Real.exp (-β * |x|)) (Real.exp (-β * |x|))).indicator
            (fun _ => C₀ * spinM2 a Φ * Real.exp (κ * |x|)) := by
        ext y; simp only [g2, Set.indicator, S, mem_ofPred_eq, mem_Icc, abs_le]
      rw [hsub, integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
          Measure.real_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.exp_pos (-β * |x|)])]
      have hexp : Real.exp (-β * |x|) * Real.exp (κ * |x|) = Real.exp (-δ * |x|) := by
        rw [← Real.exp_add]; congr 1; rw [hδ_def]; ring
      calc (Real.exp (-β * |x|) - -Real.exp (-β * |x|)) *
            (C₀ * spinM2 a Φ * Real.exp (κ * |x|))
          = 2 * C₀ * spinM2 a Φ * (Real.exp (-β * |x|) * Real.exp (κ * |x|)) := by ring
        _ = 2 * C₀ * spinM2 a Φ * Real.exp (-δ * |x|) := by rw [hexp]
    simp_rw [hslice]
    rw [integral_const_mul, ← hIδ_def]; ring
  have hint_g3 : ∫ p : ℝ × ℝ, g3 p = c₂⁻¹ * spinM2 a Φ := by
    dsimp [g3]; rw [integral_const_mul]; rfl
  have hsum_le : ∫ p : ℝ × ℝ, |Φ p| * Real.exp (κ * |p.1|) ≤
      (∫ p, g1 p) + (∫ p, g2 p) + (∫ p, g3 p) := by
    calc ∫ p : ℝ × ℝ, |Φ p| * Real.exp (κ * |p.1|)
        ≤ ∫ p : ℝ × ℝ, (g1 p + g2 p + g3 p) :=
          integral_mono hint_f ((hg1_int.add hg2_int).add hg3_int) hpt
      _ = (∫ p, g1 p + g2 p) + ∫ p, g3 p := integral_add (hg1_int.add hg2_int) hg3_int
      _ = (∫ p, g1 p) + (∫ p, g2 p) + (∫ p, g3 p) := by rw [integral_add hg1_int hg2_int]
  rw [hC_def]
  linarith

/-- Majorant weight `Θ_a(x, y) = V_1(x) V_1(y) + exp(-(π/2)(x² + y²))`. -/
noncomputable def spinTheta (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  spinV1 a p.1 * spinV1 a p.2 + Real.exp (-(π / 2) * (p.1 ^ 2 + p.2 ^ 2))

private lemma spinTheta_nonneg {a : ℝ} (ha : 2 ≤ a) (p : ℝ × ℝ) : 0 ≤ spinTheta a p :=
  add_nonneg (mul_nonneg (spinV1_nonneg ha p.1) (spinV1_nonneg ha p.2)) (Real.exp_pos _).le

private lemma spinTheta_swap (a : ℝ) (p : ℝ × ℝ) : spinTheta a p.swap = spinTheta a p := by
  unfold spinTheta; dsimp [Prod.swap]; ring_nf

private lemma spinTestClass_Theta_integrable {a : ℝ} (ha : 2 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ →
      Integrable (fun p : ℝ × ℝ => |Φ p| * spinTheta a p) ∧
      (∫ p : ℝ × ℝ, |Φ p| * spinTheta a p) ≤ C * spinM2 a Φ := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := spinTestClass_L1_le_M2 ha
  refine ⟨1 + C₀, by linarith, fun {Φ} hΦ => ?_⟩
  obtain ⟨_, hΦ_L1⟩ := hC₀ hΦ
  have hterm2 : Integrable (fun p : ℝ × ℝ => |Φ p| * Real.exp (-(π / 2) * (p.1 ^ 2 + p.2 ^ 2))) := by
    refine hΦ.int.abs.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((continuous_abs.comp hΦ.cont).mul
        (Real.continuous_exp.comp (continuous_const.mul
          ((continuous_fst.pow 2).add (continuous_snd.pow 2))))).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)]
      have hexp : Real.exp (-(π / 2) * (p.1 ^ 2 + p.2 ^ 2)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg p.1, sq_nonneg p.2])
      simpa using mul_le_mul_of_nonneg_left hexp (abs_nonneg (Φ p))
  have hsplit : (fun p : ℝ × ℝ => |Φ p| * spinTheta a p) =
      fun p => |Φ p| * spinV1 a p.1 * spinV1 a p.2 +
        |Φ p| * Real.exp (-(π / 2) * (p.1 ^ 2 + p.2 ^ 2)) := by
    ext p; unfold spinTheta; ring
  rw [hsplit]
  refine ⟨hΦ.int_M2.add hterm2, ?_⟩
  rw [integral_add hΦ.int_M2 hterm2]
  have hle2 : ∫ p : ℝ × ℝ, |Φ p| * Real.exp (-(π / 2) * (p.1 ^ 2 + p.2 ^ 2)) ≤ ∫ p, |Φ p| := by
    refine integral_mono hterm2 hΦ.int.abs fun p => ?_
    have hexp : Real.exp (-(π / 2) * (p.1 ^ 2 + p.2 ^ 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg p.1, sq_nonneg p.2])
    simpa using mul_le_mul_of_nonneg_left hexp (abs_nonneg (Φ p))
  have : ∫ p : ℝ × ℝ, |Φ p| * spinV1 a p.1 * spinV1 a p.2 = spinM2 a Φ := rfl
  linarith

/-! ### Section 2: 1D Mehler kernel `spinMehlerKernel1D` identities and `U_r` estimates -/

/-- Convenience parameters for the 1D Mehler kernel in `r`-coordinates:
`τ_r = π (1 - r) / (1 + r)`, `α_r = π (1 + r) / (1 - r)`, `λ_r = 2 √r / (1 + r)`. -/
private noncomputable def mTau (r : ℝ) : ℝ := π * ((1 - r) / (1 + r))
private noncomputable def mAlpha (r : ℝ) : ℝ := π * ((1 + r) / (1 - r))
private noncomputable def mLam (r : ℝ) : ℝ := 2 * Real.sqrt r / (1 + r)

private lemma mTau_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : 0 < mTau r :=
  mul_pos Real.pi_pos (div_pos (sub_pos.mpr hr1) (by linarith))

private lemma mTau_le {r : ℝ} (hr12 : (1 / 2 : ℝ) ≤ r) : mTau r ≤ π / 3 := by
  unfold mTau
  have h1 : (1 - r) / (1 + r) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  nlinarith [Real.pi_pos]

private lemma mAlpha_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : 0 < mAlpha r :=
  mul_pos Real.pi_pos (div_pos (by linarith) (sub_pos.mpr hr1))

private lemma mAlpha_mul_mTau {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    mAlpha r * mTau r = π ^ 2 := by
  unfold mAlpha mTau
  have h1 : (1 - r) ≠ 0 := by linarith
  have h2 : (1 + r) ≠ 0 := by linarith
  field_simp

private lemma mLam_pos {r : ℝ} (hr0 : 0 < r) : 0 < mLam r := by
  unfold mLam; positivity

private lemma mLam_le_one {r : ℝ} (hr0 : 0 ≤ r) : mLam r ≤ 1 := by
  unfold mLam
  rw [div_le_one (by linarith)]
  have : (Real.sqrt r - 1) ^ 2 ≥ 0 := sq_nonneg _
  have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0
  nlinarith

private lemma mLam_gt_three_fourths {r : ℝ} (hr12 : (1 / 2 : ℝ) ≤ r) (hr1 : r < 1) :
    (3 / 4 : ℝ) < mLam r := by
  unfold mLam
  rw [lt_div_iff₀ (by linarith)]
  have hsq : (3 * (1 + r) / 8) ^ 2 < r := by
    have : 64 * r - 9 * (1 + r) ^ 2 = (1 - r) * (9 * r - 9) + 64 * r - 9 * (1 + r) ^ 2 +
        (1 - r) * (9 - 9 * r) := by ring
    nlinarith
  have hlt : 3 * (1 + r) / 8 < Real.sqrt r := by
    rw [← Real.sqrt_sq (by linarith : 0 ≤ 3 * (1 + r) / 8)]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hsq
  linarith

private lemma spinMehlerKernel1D_nonneg {r : ℝ} (_hr1 : r < 1) (x u : ℝ) :
    0 ≤ spinMehlerKernel1D r x u := by
  unfold spinMehlerKernel1D
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le

private lemma spinMehlerKernel1D_eq_symm_form {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x u : ℝ) :
    spinMehlerKernel1D r x u =
      Real.sqrt (2 / (1 - r)) *
        Real.exp (-π * ((1 + r) * (x ^ 2 + u ^ 2) - 4 * Real.sqrt r * x * u) / (1 - r)) := by
  unfold spinMehlerKernel1D
  congr 2
  have h1 : (1 - r) ≠ 0 := by linarith
  have h2 : (1 + r) ≠ 0 := by linarith
  have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0
  have hnum : -π * ((1 - r) / (1 + r)) * x ^ 2 -
      π * ((1 + r) / (1 - r)) * (u - 2 * Real.sqrt r / (1 + r) * x) ^ 2 =
      -π * ((1 + r) * (x ^ 2 + u ^ 2) - 4 * Real.sqrt r * x * u) / (1 - r) := by
    field_simp
    ring_nf
    rw [hsq]; ring
  exact hnum

private lemma spinMehlerKernel1D_symm {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x u : ℝ) :
    spinMehlerKernel1D r x u = spinMehlerKernel1D r u x := by
  rw [spinMehlerKernel1D_eq_symm_form hr0 hr1 x u, spinMehlerKernel1D_eq_symm_form hr0 hr1 u x]
  congr 2; ring

private lemma spinMehlerKernel1D_neg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x u : ℝ) :
    spinMehlerKernel1D r (-x) (-u) = spinMehlerKernel1D r x u := by
  rw [spinMehlerKernel1D_eq_symm_form hr0 hr1 (-x) (-u), spinMehlerKernel1D_eq_symm_form hr0 hr1 x u]
  congr 2; ring

lemma spinMehlerKernel1D_prod_eq_mehlerKernel {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (p q : ℝ × ℝ) :
    spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2 =
      mehlerKernel 1 r
        ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![p.1, p.2])
        ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![q.1, q.2]) := by
  rw [spinMehlerKernel1D_eq_symm_form hr0 hr1 p.1 q.1,
      spinMehlerKernel1D_eq_symm_form hr0 hr1 p.2 q.2]
  unfold mehlerKernel
  have h1r : 0 < 1 - r := sub_pos.mpr hr1
  have hsqrt : Real.sqrt (2 / (1 - r)) * Real.sqrt (2 / (1 - r)) = ((1 - r) / 2) ^ (-(1 : ℝ)) := by
    rw [Real.mul_self_sqrt (by positivity), Real.rpow_neg_one, inv_div]
  have hnorm_p : ‖(EuclideanSpace.equiv (Fin 2) ℝ).symm ![p.1, p.2]‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  have hnorm_q : ‖(EuclideanSpace.equiv (Fin 2) ℝ).symm ![q.1, q.2]‖ ^ 2 = q.1 ^ 2 + q.2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  have hinner : @inner ℝ _ _
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![p.1, p.2])
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![q.1, q.2]) = p.1 * q.1 + p.2 * q.2 := by
    rw [PiLp.inner_apply]; simp [Fin.sum_univ_two, mul_comm]
  rw [Nat.cast_one, hnorm_p, hnorm_q, hinner]
  calc Real.sqrt (2 / (1 - r)) *
        Real.exp (-π * ((1 + r) * (p.1 ^ 2 + q.1 ^ 2) - 4 * Real.sqrt r * p.1 * q.1) / (1 - r)) *
        (Real.sqrt (2 / (1 - r)) *
        Real.exp (-π * ((1 + r) * (p.2 ^ 2 + q.2 ^ 2) - 4 * Real.sqrt r * p.2 * q.2) / (1 - r)))
      = (Real.sqrt (2 / (1 - r)) * Real.sqrt (2 / (1 - r))) *
        (Real.exp (-π * ((1 + r) * (p.1 ^ 2 + q.1 ^ 2) - 4 * Real.sqrt r * p.1 * q.1) / (1 - r)) *
         Real.exp (-π * ((1 + r) * (p.2 ^ 2 + q.2 ^ 2) - 4 * Real.sqrt r * p.2 * q.2) / (1 - r))) := by ring
    _ = ((1 - r) / 2) ^ (-(1 : ℝ)) *
        Real.exp (-π * ((1 + r) * (p.1 ^ 2 + p.2 ^ 2 + (q.1 ^ 2 + q.2 ^ 2)) -
          4 * Real.sqrt r * (p.1 * q.1 + p.2 * q.2)) / (1 - r)) := by
        rw [hsqrt, ← Real.exp_add]; congr 2; ring

private lemma integral_exp_neg_alpha_mul_cosh {α c μ : ℝ} (hα : 0 < α) :
    Integrable (fun u : ℝ => Real.exp (-α * (u - μ) ^ 2) * Real.cosh (c * u)) ∧
    (∫ u : ℝ, Real.exp (-α * (u - μ) ^ 2) * Real.cosh (c * u)) =
      Real.sqrt (π / α) * Real.exp (c ^ 2 / (4 * α)) * Real.cosh (c * μ) := by
  have hshift : ∀ s : ℝ, Real.exp (-α * (s + μ - μ) ^ 2) * Real.cosh (c * (s + μ)) =
      (1 / 2 : ℝ) * (Real.exp (c * μ) * Real.exp (-α * s ^ 2 + c * s) +
        Real.exp (-(c * μ)) * Real.exp (-α * s ^ 2 - c * s)) := by
    intro s
    rw [add_sub_cancel_right, Real.cosh_eq]
    have h1 : Real.exp (-α * s ^ 2) * Real.exp (c * (s + μ)) =
        Real.exp (c * μ) * Real.exp (-α * s ^ 2 + c * s) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (-α * s ^ 2) * Real.exp (-(c * (s + μ))) =
        Real.exp (-(c * μ)) * Real.exp (-α * s ^ 2 - c * s) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    linear_combination (1 / 2 : ℝ) * h1 + (1 / 2 : ℝ) * h2
  have hint_lin : ∀ k : ℝ, Integrable (fun s : ℝ => Real.exp (-α * s ^ 2 + k * s)) ∧
      (∫ s : ℝ, Real.exp (-α * s ^ 2 + k * s)) = Real.sqrt (π / α) * Real.exp (k ^ 2 / (4 * α)) := by
    intro k
    have hcomp : ∀ s : ℝ, Real.exp (-α * s ^ 2 + k * s) =
        Real.exp (k ^ 2 / (4 * α)) * Real.exp (-α * (s - k / (2 * α)) ^ 2) := by
      intro s; rw [← Real.exp_add]; congr 1; field_simp [hα.ne']; ring
    simp_rw [hcomp]
    have hg : Integrable (fun s : ℝ => Real.exp (-α * (s - k / (2 * α)) ^ 2)) :=
      (integrable_exp_neg_mul_sq hα).comp_sub_right (k / (2 * α))
    refine ⟨hg.const_mul _, ?_⟩
    rw [integral_const_mul, integral_sub_right_eq_self (fun s => Real.exp (-α * s ^ 2)),
        integral_gaussian α]
    ring
  have h1 := hint_lin c
  have h2 := hint_lin (-c)
  have h2' : Integrable (fun s : ℝ => Real.exp (-α * s ^ 2 - c * s)) ∧
      (∫ s : ℝ, Real.exp (-α * s ^ 2 - c * s)) = Real.sqrt (π / α) * Real.exp (c ^ 2 / (4 * α)) := by
    simpa [sub_eq_add_neg, neg_mul, neg_sq] using h2
  have hint_s : Integrable (fun s : ℝ =>
      Real.exp (-α * (s + μ - μ) ^ 2) * Real.cosh (c * (s + μ))) := by
    simp_rw [hshift]
    exact ((h1.1.const_mul _).add (h2'.1.const_mul _)).const_mul _
  have hint_u : Integrable (fun u : ℝ => Real.exp (-α * (u - μ) ^ 2) * Real.cosh (c * u)) := by
    have := hint_s.comp_sub_right μ
    simpa [sub_add_cancel] using this
  refine ⟨hint_u, ?_⟩
  rw [← integral_add_right_eq_self (fun u => Real.exp (-α * (u - μ) ^ 2) * Real.cosh (c * u)) μ]
  simp_rw [hshift]
  rw [integral_const_mul, integral_add (h1.1.const_mul _) (h2'.1.const_mul _),
      integral_const_mul, integral_const_mul, h1.2, h2'.2, Real.cosh_eq]
  ring

private lemma integral_spinMehlerKernel1D_cosh {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {b : ℝ} (hb : 0 ≤ b) (x : ℝ) :
    Integrable (fun u : ℝ => spinMehlerKernel1D r x u * Real.cosh (2 * π * Real.sqrt b * u)) ∧
    (∫ u : ℝ, spinMehlerKernel1D r x u * Real.cosh (2 * π * Real.sqrt b * u)) =
      Real.sqrt (2 / (1 + r)) * Real.exp (-mTau r * x ^ 2 + b * mTau r) *
        Real.cosh (2 * π * Real.sqrt b * (mLam r * x)) := by
  have hα := mAlpha_pos hr0 hr1
  have h1r : 0 < 1 - r := sub_pos.mpr hr1
  have h1rp : 0 < 1 + r := by linarith
  have hpt : ∀ u : ℝ, spinMehlerKernel1D r x u * Real.cosh (2 * π * Real.sqrt b * u) =
      (Real.sqrt (2 / (1 - r)) * Real.exp (-mTau r * x ^ 2)) *
        (Real.exp (-mAlpha r * (u - mLam r * x) ^ 2) * Real.cosh (2 * π * Real.sqrt b * u)) := by
    intro u
    unfold spinMehlerKernel1D mTau mAlpha mLam
    have hexp : Real.exp (-π * ((1 - r) / (1 + r)) * x ^ 2 -
        π * ((1 + r) / (1 - r)) * (u - 2 * Real.sqrt r / (1 + r) * x) ^ 2) =
        Real.exp (-(π * ((1 - r) / (1 + r))) * x ^ 2) *
        Real.exp (-(π * ((1 + r) / (1 - r))) * (u - 2 * Real.sqrt r / (1 + r) * x) ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hexp]; ring
  simp_rw [hpt]
  have hi := integral_exp_neg_alpha_mul_cosh (c := 2 * π * Real.sqrt b) (μ := mLam r * x) hα
  refine ⟨hi.1.const_mul _, ?_⟩
  rw [integral_const_mul, hi.2]
  have hsqrt : Real.sqrt (2 / (1 - r)) * Real.sqrt (π / mAlpha r) = Real.sqrt (2 / (1 + r)) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    unfold mAlpha
    field_simp [Real.pi_pos.ne', h1r.ne', h1rp.ne']
  have hexp_c : (2 * π * Real.sqrt b) ^ 2 / (4 * mAlpha r) = b * mTau r := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hb]
    unfold mAlpha mTau
    field_simp [Real.pi_pos.ne', h1r.ne', h1rp.ne']
    ring
  rw [hexp_c]
  calc Real.sqrt (2 / (1 - r)) * Real.exp (-mTau r * x ^ 2) *
        (Real.sqrt (π / mAlpha r) * Real.exp (b * mTau r) *
          Real.cosh (2 * π * Real.sqrt b * (mLam r * x)))
      = (Real.sqrt (2 / (1 - r)) * Real.sqrt (π / mAlpha r)) *
        (Real.exp (-mTau r * x ^ 2) * Real.exp (b * mTau r)) *
        Real.cosh (2 * π * Real.sqrt b * (mLam r * x)) := by ring
    _ = Real.sqrt (2 / (1 + r)) * Real.exp (-mTau r * x ^ 2 + b * mTau r) *
        Real.cosh (2 * π * Real.sqrt b * (mLam r * x)) := by rw [hsqrt, ← Real.exp_add]

/-- `U_r(x) = ∫ K_r(x, u) V_1(u) du`. -/
private noncomputable def spinUr (a r x : ℝ) : ℝ :=
  ∫ u : ℝ, spinMehlerKernel1D r x u * spinV1 a u

/-- `c_r = U_r(0) = √(2/(1+r)) (exp(a τ_r) - exp((a-2) τ_r))`. -/
private noncomputable def spinCr (a r : ℝ) : ℝ :=
  Real.sqrt (2 / (1 + r)) * (Real.exp (a * mTau r) - Real.exp ((a - 2) * mTau r))

private lemma spinUr_integrable {a r : ℝ} (ha : 2 ≤ a) (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    Integrable (fun u : ℝ => spinMehlerKernel1D r x u * spinV1 a u) := by
  have h1 := (integral_spinMehlerKernel1D_cosh hr0 hr1 (b := a) (by linarith) x).1
  have h2 := (integral_spinMehlerKernel1D_cosh hr0 hr1 (b := a - 2) (by linarith) x).1
  refine (h1.sub h2).congr (Eventually.of_forall fun u => ?_)
  dsimp [Pi.sub_apply]; unfold spinV1; ring

private lemma spinUr_eq {a r : ℝ} (ha : 2 ≤ a) (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    spinUr a r x =
      Real.sqrt (2 / (1 + r)) * Real.exp (-mTau r * x ^ 2 + a * mTau r) *
        spinV1 a (mLam r * x) +
      spinCr a r * Real.exp (-mTau r * x ^ 2) *
        Real.cosh (2 * π * Real.sqrt (a - 2) * (mLam r * x)) := by
  have h1 := integral_spinMehlerKernel1D_cosh hr0 hr1 (b := a) (by linarith) x
  have h2 := integral_spinMehlerKernel1D_cosh hr0 hr1 (b := a - 2) (by linarith) x
  have hsub : (fun u => spinMehlerKernel1D r x u * spinV1 a u) =
      fun u => spinMehlerKernel1D r x u * Real.cosh (2 * π * Real.sqrt a * u) -
        spinMehlerKernel1D r x u * Real.cosh (2 * π * Real.sqrt (a - 2) * u) := by
    ext u; unfold spinV1; ring
  unfold spinUr
  rw [hsub, integral_sub h1.1 h2.1, h1.2, h2.2]
  unfold spinV1 spinCr
  rw [Real.exp_add (-mTau r * x ^ 2) (a * mTau r),
      Real.exp_add (-mTau r * x ^ 2) ((a - 2) * mTau r)]
  ring

private lemma spinUr_zero {a r : ℝ} (ha : 2 ≤ a) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    spinUr a r 0 = spinCr a r := by
  rw [spinUr_eq ha hr0 hr1 0]
  simp [spinV1]

private lemma spinUr_nonneg {a r : ℝ} (ha : 2 ≤ a) (hr1 : r < 1) (x : ℝ) :
    0 ≤ spinUr a r x :=
  integral_nonneg fun u => mul_nonneg (spinMehlerKernel1D_nonneg hr1 x u) (spinV1_nonneg ha u)

private lemma spinCr_pos {a r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : 0 < spinCr a r := by
  unfold spinCr
  have hτ := mTau_pos hr0 hr1
  have hlt : (a - 2) * mTau r < a * mTau r := by nlinarith
  exact mul_pos (Real.sqrt_pos.mpr (by positivity)) (sub_pos.mpr (Real.exp_lt_exp.mpr hlt))

private lemma spinCr_le_mul_mTau {a : ℝ} (ha : 2 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ Ico (1 / 2 : ℝ) 1, spinCr a r ≤ C * mTau r := by
  refine ⟨4 * Real.exp (a * (π / 3)), by positivity, fun r ⟨hr12, hr1⟩ => ?_⟩
  unfold spinCr
  have hτ_pos := mTau_pos (by linarith) hr1
  have hτ_le := mTau_le hr12
  have hsqrt : Real.sqrt (2 / (1 + r)) ≤ 2 := by
    rw [Real.sqrt_le_iff]; refine ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ (by linarith)]; linarith
  have hexp_sub : Real.exp (a * mTau r) - Real.exp ((a - 2) * mTau r) ≤
      2 * mTau r * Real.exp (a * (π / 3)) := by
    have hfac : Real.exp (a * mTau r) - Real.exp ((a - 2) * mTau r) =
        Real.exp (a * mTau r) * (1 - Real.exp (-2 * mTau r)) := by
      rw [mul_sub, mul_one, ← Real.exp_add]; congr 2; ring
    have h1 : 1 - Real.exp (-2 * mTau r) ≤ 2 * mTau r := by
      have := Real.add_one_le_exp (-2 * mTau r); linarith
    have h2 : Real.exp (a * mTau r) ≤ Real.exp (a * (π / 3)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    rw [hfac]
    have hnn : 0 ≤ 1 - Real.exp (-2 * mTau r) := by
      have : Real.exp (-2 * mTau r) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    calc Real.exp (a * mTau r) * (1 - Real.exp (-2 * mTau r))
        ≤ Real.exp (a * (π / 3)) * (2 * mTau r) :=
          mul_le_mul h2 h1 hnn (Real.exp_pos _).le
      _ = 2 * mTau r * Real.exp (a * (π / 3)) := by ring
  calc Real.sqrt (2 / (1 + r)) * (Real.exp (a * mTau r) - Real.exp ((a - 2) * mTau r))
      ≤ 2 * (2 * mTau r * Real.exp (a * (π / 3))) :=
        mul_le_mul hsqrt hexp_sub (sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith))) (by norm_num)
    _ = 4 * Real.exp (a * (π / 3)) * mTau r := by ring

private lemma spinCr_tendsto_zero (a : ℝ) :
    Tendsto (spinCr a) (𝓝[<] 1) (𝓝 0) := by
  have hcont : ContinuousAt (spinCr a) 1 := by
    unfold spinCr mTau
    have h1 : ContinuousAt (fun r : ℝ => Real.sqrt (2 / (1 + r))) 1 :=
      Real.continuous_sqrt.continuousAt.comp
        (continuousAt_const.div (continuousAt_const.add continuousAt_id) (by norm_num))
    have hτ : ContinuousAt (fun r : ℝ => π * ((1 - r) / (1 + r))) 1 :=
      continuousAt_const.mul ((continuousAt_const.sub continuousAt_id).div
        (continuousAt_const.add continuousAt_id) (by norm_num))
    exact h1.mul ((Real.continuous_exp.continuousAt.comp (continuousAt_const.mul hτ)).sub
      (Real.continuous_exp.continuousAt.comp (continuousAt_const.mul hτ)))
  have hval : spinCr a 1 = 0 := by unfold spinCr mTau; simp
  simpa [hval] using hcont.tendsto.mono_left nhdsWithin_le_nhds

private lemma spinUr_bounds {a : ℝ} (ha : 2 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ Ico (1 / 2 : ℝ) 1,
      (∀ x : ℝ, 1 ≤ |x| → spinUr a r x ≤ C * Real.exp (-mTau r * x ^ 2) * spinV1 a x) ∧
      (∀ x : ℝ, |x| ≤ 1 → spinUr a r x ≤ C) ∧
      (∀ x : ℝ, spinUr a r x ≤ C * Real.exp (-mTau r * x ^ 2 + 2 * π * Real.sqrt a * |x|)) := by
  obtain ⟨βa, hβa_pos, hβa⟩ := spinV1_ge_cosh_away ha
  obtain ⟨Cc, hCc_pos, hCc⟩ := spinCr_le_mul_mTau ha
  set E_a : ℝ := Real.exp (a * (π / 3))
  set C1 : ℝ := 2 * E_a + Cc * (π / 3) * βa
  set C2 : ℝ := 2 * E_a * Real.cosh (2 * π * Real.sqrt a) + Cc * (π / 3) * Real.cosh (2 * π * Real.sqrt a)
  set C3 : ℝ := 2 * E_a + Cc * (π / 3)
  set C : ℝ := max (max C1 C2) C3
  have hC_pos : 0 < C := lt_of_lt_of_le (by positivity : 0 < C3) (le_max_right _ _)
  refine ⟨C, hC_pos, fun r hr => ?_⟩
  obtain ⟨hr12, hr1⟩ := hr
  have hr0 : 0 ≤ r := by linarith
  have hτ_pos := mTau_pos hr0 hr1
  have hτ_le := mTau_le hr12
  have hlam0 : 0 ≤ mLam r := (mLam_pos (by linarith)).le
  have hlam1 : mLam r ≤ 1 := mLam_le_one hr0
  have hsqrt : Real.sqrt (2 / (1 + r)) ≤ 2 := by
    rw [Real.sqrt_le_iff]; refine ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ (by linarith)]; linarith
  have hcr : spinCr a r ≤ Cc * (π / 3) :=
    (hCc r ⟨hr12, hr1⟩).trans (mul_le_mul_of_nonneg_left hτ_le hCc_pos.le)
  have hcosh_le : ∀ x : ℝ, Real.cosh (2 * π * Real.sqrt (a - 2) * (mLam r * x)) ≤
      Real.cosh (2 * π * Real.sqrt a * x) := fun x => by
    refine Real.cosh_le_cosh.mpr ?_
    have h1 : Real.sqrt (a - 2) ≤ Real.sqrt a := Real.sqrt_le_sqrt (by linarith)
    simp only [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)),
      abs_of_nonneg Real.pi_pos.le, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hlam0]
    have h2 : mLam r * |x| ≤ |x| := mul_le_of_le_one_left (abs_nonneg x) hlam1
    calc 2 * π * Real.sqrt (a - 2) * (mLam r * |x|)
        ≤ 2 * π * Real.sqrt a * (mLam r * |x|) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity)
      _ ≤ 2 * π * Real.sqrt a * |x| :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x => ?_⟩
  · rw [spinUr_eq ha hr0 hr1 x, Real.exp_add (-mTau r * x ^ 2) (a * mTau r)]
    have hI : Real.sqrt (2 / (1 + r)) * (Real.exp (-mTau r * x ^ 2) * Real.exp (a * mTau r)) *
        spinV1 a (mLam r * x) ≤
        2 * E_a * Real.exp (-mTau r * x ^ 2) * spinV1 a x := by
      have hEa : Real.exp (a * mTau r) ≤ E_a := Real.exp_le_exp.mpr (by nlinarith)
      have hV : spinV1 a (mLam r * x) ≤ spinV1 a x := spinV1_scale_le ha hlam0 hlam1 x
      have h1 : Real.sqrt (2 / (1 + r)) * Real.exp (a * mTau r) ≤ 2 * E_a :=
        mul_le_mul hsqrt hEa (Real.exp_pos _).le (by norm_num)
      have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-mTau r * x ^ 2)).le
      have h3 := mul_le_mul h2 hV (spinV1_nonneg ha _) (by positivity)
      linarith
    have hII : spinCr a r * Real.exp (-mTau r * x ^ 2) *
        Real.cosh (2 * π * Real.sqrt (a - 2) * (mLam r * x)) ≤
        Cc * (π / 3) * βa * Real.exp (-mTau r * x ^ 2) * spinV1 a x := by
      have hc1 : Real.cosh (2 * π * Real.sqrt (a - 2) * (mLam r * x)) ≤ βa * spinV1 a x :=
        (hcosh_le x).trans (hβa x hx)
      have h1 := mul_le_mul hcr hc1 (Real.cosh_pos _).le (by positivity)
      have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-mTau r * x ^ 2)).le
      linarith
    have hC1 : C1 ≤ C := (le_max_left C1 C2).trans (le_max_left _ C3)
    have hnn : 0 ≤ Real.exp (-mTau r * x ^ 2) * spinV1 a x :=
      mul_nonneg (Real.exp_pos _).le (spinV1_nonneg ha x)
    calc Real.sqrt (2 / (1 + r)) * (Real.exp (-mTau r * x ^ 2) * Real.exp (a * mTau r)) *
          spinV1 a (mLam r * x) +
          spinCr a r * Real.exp (-mTau r * x ^ 2) *
          Real.cosh (2 * π * Real.sqrt (a - 2) * (mLam r * x))
        ≤ C1 * Real.exp (-mTau r * x ^ 2) * spinV1 a x := by dsimp [C1]; linarith
      _ ≤ C * Real.exp (-mTau r * x ^ 2) * spinV1 a x := by nlinarith
  · rw [spinUr_eq ha hr0 hr1 x, Real.exp_add (-mTau r * x ^ 2) (a * mTau r)]
    have hexp_le1 : Real.exp (-mTau r * x ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
    have hEa : Real.exp (a * mTau r) ≤ E_a := Real.exp_le_exp.mpr (by nlinarith)
    have hV_le : spinV1 a (mLam r * x) ≤ Real.cosh (2 * π * Real.sqrt a) := by
      refine (spinV1_scale_le ha hlam0 hlam1 x).trans ((spinV1_le_cosh ha x).trans ?_)
      refine Real.cosh_le_cosh.mpr ?_
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * π * Real.sqrt a)]
      exact mul_le_of_le_one_right (by positivity) hx
    have hch_le : Real.cosh (2 * π * Real.sqrt (a - 2) * (mLam r * x)) ≤
        Real.cosh (2 * π * Real.sqrt a) := by
      refine (hcosh_le x).trans (Real.cosh_le_cosh.mpr ?_)
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * π * Real.sqrt a)]
      exact mul_le_of_le_one_right (by positivity) hx
    have hI : Real.sqrt (2 / (1 + r)) * (Real.exp (-mTau r * x ^ 2) * Real.exp (a * mTau r)) *
        spinV1 a (mLam r * x) ≤ 2 * E_a * Real.cosh (2 * π * Real.sqrt a) := by
      have h1 : Real.exp (-mTau r * x ^ 2) * Real.exp (a * mTau r) ≤ E_a := by
        calc Real.exp (-mTau r * x ^ 2) * Real.exp (a * mTau r)
            ≤ 1 * E_a := mul_le_mul hexp_le1 hEa (Real.exp_pos _).le zero_le_one
          _ = E_a := one_mul E_a
      have h2 : Real.sqrt (2 / (1 + r)) * (Real.exp (-mTau r * x ^ 2) * Real.exp (a * mTau r)) ≤
          2 * E_a := mul_le_mul hsqrt h1 (by positivity) (by norm_num)
      exact mul_le_mul h2 hV_le (spinV1_nonneg ha _) (by positivity)
    have hII : spinCr a r * Real.exp (-mTau r * x ^ 2) *
        Real.cosh (2 * π * Real.sqrt (a - 2) * (mLam r * x)) ≤
        Cc * (π / 3) * Real.cosh (2 * π * Real.sqrt a) := by
      have h1 : spinCr a r * Real.exp (-mTau r * x ^ 2) ≤ Cc * (π / 3) := by
        calc spinCr a r * Real.exp (-mTau r * x ^ 2)
            ≤ (Cc * (π / 3)) * 1 := mul_le_mul hcr hexp_le1 (Real.exp_pos _).le (by positivity)
          _ = Cc * (π / 3) := mul_one _
      exact mul_le_mul h1 hch_le (Real.cosh_pos _).le (by positivity)
    have hC2 : C2 ≤ C := (le_max_right C1 C2).trans (le_max_left _ C3)
    dsimp [C2] at hC2; linarith
  · rw [spinUr_eq ha hr0 hr1 x, Real.exp_add (-mTau r * x ^ 2) (a * mTau r),
        Real.exp_add (-mTau r * x ^ 2) (2 * π * Real.sqrt a * |x|)]
    have hEa : Real.exp (a * mTau r) ≤ E_a := Real.exp_le_exp.mpr (by nlinarith)
    have hV_le : spinV1 a (mLam r * x) ≤ Real.exp (2 * π * Real.sqrt a * |x|) :=
      (spinV1_scale_le ha hlam0 hlam1 x).trans (spinV1_le_exp ha x)
    have hch_le : Real.cosh (2 * π * Real.sqrt (a - 2) * (mLam r * x)) ≤
        Real.exp (2 * π * Real.sqrt a * |x|) := by
      refine (hcosh_le x).trans ?_
      rw [Real.cosh_eq]
      have h1 : Real.exp (2 * π * Real.sqrt a * x) ≤ Real.exp (2 * π * Real.sqrt a * |x|) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self x) (by positivity))
      have h2 : Real.exp (-(2 * π * Real.sqrt a * x)) ≤ Real.exp (2 * π * Real.sqrt a * |x|) := by
        refine Real.exp_le_exp.mpr ?_
        have hmul : 2 * π * Real.sqrt a * (-x) ≤ 2 * π * Real.sqrt a * |x| :=
          mul_le_mul_of_nonneg_left (neg_le_abs x) (by positivity)
        linarith
      linarith
    have hI : Real.sqrt (2 / (1 + r)) * (Real.exp (-mTau r * x ^ 2) * Real.exp (a * mTau r)) *
        spinV1 a (mLam r * x) ≤
        2 * E_a * (Real.exp (-mTau r * x ^ 2) * Real.exp (2 * π * Real.sqrt a * |x|)) := by
      have h1 : Real.sqrt (2 / (1 + r)) * Real.exp (a * mTau r) ≤ 2 * E_a :=
        mul_le_mul hsqrt hEa (Real.exp_pos _).le (by norm_num)
      have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-mTau r * x ^ 2)).le
      have h3 := mul_le_mul h2 hV_le (spinV1_nonneg ha _) (by positivity)
      linarith
    have hII : spinCr a r * Real.exp (-mTau r * x ^ 2) *
        Real.cosh (2 * π * Real.sqrt (a - 2) * (mLam r * x)) ≤
        Cc * (π / 3) * (Real.exp (-mTau r * x ^ 2) * Real.exp (2 * π * Real.sqrt a * |x|)) := by
      have h1 := mul_le_mul hcr hch_le (Real.cosh_pos _).le (by positivity)
      have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-mTau r * x ^ 2)).le
      linarith
    have hC3 : C3 ≤ C := le_max_right _ C3
    have hnn : 0 ≤ Real.exp (-mTau r * x ^ 2) * Real.exp (2 * π * Real.sqrt a * |x|) := by positivity
    calc Real.sqrt (2 / (1 + r)) * (Real.exp (-mTau r * x ^ 2) * Real.exp (a * mTau r)) *
          spinV1 a (mLam r * x) +
          spinCr a r * Real.exp (-mTau r * x ^ 2) *
          Real.cosh (2 * π * Real.sqrt (a - 2) * (mLam r * x))
        ≤ C3 * (Real.exp (-mTau r * x ^ 2) * Real.exp (2 * π * Real.sqrt a * |x|)) := by
          dsimp [C3]; linarith
      _ ≤ C * (Real.exp (-mTau r * x ^ 2) * Real.exp (2 * π * Real.sqrt a * |x|)) :=
          mul_le_mul_of_nonneg_right hC3 hnn

/-! ### Section 3: Fourier-even subtraction `F_r`, orthogonality, and Fourier-space bound -/

private noncomputable def vE2ToProd : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))

private lemma vVolume_preserving_e2ToProd : MeasurePreserving vE2ToProd volume volume :=
  (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).comp (PiLp.volume_preserving_ofLp (Fin 2))

private lemma vE2ToProd_apply (x : EuclideanSpace ℝ (Fin 2)) : vE2ToProd x = (x 0, x 1) := rfl

private lemma vE2ToProd_symm_apply_zero (p : ℝ × ℝ) : (vE2ToProd.symm p) 0 = p.1 := rfl
private lemma vE2ToProd_symm_apply_one (p : ℝ × ℝ) : (vE2ToProd.symm p) 1 = p.2 := rfl

/-- 1D Fourier transform of `x ↦ exp(-π x²)` is `ω ↦ exp(-π ω²)`. -/
private lemma v_fourier_gaussian_unit (ω : ℝ) :
    ∫ x : ℝ, Real.fourierChar (-(x * ω)) • (Real.exp (-π * x ^ 2) : ℂ) =
      (Real.exp (-π * ω ^ 2) : ℂ) := by
  have h1 : ∫ x : ℝ, Real.fourierChar (-(x * ω)) • (Real.exp (-π * x ^ 2) : ℂ) =
      𝓕 (fun x : ℝ => (Real.exp (-π * x ^ 2) : ℂ)) ω := by
    rw [Real.fourier_eq]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [mul_comm]
  rw [h1]
  have hb : 0 < ((π : ℝ) : ℂ).re := by simp [Real.pi_pos]
  have hfn : (fun x : ℝ => (Real.exp (-π * x ^ 2) : ℂ)) =
      fun x : ℝ => Complex.exp (-((π : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2) := by
    ext x; rw [Complex.ofReal_exp]
    have hnx : (‖x‖ : ℂ) ^ 2 = ((x ^ 2 : ℝ) : ℂ) := by
      rw [Real.norm_eq_abs, ← Complex.ofReal_pow, sq_abs]
    rw [hnx]; congr 1; push_cast; ring
  rw [hfn, fourier_gaussian_innerProductSpace hb ω]
  have hdim : (Module.finrank ℝ ℝ / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by simp
  have hpi : ((π : ℝ) : ℂ) / ((π : ℝ) : ℂ) = 1 :=
    div_self (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  have hnw : (‖ω‖ : ℂ) ^ 2 = ((ω ^ 2 : ℝ) : ℂ) := by
    rw [Real.norm_eq_abs, ← Complex.ofReal_pow, sq_abs]
  rw [hdim, hpi, Complex.one_cpow, one_mul, hnw, Complex.ofReal_exp]
  congr 1; push_cast; field_simp [Real.pi_pos.ne']

/-- 1D Fourier transform of `x ↦ exp(-π x²) * cos(2π M x y)`. -/
private lemma v_fourier_gaussian_cos (M y ξ : ℝ) :
    ∫ x : ℝ, Real.fourierChar (-(x * ξ)) •
        ((Real.exp (-π * x ^ 2) * Real.cos (2 * π * M * x * y) : ℝ) : ℂ) =
      ((1 / 2 : ℝ) : ℂ) *
        ((Real.exp (-π * (ξ - M * y) ^ 2) : ℂ) + (Real.exp (-π * (ξ + M * y) ^ 2) : ℂ)) := by
  have hcos : ∀ x : ℝ, ((Real.cos (2 * π * M * x * y) : ℝ) : ℂ) =
      ((1 / 2 : ℝ) : ℂ) *
        ((Real.fourierChar (M * x * y) : ℂ) + (Real.fourierChar (-(M * x * y)) : ℂ)) := by
    intro x
    rw [Real.fourierChar_apply, Real.fourierChar_apply, Complex.ofReal_cos, Complex.cos]
    have h1 : (2 * π * (M * x * y) : ℝ) = 2 * π * M * x * y := by ring
    have h2 : (2 * π * -(M * x * y) : ℝ) = -(2 * π * M * x * y) := by ring
    rw [h1, h2, Complex.ofReal_neg, neg_mul]
    push_cast; ring
  have hpt : ∀ x : ℝ, Real.fourierChar (-(x * ξ)) •
      ((Real.exp (-π * x ^ 2) * Real.cos (2 * π * M * x * y) : ℝ) : ℂ) =
      ((1 / 2 : ℝ) : ℂ) *
        (Real.fourierChar (-(x * (ξ - M * y))) • (Real.exp (-π * x ^ 2) : ℂ) +
         Real.fourierChar (-(x * (ξ + M * y))) • (Real.exp (-π * x ^ 2) : ℂ)) := by
    intro x
    rw [Complex.ofReal_mul, hcos x]
    simp only [Circle.smul_def, smul_eq_mul]
    have hc1 : (Real.fourierChar (-(x * ξ)) : ℂ) * (Real.fourierChar (M * x * y) : ℂ) =
        (Real.fourierChar (-(x * (ξ - M * y))) : ℂ) := by
      have : (Real.fourierChar (-(x * ξ) + M * x * y) : ℂ) =
          (Real.fourierChar (-(x * ξ)) : ℂ) * (Real.fourierChar (M * x * y) : ℂ) := by
        rw [AddChar.map_add_eq_mul]; rfl
      rw [← this]; congr 2; ring
    have hc2 : (Real.fourierChar (-(x * ξ)) : ℂ) * (Real.fourierChar (-(M * x * y)) : ℂ) =
        (Real.fourierChar (-(x * (ξ + M * y))) : ℂ) := by
      have : (Real.fourierChar (-(x * ξ) + -(M * x * y)) : ℂ) =
          (Real.fourierChar (-(x * ξ)) : ℂ) * (Real.fourierChar (-(M * x * y)) : ℂ) := by
        rw [AddChar.map_add_eq_mul]; rfl
      rw [← this]; congr 2; ring
    linear_combination ((1 / 2 : ℝ) : ℂ) * (Real.exp (-π * x ^ 2) : ℂ) * (hc1 + hc2)
  simp_rw [hpt]
  have hint_g : ∀ ω : ℝ, Integrable (fun x : ℝ =>
      Real.fourierChar (-(x * ω)) • (Real.exp (-π * x ^ 2) : ℂ)) := fun ω => by
    refine (integrable_exp_neg_mul_sq Real.pi_pos).mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact ((Real.continuous_fourierChar.comp (continuous_id.mul continuous_const).neg).smul
        (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
          (continuous_const.mul (continuous_id.pow 2))))).aestronglyMeasurable
    · rw [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [integral_const_mul, integral_add (hint_g _) (hint_g _),
      v_fourier_gaussian_unit (ξ - M * y), v_fourier_gaussian_unit (ξ + M * y)]

/-- Exact 1D Gaussian convolution:
`∫ y, exp(-π (ξ - sgn * M * y)²) * K_r(v, y) dy ≤ 2 * exp(-π / 23 * (ξ - sgn * M * λ_r * v)²)`. -/
private lemma v_gauss_conv_mehler {r : ℝ} (hr12 : (1 / 2 : ℝ) ≤ r) (hr1 : r < 1)
    (sgn : ℝ) (hsgn : sgn ^ 2 = 1) (ξ v : ℝ) :
    Integrable (fun y : ℝ => Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) * spinMehlerKernel1D r v y) ∧
    (∫ y : ℝ, Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) * spinMehlerKernel1D r v y) ≤
      2 * Real.exp (-π / 23 * (ξ - sgn * 8 * (mLam r * v)) ^ 2) := by
  have hr0 : 0 ≤ r := by linarith
  have h1r : 0 < 1 - r := sub_pos.mpr hr1
  have h1rp : 0 < 1 + r := by linarith
  have hα : 0 < mAlpha r := mAlpha_pos hr0 hr1
  set A : ℝ := mAlpha r + 64 * π with hA_def
  have hA_pos : 0 < A := by rw [hA_def]; positivity
  set b : ℝ := ξ - sgn * 8 * (mLam r * v) with hb_def
  -- Rewrite exponent in shifted variable `s = y - mLam r * v`
  have hshift : ∀ s : ℝ,
      Real.exp (-π * (ξ - sgn * 8 * (s + mLam r * v)) ^ 2) *
        spinMehlerKernel1D r v (s + mLam r * v) =
      (Real.sqrt (2 / (1 - r)) * Real.exp (-mTau r * v ^ 2) *
        Real.exp (-(π * mAlpha r / A) * b ^ 2)) *
        Real.exp (-A * (s - (8 * π * sgn * b) / A) ^ 2) := by
    intro s
    unfold spinMehlerKernel1D mTau mAlpha mLam
    rw [add_sub_cancel_right]
    have hmul_exp : Real.exp (-π * (ξ - sgn * 8 * (s + 2 * Real.sqrt r / (1 + r) * v)) ^ 2) *
        (Real.sqrt (2 / (1 - r)) *
          Real.exp (-π * ((1 - r) / (1 + r)) * v ^ 2 -
            π * ((1 + r) / (1 - r)) * s ^ 2)) =
        Real.sqrt (2 / (1 - r)) *
          Real.exp (-π * (b - sgn * 8 * s) ^ 2 - π * ((1 - r) / (1 + r)) * v ^ 2 -
            π * ((1 + r) / (1 - r)) * s ^ 2) := by
      have hb_eq : ξ - sgn * 8 * (s + 2 * Real.sqrt r / (1 + r) * v) = b - sgn * 8 * s := by
        rw [hb_def]; unfold mLam; ring
      rw [hb_eq]
      calc Real.exp (-π * (b - sgn * 8 * s) ^ 2) *
            (Real.sqrt (2 / (1 - r)) *
              Real.exp (-π * ((1 - r) / (1 + r)) * v ^ 2 - π * ((1 + r) / (1 - r)) * s ^ 2))
          = Real.sqrt (2 / (1 - r)) *
            (Real.exp (-π * (b - sgn * 8 * s) ^ 2) *
              Real.exp (-π * ((1 - r) / (1 + r)) * v ^ 2 - π * ((1 + r) / (1 - r)) * s ^ 2)) := by ring
        _ = Real.sqrt (2 / (1 - r)) *
            Real.exp (-π * (b - sgn * 8 * s) ^ 2 - π * ((1 - r) / (1 + r)) * v ^ 2 -
              π * ((1 + r) / (1 - r)) * s ^ 2) := by rw [← Real.exp_add]; congr 2; ring
    rw [hmul_exp]
    have hrhs_exp : Real.sqrt (2 / (1 - r)) * Real.exp (-(π * ((1 - r) / (1 + r))) * v ^ 2) *
        Real.exp (-(π * (π * ((1 + r) / (1 - r))) / A) * b ^ 2) *
        Real.exp (-A * (s - 8 * π * sgn * b / A) ^ 2) =
        Real.sqrt (2 / (1 - r)) *
        Real.exp (-(π * ((1 - r) / (1 + r))) * v ^ 2 +
          -(π * (π * ((1 + r) / (1 - r))) / A) * b ^ 2 +
          -A * (s - 8 * π * sgn * b / A) ^ 2) := by
      rw [mul_assoc (Real.sqrt _), mul_assoc (Real.sqrt _), ← Real.exp_add, ← Real.exp_add]
    rw [hrhs_exp]
    congr 2
    have hA_eq : A = π * ((1 + r) / (1 - r)) + 64 * π := rfl
    have hA_ne : A ≠ 0 := hA_pos.ne'
    have h1r_ne : (1 - r) ≠ 0 := h1r.ne'
    have h1rp_ne : (1 + r) ≠ 0 := h1rp.ne'
    have hpi_ne : (π : ℝ) ≠ 0 := Real.pi_pos.ne'
    field_simp [hA_ne, h1r_ne, h1rp_ne]
    rw [hA_eq]
    field_simp [h1r_ne, h1rp_ne]
    ring_nf
    rw [hsgn]; ring
  have hint_s : Integrable (fun s : ℝ =>
      Real.exp (-π * (ξ - sgn * 8 * (s + mLam r * v)) ^ 2) *
        spinMehlerKernel1D r v (s + mLam r * v)) := by
    simp_rw [hshift]
    exact ((integrable_exp_neg_mul_sq hA_pos).comp_sub_right _).const_mul _
  have hint_y : Integrable (fun y : ℝ =>
      Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) * spinMehlerKernel1D r v y) := by
    have := hint_s.comp_sub_right (mLam r * v)
    simpa [sub_add_cancel] using this
  refine ⟨hint_y, ?_⟩
  rw [← integral_add_right_eq_self
    (fun y => Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) * spinMehlerKernel1D r v y) (mLam r * v)]
  simp_rw [hshift]
  rw [integral_const_mul, integral_sub_right_eq_self (fun s => Real.exp (-A * s ^ 2)),
      integral_gaussian A]
  -- Bound prefactor `√(2/(1-r)) * √(π/A) ≤ 2` and `exp(-mTau r v²) ≤ 1`
  have hpref : Real.sqrt (2 / (1 - r)) * Real.sqrt (π / A) ≤ 2 := by
    rw [← Real.sqrt_mul (by positivity), Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    have hA_ge : mAlpha r ≤ A := by rw [hA_def]; linarith [Real.pi_pos]
    have h1 : 2 / (1 - r) * (π / A) ≤ 2 / (1 - r) * (π / mAlpha r) := by
      gcongr
    have h2 : 2 / (1 - r) * (π / mAlpha r) = 2 / (1 + r) := by
      unfold mAlpha; field_simp [Real.pi_pos.ne', h1r.ne', h1rp.ne']
    have h3 : 2 / (1 + r) ≤ 4 := by rw [div_le_iff₀ h1rp]; linarith
    linarith
  have hexp_v : Real.exp (-mTau r * v ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mTau_pos hr0 hr1, sq_nonneg v])
  -- Bound exponent: `π * mAlpha r / A ≥ π / 23`
  have hexp_b : Real.exp (-(π * mAlpha r / A) * b ^ 2) ≤ Real.exp (-π / 23 * b ^ 2) := by
    refine Real.exp_le_exp.mpr ?_
    have hratio : π / 23 ≤ π * mAlpha r / A := by
      rw [div_le_div_iff₀ (by norm_num) hA_pos]
      rw [hA_def]
      have hα_ge : 3 * π ≤ mAlpha r := by
        unfold mAlpha
        have : (3 : ℝ) ≤ (1 + r) / (1 - r) := by rw [le_div_iff₀ h1r]; linarith
        nlinarith [Real.pi_pos]
      nlinarith [Real.pi_pos]
    have hmul : (π / 23) * b ^ 2 ≤ (π * mAlpha r / A) * b ^ 2 :=
      mul_le_mul_of_nonneg_right hratio (sq_nonneg b)
    linarith
  calc Real.sqrt (2 / (1 - r)) * Real.exp (-mTau r * v ^ 2) *
        Real.exp (-(π * mAlpha r / A) * b ^ 2) * Real.sqrt (π / A)
      = (Real.sqrt (2 / (1 - r)) * Real.sqrt (π / A)) *
        Real.exp (-mTau r * v ^ 2) * Real.exp (-(π * mAlpha r / A) * b ^ 2) := by ring
    _ ≤ 2 * 1 * Real.exp (-π / 23 * b ^ 2) := by
        have h1 : Real.sqrt (2 / (1 - r)) * Real.sqrt (π / A) * Real.exp (-mTau r * v ^ 2) ≤
            2 * 1 := mul_le_mul hpref hexp_v (Real.exp_pos _).le (by norm_num)
        exact mul_le_mul h1 hexp_b (Real.exp_pos _).le (by norm_num)
    _ = 2 * Real.exp (-π / 23 * b ^ 2) := by ring

/-- Fourier orthogonality: for `Φ ∈ SpinTestClass a` and any `g ∈ L¹(ℝ²)`,
`∫ p, Φ p * g p = - ∫ p, Φ p * (𝓕 (spinToEuc g) (vE2ToProd.symm p)).re`. -/
private lemma v_fourier_odd_pairing {a : ℝ} {Φ g : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) (hg : Integrable g) :
    Integrable (fun p : ℝ × ℝ => Φ p * g p) ∧
    Integrable (fun p : ℝ × ℝ => Φ p * (𝓕 (spinToEuc g) (vE2ToProd.symm p)).re) ∧
    (∫ p : ℝ × ℝ, Φ p * g p) =
      -(∫ p : ℝ × ℝ, Φ p * (𝓕 (spinToEuc g) (vE2ToProd.symm p)).re) := by
  have hΦ_bd : ∀ p : ℝ × ℝ, |Φ p| ≤ ∫ q : ℝ × ℝ, |Φ q| := by
    intro p
    have hEuc_int : Integrable (spinToEuc Φ) := by
      have h1 : Integrable (fun x : EuclideanSpace ℝ (Fin 2) => Φ (vE2ToProd x)) :=
        vVolume_preserving_e2ToProd.integrable_comp_of_integrable hΦ.int
      exact h1.ofReal
    have hval := congrFun hΦ.fourier_odd (vE2ToProd.symm p)
    have hnorm : ‖spinToEuc Φ (vE2ToProd.symm p)‖ = ‖𝓕 (spinToEuc Φ) (vE2ToProd.symm p)‖ := by
      rw [hval, Pi.neg_apply, norm_neg]
    have hle : ‖𝓕 (spinToEuc Φ) (vE2ToProd.symm p)‖ ≤ ∫ x : EuclideanSpace ℝ (Fin 2), ‖spinToEuc Φ x‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    have hLHS : ‖spinToEuc Φ (vE2ToProd.symm p)‖ = |Φ p| := by
      simp [spinToEuc, vE2ToProd_symm_apply_zero, vE2ToProd_symm_apply_one]
    have hRHS : ∫ x : EuclideanSpace ℝ (Fin 2), ‖spinToEuc Φ x‖ = ∫ q : ℝ × ℝ, |Φ q| := by
      have : (fun x : EuclideanSpace ℝ (Fin 2) => ‖spinToEuc Φ x‖) = fun x => |Φ (vE2ToProd x)| := by
        ext x; simp [spinToEuc, vE2ToProd_apply]
      rw [this, vVolume_preserving_e2ToProd.integral_comp' (g := fun q : ℝ × ℝ => |Φ q|)]
    linarith
  set BΦ : ℝ := ∫ q : ℝ × ℝ, |Φ q|
  have hBΦ_nn : 0 ≤ BΦ := integral_nonneg fun _ => abs_nonneg _
  have hEuc_g : Integrable (spinToEuc g) :=
    (vVolume_preserving_e2ToProd.integrable_comp_of_integrable hg).ofReal
  have hEuc_Φ : Integrable (spinToEuc Φ) :=
    (vVolume_preserving_e2ToProd.integrable_comp_of_integrable hΦ.int).ofReal
  have hgHat_bd : ∀ x : EuclideanSpace ℝ (Fin 2), ‖𝓕 (spinToEuc g) x‖ ≤ ∫ q : ℝ × ℝ, |g q| := by
    intro x
    have hle : ‖𝓕 (spinToEuc g) x‖ ≤ ∫ y : EuclideanSpace ℝ (Fin 2), ‖spinToEuc g y‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    have hRHS : ∫ y : EuclideanSpace ℝ (Fin 2), ‖spinToEuc g y‖ = ∫ q : ℝ × ℝ, |g q| := by
      have : (fun y : EuclideanSpace ℝ (Fin 2) => ‖spinToEuc g y‖) = fun y => |g (vE2ToProd y)| := by
        ext y; simp [spinToEuc, vE2ToProd_apply]
      rw [this, vVolume_preserving_e2ToProd.integral_comp' (g := fun q : ℝ × ℝ => |g q|)]
    exact hle.trans_eq hRHS
  have hgHat_cont : Continuous (𝓕 (spinToEuc g)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hEuc_g
  have hint_Φg : Integrable (fun p : ℝ × ℝ => Φ p * g p) := by
    refine (hg.abs.const_mul BΦ).mono' (hΦ.cont.aestronglyMeasurable.mul hg.aestronglyMeasurable)
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hΦ_bd p) (abs_nonneg _)
  have hint_ΦgHat : Integrable (fun p : ℝ × ℝ => Φ p * (𝓕 (spinToEuc g) (vE2ToProd.symm p)).re) := by
    refine (hΦ.int.abs.const_mul (∫ q : ℝ × ℝ, |g q|)).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hsymm_meas : Measurable (fun p : ℝ × ℝ => vE2ToProd.symm p) := vE2ToProd.symm.measurable
      have hm : Measurable (fun p : ℝ × ℝ => (𝓕 (spinToEuc g) (vE2ToProd.symm p)).re) :=
        Complex.continuous_re.measurable.comp (hgHat_cont.measurable.comp hsymm_meas)
      exact (hΦ.cont.measurable.mul hm).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      have hre : |(𝓕 (spinToEuc g) (vE2ToProd.symm p)).re| ≤ ∫ q : ℝ × ℝ, |g q| :=
        (Complex.abs_re_le_norm _).trans (hgHat_bd _)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hre (abs_nonneg _)
  refine ⟨hint_Φg, hint_ΦgHat, ?_⟩
  -- Complex Fubini identity: `∫ x, Φ x * 𝓕 g x = ∫ y, 𝓕 Φ y * g y = - ∫ y, Φ y * g y`
  have hprod_int : Integrable (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      Real.fourierChar (-⟪z.1, z.2⟫) • (spinToEuc Φ z.1 * spinToEuc g z.2)) := by
    have hprod_norm : Integrable (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
        ‖spinToEuc Φ z.1‖ * ‖spinToEuc g z.2‖) := hEuc_Φ.norm.mul_prod hEuc_g.norm
    refine hprod_norm.mono' ?_ (Eventually.of_forall fun z => ?_)
    · have hmeas_c : AEStronglyMeasurable
          (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
            Real.fourierChar (-⟪z.1, z.2⟫)) volume :=
        (Real.continuous_fourierChar.comp (continuous_inner.neg)).aestronglyMeasurable
      have hmeas_Φ : AEStronglyMeasurable
          (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => spinToEuc Φ z.1) volume :=
        hEuc_Φ.aestronglyMeasurable.comp_fst
      have hmeas_g : AEStronglyMeasurable
          (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => spinToEuc g z.2) volume :=
        hEuc_g.aestronglyMeasurable.comp_snd
      exact hmeas_c.smul (hmeas_Φ.mul hmeas_g)
    · rw [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul, norm_mul]
  have hfub : ∫ x : EuclideanSpace ℝ (Fin 2), spinToEuc Φ x * 𝓕 (spinToEuc g) x =
      -(∫ y : EuclideanSpace ℝ (Fin 2), spinToEuc Φ y * spinToEuc g y) := by
    have hL : ∫ x : EuclideanSpace ℝ (Fin 2), spinToEuc Φ x * 𝓕 (spinToEuc g) x =
        ∫ x : EuclideanSpace ℝ (Fin 2), ∫ y : EuclideanSpace ℝ (Fin 2),
          Real.fourierChar (-⟪x, y⟫) • (spinToEuc Φ x * spinToEuc g y) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      dsimp only
      rw [Real.fourier_eq, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      dsimp only
      rw [real_inner_comm]
      simp only [Circle.smul_def, smul_eq_mul]; ring
    have hR : ∫ y : EuclideanSpace ℝ (Fin 2), ∫ x : EuclideanSpace ℝ (Fin 2),
          Real.fourierChar (-⟪x, y⟫) • (spinToEuc Φ x * spinToEuc g y) =
        -(∫ y : EuclideanSpace ℝ (Fin 2), spinToEuc Φ y * spinToEuc g y) := by
      have hinner : ∀ y : EuclideanSpace ℝ (Fin 2),
          (∫ x : EuclideanSpace ℝ (Fin 2),
            Real.fourierChar (-⟪x, y⟫) • (spinToEuc Φ x * spinToEuc g y)) =
          -(spinToEuc Φ y * spinToEuc g y) := by
        intro y
        have heq : (fun x => Real.fourierChar (-⟪x, y⟫) • (spinToEuc Φ x * spinToEuc g y)) =
            fun x => (Real.fourierChar (-⟪x, y⟫) • spinToEuc Φ x) * spinToEuc g y := by
          ext x; simp only [Circle.smul_def, smul_eq_mul]; ring
        rw [heq, integral_mul_const, ← Real.fourier_eq, hΦ.fourier_odd, Pi.neg_apply, neg_mul]
      simp_rw [hinner, integral_neg]
    rw [hL, MeasureTheory.integral_integral_swap hprod_int, hR]
  -- Take real parts and transfer from `EuclideanSpace ℝ (Fin 2)` to `ℝ × ℝ`
  have hre_eq := congrArg Complex.re hfub
  have hLHS_re : (∫ x : EuclideanSpace ℝ (Fin 2), spinToEuc Φ x * 𝓕 (spinToEuc g) x).re =
      ∫ p : ℝ × ℝ, Φ p * (𝓕 (spinToEuc g) (vE2ToProd.symm p)).re := by
    have hint_c : Integrable (fun x : EuclideanSpace ℝ (Fin 2) =>
        spinToEuc Φ x * 𝓕 (spinToEuc g) x) := by
      refine (hEuc_Φ.norm.const_mul (∫ q : ℝ × ℝ, |g q|)).mono'
        (hEuc_Φ.aestronglyMeasurable.mul hgHat_cont.aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_)
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hgHat_bd x) (norm_nonneg _)
    change Complex.reCLM (∫ x : EuclideanSpace ℝ (Fin 2), spinToEuc Φ x * 𝓕 (spinToEuc g) x) = _
    rw [← Complex.reCLM.integral_comp_comm hint_c]
    have hpt : (fun x : EuclideanSpace ℝ (Fin 2) => Complex.reCLM (spinToEuc Φ x * 𝓕 (spinToEuc g) x)) =
        fun x => Φ (vE2ToProd x) * (𝓕 (spinToEuc g) (vE2ToProd.symm (vE2ToProd x))).re := by
      ext x
      change (spinToEuc Φ x * 𝓕 (spinToEuc g) x).re = _
      rw [MeasurableEquiv.symm_apply_apply]
      simp [spinToEuc, vE2ToProd_apply]
    rw [hpt, vVolume_preserving_e2ToProd.integral_comp'
      (g := fun p : ℝ × ℝ => Φ p * (𝓕 (spinToEuc g) (vE2ToProd.symm p)).re)]
  have hRHS_re : (-(∫ y : EuclideanSpace ℝ (Fin 2), spinToEuc Φ y * spinToEuc g y)).re =
      -(∫ p : ℝ × ℝ, Φ p * g p) := by
    have hint_c : Integrable (fun y : EuclideanSpace ℝ (Fin 2) =>
        spinToEuc Φ y * spinToEuc g y) := by
      have h1 : Integrable (fun y : EuclideanSpace ℝ (Fin 2) => Φ (vE2ToProd y) * g (vE2ToProd y)) :=
        vVolume_preserving_e2ToProd.integrable_comp_of_integrable hint_Φg
      exact h1.ofReal.congr (Eventually.of_forall fun y => by simp [spinToEuc, vE2ToProd_apply])
    rw [Complex.neg_re]
    change -(Complex.reCLM (∫ y : EuclideanSpace ℝ (Fin 2), spinToEuc Φ y * spinToEuc g y)) = _
    rw [← Complex.reCLM.integral_comp_comm hint_c]
    have hpt : (fun y : EuclideanSpace ℝ (Fin 2) => Complex.reCLM (spinToEuc Φ y * spinToEuc g y)) =
        fun y => Φ (vE2ToProd y) * g (vE2ToProd y) := by
      ext y; simp [spinToEuc, vE2ToProd_apply]
    rw [hpt, vVolume_preserving_e2ToProd.integral_comp' (g := fun p : ℝ × ℝ => Φ p * g p)]
  rw [hLHS_re, hRHS_re] at hre_eq
  linarith

/-! ### Section 4: Construction of `F_r`, `D_r`, position-space domination, and uniform bound -/

/-- Auxiliary functions for the `D_4`-invariant bounded measurable weight `h`:
`W(u, v) = h(u, v) V_1(u) V_1(v)`,
`β_r(v) = ∫ K_r(0, u) h(u, v) V_1(u) du`,
`α_r(y) = ∫ K_r(y, v) β_r(v) V_1(v) dv`,
`F_{r, L}(x, y) = exp(-π x²) cos(16π x y) α_r(y)`,
`F_r(x, y) = F_{r, L}(x, y) + F_{r, L}(y, x)`. -/
private noncomputable def vW (a : ℝ) (h : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  h p * spinV1 a p.1 * spinV1 a p.2

private noncomputable def vBeta (a r : ℝ) (h : ℝ × ℝ → ℝ) (v : ℝ) : ℝ :=
  ∫ u : ℝ, spinMehlerKernel1D r 0 u * h (u, v) * spinV1 a u

private noncomputable def vAlpha (a r : ℝ) (h : ℝ × ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ v : ℝ, spinMehlerKernel1D r y v * vBeta a r h v * spinV1 a v

private noncomputable def vFrL (a r : ℝ) (h : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-π * p.1 ^ 2) * Real.cos (2 * π * 8 * p.1 * p.2) * vAlpha a r h p.2

private noncomputable def vFr (a r : ℝ) (h : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  vFrL a r h p + vFrL a r h p.swap

private lemma vBeta_meas {a r : ℝ} (hh : Measurable h) : Measurable (vBeta a r h) := by
  unfold vBeta
  have h1 : Measurable (fun p : ℝ × ℝ => spinMehlerKernel1D r 0 p.2 * h (p.2, p.1) * spinV1 a p.2) := by
    have hK : Continuous (fun u : ℝ => spinMehlerKernel1D r 0 u) := by
      unfold spinMehlerKernel1D; fun_prop
    have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
    exact ((hK.measurable.comp measurable_snd).mul
      (hh.comp (measurable_snd.prodMk measurable_fst))).mul (hV.measurable.comp measurable_snd)
  exact h1.stronglyMeasurable.integral_prod_right'.measurable

private lemma vBeta_abs_le {a r M : ℝ} (ha : 2 ≤ a) (hr0 : 0 ≤ r) (hr1 : r < 1)
    {h : ℝ × ℝ → ℝ} (_hM : 0 ≤ M) (hh : Measurable h) (hbd : ∀ p, |h p| ≤ M) (v : ℝ) :
    |vBeta a r h v| ≤ M * spinCr a r := by
  unfold vBeta
  have hint : Integrable (fun u : ℝ => spinMehlerKernel1D r 0 u * h (u, v) * spinV1 a u) := by
    refine ((spinUr_integrable ha hr0 hr1 0).const_mul M).mono' ?_ (Eventually.of_forall fun u => ?_)
    · have hK : Continuous (fun u : ℝ => spinMehlerKernel1D r 0 u) := by
        unfold spinMehlerKernel1D; fun_prop
      have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
      exact (((hK.measurable.mul (hh.comp (measurable_id.prodMk measurable_const))).mul
        hV.measurable)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (spinMehlerKernel1D_nonneg hr1 0 u),
          abs_of_nonneg (spinV1_nonneg ha u)]
      have := mul_le_mul_of_nonneg_left (hbd (u, v)) (spinMehlerKernel1D_nonneg hr1 0 u)
      have := mul_le_mul_of_nonneg_right this (spinV1_nonneg ha u)
      linarith
  calc |∫ u : ℝ, spinMehlerKernel1D r 0 u * h (u, v) * spinV1 a u|
      ≤ ∫ u : ℝ, |spinMehlerKernel1D r 0 u * h (u, v) * spinV1 a u| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ u : ℝ, M * (spinMehlerKernel1D r 0 u * spinV1 a u) := by
        refine integral_mono hint.abs ((spinUr_integrable ha hr0 hr1 0).const_mul M) fun u => ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (spinMehlerKernel1D_nonneg hr1 0 u),
            abs_of_nonneg (spinV1_nonneg ha u)]
        have := mul_le_mul_of_nonneg_left (hbd (u, v)) (spinMehlerKernel1D_nonneg hr1 0 u)
        have := mul_le_mul_of_nonneg_right this (spinV1_nonneg ha u)
        linarith
    _ = M * spinCr a r := by
        rw [integral_const_mul, ← spinUr, spinUr_zero ha hr0 hr1]

private lemma vAlpha_meas {a r : ℝ} (hh : Measurable h) : Measurable (vAlpha a r h) := by
  unfold vAlpha
  have hK : Continuous (fun p : ℝ × ℝ => spinMehlerKernel1D r p.1 p.2) := by
    unfold spinMehlerKernel1D; fun_prop
  have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
  have h1 : Measurable (fun p : ℝ × ℝ =>
      spinMehlerKernel1D r p.1 p.2 * vBeta a r h p.2 * spinV1 a p.2) :=
    (hK.measurable.mul ((vBeta_meas hh).comp measurable_snd)).mul (hV.measurable.comp measurable_snd)
  exact h1.stronglyMeasurable.integral_prod_right'.measurable

private lemma vAlpha_abs_le {a r M : ℝ} (ha : 2 ≤ a) (hr0 : 0 ≤ r) (hr1 : r < 1)
    {h : ℝ × ℝ → ℝ} (hM : 0 ≤ M) (hh : Measurable h) (hbd : ∀ p, |h p| ≤ M) (y : ℝ) :
    |vAlpha a r h y| ≤ M * spinCr a r * spinUr a r y := by
  unfold vAlpha
  have hint : Integrable (fun v : ℝ => spinMehlerKernel1D r y v * vBeta a r h v * spinV1 a v) := by
    refine ((spinUr_integrable ha hr0 hr1 y).const_mul (M * spinCr a r)).mono' ?_
      (Eventually.of_forall fun v => ?_)
    · have hK : Continuous (fun v : ℝ => spinMehlerKernel1D r y v) := by
        unfold spinMehlerKernel1D; fun_prop
      have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
      exact ((hK.measurable.mul (vBeta_meas hh)).mul hV.measurable).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (spinMehlerKernel1D_nonneg hr1 y v),
          abs_of_nonneg (spinV1_nonneg ha v)]
      have h1 := vBeta_abs_le ha hr0 hr1 hM hh hbd v
      have h2 := mul_le_mul_of_nonneg_left h1 (spinMehlerKernel1D_nonneg hr1 y v)
      have h3 := mul_le_mul_of_nonneg_right h2 (spinV1_nonneg ha v)
      linarith
  calc |∫ v : ℝ, spinMehlerKernel1D r y v * vBeta a r h v * spinV1 a v|
      ≤ ∫ v : ℝ, |spinMehlerKernel1D r y v * vBeta a r h v * spinV1 a v| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ v : ℝ, (M * spinCr a r) * (spinMehlerKernel1D r y v * spinV1 a v) := by
        refine integral_mono hint.abs ((spinUr_integrable ha hr0 hr1 y).const_mul _) fun v => ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (spinMehlerKernel1D_nonneg hr1 y v),
            abs_of_nonneg (spinV1_nonneg ha v)]
        have h1 := vBeta_abs_le ha hr0 hr1 hM hh hbd v
        have h2 := mul_le_mul_of_nonneg_left h1 (spinMehlerKernel1D_nonneg hr1 y v)
        have h3 := mul_le_mul_of_nonneg_right h2 (spinV1_nonneg ha v)
        linarith
    _ = M * spinCr a r * spinUr a r y := by rw [integral_const_mul]; rfl

private lemma vAlpha_eq_mehlerW_zero {a r M : ℝ} (ha : 2 ≤ a) (hr0 : 0 ≤ r) (hr1 : r < 1)
    {h : ℝ × ℝ → ℝ} (_hM : 0 ≤ M) (hh : Measurable h) (hbd : ∀ p, |h p| ≤ M) (y : ℝ) :
    spinMehlerOp r (vW a h) (0, y) = vAlpha a r h y := by
  unfold spinMehlerOp vAlpha vBeta vW
  rw [Measure.volume_eq_prod]
  have hint_prod : Integrable (fun q : ℝ × ℝ =>
      spinMehlerKernel1D r 0 q.1 * spinMehlerKernel1D r y q.2 *
        (h q * spinV1 a q.1 * spinV1 a q.2)) (volume.prod volume) := by
    have hprod_pos : Integrable (fun q : ℝ × ℝ =>
        M * ((spinMehlerKernel1D r 0 q.1 * spinV1 a q.1) *
             (spinMehlerKernel1D r y q.2 * spinV1 a q.2))) (volume.prod volume) :=
      ((spinUr_integrable ha hr0 hr1 0).mul_prod (spinUr_integrable ha hr0 hr1 y)).const_mul M
    refine hprod_pos.mono' ?_ (Eventually.of_forall fun q => ?_)
    · have hK0 : Continuous (fun u : ℝ => spinMehlerKernel1D r 0 u) := by
        unfold spinMehlerKernel1D; fun_prop
      have hKy : Continuous (fun v : ℝ => spinMehlerKernel1D r y v) := by
        unfold spinMehlerKernel1D; fun_prop
      have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
      exact (((hK0.measurable.comp measurable_fst).mul (hKy.measurable.comp measurable_snd)).mul
        ((hh.mul (hV.measurable.comp measurable_fst)).mul
          (hV.measurable.comp measurable_snd))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (spinMehlerKernel1D_nonneg hr1 0 q.1),
          abs_of_nonneg (spinMehlerKernel1D_nonneg hr1 y q.2),
          abs_of_nonneg (spinV1_nonneg ha q.1), abs_of_nonneg (spinV1_nonneg ha q.2)]
      have h1 := hbd q
      have hnn : 0 ≤ (spinMehlerKernel1D r 0 q.1 * spinV1 a q.1) *
          (spinMehlerKernel1D r y q.2 * spinV1 a q.2) :=
        mul_nonneg (mul_nonneg (spinMehlerKernel1D_nonneg hr1 0 q.1) (spinV1_nonneg ha q.1))
          (mul_nonneg (spinMehlerKernel1D_nonneg hr1 y q.2) (spinV1_nonneg ha q.2))
      have h2 := mul_le_mul_of_nonneg_right h1 hnn
      linarith
  rw [integral_prod_symm _ hint_prod]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  have hpt : (fun u : ℝ => spinMehlerKernel1D r 0 u * spinMehlerKernel1D r y v *
        (h (u, v) * spinV1 a u * spinV1 a v)) =
      fun u : ℝ => (spinMehlerKernel1D r y v * spinV1 a v) *
        (spinMehlerKernel1D r 0 u * h (u, v) * spinV1 a u) := by
    ext u; ring
  rw [hpt, integral_const_mul]; ring

private lemma integrable_exp_neg_quad_linear {τ c : ℝ} (hτ : 0 < τ) :
    Integrable (fun x : ℝ => Real.exp (-τ * x ^ 2 + c * |x|)) := by
  have h1 : Integrable (fun x : ℝ => Real.exp (-τ * x ^ 2 + c * x)) := by
    have hcomp : ∀ x : ℝ, Real.exp (-τ * x ^ 2 + c * x) =
        Real.exp (c ^ 2 / (4 * τ)) * Real.exp (-τ * (x - c / (2 * τ)) ^ 2) := by
      intro x; rw [← Real.exp_add]; congr 1; field_simp [hτ.ne']; ring
    simp_rw [hcomp]
    exact ((integrable_exp_neg_mul_sq hτ).comp_sub_right _).const_mul _
  have h2 : Integrable (fun x : ℝ => Real.exp (-τ * x ^ 2 - c * x)) := by
    have hcomp : ∀ x : ℝ, Real.exp (-τ * x ^ 2 - c * x) =
        Real.exp (c ^ 2 / (4 * τ)) * Real.exp (-τ * (x + c / (2 * τ)) ^ 2) := by
      intro x; rw [← Real.exp_add]; congr 1; field_simp [hτ.ne']; ring
    simp_rw [hcomp]
    exact ((integrable_exp_neg_mul_sq hτ).comp_add_right _).const_mul _
  refine (h1.add h2).mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (Real.continuous_exp.comp ((continuous_const.mul (continuous_id.pow 2)).add
      (continuous_const.mul continuous_abs))).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    dsimp [Pi.add_apply]
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]; linarith [Real.exp_pos (-τ * x ^ 2 - c * x)]
    · rw [abs_of_nonpos hx]
      have : -τ * x ^ 2 + c * -x = -τ * x ^ 2 - c * x := by ring
      rw [this]; linarith [Real.exp_pos (-τ * x ^ 2 + c * x)]

private lemma vFrL_integrable {a r M : ℝ} (ha : 2 ≤ a) (hr : r ∈ Ico (1 / 2 : ℝ) 1)
    {h : ℝ × ℝ → ℝ} (hM : 0 ≤ M) (hh : Measurable h) (hbd : ∀ p, |h p| ≤ M) :
    Integrable (vFrL a r h) := by
  obtain ⟨CU, hCU_pos, hCU⟩ := spinUr_bounds ha
  have hr0 : 0 ≤ r := by linarith [hr.1]
  have hr1 : r < 1 := hr.2
  have hτ_pos := mTau_pos hr0 hr1
  have hint_x : Integrable (fun x : ℝ => Real.exp (-π * x ^ 2)) :=
    integrable_exp_neg_mul_sq Real.pi_pos
  have hint_y : Integrable (fun y : ℝ =>
      M * spinCr a r * CU * Real.exp (-mTau r * y ^ 2 + 2 * π * Real.sqrt a * |y|)) :=
    (integrable_exp_neg_quad_linear hτ_pos).const_mul _
  rw [Measure.volume_eq_prod]
  refine (hint_x.mul_prod hint_y).mono' ?_ (Eventually.of_forall fun p => ?_)
  · unfold vFrL
    have h1 : Continuous (fun p : ℝ × ℝ => Real.exp (-π * p.1 ^ 2) * Real.cos (2 * π * 8 * p.1 * p.2)) := by
      fun_prop
    exact (h1.measurable.mul ((vAlpha_meas hh).comp measurable_snd)).aestronglyMeasurable
  · unfold vFrL
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    have hcos : |Real.cos (2 * π * 8 * p.1 * p.2)| ≤ 1 := Real.abs_cos_le_one _
    have hα := (vAlpha_abs_le ha hr0 hr1 hM hh hbd p.2).trans
      (mul_le_mul_of_nonneg_left ((hCU r hr).2.2 p.2) (mul_nonneg hM (spinCr_pos hr0 hr1).le))
    have h1 : Real.exp (-π * p.1 ^ 2) * |Real.cos (2 * π * 8 * p.1 * p.2)| ≤ Real.exp (-π * p.1 ^ 2) :=
      mul_le_of_le_one_right (Real.exp_pos _).le hcos
    calc Real.exp (-π * p.1 ^ 2) * |Real.cos (2 * π * 8 * p.1 * p.2)| * |vAlpha a r h p.2|
        ≤ Real.exp (-π * p.1 ^ 2) *
          (M * spinCr a r * (CU * Real.exp (-mTau r * p.2 ^ 2 + 2 * π * Real.sqrt a * |p.2|))) :=
          mul_le_mul h1 hα (abs_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (-π * p.1 ^ 2) *
          (M * spinCr a r * CU * Real.exp (-mTau r * p.2 ^ 2 + 2 * π * Real.sqrt a * |p.2|)) := by ring

private lemma vFr_integrable {a r M : ℝ} (ha : 2 ≤ a) (hr : r ∈ Ico (1 / 2 : ℝ) 1)
    {h : ℝ × ℝ → ℝ} (hM : 0 ≤ M) (hh : Measurable h) (hbd : ∀ p, |h p| ≤ M) :
    Integrable (vFr a r h) := by
  have h1 := vFrL_integrable ha hr hM hh hbd
  have h2 : Integrable (fun p : ℝ × ℝ => vFrL a r h p.swap) := by
    have hmp : MeasurePreserving Prod.swap (volume : Measure (ℝ × ℝ)) volume := by
      refine ⟨measurable_swap, ?_⟩
      rw [Measure.volume_eq_prod, Measure.prod_swap]
    exact hmp.integrable_comp_of_integrable h1
  exact h1.add h2

/-- Fourier-space bound: `‖𝓕 (spinToEuc (vFrL a r h)) (vE2ToProd.symm (ξ, η))‖ ≤ C_a * M * c_r * exp((π/3) √a |ξ|)`. -/
private lemma vFrL_fourier_bound {a : ℝ} (ha : 2 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ Ico (1 / 2 : ℝ) 1,
      ∀ {h : ℝ × ℝ → ℝ} {M : ℝ}, 0 ≤ M → Measurable h → (∀ p, |h p| ≤ M) →
        ∀ ξ η : ℝ,
          ‖𝓕 (spinToEuc (vFrL a r h)) (vE2ToProd.symm (ξ, η))‖ ≤
            C * M * spinCr a r * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |ξ|) := by
  set I_g : ℝ := ∫ w : ℝ, Real.exp (-(π / 23) * w ^ 2 + (1 / 3 : ℝ) * π * Real.sqrt a * |w|)
  have hI_g_pos : 0 < I_g := by
    refine integral_pos_of_integrable_nonneg_ne_zero (x := 0) ?_ ?_ ?_ ?_
    · exact (Real.continuous_exp.comp ((continuous_const.mul (continuous_id.pow 2)).add
        (continuous_const.mul continuous_abs)))
    · exact integrable_exp_neg_quad_linear (by positivity)
    · exact fun w => (Real.exp_pos _).le
    · exact (Real.exp_pos _).ne'
  refine ⟨I_g / 3, by positivity, fun r hr {h M} hM hh hbd ξ η => ?_⟩
  obtain ⟨hr12, hr1⟩ := hr
  have hr0 : 0 ≤ r := by linarith
  have hlam_gt : (6 : ℝ) < 8 * mLam r := by
    have := mLam_gt_three_fourths hr12 hr1; linarith
  have hlam_pos : 0 < 8 * mLam r := by linarith
  -- Compute 2D Fourier transform of `vFrL` by Fubini (`x` first, then `y`)
  have hF_eq : 𝓕 (spinToEuc (vFrL a r h)) (vE2ToProd.symm (ξ, η)) =
      ∫ y : ℝ, Real.fourierChar (-(y * η)) •
        (((1 / 2 : ℝ) : ℂ) *
          ((Real.exp (-π * (ξ - 8 * y) ^ 2) : ℂ) + (Real.exp (-π * (ξ + 8 * y) ^ 2) : ℂ)) *
          (vAlpha a r h y : ℂ)) := by
    rw [Real.fourier_eq]
    have hchg : ∫ x : EuclideanSpace ℝ (Fin 2),
          Real.fourierChar (-⟪x, vE2ToProd.symm (ξ, η)⟫) • spinToEuc (vFrL a r h) x =
        ∫ p : ℝ × ℝ,
          Real.fourierChar (-(p.2 * η)) •
            (Real.fourierChar (-(p.1 * ξ)) •
              ((Real.exp (-π * p.1 ^ 2) * Real.cos (2 * π * 8 * p.1 * p.2) : ℝ) : ℂ) *
              (vAlpha a r h p.2 : ℂ)) := by
      rw [← vVolume_preserving_e2ToProd.integral_comp']
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      dsimp only
      have hinner : ⟪x, vE2ToProd.symm (ξ, η)⟫ = x 0 * ξ + x 1 * η := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct, Fin.sum_univ_two, vE2ToProd_symm_apply_zero,
          vE2ToProd_symm_apply_one, mul_comm]
      rw [hinner, neg_add]
      have hchar : (Real.fourierChar (-(x 0 * ξ) + -(x 1 * η)) : ℂ) =
          (Real.fourierChar (-(x 1 * η)) : ℂ) * (Real.fourierChar (-(x 0 * ξ)) : ℂ) := by
        rw [AddChar.map_add_eq_mul, mul_comm]; rfl
      simp only [Circle.smul_def, smul_eq_mul, spinToEuc, vE2ToProd_apply, vFrL]
      rw [hchar, Complex.ofReal_mul]; ring
    rw [hchg, Measure.volume_eq_prod]
    have hint_prod : Integrable (fun p : ℝ × ℝ =>
        Real.fourierChar (-(p.2 * η)) •
          (Real.fourierChar (-(p.1 * ξ)) •
            ((Real.exp (-π * p.1 ^ 2) * Real.cos (2 * π * 8 * p.1 * p.2) : ℝ) : ℂ) *
            (vAlpha a r h p.2 : ℂ))) (volume.prod volume) := by
      have hFrL := vFrL_integrable ha ⟨hr12, hr1⟩ hM hh hbd
      rw [Measure.volume_eq_prod] at hFrL
      refine hFrL.norm.mono' ?_ (Eventually.of_forall fun p => ?_)
      · have h1 : Continuous (fun p : ℝ × ℝ =>
            Real.fourierChar (-(p.2 * η)) • (Real.fourierChar (-(p.1 * ξ)) •
              ((Real.exp (-π * p.1 ^ 2) * Real.cos (2 * π * 8 * p.1 * p.2) : ℝ) : ℂ))) := by
          fun_prop
        have h2 : Measurable (fun p : ℝ × ℝ => (vAlpha a r h p.2 : ℂ)) :=
          Complex.continuous_ofReal.measurable.comp ((vAlpha_meas hh).comp measurable_snd)
        have hpt : (fun p : ℝ × ℝ => Real.fourierChar (-(p.2 * η)) •
            (Real.fourierChar (-(p.1 * ξ)) •
              ((Real.exp (-π * p.1 ^ 2) * Real.cos (2 * π * 8 * p.1 * p.2) : ℝ) : ℂ) *
              (vAlpha a r h p.2 : ℂ))) =
            fun p => (Real.fourierChar (-(p.2 * η)) • (Real.fourierChar (-(p.1 * ξ)) •
              ((Real.exp (-π * p.1 ^ 2) * Real.cos (2 * π * 8 * p.1 * p.2) : ℝ) : ℂ))) *
              (vAlpha a r h p.2 : ℂ) := by
          ext p; simp only [Circle.smul_def, smul_eq_mul]; ring
        rw [hpt]; exact (h1.measurable.mul h2).aestronglyMeasurable
      · rw [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul, norm_mul,
            Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul,
            Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
            Real.norm_eq_abs, vFrL, abs_mul, abs_mul, abs_mul]
    rw [integral_prod_symm _ hint_prod]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    have hpull : (fun x : ℝ => Real.fourierChar (-(y * η)) •
          (Real.fourierChar (-(x * ξ)) •
            ((Real.exp (-π * x ^ 2) * Real.cos (2 * π * 8 * x * y) : ℝ) : ℂ) *
            (vAlpha a r h y : ℂ))) =
        fun x : ℝ => (Real.fourierChar (-(y * η)) : ℂ) *
          ((Real.fourierChar (-(x * ξ)) •
            ((Real.exp (-π * x ^ 2) * Real.cos (2 * π * 8 * x * y) : ℝ) : ℂ)) *
            (vAlpha a r h y : ℂ)) := by
      ext x; simp only [Circle.smul_def, smul_eq_mul]
    rw [hpull, integral_const_mul, integral_mul_const, v_fourier_gaussian_cos 8 y ξ]
    simp only [Circle.smul_def, smul_eq_mul]
  -- Bound norm by integral over `y`, then substitute `vAlpha` and Fubini over `v`
  rw [hF_eq]
  -- Helper: bound each ± term via `v_gauss_conv_mehler`
  have hterm : ∀ sgn : ℝ, sgn ^ 2 = 1 →
      Integrable (fun y : ℝ => Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) * |vAlpha a r h y|) ∧
      (∫ y : ℝ, Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) * |vAlpha a r h y|) ≤
        (I_g / 3) * M * spinCr a r * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |ξ|) := by
    intro sgn hsgn
    have hint_yv : Integrable (fun q : ℝ × ℝ =>
        Real.exp (-π * (ξ - sgn * 8 * q.1) ^ 2) *
          (spinMehlerKernel1D r q.1 q.2 * (M * spinCr a r) * spinV1 a q.2)) (volume.prod volume) := by
      rw [integrable_prod_iff]
      · refine ⟨Eventually.of_forall fun y => ?_, ?_⟩
        · have := (spinUr_integrable ha hr0 hr1 y).const_mul
            (Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) * (M * spinCr a r))
          refine this.congr (Eventually.of_forall fun v => by ring)
        · have hnorm_y : ∀ y : ℝ, ∫ v : ℝ,
              ‖Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) *
                (spinMehlerKernel1D r y v * (M * spinCr a r) * spinV1 a v)‖ =
              (M * spinCr a r) * (Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) * spinUr a r y) := by
            intro y
            have hpt : ∀ v : ℝ, ‖Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) *
                (spinMehlerKernel1D r y v * (M * spinCr a r) * spinV1 a v)‖ =
                (M * spinCr a r * Real.exp (-π * (ξ - sgn * 8 * y) ^ 2)) *
                  (spinMehlerKernel1D r y v * spinV1 a v) := by
              intro v
              rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le
                (mul_nonneg (mul_nonneg (spinMehlerKernel1D_nonneg hr1 y v)
                  (mul_nonneg hM (spinCr_pos hr0 hr1).le)) (spinV1_nonneg ha v)))]
              ring
            simp_rw [hpt, integral_const_mul]; unfold spinUr; ring
          simp_rw [hnorm_y]
          obtain ⟨CU, hCU_pos, hCU⟩ := spinUr_bounds ha
          refine ((integrable_exp_neg_quad_linear (mTau_pos hr0 hr1) (c := 2 * π * Real.sqrt a)).const_mul
            (M * spinCr a r * CU)).mono' ?_ (Eventually.of_forall fun y => ?_)
          · have hUr_cont : Continuous (spinUr a r) := by
              have heq : spinUr a r = fun x =>
                  Real.sqrt (2 / (1 + r)) * Real.exp (-mTau r * x ^ 2 + a * mTau r) *
                    spinV1 a (mLam r * x) +
                  spinCr a r * Real.exp (-mTau r * x ^ 2) *
                    Real.cosh (2 * π * Real.sqrt (a - 2) * (mLam r * x)) :=
                funext (spinUr_eq ha hr0 hr1)
              rw [heq]; unfold spinV1; fun_prop
            exact (continuous_const.mul ((Real.continuous_exp.comp
              (continuous_const.mul ((continuous_const.sub (continuous_const.mul continuous_id)).pow 2))).mul
              hUr_cont)).aestronglyMeasurable
          · rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hM (spinCr_pos hr0 hr1).le)
              (mul_nonneg (Real.exp_pos _).le (spinUr_nonneg ha hr1 y)))]
            have hexp1 : Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) ≤ 1 :=
              Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg (ξ - sgn * 8 * y)])
            have h1 := (hCU r ⟨hr12, hr1⟩).2.2 y
            have h2 : Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) * spinUr a r y ≤
                CU * Real.exp (-mTau r * y ^ 2 + 2 * π * Real.sqrt a * |y|) := by
              calc Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) * spinUr a r y
                  ≤ 1 * (CU * Real.exp (-mTau r * y ^ 2 + 2 * π * Real.sqrt a * |y|)) :=
                    mul_le_mul hexp1 h1 (spinUr_nonneg ha hr1 y) zero_le_one
                _ = CU * Real.exp (-mTau r * y ^ 2 + 2 * π * Real.sqrt a * |y|) := one_mul _
            have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hM (spinCr_pos (a := a) hr0 hr1).le)
            linarith
      · have hK : Continuous (fun q : ℝ × ℝ => spinMehlerKernel1D r q.1 q.2) := by
          unfold spinMehlerKernel1D; fun_prop
        have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
        exact ((Real.continuous_exp.comp (continuous_const.mul
          ((continuous_const.sub (continuous_const.mul continuous_fst)).pow 2))).mul
          ((hK.mul continuous_const).mul (hV.comp continuous_snd))).aestronglyMeasurable
    have hint_y_dom : Integrable (fun y : ℝ =>
        Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) * (M * spinCr a r * spinUr a r y)) := by
      have h1 := hint_yv.integral_prod_left
      refine h1.congr (Eventually.of_forall fun y => ?_)
      dsimp only
      have hpt : (fun v : ℝ => Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) *
            (spinMehlerKernel1D r y v * (M * spinCr a r) * spinV1 a v)) =
          fun v : ℝ => (Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) * (M * spinCr a r)) *
            (spinMehlerKernel1D r y v * spinV1 a v) := by ext v; ring
      rw [hpt, integral_const_mul]; unfold spinUr; ring
    have hint_y : Integrable (fun y : ℝ =>
        Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) * |vAlpha a r h y|) := by
      refine hint_y_dom.mono' ?_ (Eventually.of_forall fun y => ?_)
      · exact ((Real.continuous_exp.comp (continuous_const.mul
          ((continuous_const.sub (continuous_const.mul continuous_id)).pow 2))).measurable.mul
          (continuous_abs.measurable.comp (vAlpha_meas hh))).aestronglyMeasurable
      · rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))]
        exact mul_le_mul_of_nonneg_left (vAlpha_abs_le ha hr0 hr1 hM hh hbd y) (Real.exp_pos _).le
    refine ⟨hint_y, ?_⟩
    -- Swap integration order via `integral_prod_symm`
    have hle1 : ∫ y : ℝ, Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) * |vAlpha a r h y| ≤
        ∫ v : ℝ, ∫ y : ℝ, Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) *
          (spinMehlerKernel1D r y v * (M * spinCr a r) * spinV1 a v) := by
      calc ∫ y : ℝ, Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) * |vAlpha a r h y|
          ≤ ∫ y : ℝ, Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) * (M * spinCr a r * spinUr a r y) :=
            integral_mono hint_y hint_y_dom fun y =>
              mul_le_mul_of_nonneg_left (vAlpha_abs_le ha hr0 hr1 hM hh hbd y) (Real.exp_pos _).le
        _ = ∫ y : ℝ, ∫ v : ℝ, Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) *
              (spinMehlerKernel1D r y v * (M * spinCr a r) * spinV1 a v) := by
            refine integral_congr_ae (Eventually.of_forall fun y => ?_)
            dsimp only
            have hpt : (fun v : ℝ => Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) *
                  (spinMehlerKernel1D r y v * (M * spinCr a r) * spinV1 a v)) =
                fun v : ℝ => (Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) * (M * spinCr a r)) *
                  (spinMehlerKernel1D r y v * spinV1 a v) := by ext v; ring
            rw [hpt, integral_const_mul]; unfold spinUr; ring
        _ = ∫ v : ℝ, ∫ y : ℝ, Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) *
              (spinMehlerKernel1D r y v * (M * spinCr a r) * spinV1 a v) :=
            MeasureTheory.integral_integral_swap hint_yv
    -- Bound inner `y`-integral using `v_gauss_conv_mehler` and symmetry `K_r(y, v) = K_r(v, y)`
    have hinner_bd : ∀ v : ℝ,
        (∫ y : ℝ, Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) *
          (spinMehlerKernel1D r y v * (M * spinCr a r) * spinV1 a v)) ≤
        (2 * M * spinCr a r * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |ξ|)) *
          Real.exp (-(π / 23) * (ξ - sgn * 8 * (mLam r * v)) ^ 2 +
            (1 / 3 : ℝ) * π * Real.sqrt a * |ξ - sgn * 8 * (mLam r * v)|) := by
      intro v
      have hpt : (fun y : ℝ => Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) *
            (spinMehlerKernel1D r y v * (M * spinCr a r) * spinV1 a v)) =
          fun y : ℝ => (M * spinCr a r * spinV1 a v) *
            (Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) * spinMehlerKernel1D r v y) := by
        ext y; rw [spinMehlerKernel1D_symm hr0 hr1 y v]; ring
      rw [hpt, integral_const_mul]
      have hconv := (v_gauss_conv_mehler hr12 hr1 sgn hsgn ξ v).2
      have hV_exp : spinV1 a v ≤
          Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |ξ|) *
          Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |ξ - sgn * 8 * (mLam r * v)|) := by
        refine (spinV1_le_exp ha v).trans ?_
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have habs_sgn : |sgn| = 1 := by
          have : |sgn| ^ 2 = 1 := by rw [sq_abs, hsgn]
          nlinarith [abs_nonneg sgn]
        have htri : 8 * mLam r * |v| ≤ |ξ| + |ξ - sgn * 8 * (mLam r * v)| := by
          have h1 : |sgn * 8 * (mLam r * v)| = 8 * mLam r * |v| := by
            rw [abs_mul, abs_mul, habs_sgn, abs_of_pos (by norm_num : (0 : ℝ) < 8),
                abs_mul, abs_of_pos (mLam_pos (by linarith))]; ring
          rw [← h1]
          have := abs_sub_abs_le_abs_sub ξ (sgn * 8 * (mLam r * v))
          linarith [abs_sub_comm ξ (sgn * 8 * (mLam r * v)),
            abs_sub_abs_le_abs_sub (sgn * 8 * (mLam r * v)) ξ]
        have h6v : 6 * |v| ≤ |ξ| + |ξ - sgn * 8 * (mLam r * v)| := by
          have : 6 * |v| ≤ 8 * mLam r * |v| := mul_le_mul_of_nonneg_right hlam_gt.le (abs_nonneg v)
          linarith
        have hmul := mul_le_mul_of_nonneg_left h6v
          (by positivity : 0 ≤ (1 / 3 : ℝ) * π * Real.sqrt a)
        linarith
      have h1 : M * spinCr a r * spinV1 a v *
          (∫ y : ℝ, Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) * spinMehlerKernel1D r v y) ≤
          M * spinCr a r * spinV1 a v *
            (2 * Real.exp (-π / 23 * (ξ - sgn * 8 * (mLam r * v)) ^ 2)) :=
        mul_le_mul_of_nonneg_left hconv
          (mul_nonneg (mul_nonneg hM (spinCr_pos hr0 hr1).le) (spinV1_nonneg ha v))
      have h2 : M * spinCr a r * spinV1 a v *
            (2 * Real.exp (-π / 23 * (ξ - sgn * 8 * (mLam r * v)) ^ 2)) ≤
          M * spinCr a r *
            (Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |ξ|) *
             Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |ξ - sgn * 8 * (mLam r * v)|)) *
            (2 * Real.exp (-π / 23 * (ξ - sgn * 8 * (mLam r * v)) ^ 2)) := by
        have hfac := mul_le_mul_of_nonneg_left hV_exp (mul_nonneg hM (spinCr_pos (a := a) hr0 hr1).le)
        exact mul_le_mul_of_nonneg_right hfac (by positivity)
      refine (h1.trans h2).trans_eq ?_
      rw [Real.exp_add (-(π / 23) * (ξ - sgn * 8 * (mLam r * v)) ^ 2)]
      have : -π / 23 * (ξ - sgn * 8 * (mLam r * v)) ^ 2 =
          -(π / 23) * (ξ - sgn * 8 * (mLam r * v)) ^ 2 := by ring
      rw [this]; ring
    -- Evaluate the outer `v`-integral by affine change of variable `w = ξ - sgn * 8 * mLam r * v`
    have hchg_v : Integrable (fun v : ℝ =>
        Real.exp (-(π / 23) * (ξ - sgn * 8 * (mLam r * v)) ^ 2 +
          (1 / 3 : ℝ) * π * Real.sqrt a * |ξ - sgn * 8 * (mLam r * v)|)) ∧
      (∫ v : ℝ, Real.exp (-(π / 23) * (ξ - sgn * 8 * (mLam r * v)) ^ 2 +
          (1 / 3 : ℝ) * π * Real.sqrt a * |ξ - sgn * 8 * (mLam r * v)|)) =
        (8 * mLam r)⁻¹ * I_g := by
      let g0 : ℝ → ℝ := fun w =>
        Real.exp (-(π / 23) * w ^ 2 + (1 / 3 : ℝ) * π * Real.sqrt a * |w|)
      have hg0_int : Integrable g0 := integrable_exp_neg_quad_linear (by positivity)
      set c_aff : ℝ := -(sgn * 8 * mLam r)
      have habs_sgn : |sgn| = 1 := by
        have : |sgn| ^ 2 = 1 := by rw [sq_abs, hsgn]
        nlinarith [abs_nonneg sgn]
      have hc_abs : |c_aff| = 8 * mLam r := by
        dsimp [c_aff]; rw [abs_neg, abs_mul, abs_mul, habs_sgn, one_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 8), abs_of_pos (mLam_pos (by linarith))]
      have hc_ne : c_aff ≠ 0 := by
        intro hc0; have : |c_aff| = 0 := by rw [hc0, abs_zero]
        linarith [hc_abs]
      have hfn : (fun v : ℝ => Real.exp (-(π / 23) * (ξ - sgn * 8 * (mLam r * v)) ^ 2 +
            (1 / 3 : ℝ) * π * Real.sqrt a * |ξ - sgn * 8 * (mLam r * v)|)) =
          fun v => g0 (c_aff * v + ξ) := by
        ext v; dsimp [g0, c_aff]
        have : c_aff * v + ξ = ξ - sgn * 8 * (mLam r * v) := by dsimp [c_aff]; ring
        rw [this]
      rw [hfn]
      refine ⟨(hg0_int.comp_add_right ξ).comp_mul_left' hc_ne, ?_⟩
      rw [Measure.integral_comp_mul_left (fun w => g0 (w + ξ)) c_aff,
          integral_add_right_eq_self g0 ξ, abs_inv, hc_abs, smul_eq_mul]
    have hle2 : ∫ v : ℝ, ∫ y : ℝ, Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) *
          (spinMehlerKernel1D r y v * (M * spinCr a r) * spinV1 a v) ≤
        (2 * M * spinCr a r * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |ξ|)) *
          ((8 * mLam r)⁻¹ * I_g) := by
      have h1 := integral_mono hint_yv.integral_prod_right (hchg_v.1.const_mul _) hinner_bd
      rwa [integral_const_mul, hchg_v.2] at h1
    have hinv_le : (8 * mLam r)⁻¹ ≤ 1 / 6 := by
      rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left zero_le_one (by norm_num) hlam_gt.le
    calc ∫ y : ℝ, Real.exp (-π * (ξ - sgn * 8 * y) ^ 2) * |vAlpha a r h y|
        ≤ (2 * M * spinCr a r * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |ξ|)) *
            ((8 * mLam r)⁻¹ * I_g) := hle1.trans hle2
      _ ≤ (2 * M * spinCr a r * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |ξ|)) *
            ((1 / 6 : ℝ) * I_g) := by
          have hnn1 : 0 ≤ 2 * M * spinCr a r * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |ξ|) :=
            mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hM) (spinCr_pos hr0 hr1).le) (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hinv_le hI_g_pos.le) hnn1
      _ = (I_g / 3) * M * spinCr a r * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |ξ|) := by ring
  have hp := hterm 1 (by norm_num)
  have hm := hterm (-1) (by norm_num)
  have hnorm_le : ‖∫ y : ℝ, Real.fourierChar (-(y * η)) •
      (((1 / 2 : ℝ) : ℂ) *
        ((Real.exp (-π * (ξ - 8 * y) ^ 2) : ℂ) + (Real.exp (-π * (ξ + 8 * y) ^ 2) : ℂ)) *
        (vAlpha a r h y : ℂ))‖ ≤
      (1 / 2 : ℝ) * ((∫ y : ℝ, Real.exp (-π * (ξ - 8 * y) ^ 2) * |vAlpha a r h y|) +
                     (∫ y : ℝ, Real.exp (-π * (ξ + 8 * y) ^ 2) * |vAlpha a r h y|)) := by
    have hp' : Integrable (fun y : ℝ => Real.exp (-π * (ξ - 8 * y) ^ 2) * |vAlpha a r h y|) := by
      simpa using hp.1
    have hm' : Integrable (fun y : ℝ => Real.exp (-π * (ξ + 8 * y) ^ 2) * |vAlpha a r h y|) := by
      simpa [sub_neg_eq_add] using hm.1
    calc ‖∫ y : ℝ, Real.fourierChar (-(y * η)) •
          (((1 / 2 : ℝ) : ℂ) *
            ((Real.exp (-π * (ξ - 8 * y) ^ 2) : ℂ) + (Real.exp (-π * (ξ + 8 * y) ^ 2) : ℂ)) *
            (vAlpha a r h y : ℂ))‖
        ≤ ∫ y : ℝ, ‖Real.fourierChar (-(y * η)) •
          (((1 / 2 : ℝ) : ℂ) *
            ((Real.exp (-π * (ξ - 8 * y) ^ 2) : ℂ) + (Real.exp (-π * (ξ + 8 * y) ^ 2) : ℂ)) *
            (vAlpha a r h y : ℂ))‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ y : ℝ, (1 / 2 : ℝ) *
            (Real.exp (-π * (ξ - 8 * y) ^ 2) * |vAlpha a r h y| +
             Real.exp (-π * (ξ + 8 * y) ^ 2) * |vAlpha a r h y|) := by
          refine integral_mono ?_ ((hp'.add hm').const_mul (1 / 2)) fun y => ?_
          · refine ((hp'.add hm').const_mul (1 / 2)).mono' ?_ (Eventually.of_forall fun y => ?_)
            · have hc : Continuous (fun y : ℝ => Real.fourierChar (-(y * η)) •
                  (((1 / 2 : ℝ) : ℂ) *
                    ((Real.exp (-π * (ξ - 8 * y) ^ 2) : ℂ) + (Real.exp (-π * (ξ + 8 * y) ^ 2) : ℂ)))) := by
                fun_prop
              have hpt : (fun y : ℝ => ‖Real.fourierChar (-(y * η)) •
                  (((1 / 2 : ℝ) : ℂ) *
                    ((Real.exp (-π * (ξ - 8 * y) ^ 2) : ℂ) + (Real.exp (-π * (ξ + 8 * y) ^ 2) : ℂ)) *
                    (vAlpha a r h y : ℂ))‖) =
                  fun y => ‖(Real.fourierChar (-(y * η)) • (((1 / 2 : ℝ) : ℂ) *
                    ((Real.exp (-π * (ξ - 8 * y) ^ 2) : ℂ) + (Real.exp (-π * (ξ + 8 * y) ^ 2) : ℂ)))) *
                    (vAlpha a r h y : ℂ)‖ := by
                ext y; simp only [Circle.smul_def, smul_eq_mul]; congr 1; ring
              rw [hpt]
              exact (continuous_norm.measurable.comp
                (hc.measurable.mul (Complex.continuous_ofReal.measurable.comp (vAlpha_meas hh)))).aestronglyMeasurable
            · rw [Real.norm_of_nonneg (norm_nonneg _), Circle.smul_def, smul_eq_mul, norm_mul,
                  Circle.norm_coe, one_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
                  Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
              have hsum : ‖(Real.exp (-π * (ξ - 8 * y) ^ 2) : ℂ) +
                  (Real.exp (-π * (ξ + 8 * y) ^ 2) : ℂ)‖ =
                  Real.exp (-π * (ξ - 8 * y) ^ 2) + Real.exp (-π * (ξ + 8 * y) ^ 2) := by
                rw [← Complex.ofReal_add, Complex.norm_real,
                    Real.norm_of_nonneg (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
              rw [hsum]; dsimp [Pi.add_apply]; linarith
          · rw [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul, norm_mul,
                norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
            have hsum : ‖(Real.exp (-π * (ξ - 8 * y) ^ 2) : ℂ) +
                (Real.exp (-π * (ξ + 8 * y) ^ 2) : ℂ)‖ =
                Real.exp (-π * (ξ - 8 * y) ^ 2) + Real.exp (-π * (ξ + 8 * y) ^ 2) := by
              rw [← Complex.ofReal_add, Complex.norm_real,
                  Real.norm_of_nonneg (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
            rw [hsum]; linarith
      _ = (1 / 2 : ℝ) * ((∫ y : ℝ, Real.exp (-π * (ξ - 8 * y) ^ 2) * |vAlpha a r h y|) +
                         (∫ y : ℝ, Real.exp (-π * (ξ + 8 * y) ^ 2) * |vAlpha a r h y|)) := by
          rw [integral_const_mul, integral_add hp' hm']
  have hp_bd : ∫ y : ℝ, Real.exp (-π * (ξ - 8 * y) ^ 2) * |vAlpha a r h y| ≤
      (I_g / 3) * M * spinCr a r * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |ξ|) := by
    simpa using hp.2
  have hm_bd : ∫ y : ℝ, Real.exp (-π * (ξ + 8 * y) ^ 2) * |vAlpha a r h y| ≤
      (I_g / 3) * M * spinCr a r * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |ξ|) := by
    simpa [sub_neg_eq_add] using hm.2
  linarith

/-- Fourier-space integral bound: `|∫ p, Φ p * (𝓕 (spinToEuc (vFr a r h)) (vE2ToProd.symm p)).re| ≤ C_a M c_r M_2[Φ]`. -/
private lemma vFr_fourier_pairing_bound {a : ℝ} (ha : 2 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ Ico (1 / 2 : ℝ) 1,
      ∀ {h : ℝ × ℝ → ℝ} {M : ℝ}, 0 ≤ M → Measurable h → (∀ p, |h p| ≤ M) →
        ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ →
          |∫ p : ℝ × ℝ, Φ p * (𝓕 (spinToEuc (vFr a r h)) (vE2ToProd.symm p)).re| ≤
            C * M * spinCr a r * spinM2 a Φ := by
  obtain ⟨CF, hCF_pos, hCF⟩ := vFrL_fourier_bound ha
  obtain ⟨CE, hCE_pos, hCE⟩ := spinTestClass_exp_L1_le_M2 ha
  refine ⟨2 * CF * CE, by positivity, fun r hr {h M} hM hh hbd {Φ} hΦ => ?_⟩
  have h1 := vFrL_integrable ha hr hM hh hbd
  have h2 : Integrable (fun p : ℝ × ℝ => vFrL a r h p.swap) := by
    have hmp : MeasurePreserving Prod.swap (volume : Measure (ℝ × ℝ)) volume :=
      ⟨measurable_swap, by rw [Measure.volume_eq_prod, Measure.prod_swap]⟩
    exact hmp.integrable_comp_of_integrable h1
  have hEuc1 : Integrable (spinToEuc (vFrL a r h)) :=
    (vVolume_preserving_e2ToProd.integrable_comp_of_integrable h1).ofReal
  have hEuc2 : Integrable (spinToEuc (fun p => vFrL a r h p.swap)) :=
    (vVolume_preserving_e2ToProd.integrable_comp_of_integrable h2).ofReal
  have hF_add : ∀ x : EuclideanSpace ℝ (Fin 2),
      𝓕 (spinToEuc (vFr a r h)) x =
        𝓕 (spinToEuc (vFrL a r h)) x + 𝓕 (spinToEuc (fun p => vFrL a r h p.swap)) x := by
    intro x
    have hsum : spinToEuc (vFr a r h) =
        spinToEuc (vFrL a r h) + spinToEuc (fun p => vFrL a r h p.swap) := by
      ext y; simp [spinToEuc, vFr]
    rw [hsum, Real.fourier_eq, Real.fourier_eq, Real.fourier_eq]
    have hi1 : Integrable (fun v : EuclideanSpace ℝ (Fin 2) =>
        Real.fourierChar (-⟪v, x⟫) • spinToEuc (vFrL a r h) v) :=
      (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
        (L := innerₗ _) continuous_inner x).2 hEuc1
    have hi2 : Integrable (fun v : EuclideanSpace ℝ (Fin 2) =>
        Real.fourierChar (-⟪v, x⟫) • spinToEuc (fun p => vFrL a r h p.swap) v) :=
      (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
        (L := innerₗ _) continuous_inner x).2 hEuc2
    have hadd : (fun v : EuclideanSpace ℝ (Fin 2) =>
        Real.fourierChar (-⟪v, x⟫) • (spinToEuc (vFrL a r h) + spinToEuc (fun p => vFrL a r h p.swap)) v) =
        fun v => Real.fourierChar (-⟪v, x⟫) • spinToEuc (vFrL a r h) v +
          Real.fourierChar (-⟪v, x⟫) • spinToEuc (fun p => vFrL a r h p.swap) v := by
      ext v; simp only [Pi.add_apply, smul_add]
    rw [hadd]
    exact integral_add hi1 hi2
  have hF_swap : ∀ ξ η : ℝ,
      𝓕 (spinToEuc (fun p => vFrL a r h p.swap)) (vE2ToProd.symm (ξ, η)) =
        𝓕 (spinToEuc (vFrL a r h)) (vE2ToProd.symm (η, ξ)) := by
    intro ξ η
    rw [Real.fourier_eq, Real.fourier_eq]
    have hmp : MeasurePreserving Prod.swap (volume : Measure (ℝ × ℝ)) volume :=
      ⟨measurable_swap, by rw [Measure.volume_eq_prod, Measure.prod_swap]⟩
    have hL : ∫ v : EuclideanSpace ℝ (Fin 2),
        Real.fourierChar (-⟪v, vE2ToProd.symm (ξ, η)⟫) •
          spinToEuc (fun p => vFrL a r h p.swap) v =
        ∫ p : ℝ × ℝ, Real.fourierChar (-(p.1 * ξ + p.2 * η)) • (vFrL a r h p.swap : ℂ) := by
      rw [← vVolume_preserving_e2ToProd.integral_comp'
        (g := fun p : ℝ × ℝ => Real.fourierChar (-(p.1 * ξ + p.2 * η)) • (vFrL a r h p.swap : ℂ))]
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      dsimp only
      have hinner : ⟪v, vE2ToProd.symm (ξ, η)⟫ = v 0 * ξ + v 1 * η := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct, Fin.sum_univ_two, vE2ToProd_symm_apply_zero,
          vE2ToProd_symm_apply_one, mul_comm]
      rw [hinner]; rfl
    have hR : ∫ v : EuclideanSpace ℝ (Fin 2),
        Real.fourierChar (-⟪v, vE2ToProd.symm (η, ξ)⟫) • spinToEuc (vFrL a r h) v =
        ∫ p : ℝ × ℝ, Real.fourierChar (-(p.1 * η + p.2 * ξ)) • (vFrL a r h p : ℂ) := by
      rw [← vVolume_preserving_e2ToProd.integral_comp'
        (g := fun p : ℝ × ℝ => Real.fourierChar (-(p.1 * η + p.2 * ξ)) • (vFrL a r h p : ℂ))]
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      dsimp only
      have hinner : ⟪v, vE2ToProd.symm (η, ξ)⟫ = v 0 * η + v 1 * ξ := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct, Fin.sum_univ_two, vE2ToProd_symm_apply_zero,
          vE2ToProd_symm_apply_one, mul_comm]
      rw [hinner]; rfl
    have hmp_e : MeasurePreserving (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ) volume volume := by
      refine ⟨MeasurableEquiv.prodComm.measurable, ?_⟩
      change Measure.map Prod.swap volume = volume
      rw [Measure.volume_eq_prod, Measure.prod_swap]
    rw [hL, hR, ← hmp_e.integral_comp'
      (g := fun p : ℝ × ℝ => Real.fourierChar (-(p.1 * η + p.2 * ξ)) • (vFrL a r h p : ℂ))]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    dsimp [MeasurableEquiv.prodComm, Prod.swap]; congr 2; ring
  have hFr_int := vFr_integrable ha hr hM hh hbd
  have hΦ_int_hat := (v_fourier_odd_pairing hΦ hFr_int).2.1
  obtain ⟨hE_int, hE_le⟩ := hCE hΦ
  have hE_swap : Integrable (fun p : ℝ × ℝ => |Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.2|)) ∧
      (∫ p : ℝ × ℝ, |Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.2|)) =
        ∫ p : ℝ × ℝ, |Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.1|) := by
    have hmp : MeasurePreserving (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ) volume volume := by
      refine ⟨MeasurableEquiv.prodComm.measurable, ?_⟩
      change Measure.map Prod.swap volume = volume
      rw [Measure.volume_eq_prod, Measure.prod_swap]
    have hcomp : Integrable (fun p : ℝ × ℝ => |Φ p.swap| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.swap.1|)) :=
      hmp.integrable_comp_of_integrable hE_int
    have heq : (fun p : ℝ × ℝ => |Φ p.swap| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.swap.1|)) =
        fun p : ℝ × ℝ => |Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.2|) := by
      ext p; dsimp [Prod.swap]; rw [hΦ.d4_inv.2.2 p.1 p.2]
    rw [heq] at hcomp
    refine ⟨hcomp, ?_⟩
    rw [← heq]
    exact hmp.integral_comp' (g := fun p : ℝ × ℝ => |Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.1|))
  have hdom : Integrable (fun p : ℝ × ℝ =>
      (CF * M * spinCr a r) *
        (|Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.1|) +
         |Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.2|))) :=
    (hE_int.add hE_swap.1).const_mul _
  calc |∫ p : ℝ × ℝ, Φ p * (𝓕 (spinToEuc (vFr a r h)) (vE2ToProd.symm p)).re|
      ≤ ∫ p : ℝ × ℝ, |Φ p * (𝓕 (spinToEuc (vFr a r h)) (vE2ToProd.symm p)).re| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ p : ℝ × ℝ, (CF * M * spinCr a r) *
          (|Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.1|) +
           |Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.2|)) := by
        refine integral_mono hΦ_int_hat.abs hdom fun p => ?_
        rw [abs_mul, hF_add, Complex.add_re]
        have hre1 : |(𝓕 (spinToEuc (vFrL a r h)) (vE2ToProd.symm p)).re| ≤
            CF * M * spinCr a r * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.1|) :=
          (Complex.abs_re_le_norm _).trans (hCF r hr hM hh hbd p.1 p.2)
        have hre2 : |(𝓕 (spinToEuc (fun q => vFrL a r h q.swap)) (vE2ToProd.symm p)).re| ≤
            CF * M * spinCr a r * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.2|) := by
          have : vE2ToProd.symm p = vE2ToProd.symm (p.1, p.2) := rfl
          rw [this, hF_swap]
          exact (Complex.abs_re_le_norm _).trans (hCF r hr hM hh hbd p.2 p.1)
        have htri := abs_add_le
          (𝓕 (spinToEuc (vFrL a r h)) (vE2ToProd.symm p)).re
          (𝓕 (spinToEuc (fun q => vFrL a r h q.swap)) (vE2ToProd.symm p)).re
        have hsum : |(𝓕 (spinToEuc (vFrL a r h)) (vE2ToProd.symm p)).re +
            (𝓕 (spinToEuc (fun q => vFrL a r h q.swap)) (vE2ToProd.symm p)).re| ≤
            CF * M * spinCr a r *
              (Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.1|) +
               Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.2|)) := by linarith
        have := mul_le_mul_of_nonneg_left hsum (abs_nonneg (Φ p))
        linarith
    _ = (CF * M * spinCr a r) *
          ((∫ p : ℝ × ℝ, |Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.1|)) +
           (∫ p : ℝ × ℝ, |Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.2|))) := by
        rw [integral_const_mul, integral_add hE_int hE_swap.1]
    _ = 2 * (CF * M * spinCr a r) *
          (∫ p : ℝ × ℝ, |Φ p| * Real.exp ((1 / 3 : ℝ) * π * Real.sqrt a * |p.1|)) := by
        rw [hE_swap.2]; ring
    _ ≤ 2 * (CF * M * spinCr a r) * (CE * spinM2 a Φ) := by
        have hcr_nn : 0 ≤ spinCr a r := (spinCr_pos (by linarith [hr.1]) hr.2).le
        exact mul_le_mul_of_nonneg_left hE_le (by positivity)
    _ = (2 * CF * CE) * M * spinCr a r * spinM2 a Φ := by ring

/-- Key small-`|x|` difference bound on the strip `|x| < √τ_r`, `|y| > 1`:
`|(A_r W)(x, y) - (A_r W)(0, y)| ≤ C_a M x² U_r(y)`. -/
private lemma v_strip_diff_bound {a : ℝ} (ha : 2 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ Ico (1 / 2 : ℝ) 1,
      ∀ {h : ℝ × ℝ → ℝ} {M : ℝ}, 0 ≤ M → Measurable h → IsD4Invariant h → (∀ p, |h p| ≤ M) →
        ∀ x y : ℝ, x ^ 2 ≤ mTau r →
          |spinMehlerOp r (vW a h) (x, y) - vAlpha a r h y| ≤ C * M * x ^ 2 * spinUr a r y := by
  obtain ⟨Cc, hCc_pos, hCc⟩ := spinCr_le_mul_mTau ha
  -- Auxiliary finite Gaussian moment `∫ s^4 exp(-1/2 s² + 2π √a |s|) ds`
  have hint_s4 : Integrable (fun s : ℝ => s ^ 4 * Real.exp (-(1 / 2 : ℝ) * s ^ 2 + 2 * π * Real.sqrt a * |s|)) := by
    have hdom : Integrable (fun s : ℝ => (48 : ℝ) * Real.exp (-(1 / 4 : ℝ) * s ^ 2 + 2 * π * Real.sqrt a * |s|)) :=
      (integrable_exp_neg_quad_linear (by norm_num : (0 : ℝ) < 1 / 4)).const_mul 48
    refine hdom.mono' ?_ (Eventually.of_forall fun s => ?_)
    · exact ((continuous_id.pow 4).mul (Real.continuous_exp.comp
        ((continuous_const.mul (continuous_id.pow 2)).add
          (continuous_const.mul continuous_abs)))).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)]
      have hpoly : s ^ 4 * Real.exp (-(1 / 4 : ℝ) * s ^ 2) ≤ 48 := by
        have h2 : ((1 / 4 : ℝ) * s ^ 2) ^ 2 / 2 ≤ Real.exp ((1 / 4 : ℝ) * s ^ 2) := by
          have hsum := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ (1 / 4 : ℝ) * s ^ 2) 3
          simp [Finset.sum_range_succ, Nat.factorial] at hsum
          have hnn : 0 ≤ (1 / 4 : ℝ) * s ^ 2 := by positivity
          linarith
        have h3 : s ^ 4 ≤ 48 * Real.exp ((1 / 4 : ℝ) * s ^ 2) := by
          have hsq : ((1 / 4 : ℝ) * s ^ 2) ^ 2 / 2 = s ^ 4 / 32 := by ring
          have hexp_nn : 0 ≤ Real.exp ((1 / 4 : ℝ) * s ^ 2) := (Real.exp_pos _).le
          linarith
        have h4 := mul_le_mul_of_nonneg_right h3 (Real.exp_pos (-(1 / 4 : ℝ) * s ^ 2)).le
        have hcancel : Real.exp ((1 / 4 : ℝ) * s ^ 2) * Real.exp (-(1 / 4 : ℝ) * s ^ 2) = 1 := by
          rw [← Real.exp_add]; simp
        calc s ^ 4 * Real.exp (-(1 / 4 : ℝ) * s ^ 2)
            ≤ 48 * Real.exp ((1 / 4 : ℝ) * s ^ 2) * Real.exp (-(1 / 4 : ℝ) * s ^ 2) := h4
          _ = 48 * (Real.exp ((1 / 4 : ℝ) * s ^ 2) * Real.exp (-(1 / 4 : ℝ) * s ^ 2)) := by ring
          _ = 48 := by rw [hcancel, mul_one]
      have hexp : Real.exp (-(1 / 2 : ℝ) * s ^ 2 + 2 * π * Real.sqrt a * |s|) =
          Real.exp (-(1 / 4 : ℝ) * s ^ 2) * Real.exp (-(1 / 4 : ℝ) * s ^ 2 + 2 * π * Real.sqrt a * |s|) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hexp, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
  set I4 : ℝ := ∫ s : ℝ, s ^ 4 * Real.exp (-(1 / 2 : ℝ) * s ^ 2 + 2 * π * Real.sqrt a * |s|)
  have hI4_nn : 0 ≤ I4 := integral_nonneg fun s => mul_nonneg (by positivity) (Real.exp_pos _).le
  set C : ℝ := π ^ 2 * Cc + 8 * π ^ 2 * a * Real.exp (2 * π ^ 2) * I4
  have hC_pos : 0 < C := by
    have h1 : 0 < π ^ 2 * Cc := by positivity
    have h2 : 0 ≤ 8 * π ^ 2 * a * Real.exp (2 * π ^ 2) * I4 := by positivity
    linarith
  refine ⟨C, hC_pos, fun r hr {h M} hM hh hd4 hbd x y hx2 => ?_⟩
  obtain ⟨hr12, hr1⟩ := hr
  have hr0 : 0 ≤ r := by linarith
  have hτ_pos := mTau_pos hr0 hr1
  have hα_pos := mAlpha_pos hr0 hr1
  have hlam0 : 0 ≤ mLam r := (mLam_pos (by linarith)).le
  have hlam1 : mLam r ≤ 1 := mLam_le_one hr0
  have hαx2 : mAlpha r * x ^ 2 ≤ π ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hx2 hα_pos.le
    rwa [mAlpha_mul_mTau hr0 hr1] at h1
  -- Rewrite `(A_r W)(x, y) - (A_r W)(0, y)` as `∫ v, K_r(y, v) V_1(v) (∫ u, (K_r(x, u) - K_r(0, u)) h(u, v) V_1(u))`
  rw [← vAlpha_eq_mehlerW_zero ha hr0 hr1 hM hh hbd y]
  have hint_W : ∀ x₀ : ℝ, Integrable (fun q : ℝ × ℝ =>
      spinMehlerKernel1D r x₀ q.1 * spinMehlerKernel1D r y q.2 * vW a h q) (volume.prod volume) := by
    intro x₀
    have hprod_pos : Integrable (fun q : ℝ × ℝ =>
        M * ((spinMehlerKernel1D r x₀ q.1 * spinV1 a q.1) *
             (spinMehlerKernel1D r y q.2 * spinV1 a q.2))) (volume.prod volume) :=
      ((spinUr_integrable ha hr0 hr1 x₀).mul_prod (spinUr_integrable ha hr0 hr1 y)).const_mul M
    refine hprod_pos.mono' ?_ (Eventually.of_forall fun q => ?_)
    · have hKx : Continuous (fun u : ℝ => spinMehlerKernel1D r x₀ u) := by
        unfold spinMehlerKernel1D; fun_prop
      have hKy : Continuous (fun v : ℝ => spinMehlerKernel1D r y v) := by
        unfold spinMehlerKernel1D; fun_prop
      have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
      exact (((hKx.measurable.comp measurable_fst).mul (hKy.measurable.comp measurable_snd)).mul
        ((hh.mul (hV.measurable.comp measurable_fst)).mul
          (hV.measurable.comp measurable_snd))).aestronglyMeasurable
    · unfold vW
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (spinMehlerKernel1D_nonneg hr1 x₀ q.1),
          abs_of_nonneg (spinMehlerKernel1D_nonneg hr1 y q.2),
          abs_of_nonneg (spinV1_nonneg ha q.1), abs_of_nonneg (spinV1_nonneg ha q.2)]
      have hnn : 0 ≤ (spinMehlerKernel1D r x₀ q.1 * spinV1 a q.1) *
          (spinMehlerKernel1D r y q.2 * spinV1 a q.2) :=
        mul_nonneg (mul_nonneg (spinMehlerKernel1D_nonneg hr1 x₀ q.1) (spinV1_nonneg ha q.1))
          (mul_nonneg (spinMehlerKernel1D_nonneg hr1 y q.2) (spinV1_nonneg ha q.2))
      have := mul_le_mul_of_nonneg_right (hbd q) hnn
      linarith
  -- Bound the inner `u`-integral for every `v`:
  have hinner_u : ∀ v : ℝ,
      |∫ u : ℝ, (spinMehlerKernel1D r x u - spinMehlerKernel1D r 0 u) * h (u, v) * spinV1 a u| ≤
        C * M * x ^ 2 := by
    intro v
    -- Symmetrize `u ↦ -u` using evenness of `h(u, v) * V_1(u)`
    have hint_sub : Integrable (fun u : ℝ =>
        (spinMehlerKernel1D r x u - spinMehlerKernel1D r 0 u) * h (u, v) * spinV1 a u) := by
      have hi : ∀ x₀ : ℝ, Integrable (fun u : ℝ =>
          spinMehlerKernel1D r x₀ u * h (u, v) * spinV1 a u) := fun x₀ => by
        refine ((spinUr_integrable ha hr0 hr1 x₀).const_mul M).mono' ?_ (Eventually.of_forall fun u => ?_)
        · have hK : Continuous (fun u : ℝ => spinMehlerKernel1D r x₀ u) := by
            unfold spinMehlerKernel1D; fun_prop
          have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
          exact ((hK.measurable.mul (hh.comp (measurable_id.prodMk measurable_const))).mul
            hV.measurable).aestronglyMeasurable
        · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (spinMehlerKernel1D_nonneg hr1 x₀ u),
              abs_of_nonneg (spinV1_nonneg ha u)]
          have := mul_le_mul_of_nonneg_left (hbd (u, v)) (spinMehlerKernel1D_nonneg hr1 x₀ u)
          have := mul_le_mul_of_nonneg_right this (spinV1_nonneg ha u)
          linarith
      exact ((hi x).sub (hi 0)).congr (Eventually.of_forall fun u => by dsimp; ring)
    have hsym_eq : (∫ u : ℝ, (spinMehlerKernel1D r x u - spinMehlerKernel1D r 0 u) *
          h (u, v) * spinV1 a u) =
        ∫ u : ℝ, Real.sqrt (2 / (1 - r)) * Real.exp (-mAlpha r * u ^ 2) *
          (Real.exp (-mAlpha r * x ^ 2) * Real.cosh (2 * mAlpha r * mLam r * x * u) - 1) *
          h (u, v) * spinV1 a u := by
      have hneg : (∫ u : ℝ, (spinMehlerKernel1D r x (-u) - spinMehlerKernel1D r 0 (-u)) *
            h (-u, v) * spinV1 a (-u)) =
          ∫ u : ℝ, (spinMehlerKernel1D r x u - spinMehlerKernel1D r 0 u) * h (u, v) * spinV1 a u :=
        integral_neg_eq_self (fun u : ℝ =>
          (spinMehlerKernel1D r x u - spinMehlerKernel1D r 0 u) * h (u, v) * spinV1 a u) volume
      have havg : (∫ u : ℝ, (spinMehlerKernel1D r x u - spinMehlerKernel1D r 0 u) *
            h (u, v) * spinV1 a u) =
          ∫ u : ℝ, (1 / 2 : ℝ) *
            ((spinMehlerKernel1D r x u - spinMehlerKernel1D r 0 u) * h (u, v) * spinV1 a u +
             (spinMehlerKernel1D r x (-u) - spinMehlerKernel1D r 0 (-u)) * h (-u, v) * spinV1 a (-u)) := by
        rw [integral_const_mul, integral_add hint_sub hint_sub.comp_neg, hneg]; ring
      rw [havg]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      dsimp only
      rw [hd4.1 u v, spinV1_even]
      have hK_form : ∀ u₀ : ℝ, spinMehlerKernel1D r x u₀ =
          Real.sqrt (2 / (1 - r)) * Real.exp (-mAlpha r * u₀ ^ 2) *
            Real.exp (-mAlpha r * x ^ 2) * Real.exp (2 * mAlpha r * mLam r * x * u₀) := by
        intro u₀
        rw [spinMehlerKernel1D_eq_symm_form hr0 hr1 x u₀]
        rw [mul_assoc (Real.sqrt _), mul_assoc (Real.sqrt _), ← Real.exp_add, ← Real.exp_add]
        congr 2
        unfold mAlpha mLam
        have h1 : (1 - r) ≠ 0 := by linarith
        have h2 : (1 + r) ≠ 0 := by linarith
        field_simp; ring
      have hK0_form : ∀ u₀ : ℝ, spinMehlerKernel1D r 0 u₀ =
          Real.sqrt (2 / (1 - r)) * Real.exp (-mAlpha r * u₀ ^ 2) := by
        intro u₀
        rw [spinMehlerKernel1D_eq_symm_form hr0 hr1 0 u₀]
        congr 2; unfold mAlpha; ring
      rw [hK_form u, hK_form (-u), hK0_form u, hK0_form (-u), neg_sq, Real.cosh_eq]
      have hneg_arg : 2 * mAlpha r * mLam r * x * -u = -(2 * mAlpha r * mLam r * x * u) := by ring
      rw [hneg_arg]; ring
    rw [hsym_eq]
    -- Pointwise bound using `|e^{-A} cosh B - 1| ≤ A + (B^2/2) e^B`
    set gA : ℝ → ℝ := fun u => M * (mAlpha r * x ^ 2) * (spinMehlerKernel1D r 0 u * spinV1 a u)
    set gB : ℝ → ℝ := fun u =>
      (4 * π ^ 2 * a * M * x ^ 2 * Real.exp (2 * π ^ 2)) *
        (Real.sqrt (2 / (1 - r)) * mAlpha r ^ 2 * u ^ 4 *
          Real.exp (-(1 / 2 : ℝ) * mAlpha r * u ^ 2 + 2 * π * Real.sqrt a * |u|))
    have hgA_int : Integrable gA := (spinUr_integrable ha hr0 hr1 0).const_mul _
    have hgB_int_base : Integrable (fun u : ℝ =>
        Real.sqrt (2 / (1 - r)) * mAlpha r ^ 2 * u ^ 4 *
          Real.exp (-(1 / 2 : ℝ) * mAlpha r * u ^ 2 + 2 * π * Real.sqrt a * |u|)) ∧
      (∫ u : ℝ, Real.sqrt (2 / (1 - r)) * mAlpha r ^ 2 * u ^ 4 *
          Real.exp (-(1 / 2 : ℝ) * mAlpha r * u ^ 2 + 2 * π * Real.sqrt a * |u|)) ≤ 2 * I4 := by
      have hα_ge1 : 1 ≤ mAlpha r := by
        unfold mAlpha
        have : (1 : ℝ) ≤ (1 + r) / (1 - r) := by rw [one_le_div (sub_pos.mpr hr1)]; linarith
        nlinarith [Real.pi_gt_three]
      have hsqα_pos : 0 < Real.sqrt (mAlpha r) := Real.sqrt_pos.mpr hα_pos
      have hsqα_ge1 : 1 ≤ Real.sqrt (mAlpha r) := by
        rw [Real.le_sqrt zero_le_one hα_pos.le]; linarith
      have hpref : Real.sqrt (2 / (1 - r)) / Real.sqrt (mAlpha r) ≤ 2 := by
        rw [← Real.sqrt_div (by positivity), Real.sqrt_le_iff]
        refine ⟨by norm_num, ?_⟩
        unfold mAlpha
        have h1r : 0 < 1 - r := sub_pos.mpr hr1
        have h1rp : 0 < 1 + r := by linarith
        have heq : 2 / (1 - r) / (π * ((1 + r) / (1 - r))) = 2 / (π * (1 + r)) := by
          field_simp [h1r.ne', h1rp.ne', Real.pi_pos.ne']
        rw [heq, div_le_iff₀ (by positivity)]
        nlinarith [Real.pi_gt_three]
      -- Dominate by `(s ↦ s^4 exp(-1/2 s² + 2π √a |s|))` composed with `u ↦ √α * u`
      let f0 : ℝ → ℝ := fun s =>
        s ^ 4 * Real.exp (-(1 / 2 : ℝ) * s ^ 2 + 2 * π * Real.sqrt a * |s|)
      have hf0_comp : Integrable (fun u : ℝ => f0 (Real.sqrt (mAlpha r) * u)) :=
        hint_s4.comp_mul_left' hsqα_pos.ne'
      have hpt_u : ∀ u : ℝ,
          Real.sqrt (2 / (1 - r)) * mAlpha r ^ 2 * u ^ 4 *
            Real.exp (-(1 / 2 : ℝ) * mAlpha r * u ^ 2 + 2 * π * Real.sqrt a * |u|) ≤
          Real.sqrt (2 / (1 - r)) * f0 (Real.sqrt (mAlpha r) * u) := by
        intro u
        dsimp [f0]
        have h1 : (Real.sqrt (mAlpha r) * u) ^ 4 = mAlpha r ^ 2 * u ^ 4 := by
          rw [mul_pow, show Real.sqrt (mAlpha r) ^ 4 = (Real.sqrt (mAlpha r) ^ 2) ^ 2 by ring,
              Real.sq_sqrt hα_pos.le]
        have h2 : (Real.sqrt (mAlpha r) * u) ^ 2 = mAlpha r * u ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hα_pos.le]
        have h3 : |u| ≤ |Real.sqrt (mAlpha r) * u| := by
          rw [abs_mul, abs_of_pos hsqα_pos]
          exact le_mul_of_one_le_left (abs_nonneg u) hsqα_ge1
        rw [h1, h2]
        have hexp : Real.exp (-(1 / 2 : ℝ) * (mAlpha r * u ^ 2) + 2 * π * Real.sqrt a * |u|) ≤
            Real.exp (-(1 / 2 : ℝ) * (mAlpha r * u ^ 2) + 2 * π * Real.sqrt a * |Real.sqrt (mAlpha r) * u|) :=
          Real.exp_le_exp.mpr (add_le_add_right (mul_le_mul_of_nonneg_left h3 (by positivity)) _)
        have hnn : 0 ≤ Real.sqrt (2 / (1 - r)) * (mAlpha r ^ 2 * u ^ 4) := by positivity
        have hmul := mul_le_mul_of_nonneg_left hexp hnn
        have hlhs : -(1 / 2 : ℝ) * mAlpha r * u ^ 2 = -(1 / 2 : ℝ) * (mAlpha r * u ^ 2) := by ring
        rw [hlhs]
        calc Real.sqrt (2 / (1 - r)) * mAlpha r ^ 2 * u ^ 4 *
              Real.exp (-(1 / 2 : ℝ) * (mAlpha r * u ^ 2) + 2 * π * Real.sqrt a * |u|)
            = Real.sqrt (2 / (1 - r)) * (mAlpha r ^ 2 * u ^ 4) *
              Real.exp (-(1 / 2 : ℝ) * (mAlpha r * u ^ 2) + 2 * π * Real.sqrt a * |u|) := by ring
          _ ≤ Real.sqrt (2 / (1 - r)) * (mAlpha r ^ 2 * u ^ 4) *
              Real.exp (-(1 / 2 : ℝ) * (mAlpha r * u ^ 2) + 2 * π * Real.sqrt a * |Real.sqrt (mAlpha r) * u|) := hmul
          _ = Real.sqrt (2 / (1 - r)) * (mAlpha r ^ 2 * u ^ 4 *
              Real.exp (-(1 / 2 : ℝ) * (mAlpha r * u ^ 2) + 2 * π * Real.sqrt a * |Real.sqrt (mAlpha r) * u|)) := by ring
      have hint_u : Integrable (fun u : ℝ =>
          Real.sqrt (2 / (1 - r)) * mAlpha r ^ 2 * u ^ 4 *
            Real.exp (-(1 / 2 : ℝ) * mAlpha r * u ^ 2 + 2 * π * Real.sqrt a * |u|)) := by
        refine (hf0_comp.const_mul (Real.sqrt (2 / (1 - r)))).mono' ?_ (Eventually.of_forall fun u => ?_)
        · exact (by fun_prop : Continuous fun u : ℝ =>
            Real.sqrt (2 / (1 - r)) * mAlpha r ^ 2 * u ^ 4 *
              Real.exp (-(1 / 2 : ℝ) * mAlpha r * u ^ 2 + 2 * π * Real.sqrt a * |u|)).aestronglyMeasurable
        · rw [Real.norm_of_nonneg (by positivity)]
          exact hpt_u u
      refine ⟨hint_u, ?_⟩
      calc ∫ u : ℝ, Real.sqrt (2 / (1 - r)) * mAlpha r ^ 2 * u ^ 4 *
              Real.exp (-(1 / 2 : ℝ) * mAlpha r * u ^ 2 + 2 * π * Real.sqrt a * |u|)
          ≤ ∫ u : ℝ, Real.sqrt (2 / (1 - r)) * f0 (Real.sqrt (mAlpha r) * u) :=
            integral_mono hint_u (hf0_comp.const_mul _) hpt_u
        _ = Real.sqrt (2 / (1 - r)) * ((Real.sqrt (mAlpha r))⁻¹ * I4) := by
            rw [integral_const_mul, Measure.integral_comp_mul_left f0 (Real.sqrt (mAlpha r)),
                abs_inv, abs_of_pos hsqα_pos, smul_eq_mul]
        _ = (Real.sqrt (2 / (1 - r)) / Real.sqrt (mAlpha r)) * I4 := by
            rw [div_eq_mul_inv]; ring
        _ ≤ 2 * I4 := mul_le_mul_of_nonneg_right hpref hI4_nn
    have hgB_int : Integrable gB := hgB_int_base.1.const_mul _
    have hpt_dom : ∀ u : ℝ,
        |Real.sqrt (2 / (1 - r)) * Real.exp (-mAlpha r * u ^ 2) *
          (Real.exp (-mAlpha r * x ^ 2) * Real.cosh (2 * mAlpha r * mLam r * x * u) - 1) *
          h (u, v) * spinV1 a u| ≤ gA u + gB u := by
      intro u
      rw [abs_mul, abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.exp_pos _).le,
          abs_of_nonneg (spinV1_nonneg ha u)]
      set A0 : ℝ := mAlpha r * x ^ 2
      set B0 : ℝ := 2 * mAlpha r * mLam r * |x| * |u|
      have hA0_nn : 0 ≤ A0 := by positivity
      have hB0_nn : 0 ≤ B0 := by positivity
      have hcosh_eq : Real.cosh (2 * mAlpha r * mLam r * x * u) = Real.cosh B0 := by
        have habs : |2 * mAlpha r * mLam r * x * u| = B0 := by
          dsimp [B0]
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos zero_lt_two,
              abs_of_pos hα_pos, abs_of_nonneg hlam0]
        rw [← habs]; rcases le_total 0 (2 * mAlpha r * mLam r * x * u) with h0 | h0
        · rw [abs_of_nonneg h0]
        · rw [abs_of_nonpos h0, Real.cosh_neg]
      rw [hcosh_eq]
      have hcore : |Real.exp (-A0) * Real.cosh B0 - 1| ≤ A0 + B0 ^ 2 / 2 * Real.exp B0 := by
        have h1 : |Real.exp (-A0) * Real.cosh B0 - 1| =
            |(Real.exp (-A0) - 1) + Real.exp (-A0) * (Real.cosh B0 - 1)| := by congr 1; ring
        rw [h1]
        have htri := abs_add_le (Real.exp (-A0) - 1) (Real.exp (-A0) * (Real.cosh B0 - 1))
        have h2 : |Real.exp (-A0) - 1| ≤ A0 := by
          have ha1 : Real.exp (-A0) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
          have ha2 : 1 - A0 ≤ Real.exp (-A0) := by have := Real.add_one_le_exp (-A0); linarith
          rw [abs_of_nonpos (by linarith)]; linarith
        have h3 : |Real.exp (-A0) * (Real.cosh B0 - 1)| ≤ B0 ^ 2 / 2 * Real.exp B0 := by
          have hc1 : 0 ≤ Real.cosh B0 - 1 := sub_nonneg.mpr (Real.one_le_cosh B0)
          rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hc1)]
          have he1 : Real.exp (-A0) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
          calc Real.exp (-A0) * (Real.cosh B0 - 1)
              ≤ 1 * (B0 ^ 2 / 2 * Real.exp B0) :=
                mul_le_mul he1 (cosh_sub_one_le hB0_nn) hc1 zero_le_one
            _ = B0 ^ 2 / 2 * Real.exp B0 := one_mul _
        linarith
      have hK0_eq : Real.sqrt (2 / (1 - r)) * Real.exp (-mAlpha r * u ^ 2) =
          spinMehlerKernel1D r 0 u := by
        rw [spinMehlerKernel1D_eq_symm_form hr0 hr1 0 u]; congr 2; unfold mAlpha; ring
      have htermB : Real.sqrt (2 / (1 - r)) * Real.exp (-mAlpha r * u ^ 2) *
          (B0 ^ 2 / 2 * Real.exp B0) * M * spinV1 a u ≤ gB u := by
        have hB2 : B0 ^ 2 / 2 ≤ 2 * mAlpha r ^ 2 * x ^ 2 * u ^ 2 := by
          dsimp [B0]
          have hlam2 : mLam r ^ 2 ≤ 1 := by nlinarith
          have : (2 * mAlpha r * mLam r * |x| * |u|) ^ 2 / 2 =
              2 * mAlpha r ^ 2 * mLam r ^ 2 * x ^ 2 * u ^ 2 := by
            rw [mul_pow, mul_pow, mul_pow, mul_pow, sq_abs, sq_abs]; ring
          rw [this]
          have hnn : 0 ≤ 2 * mAlpha r ^ 2 * x ^ 2 * u ^ 2 := by positivity
          nlinarith
        have hexp_amgm : -mAlpha r * u ^ 2 + B0 ≤ -(1 / 2 : ℝ) * mAlpha r * u ^ 2 + 2 * π ^ 2 := by
          dsimp [B0]
          have hsq : 0 ≤ mAlpha r * (|u| / 2 - 2 * mLam r * |x|) ^ 2 := by positivity
          have hlam2 : mLam r ^ 2 ≤ 1 := by nlinarith
          have h1 : 2 * mAlpha r * mLam r * |x| * |u| ≤
              (1 / 2 : ℝ) * mAlpha r * u ^ 2 + 2 * mAlpha r * mLam r ^ 2 * x ^ 2 := by
            have hsq_exp : mAlpha r * (|u| / 2 - 2 * mLam r * |x|) ^ 2 =
                (1 / 4 : ℝ) * mAlpha r * u ^ 2 - 2 * mAlpha r * mLam r * |x| * |u| +
                4 * mAlpha r * mLam r ^ 2 * x ^ 2 := by
              rw [sub_sq, div_pow, sq_abs, mul_pow, mul_pow, sq_abs]; ring
            have hsq' : 0 ≤ mAlpha r * (|u| / 2 - mLam r * |x|) ^ 2 := by positivity
            have hsq_exp' : 2 * mAlpha r * (|u| / 2 - mLam r * |x|) ^ 2 =
                (1 / 2 : ℝ) * mAlpha r * u ^ 2 - 2 * mAlpha r * mLam r * |x| * |u| +
                2 * mAlpha r * mLam r ^ 2 * x ^ 2 := by
              rw [sub_sq, div_pow, sq_abs, mul_pow, sq_abs]; ring
            have hnn' : 0 ≤ 2 * mAlpha r * (|u| / 2 - mLam r * |x|) ^ 2 := by positivity
            linarith [hsq_exp', hnn']
          have h2 : 2 * mAlpha r * mLam r ^ 2 * x ^ 2 ≤ 2 * mAlpha r * x ^ 2 := by
            have hnn : 0 ≤ 2 * mAlpha r * x ^ 2 := by positivity
            calc 2 * mAlpha r * mLam r ^ 2 * x ^ 2
                = (2 * mAlpha r * x ^ 2) * mLam r ^ 2 := by ring
              _ ≤ (2 * mAlpha r * x ^ 2) * 1 := mul_le_mul_of_nonneg_left hlam2 hnn
              _ = 2 * mAlpha r * x ^ 2 := mul_one _
          linarith [h1, h2, hαx2]
        have hV1 := spinV1_le_sq_exp ha u
        have hexp_comb : Real.exp (-mAlpha r * u ^ 2) * Real.exp B0 *
            Real.exp (2 * π * Real.sqrt a * |u|) ≤
            Real.exp (2 * π ^ 2) *
              Real.exp (-(1 / 2 : ℝ) * mAlpha r * u ^ 2 + 2 * π * Real.sqrt a * |u|) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          exact Real.exp_le_exp.mpr (by linarith [hexp_amgm])
        dsimp [gB]
        calc Real.sqrt (2 / (1 - r)) * Real.exp (-mAlpha r * u ^ 2) *
              (B0 ^ 2 / 2 * Real.exp B0) * M * spinV1 a u
            ≤ Real.sqrt (2 / (1 - r)) * Real.exp (-mAlpha r * u ^ 2) *
              ((2 * mAlpha r ^ 2 * x ^ 2 * u ^ 2) * Real.exp B0) * M *
              (2 * π ^ 2 * a * u ^ 2 * Real.exp (2 * π * Real.sqrt a * |u|)) := by
              have h1' : B0 ^ 2 / 2 * Real.exp B0 ≤ (2 * mAlpha r ^ 2 * x ^ 2 * u ^ 2) * Real.exp B0 :=
                mul_le_mul_of_nonneg_right hB2 (Real.exp_pos _).le
              have h2' : Real.sqrt (2 / (1 - r)) * Real.exp (-mAlpha r * u ^ 2) *
                  (B0 ^ 2 / 2 * Real.exp B0) * M ≤
                  Real.sqrt (2 / (1 - r)) * Real.exp (-mAlpha r * u ^ 2) *
                  ((2 * mAlpha r ^ 2 * x ^ 2 * u ^ 2) * Real.exp B0) * M :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1' (by positivity)) hM
              exact mul_le_mul h2' hV1 (spinV1_nonneg ha u) (by positivity)
          _ = (4 * π ^ 2 * a * M * x ^ 2) * (Real.sqrt (2 / (1 - r)) * mAlpha r ^ 2 * u ^ 4) *
              (Real.exp (-mAlpha r * u ^ 2) * Real.exp B0 * Real.exp (2 * π * Real.sqrt a * |u|)) := by ring
          _ ≤ (4 * π ^ 2 * a * M * x ^ 2) * (Real.sqrt (2 / (1 - r)) * mAlpha r ^ 2 * u ^ 4) *
              (Real.exp (2 * π ^ 2) *
                Real.exp (-(1 / 2 : ℝ) * mAlpha r * u ^ 2 + 2 * π * Real.sqrt a * |u|)) :=
              mul_le_mul_of_nonneg_left hexp_comb (by positivity)
          _ = 4 * π ^ 2 * a * M * x ^ 2 * Real.exp (2 * π ^ 2) *
              (Real.sqrt (2 / (1 - r)) * mAlpha r ^ 2 * u ^ 4 *
                Real.exp (-(1 / 2 : ℝ) * mAlpha r * u ^ 2 + 2 * π * Real.sqrt a * |u|)) := by ring
      have h1 : Real.sqrt (2 / (1 - r)) * Real.exp (-mAlpha r * u ^ 2) *
            |Real.exp (-A0) * Real.cosh B0 - 1| * |h (u, v)| * spinV1 a u ≤
          Real.sqrt (2 / (1 - r)) * Real.exp (-mAlpha r * u ^ 2) *
            (A0 + B0 ^ 2 / 2 * Real.exp B0) * M * spinV1 a u := by
        have h1' : Real.sqrt (2 / (1 - r)) * Real.exp (-mAlpha r * u ^ 2) *
            |Real.exp (-A0) * Real.cosh B0 - 1| ≤
            Real.sqrt (2 / (1 - r)) * Real.exp (-mAlpha r * u ^ 2) *
            (A0 + B0 ^ 2 / 2 * Real.exp B0) :=
          mul_le_mul_of_nonneg_left hcore (by positivity)
        have h2' := mul_le_mul h1' (hbd (u, v)) (abs_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right h2' (spinV1_nonneg ha u)
      have htermA : Real.sqrt (2 / (1 - r)) * Real.exp (-mAlpha r * u ^ 2) * A0 * M * spinV1 a u = gA u := by
        rw [hK0_eq]; dsimp [gA, A0]; ring
      have hdist : Real.sqrt (2 / (1 - r)) * Real.exp (-mAlpha r * u ^ 2) *
            (A0 + B0 ^ 2 / 2 * Real.exp B0) * M * spinV1 a u =
          gA u + Real.sqrt (2 / (1 - r)) * Real.exp (-mAlpha r * u ^ 2) *
            (B0 ^ 2 / 2 * Real.exp B0) * M * spinV1 a u := by
        rw [← htermA]; ring
      simpa only [A0, B0, hcosh_eq, neg_mul] using h1.trans (hdist.le.trans (add_le_add le_rfl htermB))
    have hint_sym : Integrable (fun u : ℝ =>
        Real.sqrt (2 / (1 - r)) * Real.exp (-mAlpha r * u ^ 2) *
          (Real.exp (-mAlpha r * x ^ 2) * Real.cosh (2 * mAlpha r * mLam r * x * u) - 1) *
          h (u, v) * spinV1 a u) := by
      refine (hgA_int.add hgB_int).mono' ?_ (Eventually.of_forall fun u => ?_)
      · have hc : Continuous (fun u : ℝ =>
            Real.sqrt (2 / (1 - r)) * Real.exp (-mAlpha r * u ^ 2) *
              (Real.exp (-mAlpha r * x ^ 2) * Real.cosh (2 * mAlpha r * mLam r * x * u) - 1)) := by
          fun_prop
        have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
        exact ((hc.measurable.mul (hh.comp (measurable_id.prodMk measurable_const))).mul
          hV.measurable).aestronglyMeasurable
      · rw [Real.norm_eq_abs]; exact hpt_dom u
    have hint_gA_val : ∫ u : ℝ, gA u ≤ π ^ 2 * Cc * M * x ^ 2 := by
      dsimp [gA]
      rw [integral_const_mul, ← spinUr, spinUr_zero ha hr0 hr1]
      have hcr := hCc r ⟨hr12, hr1⟩
      have h1 : mAlpha r * spinCr a r ≤ π ^ 2 * Cc := by
        calc mAlpha r * spinCr a r
            ≤ mAlpha r * (Cc * mTau r) := mul_le_mul_of_nonneg_left hcr hα_pos.le
          _ = Cc * (mAlpha r * mTau r) := by ring
          _ = π ^ 2 * Cc := by rw [mAlpha_mul_mTau hr0 hr1]; ring
      calc M * (mAlpha r * x ^ 2) * spinCr a r
          = (mAlpha r * spinCr a r) * (M * x ^ 2) := by ring
        _ ≤ (π ^ 2 * Cc) * (M * x ^ 2) := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = π ^ 2 * Cc * M * x ^ 2 := by ring
    have hint_gB_val : ∫ u : ℝ, gB u ≤ 8 * π ^ 2 * a * Real.exp (2 * π ^ 2) * I4 * M * x ^ 2 := by
      dsimp [gB]; rw [integral_const_mul]
      have h1 := mul_le_mul_of_nonneg_left hgB_int_base.2
        (by positivity : 0 ≤ 4 * π ^ 2 * a * M * x ^ 2 * Real.exp (2 * π ^ 2))
      linarith
    calc |∫ u : ℝ, Real.sqrt (2 / (1 - r)) * Real.exp (-mAlpha r * u ^ 2) *
            (Real.exp (-mAlpha r * x ^ 2) * Real.cosh (2 * mAlpha r * mLam r * x * u) - 1) *
            h (u, v) * spinV1 a u|
        ≤ ∫ u : ℝ, |Real.sqrt (2 / (1 - r)) * Real.exp (-mAlpha r * u ^ 2) *
            (Real.exp (-mAlpha r * x ^ 2) * Real.cosh (2 * mAlpha r * mLam r * x * u) - 1) *
            h (u, v) * spinV1 a u| := abs_integral_le_integral_abs
      _ ≤ ∫ u : ℝ, (gA u + gB u) := integral_mono hint_sym.abs (hgA_int.add hgB_int) hpt_dom
      _ = (∫ u : ℝ, gA u) + ∫ u : ℝ, gB u := integral_add hgA_int hgB_int
      _ ≤ C * M * x ^ 2 := by dsimp [C]; linarith
  -- Integrate the inner `u`-bound against `K_r(y, v) V_1(v)`
  unfold spinMehlerOp
  rw [Measure.volume_eq_prod, ← integral_sub (hint_W x) (hint_W 0)]
  have hsub_int : Integrable (fun q : ℝ × ℝ =>
      spinMehlerKernel1D r x q.1 * spinMehlerKernel1D r y q.2 * vW a h q -
      spinMehlerKernel1D r 0 q.1 * spinMehlerKernel1D r y q.2 * vW a h q) (volume.prod volume) :=
    (hint_W x).sub (hint_W 0)
  rw [integral_prod_symm _ hsub_int]
  have houter_eq : (fun v : ℝ => ∫ u : ℝ,
        (spinMehlerKernel1D r x u * spinMehlerKernel1D r y v * vW a h (u, v) -
         spinMehlerKernel1D r 0 u * spinMehlerKernel1D r y v * vW a h (u, v))) =
      fun v : ℝ => (spinMehlerKernel1D r y v * spinV1 a v) *
        ∫ u : ℝ, (spinMehlerKernel1D r x u - spinMehlerKernel1D r 0 u) * h (u, v) * spinV1 a u := by
    ext v; rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => by unfold vW; ring)
  rw [houter_eq]
  have hint_outer : Integrable (fun v : ℝ => (spinMehlerKernel1D r y v * spinV1 a v) *
      ∫ u : ℝ, (spinMehlerKernel1D r x u - spinMehlerKernel1D r 0 u) * h (u, v) * spinV1 a u) := by
    rw [← houter_eq]; exact hsub_int.integral_prod_right
  calc |∫ v : ℝ, (spinMehlerKernel1D r y v * spinV1 a v) *
          ∫ u : ℝ, (spinMehlerKernel1D r x u - spinMehlerKernel1D r 0 u) * h (u, v) * spinV1 a u|
      ≤ ∫ v : ℝ, |(spinMehlerKernel1D r y v * spinV1 a v) *
          ∫ u : ℝ, (spinMehlerKernel1D r x u - spinMehlerKernel1D r 0 u) * h (u, v) * spinV1 a u| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ v : ℝ, (C * M * x ^ 2) * (spinMehlerKernel1D r y v * spinV1 a v) := by
        refine integral_mono hint_outer.abs ((spinUr_integrable ha hr0 hr1 y).const_mul _) fun v => ?_
        rw [abs_mul, abs_of_nonneg (mul_nonneg (spinMehlerKernel1D_nonneg hr1 y v) (spinV1_nonneg ha v))]
        have := mul_le_mul_of_nonneg_left (hinner_u v)
          (mul_nonneg (spinMehlerKernel1D_nonneg hr1 y v) (spinV1_nonneg ha v))
        linarith
    _ = C * M * x ^ 2 * spinUr a r y := by rw [integral_const_mul]; rfl

set_option maxHeartbeats 400000 in
/-- Position-space domination: `|(A_r W)(p) - F_r(p)| ≤ C_a M Θ_a(p)` uniformly for `r ∈ [1/2, 1)`. -/
private lemma v_Dr_dom {a : ℝ} (ha : 2 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ Ico (1 / 2 : ℝ) 1,
      ∀ {h : ℝ × ℝ → ℝ} {M : ℝ}, 0 ≤ M → Measurable h → IsD4Invariant h → (∀ p, |h p| ≤ M) →
        ∀ p : ℝ × ℝ, |spinMehlerOp r (vW a h) p - vFr a r h p| ≤ C * M * spinTheta a p := by
  obtain ⟨CU, hCU_pos, hCU⟩ := spinUr_bounds ha
  obtain ⟨Cc, hCc_pos, hCc⟩ := spinCr_le_mul_mTau ha
  obtain ⟨CS, hCS_pos, hCS⟩ := v_strip_diff_bound ha
  set E_pi : ℝ := Real.exp (π / 2)
  set C_big : ℝ := max (max (CU ^ 2 + 2 * Cc * (π / 3) * CU)
      ((CU ^ 2 + 2 * Cc * (π / 3) * CU) * Real.exp π))
    (Cc * (π / 3) * CU * E_pi +
      max (CU * (2 * Real.exp (a * (π / 3)) + Cc * Real.cosh (2 * π * Real.sqrt a) / (4 * π ^ 2)) +
            Cc * CU / (4 * π ^ 2))
          ((CS * CU + Cc * CU * (π * (π / 3 + 128 * π))) / (4 * π ^ 2)))
  have hC_pos : 0 < C_big := by
    refine lt_of_lt_of_le ?_ ((le_max_left _ _).trans (le_max_left _ _))
    positivity
  refine ⟨C_big, hC_pos, fun r hr {h M} hM hh hd4 hbd p => ?_⟩
  have ⟨hr12, hr1⟩ := hr
  have hr0 : 0 ≤ r := by linarith
  have hτ_pos := mTau_pos hr0 hr1
  have hτ_le := mTau_le hr12
  have hcr_le : spinCr a r ≤ Cc * mTau r := hCc r hr
  have hcr_bdd : spinCr a r ≤ Cc * (π / 3) :=
    hcr_le.trans (mul_le_mul_of_nonneg_left hτ_le hCc_pos.le)
  have hAW_le : ∀ x y : ℝ, |spinMehlerOp r (vW a h) (x, y)| ≤ M * spinUr a r x * spinUr a r y := by
    intro x y
    unfold spinMehlerOp
    rw [Measure.volume_eq_prod]
    have hdom : Integrable (fun q : ℝ × ℝ =>
        M * ((spinMehlerKernel1D r x q.1 * spinV1 a q.1) *
             (spinMehlerKernel1D r y q.2 * spinV1 a q.2))) (volume.prod volume) :=
      ((spinUr_integrable ha hr0 hr1 x).mul_prod (spinUr_integrable ha hr0 hr1 y)).const_mul M
    have hint : Integrable (fun q : ℝ × ℝ =>
        spinMehlerKernel1D r x q.1 * spinMehlerKernel1D r y q.2 * vW a h q) (volume.prod volume) := by
      refine hdom.mono' ?_ (Eventually.of_forall fun q => ?_)
      · have hKx : Continuous (fun u : ℝ => spinMehlerKernel1D r x u) := by
          unfold spinMehlerKernel1D; fun_prop
        have hKy : Continuous (fun v : ℝ => spinMehlerKernel1D r y v) := by
          unfold spinMehlerKernel1D; fun_prop
        have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
        exact (((hKx.measurable.comp measurable_fst).mul (hKy.measurable.comp measurable_snd)).mul
          ((hh.mul (hV.measurable.comp measurable_fst)).mul
            (hV.measurable.comp measurable_snd))).aestronglyMeasurable
      · unfold vW
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
            abs_of_nonneg (spinMehlerKernel1D_nonneg hr1 x q.1),
            abs_of_nonneg (spinMehlerKernel1D_nonneg hr1 y q.2),
            abs_of_nonneg (spinV1_nonneg ha q.1), abs_of_nonneg (spinV1_nonneg ha q.2)]
        have hnn : 0 ≤ (spinMehlerKernel1D r x q.1 * spinV1 a q.1) *
            (spinMehlerKernel1D r y q.2 * spinV1 a q.2) :=
          mul_nonneg (mul_nonneg (spinMehlerKernel1D_nonneg hr1 x q.1) (spinV1_nonneg ha q.1))
            (mul_nonneg (spinMehlerKernel1D_nonneg hr1 y q.2) (spinV1_nonneg ha q.2))
        have := mul_le_mul_of_nonneg_right (hbd q) hnn
        linarith
    calc |∫ q : ℝ × ℝ, spinMehlerKernel1D r x q.1 * spinMehlerKernel1D r y q.2 * vW a h q ∂(volume.prod volume)|
        ≤ ∫ q : ℝ × ℝ, |spinMehlerKernel1D r x q.1 * spinMehlerKernel1D r y q.2 * vW a h q| ∂(volume.prod volume) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ q : ℝ × ℝ, M * ((spinMehlerKernel1D r x q.1 * spinV1 a q.1) *
            (spinMehlerKernel1D r y q.2 * spinV1 a q.2)) ∂(volume.prod volume) := by
          refine integral_mono hint.abs hdom fun q => ?_
          unfold vW
          rw [abs_mul, abs_mul, abs_mul, abs_mul,
              abs_of_nonneg (spinMehlerKernel1D_nonneg hr1 x q.1),
              abs_of_nonneg (spinMehlerKernel1D_nonneg hr1 y q.2),
              abs_of_nonneg (spinV1_nonneg ha q.1), abs_of_nonneg (spinV1_nonneg ha q.2)]
          have hnn : 0 ≤ (spinMehlerKernel1D r x q.1 * spinV1 a q.1) *
              (spinMehlerKernel1D r y q.2 * spinV1 a q.2) :=
            mul_nonneg (mul_nonneg (spinMehlerKernel1D_nonneg hr1 x q.1) (spinV1_nonneg ha q.1))
              (mul_nonneg (spinMehlerKernel1D_nonneg hr1 y q.2) (spinV1_nonneg ha q.2))
          have := mul_le_mul_of_nonneg_right (hbd q) hnn
          linarith
      _ = M * spinUr a r x * spinUr a r y := by
          rw [integral_const_mul, integral_prod_mul
            (fun u => spinMehlerKernel1D r x u * spinV1 a u)
            (fun v => spinMehlerKernel1D r y v * spinV1 a v)]; unfold spinUr; ring
  have hFrL_le : ∀ x y : ℝ, |vFrL a r h (x, y)| ≤
      M * spinCr a r * Real.exp (-π * x ^ 2) * spinUr a r y := by
    intro x y
    unfold vFrL
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    have h1 : Real.exp (-π * x ^ 2) * |Real.cos (2 * π * 8 * x * y)| ≤ Real.exp (-π * x ^ 2) :=
      mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
    have h2 := vAlpha_abs_le ha hr0 hr1 hM hh hbd y
    have h3 := mul_le_mul h1 h2 (abs_nonneg _) (Real.exp_pos _).le
    linarith
  have hUr_away : ∀ u : ℝ, 1 ≤ |u| → spinUr a r u ≤ CU * spinV1 a u := fun u hu => by
    have h1 := (hCU r hr).1 u hu
    have hexp : Real.exp (-mTau r * u ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u])
    calc spinUr a r u ≤ CU * Real.exp (-mTau r * u ^ 2) * spinV1 a u := h1
      _ ≤ CU * 1 * spinV1 a u :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hCU_pos.le) (spinV1_nonneg ha u)
      _ = CU * spinV1 a u := by ring
  -- Helper for the strip `|x| ≤ 1 < |y|`
  have hstrip : ∀ x y : ℝ, |x| ≤ 1 → 1 ≤ |y| →
      |spinMehlerOp r (vW a h) (x, y) - vFr a r h (x, y)| ≤ C_big * M * spinTheta a (x, y) := by
    intro x y hx hy
    have htri : |spinMehlerOp r (vW a h) (x, y) - vFr a r h (x, y)| ≤
        |spinMehlerOp r (vW a h) (x, y) - vFrL a r h (x, y)| + |vFrL a r h (y, x)| := by
      unfold vFr; dsimp [Prod.swap]
      have : spinMehlerOp r (vW a h) (x, y) - (vFrL a r h (x, y) + vFrL a r h (y, x)) =
          (spinMehlerOp r (vW a h) (x, y) - vFrL a r h (x, y)) + (-vFrL a r h (y, x)) := by ring
      rw [this]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    -- Second term `|vFrL (y, x)| ≤ Cc (π/3) CU E_pi M exp(-(π/2)(x² + y²))`
    have hterm2 : |vFrL a r h (y, x)| ≤
        (Cc * (π / 3) * CU * E_pi) * M * Real.exp (-(π / 2) * (x ^ 2 + y ^ 2)) := by
      have h1 := hFrL_le y x
      have hUx := (hCU r hr).2.1 x hx
      have hexp_xy : Real.exp (-π * y ^ 2) ≤ E_pi * Real.exp (-(π / 2) * (x ^ 2 + y ^ 2)) := by
        dsimp [E_pi]; rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have hxsq : x ^ 2 ≤ 1 := by rw [← sq_abs x]; nlinarith [abs_nonneg x]
        nlinarith [Real.pi_pos, sq_nonneg y]
      calc |vFrL a r h (y, x)|
          ≤ M * spinCr a r * Real.exp (-π * y ^ 2) * spinUr a r x := h1
        _ ≤ M * (Cc * (π / 3)) * (E_pi * Real.exp (-(π / 2) * (x ^ 2 + y ^ 2))) * CU := by
            have h1' : M * spinCr a r ≤ M * (Cc * (π / 3)) := mul_le_mul_of_nonneg_left hcr_bdd hM
            have h2' : M * spinCr a r * Real.exp (-π * y ^ 2) ≤
                M * (Cc * (π / 3)) * (E_pi * Real.exp (-(π / 2) * (x ^ 2 + y ^ 2))) :=
              mul_le_mul h1' hexp_xy (Real.exp_pos _).le (by positivity)
            exact mul_le_mul h2' hUx (spinUr_nonneg ha hr1 x) (by positivity)
        _ = (Cc * (π / 3) * CU * E_pi) * M * Real.exp (-(π / 2) * (x ^ 2 + y ^ 2)) := by ring
    -- First term `|A_r W(x, y) - F_{r, L}(x, y)|` bounded by `C' * M * V_1(x) * V_1(y)`
    have hterm1 : |spinMehlerOp r (vW a h) (x, y) - vFrL a r h (x, y)| ≤
        max (CU * (2 * Real.exp (a * (π / 3)) + Cc * Real.cosh (2 * π * Real.sqrt a) / (4 * π ^ 2)) +
              Cc * CU / (4 * π ^ 2))
            ((CS * CU + Cc * CU * (π * (π / 3 + 128 * π))) / (4 * π ^ 2)) *
          M * (spinV1 a x * spinV1 a y) := by
      rcases le_or_gt (mTau r) (x ^ 2) with htx | htx
      · -- Case `τ_r ≤ x²`: bound `|A_r W|` and `|F_{r, L}|` separately
        have hUx_V : spinUr a r x ≤
            (2 * Real.exp (a * (π / 3)) + Cc * Real.cosh (2 * π * Real.sqrt a) / (4 * π ^ 2)) *
              spinV1 a x := by
          rw [spinUr_eq ha hr0 hr1 x, Real.exp_add (-mTau r * x ^ 2) (a * mTau r)]
          have hsqrt : Real.sqrt (2 / (1 + r)) ≤ 2 := by
            rw [Real.sqrt_le_iff]; refine ⟨by norm_num, ?_⟩; rw [div_le_iff₀ (by linarith)]; linarith
          have hexp1 : Real.exp (-mTau r * x ^ 2) ≤ 1 :=
            Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
          have hEa : Real.exp (a * mTau r) ≤ Real.exp (a * (π / 3)) :=
            Real.exp_le_exp.mpr (by nlinarith)
          have hV_scale : spinV1 a (mLam r * x) ≤ spinV1 a x :=
            spinV1_scale_le ha (mLam_pos (by linarith)).le (mLam_le_one hr0) x
          have hI : Real.sqrt (2 / (1 + r)) * (Real.exp (-mTau r * x ^ 2) * Real.exp (a * mTau r)) *
              spinV1 a (mLam r * x) ≤ 2 * Real.exp (a * (π / 3)) * spinV1 a x := by
            have h1 : Real.exp (-mTau r * x ^ 2) * Real.exp (a * mTau r) ≤ Real.exp (a * (π / 3)) := by
              calc Real.exp (-mTau r * x ^ 2) * Real.exp (a * mTau r)
                  ≤ 1 * Real.exp (a * (π / 3)) := mul_le_mul hexp1 hEa (Real.exp_pos _).le zero_le_one
                _ = Real.exp (a * (π / 3)) := one_mul _
            have h2 := mul_le_mul hsqrt h1 (by positivity) (by norm_num)
            exact mul_le_mul h2 hV_scale (spinV1_nonneg ha _) (by positivity)
          have hch : Real.cosh (2 * π * Real.sqrt (a - 2) * (mLam r * x)) ≤
              Real.cosh (2 * π * Real.sqrt a) := by
            refine Real.cosh_le_cosh.mpr ?_
            have h1 : Real.sqrt (a - 2) ≤ Real.sqrt a := Real.sqrt_le_sqrt (by linarith)
            have hlam1 := mLam_le_one hr0
            have hlam0 := (mLam_pos (r := r) (by linarith)).le
            rw [abs_mul, abs_mul, abs_mul, abs_of_pos zero_lt_two, abs_of_pos Real.pi_pos,
                abs_of_nonneg (Real.sqrt_nonneg _), abs_mul, abs_of_nonneg hlam0,
                abs_of_pos (by positivity : 0 < 2 * π * Real.sqrt a)]
            have hmx : mLam r * |x| ≤ 1 := (mul_le_of_le_one_left (abs_nonneg x) hlam1).trans hx
            calc 2 * π * Real.sqrt (a - 2) * (mLam r * |x|)
                ≤ 2 * π * Real.sqrt a * (mLam r * |x|) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity)
              _ ≤ 2 * π * Real.sqrt a := mul_le_of_le_one_right (by positivity) hmx
          have hcr_V : spinCr a r ≤ (Cc / (4 * π ^ 2)) * spinV1 a x := by
            have hV := spinV1_ge_four_pi_sq_mul_sq_v ha x
            have h1 : mTau r ≤ spinV1 a x / (4 * π ^ 2) := by
              rw [le_div_iff₀ (by positivity)]
              have h4 : 4 * π ^ 2 * mTau r ≤ 4 * π ^ 2 * x ^ 2 :=
                mul_le_mul_of_nonneg_left htx (by positivity)
              linarith
            calc spinCr a r ≤ Cc * mTau r := hcr_le
              _ ≤ Cc * (spinV1 a x / (4 * π ^ 2)) := mul_le_mul_of_nonneg_left h1 hCc_pos.le
              _ = (Cc / (4 * π ^ 2)) * spinV1 a x := by ring
          have hII : spinCr a r * Real.exp (-mTau r * x ^ 2) *
              Real.cosh (2 * π * Real.sqrt (a - 2) * (mLam r * x)) ≤
              (Cc * Real.cosh (2 * π * Real.sqrt a) / (4 * π ^ 2)) * spinV1 a x := by
            have h1 : spinCr a r * Real.exp (-mTau r * x ^ 2) ≤ (Cc / (4 * π ^ 2)) * spinV1 a x :=
              (mul_le_of_le_one_right (spinCr_pos hr0 hr1).le hexp1).trans hcr_V
            have h2 := mul_le_mul h1 hch (Real.cosh_pos _).le (mul_nonneg (by positivity) (spinV1_nonneg ha x))
            exact h2.trans_eq (by ring)
          exact (add_le_add hI hII).trans_eq (by ring)
        have hcr_V : spinCr a r ≤ (Cc / (4 * π ^ 2)) * spinV1 a x := by
          have hV := spinV1_ge_four_pi_sq_mul_sq_v ha x
          have h1 : mTau r ≤ spinV1 a x / (4 * π ^ 2) := by
            rw [le_div_iff₀ (by positivity)]
            have h4 : 4 * π ^ 2 * mTau r ≤ 4 * π ^ 2 * x ^ 2 :=
              mul_le_mul_of_nonneg_left htx (by positivity)
            linarith
          calc spinCr a r ≤ Cc * mTau r := hcr_le
            _ ≤ Cc * (spinV1 a x / (4 * π ^ 2)) := mul_le_mul_of_nonneg_left h1 hCc_pos.le
            _ = (Cc / (4 * π ^ 2)) * spinV1 a x := by ring
        have hA : |spinMehlerOp r (vW a h) (x, y)| ≤
            CU * (2 * Real.exp (a * (π / 3)) + Cc * Real.cosh (2 * π * Real.sqrt a) / (4 * π ^ 2)) *
              M * (spinV1 a x * spinV1 a y) := by
          have h1 := hAW_le x y
          have hUy := hUr_away y hy
          have h2 : M * spinUr a r x * spinUr a r y ≤
              M * ((2 * Real.exp (a * (π / 3)) + Cc * Real.cosh (2 * π * Real.sqrt a) / (4 * π ^ 2)) *
                spinV1 a x) * (CU * spinV1 a y) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hUx_V hM) hUy (spinUr_nonneg ha hr1 y)
              (mul_nonneg hM (mul_nonneg (by positivity) (spinV1_nonneg ha x)))
          exact (h1.trans h2).trans_eq (by ring)
        have hF : |vFrL a r h (x, y)| ≤ (Cc * CU / (4 * π ^ 2)) * M * (spinV1 a x * spinV1 a y) := by
          have h1 := hFrL_le x y
          have hexp1 : Real.exp (-π * x ^ 2) ≤ 1 :=
            Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg x])
          have hUy := hUr_away y hy
          have h2 : M * spinCr a r * Real.exp (-π * x ^ 2) * spinUr a r y ≤
              M * ((Cc / (4 * π ^ 2)) * spinV1 a x) * 1 * (CU * spinV1 a y) :=
            mul_le_mul
              (mul_le_mul (mul_le_mul_of_nonneg_left hcr_V hM) hexp1 (Real.exp_pos _).le
                (mul_nonneg hM (mul_nonneg (by positivity) (spinV1_nonneg ha x))))
              hUy (spinUr_nonneg ha hr1 y)
              (mul_nonneg (mul_nonneg hM (mul_nonneg (by positivity) (spinV1_nonneg ha x))) zero_le_one)
          exact (h1.trans h2).trans_eq (by ring)
        have hle_max := le_max_left
          (CU * (2 * Real.exp (a * (π / 3)) + Cc * Real.cosh (2 * π * Real.sqrt a) / (4 * π ^ 2)) +
            Cc * CU / (4 * π ^ 2))
          ((CS * CU + Cc * CU * (π * (π / 3 + 128 * π))) / (4 * π ^ 2))
        have hnn : 0 ≤ M * (spinV1 a x * spinV1 a y) :=
          mul_nonneg hM (mul_nonneg (spinV1_nonneg ha x) (spinV1_nonneg ha y))
        have hdiff := abs_sub (spinMehlerOp r (vW a h) (x, y)) (vFrL a r h (x, y))
        calc |spinMehlerOp r (vW a h) (x, y) - vFrL a r h (x, y)|
            ≤ |spinMehlerOp r (vW a h) (x, y)| + |vFrL a r h (x, y)| := hdiff
          _ ≤ (CU * (2 * Real.exp (a * (π / 3)) + Cc * Real.cosh (2 * π * Real.sqrt a) / (4 * π ^ 2)) +
                Cc * CU / (4 * π ^ 2)) * M * (spinV1 a x * spinV1 a y) := by linarith
          _ ≤ _ := by nlinarith
      · -- Case `x² < τ_r`: split at `vAlpha a r h y`
        have hsplit : |spinMehlerOp r (vW a h) (x, y) - vFrL a r h (x, y)| ≤
            |spinMehlerOp r (vW a h) (x, y) - vAlpha a r h y| +
            |vAlpha a r h y - vFrL a r h (x, y)| := by
          have : spinMehlerOp r (vW a h) (x, y) - vFrL a r h (x, y) =
              (spinMehlerOp r (vW a h) (x, y) - vAlpha a r h y) +
              (vAlpha a r h y - vFrL a r h (x, y)) := by ring
          rw [this]; exact abs_add_le _ _
        have h1 : |spinMehlerOp r (vW a h) (x, y) - vAlpha a r h y| ≤
            CS * CU * M * x ^ 2 * spinV1 a y := by
          have hs := hCS r hr hM hh hd4 hbd x y htx.le
          have hUy := hUr_away y hy
          have hmul := mul_le_mul_of_nonneg_left hUy (by positivity : 0 ≤ CS * M * x ^ 2)
          linarith
        have h2 : |vAlpha a r h y - vFrL a r h (x, y)| ≤
            Cc * CU * (π * (π / 3 + 128 * π)) * M * x ^ 2 * spinV1 a y := by
          have hfac : vAlpha a r h y - vFrL a r h (x, y) =
              vAlpha a r h y * (1 - Real.exp (-π * x ^ 2) * Real.cos (2 * π * 8 * x * y)) := by
            unfold vFrL; ring
          rw [hfac, abs_mul]
          have htrig : |1 - Real.exp (-π * x ^ 2) * Real.cos (2 * π * 8 * x * y)| ≤
              π * x ^ 2 * (1 + 128 * π * y ^ 2) := by
            have h1_split : 1 - Real.exp (-π * x ^ 2) * Real.cos (2 * π * 8 * x * y) =
                (1 - Real.exp (-π * x ^ 2)) +
                Real.exp (-π * x ^ 2) * (1 - Real.cos (2 * π * 8 * x * y)) := by ring
            rw [h1_split]
            have htri' := abs_add_le (1 - Real.exp (-π * x ^ 2))
              (Real.exp (-π * x ^ 2) * (1 - Real.cos (2 * π * 8 * x * y)))
            have he1 : |1 - Real.exp (-π * x ^ 2)| ≤ π * x ^ 2 := by
              have ha1 : Real.exp (-π * x ^ 2) ≤ 1 :=
                Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg x])
              have ha2 : 1 - π * x ^ 2 ≤ Real.exp (-π * x ^ 2) := by
                have := Real.add_one_le_exp (-π * x ^ 2); linarith
              rw [abs_of_nonneg (by linarith)]; linarith
            have hc1 : |Real.exp (-π * x ^ 2) * (1 - Real.cos (2 * π * 8 * x * y))| ≤
                (2 * π * 8 * x * y) ^ 2 / 2 := by
              have hnn : 0 ≤ 1 - Real.cos (2 * π * 8 * x * y) := by linarith [Real.cos_le_one (2 * π * 8 * x * y)]
              rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hnn)]
              have he_le1 : Real.exp (-π * x ^ 2) ≤ 1 :=
                Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg x])
              have hcos_lb : 1 - Real.cos (2 * π * 8 * x * y) ≤ (2 * π * 8 * x * y) ^ 2 / 2 := by
                have hsin : 1 - Real.cos (2 * π * 8 * x * y) =
                    2 * Real.sin ((2 * π * 8 * x * y) / 2) ^ 2 := by
                  have := Real.cos_two_mul ((2 * π * 8 * x * y) / 2)
                  have hsc := Real.sin_sq_add_cos_sq ((2 * π * 8 * x * y) / 2)
                  have h2m : 2 * ((2 * π * 8 * x * y) / 2) = 2 * π * 8 * x * y := by ring
                  rw [h2m] at this; linarith
                rw [hsin]
                have habs : |Real.sin ((2 * π * 8 * x * y) / 2)| ≤ |(2 * π * 8 * x * y) / 2| :=
                  Real.abs_sin_le_abs
                have hsq : Real.sin ((2 * π * 8 * x * y) / 2) ^ 2 ≤ ((2 * π * 8 * x * y) / 2) ^ 2 := by
                  rw [← sq_abs (Real.sin _), ← sq_abs ((2 * π * 8 * x * y) / 2)]
                  exact pow_le_pow_left₀ (abs_nonneg _) habs 2
                linarith
              calc Real.exp (-π * x ^ 2) * (1 - Real.cos (2 * π * 8 * x * y))
                  ≤ 1 * ((2 * π * 8 * x * y) ^ 2 / 2) := mul_le_mul he_le1 hcos_lb hnn zero_le_one
                _ = (2 * π * 8 * x * y) ^ 2 / 2 := one_mul _
            linarith
          have hαy : |vAlpha a r h y| ≤ M * (Cc * mTau r) * (CU * Real.exp (-mTau r * y ^ 2) * spinV1 a y) := by
            have ha1 := vAlpha_abs_le ha hr0 hr1 hM hh hbd y
            have ha2 := (hCU r hr).1 y hy
            have h1' : M * spinCr a r ≤ M * (Cc * mTau r) := mul_le_mul_of_nonneg_left hcr_le hM
            exact ha1.trans (mul_le_mul h1' ha2 (spinUr_nonneg ha hr1 y) (by positivity))
          have hze : mTau r * y ^ 2 * Real.exp (-mTau r * y ^ 2) ≤ 1 := by
            have h1 : mTau r * y ^ 2 ≤ Real.exp (mTau r * y ^ 2) := by
              have := Real.add_one_le_exp (mTau r * y ^ 2); linarith
            have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-mTau r * y ^ 2)).le
            have hcancel : Real.exp (mTau r * y ^ 2) * Real.exp (-mTau r * y ^ 2) = 1 := by
              rw [← Real.exp_add]; simp
            exact h2.trans_eq hcancel
          have hcomb : mTau r * Real.exp (-mTau r * y ^ 2) * (1 + 128 * π * y ^ 2) ≤
              π / 3 + 128 * π := by
            have he1 : Real.exp (-mTau r * y ^ 2) ≤ 1 :=
              Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg y])
            have h1 : mTau r * Real.exp (-mTau r * y ^ 2) ≤ π / 3 :=
              (mul_le_of_le_one_right hτ_pos.le he1).trans hτ_le
            have h2 : 128 * π * (mTau r * y ^ 2 * Real.exp (-mTau r * y ^ 2)) ≤ 128 * π := by
              have := mul_le_mul_of_nonneg_left hze (by positivity : 0 ≤ 128 * π)
              exact this.trans_eq (mul_one _)
            have hexp : mTau r * Real.exp (-mTau r * y ^ 2) * (1 + 128 * π * y ^ 2) =
                mTau r * Real.exp (-mTau r * y ^ 2) +
                128 * π * (mTau r * y ^ 2 * Real.exp (-mTau r * y ^ 2)) := by ring
            rw [hexp]; exact add_le_add h1 h2
          calc |vAlpha a r h y| * |1 - Real.exp (-π * x ^ 2) * Real.cos (2 * π * 8 * x * y)|
              ≤ (M * (Cc * mTau r) * (CU * Real.exp (-mTau r * y ^ 2) * spinV1 a y)) *
                  (π * x ^ 2 * (1 + 128 * π * y ^ 2)) :=
                mul_le_mul hαy htrig (abs_nonneg _)
                  (mul_nonneg (by positivity) (mul_nonneg (by positivity) (spinV1_nonneg ha y)))
            _ = (Cc * CU * π * M * x ^ 2 * spinV1 a y) *
                  (mTau r * Real.exp (-mTau r * y ^ 2) * (1 + 128 * π * y ^ 2)) := by ring
            _ ≤ (Cc * CU * π * M * x ^ 2 * spinV1 a y) * (π / 3 + 128 * π) :=
                mul_le_mul_of_nonneg_left hcomb (mul_nonneg (by positivity) (spinV1_nonneg ha y))
            _ = Cc * CU * (π * (π / 3 + 128 * π)) * M * x ^ 2 * spinV1 a y := by ring
        have hx2_V : x ^ 2 ≤ spinV1 a x / (4 * π ^ 2) := by
          rw [le_div_iff₀ (by positivity)]
          linarith [spinV1_ge_four_pi_sq_mul_sq_v ha x]
        set K_s : ℝ := CS * CU + Cc * CU * (π * (π / 3 + 128 * π))
        have hK_s_nn : 0 ≤ K_s := by dsimp [K_s]; positivity
        have hle_max := le_max_right
          (CU * (2 * Real.exp (a * (π / 3)) + Cc * Real.cosh (2 * π * Real.sqrt a) / (4 * π ^ 2)) +
            Cc * CU / (4 * π ^ 2))
          (K_s / (4 * π ^ 2))
        have hnn : 0 ≤ M * (spinV1 a x * spinV1 a y) :=
          mul_nonneg hM (mul_nonneg (spinV1_nonneg ha x) (spinV1_nonneg ha y))
        have hsum : K_s * M * x ^ 2 * spinV1 a y ≤
            (K_s / (4 * π ^ 2)) * M * (spinV1 a x * spinV1 a y) := by
          have hmul := mul_le_mul_of_nonneg_left hx2_V (mul_nonneg hK_s_nn hM)
          have hmul2 := mul_le_mul_of_nonneg_right hmul (spinV1_nonneg ha y)
          exact hmul2.trans_eq (by ring)
        have h12 : |spinMehlerOp r (vW a h) (x, y) - vFrL a r h (x, y)| ≤
            K_s * M * x ^ 2 * spinV1 a y := by
          refine (hsplit.trans (add_le_add h1 h2)).trans_eq ?_
          dsimp [K_s]; ring
        have hle_fin : (K_s / (4 * π ^ 2)) * (M * (spinV1 a x * spinV1 a y)) ≤
            max (CU * (2 * Real.exp (a * (π / 3)) + Cc * Real.cosh (2 * π * Real.sqrt a) / (4 * π ^ 2)) +
              Cc * CU / (4 * π ^ 2))
              (K_s / (4 * π ^ 2)) * (M * (spinV1 a x * spinV1 a y)) :=
          mul_le_mul_of_nonneg_right hle_max hnn
        have hstep := h12.trans hsum
        rw [mul_assoc] at hstep ⊢
        exact hstep.trans hle_fin
    have hC_strip : Cc * (π / 3) * CU * E_pi +
        max (CU * (2 * Real.exp (a * (π / 3)) + Cc * Real.cosh (2 * π * Real.sqrt a) / (4 * π ^ 2)) +
              Cc * CU / (4 * π ^ 2))
            ((CS * CU + Cc * CU * (π * (π / 3 + 128 * π))) / (4 * π ^ 2)) ≤ C_big :=
      le_max_right _ _
    have h1_le : max (CU * (2 * Real.exp (a * (π / 3)) + Cc * Real.cosh (2 * π * Real.sqrt a) / (4 * π ^ 2)) +
              Cc * CU / (4 * π ^ 2))
            ((CS * CU + Cc * CU * (π * (π / 3 + 128 * π))) / (4 * π ^ 2)) ≤ C_big :=
      le_trans (le_add_of_nonneg_left (by positivity)) hC_strip
    have h2_le : Cc * (π / 3) * CU * E_pi ≤ C_big :=
      le_trans (le_add_of_nonneg_right (by positivity)) hC_strip
    unfold spinTheta; dsimp only
    have hnn1 : 0 ≤ M * (spinV1 a x * spinV1 a y) :=
      mul_nonneg hM (mul_nonneg (spinV1_nonneg ha x) (spinV1_nonneg ha y))
    have hnn2 : 0 ≤ M * Real.exp (-(π / 2) * (x ^ 2 + y ^ 2)) :=
      mul_nonneg hM (Real.exp_pos _).le
    have ht1' : |spinMehlerOp r (vW a h) (x, y) - vFrL a r h (x, y)| ≤
        C_big * (M * (spinV1 a x * spinV1 a y)) := by
      rw [mul_assoc] at hterm1
      exact hterm1.trans (mul_le_mul_of_nonneg_right h1_le hnn1)
    have ht2' : |vFrL a r h (y, x)| ≤ C_big * (M * Real.exp (-(π / 2) * (x ^ 2 + y ^ 2))) := by
      rw [mul_assoc] at hterm2
      exact hterm2.trans (mul_le_mul_of_nonneg_right h2_le hnn2)
    calc |spinMehlerOp r (vW a h) (x, y) - vFr a r h (x, y)|
        ≤ |spinMehlerOp r (vW a h) (x, y) - vFrL a r h (x, y)| + |vFrL a r h (y, x)| := htri
      _ ≤ C_big * (M * (spinV1 a x * spinV1 a y)) +
          C_big * (M * Real.exp (-(π / 2) * (x ^ 2 + y ^ 2))) := add_le_add ht1' ht2'
      _ = C_big * M * (spinV1 a x * spinV1 a y + Real.exp (-(π / 2) * (x ^ 2 + y ^ 2))) := by ring
  -- Case split on the 4 regions of `(p.1, p.2)`
  rcases le_or_gt 1 |p.1| with hp1 | hp1 <;> rcases le_or_gt 1 |p.2| with hp2 | hp2
  · -- Region 1: `|p.1| ≥ 1 ∧ |p.2| ≥ 1`
    have hA : |spinMehlerOp r (vW a h) p| ≤ CU ^ 2 * M * (spinV1 a p.1 * spinV1 a p.2) := by
      have h1 := hAW_le p.1 p.2
      have hU1 := hUr_away p.1 hp1
      have hU2 := hUr_away p.2 hp2
      have h2 : M * spinUr a r p.1 * spinUr a r p.2 ≤ M * (CU * spinV1 a p.1) * (CU * spinV1 a p.2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hU1 hM) hU2 (spinUr_nonneg ha hr1 p.2)
          (mul_nonneg hM (mul_nonneg hCU_pos.le (spinV1_nonneg ha p.1)))
      exact (h1.trans h2).trans_eq (by ring)
    have hF1 : |vFrL a r h p| ≤ Cc * (π / 3) * CU * M * (spinV1 a p.1 * spinV1 a p.2) := by
      have h1 := hFrL_le p.1 p.2
      have hU2 := hUr_away p.2 hp2
      have hexp1 : Real.exp (-π * p.1 ^ 2) ≤ spinV1 a p.1 := by
        have hV := spinV1_ge_four_pi_sq_mul_sq_v ha p.1
        have hp1sq : 1 ≤ p.1 ^ 2 := by rw [← sq_abs p.1]; nlinarith [abs_nonneg p.1]
        have he1 : Real.exp (-π * p.1 ^ 2) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg p.1])
        nlinarith [Real.pi_gt_three]
      have h2 : M * spinCr a r * Real.exp (-π * p.1 ^ 2) * spinUr a r p.2 ≤
          M * (Cc * (π / 3)) * spinV1 a p.1 * (CU * spinV1 a p.2) :=
        mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left hcr_bdd hM) hexp1 (Real.exp_pos _).le (by positivity))
          hU2 (spinUr_nonneg ha hr1 p.2)
          (mul_nonneg (by positivity) (spinV1_nonneg ha p.1))
      exact (h1.trans h2).trans_eq (by ring)
    have hF2 : |vFrL a r h p.swap| ≤ Cc * (π / 3) * CU * M * (spinV1 a p.1 * spinV1 a p.2) := by
      change |vFrL a r h (p.2, p.1)| ≤ _
      have h1 := hFrL_le p.2 p.1
      have hU1 := hUr_away p.1 hp1
      have hexp2 : Real.exp (-π * p.2 ^ 2) ≤ spinV1 a p.2 := by
        have hV := spinV1_ge_four_pi_sq_mul_sq_v ha p.2
        have hp2sq : 1 ≤ p.2 ^ 2 := by rw [← sq_abs p.2]; nlinarith [abs_nonneg p.2]
        have he2 : Real.exp (-π * p.2 ^ 2) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg p.2])
        nlinarith [Real.pi_gt_three]
      have h2 : M * spinCr a r * Real.exp (-π * p.2 ^ 2) * spinUr a r p.1 ≤
          M * (Cc * (π / 3)) * spinV1 a p.2 * (CU * spinV1 a p.1) :=
        mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left hcr_bdd hM) hexp2 (Real.exp_pos _).le (by positivity))
          hU1 (spinUr_nonneg ha hr1 p.1)
          (mul_nonneg (by positivity) (spinV1_nonneg ha p.2))
      exact (h1.trans h2).trans_eq (by ring)
    have hC1 : CU ^ 2 + 2 * Cc * (π / 3) * CU ≤ C_big :=
      (le_max_left _ _).trans (le_max_left _ _)
    have htri : |spinMehlerOp r (vW a h) p - vFr a r h p| ≤
        |spinMehlerOp r (vW a h) p| + |vFrL a r h p| + |vFrL a r h p.swap| := by
      unfold vFr
      have h1 := abs_sub (spinMehlerOp r (vW a h) p) (vFrL a r h p + vFrL a r h p.swap)
      have h2 := abs_add_le (vFrL a r h p) (vFrL a r h p.swap)
      linarith
    have hV_le_Th : spinV1 a p.1 * spinV1 a p.2 ≤ spinTheta a p := by
      unfold spinTheta; linarith [Real.exp_pos (-(π / 2) * (p.1 ^ 2 + p.2 ^ 2))]
    have hnn : 0 ≤ M * (spinV1 a p.1 * spinV1 a p.2) :=
      mul_nonneg hM (mul_nonneg (spinV1_nonneg ha p.1) (spinV1_nonneg ha p.2))
    calc |spinMehlerOp r (vW a h) p - vFr a r h p|
        ≤ (CU ^ 2 + 2 * Cc * (π / 3) * CU) * (M * (spinV1 a p.1 * spinV1 a p.2)) := by
          have := add_le_add (add_le_add hA hF1) hF2
          exact (htri.trans this).trans_eq (by ring)
      _ ≤ C_big * (M * (spinV1 a p.1 * spinV1 a p.2)) := mul_le_mul_of_nonneg_right hC1 hnn
      _ ≤ C_big * (M * spinTheta a p) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hV_le_Th hM) hC_pos.le
      _ = C_big * M * spinTheta a p := by ring
  · -- Region 4: `|p.1| ≥ 1 ∧ |p.2| < 1` — swap to Region 3!
    have hswap_eq : spinMehlerOp r (vW a h) p - vFr a r h p =
        spinMehlerOp r (vW a h) p.swap - vFr a r h p.swap := by
      have hF_sw : vFr a r h p.swap = vFr a r h p := by
        unfold vFr; simp [add_comm]
      have hAW_sw : spinMehlerOp r (vW a h) p.swap = spinMehlerOp r (vW a h) p := by
        unfold spinMehlerOp
        have hmp_e : MeasurePreserving (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ) volume volume := by
          refine ⟨MeasurableEquiv.prodComm.measurable, ?_⟩
          change Measure.map Prod.swap volume = volume
          rw [Measure.volume_eq_prod, Measure.prod_swap]
        rw [← hmp_e.integral_comp'
          (g := fun q : ℝ × ℝ => spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2 * vW a h q)]
        refine integral_congr_ae (Eventually.of_forall fun q => ?_)
        dsimp [MeasurableEquiv.prodComm, Prod.swap, vW]
        rw [hd4.2.2 q.1 q.2]; ring
      rw [hF_sw, hAW_sw]
    rw [hswap_eq, ← spinTheta_swap a p]
    exact hstrip p.2 p.1 hp2.le hp1
  · -- Region 3: `|p.1| < 1 ∧ |p.2| ≥ 1`
    exact hstrip p.1 p.2 hp1.le hp2
  · -- Region 2: `|p.1| < 1 ∧ |p.2| < 1`
    have hU1 := (hCU r hr).2.1 p.1 hp1.le
    have hU2 := (hCU r hr).2.1 p.2 hp2.le
    have hA : |spinMehlerOp r (vW a h) p| ≤ CU ^ 2 * M := by
      have h1 := hAW_le p.1 p.2
      have h2 : M * spinUr a r p.1 * spinUr a r p.2 ≤ M * CU * CU :=
        mul_le_mul (mul_le_mul_of_nonneg_left hU1 hM) hU2 (spinUr_nonneg ha hr1 p.2) (by positivity)
      exact (h1.trans h2).trans_eq (by ring)
    have hF1 : |vFrL a r h p| ≤ Cc * (π / 3) * CU * M := by
      have h1 := hFrL_le p.1 p.2
      have he1 : Real.exp (-π * p.1 ^ 2) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg p.1])
      have h2 : M * spinCr a r * Real.exp (-π * p.1 ^ 2) * spinUr a r p.2 ≤
          M * (Cc * (π / 3)) * 1 * CU :=
        mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left hcr_bdd hM) he1 (Real.exp_pos _).le (by positivity))
          hU2 (spinUr_nonneg ha hr1 p.2) (by positivity)
      exact (h1.trans h2).trans_eq (by ring)
    have hF2 : |vFrL a r h p.swap| ≤ Cc * (π / 3) * CU * M := by
      change |vFrL a r h (p.2, p.1)| ≤ _
      have h1 := hFrL_le p.2 p.1
      have he2 : Real.exp (-π * p.2 ^ 2) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg p.2])
      have h2 : M * spinCr a r * Real.exp (-π * p.2 ^ 2) * spinUr a r p.1 ≤
          M * (Cc * (π / 3)) * 1 * CU :=
        mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left hcr_bdd hM) he2 (Real.exp_pos _).le (by positivity))
          hU1 (spinUr_nonneg ha hr1 p.1) (by positivity)
      exact (h1.trans h2).trans_eq (by ring)
    have h1_le_Th : 1 ≤ Real.exp π * spinTheta a p := by
      have hsq : p.1 ^ 2 + p.2 ^ 2 ≤ 2 := by
        have h1 : p.1 ^ 2 ≤ 1 := by rw [← sq_abs p.1]; nlinarith [abs_nonneg p.1]
        have h2 : p.2 ^ 2 ≤ 1 := by rw [← sq_abs p.2]; nlinarith [abs_nonneg p.2]
        linarith
      have hexp : 1 ≤ Real.exp π * Real.exp (-(π / 2) * (p.1 ^ 2 + p.2 ^ 2)) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith [Real.pi_pos])
      have hTh : Real.exp (-(π / 2) * (p.1 ^ 2 + p.2 ^ 2)) ≤ spinTheta a p := by
        unfold spinTheta; linarith [mul_nonneg (spinV1_nonneg ha p.1) (spinV1_nonneg ha p.2)]
      exact hexp.trans (mul_le_mul_of_nonneg_left hTh (Real.exp_pos π).le)
    have hC2 : (CU ^ 2 + 2 * Cc * (π / 3) * CU) * Real.exp π ≤ C_big :=
      (le_max_right _ _).trans (le_max_left _ _)
    have htri : |spinMehlerOp r (vW a h) p - vFr a r h p| ≤
        |spinMehlerOp r (vW a h) p| + |vFrL a r h p| + |vFrL a r h p.swap| := by
      unfold vFr
      have h1 := abs_sub (spinMehlerOp r (vW a h) p) (vFrL a r h p + vFrL a r h p.swap)
      have h2 := abs_add_le (vFrL a r h p) (vFrL a r h p.swap)
      linarith
    have hnn_Th : 0 ≤ M * spinTheta a p := mul_nonneg hM (spinTheta_nonneg ha p)
    calc |spinMehlerOp r (vW a h) p - vFr a r h p|
        ≤ (CU ^ 2 + 2 * Cc * (π / 3) * CU) * M * 1 := by linarith
      _ ≤ (CU ^ 2 + 2 * Cc * (π / 3) * CU) * M * (Real.exp π * spinTheta a p) :=
          mul_le_mul_of_nonneg_left h1_le_Th (by positivity)
      _ = ((CU ^ 2 + 2 * Cc * (π / 3) * CU) * Real.exp π) * (M * spinTheta a p) := by ring
      _ ≤ C_big * (M * spinTheta a p) := mul_le_mul_of_nonneg_right hC2 hnn_Th
      _ = C_big * M * spinTheta a p := by ring

/-- Fubini symmetry of `spinMehlerOp r` against `vW a h` and decomposition into `D_r` and `F̂_r`. -/
private lemma v_mehler_decomp {a r M : ℝ} (ha : 2 ≤ a) (hr : r ∈ Ico (1 / 2 : ℝ) 1)
    {h : ℝ × ℝ → ℝ} (hM : 0 ≤ M) (hh : Measurable h) (hd4 : IsD4Invariant h) (hbd : ∀ p, |h p| ≤ M)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) :
    (∫ p : ℝ × ℝ, spinMehlerOp r Φ p * vW a h p) =
      (∫ p : ℝ × ℝ, Φ p * (spinMehlerOp r (vW a h) p - vFr a r h p)) -
      (∫ p : ℝ × ℝ, Φ p * (𝓕 (spinToEuc (vFr a r h)) (vE2ToProd.symm p)).re) := by
  have ⟨hr12, hr1⟩ := hr
  have hr0 : 0 ≤ r := by linarith
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := spinTestClass_L1_le_M2 ha
  obtain ⟨hΦ_inf, _⟩ := hC₀ hΦ
  -- Joint integrability of `K_r(p.1, q.1) K_r(p.2, q.2) Φ(q) W(p)` on `ℝ² × ℝ²`
  have hprod_int : Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      spinMehlerKernel1D r z.1.1 z.2.1 * spinMehlerKernel1D r z.1.2 z.2.2 *
        Φ z.2 * vW a h z.1) (volume.prod volume) := by
    rw [integrable_prod_iff]
    · refine ⟨Eventually.of_forall fun p => ?_, ?_⟩
      · have hint_K : Integrable (fun q : ℝ × ℝ =>
            spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2) := by
          rw [Measure.volume_eq_prod]
          have h1 := (integral_spinMehlerKernel1D_cosh hr0 hr1 (b := 0) le_rfl p.1).1
          have h2 := (integral_spinMehlerKernel1D_cosh hr0 hr1 (b := 0) le_rfl p.2).1
          simp only [Real.sqrt_zero, mul_zero, zero_mul, Real.cosh_zero, mul_one] at h1 h2
          exact h1.mul_prod h2
        refine (hint_K.const_mul (C₀ * spinM2 a Φ * |vW a h p|)).mono' ?_
          (Eventually.of_forall fun q => ?_)
        · have hK : Continuous (fun q : ℝ × ℝ =>
              spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2 * Φ q * vW a h p) := by
            have hK0 : Continuous (fun q : ℝ × ℝ =>
                spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2) := by
              unfold spinMehlerKernel1D; fun_prop
            exact (hK0.mul hΦ.cont).mul continuous_const
          exact hK.aestronglyMeasurable
        · rw [Real.norm_eq_abs, abs_mul, abs_mul,
              abs_of_nonneg (mul_nonneg (spinMehlerKernel1D_nonneg hr1 p.1 q.1)
                (spinMehlerKernel1D_nonneg hr1 p.2 q.2))]
          have h1 := hΦ_inf q
          have hnn := mul_nonneg (spinMehlerKernel1D_nonneg hr1 p.1 q.1)
            (spinMehlerKernel1D_nonneg hr1 p.2 q.2)
          have h2 := mul_le_mul_of_nonneg_left h1 hnn
          have h3 := mul_le_mul_of_nonneg_right h2 (abs_nonneg (vW a h p))
          linarith
      · have hτ_pos := mTau_pos hr0 hr1
        have hdom_p : Integrable (fun p : ℝ × ℝ =>
            (2 * C₀ * spinM2 a Φ * M) *
              (Real.exp (-mTau r * p.1 ^ 2 + 2 * π * Real.sqrt a * |p.1|) *
               Real.exp (-mTau r * p.2 ^ 2 + 2 * π * Real.sqrt a * |p.2|))) := by
          rw [Measure.volume_eq_prod]
          exact ((integrable_exp_neg_quad_linear hτ_pos).mul_prod
            (integrable_exp_neg_quad_linear hτ_pos)).const_mul _
        refine hdom_p.mono' ?_ (Eventually.of_forall fun p => ?_)
        · have hmeas_inner : Measurable (fun p : ℝ × ℝ => ∫ q : ℝ × ℝ,
              ‖spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2 *
                Φ q * vW a h p‖) := by
            have hK : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
                spinMehlerKernel1D r z.1.1 z.2.1 * spinMehlerKernel1D r z.1.2 z.2.2) := by
              unfold spinMehlerKernel1D; fun_prop
            have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
            have hW_m : Measurable (vW a h) :=
              (hh.mul (hV.measurable.comp measurable_fst)).mul (hV.measurable.comp measurable_snd)
            exact (continuous_norm.measurable.comp
              (((hK.measurable.mul (hΦ.cont.measurable.comp measurable_snd)).mul
                (hW_m.comp measurable_fst)))).stronglyMeasurable.integral_prod_right'.measurable
          exact hmeas_inner.aestronglyMeasurable
        · rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
          have hK_int : ∀ x : ℝ, Integrable (fun u : ℝ => spinMehlerKernel1D r x u) ∧
              (∫ u : ℝ, spinMehlerKernel1D r x u) =
                Real.sqrt (2 / (1 + r)) * Real.exp (-mTau r * x ^ 2) := fun x => by
            have h1 := integral_spinMehlerKernel1D_cosh hr0 hr1 (b := 0) le_rfl x
            simpa [Real.sqrt_zero, mul_zero, zero_mul, Real.cosh_zero] using h1
          have hprodK : Integrable (fun q : ℝ × ℝ =>
              (C₀ * spinM2 a Φ * |vW a h p|) *
                (spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2)) := by
            rw [Measure.volume_eq_prod]
            exact ((hK_int p.1).1.mul_prod (hK_int p.2).1).const_mul _
          have hle1 : (∫ q : ℝ × ℝ, ‖spinMehlerKernel1D r p.1 q.1 *
                spinMehlerKernel1D r p.2 q.2 * Φ q * vW a h p‖) ≤
              (C₀ * spinM2 a Φ * |vW a h p|) *
                ((Real.sqrt (2 / (1 + r)) * Real.exp (-mTau r * p.1 ^ 2)) *
                 (Real.sqrt (2 / (1 + r)) * Real.exp (-mTau r * p.2 ^ 2))) := by
            have hint_q : Integrable (fun q : ℝ × ℝ =>
                ‖spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2 * Φ q * vW a h p‖) := by
              refine hprodK.mono' ?_ (Eventually.of_forall fun q => ?_)
              · have hK : Continuous (fun q : ℝ × ℝ =>
                    spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2) := by
                  unfold spinMehlerKernel1D; fun_prop
                exact (continuous_norm.comp ((hK.mul hΦ.cont).mul continuous_const)).aestronglyMeasurable
              · rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_eq_abs, abs_mul, abs_mul,
                    abs_of_nonneg (mul_nonneg (spinMehlerKernel1D_nonneg hr1 p.1 q.1)
                      (spinMehlerKernel1D_nonneg hr1 p.2 q.2))]
                have h1 := hΦ_inf q
                have hnn := mul_nonneg (spinMehlerKernel1D_nonneg hr1 p.1 q.1)
                  (spinMehlerKernel1D_nonneg hr1 p.2 q.2)
                have h2 := mul_le_mul_of_nonneg_left h1 hnn
                have h3 := mul_le_mul_of_nonneg_right h2 (abs_nonneg (vW a h p))
                linarith
            calc ∫ q : ℝ × ℝ, ‖spinMehlerKernel1D r p.1 q.1 *
                    spinMehlerKernel1D r p.2 q.2 * Φ q * vW a h p‖
                ≤ ∫ q : ℝ × ℝ, (C₀ * spinM2 a Φ * |vW a h p|) *
                    (spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2) := by
                  refine integral_mono hint_q hprodK fun q => ?_
                  rw [Real.norm_eq_abs, abs_mul, abs_mul,
                      abs_of_nonneg (mul_nonneg (spinMehlerKernel1D_nonneg hr1 p.1 q.1)
                        (spinMehlerKernel1D_nonneg hr1 p.2 q.2))]
                  have h1 := hΦ_inf q
                  have hnn := mul_nonneg (spinMehlerKernel1D_nonneg hr1 p.1 q.1)
                    (spinMehlerKernel1D_nonneg hr1 p.2 q.2)
                  have h2 := mul_le_mul_of_nonneg_left h1 hnn
                  have h3 := mul_le_mul_of_nonneg_right h2 (abs_nonneg (vW a h p))
                  linarith
              _ = (C₀ * spinM2 a Φ * |vW a h p|) *
                    ((Real.sqrt (2 / (1 + r)) * Real.exp (-mTau r * p.1 ^ 2)) *
                     (Real.sqrt (2 / (1 + r)) * Real.exp (-mTau r * p.2 ^ 2))) := by
                  rw [integral_const_mul, Measure.volume_eq_prod, integral_prod_mul,
                      (hK_int p.1).2, (hK_int p.2).2]
          have hsqrt2 : Real.sqrt (2 / (1 + r)) * Real.sqrt (2 / (1 + r)) ≤ 2 := by
            rw [Real.mul_self_sqrt (by positivity), div_le_iff₀ (by linarith)]; linarith
          have hW_bd : |vW a h p| ≤ M * Real.exp (2 * π * Real.sqrt a * |p.1|) *
              Real.exp (2 * π * Real.sqrt a * |p.2|) := by
            unfold vW
            rw [abs_mul, abs_mul, abs_of_nonneg (spinV1_nonneg ha p.1),
                abs_of_nonneg (spinV1_nonneg ha p.2)]
            have h1 := hbd p
            have h2 := spinV1_le_exp ha p.1
            have h3 := spinV1_le_exp ha p.2
            exact mul_le_mul (mul_le_mul h1 h2 (spinV1_nonneg ha p.1) hM) h3 (spinV1_nonneg ha p.2) (by positivity)
          calc ∫ q : ℝ × ℝ, ‖spinMehlerKernel1D r p.1 q.1 *
                  spinMehlerKernel1D r p.2 q.2 * Φ q * vW a h p‖
              ≤ (C₀ * spinM2 a Φ * |vW a h p|) *
                  ((Real.sqrt (2 / (1 + r)) * Real.sqrt (2 / (1 + r))) *
                    Real.exp (-mTau r * p.1 ^ 2) * Real.exp (-mTau r * p.2 ^ 2)) := by
                linarith [show (Real.sqrt (2 / (1 + r)) * Real.exp (-mTau r * p.1 ^ 2)) *
                  (Real.sqrt (2 / (1 + r)) * Real.exp (-mTau r * p.2 ^ 2)) =
                  (Real.sqrt (2 / (1 + r)) * Real.sqrt (2 / (1 + r))) *
                    Real.exp (-mTau r * p.1 ^ 2) * Real.exp (-mTau r * p.2 ^ 2) by ring]
            _ ≤ (C₀ * spinM2 a Φ * (M * Real.exp (2 * π * Real.sqrt a * |p.1|) *
                  Real.exp (2 * π * Real.sqrt a * |p.2|))) *
                  (2 * Real.exp (-mTau r * p.1 ^ 2) * Real.exp (-mTau r * p.2 ^ 2)) := by
                have hM2 := spinM2_nonneg ha Φ
                gcongr
            _ = (2 * C₀ * spinM2 a Φ * M) *
                  (Real.exp (-mTau r * p.1 ^ 2 + 2 * π * Real.sqrt a * |p.1|) *
                   Real.exp (-mTau r * p.2 ^ 2 + 2 * π * Real.sqrt a * |p.2|)) := by
                rw [Real.exp_add (-mTau r * p.1 ^ 2), Real.exp_add (-mTau r * p.2 ^ 2)]; ring
    · have hK : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
          spinMehlerKernel1D r z.1.1 z.2.1 * spinMehlerKernel1D r z.1.2 z.2.2) := by
        unfold spinMehlerKernel1D; fun_prop
      have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
      have hW_m : Measurable (vW a h) :=
        (hh.mul (hV.measurable.comp measurable_fst)).mul (hV.measurable.comp measurable_snd)
      exact ((hK.measurable.mul (hΦ.cont.measurable.comp measurable_snd)).mul
        (hW_m.comp measurable_fst)).aestronglyMeasurable
  -- Swap integrals: `∫ (A_r Φ) W = ∫ Φ (A_r W)`
  have hswap : (∫ p : ℝ × ℝ, spinMehlerOp r Φ p * vW a h p) =
      ∫ q : ℝ × ℝ, Φ q * spinMehlerOp r (vW a h) q := by
    have hL : (∫ p : ℝ × ℝ, spinMehlerOp r Φ p * vW a h p) =
        ∫ p : ℝ × ℝ, ∫ q : ℝ × ℝ,
          spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2 * Φ q * vW a h p := by
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      dsimp only; unfold spinMehlerOp; rw [← integral_mul_const]
    have hR : (∫ q : ℝ × ℝ, Φ q * spinMehlerOp r (vW a h) q) =
        ∫ q : ℝ × ℝ, ∫ p : ℝ × ℝ,
          spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2 * Φ q * vW a h p := by
      refine integral_congr_ae (Eventually.of_forall fun q => ?_)
      dsimp only; unfold spinMehlerOp; rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      dsimp only
      rw [spinMehlerKernel1D_symm hr0 hr1 q.1 p.1, spinMehlerKernel1D_symm hr0 hr1 q.2 p.2]; ring
    rw [hL, hR, MeasureTheory.integral_integral_swap hprod_int]
  rw [hswap]
  have hFr_int := vFr_integrable ha hr hM hh hbd
  obtain ⟨hΦFr_int, _, hΦFr_eq⟩ := v_fourier_odd_pairing hΦ hFr_int
  obtain ⟨CD, _, hCD⟩ := v_Dr_dom ha
  obtain ⟨CTh, _, hCTh⟩ := spinTestClass_Theta_integrable ha
  have hDr_int : Integrable (fun q : ℝ × ℝ => Φ q * (spinMehlerOp r (vW a h) q - vFr a r h q)) := by
    refine ((hCTh hΦ).1.const_mul (CD * M)).mono' ?_ (Eventually.of_forall fun q => ?_)
    · have hAW_m : Measurable (spinMehlerOp r (vW a h)) := by
        unfold spinMehlerOp
        have hK : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
            spinMehlerKernel1D r z.1.1 z.2.1 * spinMehlerKernel1D r z.1.2 z.2.2) := by
          unfold spinMehlerKernel1D; fun_prop
        have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
        have hW_m : Measurable (vW a h) :=
          (hh.mul (hV.measurable.comp measurable_fst)).mul (hV.measurable.comp measurable_snd)
        exact (hK.measurable.mul (hW_m.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
      have hFr_m : Measurable (vFr a r h) := by
        have hFrL_m : Measurable (vFrL a r h) := by
          unfold vFrL
          have hc : Continuous (fun p : ℝ × ℝ =>
              Real.exp (-π * p.1 ^ 2) * Real.cos (2 * π * 8 * p.1 * p.2)) := by fun_prop
          exact hc.measurable.mul ((vAlpha_meas hh).comp measurable_snd)
        exact hFrL_m.add (hFrL_m.comp measurable_swap)
      exact (hΦ.cont.measurable.mul (hAW_m.sub hFr_m)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      have h1 := hCD r hr hM hh hd4 hbd q
      have h2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg (Φ q))
      linarith
  have hsplit : (fun q : ℝ × ℝ => Φ q * spinMehlerOp r (vW a h) q) =
      fun q => Φ q * (spinMehlerOp r (vW a h) q - vFr a r h q) + Φ q * vFr a r h q := by
    ext q; ring
  rw [hsplit, integral_add hDr_int hΦFr_int, hΦFr_eq]; ring

/-! ### Section 5: Convergence as `r ↑ 1` and proof of `SpinDV` -/

/-- On a compact box `K_R = [-R, R]²`, `∫_{K_R} (A_r Φ) W → ∫_{K_R} Φ W` as `r ↑ 1`. -/
private lemma v_tendsto_box {a M R : ℝ} (ha : 2 ≤ a) (hM : 0 ≤ M) (hR : 0 ≤ R)
    {h : ℝ × ℝ → ℝ} (hh : Measurable h) (hbd : ∀ p, |h p| ≤ M)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) :
    let K : Set (ℝ × ℝ) := Icc (-R) R ×ˢ Icc (-R) R
    Tendsto (fun r => ∫ p : ℝ × ℝ, spinMehlerOp r Φ p * K.indicator (vW a h) p)
      (𝓝[<] 1) (𝓝 (∫ p : ℝ × ℝ, Φ p * K.indicator (vW a h) p)) := by
  intro K
  have hK_meas : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := spinTestClass_L1_le_M2 ha
  obtain ⟨hΦ_inf, _⟩ := hC₀ hΦ
  -- Pointwise convergence `spinMehlerOp r Φ p → Φ p` via `tendsto_mehlerMean_of_continuous_weight`
  have hpt_tend : ∀ p : ℝ × ℝ, Tendsto (fun r => spinMehlerOp r Φ p) (𝓝[<] 1) (𝓝 (Φ p)) := by
    intro p
    let fE : RadialSpace 1 → ℝ := fun x => Φ (vE2ToProd x)
    have hfE_cont : Continuous fE := hΦ.cont.comp (by
      show Continuous vE2ToProd
      exact ((continuous_apply (0 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous).prodMk
        ((continuous_apply (1 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous) :
        Continuous vE2ToProd)
    have hfE_bd : ∀ y : RadialSpace 1, |fE y| ≤ (C₀ * spinM2 a Φ) * euclideanWeight 0 0 y := by
      intro y; unfold euclideanWeight; simp [fE]; exact hΦ_inf (vE2ToProd y)
    have ht := tendsto_mehlerMean_of_continuous_weight hfE_cont (b := 0) (d := 0)
      (mul_nonneg hC₀_pos.le (spinM2_nonneg ha Φ)) hfE_bd (vE2ToProd.symm p)
    have hval : fE (vE2ToProd.symm p) = Φ p := by simp [fE]
    rw [hval] at ht
    refine ht.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r ⟨hr0, hr1⟩
    unfold mehlerMean spinMehlerOp
    rw [← vVolume_preserving_e2ToProd.integral_comp' (g := fun q : ℝ × ℝ =>
      spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2 * Φ q)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp [fE]
    have hK := spinMehlerKernel1D_prod_eq_mehlerKernel hr0.le hr1 p (vE2ToProd y)
    have heq_p : (EuclideanSpace.equiv (Fin 2) ℝ).symm ![p.1, p.2] = vE2ToProd.symm p := by
      ext i; fin_cases i <;> rfl
    have heq_y : (EuclideanSpace.equiv (Fin 2) ℝ).symm ![(vE2ToProd y).1, (vE2ToProd y).2] = y := by
      ext i; fin_cases i <;> rfl
    rw [heq_p, heq_y] at hK
    rw [hK]
  -- Dominated convergence on `ℝ²` with compactly supported majorant `2 * C₀ * M₂ * M * cosh(2π√a R)² * 1_K`
  set B_box : ℝ := 2 * C₀ * spinM2 a Φ * M * Real.cosh (2 * π * Real.sqrt a * R) ^ 2
  have hB_nn : 0 ≤ B_box := mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (spinM2_nonneg ha Φ)) hM)
    (sq_nonneg _)
  have hdom_int : Integrable (K.indicator (fun _ : ℝ × ℝ => B_box)) :=
    (integrableOn_const (hs := by
      rw [Measure.volume_eq_prod, Measure.prod_prod]
      exact ENNReal.mul_lt_top measure_Icc_lt_top measure_Icc_lt_top |>.ne)).integrable_indicator hK_meas
  refine tendsto_integral_filter_of_dominated_convergence
    (F := fun r p => spinMehlerOp r Φ p * K.indicator (vW a h) p)
    (f := fun p => Φ p * K.indicator (vW a h) p)
    (bound := K.indicator (fun _ => B_box)) ?_ ?_ hdom_int ?_
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r ⟨hr12, hr1⟩
    have hAr_m : Measurable (spinMehlerOp r Φ) := by
      unfold spinMehlerOp
      have hK_c : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
          spinMehlerKernel1D r z.1.1 z.2.1 * spinMehlerKernel1D r z.1.2 z.2.2) := by
        unfold spinMehlerKernel1D; fun_prop
      exact (hK_c.measurable.mul (hΦ.cont.measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
    have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
    have hW_m : Measurable (vW a h) :=
      (hh.mul (hV.measurable.comp measurable_fst)).mul (hV.measurable.comp measurable_snd)
    exact (hAr_m.mul (hW_m.indicator hK_meas)).aestronglyMeasurable
  · filter_upwards [Ico_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r ⟨hr12, hr1⟩
    filter_upwards with p
    by_cases hp : p ∈ K
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Real.norm_eq_abs, abs_mul]
      have hAr_le : |spinMehlerOp r Φ p| ≤ 2 * C₀ * spinM2 a Φ := by
        have hr0 : 0 ≤ r := by linarith
        have hK_int : ∀ x : ℝ, Integrable (fun u : ℝ => spinMehlerKernel1D r x u) ∧
            (∫ u : ℝ, spinMehlerKernel1D r x u) =
              Real.sqrt (2 / (1 + r)) * Real.exp (-mTau r * x ^ 2) := fun x => by
          have h1 := integral_spinMehlerKernel1D_cosh hr0 hr1 (b := 0) le_rfl x
          simpa [Real.sqrt_zero, mul_zero, zero_mul, Real.cosh_zero] using h1
        have hprodK : Integrable (fun q : ℝ × ℝ =>
            (C₀ * spinM2 a Φ) * (spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2)) := by
          rw [Measure.volume_eq_prod]
          exact ((hK_int p.1).1.mul_prod (hK_int p.2).1).const_mul _
        have hint : Integrable (fun q : ℝ × ℝ =>
            spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2 * Φ q) := by
          refine hprodK.mono' ?_ (Eventually.of_forall fun q => ?_)
          · have hKc : Continuous (fun q : ℝ × ℝ =>
                spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2) := by
              unfold spinMehlerKernel1D; fun_prop
            exact (hKc.mul hΦ.cont).aestronglyMeasurable
          · rw [Real.norm_eq_abs, abs_mul,
                abs_of_nonneg (mul_nonneg (spinMehlerKernel1D_nonneg hr1 p.1 q.1)
                  (spinMehlerKernel1D_nonneg hr1 p.2 q.2))]
            have := mul_le_mul_of_nonneg_left (hΦ_inf q)
              (mul_nonneg (spinMehlerKernel1D_nonneg hr1 p.1 q.1)
                (spinMehlerKernel1D_nonneg hr1 p.2 q.2))
            linarith
        calc |spinMehlerOp r Φ p|
            ≤ ∫ q : ℝ × ℝ, |spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2 * Φ q| :=
              abs_integral_le_integral_abs
          _ ≤ ∫ q : ℝ × ℝ, (C₀ * spinM2 a Φ) *
                (spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2) := by
              refine integral_mono hint.abs hprodK fun q => ?_
              rw [abs_mul, abs_of_nonneg (mul_nonneg (spinMehlerKernel1D_nonneg hr1 p.1 q.1)
                (spinMehlerKernel1D_nonneg hr1 p.2 q.2))]
              have := mul_le_mul_of_nonneg_left (hΦ_inf q)
                (mul_nonneg (spinMehlerKernel1D_nonneg hr1 p.1 q.1)
                  (spinMehlerKernel1D_nonneg hr1 p.2 q.2))
              linarith
          _ = (C₀ * spinM2 a Φ) * ((Real.sqrt (2 / (1 + r)) * Real.sqrt (2 / (1 + r))) *
                Real.exp (-mTau r * p.1 ^ 2) * Real.exp (-mTau r * p.2 ^ 2)) := by
              rw [integral_const_mul, Measure.volume_eq_prod, integral_prod_mul,
                  (hK_int p.1).2, (hK_int p.2).2]; ring
          _ ≤ (C₀ * spinM2 a Φ) * (2 * 1 * 1) := by
              have hsq : Real.sqrt (2 / (1 + r)) * Real.sqrt (2 / (1 + r)) ≤ 2 := by
                rw [Real.mul_self_sqrt (by positivity), div_le_iff₀ (by linarith)]; linarith
              have he1 : Real.exp (-mTau r * p.1 ^ 2) ≤ 1 :=
                Real.exp_le_one_iff.mpr (by nlinarith [mTau_pos hr0 hr1, sq_nonneg p.1])
              have he2 : Real.exp (-mTau r * p.2 ^ 2) ≤ 1 :=
                Real.exp_le_one_iff.mpr (by nlinarith [mTau_pos hr0 hr1, sq_nonneg p.2])
              have hM2 := spinM2_nonneg ha Φ
              gcongr
          _ = 2 * C₀ * spinM2 a Φ := by ring
      have hW_le : |vW a h p| ≤ M * Real.cosh (2 * π * Real.sqrt a * R) ^ 2 := by
        unfold vW
        rw [abs_mul, abs_mul, abs_of_nonneg (spinV1_nonneg ha p.1),
            abs_of_nonneg (spinV1_nonneg ha p.2)]
        have hV_le : ∀ u : ℝ, u ∈ Icc (-R) R → spinV1 a u ≤ Real.cosh (2 * π * Real.sqrt a * R) := by
          intro u hu
          refine (spinV1_le_cosh ha u).trans (Real.cosh_le_cosh.mpr ?_)
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * π * Real.sqrt a),
              abs_of_nonneg (by positivity : 0 ≤ 2 * π * Real.sqrt a * R)]
          have hu_abs : |u| ≤ R := abs_le.mpr hu
          exact mul_le_mul_of_nonneg_left hu_abs (by positivity)
        have h1 := hbd p
        have h2 := hV_le p.1 hp.1
        have h3 := hV_le p.2 hp.2
        calc |h p| * spinV1 a p.1 * spinV1 a p.2
            ≤ M * Real.cosh (2 * π * Real.sqrt a * R) * Real.cosh (2 * π * Real.sqrt a * R) :=
              mul_le_mul (mul_le_mul h1 h2 (spinV1_nonneg ha p.1) hM) h3 (spinV1_nonneg ha p.2)
                (mul_nonneg hM (Real.cosh_pos _).le)
          _ = M * Real.cosh (2 * π * Real.sqrt a * R) ^ 2 := by ring
      calc |spinMehlerOp r Φ p| * |vW a h p|
          ≤ (2 * C₀ * spinM2 a Φ) * (M * Real.cosh (2 * π * Real.sqrt a * R) ^ 2) :=
            mul_le_mul hAr_le hW_le (abs_nonneg _) (mul_nonneg (by positivity) (spinM2_nonneg ha Φ))
        _ = B_box := by dsimp [B_box]; ring
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, mul_zero, norm_zero]
  · filter_upwards with p
    exact (hpt_tend p).mul_const _

/-- For `h_out = h · 1_{K_Rᶜ}` (`R ≥ 2`), `∫_{K_{R/2}} Φ D_{r, out} → 0` as `r ↑ 1`. -/
private lemma v_tendsto_inner_tail {a M R : ℝ} (ha : 2 ≤ a) (hM : 0 ≤ M) (hR : 2 ≤ R)
    {h : ℝ × ℝ → ℝ} (hh : Measurable h) (hbd : ∀ p, |h p| ≤ M)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) :
    let K : Set (ℝ × ℝ) := Icc (-R) R ×ˢ Icc (-R) R
    let K2 : Set (ℝ × ℝ) := Icc (-(R / 2)) (R / 2) ×ˢ Icc (-(R / 2)) (R / 2)
    let h_out : ℝ × ℝ → ℝ := Kᶜ.indicator h
    Tendsto (fun r => ∫ p in K2, Φ p * (spinMehlerOp r (vW a h_out) p - vFr a r h_out p))
      (𝓝[<] 1) (𝓝 0) := by
  intro K K2 h_out
  have hK_meas : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  have hK2_meas : MeasurableSet K2 := measurableSet_Icc.prod measurableSet_Icc
  have hh_out : Measurable h_out := hh.indicator hK_meas.compl
  have hbd_out : ∀ p, |h_out p| ≤ M := fun p => by
    dsimp [h_out]
    by_cases hp : p ∈ Kᶜ
    · rw [Set.indicator_of_mem hp]; exact hbd p
    · rw [Set.indicator_of_notMem hp, abs_zero]; exact hM
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := spinTestClass_L1_le_M2 ha
  obtain ⟨hΦ_inf, _⟩ := hC₀ hΦ
  obtain ⟨CU, hCU_pos, hCU⟩ := spinUr_bounds ha
  -- Show uniform convergence to `0` of `A_r W_out` and `F_{r, out}` on `K2`
  -- Step 1: `|A_r W_out(p)|` on `K2` vanishes as `r ↑ 1`:
  -- For `p ∈ K2` and `q ∈ Kᶜ`, either `|q.1| > R` (so `|p.1 - q.1| ≥ R/2 ≥ 1`) or `|q.2| > R`.
  -- Use `K_r(x, u) ≤ √(2/(1-r)) exp(-π / (1-r) * (x - u)²)` (from `mehlerKernel_le_half_gaussian`!)
  -- and split `-π/(1-r) (x-u)² = -π/(2(1-r)) (x-u)² - π/(2(1-r)) (x-u)² ≤ -π R²/(8(1-r)) - π/2 (x-u)²`!
  have hK1_half : ∀ {r : ℝ}, (1 / 2 : ℝ) ≤ r → r < 1 → ∀ x u : ℝ,
      spinMehlerKernel1D r x u ≤
        Real.sqrt (2 / (1 - r)) * Real.exp (-π / (1 - r) * (x - u) ^ 2) := by
    intro r hr12 hr1 x u
    rw [spinMehlerKernel1D_eq_symm_form (by linarith) hr1 x u]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.sqrt_nonneg _)
    have h1r : 0 < 1 - r := sub_pos.mpr hr1
    have hsq_r : (1 : ℝ) ≤ 2 * Real.sqrt r := by
      have : (1 : ℝ) ≤ 4 * r := by linarith
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt (4 * r) := Real.sqrt_le_sqrt this
        _ = 2 * Real.sqrt r := by
            rw [show (4 : ℝ) * r = 2 ^ 2 * r by ring, Real.sqrt_mul (sq_nonneg 2), Real.sqrt_sq zero_le_two]
    have hquad : 2 * Real.sqrt r * (x - u) ^ 2 ≤ (1 + r) * (x ^ 2 + u ^ 2) - 4 * Real.sqrt r * x * u := by
      have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt (by linarith)
      have : (1 + r) * (x ^ 2 + u ^ 2) - 4 * Real.sqrt r * x * u - 2 * Real.sqrt r * (x - u) ^ 2 =
          (1 - Real.sqrt r) ^ 2 * (x ^ 2 + u ^ 2) := by
        linear_combination (x ^ 2 + u ^ 2) * hsq.symm
      have hnn : 0 ≤ (1 - Real.sqrt r) ^ 2 * (x ^ 2 + u ^ 2) := by positivity
      linarith
    have hge : (x - u) ^ 2 ≤ (1 + r) * (x ^ 2 + u ^ 2) - 4 * Real.sqrt r * x * u := by
      have : (x - u) ^ 2 ≤ 2 * Real.sqrt r * (x - u) ^ 2 :=
        le_mul_of_one_le_left (sq_nonneg _) hsq_r
      linarith
    have hdiv : -π * ((1 + r) * (x ^ 2 + u ^ 2) - 4 * Real.sqrt r * x * u) / (1 - r) ≤
        -π * (x - u) ^ 2 / (1 - r) := by
      refine div_le_div_of_nonneg_right ?_ h1r.le
      nlinarith [Real.pi_pos]
    exact hdiv.trans_eq (by ring)
  -- For `|x| ≤ R/2` and `|u| ≥ R`, `|x - u| ≥ R/2 ≥ 1` and `|u| ≤ |x - u| + R/2`:
  set I_tail : ℝ := ∫ s : ℝ, Real.exp (-π * s ^ 2 + 2 * π * Real.sqrt a * |s|)
  have hI_tail_nn : 0 ≤ I_tail := integral_nonneg fun _ => (Real.exp_pos _).le
  set C_U_box : ℝ := CU * Real.exp (2 * π * Real.sqrt a * (R / 2))
  have htail_1D : ∀ r ∈ Ico (1 / 2 : ℝ) 1, ∀ x : ℝ, |x| ≤ R / 2 →
      (∫ u in {u : ℝ | R < |u|}, spinMehlerKernel1D r x u * spinV1 a u) ≤
        Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
          Real.exp (2 * π * Real.sqrt a * (R / 2)) * I_tail := by
    intro r ⟨hr12, hr1⟩ x hx
    have h1r : 0 < 1 - r := sub_pos.mpr hr1
    have h1r_le : 1 - r ≤ 1 / 2 := by linarith
    have hint_dom : Integrable (fun u : ℝ =>
        (Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
          Real.exp (2 * π * Real.sqrt a * (R / 2))) *
          Real.exp (-π * (x - u) ^ 2 + 2 * π * Real.sqrt a * |x - u|)) := by
      have h1 : Integrable (fun s : ℝ => Real.exp (-π * s ^ 2 + 2 * π * Real.sqrt a * |s|)) :=
        integrable_exp_neg_quad_linear Real.pi_pos
      have h2 := (h1.comp_sub_left x).const_mul
        (Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
          Real.exp (2 * π * Real.sqrt a * (R / 2)))
      exact h2
    have hle1 : ∫ u in {u : ℝ | R < |u|}, spinMehlerKernel1D r x u * spinV1 a u ≤
        ∫ u in {u : ℝ | R < |u|},
          (Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
            Real.exp (2 * π * Real.sqrt a * (R / 2))) *
            Real.exp (-π * (x - u) ^ 2 + 2 * π * Real.sqrt a * |x - u|) := by
      refine setIntegral_mono_on (spinUr_integrable ha (by linarith) hr1 x).integrableOn
        hint_dom.integrableOn
        (measurableSet_lt measurable_const continuous_abs.measurable) fun u hu => ?_
      have hxu : 1 ≤ |x - u| := by
        have h1 : |u| - |x| ≤ |u - x| := abs_sub_abs_le_abs_sub u x
        rw [abs_sub_comm] at h1
        have hu' : R < |u| := hu
        linarith
      have hxusq : 1 ≤ (x - u) ^ 2 := by rw [← sq_abs (x - u)]; nlinarith [abs_nonneg (x - u)]
      have hhalf : -π / (1 - r) * (x - u) ^ 2 ≤ -π / (2 * (1 - r)) - π * (x - u) ^ 2 := by
        have hpos : 0 < π / (2 * (1 - r)) := by positivity
        have h1 : π / (2 * (1 - r)) ≤ π / (2 * (1 - r)) * (x - u) ^ 2 :=
          le_mul_of_one_le_right hpos.le hxusq
        have h2 : π * (x - u) ^ 2 ≤ π / (2 * (1 - r)) * (x - u) ^ 2 := by
          have : π ≤ π / (2 * (1 - r)) := by rw [le_div_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
          exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
        have hsplit : -π / (1 - r) * (x - u) ^ 2 =
            -(π / (2 * (1 - r)) * (x - u) ^ 2) - (π / (2 * (1 - r)) * (x - u) ^ 2) := by
          field_simp [h1r.ne']; ring
        have hneg : -π / (2 * (1 - r)) = -(π / (2 * (1 - r))) := by ring
        linarith
      have hu_tri : |u| ≤ R / 2 + |x - u| := by
        have h1 : |u| - |x| ≤ |u - x| := abs_sub_abs_le_abs_sub u x
        rw [abs_sub_comm] at h1; linarith
      calc spinMehlerKernel1D r x u * spinV1 a u
          ≤ (Real.sqrt (2 / (1 - r)) * Real.exp (-π / (1 - r) * (x - u) ^ 2)) *
              Real.exp (2 * π * Real.sqrt a * |u|) :=
            mul_le_mul (hK1_half hr12 hr1 x u) (spinV1_le_exp ha u) (spinV1_nonneg ha u) (by positivity)
        _ = Real.sqrt (2 / (1 - r)) *
              Real.exp (-π / (1 - r) * (x - u) ^ 2 + 2 * π * Real.sqrt a * |u|) := by
            rw [mul_assoc, ← Real.exp_add]
        _ ≤ Real.sqrt (2 / (1 - r)) *
              Real.exp (-π / (2 * (1 - r)) - π * (x - u) ^ 2 +
                2 * π * Real.sqrt a * (R / 2 + |x - u|)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.sqrt_nonneg _)
            have := mul_le_mul_of_nonneg_left hu_tri (by positivity : 0 ≤ 2 * π * Real.sqrt a)
            linarith
        _ = (Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
              Real.exp (2 * π * Real.sqrt a * (R / 2))) *
              Real.exp (-π * (x - u) ^ 2 + 2 * π * Real.sqrt a * |x - u|) := by
            rw [mul_assoc (Real.sqrt _), mul_assoc (Real.sqrt _), ← Real.exp_add, ← Real.exp_add]
            congr 2; ring
    have hle2 : ∫ u in {u : ℝ | R < |u|},
          (Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
            Real.exp (2 * π * Real.sqrt a * (R / 2))) *
            Real.exp (-π * (x - u) ^ 2 + 2 * π * Real.sqrt a * |x - u|) ≤
        ∫ u : ℝ,
          (Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
            Real.exp (2 * π * Real.sqrt a * (R / 2))) *
            Real.exp (-π * (x - u) ^ 2 + 2 * π * Real.sqrt a * |x - u|) :=
      setIntegral_le_integral hint_dom (Eventually.of_forall fun _ => by positivity)
    have heq : (∫ u : ℝ, (Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
            Real.exp (2 * π * Real.sqrt a * (R / 2))) *
            Real.exp (-π * (x - u) ^ 2 + 2 * π * Real.sqrt a * |x - u|)) =
        Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
          Real.exp (2 * π * Real.sqrt a * (R / 2)) * I_tail := by
      rw [integral_const_mul, integral_sub_left_eq_self
        (f := fun s => Real.exp (-π * s ^ 2 + 2 * π * Real.sqrt a * |s|)) volume x]
    exact (hle1.trans hle2).trans_eq heq
  -- Uniform bound on `|A_r W_out(p) - F_{r, out}(p)|` for `p ∈ K2`
  have hUr_K2 : ∀ r ∈ Ico (1 / 2 : ℝ) 1, ∀ x : ℝ, |x| ≤ R / 2 → spinUr a r x ≤ C_U_box := by
    intro r hr x hx
    have h1 := (hCU r hr).2.2 x
    have he1 : Real.exp (-mTau r * x ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mTau_pos (by linarith [hr.1]) hr.2, sq_nonneg x])
    have he2 : Real.exp (2 * π * Real.sqrt a * |x|) ≤ Real.exp (2 * π * Real.sqrt a * (R / 2)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx (by positivity))
    calc spinUr a r x
        ≤ CU * Real.exp (-mTau r * x ^ 2 + 2 * π * Real.sqrt a * |x|) := h1
      _ = CU * (Real.exp (-mTau r * x ^ 2) * Real.exp (2 * π * Real.sqrt a * |x|)) := by
          rw [Real.exp_add]
      _ ≤ CU * (1 * Real.exp (2 * π * Real.sqrt a * (R / 2))) := by gcongr
      _ = C_U_box := by dsimp [C_U_box]; ring
  let g_r : ℝ → ℝ := fun r =>
    (C₀ * spinM2 a Φ * R ^ 2) *
      (2 * M * C_U_box * Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
          Real.exp (2 * π * Real.sqrt a * (R / 2)) * I_tail +
       2 * M * C_U_box * spinCr a r)
  have hg_r_tend : Tendsto g_r (𝓝[<] 1) (𝓝 0) := by
    have hdecay : Tendsto (fun r : ℝ => Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))))
        (𝓝[<] 1) (𝓝 0) := by
      -- Substitute `t = 1 / (1 - r) → +∞`: `√(2t) * exp(-π t / 2) ≤ 2 t * exp(-π t / 2) → 0`
      have ht : Tendsto (fun r : ℝ => (1 - r)⁻¹) (𝓝[<] 1) atTop := by
        refine Tendsto.inv_tendsto_nhdsGT_zero ?_
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have : Tendsto (fun r : ℝ => 1 - r) (𝓝 1) (𝓝 (1 - 1)) :=
            tendsto_const_nhds.sub tendsto_id
          simpa using this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with r hr
          exact sub_pos.mpr hr
      have h0 : Tendsto (fun t : ℝ => Real.sqrt (2 * t) * Real.exp (-(π / 2) * t)) atTop (𝓝 0) := by
        refine squeeze_zero_norm' ?_ (by
          have h1 := tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
          have h2 := h1.comp (tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < π / 2))
          have h3 := h2.const_mul (4 / π)
          simpa [mul_zero] using h3 :
            Tendsto (fun t : ℝ => (4 / π) * (((π / 2) * t) ^ 1 * Real.exp (-((π / 2) * t)))) atTop (𝓝 0))
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
        rw [Real.norm_of_nonneg (by positivity)]
        have hsq : Real.sqrt (2 * t) ≤ 2 * t := by
          rw [Real.sqrt_le_iff]; refine ⟨by linarith, by nlinarith⟩
        have hmul := mul_le_mul_of_nonneg_right hsq (Real.exp_pos (-(π / 2) * t)).le
        refine hmul.trans_eq ?_
        field_simp [Real.pi_pos.ne']; ring
      refine (h0.comp ht).congr' ?_
      filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r ⟨_, hr1⟩
      dsimp [Function.comp]
      have h1 : 2 * (1 - r)⁻¹ = 2 / (1 - r) := by rw [div_eq_mul_inv]
      have h2 : -(π / 2) * (1 - r)⁻¹ = -π / (2 * (1 - r)) := by
        have h1r : (1 - r) ≠ 0 := sub_ne_zero.mpr hr1.ne'
        field_simp [h1r]
      rw [h1, h2]
    have h1 := (hdecay.const_mul (2 * M * C_U_box)).mul_const
      (Real.exp (2 * π * Real.sqrt a * (R / 2)) * I_tail)
    have h2 := (spinCr_tendsto_zero a).const_mul (2 * M * C_U_box)
    have h3 := (h1.add h2).const_mul (C₀ * spinM2 a Φ * R ^ 2)
    have hfin : (fun r => (C₀ * spinM2 a Φ * R ^ 2) *
        (2 * M * C_U_box * (Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r)))) *
          (Real.exp (2 * π * Real.sqrt a * (R / 2)) * I_tail) +
         2 * M * C_U_box * spinCr a r)) = g_r := by
      ext r; dsimp [g_r]; ring
    rw [hfin] at h3
    simpa using h3
  refine squeeze_zero_norm' ?_ hg_r_tend
  filter_upwards [Ico_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r hr
  have ⟨hr12, hr1⟩ := hr
  have hr0 : 0 ≤ r := by linarith
  -- Pointwise bound on `K2`
  have hpt_K2 : ∀ p ∈ K2,
      |Φ p * (spinMehlerOp r (vW a h_out) p - vFr a r h_out p)| ≤
        (C₀ * spinM2 a Φ) *
          (2 * M * C_U_box * Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
              Real.exp (2 * π * Real.sqrt a * (R / 2)) * I_tail +
           2 * M * C_U_box * spinCr a r) := by
    intro p hp
    have hp1 : |p.1| ≤ R / 2 := abs_le.mpr hp.1
    have hp2 : |p.2| ≤ R / 2 := abs_le.mpr hp.2
    -- Bound `|A_r W_out(p)|`
    have hAW_out : |spinMehlerOp r (vW a h_out) p| ≤
        2 * M * C_U_box * Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
          Real.exp (2 * π * Real.sqrt a * (R / 2)) * I_tail := by
      unfold spinMehlerOp
      rw [Measure.volume_eq_prod]
      let S1 : Set (ℝ × ℝ) := {q : ℝ × ℝ | R < |q.1|}
      let S2 : Set (ℝ × ℝ) := {q : ℝ × ℝ | R < |q.2|}
      have hS1_m : MeasurableSet S1 := measurableSet_lt measurable_const (continuous_abs.comp continuous_fst).measurable
      have hS2_m : MeasurableSet S2 := measurableSet_lt measurable_const (continuous_abs.comp continuous_snd).measurable
      have hdom_all : Integrable (fun q : ℝ × ℝ =>
          M * ((spinMehlerKernel1D r p.1 q.1 * spinV1 a q.1) *
               (spinMehlerKernel1D r p.2 q.2 * spinV1 a q.2))) (volume.prod volume) :=
        ((spinUr_integrable ha hr0 hr1 p.1).mul_prod (spinUr_integrable ha hr0 hr1 p.2)).const_mul M
      have hint_Wout : Integrable (fun q : ℝ × ℝ =>
          spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2 * vW a h_out q) (volume.prod volume) := by
        refine hdom_all.mono' ?_ (Eventually.of_forall fun q => ?_)
        · have hK1 : Continuous (fun u : ℝ => spinMehlerKernel1D r p.1 u) := by
            unfold spinMehlerKernel1D; fun_prop
          have hK2 : Continuous (fun v : ℝ => spinMehlerKernel1D r p.2 v) := by
            unfold spinMehlerKernel1D; fun_prop
          have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
          exact (((hK1.measurable.comp measurable_fst).mul (hK2.measurable.comp measurable_snd)).mul
            ((hh_out.mul (hV.measurable.comp measurable_fst)).mul
              (hV.measurable.comp measurable_snd))).aestronglyMeasurable
        · unfold vW
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
              abs_of_nonneg (spinMehlerKernel1D_nonneg hr1 p.1 q.1),
              abs_of_nonneg (spinMehlerKernel1D_nonneg hr1 p.2 q.2),
              abs_of_nonneg (spinV1_nonneg ha q.1), abs_of_nonneg (spinV1_nonneg ha q.2)]
          have hnn : 0 ≤ (spinMehlerKernel1D r p.1 q.1 * spinV1 a q.1) *
              (spinMehlerKernel1D r p.2 q.2 * spinV1 a q.2) :=
            mul_nonneg (mul_nonneg (spinMehlerKernel1D_nonneg hr1 p.1 q.1) (spinV1_nonneg ha q.1))
              (mul_nonneg (spinMehlerKernel1D_nonneg hr1 p.2 q.2) (spinV1_nonneg ha q.2))
          have := mul_le_mul_of_nonneg_right (hbd_out q) hnn; linarith
      have hpt_ind : ∀ q : ℝ × ℝ,
          |spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2 * vW a h_out q| ≤
          S1.indicator (fun q => M * ((spinMehlerKernel1D r p.1 q.1 * spinV1 a q.1) *
            (spinMehlerKernel1D r p.2 q.2 * spinV1 a q.2))) q +
          S2.indicator (fun q => M * ((spinMehlerKernel1D r p.1 q.1 * spinV1 a q.1) *
            (spinMehlerKernel1D r p.2 q.2 * spinV1 a q.2))) q := by
        intro q
        by_cases hqK : q ∈ K
        · have h0 : h_out q = 0 := Set.indicator_of_notMem (not_not.mpr hqK) h
          unfold vW; rw [h0, zero_mul, zero_mul, mul_zero, abs_zero]
          exact add_nonneg
            (Set.indicator_nonneg (fun _ _ => mul_nonneg hM (mul_nonneg
              (mul_nonneg (spinMehlerKernel1D_nonneg hr1 _ _) (spinV1_nonneg ha _))
              (mul_nonneg (spinMehlerKernel1D_nonneg hr1 _ _) (spinV1_nonneg ha _)))) q)
            (Set.indicator_nonneg (fun _ _ => mul_nonneg hM (mul_nonneg
              (mul_nonneg (spinMehlerKernel1D_nonneg hr1 _ _) (spinV1_nonneg ha _))
              (mul_nonneg (spinMehlerKernel1D_nonneg hr1 _ _) (spinV1_nonneg ha _)))) q)
        · have hq_or : q ∈ S1 ∨ q ∈ S2 := by
            by_contra hneither
            push Not at hneither
            have h1 : |q.1| ≤ R := not_lt.mp hneither.1
            have h2 : |q.2| ≤ R := not_lt.mp hneither.2
            exact hqK ⟨abs_le.mp h1, abs_le.mp h2⟩
          have hbound_q : |spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2 * vW a h_out q| ≤
              M * ((spinMehlerKernel1D r p.1 q.1 * spinV1 a q.1) *
                   (spinMehlerKernel1D r p.2 q.2 * spinV1 a q.2)) := by
            unfold vW
            rw [abs_mul, abs_mul, abs_mul, abs_mul,
                abs_of_nonneg (spinMehlerKernel1D_nonneg hr1 p.1 q.1),
                abs_of_nonneg (spinMehlerKernel1D_nonneg hr1 p.2 q.2),
                abs_of_nonneg (spinV1_nonneg ha q.1), abs_of_nonneg (spinV1_nonneg ha q.2)]
            have hnn : 0 ≤ (spinMehlerKernel1D r p.1 q.1 * spinV1 a q.1) *
                (spinMehlerKernel1D r p.2 q.2 * spinV1 a q.2) :=
              mul_nonneg (mul_nonneg (spinMehlerKernel1D_nonneg hr1 p.1 q.1) (spinV1_nonneg ha q.1))
                (mul_nonneg (spinMehlerKernel1D_nonneg hr1 p.2 q.2) (spinV1_nonneg ha q.2))
            have := mul_le_mul_of_nonneg_right (hbd_out q) hnn; linarith
          rcases hq_or with hq1 | hq2
          · rw [Set.indicator_of_mem hq1]
            linarith [Set.indicator_nonneg (s := S2) (f := fun q => M *
              ((spinMehlerKernel1D r p.1 q.1 * spinV1 a q.1) *
               (spinMehlerKernel1D r p.2 q.2 * spinV1 a q.2)))
              (fun _ _ => mul_nonneg hM (mul_nonneg
                (mul_nonneg (spinMehlerKernel1D_nonneg hr1 _ _) (spinV1_nonneg ha _))
                (mul_nonneg (spinMehlerKernel1D_nonneg hr1 _ _) (spinV1_nonneg ha _)))) q]
          · rw [Set.indicator_of_mem hq2]
            linarith [Set.indicator_nonneg (s := S1) (f := fun q => M *
              ((spinMehlerKernel1D r p.1 q.1 * spinV1 a q.1) *
               (spinMehlerKernel1D r p.2 q.2 * spinV1 a q.2)))
              (fun _ _ => mul_nonneg hM (mul_nonneg
                (mul_nonneg (spinMehlerKernel1D_nonneg hr1 _ _) (spinV1_nonneg ha _))
                (mul_nonneg (spinMehlerKernel1D_nonneg hr1 _ _) (spinV1_nonneg ha _)))) q]
      have hI1 : ∫ q : ℝ × ℝ, S1.indicator (fun q => M *
            ((spinMehlerKernel1D r p.1 q.1 * spinV1 a q.1) *
             (spinMehlerKernel1D r p.2 q.2 * spinV1 a q.2))) q ∂(volume.prod volume) ≤
          M * C_U_box * Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
            Real.exp (2 * π * Real.sqrt a * (R / 2)) * I_tail := by
        have hfac : S1.indicator (fun q : ℝ × ℝ => M *
            ((spinMehlerKernel1D r p.1 q.1 * spinV1 a q.1) *
             (spinMehlerKernel1D r p.2 q.2 * spinV1 a q.2))) =
            fun q => M * (({u : ℝ | R < |u|}.indicator (fun u => spinMehlerKernel1D r p.1 u * spinV1 a u) q.1) *
              (spinMehlerKernel1D r p.2 q.2 * spinV1 a q.2)) := by
          ext q; by_cases hq : R < |q.1|
          · simp [S1, hq]
          · simp [S1, hq]
        rw [hfac, integral_const_mul, integral_prod_mul
            (fun u => {u : ℝ | R < |u|}.indicator (fun u => spinMehlerKernel1D r p.1 u * spinV1 a u) u)
            (fun v => spinMehlerKernel1D r p.2 v * spinV1 a v),
            integral_indicator (measurableSet_lt measurable_const continuous_abs.measurable)]
        have h1 := htail_1D r hr p.1 hp1
        have h2 := hUr_K2 r hr p.2 hp2
        change M * ((∫ u in {u : ℝ | R < |u|}, spinMehlerKernel1D r p.1 u * spinV1 a u) *
          spinUr a r p.2) ≤ _
        calc M * ((∫ u in {u : ℝ | R < |u|}, spinMehlerKernel1D r p.1 u * spinV1 a u) *
              spinUr a r p.2)
            ≤ M * ((Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
                Real.exp (2 * π * Real.sqrt a * (R / 2)) * I_tail) * C_U_box) := by
              have hnn : 0 ≤ ∫ u in {u : ℝ | R < |u|}, spinMehlerKernel1D r p.1 u * spinV1 a u :=
                setIntegral_nonneg (measurableSet_lt measurable_const continuous_abs.measurable)
                  fun u _ => mul_nonneg (spinMehlerKernel1D_nonneg hr1 p.1 u) (spinV1_nonneg ha u)
              have := mul_le_mul h1 h2 (spinUr_nonneg ha hr1 p.2) (by positivity)
              exact mul_le_mul_of_nonneg_left this hM
          _ = M * C_U_box * Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
                Real.exp (2 * π * Real.sqrt a * (R / 2)) * I_tail := by ring
      have hI2 : ∫ q : ℝ × ℝ, S2.indicator (fun q => M *
            ((spinMehlerKernel1D r p.1 q.1 * spinV1 a q.1) *
             (spinMehlerKernel1D r p.2 q.2 * spinV1 a q.2))) q ∂(volume.prod volume) ≤
          M * C_U_box * Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
            Real.exp (2 * π * Real.sqrt a * (R / 2)) * I_tail := by
        have hfac : S2.indicator (fun q : ℝ × ℝ => M *
            ((spinMehlerKernel1D r p.1 q.1 * spinV1 a q.1) *
             (spinMehlerKernel1D r p.2 q.2 * spinV1 a q.2))) =
            fun q => M * ((spinMehlerKernel1D r p.1 q.1 * spinV1 a q.1) *
              ({v : ℝ | R < |v|}.indicator (fun v => spinMehlerKernel1D r p.2 v * spinV1 a v) q.2)) := by
          ext q; by_cases hq : R < |q.2|
          · simp [S2, hq]
          · simp [S2, hq]
        rw [hfac, integral_const_mul, integral_prod_mul
            (fun u => spinMehlerKernel1D r p.1 u * spinV1 a u)
            (fun v => {v : ℝ | R < |v|}.indicator (fun v => spinMehlerKernel1D r p.2 v * spinV1 a v) v),
            integral_indicator (measurableSet_lt measurable_const continuous_abs.measurable)]
        have h1 := hUr_K2 r hr p.1 hp1
        have h2 := htail_1D r hr p.2 hp2
        change M * (spinUr a r p.1 *
          (∫ v in {v : ℝ | R < |v|}, spinMehlerKernel1D r p.2 v * spinV1 a v)) ≤ _
        calc M * (spinUr a r p.1 *
              (∫ v in {v : ℝ | R < |v|}, spinMehlerKernel1D r p.2 v * spinV1 a v))
            ≤ M * (C_U_box * (Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
                Real.exp (2 * π * Real.sqrt a * (R / 2)) * I_tail)) := by
              have hnn : 0 ≤ ∫ v in {v : ℝ | R < |v|}, spinMehlerKernel1D r p.2 v * spinV1 a v :=
                setIntegral_nonneg (measurableSet_lt measurable_const continuous_abs.measurable)
                  fun v _ => mul_nonneg (spinMehlerKernel1D_nonneg hr1 p.2 v) (spinV1_nonneg ha v)
              have := mul_le_mul h1 h2 hnn (by positivity)
              exact mul_le_mul_of_nonneg_left this hM
          _ = M * C_U_box * Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
                Real.exp (2 * π * Real.sqrt a * (R / 2)) * I_tail := by ring
      calc |∫ q : ℝ × ℝ, spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2 *
              vW a h_out q ∂(volume.prod volume)|
          ≤ ∫ q : ℝ × ℝ, |spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2 *
              vW a h_out q| ∂(volume.prod volume) := abs_integral_le_integral_abs
        _ ≤ ∫ q : ℝ × ℝ, (S1.indicator (fun q => M * ((spinMehlerKernel1D r p.1 q.1 * spinV1 a q.1) *
              (spinMehlerKernel1D r p.2 q.2 * spinV1 a q.2))) q +
            S2.indicator (fun q => M * ((spinMehlerKernel1D r p.1 q.1 * spinV1 a q.1) *
              (spinMehlerKernel1D r p.2 q.2 * spinV1 a q.2))) q) ∂(volume.prod volume) :=
            integral_mono hint_Wout.abs ((hdom_all.indicator hS1_m).add (hdom_all.indicator hS2_m)) hpt_ind
        _ = (∫ q : ℝ × ℝ, S1.indicator _ q ∂(volume.prod volume)) +
            (∫ q : ℝ × ℝ, S2.indicator _ q ∂(volume.prod volume)) :=
            integral_add (hdom_all.indicator hS1_m) (hdom_all.indicator hS2_m)
        _ ≤ 2 * M * C_U_box * Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
              Real.exp (2 * π * Real.sqrt a * (R / 2)) * I_tail := by linarith
    -- Bound `|F_{r, out}(p)|`
    have hFr_out : |vFr a r h_out p| ≤ 2 * M * C_U_box * spinCr a r := by
      have hL : ∀ x y : ℝ, |y| ≤ R / 2 → |vFrL a r h_out (x, y)| ≤ M * C_U_box * spinCr a r := by
        intro x y hy
        unfold vFrL
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
        have he1 : Real.exp (-π * x ^ 2) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg x])
        have hc1 : |Real.cos (2 * π * 8 * x * y)| ≤ 1 := Real.abs_cos_le_one _
        have h1 : Real.exp (-π * x ^ 2) * |Real.cos (2 * π * 8 * x * y)| ≤ 1 :=
          (mul_le_of_le_one_right (Real.exp_pos _).le hc1).trans he1
        have hα := (vAlpha_abs_le ha hr0 hr1 hM hh_out hbd_out y).trans
          (mul_le_mul_of_nonneg_left (hUr_K2 r hr y hy) (mul_nonneg hM (spinCr_pos hr0 hr1).le))
        calc Real.exp (-π * x ^ 2) * |Real.cos (2 * π * 8 * x * y)| * |vAlpha a r h_out y|
            ≤ 1 * (M * spinCr a r * C_U_box) := mul_le_mul h1 hα (abs_nonneg _) zero_le_one
          _ = M * C_U_box * spinCr a r := by ring
      unfold vFr
      have htri := abs_add_le (vFrL a r h_out p) (vFrL a r h_out p.swap)
      have h1 : |vFrL a r h_out p| ≤ M * C_U_box * spinCr a r := hL p.1 p.2 hp2
      have h2 : |vFrL a r h_out p.swap| ≤ M * C_U_box * spinCr a r := hL p.2 p.1 hp1
      linarith
    rw [abs_mul]
    have hdiff := abs_sub (spinMehlerOp r (vW a h_out) p) (vFr a r h_out p)
    have hsum : |spinMehlerOp r (vW a h_out) p - vFr a r h_out p| ≤
        2 * M * C_U_box * Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
          Real.exp (2 * π * Real.sqrt a * (R / 2)) * I_tail +
        2 * M * C_U_box * spinCr a r := by linarith
    exact mul_le_mul (hΦ_inf p) hsum (abs_nonneg _) (mul_nonneg hC₀_pos.le (spinM2_nonneg ha Φ))
  -- Integrate constant bound over `K2` of measure `R²`
  rw [Real.norm_eq_abs]
  have hvol_K2 : volume.real K2 = R ^ 2 := by
    rw [Measure.real_def, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
        ← ENNReal.ofReal_mul (by linarith), ENNReal.toReal_ofReal (by nlinarith)]
    ring
  have hle_int : |∫ p in K2, Φ p * (spinMehlerOp r (vW a h_out) p - vFr a r h_out p)| ≤
      volume.real K2 * ((C₀ * spinM2 a Φ) *
        (2 * M * C_U_box * Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
            Real.exp (2 * π * Real.sqrt a * (R / 2)) * I_tail +
         2 * M * C_U_box * spinCr a r)) := by
    have hmeas_f : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Φ p * (spinMehlerOp r (vW a h_out) p - vFr a r h_out p))
        (volume.restrict K2) := by
      have hAW_m : Measurable (spinMehlerOp r (vW a h_out)) := by
        unfold spinMehlerOp
        have hK_c : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
            spinMehlerKernel1D r z.1.1 z.2.1 * spinMehlerKernel1D r z.1.2 z.2.2) := by
          unfold spinMehlerKernel1D; fun_prop
        have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
        have hW_m : Measurable (vW a h_out) :=
          (hh_out.mul (hV.measurable.comp measurable_fst)).mul (hV.measurable.comp measurable_snd)
        exact (hK_c.measurable.mul (hW_m.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
      have hFr_m : Measurable (vFr a r h_out) := by
        have hFrL_m : Measurable (vFrL a r h_out) := by
          unfold vFrL
          have hc : Continuous (fun p : ℝ × ℝ =>
              Real.exp (-π * p.1 ^ 2) * Real.cos (2 * π * 8 * p.1 * p.2)) := by fun_prop
          exact hc.measurable.mul ((vAlpha_meas hh_out).comp measurable_snd)
        exact hFrL_m.add (hFrL_m.comp measurable_swap)
      exact (hΦ.cont.measurable.mul (hAW_m.sub hFr_m)).aestronglyMeasurable
    have hfin_K2 : volume K2 < ⊤ := by
      rw [Measure.volume_eq_prod, Measure.prod_prod]
      exact ENNReal.mul_lt_top measure_Icc_lt_top measure_Icc_lt_top
    have hint_c : IntegrableOn (fun _ : ℝ × ℝ => (C₀ * spinM2 a Φ) *
        (2 * M * C_U_box * Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
            Real.exp (2 * π * Real.sqrt a * (R / 2)) * I_tail +
         2 * M * C_U_box * spinCr a r)) K2 :=
      integrableOn_const (hs := hfin_K2.ne)
    have hint_f : IntegrableOn (fun p : ℝ × ℝ =>
        Φ p * (spinMehlerOp r (vW a h_out) p - vFr a r h_out p)) K2 := by
      refine hint_c.mono' hmeas_f ?_
      filter_upwards [ae_restrict_mem hK2_meas] with p hp
      rw [Real.norm_eq_abs]; exact hpt_K2 p hp
    calc |∫ p in K2, Φ p * (spinMehlerOp r (vW a h_out) p - vFr a r h_out p)|
        ≤ ∫ p in K2, |Φ p * (spinMehlerOp r (vW a h_out) p - vFr a r h_out p)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _ in K2, (C₀ * spinM2 a Φ) *
            (2 * M * C_U_box * Real.sqrt (2 / (1 - r)) * Real.exp (-π / (2 * (1 - r))) *
                Real.exp (2 * π * Real.sqrt a * (R / 2)) * I_tail +
             2 * M * C_U_box * spinCr a r) :=
          setIntegral_mono_on hint_f.abs hint_c hK2_meas hpt_K2
      _ = volume.real K2 * _ := by rw [setIntegral_const, smul_eq_mul]
  rw [hvol_K2] at hle_int
  exact hle_int.trans_eq (by dsimp [g_r]; ring)

/-- **`sd:V`** (Lemma SD-V: Mehler continuity on `\overline{\mathcal A}_{\rm spin}`),
proved unconditionally for all `a ≥ 2`. -/
theorem spinDV : SpinDV := by
  intro a ha
  obtain ⟨CD, hCD_pos, hCD⟩ := v_Dr_dom ha
  obtain ⟨CTh, hCTh_pos, hCTh⟩ := spinTestClass_Theta_integrable ha
  obtain ⟨CF, hCF_pos, hCF⟩ := vFr_fourier_pairing_bound ha
  obtain ⟨Cc, hCc_pos, hCc⟩ := spinCr_le_mul_mTau ha
  set C_unif : ℝ := CD * CTh + CF * (Cc * (π / 3))
  refine ⟨C_unif, by positivity, fun {h M} hM hh hd4 hbd {Φ} hΦ => ?_⟩
  -- Helper: uniform bound for any `D_4`-invariant bounded measurable `h'` (`|h'| ≤ M`)
  have hunif_aux : ∀ {h' : ℝ × ℝ → ℝ}, Measurable h' → IsD4Invariant h' → (∀ p, |h' p| ≤ M) →
      ∀ r ∈ Ico (1 / 2 : ℝ) 1,
        |∫ p : ℝ × ℝ, spinMehlerOp r Φ p * vW a h' p| ≤ C_unif * M * spinM2 a Φ := by
    intro h' hh' hd4' hbd' r hr
    rw [v_mehler_decomp ha hr hM hh' hd4' hbd' hΦ]
    have h1 : |∫ p : ℝ × ℝ, Φ p * (spinMehlerOp r (vW a h') p - vFr a r h' p)| ≤
        CD * CTh * M * spinM2 a Φ := by
      have hTh_int := (hCTh hΦ).1
      have hTh_le := (hCTh hΦ).2
      have hAW_m : Measurable (spinMehlerOp r (vW a h')) := by
        unfold spinMehlerOp
        have hK_c : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
            spinMehlerKernel1D r z.1.1 z.2.1 * spinMehlerKernel1D r z.1.2 z.2.2) := by
          unfold spinMehlerKernel1D; fun_prop
        have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
        have hW_m : Measurable (vW a h') :=
          (hh'.mul (hV.measurable.comp measurable_fst)).mul (hV.measurable.comp measurable_snd)
        exact (hK_c.measurable.mul (hW_m.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
      have hFr_m : Measurable (vFr a r h') := by
        have hFrL_m : Measurable (vFrL a r h') := by
          unfold vFrL
          have hc : Continuous (fun p : ℝ × ℝ =>
              Real.exp (-π * p.1 ^ 2) * Real.cos (2 * π * 8 * p.1 * p.2)) := by fun_prop
          exact hc.measurable.mul ((vAlpha_meas hh').comp measurable_snd)
        exact hFrL_m.add (hFrL_m.comp measurable_swap)
      have hint_Dr : Integrable (fun p : ℝ × ℝ =>
          Φ p * (spinMehlerOp r (vW a h') p - vFr a r h' p)) := by
        refine (hTh_int.const_mul (CD * M)).mono'
          (hΦ.cont.measurable.mul (hAW_m.sub hFr_m)).aestronglyMeasurable
          (Eventually.of_forall fun p => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        have := mul_le_mul_of_nonneg_left (hCD r hr hM hh' hd4' hbd' p) (abs_nonneg (Φ p))
        linarith
      calc |∫ p : ℝ × ℝ, Φ p * (spinMehlerOp r (vW a h') p - vFr a r h' p)|
          ≤ ∫ p : ℝ × ℝ, |Φ p * (spinMehlerOp r (vW a h') p - vFr a r h' p)| :=
            abs_integral_le_integral_abs
        _ ≤ ∫ p : ℝ × ℝ, (CD * M) * (|Φ p| * spinTheta a p) := by
            refine integral_mono hint_Dr.abs (hTh_int.const_mul _) fun p => ?_
            rw [abs_mul]
            have := mul_le_mul_of_nonneg_left (hCD r hr hM hh' hd4' hbd' p) (abs_nonneg (Φ p))
            linarith
        _ = (CD * M) * ∫ p : ℝ × ℝ, |Φ p| * spinTheta a p := integral_const_mul _ _
        _ ≤ (CD * M) * (CTh * spinM2 a Φ) := mul_le_mul_of_nonneg_left hTh_le (by positivity)
        _ = CD * CTh * M * spinM2 a Φ := by ring
    have h2 : |∫ p : ℝ × ℝ, Φ p * (𝓕 (spinToEuc (vFr a r h')) (vE2ToProd.symm p)).re| ≤
        CF * (Cc * (π / 3)) * M * spinM2 a Φ := by
      have hcr : spinCr a r ≤ Cc * (π / 3) :=
        (hCc r hr).trans (mul_le_mul_of_nonneg_left (mTau_le hr.1) hCc_pos.le)
      have hF := hCF r hr hM hh' hbd' hΦ
      have hM2 := spinM2_nonneg ha Φ
      calc |∫ p : ℝ × ℝ, Φ p * (𝓕 (spinToEuc (vFr a r h')) (vE2ToProd.symm p)).re|
          ≤ CF * M * spinCr a r * spinM2 a Φ := hF
        _ ≤ CF * M * (Cc * (π / 3)) * spinM2 a Φ := by gcongr
        _ = CF * (Cc * (π / 3)) * M * spinM2 a Φ := by ring
    have htri := abs_sub (∫ p : ℝ × ℝ, Φ p * (spinMehlerOp r (vW a h') p - vFr a r h' p))
      (∫ p : ℝ × ℝ, Φ p * (𝓕 (spinToEuc (vFr a r h')) (vE2ToProd.symm p)).re)
    dsimp [C_unif]; linarith
  refine ⟨fun r hr => by simpa only [vW, mul_assoc] using hunif_aux hh hd4 hbd r hr, ?_⟩
  -- Part 2: `Tendsto (fun r => ∫ (A_r Φ) W) (𝓝[<] 1) (𝓝 (∫ Φ W))`
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Since `|Φ| * Θ ∈ L¹`, choose `R ≥ 2` with `(CD + 1) * M * ∫_{K_{R/2}ᶜ} |Φ| Θ < ε / 2`
  have hTh_int := (hCTh hΦ).1
  have htail_tend : Tendsto (fun n : ℕ =>
      ∫ p in (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) ×ˢ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))ᶜ,
        |Φ p| * spinTheta a p) atTop (𝓝 0) := by
    let B : ℕ → Set (ℝ × ℝ) := fun n =>
      Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) ×ˢ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)
    have hB_meas : ∀ n, MeasurableSet (B n) := fun _ => measurableSet_Icc.prod measurableSet_Icc
    have hsub : (fun n : ℕ => ∫ p in (B n)ᶜ, |Φ p| * spinTheta a p) =
        fun n => ∫ p : ℝ × ℝ, (B n)ᶜ.indicator (fun p => |Φ p| * spinTheta a p) p := by
      ext n; exact (integral_indicator (hB_meas n).compl).symm
    rw [hsub]
    have h0 : (0 : ℝ) = ∫ _ : ℝ × ℝ, (0 : ℝ) := by simp
    rw [h0]
    refine tendsto_integral_of_dominated_convergence (bound := fun p => |Φ p| * spinTheta a p) ?_ hTh_int ?_ ?_
    · intro n; exact hTh_int.aestronglyMeasurable.indicator (hB_meas n).compl
    · intro n; filter_upwards with p
      rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (spinTheta_nonneg ha _)) _)]
      by_cases hp : p ∈ (B n)ᶜ
      · rw [Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem hp]; exact mul_nonneg (abs_nonneg _) (spinTheta_nonneg ha _)
    · filter_upwards with p
      refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil (max |p.1| |p.2|)) fun n hn => ?_
      have hpB : p ∈ B n := by
        have h1 : |p.1| ≤ (n : ℝ) + 1 := by
          have : |p.1| ≤ (Nat.ceil (max |p.1| |p.2|) : ℝ) :=
            (le_max_left _ _).trans (Nat.le_ceil _)
          have : (Nat.ceil (max |p.1| |p.2|) : ℝ) ≤ n := Nat.cast_le.mpr hn
          linarith
        have h2 : |p.2| ≤ (n : ℝ) + 1 := by
          have : |p.2| ≤ (Nat.ceil (max |p.1| |p.2|) : ℝ) :=
            (le_max_right _ _).trans (Nat.le_ceil _)
          have : (Nat.ceil (max |p.1| |p.2|) : ℝ) ≤ n := Nat.cast_le.mpr hn
          linarith
        exact ⟨abs_le.mp h1, abs_le.mp h2⟩
      exact Set.indicator_of_notMem (not_not.mpr hpB) _
  have hδ_pos : 0 < ε / (2 * ((CD + 1) * M + 1)) := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp (htail_tend.eventually (Metric.ball_mem_nhds 0 hδ_pos))
  set R : ℝ := 2 * ((N : ℝ) + 1)
  have hR_ge2 : 2 ≤ R := by dsimp [R]; linarith [Nat.cast_nonneg (α := ℝ) N]
  let K : Set (ℝ × ℝ) := Icc (-R) R ×ˢ Icc (-R) R
  let K2 : Set (ℝ × ℝ) := Icc (-(R / 2)) (R / 2) ×ˢ Icc (-(R / 2)) (R / 2)
  have hK_meas : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  have hK2_meas : MeasurableSet K2 := measurableSet_Icc.prod measurableSet_Icc
  have hK2_eq : K2 = Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1) ×ˢ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1) := by
    dsimp [K2, R]; congr 1 <;> congr 1 <;> ring
  have htail_small : (CD + 1) * M * (∫ p in K2ᶜ, |Φ p| * spinTheta a p) < ε / 2 := by
    have h1 := hN N le_rfl
    rw [Real.dist_eq, sub_zero, ← hK2_eq,
        abs_of_nonneg (setIntegral_nonneg hK2_meas.compl fun p _ => mul_nonneg (abs_nonneg _) (spinTheta_nonneg ha _))] at h1
    have h2 : (CD + 1) * M < (CD + 1) * M + 1 := by linarith
    have hnn : 0 ≤ ∫ p in K2ᶜ, |Φ p| * spinTheta a p :=
      setIntegral_nonneg hK2_meas.compl fun p _ => mul_nonneg (abs_nonneg _) (spinTheta_nonneg ha _)
    calc (CD + 1) * M * (∫ p in K2ᶜ, |Φ p| * spinTheta a p)
        ≤ ((CD + 1) * M + 1) * (∫ p in K2ᶜ, |Φ p| * spinTheta a p) :=
          mul_le_mul_of_nonneg_right h2.le hnn
      _ < ((CD + 1) * M + 1) * (ε / (2 * ((CD + 1) * M + 1))) :=
          mul_lt_mul_of_pos_left h1 (by positivity)
      _ = ε / 2 := by field_simp [show (CD + 1) * M + 1 ≠ 0 by positivity]
  -- Split `h = h_in + h_out` with `h_in = K.indicator h`, `h_out = Kᶜ.indicator h`
  let h_in : ℝ × ℝ → ℝ := K.indicator h
  let h_out : ℝ × ℝ → ℝ := Kᶜ.indicator h
  have hh_in : Measurable h_in := hh.indicator hK_meas
  have hh_out : Measurable h_out := hh.indicator hK_meas.compl
  have hK_d4 : ∀ p, (p ∈ K ↔ (-p.1, p.2) ∈ K) ∧ (p ∈ K ↔ (p.1, -p.2) ∈ K) ∧ (p ∈ K ↔ p.swap ∈ K) := by
    intro p
    refine ⟨?_, ?_, ?_⟩
    · simp only [K, mem_prod, mem_Icc]; constructor <;> rintro ⟨⟨h1, h2⟩, h3⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h3⟩
    · simp only [K, mem_prod, mem_Icc]; constructor <;> rintro ⟨h1, ⟨h2, h3⟩⟩ <;> exact ⟨h1, ⟨by linarith, by linarith⟩⟩
    · simp only [K, mem_prod, mem_Icc, Prod.swap]; tauto
  have hd4_out : IsD4Invariant h_out := by
    refine ⟨fun rL rR => ?_, fun rL rR => ?_, fun rL rR => ?_⟩
    · dsimp [h_out]; by_cases hp : (rL, rR) ∈ K
      · rw [Set.indicator_of_notMem (not_not.mpr ((hK_d4 (rL, rR)).1.mp hp)),
            Set.indicator_of_notMem (not_not.mpr hp)]
      · rw [Set.indicator_of_mem (mt (hK_d4 (rL, rR)).1.mpr hp),
            Set.indicator_of_mem hp, hd4.1]
    · dsimp [h_out]; by_cases hp : (rL, rR) ∈ K
      · rw [Set.indicator_of_notMem (not_not.mpr ((hK_d4 (rL, rR)).2.1.mp hp)),
            Set.indicator_of_notMem (not_not.mpr hp)]
      · rw [Set.indicator_of_mem (mt (hK_d4 (rL, rR)).2.1.mpr hp),
            Set.indicator_of_mem hp, hd4.2.1]
    · dsimp [h_out]; by_cases hp : (rL, rR) ∈ K
      · rw [Set.indicator_of_notMem (not_not.mpr ((hK_d4 (rL, rR)).2.2.mp hp)),
            Set.indicator_of_notMem (not_not.mpr hp)]
      · rw [Set.indicator_of_mem (mt (hK_d4 (rL, rR)).2.2.mpr hp),
            Set.indicator_of_mem hp, hd4.2.2]
  have hbd_out : ∀ p, |h_out p| ≤ M := fun p => by
    dsimp [h_out]
    by_cases hp : p ∈ Kᶜ
    · rw [Set.indicator_of_mem hp]; exact hbd p
    · rw [Set.indicator_of_notMem hp, abs_zero]; exact hM
  -- Three vanishing limits as `r ↑ 1`
  have ht1 := v_tendsto_box ha hM (by linarith : 0 ≤ R) hh hbd hΦ
  have ht2 := v_tendsto_inner_tail ha hM hR_ge2 hh hbd hΦ
  have ht3 : Tendsto (fun r => ∫ p : ℝ × ℝ,
      Φ p * (𝓕 (spinToEuc (vFr a r h_out)) (vE2ToProd.symm p)).re) (𝓝[<] 1) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by
      simpa using (spinCr_tendsto_zero a).const_mul (CF * M * spinM2 a Φ) |>.mul_const (1 : ℝ) :
        Tendsto (fun r => CF * M * spinM2 a Φ * spinCr a r * 1) (𝓝[<] 1) (𝓝 0))
    filter_upwards [Ico_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r hr
    rw [Real.norm_eq_abs]
    have hF := hCF r hr hM hh_out hbd_out hΦ
    linarith
  filter_upwards [Ico_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1),
    ht1.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 6)),
    ht2.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 6)),
    ht3.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 6))]
    with r hr h1 h2 h3
  rw [Real.dist_eq]
  have hW_split : ∀ p : ℝ × ℝ, vW a h p = K.indicator (vW a h) p + vW a h_out p := by
    intro p; unfold vW h_out
    by_cases hp : p ∈ K
    · rw [Set.indicator_of_mem hp, Set.indicator_of_notMem (not_not.mpr hp)]; ring
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_mem hp]; ring
  have hPhiW_int : Integrable (fun p : ℝ × ℝ => Φ p * vW a h p) := by
    refine (hΦ.int_M2.const_mul M).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
      have hW_m : Measurable (vW a h) :=
        (hh.mul (hV.measurable.comp measurable_fst)).mul (hV.measurable.comp measurable_snd)
      exact (hΦ.cont.measurable.mul hW_m).aestronglyMeasurable
    · unfold vW
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (spinV1_nonneg ha p.1), abs_of_nonneg (spinV1_nonneg ha p.2)]
      have hnn := mul_nonneg (abs_nonneg (Φ p)) (mul_nonneg (spinV1_nonneg ha p.1) (spinV1_nonneg ha p.2))
      have := mul_le_mul_of_nonneg_right (hbd p) hnn; linarith
  have hPhiW_in_int : Integrable (fun p : ℝ × ℝ => Φ p * K.indicator (vW a h) p) := by
    have heq : (fun p : ℝ × ℝ => Φ p * K.indicator (vW a h) p) =
        K.indicator (fun p => Φ p * vW a h p) := by
      ext p; by_cases hp : p ∈ K <;> simp [hp]
    rw [heq]; exact hPhiW_int.indicator hK_meas
  have hPhiW_out_int : Integrable (fun p : ℝ × ℝ => Φ p * vW a h_out p) := by
    have heq : (fun p : ℝ × ℝ => Φ p * vW a h_out p) =
        Kᶜ.indicator (fun p => Φ p * vW a h p) := by
      ext p; unfold vW h_out; by_cases hp : p ∈ K <;> simp [hp]
    rw [heq]; exact hPhiW_int.indicator hK_meas.compl
  have hArW_int : ∀ {h' : ℝ × ℝ → ℝ}, Measurable h' → (∀ p, |h' p| ≤ M) →
      Integrable (fun p : ℝ × ℝ => spinMehlerOp r Φ p * vW a h' p) := by
    intro h' hh' hbd'
    have hr0 : 0 ≤ r := by linarith [hr.1]
    have hr1 : r < 1 := hr.2
    obtain ⟨C₀, hC₀_pos, hC₀⟩ := spinTestClass_L1_le_M2 ha
    obtain ⟨hΦ_inf, _⟩ := hC₀ hΦ
    have hτ_pos := mTau_pos hr0 hr1
    have hdom_p : Integrable (fun p : ℝ × ℝ =>
        (2 * C₀ * spinM2 a Φ * M) *
          (Real.exp (-mTau r * p.1 ^ 2 + 2 * π * Real.sqrt a * |p.1|) *
           Real.exp (-mTau r * p.2 ^ 2 + 2 * π * Real.sqrt a * |p.2|))) := by
      rw [Measure.volume_eq_prod]
      exact ((integrable_exp_neg_quad_linear hτ_pos).mul_prod
        (integrable_exp_neg_quad_linear hτ_pos)).const_mul _
    refine hdom_p.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hAr_m : Measurable (spinMehlerOp r Φ) := by
        unfold spinMehlerOp
        have hK_c : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
            spinMehlerKernel1D r z.1.1 z.2.1 * spinMehlerKernel1D r z.1.2 z.2.2) := by
          unfold spinMehlerKernel1D; fun_prop
        exact (hK_c.measurable.mul (hΦ.cont.measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
      have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
      have hW_m : Measurable (vW a h') :=
        (hh'.mul (hV.measurable.comp measurable_fst)).mul (hV.measurable.comp measurable_snd)
      exact (hAr_m.mul hW_m).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      have hK_int : ∀ x : ℝ, Integrable (fun u : ℝ => spinMehlerKernel1D r x u) ∧
          (∫ u : ℝ, spinMehlerKernel1D r x u) =
            Real.sqrt (2 / (1 + r)) * Real.exp (-mTau r * x ^ 2) := fun x => by
        have h1 := integral_spinMehlerKernel1D_cosh hr0 hr1 (b := 0) le_rfl x
        simpa [Real.sqrt_zero, mul_zero, zero_mul, Real.cosh_zero] using h1
      have hprodK : Integrable (fun q : ℝ × ℝ =>
          (C₀ * spinM2 a Φ) * (spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2)) := by
        rw [Measure.volume_eq_prod]
        exact ((hK_int p.1).1.mul_prod (hK_int p.2).1).const_mul _
      have hint_q : Integrable (fun q : ℝ × ℝ =>
          spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2 * Φ q) := by
        refine hprodK.mono' ?_ (Eventually.of_forall fun q => ?_)
        · have hKc : Continuous (fun q : ℝ × ℝ =>
              spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2) := by
            unfold spinMehlerKernel1D; fun_prop
          exact (hKc.mul hΦ.cont).aestronglyMeasurable
        · rw [Real.norm_eq_abs, abs_mul,
              abs_of_nonneg (mul_nonneg (spinMehlerKernel1D_nonneg hr1 p.1 q.1)
                (spinMehlerKernel1D_nonneg hr1 p.2 q.2))]
          have := mul_le_mul_of_nonneg_left (hΦ_inf q)
            (mul_nonneg (spinMehlerKernel1D_nonneg hr1 p.1 q.1)
              (spinMehlerKernel1D_nonneg hr1 p.2 q.2))
          linarith
      have hAr_le : |spinMehlerOp r Φ p| ≤
          2 * C₀ * spinM2 a Φ * Real.exp (-mTau r * p.1 ^ 2) * Real.exp (-mTau r * p.2 ^ 2) := by
        calc |spinMehlerOp r Φ p|
            ≤ ∫ q : ℝ × ℝ, |spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2 * Φ q| :=
              abs_integral_le_integral_abs
          _ ≤ ∫ q : ℝ × ℝ, (C₀ * spinM2 a Φ) *
                (spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2) := by
              refine integral_mono hint_q.abs hprodK fun q => ?_
              rw [abs_mul, abs_of_nonneg (mul_nonneg (spinMehlerKernel1D_nonneg hr1 p.1 q.1)
                (spinMehlerKernel1D_nonneg hr1 p.2 q.2))]
              have := mul_le_mul_of_nonneg_left (hΦ_inf q)
                (mul_nonneg (spinMehlerKernel1D_nonneg hr1 p.1 q.1)
                  (spinMehlerKernel1D_nonneg hr1 p.2 q.2))
              linarith
          _ = (C₀ * spinM2 a Φ) * ((Real.sqrt (2 / (1 + r)) * Real.sqrt (2 / (1 + r))) *
                Real.exp (-mTau r * p.1 ^ 2) * Real.exp (-mTau r * p.2 ^ 2)) := by
              rw [integral_const_mul, Measure.volume_eq_prod, integral_prod_mul,
                  (hK_int p.1).2, (hK_int p.2).2]; ring
          _ ≤ (C₀ * spinM2 a Φ) * (2 * Real.exp (-mTau r * p.1 ^ 2) * Real.exp (-mTau r * p.2 ^ 2)) := by
              have hsq : Real.sqrt (2 / (1 + r)) * Real.sqrt (2 / (1 + r)) ≤ 2 := by
                rw [Real.mul_self_sqrt (by positivity), div_le_iff₀ (by linarith)]; linarith
              have hM2 := spinM2_nonneg ha Φ
              gcongr
          _ = 2 * C₀ * spinM2 a Φ * Real.exp (-mTau r * p.1 ^ 2) * Real.exp (-mTau r * p.2 ^ 2) := by ring
      have hW_bd : |vW a h' p| ≤ M * Real.exp (2 * π * Real.sqrt a * |p.1|) *
          Real.exp (2 * π * Real.sqrt a * |p.2|) := by
        unfold vW
        rw [abs_mul, abs_mul, abs_of_nonneg (spinV1_nonneg ha p.1),
            abs_of_nonneg (spinV1_nonneg ha p.2)]
        exact mul_le_mul (mul_le_mul (hbd' p) (spinV1_le_exp ha p.1) (spinV1_nonneg ha p.1) hM)
          (spinV1_le_exp ha p.2) (spinV1_nonneg ha p.2) (by positivity)
      calc |spinMehlerOp r Φ p| * |vW a h' p|
          ≤ (2 * C₀ * spinM2 a Φ * Real.exp (-mTau r * p.1 ^ 2) * Real.exp (-mTau r * p.2 ^ 2)) *
              (M * Real.exp (2 * π * Real.sqrt a * |p.1|) * Real.exp (2 * π * Real.sqrt a * |p.2|)) :=
            mul_le_mul hAr_le hW_bd (abs_nonneg _)
              (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (spinM2_nonneg ha Φ))
                (Real.exp_pos _).le) (Real.exp_pos _).le)
        _ = (2 * C₀ * spinM2 a Φ * M) *
              (Real.exp (-mTau r * p.1 ^ 2 + 2 * π * Real.sqrt a * |p.1|) *
               Real.exp (-mTau r * p.2 ^ 2 + 2 * π * Real.sqrt a * |p.2|)) := by
            rw [Real.exp_add (-mTau r * p.1 ^ 2), Real.exp_add (-mTau r * p.2 ^ 2)]; ring
  have hAr_in_int : Integrable (fun p : ℝ × ℝ => spinMehlerOp r Φ p * K.indicator (vW a h) p) := by
    have heq : (fun p : ℝ × ℝ => spinMehlerOp r Φ p * K.indicator (vW a h) p) =
        fun p => spinMehlerOp r Φ p * vW a h_in p := by
      ext p; unfold vW h_in; by_cases hp : p ∈ K <;> simp [hp]
    rw [heq]; exact hArW_int hh_in (fun p => by
      dsimp [h_in]
      by_cases hp : p ∈ K
      · rw [Set.indicator_of_mem hp]; exact hbd p
      · rw [Set.indicator_of_notMem hp, abs_zero]; exact hM)
  have hAr_out_int : Integrable (fun p : ℝ × ℝ => spinMehlerOp r Φ p * vW a h_out p) :=
    hArW_int hh_out hbd_out
  have hLHS_split : (∫ p : ℝ × ℝ, spinMehlerOp r Φ p * h p * spinV1 a p.1 * spinV1 a p.2) =
      (∫ p : ℝ × ℝ, spinMehlerOp r Φ p * K.indicator (vW a h) p) +
      (∫ p : ℝ × ℝ, spinMehlerOp r Φ p * vW a h_out p) := by
    have hpt : (fun p : ℝ × ℝ => spinMehlerOp r Φ p * h p * spinV1 a p.1 * spinV1 a p.2) =
        fun p => spinMehlerOp r Φ p * K.indicator (vW a h) p + spinMehlerOp r Φ p * vW a h_out p := by
      ext p
      have h1 : spinMehlerOp r Φ p * h p * spinV1 a p.1 * spinV1 a p.2 =
          spinMehlerOp r Φ p * vW a h p := by unfold vW; ring
      rw [h1, hW_split p, mul_add]
    rw [hpt, integral_add hAr_in_int hAr_out_int]
  have hRHS_split : (∫ p : ℝ × ℝ, Φ p * h p * spinV1 a p.1 * spinV1 a p.2) =
      (∫ p : ℝ × ℝ, Φ p * K.indicator (vW a h) p) +
      (∫ p : ℝ × ℝ, Φ p * vW a h_out p) := by
    have hpt : (fun p : ℝ × ℝ => Φ p * h p * spinV1 a p.1 * spinV1 a p.2) =
        fun p => Φ p * K.indicator (vW a h) p + Φ p * vW a h_out p := by
      ext p
      have h1 : Φ p * h p * spinV1 a p.1 * spinV1 a p.2 = Φ p * vW a h p := by unfold vW; ring
      rw [h1, hW_split p, mul_add]
    rw [hpt, integral_add hPhiW_in_int hPhiW_out_int]
  -- Decompose `∫ (A_r Φ) W_out` via `v_mehler_decomp` and split `D_{r, out}` into `K2` and `K2ᶜ`
  have hDr_out_int : Integrable (fun p : ℝ × ℝ =>
      Φ p * (spinMehlerOp r (vW a h_out) p - vFr a r h_out p)) := by
    have hAW_m : Measurable (spinMehlerOp r (vW a h_out)) := by
      unfold spinMehlerOp
      have hK_c : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
          spinMehlerKernel1D r z.1.1 z.2.1 * spinMehlerKernel1D r z.1.2 z.2.2) := by
        unfold spinMehlerKernel1D; fun_prop
      have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
      have hW_m : Measurable (vW a h_out) :=
        (hh_out.mul (hV.measurable.comp measurable_fst)).mul (hV.measurable.comp measurable_snd)
      exact (hK_c.measurable.mul (hW_m.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
    have hFr_m : Measurable (vFr a r h_out) := by
      have hFrL_m : Measurable (vFrL a r h_out) := by
        unfold vFrL
        have hc : Continuous (fun p : ℝ × ℝ =>
            Real.exp (-π * p.1 ^ 2) * Real.cos (2 * π * 8 * p.1 * p.2)) := by fun_prop
        exact hc.measurable.mul ((vAlpha_meas hh_out).comp measurable_snd)
      exact hFrL_m.add (hFrL_m.comp measurable_swap)
    refine (hTh_int.const_mul (CD * M)).mono'
      (hΦ.cont.measurable.mul (hAW_m.sub hFr_m)).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have := mul_le_mul_of_nonneg_left (hCD r hr hM hh_out hd4_out hbd_out p) (abs_nonneg (Φ p))
    linarith
  have hDr_split : (∫ p : ℝ × ℝ, Φ p * (spinMehlerOp r (vW a h_out) p - vFr a r h_out p)) =
      (∫ p in K2, Φ p * (spinMehlerOp r (vW a h_out) p - vFr a r h_out p)) +
      (∫ p in K2ᶜ, Φ p * (spinMehlerOp r (vW a h_out) p - vFr a r h_out p)) :=
    (integral_add_compl hK2_meas hDr_out_int).symm
  have hDr_outer : |∫ p in K2ᶜ, Φ p * (spinMehlerOp r (vW a h_out) p - vFr a r h_out p)| ≤
      CD * M * ∫ p in K2ᶜ, |Φ p| * spinTheta a p := by
    calc |∫ p in K2ᶜ, Φ p * (spinMehlerOp r (vW a h_out) p - vFr a r h_out p)|
        ≤ ∫ p in K2ᶜ, |Φ p * (spinMehlerOp r (vW a h_out) p - vFr a r h_out p)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ p in K2ᶜ, (CD * M) * (|Φ p| * spinTheta a p) := by
          refine setIntegral_mono_on hDr_out_int.abs.integrableOn (hTh_int.const_mul _).integrableOn
            hK2_meas.compl fun p _ => ?_
          rw [abs_mul]
          have := mul_le_mul_of_nonneg_left (hCD r hr hM hh_out hd4_out hbd_out p) (abs_nonneg (Φ p))
          linarith
      _ = CD * M * ∫ p in K2ᶜ, |Φ p| * spinTheta a p := integral_const_mul _ _
  have hW_outer : |∫ p : ℝ × ℝ, Φ p * vW a h_out p| ≤ M * ∫ p in K2ᶜ, |Φ p| * spinTheta a p := by
    have hsub_K : Kᶜ ⊆ K2ᶜ := compl_subset_compl.mpr fun p ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ =>
      ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    have heq_Kc : (∫ p : ℝ × ℝ, Φ p * vW a h_out p) = ∫ p in Kᶜ, Φ p * vW a h p := by
      have : (fun p : ℝ × ℝ => Φ p * vW a h_out p) = Kᶜ.indicator (fun p => Φ p * vW a h p) := by
        ext p; unfold vW h_out; by_cases hp : p ∈ K <;> simp [hp]
      rw [this, integral_indicator hK_meas.compl]
    rw [heq_Kc]
    calc |∫ p in Kᶜ, Φ p * vW a h p|
        ≤ ∫ p in Kᶜ, |Φ p * vW a h p| := abs_integral_le_integral_abs
      _ ≤ ∫ p in K2ᶜ, |Φ p * vW a h p| :=
          setIntegral_mono_set hPhiW_int.abs.integrableOn
            (Eventually.of_forall fun _ => abs_nonneg _) (Eventually.of_forall fun _ hp => hsub_K hp)
      _ ≤ ∫ p in K2ᶜ, M * (|Φ p| * spinTheta a p) := by
          refine setIntegral_mono_on hPhiW_int.abs.integrableOn (hTh_int.const_mul M).integrableOn
            hK2_meas.compl fun p _ => ?_
          unfold vW
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (spinV1_nonneg ha p.1),
              abs_of_nonneg (spinV1_nonneg ha p.2)]
          have hV_le_Th : spinV1 a p.1 * spinV1 a p.2 ≤ spinTheta a p := by
            unfold spinTheta; linarith [Real.exp_pos (-(π / 2) * (p.1 ^ 2 + p.2 ^ 2))]
          have h1 := hbd p
          have h2 := mul_le_mul_of_nonneg_left hV_le_Th (abs_nonneg (Φ p))
          have h3 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (abs_nonneg (Φ p)) (mul_nonneg (spinV1_nonneg ha p.1) (spinV1_nonneg ha p.2)))
          have h4 := mul_le_mul_of_nonneg_left h2 hM
          linarith
      _ = M * ∫ p in K2ᶜ, |Φ p| * spinTheta a p := integral_const_mul _ _
  -- Combine all bounds
  rw [hLHS_split, hRHS_split, v_mehler_decomp ha hr hM hh_out hd4_out hbd_out hΦ, hDr_split]
  rw [Real.dist_eq] at h1 h2 h3
  rw [sub_zero] at h2 h3
  have hcomb :
      |(∫ p, spinMehlerOp r Φ p * K.indicator (vW a h) p) +
        ((∫ p in K2, Φ p * (spinMehlerOp r (vW a h_out) p - vFr a r h_out p)) +
         (∫ p in K2ᶜ, Φ p * (spinMehlerOp r (vW a h_out) p - vFr a r h_out p)) -
         ∫ p, Φ p * (𝓕 (spinToEuc (vFr a r h_out)) (vE2ToProd.symm p)).re) -
       ((∫ p, Φ p * K.indicator (vW a h) p) + ∫ p, Φ p * vW a h_out p)| ≤
      |(∫ p, spinMehlerOp r Φ p * K.indicator (vW a h) p) -
        (∫ p, Φ p * K.indicator (vW a h) p)| +
      |∫ p in K2, Φ p * (spinMehlerOp r (vW a h_out) p - vFr a r h_out p)| +
      |∫ p in K2ᶜ, Φ p * (spinMehlerOp r (vW a h_out) p - vFr a r h_out p)| +
      |∫ p, Φ p * (𝓕 (spinToEuc (vFr a r h_out)) (vE2ToProd.symm p)).re| +
      |∫ p, Φ p * vW a h_out p| := by
    set A1 := (∫ p, spinMehlerOp r Φ p * K.indicator (vW a h) p) - (∫ p, Φ p * K.indicator (vW a h) p)
    set A2 := ∫ p in K2, Φ p * (spinMehlerOp r (vW a h_out) p - vFr a r h_out p)
    set A3 := ∫ p in K2ᶜ, Φ p * (spinMehlerOp r (vW a h_out) p - vFr a r h_out p)
    set A4 := ∫ p, Φ p * (𝓕 (spinToEuc (vFr a r h_out)) (vE2ToProd.symm p)).re
    set A5 := ∫ p, Φ p * vW a h_out p
    have hrearr :
        (∫ p, spinMehlerOp r Φ p * K.indicator (vW a h) p) + (A2 + A3 - A4) -
          ((∫ p, Φ p * K.indicator (vW a h) p) + A5) =
        A1 + A2 + A3 + (-A4) + (-A5) := by dsimp [A1]; ring
    rw [hrearr]
    have t1 := abs_add_le (A1 + A2 + A3 + (-A4)) (-A5)
    have t2 := abs_add_le (A1 + A2 + A3) (-A4)
    have t3 := abs_add_le (A1 + A2) A3
    have t4 := abs_add_le A1 A2
    rw [abs_neg] at t1
    rw [abs_neg] at t2
    linarith
  linarith

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinDV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinDV

end FormalResearch.ModularBootstrap.Spin
