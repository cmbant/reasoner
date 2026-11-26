module

public import FormalResearch.ModularBootstrap.Spin.SpinD2SD
public import FormalResearch.ModularBootstrap.Spin.SpinS2xS21

/-!
# Theorem SD (`sd:SD`), quadrant positivity, class hierarchy, and `SpinDW → SpinDSD`

Proves unconditionally for all `a ≥ 2`:
- `spinTestClass_L1_le_M2`: `∃ C > 0, ∀ Φ ∈ SpinTestClass a, ‖Φ‖_∞ ≤ ‖Φ‖_1 ≤ C * M_2[Φ]`
  (extending the `c ≥ 40` bound of `SpinS21` to every `a ≥ 2`, with an `a`-dependent constant);
- `spinLiftTToR_mem_SpinTestClassJ`: every `Φ ∈ SpinCertifiedT a` lifts to `SpinTestClassJ a`;
- `spinCertifiedThr_quadrant_nonempty`: the certified feasible set on the quadrant is nonempty;
- `spinThrInf_quadrant_hierarchy`:
  `0 < spinThrInf (SpinTestClass a) liouvilleCone a ≤ spinThrInf (SpinTestClassJ a) liouvilleCone a ≤ spinCertifiedThr a (spinConeB 0) ∅`.

And assembles the full `SpinDSD` from `SpinDW` (`sd:W`, weak duality for the full continuous
class on the quadrant):
- `spinDSD_of_spinDW : SpinDW → SpinDSD`.
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

/-! ### Section 1: Fixed-charge `L^1` / `L^∞` bound on `SpinTestClass a` for all `a ≥ 2` -/

private lemma spinV1_ge_four_pi_sq_mul_sq' {a : ℝ} (ha : 2 ≤ a) (r : ℝ) :
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

private lemma spinV1_ge_exp_away {a : ℝ} (ha : 2 ≤ a) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ r : ℝ, 1 / 4 ≤ |r| →
      c₁ * Real.exp (π * Real.sqrt a * |r|) ≤ spinV1 a r := by
  set A : ℝ := Real.sqrt a + Real.sqrt (a - 2)
  set B : ℝ := Real.sqrt a - Real.sqrt (a - 2)
  have hA_ge : Real.sqrt a ≤ A := by dsimp [A]; linarith [Real.sqrt_nonneg (a - 2)]
  have hB_pos : 0 < B := sub_pos.mpr (Real.sqrt_lt_sqrt (by linarith) (by linarith))
  set β : ℝ := π * Real.sqrt a / 2
  have hβ_pos : 0 < β := by dsimp [β]; positivity
  set c₁ : ℝ := min (4 * π ^ 2 * (1 / 4) ^ 2 * Real.exp (-2 * β)) ((1 / 2) * π * B)
  have hc₁_pos : 0 < c₁ := lt_min (by positivity) (by positivity)
  refine ⟨c₁, hc₁_pos, fun r hr => ?_⟩
  rcases le_total 1 |r| with hr1 | hr1
  · have habs : spinV1 a r = spinV1 a |r| := by
      rcases le_total 0 r with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, spinV1_even]
    rw [habs, spinV1_eq_mul_sinh a |r|]
    have hx_ge : 1 ≤ π * |r| * A := by
      have hsqa : 1 ≤ Real.sqrt a := by
        rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
      have hpi : 1 ≤ π := by linarith [Real.pi_gt_three]
      have h1 : 1 ≤ π * |r| := by nlinarith
      nlinarith
    have hsinh_ge : (1 / 4 : ℝ) * Real.exp (π * |r| * A) ≤ Real.sinh (π * |r| * A) := by
      rw [Real.sinh_eq]
      have hexp2 : (2 : ℝ) ≤ Real.exp (2 * (π * |r| * A)) := by
        have := Real.add_one_le_exp (2 * (π * |r| * A)); linarith
      have hneg : Real.exp (-(π * |r| * A)) ≤ (1 / 2 : ℝ) * Real.exp (π * |r| * A) := by
        have hmul : Real.exp (-(π * |r| * A)) * Real.exp (π * |r| * A) = 1 := by
          rw [← Real.exp_add]; simp
        have hsq : Real.exp (π * |r| * A) * Real.exp (π * |r| * A) = Real.exp (2 * (π * |r| * A)) := by
          rw [← Real.exp_add]; congr 1; ring
        have hpos := Real.exp_pos (π * |r| * A)
        nlinarith
      linarith
    have hsinhB : π * B ≤ Real.sinh (π * |r| * B) := by
      have h1 : π * |r| * B ≤ Real.sinh (π * |r| * B) := Real.self_le_sinh_iff.mpr (by positivity)
      have h2 : π * B ≤ π * |r| * B :=
        mul_le_mul_of_nonneg_right (by nlinarith [Real.pi_pos]) hB_pos.le
      linarith
    have hexp_mono : Real.exp (π * Real.sqrt a * |r|) ≤ Real.exp (π * |r| * A) := by
      refine Real.exp_le_exp.mpr ?_
      have : π * |r| * Real.sqrt a ≤ π * |r| * A := mul_le_mul_of_nonneg_left hA_ge (by positivity)
      linarith
    have hc₁_le : c₁ ≤ (1 / 2) * π * B := min_le_right _ _
    calc c₁ * Real.exp (π * Real.sqrt a * |r|)
        ≤ ((1 / 2) * π * B) * Real.exp (π * |r| * A) :=
          mul_le_mul hc₁_le hexp_mono (Real.exp_pos _).le (by positivity)
      _ = 2 * ((1 / 4 : ℝ) * Real.exp (π * |r| * A)) * (π * B) := by ring
      _ ≤ 2 * Real.sinh (π * |r| * A) * Real.sinh (π * |r| * B) := by gcongr
  · have h1 := spinV1_ge_four_pi_sq_mul_sq' ha r
    have hsq : (1 / 4 : ℝ) ^ 2 ≤ r ^ 2 := by
      rw [← sq_abs r]; exact pow_le_pow_left₀ (by norm_num) hr 2
    have h2 : 4 * π ^ 2 * (1 / 4 : ℝ) ^ 2 ≤ spinV1 a r := by nlinarith [Real.pi_pos]
    have hexp_le : Real.exp (π * Real.sqrt a * |r|) ≤ Real.exp (2 * β) := by
      refine Real.exp_le_exp.mpr ?_
      have : π * Real.sqrt a = 2 * β := by dsimp [β]; ring
      rw [this]; nlinarith
    have hc₁_le : c₁ ≤ 4 * π ^ 2 * (1 / 4) ^ 2 * Real.exp (-2 * β) := min_le_left _ _
    calc c₁ * Real.exp (π * Real.sqrt a * |r|)
        ≤ (4 * π ^ 2 * (1 / 4) ^ 2 * Real.exp (-2 * β)) * Real.exp (2 * β) :=
          mul_le_mul hc₁_le hexp_le (Real.exp_pos _).le (by positivity)
      _ = 4 * π ^ 2 * (1 / 4) ^ 2 * (Real.exp (-2 * β) * Real.exp (2 * β)) := by ring
      _ = 4 * π ^ 2 * (1 / 4) ^ 2 := by rw [← Real.exp_add]; simp
      _ ≤ spinV1 a r := h2

private lemma integrable_exp_neg_abs {β : ℝ} (hβ : 0 < β) :
    Integrable (fun y : ℝ => Real.exp (-β * |y|)) := by
  have hi1 : IntegrableOn (fun y : ℝ => Real.exp (-β * |y|)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hβ) 0).congr_fun
      (fun y hy => by rw [abs_of_pos hy]) measurableSet_Ioi
  have hi2 : IntegrableOn (fun y : ℝ => Real.exp (-β * |y|)) (Iic 0) :=
    (integrableOn_exp_mul_Iic hβ 0).congr_fun
      (fun y hy => by rw [abs_of_nonpos hy]; ring_nf) measurableSet_Iic
  rw [← integrableOn_univ, show (univ : Set ℝ) = Iic 0 ∪ Ioi 0 from by ext y; simp]
  exact hi2.union hi1

private lemma integral_exp_neg_abs {β : ℝ} (hβ : 0 < β) :
    ∫ y : ℝ, Real.exp (-β * |y|) = 2 / β := by
  have h1 : ∫ y in Ioi (0 : ℝ), Real.exp (-β * |y|) = 1 / β := by
    rw [setIntegral_congr_fun (g := fun y : ℝ => Real.exp (-β * y)) measurableSet_Ioi
          (fun y hy => by rw [abs_of_pos hy]),
        integral_exp_mul_Ioi (neg_lt_zero.mpr hβ) 0]
    simp [div_eq_inv_mul]
  have h2 : ∫ y in Iic (0 : ℝ), Real.exp (-β * |y|) = 1 / β := by
    rw [setIntegral_congr_fun (g := fun y : ℝ => Real.exp (β * y)) measurableSet_Iic
          (fun y hy => by rw [abs_of_nonpos hy]; congr 1; ring),
        integral_exp_mul_Iic hβ 0]
    simp [div_eq_inv_mul]
  rw [← integral_add_compl measurableSet_Iic (integrable_exp_neg_abs hβ),
      show (Iic (0 : ℝ))ᶜ = Ioi 0 from compl_Iic, h1, h2]
  ring

/-- Fixed-charge `L^1` / `L^∞` control on `SpinTestClass a` for every `a ≥ 2` (extending `SpinS21`
from `c ≥ 40` to all `a ≥ 2`, with an `a`-dependent constant). -/
theorem spinTestClass_L1_le_M2 {a : ℝ} (ha : 2 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ →
      (∀ p : ℝ × ℝ, |Φ p| ≤ C * spinM2 a Φ) ∧
      ∫ q : ℝ × ℝ, |Φ q| ≤ C * spinM2 a Φ := by
  obtain ⟨c₁, hc₁_pos, hc₁⟩ := spinV1_ge_exp_away ha
  set β : ℝ := π * Real.sqrt a / 2 with hβdef
  have hβ_pos : 0 < β := by rw [hβdef]; positivity
  set η : ℝ := β / 100 with hηdef
  have hη_pos : 0 < η := by rw [hηdef]; positivity
  let S_sq : Set (ℝ × ℝ) := Icc (-(1 / 4 : ℝ)) (1 / 4) ×ˢ Icc (-(1 / 4 : ℝ)) (1 / 4)
  let S₁ : Set (ℝ × ℝ) := {p : ℝ × ℝ | 1 / 4 ≤ |p.2| ∧ |p.1| ≤ η * Real.exp (-β * |p.2|)}
  let S₂ : Set (ℝ × ℝ) := Prod.swap ⁻¹' S₁
  let E : Set (ℝ × ℝ) := S_sq ∪ S₁ ∪ S₂
  have hS₁_meas : MeasurableSet S₁ :=
    (measurableSet_le measurable_const (continuous_abs.comp continuous_snd).measurable).inter
      (measurableSet_le (continuous_abs.comp continuous_fst).measurable
        (measurable_const.mul (Real.continuous_exp.comp
          (continuous_const.mul (continuous_abs.comp continuous_snd))).measurable))
  have hS_sq_meas : MeasurableSet S_sq := measurableSet_Icc.prod measurableSet_Icc
  have hE_meas : MeasurableSet E := (hS_sq_meas.union hS₁_meas).union (measurable_swap hS₁_meas)
  have hvol_sq : volume S_sq = ENNReal.ofReal (1 / 4 : ℝ) := by
    dsimp only [S_sq]
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hvol_S₁ : volume S₁ ≤ ENNReal.ofReal (1 / 25 : ℝ) := by
    have hsw : volume S₁ = volume (Prod.swap ⁻¹' S₁) := by
      have hmp : Measure.map Prod.swap (volume : Measure (ℝ × ℝ)) = volume := by
        rw [Measure.volume_eq_prod, Measure.prod_swap]
      rw [← Measure.map_apply measurable_swap hS₁_meas, hmp]
    rw [hsw, Measure.volume_eq_prod, Measure.prod_apply (measurable_swap hS₁_meas)]
    have hslice : ∀ y : ℝ, volume (Prod.mk y ⁻¹' (Prod.swap ⁻¹' S₁)) ≤
        ENNReal.ofReal (2 * η * Real.exp (-β * |y|)) := by
      intro y
      have hsub : Prod.mk y ⁻¹' (Prod.swap ⁻¹' S₁) ⊆
          Icc (-(η * Real.exp (-β * |y|))) (η * Real.exp (-β * |y|)) := by
        intro x hx; exact abs_le.mp hx.2
      refine (measure_mono hsub).trans ?_
      rw [Real.volume_Icc]
      refine ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
    calc ∫⁻ y : ℝ, volume (Prod.mk y ⁻¹' (Prod.swap ⁻¹' S₁))
        ≤ ∫⁻ y : ℝ, ENNReal.ofReal (2 * η * Real.exp (-β * |y|)) := lintegral_mono hslice
      _ = ENNReal.ofReal (∫ y : ℝ, 2 * η * Real.exp (-β * |y|)) :=
          (ofReal_integral_eq_lintegral_ofReal ((integrable_exp_neg_abs hβ_pos).const_mul (2 * η))
            (Eventually.of_forall fun y => by positivity)).symm
      _ = ENNReal.ofReal (1 / 25 : ℝ) := by
          rw [integral_const_mul, integral_exp_neg_abs hβ_pos, hηdef]
          congr 1; field_simp [hβ_pos.ne']; ring
  have hvol_S₂ : volume S₂ ≤ ENNReal.ofReal (1 / 25 : ℝ) := by
    have hmp : Measure.map Prod.swap (volume : Measure (ℝ × ℝ)) = volume := by
      rw [Measure.volume_eq_prod, Measure.prod_swap]
    have heq : volume S₂ = volume S₁ := by
      dsimp only [S₂]
      rw [← Measure.map_apply measurable_swap hS₁_meas, hmp]
    rw [heq]; exact hvol_S₁
  have hvol_E : volume E ≤ ENNReal.ofReal (33 / 100 : ℝ) := by
    calc volume E ≤ volume (S_sq ∪ S₁) + volume S₂ := measure_union_le _ _
      _ ≤ volume S_sq + volume S₁ + volume S₂ := add_le_add (measure_union_le _ _) le_rfl
      _ ≤ ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 25) + ENNReal.ofReal (1 / 25) :=
          add_le_add (add_le_add hvol_sq.le hvol_S₁) hvol_S₂
      _ = ENNReal.ofReal (33 / 100 : ℝ) := by
          rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
              ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          congr 1; norm_num
  have hvol_E_real : volume.real E ≤ 33 / 100 := by
    rw [Measure.real_def]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol_E).trans_eq
      (ENNReal.toReal_ofReal (by norm_num))
  set ca : ℝ := min ((4 * π ^ 2 * (1 / 4) ^ 2) ^ 2) (4 * π ^ 2 * η ^ 2 * c₁) with hca_def
  have hca_pos : 0 < ca := lt_min (by positivity) (by positivity)
  have hoffE : ∀ p ∈ Eᶜ, ca ≤ spinV1 a p.1 * spinV1 a p.2 := by
    intro p hp
    simp only [E, mem_compl_iff, mem_union, not_or] at hp
    obtain ⟨⟨hnot_sq, hnot_s1⟩, hnot_s2⟩ := hp
    by_cases h1 : 1 / 4 ≤ |p.1|
    · by_cases h2 : 1 / 4 ≤ |p.2|
      · have hv1 : 4 * π ^ 2 * (1 / 4) ^ 2 ≤ spinV1 a p.1 := by
          have := spinV1_ge_four_pi_sq_mul_sq' ha p.1
          have hsq : (1 / 4 : ℝ) ^ 2 ≤ p.1 ^ 2 := by rw [← sq_abs p.1]; exact pow_le_pow_left₀ (by norm_num) h1 2
          nlinarith [Real.pi_pos]
        have hv2 : 4 * π ^ 2 * (1 / 4) ^ 2 ≤ spinV1 a p.2 := by
          have := spinV1_ge_four_pi_sq_mul_sq' ha p.2
          have hsq : (1 / 4 : ℝ) ^ 2 ≤ p.2 ^ 2 := by rw [← sq_abs p.2]; exact pow_le_pow_left₀ (by norm_num) h2 2
          nlinarith [Real.pi_pos]
        calc ca ≤ (4 * π ^ 2 * (1 / 4) ^ 2) ^ 2 := min_le_left _ _
          _ = (4 * π ^ 2 * (1 / 4) ^ 2) * (4 * π ^ 2 * (1 / 4) ^ 2) := sq _
          _ ≤ spinV1 a p.1 * spinV1 a p.2 := mul_le_mul hv1 hv2 (by positivity) (spinV1_nonneg ha p.1)
      · have hgt : η * Real.exp (-β * |p.1|) < |p.2| := by
          by_contra hle; push Not at hle
          exact hnot_s2 ⟨h1, hle⟩
        have hv2 : 4 * π ^ 2 * η ^ 2 * Real.exp (-2 * β * |p.1|) ≤ spinV1 a p.2 := by
          have hsq : (η * Real.exp (-β * |p.1|)) ^ 2 ≤ p.2 ^ 2 := by
            rw [← sq_abs p.2]; exact pow_le_pow_left₀ (by positivity) hgt.le 2
          have hexp : (η * Real.exp (-β * |p.1|)) ^ 2 = η ^ 2 * Real.exp (-2 * β * |p.1|) := by
            rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring
          have := spinV1_ge_four_pi_sq_mul_sq' ha p.2
          rw [hexp] at hsq; nlinarith [Real.pi_pos]
        have hv1 : c₁ * Real.exp (2 * β * |p.1|) ≤ spinV1 a p.1 := by
          have heq : 2 * β * |p.1| = π * Real.sqrt a * |p.1| := by rw [hβdef]; ring
          rw [heq]; exact hc₁ p.1 h1
        calc ca ≤ 4 * π ^ 2 * η ^ 2 * c₁ := min_le_right _ _
          _ = (c₁ * Real.exp (2 * β * |p.1|)) * (4 * π ^ 2 * η ^ 2 * Real.exp (-2 * β * |p.1|)) := by
              have : Real.exp (2 * β * |p.1|) * Real.exp (-2 * β * |p.1|) = 1 := by
                rw [← Real.exp_add]; simp
              linear_combination 4 * π ^ 2 * η ^ 2 * c₁ * this.symm
          _ ≤ spinV1 a p.1 * spinV1 a p.2 := mul_le_mul hv1 hv2 (by positivity) (spinV1_nonneg ha p.1)
    · have h2 : 1 / 4 ≤ |p.2| := by
        by_contra hlt; push Not at hlt h1
        exact hnot_sq ⟨abs_le.mp h1.le, abs_le.mp hlt.le⟩
      have hgt : η * Real.exp (-β * |p.2|) < |p.1| := by
        by_contra hle; push Not at hle
        exact hnot_s1 ⟨h2, hle⟩
      have hv1 : 4 * π ^ 2 * η ^ 2 * Real.exp (-2 * β * |p.2|) ≤ spinV1 a p.1 := by
        have hsq : (η * Real.exp (-β * |p.2|)) ^ 2 ≤ p.1 ^ 2 := by
          rw [← sq_abs p.1]; exact pow_le_pow_left₀ (by positivity) hgt.le 2
        have hexp : (η * Real.exp (-β * |p.2|)) ^ 2 = η ^ 2 * Real.exp (-2 * β * |p.2|) := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring
        have := spinV1_ge_four_pi_sq_mul_sq' ha p.1
        rw [hexp] at hsq; nlinarith [Real.pi_pos]
      have hv2 : c₁ * Real.exp (2 * β * |p.2|) ≤ spinV1 a p.2 := by
        have heq : 2 * β * |p.2| = π * Real.sqrt a * |p.2| := by rw [hβdef]; ring
        rw [heq]; exact hc₁ p.2 h2
      calc ca ≤ 4 * π ^ 2 * η ^ 2 * c₁ := min_le_right _ _
        _ = (4 * π ^ 2 * η ^ 2 * Real.exp (-2 * β * |p.2|)) * (c₁ * Real.exp (2 * β * |p.2|)) := by
            have : Real.exp (-2 * β * |p.2|) * Real.exp (2 * β * |p.2|) = 1 := by
              rw [← Real.exp_add]; simp
            linear_combination 4 * π ^ 2 * η ^ 2 * c₁ * this.symm
        _ ≤ spinV1 a p.1 * spinV1 a p.2 := mul_le_mul hv1 hv2 (by positivity) (spinV1_nonneg ha p.1)
  refine ⟨100 / (67 * ca), by positivity, fun {Φ} hΦ => ?_⟩
  have hL1_le : ∫ q : ℝ × ℝ, |Φ q| ≤ (100 / (67 * ca)) * spinM2 a Φ := by
    set I₁ : ℝ := ∫ q : ℝ × ℝ, |Φ q|
    have hI₁_nn : 0 ≤ I₁ := integral_nonneg fun _ => abs_nonneg _
    have hsplit : I₁ = (∫ q in E, |Φ q|) + ∫ q in Eᶜ, |Φ q| :=
      (integral_add_compl hE_meas hΦ.int.abs).symm
    have hE_le : ∫ q in E, |Φ q| ≤ (33 / 100 : ℝ) * I₁ := by
      have hfinE : volume E < ∞ := lt_of_le_of_lt hvol_E ENNReal.ofReal_lt_top
      have h1 : ∫ q in E, |Φ q| ≤ ∫ _ in E, I₁ :=
        setIntegral_mono_on hΦ.int.abs.integrableOn (integrableOn_const hfinE.ne) hE_meas
          fun p _ => spinTestClass_abs_le_integral_abs hΦ p
      rw [setIntegral_const, smul_eq_mul] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right hvol_E_real hI₁_nn)
    have hEc_le : ca * ∫ q in Eᶜ, |Φ q| ≤ spinM2 a Φ := by
      rw [← integral_const_mul]
      have h1 : ∫ q in Eᶜ, ca * |Φ q| ≤ ∫ q in Eᶜ, |Φ q| * spinV1 a q.1 * spinV1 a q.2 := by
        refine setIntegral_mono_on (hΦ.int.abs.const_mul ca).integrableOn hΦ.int_M2.integrableOn
          hE_meas.compl fun p hp => ?_
        have h := hoffE p hp
        calc ca * |Φ p| ≤ (spinV1 a p.1 * spinV1 a p.2) * |Φ p| :=
              mul_le_mul_of_nonneg_right h (abs_nonneg _)
          _ = |Φ p| * spinV1 a p.1 * spinV1 a p.2 := by ring
      have h2 : ∫ q in Eᶜ, |Φ q| * spinV1 a q.1 * spinV1 a q.2 ≤ spinM2 a Φ :=
        setIntegral_le_integral hΦ.int_M2 (Eventually.of_forall fun p =>
          mul_nonneg (mul_nonneg (abs_nonneg _) (spinV1_nonneg ha p.1)) (spinV1_nonneg ha p.2))
      exact h1.trans h2
    have h67 : (67 / 100 : ℝ) * I₁ ≤ ∫ q in Eᶜ, |Φ q| := by linarith
    have hmul : (67 / 100 : ℝ) * ca * I₁ ≤ spinM2 a Φ := by nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  exact ⟨fun p => (spinTestClass_abs_le_integral_abs hΦ p).trans hL1_le, hL1_le⟩

/-! ### Section 2: `SpinCertifiedT` lifts to `SpinTestClassJ` via 1D Laguerre Fourier eigenfunctions -/

private lemma spinD2_fourier_gaussian_1D {β : ℝ} (hβ : 0 < β) (ξ : ℝ) :
    𝓕 (fun r : ℝ => (Real.exp (-π * β * r ^ 2) : ℂ)) ξ =
      ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Real.exp (-π * β⁻¹ * ξ ^ 2) : ℂ) := by
  have hb : 0 < ((π * β : ℝ) : ℂ).re := by simp [Real.pi_pos, hβ]
  have hfn : (fun r : ℝ => (Real.exp (-π * β * r ^ 2) : ℂ)) =
      fun r => Complex.exp (-((π * β : ℝ) : ℂ) * (‖r‖ : ℂ) ^ 2) := by
    ext r
    rw [Complex.ofReal_exp]
    have hnr : (‖r‖ : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) := by
      rw [Real.norm_eq_abs, ← Complex.ofReal_pow, sq_abs]
    rw [hnr]; congr 1; push_cast; ring
  rw [hfn, fourier_gaussian_innerProductSpace hb ξ]
  have hdim : (Module.finrank ℝ ℝ / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by simp
  rw [hdim]
  have hpi : ((π : ℝ) : ℂ) / ((π * β : ℝ) : ℂ) = ((β⁻¹ : ℝ) : ℂ) := by
    have hp : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hbc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
    push_cast; field_simp
  have hnrξ : (‖ξ‖ : ℂ) ^ 2 = ((ξ ^ 2 : ℝ) : ℂ) := by
    rw [Real.norm_eq_abs, ← Complex.ofReal_pow, sq_abs]
  rw [hpi, ← Complex.ofReal_cpow (by positivity : 0 ≤ β⁻¹), Real.inv_rpow hβ.le,
    ← Real.rpow_neg hβ.le, Complex.ofReal_exp, hnrξ]
  congr 2; push_cast
  have hpi_ne : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hb_ne : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
  field_simp

private lemma real_power_series_coeff_zero {c : ℕ → ℝ} {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hbd : ∀ k, |c k| ≤ M * r⁻¹ ^ k)
    (hzero : ∀ z : ℝ, |z| < r → HasSum (fun k : ℕ => c k * z ^ k) 0) :
    ∀ k : ℕ, c k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    -- Evaluate at `z ∈ (0, r/2)` and let `z → 0`
    have htail_le : ∀ z : ℝ, 0 < z → z < r / 2 →
        |c k| ≤ M * r⁻¹ ^ k * (2 * z / r) := by
      intro z hz0 hzr
      have hz_lt : |z| < r := by rw [abs_of_pos hz0]; linarith
      have hsum0 := hzero z hz_lt
      have hsplit : ∑' m : ℕ, c m * z ^ m =
          (∑ m ∈ Finset.range k, c m * z ^ m) +
            c k * z ^ k + ∑' m : ℕ, c (m + (k + 1)) * z ^ (m + (k + 1)) := by
        have hs : Summable (fun m : ℕ => c m * z ^ m) := hsum0.summable
        rw [← hs.sum_add_tsum_nat_add (k + 1), Finset.sum_range_succ, add_assoc]
      have hprefix : ∑ m ∈ Finset.range k, c m * z ^ m = 0 :=
        Finset.sum_eq_zero fun m hm => by rw [ih m (Finset.mem_range.mp hm), zero_mul]
      have htsum0 : ∑' m : ℕ, c m * z ^ m = 0 := hsum0.tsum_eq
      rw [htsum0, hprefix, zero_add] at hsplit
      have hck_eq : c k * z ^ k = -(∑' m : ℕ, c (m + (k + 1)) * z ^ (m + (k + 1))) := by linarith
      have hq_lt : z / r < 1 / 2 := (div_lt_iff₀ hr).mpr (by linarith)
      have hq_nn : 0 ≤ z / r := div_nonneg hz0.le hr.le
      have hgeom : Summable (fun m : ℕ => (M * r⁻¹ ^ (k + 1) * z ^ (k + 1)) * (z / r) ^ m) :=
        (summable_geometric_of_lt_one hq_nn (hq_lt.trans (by norm_num))).mul_left _
      have hterm_le : ∀ m : ℕ, ‖c (m + (k + 1)) * z ^ (m + (k + 1))‖ ≤
          (M * r⁻¹ ^ (k + 1) * z ^ (k + 1)) * (z / r) ^ m := by
        intro m
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hz0]
        have hb := hbd (m + (k + 1))
        calc |c (m + (k + 1))| * z ^ (m + (k + 1))
            ≤ (M * r⁻¹ ^ (m + (k + 1))) * z ^ (m + (k + 1)) :=
              mul_le_mul_of_nonneg_right hb (pow_nonneg hz0.le _)
          _ = (M * r⁻¹ ^ (k + 1) * z ^ (k + 1)) * (z / r) ^ m := by
              rw [pow_add, pow_add, div_eq_mul_inv, mul_pow]; ring
      have hnorm_le : |c k * z ^ k| ≤
          ∑' m : ℕ, (M * r⁻¹ ^ (k + 1) * z ^ (k + 1)) * (z / r) ^ m := by
        rw [hck_eq, abs_neg]
        have hsum_norm : Summable (fun m : ℕ => ‖c (m + (k + 1)) * z ^ (m + (k + 1))‖) :=
          Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le hgeom
        exact (norm_tsum_le_tsum_norm hsum_norm).trans
          (Summable.tsum_le_tsum hterm_le hsum_norm hgeom)
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq_nn (hq_lt.trans (by norm_num))] at hnorm_le
      have hdenom : 1 / 2 ≤ 1 - z / r := by linarith
      have hinv_le : (1 - z / r)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      have hck_abs : |c k| * z ^ k ≤ (M * r⁻¹ ^ (k + 1) * z ^ (k + 1)) * 2 := by
        rw [abs_mul, abs_pow, abs_of_pos hz0] at hnorm_le
        exact hnorm_le.trans (mul_le_mul_of_nonneg_left hinv_le (by positivity))
      have hzpow_pos : 0 < z ^ k := pow_pos hz0 k
      have hcancel : |c k| * z ^ k ≤ (M * r⁻¹ ^ k * (2 * z / r)) * z ^ k := by
        refine hck_abs.trans_eq ?_
        rw [pow_succ, pow_succ, div_eq_mul_inv]; ring
      exact le_of_mul_le_mul_right hcancel hzpow_pos
    by_contra hne
    have hpos : 0 < |c k| := abs_pos.mpr hne
    have hMpos : 0 < M * r⁻¹ ^ k + 1 := by positivity
    set z : ℝ := min (r / 4) (|c k| * r / (4 * (M * r⁻¹ ^ k + 1)))
    have hz0 : 0 < z := lt_min (by linarith) (by positivity)
    have hzr : z < r / 2 := (min_le_left _ _).trans_lt (by linarith)
    have hle := htail_le z hz0 hzr
    have hz2 : z ≤ |c k| * r / (4 * (M * r⁻¹ ^ k + 1)) := min_le_right _ _
    have hbound2 : M * r⁻¹ ^ k * (2 * z / r) ≤ |c k| / 2 := by
      have h1 : 2 * z / r ≤ |c k| / (2 * (M * r⁻¹ ^ k + 1)) := by
        rw [div_le_iff₀ hr]
        have h2 := mul_le_mul_of_nonneg_left hz2 (by norm_num : (0 : ℝ) ≤ 2)
        have : 2 * (|c k| * r / (4 * (M * r⁻¹ ^ k + 1))) = |c k| / (2 * (M * r⁻¹ ^ k + 1)) * r := by
          field_simp [hMpos.ne']; ring
        linarith
      have h3 : M * r⁻¹ ^ k * (|c k| / (2 * (M * r⁻¹ ^ k + 1))) ≤ |c k| / 2 := by
        have hratio : M * r⁻¹ ^ k / (M * r⁻¹ ^ k + 1) ≤ 1 :=
          (div_le_one hMpos).mpr (by linarith)
        calc M * r⁻¹ ^ k * (|c k| / (2 * (M * r⁻¹ ^ k + 1)))
            = (M * r⁻¹ ^ k / (M * r⁻¹ ^ k + 1)) * (|c k| / 2) := by
                field_simp [hMpos.ne']
          _ ≤ 1 * (|c k| / 2) := mul_le_mul_of_nonneg_right hratio (by positivity)
          _ = |c k| / 2 := one_mul _
      exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans h3
    linarith

/-- 1D Fourier eigenfunction identity for `ψ_k(r²/2) = L_k^{(-1/2)}(2π r²) e^{-π r²}`:
`𝓕(r ↦ ψ_k(r²/2))(ξ) = (-1)^k ψ_k(ξ²/2)`. -/
private lemma spin_fourier_lagPsi_1D (k : ℕ) (ξ : ℝ) :
    𝓕 (fun r : ℝ => (lagPsi (1 / 2) k (r ^ 2 / 2) : ℂ)) ξ =
      ((-1 : ℝ) ^ k : ℂ) * (lagPsi (1 / 2) k (ξ ^ 2 / 2) : ℂ) := by
  have hbound : ∀ m : ℕ, ∀ r : ℝ,
      |lagPsi (1 / 2) m (r ^ 2 / 2)| ≤
        (1 - (1 / 2 : ℝ)) ^ (-(1 / 2 : ℝ)) * (1 / 2 : ℝ)⁻¹ ^ m *
          Real.exp (-π / 3 * r ^ 2) := by
    intro m r
    have h := abs_lagPsi_le (w := 1 / 2) (by norm_num) (θ := 1 / 2) (by norm_num) (by norm_num)
      (t := r ^ 2 / 2) (by positivity) m
    refine h.trans_eq ?_
    congr 2; ring
  have hgauss_int : Integrable (fun r : ℝ => Real.exp (-π / 3 * r ^ 2)) := by
    have h := integrable_exp_neg_mul_sq (b := π / 3) (by positivity)
    exact h.congr (Eventually.of_forall fun r => by simp [neg_div, neg_mul])
  set A : ℝ := (1 - (1 / 2 : ℝ)) ^ (-(1 / 2 : ℝ))
  have hA_pos : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  set C_coeff : ℝ := A * (∫ r : ℝ, Real.exp (-π / 3 * r ^ 2)) + A * Real.exp (-π / 3 * ξ ^ 2)
  have hC_nn : 0 ≤ C_coeff := add_nonneg
    (mul_nonneg hA_pos.le (integral_nonneg fun _ => (Real.exp_pos _).le))
    (mul_nonneg hA_pos.le (Real.exp_pos _).le)
  have hcoeff_bd : ∀ m : ℕ,
      ‖𝓕 (fun r : ℝ => (lagPsi (1 / 2) m (r ^ 2 / 2) : ℂ)) ξ -
        ((-1 : ℝ) ^ m : ℂ) * (lagPsi (1 / 2) m (ξ ^ 2 / 2) : ℂ)‖ ≤
        C_coeff * (1 / 4 : ℝ)⁻¹ ^ m := by
    intro m
    have h1 : ‖𝓕 (fun r : ℝ => (lagPsi (1 / 2) m (r ^ 2 / 2) : ℂ)) ξ‖ ≤
        (A * (∫ r : ℝ, Real.exp (-π / 3 * r ^ 2))) * (1 / 2 : ℝ)⁻¹ ^ m := by
      rw [Real.fourier_eq]
      calc ‖∫ r : ℝ, 𝐞 (-⟪r, ξ⟫) • (lagPsi (1 / 2) m (r ^ 2 / 2) : ℂ)‖
          ≤ ∫ r : ℝ, ‖𝐞 (-⟪r, ξ⟫) • (lagPsi (1 / 2) m (r ^ 2 / 2) : ℂ)‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ r : ℝ, (A * (1 / 2 : ℝ)⁻¹ ^ m) * Real.exp (-π / 3 * r ^ 2) := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              (hgauss_int.const_mul _) (Eventually.of_forall fun r => ?_)
            dsimp only
            rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs]
            exact hbound m r
        _ = (A * (∫ r : ℝ, Real.exp (-π / 3 * r ^ 2))) * (1 / 2 : ℝ)⁻¹ ^ m := by
            rw [integral_const_mul]; ring
    have h2 : ‖((-1 : ℝ) ^ m : ℂ) * (lagPsi (1 / 2) m (ξ ^ 2 / 2) : ℂ)‖ ≤
        (A * Real.exp (-π / 3 * ξ ^ 2)) * (1 / 2 : ℝ)⁻¹ ^ m := by
      rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_neg, abs_one, one_pow, one_mul]
      exact (hbound m ξ).trans_eq (by ring)
    have hpow : (1 / 2 : ℝ)⁻¹ ^ m ≤ (1 / 4 : ℝ)⁻¹ ^ m :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) m
    calc ‖𝓕 (fun r : ℝ => (lagPsi (1 / 2) m (r ^ 2 / 2) : ℂ)) ξ -
            ((-1 : ℝ) ^ m : ℂ) * (lagPsi (1 / 2) m (ξ ^ 2 / 2) : ℂ)‖
        ≤ ‖𝓕 (fun r : ℝ => (lagPsi (1 / 2) m (r ^ 2 / 2) : ℂ)) ξ‖ +
          ‖((-1 : ℝ) ^ m : ℂ) * (lagPsi (1 / 2) m (ξ ^ 2 / 2) : ℂ)‖ := norm_sub_le _ _
      _ ≤ C_coeff * (1 / 2 : ℝ)⁻¹ ^ m := by dsimp [C_coeff]; linarith
      _ ≤ C_coeff * (1 / 4 : ℝ)⁻¹ ^ m := mul_le_mul_of_nonneg_left hpow hC_nn
  -- Generating series identity for `|z| < 1/4`
  have hseries : ∀ z : ℝ, |z| < 1 / 4 →
      HasSum (fun m : ℕ => ((z ^ m : ℝ) : ℂ) *
          (𝓕 (fun r : ℝ => (lagPsi (1 / 2) m (r ^ 2 / 2) : ℂ)) ξ -
            ((-1 : ℝ) ^ m : ℂ) * (lagPsi (1 / 2) m (ξ ^ 2 / 2) : ℂ))) 0 := by
    intro z hz
    have hz1 : |z| < 1 := hz.trans (by norm_num)
    have h1mz : 0 < 1 - z := by linarith [(abs_lt.mp hz1).2]
    have h1pz : 0 < 1 + z := by linarith [(abs_lt.mp hz1).1]
    set β : ℝ := (1 + z) / (1 - z) with hβdef
    have hβ_pos : 0 < β := div_pos h1pz h1mz
    have hgen : ∀ (w_arg : ℝ), |w_arg| < 1 → ∀ r : ℝ,
        HasSum (fun m : ℕ => ((w_arg ^ m : ℝ) : ℂ) * (lagPsi (1 / 2) m (r ^ 2 / 2) : ℂ))
          (((1 - w_arg) ^ (-(1 / 2 : ℝ)) : ℝ) *
            (Real.exp (-π * ((1 + w_arg) / (1 - w_arg)) * r ^ 2) : ℂ)) := by
      intro w_arg hw r
      have h1mw : 0 < 1 - w_arg := by linarith [(abs_lt.mp hw).2]
      have h := hasSum_lagL_gen_real (w := 1 / 2) (by norm_num) (2 * π * r ^ 2) hw
      have hmul := h.mul_left (Real.exp (-π * r ^ 2))
      have hpt : (fun m : ℕ => Real.exp (-π * r ^ 2) * (lagL (1 / 2) m (2 * π * r ^ 2) * w_arg ^ m)) =
          fun m => w_arg ^ m * lagPsi (1 / 2) m (r ^ 2 / 2) := by
        ext m; unfold lagPsi
        rw [show 4 * π * (r ^ 2 / 2) = 2 * π * r ^ 2 by ring,
            show -2 * π * (r ^ 2 / 2) = -π * r ^ 2 by ring]
        ring
      have hrhs : Real.exp (-π * r ^ 2) * lagGenReal (1 / 2) (2 * π * r ^ 2) w_arg =
          (1 - w_arg) ^ (-(1 / 2 : ℝ)) * Real.exp (-π * ((1 + w_arg) / (1 - w_arg)) * r ^ 2) := by
        unfold lagGenReal
        rw [mul_left_comm, ← Real.exp_add]
        congr 2; field_simp [h1mw.ne']; ring
      rw [hpt, hrhs] at hmul
      have hmulC := Complex.hasSum_ofReal.mpr hmul
      rw [Complex.ofReal_mul] at hmulC
      exact hmulC.congr_fun fun m => by rw [Complex.ofReal_mul]
    have hdom_sum : Summable (fun m : ℕ => ∫ r : ℝ, ‖𝐞 (-⟪r, ξ⟫) • (((z ^ m : ℝ) : ℂ) *
        (lagPsi (1 / 2) m (r ^ 2 / 2) : ℂ))‖) := by
      have hgeo : Summable (fun m : ℕ => (A * ∫ r : ℝ, Real.exp (-π / 3 * r ^ 2)) * (2 * |z|) ^ m) :=
        (summable_geometric_of_lt_one (by positivity) (by linarith)).mul_left _
      refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun _ => norm_nonneg _) (fun m => ?_) hgeo
      have hpt : ∀ r : ℝ, ‖𝐞 (-⟪r, ξ⟫) • (((z ^ m : ℝ) : ℂ) * (lagPsi (1 / 2) m (r ^ 2 / 2) : ℂ))‖ ≤
          (A * (2 * |z|) ^ m) * Real.exp (-π / 3 * r ^ 2) := by
        intro r
        rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul, norm_mul,
            Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
        have hb := hbound m r
        have h2 : |z| ^ m * ((1 / 2 : ℝ)⁻¹ ^ m) = (2 * |z|) ^ m := by
          rw [← mul_pow]; congr 1; ring
        calc |z| ^ m * |lagPsi (1 / 2) m (r ^ 2 / 2)|
            ≤ |z| ^ m * (A * (1 / 2 : ℝ)⁻¹ ^ m * Real.exp (-π / 3 * r ^ 2)) :=
              mul_le_mul_of_nonneg_left hb (pow_nonneg (abs_nonneg _) m)
          _ = A * (|z| ^ m * (1 / 2 : ℝ)⁻¹ ^ m) * Real.exp (-π / 3 * r ^ 2) := by ring
          _ = (A * (2 * |z|) ^ m) * Real.exp (-π / 3 * r ^ 2) := by rw [h2]
      calc ∫ r : ℝ, ‖𝐞 (-⟪r, ξ⟫) • (((z ^ m : ℝ) : ℂ) * (lagPsi (1 / 2) m (r ^ 2 / 2) : ℂ))‖
          ≤ ∫ r : ℝ, (A * (2 * |z|) ^ m) * Real.exp (-π / 3 * r ^ 2) :=
            integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              (hgauss_int.const_mul _) (Eventually.of_forall hpt)
        _ = (A * ∫ r : ℝ, Real.exp (-π / 3 * r ^ 2)) * (2 * |z|) ^ m := by
            rw [integral_const_mul]; ring
    have hint_m : ∀ m : ℕ, Integrable (fun r : ℝ =>
        𝐞 (-⟪r, ξ⟫) • (((z ^ m : ℝ) : ℂ) * (lagPsi (1 / 2) m (r ^ 2 / 2) : ℂ))) := by
      intro m
      refine (hgauss_int.const_mul (A * (2 * |z|) ^ m)).mono' ?_ (Eventually.of_forall fun r => ?_)
      · exact (Continuous.aestronglyMeasurable (by
          have hc : Continuous (fun r : ℝ => lagPsi (1 / 2) m (r ^ 2 / 2)) :=
            (continuous_lagPsi (1 / 2) m).comp ((continuous_pow 2).div_const 2)
          fun_prop))
      · rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul, norm_mul,
            Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
        have hb := hbound m r
        have h2 : |z| ^ m * ((1 / 2 : ℝ)⁻¹ ^ m) = (2 * |z|) ^ m := by
          rw [← mul_pow]; congr 1; ring
        calc |z| ^ m * |lagPsi (1 / 2) m (r ^ 2 / 2)|
            ≤ |z| ^ m * (A * (1 / 2 : ℝ)⁻¹ ^ m * Real.exp (-π / 3 * r ^ 2)) :=
              mul_le_mul_of_nonneg_left hb (pow_nonneg (abs_nonneg _) m)
          _ = A * (|z| ^ m * (1 / 2 : ℝ)⁻¹ ^ m) * Real.exp (-π / 3 * r ^ 2) := by ring
          _ = (A * (2 * |z|) ^ m) * Real.exp (-π / 3 * r ^ 2) := by rw [h2]
    have hlhs := hasSum_integral_of_summable_integral_norm hint_m hdom_sum
    have htsum_pt : (fun r : ℝ => ∑' m : ℕ, 𝐞 (-⟪r, ξ⟫) • (((z ^ m : ℝ) : ℂ) * (lagPsi (1 / 2) m (r ^ 2 / 2) : ℂ))) =
        fun r => (((1 - z) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          (𝐞 (-⟪r, ξ⟫) • (Real.exp (-π * β * r ^ 2) : ℂ)) := by
      ext r
      have h1 := ((hgen z hz1 r).const_smul (𝐞 (-⟪r, ξ⟫))).tsum_eq
      rw [h1, Circle.smul_def, Circle.smul_def]; ring
    have hint_lhs : ∫ r : ℝ, (((1 - z) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          (𝐞 (-⟪r, ξ⟫) • (Real.exp (-π * β * r ^ 2) : ℂ)) =
        (((1 + z) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Real.exp (-π * β⁻¹ * ξ ^ 2) : ℂ) := by
      rw [integral_const_mul, ← Real.fourier_eq, spinD2_fourier_gaussian_1D hβ_pos ξ, ← mul_assoc]
      congr 1
      rw [← Complex.ofReal_mul]
      congr 1
      rw [← Real.mul_rpow h1mz.le hβ_pos.le, hβdef, mul_div_cancel₀ _ h1mz.ne']
    have hlhs' : HasSum (fun m : ℕ => ((z ^ m : ℝ) : ℂ) * 𝓕 (fun r : ℝ => (lagPsi (1 / 2) m (r ^ 2 / 2) : ℂ)) ξ)
        ((((1 + z) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Real.exp (-π * β⁻¹ * ξ ^ 2) : ℂ)) := by
      rw [htsum_pt, hint_lhs] at hlhs
      refine hlhs.congr_fun fun m => ?_
      rw [Real.fourier_eq, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      dsimp only
      rw [Circle.smul_def, Circle.smul_def]; ring
    have hrhs' : HasSum (fun m : ℕ => ((z ^ m : ℝ) : ℂ) *
          (((-1 : ℝ) ^ m : ℂ) * (lagPsi (1 / 2) m (ξ ^ 2 / 2) : ℂ)))
        ((((1 + z) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Real.exp (-π * β⁻¹ * ξ ^ 2) : ℂ)) := by
      have h := hgen (-z) (by rwa [abs_neg]) ξ
      have h2 : (1 + (-z)) / (1 - (-z)) = β⁻¹ := by rw [hβdef, inv_div]; ring_nf
      have h1 : 1 - (-z) = 1 + z := by ring
      rw [h2, h1] at h
      refine h.congr_fun fun m => ?_
      push_cast
      rw [← mul_assoc, ← mul_pow]
      congr 2; ring
    have hsub := hlhs'.sub hrhs'
    rw [sub_self] at hsub
    exact hsub.congr_fun fun m => by ring
  -- Extract real and imaginary parts and apply `real_power_series_coeff_zero`
  set d : ℕ → ℂ := fun m =>
    𝓕 (fun r : ℝ => (lagPsi (1 / 2) m (r ^ 2 / 2) : ℂ)) ξ -
      ((-1 : ℝ) ^ m : ℂ) * (lagPsi (1 / 2) m (ξ ^ 2 / 2) : ℂ)
  have hre : (d k).re = 0 := by
    refine real_power_series_coeff_zero (r := 1 / 4) (M := C_coeff) (by norm_num) hC_nn
      (fun m => (Complex.abs_re_le_norm (d m)).trans (hcoeff_bd m)) (fun z hz => ?_) k
    have h := Complex.reCLM.hasSum (hseries z hz)
    refine h.congr_fun fun m => ?_
    change (d m).re * z ^ m = Complex.reCLM (((z ^ m : ℝ) : ℂ) * d m)
    rw [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_comm]
  have him : (d k).im = 0 := by
    refine real_power_series_coeff_zero (r := 1 / 4) (M := C_coeff) (by norm_num) hC_nn
      (fun m => (Complex.abs_im_le_norm (d m)).trans (hcoeff_bd m)) (fun z hz => ?_) k
    have h := Complex.imCLM.hasSum (hseries z hz)
    refine h.congr_fun fun m => ?_
    change (d m).im * z ^ m = Complex.imCLM (((z ^ m : ℝ) : ℂ) * d m)
    rw [Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, mul_comm]
  have hd0 : d k = 0 := Complex.ext hre him
  exact sub_eq_zero.mp hd0

private lemma spin_lagPsi_sq_cosh_integrable (a : ℝ) (k : ℕ) :
    Integrable (fun r : ℝ => |lagPsi (1 / 2) k (r ^ 2 / 2)| * Real.cosh (2 * π * Real.sqrt a * r)) := by
  have hgauss : Integrable (fun r : ℝ => Real.exp (-(π / 6) * r ^ 2)) :=
    (integrable_exp_neg_mul_sq (b := π / 6) (by positivity)).congr
      (Eventually.of_forall fun r => by simp [neg_mul])
  set A : ℝ := (1 - (1 / 2 : ℝ)) ^ (-(1 / 2 : ℝ)) * (1 / 2 : ℝ)⁻¹ ^ k
  set M : ℝ := A * Real.exp (6 * π * max a 0)
  refine (hgauss.const_mul M).mono' ?_ (Eventually.of_forall fun r => ?_)
  · exact (Continuous.aestronglyMeasurable (by
      have hc : Continuous (fun r : ℝ => lagPsi (1 / 2) k (r ^ 2 / 2)) :=
        (continuous_lagPsi (1 / 2) k).comp ((continuous_pow 2).div_const 2)
      fun_prop))
  · rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)]
    have hb := abs_lagPsi_le (w := 1 / 2) (by norm_num) (θ := 1 / 2) (by norm_num) (by norm_num)
      (t := r ^ 2 / 2) (by positivity) k
    have hcosh : Real.cosh (2 * π * Real.sqrt a * r) ≤ Real.exp (2 * π * Real.sqrt a * |r|) := by
      rw [Real.cosh_eq]
      have h1 : Real.exp (2 * π * Real.sqrt a * r) ≤ Real.exp (2 * π * Real.sqrt a * |r|) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self r) (by positivity))
      have h2 : Real.exp (-(2 * π * Real.sqrt a * r)) ≤ Real.exp (2 * π * Real.sqrt a * |r|) := by
        refine Real.exp_le_exp.mpr ?_
        have : -r ≤ |r| := neg_le_abs r
        have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 2 * π * Real.sqrt a)
        linarith
      linarith
    have hcomp : -2 * π * ((1 - (1 / 2 : ℝ)) / (1 + 1 / 2)) * (r ^ 2 / 2) + 2 * π * Real.sqrt a * |r| ≤
        6 * π * max a 0 + -(π / 6) * r ^ 2 := by
      have hsq : 0 ≤ (|r| - 6 * Real.sqrt a) ^ 2 := sq_nonneg _
      have ha_sq : Real.sqrt a ^ 2 ≤ max a 0 := by
        rcases le_total 0 a with h | h
        · rw [Real.sq_sqrt h]; exact le_max_left _ _
        · rw [Real.sqrt_eq_zero_of_nonpos h]; simp
      have habs2 : |r| ^ 2 = r ^ 2 := sq_abs r
      have hpi : 0 < π := Real.pi_pos
      nlinarith
    calc |lagPsi (1 / 2) k (r ^ 2 / 2)| * Real.cosh (2 * π * Real.sqrt a * r)
        ≤ (A * Real.exp (-2 * π * ((1 - (1 / 2 : ℝ)) / (1 + 1 / 2)) * (r ^ 2 / 2))) *
            Real.exp (2 * π * Real.sqrt a * |r|) :=
          mul_le_mul hb hcosh (Real.cosh_pos _).le (by positivity)
      _ = A * Real.exp (-2 * π * ((1 - (1 / 2 : ℝ)) / (1 + 1 / 2)) * (r ^ 2 / 2) +
            2 * π * Real.sqrt a * |r|) := by rw [mul_assoc, ← Real.exp_add]
      _ ≤ A * Real.exp (6 * π * max a 0 + -(π / 6) * r ^ 2) := by
          gcongr
      _ = M * Real.exp (-(π / 6) * r ^ 2) := by rw [Real.exp_add]; dsimp [M]; ring

private lemma spin_lagPsi_prod_fourier (m n : ℕ) (hmn : Odd (m + n)) :
    𝓕 (spinToEuc (fun p : ℝ × ℝ => lagPsi (1 / 2) m (p.1 ^ 2 / 2) * lagPsi (1 / 2) n (p.2 ^ 2 / 2))) =
      -(spinToEuc (fun p : ℝ × ℝ => lagPsi (1 / 2) m (p.1 ^ 2 / 2) * lagPsi (1 / 2) n (p.2 ^ 2 / 2))) := by
  ext ξ
  rw [Real.fourier_eq, Pi.neg_apply]
  let e : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))
  have hmpe : MeasurePreserving e volume volume :=
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).comp (PiLp.volume_preserving_ofLp (Fin 2))
  have hconv : ∫ v : EuclideanSpace ℝ (Fin 2),
      𝐞 (-⟪v, ξ⟫) • spinToEuc (fun p : ℝ × ℝ => lagPsi (1 / 2) m (p.1 ^ 2 / 2) * lagPsi (1 / 2) n (p.2 ^ 2 / 2)) v =
      ∫ p : ℝ × ℝ,
        (𝐞 (-(p.1 * ξ 0)) • (lagPsi (1 / 2) m (p.1 ^ 2 / 2) : ℂ)) *
        (𝐞 (-(p.2 * ξ 1)) • (lagPsi (1 / 2) n (p.2 ^ 2 / 2) : ℂ)) := by
    rw [← hmpe.integral_comp']
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    have hinner : ⟪v, ξ⟫ = v 0 * ξ 0 + v 1 * ξ 1 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
      simp [mul_comm]
    have hev : e v = (v 0, v 1) := rfl
    dsimp only
    rw [hev, hinner]
    simp only [spinToEuc, neg_add, Circle.smul_def, Complex.ofReal_mul,
      AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  rw [hconv, Measure.volume_eq_prod]
  rw [integral_prod_mul
    (fun x : ℝ => 𝐞 (-(x * ξ 0)) • (lagPsi (1 / 2) m (x ^ 2 / 2) : ℂ))
    (fun y : ℝ => 𝐞 (-(y * ξ 1)) • (lagPsi (1 / 2) n (y ^ 2 / 2) : ℂ))]
  have h1 : ∫ x : ℝ, 𝐞 (-(x * ξ 0)) • (lagPsi (1 / 2) m (x ^ 2 / 2) : ℂ) =
      𝓕 (fun r : ℝ => (lagPsi (1 / 2) m (r ^ 2 / 2) : ℂ)) (ξ 0) := by
    rw [Real.fourier_eq]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    have hmul : ⟪x, ξ 0⟫ = x * ξ 0 := by rw [RCLike.inner_apply]; simp [mul_comm]
    rw [hmul]
  have h2 : ∫ y : ℝ, 𝐞 (-(y * ξ 1)) • (lagPsi (1 / 2) n (y ^ 2 / 2) : ℂ) =
      𝓕 (fun r : ℝ => (lagPsi (1 / 2) n (r ^ 2 / 2) : ℂ)) (ξ 1) := by
    rw [Real.fourier_eq]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    have hmul : ⟪y, ξ 1⟫ = y * ξ 1 := by rw [RCLike.inner_apply]; simp [mul_comm]
    rw [hmul]
  rw [h1, h2, spin_fourier_lagPsi_1D m (ξ 0), spin_fourier_lagPsi_1D n (ξ 1)]
  have hodd : ((-1 : ℝ) ^ m : ℂ) * ((-1 : ℝ) ^ n : ℂ) = -1 := by
    rw [← pow_add, ← Complex.ofReal_pow, hmn.neg_one_pow]; simp
  simp only [spinToEuc, Complex.ofReal_mul]
  linear_combination (lagPsi (1 / 2) m (ξ 0 ^ 2 / 2) : ℂ) * (lagPsi (1 / 2) n (ξ 1 ^ 2 / 2) : ℂ) * hodd

private lemma spinOddLaguerreBasis_mem_SpinTestClassJ {a : ℝ} (ha : 2 ≤ a) {m n : ℕ}
    (hmn : Odd (m + n)) :
    SpinTestClassJ a (spinOddLaguerreBasis m n) := by
  have hmn' : Odd (n + m) := by rwa [add_comm]
  have hint_prod : ∀ k l : ℕ, Integrable (fun p : ℝ × ℝ =>
      |lagPsi (1 / 2) k (p.1 ^ 2 / 2) * lagPsi (1 / 2) l (p.2 ^ 2 / 2)| *
        Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2)) := by
    intro k l
    have h := (spin_lagPsi_sq_cosh_integrable a k).mul_prod (spin_lagPsi_sq_cosh_integrable a l)
    rw [← Measure.volume_eq_prod] at h
    exact h.congr (Eventually.of_forall fun p => by dsimp only; rw [abs_mul]; ring)
  have hcont : Continuous (spinOddLaguerreBasis m n) := by
    unfold spinOddLaguerreBasis
    have h1 : Continuous (fun r : ℝ => lagPsi (1 / 2) m (r ^ 2 / 2)) :=
      (continuous_lagPsi (1 / 2) m).comp ((continuous_pow 2).div_const 2)
    have h2 : Continuous (fun r : ℝ => lagPsi (1 / 2) n (r ^ 2 / 2)) :=
      (continuous_lagPsi (1 / 2) n).comp ((continuous_pow 2).div_const 2)
    exact continuous_const.mul
      (((h1.comp continuous_fst).mul (h2.comp continuous_snd)).add
       ((h1.comp continuous_snd).mul (h2.comp continuous_fst)))
  have hint_J : Integrable (fun p : ℝ × ℝ =>
      |spinOddLaguerreBasis m n p| * Real.cosh (2 * π * Real.sqrt a * p.1) *
        Real.cosh (2 * π * Real.sqrt a * p.2)) := by
    have hdom := ((hint_prod m n).add (hint_prod n m)).const_mul (1 / 2 : ℝ)
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((hcont.abs.mul (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)
          (Real.cosh_pos _).le)]
      unfold spinOddLaguerreBasis
      have htri := abs_add_le
        (lagPsi (1 / 2) m (p.1 ^ 2 / 2) * lagPsi (1 / 2) n (p.2 ^ 2 / 2))
        (lagPsi (1 / 2) m (p.2 ^ 2 / 2) * lagPsi (1 / 2) n (p.1 ^ 2 / 2))
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have hc1 : 0 ≤ Real.cosh (2 * π * Real.sqrt a * p.1) := (Real.cosh_pos _).le
      have hc2 : 0 ≤ Real.cosh (2 * π * Real.sqrt a * p.2) := (Real.cosh_pos _).le
      have hsw : |lagPsi (1 / 2) m (p.2 ^ 2 / 2) * lagPsi (1 / 2) n (p.1 ^ 2 / 2)| =
          |lagPsi (1 / 2) n (p.1 ^ 2 / 2) * lagPsi (1 / 2) m (p.2 ^ 2 / 2)| := by rw [mul_comm]
      rw [hsw] at htri
      dsimp only [Pi.add_apply]
      nlinarith [mul_nonneg hc1 hc2]
  have hint : Integrable (spinOddLaguerreBasis m n) := by
    refine hint_J.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    have h12 : 1 ≤ Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2) :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_cosh _) (Real.one_le_cosh _)
    nlinarith [abs_nonneg (spinOddLaguerreBasis m n p)]
  have hint_M2 : Integrable (fun p : ℝ × ℝ =>
      |spinOddLaguerreBasis m n p| * spinV1 a p.1 * spinV1 a p.2) := by
    refine hint_J.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hV1 : Continuous (spinV1 a) := by unfold spinV1; fun_prop
      exact ((hcont.abs.mul (hV1.comp continuous_fst)).mul (hV1.comp continuous_snd)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (spinV1_nonneg ha p.1))
          (spinV1_nonneg ha p.2))]
      have hv1 : spinV1 a p.1 ≤ Real.cosh (2 * π * Real.sqrt a * p.1) := by
        unfold spinV1; linarith [Real.cosh_pos (2 * π * Real.sqrt (a - 2) * p.1)]
      have hv2 : spinV1 a p.2 ≤ Real.cosh (2 * π * Real.sqrt a * p.2) := by
        unfold spinV1; linarith [Real.cosh_pos (2 * π * Real.sqrt (a - 2) * p.2)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hv1 (abs_nonneg _)) hv2
        (spinV1_nonneg ha p.2) (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)
  have hd4 : IsD4Invariant (spinOddLaguerreBasis m n) :=
    ⟨fun r₁ r₂ => by unfold spinOddLaguerreBasis; simp,
     fun r₁ r₂ => by unfold spinOddLaguerreBasis; simp,
     fun r₁ r₂ => by unfold spinOddLaguerreBasis; ring⟩
  have hfo : 𝓕 (spinToEuc (spinOddLaguerreBasis m n)) = -(spinToEuc (spinOddLaguerreBasis m n)) := by
    let g₁ : ℝ × ℝ → ℝ := fun p => lagPsi (1 / 2) m (p.1 ^ 2 / 2) * lagPsi (1 / 2) n (p.2 ^ 2 / 2)
    let g₂ : ℝ × ℝ → ℝ := fun p => lagPsi (1 / 2) n (p.1 ^ 2 / 2) * lagPsi (1 / 2) m (p.2 ^ 2 / 2)
    have hsplit : spinToEuc (spinOddLaguerreBasis m n) =
        ((1 / 2 : ℝ) : ℂ) • (spinToEuc g₁ + spinToEuc g₂) := by
      ext v
      simp only [spinToEuc, Pi.smul_apply, Pi.add_apply, smul_eq_mul, spinOddLaguerreBasis, g₁, g₂]
      push_cast; ring
    have hint_g : ∀ k l : ℕ, Integrable (spinToEuc (fun p : ℝ × ℝ =>
        lagPsi (1 / 2) k (p.1 ^ 2 / 2) * lagPsi (1 / 2) l (p.2 ^ 2 / 2))) := by
      intro k l
      have h0 : Integrable (fun p : ℝ × ℝ =>
          lagPsi (1 / 2) k (p.1 ^ 2 / 2) * lagPsi (1 / 2) l (p.2 ^ 2 / 2)) := by
        refine (hint_prod k l).mono' ?_ (Eventually.of_forall fun p => ?_)
        · have h1 : Continuous (fun r : ℝ => lagPsi (1 / 2) k (r ^ 2 / 2)) :=
            (continuous_lagPsi (1 / 2) k).comp ((continuous_pow 2).div_const 2)
          have h2 : Continuous (fun r : ℝ => lagPsi (1 / 2) l (r ^ 2 / 2)) :=
            (continuous_lagPsi (1 / 2) l).comp ((continuous_pow 2).div_const 2)
          exact ((h1.comp continuous_fst).mul (h2.comp continuous_snd)).aestronglyMeasurable
        · rw [Real.norm_eq_abs]
          have h12 : 1 ≤ Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2) :=
            one_le_mul_of_one_le_of_one_le (Real.one_le_cosh _) (Real.one_le_cosh _)
          nlinarith [abs_nonneg (lagPsi (1 / 2) k (p.1 ^ 2 / 2) * lagPsi (1 / 2) l (p.2 ^ 2 / 2))]
      let e : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))
      have hmpe : MeasurePreserving e volume volume :=
        (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).comp (PiLp.volume_preserving_ofLp (Fin 2))
      exact (hmpe.integrable_comp_emb e.measurableEmbedding).mpr h0.ofReal
    rw [hsplit]
    have hsmul : ∀ (c : ℂ) (f : EuclideanSpace ℝ (Fin 2) → ℂ), 𝓕 (c • f) = c • 𝓕 f := fun c f => by
      ext w; simp only [Real.fourier_eq, Pi.smul_apply]; simp_rw [smul_comm _ c]; exact integral_smul c _
    have hadd : ∀ (f₁ f₂ : EuclideanSpace ℝ (Fin 2) → ℂ), Integrable f₁ → Integrable f₂ →
        𝓕 (f₁ + f₂) = 𝓕 f₁ + 𝓕 f₂ := fun f₁ f₂ h₁ h₂ => by
      ext w
      simp only [Real.fourier_eq, Pi.add_apply]
      have hi1 := (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
        (L := innerₗ (EuclideanSpace ℝ (Fin 2))) continuous_inner w).2 h₁
      have hi2 := (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
        (L := innerₗ (EuclideanSpace ℝ (Fin 2))) continuous_inner w).2 h₂
      simp_rw [smul_add]; exact integral_add hi1 hi2
    rw [hsmul, hadd _ _ (hint_g m n) (hint_g n m),
        spin_lagPsi_prod_fourier m n hmn, spin_lagPsi_prod_fourier n m hmn']
    ext v; simp [g₁, g₂]; ring
  exact ⟨⟨hcont, hint, hd4, hfo, hint_M2⟩, hint_J⟩

/-- Every certified test `Φ ∈ SpinCertifiedT a` lifts to `SpinTestClassJ a`. -/
theorem spinLiftTToR_mem_SpinTestClassJ {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinCertifiedT a Φ) :
    SpinTestClassJ a (spinLiftTToR Φ) := by
  have hzero : SpinTestClassJ a 0 := by
    refine ⟨⟨continuous_const, integrable_zero _ _ _, ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩,
      ?_, ?_⟩, ?_⟩
    · ext v; simp [spinToEuc, Real.fourier_eq]
    · simp
    · simp
  have hadd : ∀ {f g : ℝ × ℝ → ℝ}, SpinTestClassJ a f → SpinTestClassJ a g →
      SpinTestClassJ a (f + g) := by
    intro f g hf hg
    have hfo : 𝓕 (spinToEuc (f + g)) = -(spinToEuc (f + g)) := by
      have heq : spinToEuc (f + g) = spinToEuc f + spinToEuc g := by
        ext v; simp [spinToEuc]
      have hfi : Integrable (spinToEuc f) := by
        let e : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
          (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))
        have hmpe : MeasurePreserving e volume volume :=
          (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).comp (PiLp.volume_preserving_ofLp (Fin 2))
        exact (hmpe.integrable_comp_emb e.measurableEmbedding).mpr hf.base.int.ofReal
      have hgi : Integrable (spinToEuc g) := by
        let e : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
          (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))
        have hmpe : MeasurePreserving e volume volume :=
          (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).comp (PiLp.volume_preserving_ofLp (Fin 2))
        exact (hmpe.integrable_comp_emb e.measurableEmbedding).mpr hg.base.int.ofReal
      rw [heq]
      ext w
      simp only [Real.fourier_eq, Pi.add_apply, Pi.neg_apply]
      have hi1 : Integrable (fun v : EuclideanSpace ℝ (Fin 2) => 𝐞 (-⟪v, w⟫) • spinToEuc f v) :=
        (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
          (L := innerₗ (EuclideanSpace ℝ (Fin 2))) continuous_inner w).2 hfi
      have hi2 : Integrable (fun v : EuclideanSpace ℝ (Fin 2) => 𝐞 (-⟪v, w⟫) • spinToEuc g v) :=
        (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
          (L := innerₗ (EuclideanSpace ℝ (Fin 2))) continuous_inner w).2 hgi
      simp_rw [smul_add]
      rw [integral_add hi1 hi2, ← Real.fourier_eq, ← Real.fourier_eq,
          hf.base.fourier_odd, hg.base.fourier_odd]
      simp; ring
    have hint_J : Integrable (fun p : ℝ × ℝ =>
        |(f + g) p| * Real.cosh (2 * π * Real.sqrt a * p.1) *
          Real.cosh (2 * π * Real.sqrt a * p.2)) := by
      refine (hf.int_J.add hg.int_J).mono' ?_ (Eventually.of_forall fun p => ?_)
      · exact (((hf.base.cont.add hg.base.cont).abs.mul (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
      · rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)
            (Real.cosh_pos _).le)]
        have htri := abs_add_le (f p) (g p)
        have hc := mul_nonneg (Real.cosh_pos (2 * π * Real.sqrt a * p.1)).le
          (Real.cosh_pos (2 * π * Real.sqrt a * p.2)).le
        dsimp only [Pi.add_apply]
        nlinarith
    have hint_M2 : Integrable (fun p : ℝ × ℝ =>
        |(f + g) p| * spinV1 a p.1 * spinV1 a p.2) := by
      refine (hf.base.int_M2.add hg.base.int_M2).mono' ?_ (Eventually.of_forall fun p => ?_)
      · have hV1 : Continuous (spinV1 a) := by unfold spinV1; fun_prop
        exact (((hf.base.cont.add hg.base.cont).abs.mul (hV1.comp continuous_fst)).mul
          (hV1.comp continuous_snd)).aestronglyMeasurable
      · rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (spinV1_nonneg ha p.1))
            (spinV1_nonneg ha p.2))]
        have htri := abs_add_le (f p) (g p)
        have hv := mul_nonneg (spinV1_nonneg ha p.1) (spinV1_nonneg ha p.2)
        dsimp only [Pi.add_apply]
        nlinarith
    exact ⟨⟨hf.base.cont.add hg.base.cont, hf.base.int.add hg.base.int,
      ⟨fun x y => by simp [hf.base.d4_inv.1, hg.base.d4_inv.1],
       fun x y => by simp [hf.base.d4_inv.2.1, hg.base.d4_inv.2.1],
       fun x y => by simp [hf.base.d4_inv.2.2, hg.base.d4_inv.2.2]⟩, hfo, hint_M2⟩, hint_J⟩
  have hsmul : ∀ (c : ℝ) {f : ℝ × ℝ → ℝ}, SpinTestClassJ a f → SpinTestClassJ a (c • f) := by
    intro c f hf
    have hfo : 𝓕 (spinToEuc (c • f)) = -(spinToEuc (c • f)) := by
      have heq : spinToEuc (c • f) = (c : ℂ) • spinToEuc f := by
        ext v; simp [spinToEuc]
      rw [heq]
      ext w
      simp only [Real.fourier_eq, Pi.smul_apply, Pi.neg_apply]
      simp_rw [smul_comm _ (c : ℂ)]
      rw [integral_smul, ← Real.fourier_eq, hf.base.fourier_odd]
      simp
    have hint_J : Integrable (fun p : ℝ × ℝ =>
        |(c • f) p| * Real.cosh (2 * π * Real.sqrt a * p.1) *
          Real.cosh (2 * π * Real.sqrt a * p.2)) := by
      refine (hf.int_J.const_mul |c|).congr (Eventually.of_forall fun p => ?_)
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]; ring
    have hint_M2 : Integrable (fun p : ℝ × ℝ =>
        |(c • f) p| * spinV1 a p.1 * spinV1 a p.2) := by
      refine (hf.base.int_M2.const_mul |c|).congr (Eventually.of_forall fun p => ?_)
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]; ring
    exact ⟨⟨hf.base.cont.const_smul c, hf.base.int.smul c,
      ⟨fun x y => by simp [hf.base.d4_inv.1],
       fun x y => by simp [hf.base.d4_inv.2.1],
       fun x y => by simp [hf.base.d4_inv.2.2]⟩, hfo, hint_M2⟩, hint_J⟩
  unfold SpinCertifiedT at hΦ
  refine Submodule.span_induction (p := fun f _ => SpinTestClassJ a (spinLiftTToR f))
    ?_ ?_ ?_ ?_ hΦ
  · rintro f (⟨m, n, hmn, rfl⟩ | ⟨β₀, hβ₀, hβ₀2, rfl⟩)
    · have heq : spinLiftTToR (spinOddLagBasisT m n) = spinOddLaguerreBasis m n := rfl
      rw [heq]
      exact spinOddLaguerreBasis_mem_SpinTestClassJ ha hmn
    · have heq : spinLiftTToR (fun p : ℝ × ℝ => hMaj a β₀ (p.1 + p.2)) =
          spinRadialLift (hMaj a β₀) := by
        ext r; unfold spinLiftTToR spinRadialLift; dsimp only
        rw [show r.1 ^ 2 / 2 + r.2 ^ 2 / 2 = (r.1 ^ 2 + r.2 ^ 2) / 2 by ring]
      rw [heq]
      have ht0_pos : 0 < max (t0 β₀) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
      exact ((spinDM ha).1 ht0_pos hβ₀ hβ₀2 (le_max_left _ _)).1
  · have : spinLiftTToR (0 : ℝ × ℝ → ℝ) = 0 := rfl
    rw [this]; exact hzero
  · intro f g _ _ hf hg
    have : spinLiftTToR (f + g) = spinLiftTToR f + spinLiftTToR g := rfl
    rw [this]; exact hadd hf hg
  · intro c f _ hf
    have : spinLiftTToR (c • f) = c • spinLiftTToR f := rfl
    rw [this]; exact hsmul c hf

/-! ### Section 3: Unconditional quadrant positivity, hierarchy, and `SpinDW → SpinDSD` -/

/-- The certified feasible set on the quadrant `liouvilleCone` is nonempty for every `a ≥ 2`. -/
theorem spinCertifiedThr_quadrant_nonempty {a : ℝ} (ha : 2 ≤ a) :
    {T : ℝ | 0 < T ∧ ∃ Φ, SpinCertifiedT a Φ ∧ 0 < spinVacT a Φ ∧
      ∀ p ∈ (∅ : Set (ℝ × ℝ)) ∪ spinConeSlice (spinConeB 0) T, 0 ≤ Φ p}.Nonempty := by
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  have hc_pos : (0 : ℝ) < 12 * a := by linarith
  have hc_shift : 12 * virasoroProblem.totalShift ≤ 12 * a := by
    rw [virasoroProblem_totalShift]; linarith
  obtain ⟨τ₁, hτ₁, g₁, hg₁⟩ := exists_feasible_of_compact virasoroProblem hc_pos hc_shift
    isCompact_empty (empty_subset _)
  have hne : (constrainedGaps virasoroProblem (12 * a) ∅).Nonempty := ⟨τ₁, hτ₁, g₁, hg₁⟩
  set T₁ : ℝ := max 1 (constrainedThreshold virasoroProblem (12 * a) ∅ + 1)
  have hT₁_pos : 0 < T₁ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hno : ∀ N q, ¬ spinOddLagFeasible a N (spinConeSlice (spinConeB 0) T₁) q := by
    rintro N q ⟨hq_mem, hq_nn, hq_vac⟩
    have hmem : T₁ ∈ {T : ℝ | 0 < T ∧ ∃ Φ, SpinCertifiedT a Φ ∧ 0 < spinVacT a Φ ∧
        ∀ p ∈ (∅ : Set (ℝ × ℝ)) ∪ spinConeSlice (spinConeB 0) T, 0 ≤ Φ p} :=
      ⟨hT₁_pos, fun p => Real.exp (-2 * π * (p.1 + p.2)) * q p,
        exp_mul_mem_SpinCertifiedT hq_mem, hq_vac, by simpa using hq_nn⟩
    rw [hemp] at hmem
    exact hmem
  have hXc : IsClosed (spinConeSlice (spinConeB 0) T₁) :=
    isClosed_spinConeSlice (isClosed_spinConeB 0) T₁
  have hXs : IsSwapInvariantSet (spinConeSlice (spinConeB 0) T₁) :=
    isSwapInvariantSet_spinConeSlice (isSwapInvariantSet_spinConeB 0) T₁
  obtain ⟨meas, -⟩ := (spinDLPi ha le_rfl hT₁_pos hXc hXs Subset.rfl).1 hno
  let meas_12 : SpinCrossingMeasureOn (12 * a / 12) (spinConeSlice (spinConeB 0) T₁) :=
    { ν := meas.ν
      supp := meas.supp
      finite_laplace := meas.finite_laplace
      crossing := fun hL hR => by rw [show 12 * a / 12 = a by ring]; exact meas.crossing hL hR }
  let rad_meas : AdmissibleCrossingMeasure virasoroProblem (12 * a / 12) :=
    meas_12.toRadAdmissible (fun _ (hp : _ ∈ spinConeSlice (spinConeB 0) T₁) => hT₁_pos.le.trans hp.2)
  have hrad_supp : rad_meas.ν (∅ ∪ Ici T₁)ᶜ = 0 := by
    rw [empty_union]
    change spinRadMarginal meas.ν (Ici T₁)ᶜ = 0
    unfold spinRadMarginal
    have hmeas_sum : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
    rw [Measure.map_apply hmeas_sum isClosed_Ici.measurableSet.compl]
    have hsub : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' (Ici T₁)ᶜ ⊆ (spinConeSlice (spinConeB 0) T₁)ᶜ :=
      fun p hp hpX => hp hpX.2
    exact measure_mono_null hsub meas.supp
  have hle := le_constrainedThreshold_of_crossingMeasure virasoroProblem hc_pos hc_shift hne rad_meas hrad_supp
  have hgt : constrainedThreshold virasoroProblem (12 * a) ∅ < T₁ :=
    lt_of_lt_of_le (by linarith) (le_max_right _ _)
  linarith

/-- **Quadrant positivity and test-class hierarchy (unconditional)** for all `a ≥ 2`:
`0 < spinThrInf (SpinTestClass a) liouvilleCone a ≤ spinThrInf (SpinTestClassJ a) liouvilleCone a ≤ spinCertifiedThr a (spinConeB 0) ∅`. -/
theorem spinThrInf_quadrant_hierarchy {a : ℝ} (ha : 2 ≤ a) :
    0 < spinThrInf (SpinTestClass a) liouvilleCone a ∧
    spinThrInf (SpinTestClass a) liouvilleCone a ≤
      spinThrInf (SpinTestClassJ a) liouvilleCone a ∧
    spinThrInf (SpinTestClassJ a) liouvilleCone a ≤
      spinCertifiedThr a (spinConeB 0) ∅ := by
  have hcert_ne := spinCertifiedThr_quadrant_nonempty ha
  have hJ_le_cert : spinThrInf (SpinTestClassJ a) liouvilleCone a ≤
      spinCertifiedThr a (spinConeB 0) ∅ := by
    unfold spinThrInf spinCertifiedThr
    refine le_csInf hcert_ne ?_
    rintro T ⟨hT0, Φ, hΦmem, hΦvac, hΦnn⟩
    refine csInf_le ⟨0, fun τ hτ => hτ.1.le⟩ ⟨hT0, spinLiftTToR Φ,
      spinLiftTToR_mem_SpinTestClassJ ha hΦmem, hΦvac, fun p hp => ?_⟩
    have hmem : p ∈ (∅ : Set (ℝ × ℝ)) ∪ spinConeSlice (spinConeB 0) T := by
      rw [empty_union, spinConeSlice_quadrant]; exact hp
    have heval : spinEvalT (spinLiftTToR Φ) p = Φ p := by
      unfold spinEvalT spinLiftTToR
      have hp1 : (Real.sqrt (2 * p.1)) ^ 2 / 2 = p.1 := by
        rw [Real.sq_sqrt (by linarith [hp.1])]; ring
      have hp2 : (Real.sqrt (2 * p.2)) ^ 2 / 2 = p.2 := by
        rw [Real.sq_sqrt (by linarith [hp.2.1])]; ring
      simp only [hp1, hp2]
    rw [heval]; exact hΦnn p hmem
  have hJ_ne : {T : ℝ | 0 < T ∧ ∃ Φ, SpinIsFeasible (SpinTestClassJ a) liouvilleCone a T Φ}.Nonempty := by
    obtain ⟨T, hT0, Φ, hΦmem, hΦvac, hΦnn⟩ := hcert_ne
    refine ⟨T, hT0, spinLiftTToR Φ, spinLiftTToR_mem_SpinTestClassJ ha hΦmem, hΦvac, fun p hp => ?_⟩
    have hmem : p ∈ (∅ : Set (ℝ × ℝ)) ∪ spinConeSlice (spinConeB 0) T := by
      rw [empty_union, spinConeSlice_quadrant]; exact hp
    have heval : spinEvalT (spinLiftTToR Φ) p = Φ p := by
      unfold spinEvalT spinLiftTToR
      have hp1 : (Real.sqrt (2 * p.1)) ^ 2 / 2 = p.1 := by
        rw [Real.sq_sqrt (by linarith [hp.1])]; ring
      have hp2 : (Real.sqrt (2 * p.2)) ^ 2 / 2 = p.2 := by
        rw [Real.sq_sqrt (by linarith [hp.2.1])]; ring
      simp only [hp1, hp2]
    rw [heval]; exact hΦnn p hmem
  have hfull_le_J : spinThrInf (SpinTestClass a) liouvilleCone a ≤
      spinThrInf (SpinTestClassJ a) liouvilleCone a := by
    unfold spinThrInf
    refine le_csInf hJ_ne ?_
    rintro T ⟨hT0, Φ, hΦJ, hΦvac, hΦnn⟩
    exact csInf_le ⟨0, fun τ hτ => hτ.1.le⟩ ⟨hT0, Φ, hΦJ.base, hΦvac, hΦnn⟩
  have hfull_ne : {T : ℝ | 0 < T ∧ ∃ Φ, SpinIsFeasible (SpinTestClass a) liouvilleCone a T Φ}.Nonempty := by
    obtain ⟨T, hT0, Φ, hΦJ, hΦvac, hΦnn⟩ := hJ_ne
    exact ⟨T, hT0, Φ, hΦJ.base, hΦvac, hΦnn⟩
  -- Quadrant positivity `0 < spinThrInf (SpinTestClass a) liouvilleCone a`
  obtain ⟨C, hC_pos, hC⟩ := spinTestClass_L1_le_M2 ha
  have hV1_1_pos : 0 < spinV1 a 1 := by
    have := spinV1_ge_four_pi_sq_mul_sq' ha 1
    have hpi : 0 < π := Real.pi_pos
    nlinarith
  have hV1_le : ∀ r : ℝ, |r| ≤ 1 → spinV1 a r ≤ spinV1 a 1 := by
    intro r hr
    have habs : spinV1 a r = spinV1 a |r| := by
      rcases le_total 0 r with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, spinV1_even]
    rw [habs, spinV1_eq_mul_sinh a |r|, spinV1_eq_mul_sinh a 1]
    have hA : 0 ≤ Real.sqrt a + Real.sqrt (a - 2) := by positivity
    have hB : 0 ≤ Real.sqrt a - Real.sqrt (a - 2) :=
      sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
    have h1 : Real.sinh (π * |r| * (Real.sqrt a + Real.sqrt (a - 2))) ≤
        Real.sinh (π * 1 * (Real.sqrt a + Real.sqrt (a - 2))) :=
      Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_right (by nlinarith [Real.pi_pos]) hA)
    have h2 : Real.sinh (π * |r| * (Real.sqrt a - Real.sqrt (a - 2))) ≤
        Real.sinh (π * 1 * (Real.sqrt a - Real.sqrt (a - 2))) :=
      Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_right (by nlinarith [Real.pi_pos]) hB)
    have hnn1 : 0 ≤ Real.sinh (π * |r| * (Real.sqrt a + Real.sqrt (a - 2))) :=
      Real.sinh_nonneg_iff.mpr (by positivity)
    have hnn2 : 0 ≤ Real.sinh (π * |r| * (Real.sqrt a - Real.sqrt (a - 2))) :=
      Real.sinh_nonneg_iff.mpr (by positivity)
    nlinarith
  set Tmin : ℝ := min (1 / 2) (1 / (16 * C * spinV1 a 1 ^ 2))
  have hTmin_pos : 0 < Tmin := lt_min (by norm_num) (by positivity)
  have hpos : Tmin ≤ spinThrInf (SpinTestClass a) liouvilleCone a := by
    unfold spinThrInf
    refine le_csInf hfull_ne ?_
    rintro T ⟨hT0, Φ, hfeas⟩
    by_cases hT_half : 1 / 2 ≤ T
    · exact (min_le_left _ _).trans hT_half
    · push Not at hT_half
      have hweak := hfeas.isWeaklyFeasible ha
      have hM2_pos : 0 < spinM2 a Φ := hweak.2.1
      have hhalf := spin_half_mass ha hfeas.1 hfeas.2.1.le
      set R : ℝ := Real.sqrt (2 * T)
      have hR_nn : 0 ≤ R := Real.sqrt_nonneg _
      have hR_le1 : R ≤ 1 := by
        rw [Real.sqrt_le_one]; linarith
      let K : Set (ℝ × ℝ) := Icc (-R) R ×ˢ Icc (-R) R
      have hK_meas : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
      have hzero_out : ∀ p ∈ Kᶜ, max (-Φ p) 0 * spinV1 a p.1 * spinV1 a p.2 = 0 := by
        intro p hpK
        have hsum_ge : T ≤ p.1 ^ 2 / 2 + p.2 ^ 2 / 2 := by
          by_contra hlt; push Not at hlt
          apply hpK
          have h1 : p.1 ^ 2 ≤ 2 * T := by nlinarith [sq_nonneg p.2]
          have h2 : p.2 ^ 2 ≤ 2 * T := by nlinarith [sq_nonneg p.1]
          have ha1 : |p.1| ≤ R := by rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt h1
          have ha2 : |p.2| ≤ R := by rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt h2
          exact ⟨abs_le.mp ha1, abs_le.mp ha2⟩
        have hmem_cone : (p.1 ^ 2 / 2, p.2 ^ 2 / 2) ∈ liouvilleCone T :=
          ⟨by positivity, by positivity, hsum_ge⟩
        have hnn_eval := hfeas.2.2 (p.1 ^ 2 / 2, p.2 ^ 2 / 2) hmem_cone
        have heq_Φ : spinEvalT Φ (p.1 ^ 2 / 2, p.2 ^ 2 / 2) = Φ p := by
          unfold spinEvalT
          rw [show 2 * (p.1 ^ 2 / 2) = p.1 ^ 2 by ring,
              show 2 * (p.2 ^ 2 / 2) = p.2 ^ 2 by ring,
              Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
          rcases le_total 0 p.1 with h1 | h1 <;> rcases le_total 0 p.2 with h2 | h2
          · rw [abs_of_nonneg h1, abs_of_nonneg h2]
          · rw [abs_of_nonneg h1, abs_of_nonpos h2, hfeas.1.d4_inv.2.1]
          · rw [abs_of_nonpos h1, abs_of_nonneg h2, hfeas.1.d4_inv.1]
          · rw [abs_of_nonpos h1, abs_of_nonpos h2, hfeas.1.d4_inv.1, hfeas.1.d4_inv.2.1]
        rw [heq_Φ] at hnn_eval
        rw [max_eq_right (by linarith)]; ring
      have hint_eq : ∫ p : ℝ × ℝ, max (-Φ p) 0 * spinV1 a p.1 * spinV1 a p.2 =
          ∫ p in K, max (-Φ p) 0 * spinV1 a p.1 * spinV1 a p.2 := by
        rw [← integral_add_compl hK_meas (hfeas.1.int_neg_part ha)]
        have h0 : ∫ p in Kᶜ, max (-Φ p) 0 * spinV1 a p.1 * spinV1 a p.2 = 0 :=
          setIntegral_eq_zero_of_forall_eq_zero hzero_out
        linarith
      have hvolK : volume.real K = 8 * T := by
        dsimp only [K]
        rw [Measure.real_def, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
            ← ENNReal.ofReal_mul (by linarith), ENNReal.toReal_ofReal (by nlinarith)]
        have hRsq : R ^ 2 = 2 * T := Real.sq_sqrt (by linarith)
        nlinarith
      have hfinK : volume K < ∞ := by
        dsimp only [K]
        rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
      have hbd_K : ∫ p in K, max (-Φ p) 0 * spinV1 a p.1 * spinV1 a p.2 ≤
          8 * C * spinV1 a 1 ^ 2 * T * spinM2 a Φ := by
        have h1 : ∫ p in K, max (-Φ p) 0 * spinV1 a p.1 * spinV1 a p.2 ≤
            ∫ _ in K, (C * spinM2 a Φ * spinV1 a 1 ^ 2) := by
          refine setIntegral_mono_on (hfeas.1.int_neg_part ha).integrableOn
            (integrableOn_const hfinK.ne) hK_meas fun p hp => ?_
          have hp1 : |p.1| ≤ 1 := (abs_le.mpr hp.1).trans hR_le1
          have hp2 : |p.2| ≤ 1 := (abs_le.mpr hp.2).trans hR_le1
          have hΦp : max (-Φ p) 0 ≤ C * spinM2 a Φ :=
            (max_le (neg_le_abs _) (abs_nonneg _)).trans ((hC hfeas.1).1 p)
          have hv1 : spinV1 a p.1 ≤ spinV1 a 1 := hV1_le p.1 hp1
          have hv2 : spinV1 a p.2 ≤ spinV1 a 1 := hV1_le p.2 hp2
          calc max (-Φ p) 0 * spinV1 a p.1 * spinV1 a p.2
              ≤ (C * spinM2 a Φ) * spinV1 a 1 * spinV1 a 1 :=
                mul_le_mul (mul_le_mul hΦp hv1 (spinV1_nonneg ha p.1) (by positivity))
                  hv2 (spinV1_nonneg ha p.2) (by positivity)
            _ = C * spinM2 a Φ * spinV1 a 1 ^ 2 := by ring
        rw [setIntegral_const, smul_eq_mul, hvolK] at h1
        linarith
      have hle_M2 : (1 / 2 : ℝ) * spinM2 a Φ ≤ 8 * C * spinV1 a 1 ^ 2 * T * spinM2 a Φ := by
        linarith
      have hle_T : 1 / (16 * C * spinV1 a 1 ^ 2) ≤ T := by
        rw [div_le_iff₀ (by positivity)]
        have hcancel : (1 / 2 : ℝ) ≤ 8 * C * spinV1 a 1 ^ 2 * T :=
          le_of_mul_le_mul_right (by linarith) hM2_pos
        linarith
      exact (min_le_right _ _).trans hle_T
  exact ⟨hTmin_pos.trans_le hpos, hfull_le_J, hJ_le_cert⟩

/-- **Theorem SD (`sd:SD`) assembled from `SpinDW`** (`sd:W`, weak duality for the full continuous
class on the quadrant). Conjunct 1 is proved unconditionally (`spinDSD_cone`); Conjunct 2 combines
the unconditional `spinThrInf_quadrant_hierarchy` with `SpinDW`. -/
theorem spinDSD_of_spinDW (hW : SpinDW) : SpinDSD := by
  refine ⟨fun {a B} ha hB {Ω F} hΩc hΩs hΩB hFc hFs hFsub hTpos =>
    spinDSD_cone ha hB hΩc hΩs hΩB hFc hFs hFsub hTpos, ?_⟩
  intro a ha
  obtain ⟨hpos, hfull_le_J, hJ_le_cert⟩ := spinThrInf_quadrant_hierarchy ha
  have hcert_pos : 0 < spinCertifiedThr a (spinConeB 0) ∅ :=
    hpos.trans_le (hfull_le_J.trans hJ_le_cert)
  obtain ⟨-, ⟨meas, -⟩, -⟩ := spinDSD_cone ha le_rfl (isClosed_spinConeB 0)
    (isSwapInvariantSet_spinConeB 0) Subset.rfl isCompact_empty
    (fun _ h => h) (empty_subset _) hcert_pos
  set Tcert := spinCertifiedThr a (spinConeB 0) ∅
  have hmeas_supp_cone : meas.ν (liouvilleCone Tcert)ᶜ = 0 := by
    have heq : (∅ : Set (ℝ × ℝ)) ∪ spinConeSlice (spinConeB 0) Tcert = liouvilleCone Tcert := by
      rw [empty_union, spinConeSlice_quadrant]
    rw [← heq]; exact meas.supp
  let measQ : SpinCrossingMeasure a :=
    meas.toQuadrant (by
      rw [empty_union]; exact inter_subset_left)
  have hfull_ne : {T : ℝ | 0 < T ∧ ∃ Φ, SpinIsFeasible (SpinTestClass a) liouvilleCone a T Φ}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have : spinThrInf (SpinTestClass a) liouvilleCone a = 0 := by
      unfold spinThrInf; rw [hemp, Real.sInf_empty]
    linarith
  have hcert_le_full : Tcert ≤ spinThrInf (SpinTestClass a) liouvilleCone a := by
    unfold spinThrInf
    refine le_csInf hfull_ne ?_
    rintro T ⟨hT0, Φ, hΦ⟩
    by_contra hlt
    push Not at hlt
    have hnn_ae : ∀ᵐ p ∂measQ.ν, 0 ≤ spinEvalT Φ p := by
      have : ∀ᵐ p ∂measQ.ν, p ∉ (liouvilleCone Tcert)ᶜ :=
        measure_eq_zero_iff_ae_notMem.1 hmeas_supp_cone
      filter_upwards [this] with p hp
      have hpC : p ∈ liouvilleCone Tcert := not_not.mp hp
      exact hΦ.2.2 p ⟨hpC.1, hpC.2.1, hlt.le.trans hpC.2.2⟩
    have hvac_le : spinPhiVac a Φ ≤ 0 := (hW ha measQ hΦ.1 hT0 hΦ.2.2).2.2.1 hnn_ae
    linarith [hΦ.2.1]
  exact ⟨hpos, le_antisymm hfull_le_J (hJ_le_cert.trans hcert_le_full),
    le_antisymm hJ_le_cert (hcert_le_full.trans hfull_le_J)⟩

/-! ### Axiom guards -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinTestClass_L1_le_M2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinTestClass_L1_le_M2

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinLiftTToR_mem_SpinTestClassJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinLiftTToR_mem_SpinTestClassJ

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinCertifiedThr_quadrant_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinCertifiedThr_quadrant_nonempty

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinThrInf_quadrant_hierarchy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinThrInf_quadrant_hierarchy

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinDSD_of_spinDW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinDSD_of_spinDW

end FormalResearch.ModularBootstrap.Spin
