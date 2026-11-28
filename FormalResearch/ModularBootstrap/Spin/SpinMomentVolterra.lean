module

public import FormalResearch.ModularBootstrap.Spin.SpinMomentEq
public import FormalResearch.ModularBootstrap.Crossing.MehlerOddMoment

/-!
# SPIN-M part 2: Volterra reduction, vacuum kernel `H_C`, and exact pairing (`sd:spinmoment-pair`)

Formalises the weight-5 homogeneous reduction and exact pairing of
`CFT/modular_bootstrap/paper/spinning_airy_moment_proof.tex` (`sd:spinmoment-proof-sec`):

* `spinVolterraDens`, `spinVolterraAdjoint`: Volterra operator `(K ν₀)(dt) = ½ (∫_{r ≤ t} (3r - t) dν₀(r)) dt`
  and its adjoint `(K* g)(r) = ∫_r^∞ ((3r - t)/2) g(t) dt`.
* `spinVacuumD`, `spinVacB`, `spinVacHC`: weight-`w` vacuum kernel `D_w(α, t) = 2π K_w(α, t)`,
  `B_C(t)` (`sd:spinmoment-B`), and `H_C(t) = B_C(t) - 2 D_{5,1}(t)` (`sd:spinmoment-HC`).
* `spinVacB_eq_integral` & `spinVacHC_abs_le`: integral representation of `B_C` against
  `φ(α) = -(K ν_v)(-α)` on `[a - 2, a]`, giving the uniform pointwise bound
  `|H_C(t)| ≤ (2 a + 4) D_5(a, t)` (`sd:spinmoment-source`) for all `a ≥ 2, t ≥ 0`.
* `spinMoment_pair`: exact weight-5 pairing (`sd:spinmoment-pair`) for every `g ∈ Ā_5(a)` with
  fixed-charge sub-Gaussian decay `|g(t)| ≤ C_g exp(-4π √(a t) - δ √t)` (`δ > 0`), proved by
  applying `Crossing.MehlerOddMoment.lemma_fwA_part3_unconditional` (`w = 5`, `fw:abel`(3))
  to the Jordan positive/negative measures on `RadialSpace 5`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal Nat

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing

/-! ### Section 1: Volterra operator `K`, adjoint `K*`, and exponential Laplace transform -/

/-- Volterra density `(K ν₀)(t) = ∫_{r ≤ t} ((3r - t) / 2) dν₀(r)`. -/
noncomputable def spinVolterraDens (ν : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ r in Iic t, (3 * r - t) / 2 ∂ν

/-- Adjoint Volterra operator `(K* g)(r) = ∫_r^∞ ((3r - t) / 2) g(t) dt`. -/
noncomputable def spinVolterraAdjoint (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ t in Ici r, (3 * r - t) / 2 * g t

lemma measurable_spinVolterraDens (ν : Measure ℝ) [SFinite ν] :
    Measurable (spinVolterraDens ν) := by
  let f : ℝ → ℝ → ℝ := fun t r => (Iic t).indicator (fun r' => (3 * r' - t) / 2) r
  have hf_eq : spinVolterraDens ν = fun t => ∫ r, f t r ∂ν := by
    ext t; unfold spinVolterraDens; simp only [f, integral_indicator measurableSet_Iic]
  rw [hf_eq]
  have hmeas_ind : Measurable (Set.indicator {p : ℝ × ℝ | p.2 ≤ p.1} fun p : ℝ × ℝ => (3 * p.2 - p.1) / 2) :=
    Measurable.indicator (by fun_prop) (measurableSet_le measurable_snd measurable_fst)
  have hfeq : (fun p : ℝ × ℝ => f p.1 p.2) =
      Set.indicator {p : ℝ × ℝ | p.2 ≤ p.1} fun p : ℝ × ℝ => (3 * p.2 - p.1) / 2 :=
    funext fun p => by dsimp [f]; rw [Set.indicator_apply, Set.indicator_apply]; rfl
  have hsm : StronglyMeasurable fun p : ℝ × ℝ => f p.1 p.2 := (hfeq ▸ hmeas_ind).stronglyMeasurable
  exact hsm.integral_prod_right'.measurable

lemma spinVolterraDens_abs_le {ν : Measure ℝ} (hν_supp : ν (Iio 0) = 0)
    (hν_fin : ∀ R : ℝ, ν (Icc 0 R) < ⊤) {t : ℝ} (ht : 0 ≤ t) :
    |spinVolterraDens ν t| ≤ t * (ν (Icc 0 t)).toReal := by
  unfold spinVolterraDens
  have hIic_eq : ν.restrict (Iic t) = ν.restrict (Icc 0 t) := by
    refine Measure.restrict_congr_set ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hν_supp] with r hr
    show (r ∈ Iic t) ↔ (r ∈ Icc 0 t)
    exact ⟨fun hrt => ⟨not_lt.1 hr, hrt⟩, fun h => h.2⟩
  rw [hIic_eq]
  have hfin : (ν.restrict (Icc 0 t)) Set.univ < ⊤ := by simpa using hν_fin t
  have : IsFiniteMeasure (ν.restrict (Icc 0 t)) := ⟨hfin⟩
  have hle : ∀ r ∈ Icc (0 : ℝ) t, ‖(3 * r - t) / 2‖ ≤ t := fun r hr => by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hr.1, hr.2]
  calc |∫ r in Icc 0 t, (3 * r - t) / 2 ∂ν|
      = ‖∫ r, (3 * r - t) / 2 ∂(ν.restrict (Icc 0 t))‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ r, t ∂(ν.restrict (Icc 0 t)) := by
        refine norm_integral_le_of_norm_le (integrable_const t) ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        exact hle r hr
    _ = (ν (Icc 0 t)).toReal * t := by simp [Measure.real_def]
    _ = t * (ν (Icc 0 t)).toReal := mul_comm _ _

lemma spinVolterra_exp_integral (r : ℝ) {β : ℝ} (hβ : 0 < β) :
    IntegrableOn (fun t => (3 * r - t) / 2 * Real.exp (-2 * π * β * t)) (Ici r) ∧
      ∫ t in Ici r, (3 * r - t) / 2 * Real.exp (-2 * π * β * t) =
        Real.exp (-2 * π * β * r) * (r / (2 * π * β) - 1 / (2 * (2 * π * β) ^ 2)) := by
  let a : ℝ := 2 * π * β
  have ha : 0 < a := by positivity
  have h0_int : IntegrableOn (fun s : ℝ => Real.exp (-a * s)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith : -a < 0) 0
  have h1_int : IntegrableOn (fun s : ℝ => s * Real.exp (-a * s)) (Ioi 0) := by
    refine ((integrableOn_exp_mul_Ioi (by linarith : -(a / 2) < 0) 0).const_mul (2 / a)).mono'
      ((by fun_prop : Continuous fun s : ℝ => s * Real.exp (-a * s)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 ≤ s := (mem_Ioi.1 hs).le
    rw [Real.norm_of_nonneg (mul_nonneg hs0 (Real.exp_pos _).le)]
    have hlex : a / 2 * s ≤ Real.exp (a / 2 * s) := by
      have := Real.add_one_le_exp (a / 2 * s); linarith
    have hs_le : s ≤ 2 / a * Real.exp (a / 2 * s) := by
      calc s = (2 / a) * (a / 2 * s) := by field_simp [ha.ne']
        _ ≤ (2 / a) * Real.exp (a / 2 * s) := mul_le_mul_of_nonneg_left hlex (by positivity)
    calc s * Real.exp (-a * s) ≤ (2 / a * Real.exp (a / 2 * s)) * Real.exp (-a * s) :=
          mul_le_mul_of_nonneg_right hs_le (Real.exp_pos _).le
      _ = (2 / a) * Real.exp (-(a / 2) * s) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hInt_Ioi : IntegrableOn (fun s : ℝ => (r - s / 2) * Real.exp (-a * s)) (Ioi 0) :=
    IntegrableOn.congr_fun ((h0_int.const_mul r).sub (h1_int.const_mul (1 / 2 : ℝ)))
      (fun s _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi
  have hVal0 : ∫ s in Ioi (0 : ℝ), Real.exp (-a * s) = a⁻¹ := by
    have hgam : Real.Gamma 1 = 1 := Real.Gamma_one
    have hpow := Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 1) ha
    have hcongr : ∫ s in Ioi (0 : ℝ), s ^ ((1 : ℝ) - 1) * Real.exp (-(a * s)) =
        ∫ s in Ioi (0 : ℝ), Real.exp (-a * s) :=
      setIntegral_congr_fun measurableSet_Ioi fun s _ => by
        rw [sub_self, Real.rpow_zero, one_mul]; congr 1; ring
    rw [hcongr, hgam, mul_one, Real.rpow_one, one_div] at hpow
    exact hpow
  have hVal1 : ∫ s in Ioi (0 : ℝ), s * Real.exp (-a * s) = (1 / a) ^ 2 := by
    have hgam : Real.Gamma 2 = 1 := by
      rw [show (2 : ℝ) = ((1 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]; simp
    have hpow := Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 2) ha
    have hcongr : ∫ s in Ioi (0 : ℝ), s ^ ((2 : ℝ) - 1) * Real.exp (-(a * s)) =
        ∫ s in Ioi (0 : ℝ), s * Real.exp (-a * s) :=
      setIntegral_congr_fun measurableSet_Ioi fun s _ => by
        rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]; congr 1; ring
    rw [hcongr, hgam, mul_one, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hpow
    exact hpow
  have hVal_Ioi : ∫ s in Ioi (0 : ℝ), (r - s / 2) * Real.exp (-a * s) =
      r / a - 1 / (2 * a ^ 2) := by
    have heq : (fun s : ℝ => (r - s / 2) * Real.exp (-a * s)) =
        fun s => r * Real.exp (-a * s) - (1 / 2 : ℝ) * (s * Real.exp (-a * s)) := by ext s; ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => congrFun heq s),
      integral_sub (h0_int.const_mul r) (h1_int.const_mul (1 / 2 : ℝ)),
      integral_const_mul, integral_const_mul, hVal0, hVal1]
    field_simp
  have hIci_to_Ioi : IntegrableOn (fun s : ℝ => (r - s / 2) * Real.exp (-a * s)) (Ici 0) :=
    hInt_Ioi.congr_set_ae Ioi_ae_eq_Ici.symm
  have hshift : ∀ t : ℝ, (3 * r - t) / 2 * Real.exp (-2 * π * β * t) =
      Real.exp (-a * r) * ((r - (t - r) / 2) * Real.exp (-a * (t - r))) := fun t => by
    have hexp : Real.exp (-2 * π * β * t) = Real.exp (-a * r) * Real.exp (-a * (t - r)) := by
      dsimp [a]; rw [← Real.exp_add]; congr 1; ring
    rw [hexp]; ring
  have hInt_ind0 : Integrable (Set.indicator (Ici 0) (fun s : ℝ => (r - s / 2) * Real.exp (-a * s))) :=
    (integrable_indicator_iff measurableSet_Ici).2 hIci_to_Ioi
  have hInt_indr : Integrable (Set.indicator (Ici r) (fun t : ℝ => (r - (t - r) / 2) * Real.exp (-a * (t - r)))) := by
    have hcomp := hInt_ind0.comp_add_right (-r)
    refine hcomp.congr (Eventually.of_forall fun t => ?_)
    dsimp only
    rw [Set.indicator_apply, Set.indicator_apply]
    simp only [mem_Ici]
    by_cases h1 : r ≤ t
    · have h0 : 0 ≤ t + -r := by linarith
      simp [h1, h0]; ring
    · have h0 : ¬ 0 ≤ t + -r := by linarith
      simp [h1, h0]
  have hInt_map : IntegrableOn (fun t : ℝ => (r - (t - r) / 2) * Real.exp (-a * (t - r))) (Ici r) :=
    (integrable_indicator_iff measurableSet_Ici).1 hInt_indr
  refine ⟨IntegrableOn.congr_fun (hInt_map.const_mul (Real.exp (-a * r)))
      (fun t _ => (hshift t).symm) measurableSet_Ici, ?_⟩
  have htrans : ∫ t in Ici r, (r - (t - r) / 2) * Real.exp (-a * (t - r)) =
      ∫ s in Ioi (0 : ℝ), (r - s / 2) * Real.exp (-a * s) := by
    rw [← integral_indicator measurableSet_Ici,
      ← integral_add_right_eq_self (Set.indicator (Ici r) (fun t : ℝ => (r - (t - r) / 2) * Real.exp (-a * (t - r)))) r]
    have heq_ind : (fun s : ℝ => (Ici r).indicator (fun t => (r - (t - r) / 2) * Real.exp (-a * (t - r))) (s + r)) =
        (Ici 0).indicator (fun s => (r - s / 2) * Real.exp (-a * s)) := by
      ext s; simp [Set.indicator]
    rw [heq_ind, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  rw [show ∫ t in Ici r, (3 * r - t) / 2 * Real.exp (-2 * π * β * t) =
      ∫ t in Ici r, Real.exp (-a * r) * ((r - (t - r) / 2) * Real.exp (-a * (t - r))) from
      setIntegral_congr_fun measurableSet_Ici fun t _ => hshift t,
    integral_const_mul, htrans, hVal_Ioi]
  dsimp [a]; ring_nf

/-! ### Section 2: Vacuum kernels `D_w`, derivative in `α`, `B_C`, and `H_C` -/

/-- Vacuum kernel `D_w(α, t) = 2π K_w(α, t)` (`spinning_airy_moment_proof.tex`). -/
noncomputable def spinVacuumD (w : ℕ) (α t : ℝ) : ℝ :=
  2 * π * kernelK w α t

lemma spinVacuumD_nonneg {w : ℕ} {α t : ℝ} (hα : 0 ≤ α) (ht : 0 ≤ t) :
    0 ≤ spinVacuumD w α t :=
  mul_nonneg (by positivity) (kernelK_nonneg hα ht)

lemma spinVacuumD_mono_alpha {w : ℕ} {α₁ α₂ t : ℝ} (hα₁ : 0 ≤ α₁) (hα : α₁ ≤ α₂) (ht : 0 ≤ t) :
    spinVacuumD w α₁ t ≤ spinVacuumD w α₂ t :=
  mul_le_mul_of_nonneg_left (kernelK_mono_alpha hα₁ hα ht) (by positivity)

lemma spinVacuumD_continuous_alpha (w : ℕ) (t : ℝ) : Continuous (fun α : ℝ => spinVacuumD w α t) := by
  unfold spinVacuumD kernelK kernelKTerm
  refine continuous_const.mul (continuous_const.mul ?_)
  refine continuous_iff_continuousAt.mpr fun α₀ => ?_
  let R : ℝ := |α₀| + 1
  let M : ℕ → ℝ := fun k => (4 * π ^ 2 * R * |t|) ^ k / (k.factorial : ℝ)
  have hM : Summable M := Real.summable_pow_div_factorial _
  have hcont_unif : ContinuousOn (fun α : ℝ => ∑' k : ℕ, (4 * π ^ 2 * α * t) ^ k /
      ((k.factorial : ℝ) * ((k + w - 1).factorial : ℝ))) (Icc (-R) R) := by
    refine continuousOn_tsum (fun k => (by fun_prop : Continuous fun α : ℝ =>
        (4 * π ^ 2 * α * t) ^ k / ((k.factorial : ℝ) * ((k + w - 1).factorial : ℝ))).continuousOn) hM ?_
    intro k α hα
    have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) := by positivity
    have hfac2_pos : (0 : ℝ) < ((k + w - 1).factorial : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (mul_pos hfac_pos hfac2_pos)]
    have hfac : (1 : ℝ) ≤ ((k + w - 1).factorial : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
    have h1 : |4 * π ^ 2 * α * t| ≤ 4 * π ^ 2 * R * |t| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < (4 : ℝ)),
        abs_of_pos (sq_pos_of_pos Real.pi_pos)]
      have hα_le : |α| ≤ R := abs_le.mpr hα
      gcongr
    have hpow_le : |4 * π ^ 2 * α * t| ^ k ≤ (4 * π ^ 2 * R * |t|) ^ k :=
      pow_le_pow_left₀ (abs_nonneg _) h1 k
    have hdiv1 : |4 * π ^ 2 * α * t| ^ k / ((k.factorial : ℝ) * ((k + w - 1).factorial : ℝ)) ≤
        (4 * π ^ 2 * R * |t|) ^ k / ((k.factorial : ℝ) * ((k + w - 1).factorial : ℝ)) :=
      div_le_div_of_nonneg_right hpow_le (by positivity)
    have hdiv2 : (4 * π ^ 2 * R * |t|) ^ k / ((k.factorial : ℝ) * ((k + w - 1).factorial : ℝ)) ≤ M k := by
      dsimp [M]; refine div_le_div_of_nonneg_left (pow_nonneg (by positivity) k) hfac_pos ?_
      exact le_mul_of_one_le_right hfac_pos.le hfac
    exact hdiv1.trans hdiv2
  have hmem : α₀ ∈ Ioo (-R) R := ⟨by dsimp [R]; linarith [neg_abs_le α₀], by dsimp [R]; linarith [le_abs_self α₀]⟩
  exact hcont_unif.continuousAt (Icc_mem_nhds hmem.1 hmem.2)

lemma spinVacuumD_laplace {w : ℕ} (hw : 1 ≤ w) (α : ℝ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t => spinVacuumD w α t * Real.exp (-2 * π * b * t)) (Ioi 0) ∧
      ∫ t in Ioi 0, spinVacuumD w α t * Real.exp (-2 * π * b * t) =
        b ^ (-(w : ℝ)) * Real.exp (2 * π * α / b) := by
  have hk := kernelK_laplace hw α hb
  refine ⟨IntegrableOn.congr_fun (hk.1.const_mul (2 * π)) (fun t _ => by unfold spinVacuumD; ring) measurableSet_Ioi, ?_⟩
  rw [show (fun t => spinVacuumD w α t * Real.exp (-2 * π * b * t)) =
      fun t => (2 * π) * (kernelK w α t * Real.exp (-2 * π * b * t)) from
      funext fun t => by unfold spinVacuumD; ring,
    integral_const_mul, hk.2]

lemma hasDerivAt_spinVacuumD_alpha {w : ℕ} (hw : 1 ≤ w) (α t : ℝ) :
    HasDerivAt (fun α' => spinVacuumD w α' t) (2 * π * spinVacuumD (w + 1) α t) α := by
  let S : ℕ → ℝ → ℝ := fun k α' => kernelKTerm w α' t k
  let S' : ℕ → ℝ → ℝ := fun k α' => match k with
    | 0 => 0
    | k + 1 => 4 * π ^ 2 * t * kernelKTerm (w + 1) α' t k
  let R : ℝ := |α| + 1
  let B : ℕ → ℝ := fun k => match k with
    | 0 => 0
    | k + 1 => (4 * π ^ 2 * |t|) * (4 * π ^ 2 * R * |t|) ^ k / (k.factorial : ℝ)
  have hB : Summable B := by
    rw [← summable_nat_add_iff 1]
    exact ((Real.summable_pow_div_factorial (4 * π ^ 2 * R * |t|)).mul_left (4 * π ^ 2 * |t|)).congr fun k => by
      dsimp [B]; ring
  have hderiv_k : ∀ k : ℕ, ∀ α' ∈ Ioo (-R) R, HasDerivAt (S k) (S' k α') α' := fun k α' _ => by
    cases k with
    | zero => simpa [S, S', kernelKTerm] using hasDerivAt_const α' (kernelKTerm w α' t 0)
    | succ k =>
      dsimp [S, S', kernelKTerm]
      have hlin : HasDerivAt (fun x : ℝ => 4 * π ^ 2 * x * t) (4 * π ^ 2 * t) α' :=
        ((hasDerivAt_id α').const_mul (4 * π ^ 2) |>.mul_const t).congr_deriv (by ring)
      have hpow := (hlin.pow (k + 1)).div_const (((k + 1).factorial : ℝ) * (((k + 1) + w - 1).factorial : ℝ))
      refine hpow.congr_deriv ?_
      rw [show k + 1 - 1 = k by omega, show k + 1 + w - 1 = k + w by omega]
      have hfac1 : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      rw [hfac1]; push_cast; field_simp
  have hbound : ∀ k : ℕ, ∀ α' ∈ Ioo (-R) R, ‖S' k α'‖ ≤ B k := fun k α' hα' => by
    cases k with
    | zero => simp [S', B]
    | succ k =>
      dsimp [S', B, kernelKTerm]
      have hα_bd : |α'| ≤ R := abs_le.mpr ⟨hα'.1.le, hα'.2.le⟩
      have hfac : (1 : ℝ) ≤ ((k + w).factorial : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
      have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) := by positivity
      have hkw_pos : (0 : ℝ) < (k.factorial : ℝ) * ((k + w).factorial : ℝ) := by positivity
      have hrew : |4 * π ^ 2 * t * ((4 * π ^ 2 * α' * t) ^ k / ((k.factorial : ℝ) * ((k + w).factorial : ℝ)))| =
          4 * π ^ 2 * |t| * (|4 * π ^ 2 * α' * t| ^ k / ((k.factorial : ℝ) * ((k + w).factorial : ℝ))) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
          abs_of_pos (sq_pos_of_pos Real.pi_pos), abs_div, abs_pow, abs_of_pos hkw_pos]
      rw [hrew]
      have h1 : |4 * π ^ 2 * α' * t| ≤ 4 * π ^ 2 * R * |t| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
          abs_of_pos (sq_pos_of_pos Real.pi_pos)]
        gcongr
      have hpow : |4 * π ^ 2 * α' * t| ^ k ≤ (4 * π ^ 2 * R * |t|) ^ k :=
        pow_le_pow_left₀ (abs_nonneg _) h1 k
      have hdiv1 : 4 * π ^ 2 * |t| * (|4 * π ^ 2 * α' * t| ^ k / ((k.factorial : ℝ) * ((k + w).factorial : ℝ))) ≤
          4 * π ^ 2 * |t| * ((4 * π ^ 2 * R * |t|) ^ k / ((k.factorial : ℝ) * ((k + w).factorial : ℝ))) := by
        gcongr
      have hdiv2 : 4 * π ^ 2 * |t| * ((4 * π ^ 2 * R * |t|) ^ k / ((k.factorial : ℝ) * ((k + w).factorial : ℝ))) ≤
          4 * π ^ 2 * |t| * (4 * π ^ 2 * R * |t|) ^ k / (k.factorial : ℝ) := by
        rw [mul_div_assoc']
        exact div_le_div_of_nonneg_left (by positivity) hfac_pos (le_mul_of_one_le_right hfac_pos.le hfac)
      exact hdiv1.trans hdiv2
  have hmem_α : α ∈ Ioo (-R) R := ⟨by dsimp [R]; linarith [neg_abs_le α], by dsimp [R]; linarith [le_abs_self α]⟩
  have hmem_0 : (0 : ℝ) ∈ Ioo (-R) R := ⟨by dsimp [R]; linarith [abs_nonneg α], by dsimp [R]; linarith [abs_nonneg α]⟩
  have hd_tsum := hasDerivAt_tsum_of_isPreconnected hB isOpen_Ioo isPreconnected_Ioo
    hderiv_k hbound hmem_0 (summable_kernelKTerm w 0 t) hmem_α
  have hd_S' : HasSum (fun k => S' k α) (∑' k : ℕ, 4 * π ^ 2 * t * kernelKTerm (w + 1) α t k) := by
    have hs1 : Summable (fun k => 4 * π ^ 2 * t * kernelKTerm (w + 1) α t k) :=
      (summable_kernelKTerm (w + 1) α t).mul_left _
    have hshift := hs1.hasSum
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, S', sub_zero]
    exact hshift
  have hd_val := hd_tsum.congr_deriv (hd_S'.tsum_eq)
  have hev : (fun α' : ℝ => 2 * π * (2 * π * t) ^ (w - 1) * ∑' k : ℕ, S k α') =
      fun α' : ℝ => spinVacuumD w α' t := funext fun α' => by
    unfold spinVacuumD kernelK; dsimp [S]; ring
  rw [← hev]
  refine (hd_val.const_mul (2 * π * (2 * π * t) ^ (w - 1))).congr_deriv ?_
  unfold spinVacuumD kernelK
  have hsum2 : (∑' i : ℕ, 4 * π ^ 2 * t * kernelKTerm (w + 1) α t i) =
      4 * π ^ 2 * t * ∑' i : ℕ, kernelKTerm (w + 1) α t i := tsum_mul_left
  rw [hsum2, show (w + 1 - 1) = (w - 1) + 1 by omega, pow_succ]
  ring

/-- Vacuum Volterra kernel `B_C(t)` (`sd:spinmoment-B`). -/
noncomputable def spinVacB (a t : ℝ) : ℝ :=
  (spinVacuumD 3 a t - 2 * spinVacuumD 3 (a - 1) t + spinVacuumD 3 (a - 2) t) / (8 * π ^ 2) +
    (a * spinVacuumD 4 a t - 2 * (a - 1) * spinVacuumD 4 (a - 1) t +
      (a - 2) * spinVacuumD 4 (a - 2) t) / (2 * π)

/-- Full vacuum source `H_C(t) = B_C(t) - 2 D_{5,1}(t)` (`sd:spinmoment-HC`). -/
noncomputable def spinVacHC (a t : ℝ) : ℝ :=
  spinVacB a t - 2 * spinVacuumD 5 (a - 1) t

/-- Integral representation of `B_C(t)` on `[a - 2, a - 1]` and `[a - 1, a]`. -/
theorem spinVacB_eq_integral (a t : ℝ) :
    spinVacB a t =
      (∫ α in (a - 2)..(a - 1), ((α - 3 * a + 6) / 2) * spinVacuumD 5 α t) +
      (∫ α in (a - 1)..a, ((3 * a - α) / 2) * spinVacuumD 5 α t) := by
  have hI1 : ∫ α in (a - 2)..(a - 1), ((α - 3 * a + 6) / 2) * spinVacuumD 5 α t =
      (((a - 1) - 3 * a + 6) / 2 * spinVacuumD 4 (a - 1) t -
        ((a - 2) - 3 * a + 6) / 2 * spinVacuumD 4 (a - 2) t) / (2 * π) -
        (spinVacuumD 3 (a - 1) t - spinVacuumD 3 (a - 2) t) / (8 * π ^ 2) := by
    let F1 : ℝ → ℝ := fun α =>
      ((α - 3 * a + 6) / 2) * (spinVacuumD 4 α t / (2 * π)) - spinVacuumD 3 α t / (8 * π ^ 2)
    have hderiv : ∀ α ∈ uIcc (a - 2) (a - 1),
        HasDerivAt F1 (((α - 3 * a + 6) / 2) * spinVacuumD 5 α t) α := fun α _ => by
      have hdL : HasDerivAt (fun x : ℝ => (x - 3 * a + 6) / 2) (1 / 2) α := by
        simpa [sub_eq_add_neg, add_assoc] using (((hasDerivAt_id α).sub_const (3 * a)).add_const 6).div_const 2
      have hdD4 := (hasDerivAt_spinVacuumD_alpha (w := 4) (by norm_num) α t).div_const (2 * π)
      have hdD3 := (hasDerivAt_spinVacuumD_alpha (w := 3) (by norm_num) α t).div_const (8 * π ^ 2)
      refine ((hdL.mul hdD4).sub hdD3).congr_deriv ?_
      field_simp [Real.pi_ne_zero]; ring
    have hint : IntervalIntegrable (fun α => ((α - 3 * a + 6) / 2) * spinVacuumD 5 α t) volume (a - 2) (a - 1) :=
      (Continuous.mul (by fun_prop) (spinVacuumD_continuous_alpha 5 t)).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    dsimp [F1]; field_simp [Real.pi_ne_zero]; ring
  have hI2 : ∫ α in (a - 1)..a, ((3 * a - α) / 2) * spinVacuumD 5 α t =
      (a * spinVacuumD 4 a t - (a + 1 / 2) * spinVacuumD 4 (a - 1) t) / (2 * π) +
        (spinVacuumD 3 a t - spinVacuumD 3 (a - 1) t) / (8 * π ^ 2) := by
    let F2 : ℝ → ℝ := fun α =>
      ((3 * a - α) / 2) * (spinVacuumD 4 α t / (2 * π)) + spinVacuumD 3 α t / (8 * π ^ 2)
    have hderiv : ∀ α ∈ uIcc (a - 1) a,
        HasDerivAt F2 (((3 * a - α) / 2) * spinVacuumD 5 α t) α := fun α _ => by
      have hdL : HasDerivAt (fun x : ℝ => (3 * a - x) / 2) (-1 / 2) α :=
        (((hasDerivAt_const α (3 * a)).sub (hasDerivAt_id α)).div_const 2).congr_deriv (by ring)
      have hdD4 := (hasDerivAt_spinVacuumD_alpha (w := 4) (by norm_num) α t).div_const (2 * π)
      have hdD3 := (hasDerivAt_spinVacuumD_alpha (w := 3) (by norm_num) α t).div_const (8 * π ^ 2)
      refine ((hdL.mul hdD4).add hdD3).congr_deriv ?_
      field_simp [Real.pi_ne_zero]; ring
    have hint : IntervalIntegrable (fun α => ((3 * a - α) / 2) * spinVacuumD 5 α t) volume (a - 1) a :=
      (Continuous.mul (by fun_prop) (spinVacuumD_continuous_alpha 5 t)).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    dsimp [F2]; field_simp [Real.pi_ne_zero]; ring
  rw [hI1, hI2]
  unfold spinVacB
  ring

/-- Uniform pointwise source bound (`sd:spinmoment-source`): for all `a ≥ 2` and `t ≥ 0`,
`|H_C(t)| ≤ (2a + 4) D_5(a, t)`. -/
theorem spinVacHC_abs_le {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) :
    |spinVacHC a t| ≤ (2 * a + 4) * spinVacuumD 5 a t := by
  have ha1 : 0 ≤ a - 1 := by linarith
  have ha2 : 0 ≤ a - 2 := by linarith
  have hD5_nn : 0 ≤ spinVacuumD 5 a t := spinVacuumD_nonneg (by linarith) ht
  have hterm0 : |2 * spinVacuumD 5 (a - 1) t| ≤ 2 * spinVacuumD 5 a t := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (spinVacuumD_nonneg ha1 ht))]
    exact mul_le_mul_of_nonneg_left (spinVacuumD_mono_alpha ha1 (by linarith) ht) (by norm_num)
  have hterm1 : |∫ α in (a - 2)..(a - 1), ((α - 3 * a + 6) / 2) * spinVacuumD 5 α t| ≤
      (a + 1) * spinVacuumD 5 a t := by
    have hbd : ∀ α ∈ uIoc (a - 2) (a - 1),
        ‖((α - 3 * a + 6) / 2) * spinVacuumD 5 α t‖ ≤ (a + 1) * spinVacuumD 5 a t := by
      intro α hα
      rw [uIoc_of_le (by linarith : a - 2 ≤ a - 1), mem_Ioc] at hα
      have hα0 : 0 ≤ α := by linarith [hα.1]
      have hD : spinVacuumD 5 α t ≤ spinVacuumD 5 a t := spinVacuumD_mono_alpha hα0 (by linarith [hα.2]) ht
      have hφ : |(α - 3 * a + 6) / 2| ≤ a + 1 := by rw [abs_le]; constructor <;> linarith [hα.1, hα.2]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (spinVacuumD_nonneg hα0 ht)]
      exact mul_le_mul hφ hD (spinVacuumD_nonneg hα0 ht) (by linarith)
    calc _ ≤ ((a + 1) * spinVacuumD 5 a t) * |(a - 1) - (a - 2)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbd
      _ = (a + 1) * spinVacuumD 5 a t := by
          rw [show (a - 1) - (a - 2) = 1 by ring, abs_one, mul_one]
  have hterm2 : |∫ α in (a - 1)..a, ((3 * a - α) / 2) * spinVacuumD 5 α t| ≤
      (a + 1) * spinVacuumD 5 a t := by
    have hbd : ∀ α ∈ uIoc (a - 1) a,
        ‖((3 * a - α) / 2) * spinVacuumD 5 α t‖ ≤ (a + 1) * spinVacuumD 5 a t := by
      intro α hα
      rw [uIoc_of_le (by linarith : a - 1 ≤ a), mem_Ioc] at hα
      have hα0 : 0 ≤ α := by linarith [hα.1]
      have hD : spinVacuumD 5 α t ≤ spinVacuumD 5 a t := spinVacuumD_mono_alpha hα0 hα.2 ht
      have hφ : |(3 * a - α) / 2| ≤ a + 1 := by rw [abs_le]; constructor <;> linarith [hα.1, hα.2]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (spinVacuumD_nonneg hα0 ht)]
      exact mul_le_mul hφ hD (spinVacuumD_nonneg hα0 ht) (by linarith)
    calc _ ≤ ((a + 1) * spinVacuumD 5 a t) * |a - (a - 1)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbd
      _ = (a + 1) * spinVacuumD 5 a t := by
          rw [show a - (a - 1) = 1 by ring, abs_one, mul_one]
  unfold spinVacHC
  rw [spinVacB_eq_integral]
  calc |((∫ α in (a - 2)..(a - 1), _) + ∫ α in (a - 1)..a, _) - 2 * spinVacuumD 5 (a - 1) t|
      ≤ |(∫ α in (a - 2)..(a - 1), _) + ∫ α in (a - 1)..a, _| + |2 * spinVacuumD 5 (a - 1) t| := abs_sub _ _
    _ ≤ (|∫ α in (a - 2)..(a - 1), _| + |∫ α in (a - 1)..a, _|) + |2 * spinVacuumD 5 (a - 1) t| :=
        add_le_add (abs_add_le _ _) le_rfl
    _ ≤ ((a + 1) * spinVacuumD 5 a t + (a + 1) * spinVacuumD 5 a t) + 2 * spinVacuumD 5 a t :=
        add_le_add (add_le_add hterm1 hterm2) hterm0
    _ = (2 * a + 4) * spinVacuumD 5 a t := by ring

lemma continuous_spinVacHC (a : ℝ) : Continuous (spinVacHC a) := by
  unfold spinVacHC spinVacB spinVacuumD
  have hK : ∀ w α, Continuous (fun t => 2 * π * kernelK w α t) := fun w α =>
    continuous_const.mul (continuous_kernelK w α)
  exact (((((hK 3 a).sub ((hK 3 (a - 1)).const_mul 2)).add (hK 3 (a - 2))).div_const _).add
    ((((hK 4 a).const_mul a).sub ((hK 4 (a - 1)).const_mul (2 * (a - 1)))).add
      ((hK 4 (a - 2)).const_mul (a - 2)) |>.div_const _)).sub ((hK 5 (a - 1)).const_mul 2)

lemma spinVacHC_laplace {a b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t => spinVacHC a t * Real.exp (-2 * π * b * t)) (Ioi 0) ∧
      ∫ t in Ioi 0, spinVacHC a t * Real.exp (-2 * π * b * t) =
        b ^ (-(3 : ℝ)) / (8 * π ^ 2) *
            (Real.exp (2 * π * a / b) - 2 * Real.exp (2 * π * (a - 1) / b) + Real.exp (2 * π * (a - 2) / b)) +
          b ^ (-(4 : ℝ)) / (2 * π) *
            (a * Real.exp (2 * π * a / b) - 2 * (a - 1) * Real.exp (2 * π * (a - 1) / b) +
              (a - 2) * Real.exp (2 * π * (a - 2) / b)) -
          2 * (b ^ (-(5 : ℝ)) * Real.exp (2 * π * (a - 1) / b)) := by
  have h3a := spinVacuumD_laplace (w := 3) (by norm_num) a hb
  have h3b := spinVacuumD_laplace (w := 3) (by norm_num) (a - 1) hb
  have h3c := spinVacuumD_laplace (w := 3) (by norm_num) (a - 2) hb
  have h4a := spinVacuumD_laplace (w := 4) (by norm_num) a hb
  have h4b := spinVacuumD_laplace (w := 4) (by norm_num) (a - 1) hb
  have h4c := spinVacuumD_laplace (w := 4) (by norm_num) (a - 2) hb
  have h5b := spinVacuumD_laplace (w := 5) (by norm_num) (a - 1) hb
  have heq : (fun t : ℝ => spinVacHC a t * Real.exp (-2 * π * b * t)) =
      fun t : ℝ =>
        ((8 * π ^ 2)⁻¹ * (spinVacuumD 3 a t * Real.exp (-2 * π * b * t)) -
          (2 / (8 * π ^ 2)) * (spinVacuumD 3 (a - 1) t * Real.exp (-2 * π * b * t)) +
          (8 * π ^ 2)⁻¹ * (spinVacuumD 3 (a - 2) t * Real.exp (-2 * π * b * t))) +
        ((a / (2 * π)) * (spinVacuumD 4 a t * Real.exp (-2 * π * b * t)) -
          (2 * (a - 1) / (2 * π)) * (spinVacuumD 4 (a - 1) t * Real.exp (-2 * π * b * t)) +
          ((a - 2) / (2 * π)) * (spinVacuumD 4 (a - 2) t * Real.exp (-2 * π * b * t))) -
        2 * (spinVacuumD 5 (a - 1) t * Real.exp (-2 * π * b * t)) := by
    ext t; unfold spinVacHC spinVacB; ring
  have h3a' := (h3a.1.const_mul (8 * π ^ 2)⁻¹).congr (ae_of_all _ fun _ => rfl)
  have h3b' := (h3b.1.const_mul (2 / (8 * π ^ 2))).congr (ae_of_all _ fun _ => rfl)
  have h3c' := (h3c.1.const_mul (8 * π ^ 2)⁻¹).congr (ae_of_all _ fun _ => rfl)
  have h4a' := (h4a.1.const_mul (a / (2 * π))).congr (ae_of_all _ fun _ => rfl)
  have h4b' := (h4b.1.const_mul (2 * (a - 1) / (2 * π))).congr (ae_of_all _ fun _ => rfl)
  have h4c' := (h4c.1.const_mul ((a - 2) / (2 * π))).congr (ae_of_all _ fun _ => rfl)
  have h5b' := (h5b.1.const_mul (2 : ℝ)).congr (ae_of_all _ fun _ => rfl)
  have h3ab : IntegrableOn (fun t : ℝ => (8 * π ^ 2)⁻¹ * (spinVacuumD 3 a t * Real.exp (-2 * π * b * t)) -
      2 / (8 * π ^ 2) * (spinVacuumD 3 (a - 1) t * Real.exp (-2 * π * b * t))) (Ioi 0) := h3a'.sub h3b'
  have h3abc : IntegrableOn (fun t : ℝ => ((8 * π ^ 2)⁻¹ * (spinVacuumD 3 a t * Real.exp (-2 * π * b * t)) -
      2 / (8 * π ^ 2) * (spinVacuumD 3 (a - 1) t * Real.exp (-2 * π * b * t))) +
      (8 * π ^ 2)⁻¹ * (spinVacuumD 3 (a - 2) t * Real.exp (-2 * π * b * t))) (Ioi 0) := h3ab.add h3c'
  have h4ab : IntegrableOn (fun t : ℝ => a / (2 * π) * (spinVacuumD 4 a t * Real.exp (-2 * π * b * t)) -
      2 * (a - 1) / (2 * π) * (spinVacuumD 4 (a - 1) t * Real.exp (-2 * π * b * t))) (Ioi 0) := h4a'.sub h4b'
  have h4abc : IntegrableOn (fun t : ℝ => (a / (2 * π) * (spinVacuumD 4 a t * Real.exp (-2 * π * b * t)) -
      2 * (a - 1) / (2 * π) * (spinVacuumD 4 (a - 1) t * Real.exp (-2 * π * b * t))) +
      (a - 2) / (2 * π) * (spinVacuumD 4 (a - 2) t * Real.exp (-2 * π * b * t))) (Ioi 0) := h4ab.add h4c'
  have h34 : IntegrableOn (fun t : ℝ => (((8 * π ^ 2)⁻¹ * (spinVacuumD 3 a t * Real.exp (-2 * π * b * t)) -
      2 / (8 * π ^ 2) * (spinVacuumD 3 (a - 1) t * Real.exp (-2 * π * b * t))) +
      (8 * π ^ 2)⁻¹ * (spinVacuumD 3 (a - 2) t * Real.exp (-2 * π * b * t))) +
      ((a / (2 * π) * (spinVacuumD 4 a t * Real.exp (-2 * π * b * t)) -
      2 * (a - 1) / (2 * π) * (spinVacuumD 4 (a - 1) t * Real.exp (-2 * π * b * t))) +
      (a - 2) / (2 * π) * (spinVacuumD 4 (a - 2) t * Real.exp (-2 * π * b * t)))) (Ioi 0) := h3abc.add h4abc
  have hInt : IntegrableOn (fun t => spinVacHC a t * Real.exp (-2 * π * b * t)) (Ioi 0) :=
    IntegrableOn.congr_fun (h34.sub h5b')
      (fun t _ => by simp only [Pi.sub_apply]; exact (congrFun heq t).symm) measurableSet_Ioi
  refine ⟨hInt, ?_⟩
  rw [show ∫ (t : ℝ) in Ioi 0, spinVacHC a t * Real.exp (-2 * π * b * t) =
      ∫ (t : ℝ) in Ioi 0,
        (((8 * π ^ 2)⁻¹ * (spinVacuumD 3 a t * Real.exp (-2 * π * b * t)) -
          2 / (8 * π ^ 2) * (spinVacuumD 3 (a - 1) t * Real.exp (-2 * π * b * t))) +
          (8 * π ^ 2)⁻¹ * (spinVacuumD 3 (a - 2) t * Real.exp (-2 * π * b * t))) +
        ((a / (2 * π) * (spinVacuumD 4 a t * Real.exp (-2 * π * b * t)) -
          2 * (a - 1) / (2 * π) * (spinVacuumD 4 (a - 1) t * Real.exp (-2 * π * b * t))) +
          (a - 2) / (2 * π) * (spinVacuumD 4 (a - 2) t * Real.exp (-2 * π * b * t))) -
        2 * (spinVacuumD 5 (a - 1) t * Real.exp (-2 * π * b * t)) from
      setIntegral_congr_fun measurableSet_Ioi fun t _ => congrFun heq t]
  rw [integral_sub h34 h5b', integral_add h3abc h4abc, integral_add h3ab h3c', integral_sub h3a' h3b',
    integral_add h4ab h4c', integral_sub h4a' h4b',
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    h3a.2, h3b.2, h3c.2, h4a.2, h4b.2, h4c.2, h5b.2]
  ring

/-! ### Section 3: Sub-exponential and Cardy-weight envelopes -/

lemma cardyV_le_sub_exp {w : ℕ} (hw : 1 ≤ w) {a : ℝ} (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      kernelK w a t ≤ C * (1 + t) ^ (w - 1) * Real.exp (4 * π * Real.sqrt (a * t)) := by
  refine ⟨(2 * π) ^ (w - 1), by positivity, fun t ht => ?_⟩
  unfold kernelK
  have hsum_le : ∑' k : ℕ, kernelKTerm w a t k ≤ Real.exp (4 * π * Real.sqrt (a * t)) := by
    have hexp_even : ∑' k : ℕ, (4 * π ^ 2 * a * t) ^ k / ((k.factorial : ℝ) ^ 2) ≤
        Real.exp (4 * π * Real.sqrt (a * t)) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      have hterm_le : ∀ k : ℕ, (4 * π ^ 2 * a * t) ^ k / ((k.factorial : ℝ) ^ 2) ≤
          ((4 * π * Real.sqrt (a * t)) ^ (2 * k) / ((2 * k).factorial : ℝ)) := fun k => by
        have hsq : (4 * π * Real.sqrt (a * t)) ^ (2 * k) = 4 ^ k * (4 * π ^ 2 * a * t) ^ k := by
          have hbase : (4 * π * Real.sqrt (a * t)) ^ 2 = 4 * (4 * π ^ 2 * a * t) := by
            rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg ha ht)]; ring
          rw [pow_mul, hbase, mul_pow]
        have hfac : ((2 * k).factorial : ℝ) ≤ 4 ^ k * (k.factorial : ℝ) ^ 2 := by
          have hchoose : (2 * k).choose k ≤ 2 ^ (2 * k) := by
            have := Nat.sum_range_choose (2 * k)
            calc (2 * k).choose k ≤ ∑ i ∈ Finset.range (2 * k + 1), (2 * k).choose i :=
                  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
              _ = 2 ^ (2 * k) := this
          have hmul : (2 * k).factorial = (2 * k).choose k * (k.factorial * k.factorial) := by
            have := Nat.choose_mul_factorial_mul_factorial (by omega : k ≤ 2 * k)
            rw [show 2 * k - k = k by omega, mul_assoc] at this
            exact this.symm
          exact_mod_cast (hmul ▸ Nat.mul_le_mul_right (k.factorial * k.factorial) hchoose).trans_eq (by
            rw [show 2 ^ (2 * k) = 4 ^ k by rw [pow_mul]; norm_num]; ring)
        rw [hsq]
        have hnum : 0 ≤ (4 * π ^ 2 * a * t) ^ k := by positivity
        have hden1 : 0 < ((2 * k).factorial : ℝ) := by positivity
        have hden2 : 0 < (k.factorial : ℝ) ^ 2 := by positivity
        rw [div_le_div_iff₀ hden2 hden1]
        calc (4 * π ^ 2 * a * t) ^ k * ((2 * k).factorial : ℝ)
            ≤ (4 * π ^ 2 * a * t) ^ k * (4 ^ k * (k.factorial : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_left hfac hnum
          _ = 4 ^ k * (4 * π ^ 2 * a * t) ^ k * (k.factorial : ℝ) ^ 2 := by ring
      have hsumm_lhs : Summable fun k : ℕ => (4 * π ^ 2 * a * t) ^ k / ((k.factorial : ℝ) ^ 2) := by
        refine (Real.summable_pow_div_factorial (4 * π ^ 2 * a * t)).of_norm_bounded fun k => ?_
        have hfac : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
      have hsumm_rhs : Summable fun k : ℕ => (4 * π * Real.sqrt (a * t)) ^ (2 * k) / ((2 * k).factorial : ℝ) := by
        have hsub : (fun k : ℕ => (4 * π * Real.sqrt (a * t)) ^ (2 * k) / ((2 * k).factorial : ℝ)) =
            (fun n : ℕ => (4 * π * Real.sqrt (a * t)) ^ n / (n.factorial : ℝ)) ∘ (fun k => 2 * k) := rfl
        rw [hsub]
        exact (Real.summable_pow_div_factorial _).comp_injective (fun _ _ h => by omega)
      have hle1 := hsumm_lhs.tsum_le_tsum hterm_le hsumm_rhs
      have hle2 : ∑' k : ℕ, (4 * π * Real.sqrt (a * t)) ^ (2 * k) / ((2 * k).factorial : ℝ) ≤
          ∑' n : ℕ, (4 * π * Real.sqrt (a * t)) ^ n / (n.factorial : ℝ) :=
        hsumm_rhs.tsum_le_tsum_of_inj (fun k => 2 * k) (fun _ _ h => by dsimp only at h; omega)
          (fun _ _ => by positivity) (fun _ => le_rfl) (Real.summable_pow_div_factorial _)
      exact hle1.trans hle2
    have hK_le : ∑' k : ℕ, kernelKTerm w a t k ≤
        ∑' k : ℕ, (4 * π ^ 2 * a * t) ^ k / ((k.factorial : ℝ) ^ 2) := by
      refine (summable_kernelKTerm w a t).tsum_le_tsum (fun k => ?_) ?_
      · unfold kernelKTerm
        refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        have hfac : (k.factorial : ℝ) ≤ ((k + w - 1).factorial : ℝ) := by
          exact_mod_cast Nat.factorial_le (by omega)
        calc (k.factorial : ℝ) ^ 2 = (k.factorial : ℝ) * (k.factorial : ℝ) := sq _
          _ ≤ (k.factorial : ℝ) * ((k + w - 1).factorial : ℝ) :=
              mul_le_mul_of_nonneg_left hfac (by positivity)
      · refine (Real.summable_pow_div_factorial (4 * π ^ 2 * a * t)).of_norm_bounded fun k => ?_
        have hfac : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    exact hK_le.trans hexp_even
  have hpow : (2 * π * t) ^ (w - 1) ≤ (2 * π) ^ (w - 1) * (1 + t) ^ (w - 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [Real.pi_pos, ht]) (w - 1)
  calc (2 * π * t) ^ (w - 1) * ∑' k : ℕ, kernelKTerm w a t k
      ≤ ((2 * π) ^ (w - 1) * (1 + t) ^ (w - 1)) * Real.exp (4 * π * Real.sqrt (a * t)) :=
        mul_le_mul hpow hsum_le (tsum_nonneg fun _ => by unfold kernelKTerm; positivity) (by positivity)
    _ = _ := by ring

lemma rpow_neg_six_le_exp_neg_sqrt {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      Real.exp (-δ * Real.sqrt t) ≤ C * (1 + 2 * t) ^ (-6 : ℝ) := by
  let K : ℝ := 1 + 2 / δ ^ 2
  let C : ℝ := 64 * ((Nat.factorial 12 : ℝ) + 1) * K ^ 6
  refine ⟨C, by dsimp [C, K]; positivity, fun t ht => ?_⟩
  have h1t : 0 < 1 + 2 * t := by positivity
  let y : ℝ := δ * Real.sqrt t
  have hy : 0 ≤ y := mul_nonneg hδ.le (Real.sqrt_nonneg _)
  have ht_eq : 2 * t = (2 / δ ^ 2) * y ^ 2 := by
    dsimp [y]; rw [mul_pow, Real.sq_sqrt ht]; field_simp [hδ.ne']
  have h1t_le : 1 + 2 * t ≤ K * (1 + y ^ 2) := by
    rw [ht_eq]; dsimp [K]; nlinarith [sq_nonneg y, show 0 ≤ 2 / δ ^ 2 by positivity]
  have h6_le : (1 + 2 * t) ^ 6 ≤ K ^ 6 * (1 + y ^ 2) ^ 6 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ h1t.le h1t_le 6
  have hexp_1 : 1 ≤ Real.exp y := Real.one_le_exp hy
  have hexp_12 : y ^ 12 / (Nat.factorial 12 : ℝ) ≤ Real.exp y := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    exact (Real.summable_pow_div_factorial y).le_tsum 12
      fun k _ => div_nonneg (pow_nonneg hy k) (by positivity)
  have hy_bd : (1 + y ^ 2) ^ 6 ≤ 64 * ((Nat.factorial 12 : ℝ) + 1) * Real.exp y := by
    rcases le_or_gt y 1 with hy1 | hy1
    · have hpow : (1 + y ^ 2) ^ 6 ≤ 2 ^ 6 := pow_le_pow_left₀ (by positivity) (by nlinarith) 6
      calc (1 + y ^ 2) ^ 6 ≤ 64 := hpow.trans_eq (by norm_num)
        _ ≤ 64 * ((Nat.factorial 12 : ℝ) + 1) * 1 := by
            have hfac : (0 : ℝ) ≤ (Nat.factorial 12 : ℝ) := by positivity
            linarith
        _ ≤ 64 * ((Nat.factorial 12 : ℝ) + 1) * Real.exp y :=
            mul_le_mul_of_nonneg_left hexp_1 (by positivity)
    · have hpow : (1 + y ^ 2) ^ 6 ≤ (2 * y ^ 2) ^ 6 :=
        pow_le_pow_left₀ (by positivity) (by nlinarith) 6
      have h12 : y ^ 12 ≤ (Nat.factorial 12 : ℝ) * Real.exp y := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Nat.factorial 12 : ℝ))] at hexp_12
        linarith
      calc (1 + y ^ 2) ^ 6 ≤ 64 * y ^ 12 := hpow.trans_eq (by ring)
        _ ≤ 64 * ((Nat.factorial 12 : ℝ) * Real.exp y) := mul_le_mul_of_nonneg_left h12 (by norm_num)
        _ ≤ 64 * ((Nat.factorial 12 : ℝ) + 1) * Real.exp y := by
            have he : 0 ≤ Real.exp y := (Real.exp_pos _).le
            nlinarith
  have hprod_le : (1 + 2 * t) ^ 6 ≤ C * Real.exp y :=
    h6_le.trans ((mul_le_mul_of_nonneg_left hy_bd (by positivity)).trans_eq (by dsimp [C]; ring))
  have hrp : (1 + 2 * t) ^ (-6 : ℝ) = 1 / (1 + 2 * t) ^ 6 := by
    rw [show (-6 : ℝ) = ((-6 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg, one_div]; norm_cast
  rw [hrp, show -δ * Real.sqrt t = -y by dsimp [y]; ring, Real.exp_neg]
  rw [mul_one_div, le_div_iff₀ (pow_pos h1t 6), inv_mul_le_iff₀ (Real.exp_pos y)]
  exact hprod_le.trans_eq (mul_comm _ _)

lemma exp_neg_mul_le_cardyWeight {ε a : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      Real.exp (-2 * ε * t) ≤ C * cardyWeight (-6) (-2 * Real.sqrt 2 * π * Real.sqrt a) t := by
  let K : ℝ := 1 + 2 / ε
  let A : ℝ := Real.exp ((4 * π * Real.sqrt a) ^ 2 / (4 * ε))
  let C : ℝ := A * 64 * ((Nat.factorial 6 : ℝ) + 1) * K ^ 6
  refine ⟨C, by dsimp [C, A, K]; positivity, fun t ht => ?_⟩
  have h1t : 0 < 1 + 2 * t := by positivity
  have hcardy_eq : cardyWeight (-6) (-2 * Real.sqrt 2 * π * Real.sqrt a) t =
      (1 + 2 * t) ^ (-6 : ℝ) * Real.exp (-4 * π * Real.sqrt (a * t)) := by
    unfold cardyWeight
    congr 1; congr 1
    rw [Real.sqrt_mul (by norm_num) t, Real.sqrt_mul ha t]
    have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    calc -2 * √2 * π * √a * (√2 * √t) = -2 * (√2 * √2) * π * (√a * √t) := by ring
      _ = -4 * π * (√a * √t) := by rw [h2]; ring
  rw [hcardy_eq]
  have hquad : 4 * π * Real.sqrt (a * t) - ε * t ≤ (4 * π * Real.sqrt a) ^ 2 / (4 * ε) := by
    have hsq : 0 ≤ (ε * Real.sqrt t - 2 * π * Real.sqrt a) ^ 2 := sq_nonneg _
    have hst : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
    have hm : Real.sqrt (a * t) = Real.sqrt a * Real.sqrt t := Real.sqrt_mul ha t
    rw [hm]
    have h1 : ε ^ 2 * t - 4 * π * ε * Real.sqrt a * Real.sqrt t + (2 * π * Real.sqrt a) ^ 2 ≥ 0 := by
      have hexp : (ε * Real.sqrt t - 2 * π * Real.sqrt a) ^ 2 =
          ε ^ 2 * (Real.sqrt t) ^ 2 - 4 * π * ε * Real.sqrt a * Real.sqrt t + (2 * π * Real.sqrt a) ^ 2 := by ring
      rw [hst] at hexp; linarith
    have h2 : ε * t - 4 * π * Real.sqrt a * Real.sqrt t + (4 * π * Real.sqrt a) ^ 2 / (4 * ε) ≥ 0 := by
      have := div_nonneg h1 hε.le
      calc _ = (ε ^ 2 * t - 4 * π * ε * Real.sqrt a * Real.sqrt t + (2 * π * Real.sqrt a) ^ 2) / ε := by
            field_simp [hε.ne']; ring
        _ ≥ 0 := this
    linarith
  let y : ℝ := ε * t
  have hy : 0 ≤ y := mul_nonneg hε.le ht
  have h1t_le : 1 + 2 * t ≤ K * (1 + y) := by
    have : 2 * t = (2 / ε) * y := by dsimp [y]; field_simp [hε.ne']
    rw [this]; dsimp [K]; nlinarith [show 0 ≤ 2 / ε by positivity]
  have h6_le : (1 + 2 * t) ^ 6 ≤ K ^ 6 * (1 + y) ^ 6 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ h1t.le h1t_le 6
  have hexp_1 : 1 ≤ Real.exp y := Real.one_le_exp hy
  have hexp_6 : y ^ 6 / (Nat.factorial 6 : ℝ) ≤ Real.exp y := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    exact (Real.summable_pow_div_factorial y).le_tsum 6
      fun k _ => div_nonneg (pow_nonneg hy k) (by positivity)
  have hy_bd : (1 + y) ^ 6 ≤ 64 * ((Nat.factorial 6 : ℝ) + 1) * Real.exp y := by
    rcases le_or_gt y 1 with hy1 | hy1
    · have hpow : (1 + y) ^ 6 ≤ 2 ^ 6 := pow_le_pow_left₀ (by positivity) (by linarith) 6
      calc (1 + y) ^ 6 ≤ 64 := hpow.trans_eq (by norm_num)
        _ ≤ 64 * ((Nat.factorial 6 : ℝ) + 1) * 1 := by
            have hfac : (0 : ℝ) ≤ (Nat.factorial 6 : ℝ) := by positivity
            linarith
        _ ≤ 64 * ((Nat.factorial 6 : ℝ) + 1) * Real.exp y :=
            mul_le_mul_of_nonneg_left hexp_1 (by positivity)
    · have hpow : (1 + y) ^ 6 ≤ (2 * y) ^ 6 := pow_le_pow_left₀ (by positivity) (by linarith) 6
      have h6 : y ^ 6 ≤ (Nat.factorial 6 : ℝ) * Real.exp y := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Nat.factorial 6 : ℝ))] at hexp_6
        linarith
      calc (1 + y) ^ 6 ≤ 64 * y ^ 6 := hpow.trans_eq (by ring)
        _ ≤ 64 * ((Nat.factorial 6 : ℝ) * Real.exp y) := mul_le_mul_of_nonneg_left h6 (by norm_num)
        _ ≤ 64 * ((Nat.factorial 6 : ℝ) + 1) * Real.exp y := by
            have he : 0 ≤ Real.exp y := (Real.exp_pos _).le; nlinarith
  have h1t6 : (1 + 2 * t) ^ 6 ≤ (64 * ((Nat.factorial 6 : ℝ) + 1) * K ^ 6) * Real.exp y :=
    h6_le.trans ((mul_le_mul_of_nonneg_left hy_bd (by positivity)).trans_eq (by ring))
  have hrp : (1 + 2 * t) ^ (-6 : ℝ) = 1 / (1 + 2 * t) ^ 6 := by
    rw [show (-6 : ℝ) = ((-6 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg, one_div]; norm_cast
  rw [hrp, show C * (1 / (1 + 2 * t) ^ 6 * Real.exp (-4 * π * Real.sqrt (a * t))) =
      C * Real.exp (-4 * π * Real.sqrt (a * t)) / (1 + 2 * t) ^ 6 by ring,
    le_div_iff₀ (pow_pos h1t 6)]
  calc Real.exp (-2 * ε * t) * (1 + 2 * t) ^ 6
      ≤ Real.exp (-2 * ε * t) * ((64 * ((Nat.factorial 6 : ℝ) + 1) * K ^ 6) * Real.exp (ε * t)) :=
        mul_le_mul_of_nonneg_left h1t6 (Real.exp_pos _).le
    _ = (64 * ((Nat.factorial 6 : ℝ) + 1) * K ^ 6) * Real.exp (-ε * t) := by
        rw [mul_left_comm, ← Real.exp_add]; ring_nf
    _ ≤ (64 * ((Nat.factorial 6 : ℝ) + 1) * K ^ 6) * (A * Real.exp (-4 * π * Real.sqrt (a * t))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hle : -ε * t ≤ (4 * π * Real.sqrt a) ^ 2 / (4 * ε) + (-4 * π * Real.sqrt (a * t)) := by linarith
        exact (Real.exp_le_exp.mpr hle).trans_eq (Real.exp_add _ _)
    _ = C * Real.exp (-4 * π * Real.sqrt (a * t)) := by dsimp [C]; ring

lemma integrableOn_one_add_rpow_neg_two :
    IntegrableOn (fun t : ℝ => (1 + t) ^ (-2 : ℝ)) (Ici 0) := by
  have h1 : IntegrableOn (fun s : ℝ => s ^ (-2 : ℝ)) (Ici 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one).congr_set_ae
      Ioi_ae_eq_Ici.symm
  have hind : Integrable (Set.indicator (Ici 1) (fun s : ℝ => s ^ (-2 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Ici).2 h1
  have hind0 := hind.comp_add_right 1
  have heq : (fun t : ℝ => Set.indicator (Ici 1) (fun s : ℝ => s ^ (-2 : ℝ)) (t + 1)) =
      Set.indicator (Ici 0) (fun t : ℝ => (1 + t) ^ (-2 : ℝ)) := by
    ext t; simp [Set.indicator, add_comm t 1]
  rw [heq] at hind0
  exact (integrable_indicator_iff measurableSet_Ici).1 hind0

lemma cardyWeight_wbd_eq {a : ℝ} (ha : 0 ≤ a) {t : ℝ} (_ht : 0 ≤ t) :
    cardyWeight (-6) (-2 * Real.sqrt 2 * π * Real.sqrt a) t =
      (1 + 2 * t) ^ (-6 : ℝ) * Real.exp (-4 * π * Real.sqrt (a * t)) := by
  unfold cardyWeight
  congr 1; congr 1
  rw [Real.sqrt_mul (by norm_num) t, Real.sqrt_mul ha t]
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc -2 * √2 * π * √a * (√2 * √t) = -2 * (√2 * √2) * π * (√a * √t) := by ring
    _ = -4 * π * (√a * √t) := by rw [h2]; ring

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinVacB_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spinVacB_eq_integral

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinVacHC_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spinVacHC_abs_le

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinVacHC_laplace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spinVacHC_laplace

end FormalResearch.ModularBootstrap.Spin
