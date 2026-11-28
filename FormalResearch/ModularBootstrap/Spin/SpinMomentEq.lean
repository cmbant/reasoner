module

public import FormalResearch.ModularBootstrap.Spin.SpinDDefs

/-!
# SPIN-M part 1: auxiliary weight-5 problem, spin-square marginal `M`, and `sd:eSD3`

Formalises the transverse crossing differential identity of `CFT/modular_bootstrap/paper/spinning_airy_moment_proof.tex`
(`sd:spinmoment-proof-sec`):

* `spinMomentW5Prob`: the auxiliary `(w, Q) = (5, 1)` fixed-weight problem (`Q ≡ 1`, `totalShift = 0`,
  `cardyV a t = kernelK 5 a t`).
* `spinMomentMeasure`: the spin-square dimension marginal `M = (π_t)_* (j² ν)` (`t = t_L + t_R`,
  `j = t_L - t_R`), with `|j| ≤ t + 2B` on `E_B`, support on `[τ, ∞)`, and finite Laplace transform.
* `spinMomentF0`, `spinMomentY`, `spinOpA`, and **`sd_eSD3`**:
  `(1 - S_5) Y = 2 A F_0`, proved by differentiating `(sd:eSD1)` twice along `(b + h, b - h)` at `h = 0`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing

/-! ### Section 1: Auxiliary weight-5 problem `(w, Q) = (5, 1)` and spin-square marginal `M` -/

/-- Auxiliary fixed-weight problem with `w = 5` and `Q ≡ 1` (`m = 0`). -/
def spinMomentW5Prob : FixedWeightProblem where
  w := 5
  hw := by norm_num
  m := 0
  μ := fun l => Fin.elim0 l
  hμ := fun l => Fin.elim0 l

@[simp] lemma spinMomentW5Prob_w : spinMomentW5Prob.w = 5 := rfl
@[simp] lemma spinMomentW5Prob_m : spinMomentW5Prob.m = 0 := rfl

lemma spinMomentW5Prob_totalShift : spinMomentW5Prob.totalShift = 0 := by
  simp [FixedWeightProblem.totalShift, spinMomentW5Prob, Finset.sum_eq_zero (fun l _ => Fin.elim0 l)]

lemma spinMomentW5Prob_nullPoly (q : ℝ) : spinMomentW5Prob.nullPoly q = 1 := by
  simp [FixedWeightProblem.nullPoly, spinMomentW5Prob, Finset.prod_eq_one (fun l _ => Fin.elim0 l)]

lemma spinMomentW5Prob_cardyV (a t : ℝ) :
    spinMomentW5Prob.cardyV a t = kernelK 5 a t := by
  unfold FixedWeightProblem.cardyV FixedWeightProblem.shiftSum spinMomentW5Prob
  rw [Finset.sum_eq_single (∅ : Finset (Fin 0))]
  · simp
  · intro s _ hs; exfalso; exact hs (Finset.eq_empty_of_forall_notMem fun x _ => Fin.elim0 x)
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Spin-square dimension marginal `M = (π_t)_* (j² ν)` where `t = t_L + t_R` and `j = t_L - t_R`. -/
noncomputable def spinMomentMeasure (ν : Measure (ℝ × ℝ)) : Measure ℝ :=
  (ν.withDensity (fun p : ℝ × ℝ => ENNReal.ofReal ((p.1 - p.2) ^ 2))).map (fun p : ℝ × ℝ => p.1 + p.2)

lemma spinMomentMeasure_apply_set {ν : Measure (ℝ × ℝ)} {S : Set ℝ} (hS : MeasurableSet S) :
    spinMomentMeasure ν S =
      ∫⁻ p in (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' S, ENNReal.ofReal ((p.1 - p.2) ^ 2) ∂ν := by
  unfold spinMomentMeasure
  have hm : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
  rw [Measure.map_apply hm hS, withDensity_apply _ (hm hS)]

lemma spin_diff_le_of_mem_spinConeB {B : ℝ} {p : ℝ × ℝ} (hp : p ∈ spinConeB B) :
    |p.1 - p.2| ≤ p.1 + p.2 + 2 * B := by
  have h1 : -B ≤ p.1 := hp.1
  have h2 : -B ≤ p.2 := hp.2
  rw [abs_le]; constructor <;> linarith

lemma spin_diff_sq_le_of_mem_spinConeB {B : ℝ} {p : ℝ × ℝ} (hp : p ∈ spinConeB B) :
    (p.1 - p.2) ^ 2 ≤ (p.1 + p.2 + 2 * B) ^ 2 :=
  (sq_abs _).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) (spin_diff_le_of_mem_spinConeB hp) 2)

lemma spinConeB_subset_add {B₁ B₂ : ℝ} (h : B₁ ≤ B₂) : spinConeB B₁ ⊆ spinConeB B₂ :=
  fun _ hp => ⟨by linarith [hp.1], by linarith [hp.2]⟩

lemma spinMomentMeasure_Iio_eq_zero {a B τ : ℝ}
    {X : Set (ℝ × ℝ)} (hsub : X ⊆ spinConeB B ∩ {p : ℝ × ℝ | τ ≤ p.1 + p.2})
    (meas : SpinCrossingMeasureOn a X) :
    spinMomentMeasure meas.ν (Iio τ) = 0 := by
  rw [spinMomentMeasure_apply_set measurableSet_Iio]
  have hpre : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Iio τ ⊆ Xᶜ := by
    intro p hp hpX
    have h1 : τ ≤ p.1 + p.2 := (hsub hpX).2
    have h2 : p.1 + p.2 < τ := hp
    linarith
  exact setLIntegral_measure_zero _ _ (measure_mono_null hpre meas.supp)

lemma integrable_spinMomentMeasure_of_integrable {ν : Measure (ℝ × ℝ)} {f : ℝ → ℝ}
    (hf : Measurable f)
    (hInt : Integrable (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2 * f (p.1 + p.2)) ν) :
    Integrable f (spinMomentMeasure ν) := by
  unfold spinMomentMeasure
  have hm : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
  have hd : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal ((p.1 - p.2) ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).pow_const 2)
  rw [integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable,
    integrable_withDensity_iff_integrable_smul' hd (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine hInt.congr (Eventually.of_forall fun p => ?_)
  dsimp only [Function.comp_def]
  rw [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

lemma integral_spinMomentMeasure {ν : Measure (ℝ × ℝ)} {f : ℝ → ℝ}
    (hf : Measurable f) :
    ∫ t, f t ∂(spinMomentMeasure ν) =
      ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 * f (p.1 + p.2) ∂ν := by
  unfold spinMomentMeasure
  have hm : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
  have hd : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal ((p.1 - p.2) ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).pow_const 2)
  rw [integral_map hm.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hd (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp only [Function.comp_def]
  rw [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

lemma spin_poly_exp_le {β : ℝ} (hβ : 0 < β) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → x ^ k * Real.exp (-β * x) ≤ C := by
  refine ⟨(k.factorial : ℝ) / β ^ k, by positivity, fun x hx => ?_⟩
  have h1 := Real.pow_div_factorial_le_exp (β * x) (mul_nonneg hβ.le hx) k
  have h2 : (β * x) ^ k * Real.exp (-(β * x)) ≤ (k.factorial : ℝ) := by
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
    have h1' := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ k.factorial)
    rw [div_mul_cancel₀ _ (by positivity)] at h1'
    exact h1'.trans (mul_comm _ _).le
  have h3 : x ^ k * Real.exp (-β * x) = ((β * x) ^ k * Real.exp (-(β * x))) / β ^ k := by
    rw [mul_pow]; field_simp [hβ.ne']
  rw [h3]
  exact div_le_div_of_nonneg_right h2 (by positivity)

lemma spin_pow_add_exp_integrable {a B : ℝ} {X : Set (ℝ × ℝ)}
    (hX : X ⊆ spinConeB B) (meas : SpinCrossingMeasureOn a X) (k : ℕ) {β : ℝ} (hβ : 0 < β) :
    Integrable (fun p : ℝ × ℝ => (p.1 + p.2 + 2 * B) ^ k * Real.exp (-2 * π * β * (p.1 + p.2)))
      meas.ν := by
  obtain ⟨C, hC, hpoly⟩ := spin_poly_exp_le (by positivity : 0 < π * β) k
  have hae : ∀ᵐ p ∂meas.ν, p ∈ spinConeB B := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 meas.supp] with p hp
    by_contra hpB; exact hp (fun hpX => hpB (hX hpX))
  let C' : ℝ := C * Real.exp (2 * π * β * B)
  refine (meas.finite_laplace (half_pos hβ)).const_mul C' |>.mono'
    (by fun_prop : Continuous fun p : ℝ × ℝ =>
      (p.1 + p.2 + 2 * B) ^ k * Real.exp (-2 * π * β * (p.1 + p.2))).aestronglyMeasurable
    ?_
  filter_upwards [hae] with p hp
  have hsum : 0 ≤ p.1 + p.2 + 2 * B := by linarith [hp.1, hp.2]
  have h2 := hpoly (p.1 + p.2 + 2 * B) hsum
  have hmul : (p.1 + p.2 + 2 * B) ^ k * Real.exp (-π * β * (p.1 + p.2)) ≤ C' := by
    have h4 : (p.1 + p.2 + 2 * B) ^ k * Real.exp (-π * β * (p.1 + p.2)) =
        ((p.1 + p.2 + 2 * B) ^ k * Real.exp (-(π * β) * (p.1 + p.2 + 2 * B))) *
          Real.exp (2 * π * β * B) := by
      rw [mul_assoc ((p.1 + p.2 + 2 * B) ^ k), ← Real.exp_add]; congr 2; ring
    rw [h4]
    exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  have hsplit : Real.exp (-2 * π * β * (p.1 + p.2)) =
      Real.exp (-π * β * (p.1 + p.2)) * Real.exp (-2 * π * (β / 2) * (p.1 + p.2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hnn1 : 0 ≤ (p.1 + p.2 + 2 * B) ^ k * Real.exp (-2 * π * β * (p.1 + p.2)) := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hnn1]
  rw [hsplit, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hmul (Real.exp_pos _).le

lemma spin_diff_sq_exp_integrable {a B : ℝ} {X : Set (ℝ × ℝ)}
    (hX : X ⊆ spinConeB B) (meas : SpinCrossingMeasureOn a X) {β : ℝ} (hβ : 0 < β) :
    Integrable (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2 * Real.exp (-2 * π * β * (p.1 + p.2))) meas.ν := by
  have hae : ∀ᵐ p ∂meas.ν, p ∈ spinConeB B := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 meas.supp] with p hp
    by_contra hpB; exact hp (fun hpX => hpB (hX hpX))
  refine (spin_pow_add_exp_integrable hX meas 2 hβ).mono'
    (by fun_prop : Continuous fun p : ℝ × ℝ =>
      (p.1 - p.2) ^ 2 * Real.exp (-2 * π * β * (p.1 + p.2))).aestronglyMeasurable ?_
  filter_upwards [hae] with p hp
  have hsum : 0 ≤ p.1 + p.2 + 2 * B := by linarith [hp.1, hp.2]
  have hnn1 : 0 ≤ (p.1 - p.2) ^ 2 * Real.exp (-2 * π * β * (p.1 + p.2)) := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hnn1]
  exact mul_le_mul_of_nonneg_right (spin_diff_sq_le_of_mem_spinConeB hp) (Real.exp_pos _).le

lemma spin_sum_exp_integrable {a B : ℝ} (hB : 0 ≤ B) {X : Set (ℝ × ℝ)}
    (hX : X ⊆ spinConeB B) (meas : SpinCrossingMeasureOn a X) {β : ℝ} (hβ : 0 < β) :
    Integrable (fun p : ℝ × ℝ => (p.1 + p.2) * Real.exp (-2 * π * β * (p.1 + p.2))) meas.ν := by
  have hae : ∀ᵐ p ∂meas.ν, p ∈ spinConeB B := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 meas.supp] with p hp
    by_contra hpB; exact hp (fun hpX => hpB (hX hpX))
  refine (spin_pow_add_exp_integrable (hX.trans (spinConeB_subset_add (by linarith : B ≤ 2 * B))) meas 1 hβ).mono'
    (by fun_prop : Continuous fun p : ℝ × ℝ =>
      (p.1 + p.2) * Real.exp (-2 * π * β * (p.1 + p.2))).aestronglyMeasurable ?_
  filter_upwards [hae] with p hp
  have hsum : 0 ≤ p.1 + p.2 + 2 * (2 * B) := by linarith [hp.1, hp.2]
  have h1 : |p.1 + p.2| ≤ p.1 + p.2 + 2 * (2 * B) := by rw [abs_le]; constructor <;> linarith [hp.1, hp.2]
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), pow_one]
  exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le

lemma spinMomentMeasure_finite_laplace {a B : ℝ} {X : Set (ℝ × ℝ)}
    (hX : X ⊆ spinConeB B) (meas : SpinCrossingMeasureOn a X) {β : ℝ} (hβ : 0 < β) :
    Integrable (fun t : ℝ => Real.exp (-2 * π * β * t)) (spinMomentMeasure meas.ν) :=
  integrable_spinMomentMeasure_of_integrable (by fun_prop) (spin_diff_sq_exp_integrable hX meas hβ)

/-! ### Section 2: Transverse crossing equation `sd:eSD3` -/

/-- Total thermal transform `F_0(b) = ℒ(ν_0 + ν_v)(b)` (`spinning_airy_moment_proof.tex`). -/
noncomputable def spinMomentF0 (a : ℝ) (ν : Measure (ℝ × ℝ)) (b : ℝ) : ℝ :=
  (∫ p : ℝ × ℝ, Real.exp (-2 * π * b * (p.1 + p.2)) ∂ν) + spinVacuumV a b b

/-- Spin-square transform `Y(b) = (2π)² ℒ(M + M_v)(b)` with `M_v = -2 δ_{-a+1}`. -/
noncomputable def spinMomentY (a : ℝ) (ν : Measure (ℝ × ℝ)) (b : ℝ) : ℝ :=
  (2 * π) ^ 2 *
    ((∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 * Real.exp (-2 * π * b * (p.1 + p.2)) ∂ν) -
      2 * Real.exp (2 * π * (a - 1) * b))

/-- Differential operator `A f(b) = -f(b)/(2 b²) - f'(b)/b`. -/
noncomputable def spinOpA (f : ℝ → ℝ) (b : ℝ) : ℝ :=
  -f b / (2 * b ^ 2) - deriv f b / b

private lemma hasDerivAt_const_add_id (b h : ℝ) : HasDerivAt (fun x : ℝ => b + x) 1 h := by
  simpa using (hasDerivAt_id h).const_add b

private lemma hasDerivAt_const_sub_id (b h : ℝ) : HasDerivAt (fun x : ℝ => b - x) (-1) h := by
  simpa using (hasDerivAt_id h).const_sub b

private lemma hasDerivAt_spinThermalX_h1 (b tL tR h : ℝ) :
    HasDerivAt (fun h' : ℝ => Real.exp (-2 * π * ((b + h') * tL + (b - h') * tR)))
      (-2 * π * (tL - tR) * Real.exp (-2 * π * ((b + h) * tL + (b - h) * tR))) h := by
  have h1 : HasDerivAt (fun h' : ℝ => -2 * π * ((b + h') * tL + (b - h') * tR))
      (-2 * π * (tL - tR)) h :=
    ((((hasDerivAt_const_add_id b h).mul_const tL).add
      ((hasDerivAt_const_sub_id b h).mul_const tR)).const_mul (-2 * π)).congr_deriv (by ring)
  exact h1.exp.congr_deriv (by ring)

private lemma hasDerivAt_spinThermalX_h1d (b tL tR h : ℝ) :
    HasDerivAt
      (fun h' : ℝ => -2 * π * (tL - tR) * Real.exp (-2 * π * ((b + h') * tL + (b - h') * tR)))
      ((2 * π) ^ 2 * (tL - tR) ^ 2 * Real.exp (-2 * π * ((b + h) * tL + (b - h) * tR))) h :=
  ((hasDerivAt_spinThermalX_h1 b tL tR h).const_mul (-2 * π * (tL - tR))).congr_deriv (by ring)

private noncomputable def spinX2 (b tL tR h : ℝ) : ℝ :=
  ((b + h) * (b - h)) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * (tL / (b + h) + tR / (b - h)))

private noncomputable def spinX2Deriv (b tL tR h : ℝ) : ℝ :=
  (h * ((b + h) * (b - h)) ^ (-(3 / 2 : ℝ)) +
    ((b + h) * (b - h)) ^ (-(1 / 2 : ℝ)) * (2 * π * (tL / (b + h) ^ 2 - tR / (b - h) ^ 2))) *
    Real.exp (-2 * π * (tL / (b + h) + tR / (b - h)))

private noncomputable def spinX2Deriv2 (b tL tR h : ℝ) : ℝ :=
  (((b + h) * (b - h)) ^ (-(3 / 2 : ℝ)) + 3 * h ^ 2 * ((b + h) * (b - h)) ^ (-(5 / 2 : ℝ)) +
    2 * h * ((b + h) * (b - h)) ^ (-(3 / 2 : ℝ)) * (2 * π * (tL / (b + h) ^ 2 - tR / (b - h) ^ 2)) +
    ((b + h) * (b - h)) ^ (-(1 / 2 : ℝ)) *
      ((-4 * π * (tL / (b + h) ^ 3 + tR / (b - h) ^ 3)) +
        (2 * π * (tL / (b + h) ^ 2 - tR / (b - h) ^ 2)) ^ 2)) *
    Real.exp (-2 * π * (tL / (b + h) + tR / (b - h)))

private lemma hasDerivAt_spinX2 {b : ℝ} (tL tR : ℝ) {h : ℝ} (hh : h ∈ Ioo (-b / 2) (b / 2)) :
    HasDerivAt (spinX2 b tL tR) (spinX2Deriv b tL tR h) h := by
  have hp1 : 0 < b + h := by linarith [hh.1, hh.2]
  have hp2 : 0 < b - h := by linarith [hh.1, hh.2]
  have hprod : 0 < (b + h) * (b - h) := mul_pos hp1 hp2
  have hpoly : HasDerivAt (fun h' => (b + h') * (b - h')) (-2 * h) h :=
    ((hasDerivAt_const_add_id b h).mul (hasDerivAt_const_sub_id b h)).congr_deriv (by ring)
  have hu : HasDerivAt (fun h' => ((b + h') * (b - h')) ^ (-(1 / 2 : ℝ)))
      (h * ((b + h) * (b - h)) ^ (-(3 / 2 : ℝ))) h := by
    refine (hpoly.rpow_const (Or.inl hprod.ne')).congr_deriv ?_
    rw [show -(1 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) by norm_num]; ring
  have hdivL : HasDerivAt (fun h' => tL / (b + h')) (-tL / (b + h) ^ 2) h :=
    (((hasDerivAt_const_add_id b h).inv hp1.ne').const_mul tL |>.congr_of_eventuallyEq
      (Eventually.of_forall fun _ => by simp [div_eq_mul_inv])).congr_deriv (by ring)
  have hdivR : HasDerivAt (fun h' => tR / (b - h')) (tR / (b - h) ^ 2) h :=
    (((hasDerivAt_const_sub_id b h).inv hp2.ne').const_mul tR |>.congr_of_eventuallyEq
      (Eventually.of_forall fun _ => by simp [div_eq_mul_inv])).congr_deriv (by ring)
  have hE : HasDerivAt (fun h' => -2 * π * (tL / (b + h') + tR / (b - h')))
      (2 * π * (tL / (b + h) ^ 2 - tR / (b - h) ^ 2)) h :=
    ((hdivL.add hdivR).const_mul (-2 * π)).congr_deriv (by ring)
  exact (hu.mul hE.exp).congr_deriv (by dsimp [spinX2Deriv]; ring)

private lemma hasDerivAt_spinX2Deriv {b : ℝ} (tL tR : ℝ) {h : ℝ} (hh : h ∈ Ioo (-b / 2) (b / 2)) :
    HasDerivAt (spinX2Deriv b tL tR) (spinX2Deriv2 b tL tR h) h := by
  have hp1 : 0 < b + h := by linarith [hh.1, hh.2]
  have hp2 : 0 < b - h := by linarith [hh.1, hh.2]
  have hprod : 0 < (b + h) * (b - h) := mul_pos hp1 hp2
  have hpoly : HasDerivAt (fun h' => (b + h') * (b - h')) (-2 * h) h :=
    ((hasDerivAt_const_add_id b h).mul (hasDerivAt_const_sub_id b h)).congr_deriv (by ring)
  have hu1 : HasDerivAt (fun h' => ((b + h') * (b - h')) ^ (-(1 / 2 : ℝ)))
      (h * ((b + h) * (b - h)) ^ (-(3 / 2 : ℝ))) h := by
    refine (hpoly.rpow_const (Or.inl hprod.ne')).congr_deriv ?_
    rw [show -(1 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) by norm_num]; ring
  have hu3 : HasDerivAt (fun h' => ((b + h') * (b - h')) ^ (-(3 / 2 : ℝ)))
      (3 * h * ((b + h) * (b - h)) ^ (-(5 / 2 : ℝ))) h := by
    refine (hpoly.rpow_const (Or.inl hprod.ne')).congr_deriv ?_
    rw [show -(3 / 2 : ℝ) - 1 = -(5 / 2 : ℝ) by norm_num]; ring
  have hterm1 : HasDerivAt (fun h' => h' * ((b + h') * (b - h')) ^ (-(3 / 2 : ℝ)))
      (((b + h) * (b - h)) ^ (-(3 / 2 : ℝ)) + 3 * h ^ 2 * ((b + h) * (b - h)) ^ (-(5 / 2 : ℝ))) h :=
    ((hasDerivAt_id h).mul hu3).congr_deriv (by simp; ring)
  have hfL : HasDerivAt (fun h' => tL / (b + h') ^ 2) (-2 * tL / (b + h) ^ 3) h := by
    have hsq := (((hasDerivAt_const_add_id b h).fun_pow 2).congr_deriv (by ring : _ = 2 * (b + h)))
    refine (((hsq.inv (pow_ne_zero 2 hp1.ne')).const_mul tL).congr_of_eventuallyEq
      (Eventually.of_forall fun _ => by simp [div_eq_mul_inv])).congr_deriv (by field_simp)
  have hfR : HasDerivAt (fun h' => tR / (b - h') ^ 2) (2 * tR / (b - h) ^ 3) h := by
    have hsq := (((hasDerivAt_const_sub_id b h).fun_pow 2).congr_deriv (by ring : _ = -2 * (b - h)))
    refine (((hsq.inv (pow_ne_zero 2 hp2.ne')).const_mul tR).congr_of_eventuallyEq
      (Eventually.of_forall fun _ => by simp [div_eq_mul_inv])).congr_deriv (by field_simp)
  have hg : HasDerivAt (fun h' => 2 * π * (tL / (b + h') ^ 2 - tR / (b - h') ^ 2))
      (-4 * π * (tL / (b + h) ^ 3 + tR / (b - h) ^ 3)) h :=
    ((hfL.fun_sub hfR).const_mul (2 * π)).congr_deriv (by ring)
  have hdivL : HasDerivAt (fun h' => tL / (b + h')) (-tL / (b + h) ^ 2) h :=
    (((hasDerivAt_const_add_id b h).inv hp1.ne').const_mul tL |>.congr_of_eventuallyEq
      (Eventually.of_forall fun _ => by simp [div_eq_mul_inv])).congr_deriv (by ring)
  have hdivR : HasDerivAt (fun h' => tR / (b - h')) (tR / (b - h) ^ 2) h :=
    (((hasDerivAt_const_sub_id b h).inv hp2.ne').const_mul tR |>.congr_of_eventuallyEq
      (Eventually.of_forall fun _ => by simp [div_eq_mul_inv])).congr_deriv (by ring)
  have he : HasDerivAt (fun h' => Real.exp (-2 * π * (tL / (b + h') + tR / (b - h'))))
      (Real.exp (-2 * π * (tL / (b + h) + tR / (b - h))) *
        (2 * π * (tL / (b + h) ^ 2 - tR / (b - h) ^ 2))) h :=
    (((hdivL.fun_add hdivR).const_mul (-2 * π)).exp).congr_deriv (by ring)
  exact ((hterm1.fun_add (hu1.fun_mul hg)).fun_mul he).congr_deriv (by dsimp [spinX2Deriv2]; ring)

private lemma spinX2Deriv2_zero {b : ℝ} (hb : 0 < b) (tL tR : ℝ) :
    spinX2Deriv2 b tL tR 0 =
      (b ^ (-(3 : ℝ)) - 4 * π * (tL + tR) * b ^ (-(4 : ℝ)) +
        b ^ (-(5 : ℝ)) * (2 * π) ^ 2 * (tL - tR) ^ 2) *
        Real.exp (-2 * π * b⁻¹ * (tL + tR)) := by
  dsimp [spinX2Deriv2]
  simp only [add_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, zero_mul]
  have hb32 : (b * b) ^ (-(3 / 2 : ℝ)) = b ^ (-(3 : ℝ)) := by
    rw [← pow_two, ← Real.rpow_natCast b 2, ← Real.rpow_mul hb.le]; norm_num
  have hb12 : (b * b) ^ (-(1 / 2 : ℝ)) = b ^ (-(1 : ℝ)) := by
    rw [← pow_two, ← Real.rpow_natCast b 2, ← Real.rpow_mul hb.le]; norm_num
  rw [hb32, hb12]
  have h1 : b ^ (-(1 : ℝ)) = 1 / b := by rw [Real.rpow_neg hb.le, one_div, Real.rpow_one]
  have h3 : b ^ (-(3 : ℝ)) = 1 / b ^ 3 := by rw [Real.rpow_neg hb.le, one_div]; norm_cast
  have h4 : b ^ (-(4 : ℝ)) = 1 / b ^ 4 := by rw [Real.rpow_neg hb.le, one_div]; norm_cast
  have h5 : b ^ (-(5 : ℝ)) = 1 / b ^ 5 := by rw [Real.rpow_neg hb.le, one_div]; norm_cast
  have hexp : tL / b + tR / b = b⁻¹ * (tL + tR) := by ring
  rw [h1, h3, h4, h5, hexp]; field_simp [hb.ne']; ring

private lemma spinThermalXVac_eq_four_atoms (a βL βR : ℝ) :
    spinThermalXVac a βL βR =
      spinThermalX βL βR (-a / 2) (-a / 2) -
      spinThermalX βL βR (-a / 2) (-(a - 2) / 2) -
      spinThermalX βL βR (-(a - 2) / 2) (-a / 2) +
      spinThermalX βL βR (-(a - 2) / 2) (-(a - 2) / 2) := by
  unfold spinThermalXVac spinVacuumV spinVacuumQ spinThermalX
  have e1 : ∀ x y : ℝ, Real.exp (π * a * x) * Real.exp (π * a * y) =
      Real.exp (-2 * π * (x * (-a / 2) + y * (-a / 2))) := fun _ _ => by rw [← Real.exp_add]; congr 1; ring
  have e2 : ∀ x y : ℝ, Real.exp (π * a * x) * (Real.exp (π * a * y) * Real.exp (-2 * π * y)) =
      Real.exp (-2 * π * (x * (-a / 2) + y * (-(a - 2) / 2))) := fun _ _ => by
    simp only [← Real.exp_add]; congr 1; ring
  have e3 : ∀ x y : ℝ, (Real.exp (π * a * x) * Real.exp (-2 * π * x)) * Real.exp (π * a * y) =
      Real.exp (-2 * π * (x * (-(a - 2) / 2) + y * (-a / 2))) := fun _ _ => by
    simp only [← Real.exp_add]; congr 1; ring
  have e4 : ∀ x y : ℝ, (Real.exp (π * a * x) * Real.exp (-2 * π * x)) *
      (Real.exp (π * a * y) * Real.exp (-2 * π * y)) =
      Real.exp (-2 * π * (x * (-(a - 2) / 2) + y * (-(a - 2) / 2))) := fun _ _ => by
    simp only [← Real.exp_add]; congr 1; ring
  have d1 : ∀ x y : ℝ, (-a / 2) / x + (-a / 2) / y = x⁻¹ * (-a / 2) + y⁻¹ * (-a / 2) := fun _ _ => by ring
  have d2 : ∀ x y : ℝ, (-a / 2) / x + (-(a - 2) / 2) / y = x⁻¹ * (-a / 2) + y⁻¹ * (-(a - 2) / 2) :=
    fun _ _ => by ring
  have d3 : ∀ x y : ℝ, (-(a - 2) / 2) / x + (-a / 2) / y = x⁻¹ * (-(a - 2) / 2) + y⁻¹ * (-a / 2) :=
    fun _ _ => by ring
  have d4 : ∀ x y : ℝ, (-(a - 2) / 2) / x + (-(a - 2) / 2) / y =
      x⁻¹ * (-(a - 2) / 2) + y⁻¹ * (-(a - 2) / 2) := fun _ _ => by ring
  rw [d1 βL βR, d2 βL βR, d3 βL βR, d4 βL βR]
  have v1 : Real.exp (π * a * βL) * (1 - Real.exp (-2 * π * βL)) *
        (Real.exp (π * a * βR) * (1 - Real.exp (-2 * π * βR))) =
      Real.exp (-2 * π * (βL * (-a / 2) + βR * (-a / 2))) -
      Real.exp (-2 * π * (βL * (-a / 2) + βR * (-(a - 2) / 2))) -
      Real.exp (-2 * π * (βL * (-(a - 2) / 2) + βR * (-a / 2))) +
      Real.exp (-2 * π * (βL * (-(a - 2) / 2) + βR * (-(a - 2) / 2))) := by
    rw [← e1 βL βR, ← e2 βL βR, ← e3 βL βR, ← e4 βL βR]; ring
  have v2 : Real.exp (π * a * βL⁻¹) * (1 - Real.exp (-2 * π * βL⁻¹)) *
        (Real.exp (π * a * βR⁻¹) * (1 - Real.exp (-2 * π * βR⁻¹))) =
      Real.exp (-2 * π * (βL⁻¹ * (-a / 2) + βR⁻¹ * (-a / 2))) -
      Real.exp (-2 * π * (βL⁻¹ * (-a / 2) + βR⁻¹ * (-(a - 2) / 2))) -
      Real.exp (-2 * π * (βL⁻¹ * (-(a - 2) / 2) + βR⁻¹ * (-a / 2))) +
      Real.exp (-2 * π * (βL⁻¹ * (-(a - 2) / 2) + βR⁻¹ * (-(a - 2) / 2))) := by
    rw [← e1 βL⁻¹ βR⁻¹, ← e2 βL⁻¹ βR⁻¹, ← e3 βL⁻¹ βR⁻¹, ← e4 βL⁻¹ βR⁻¹]; ring
  rw [v1, v2]; ring

private lemma spin_cone_exp_dom {b : ℝ} (hb : 0 < b) {B : ℝ} (hB : 0 ≤ B)
    {p : ℝ × ℝ} (hp : p ∈ spinConeB B) {h : ℝ} (hh : h ∈ Ioo (-b / 2) (b / 2)) :
    -2 * π * ((b + h) * p.1 + (b - h) * p.2) ≤
      -2 * π * (b / 2) * (p.1 + p.2) + 4 * π * b * B ∧
    -2 * π * (p.1 / (b + h) + p.2 / (b - h)) ≤
      -2 * π * (2 / (3 * b)) * (p.1 + p.2) + 4 * π * B / b := by
  have hp1 : 0 ≤ p.1 + B := by linarith [hp.1]
  have hp2 : 0 ≤ p.2 + B := by linarith [hp.2]
  have hbh1 : b / 2 ≤ b + h := by linarith [hh.1]
  have hbh2 : b / 2 ≤ b - h := by linarith [hh.2]
  have hi1 : 2 / (3 * b) ≤ (b + h)⁻¹ := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by linarith)]; nlinarith [hh.2]
  have hi2 : 2 / (3 * b) ≤ (b - h)⁻¹ := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by linarith)]; nlinarith [hh.1]
  have hL' : (b + h)⁻¹ ≤ 2 / b := by rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) hb]; nlinarith
  have hR' : (b - h)⁻¹ ≤ 2 / b := by rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) hb]; nlinarith
  have h1a : (b / 2) * (p.1 + B) ≤ (b + h) * (p.1 + B) := mul_le_mul_of_nonneg_right hbh1 hp1
  have h1b : (b / 2) * (p.2 + B) ≤ (b - h) * (p.2 + B) := mul_le_mul_of_nonneg_right hbh2 hp2
  have h1 : (b / 2) * (p.1 + p.2) - 2 * b * B ≤ (b + h) * p.1 + (b - h) * p.2 := by
    have : (b + h) * (p.1 + B) + (b - h) * (p.2 + B) = (b + h) * p.1 + (b - h) * p.2 + 2 * b * B := by ring
    have : (b / 2) * (p.1 + B) + (b / 2) * (p.2 + B) = (b / 2) * (p.1 + p.2) + b * B := by ring
    linarith [mul_nonneg hb.le hB]
  have h2a : (2 / (3 * b)) * (p.1 + B) ≤ (b + h)⁻¹ * (p.1 + B) := mul_le_mul_of_nonneg_right hi1 hp1
  have h2b : (2 / (3 * b)) * (p.2 + B) ≤ (b - h)⁻¹ * (p.2 + B) := mul_le_mul_of_nonneg_right hi2 hp2
  have hLB : (b + h)⁻¹ * B ≤ (2 / b) * B := mul_le_mul_of_nonneg_right hL' hB
  have hRB : (b - h)⁻¹ * B ≤ (2 / b) * B := mul_le_mul_of_nonneg_right hR' hB
  have h2 : (2 / (3 * b)) * (p.1 + p.2) - 2 * B / b ≤ p.1 / (b + h) + p.2 / (b - h) := by
    have eL : (2 / (3 * b)) * (p.1 + p.2) + 4 * B / (3 * b) =
        (2 / (3 * b)) * (p.1 + B) + (2 / (3 * b)) * (p.2 + B) := by ring
    have eR : p.1 / (b + h) + p.2 / (b - h) + ((b + h)⁻¹ * B + (b - h)⁻¹ * B) =
        (b + h)⁻¹ * (p.1 + B) + (b - h)⁻¹ * (p.2 + B) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    have hsum2 : (2 / (3 * b)) * (p.1 + p.2) + 4 * B / (3 * b) ≤
        p.1 / (b + h) + p.2 / (b - h) + ((b + h)⁻¹ * B + (b - h)⁻¹ * B) := by linarith [add_le_add h2a h2b]
    have hinvsum : (b + h)⁻¹ + (b - h)⁻¹ ≤ 8 / (3 * b) := by
      have hh2 : h ^ 2 ≤ (b / 2) ^ 2 := by
        rw [sq_le_sq, abs_of_pos (half_pos hb)]
        rw [abs_le]; constructor <;> linarith [hh.1, hh.2]
      have hp_lo : 3 * b ^ 2 / 4 ≤ (b + h) * (b - h) := by nlinarith
      have hbh_pos : 0 < (b + h) * (b - h) := lt_of_lt_of_le (by positivity) hp_lo
      have e : (b + h)⁻¹ + (b - h)⁻¹ = 2 * b / ((b + h) * (b - h)) := by
        field_simp [show b + h ≠ 0 by linarith, show b - h ≠ 0 by linarith]; ring
      rw [e, div_le_div_iff₀ hbh_pos (by positivity)]
      nlinarith
    have hBsum : (b + h)⁻¹ * B + (b - h)⁻¹ * B ≤ 8 * B / (3 * b) := by
      calc _ = ((b + h)⁻¹ + (b - h)⁻¹) * B := by ring
        _ ≤ (8 / (3 * b)) * B := mul_le_mul_of_nonneg_right hinvsum hB
        _ = 8 * B / (3 * b) := by ring
    have hle2 : 4 * B / (3 * b) ≤ 2 * B / b := by rw [div_le_div_iff₀ (by positivity) hb]; nlinarith
    have hsub_id : 8 * B / (3 * b) - 4 * B / (3 * b) = 4 * B / (3 * b) := by ring
    linarith
  constructor
  · have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * π)
    nlinarith
  · have hmul := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * π)
    nlinarith [show 2 * π * (2 / (3 * b) * (p.1 + p.2) - 2 * B / b) =
        2 * π * (2 / (3 * b)) * (p.1 + p.2) - 4 * π * B / b by ring,
      show 2 * π * (p.1 / (b + h) + p.2 / (b - h)) =
        2 * π * (p.1 / (b + h) + p.2 / (b - h)) by ring]

private lemma spin_cone_dom_bounds {b B : ℝ} (hb : 0 < b) (hB : 0 ≤ B) :
    ∃ Cdom : ℝ, 0 ≤ Cdom ∧ ∀ p ∈ spinConeB B, ∀ h ∈ Metric.ball (0 : ℝ) (b / 2),
      |-2 * π * (p.1 - p.2) * Real.exp (-2 * π * ((b + h) * p.1 + (b - h) * p.2)) -
        spinX2Deriv b p.1 p.2 h| ≤
        Cdom * ((p.1 + p.2 + 2 * (2 * B + 1 / 2)) ^ 2 *
          Real.exp (-2 * π * min (b / 2) (2 / (3 * b)) * (p.1 + p.2))) ∧
      |(2 * π) ^ 2 * (p.1 - p.2) ^ 2 * Real.exp (-2 * π * ((b + h) * p.1 + (b - h) * p.2)) -
        spinX2Deriv2 b p.1 p.2 h| ≤
        Cdom * ((p.1 + p.2 + 2 * (2 * B + 1 / 2)) ^ 2 *
          Real.exp (-2 * π * min (b / 2) (2 / (3 * b)) * (p.1 + p.2))) := by
  let β_min := min (b / 2) (2 / (3 * b))
  let β_max := max (b / 2) (2 / (3 * b))
  let U0 := (3 * b ^ 2 / 4) ^ (-(1 / 2 : ℝ))
  let U3 := (3 * b ^ 2 / 4) ^ (-(3 / 2 : ℝ))
  let U5 := (3 * b ^ 2 / 4) ^ (-(5 / 2 : ℝ))
  let EB := Real.exp (4 * π * β_max * B)
  let E1 := Real.exp (4 * π * b * B) * EB
  let E2 := Real.exp (4 * π * B / b) * EB
  let C1d := 2 * π * E1 + (b / 2 * U3 + U0 * (2 * π * (8 / b ^ 2))) * E2
  let C2d := (2 * π) ^ 2 * E1 +
    (U3 + 3 * (b / 2) ^ 2 * U5 + 2 * (b / 2) * U3 * (2 * π * (8 / b ^ 2)) +
      U0 * (4 * π * (32 / b ^ 3) + (2 * π * (8 / b ^ 2)) ^ 2)) * E2
  refine ⟨max C1d C2d, le_max_of_le_left (by positivity), fun p hp h hh => ?_⟩
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt] at hh
  have hI : h ∈ Ioo (-b / 2) (b / 2) := ⟨by linarith, by linarith⟩
  have hcone := spin_cone_exp_dom hb hB hp hI
  let S := p.1 + p.2 + 2 * (2 * B + 1 / 2)
  have hS1 : 1 ≤ S := by dsimp [S]; linarith [hp.1, hp.2]
  have hS_nn : 0 ≤ S := by linarith
  have hdiff_S : |p.1 - p.2| ≤ S := (spin_diff_le_of_mem_spinConeB hp).trans (by dsimp [S]; linarith)
  have hdiff2_S2 : (p.1 - p.2) ^ 2 ≤ S ^ 2 :=
    (sq_abs _).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) hdiff_S 2)
  have hp1_S : |p.1| ≤ S := by rw [abs_le]; constructor <;> [dsimp [S]; dsimp [S]] <;> linarith [hp.1, hp.2]
  have hp2_S : |p.2| ≤ S := by rw [abs_le]; constructor <;> [dsimp [S]; dsimp [S]] <;> linarith [hp.1, hp.2]
  have h1_le_S2 : 1 ≤ S ^ 2 := by nlinarith
  have hS_le_S2 : S ≤ S ^ 2 := by nlinarith
  have hsum_pos : 0 ≤ p.1 + p.2 + 2 * B := by linarith [hp.1, hp.2]
  have hβ_min_nn : 0 ≤ β_min := le_min (half_pos hb).le (by positivity)
  have hexp_shift : ∀ {β' : ℝ}, β_min ≤ β' → β' ≤ β_max →
      Real.exp (-2 * π * β' * (p.1 + p.2)) ≤ EB * Real.exp (-2 * π * β_min * (p.1 + p.2)) := by
    intro β' hlo hhi
    have h1 : 0 ≤ (β' - β_min) * (p.1 + p.2 + 2 * B) := mul_nonneg (by linarith) hsum_pos
    have h2 : (β' - β_min) * (2 * B) ≤ β_max * (2 * B) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hx : β_min * (p.1 + p.2) - β' * (p.1 + p.2) ≤ 2 * β_max * B := by linarith
    have h3 : -2 * π * β' * (p.1 + p.2) ≤ 4 * π * β_max * B + -2 * π * β_min * (p.1 + p.2) := by
      have := mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ 2 * π); linarith
    calc Real.exp (-2 * π * β' * (p.1 + p.2))
        ≤ Real.exp (4 * π * β_max * B + -2 * π * β_min * (p.1 + p.2)) := Real.exp_le_exp.mpr h3
      _ = EB * Real.exp (-2 * π * β_min * (p.1 + p.2)) := Real.exp_add _ _
  have hK1_bd : Real.exp (-2 * π * ((b + h) * p.1 + (b - h) * p.2)) ≤
      E1 * Real.exp (-2 * π * β_min * (p.1 + p.2)) := by
    calc _ ≤ Real.exp (4 * π * b * B + -2 * π * (b / 2) * (p.1 + p.2)) := Real.exp_le_exp.mpr (by linarith [hcone.1])
      _ = Real.exp (4 * π * b * B) * Real.exp (-2 * π * (b / 2) * (p.1 + p.2)) := Real.exp_add _ _
      _ ≤ Real.exp (4 * π * b * B) * (EB * Real.exp (-2 * π * β_min * (p.1 + p.2))) := by
        gcongr; exact hexp_shift (min_le_left _ _) (le_max_left _ _)
      _ = E1 * Real.exp (-2 * π * β_min * (p.1 + p.2)) := by dsimp [E1]; ring
  have hE2_bd : Real.exp (-2 * π * (p.1 / (b + h) + p.2 / (b - h))) ≤
      E2 * Real.exp (-2 * π * β_min * (p.1 + p.2)) := by
    calc _ ≤ Real.exp (4 * π * B / b + -2 * π * (2 / (3 * b)) * (p.1 + p.2)) :=
          Real.exp_le_exp.mpr (by linarith [hcone.2])
      _ = Real.exp (4 * π * B / b) * Real.exp (-2 * π * (2 / (3 * b)) * (p.1 + p.2)) := Real.exp_add _ _
      _ ≤ Real.exp (4 * π * B / b) * (EB * Real.exp (-2 * π * β_min * (p.1 + p.2))) := by
        gcongr; exact hexp_shift (min_le_right _ _) (le_max_right _ _)
      _ = E2 * Real.exp (-2 * π * β_min * (p.1 + p.2)) := by dsimp [E2]; ring
  have hbh1 : b / 2 ≤ b + h := by linarith [hI.1]
  have hbh2 : b / 2 ≤ b - h := by linarith [hI.2]
  have hbh1_pos : 0 < b + h := by linarith [half_pos hb]
  have hbh2_pos : 0 < b - h := by linarith [half_pos hb]
  have hh_abs : |h| ≤ b / 2 := abs_le.mpr ⟨by linarith [hI.1], by linarith [hI.2]⟩
  have hh2 : h ^ 2 ≤ (b / 2) ^ 2 := by rw [sq_le_sq, abs_of_pos (half_pos hb)]; exact hh_abs
  have hprod_lo : 3 * b ^ 2 / 4 ≤ (b + h) * (b - h) := by
    have heq : (b + h) * (b - h) = b ^ 2 - h ^ 2 := by ring
    linarith [heq, hh2]
  have hprod_pos : 0 < (b + h) * (b - h) := mul_pos hbh1_pos hbh2_pos
  have hU0 : ((b + h) * (b - h)) ^ (-(1 / 2 : ℝ)) ≤ U0 :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hprod_lo (by norm_num)
  have hU3 : ((b + h) * (b - h)) ^ (-(3 / 2 : ℝ)) ≤ U3 :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hprod_lo (by norm_num)
  have hU5 : ((b + h) * (b - h)) ^ (-(5 / 2 : ℝ)) ≤ U5 :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hprod_lo (by norm_num)
  have hinv2L : 1 / (b + h) ^ 2 ≤ 4 / b ^ 2 := by
    have hsq : (b / 2) ^ 2 ≤ (b + h) ^ 2 := pow_le_pow_left₀ (by positivity) hbh1 2
    exact (one_div_le_one_div_of_le (sq_pos_of_pos (half_pos hb)) hsq).trans_eq (by ring)
  have hinv2R : 1 / (b - h) ^ 2 ≤ 4 / b ^ 2 := by
    have hsq : (b / 2) ^ 2 ≤ (b - h) ^ 2 := pow_le_pow_left₀ (by positivity) hbh2 2
    exact (one_div_le_one_div_of_le (sq_pos_of_pos (half_pos hb)) hsq).trans_eq (by ring)
  have hinv3L : 1 / (b + h) ^ 3 ≤ 8 / b ^ 3 := by
    have hcu : (b / 2) ^ 3 ≤ (b + h) ^ 3 := pow_le_pow_left₀ (by positivity) hbh1 3
    exact (one_div_le_one_div_of_le (pow_pos (half_pos hb) 3) hcu).trans_eq (by ring)
  have hinv3R : 1 / (b - h) ^ 3 ≤ 8 / b ^ 3 := by
    have hcu : (b / 2) ^ 3 ≤ (b - h) ^ 3 := pow_le_pow_left₀ (by positivity) hbh2 3
    exact (one_div_le_one_div_of_le (pow_pos (half_pos hb) 3) hcu).trans_eq (by ring)
  have hEp : |2 * π * (p.1 / (b + h) ^ 2 - p.2 / (b - h) ^ 2)| ≤ 2 * π * (8 / b ^ 2) * S := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * π)]
    have h1 : |p.1 / (b + h) ^ 2 - p.2 / (b - h) ^ 2| ≤
        |p.1| * (1 / (b + h) ^ 2) + |p.2| * (1 / (b - h) ^ 2) := by
      calc _ ≤ |p.1 / (b + h) ^ 2| + |p.2 / (b - h) ^ 2| := abs_sub _ _
        _ = |p.1| * (1 / (b + h) ^ 2) + |p.2| * (1 / (b - h) ^ 2) := by
            rw [abs_div, abs_div, abs_of_pos (sq_pos_of_pos hbh1_pos),
              abs_of_pos (sq_pos_of_pos hbh2_pos)]; ring
    have h2 : |p.1| * (1 / (b + h) ^ 2) + |p.2| * (1 / (b - h) ^ 2) ≤ S * (4 / b ^ 2) + S * (4 / b ^ 2) :=
      add_le_add (mul_le_mul hp1_S hinv2L (by positivity) hS_nn) (mul_le_mul hp2_S hinv2R (by positivity) hS_nn)
    have hle : |p.1 / (b + h) ^ 2 - p.2 / (b - h) ^ 2| ≤ 8 / b ^ 2 * S :=
      (h1.trans h2).trans_eq (by ring)
    exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans_eq (by ring)
  have hEpp : |-4 * π * (p.1 / (b + h) ^ 3 + p.2 / (b - h) ^ 3)| ≤ 4 * π * (16 / b ^ 3) * S := by
    rw [abs_mul, show |-4 * π| = 4 * π by rw [abs_mul, show |(-4 : ℝ)| = 4 by norm_num, abs_of_pos Real.pi_pos]]
    have h1 : |p.1 / (b + h) ^ 3 + p.2 / (b - h) ^ 3| ≤
        |p.1| * (1 / (b + h) ^ 3) + |p.2| * (1 / (b - h) ^ 3) := by
      calc _ ≤ |p.1 / (b + h) ^ 3| + |p.2 / (b - h) ^ 3| := abs_add_le _ _
        _ = |p.1| * (1 / (b + h) ^ 3) + |p.2| * (1 / (b - h) ^ 3) := by
            rw [abs_div, abs_div, abs_of_pos (pow_pos hbh1_pos 3),
              abs_of_pos (pow_pos hbh2_pos 3)]; ring
    have h2 : |p.1| * (1 / (b + h) ^ 3) + |p.2| * (1 / (b - h) ^ 3) ≤ S * (8 / b ^ 3) + S * (8 / b ^ 3) :=
      add_le_add (mul_le_mul hp1_S hinv3L (by positivity) hS_nn) (mul_le_mul hp2_S hinv3R (by positivity) hS_nn)
    have hle : |p.1 / (b + h) ^ 3 + p.2 / (b - h) ^ 3| ≤ 16 / b ^ 3 * S :=
      (h1.trans h2).trans_eq (by ring)
    exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans_eq (by ring)
  have hX2d_bd : |spinX2Deriv b p.1 p.2 h| ≤
      (b / 2 * U3 + U0 * (2 * π * (8 / b ^ 2))) * S ^ 2 *
        (E2 * Real.exp (-2 * π * β_min * (p.1 + p.2))) := by
    dsimp [spinX2Deriv]; rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have ha : |h * ((b + h) * (b - h)) ^ (-(3 / 2 : ℝ))| ≤ (b / 2) * U3 * S ^ 2 := by
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hprod_pos _)]
      exact (mul_le_mul hh_abs hU3 (by positivity) (by positivity)).trans
        (le_mul_of_one_le_right (by positivity) h1_le_S2)
    have hb' : |((b + h) * (b - h)) ^ (-(1 / 2 : ℝ)) * (2 * π * (p.1 / (b + h) ^ 2 - p.2 / (b - h) ^ 2))| ≤
        U0 * (2 * π * (8 / b ^ 2)) * S ^ 2 := by
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hprod_pos _)]
      calc _ ≤ U0 * (2 * π * (8 / b ^ 2) * S) := mul_le_mul hU0 hEp (abs_nonneg _) (by positivity)
        _ = (U0 * (2 * π * (8 / b ^ 2))) * S := by ring
        _ ≤ (U0 * (2 * π * (8 / b ^ 2))) * S ^ 2 := mul_le_mul_of_nonneg_left hS_le_S2 (by positivity)
    have hfront : |h * ((b + h) * (b - h)) ^ (-(3 / 2 : ℝ)) +
        ((b + h) * (b - h)) ^ (-(1 / 2 : ℝ)) * (2 * π * (p.1 / (b + h) ^ 2 - p.2 / (b - h) ^ 2))| ≤
        (b / 2 * U3 + U0 * (2 * π * (8 / b ^ 2))) * S ^ 2 :=
      ((abs_add_le _ _).trans (add_le_add ha hb')).trans_eq (by ring)
    exact mul_le_mul hfront hE2_bd (Real.exp_pos _).le (by positivity)
  have hEp2 : (2 * π * (p.1 / (b + h) ^ 2 - p.2 / (b - h) ^ 2)) ^ 2 ≤ (2 * π * (8 / b ^ 2)) ^ 2 * S ^ 2 := by
    calc _ = |2 * π * (p.1 / (b + h) ^ 2 - p.2 / (b - h) ^ 2)| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * π * (8 / b ^ 2) * S) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hEp 2
      _ = (2 * π * (8 / b ^ 2)) ^ 2 * S ^ 2 := by ring
  have hX2dd_bd : |spinX2Deriv2 b p.1 p.2 h| ≤
      (U3 + 3 * (b / 2) ^ 2 * U5 + 2 * (b / 2) * U3 * (2 * π * (8 / b ^ 2)) +
        U0 * (4 * π * (32 / b ^ 3) + (2 * π * (8 / b ^ 2)) ^ 2)) * S ^ 2 *
        (E2 * Real.exp (-2 * π * β_min * (p.1 + p.2))) := by
    dsimp [spinX2Deriv2]; rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have ht1 : |((b + h) * (b - h)) ^ (-(3 / 2 : ℝ)) + 3 * h ^ 2 * ((b + h) * (b - h)) ^ (-(5 / 2 : ℝ))| ≤
        (U3 + 3 * (b / 2) ^ 2 * U5) * S ^ 2 := by
      rw [abs_of_nonneg (by positivity)]
      have hsum12 : ((b + h) * (b - h)) ^ (-(3 / 2 : ℝ)) + 3 * h ^ 2 * ((b + h) * (b - h)) ^ (-(5 / 2 : ℝ)) ≤
          U3 + 3 * (b / 2) ^ 2 * U5 :=
        add_le_add hU3 (mul_le_mul (mul_le_mul_of_nonneg_left hh2 (by norm_num)) hU5 (by positivity) (by positivity))
      exact hsum12.trans (le_mul_of_one_le_right (by positivity) h1_le_S2)
    have ht2 : |2 * h * ((b + h) * (b - h)) ^ (-(3 / 2 : ℝ)) * (2 * π * (p.1 / (b + h) ^ 2 - p.2 / (b - h) ^ 2))| ≤
        2 * (b / 2) * U3 * (2 * π * (8 / b ^ 2)) * S ^ 2 := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (Real.rpow_pos_of_pos hprod_pos _)]
      have hm1 : 2 * |h| * ((b + h) * (b - h)) ^ (-(3 / 2 : ℝ)) ≤ 2 * (b / 2) * U3 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hh_abs (by norm_num)) hU3 (by positivity) (by positivity)
      have hm2 : 2 * |h| * ((b + h) * (b - h)) ^ (-(3 / 2 : ℝ)) *
          |2 * π * (p.1 / (b + h) ^ 2 - p.2 / (b - h) ^ 2)| ≤
          2 * (b / 2) * U3 * (2 * π * (8 / b ^ 2) * S) :=
        mul_le_mul hm1 hEp (abs_nonneg _) (by positivity)
      have hS1' : 2 * (b / 2) * U3 * (2 * π * (8 / b ^ 2)) * S ≤
          2 * (b / 2) * U3 * (2 * π * (8 / b ^ 2)) * S ^ 2 :=
        mul_le_mul_of_nonneg_left hS_le_S2 (by positivity)
      exact hm2.trans ((le_of_eq (by ring)).trans hS1')
    have ht3 : |((b + h) * (b - h)) ^ (-(1 / 2 : ℝ)) *
        ((-4 * π * (p.1 / (b + h) ^ 3 + p.2 / (b - h) ^ 3)) +
          (2 * π * (p.1 / (b + h) ^ 2 - p.2 / (b - h) ^ 2)) ^ 2)| ≤
        U0 * (4 * π * (32 / b ^ 3) + (2 * π * (8 / b ^ 2)) ^ 2) * S ^ 2 := by
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hprod_pos _)]
      have h16 : 4 * π * (16 / b ^ 3) ≤ 4 * π * (32 / b ^ 3) := by gcongr; norm_num
      have h1 : 4 * π * (16 / b ^ 3) * S ≤ 4 * π * (32 / b ^ 3) * S ^ 2 :=
        (mul_le_mul_of_nonneg_right h16 hS_nn).trans (mul_le_mul_of_nonneg_left hS_le_S2 (by positivity))
      have hEp2_abs : |(2 * π * (p.1 / (b + h) ^ 2 - p.2 / (b - h) ^ 2)) ^ 2| ≤
          (2 * π * (8 / b ^ 2)) ^ 2 * S ^ 2 := by
        rw [abs_of_nonneg (sq_nonneg _)]; exact hEp2
      have hsum_in : |-4 * π * (p.1 / (b + h) ^ 3 + p.2 / (b - h) ^ 3) +
          (2 * π * (p.1 / (b + h) ^ 2 - p.2 / (b - h) ^ 2)) ^ 2| ≤
          (4 * π * (32 / b ^ 3) + (2 * π * (8 / b ^ 2)) ^ 2) * S ^ 2 := by
        have hstep1 := (abs_add_le _ _).trans (add_le_add hEpp hEp2_abs)
        have hstep2 : 4 * π * (16 / b ^ 3) * S + (2 * π * (8 / b ^ 2)) ^ 2 * S ^ 2 ≤
            (4 * π * (32 / b ^ 3) + (2 * π * (8 / b ^ 2)) ^ 2) * S ^ 2 := by
          rw [add_mul]
          exact add_le_add h1 le_rfl
        exact hstep1.trans hstep2
      exact (mul_le_mul hU0 hsum_in (abs_nonneg _) (by positivity)).trans_eq (by ring)
    have hfront : |((b + h) * (b - h)) ^ (-(3 / 2 : ℝ)) + 3 * h ^ 2 * ((b + h) * (b - h)) ^ (-(5 / 2 : ℝ)) +
        2 * h * ((b + h) * (b - h)) ^ (-(3 / 2 : ℝ)) * (2 * π * (p.1 / (b + h) ^ 2 - p.2 / (b - h) ^ 2)) +
        ((b + h) * (b - h)) ^ (-(1 / 2 : ℝ)) *
          ((-4 * π * (p.1 / (b + h) ^ 3 + p.2 / (b - h) ^ 3)) +
            (2 * π * (p.1 / (b + h) ^ 2 - p.2 / (b - h) ^ 2)) ^ 2)| ≤
        (U3 + 3 * (b / 2) ^ 2 * U5 + 2 * (b / 2) * U3 * (2 * π * (8 / b ^ 2)) +
          U0 * (4 * π * (32 / b ^ 3) + (2 * π * (8 / b ^ 2)) ^ 2)) * S ^ 2 := by
      have hadd1 := (abs_add_le _ _).trans (add_le_add ht1 ht2)
      have hadd2 := (abs_add_le _ _).trans (add_le_add hadd1 ht3)
      exact hadd2.trans_eq (by ring)
    exact mul_le_mul hfront hE2_bd (Real.exp_pos _).le (by positivity)
  constructor
  · calc |-2 * π * (p.1 - p.2) * Real.exp (-2 * π * ((b + h) * p.1 + (b - h) * p.2)) - spinX2Deriv b p.1 p.2 h|
        ≤ 2 * π * |p.1 - p.2| * Real.exp (-2 * π * ((b + h) * p.1 + (b - h) * p.2)) + |spinX2Deriv b p.1 p.2 h| := by
          refine (abs_sub _ _).trans_eq ?_; congr 1
          rw [abs_mul, abs_mul, show |-2 * π| = 2 * π by rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num, abs_of_pos Real.pi_pos],
            abs_of_pos (Real.exp_pos _)]
      _ ≤ 2 * π * S * (E1 * Real.exp (-2 * π * β_min * (p.1 + p.2))) +
            (b / 2 * U3 + U0 * (2 * π * (8 / b ^ 2))) * S ^ 2 *
              (E2 * Real.exp (-2 * π * β_min * (p.1 + p.2))) :=
          add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hdiff_S (by positivity)) hK1_bd (Real.exp_pos _).le (by positivity)) hX2d_bd
      _ ≤ C1d * (S ^ 2 * Real.exp (-2 * π * β_min * (p.1 + p.2))) := by
          have h1 : 2 * π * S * (E1 * Real.exp (-2 * π * β_min * (p.1 + p.2))) ≤
              2 * π * S ^ 2 * (E1 * Real.exp (-2 * π * β_min * (p.1 + p.2))) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS_le_S2 (by positivity)) (by positivity)
          exact (add_le_add h1 le_rfl).trans_eq (by dsimp [C1d]; ring)
      _ ≤ max C1d C2d * (S ^ 2 * Real.exp (-2 * π * β_min * (p.1 + p.2))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · calc |(2 * π) ^ 2 * (p.1 - p.2) ^ 2 * Real.exp (-2 * π * ((b + h) * p.1 + (b - h) * p.2)) -
            spinX2Deriv2 b p.1 p.2 h|
        ≤ (2 * π) ^ 2 * (p.1 - p.2) ^ 2 * Real.exp (-2 * π * ((b + h) * p.1 + (b - h) * p.2)) +
            |spinX2Deriv2 b p.1 p.2 h| := by
          refine (abs_sub _ _).trans_eq ?_; congr 1
          rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _), abs_of_pos (Real.exp_pos _)]
      _ ≤ (2 * π) ^ 2 * S ^ 2 * (E1 * Real.exp (-2 * π * β_min * (p.1 + p.2))) +
            (U3 + 3 * (b / 2) ^ 2 * U5 + 2 * (b / 2) * U3 * (2 * π * (8 / b ^ 2)) +
              U0 * (4 * π * (32 / b ^ 3) + (2 * π * (8 / b ^ 2)) ^ 2)) * S ^ 2 *
              (E2 * Real.exp (-2 * π * β_min * (p.1 + p.2))) :=
          add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hdiff2_S2 (sq_nonneg _)) hK1_bd
            (Real.exp_pos _).le (by positivity)) hX2dd_bd
      _ = C2d * (S ^ 2 * Real.exp (-2 * π * β_min * (p.1 + p.2))) := by dsimp [C2d]; ring
      _ ≤ max C1d C2d * (S ^ 2 * Real.exp (-2 * π * β_min * (p.1 + p.2))) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

private lemma spinMomentF0_hasDerivAt {a B : ℝ} (hB : 0 ≤ B) {X : Set (ℝ × ℝ)}
    (hX : X ⊆ spinConeB B) (meas : SpinCrossingMeasureOn a X) {b : ℝ} (hb : 0 < b) :
    HasDerivAt (fun y : ℝ => ∫ p : ℝ × ℝ, Real.exp (-2 * π * y * (p.1 + p.2)) ∂meas.ν)
      (-2 * π * ∫ p : ℝ × ℝ, (p.1 + p.2) * Real.exp (-2 * π * b * (p.1 + p.2)) ∂meas.ν) b := by
  let β0 : ℝ := b / 2
  have hβ0 : 0 < β0 := half_pos hb
  have hF_meas : ∀ᶠ y in 𝓝 b,
      AEStronglyMeasurable (fun p : ℝ × ℝ => Real.exp (-2 * π * y * (p.1 + p.2))) meas.ν :=
    Eventually.of_forall fun y =>
      (by fun_prop : Continuous fun p : ℝ × ℝ => Real.exp (-2 * π * y * (p.1 + p.2))).aestronglyMeasurable
  have hF_int : Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * b * (p.1 + p.2))) meas.ν :=
    meas.finite_laplace hb
  have hF'_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => -2 * π * (p.1 + p.2) * Real.exp (-2 * π * b * (p.1 + p.2))) meas.ν :=
    (by fun_prop : Continuous fun p : ℝ × ℝ =>
      -2 * π * (p.1 + p.2) * Real.exp (-2 * π * b * (p.1 + p.2))).aestronglyMeasurable
  let bound : ℝ × ℝ → ℝ := fun p =>
    (2 * π * Real.exp (2 * π * b * (2 * B))) * (p.1 + p.2 + 2 * (2 * B)) *
      Real.exp (-2 * π * β0 * (p.1 + p.2))
  have hbound_int : Integrable bound meas.ν := by
    simpa [bound, pow_one, mul_assoc] using
      (spin_pow_add_exp_integrable (hX.trans (spinConeB_subset_add (by linarith : B ≤ 2 * B)))
        meas 1 hβ0).const_mul (2 * π * Real.exp (2 * π * b * (2 * B)))
  have hae : ∀ᵐ p ∂meas.ν, p ∈ spinConeB B := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 meas.supp] with p hp
    by_contra hpB; exact hp (fun hpX => hpB (hX hpX))
  have h_bound : ∀ᵐ p ∂meas.ν, ∀ y ∈ Metric.ball b (b / 2),
      ‖-2 * π * (p.1 + p.2) * Real.exp (-2 * π * y * (p.1 + p.2))‖ ≤ bound p := by
    filter_upwards [hae] with p hp y hy
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hy
    have hy_lo : β0 ≤ y := by dsimp [β0]; linarith
    have hsum : 0 ≤ p.1 + p.2 + 2 * (2 * B) := by linarith [hp.1, hp.2]
    have h1 : |p.1 + p.2| ≤ p.1 + p.2 + 2 * (2 * B) := by rw [abs_le]; constructor <;> linarith [hp.1, hp.2]
    have hexp : -2 * π * y * (p.1 + p.2) ≤ -2 * π * β0 * (p.1 + p.2) + 2 * π * b * (2 * B) := by
      have hp12 : β0 * (p.1 + p.2 + 2 * B) ≤ y * (p.1 + p.2 + 2 * B) :=
        mul_le_mul_of_nonneg_right hy_lo (by linarith [hp.1, hp.2])
      have hyB : (y - β0) * (2 * B) ≤ b * (2 * B) :=
        mul_le_mul_of_nonneg_right (by dsimp [β0]; linarith) (by positivity)
      have hx : β0 * (p.1 + p.2) - y * (p.1 + p.2) ≤ b * (2 * B) := by linarith
      have := mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ 2 * π); linarith
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      show |-2 * π| = 2 * π by rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num, abs_of_pos Real.pi_pos],
      abs_of_pos (Real.exp_pos _)]
    calc 2 * π * |p.1 + p.2| * Real.exp (-2 * π * y * (p.1 + p.2))
        ≤ 2 * π * (p.1 + p.2 + 2 * (2 * B)) *
            Real.exp (-2 * π * β0 * (p.1 + p.2) + 2 * π * b * (2 * B)) := by gcongr
      _ = bound p := by rw [Real.exp_add]; dsimp [bound]; ring
  have h_diff : ∀ᵐ p ∂meas.ν, ∀ y ∈ Metric.ball b (b / 2),
      HasDerivAt (fun y' : ℝ => Real.exp (-2 * π * y' * (p.1 + p.2)))
        (-2 * π * (p.1 + p.2) * Real.exp (-2 * π * y * (p.1 + p.2))) y :=
    Eventually.of_forall fun p y _ => by
      have hlin : HasDerivAt (fun y' : ℝ => -2 * π * y' * (p.1 + p.2)) (-2 * π * (p.1 + p.2)) y := by
        simpa [mul_assoc] using ((hasDerivAt_id y).const_mul (-2 * π)).mul_const (p.1 + p.2)
      exact hlin.exp.congr_deriv (by ring)
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds b (half_pos hb))
    hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  rw [show (fun p : ℝ × ℝ => -2 * π * (p.1 + p.2) * Real.exp (-2 * π * b * (p.1 + p.2))) =
      fun p => (-2 * π) * ((p.1 + p.2) * Real.exp (-2 * π * b * (p.1 + p.2))) by ext p; ring,
    integral_const_mul] at key
  exact key

/-- **Equation `(sd:eSD3)`** (`spinning_airy_moment_proof.tex`):
`(1 - S_5) Y = 2 A F_0` for any `SpinCrossingMeasureOn a X` (`X ⊆ E_B`) and `b > 0`. -/
theorem sd_eSD3 {a B : ℝ} (hB : 0 ≤ B) {X : Set (ℝ × ℝ)}
    (hX : X ⊆ spinConeB B) (meas : SpinCrossingMeasureOn a X) {b : ℝ} (hb : 0 < b) :
    spinMomentY a meas.ν b - b ^ (-(5 : ℝ)) * spinMomentY a meas.ν b⁻¹ =
      2 * spinOpA (spinMomentF0 a meas.ν) b := by
  have hF0_inv : ∀ {y : ℝ}, 0 < y → spinMomentF0 a meas.ν y = y⁻¹ * spinMomentF0 a meas.ν y⁻¹ := by
    intro y hy
    have hc := meas.crossing hy hy
    have hx : (fun p : ℝ × ℝ => spinThermalX y y p.1 p.2) =
        fun p : ℝ × ℝ => Real.exp (-2 * π * y * (p.1 + p.2)) -
          y⁻¹ * Real.exp (-2 * π * y⁻¹ * (p.1 + p.2)) := by
      ext p; unfold spinThermalX
      have hpow : (y * y) ^ (-(1 / 2 : ℝ)) = y⁻¹ := by
        rw [← pow_two, ← Real.rpow_natCast y 2, ← Real.rpow_mul hy.le]; norm_num; exact Real.rpow_neg_one y
      rw [hpow]; congr 1 <;> [ring_nf; ring_nf]
    rw [hx, integral_sub (meas.finite_laplace hy) ((meas.finite_laplace (inv_pos.mpr hy)).const_mul _),
      integral_const_mul] at hc
    unfold spinThermalXVac at hc
    have hpow : (y * y) ^ (-(1 / 2 : ℝ)) = y⁻¹ := by
      rw [← pow_two, ← Real.rpow_natCast y 2, ← Real.rpow_mul hy.le]; norm_num; exact Real.rpow_neg_one y
    rw [hpow] at hc
    unfold spinMomentF0; linarith
  have hvac_diff : ∀ {y : ℝ}, 0 < y →
      ∃ dvy : ℝ, HasDerivAt (fun x => spinVacuumV a x x) dvy y := fun {y} _ => by
    unfold spinVacuumV spinVacuumQ
    exact ⟨_, (((((hasDerivAt_id y).const_mul (π * a)).exp).mul
      ((hasDerivAt_const y 1).sub (((hasDerivAt_id y).const_mul (-2 * π)).exp))).mul
      ((((hasDerivAt_id y).const_mul (π * a)).exp).mul
      ((hasDerivAt_const y 1).sub (((hasDerivAt_id y).const_mul (-2 * π)).exp))))⟩
  have hF0_d_inv : HasDerivAt (spinMomentF0 a meas.ν)
      ((-2 * π * ∫ p : ℝ × ℝ, (p.1 + p.2) * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)) ∂meas.ν) +
        (hvac_diff (inv_pos.mpr hb)).choose) b⁻¹ :=
    (spinMomentF0_hasDerivAt hB hX meas (inv_pos.mpr hb)).add (hvac_diff (inv_pos.mpr hb)).choose_spec
  have hF0_d_b : HasDerivAt (spinMomentF0 a meas.ν)
      (-b ^ (-2 : ℤ) * spinMomentF0 a meas.ν b⁻¹ -
        b ^ (-3 : ℤ) * ((-2 * π * ∫ p : ℝ × ℝ, (p.1 + p.2) * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)) ∂meas.ν) +
          (hvac_diff (inv_pos.mpr hb)).choose)) b := by
    have hinv_b : HasDerivAt (fun x : ℝ => x⁻¹) (-b ^ (-2 : ℤ)) b :=
      (hasDerivAt_inv hb.ne').congr_deriv (by rw [zpow_neg]; norm_cast)
    have hmul := hinv_b.mul (hF0_d_inv.comp b hinv_b)
    have hev : (fun x : ℝ => x⁻¹ * spinMomentF0 a meas.ν x⁻¹) =ᶠ[𝓝 b] spinMomentF0 a meas.ν := by
      filter_upwards [eventually_gt_nhds hb] with y hy; exact (hF0_inv hy).symm
    refine (hmul.congr_of_eventuallyEq hev.symm).congr_deriv ?_
    have hz2 : b ^ (-2 : ℤ) = 1 / b ^ 2 := by rw [zpow_neg, one_div]; norm_cast
    have hz3 : b ^ (-3 : ℤ) = 1 / b ^ 3 := by rw [zpow_neg, one_div]; norm_cast
    have halg : ∀ (F I D : ℝ),
        -b ^ (-2 : ℤ) * F + b⁻¹ * ((I + D) * -b ^ (-2 : ℤ)) =
          -b ^ (-2 : ℤ) * F - b ^ (-3 : ℤ) * (I + D) := fun F I D => by
      rw [hz2, hz3]; field_simp [hb.ne']; ring
    dsimp only [Function.comp_def]
    exact halg (spinMomentF0 a meas.ν b⁻¹)
      (-2 * π * ∫ p : ℝ × ℝ, (p.1 + p.2) * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)) ∂meas.ν)
      (hvac_diff (inv_pos.mpr hb)).choose
  have hOpA_eq : 2 * spinOpA (spinMomentF0 a meas.ν) b =
      b ^ (-(3 : ℝ)) * spinMomentF0 a meas.ν b⁻¹ +
        2 * b ^ (-(4 : ℝ)) *
          ((-2 * π * ∫ p : ℝ × ℝ, (p.1 + p.2) * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)) ∂meas.ν) +
            (hvac_diff (inv_pos.mpr hb)).choose) := by
    unfold spinOpA; rw [hF0_inv hb, hF0_d_b.deriv]
    have hb3 : b ^ (-(3 : ℝ)) = 1 / b ^ 3 := by rw [Real.rpow_neg hb.le, one_div]; norm_cast
    have hb4 : b ^ (-(4 : ℝ)) = 1 / b ^ 4 := by rw [Real.rpow_neg hb.le, one_div]; norm_cast
    have hz2 : b ^ (-2 : ℤ) = 1 / b ^ 2 := by rw [zpow_neg, one_div]; norm_cast
    have hz3 : b ^ (-3 : ℤ) = 1 / b ^ 3 := by rw [zpow_neg, one_div]; norm_cast
    have halg : ∀ (F I D : ℝ),
        2 * (-(b⁻¹ * F) / (2 * b ^ 2) - (-b ^ (-2 : ℤ) * F - b ^ (-3 : ℤ) * (I + D)) / b) =
          b ^ (-(3 : ℝ)) * F + 2 * b ^ (-(4 : ℝ)) * (I + D) := fun F I D => by
      rw [hb3, hb4, hz2, hz3]; field_simp [hb.ne']; ring
    exact halg (spinMomentF0 a meas.ν b⁻¹)
      (-2 * π * ∫ p : ℝ × ℝ, (p.1 + p.2) * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)) ∂meas.ν)
      (hvac_diff (inv_pos.mpr hb)).choose
  let K1 : ℝ → ℝ × ℝ → ℝ := fun h p => Real.exp (-2 * π * ((b + h) * p.1 + (b - h) * p.2))
  let K2 : ℝ → ℝ × ℝ → ℝ := fun h p => spinX2 b p.1 p.2 h
  let Kd : ℝ → ℝ × ℝ → ℝ := fun h p => -2 * π * (p.1 - p.2) * K1 h p - spinX2Deriv b p.1 p.2 h
  let Kdd : ℝ → ℝ × ℝ → ℝ := fun h p => (2 * π) ^ 2 * (p.1 - p.2) ^ 2 * K1 h p - spinX2Deriv2 b p.1 p.2 h
  have hae : ∀ᵐ p ∂meas.ν, p ∈ spinConeB B := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 meas.supp] with p hp
    by_contra hpB; exact hp (fun hpX => hpB (hX hpX))
  have hmem_Ioo : ∀ {h : ℝ}, h ∈ Metric.ball (0 : ℝ) (b / 2) → h ∈ Ioo (-b / 2) (b / 2) := fun hh => by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt] at hh
    exact ⟨by linarith, by linarith⟩
  have hX12_int : ∀ h ∈ Metric.ball (0 : ℝ) (b / 2),
      Integrable (fun p : ℝ × ℝ => spinThermalX (b + h) (b - h) p.1 p.2) meas.ν := by
    intro h hh
    have hI := hmem_Ioo hh
    have h1 : Integrable (K1 h) meas.ν := by
      refine (meas.finite_laplace (half_pos hb)).const_mul (Real.exp (4 * π * b * B)) |>.mono'
        (by fun_prop : Continuous (K1 h)).aestronglyMeasurable ?_
      filter_upwards [hae] with p hp
      have hc := (spin_cone_exp_dom hb hB hp hI).1
      have hnn1 : 0 ≤ Real.exp (-2 * π * ((b + h) * p.1 + (b - h) * p.2)) := (Real.exp_pos _).le
      rw [Real.norm_eq_abs, abs_of_nonneg hnn1]
      calc Real.exp (-2 * π * ((b + h) * p.1 + (b - h) * p.2))
          ≤ Real.exp (4 * π * b * B + -2 * π * (b / 2) * (p.1 + p.2)) := Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp (4 * π * b * B) * Real.exp (-2 * π * (b / 2) * (p.1 + p.2)) := Real.exp_add _ _
    have h2 : Integrable (K2 h) meas.ν := by
      have hprod : 0 < ((b + h) * (b - h)) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_pos_of_pos (mul_pos (by linarith [hI.1]) (by linarith [hI.2])) _
      have hcontK2 : Continuous (K2 h) := by
        dsimp [K2, spinX2]
        exact continuous_const.mul (Real.continuous_exp.comp
          (continuous_const.mul ((continuous_fst.div_const _).add (continuous_snd.div_const _))))
      refine (meas.finite_laplace (by positivity : 0 < 2 / (3 * b))).const_mul
          (((b + h) * (b - h)) ^ (-(1 / 2 : ℝ)) * Real.exp (4 * π * B / b)) |>.mono'
        hcontK2.aestronglyMeasurable ?_
      filter_upwards [hae] with p hp
      have hc := (spin_cone_exp_dom hb hB hp hI).2
      dsimp [K2, spinX2]
      have hnn1 : 0 ≤ ((b + h) * (b - h)) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * (p.1 / (b + h) + p.2 / (b - h))) := by positivity
      simp only [abs_of_nonneg hnn1]
      calc ((b + h) * (b - h)) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * (p.1 / (b + h) + p.2 / (b - h)))
          ≤ ((b + h) * (b - h)) ^ (-(1 / 2 : ℝ)) *
              Real.exp (4 * π * B / b + -2 * π * (2 / (3 * b)) * (p.1 + p.2)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hprod.le
        _ = _ := by rw [Real.exp_add, ← mul_assoc]
    exact h1.sub h2
  obtain ⟨Cdom, hCdom_nn, hdom⟩ := spin_cone_dom_bounds hb hB
  let β_min := min (b / 2) (2 / (3 * b))
  have hβ_min : 0 < β_min := lt_min (half_pos hb) (by positivity)
  let domFun : ℝ × ℝ → ℝ := fun p =>
    Cdom * ((p.1 + p.2 + 2 * (2 * B + 1 / 2)) ^ 2 * Real.exp (-2 * π * β_min * (p.1 + p.2)))
  have hdom_int : Integrable domFun meas.ν :=
    (spin_pow_add_exp_integrable (hX.trans (spinConeB_subset_add (by linarith))) meas 2 hβ_min).const_mul Cdom
  have hKd_cont : ∀ y : ℝ, Continuous (Kd y) := fun y => by
    dsimp [Kd, K1, spinX2Deriv]; refine Continuous.sub (by fun_prop) ?_
    exact (continuous_const.add (continuous_const.mul (continuous_const.mul
      ((continuous_fst.div_const _).sub (continuous_snd.div_const _))))).mul
      (Real.continuous_exp.comp (continuous_const.mul ((continuous_fst.div_const _).add (continuous_snd.div_const _))))
  have hKdd_cont0 : Continuous (Kdd 0) := by
    dsimp [Kdd, K1, spinX2Deriv2]; refine Continuous.sub (by fun_prop) ?_
    have hc1 : Continuous (fun p : ℝ × ℝ => 2 * π * (p.1 / (b + 0) ^ 2 - p.2 / (b - 0) ^ 2)) :=
      continuous_const.mul ((continuous_fst.div_const _).sub (continuous_snd.div_const _))
    have hc2 : Continuous (fun p : ℝ × ℝ => -4 * π * (p.1 / (b + 0) ^ 3 + p.2 / (b - 0) ^ 3)) :=
      continuous_const.mul ((continuous_fst.div_const _).add (continuous_snd.div_const _))
    have hc3 : Continuous (fun p : ℝ × ℝ => Real.exp (-2 * π * (p.1 / (b + 0) + p.2 / (b - 0)))) :=
      Real.continuous_exp.comp (continuous_const.mul ((continuous_fst.div_const _).add (continuous_snd.div_const _)))
    exact ((continuous_const.add (continuous_const.mul hc1)).add
      (continuous_const.mul (hc2.add (hc1.pow 2)))).mul hc3
  have h_d1 : ∀ h ∈ Metric.ball (0 : ℝ) (b / 2),
      HasDerivAt (fun h' => ∫ p : ℝ × ℝ, spinThermalX (b + h') (b - h') p.1 p.2 ∂meas.ν)
        (∫ p : ℝ × ℝ, Kd h p ∂meas.ν) h := fun h hh => by
    have hK_cont : ∀ᶠ y in 𝓝 h,
        AEStronglyMeasurable (fun p : ℝ × ℝ => spinThermalX (b + y) (b - y) p.1 p.2) meas.ν :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hh) fun y hy => (hX12_int y hy).1
    have hdiff : ∀ᵐ p ∂meas.ν, ∀ y ∈ Metric.ball (0 : ℝ) (b / 2),
        HasDerivAt (fun y' => spinThermalX (b + y') (b - y') p.1 p.2) (Kd y p) y :=
      Eventually.of_forall fun p y hy =>
        (hasDerivAt_spinThermalX_h1 b p.1 p.2 y).sub (hasDerivAt_spinX2 p.1 p.2 (hmem_Ioo hy))
    have hbd : ∀ᵐ p ∂meas.ν, ∀ y ∈ Metric.ball (0 : ℝ) (b / 2), ‖Kd y p‖ ≤ domFun p := by
      filter_upwards [hae] with p hp y hy
      simpa [domFun, Kd, K1, Real.norm_eq_abs] using (hdom p hp y hy).1
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.isOpen_ball.mem_nhds hh)
      hK_cont (hX12_int h hh) (hKd_cont h).aestronglyMeasurable
      hbd hdom_int hdiff).2
  have hKd_int0 : Integrable (Kd 0) meas.ν := by
    refine hdom_int.mono' (hKd_cont 0).aestronglyMeasurable ?_
    filter_upwards [hae] with p hp
    simpa [domFun, Kd, K1, Real.norm_eq_abs] using (hdom p hp 0 (Metric.mem_ball_self (half_pos hb))).1
  have h_d2 : HasDerivAt (fun h' => ∫ p : ℝ × ℝ, Kd h' p ∂meas.ν)
      (∫ p : ℝ × ℝ, Kdd 0 p ∂meas.ν) 0 := by
    have hdiff : ∀ᵐ p ∂meas.ν, ∀ y ∈ Metric.ball (0 : ℝ) (b / 2),
        HasDerivAt (fun y' => Kd y' p) (Kdd y p) y :=
      Eventually.of_forall fun p y hy =>
        (hasDerivAt_spinThermalX_h1d b p.1 p.2 y).sub (hasDerivAt_spinX2Deriv p.1 p.2 (hmem_Ioo hy))
    have hbd : ∀ᵐ p ∂meas.ν, ∀ y ∈ Metric.ball (0 : ℝ) (b / 2), ‖Kdd y p‖ ≤ domFun p := by
      filter_upwards [hae] with p hp y hy
      simpa [domFun, Kdd, K1, Real.norm_eq_abs] using (hdom p hp y hy).2
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds 0 (half_pos hb))
      (Eventually.of_forall fun y => (hKd_cont y).aestronglyMeasurable) hKd_int0
      hKdd_cont0.aestronglyMeasurable hbd hdom_int hdiff).2
  have hvac_d1 : ∀ h ∈ Metric.ball (0 : ℝ) (b / 2),
      HasDerivAt (fun h' => spinThermalXVac a (b + h') (b - h'))
        (Kd h (-a / 2, -a / 2) - Kd h (-a / 2, -(a - 2) / 2) -
          Kd h (-(a - 2) / 2, -a / 2) + Kd h (-(a - 2) / 2, -(a - 2) / 2)) h := fun h hh => by
    have ha : ∀ tL tR, HasDerivAt (fun h' => spinThermalX (b + h') (b - h') tL tR) (Kd h (tL, tR)) h :=
      fun tL tR => (hasDerivAt_spinThermalX_h1 b tL tR h).sub (hasDerivAt_spinX2 tL tR (hmem_Ioo hh))
    have hsum := (((ha (-a / 2) (-a / 2)).fun_sub (ha (-a / 2) (-(a - 2) / 2))).fun_sub
      (ha (-(a - 2) / 2) (-a / 2))).fun_add (ha (-(a - 2) / 2) (-(a - 2) / 2))
    exact hsum.congr_of_eventuallyEq (Eventually.of_forall fun h' =>
      spinThermalXVac_eq_four_atoms a (b + h') (b - h'))
  have hvac_d2 : HasDerivAt
      (fun h' => Kd h' (-a / 2, -a / 2) - Kd h' (-a / 2, -(a - 2) / 2) -
        Kd h' (-(a - 2) / 2, -a / 2) + Kd h' (-(a - 2) / 2, -(a - 2) / 2))
      (Kdd 0 (-a / 2, -a / 2) - Kdd 0 (-a / 2, -(a - 2) / 2) -
        Kdd 0 (-(a - 2) / 2, -a / 2) + Kdd 0 (-(a - 2) / 2, -(a - 2) / 2)) 0 := by
    have ha : ∀ tL tR, HasDerivAt (fun h' => Kd h' (tL, tR)) (Kdd 0 (tL, tR)) 0 := fun tL tR =>
      (hasDerivAt_spinThermalX_h1d b tL tR 0).sub
        (hasDerivAt_spinX2Deriv tL tR (hmem_Ioo (Metric.mem_ball_self (half_pos hb))))
    exact (((ha (-a / 2) (-a / 2)).fun_sub (ha (-a / 2) (-(a - 2) / 2))).fun_sub
      (ha (-(a - 2) / 2) (-a / 2))).fun_add (ha (-(a - 2) / 2) (-(a - 2) / 2))
  have h_tot_zero : ∀ h ∈ Metric.ball (0 : ℝ) (b / 2),
      (∫ p : ℝ × ℝ, Kd h p ∂meas.ν) +
        (Kd h (-a / 2, -a / 2) - Kd h (-a / 2, -(a - 2) / 2) -
          Kd h (-(a - 2) / 2, -a / 2) + Kd h (-(a - 2) / 2, -(a - 2) / 2)) = 0 := by
    intro h hh
    have hd := (h_d1 h hh).fun_add (hvac_d1 h hh)
    have hzero : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 h] fun h' =>
        (∫ p : ℝ × ℝ, spinThermalX (b + h') (b - h') p.1 p.2 ∂meas.ν) +
        spinThermalXVac a (b + h') (b - h') := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hh] with y hy
      have hI := hmem_Ioo hy
      rw [meas.crossing (by linarith [hI.1]) (by linarith [hI.2]), neg_add_cancel]
    exact (hd.congr_of_eventuallyEq hzero).unique (hasDerivAt_const h 0)
  have h_tot_d2 : (∫ p : ℝ × ℝ, Kdd 0 p ∂meas.ν) +
      (Kdd 0 (-a / 2, -a / 2) - Kdd 0 (-a / 2, -(a - 2) / 2) -
        Kdd 0 (-(a - 2) / 2, -a / 2) + Kdd 0 (-(a - 2) / 2, -(a - 2) / 2)) = 0 := by
    have hd := h_d2.fun_add hvac_d2
    have hzero : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 0] fun h' =>
        (∫ p : ℝ × ℝ, Kd h' p ∂meas.ν) +
        (Kd h' (-a / 2, -a / 2) - Kd h' (-a / 2, -(a - 2) / 2) -
          Kd h' (-(a - 2) / 2, -a / 2) + Kd h' (-(a - 2) / 2, -(a - 2) / 2)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (half_pos hb))] with y hy
      exact (h_tot_zero y hy).symm
    exact (hd.congr_of_eventuallyEq hzero).unique (hasDerivAt_const 0 0)
  have hKdd_expand : ∀ tL tR : ℝ,
      Kdd 0 (tL, tR) =
        (2 * π) ^ 2 * (tL - tR) ^ 2 * Real.exp (-2 * π * b * (tL + tR)) -
        b ^ (-(5 : ℝ)) * (2 * π) ^ 2 * (tL - tR) ^ 2 * Real.exp (-2 * π * b⁻¹ * (tL + tR)) -
        (b ^ (-(3 : ℝ)) * Real.exp (-2 * π * b⁻¹ * (tL + tR)) -
          4 * π * (tL + tR) * b ^ (-(4 : ℝ)) * Real.exp (-2 * π * b⁻¹ * (tL + tR))) := by
    intro tL tR; dsimp [Kdd, K1]; rw [spinX2Deriv2_zero hb tL tR]
    simp only [add_zero, sub_zero]; rw [show b * tL + b * tR = b * (tL + tR) by ring]; ring
  have hInt1 : Integrable (fun p : ℝ × ℝ => (2 * π) ^ 2 * (p.1 - p.2) ^ 2 * Real.exp (-2 * π * b * (p.1 + p.2))) meas.ν :=
    ((spin_diff_sq_exp_integrable hX meas hb).const_mul ((2 * π) ^ 2)).congr (Eventually.of_forall fun p => by ring)
  have hInt2 : Integrable (fun p : ℝ × ℝ => b ^ (-(5 : ℝ)) * (2 * π) ^ 2 * (p.1 - p.2) ^ 2 *
      Real.exp (-2 * π * b⁻¹ * (p.1 + p.2))) meas.ν :=
    ((spin_diff_sq_exp_integrable hX meas (inv_pos.mpr hb)).const_mul (b ^ (-(5 : ℝ)) * (2 * π) ^ 2)).congr
      (Eventually.of_forall fun p => by ring)
  have hInt3 : Integrable (fun p : ℝ × ℝ => b ^ (-(3 : ℝ)) * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2))) meas.ν :=
    (meas.finite_laplace (inv_pos.mpr hb)).const_mul _
  have hInt4 : Integrable (fun p : ℝ × ℝ => 4 * π * (p.1 + p.2) * b ^ (-(4 : ℝ)) * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2))) meas.ν :=
    ((spin_sum_exp_integrable hB hX meas (inv_pos.mpr hb)).const_mul (4 * π * b ^ (-(4 : ℝ)))).congr
      (Eventually.of_forall fun p => by ring)
  have hIntKdd : ∫ p : ℝ × ℝ, Kdd 0 p ∂meas.ν =
      (2 * π) ^ 2 * (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 * Real.exp (-2 * π * b * (p.1 + p.2)) ∂meas.ν) -
      b ^ (-(5 : ℝ)) * (2 * π) ^ 2 * (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)) ∂meas.ν) -
      (b ^ (-(3 : ℝ)) * (∫ p : ℝ × ℝ, Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)) ∂meas.ν) -
        4 * π * b ^ (-(4 : ℝ)) * (∫ p : ℝ × ℝ, (p.1 + p.2) * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)) ∂meas.ν)) := by
    have heq : (fun p : ℝ × ℝ => Kdd 0 p) = fun p =>
        ((2 * π) ^ 2 * (p.1 - p.2) ^ 2 * Real.exp (-2 * π * b * (p.1 + p.2)) -
          b ^ (-(5 : ℝ)) * (2 * π) ^ 2 * (p.1 - p.2) ^ 2 * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2))) -
        (b ^ (-(3 : ℝ)) * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)) -
          4 * π * (p.1 + p.2) * b ^ (-(4 : ℝ)) * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2))) := by
      ext p; exact hKdd_expand p.1 p.2
    rw [heq]
    rw [integral_sub (f := fun p : ℝ × ℝ =>
        (2 * π) ^ 2 * (p.1 - p.2) ^ 2 * Real.exp (-2 * π * b * (p.1 + p.2)) -
          b ^ (-(5 : ℝ)) * (2 * π) ^ 2 * (p.1 - p.2) ^ 2 * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)))
      (g := fun p : ℝ × ℝ =>
        b ^ (-(3 : ℝ)) * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)) -
          4 * π * (p.1 + p.2) * b ^ (-(4 : ℝ)) * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)))
      (hInt1.sub hInt2) (hInt3.sub hInt4)]
    rw [integral_sub (f := fun p : ℝ × ℝ =>
        (2 * π) ^ 2 * (p.1 - p.2) ^ 2 * Real.exp (-2 * π * b * (p.1 + p.2)))
      (g := fun p : ℝ × ℝ =>
        b ^ (-(5 : ℝ)) * (2 * π) ^ 2 * (p.1 - p.2) ^ 2 * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)))
      hInt1 hInt2]
    rw [integral_sub (f := fun p : ℝ × ℝ => b ^ (-(3 : ℝ)) * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)))
      (g := fun p : ℝ × ℝ =>
        4 * π * (p.1 + p.2) * b ^ (-(4 : ℝ)) * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)))
      hInt3 hInt4]
    have e1 : ∫ p : ℝ × ℝ, (2 * π) ^ 2 * (p.1 - p.2) ^ 2 * Real.exp (-2 * π * b * (p.1 + p.2)) ∂meas.ν =
        (2 * π) ^ 2 * ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 * Real.exp (-2 * π * b * (p.1 + p.2)) ∂meas.ν := by
      rw [← integral_const_mul]; congr 1; ext p; ring
    have e2 : ∫ p : ℝ × ℝ, b ^ (-(5 : ℝ)) * (2 * π) ^ 2 * (p.1 - p.2) ^ 2 *
          Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)) ∂meas.ν =
        b ^ (-(5 : ℝ)) * (2 * π) ^ 2 * ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 *
          Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)) ∂meas.ν := by
      rw [← integral_const_mul]; congr 1; ext p; ring
    have e3 : ∫ p : ℝ × ℝ, b ^ (-(3 : ℝ)) * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)) ∂meas.ν =
        b ^ (-(3 : ℝ)) * ∫ p : ℝ × ℝ, Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)) ∂meas.ν :=
      integral_const_mul _ _
    have e4 : ∫ p : ℝ × ℝ, 4 * π * (p.1 + p.2) * b ^ (-(4 : ℝ)) * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)) ∂meas.ν =
        4 * π * b ^ (-(4 : ℝ)) * ∫ p : ℝ × ℝ, (p.1 + p.2) * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)) ∂meas.ν := by
      rw [← integral_const_mul]; congr 1; ext p; ring
    rw [e1, e2, e3, e4]
  have hV_eq : (fun x : ℝ => spinVacuumV a x x) = fun x =>
      Real.exp (2 * π * a * x) - 2 * Real.exp (2 * π * (a - 1) * x) + Real.exp (2 * π * (a - 2) * x) := by
    ext x; unfold spinVacuumV spinVacuumQ
    have h1 : Real.exp (π * a * x) * Real.exp (π * a * x) = Real.exp (2 * π * a * x) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (π * a * x) * Real.exp (-2 * π * x) * Real.exp (π * a * x) =
        Real.exp (2 * π * (a - 1) * x) := by simp only [← Real.exp_add]; congr 1; ring
    have h3 : Real.exp (π * a * x) * Real.exp (-2 * π * x) *
        (Real.exp (π * a * x) * Real.exp (-2 * π * x)) = Real.exp (2 * π * (a - 2) * x) := by
      simp only [← Real.exp_add]; congr 1; ring
    calc Real.exp (π * a * x) * (1 - Real.exp (-2 * π * x)) *
          (Real.exp (π * a * x) * (1 - Real.exp (-2 * π * x)))
        = Real.exp (π * a * x) * Real.exp (π * a * x) -
            2 * (Real.exp (π * a * x) * Real.exp (-2 * π * x) * Real.exp (π * a * x)) +
            Real.exp (π * a * x) * Real.exp (-2 * π * x) *
              (Real.exp (π * a * x) * Real.exp (-2 * π * x)) := by ring
      _ = _ := by rw [h1, h2, h3]
  have hvac_4_deriv : (hvac_diff (inv_pos.mpr hb)).choose =
      2 * π * (a * Real.exp (2 * π * a * b⁻¹) - 2 * (a - 1) * Real.exp (2 * π * (a - 1) * b⁻¹) +
        (a - 2) * Real.exp (2 * π * (a - 2) * b⁻¹)) := by
    have hd_expl : HasDerivAt (fun x : ℝ => spinVacuumV a x x)
        (2 * π * (a * Real.exp (2 * π * a * b⁻¹) - 2 * (a - 1) * Real.exp (2 * π * (a - 1) * b⁻¹) +
          (a - 2) * Real.exp (2 * π * (a - 2) * b⁻¹))) b⁻¹ := by
      have d1 := ((hasDerivAt_id b⁻¹).const_mul (2 * π * a)).exp
      have d2 := (((hasDerivAt_id b⁻¹).const_mul (2 * π * (a - 1))).exp).const_mul 2
      have d3 := ((hasDerivAt_id b⁻¹).const_mul (2 * π * (a - 2))).exp
      rw [hV_eq]
      exact ((d1.fun_sub d2).fun_add d3).congr_deriv (by simp; ring)
    exact (hvac_diff (inv_pos.mpr hb)).choose_spec.unique hd_expl
  have hvac_Kdd_eq : Kdd 0 (-a / 2, -a / 2) - Kdd 0 (-a / 2, -(a - 2) / 2) -
      Kdd 0 (-(a - 2) / 2, -a / 2) + Kdd 0 (-(a - 2) / 2, -(a - 2) / 2) =
      (2 * π) ^ 2 * (-2 * Real.exp (2 * π * (a - 1) * b)) -
        b ^ (-(5 : ℝ)) * (2 * π) ^ 2 * (-2 * Real.exp (2 * π * (a - 1) * b⁻¹)) -
        (b ^ (-(3 : ℝ)) * spinVacuumV a b⁻¹ b⁻¹ + 2 * b ^ (-(4 : ℝ)) * (hvac_diff (inv_pos.mpr hb)).choose) := by
    rw [hKdd_expand, hKdd_expand, hKdd_expand, hKdd_expand, hvac_4_deriv, congrFun hV_eq b⁻¹]
    rw [show (-a / 2 + -a / 2 : ℝ) = -a by ring,
      show (-a / 2 + -(a - 2) / 2 : ℝ) = -(a - 1) by ring,
      show (-(a - 2) / 2 + -a / 2 : ℝ) = -(a - 1) by ring,
      show (-(a - 2) / 2 + -(a - 2) / 2 : ℝ) = -(a - 2) by ring,
      show (-a / 2 - -a / 2 : ℝ) = 0 by ring,
      show (-a / 2 - -(a - 2) / 2 : ℝ) = -1 by ring,
      show (-(a - 2) / 2 - -a / 2 : ℝ) = 1 by ring,
      show (-(a - 2) / 2 - -(a - 2) / 2 : ℝ) = 0 by ring,
      show -2 * π * b * -a = 2 * π * a * b by ring,
      show -2 * π * b * -(a - 1) = 2 * π * (a - 1) * b by ring,
      show -2 * π * b * -(a - 2) = 2 * π * (a - 2) * b by ring,
      show -2 * π * b⁻¹ * -a = 2 * π * a * b⁻¹ by ring,
      show -2 * π * b⁻¹ * -(a - 1) = 2 * π * (a - 1) * b⁻¹ by ring,
      show -2 * π * b⁻¹ * -(a - 2) = 2 * π * (a - 2) * b⁻¹ by ring]
    ring
  rw [hIntKdd, hvac_Kdd_eq] at h_tot_d2
  unfold spinMomentY
  rw [hOpA_eq]
  unfold spinMomentF0
  linarith

/-- info: 'FormalResearch.ModularBootstrap.Spin.sd_eSD3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sd_eSD3

end FormalResearch.ModularBootstrap.Spin
