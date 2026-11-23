module

public import FormalResearch.Special.BesselNormalized
public import FormalResearch.Special.JacobiBeta

/-!
# The Poisson integral of the real-order Bessel function

For real `ν > -1/2` (`DLMF 10.9.4`):
`besselNorm ν x = Γ(ν+1) / (√π Γ(ν+1/2)) ∫_{-1}^1 (1-t²)^{ν-1/2} cos (x t) dt`,
proved by expanding `cos` and integrating termwise against the Beta integral.  Consequently
`|besselNorm ν x| ≤ 1`.
-/

@[expose] public section

open MeasureTheory intervalIntegral Set
open scoped Nat Interval Real

namespace FormalResearch.Special

/-- The weight `(1 - t²)^a` is interval integrable on `[-1,1]` for `a > -1`. -/
lemma intervalIntegrable_one_sub_sq_rpow_neg {a : ℝ} (ha : -1 < a) :
    IntervalIntegrable (fun t : ℝ => (1 - t ^ 2) ^ a) volume (-1) 1 := by
  refine (jacobiW_intervalIntegrable ha ha).congr ?_
  intro t ht
  rw [uIoc_of_le (by norm_num)] at ht
  unfold jacobiW
  rw [← Real.mul_rpow (by linarith [ht.2]) (by linarith [ht.1])]
  congr 1
  ring

/-- The weight `(1 - t²)^a` is interval integrable on `[0,1]` for `a > -1`. -/
lemma intervalIntegrable_one_sub_sq_rpow {a : ℝ} (ha : -1 < a) :
    IntervalIntegrable (fun t : ℝ => (1 - t ^ 2) ^ a) volume 0 1 :=
  (intervalIntegrable_one_sub_sq_rpow_neg ha).mono_set
    (by rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
        exact Icc_subset_Icc (by norm_num) le_rfl)

/-- The moments of the weight: for `a > -1`,
`∫_0^1 (1-t²)^a t^{2k} dt = Γ(k+1/2) Γ(a+1) / (2 Γ(k+a+3/2))`. -/
theorem integral_one_sub_sq_rpow_mul_pow {a : ℝ} (ha : -1 < a) (k : ℕ) :
    ∫ t in (0 : ℝ)..1, (1 - t ^ 2) ^ a * t ^ (2 * k) =
      Real.Gamma (k + 1 / 2) * Real.Gamma (a + 1) / (2 * Real.Gamma (k + a + 3 / 2)) := by
  set g : ℝ → ℝ := fun y => y ^ ((k : ℝ) + 1 / 2 - 1) * (1 - y) ^ (a + 1 - 1) with hg
  have hu : (0 : ℝ) < k + 1 / 2 := by positivity
  have hv : (0 : ℝ) < a + 1 := by linarith
  have hB := real_betaIntegral hu hv
  have hBpos : 0 < Real.Gamma (k + 1 / 2) * Real.Gamma (a + 1) / Real.Gamma (k + 1 / 2 + (a + 1)) :=
    div_pos (mul_pos (Real.Gamma_pos_of_pos hu) (Real.Gamma_pos_of_pos hv))
      (Real.Gamma_pos_of_pos (by linarith))
  have hgint : IntervalIntegrable g volume 0 1 := by
    by_contra hnot
    have := intervalIntegral.integral_undef hnot
    rw [hg] at this
    rw [this] at hB
    linarith
  have hgI : IntegrableOn g (Icc 0 1) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hgint
  -- the pointwise identity on `(0,1]`
  have hpt : ∀ t ∈ Ioc (0 : ℝ) 1, (g ∘ fun t : ℝ => t ^ 2) t * (2 * t) =
      2 * ((1 - t ^ 2) ^ a * t ^ (2 * k)) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    simp only [Function.comp, hg, add_sub_cancel_right]
    have h1 : (t ^ 2) ^ ((k : ℝ) + 1 / 2 - 1) * t = t ^ (2 * k) := by
      rw [← Real.rpow_two, ← Real.rpow_mul ht0.le, ← Real.rpow_add_one ht0.ne']
      rw [show 2 * ((k : ℝ) + 1 / 2 - 1) + 1 = ((2 * k : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    calc (t ^ 2) ^ ((k : ℝ) + 1 / 2 - 1) * (1 - t ^ 2) ^ a * (2 * t)
        = 2 * ((1 - t ^ 2) ^ a * ((t ^ 2) ^ ((k : ℝ) + 1 / 2 - 1) * t)) := by ring
      _ = _ := by rw [h1]
  have hW : IntegrableOn (fun t : ℝ => (1 - t ^ 2) ^ a * t ^ (2 * k)) (Ioc 0 1) := by
    have h := (intervalIntegrable_one_sub_sq_rpow ha).mul_continuousOn
      (g := fun t : ℝ => t ^ (2 * k)) (by fun_prop)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h
  have hsub : ∫ t in (0 : ℝ)..1, (g ∘ fun t : ℝ => t ^ 2) t * (2 * t) =
      ∫ u in (0 ^ 2 : ℝ)..1 ^ 2, g u := by
    refine intervalIntegral.integral_comp_mul_deriv''' (f := fun t : ℝ => t ^ 2)
      (f' := fun t => 2 * t) (by fun_prop) ?_ ?_ ?_ ?_
    · intro x hx
      exact ((hasDerivAt_pow 2 x).hasDerivWithinAt).congr_deriv (by simp)
    · rw [min_eq_left zero_le_one, max_eq_right zero_le_one]
      refine ContinuousOn.mono ?_ (show (fun t : ℝ => t ^ 2) '' Ioo 0 1 ⊆ Ioo 0 1 from ?_)
      · refine ContinuousOn.mul (ContinuousOn.rpow_const continuousOn_id fun y hy => Or.inl hy.1.ne')
          (ContinuousOn.rpow_const (by fun_prop) fun y hy => Or.inl (by linarith [hy.2]))
      · rintro _ ⟨t, ht, rfl⟩
        exact ⟨by nlinarith [ht.1], by nlinarith [ht.1, ht.2]⟩
    · refine hgI.mono_set ?_
      rw [uIcc_of_le zero_le_one]
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨by nlinarith [ht.1], by nlinarith [ht.1, ht.2]⟩
    · rw [uIcc_of_le zero_le_one, integrableOn_Icc_iff_integrableOn_Ioc]
      exact IntegrableOn.congr_fun (show IntegrableOn
        (fun t : ℝ => 2 * ((1 - t ^ 2) ^ a * t ^ (2 * k))) (Ioc 0 1) volume from hW.const_mul 2)
        (fun t ht => (hpt t ht).symm) measurableSet_Ioc
  have hlhs : ∫ t in (0 : ℝ)..1, (g ∘ fun t : ℝ => t ^ 2) t * (2 * t) =
      2 * ∫ t in (0 : ℝ)..1, (1 - t ^ 2) ^ a * t ^ (2 * k) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [uIoc_of_le zero_le_one] at ht
    exact hpt t ht
  rw [hlhs] at hsub
  norm_num at hsub
  rw [hB] at hsub
  have hden : Real.Gamma (k + 1 / 2 + (a + 1)) = Real.Gamma (k + a + 3 / 2) := by
    congr 1; ring
  rw [hden] at hsub
  have hGp : 0 < Real.Gamma (k + a + 3 / 2) :=
    Real.Gamma_pos_of_pos (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  rw [eq_div_iff (mul_pos two_pos hGp).ne']
  rw [eq_div_iff hGp.ne'] at hsub
  linarith


/-- `Γ(k + 1/2) = √π (2k)! / (4^k k!)`. -/
lemma gamma_nat_add_half (k : ℕ) :
    Real.Gamma (k + 1 / 2) = √π * ((2 * k)! : ℝ) / (4 ^ k * (k ! : ℝ)) := by
  induction k with
  | zero => simpa using Real.Gamma_one_half_eq
  | succ k ih =>
    have h1 : ((k + 1 : ℕ) : ℝ) + 1 / 2 = ((k : ℝ) + 1 / 2) + 1 := by push_cast; ring
    rw [h1, Real.Gamma_add_one (by positivity), ih]
    have h2 : (2 * (k + 1))! = (2 * k + 2) * (2 * k + 1) * (2 * k)! := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      ring
    rw [h2, Nat.factorial_succ]
    push_cast
    have hk : (k ! : ℝ) ≠ 0 := by positivity
    field_simp
    ring


/-- The `k`-th term of the cosine expansion against the weight. -/
private noncomputable def poissonTerm (a x : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  (1 - t ^ 2) ^ a * ((-1) ^ k * (x * t) ^ (2 * k) / ((2 * k)! : ℝ))

private lemma poissonTerm_integrable {a : ℝ} (ha : -1 < a) (x : ℝ) (k : ℕ) :
    IntegrableOn (poissonTerm a x k) (Ioc 0 1) volume := by
  have h := (intervalIntegrable_one_sub_sq_rpow ha).mul_continuousOn
    (g := fun t : ℝ => (-1) ^ k * (x * t) ^ (2 * k) / ((2 * k)! : ℝ)) (by fun_prop)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h

private lemma poissonTerm_integral {a : ℝ} (ha : -1 < a) (x : ℝ) (k : ℕ) :
    ∫ t in Ioc (0 : ℝ) 1, poissonTerm a x k t =
      (-1) ^ k * x ^ (2 * k) / ((2 * k)! : ℝ) *
        (Real.Gamma (k + 1 / 2) * Real.Gamma (a + 1) / (2 * Real.Gamma (k + a + 3 / 2))) := by
  rw [← integral_one_sub_sq_rpow_mul_pow ha k, intervalIntegral.integral_of_le zero_le_one,
    ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [poissonTerm, mul_pow]
  ring

private lemma poissonTerm_norm_integral_le {a : ℝ} (ha : -1 < a) (x : ℝ) (k : ℕ) :
    ∫ t in Ioc (0 : ℝ) 1, ‖poissonTerm a x k t‖ ≤
      (∫ t in Ioc (0 : ℝ) 1, (1 - t ^ 2) ^ a) * (|x| ^ (2 * k) / ((2 * k)! : ℝ)) := by
  have hW : IntegrableOn (fun t : ℝ => (1 - t ^ 2) ^ a) (Ioc 0 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegrable_one_sub_sq_rpow ha)
  rw [← MeasureTheory.integral_mul_const]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
    (hW.mul_const _) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
  have hw : 0 ≤ (1 - t ^ 2) ^ a := Real.rpow_nonneg (by nlinarith [ht.1, ht.2]) _
  have hxt : |x * t| ^ (2 * k) ≤ |x| ^ (2 * k) := by
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
    rw [abs_mul, abs_of_pos ht.1]
    exact mul_le_of_le_one_right (abs_nonneg _) ht.2
  simp only [poissonTerm, Real.norm_eq_abs, abs_mul, abs_of_nonneg hw, abs_div, abs_pow,
    abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
  rw [← abs_mul]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hxt (by positivity)) hw

/-- **Poisson integral over `[0,1]`**: for `a > -1`,
`∫_0^1 (1-t²)^a cos(xt) dt = ∑_k (-1)^k x^{2k}/(2k)! · Γ(k+1/2)Γ(a+1)/(2Γ(k+a+3/2))`. -/
theorem integral_one_sub_sq_rpow_mul_cos {a : ℝ} (ha : -1 < a) (x : ℝ) :
    ∫ t in (0 : ℝ)..1, (1 - t ^ 2) ^ a * Real.cos (x * t) =
      ∑' k : ℕ, (-1) ^ k * x ^ (2 * k) / ((2 * k)! : ℝ) *
        (Real.Gamma (k + 1 / 2) * Real.Gamma (a + 1) / (2 * Real.Gamma (k + a + 3 / 2))) := by
  have hint := integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Ioc (0 : ℝ) 1)) (F := poissonTerm a x)
    (fun k => poissonTerm_integrable ha x k)
    (by
      refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _)
        (fun k => poissonTerm_norm_integral_le ha x k) ?_
      refine Summable.mul_left _ ?_
      have := Real.hasSum_cosh |x|
      simpa using this.summable)
  have hsum : ∀ t : ℝ, ∑' k, poissonTerm a x k t = (1 - t ^ 2) ^ a * Real.cos (x * t) := by
    intro t
    unfold poissonTerm
    rw [tsum_mul_left]
    congr 1
    exact (Real.hasSum_cos (x * t)).tsum_eq
  simp only [hsum, poissonTerm_integral ha x] at hint
  rw [intervalIntegral.integral_of_le zero_le_one, ← hint]

/-- **Poisson integral over `[-1,1]`** (even integrand). -/
theorem integral_neg_one_one_one_sub_sq_rpow_mul_cos {a : ℝ} (ha : -1 < a) (x : ℝ) :
    ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ a * Real.cos (x * t) =
      2 * ∫ t in (0 : ℝ)..1, (1 - t ^ 2) ^ a * Real.cos (x * t) := by
  set h : ℝ → ℝ := fun t => (1 - t ^ 2) ^ a * Real.cos (x * t) with hh
  have hI : IntervalIntegrable h volume (-1) 1 :=
    (intervalIntegrable_one_sub_sq_rpow_neg ha).mul_continuousOn (g := fun t : ℝ => Real.cos (x * t))
      (by fun_prop)
  have h0 : IntervalIntegrable h volume (-1) 0 := hI.mono_set (by
    rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
    exact Icc_subset_Icc le_rfl (by norm_num))
  have h1 : IntervalIntegrable h volume 0 1 := hI.mono_set (by
    rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
    exact Icc_subset_Icc (by norm_num) le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals h0 h1]
  have hneg : ∫ t in (-1 : ℝ)..0, h t = ∫ t in (0 : ℝ)..1, h t := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) h
    simp only [neg_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hh, neg_sq, mul_neg, Real.cos_neg]
  rw [hneg]
  ring


/-- The normalising constant `Γ(ν+1) / (√π Γ(ν+1/2))` of the Poisson integral. -/
noncomputable def besselPoissonConst (ν : ℝ) : ℝ :=
  Real.Gamma (ν + 1) / (√π * Real.Gamma (ν + 1 / 2))

lemma besselPoissonConst_pos {ν : ℝ} (hν : -1 / 2 < ν) : 0 < besselPoissonConst ν := by
  unfold besselPoissonConst
  exact div_pos (Real.Gamma_pos_of_pos (by linarith))
    (mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (Real.Gamma_pos_of_pos (by linarith)))

/-- **Poisson integral for the real-order Bessel function** (`DLMF 10.9.4`), `ν > -1/2`:
`besselNorm ν x = Γ(ν+1)/(√π Γ(ν+1/2)) ∫_{-1}^1 (1-t²)^{ν-1/2} cos(x t) dt`. -/
theorem besselNorm_eq_integral {ν : ℝ} (hν : -1 / 2 < ν) (x : ℝ) :
    besselNorm ν x = besselPoissonConst ν *
      ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ (ν - 1 / 2) * Real.cos (x * t) := by
  have ha : -1 < ν - 1 / 2 := by linarith
  rw [integral_neg_one_one_one_sub_sq_rpow_mul_cos ha, integral_one_sub_sq_rpow_mul_cos ha]
  unfold besselNorm besselPoissonConst
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  have hG1 : 0 < Real.Gamma (ν + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hsq : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  refine tsum_congr fun k => ?_
  have hk : 0 < Real.Gamma (ν + k + 1) := Real.Gamma_pos_of_pos (by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  have hgam := gamma_nat_add_half k
  have e1 : ν - 1 / 2 + 1 = ν + 1 / 2 := by ring
  have e2 : (k : ℝ) + (ν - 1 / 2) + 3 / 2 = ν + k + 1 := by ring
  rw [e1, e2, hgam, besselNormCoeff]
  have hf : (k ! : ℝ) ≠ 0 := by positivity
  have hf2 : ((2 * k)! : ℝ) ≠ 0 := by positivity
  rw [div_pow, show (2 : ℝ) ^ (2 * k) = 4 ^ k by rw [pow_mul]; norm_num]
  have h1 := hG1.ne'
  have h2 := hk.ne'
  have h3 := hsq.ne'
  generalize Real.Gamma (ν + 1 / 2) = G at *
  generalize Real.Gamma (ν + k + 1) = H at *
  generalize Real.Gamma (ν + 1) = Z at *
  generalize √π = S at *
  field_simp

/-- Normalisation: the Poisson integral at `x = 0` is `1`, i.e. the weight integrates to
`√π Γ(ν+1/2)/Γ(ν+1)`. -/
theorem besselPoissonConst_mul_integral_weight {ν : ℝ} (hν : -1 / 2 < ν) :
    besselPoissonConst ν * ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ (ν - 1 / 2) = 1 := by
  have h := besselNorm_eq_integral hν 0
  rw [besselNorm_zero (by linarith)] at h
  simpa using h.symm

/-- **The kernel bound** `|besselNorm ν x| ≤ 1` for `ν > -1/2` and all real `x`
(`fourier_mellin.tex`, after `eq:hankel`: "the integral representation of `J_{c-1}` gives
`|K^{(c)}| ≤ 1`"). -/
theorem abs_besselNorm_le_one {ν : ℝ} (hν : -1 / 2 < ν) (x : ℝ) : |besselNorm ν x| ≤ 1 := by
  have ha : -1 < ν - 1 / 2 := by linarith
  have hc := besselPoissonConst_pos hν
  have hW := intervalIntegrable_one_sub_sq_rpow_neg ha
  have hWc : IntervalIntegrable (fun t : ℝ => (1 - t ^ 2) ^ (ν - 1 / 2) * Real.cos (x * t))
      volume (-1) 1 := hW.mul_continuousOn (g := fun t : ℝ => Real.cos (x * t)) (by fun_prop)
  have hle : |∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ (ν - 1 / 2) * Real.cos (x * t)| ≤
      ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ (ν - 1 / 2) := by
    refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans ?_
    refine intervalIntegral.integral_mono_on (by norm_num) hWc.abs hW fun t ht => ?_
    have hw : 0 ≤ (1 - t ^ 2) ^ (ν - 1 / 2) := Real.rpow_nonneg (by nlinarith [ht.1, ht.2]) _
    rw [abs_mul, abs_of_nonneg hw]
    exact mul_le_of_le_one_right hw (Real.abs_cos_le_one _)
  rw [besselNorm_eq_integral hν, abs_mul, abs_of_pos hc]
  calc besselPoissonConst ν * |∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ (ν - 1 / 2) * Real.cos (x * t)|
      ≤ besselPoissonConst ν * ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ (ν - 1 / 2) :=
        mul_le_mul_of_nonneg_left hle hc.le
    _ = 1 := besselPoissonConst_mul_integral_weight hν

/-! ### Axiom guards -/

/-- info: 'FormalResearch.Special.besselNorm_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselNorm_eq_integral

/-- info: 'FormalResearch.Special.abs_besselNorm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abs_besselNorm_le_one

end FormalResearch.Special
