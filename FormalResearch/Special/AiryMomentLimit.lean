module

public import FormalResearch.Special.AiryMomentCells
public import FormalResearch.Special.AiryLogDerivAsym

/-!
# The moment identity and the finite linear moment (phase-free)

Abstract form of the argument of `cts:airy-sum-zero` (Airy linear moment).  Let `m_n ≥ 0` satisfy
(i) the two-term sum rule `Σ_n (x + m_n)^{-2} = 1/(2√x) - 1/(4x²) + O(x^{-7/2})` for `x ≥ 1`, and
(ii) `m_n = κ c_n^{2/3} + O((n+1)^{-4/3})` with `c_n = n + 3/4`, `κ³ = (3π/2)²`.

* `head_tendsto`, `diff_tsum_tendsto`, `dcell_tsum_tendsto`: the three limits of `x³ ×` (head integral; difference of the
  two resolvent series; summed cell defects) as `x → ∞` (dominated convergence for series);
* **`moment_identity`**: `Σ_n (m_n - κ c_n^{2/3}) + κ Σ_n d₀(c_n) = κ ∫_0^{1/4} u^{2/3} du`, from `x³ ×` the sum rule as
  `x → ∞` (the `x^{-2}` terms cancel exactly by the Beta integral `cphi_integral`; the `x^{-3}` coefficient is the identity);
* **`moment_finite`**: `|Σ_{n<K} m_n/κ - ∫_0^{K+1/4} u^{2/3}| ≤ C K^{-1/3}` for `K ≥ 1` (`wn_tail`: tail of the `4/3`-series).

All proved.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral Filter Topology
open scoped Real

namespace FormalResearch.Special.AiryMoment

lemma summable_wn : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(4 / 3) : ℝ)) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num : (-(4 / 3) : ℝ) < -1))
  simpa using this

/-- Summed cell defects: `x³ Σ_n (φ_x(c_n) - ∫_{cell_n} φ_x) → -2κ Σ_n d₀(c_n)`. -/
theorem dcell_tsum_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun x : ℝ => x ^ 3 * ∑' n, dcell κ x n) atTop (𝓝 (-(2 * κ * ∑' n, d0c n))) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (x : ℝ) (n : ℕ) => x ^ 3 * dcell κ x n) (g := fun n => -(2 * κ * d0c n))
    (bound := fun n : ℕ => (5 / 3 * κ * c43 + 2 * κ * (2 / 9 / 12 * c43)) * ((n : ℝ) + 1) ^ (-(4 / 3) : ℝ))
    (summable_wn.mul_left _) (fun n => dcell_tendsto hκ n)
    (by
      filter_upwards [eventually_gt_atTop 0] with x hx n
      rw [Real.norm_eq_abs]
      exact dcell_bound hκ hx n)
  simp only [tsum_mul_left, tsum_neg] at h
  exact h

lemma diff_identity {x a b : ℝ} (hx : 0 < x) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((x + a) ^ 2)⁻¹ - ((x + b) ^ 2)⁻¹ = -(a - b) * (2 * x + a + b) / ((x + a) ^ 2 * (x + b) ^ 2) := by
  have h1 : 0 < x + a := by linarith
  have h2 : 0 < x + b := by linarith
  field_simp
  ring

lemma diff_dom {x a b : ℝ} (hx : 0 < x) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |x ^ 3 * (((x + a) ^ 2)⁻¹ - ((x + b) ^ 2)⁻¹)| ≤ 2 * |a - b| := by
  rw [diff_identity hx ha hb]
  have h1 : 0 < x + a := by linarith
  have h2 : 0 < x + b := by linarith
  have hD : 0 < (x + a) ^ 2 * (x + b) ^ 2 := by positivity
  have e : x ^ 3 * (-(a - b) * (2 * x + a + b) / ((x + a) ^ 2 * (x + b) ^ 2)) =
      -(a - b) * (x ^ 3 * (2 * x + a + b) / ((x + a) ^ 2 * (x + b) ^ 2)) := by ring
  rw [e, abs_mul, abs_neg]
  have hq : x ^ 3 * (2 * x + a + b) / ((x + a) ^ 2 * (x + b) ^ 2) ≤ 2 := by
    rw [div_le_iff₀ hD]
    have h3 : x * (x + a + b) ≤ (x + a) * (x + b) := by nlinarith only [mul_nonneg ha hb]
    have h4 : 0 ≤ x * (x + a + b) := by positivity
    have h5 : (x * (x + a + b)) ^ 2 ≤ ((x + a) * (x + b)) ^ 2 := pow_le_pow_left₀ h4 h3 2
    have h6 : x * (2 * x + a + b) ≤ 2 * (x + a + b) ^ 2 := by nlinarith only [ha, hb, hx]
    have h7 : x ^ 2 * (x + a + b) ^ 2 ≤ (x + a) ^ 2 * (x + b) ^ 2 := by nlinarith only [h5]
    calc x ^ 3 * (2 * x + a + b) = x ^ 2 * (x * (2 * x + a + b)) := by ring
      _ ≤ x ^ 2 * (2 * (x + a + b) ^ 2) := mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = 2 * (x ^ 2 * (x + a + b) ^ 2) := by ring
      _ ≤ 2 * ((x + a) ^ 2 * (x + b) ^ 2) := by linarith only [h7]
  have hq0 : 0 ≤ x ^ 3 * (2 * x + a + b) / ((x + a) ^ 2 * (x + b) ^ 2) := by positivity
  rw [abs_of_nonneg hq0, mul_comm]
  exact mul_le_mul_of_nonneg_right hq (abs_nonneg _) |>.trans (le_of_eq (by ring))

lemma diff_tendsto {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto (fun x : ℝ => x ^ 3 * (((x + a) ^ 2)⁻¹ - ((x + b) ^ 2)⁻¹)) atTop (𝓝 (-(2 * (a - b)))) := by
  have hN : Tendsto (fun x : ℝ => 2 + (a + b) * x⁻¹) atTop (𝓝 2) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).add
      ((tendsto_const_nhds (x := a + b)).mul tendsto_inv_atTop_zero)
  have hD : Tendsto (fun x : ℝ => (1 + a * x⁻¹) ^ 2 * (1 + b * x⁻¹) ^ 2) atTop (𝓝 1) := by
    have h1 : Tendsto (fun x : ℝ => 1 + a * x⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
        ((tendsto_const_nhds (x := a)).mul tendsto_inv_atTop_zero)
    have h2 : Tendsto (fun x : ℝ => 1 + b * x⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
        ((tendsto_const_nhds (x := b)).mul tendsto_inv_atTop_zero)
    simpa using (h1.pow 2).mul (h2.pow 2)
  have h := ((hN.div hD one_ne_zero).const_mul (-(a - b)))
  have e : -(a - b) * (2 / 1) = -(2 * (a - b)) := by ring
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [diff_identity hx ha hb]
  simp only [Pi.div_apply]
  field_simp
  ring

/-- **Summed difference of two resolvent series**: if `a_n, b_n ≥ 0` and `|a_n - b_n| ≤ ε_n` with `Σ ε_n < ∞`, then
`x³ Σ_n ((x + a_n)^{-2} - (x + b_n)^{-2}) → -2 Σ_n (a_n - b_n)`. -/
theorem diff_tsum_tendsto {a b ε : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hε : Summable ε) (hab : ∀ n, |a n - b n| ≤ ε n) :
    Tendsto (fun x : ℝ => x ^ 3 * ∑' n, (((x + a n) ^ 2)⁻¹ - ((x + b n) ^ 2)⁻¹)) atTop
      (𝓝 (-(2 * ∑' n, (a n - b n)))) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (x : ℝ) (n : ℕ) => x ^ 3 * (((x + a n) ^ 2)⁻¹ - ((x + b n) ^ 2)⁻¹))
    (g := fun n => -(2 * (a n - b n))) (bound := fun n => 2 * ε n) (hε.mul_left 2)
    (fun n => diff_tendsto (ha n) (hb n))
    (by
      filter_upwards [eventually_gt_atTop 0] with x hx n
      rw [Real.norm_eq_abs]
      exact (diff_dom hx (ha n) (hb n)).trans (by linarith only [hab n]))
  simp only [tsum_mul_left, tsum_neg] at h
  exact h

lemma sp_contOn : ContinuousOn (fun u : ℝ => u ^ (2 / 3 : ℝ)) (Icc 0 (1 / 4)) :=
  (Real.continuous_rpow_const (by norm_num)).continuousOn

lemma cphi_contOn {κ x : ℝ} (hκ : 0 < κ) (hx : 0 < x) : ContinuousOn (cphi κ x) (Icc 0 (1 / 4)) := by
  intro u hu
  unfold cphi
  have h1 : ContinuousAt (fun u : ℝ => x + κ * u ^ (2 / 3 : ℝ)) u :=
    continuousAt_const.add (continuousAt_const.mul (Real.continuous_rpow_const (by norm_num)).continuousAt)
  have hne : (x + κ * u ^ (2 / 3 : ℝ)) ^ 2 ≠ 0 := by
    have := Real.rpow_nonneg hu.1 (2 / 3 : ℝ)
    positivity
  exact ((h1.pow 2).inv₀ hne).continuousWithinAt

/-- Head of the integral: `x³ (∫_0^{1/4} φ_x - (1/4) x^{-2}) → -2κ ∫_0^{1/4} u^{2/3}` as `x → ∞`. -/
theorem head_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun x : ℝ => x ^ 3 * ((∫ u in (0 : ℝ)..(1 / 4), cphi κ x u) - 1 / 4 * (x ^ 2)⁻¹)) atTop
      (𝓝 (-(2 * κ * ∫ u in (0 : ℝ)..(1 / 4), u ^ (2 / 3 : ℝ)))) := by
  set Sint : ℝ := ∫ u in (0 : ℝ)..(1 / 4), u ^ (2 / 3 : ℝ) with hS
  have hsI : IntervalIntegrable (fun u : ℝ => u ^ (2 / 3 : ℝ)) volume 0 (1 / 4) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num)]; exact sp_contOn
  -- the identity and the bounds
  have key : ∀ x : ℝ, 0 < x →
      x ^ 3 * ((∫ u in (0 : ℝ)..(1 / 4), cphi κ x u) - 1 / 4 * (x ^ 2)⁻¹) + 2 * κ * Sint ∈
        Icc (0 : ℝ) (15 / 4 * κ ^ 2 / x) := by
    intro x hx
    set R : ℝ → ℝ := fun u => ((x + κ * u ^ (2 / 3 : ℝ)) ^ 2)⁻¹ - (x ^ 2)⁻¹ +
      2 * (x ^ 3)⁻¹ * ((x + κ * u ^ (2 / 3 : ℝ)) - x) with hR
    have hphiI : IntervalIntegrable (cphi κ x) volume 0 (1 / 4) := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num)]; exact cphi_contOn hκ hx
    have e : R = fun u => (cphi κ x u - (x ^ 2)⁻¹) + (2 * κ * (x ^ 3)⁻¹) * (u ^ (2 / 3 : ℝ)) := by
      funext u; simp only [hR, cphi]; ring
    have hRi : IntervalIntegrable R volume 0 (1 / 4) := by
      rw [e]
      exact (hphiI.sub intervalIntegrable_const).add (hsI.const_mul _)
    have hRint : (∫ u in (0 : ℝ)..(1 / 4), R u) =
        (∫ u in (0 : ℝ)..(1 / 4), cphi κ x u) - 1 / 4 * (x ^ 2)⁻¹ + 2 * κ * (x ^ 3)⁻¹ * Sint := by
      rw [e, intervalIntegral.integral_add (hphiI.sub intervalIntegrable_const) (hsI.const_mul _),
        integral_sub hphiI intervalIntegrable_const, intervalIntegral.integral_const_mul]
      simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      rw [← hS]
    have hRb : ∀ u ∈ Icc (0 : ℝ) (1 / 4), 0 ≤ R u ∧ R u ≤ 15 * κ ^ 2 / x ^ 4 := by
      intro u hu
      have hsu : 0 ≤ u ^ (2 / 3 : ℝ) := Real.rpow_nonneg hu.1 _
      have hs1 : u ^ (2 / 3 : ℝ) ≤ 1 := by
        calc u ^ (2 / 3 : ℝ) ≤ 1 ^ (2 / 3 : ℝ) :=
              Real.rpow_le_rpow hu.1 (by linarith [hu.2]) (by norm_num)
          _ = 1 := Real.one_rpow _
      have hyu : 0 < x + κ * u ^ (2 / 3 : ℝ) := by positivity
      have hyy : x / 3 ≤ x + κ * u ^ (2 / 3 : ℝ) := by nlinarith only [hκ, hsu, hx]
      obtain ⟨h1, h2⟩ := inv_sq_taylor hyu hx hyy
      refine ⟨h1, h2.trans ?_⟩
      have : (x + κ * u ^ (2 / 3 : ℝ) - x) ^ 2 ≤ κ ^ 2 := by
        have e1 : x + κ * u ^ (2 / 3 : ℝ) - x = κ * u ^ (2 / 3 : ℝ) := by ring
        rw [e1, mul_pow]
        have : (u ^ (2 / 3 : ℝ)) ^ 2 ≤ 1 := by nlinarith only [hsu, hs1]
        nlinarith only [this, sq_nonneg κ]
      have hfin : 15 * (x + κ * u ^ (2 / 3 : ℝ) - x) ^ 2 / x ^ 4 ≤ 15 * κ ^ 2 / x ^ 4 := by gcongr
      exact hfin
    have hlo : 0 ≤ (∫ u in (0 : ℝ)..(1 / 4), R u) := by
      exact intervalIntegral.integral_nonneg (by norm_num) (fun u hu => (hRb u hu).1)
    have hhi : (∫ u in (0 : ℝ)..(1 / 4), R u) ≤ 1 / 4 * (15 * κ ^ 2 / x ^ 4) := by
      have := intervalIntegral.integral_mono_on (a := 0) (b := 1 / 4) (by norm_num) hRi
        (intervalIntegrable_const (c := 15 * κ ^ 2 / x ^ 4)) (fun u hu => (hRb u hu).2)
      simp only [intervalIntegral.integral_const, smul_eq_mul] at this
      linarith only [this]
    rw [hRint] at hlo hhi
    have hx3 : x ^ 3 * (x ^ 3)⁻¹ = 1 := by field_simp
    have e2 : x ^ 3 * ((∫ u in (0 : ℝ)..(1 / 4), cphi κ x u) - 1 / 4 * (x ^ 2)⁻¹) + 2 * κ * Sint =
        x ^ 3 * ((∫ u in (0 : ℝ)..(1 / 4), cphi κ x u) - 1 / 4 * (x ^ 2)⁻¹ + 2 * κ * (x ^ 3)⁻¹ * Sint) := by
      field_simp
    rw [e2]
    constructor
    · exact mul_nonneg (by positivity) hlo
    · calc _ ≤ x ^ 3 * (1 / 4 * (15 * κ ^ 2 / x ^ 4)) := mul_le_mul_of_nonneg_left hhi (by positivity)
        _ = 15 / 4 * κ ^ 2 / x := by field_simp
  have hlim : Tendsto (fun x : ℝ => x ^ 3 * ((∫ u in (0 : ℝ)..(1 / 4), cphi κ x u) - 1 / 4 * (x ^ 2)⁻¹) +
      2 * κ * Sint) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun x : ℝ => 15 / 4 * κ ^ 2 / x)
    · filter_upwards [eventually_gt_atTop 0] with x hx using (key x hx).1
    · filter_upwards [eventually_gt_atTop 0] with x hx using (key x hx).2
    · simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (15 / 4 * κ ^ 2)
  have := hlim.sub_const (2 * κ * Sint)
  simp only [zero_sub] at this
  refine this.congr' ?_
  filter_upwards with x
  ring

lemma cell_endpoints (n : ℕ) : cc n - 1 / 2 = (n : ℝ) + 1 / 4 ∧ cc n + 1 / 2 = ((n + 1 : ℕ) : ℝ) + 1 / 4 := by
  unfold cc; push_cast; constructor <;> ring

/-- The sum of the cell integrals of an integrable positive kernel is its integral over `(1/4, ∞)`. -/
lemma cell_sum_eq {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi (1 / 4))) (hc : ContinuousOn f (Ici (1 / 4)))
    (hs : Summable (fun n : ℕ => ∫ u in (cc n - 1 / 2)..(cc n + 1 / 2), f u)) :
    ∑' n : ℕ, (∫ u in (cc n - 1 / 2)..(cc n + 1 / 2), f u) = ∫ u in Ioi (1 / 4 : ℝ), f u := by
  have hcell : ∀ n : ℕ, (∫ u in (cc n - 1 / 2)..(cc n + 1 / 2), f u) =
      ∫ u in ((n : ℝ) + 1 / 4)..(((n + 1 : ℕ) : ℝ) + 1 / 4), f u := by
    intro n; rw [(cell_endpoints n).1, (cell_endpoints n).2]
  have hint : ∀ n : ℕ, IntervalIntegrable f volume ((n : ℝ) + 1 / 4) (((n + 1 : ℕ) : ℝ) + 1 / 4) := by
    intro n
    apply ContinuousOn.intervalIntegrable
    refine hc.mono ?_
    rw [uIcc_of_le (by push_cast; linarith)]
    intro u hu
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact mem_Ici.mpr (by linarith [hu.1])
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, (∫ u in (cc n - 1 / 2)..(cc n + 1 / 2), f u) =
      ∫ u in (1 / 4 : ℝ)..((N : ℝ) + 1 / 4), f u := by
    intro N
    simp_rw [hcell]
    have := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume)
      (a := fun k : ℕ => (k : ℝ) + 1 / 4) (n := N) (fun k _ => hint k)
    simpa using this
  have h1 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (∫ u in (cc n - 1 / 2)..(cc n + 1 / 2), f u))
      atTop (𝓝 (∑' n : ℕ, (∫ u in (cc n - 1 / 2)..(cc n + 1 / 2), f u))) := hs.hasSum.tendsto_sum_nat
  have h2 : Tendsto (fun N : ℕ => ∫ u in (1 / 4 : ℝ)..((N : ℝ) + 1 / 4), f u) atTop
      (𝓝 (∫ u in Ioi (1 / 4 : ℝ), f u)) := by
    apply intervalIntegral_tendsto_integral_Ioi (1 / 4 : ℝ) hf
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  simp_rw [hpart] at h1
  exact tendsto_nhds_unique h1 h2

lemma cphi_contOn_Ici {κ x : ℝ} (hκ : 0 < κ) (hx : 0 < x) : ContinuousOn (cphi κ x) (Ici 0) := by
  intro u hu
  unfold cphi
  have h1 : ContinuousAt (fun u : ℝ => x + κ * u ^ (2 / 3 : ℝ)) u :=
    continuousAt_const.add (continuousAt_const.mul (Real.continuous_rpow_const (by norm_num)).continuousAt)
  have hne : (x + κ * u ^ (2 / 3 : ℝ)) ^ 2 ≠ 0 := by
    have := Real.rpow_nonneg (mem_Ici.mp hu) (2 / 3 : ℝ)
    positivity
  exact ((h1.pow 2).inv₀ hne).continuousWithinAt

lemma head_add_tail {κ x : ℝ} (hκ : 0 < κ) (hκ3 : κ ^ 3 = (3 * π / 2) ^ 2) (hx : 0 < x) :
    (∫ u in Ioi (1 / 4 : ℝ), cphi κ x u) =
      1 / (2 * √x) - ∫ u in (0 : ℝ)..(1 / 4), cphi κ x u := by
  have hI := cphi_integrableOn hκ hx
  have h1 : IntegrableOn (cphi κ x) (Ioc 0 (1 / 4)) := hI.mono_set (Ioc_subset_Ioi_self)
  have h2 : IntegrableOn (cphi κ x) (Ioi (1 / 4)) := hI.mono_set (Ioi_subset_Ioi (by norm_num))
  have h3 := setIntegral_union (μ := volume) (f := cphi κ x) (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi h1 h2
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num), cphi_integral hκ hκ3 hx,
    ← intervalIntegral.integral_of_le (by norm_num)] at h3
  linarith only [h3]

/-- **The moment identity.**  If `m_n ≥ 0` satisfy the two-term sum rule
`Σ_n (x + m_n)^{-2} = 1/(2√x) - 1/(4x²) + O(x^{-7/2})` (`x ≥ 1`) and `m_n = κ c_n^{2/3} + O((n+1)^{-4/3})`, then
`Σ_n (m_n - κ c_n^{2/3}) + κ Σ_n d₀(c_n) = κ ∫_0^{1/4} u^{2/3} du`. -/
theorem moment_identity {κ Cη : ℝ} (hκ : 0 < κ) (hκ3 : κ ^ 3 = (3 * π / 2) ^ 2) {m : ℕ → ℝ} {E : ℝ → ℝ}
    (hm0 : ∀ n, 0 ≤ m n)
    (hη : ∀ n, |m n - κ * cc n ^ (2 / 3 : ℝ)| ≤ Cη * ((n : ℝ) + 1) ^ (-(4 / 3) : ℝ))
    (hsum : ∀ x : ℝ, 1 ≤ x → HasSum (fun n => ((x + m n) ^ 2)⁻¹) (E x))
    (hE : ∀ x : ℝ, 1 ≤ x → |E x - (1 / (2 * √x) - 1 / (4 * x ^ 2))| ≤ 5 / (x ^ 3 * √x)) :
    ∑' n, (m n - κ * cc n ^ (2 / 3 : ℝ)) + κ * ∑' n, d0c n =
      κ * ∫ u in (0 : ℝ)..(1 / 4), u ^ (2 / 3 : ℝ) := by
  set μ : ℕ → ℝ := fun n => κ * cc n ^ (2 / 3 : ℝ) with hμ
  have hμ0 : ∀ n, 0 ≤ μ n := fun n => by
    have : 0 ≤ cc n := by unfold cc; positivity
    simp only [hμ]; positivity
  have hεs : Summable (fun n : ℕ => Cη * ((n : ℝ) + 1) ^ (-(4 / 3) : ℝ)) := summable_wn.mul_left _
  have hid : ∀ x : ℝ, 1 ≤ x →
      x ^ 3 * (E x - (1 / (2 * √x) - 1 / (4 * x ^ 2))) =
        x ^ 3 * ∑' n, (((x + m n) ^ 2)⁻¹ - ((x + μ n) ^ 2)⁻¹) + x ^ 3 * ∑' n, dcell κ x n -
          x ^ 3 * ((∫ u in (0 : ℝ)..(1 / 4), cphi κ x u) - 1 / 4 * (x ^ 2)⁻¹) := by
    intro x hx1
    have hx : 0 < x := by linarith
    have hf := hsum x hx1
    have hdiffS : Summable (fun n => ((x + m n) ^ 2)⁻¹ - ((x + μ n) ^ 2)⁻¹) := by
      refine Summable.of_norm_bounded (g := fun n => 2 / x ^ 3 * (Cη * ((n : ℝ) + 1) ^ (-(4 / 3) : ℝ)))
        (hεs.mul_left _) (fun n => ?_)
      rw [Real.norm_eq_abs]
      have := diff_dom hx (hm0 n) (hμ0 n)
      rw [abs_mul, abs_of_pos (pow_pos hx 3)] at this
      have h3 : 0 < x ^ 3 := pow_pos hx 3
      calc _ ≤ 2 * |m n - μ n| / x ^ 3 := by
            rw [le_div_iff₀ h3]; linarith only [this]
        _ ≤ 2 * (Cη * ((n : ℝ) + 1) ^ (-(4 / 3) : ℝ)) / x ^ 3 := by
            gcongr; exact hη n
        _ = _ := by ring
    have hgS : Summable (fun n => ((x + μ n) ^ 2)⁻¹) := by
      have := hf.summable.sub hdiffS
      simpa using this
    have hdS : Summable (fun n => dcell κ x n) := by
      refine Summable.of_norm_bounded (g := fun n => (5 / 3 * κ * c43 + 2 * κ * (2 / 9 / 12 * c43)) / x ^ 3 *
        ((n : ℝ) + 1) ^ (-(4 / 3) : ℝ)) (summable_wn.mul_left _) (fun n => ?_)
      rw [Real.norm_eq_abs]
      have := dcell_bound hκ hx n
      rw [abs_mul, abs_of_pos (pow_pos hx 3)] at this
      have h3 : 0 < x ^ 3 := pow_pos hx 3
      rw [div_mul_eq_mul_div, le_div_iff₀ h3]
      linarith only [this]
    have hcS : Summable (fun n : ℕ => ∫ u in (cc n - 1 / 2)..(cc n + 1 / 2), cphi κ x u) := by
      have := hgS.sub hdS
      refine this.congr (fun n => ?_)
      simp only [dcell, cphi, hμ]
      ring
    have hcsum := cell_sum_eq (f := cphi κ x)
      ((cphi_integrableOn hκ hx).mono_set (Ioi_subset_Ioi (by norm_num)))
      ((cphi_contOn_Ici hκ hx).mono (fun u hu => le_trans (by norm_num) (mem_Ici.mp hu))) hcS
    rw [head_add_tail hκ hκ3 hx] at hcsum
    -- decompose
    have h1 : ∑' n, ((x + μ n) ^ 2)⁻¹ = ∑' n, (∫ u in (cc n - 1 / 2)..(cc n + 1 / 2), cphi κ x u) +
        ∑' n, dcell κ x n := by
      rw [← hcS.tsum_add hdS]
      refine tsum_congr (fun n => ?_)
      simp only [dcell, cphi, hμ]
      ring
    have h2 : E x = ∑' n, (((x + m n) ^ 2)⁻¹ - ((x + μ n) ^ 2)⁻¹) + ∑' n, ((x + μ n) ^ 2)⁻¹ := by
      rw [← hdiffS.tsum_add hgS, ← hf.tsum_eq]
      exact tsum_congr (fun n => by ring)
    rw [h2, h1, hcsum]
    ring
  have hlhs : Tendsto (fun x : ℝ => x ^ 3 * (E x - (1 / (2 * √x) - 1 / (4 * x ^ 2)))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun x : ℝ => 5 / √x)
    · filter_upwards [eventually_ge_atTop 1] with x hx
      have hx0 : 0 < x := by linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hx0 3)]
      calc x ^ 3 * |E x - (1 / (2 * √x) - 1 / (4 * x ^ 2))| ≤ x ^ 3 * (5 / (x ^ 3 * √x)) :=
            mul_le_mul_of_nonneg_left (hE x hx) (by positivity)
        _ = 5 / √x := by
            have : 0 < √x := Real.sqrt_pos.mpr hx0
            field_simp
    · exact tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hrhs := ((diff_tsum_tendsto hm0 hμ0 hεs hη).add (dcell_tsum_tendsto hκ)).sub (head_tendsto hκ)
  have hrhs' : Tendsto (fun x : ℝ => x ^ 3 * (E x - (1 / (2 * √x) - 1 / (4 * x ^ 2)))) atTop
      (𝓝 (-(2 * ∑' n, (m n - μ n)) + -(2 * κ * ∑' n, d0c n) - -(2 * κ * ∫ u in (0 : ℝ)..(1 / 4), u ^ (2 / 3 : ℝ)))) := by
    refine hrhs.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    exact (hid x hx).symm
  have := tendsto_nhds_unique hlhs hrhs'
  simp only [hμ] at this
  linarith only [this]

lemma wn_step {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) + 1) ^ (-(4 / 3) : ℝ) ≤ 3 * ((n : ℝ) ^ (-(1 / 3) : ℝ) - ((n : ℝ) + 1) ^ (-(1 / 3) : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set D : Set ℝ := Icc (n : ℝ) ((n : ℝ) + 1) with hD
  have hpos : ∀ t ∈ D, 0 < t := fun t ht => by linarith [ht.1]
  have hd : ∀ t ∈ D, HasDerivAt (fun t : ℝ => -3 * t ^ (-(1 / 3) : ℝ)) (t ^ (-(4 / 3) : ℝ)) t := by
    intro t ht
    have := (Real.hasDerivAt_rpow_const (p := (-(1 / 3) : ℝ)) (Or.inl (hpos t ht).ne')).const_mul (-3 : ℝ)
    refine this.congr_deriv ?_
    norm_num
    ring
  have h := (convex_Icc (n : ℝ) ((n : ℝ) + 1)).mul_sub_le_image_sub_of_le_deriv
    (f := fun t : ℝ => -3 * t ^ (-(1 / 3) : ℝ)) (C := ((n : ℝ) + 1) ^ (-(4 / 3) : ℝ))
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => by
      rw [interior_Icc] at ht
      exact (hd t ⟨ht.1.le, ht.2.le⟩).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [interior_Icc] at ht
      rw [(hd t ⟨ht.1.le, ht.2.le⟩).deriv]
      exact Real.rpow_le_rpow_of_nonpos (hpos t ⟨ht.1.le, ht.2.le⟩) ht.2.le (by norm_num))
    (n : ℝ) ⟨le_rfl, by linarith⟩ ((n : ℝ) + 1) ⟨by linarith, le_rfl⟩ (by linarith)
  simp only [add_sub_cancel_left, mul_one] at h
  linarith only [h]

/-- Tail of the `4/3`-series: `Σ_{j ≥ 0} (j + K + 1)^{-4/3} ≤ 3 K^{-1/3}` for `K ≥ 1`. -/
lemma wn_tail {K : ℕ} (hK : 1 ≤ K) :
    ∑' j : ℕ, ((((j + K : ℕ) : ℝ)) + 1) ^ (-(4 / 3) : ℝ) ≤ 3 * (K : ℝ) ^ (-(1 / 3) : ℝ) := by
  have hpart : ∀ N : ℕ, ∑ j ∈ Finset.range N, ((((j + K : ℕ) : ℝ)) + 1) ^ (-(4 / 3) : ℝ) ≤
      3 * ((K : ℝ) ^ (-(1 / 3) : ℝ) - (((N + K : ℕ) : ℝ)) ^ (-(1 / 3) : ℝ)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have := wn_step (n := N + K) (by omega)
      have e : ((N + 1 + K : ℕ) : ℝ) = ((N + K : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [e]
      linarith only [ih, this]
  have hnn : ∀ j : ℕ, 0 ≤ ((((j + K : ℕ) : ℝ)) + 1) ^ (-(4 / 3) : ℝ) := fun j => by positivity
  refine Real.tsum_le_of_sum_range_le hnn (fun N => ?_)
  refine (hpart N).trans ?_
  have : 0 ≤ (((N + K : ℕ) : ℝ)) ^ (-(1 / 3) : ℝ) := by positivity
  linarith only [this]

lemma cell_partial {f : ℝ → ℝ} (hc : ContinuousOn f (Ici (1 / 4))) (N : ℕ) :
    ∑ n ∈ Finset.range N, (∫ u in (cc n - 1 / 2)..(cc n + 1 / 2), f u) =
      ∫ u in (1 / 4 : ℝ)..((N : ℝ) + 1 / 4), f u := by
  have hcell : ∀ n : ℕ, (∫ u in (cc n - 1 / 2)..(cc n + 1 / 2), f u) =
      ∫ u in ((n : ℝ) + 1 / 4)..(((n + 1 : ℕ) : ℝ) + 1 / 4), f u := by
    intro n; rw [(cell_endpoints n).1, (cell_endpoints n).2]
  have hint : ∀ n : ℕ, IntervalIntegrable f volume ((n : ℝ) + 1 / 4) (((n + 1 : ℕ) : ℝ) + 1 / 4) := by
    intro n
    apply ContinuousOn.intervalIntegrable
    refine hc.mono ?_
    rw [uIcc_of_le (by push_cast; linarith)]
    intro u hu
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact mem_Ici.mpr (by linarith [hu.1])
  simp_rw [hcell]
  have := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume)
    (a := fun k : ℕ => (k : ℝ) + 1 / 4) (n := N) (fun k _ => hint k)
  simpa using this

/-- **The finite linear moment.**  Under the hypotheses of `moment_identity`, for `K ≥ 1`
`|Σ_{n<K} m_n/κ - ∫_0^{K+1/4} u^{2/3} du| ≤ C K^{-1/3}`. -/
theorem moment_finite {κ Cη : ℝ} (hκ : 0 < κ) (hκ3 : κ ^ 3 = (3 * π / 2) ^ 2) {m : ℕ → ℝ} {E : ℝ → ℝ}
    (hm0 : ∀ n, 0 ≤ m n)
    (hη : ∀ n, |m n - κ * cc n ^ (2 / 3 : ℝ)| ≤ Cη * ((n : ℝ) + 1) ^ (-(4 / 3) : ℝ))
    (hsum : ∀ x : ℝ, 1 ≤ x → HasSum (fun n => ((x + m n) ^ 2)⁻¹) (E x))
    (hE : ∀ x : ℝ, 1 ≤ x → |E x - (1 / (2 * √x) - 1 / (4 * x ^ 2))| ≤ 5 / (x ^ 3 * √x)) :
    ∃ C : ℝ, ∀ K : ℕ, 1 ≤ K →
      |(∑ n ∈ Finset.range K, m n) / κ - ∫ u in (0 : ℝ)..((K : ℝ) + 1 / 4), u ^ (2 / 3 : ℝ)| ≤
        C * (K : ℝ) ^ (-(1 / 3) : ℝ) := by
  have hid := moment_identity hκ hκ3 hm0 hη hsum hE
  set μ : ℕ → ℝ := fun n => κ * cc n ^ (2 / 3 : ℝ) with hμ
  set I0 : ℝ := ∫ u in (0 : ℝ)..(1 / 4), u ^ (2 / 3 : ℝ) with hI0
  set A : ℝ := Cη / κ + 2 / 9 / 12 * c43 with hA
  have hCη : 0 ≤ Cη := by
    have h0 := (abs_nonneg _).trans (hη 0)
    have hp : 0 < (((0 : ℕ) : ℝ) + 1) ^ (-(4 / 3) : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    by_contra hneg
    have hneg' : Cη < 0 := not_le.mp hneg
    nlinarith only [h0, hp, hneg']
  set t : ℕ → ℝ := fun n => (m n - μ n) / κ + d0c n with ht
  have hbt : ∀ n, |t n| ≤ A * ((n : ℝ) + 1) ^ (-(4 / 3) : ℝ) := by
    intro n
    have h1 : |(m n - μ n) / κ| ≤ Cη / κ * ((n : ℝ) + 1) ^ (-(4 / 3) : ℝ) := by
      rw [abs_div, abs_of_pos hκ, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (hη n) hκ.le
    have h2 := d0c_bound n
    calc |t n| ≤ |(m n - μ n) / κ| + |d0c n| := abs_add_le _ _
      _ ≤ _ := by rw [hA]; nlinarith only [h1, h2]
  have htS : Summable t := Summable.of_norm_bounded (summable_wn.mul_left A)
    (fun n => by rw [Real.norm_eq_abs]; exact hbt n)
  have hηS : Summable (fun n => (m n - μ n) / κ) := by
    refine Summable.of_norm_bounded (summable_wn.mul_left (Cη / κ)) (fun n => ?_)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hκ, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (hη n) hκ.le
  have hdS : Summable (fun n => d0c n) := Summable.of_norm_bounded (summable_wn.mul_left (2 / 9 / 12 * c43))
    (fun n => by rw [Real.norm_eq_abs]; exact d0c_bound n)
  have htsum : ∑' n, t n = I0 := by
    have := hηS.tsum_add hdS
    simp only [ht]
    rw [this, tsum_div_const]
    field_simp
    linarith only [hid]
  have hsc : ContinuousOn (fun u : ℝ => u ^ (2 / 3 : ℝ)) (Ici (1 / 4)) :=
    (Real.continuous_rpow_const (by norm_num)).continuousOn
  have hsI : IntervalIntegrable (fun u : ℝ => u ^ (2 / 3 : ℝ)) volume 0 (1 / 4) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num)]; exact sp_contOn
  have hsI2 : ∀ K : ℕ, IntervalIntegrable (fun u : ℝ => u ^ (2 / 3 : ℝ)) volume (1 / 4) ((K : ℝ) + 1 / 4) := by
    intro K
    apply ContinuousOn.intervalIntegrable
    refine hsc.mono ?_
    rw [uIcc_of_le (by have : (0 : ℝ) ≤ K := Nat.cast_nonneg K; linarith)]
    intro u hu; exact mem_Ici.mpr hu.1
  refine ⟨3 * A, fun K hK => ?_⟩
  -- exact formula for the finite moment
  have hfin : (∑ n ∈ Finset.range K, m n) / κ - ∫ u in (0 : ℝ)..((K : ℝ) + 1 / 4), u ^ (2 / 3 : ℝ) =
      ∑ n ∈ Finset.range K, t n - I0 := by
    have e1 : (∑ n ∈ Finset.range K, m n) / κ =
        ∑ n ∈ Finset.range K, ((m n - μ n) / κ + cc n ^ (2 / 3 : ℝ)) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      simp only [hμ]; field_simp; ring
    have e2 : ∑ n ∈ Finset.range K, cc n ^ (2 / 3 : ℝ) =
        ∑ n ∈ Finset.range K, d0c n + ∫ u in (1 / 4 : ℝ)..((K : ℝ) + 1 / 4), u ^ (2 / 3 : ℝ) := by
      rw [← cell_partial hsc K, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      simp [d0c]
    have e3 : ∫ u in (0 : ℝ)..((K : ℝ) + 1 / 4), u ^ (2 / 3 : ℝ) =
        I0 + ∫ u in (1 / 4 : ℝ)..((K : ℝ) + 1 / 4), u ^ (2 / 3 : ℝ) :=
      (intervalIntegral.integral_add_adjacent_intervals hsI (hsI2 K)).symm
    rw [e1, Finset.sum_add_distrib, e2, e3]
    simp only [ht, Finset.sum_add_distrib]
    ring
  rw [hfin, ← htsum, ← htS.sum_add_tsum_nat_add K]
  have hsum2 : Summable (fun j : ℕ => A * ((((j + K : ℕ) : ℝ)) + 1) ^ (-(4 / 3) : ℝ)) := by
    have := (summable_nat_add_iff K).mpr (summable_wn.mul_left A)
    exact this
  have htail := tsum_of_norm_bounded hsum2.hasSum (f := fun j : ℕ => t (j + K))
    (fun j => by rw [Real.norm_eq_abs]; exact hbt (j + K))
  rw [tsum_mul_left] at htail
  have hw := wn_tail hK
  have hA0 : 0 ≤ A := by
    rw [hA]; have := c43_pos; positivity
  rw [sub_add_cancel_left, abs_neg, ← Real.norm_eq_abs]
  calc ‖∑' j : ℕ, t (j + K)‖ ≤ A * ∑' j : ℕ, ((((j + K : ℕ) : ℝ)) + 1) ^ (-(4 / 3) : ℝ) := htail
    _ ≤ A * (3 * (K : ℝ) ^ (-(1 / 3) : ℝ)) := mul_le_mul_of_nonneg_left hw hA0
    _ = 3 * A * (K : ℝ) ^ (-(1 / 3) : ℝ) := by ring

/-- info: 'FormalResearch.Special.AiryMoment.moment_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms moment_finite

end FormalResearch.Special.AiryMoment
