module

public import FormalResearch.Special.AiryCftQNCZeros
public import FormalResearch.Special.AiryCftQSamplePt

/-!
# Theorem Q (3) for `N = P Ai + Q Ai'` and the Clark functions: the sampling bound

For real `P`, `Q ≠ 0`, `N = P Ai + Q Ai'`, `D = P² - z Q²` and `f` entire with `‖f(u)‖ ≤ C₀ (1+|u|)^ν e(u)` (any real `ν`), `f ∈ L¹(ℝ)`:
**there is a constant `C = C(P, Q)`** with, for every finite set `S` of zeros of `N`,

`Σ_{z ∈ S} ‖f(z) D(z)/N'(z)²‖ ≤ C ∫_{x<0} ‖f‖`        (`airyNC_sampling_sum`),

hence the series over the zero subtype is absolutely summable (`airyNC_summable`).  (For the Clark functions `D/N'² = 1/K(z,z)`.)

Proof: as for `Ai` (`AiryCftQSample`), with three differences.

1. *Far zeros* `t ≤ -1`: the weight bound `‖D/N'²‖ ≤ W (1+|t|)^{-1/2}` (`airyNC_weight_norm_le`) and the single-point kernel bound
   `airyQ_far_le` give `‖f(t) D/N'²‖ ≤ W (4/π)(∫ ‖G‖ r²/((s-x)²+r²) + e⁴ ∫ ‖G‖ r²/((s+x)²+r²))`, `x = √(-t)`, `r = 1/(4x²)`.
2. The zeros of `N` interlace those of `Ai` and need **not** be separated like them: with `n = airyNIdx t` one has `√(-a_n) < x < √(-a_{n+1})`, so
   `x` is separated only up to a shift of one index (`ncRoot_sep_abs`); the kernel sum is bounded for such labelled families
   (`separated_kernel_sum`, generalised from the case of `Ai`), so the Carleson-type sum is uniformly bounded.
3. *Near zeros* `t > -1`: there are only finitely many (all of index `0`, `airyNC_near_finite`), and at each of them `‖f(t)‖ ≤ C(t) ∫_{x<0}‖f‖` by
   the fixed-point bound `airyQ_f_point` (Cauchy's formula for `H = G/z`); this is the only place where the constant depends on `(P, Q)` beyond `W`.

All **proved**.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real

namespace FormalResearch.Special

lemma airyNC_zero_eq_ofReal (P Q : ℝ) (hQ : Q ≠ 0) (z : {z : ℂ // airyNC P Q z = 0}) :
    z.1 = ((z.1.re : ℝ) : ℂ) := by
  have him := airyNC_zero_im P Q hQ z.2
  exact Complex.ext (by simp) (by simp [him])

lemma airyNC_zero_ofReal (P Q : ℝ) (hQ : Q ≠ 0) (z : {z : ℂ // airyNC P Q z = 0}) :
    airyNC P Q ((z.1.re : ℝ) : ℂ) = 0 := by
  rw [← airyNC_zero_eq_ofReal P Q hQ z]; exact z.2

/-- **Theorem Q (3) for `N = P Ai + Q Ai'`, finite partial sums.** -/
theorem airyNC_sampling_sum (P Q : ℝ) (hQ : Q ≠ 0) : ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : ℂ → ℂ} (_ : Differentiable ℂ f)
    (_ : Integrable (fun x : ℝ => f (x : ℂ))) {C₀ ν : ℝ} (_ : 0 ≤ C₀)
    (_ : ∀ u : ℂ, ‖f u‖ ≤ C₀ * (1 + ‖u‖) ^ ν * airyEnv u)
    (S : Finset {z : ℂ // airyNC P Q z = 0}),
    ∑ z ∈ S, ‖f z.1 * (airyDC P Q z.1 / airyNC' P Q z.1 ^ 2)‖ ≤ C * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := by
  classical
  have hpi := Real.pi_pos
  -- the kernel constant
  obtain ⟨K, hK⟩ := FormalResearch.Hardy.separated_kernel_sum (ι := {z : ℂ // airyNC P Q z = 0})
    (c := fun z => √(-z.1.re)) (d := fun z => airyNIdx z.1.re) (s := 1) (κ := 1) (by norm_num) (by norm_num)
  -- the near constants
  have hnear : ∀ z : {z : ℂ // airyNC P Q z = 0}, ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : ℂ → ℂ} (_ : Differentiable ℂ f)
      (_ : Integrable (fun x : ℝ => f (x : ℂ))) {C₀ ν : ℝ} (_ : 0 ≤ C₀)
      (_ : ∀ u : ℂ, ‖f u‖ ≤ C₀ * (1 + ‖u‖) ^ ν * airyEnv u),
      ‖f z.1‖ ≤ C * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := fun z => airyQ_f_point z.1
  choose Cz hCz0 hCz using hnear
  set Zn := (airyNC_near_finite P Q hQ).toFinset with hZn
  set wt : {z : ℂ // airyNC P Q z = 0} → ℝ := fun z => ‖airyDC P Q z.1 / airyNC' P Q z.1 ^ 2‖ with hwt
  set W : ℝ := 8 * π ^ 2 * (3 * |P| + 5 * |Q|) ^ 2 / Q ^ 2 with hW
  have hW0 : 0 ≤ W := by positivity
  have hK0 : 0 ≤ K := by
    have := hK ∅ (by simp) (by simp) (by simp) (by simp) 0
    simpa using this
  refine ⟨W * (4 / π) * (1 + Real.exp 4) * K + ∑ z ∈ Zn, wt z * Cz z,
    by have : 0 ≤ ∑ z ∈ Zn, wt z * Cz z := Finset.sum_nonneg fun z _ => mul_nonneg (norm_nonneg _) (hCz0 z)
       positivity, fun {f} hf hfi {C₀ ν} hC hb S => ?_⟩
  set g : ℝ → ℝ := fun t => ‖airyQG f (t : ℂ)‖ with hg
  have hgi : Integrable g := (airyQ_boundary hf hfi).1.norm
  have hgint : ∫ t : ℝ, g t = ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := (airyQ_boundary hf hfi).2
  have hg0 : ∀ t, 0 ≤ g t := fun t => norm_nonneg _
  have hI0 : 0 ≤ ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := integral_nonneg fun x => norm_nonneg _
  rw [← Finset.sum_filter_add_sum_filter_not S (fun z => z.1.re ≤ -1)]
  set Sf := S.filter (fun z => z.1.re ≤ -1) with hSf
  set Sn := S.filter (fun z => ¬ z.1.re ≤ -1) with hSn
  -- near part
  have hnearsum : ∑ z ∈ Sn, ‖f z.1 * (airyDC P Q z.1 / airyNC' P Q z.1 ^ 2)‖ ≤
      (∑ z ∈ Zn, wt z * Cz z) * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := by
    have hsub : Sn ⊆ Zn := by
      intro z hz
      have := (Finset.mem_filter.mp hz).2
      rw [hZn, Set.Finite.mem_toFinset]
      show -1 < z.1.re
      push Not at this; exact this
    calc ∑ z ∈ Sn, ‖f z.1 * (airyDC P Q z.1 / airyNC' P Q z.1 ^ 2)‖
        ≤ ∑ z ∈ Zn, ‖f z.1 * (airyDC P Q z.1 / airyNC' P Q z.1 ^ 2)‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
      _ ≤ ∑ z ∈ Zn, wt z * Cz z * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := by
          refine Finset.sum_le_sum fun z _ => ?_
          rw [norm_mul, mul_comm]
          have := mul_le_mul_of_nonneg_left (hCz z hf hfi hC hb)
            (norm_nonneg (airyDC P Q z.1 / airyNC' P Q z.1 ^ 2))
          simp only [hwt]
          linarith
      _ = _ := by rw [Finset.sum_mul]
  -- far part
  have hfar : ∑ z ∈ Sf, ‖f z.1 * (airyDC P Q z.1 / airyNC' P Q z.1 ^ 2)‖ ≤
      (W * (4 / π) * (1 + Real.exp 4) * K) * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := by
    set c : {z : ℂ // airyNC P Q z = 0} → ℝ := fun z => √(-z.1.re) with hc
    set r : {z : ℂ // airyNC P Q z = 0} → ℝ := fun z => 1 / (4 * c z ^ 2) with hr
    have hfarmem : ∀ z ∈ Sf, z.1.re ≤ -1 := fun z hz => (Finset.mem_filter.mp hz).2
    have hc1 : ∀ z ∈ Sf, 1 ≤ c z := fun z hz => ncRoot_ge_one (hfarmem z hz)
    have hr0 : ∀ z ∈ Sf, 0 < r z := fun z hz => by
      have := hc1 z hz; simp only [hr]; positivity
    -- pointwise bound
    have hpt : ∀ z ∈ Sf, ‖f z.1 * (airyDC P Q z.1 / airyNC' P Q z.1 ^ 2)‖ ≤
        W * (4 / π) * ((∫ t : ℝ, g t * (r z ^ 2 / ((t - c z) ^ 2 + r z ^ 2))) +
          Real.exp 4 * ∫ t : ℝ, g t * (r z ^ 2 / ((t + c z) ^ 2 + r z ^ 2))) := by
      intro z hz
      have ht := hfarmem z hz
      have hz0 := airyNC_zero_ofReal P Q hQ z
      have hzeq := airyNC_zero_eq_ofReal P Q hQ z
      have hcz1 := hc1 z hz
      have hcz0 : 0 < c z := by linarith
      have hsq : c z ^ 2 = -z.1.re := by
        simp only [hc]; rw [Real.sq_sqrt (by linarith)]
      have hw := airyNC_weight_norm_le P Q hQ hz0 ht
      have habs : (1 + |z.1.re|) = 1 + c z ^ 2 := by
        rw [hsq, abs_of_nonpos (by linarith)]
      rw [habs] at hw
      have hw' : ‖airyDC P Q (z.1.re : ℂ) / airyNC' P Q (z.1.re : ℂ) ^ 2‖ ≤ W * (1 / c z) := by
        refine hw.trans ?_
        have := one_add_sq_rpow_le hcz0
        rw [hW]
        exact mul_le_mul_of_nonneg_left this (by positivity)
      have hfar := airyQ_far_le hf hfi hC hb hcz1
      have hre : ((-(c z ^ 2) : ℝ) : ℂ) = (z.1.re : ℂ) := by rw [hsq]; push_cast; ring
      rw [hre] at hfar
      rw [hzeq, norm_mul]
      have e1 : ‖f (z.1.re : ℂ)‖ * ‖airyDC P Q (z.1.re : ℂ) / airyNC' P Q (z.1.re : ℂ) ^ 2‖ ≤
          ‖f (z.1.re : ℂ)‖ * (W * (1 / c z)) := mul_le_mul_of_nonneg_left hw' (norm_nonneg _)
      refine e1.trans ?_
      have e2 : ‖f (z.1.re : ℂ)‖ * (W * (1 / c z)) = W * (‖f (z.1.re : ℂ)‖ / c z) := by ring
      rw [e2, mul_assoc]
      exact mul_le_mul_of_nonneg_left hfar hW0
    -- integrability
    have hk1 : ∀ z ∈ Sf, Integrable (fun t : ℝ => g t * (r z ^ 2 / ((t - c z) ^ 2 + r z ^ 2))) := fun z hz =>
      integrable_mul_kern hgi (c z) (r z) (hr0 z hz)
    have hk2 : ∀ z ∈ Sf, Integrable (fun t : ℝ => g t * (r z ^ 2 / ((t + c z) ^ 2 + r z ^ 2))) := fun z hz => by
      have := integrable_mul_kern hgi (-c z) (r z) (hr0 z hz)
      simpa [sub_neg_eq_add] using this
    -- kernel sum hypotheses
    have hinj : Set.InjOn (fun z : {z : ℂ // airyNC P Q z = 0} => airyNIdx z.1.re) (Sf : Set _) := by
      intro z₁ _ z₂ _ h12
      have := airyNIdx_injOn P Q hQ (airyNC_zero_ofReal P Q hQ z₁) (airyNC_zero_ofReal P Q hQ z₂) h12
      apply Subtype.ext
      rw [airyNC_zero_eq_ofReal P Q hQ z₁, airyNC_zero_eq_ofReal P Q hQ z₂, this]
    have hKs := hK Sf (fun z hz => by have := hc1 z hz; simp only [hc] at this ⊢; linarith)
      (fun z hz => by
        have := ncRoot_growth hQ (airyNC_zero_ofReal P Q hQ z) (hfarmem z hz)
        simpa using this)
      hinj
      (fun z₁ h₁ z₂ h₂ hne => by
        have := ncRoot_sep_abs hQ (airyNC_zero_ofReal P Q hQ z₁) (airyNC_zero_ofReal P Q hQ z₂)
          (hfarmem z₁ h₁) (hfarmem z₂ h₂)
        simpa using this)
    have hS1 : ∑ z ∈ Sf, ∫ t : ℝ, g t * (r z ^ 2 / ((t - c z) ^ 2 + r z ^ 2)) ≤ K * (∫ t, g t) := by
      rw [← integral_finsetSum _ hk1, ← integral_const_mul]
      refine integral_mono (integrable_finsetSum _ hk1) (hgi.const_mul K) (fun t => ?_)
      rw [← Finset.mul_sum]
      have := hKs t
      simp only [hr, hc] at this ⊢
      nlinarith [hg0 t]
    have hS2 : ∑ z ∈ Sf, ∫ t : ℝ, g t * (r z ^ 2 / ((t + c z) ^ 2 + r z ^ 2)) ≤ K * (∫ t, g t) := by
      rw [← integral_finsetSum _ hk2, ← integral_const_mul]
      refine integral_mono (integrable_finsetSum _ hk2) (hgi.const_mul K) (fun t => ?_)
      rw [← Finset.mul_sum]
      have := hKs (-t)
      have e : ∀ z : {z : ℂ // airyNC P Q z = 0}, (t + c z) ^ 2 = (-t - c z) ^ 2 := fun z => by ring
      simp only [e]
      simp only [hr, hc] at this ⊢
      nlinarith [hg0 t]
    calc ∑ z ∈ Sf, ‖f z.1 * (airyDC P Q z.1 / airyNC' P Q z.1 ^ 2)‖
        ≤ ∑ z ∈ Sf, W * (4 / π) * ((∫ t : ℝ, g t * (r z ^ 2 / ((t - c z) ^ 2 + r z ^ 2))) +
          Real.exp 4 * ∫ t : ℝ, g t * (r z ^ 2 / ((t + c z) ^ 2 + r z ^ 2))) := Finset.sum_le_sum hpt
      _ = W * (4 / π) * ((∑ z ∈ Sf, ∫ t : ℝ, g t * (r z ^ 2 / ((t - c z) ^ 2 + r z ^ 2))) +
          Real.exp 4 * ∑ z ∈ Sf, ∫ t : ℝ, g t * (r z ^ 2 / ((t + c z) ^ 2 + r z ^ 2))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ W * (4 / π) * (K * (∫ t, g t) + Real.exp 4 * (K * (∫ t, g t))) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hS1 (mul_le_mul_of_nonneg_left hS2 (Real.exp_pos 4).le))
            (by positivity)
      _ = W * (4 / π) * (1 + Real.exp 4) * K * (∫ t, g t) := by ring
      _ = _ := by rw [hgint]
  calc _ ≤ _ := add_le_add hfar hnearsum
    _ = _ := by ring

/-- info: 'FormalResearch.Special.airyNC_sampling_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyNC_sampling_sum

end FormalResearch.Special
