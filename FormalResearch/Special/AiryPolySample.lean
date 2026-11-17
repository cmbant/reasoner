module

public import FormalResearch.Special.AiryPolyWeights
public import FormalResearch.Special.AiryPolyQuad
public import FormalResearch.Special.AiryCftQNCSample

/-!
# Theorem Q (3) for `N = P·Ai + Q·Ai'`, Hermite-Biehler `(P, Q)`: the sampling bound and the unconditional Airy quadrature

For real polynomials `P`, `Q ≠ 0` with `Q + iP` having all roots in the open lower half plane (`AiryPQHB`), `N = P Ai + Q Ai'`,
`D = P (P + Q') - Q (P' + zQ)` and `f` entire with `‖f(u)‖ ≤ C₀ (1+|u|)^ν e(u)` (any real `ν`), `f ∈ L¹(ℝ)`:

* `airyPQ_sampling_sum`: there is a constant `C = C(P, Q)` with, for every finite set `S` of zeros of `N`,
  `Σ_{z ∈ S} ‖f(z) D(z)/N'(z)²‖ ≤ C ∫_{x<0} ‖f‖` (`general_theorems.tex` Lemma 1.0′(d) and Theorem Q (3) for the Hermite-Biehler `N`);
* `airyPQ_summable`, **`airyPQ_hasSum_unc`**: `Σ_{N(z)=0} f(z) D(z)/N'(z)² = ∫_ℝ f`, absolutely convergent, no summability hypothesis
  (`SOFT_EDGE_THEOREMS.md` Lemma 4.6, quadrature; this is the input (HB) of `SE5_FIVE_LEVEL_AIRY.md` and Theorem 4.7).

Proof: as for constant `P`, `Q` (`AiryCftQNCSample`), with the following changes.  Far zeros `t ≤ -T` (`T ≥ 1` beyond the real roots of `Q`
(`airyPQ_far_ex`) and large enough for the weight bound `‖D/N'²‖ ≤ 882π²/√(-t)`, `airyPQ_weight_norm_le`): `Ai(t) ≠ 0`, the index
`airyNIdx t` is injective on them (`airyPQ_injOn_far`: `m = Ai'/Ai` strictly decreasing, `-P/Q` increasing) and separated up to a shift of one index
(`airyPQ_root_sep_abs`), so the kernel sum is bounded (`separated_kernel_sum`).  Near zeros `t > -T`: finitely many (`airyPQ_zeros_finite` for
`‖z‖ ≤ max(T, T')`, and `airyPQ_no_zero_sector` for the positive ones), each handled by the fixed-point bound `airyQ_f_point`.  All **proved**.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric Polynomial
open scoped Real

namespace FormalResearch.Special

lemma airyPQ_zero_ofReal {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (z : {z : ℂ // airyPQN P Q z = 0}) :
    airyPQN P Q ((z.1.re : ℝ) : ℂ) = 0 := by
  rw [← airyPQ_zero_eq_ofReal hHB z.2]; exact z.2

/-- **Theorem Q (3) for a Hermite-Biehler `N = P Ai + Q Ai'`, finite partial sums.** -/
theorem airyPQ_sampling_sum {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : ℂ → ℂ} (_ : Differentiable ℂ f)
    (_ : Integrable (fun x : ℝ => f (x : ℂ))) {C₀ ν : ℝ} (_ : 0 ≤ C₀)
    (_ : ∀ u : ℂ, ‖f u‖ ≤ C₀ * (1 + ‖u‖) ^ ν * airyEnv u)
    (S : Finset {z : ℂ // airyPQN P Q z = 0}),
    ∑ z ∈ S, ‖f z.1 * (airyPQD P Q z.1 / airyPQN' P Q z.1 ^ 2)‖ ≤ C * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := by
  classical
  have hpi := Real.pi_pos
  obtain ⟨T0, hT01, hT0⟩ := airyPQ_far_ex hQ
  obtain ⟨T1, hT11, hT1⟩ := airyPQ_weight_norm_le hHB hQ
  obtain ⟨T2, hT21, hT2⟩ := airyPQ_no_zero_sector P Q (Or.inr hQ)
  set T : ℝ := max T0 T1 with hT
  have hT1' : 1 ≤ T := hT01.trans (le_max_left _ _)
  -- the kernel constant
  obtain ⟨K, hK⟩ := FormalResearch.Hardy.separated_kernel_sum (ι := {z : ℂ // airyPQN P Q z = 0})
    (c := fun z => √(-z.1.re)) (d := fun z => airyNIdx z.1.re) (s := 1) (κ := 1) (by norm_num) (by norm_num)
  -- the near constants
  have hnear : ∀ z : {z : ℂ // airyPQN P Q z = 0}, ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : ℂ → ℂ} (_ : Differentiable ℂ f)
      (_ : Integrable (fun x : ℝ => f (x : ℂ))) {C₀ ν : ℝ} (_ : 0 ≤ C₀)
      (_ : ∀ u : ℂ, ‖f u‖ ≤ C₀ * (1 + ‖u‖) ^ ν * airyEnv u),
      ‖f z.1‖ ≤ C * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := fun z => airyQ_f_point z.1
  choose Cz hCz0 hCz using hnear
  -- finitely many near zeros
  have hnearfin : {z : {z : ℂ // airyPQN P Q z = 0} | -T < z.1.re}.Finite := by
    have hfin := airyPQ_zeros_finite hHB (max T T2)
    refine (Set.Finite.preimage (f := Subtype.val) Subtype.val_injective.injOn hfin).subset ?_
    intro z hz
    have hz' : -T < z.1.re := hz
    have hzeq := airyPQ_zero_eq_ofReal hHB z.2
    refine ⟨z.2, ?_⟩
    rw [hzeq, Complex.norm_real, Real.norm_eq_abs]
    by_cases hneg : z.1.re < 0
    · rw [abs_of_neg hneg]
      exact (by linarith : -z.1.re ≤ T).trans (le_max_left _ _)
    · push Not at hneg
      rw [abs_of_nonneg hneg]
      by_contra hlt
      push Not at hlt
      have hge : T2 ≤ ‖(z.1.re : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hneg]
        exact ((le_max_right _ _).trans hlt.le)
      refine hT2 (z.1.re : ℂ) hge (by
        rw [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hneg]; linarith) ?_
      rw [← hzeq]; exact z.2
  set Zn := hnearfin.toFinset with hZn
  set wt : {z : ℂ // airyPQN P Q z = 0} → ℝ := fun z => ‖airyPQD P Q z.1 / airyPQN' P Q z.1 ^ 2‖ with hwt
  set W : ℝ := 882 * π ^ 2 with hW
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
  rw [← Finset.sum_filter_add_sum_filter_not S (fun z => z.1.re ≤ -T)]
  set Sf := S.filter (fun z => z.1.re ≤ -T) with hSf
  set Sn := S.filter (fun z => ¬ z.1.re ≤ -T) with hSn
  -- near part
  have hnearsum : ∑ z ∈ Sn, ‖f z.1 * (airyPQD P Q z.1 / airyPQN' P Q z.1 ^ 2)‖ ≤
      (∑ z ∈ Zn, wt z * Cz z) * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := by
    have hsub : Sn ⊆ Zn := by
      intro z hz
      have := (Finset.mem_filter.mp hz).2
      rw [hZn, Set.Finite.mem_toFinset]
      show -T < z.1.re
      push Not at this; exact this
    calc ∑ z ∈ Sn, ‖f z.1 * (airyPQD P Q z.1 / airyPQN' P Q z.1 ^ 2)‖
        ≤ ∑ z ∈ Zn, ‖f z.1 * (airyPQD P Q z.1 / airyPQN' P Q z.1 ^ 2)‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
      _ ≤ ∑ z ∈ Zn, wt z * Cz z * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := by
          refine Finset.sum_le_sum fun z _ => ?_
          rw [norm_mul, mul_comm]
          have := mul_le_mul_of_nonneg_left (hCz z hf hfi hC hb)
            (norm_nonneg (airyPQD P Q z.1 / airyPQN' P Q z.1 ^ 2))
          simp only [hwt]
          linarith
      _ = _ := by rw [Finset.sum_mul]
  -- far part
  have hfar : ∑ z ∈ Sf, ‖f z.1 * (airyPQD P Q z.1 / airyPQN' P Q z.1 ^ 2)‖ ≤
      (W * (4 / π) * (1 + Real.exp 4) * K) * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := by
    set c : {z : ℂ // airyPQN P Q z = 0} → ℝ := fun z => √(-z.1.re) with hc
    set r : {z : ℂ // airyPQN P Q z = 0} → ℝ := fun z => 1 / (4 * c z ^ 2) with hr
    have hfarmem : ∀ z ∈ Sf, z.1.re ≤ -T := fun z hz => (Finset.mem_filter.mp hz).2
    have hfarmem1 : ∀ z ∈ Sf, z.1.re ≤ -1 := fun z hz => by linarith [hfarmem z hz]
    have hc1 : ∀ z ∈ Sf, 1 ≤ c z := fun z hz => ncRoot_ge_one (hfarmem1 z hz)
    have hr0 : ∀ z ∈ Sf, 0 < r z := fun z hz => by
      have := hc1 z hz; simp only [hr]; positivity
    have hAi : ∀ z ∈ Sf, airyAi z.1.re ≠ 0 := fun z hz => by
      have h0 : T0 ≤ T := le_max_left _ _
      have := hfarmem z hz
      exact airyPQ_airyAi_ne (hT0 z.1.re (by linarith)) (airyPQ_zero_ofReal hHB z)
    -- pointwise bound
    have hpt : ∀ z ∈ Sf, ‖f z.1 * (airyPQD P Q z.1 / airyPQN' P Q z.1 ^ 2)‖ ≤
        W * (4 / π) * ((∫ t : ℝ, g t * (r z ^ 2 / ((t - c z) ^ 2 + r z ^ 2))) +
          Real.exp 4 * ∫ t : ℝ, g t * (r z ^ 2 / ((t + c z) ^ 2 + r z ^ 2))) := by
      intro z hz
      have ht := hfarmem z hz
      have hz0 := airyPQ_zero_ofReal hHB z
      have hzeq := airyPQ_zero_eq_ofReal hHB z.2
      have hcz1 := hc1 z hz
      have hcz0 : 0 < c z := by linarith
      have hsq : c z ^ 2 = -z.1.re := by
        simp only [hc]; rw [Real.sq_sqrt (by linarith [hfarmem1 z hz])]
      have hw := hT1 z.1.re (by have : T1 ≤ T := le_max_right _ _; linarith) hz0
      have hw' : ‖airyPQD P Q (z.1.re : ℂ) / airyPQN' P Q (z.1.re : ℂ) ^ 2‖ ≤ W * (1 / c z) := hw
      have hfar := airyQ_far_le hf hfi hC hb hcz1
      have hre : ((-(c z ^ 2) : ℝ) : ℂ) = (z.1.re : ℂ) := by rw [hsq]; push_cast; ring
      rw [hre] at hfar
      rw [hzeq, norm_mul]
      have e1 : ‖f (z.1.re : ℂ)‖ * ‖airyPQD P Q (z.1.re : ℂ) / airyPQN' P Q (z.1.re : ℂ) ^ 2‖ ≤
          ‖f (z.1.re : ℂ)‖ * (W * (1 / c z)) := mul_le_mul_of_nonneg_left hw' (norm_nonneg _)
      refine e1.trans ?_
      have e2 : ‖f (z.1.re : ℂ)‖ * (W * (1 / c z)) = W * (‖f (z.1.re : ℂ)‖ / c z) := by ring
      rw [e2]
      refine (mul_le_mul_of_nonneg_left hfar hW0).trans (le_of_eq ?_)
      ring
    -- integrability
    have hk1 : ∀ z ∈ Sf, Integrable (fun t : ℝ => g t * (r z ^ 2 / ((t - c z) ^ 2 + r z ^ 2))) := fun z hz =>
      integrable_mul_kern hgi (c z) (r z) (hr0 z hz)
    have hk2 : ∀ z ∈ Sf, Integrable (fun t : ℝ => g t * (r z ^ 2 / ((t + c z) ^ 2 + r z ^ 2))) := fun z hz => by
      have := integrable_mul_kern hgi (-c z) (r z) (hr0 z hz)
      simpa [sub_neg_eq_add] using this
    -- kernel sum hypotheses
    have hinj : Set.InjOn (fun z : {z : ℂ // airyPQN P Q z = 0} => airyNIdx z.1.re) (Sf : Set _) := by
      intro z₁ h₁ z₂ h₂ h12
      have e1 := hfarmem z₁ h₁
      have e2 := hfarmem z₂ h₂
      have h0 : T0 ≤ T := le_max_left _ _
      have := airyPQ_injOn_far hHB hT0 (by linarith) (by linarith) (airyPQ_zero_ofReal hHB z₁)
        (airyPQ_zero_ofReal hHB z₂) h12
      apply Subtype.ext
      rw [airyPQ_zero_eq_ofReal hHB z₁.2, airyPQ_zero_eq_ofReal hHB z₂.2, this]
    have hKs := hK Sf (fun z hz => by have := hc1 z hz; simp only [hc] at this ⊢; linarith)
      (fun z hz => by
        have := airyPQ_root_growth (hAi z hz) (hfarmem1 z hz)
        simpa using this)
      hinj
      (fun z₁ h₁ z₂ h₂ hne => by
        have := airyPQ_root_sep_abs (hAi z₁ h₁) (hAi z₂ h₂) (hfarmem1 z₁ h₁) (hfarmem1 z₂ h₂)
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
      have e : ∀ z : {z : ℂ // airyPQN P Q z = 0}, (t + c z) ^ 2 = (-t - c z) ^ 2 := fun z => by ring
      simp only [e]
      simp only [hr, hc] at this ⊢
      nlinarith [hg0 t]
    calc ∑ z ∈ Sf, ‖f z.1 * (airyPQD P Q z.1 / airyPQN' P Q z.1 ^ 2)‖
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

/-- **Absolute summability** of the quadrature series over the zeros of a Hermite-Biehler `N = P Ai + Q Ai'`. -/
theorem airyPQ_summable {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfi : Integrable (fun x : ℝ => f (x : ℂ))) {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    Summable (fun z : {z : ℂ // airyPQN P Q z = 0} => ‖f z * (airyPQD P Q z / airyPQN' P Q z ^ 2)‖) := by
  obtain ⟨B, -, hB⟩ := airyPQ_sampling_sum hHB hQ
  exact summable_of_sum_le (fun z => norm_nonneg _) (fun S => hB hf hfi hC hb S)

/-- **Theorem Q (4) for a Hermite-Biehler `N = P Ai + Q Ai'`, unconditional** (`SOFT_EDGE_THEOREMS.md` Lemma 4.6): for `f` entire,
`‖f(u)‖ ≤ C (1+|u|)^ν e(u)` (any real `ν`), `f ∈ L¹(ℝ)`: `∫_ℝ f = Σ_{N(z)=0} f(z) D(z)/N'(z)²`, absolutely convergent;
the zeros are real and simple and the weights `D/N'²` are positive. -/
theorem airyPQ_hasSum_unc {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfi : Integrable (fun x : ℝ => f (x : ℂ))) {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    HasSum (fun z : {z : ℂ // airyPQN P Q z = 0} => f z * (airyPQD P Q z / airyPQN' P Q z ^ 2))
      (∫ x : ℝ, f (x : ℂ)) :=
  airyPQ_hasSum hHB hQ hf hfi hC hb (airyPQ_summable hHB hQ hf hfi hC hb).of_norm

/-- info: 'FormalResearch.Special.airyPQ_sampling_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_sampling_sum

/-- info: 'FormalResearch.Special.airyPQ_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_summable

/-- info: 'FormalResearch.Special.airyPQ_hasSum_unc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_hasSum_unc

end FormalResearch.Special
