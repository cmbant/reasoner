module

public import FormalResearch.Special.AiryTransformProj
public import FormalResearch.Special.AiryTransformEnv

/-!
# Complex evaluation on the Airy Paley–Wiener space: `Ψφ` is entire with growth `√(1+|z|) e(z)^{1/2}`

For `φ ∈ L²(ℝ)` put `Ψφ(z) = ∫_{t>0} φ(t) Ai(z+t) dt` for **complex** `z` (`airyPsiC`); on real `z = u` this is
the Airy transform `A(Pφ)(u)` (`airyA_indProj_ae`, `airyPsiC_ofReal`).  Proved:

* `norm_airyPsiC_le`: `‖Ψφ(z)‖² ≤ ‖φ‖² κ(z̄)`, `κ(z) = ‖1_{t>0} Ai(z+·)‖² = K(z,z̄)` (Cauchy–Schwarz), and by
  `AiryTransformEnv`, `‖Ψφ(z)‖² ≤ 23 ‖φ‖² (1+|z|) e(z)`, `e(z) = exp(-(4/3) Re z^{3/2})`;
* `differentiable_airyPsiC`: **`Ψφ` is entire**.  Proof: the truncations `Ψ_R φ(z) = ∫_{0<t≤R} φ(t) Ai(z+t) dt` are
  entire (differentiation under the integral on a finite interval, bound by `‖φ‖₁ · sup |Ai'|` on a compact
  set), and `‖Ψφ(z) - Ψ_R φ(z)‖ ≤ ‖1_{t>R} φ‖ √κ(z̄) → 0` locally uniformly in `z`, so `Ψφ` is entire
  (`TendstoLocallyUniformlyOn.differentiableOn`).

Together with `AiryTransformProj` this gives the entire-function model `PW = {Ψφ : φ ∈ L²(0,∞)}` of the Airy
Paley–Wiener space; the Parseval sum at the Airy zeros is in `AiryTransformParseval`.

**Not formalised:** the sharp exponent `(1+|z|)^{1/2}` (not needed), and any converse "every entire `F` with the growth
bound and `F ∈ L²(ℝ)` lies in `PW`" (Paley–Wiener–Schwartz direction, survey item T7).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped ComplexInnerProductSpace Real

namespace FormalResearch.Special

lemma airyHalfC_memLp (w : ℂ) :
    MemLp (fun t : ℝ => (Ioi (0 : ℝ)).indicator (fun t : ℝ => airyAiC (w + (t : ℂ))) t) 2 volume := by
  have hc : Continuous fun t : ℝ => airyAiC (w + (t : ℂ)) :=
    differentiable_airyAiC.continuous.comp (continuous_const.add Complex.continuous_ofReal)
  have hm : AEStronglyMeasurable
      (fun t : ℝ => (Ioi (0 : ℝ)).indicator (fun t : ℝ => airyAiC (w + (t : ℂ))) t) volume :=
    hc.aestronglyMeasurable.indicator measurableSet_Ioi
  rw [memLp_two_iff_integrable_sq_norm hm]
  have h := integrableOn_airyAiC_sq w
  rw [← integrable_indicator_iff measurableSet_Ioi] at h
  refine h.congr (Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Ioi (0 : ℝ) <;> simp [ht]

/-- `t ↦ 1_{t>0} Ai(w+t)` as an element of `L²(ℝ)`, `w ∈ ℂ`. -/
noncomputable def airyHalfC (w : ℂ) : AiryL2 := (airyHalfC_memLp w).toLp _

lemma airyHalfC_coeFn (w : ℂ) :
    airyHalfC w =ᵐ[volume] fun t : ℝ => (Ioi (0 : ℝ)).indicator (fun t : ℝ => airyAiC (w + (t : ℂ))) t :=
  (airyHalfC_memLp w).coeFn_toLp

lemma norm_airyHalfC_sq (w : ℂ) : ‖airyHalfC w‖ ^ 2 = airyKappa w := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (airyHalfC w)
  rw [MeasureTheory.L2.inner_def] at h
  have h2 : ∫ t, (inner ℂ (airyHalfC w t) (airyHalfC w t) : ℂ) =
      ((∫ t : ℝ in Ioi (0 : ℝ), ‖airyAiC (w + (t : ℂ))‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae ?_
    filter_upwards [airyHalfC_coeFn w] with t ht
    rw [ht]
    by_cases hh : t ∈ Ioi (0 : ℝ)
    · simp [hh, inner_self_eq_norm_sq_to_K]
    · simp [hh]
  rw [h2] at h
  apply Complex.ofReal_injective
  unfold airyKappa
  push_cast at h ⊢
  exact h.symm

lemma airyHalfC_ofReal (x : ℝ) : airyHalfC (x : ℂ) = airyHalf x := by
  refine Lp.ext ?_
  filter_upwards [airyHalfC_coeFn (x : ℂ), airyHalf_coeFn x] with t h1 h2
  rw [h1, h2]
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · simp [ht, ← Complex.ofReal_add, airyAiC_ofReal]
  · simp [ht]

/-- `Ψφ(z) = ∫_{t>0} φ(t) Ai(z+t) dt`, `z ∈ ℂ`. -/
noncomputable def airyPsiC (φ : AiryL2) (z : ℂ) : ℂ := ∫ t : ℝ in Ioi (0 : ℝ), φ t * airyAiC (z + (t : ℂ))

lemma airyPsiC_ofReal (φ : AiryL2) (x : ℝ) : airyPsiC φ (x : ℂ) = airyPsi φ x := by
  unfold airyPsiC airyPsi
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp [← Complex.ofReal_add, airyAiC_ofReal]

/-- `Ψφ(z) = ⟨1_{t>0} Ai(z̄+·), φ⟩`. -/
lemma airyPsiC_eq_inner (φ : AiryL2) (z : ℂ) :
    airyPsiC φ z = inner ℂ (airyHalfC ((starRingEnd ℂ) z)) φ := by
  rw [MeasureTheory.L2.inner_def, airyPsiC, ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae ?_
  filter_upwards [airyHalfC_coeFn ((starRingEnd ℂ) z)] with t ht
  rw [ht, RCLike.inner_apply]
  by_cases hh : t ∈ Ioi (0 : ℝ)
  · simp only [Set.indicator_of_mem hh]
    have e : (starRingEnd ℂ) (airyAiC ((starRingEnd ℂ) z + (t : ℂ))) = airyAiC (z + (t : ℂ)) := by
      rw [conj_airyAiC]; simp
    rw [e]
  · simp [hh]

lemma norm_airyPsiC_le (φ : AiryL2) (z : ℂ) :
    ‖airyPsiC φ z‖ ≤ ‖φ‖ * √(airyKappa ((starRingEnd ℂ) z)) := by
  rw [airyPsiC_eq_inner]
  refine (norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_
  rw [mul_comm]
  gcongr
  rw [← norm_airyHalfC_sq, Real.sqrt_sq (norm_nonneg _)]

/-- `‖Ψφ(z)‖² ≤ 23 ‖φ‖² (1+‖z‖) e(z)`. -/
theorem norm_airyPsiC_sq_le (φ : AiryL2) (z : ℂ) :
    ‖airyPsiC φ z‖ ^ 2 ≤ 23 * ‖φ‖ ^ 2 * (1 + ‖z‖) * airyEnv z := by
  have h1 := norm_airyPsiC_le φ z
  have h2 := airyKappa_le' ((starRingEnd ℂ) z)
  rw [airyEnv_conj, Complex.norm_conj] at h2
  have h3 := airyKappa_nonneg ((starRingEnd ℂ) z)
  have h4 : ‖airyPsiC φ z‖ ^ 2 ≤ (‖φ‖ * √(airyKappa ((starRingEnd ℂ) z))) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [mul_pow, Real.sq_sqrt h3] at h4
  calc ‖airyPsiC φ z‖ ^ 2 ≤ ‖φ‖ ^ 2 * airyKappa ((starRingEnd ℂ) z) := h4
    _ ≤ ‖φ‖ ^ 2 * (23 * (1 + ‖z‖) * airyEnv z) := by gcongr
    _ = _ := by ring

/-! ### Entireness -/

/-- The tail projection onto `L²(R, ∞)`. -/
noncomputable def airyTail (R : ℝ) : AiryL2 →L[ℂ] AiryL2 := airyIndProj (measurableSet_Ioi (a := R))

lemma norm_airyTail_sq (R : ℝ) (φ : AiryL2) :
    ‖airyTail R φ‖ ^ 2 = ∫ t, (Ioi R).indicator (fun t => ‖φ t‖ ^ 2) t := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (airyTail R φ)
  rw [MeasureTheory.L2.inner_def] at h
  have h2 : ∫ t, (inner ℂ (airyTail R φ t) (airyTail R φ t) : ℂ) =
      ((∫ t, (Ioi R).indicator (fun t => ‖φ t‖ ^ 2) t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [airyIndProj_coeFn (measurableSet_Ioi (a := R)) φ] with t ht
    show inner ℂ (airyIndProj (measurableSet_Ioi (a := R)) φ t) (airyIndProj (measurableSet_Ioi (a := R)) φ t) = _
    rw [ht]
    by_cases hh : t ∈ Ioi R
    · simp [hh, inner_self_eq_norm_sq_to_K]
    · simp [hh]
  rw [h2] at h
  apply Complex.ofReal_injective
  push_cast at h ⊢
  exact h.symm

lemma tendsto_norm_airyTail (φ : AiryL2) :
    Tendsto (fun n : ℕ => ‖airyTail (n : ℝ) φ‖) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ∫ t, (Ioi (n : ℝ)).indicator (fun t => ‖φ t‖ ^ 2) t) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := (volume : Measure ℝ))
      (F := fun (n : ℕ) t => (Ioi (n : ℝ)).indicator (fun t => ‖φ t‖ ^ 2) t)
      (f := fun _ => (0 : ℝ)) (fun t => ‖φ t‖ ^ 2) ?_ (integrable_norm_sq_lp φ) ?_ ?_
    · simpa using this
    · intro n
      exact ((integrable_norm_sq_lp φ).indicator measurableSet_Ioi).aestronglyMeasurable
    · intro n
      refine Eventually.of_forall fun t => ?_
      by_cases ht : t ∈ Ioi (n : ℝ) <;> simp [ht]
    · refine Eventually.of_forall fun t => ?_
      have : ∀ᶠ n : ℕ in atTop, t ∉ Ioi (n : ℝ) := by
        filter_upwards [eventually_ge_atTop (⌈t⌉₊)] with n hn
        simp only [mem_Ioi, not_lt]
        exact (Nat.le_ceil t).trans (by exact_mod_cast hn)
      exact tendsto_const_nhds.congr' (by filter_upwards [this] with n hn; simp [hn])
  have h2 : Tendsto (fun n : ℕ => √(∫ t, (Ioi (n : ℝ)).indicator (fun t => ‖φ t‖ ^ 2) t)) atTop (𝓝 0) := by
    have := h.sqrt
    simpa only [Real.sqrt_zero] using this
  refine h2.congr fun n => ?_
  rw [← norm_airyTail_sq, Real.sqrt_sq (norm_nonneg _)]

lemma continuous_deriv_airyAiC : Continuous (deriv airyAiC) :=
  continuous_iff_continuousAt.mpr fun z => (hasDerivAt_deriv_airyAiC z).continuousAt

lemma continuous_airyAiC : Continuous airyAiC := differentiable_airyAiC.continuous

/-- Truncated transform `Ψ_R φ(z) = ∫_{0<t≤R} φ(t) Ai(z+t) dt`. -/
noncomputable def airyPsiTrunc (φ : AiryL2) (R : ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioc (0 : ℝ) R, φ t * airyAiC (z + (t : ℂ))

lemma integrableOn_airyL2_Icc (φ : AiryL2) (a b : ℝ) : IntegrableOn (fun t => (φ t : ℂ)) (Icc a b) :=
  ((Lp.memLp φ).locallyIntegrable (by norm_num)).integrableOn_isCompact isCompact_Icc

lemma differentiable_airyPsiTrunc (φ : AiryL2) (R : ℝ) : Differentiable ℂ (airyPsiTrunc φ R) := by
  intro z₀
  -- compact set of arguments
  set Kc : Set ℂ := (fun p : ℂ × ℝ => p.1 + (p.2 : ℂ)) '' (Metric.closedBall z₀ 1 ×ˢ Icc (0 : ℝ) R) with hKc
  have hKcomp : IsCompact Kc :=
    ((isCompact_closedBall z₀ 1).prod isCompact_Icc).image
      (by fun_prop : Continuous fun p : ℂ × ℝ => p.1 + (p.2 : ℂ))
  obtain ⟨M1, hM1⟩ := hKcomp.exists_bound_of_continuousOn continuous_airyAiC.continuousOn
  obtain ⟨M2, hM2⟩ := hKcomp.exists_bound_of_continuousOn continuous_deriv_airyAiC.continuousOn
  have hmem : ∀ z ∈ Metric.closedBall z₀ 1, ∀ t ∈ Ioc (0 : ℝ) R, z + (t : ℂ) ∈ Kc := fun z hz t ht =>
    ⟨(z, t), ⟨hz, ⟨ht.1.le, ht.2⟩⟩, rfl⟩
  have hint : IntegrableOn (fun t => (φ t : ℂ)) (Ioc (0 : ℝ) R) :=
    (integrableOn_airyL2_Icc φ 0 R).mono_set Ioc_subset_Icc_self
  have hφm : AEStronglyMeasurable (fun t => (φ t : ℂ)) (volume.restrict (Ioc (0 : ℝ) R)) :=
    (Lp.aestronglyMeasurable φ).restrict
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioc (0 : ℝ) R))
    (F := fun (z : ℂ) (t : ℝ) => φ t * airyAiC (z + (t : ℂ)))
    (F' := fun (z : ℂ) (t : ℝ) => φ t * deriv airyAiC (z + (t : ℂ)))
    (x₀ := z₀) (s := Metric.ball z₀ 1) (bound := fun t => ‖φ t‖ * M2)
    (Metric.ball_mem_nhds z₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact key.2.differentiableAt
  · exact Eventually.of_forall fun z => hφm.mul
      (continuous_airyAiC.comp (continuous_const.add Complex.continuous_ofReal)).aestronglyMeasurable
  · refine (hint.norm.mul_const M1).mono' (hφm.mul
      (continuous_airyAiC.comp (continuous_const.add Complex.continuous_ofReal)).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hM1 _ (hmem z₀ (Metric.mem_closedBall_self one_pos.le) t ht))
      (norm_nonneg _)
  · exact hφm.mul
      (continuous_deriv_airyAiC.comp (continuous_const.add Complex.continuous_ofReal)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht z hz => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hM2 _ (hmem z (Metric.ball_subset_closedBall hz) t ht))
      (norm_nonneg _)
  · exact hint.norm.mul_const M2
  · refine Eventually.of_forall fun t => ?_
    intro z _
    have h1 : HasDerivAt airyAiC (deriv airyAiC (z + (t : ℂ))) (z + (t : ℂ)) :=
      (differentiable_airyAiC _).hasDerivAt
    exact (h1.comp_add_const z (t : ℂ)).const_mul (φ t)

lemma integrableOn_airyPsiC_integrand (φ : AiryL2) (z : ℂ) :
    IntegrableOn (fun t : ℝ => φ t * airyAiC (z + (t : ℂ))) (Ioi (0 : ℝ)) := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (airyHalfC ((starRingEnd ℂ) z)) φ
  rw [← integrable_indicator_iff measurableSet_Ioi]
  refine h.congr ?_
  filter_upwards [airyHalfC_coeFn ((starRingEnd ℂ) z)] with t ht
  rw [ht, RCLike.inner_apply]
  by_cases hh : t ∈ Ioi (0 : ℝ)
  · simp only [Set.indicator_of_mem hh]
    have e : (starRingEnd ℂ) (airyAiC ((starRingEnd ℂ) z + (t : ℂ))) = airyAiC (z + (t : ℂ)) := by
      rw [conj_airyAiC]; simp
    rw [e]
  · simp [hh]

lemma airyPsiC_split (φ : AiryL2) (z : ℂ) {n : ℝ} (hn : 0 ≤ n) :
    airyPsiC φ z = airyPsiTrunc φ n z + airyPsiC (airyTail n φ) z := by
  have hI := integrableOn_airyPsiC_integrand φ z
  have e1 : airyPsiC (airyTail n φ) z = ∫ t : ℝ in Ioi n, φ t * airyAiC (z + (t : ℂ)) := by
    unfold airyPsiC
    have : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), (airyTail n φ t) * airyAiC (z + (t : ℂ)) =
        (Ioi n).indicator (fun t : ℝ => φ t * airyAiC (z + (t : ℂ))) t := by
      filter_upwards [ae_restrict_of_ae (airyIndProj_coeFn (measurableSet_Ioi (a := n)) φ)] with t ht
      show (airyIndProj (measurableSet_Ioi (a := n)) φ t) * _ = _
      rw [ht]
      by_cases hh : t ∈ Ioi n <;> simp [hh]
    rw [integral_congr_ae this, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi,
      max_eq_right hn]
  rw [e1, airyPsiC, airyPsiTrunc]
  conv_lhs => rw [← Ioc_union_Ioi_eq_Ioi hn]
  refine setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi ?_ ?_
  · rw [← Ioc_union_Ioi_eq_Ioi hn] at hI; exact hI.mono_set subset_union_left
  · rw [← Ioc_union_Ioi_eq_Ioi hn] at hI; exact hI.mono_set subset_union_right

lemma airyKappa_conj_le (z : ℂ) {r : ℝ} (hr : ‖z‖ ≤ r) :
    airyKappa ((starRingEnd ℂ) z) ≤ 23 * (1 + r) * Real.exp ((4 / 3) * r ^ (3 / 2 : ℝ)) := by
  have h1 := airyKappa_le' ((starRingEnd ℂ) z)
  rw [airyEnv_conj, Complex.norm_conj] at h1
  have h2 : airyEnv z ≤ Real.exp ((4 / 3) * r ^ (3 / 2 : ℝ)) := by
    unfold airyEnv
    refine Real.exp_le_exp.mpr ?_
    have := re_cpow_three_halves_le z
    have h3 : ‖z‖ ^ (3 / 2 : ℝ) ≤ r ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg _) hr (by norm_num)
    nlinarith
  have h4 : 0 ≤ 23 * (1 + ‖z‖) := by positivity
  calc airyKappa ((starRingEnd ℂ) z) ≤ 23 * (1 + ‖z‖) * airyEnv z := h1
    _ ≤ 23 * (1 + r) * Real.exp ((4 / 3) * r ^ (3 / 2 : ℝ)) := by
        apply mul_le_mul (by linarith) h2 (airyEnv_pos z).le (by linarith [norm_nonneg z])

lemma tendstoLocallyUniformly_airyPsiTrunc (φ : AiryL2) :
    TendstoLocallyUniformly (fun n : ℕ => airyPsiTrunc φ (n : ℝ)) (airyPsiC φ) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨r, hr⟩ := hK.isBounded.exists_norm_le
  set r' := max r 0 with hr'
  have hr'0 : 0 ≤ r' := le_max_right _ _
  set C := √(23 * (1 + r') * Real.exp ((4 / 3) * r' ^ (3 / 2 : ℝ))) + 1 with hC
  have hCpos : 0 < C := by positivity
  have h := (tendsto_norm_airyTail φ).eventually (Iio_mem_nhds (show 0 < ε / C by positivity))
  filter_upwards [h] with n hn z hz
  have hz' : ‖z‖ ≤ r' := (hr z hz).trans (le_max_left _ _)
  rw [dist_eq_norm, airyPsiC_split φ z (Nat.cast_nonneg n), add_sub_cancel_left]
  have h1 := norm_airyPsiC_le (airyTail (n : ℝ) φ) z
  have h2 := airyKappa_conj_le z hz'
  have h3 : √(airyKappa ((starRingEnd ℂ) z)) ≤ C := by
    have := Real.sqrt_le_sqrt h2
    linarith
  have h4 : ‖airyTail (n : ℝ) φ‖ * C < ε := by
    have := mul_lt_mul_of_pos_right (show ‖airyTail (n : ℝ) φ‖ < ε / C from hn) hCpos
    rwa [div_mul_cancel₀ _ hCpos.ne'] at this
  calc ‖airyPsiC (airyTail (n : ℝ) φ) z‖ ≤ ‖airyTail (n : ℝ) φ‖ * √(airyKappa ((starRingEnd ℂ) z)) := h1
    _ ≤ ‖airyTail (n : ℝ) φ‖ * C := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ < ε := h4

/-- **`Ψφ` is entire.** -/
theorem differentiable_airyPsiC (φ : AiryL2) : Differentiable ℂ (airyPsiC φ) := by
  have h := (tendstoLocallyUniformly_airyPsiTrunc φ).tendstoLocallyUniformlyOn (s := Set.univ)
  have := h.differentiableOn (Eventually.of_forall fun n =>
    (differentiable_airyPsiTrunc φ (n : ℝ)).differentiableOn) isOpen_univ
  exact differentiableOn_univ.mp this

/-- info: 'FormalResearch.Special.differentiable_airyPsiC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.differentiable_airyPsiC

/-- info: 'FormalResearch.Special.norm_airyPsiC_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.norm_airyPsiC_sq_le

end FormalResearch.Special
