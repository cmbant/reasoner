module

public import FormalResearch.Special.AiryCftQuadrature
public import FormalResearch.Special.AiryCftQArc
public import FormalResearch.Complex.HardyArcDecay

/-!
# Theorem Q (1), (4): the Airy quadrature for the whole class `𝒢`, in limit form

Statement formalised (CFT `AIRY_POISSON.md` Theorem Q (1) and (4), limit form): let `f` be entire with
`‖f(u)‖ ≤ C (1+|u|)^ν e(u)` for some **arbitrary real** `ν`, and `f ∈ L¹(ℝ)` (automatic only for `ν < -1`).  Then

* (`airyQ_defect_le_boundary`) on every good circle `|u| = a²` (zero-free for `Ai`, with the ratio bounds),
  `|Σ_{a_n > -a²} f(a_n)/Ai'(a_n)² - ∫_{-a²}^{a²} f| ≤ 15√π ∫_{x<0} |f|`;
* (`airyQ_tendsto`) along the good circles the partial sums converge to `∫_ℝ f`;
* (`airyQ_hasSum`) if the series `Σ f(a_n)/Ai'(a_n)²` is summable, it sums to `∫_ℝ f`.

Proof: Theorem D in integral form (`airyQ_defect_le_arc`) bounds the defect by `30√π` times the semicircle integral
`a ∫_0^π |G(ae^{iφ})| dφ` of `G(z) = z f(-z²) exp((4/3) i z³)`, which is entire with polynomial growth and
`L¹` boundary values (`AiryCftQUnfold`); the Hardy-space Fejér–Riesz bounds (`HardyArcDecay`) give `≤ (1/2) ‖G‖_{L¹(ℝ)}
= (1/2) ∫_{x<0}|f|` and `→ 0`.  All **proved**.

The `HasSum` form here (`airyQ_hasSum`) assumes summability.  Theorem Q (3), the sampling bound, is now formalised
(`airyQ_sampling` in `AiryCftQSample`, by a weighted Fejér–Riesz bound and a Carleson-type kernel sum; the Poisson representation of `G`
is not needed), and gives summability for every real `ν` with `f ∈ L¹(ℝ)`, so `airyQ_hasSum_unc` (`AiryCftQUnc`) is the hypothesis-free
statement; `airyQ_hasSum` is superseded in scope by it but kept (the sampling modules import this file, so the assumed-summability form
cannot be derived from them here).  Not formalised: the Poisson representation of `G` (Lemma H) and the sharp pointwise bound Theorem Q (2).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- The hypotheses on `f` of Theorem Q, bundled for `airyQG`: `DiffContOnCl`, polynomial growth, integrable boundary. -/
lemma airyQ_hardy_hyp {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    DiffContOnCl ℂ (airyQG f) {z : ℂ | 0 < z.im} ∧
      (∀ z : ℂ, 0 ≤ z.im → ‖airyQG f z‖ ≤ C * (1 + ‖z‖) ^ (2 * ⌈max ν 0⌉₊ + 1)) ∧
      Integrable (fun x : ℝ => airyQG f (x : ℂ)) :=
  ⟨(airyQ_differentiable_G hf).diffContOnCl, fun _ hz => airyQ_G_growth hC hb hz, (airyQ_boundary hf hfi).1⟩

/-- **Theorem Q (1), defect bound.**  On a good circle `|u| = a²`:
`|Σ_{n ≤ N} f(a_n)/Ai'(a_n)² - ∫_{-a²}^{a²} f| ≤ 15√π ∫_{x<0} |f|`. -/
theorem airyQ_defect_le_boundary {N : ℕ} {a : ℝ} (ha : 0 < a)
    (hD : CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) (a ^ 2))
    (hup : ∀ u : ℂ, ‖u‖ = a ^ 2 → 0 ≤ u.im →
      ‖(airyBiC u - I * airyAiC u) / airyAiC u‖ * airyEnv u ≤ 30 * √π)
    (hlo : ∀ u : ℂ, ‖u‖ = a ^ 2 → u.im ≤ 0 →
      ‖(airyBiC u + I * airyAiC u) / airyAiC u‖ * airyEnv u ≤ 30 * √π)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    ‖(∑ n ∈ Finset.Icc 1 N, f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2) -
        ∫ x in (-(a ^ 2))..(a ^ 2), f (x : ℂ)‖ ≤ 15 * √π * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := by
  obtain ⟨h1, h2, h3⟩ := airyQ_hardy_hyp hf hfi hC hb
  have h4 := FormalResearch.Hardy.hardy_arc_le_poly h1 h2 h3 ha
  rw [(airyQ_boundary hf hfi).2] at h4
  refine (airyQ_defect_le_arc ha hD hup hlo hf).trans ?_
  have : 0 ≤ √π := Real.sqrt_nonneg _
  nlinarith

/-- **Theorem Q (1) + (4), limit form.**  For `f` entire with `‖f(u)‖ ≤ C (1+|u|)^ν e(u)` (any real `ν`) and
`f ∈ L¹(ℝ)`, the partial sums `Σ_{n ≤ N_k} f(a_n)/Ai'(a_n)²` over the good circles converge to `∫_ℝ f`. -/
theorem airyQ_tendsto {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    ∃ N : ℕ → ℕ, Tendsto N atTop atTop ∧
      Tendsto (fun k => ∑ n ∈ Finset.Icc 1 (N k), f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2)
        atTop (𝓝 (∫ x : ℝ, f (x : ℂ))) := by
  obtain ⟨r, N, h1, h3, h4, h5, h6⟩ := airyCft_circles_ratio
  refine ⟨N, airyCft_N_tendsto h1 h3, ?_⟩
  obtain ⟨hG1, hG2, hG3⟩ := airyQ_hardy_hyp hf hfi hC hb
  have hr0 : ∀ k, 0 < r k := fun k => by linarith [h1 k, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hrt : Tendsto r atTop atTop :=
    tendsto_atTop_mono (f := fun k : ℕ => (k : ℝ) + 10) (fun k => h1 k)
      (tendsto_atTop_add_const_right _ (10 : ℝ) tendsto_natCast_atTop_atTop)
  have hrt' : Tendsto (fun k => -r k) atTop atBot := tendsto_neg_atTop_atBot.comp hrt
  have hI : Tendsto (fun k => ∫ x in (-(r k))..(r k), f (x : ℂ)) atTop (𝓝 (∫ x : ℝ, f (x : ℂ))) :=
    intervalIntegral_tendsto_integral hfi hrt' hrt
  have hsq : Tendsto (fun k => √(r k)) atTop atTop := Real.tendsto_sqrt_atTop.comp hrt
  have hA := (FormalResearch.Hardy.hardy_arc_tendsto_zero hG1 hG2 hG3).comp hsq
  have hdef : ∀ k, ‖(∑ n ∈ Finset.Icc 1 (N k), f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2) -
      ∫ x in (-(r k))..(r k), f (x : ℂ)‖ ≤
      30 * √π * (√(r k) * ∫ φ in (0 : ℝ)..π, ‖airyQG f (circleMap 0 (√(r k)) φ)‖) := by
    intro k
    have hpos : 0 < √(r k) := Real.sqrt_pos.mpr (hr0 k)
    have e2 : √(r k) ^ 2 = r k := Real.sq_sqrt (hr0 k).le
    have := airyQ_defect_le_arc hpos (by rw [e2]; exact h4 k)
      (fun u hu hi => h5 k u (by rw [hu, e2]) hi) (fun u hu hi => h6 k u (by rw [hu, e2]) hi) hf
    rwa [e2] at this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hI' : Tendsto (fun k => ‖(∫ x in (-(r k))..(r k), f (x : ℂ)) - ∫ x : ℝ, f (x : ℂ)‖) atTop (𝓝 0) := by
    have := hI.sub_const (∫ x : ℝ, f (x : ℂ))
    rw [sub_self] at this
    simpa using this.norm
  have hE : Tendsto (fun k => ‖(∫ x in (-(r k))..(r k), f (x : ℂ)) - ∫ x : ℝ, f (x : ℂ)‖ +
      30 * √π * (√(r k) * ∫ φ in (0 : ℝ)..π, ‖airyQG f (circleMap 0 (√(r k)) φ)‖)) atTop (𝓝 0) := by
    simpa using hI'.add (hA.const_mul (30 * √π))
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hE
  calc _ ≤ ‖(∑ n ∈ Finset.Icc 1 (N k), f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2) -
      ∫ x in (-(r k))..(r k), f (x : ℂ)‖ + ‖(∫ x in (-(r k))..(r k), f (x : ℂ)) - ∫ x : ℝ, f (x : ℂ)‖ := by
        have := norm_add_le ((∑ n ∈ Finset.Icc 1 (N k), f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2) -
          ∫ x in (-(r k))..(r k), f (x : ℂ)) ((∫ x in (-(r k))..(r k), f (x : ℂ)) - ∫ x : ℝ, f (x : ℂ))
        rwa [sub_add_sub_cancel] at this
    _ ≤ _ := by rw [add_comm]; gcongr; exact hdef k

/-- **Theorem Q (4), `HasSum` form.**  If `Σ_n f(a_n)/Ai'(a_n)²` is summable, its sum is `∫_ℝ f`. -/
theorem airyQ_hasSum {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hs : Summable (fun n : ℕ => f (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2)) :
    HasSum (fun n : ℕ => f (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2)
      (∫ x : ℝ, f (x : ℂ)) := by
  obtain ⟨N, hN, ht⟩ := airyQ_tendsto hf hfi hC hb
  have h1 : Tendsto (fun k => ∑ j ∈ Finset.range (N k),
      f (airyZero (j + 1) : ℂ) / (deriv airyAiC (airyZero (j + 1) : ℂ)) ^ 2) atTop (𝓝 (∑' j,
      f (airyZero (j + 1) : ℂ) / (deriv airyAiC (airyZero (j + 1) : ℂ)) ^ 2)) :=
    (hs.hasSum.tendsto_sum_nat).comp hN
  have h2 : Tendsto (fun k => ∑ j ∈ Finset.range (N k),
      f (airyZero (j + 1) : ℂ) / (deriv airyAiC (airyZero (j + 1) : ℂ)) ^ 2) atTop (𝓝 (∫ x : ℝ, f (x : ℂ))) := by
    refine ht.congr fun k => ?_
    exact airyCft_sum_Icc (fun n : ℕ => f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2) (N k)
  rw [← tendsto_nhds_unique h1 h2]
  exact hs.hasSum

/-- info: 'FormalResearch.Special.airyQ_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyQ_tendsto

/-- info: 'FormalResearch.Special.airyQ_defect_le_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyQ_defect_le_boundary

/-- info: 'FormalResearch.Special.airyQ_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyQ_hasSum

end FormalResearch.Special
