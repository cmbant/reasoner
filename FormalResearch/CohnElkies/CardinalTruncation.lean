module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import FormalResearch.Special.AiryPwsMain

/-!
# `L¹` and `H^∞` control of squares of `L²` functions under cardinal truncation (GT.0)

Source: `CFT/sign_uncertainty/paper/ce_o1_global_transfer.tex`, Subsection GT.0 (`cegt:GT0`):
"Explicitly, if `H_{c,N} → H_c` in `L²`, then `‖H_{c,N}² − H_c²‖₁ ≤ (‖H_{c,N}‖₂ + ‖H_c‖₂) ‖H_{c,N} − H_c‖₂ → 0`.
The Airy Paley–Wiener estimate of Theorem 3.1 then gives `‖(H_{c,N}²)~ − (H_c²)~‖_{H^∞} ≤ k ‖H_{c,N}² − H_c²‖₁ → 0`."

**Statements proved**:

* `eLpNorm_sq_sub_sq_le` and `tendsto_eLpNorm_sq_sub_sq` (for any `RCLike 𝕜` on `ℝ`):
  `‖H_N² − H²‖₁ ≤ (‖H_N‖₂ + ‖H‖₂) ‖H_N − H‖₂` and its `L² → L¹` limit form.
* `airyFtilde_sq_sub_sq_norm_le`: combining `eLpNorm_sq_sub_sq_le` with `FormalResearch.Special.airyFtilde_norm_le`,
  for `H_N², H² ∈ G` (`AiryClassG`) and `Im ζ ≥ 0`,
  `‖(H_N²)~(ζ) − (H²)~(ζ)‖ ≤ k · ((‖H_N‖₂ + ‖H‖₂) · ‖H_N − H‖₂).toReal` (`k = 2^{2/3}`).
* `tendsto_airyFtilde_sq_sub_sq`: if `H_i → H` in `L²(ℝ)` and `H_i², H² ∈ G`, then `(H_i²)~ → (H²)~` uniformly
  on the closed upper half-plane `{ζ : ℂ | 0 ≤ ζ.im}` (`H^∞` convergence).
-/

@[expose] public section

namespace FormalResearch.CohnElkies

open MeasureTheory Filter Topology
open scoped ENNReal

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Pointwise factorisation: `‖a² − b²‖ = ‖a − b‖ ‖a + b‖ ≤ ‖a − b‖ (‖a‖ + ‖b‖)`. -/
lemma norm_sq_sub_sq_le (a b : 𝕜) : ‖a ^ 2 - b ^ 2‖ ≤ ‖a - b‖ * (‖a‖ + ‖b‖) := by
  have e : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [e, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_add_le a b) (norm_nonneg _)

/-- **CEQ22 (GT.0), inequality form.** For `L²` functions `H_N, H` on `ℝ`,
`‖H_N² − H²‖₁ ≤ (‖H_N‖₂ + ‖H‖₂) ‖H_N − H‖₂`. -/
theorem eLpNorm_sq_sub_sq_le (HN H : ℝ → 𝕜) (hHN : MemLp HN 2 volume) (hH : MemLp H 2 volume) :
    eLpNorm (fun x => HN x ^ 2 - H x ^ 2) 1 volume ≤
      (eLpNorm HN 2 volume + eLpNorm H 2 volume) * eLpNorm (fun x => HN x - H x) 2 volume := by
  have hmeas_sq : AEStronglyMeasurable (fun x => HN x ^ 2 - H x ^ 2) volume :=
    (hHN.aestronglyMeasurable.pow 2).sub (hH.aestronglyMeasurable.pow 2)
  have hd : AEStronglyMeasurable (fun x => ‖HN x - H x‖) volume :=
    (hHN.aestronglyMeasurable.sub hH.aestronglyMeasurable).norm
  have hs : AEStronglyMeasurable (fun x => ‖HN x‖ + ‖H x‖) volume :=
    hHN.aestronglyMeasurable.norm.add hH.aestronglyMeasurable.norm
  -- (a) pointwise domination by a product of real norms
  have step1 : eLpNorm (fun x => HN x ^ 2 - H x ^ 2) 1 volume ≤
      eLpNorm (fun x => ‖HN x - H x‖ * (‖HN x‖ + ‖H x‖)) 1 volume :=
    eLpNorm_mono_real hmeas_sq fun x => norm_sq_sub_sq_le (HN x) (H x)
  -- (b) Hölder with exponents (2, 2, 1) on the product of norms
  have step2 : eLpNorm (fun x => ‖HN x - H x‖ * (‖HN x‖ + ‖H x‖)) 1 volume ≤
      eLpNorm (fun x => ‖HN x - H x‖) 2 volume * eLpNorm (fun x => ‖HN x‖ + ‖H x‖) 2 volume := by
    have hcont : Continuous (fun p : ℝ × ℝ => p.1 * p.2) := continuous_fst.mul continuous_snd
    have hpt : ∀ᵐ x ∂(volume : Measure ℝ),
        ‖(fun a b : ℝ => a * b) (‖HN x - H x‖) (‖HN x‖ + ‖H x‖)‖ ≤
          ((1 : NNReal) : ℝ) * ‖‖HN x - H x‖‖ * ‖‖HN x‖ + ‖H x‖‖ := by
      refine ae_of_all _ fun x => ?_
      have h1 : 0 ≤ ‖HN x - H x‖ := norm_nonneg _
      have h2 : 0 ≤ ‖HN x‖ + ‖H x‖ := by positivity
      simp only [NNReal.coe_one, one_mul, norm_mul, Real.norm_of_nonneg h1,
        Real.norm_of_nonneg h2, le_refl]
    have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := 2) (q := 2) (r := 1)
      (fun a b : ℝ => a * b) 1 hcont hd hs hpt
    simpa using this
  -- (c) Minkowski for the sum of norms, and `‖·‖` does not change the `L²` norm
  have step3 : eLpNorm (fun x => ‖HN x‖ + ‖H x‖) 2 volume ≤
      eLpNorm HN 2 volume + eLpNorm H 2 volume := by
    have h : eLpNorm (fun x => ‖HN x‖ + ‖H x‖) 2 volume
        ≤ eLpNorm (fun x => ‖HN x‖) 2 volume + eLpNorm (fun x => ‖H x‖) 2 volume :=
      eLpNorm_add_le (by norm_num)
    rwa [eLpNorm_norm HN hHN.aestronglyMeasurable, eLpNorm_norm H hH.aestronglyMeasurable] at h
  have hdiff : eLpNorm (fun x => ‖HN x - H x‖) 2 volume = eLpNorm (fun x => HN x - H x) 2 volume :=
    eLpNorm_norm _ (hHN.aestronglyMeasurable.sub hH.aestronglyMeasurable)
  calc eLpNorm (fun x => HN x ^ 2 - H x ^ 2) 1 volume
      ≤ eLpNorm (fun x => ‖HN x - H x‖ * (‖HN x‖ + ‖H x‖)) 1 volume := step1
    _ ≤ eLpNorm (fun x => ‖HN x - H x‖) 2 volume * eLpNorm (fun x => ‖HN x‖ + ‖H x‖) 2 volume :=
        step2
    _ ≤ eLpNorm (fun x => HN x - H x) 2 volume * (eLpNorm HN 2 volume + eLpNorm H 2 volume) := by
        rw [hdiff]
        exact mul_le_mul' le_rfl step3
    _ = (eLpNorm HN 2 volume + eLpNorm H 2 volume) * eLpNorm (fun x => HN x - H x) 2 volume :=
        mul_comm _ _

/-- **CEQ22 (GT.0), limit form.** If `H_i → H` in `L²` along a filter (`‖H_i − H‖₂ → 0`), then
`H_i² → H²` in `L¹` (`‖H_i² − H²‖₁ → 0`). The `H_i` and `H` are `L²` functions on `ℝ`. -/
theorem tendsto_eLpNorm_sq_sub_sq {ι : Type*} {l : Filter ι} (HN : ι → ℝ → 𝕜) (H : ℝ → 𝕜)
    (hHN : ∀ i, MemLp (HN i) 2 volume) (hH : MemLp H 2 volume)
    (hconv : Tendsto (fun i => eLpNorm (fun x => HN i x - H x) 2 volume) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (fun x => HN i x ^ 2 - H x ^ 2) 1 volume) l (𝓝 0) := by
  set K : ℝ≥0∞ := eLpNorm H 2 volume with hK
  have hKtop : K ≠ ⊤ := hH.eLpNorm_lt_top.ne
  set δ : ι → ℝ≥0∞ := fun i => eLpNorm (fun x => HN i x - H x) 2 volume with hδdef
  -- triangle inequality: `‖H_i‖₂ ≤ ‖H_i − H‖₂ + ‖H‖₂`
  have htri : ∀ i, eLpNorm (HN i) 2 volume ≤ δ i + K := by
    intro i
    have h : eLpNorm (fun x => HN i x - H x + H x) 2 volume
        ≤ eLpNorm (fun x => HN i x - H x) 2 volume + eLpNorm H 2 volume :=
      eLpNorm_add_le (by norm_num)
    have e : (fun x => HN i x - H x + H x) = HN i := funext fun x => sub_add_cancel _ _
    rw [e] at h
    exact h
  -- the pointwise bound on the `L¹` norm
  have hbound : ∀ i, eLpNorm (fun x => HN i x ^ 2 - H x ^ 2) 1 volume ≤ ((δ i + K) + K) * δ i := by
    intro i
    have h := eLpNorm_sq_sub_sq_le (HN i) H (hHN i) hH
    exact h.trans (mul_le_mul' (add_le_add (htri i) le_rfl) le_rfl)
  -- the upper bound tends to zero
  have hδt : Tendsto δ l (𝓝 0) := hconv
  have hA : Tendsto (fun i => (δ i + K) + K) l (𝓝 ((0 + K) + K)) :=
    (hδt.add tendsto_const_nhds).add tendsto_const_nhds
  have hKK : (0 + K) + K ≠ ⊤ := by
    rw [zero_add]
    exact ENNReal.add_ne_top.2 ⟨hKtop, hKtop⟩
  have hup : Tendsto (fun i => ((δ i + K) + K) * δ i) l (𝓝 (((0 + K) + K) * 0)) :=
    ENNReal.Tendsto.mul hA (Or.inr ENNReal.zero_ne_top) hδt (Or.inr hKK)
  rw [mul_zero] at hup
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun _ => zero_le) hbound

/-- info: 'FormalResearch.CohnElkies.eLpNorm_sq_sub_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eLpNorm_sq_sub_sq_le

/-- info: 'FormalResearch.CohnElkies.tendsto_eLpNorm_sq_sub_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_eLpNorm_sq_sub_sq

section AiryPws

open FormalResearch.Special

private lemma integrable_airyIntegrand_of_im_nonneg {f : ℂ → ℂ} (hf : AiryClassG f) {ζ : ℂ}
    (hζ : 0 ≤ ζ.im) : Integrable (fun u : ℝ => f (u : ℂ) * Complex.exp (-(Complex.I * ζ * (u : ℂ)))) := by
  obtain ⟨C, N, hC, hb⟩ := hf.bound
  refine (integrable_airyPwsDom hf (C := C) (N := N) 1 (ζ.im + 1)).mono' ?_ ?_
  · exact (hf.differentiable.continuous.comp Complex.continuous_ofReal |>.mul
      (by fun_prop)).aestronglyMeasurable
  · refine Eventually.of_forall fun u => ?_
    simpa only [Real.norm_of_nonneg (norm_nonneg _)] using
      airyPws_norm_integrand_le' hC hb ζ hζ (by linarith) u

private lemma integral_norm_eq_eLpNorm_one_toReal {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g volume) :
    (∫ u : ℝ, ‖g u‖) = (eLpNorm g 1 volume).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => norm_nonneg _) hg.norm,
    eLpNorm_one_eq_lintegral_eNorm hg]
  simp only [ofReal_norm]

/-- The Airy Paley–Wiener class `G` is closed under subtraction. -/
lemma airyClassG_sub {f g : ℂ → ℂ} (hf : AiryClassG f) (hg : AiryClassG g) :
    AiryClassG (fun z => f z - g z) := by
  obtain ⟨Cf, Nf, hCf, hbf⟩ := hf.bound
  obtain ⟨Cg, Ng, hCg, hbg⟩ := hg.bound
  refine ⟨hf.differentiable.sub hg.differentiable, hf.integrable.sub hg.integrable, ?_⟩
  refine ⟨Cf + Cg, max Nf Ng, add_nonneg hCf hCg, fun z => ?_⟩
  have h1z : 1 ≤ 1 + ‖z‖ := le_add_of_nonneg_right (norm_nonneg z)
  have hpf : (1 + ‖z‖) ^ Nf ≤ (1 + ‖z‖) ^ max Nf Ng := pow_le_pow_right₀ h1z (le_max_left Nf Ng)
  have hpg : (1 + ‖z‖) ^ Ng ≤ (1 + ‖z‖) ^ max Nf Ng := pow_le_pow_right₀ h1z (le_max_right Nf Ng)
  have he : 0 ≤ airyEnv z := (airyEnv_pos z).le
  calc ‖f z - g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_sub_le _ _
    _ ≤ Cf * (1 + ‖z‖) ^ Nf * airyEnv z + Cg * (1 + ‖z‖) ^ Ng * airyEnv z :=
        add_le_add (hbf z) (hbg z)
    _ ≤ Cf * (1 + ‖z‖) ^ max Nf Ng * airyEnv z + Cg * (1 + ‖z‖) ^ max Nf Ng * airyEnv z := by
        gcongr
    _ = (Cf + Cg) * (1 + ‖z‖) ^ max Nf Ng * airyEnv z := by ring

lemma airyFtilde_sub {f g : ℂ → ℂ} (hf : AiryClassG f) (hg : AiryClassG g) {ζ : ℂ} (hζ : 0 ≤ ζ.im) :
    airyFtilde (fun z => f z - g z) ζ = airyFtilde f ζ - airyFtilde g ζ := by
  unfold airyFtilde airyFhat
  have hi1 := integrable_airyIntegrand_of_im_nonneg hf hζ
  have hi2 := integrable_airyIntegrand_of_im_nonneg hg hζ
  have hsub :
      (∫ u : ℝ, (f (u : ℂ) - g (u : ℂ)) * Complex.exp (-(Complex.I * ζ * (u : ℂ)))) =
        (∫ u : ℝ, f (u : ℂ) * Complex.exp (-(Complex.I * ζ * (u : ℂ)))) -
          ∫ u : ℝ, g (u : ℂ) * Complex.exp (-(Complex.I * ζ * (u : ℂ))) := by
    simp_rw [sub_mul]
    exact integral_sub hi1 hi2
  rw [hsub, mul_sub]

/-- **GT.0, `H^∞` inequality.** For complex entire `H_N, H` whose squares belong to `AiryClassG` and
whose restrictions to `ℝ` belong to `L²(ℝ)`, on the closed upper half-plane `Im ζ ≥ 0`,
`‖(H_N²)~(ζ) − (H²)~(ζ)‖ ≤ k · ((‖H_N‖₂ + ‖H‖₂) · ‖H_N − H‖₂).toReal` (`k = 2^{2/3}`). -/
theorem airyFtilde_sq_sub_sq_norm_le (HN H : ℂ → ℂ)
    (hHN2 : AiryClassG (fun z => HN z ^ 2)) (hH2 : AiryClassG (fun z => H z ^ 2))
    (hHN : MemLp (fun x : ℝ => HN (x : ℂ)) 2 volume)
    (hH : MemLp (fun x : ℝ => H (x : ℂ)) 2 volume) {ζ : ℂ} (hζ : 0 ≤ ζ.im) :
    ‖airyFtilde (fun z => HN z ^ 2) ζ - airyFtilde (fun z => H z ^ 2) ζ‖ ≤
      airyPhiK *
        ((eLpNorm (fun x : ℝ => HN (x : ℂ)) 2 volume + eLpNorm (fun x : ℝ => H (x : ℂ)) 2 volume) *
          eLpNorm (fun x : ℝ => HN (x : ℂ) - H (x : ℂ)) 2 volume).toReal := by
  have hsub : AiryClassG (fun z => HN z ^ 2 - H z ^ 2) := airyClassG_sub hHN2 hH2
  rw [← airyFtilde_sub hHN2 hH2 hζ]
  have hpw := airyFtilde_norm_le hsub hζ
  have hint_eq : (∫ u : ℝ, ‖HN (u : ℂ) ^ 2 - H (u : ℂ) ^ 2‖) =
      (eLpNorm (fun u : ℝ => HN (u : ℂ) ^ 2 - H (u : ℂ) ^ 2) 1 volume).toReal :=
    integral_norm_eq_eLpNorm_one_toReal hsub.integrable.aestronglyMeasurable
  have hl1 := eLpNorm_sq_sub_sq_le (𝕜 := ℂ) (fun x : ℝ => HN (x : ℂ)) (fun x : ℝ => H (x : ℂ)) hHN hH
  have htop :
      (eLpNorm (fun x : ℝ => HN (x : ℂ)) 2 volume + eLpNorm (fun x : ℝ => H (x : ℂ)) 2 volume) *
        eLpNorm (fun x : ℝ => HN (x : ℂ) - H (x : ℂ)) 2 volume ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨hHN.eLpNorm_lt_top.ne, hH.eLpNorm_lt_top.ne⟩) ?_
    exact (hHN.sub hH).eLpNorm_lt_top.ne
  have htoReal :
      (eLpNorm (fun u : ℝ => HN (u : ℂ) ^ 2 - H (u : ℂ) ^ 2) 1 volume).toReal ≤
        ((eLpNorm (fun x : ℝ => HN (x : ℂ)) 2 volume + eLpNorm (fun x : ℝ => H (x : ℂ)) 2 volume) *
          eLpNorm (fun x : ℝ => HN (x : ℂ) - H (x : ℂ)) 2 volume).toReal :=
    ENNReal.toReal_mono htop hl1
  have hk : 0 ≤ airyPhiK := by unfold airyPhiK; positivity
  calc ‖airyFtilde (fun z => HN z ^ 2 - H z ^ 2) ζ‖
      ≤ airyPhiK * ∫ u : ℝ, ‖HN (u : ℂ) ^ 2 - H (u : ℂ) ^ 2‖ := hpw
    _ = airyPhiK * (eLpNorm (fun u : ℝ => HN (u : ℂ) ^ 2 - H (u : ℂ) ^ 2) 1 volume).toReal := by
        rw [hint_eq]
    _ ≤ airyPhiK *
          ((eLpNorm (fun x : ℝ => HN (x : ℂ)) 2 volume + eLpNorm (fun x : ℝ => H (x : ℂ)) 2 volume) *
            eLpNorm (fun x : ℝ => HN (x : ℂ) - H (x : ℂ)) 2 volume).toReal := by
        gcongr

/-- **GT.0, `H^∞` convergence.** If `H_i → H` in `L²(ℝ)` and `H_i², H² ∈ G`, then `(H_i²)~ → (H²)~`
uniformly on the closed upper half-plane `{ζ : ℂ | 0 ≤ ζ.im}`. -/
theorem tendsto_airyFtilde_sq_sub_sq {ι : Type*} {l : Filter ι} (HN : ι → ℂ → ℂ) (H : ℂ → ℂ)
    (hHN2 : ∀ i, AiryClassG (fun z => HN i z ^ 2)) (hH2 : AiryClassG (fun z => H z ^ 2))
    (hHN : ∀ i, MemLp (fun x : ℝ => HN i (x : ℂ)) 2 volume)
    (hH : MemLp (fun x : ℝ => H (x : ℂ)) 2 volume)
    (hconv : Tendsto (fun i => eLpNorm (fun x : ℝ => HN i (x : ℂ) - H (x : ℂ)) 2 volume) l (𝓝 0)) :
    TendstoUniformlyOn (fun i ζ => airyFtilde (fun z => HN i z ^ 2) ζ)
      (airyFtilde (fun z => H z ^ 2)) l {ζ : ℂ | 0 ≤ ζ.im} := by
  have hl1 :
      Tendsto (fun i => eLpNorm (fun x : ℝ => HN i (x : ℂ) ^ 2 - H (x : ℂ) ^ 2) 1 volume) l (𝓝 0) :=
    tendsto_eLpNorm_sq_sub_sq (fun i x => HN i (x : ℂ)) (fun x => H (x : ℂ)) hHN hH hconv
  have hl1_real :
      Tendsto (fun i => airyPhiK *
        (eLpNorm (fun x : ℝ => HN i (x : ℂ) ^ 2 - H (x : ℂ) ^ 2) 1 volume).toReal) l (𝓝 0) := by
    have ht : Tendsto (fun i =>
        (eLpNorm (fun x : ℝ => HN i (x : ℂ) ^ 2 - H (x : ℂ) ^ 2) 1 volume).toReal) l (𝓝 0) :=
      by simpa [Function.comp_def] using (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hl1
    simpa using tendsto_const_nhds.mul ht
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hl1_real.eventually (gt_mem_nhds hε)] with i hi ζ hζ
  have hsub : AiryClassG (fun z => HN i z ^ 2 - H z ^ 2) := airyClassG_sub (hHN2 i) hH2
  have hpw := airyFtilde_norm_le hsub hζ
  have hint_eq : (∫ u : ℝ, ‖HN i (u : ℂ) ^ 2 - H (u : ℂ) ^ 2‖) =
      (eLpNorm (fun u : ℝ => HN i (u : ℂ) ^ 2 - H (u : ℂ) ^ 2) 1 volume).toReal :=
    integral_norm_eq_eLpNorm_one_toReal hsub.integrable.aestronglyMeasurable
  rw [dist_comm, dist_eq_norm, ← airyFtilde_sub (hHN2 i) hH2 hζ]
  calc ‖airyFtilde (fun z => HN i z ^ 2 - H z ^ 2) ζ‖
      ≤ airyPhiK * ∫ u : ℝ, ‖HN i (u : ℂ) ^ 2 - H (u : ℂ) ^ 2‖ := hpw
    _ = airyPhiK * (eLpNorm (fun u : ℝ => HN i (u : ℂ) ^ 2 - H (u : ℂ) ^ 2) 1 volume).toReal := by
        rw [hint_eq]
    _ < ε := hi

/-- info: 'FormalResearch.CohnElkies.airyFtilde_sq_sub_sq_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyFtilde_sq_sub_sq_norm_le

/-- info: 'FormalResearch.CohnElkies.tendsto_airyFtilde_sq_sub_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_airyFtilde_sq_sub_sq

end AiryPws

end FormalResearch.CohnElkies
