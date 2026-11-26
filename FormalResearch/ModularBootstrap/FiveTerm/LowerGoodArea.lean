module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerMainDefs
public import FormalResearch.ModularBootstrap.Contour.VirasoroScaleChoice
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.BootstrapHB
public import FormalResearch.SignUncertainty.CtHalfDiscPoisson
public import FormalResearch.Special.AiryEnvelope

/-!
# Half-disc Poisson area bound for `lowerEta` (`cts:rosc-uncond` (1))

Proves the analytic building blocks for the `O(1)` bound on `lowerEta virasoroProblem phi c g R`:
* `lowerGood_re_cpow_three_halves_lip` and `lowerGood_airyEnv_ratio_le`: comparability of `airyEnv` at `u`
  and `φ_c(u)` on `‖u‖ ≤ lowerRmax c₁ c`;
* `lowerGood_inv_norm_area_le`: `∫⁻ z in closedBall 0 R_d, (ENNReal.ofReal ‖z - t‖)⁻¹ ≤ 3 π R_d`;
* `lowerGood_GReg`: `G_reg(w) = (1 - w²/A²)² w Ψ̃(-w²) exp((4/3) i w³)`;
* `lowerGood_GReg_poisson_bound`: pointwise bound on `‖G_reg(z)‖` for `z ∈ openHalfDisc A`, `‖z‖ ≤ A / 4`,
  splitting into the diameter Poisson integral and the `O(c^{-1/3} r₀)` semicircle error (from `YVInputFor`
  and `virasoroPsiTilde_typeII_envelope`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Contour FormalResearch.SignUncertainty.CtHalfDiscPoisson
open FormalResearch.HalfDiscCauchy FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.PoissonJensen FormalResearch.ModularBootstrap.TipFront

/-! ### 1. Lipschitz bound for `Re (z^{3/2})` and `airyEnv` comparability -/

private lemma continuous_re_cpow_three_halves' :
    Continuous (fun z : ℂ => (z ^ (3 / 2 : ℂ)).re) := by
  have heq : (fun z : ℂ => (z ^ (3 / 2 : ℂ)).re) =
      fun z => 3 * z.re * √((‖z‖ + z.re) / 2) - 2 * (√((‖z‖ + z.re) / 2)) ^ 3 := by
    ext z
    rw [re_cpow_three_halves_eq]
    dsimp [airySqrtRe]
    have h1 := airySqrtRe_sq_sub z
    have h2 := airySqrtRe_sq_add z
    have hnn : 0 ≤ airySqrtRe z := airySqrtRe_nonneg z
    have hsq : airySqrtRe z ^ 2 = (‖z‖ + z.re) / 2 := by linarith
    have hsq2 : √((‖z‖ + z.re) / 2) = airySqrtRe z := by
      rw [← hsq, Real.sqrt_sq hnn]
    rw [hsq2]
    rfl
  rw [heq]
  fun_prop

private lemma re_cpow_three_halves_lip_slit' {z₁ z₂ : ℂ}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, (1 - t) • z₁ + t • z₂ ∈ Complex.slitPlane)
    {M : ℝ} (_hM0 : 0 ≤ M) (hz₁ : ‖z₁‖ ≤ M) (hz₂ : ‖z₂‖ ≤ M) :
    |(z₁ ^ (3 / 2 : ℂ)).re - (z₂ ^ (3 / 2 : ℂ)).re| ≤ (3 / 2 : ℝ) * √M * ‖z₁ - z₂‖ := by
  let γ : ℝ → ℂ := fun t => (1 - t) • z₁ + t • z₂
  let f : ℝ → ℝ := fun t => (γ t ^ (3 / 2 : ℂ)).re
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt f (((3 / 2 : ℂ) * γ t ^ (1 / 2 : ℂ) * (z₂ - z₁)).re) t := by
    intro t ht
    have hγ_deriv : HasDerivAt γ (z₂ - z₁) t := by
      have h1 : γ = fun s : ℝ => z₁ + (s : ℂ) * (z₂ - z₁) := by
        ext s; apply Complex.ext <;> dsimp [γ] <;> simp <;> ring
      rw [h1]
      have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * (z₂ - z₁)) (1 * (z₂ - z₁)) t :=
        (Complex.ofRealCLM.hasDerivAt).mul_const (z₂ - z₁)
      simpa using hlin.const_add z₁
    have hcp : HasDerivAt (fun w : ℂ => w ^ (3 / 2 : ℂ))
        ((3 / 2 : ℂ) * γ t ^ ((3 / 2 : ℂ) - 1)) (γ t) :=
      (Complex.hasStrictDerivAt_cpow_const (hseg t ht)).hasDerivAt
    rw [show (3 / 2 : ℂ) - 1 = (1 / 2 : ℂ) by norm_num] at hcp
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hcp.comp t hγ_deriv)
  have hcont_d : ContinuousOn (fun t => ((3 / 2 : ℂ) * γ t ^ (1 / 2 : ℂ) * (z₂ - z₁)).re) (Icc 0 1) := by
    refine Complex.continuous_re.comp_continuousOn ?_
    refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const ?_) continuousOn_const
    intro t ht
    have hf_cont : ContinuousAt (fun z : ℂ => z ^ (1 / 2 : ℂ)) (γ t) :=
      (Complex.hasStrictDerivAt_cpow_const (c := (1 / 2 : ℂ)) (hseg t ht)).hasDerivAt.continuousAt
    have hg_cont : ContinuousAt γ t := (by fun_prop : Continuous γ).continuousAt
    exact (hf_cont.comp hg_cont).continuousWithinAt
  have hev := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => by rw [Set.uIcc_of_le zero_le_one] at ht; exact hderiv t ht)
    (hcont_d.intervalIntegrable_of_Icc zero_le_one)
  have hf0 : f 0 = (z₁ ^ (3 / 2 : ℂ)).re := by simp [f, γ]
  have hf1 : f 1 = (z₂ ^ (3 / 2 : ℂ)).re := by simp [f, γ]
  rw [hf1, hf0] at hev
  rw [abs_sub_comm, ← hev]
  calc |∫ t in (0 : ℝ)..1, ((3 / 2 : ℂ) * γ t ^ (1 / 2 : ℂ) * (z₂ - z₁)).re|
      ≤ ∫ t in (0 : ℝ)..1, |((3 / 2 : ℂ) * γ t ^ (1 / 2 : ℂ) * (z₂ - z₁)).re| := by
        simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
          (f := fun t => ((3 / 2 : ℂ) * γ t ^ (1 / 2 : ℂ) * (z₂ - z₁)).re) zero_le_one
    _ ≤ ∫ _ in (0 : ℝ)..1, (3 / 2 : ℝ) * √M * ‖z₁ - z₂‖ := by
        refine intervalIntegral.integral_mono_on zero_le_one
          (ContinuousOn.abs hcont_d |>.intervalIntegrable_of_Icc zero_le_one)
          intervalIntegrable_const fun t ht => ?_
        have ht0 : 0 ≤ t := ht.1
        have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
        have hγM : ‖γ t‖ ≤ M := by
          dsimp [γ]
          calc ‖(1 - t) • z₁ + t • z₂‖ ≤ ‖(1 - t) • z₁‖ + ‖t • z₂‖ := norm_add_le _ _
            _ = (1 - t) * ‖z₁‖ + t * ‖z₂‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg ht1, Real.norm_of_nonneg ht0]
            _ ≤ (1 - t) * M + t * M := by gcongr
            _ = M := by ring
        calc |((3 / 2 : ℂ) * γ t ^ (1 / 2 : ℂ) * (z₂ - z₁)).re|
            ≤ ‖(3 / 2 : ℂ) * γ t ^ (1 / 2 : ℂ) * (z₂ - z₁)‖ := Complex.abs_re_le_norm _
          _ = (3 / 2 : ℝ) * √‖γ t‖ * ‖z₂ - z₁‖ := by
              rw [norm_mul, norm_mul, show ‖(3 / 2 : ℂ)‖ = (3 / 2 : ℝ) by norm_num, norm_cpow_half]
          _ ≤ (3 / 2 : ℝ) * √M * ‖z₁ - z₂‖ := by
              rw [norm_sub_rev z₂ z₁]
              have h1t : 0 ≤ (3 / 2 : ℝ) := by norm_num
              gcongr
    _ = (3 / 2 : ℝ) * √M * ‖z₁ - z₂‖ := by simp

private lemma re_cpow_three_halves_lip_halfPlane {z₁ z₂ : ℂ} {M : ℝ} (hM0 : 0 ≤ M)
    (hz₁ : ‖z₁‖ ≤ M) (hz₂ : ‖z₂‖ ≤ M)
    (hsign : (0 ≤ z₁.im ∧ 0 ≤ z₂.im) ∨ (z₁.im ≤ 0 ∧ z₂.im ≤ 0)) :
    |(z₁ ^ (3 / 2 : ℂ)).re - (z₂ ^ (3 / 2 : ℂ)).re| ≤ (3 / 2 : ℝ) * √M * ‖z₁ - z₂‖ := by
  have h_lim : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ s * ((1 - t) • z₁ + t • z₂).im) →
      |(z₁ ^ (3 / 2 : ℂ)).re - (z₂ ^ (3 / 2 : ℂ)).re| ≤ (3 / 2 : ℝ) * √M * ‖z₁ - z₂‖ := by
    intro s hs him
    have h_eps : ∀ ε : ℝ, 0 < ε →
        |((z₁ + (s * ε : ℝ) * I) ^ (3 / 2 : ℂ)).re - ((z₂ + (s * ε : ℝ) * I) ^ (3 / 2 : ℂ)).re| ≤
          (3 / 2 : ℝ) * √(M + ε) * ‖z₁ - z₂‖ := by
      intro ε hε
      have hseg : ∀ t ∈ Icc (0 : ℝ) 1,
          (1 - t) • (z₁ + (s * ε : ℝ) * I) + t • (z₂ + (s * ε : ℝ) * I) ∈ Complex.slitPlane := by
        intro t ht
        have him_t := him t ht
        have him_eq : ((1 - t) • (z₁ + (s * ε : ℝ) * I) + t • (z₂ + (s * ε : ℝ) * I)).im =
            ((1 - t) • z₁ + t • z₂).im + s * ε := by
          simp [Complex.add_im]; ring
        rw [Complex.mem_slitPlane_iff]
        right
        rw [him_eq]
        rcases hs with rfl | rfl
        · linarith
        · linarith
      have h1 : ‖z₁ + (s * ε : ℝ) * I‖ ≤ M + ε := by
        calc ‖z₁ + (s * ε : ℝ) * I‖ ≤ ‖z₁‖ + ‖((s * ε : ℝ) : ℂ) * I‖ := norm_add_le _ _
          _ ≤ M + ε := by
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
              abs_of_pos hε]
            rcases hs with rfl | rfl <;> simp at * <;> linarith
      have h2 : ‖z₂ + (s * ε : ℝ) * I‖ ≤ M + ε := by
        calc ‖z₂ + (s * ε : ℝ) * I‖ ≤ ‖z₂‖ + ‖((s * ε : ℝ) : ℂ) * I‖ := norm_add_le _ _
          _ ≤ M + ε := by
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
              abs_of_pos hε]
            rcases hs with rfl | rfl <;> simp at * <;> linarith
      have hsub : (z₁ + (s * ε : ℝ) * I) - (z₂ + (s * ε : ℝ) * I) = z₁ - z₂ := by ring
      have hbd := re_cpow_three_halves_lip_slit' hseg (by linarith) h1 h2
      rwa [hsub] at hbd
    have hL : Tendsto (fun ε : ℝ => |((z₁ + (s * ε : ℝ) * I) ^ (3 / 2 : ℂ)).re -
          ((z₂ + (s * ε : ℝ) * I) ^ (3 / 2 : ℂ)).re|) (𝓝[>] 0)
        (𝓝 |(z₁ ^ (3 / 2 : ℂ)).re - (z₂ ^ (3 / 2 : ℂ)).re|) := by
      have ht1 : Tendsto (fun ε : ℝ => z₁ + ((s * ε : ℝ) : ℂ) * I) (𝓝[>] 0) (𝓝 z₁) := by
        have hcont : Continuous (fun ε : ℝ => z₁ + ((s * ε : ℝ) : ℂ) * I) := by fun_prop
        simpa using (hcont.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
      have ht2 : Tendsto (fun ε : ℝ => z₂ + ((s * ε : ℝ) : ℂ) * I) (𝓝[>] 0) (𝓝 z₂) := by
        have hcont : Continuous (fun ε : ℝ => z₂ + ((s * ε : ℝ) : ℂ) * I) := by fun_prop
        simpa using (hcont.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
      exact (((continuous_re_cpow_three_halves'.continuousAt.tendsto.comp ht1).sub
        (continuous_re_cpow_three_halves'.continuousAt.tendsto.comp ht2)).abs)
    have hR : Tendsto (fun ε : ℝ => (3 / 2 : ℝ) * √(M + ε) * ‖z₁ - z₂‖) (𝓝[>] 0)
        (𝓝 ((3 / 2 : ℝ) * √M * ‖z₁ - z₂‖)) := by
      have hcont : Continuous (fun ε : ℝ => (3 / 2 : ℝ) * √(M + ε) * ‖z₁ - z₂‖) := by fun_prop
      simpa using (hcont.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    exact le_of_tendsto_of_tendsto hL hR (eventually_nhdsWithin_of_forall fun ε hε => h_eps ε hε)
  rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine h_lim 1 (Or.inl rfl) fun t ht => ?_
    simp only [one_mul, Complex.add_im, Complex.smul_im]
    exact add_nonneg (mul_nonneg (by linarith [ht.2]) h1) (mul_nonneg ht.1 h2)
  · refine h_lim (-1) (Or.inr rfl) fun t ht => ?_
    have him' : ((1 - t) • z₁ + t • z₂).im = (1 - t) * z₁.im + t * z₂.im := by simp
    rw [him']
    have : (1 - t) * z₁.im + t * z₂.im ≤ 0 :=
      add_nonpos (mul_nonpos_of_nonneg_of_nonpos (by linarith [ht.2]) h1)
        (mul_nonpos_of_nonneg_of_nonpos ht.1 h2)
    linarith

/-- Global Lipschitz bound for `z ↦ Re(z^{3/2})` on `closedBall 0 M`:
`|Re(z₁^{3/2}) - Re(z₂^{3/2})| ≤ (3/2) √M ‖z₁ - z₂‖`. -/
theorem lowerGood_re_cpow_three_halves_lip {z₁ z₂ : ℂ} {M : ℝ} (hM0 : 0 ≤ M)
    (hz₁ : ‖z₁‖ ≤ M) (hz₂ : ‖z₂‖ ≤ M) :
    |(z₁ ^ (3 / 2 : ℂ)).re - (z₂ ^ (3 / 2 : ℂ)).re| ≤ (3 / 2 : ℝ) * √M * ‖z₁ - z₂‖ := by
  by_cases hsame : (0 ≤ z₁.im ∧ 0 ≤ z₂.im) ∨ (z₁.im ≤ 0 ∧ z₂.im ≤ 0)
  · exact re_cpow_three_halves_lip_halfPlane hM0 hz₁ hz₂ hsame
  have hopp : (z₁.im < 0 ∧ 0 < z₂.im) ∨ (0 < z₁.im ∧ z₂.im < 0) := by
    rcases le_or_gt 0 z₁.im with h1 | h1 <;> rcases le_or_gt 0 z₂.im with h2 | h2
    · exact absurd (Or.inl ⟨h1, h2⟩) hsame
    · by_cases h10 : z₁.im = 0
      · exact absurd (Or.inr ⟨h10.le, h2.le⟩) hsame
      · exact Or.inr ⟨lt_of_le_of_ne h1 (Ne.symm h10), h2⟩
    · by_cases h20 : z₂.im = 0
      · exact absurd (Or.inr ⟨h1.le, h20.le⟩) hsame
      · exact Or.inl ⟨h1, lt_of_le_of_ne h2 (Ne.symm h20)⟩
    · exact absurd (Or.inr ⟨h1.le, h2.le⟩) hsame
  have hne : z₁.im - z₂.im ≠ 0 := by
    rcases hopp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  let t₀ : ℝ := z₁.im / (z₁.im - z₂.im)
  have ht₀_mem : t₀ ∈ Icc (0 : ℝ) 1 := by
    rcases hopp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · constructor
      · exact div_nonneg_of_nonpos h1.le (by linarith)
      · rw [div_le_one_of_neg (by linarith)]; linarith
    · constructor
      · exact div_nonneg h1.le (by linarith)
      · rw [div_le_one (by linarith)]; linarith
  let z₀ : ℂ := (1 - t₀) • z₁ + t₀ • z₂
  have hz₀_im : z₀.im = 0 := by
    dsimp [z₀, t₀]
    simp only [Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    field_simp [hne]; ring
  have hz₀_M : ‖z₀‖ ≤ M := by
    dsimp [z₀]
    have ht0_nn : 0 ≤ t₀ := ht₀_mem.1
    have ht1_nn : 0 ≤ 1 - t₀ := by linarith [ht₀_mem.2]
    calc ‖(1 - t₀) • z₁ + t₀ • z₂‖ ≤ ‖(1 - t₀) • z₁‖ + ‖t₀ • z₂‖ := norm_add_le _ _
      _ = (1 - t₀) * ‖z₁‖ + t₀ * ‖z₂‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ht1_nn, Real.norm_of_nonneg ht0_nn]
      _ ≤ (1 - t₀) * M + t₀ * M := by gcongr
      _ = M := by ring
  have hnorm_sum : ‖z₁ - z₀‖ + ‖z₀ - z₂‖ = ‖z₁ - z₂‖ := by
    have e1 : z₁ - z₀ = t₀ • (z₁ - z₂) := by dsimp [z₀]; apply Complex.ext <;> simp <;> ring
    have e2 : z₀ - z₂ = (1 - t₀) • (z₁ - z₂) := by dsimp [z₀]; apply Complex.ext <;> simp <;> ring
    rw [e1, e2, norm_smul, norm_smul, Real.norm_of_nonneg ht₀_mem.1,
      Real.norm_of_nonneg (by linarith [ht₀_mem.2])]
    ring
  have hs1 : (0 ≤ z₁.im ∧ 0 ≤ z₀.im) ∨ (z₁.im ≤ 0 ∧ z₀.im ≤ 0) := by
    rcases le_or_gt 0 z₁.im with h1 | h1
    · exact Or.inl ⟨h1, hz₀_im.ge⟩
    · exact Or.inr ⟨h1.le, hz₀_im.le⟩
  have hs2 : (0 ≤ z₀.im ∧ 0 ≤ z₂.im) ∨ (z₀.im ≤ 0 ∧ z₂.im ≤ 0) := by
    rcases le_or_gt 0 z₂.im with h2 | h2
    · exact Or.inl ⟨hz₀_im.ge, h2⟩
    · exact Or.inr ⟨hz₀_im.le, h2.le⟩
  have hb1 := re_cpow_three_halves_lip_halfPlane hM0 hz₁ hz₀_M hs1
  have hb2 := re_cpow_three_halves_lip_halfPlane hM0 hz₀_M hz₂ hs2
  calc |(z₁ ^ (3 / 2 : ℂ)).re - (z₂ ^ (3 / 2 : ℂ)).re|
      ≤ |(z₁ ^ (3 / 2 : ℂ)).re - (z₀ ^ (3 / 2 : ℂ)).re| +
          |(z₀ ^ (3 / 2 : ℂ)).re - (z₂ ^ (3 / 2 : ℂ)).re| := abs_sub_le _ _ _
    _ ≤ (3 / 2 : ℝ) * √M * ‖z₁ - z₀‖ + (3 / 2 : ℝ) * √M * ‖z₀ - z₂‖ := add_le_add hb1 hb2
    _ = (3 / 2 : ℝ) * √M * (‖z₁ - z₀‖ + ‖z₀ - z₂‖) := by ring
    _ = (3 / 2 : ℝ) * √M * ‖z₁ - z₂‖ := by rw [hnorm_sum]

/-- `airyEnv z₁ ≤ exp(2 √M ‖z₁ - z₂‖) airyEnv z₂` for `‖z₁‖, ‖z₂‖ ≤ M`. -/
theorem lowerGood_airyEnv_ratio_le {z₁ z₂ : ℂ} {M : ℝ} (hM0 : 0 ≤ M)
    (hz₁ : ‖z₁‖ ≤ M) (hz₂ : ‖z₂‖ ≤ M) :
    airyEnv z₁ ≤ Real.exp (2 * √M * ‖z₁ - z₂‖) * airyEnv z₂ := by
  have hlip := lowerGood_re_cpow_three_halves_lip hM0 hz₁ hz₂
  have hsub := (abs_le.mp hlip).1
  unfold airyEnv
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  linarith

/-! ### 2. 2D area integral of `‖z - t‖⁻¹` -/

/-- For `R_d > 0` and any `t : ℝ`, `∫⁻ z in closedBall 0 R_d, (ENNReal.ofReal ‖z - t‖)⁻¹ ≤ 3 π R_d`. -/
theorem lowerGood_inv_norm_area_le {R_d : ℝ} (hRd : 0 < R_d) (t : ℝ) :
    ∫⁻ z in closedBall (0 : ℂ) R_d, (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹ ≤
      ENNReal.ofReal (3 * π * R_d) := by
  let S₁ : Set ℂ := closedBall (0 : ℂ) R_d ∩ ball (t : ℂ) R_d
  let S₂ : Set ℂ := closedBall (0 : ℂ) R_d \ ball (t : ℂ) R_d
  have hS_eq : closedBall (0 : ℂ) R_d = S₁ ∪ S₂ := by
    ext z; simp [S₁, S₂]
  have h_split : ∫⁻ z in closedBall (0 : ℂ) R_d, (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹ ≤
      (∫⁻ z in ball (t : ℂ) R_d, (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹) +
      (∫⁻ z in S₂, (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹) := by
    rw [hS_eq]
    refine (lintegral_union_le _ _ _).trans (add_le_add ?_ le_rfl)
    exact lintegral_mono_set Set.inter_subset_right
  have h_ball : ∫⁻ z in ball (t : ℂ) R_d, (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹ ≤
      ENNReal.ofReal (2 * π * R_d) := by
    have htr : ∫⁻ z in ball (t : ℂ) R_d, (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹ =
        ∫⁻ w in ball (0 : ℂ) R_d, (ENNReal.ofReal ‖w‖)⁻¹ := by
      rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]
      rw [← MeasureTheory.lintegral_add_right_eq_self (μ := volume)
        (fun w : ℂ => (ball (0 : ℂ) R_d).indicator (fun z => (ENNReal.ofReal ‖z‖)⁻¹) w) (-(t : ℂ))]
      congr 1; ext z
      by_cases h : ‖z - (t : ℂ)‖ < R_d
      · have h1 : z ∈ ball (t : ℂ) R_d := by simpa [mem_ball, dist_eq_norm] using h
        have h2 : z + -(t : ℂ) ∈ ball (0 : ℂ) R_d := by
          simpa [mem_ball, dist_eq_norm, sub_eq_add_neg] using h
        simp [h1, h2, sub_eq_add_neg]
      · have h1 : z ∉ ball (t : ℂ) R_d := by simpa [mem_ball, dist_eq_norm] using h
        have h2 : z + -(t : ℂ) ∉ ball (0 : ℂ) R_d := by
          simpa [mem_ball, dist_eq_norm, sub_eq_add_neg] using h
        simp [h1, h2]
    have h_polar_eq : ∫⁻ w in ball (0 : ℂ) R_d, (ENNReal.ofReal ‖w‖)⁻¹ =
        ∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 • (ball (0 : ℂ) R_d).indicator (fun z => (ENNReal.ofReal ‖z‖)⁻¹)
            (Complex.polarCoord.symm p) := by
      rw [← lintegral_indicator measurableSet_ball]
      exact (Complex.lintegral_comp_polarCoord_symm _).symm
    rw [htr, h_polar_eq]
    have h_polar : (∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 • (ball (0 : ℂ) R_d).indicator (fun z => (ENNReal.ofReal ‖z‖)⁻¹)
          (Complex.polarCoord.symm p)) ≤
        ∫⁻ p in (Ioo (0 : ℝ) R_d) ×ˢ (Ioo (-π) π), 1 := by
      have h_pt : ∀ p ∈ Complex.polarCoord.target,
          ENNReal.ofReal p.1 • (ball (0 : ℂ) R_d).indicator (fun z => (ENNReal.ofReal ‖z‖)⁻¹)
            (Complex.polarCoord.symm p) ≤
          ((Ioo (0 : ℝ) R_d) ×ˢ (Ioo (-π) π)).indicator (fun _ => (1 : ENNReal)) p := by
        intro p hp
        have hp1 : 0 < p.1 := hp.1
        have hsymm : Complex.polarCoord.symm p = (p.1 : ℂ) * Complex.exp (p.2 * I) := by
          simp [Complex.exp_mul_I]
        have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
          rw [hsymm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp1,
            Complex.norm_exp_ofReal_mul_I, mul_one]
        by_cases hmem : Complex.polarCoord.symm p ∈ ball (0 : ℂ) R_d
        · have hp_in : p ∈ (Ioo (0 : ℝ) R_d) ×ˢ (Ioo (-π) π) := by
            rw [mem_ball_zero_iff, hnorm] at hmem
            exact ⟨⟨hp1, hmem⟩, hp.2⟩
          simp only [Set.indicator_of_mem hmem, Set.indicator_of_mem hp_in, hnorm, smul_eq_mul]
          exact (ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hp1).ne' ENNReal.ofReal_ne_top).le
        · simp only [Set.indicator_of_notMem hmem, smul_zero, zero_le]
      calc (∫⁻ p in Complex.polarCoord.target,
            ENNReal.ofReal p.1 • (ball (0 : ℂ) R_d).indicator (fun z => (ENNReal.ofReal ‖z‖)⁻¹)
              (Complex.polarCoord.symm p))
          ≤ ∫⁻ p in Complex.polarCoord.target,
              ((Ioo (0 : ℝ) R_d) ×ˢ (Ioo (-π) π)).indicator (fun _ => (1 : ENNReal)) p :=
            setLIntegral_mono' (measurableSet_Ioi.prod measurableSet_Ioo) h_pt
        _ ≤ ∫⁻ p, ((Ioo (0 : ℝ) R_d) ×ˢ (Ioo (-π) π)).indicator (fun _ => (1 : ENNReal)) p :=
            setLIntegral_le_lintegral _ _
        _ = ∫⁻ p in (Ioo (0 : ℝ) R_d) ×ˢ (Ioo (-π) π), 1 :=
            lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo) _
    refine h_polar.trans_eq ?_
    rw [setLIntegral_one, Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Ioo, Real.volume_Ioo, sub_zero, show π - -π = 2 * π by ring,
      ← ENNReal.ofReal_mul hRd.le, mul_comm R_d (2 * π)]
  have h_S2 : ∫⁻ z in S₂, (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹ ≤ ENNReal.ofReal (π * R_d) := by
    have hle : ∀ z ∈ S₂, (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹ ≤ (ENNReal.ofReal R_d)⁻¹ := by
      intro z hz
      have hge : R_d ≤ ‖z - (t : ℂ)‖ := by
        have := hz.2
        rw [mem_ball, dist_eq_norm] at this
        exact not_lt.mp this
      exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hge)
    have hm : ∫⁻ z in S₂, (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹ ≤
        ∫⁻ _ in S₂, (ENNReal.ofReal R_d)⁻¹ :=
      setLIntegral_mono' (measurableSet_closedBall.diff measurableSet_ball) hle
    refine hm.trans ?_
    rw [setLIntegral_const]
    have hvol : volume S₂ ≤ ENNReal.ofReal (π * R_d ^ 2) := by
      calc volume S₂ ≤ volume (closedBall (0 : ℂ) R_d) := measure_mono Set.sdiff_subset
        _ = ENNReal.ofReal (π * R_d ^ 2) := by
          rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow hRd.le,
            show (NNReal.pi : ENNReal) = ENNReal.ofReal π by
              rw [ENNReal.ofReal_eq_coe_nnreal Real.pi_pos.le]; rfl,
            ← ENNReal.ofReal_mul (pow_nonneg hRd.le 2), mul_comm]
    calc (ENNReal.ofReal R_d)⁻¹ * volume S₂
        ≤ (ENNReal.ofReal R_d)⁻¹ * ENNReal.ofReal (π * R_d ^ 2) := by gcongr
      _ = ENNReal.ofReal (π * R_d) := by
          rw [← ENNReal.ofReal_inv_of_pos hRd, ← ENNReal.ofReal_mul (inv_nonneg.mpr hRd.le)]
          congr 1; field_simp
  calc ∫⁻ z in closedBall (0 : ℂ) R_d, (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹
      ≤ (∫⁻ z in ball (t : ℂ) R_d, (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹) +
          (∫⁻ z in S₂, (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹) := h_split
    _ ≤ ENNReal.ofReal (2 * π * R_d) + ENNReal.ofReal (π * R_d) := add_le_add h_ball h_S2
    _ = ENNReal.ofReal (3 * π * R_d) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-! ### 3. Half-disc Poisson bound for `G_reg` -/

/-- `((ζ^2))^{1/2} = ζ` when `Re ζ > 0`. -/
lemma lowerGood_cpow_half_sq_of_re_pos {ζ : ℂ} (hζ : 0 < ζ.re) : (ζ ^ 2) ^ (1 / 2 : ℂ) = ζ := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (cpow_half_sq (ζ ^ 2)) with h | h
  · exact h
  · have hre := cpow_half_re_nonneg (ζ ^ 2)
    rw [h, Complex.neg_re] at hre
    linarith

/-- For `w` with `0 < w.im`, `((-w^2)^{1/2}).re = w.im` and `airyEnv (-w^2) = ‖exp((4/3) i w^3)‖⁻¹`. -/
lemma lowerGood_airyEnv_neg_sq_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    ((-(w ^ 2)) ^ (1 / 2 : ℂ)).re = w.im ∧
      airyEnv (-(w ^ 2)) = (‖Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)‖)⁻¹ := by
  have hζ_re : 0 < (-I * w).re := by simp [hw]
  have hsq : (-I * w) ^ 2 = -(w ^ 2) := by
    rw [mul_pow, neg_sq, Complex.I_sq]; ring
  have hhalf : (-(w ^ 2)) ^ (1 / 2 : ℂ) = -I * w := by
    rw [← hsq]; exact lowerGood_cpow_half_sq_of_re_pos hζ_re
  refine ⟨by rw [hhalf]; simp, ?_⟩
  have h32 : (-(w ^ 2)) ^ (3 / 2 : ℂ) = I * w ^ 3 := by
    rw [← cpow_half_cube, hhalf, mul_pow, show (-I) ^ 3 = I by
      calc (-I) ^ 3 = -(I ^ 2 * I) := by ring
        _ = -((-1) * I) := by rw [Complex.I_sq]
        _ = I := by ring]
  unfold airyEnv
  rw [h32, Complex.norm_exp, ← Real.exp_neg]
  congr 1
  simp [Complex.mul_re]

/-- Regularised Airy-unfolded test `G_reg(w) = (1 - w²/A²)² w Ψ̃(-w²) exp((4/3) i w³)`. -/
noncomputable def lowerGoodGReg (A c : ℝ) (g : ℝ → ℝ) (w : ℂ) : ℂ :=
  (1 - w ^ 2 / (A : ℂ) ^ 2) ^ 2 * w * virasoroPsiTilde c g (-(w ^ 2)) *
    Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)

/-- Analyticity of `lowerGoodGReg` on `closedBall 0 A` when `A^2 ≤ virasoroAC c ^ 2` and `1000 ≤ c`. -/
lemma lowerGood_GReg_analytic {A c : ℝ} (hc : 1000 ≤ c) (hA0 : 0 < A)
    (hA_ub : A ^ 2 ≤ virasoroAC c ^ 2) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c / 12) g) :
    AnalyticOnNhd ℂ (lowerGoodGReg A c g) (closedBall (0 : ℂ) A) := by
  have hc_pos : 0 < c := by linarith
  intro w hw
  have hw_norm : ‖w‖ ≤ A := mem_closedBall_zero_iff.mp hw
  have hneg_mem : -(w ^ 2) ∈ closedBall (0 : ℂ) (virasoroAC c ^ 2) := by
    rw [mem_closedBall_zero_iff, norm_neg, norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg w) hw_norm 2).trans hA_ub
  have hpsi : AnalyticAt ℂ (fun z => virasoroPsiTilde c g (-(z ^ 2))) w :=
    (virasoroPsiTilde_analyticOnNhd hc hg _ (virasoro_closedBall_subset_psiDom hc_pos hneg_mem)).comp_of_eq
      ((analyticAt_id.pow 2).neg) rfl
  have hpre : AnalyticAt ℂ (fun z => (1 - z ^ 2 / (A : ℂ) ^ 2) ^ 2 * z) w :=
    (((analyticAt_const.sub ((analyticAt_id.pow 2).div analyticAt_const
      (by exact_mod_cast (pow_pos hA0 2).ne'))).pow 2).mul analyticAt_id)
  have hexp : AnalyticAt ℂ (fun z => Complex.exp ((4 / 3 : ℂ) * I * z ^ 3)) w :=
    (analyticAt_const.mul (analyticAt_id.pow 3)).cexp
  exact (hpre.mul hpsi).mul hexp

/-- Pointwise half-disc Poisson bound for `lowerGoodGReg A c g` at `z ∈ openHalfDisc A` with `‖z‖ ≤ A / 4`. -/
theorem lowerGood_GReg_poisson_bound {A c T L' : ℝ} {g : ℝ → ℝ}
    (hc_Q : virasoroCQEnv ≤ c)
    (hA0 : 0 < A) (hA_ub : A ^ 2 ≤ virasoroAC c ^ 2)
    (hSig : virasoroSigma c * (2 * A * c ^ (-(1 / 12 : ℝ))) ≤ 1)
    (hg : virasoroProblem.IsWeaklyFeasible (c / 12) T g)
    (hYV : YVEnvBound (virasoroPsiTilde c g) c (A ^ 2) L') (hL' : 0 ≤ L')
    {z : ℂ} (hz : z ∈ openHalfDisc A) (hz4 : ‖z‖ ≤ A / 4) :
    ‖lowerGoodGReg A c g z‖ ≤
      (∫ t in (-A)..A, pDiam A z t * ‖lowerGoodGReg A c g (t : ℂ)‖) +
        12 * π * z.im * (L' * A ^ (-3 : ℝ) + virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ)) := by
  have hc_10000 : 10000 ≤ c :=
    (by unfold c_PJ_complex; norm_num : (10000 : ℝ) ≤ c_PJ_complex).trans
      (c_PJ_complex_le_virasoroCQEnv.trans hc_Q)
  have hc_pos : 0 < c := by linarith
  have hc_ge1 : 1 ≤ c := by linarith
  have ha : virasoroProblem.totalShift ≤ c / 12 := by
    rw [virasoroProblem_totalShift]; linarith
  have hM_pos : 0 < virasoroProblem.cardyNorm (c / 12) g :=
    cardyNorm_pos_of_nonzero ha hg.1 hg.2.1
  have han := lowerGood_GReg_analytic (by linarith) hA0 hA_ub hg.1
  have hcont : ContinuousOn (lowerGoodGReg A c g) (closedHalfDisc A) :=
    han.continuousOn.mono fun _ hw => mem_closedBall_zero_iff.mpr hw.1
  have hdiff : DifferentiableOn ℂ (lowerGoodGReg A c g) (openHalfDisc A) :=
    han.differentiableOn.mono fun _ hw => mem_closedBall_zero_iff.mpr hw.1.le
  have hpois := ct_halfDisc_poisson hA0 hz hcont hdiff
  have hdiam_cont : ContinuousOn (fun t : ℝ => (pDiam A z t : ℂ) * lowerGoodGReg A c g (t : ℂ))
      (Icc (-A) A) := by
    have hp_cont : ContinuousOn (fun t : ℝ => (pDiam A z t : ℂ)) (Icc (-A) A) := by
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      unfold pDiam
      refine ContinuousOn.div (by fun_prop) ?_ fun t ht => ?_
      · exact (ContinuousOn.mul (by fun_prop) (by fun_prop))
      · have h1 : Complex.normSq (z - (t : ℂ)) ≠ 0 := by
          rw [Ne, Complex.normSq_eq_zero]
          intro h
          have him := congrArg Complex.im (sub_eq_zero.mp h)
          simp at him; linarith [hz.2]
        have h2 : Complex.normSq (((A : ℂ) ^ 2) - (t : ℂ) * z) ≠ 0 := by
          rw [Ne, Complex.normSq_eq_zero]
          intro h
          have hnorm : ‖(t : ℂ) * z‖ = A ^ 2 := by
            have := congrArg norm (sub_eq_zero.mp h)
            simpa [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA0] using this.symm
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hnorm
          have hle : |t| * ‖z‖ ≤ A * (A / 4) := mul_le_mul (abs_le.mpr ht) hz4 (norm_nonneg _) hA0.le
          nlinarith
        exact mul_ne_zero h1 h2
    exact hp_cont.mul (hcont.comp Complex.continuous_ofReal.continuousOn fun t ht =>
      ofReal_mem_closedHalfDisc ht)
  have harc_cont : ContinuousOn (fun θ : ℝ => (pArc A z θ : ℂ) * lowerGoodGReg A c g (A * Complex.exp (θ * I)))
      (Icc 0 π) := by
    have hp_cont : ContinuousOn (fun θ : ℝ => (pArc A z θ : ℂ)) (Icc 0 π) := by
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      unfold pArc
      refine ContinuousOn.div (by fun_prop) ?_ fun θ _ => ?_
      · exact ContinuousOn.mul (by fun_prop) (by fun_prop)
      · have hD1 := normSq_sub_arc_ge hA0 hz4 (A * Complex.exp (θ * I)) (norm_arc A θ hA0)
        have hD2 := normSq_sub_arc_ge hA0 hz4 (A * Complex.exp (-(θ : ℂ) * I)) (by
          have : -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I := by push_cast; ring
          rw [this]; exact norm_arc A (-θ) hA0)
        have hpos : 0 < (3 * A / 4) ^ 2 := by positivity
        exact (mul_pos (lt_of_lt_of_le hpos hD1) (lt_of_lt_of_le hpos hD2)).ne'
    exact hp_cont.mul (hcont.comp (by fun_prop) fun θ hθ => arc_mem_closedHalfDisc hA0 hθ)
  have hnorm_pois : ‖lowerGoodGReg A c g z‖ ≤
      (∫ t in (-A)..A, pDiam A z t * ‖lowerGoodGReg A c g (t : ℂ)‖) +
        12 * π * z.im * (L' * A ^ (-3 : ℝ) + virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ)) := by
    rw [hpois]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · have hi := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
        (f := fun t : ℝ => (pDiam A z t : ℂ) * lowerGoodGReg A c g (t : ℂ)) (by linarith : -A ≤ A)
      refine hi.trans_eq (intervalIntegral.integral_congr fun t ht => ?_)
      rw [uIcc_of_le (by linarith)] at ht
      have hp0 : 0 ≤ pDiam A z t := by
        unfold pDiam
        have hzA : Complex.normSq z ≤ A ^ 2 := by
          rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (norm_nonneg _) hz.1.le 2
        have htA : t ^ 2 ≤ A ^ 2 := by
          rw [← sq_abs t]
          exact pow_le_pow_left₀ (abs_nonneg t) (abs_le.mpr ht) 2
        have hz2 : 0 ≤ z.im := hz.2.le
        have hnum : 0 ≤ z.im / π * ((A ^ 2 - Complex.normSq z) * (A ^ 2 - t ^ 2)) := by
          have : 0 ≤ (A ^ 2 - Complex.normSq z) * (A ^ 2 - t ^ 2) := mul_nonneg (by linarith) (by linarith)
          positivity [Real.pi_pos]
        exact div_nonneg hnum (mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0]
    · have hi := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
        (f := fun θ : ℝ => (pArc A z θ : ℂ) * lowerGoodGReg A c g (A * Complex.exp (θ * I))) Real.pi_pos.le
      have hi_eq : ∫ θ in (0 : ℝ)..π, ‖(pArc A z θ : ℂ) * lowerGoodGReg A c g (A * Complex.exp (θ * I))‖ =
          ∫ θ in (0 : ℝ)..π, pArc A z θ * ‖lowerGoodGReg A c g (A * Complex.exp (θ * I))‖ := by
        refine intervalIntegral.integral_congr fun θ hθ => ?_
        rw [uIcc_of_le Real.pi_pos.le] at hθ
        have hp0 := (pArc_le hA0 hz.2 hz4 hθ.1 hθ.2).1
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0]
      rw [hi_eq] at hi
      refine hi.trans ?_
      have h_int_le : ∫ θ in (0 : ℝ)..π, pArc A z θ * ‖lowerGoodGReg A c g (A * Complex.exp (θ * I))‖ ≤
          ∫ _ in (0 : ℝ)..π, 12 * z.im * (L' * A ^ (-3 : ℝ) + virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ)) := by
        have hcont_lhs : ContinuousOn (fun θ : ℝ => pArc A z θ * ‖lowerGoodGReg A c g (A * Complex.exp (θ * I))‖)
            (Icc 0 π) := by
          have := harc_cont.norm
          refine this.congr fun θ hθ => ?_
          dsimp only
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pArc_le hA0 hz.2 hz4 hθ.1 hθ.2).1]
        refine intervalIntegral.integral_mono_on Real.pi_pos.le
          (hcont_lhs.intervalIntegrable_of_Icc Real.pi_pos.le) intervalIntegrable_const fun θ hθ => ?_
        have hp_le := (pArc_le hA0 hz.2 hz4 hθ.1 hθ.2).2
        have hsin_nn : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
        have hsin_le1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
        by_cases hsin0 : Real.sin θ = 0
        · have hp0 : pArc A z θ = 0 := by
            have := (pArc_le hA0 hz.2 hz4 hθ.1 hθ.2).1
            rw [hsin0, mul_zero] at hp_le
            linarith
          rw [hp0, zero_mul]
          have := virasoroEnvC0_pos
          have := Real.exp_pos (1 : ℝ)
          have := hz.2
          positivity
        have hsin_pos : 0 < Real.sin θ := lt_of_le_of_ne hsin_nn (Ne.symm hsin0)
        set w : ℂ := (A : ℂ) * Complex.exp (θ * I) with hw
        set u : ℂ := -(w ^ 2) with hu
        have hw_im : w.im = A * Real.sin θ := by
          rw [hw, Complex.exp_mul_I]; simp [Complex.mul_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
        have hw_im_pos : 0 < w.im := by rw [hw_im]; positivity
        have hw_norm : ‖w‖ = A := norm_arc A θ hA0
        have hu_norm : ‖u‖ = A ^ 2 := by rw [hu, norm_neg, norm_pow, hw_norm]
        have h_env := lowerGood_airyEnv_neg_sq_of_im_pos hw_im_pos
        have hu_re_sqrt : (u ^ (1 / 2 : ℂ)).re = A * Real.sin θ := by
          rw [hu, h_env.1, hw_im]
        have h_pre_norm : ‖(1 - w ^ 2 / (A : ℂ) ^ 2) ^ 2‖ = 4 * Real.sin θ ^ 2 := by
          have hw2 : w ^ 2 / (A : ℂ) ^ 2 = Complex.exp (2 * θ * I) := by
            rw [hw, mul_pow, mul_div_cancel_left₀ _ (by exact_mod_cast (pow_pos hA0 2).ne'),
              ← Complex.exp_nat_mul]
            congr 1; push_cast; ring
          rw [norm_pow, hw2]
          have h1 : ‖1 - Complex.exp (2 * θ * I)‖ = 2 * Real.sin θ := by
            have e : 1 - Complex.exp (2 * θ * I) =
                Complex.exp (θ * I) * (Complex.exp (-(θ : ℂ) * I) - Complex.exp (θ * I)) := by
              rw [mul_sub, ← Complex.exp_add, ← Complex.exp_add]
              simp [show (θ : ℂ) * I + (θ : ℂ) * I = 2 * θ * I by ring]
            rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
            have e2 : Complex.exp (-(θ : ℂ) * I) - Complex.exp (θ * I) =
                ((-2 * Real.sin θ : ℝ) : ℂ) * I := by
              rw [show -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
                Complex.exp_mul_I, Complex.exp_mul_I]
              simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
              push_cast; ring
            rw [e2, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
              abs_neg, abs_two, abs_of_nonneg hsin_nn]
          rw [h1]; ring
        have hGreg_norm : ‖lowerGoodGReg A c g w‖ =
            4 * Real.sin θ ^ 2 * A * (‖virasoroPsiTilde c g u‖ / airyEnv u) := by
          unfold lowerGoodGReg
          rw [norm_mul, norm_mul, norm_mul, h_pre_norm, hw_norm, ← hu, h_env.2]
          have henv_pos := airyEnv_pos u
          field_simp [henv_pos.ne']
        have h_psi_ratio : ‖virasoroPsiTilde c g u‖ / airyEnv u ≤
            L' * A ^ (-3 : ℝ) * Real.sin θ ^ (-(3 / 2 : ℝ)) +
              virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ) * (Real.sin θ)⁻¹ := by
          have henv_pos := airyEnv_pos u
          by_cases hsin_cut : 2 * c ^ (-(1 / 12 : ℝ)) ≤ Real.sin θ
          · have hYV_u : ‖virasoroPsiTilde c g u‖ ≤
                L' * airyEnv u * ((u ^ (1 / 2 : ℂ)).re) ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ)) := by
              by_cases hu_im : 0 ≤ u.im
              · exact hYV u hu_im (by linarith [hu_norm]) (by linarith [hu_norm]) (by
                  rw [hu_norm, Real.sqrt_sq hA0.le, hu_re_sqrt]
                  calc 2 * c ^ (-(1 / 12 : ℝ)) * A ≤ Real.sin θ * A :=
                        mul_le_mul_of_nonneg_right hsin_cut hA0.le
                    _ = A * Real.sin θ := by ring)
              · have hconj_im : 0 ≤ ((starRingEnd ℂ) u).im := by simp; linarith
                have hconj_norm : ‖(starRingEnd ℂ) u‖ = A ^ 2 := by simp [hu_norm]
                have hconj_re : (((starRingEnd ℂ) u) ^ (1 / 2 : ℂ)).re = A * Real.sin θ := by
                  rw [show (((starRingEnd ℂ) u) ^ (1 / 2 : ℂ)).re = airySqrtRe ((starRingEnd ℂ) u) from rfl,
                    airySqrtRe_conj]; exact hu_re_sqrt
                have hYV' := hYV ((starRingEnd ℂ) u) hconj_im (by linarith [hconj_norm])
                  (by linarith [hconj_norm]) (by
                    rw [hconj_norm, Real.sqrt_sq hA0.le, hconj_re]
                    calc 2 * c ^ (-(1 / 12 : ℝ)) * A ≤ Real.sin θ * A :=
                          mul_le_mul_of_nonneg_right hsin_cut hA0.le
                      _ = A * Real.sin θ := by ring)
                have hconj := virasoroPsiTilde_conj hc_Q hg.1 hM_pos
                  (mem_closedBall_zero_iff.mpr (hu_norm.le.trans hA_ub))
                rw [show (starRingEnd ℂ) u = star u from rfl, hconj, norm_star,
                  show star u = (starRingEnd ℂ) u from rfl, airyEnv_conj, hconj_re,
                  hconj_norm, ← hu_norm, ← hu_re_sqrt] at hYV'
                exact hYV'
            have h1 : ‖virasoroPsiTilde c g u‖ / airyEnv u ≤
                L' * A ^ (-3 : ℝ) * Real.sin θ ^ (-(3 / 2 : ℝ)) := by
              rw [div_le_iff₀ henv_pos]
              refine hYV_u.trans_eq ?_
              rw [hu_re_sqrt, hu_norm, Real.mul_rpow hA0.le hsin_nn,
                ← Real.rpow_natCast A 2, ← Real.rpow_mul hA0.le]
              have hA_pow : A ^ (-(3 / 2 : ℝ)) * A ^ ((2 : ℝ) * -(3 / 4 : ℝ)) = A ^ (-3 : ℝ) := by
                rw [← Real.rpow_add hA0]; congr 1; norm_num
              calc L' * airyEnv u * (A ^ (-(3 / 2 : ℝ)) * Real.sin θ ^ (-(3 / 2 : ℝ))) *
                    A ^ ((2 : ℝ) * -(3 / 4 : ℝ))
                  = L' * (A ^ (-(3 / 2 : ℝ)) * A ^ ((2 : ℝ) * -(3 / 4 : ℝ))) *
                      Real.sin θ ^ (-(3 / 2 : ℝ)) * airyEnv u := by ring
                _ = L' * A ^ (-3 : ℝ) * Real.sin θ ^ (-(3 / 2 : ℝ)) * airyEnv u := by rw [hA_pow]
            have h2 : 0 ≤ virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ) * (Real.sin θ)⁻¹ :=
              mul_nonneg (by have := virasoroEnvC0_pos; positivity) (inv_nonneg.mpr hsin_nn)
            linarith
          · have hsin_lt : Real.sin θ < 2 * c ^ (-(1 / 12 : ℝ)) := not_le.mp hsin_cut
            have hu_mem : u ∈ closedBall (0 : ℂ) (virasoroAC c ^ 2) := by
              rw [mem_closedBall_zero_iff, hu_norm]; exact hA_ub
            have hu_not_cut : ¬ (u.im = 0 ∧ u.re ≤ 0) := by
              intro ⟨him, hre⟩
              have hu_ne : u ≠ 0 := by intro h0; rw [h0, norm_zero] at hu_norm; nlinarith
              have hre0 : (u ^ (1 / 2 : ℂ)).re = 0 := by
                have harg := Complex.arg_eq_pi_iff.mpr ⟨lt_of_le_of_ne hre (fun h => hu_ne (Complex.ext h him)), him⟩
                rw [Complex.cpow_def_of_ne_zero hu_ne, Complex.exp_re]
                have : (Complex.log u * (1 / 2 : ℂ)).im = π / 2 := by simp [Complex.log_im, harg]; ring
                rw [this, Real.cos_pi_div_two, mul_zero]
              rw [hu_re_sqrt] at hre0
              nlinarith [mul_pos hA0 hsin_pos]
            have hII := virasoroPsiTilde_typeII_envelope hc_Q hg.1 hM_pos hu_mem hu_not_cut
            have hsig_bd : virasoroSigma c * (u ^ (1 / 2 : ℂ)).re ≤ 1 := by
              rw [hu_re_sqrt]
              have hsig_nn := virasoroSigma_nonneg hc_ge1
              calc virasoroSigma c * (A * Real.sin θ)
                  ≤ virasoroSigma c * (A * (2 * c ^ (-(1 / 12 : ℝ)))) :=
                    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsin_lt.le hA0.le) hsig_nn
                _ = virasoroSigma c * (2 * A * c ^ (-(1 / 12 : ℝ))) := by ring
                _ ≤ 1 := hSig
            have h1 : ‖virasoroPsiTilde c g u‖ / airyEnv u ≤
                virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ) * (Real.sin θ)⁻¹ := by
              rw [div_le_iff₀ henv_pos]
              refine hII.trans ?_
              have hexp_le : Real.exp (virasoroSigma c * (u ^ (1 / 2 : ℂ)).re) ≤ Real.exp 1 :=
                Real.exp_le_exp.mpr hsig_bd
              have hu_pow : ‖u‖ ^ (-(1 / 2 : ℝ)) = A ^ (-1 : ℝ) := by
                rw [hu_norm, ← Real.rpow_natCast A 2, ← Real.rpow_mul hA0.le]; congr 1; norm_num
              have hre_inv : ((u ^ (1 / 2 : ℂ)).re)⁻¹ = A ^ (-1 : ℝ) * (Real.sin θ)⁻¹ := by
                rw [hu_re_sqrt, mul_inv, Real.rpow_neg_one]
              rw [hu_pow, hre_inv]
              have hA2 : A ^ (-1 : ℝ) * A ^ (-1 : ℝ) = A ^ (-2 : ℝ) := by
                rw [← Real.rpow_add hA0]; norm_num
              have hC0_nn := virasoroEnvC0_pos.le
              have henv_nn := henv_pos.le
              calc virasoroEnvC0 * airyEnv u * Real.exp (virasoroSigma c * (u ^ (1 / 2 : ℂ)).re) *
                    A ^ (-1 : ℝ) * (A ^ (-1 : ℝ) * (Real.sin θ)⁻¹)
                  ≤ virasoroEnvC0 * airyEnv u * Real.exp 1 * A ^ (-1 : ℝ) * (A ^ (-1 : ℝ) * (Real.sin θ)⁻¹) := by
                    gcongr
                _ = virasoroEnvC0 * Real.exp 1 * (A ^ (-1 : ℝ) * A ^ (-1 : ℝ)) * (Real.sin θ)⁻¹ * airyEnv u := by
                    ring
                _ = virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ) * (Real.sin θ)⁻¹ * airyEnv u := by rw [hA2]
            have h2 : 0 ≤ L' * A ^ (-3 : ℝ) * Real.sin θ ^ (-(3 / 2 : ℝ)) :=
              mul_nonneg (mul_nonneg hL' (Real.rpow_nonneg hA0.le _)) (Real.rpow_nonneg hsin_nn _)
            linarith
        have h_prod : pArc A z θ * ‖lowerGoodGReg A c g w‖ ≤
            12 * z.im * (L' * A ^ (-3 : ℝ) + virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ)) := by
          have hG_nn : 0 ≤ ‖lowerGoodGReg A c g w‖ := norm_nonneg _
          have h1 : pArc A z θ * ‖lowerGoodGReg A c g w‖ ≤
              (3 * (z.im / A) * Real.sin θ) *
                (4 * Real.sin θ ^ 2 * A *
                  (L' * A ^ (-3 : ℝ) * Real.sin θ ^ (-(3 / 2 : ℝ)) +
                    virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ) * (Real.sin θ)⁻¹)) := by
            refine mul_le_mul hp_le ?_ hG_nn (by positivity [hz.2.le])
            rw [hGreg_norm]
            exact mul_le_mul_of_nonneg_left h_psi_ratio (by positivity)
          refine h1.trans ?_
          have h_simp : (3 * (z.im / A) * Real.sin θ) *
              (4 * Real.sin θ ^ 2 * A *
                (L' * A ^ (-3 : ℝ) * Real.sin θ ^ (-(3 / 2 : ℝ)) +
                  virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ) * (Real.sin θ)⁻¹)) =
              12 * z.im * (L' * A ^ (-3 : ℝ) * Real.sin θ ^ (3 / 2 : ℝ) +
                virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ) * Real.sin θ ^ 2) := by
            have hs3 : Real.sin θ * Real.sin θ ^ 2 * Real.sin θ ^ (-(3 / 2 : ℝ)) =
                Real.sin θ ^ (3 / 2 : ℝ) := by
              calc Real.sin θ * Real.sin θ ^ 2 * Real.sin θ ^ (-(3 / 2 : ℝ))
                  = Real.sin θ ^ (1 : ℝ) * Real.sin θ ^ (2 : ℝ) * Real.sin θ ^ (-(3 / 2 : ℝ)) := by
                    simp [Real.rpow_one]
                _ = Real.sin θ ^ (3 / 2 : ℝ) := by
                    rw [← Real.rpow_add hsin_pos, ← Real.rpow_add hsin_pos]
                    congr 1; norm_num
            field_simp [hA0.ne', hsin_pos.ne']
            calc 3 * z.im * Real.sin θ ^ 2 * 4 *
                  (Real.sin θ * L' * A ^ (-3 : ℝ) * Real.sin θ ^ (-(3 / 2 : ℝ)) +
                    virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ))
                = 12 * z.im * (L' * A ^ (-3 : ℝ) * (Real.sin θ * Real.sin θ ^ 2 * Real.sin θ ^ (-(3 / 2 : ℝ))) +
                    virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ) * Real.sin θ ^ 2) := by ring
              _ = z.im * 12 * (L' * A ^ (-3 : ℝ) * Real.sin θ ^ (3 / 2 : ℝ) +
                    Real.sin θ ^ 2 * virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ)) := by
                  rw [hs3]; ring
          rw [h_simp]
          have hs32_le : Real.sin θ ^ (3 / 2 : ℝ) ≤ 1 :=
            Real.rpow_le_one hsin_nn hsin_le1 (by norm_num)
          have hs2_le : Real.sin θ ^ 2 ≤ 1 := pow_le_one₀ hsin_nn hsin_le1
          have hC0_nn := virasoroEnvC0_pos.le
          have hz_im := hz.2.le
          exact mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_of_le_one_right (by positivity) hs32_le)
              (mul_le_of_le_one_right (by positivity) hs2_le))
            (by positivity)
        exact h_prod
      refine h_int_le.trans ?_
      rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      linarith
  exact hnorm_pois

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.lowerGood_re_cpow_three_halves_lip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.lowerGood_re_cpow_three_halves_lip

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.lowerGood_inv_norm_area_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.lowerGood_inv_norm_area_le

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.lowerGood_GReg_poisson_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.lowerGood_GReg_poisson_bound
