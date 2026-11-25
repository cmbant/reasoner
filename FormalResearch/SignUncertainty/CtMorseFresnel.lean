module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The Fresnel integral against a smooth cutoff

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:morse-expansion` (the "Abel" step).  **Proved.**

For `χ ∈ C^∞(ℝ)` real, equal to `1` near `0` and to `0` for large `|x|`, and `σ = ±1`, `μ > 0`:
`|∫ χ(x) e^{iσμx²/2} dx - e^{iσπ/4} √(2π/μ)| ≤ K_N μ^{-N}` for every `N ≥ 1`, with `K_N` depending only on `χ, N`.

Proof: damp by `e^{-εx²/2}`; on `ψ = 1 - χ` (which vanishes near `0`) integrate by parts `N` times against
`(iσμ - ε)⁻¹ x⁻¹ ∂_x` (no boundary terms, uniformly in `ε`), and evaluate the full Gaussian integral
`∫ e^{(iσμ - ε)x²/2} = (2π/(ε - iσμ))^{1/2}`, then let `ε ↓ 0`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty.CtMorse

/-- The damped Fresnel kernel `e^{(iλ - ε)x²/2}`. -/
noncomputable def phiE (lam ε : ℝ) (x : ℝ) : ℂ := Complex.exp (((Complex.I * lam - ε) * (x : ℂ) ^ 2) / 2)

lemma norm_phiE (lam ε x : ℝ) : ‖phiE lam ε x‖ = Real.exp (-ε * x ^ 2 / 2) := by
  unfold phiE
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.sub_re, pow_two]

lemma norm_phiE_le {lam ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) : ‖phiE lam ε x‖ ≤ 1 := by
  rw [norm_phiE]; apply Real.exp_le_one_iff.mpr; nlinarith only [hε, sq_nonneg x]

lemma continuous_phiE (lam ε : ℝ) : Continuous (phiE lam ε) := by unfold phiE; fun_prop

lemma hasDerivAt_phiE (lam ε x : ℝ) :
    HasDerivAt (phiE lam ε) (((Complex.I * lam - ε) * (x : ℂ)) * phiE lam ε x) x := by
  unfold phiE
  have h1 : HasDerivAt (fun y : ℝ => (((Complex.I * lam - ε) * (y : ℂ) ^ 2) / 2))
      (((Complex.I * lam - ε) * (2 * (x : ℂ))) / 2) x := by
    have := (((hasDerivAt_id (x : ℂ)).pow 2).const_mul (Complex.I * lam - ε)).div_const 2
    have h2 := this.comp_ofReal
    simpa using h2
  have h3 := h1.cexp
  refine h3.congr_deriv ?_
  ring

lemma integrable_phiE_mul {lam ε : ℝ} (hε : 0 < ε) {f : ℝ → ℂ} (hf : Continuous f) {B : ℝ}
    (hB : ∀ x, ‖f x‖ ≤ B) : Integrable fun x => f x * phiE lam ε x := by
  have hg : Integrable fun x : ℝ => B * Real.exp (-(ε / 2) * x ^ 2) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < ε / 2)).const_mul B
  refine hg.mono' (hf.mul (continuous_phiE lam ε)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_phiE]
  have : Real.exp (-ε * x ^ 2 / 2) = Real.exp (-(ε / 2) * x ^ 2) := by congr 1; ring
  rw [this]
  exact mul_le_mul_of_nonneg_right (hB x) (Real.exp_pos _).le

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The sequence `ψ_0 = ψ`, `ψ_{k+1} = (ψ_k / x)'`. -/
noncomputable def psiSeq (ψ : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => ψ
  | k + 1 => deriv (fun y : ℝ => psiSeq ψ k y / (y : ℂ))

/-- The constants in the tail `ψ_k(x) = c_k x^{-2k}` (`c_0 = 1`, `c_{k+1} = -(2k+1) c_k`). -/
def cK : ℕ → ℝ
  | 0 => 1
  | k + 1 => -(2 * (k : ℝ) + 1) * cK k

lemma u_contDiff {φ : ℝ → ℂ} {δ : ℝ} (hδ : 0 < δ) (hs : ContDiff ℝ ∞' φ) (hz : ∀ x, |x| < δ → φ x = 0) :
    ContDiff ℝ ∞' (fun y : ℝ => φ y / (y : ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have hev : (fun y : ℝ => φ y / (y : ℂ)) =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℂ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with y hy
      rw [hz y (by simpa [Real.dist_eq] using hy), zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hg : ContDiffAt ℝ ∞' (fun y : ℝ => (y : ℂ)) x := Complex.ofRealCLM.contDiff.contDiffAt
    have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    have hinv : ContDiffAt ℝ ∞' (fun y : ℝ => ((y : ℂ))⁻¹) x :=
      ((contDiffAt_inv ℂ hx').restrict_scalars ℝ).comp x hg
    simp only [div_eq_mul_inv]
    exact hs.contDiffAt.mul hinv

lemma psiSeq_step {φ : ℝ → ℂ} {δ A : ℝ} {k : ℕ} (hδ : 0 < δ) (hA : 0 ≤ A) (hs : ContDiff ℝ ∞' φ)
    (hz : ∀ x, |x| < δ → φ x = 0) (ht : ∀ x, A < |x| → φ x = ((cK k * x ^ (-(2 * k : ℤ)) : ℝ) : ℂ)) :
    ContDiff ℝ ∞' (deriv fun y : ℝ => φ y / (y : ℂ)) ∧
    (∀ x, |x| < δ → deriv (fun y : ℝ => φ y / (y : ℂ)) x = 0) ∧
    (∀ x, A < |x| → deriv (fun y : ℝ => φ y / (y : ℂ)) x = ((cK (k + 1) * x ^ (-(2 * (k + 1) : ℤ)) : ℝ) : ℂ)) := by
  have hu := u_contDiff hδ hs hz
  refine ⟨(contDiff_infty_iff_deriv.mp hu).2, fun x hx => ?_, fun x hx => ?_⟩
  · have hev : (fun y : ℝ => φ y / (y : ℂ)) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      have : ∀ᶠ y : ℝ in 𝓝 x, |y| < δ := (continuous_abs.tendsto x).eventually (gt_mem_nhds hx)
      filter_upwards [this] with y hy
      rw [hz y hy, zero_div]
    rw [hev.deriv_eq]; simp
  · have hx0 : x ≠ 0 := by
      intro h; rw [h, abs_zero] at hx; linarith
    have hev : (fun y : ℝ => φ y / (y : ℂ)) =ᶠ[𝓝 x] fun y : ℝ => ((cK k * y ^ (-(2 * k + 1 : ℤ)) : ℝ) : ℂ) := by
      have : ∀ᶠ y : ℝ in 𝓝 x, A < |y| := (continuous_abs.tendsto x).eventually (lt_mem_nhds hx)
      filter_upwards [this] with y hy
      have hy0 : y ≠ 0 := by
        intro h; rw [h, abs_zero] at hy; linarith
      rw [ht y hy]
      have : (y : ℂ) ≠ 0 := by exact_mod_cast hy0
      push_cast
      rw [zpow_neg, zpow_neg]
      have e : (2 * (k : ℤ) + 1) = (2 * k : ℤ) + 1 := rfl
      rw [e, zpow_add₀ this, zpow_one]
      field_simp
    rw [hev.deriv_eq]
    have hd : HasDerivAt (fun y : ℝ => cK k * y ^ (-(2 * k + 1 : ℤ)))
        (cK k * ((-(2 * k + 1 : ℤ) : ℤ) * x ^ (-(2 * k + 1 : ℤ) - 1))) x :=
      (hasDerivAt_zpow (-(2 * k + 1 : ℤ)) x (Or.inl hx0)).const_mul (cK k)
    have hd' := hd.ofReal_comp
    rw [hd'.deriv]
    have e1 : (-(2 * k + 1 : ℤ) - 1 : ℤ) = -(2 * ((k + 1 : ℕ) : ℤ) : ℤ) := by push_cast; ring
    have e2 : cK (k + 1) = -(2 * (k : ℝ) + 1) * cK k := rfl
    rw [e1, e2]
    push_cast
    ring_nf

lemma psiSeq_props {ψ : ℝ → ℂ} {δ A : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A) (hs : ContDiff ℝ ∞' ψ) (hz : ∀ x, |x| < δ → ψ x = 0)
    (ht : ∀ x, A < |x| → ψ x = 1) (k : ℕ) :
    ContDiff ℝ ∞' (psiSeq ψ k) ∧ (∀ x, |x| < δ → psiSeq ψ k x = 0) ∧
      (∀ x, A < |x| → psiSeq ψ k x = ((cK k * x ^ (-(2 * k : ℤ)) : ℝ) : ℂ)) := by
  induction k with
  | zero => exact ⟨hs, hz, fun x hx => by simp [psiSeq, cK, ht x hx]⟩
  | succ k ih => exact psiSeq_step hδ hA ih.1 ih.2.1 ih.2.2

lemma exists_bound_of_tail {f : ℝ → ℂ} (hf : Continuous f) {T B : ℝ} (h : ∀ x, T ≤ |x| → ‖f x‖ ≤ B) :
    ∃ D : ℝ, ∀ x, ‖f x‖ ≤ D := by
  obtain ⟨D, hD⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max D B, fun x => ?_⟩
  by_cases hx : T ≤ |x|
  · exact (h x hx).trans (le_max_right _ _)
  · have : x ∈ Icc (-T) T := abs_le.mp (not_le.mp hx).le
    exact (hD x this).trans (le_max_left _ _)

lemma tail_norm {c x : ℝ} {k : ℕ} (hx : 1 ≤ |x|) :
    ‖((c * x ^ (-(2 * k : ℤ)) : ℝ) : ℂ)‖ ≤ |c| := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_zpow]
  have h1 : |x| ^ (-(2 * k : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ hx (by omega)
  have h0 : 0 ≤ |x| ^ (-(2 * k : ℤ)) := by positivity
  calc |c| * |x| ^ (-(2 * k : ℤ)) ≤ |c| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
    _ = |c| := mul_one _

lemma tail_norm' {c x : ℝ} {k : ℕ} (hk : 1 ≤ k) (hx : 1 ≤ |x|) :
    ‖((c * x ^ (-(2 * k : ℤ)) : ℝ) : ℂ)‖ ≤ 2 * |c| * (1 + x ^ 2)⁻¹ := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_zpow]
  have hy : (0 : ℝ) < |x| := by linarith
  have h1 : |x| ^ (-(2 * k : ℤ)) ≤ (|x| ^ 2)⁻¹ := by
    have : -(2 * k : ℤ) = -((2 * k : ℕ) : ℤ) := by push_cast; ring
    rw [this, zpow_neg, zpow_natCast]
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_right₀ hx (by omega)
  have h2 : (|x| ^ 2)⁻¹ ≤ 2 * (1 + x ^ 2)⁻¹ := by
    rw [sq_abs]
    have : 1 ≤ x ^ 2 := by nlinarith only [hx, sq_abs x]
    rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [this]
  calc |c| * |x| ^ (-(2 * k : ℤ)) ≤ |c| * (2 * (1 + x ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg c)
    _ = _ := by ring

section Props

variable {ψ : ℝ → ℂ} {δ A : ℝ}

lemma psiSeq_bdd (hδ : 0 < δ) (hA : 0 ≤ A) (hs : ContDiff ℝ ∞' ψ) (hz : ∀ x, |x| < δ → ψ x = 0)
    (ht : ∀ x, A < |x| → ψ x = 1) (k : ℕ) : ∃ D : ℝ, ∀ x, ‖psiSeq ψ k x‖ ≤ D := by
  obtain ⟨h1, -, h3⟩ := psiSeq_props hδ hA hs hz ht k
  refine exists_bound_of_tail (T := A + 1) (B := |cK k|) h1.continuous (fun x hx => ?_)
  have hx1 : 1 ≤ |x| := by linarith
  have hxA : A < |x| := by linarith
  rw [h3 x hxA]
  exact tail_norm hx1

lemma psiSeq_decay (hδ : 0 < δ) (hA : 0 ≤ A) (hs : ContDiff ℝ ∞' ψ) (hz : ∀ x, |x| < δ → ψ x = 0)
    (ht : ∀ x, A < |x| → ψ x = 1) {k : ℕ} (hk : 1 ≤ k) : ∃ D : ℝ, ∀ x, ‖psiSeq ψ k x‖ ≤ D * (1 + x ^ 2)⁻¹ := by
  obtain ⟨h1, -, h3⟩ := psiSeq_props hδ hA hs hz ht k
  have hc : Continuous fun x : ℝ => ‖psiSeq ψ k x‖ * (1 + x ^ 2) := by
    have := h1.continuous; fun_prop
  obtain ⟨D, hD⟩ := (isCompact_Icc (a := -(A + 1)) (b := A + 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max D (2 * |cK k|), fun x => ?_⟩
  have hpos : 0 < 1 + x ^ 2 := by positivity
  by_cases hx : A + 1 ≤ |x|
  · have hx1 : 1 ≤ |x| := by linarith
    have hxA : A < |x| := by linarith
    rw [h3 x hxA]
    exact (tail_norm' hk hx1).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  · have hxm : x ∈ Icc (-(A + 1)) (A + 1) := abs_le.mp (not_le.mp hx).le
    have := hD x hxm
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
    calc ‖psiSeq ψ k x‖ = ‖psiSeq ψ k x‖ * (1 + x ^ 2) * (1 + x ^ 2)⁻¹ := by field_simp
      _ ≤ D * (1 + x ^ 2)⁻¹ := mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- `∫ ψ_k φ_ε = -(c_ε)⁻¹ ∫ ψ_{k+1} φ_ε` (one integration by parts against `x⁻¹ ∂_x`). -/
lemma ibp_psi (hδ : 0 < δ) (hA : 0 ≤ A) (hs : ContDiff ℝ ∞' ψ) (hz : ∀ x, |x| < δ → ψ x = 0)
    (ht : ∀ x, A < |x| → ψ x = 1) {lam ε : ℝ} (hε : 0 < ε) (hlam : lam ≠ 0) (k : ℕ) :
    ∫ x, psiSeq ψ k x * phiE lam ε x =
      -(Complex.I * lam - ε)⁻¹ * ∫ x, psiSeq ψ (k + 1) x * phiE lam ε x := by
  obtain ⟨hs0, hz0, ht0⟩ := psiSeq_props hδ hA hs hz ht k
  obtain ⟨hs1, -, -⟩ := psiSeq_props hδ hA hs hz ht (k + 1)
  set c : ℂ := Complex.I * lam - ε with hc
  have hc0 : c ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [hc] at this
    exact hlam this
  set u : ℝ → ℂ := fun y => psiSeq ψ k y / (y : ℂ) with hu
  have hus : ContDiff ℝ ∞' u := u_contDiff hδ hs0 hz0
  have hud : ∀ x, HasDerivAt u (psiSeq ψ (k + 1) x) x := fun x =>
    ((hus.differentiable (by simp)) x).hasDerivAt
  have hux : ∀ x : ℝ, u x * (x : ℂ) = psiSeq ψ k x := by
    intro x
    by_cases hx : x = 0
    · subst hx; rw [hz0 0 (by simpa using hδ)]; simp
    · have : (x : ℂ) ≠ 0 := by exact_mod_cast hx
      simp only [hu]; field_simp
  obtain ⟨Dk, hDk⟩ := psiSeq_bdd hδ hA hs hz ht k
  obtain ⟨Dk1, hDk1⟩ := psiSeq_bdd hδ hA hs hz ht (k + 1)
  obtain ⟨Du, hDu⟩ : ∃ D : ℝ, ∀ x, ‖u x‖ ≤ D := by
    refine exists_bound_of_tail (T := 1) (B := Dk) hus.continuous (fun x hx => ?_)
    simp only [hu, norm_div, Complex.norm_real, Real.norm_eq_abs]
    rw [div_le_iff₀ (by linarith)]
    calc ‖psiSeq ψ k x‖ ≤ Dk := hDk x
      _ ≤ Dk * |x| := by
          have : 0 ≤ Dk := (norm_nonneg _).trans (hDk 0)
          nlinarith only [this, hx]
  have hF : ∀ x, HasDerivAt (fun y => u y * phiE lam ε y)
      (psiSeq ψ (k + 1) x * phiE lam ε x + c * (psiSeq ψ k x * phiE lam ε x)) x := by
    intro x
    have h := (hud x).mul (hasDerivAt_phiE lam ε x)
    refine h.congr_deriv ?_
    rw [← hux x]; ring
  have i1 : Integrable fun x => psiSeq ψ (k + 1) x * phiE lam ε x :=
    integrable_phiE_mul hε hs1.continuous hDk1
  have i2 : Integrable fun x => psiSeq ψ k x * phiE lam ε x := integrable_phiE_mul hε hs0.continuous hDk
  have i3 : Integrable fun x => u x * phiE lam ε x := integrable_phiE_mul hε hus.continuous hDu
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hF (i1.add (i2.const_mul c)) i3
  rw [integral_add i1 (i2.const_mul c), integral_const_mul] at h0
  have h1 : c * ∫ x, psiSeq ψ k x * phiE lam ε x = -∫ x, psiSeq ψ (k + 1) x * phiE lam ε x := by
    linear_combination h0
  calc ∫ x, psiSeq ψ k x * phiE lam ε x = c⁻¹ * (c * ∫ x, psiSeq ψ k x * phiE lam ε x) :=
        (inv_mul_cancel_left₀ hc0 _).symm
    _ = _ := by rw [h1]; ring

lemma ibp_iter (hδ : 0 < δ) (hA : 0 ≤ A) (hs : ContDiff ℝ ∞' ψ) (hz : ∀ x, |x| < δ → ψ x = 0)
    (ht : ∀ x, A < |x| → ψ x = 1) {lam ε : ℝ} (hε : 0 < ε) (hlam : lam ≠ 0) (N : ℕ) :
    ∫ x, ψ x * phiE lam ε x =
      (-(Complex.I * lam - ε)⁻¹) ^ N * ∫ x, psiSeq ψ N x * phiE lam ε x := by
  induction N with
  | zero => simp [psiSeq]
  | succ N ih =>
    rw [ih, ibp_psi hδ hA hs hz ht hε hlam N, pow_succ]
    ring

/-- `‖∫ ψ φ_ε‖ ≤ |λ|^{-N} ‖ψ_N‖_{L¹}` uniformly in `ε > 0`. -/
lemma norm_integral_psi_le (hδ : 0 < δ) (hA : 0 ≤ A) (hs : ContDiff ℝ ∞' ψ) (hz : ∀ x, |x| < δ → ψ x = 0)
    (ht : ∀ x, A < |x| → ψ x = 1) {N : ℕ} (hN : 1 ≤ N) :
    ∃ K : ℝ, ∀ {lam ε : ℝ}, 0 < ε → lam ≠ 0 → ‖∫ x, ψ x * phiE lam ε x‖ ≤ K / |lam| ^ N := by
  obtain ⟨D, hD⟩ := psiSeq_decay hδ hA hs hz ht hN
  obtain ⟨hsN, -, -⟩ := psiSeq_props hδ hA hs hz ht N
  have hint : Integrable fun x => ‖psiSeq ψ N x‖ := by
    have h1 : Integrable fun x : ℝ => D * (1 + x ^ 2)⁻¹ := integrable_inv_one_add_sq.const_mul D
    exact h1.mono' hsN.continuous.norm.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hD x)
  refine ⟨∫ x, ‖psiSeq ψ N x‖, fun {lam ε} hε hlam => ?_⟩
  rw [ibp_iter hδ hA hs hz ht hε hlam N, norm_mul, norm_pow, norm_neg, norm_inv]
  have hc : |lam| ≤ ‖Complex.I * lam - ε‖ := by
    have := Complex.abs_im_le_norm (Complex.I * lam - ε)
    simpa using this
  have hlam' : 0 < |lam| := abs_pos.mpr hlam
  have h1 : ‖(Complex.I * lam - ε)‖⁻¹ ≤ |lam|⁻¹ := inv_anti₀ hlam' hc
  have h2 : ‖∫ x, psiSeq ψ N x * phiE lam ε x‖ ≤ ∫ x, ‖psiSeq ψ N x‖ := by
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun x => norm_nonneg _) hint (Eventually.of_forall fun x => ?_))
    show ‖psiSeq ψ N x * phiE lam ε x‖ ≤ ‖psiSeq ψ N x‖
    rw [norm_mul]
    have := norm_phiE_le (lam := lam) hε.le x
    exact mul_le_of_le_one_right (norm_nonneg _) this
  calc ‖Complex.I * lam - ε‖⁻¹ ^ N * ‖∫ x, psiSeq ψ N x * phiE lam ε x‖
      ≤ |lam|⁻¹ ^ N * ∫ x, ‖psiSeq ψ N x‖ := by
        apply mul_le_mul (pow_le_pow_left₀ (by positivity) h1 N) h2 (norm_nonneg _) (by positivity)
    _ = _ := by rw [inv_pow, div_eq_inv_mul]

end Props

lemma phiE_zero_eq (σ μ x : ℝ) :
    phiE (σ * μ) 0 x = Complex.exp (Complex.I * ((σ * μ : ℝ) : ℂ) * (x : ℂ) ^ 2 / 2) := by
  unfold phiE; congr 1; push_cast; ring

/-- The Gaussian value `∫ e^{(iλ-ε)x²/2} dx = (2π/(ε - iλ))^{1/2}`. -/
lemma integral_phiE {lam ε : ℝ} (hε : 0 < ε) :
    ∫ x, phiE lam ε x = ((π : ℂ) / (((ε : ℂ) - Complex.I * lam) / 2)) ^ (1 / 2 : ℂ) := by
  have hb : 0 < (((ε : ℂ) - Complex.I * lam) / 2).re := by simp; linarith
  rw [← integral_gaussian_complex hb]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [phiE]; congr 1; ring

lemma fresnel_value {σ μ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hμ : 0 < μ) :
    ((π : ℂ) / (((0 : ℝ) - Complex.I * ((σ * μ : ℝ) : ℂ)) / 2)) ^ (1 / 2 : ℂ) =
      Complex.exp (σ * (π / 4) * Complex.I) * ((Real.sqrt (2 * π / μ) : ℝ) : ℂ) := by
  have hr : 0 < 2 * π / μ := by positivity
  have hσ2 : σ * σ = 1 := by rcases hσ with h | h <;> subst h <;> norm_num
  have hz : ((π : ℂ) / (((0 : ℝ) - Complex.I * ((σ * μ : ℝ) : ℂ)) / 2)) =
      ((2 * π / μ : ℝ) : ℂ) * (Complex.I * σ) := by
    have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
    have hσ3 : (σ : ℂ) * σ = 1 := by exact_mod_cast hσ2
    have hσ' : (σ : ℂ) ≠ 0 := by intro h; rw [h] at hσ3; simp at hσ3
    have hden : (((0 : ℝ) : ℂ) - Complex.I * ((σ * μ : ℝ) : ℂ)) / 2 ≠ 0 := by
      push_cast
      simp [hμ', hσ']
    rw [div_eq_iff hden]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    linear_combination (-(μ : ℂ)) * hσ3
  rw [hz]
  have hI : (Complex.I * (σ : ℂ)) ≠ 0 := by
    rcases hσ with h | h <;> subst h <;> simp
  have hne : ((2 * π / μ : ℝ) : ℂ) * (Complex.I * σ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hr.ne') hI
  rw [Complex.cpow_def_of_ne_zero hne, Complex.log_ofReal_mul hr hI]
  have hlog : Complex.log (Complex.I * σ) = (σ : ℂ) * (π / 2) * Complex.I := by
    rcases hσ with h | h <;> subst h
    · simp [Complex.log_I]
    · simp [Complex.log_neg_I]
  rw [hlog]
  have hs : ((Real.sqrt (2 * π / μ) : ℝ) : ℂ) = Complex.exp (((Real.log (2 * π / μ) : ℝ) : ℂ) * (1 / 2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr]
    push_cast; rfl
  rw [hs, ← Complex.exp_add]
  congr 1
  ring

/-- **Fresnel integral against a smooth cutoff** (`ct:morse-expansion`, Abel step).  For `χ` real `C^∞`, `= 1` on
`|x| < δ` and `= 0` for `|x| > A`, `σ = ±1`, `μ > 0`:
`|∫ χ(x) e^{iσμx²/2} dx - e^{iσπ/4} √(2π/μ)| ≤ K / μ^N`, `K` depending only on `χ, N` (`N ≥ 1`). -/
theorem cutoff_fresnel {χ : ℝ → ℝ} {δ A : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A) (hχ : ContDiff ℝ ∞' χ)
    (h1 : ∀ x, |x| < δ → χ x = 1) (h0 : ∀ x, A < |x| → χ x = 0) {N : ℕ} (hN : 1 ≤ N) :
    ∃ K : ℝ, ∀ {σ μ : ℝ}, (σ = 1 ∨ σ = -1) → 0 < μ →
      ‖(∫ x : ℝ, (χ x : ℂ) * Complex.exp (Complex.I * ((σ * μ : ℝ) : ℂ) * (x : ℂ) ^ 2 / 2)) -
        Complex.exp (σ * (π / 4) * Complex.I) * ((Real.sqrt (2 * π / μ) : ℝ) : ℂ)‖ ≤ K / μ ^ N := by
  set ψ : ℝ → ℂ := fun x => 1 - (χ x : ℂ) with hψ
  have hs : ContDiff ℝ ∞' ψ := contDiff_const.sub (Complex.ofRealCLM.contDiff.comp hχ)
  have hz : ∀ x, |x| < δ → ψ x = 0 := fun x hx => by simp [hψ, h1 x hx]
  have ht : ∀ x, A < |x| → ψ x = 1 := fun x hx => by simp [hψ, h0 x hx]
  obtain ⟨K, hK⟩ := norm_integral_psi_le hδ hA hs hz ht hN
  refine ⟨K, fun {σ μ} hσ hμ => ?_⟩
  set lam : ℝ := σ * μ with hlam
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> subst h <;> norm_num
  have hlam0 : lam ≠ 0 := mul_ne_zero hσ0 hμ.ne'
  have habs : |lam| = μ := by
    rw [hlam, abs_mul, abs_of_pos hμ]; rcases hσ with h | h <;> subst h <;> simp
  -- continuity of χ, compact support
  have hχc : Continuous (fun x : ℝ => (χ x : ℂ)) := Complex.continuous_ofReal.comp hχ.continuous
  have hχi : Integrable fun x : ℝ => (χ x : ℂ) := by
    refine hχc.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_Icc (a := -(A + 1)) (b := A + 1)) ?_)
    intro x hx
    have : A < |x| := by
      by_contra hle
      exact hx (abs_le.mp (by linarith [not_lt.mp hle] : |x| ≤ A + 1))
    simp [h0 x this]
  -- the damped identity
  have hε : ∀ ε : ℝ, 0 < ε →
      ‖(∫ x, phiE lam ε x) - ∫ x, (χ x : ℂ) * phiE lam ε x‖ ≤ K / μ ^ N := by
    intro ε hε
    have hi1 : Integrable fun x => phiE lam ε x := by
      simpa using integrable_phiE_mul (lam := lam) hε (f := fun _ => (1 : ℂ)) continuous_const
        (B := 1) (fun x => by simp)
    have hi2 : Integrable fun x => (χ x : ℂ) * phiE lam ε x := by
      obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ x, ‖(χ x : ℂ)‖ ≤ B :=
        exists_bound_of_tail hχc (T := A + 1) (B := 0) (fun x hx => by
          have : A < |x| := by linarith
          simp [h0 x this])
      exact integrable_phiE_mul hε hχc hB
    have : ∫ x, ψ x * phiE lam ε x = (∫ x, phiE lam ε x) - ∫ x, (χ x : ℂ) * phiE lam ε x := by
      rw [← integral_sub hi1 hi2]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp [hψ]; ring
    rw [← this]
    have := hK hε hlam0
    rwa [habs] at this
  -- the limit ε → 0+
  have hlim1 : Tendsto (fun ε : ℝ => ∫ x, (χ x : ℂ) * phiE lam ε x) (𝓝[>] 0)
      (𝓝 (∫ x, (χ x : ℂ) * phiE lam 0 x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖(χ x : ℂ)‖) ?_ ?_ hχi.norm ?_
    · exact Eventually.of_forall fun ε => (hχc.mul (continuous_phiE lam ε)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε'
      refine Eventually.of_forall fun x => ?_
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_phiE_le (le_of_lt (show (0 : ℝ) < ε from hε')) x)
    · refine Eventually.of_forall fun x => ?_
      have : Continuous fun ε : ℝ => (χ x : ℂ) * phiE lam ε x := by unfold phiE; fun_prop
      exact (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hslit : ((π : ℂ) / (((0 : ℝ) - Complex.I * (lam : ℂ)) / 2)) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    have : ((π : ℂ) / (((0 : ℝ) - Complex.I * (lam : ℂ)) / 2)) = ((2 * π / lam : ℝ) : ℂ) * Complex.I := by
      have hl' : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam0
      push_cast
      field_simp
      ring_nf
      rw [Complex.I_sq]; ring
    rw [this]
    simp [Real.pi_pos.ne', hlam0]
  have hlim2 : Tendsto (fun ε : ℝ => ∫ x, phiE lam ε x) (𝓝[>] 0)
      (𝓝 (((π : ℂ) / (((0 : ℝ) - Complex.I * (lam : ℂ)) / 2)) ^ (1 / 2 : ℂ))) := by
    have hcont : ContinuousAt (fun ε : ℝ => ((π : ℂ) / (((ε : ℂ) - Complex.I * lam) / 2)) ^ (1 / 2 : ℂ)) 0 := by
      have hd : ContinuousAt (fun ε : ℝ => (π : ℂ) / (((ε : ℂ) - Complex.I * lam) / 2)) 0 := by
        refine ContinuousAt.div continuousAt_const (by fun_prop) ?_
        simp only [Complex.ofReal_zero, zero_sub]
        have : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam0
        simp [this]
      have h2 : ContinuousAt (fun z : ℂ => z ^ (1 / 2 : ℂ)) ((π : ℂ) / ((((0 : ℝ) : ℂ) - Complex.I * lam) / 2)) :=
        continuousAt_cpow_const (by simpa using hslit)
      exact h2.comp (f := fun ε : ℝ => (π : ℂ) / (((ε : ℂ) - Complex.I * lam) / 2)) hd
    have h3 := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε'
    rw [integral_phiE (show (0 : ℝ) < ε from hε')]
  have hlim := hlim2.sub hlim1
  have hfin := le_of_tendsto (b := K / μ ^ N) hlim.norm (by
    filter_upwards [self_mem_nhdsWithin] with ε hε'
    exact hε ε (show (0 : ℝ) < ε from hε'))
  have e1 : (∫ x, (χ x : ℂ) * phiE lam 0 x) =
      ∫ x : ℝ, (χ x : ℂ) * Complex.exp (Complex.I * ((σ * μ : ℝ) : ℂ) * (x : ℂ) ^ 2 / 2) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hlam, phiE_zero_eq]
  rw [e1, hlam, fresnel_value hσ hμ] at hfin
  rw [norm_sub_rev]
  exact hfin

/-- info: 'FormalResearch.SignUncertainty.CtMorse.cutoff_fresnel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cutoff_fresnel

end FormalResearch.SignUncertainty.CtMorse
