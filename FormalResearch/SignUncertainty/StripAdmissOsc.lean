module

public import FormalResearch.CohnElkies.TwoIBPPhase
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# An oscillatory-integral tail lemma for amplitudes with a Hölder cusp at the origin

Source: `CFT/sign_uncertainty/paper/mellin_airy_toolkit.tex`, proof of Lemma T.8 (`uct:admiss`), second paragraph of (2): the decomposition
`g = g_out + g_1 + g_2 + g_3 + g_4` of an amplitude `g` with `|∂^j(g - g(0))| ≲ |τ|^{α-j}` near `0` and `|∂^j g| ≲ (1+|τ|)^{-5/2}` away from `0`,
and two integrations by parts against a phase `ψ` with `ψ' ≥ λ`.

Abstract statement (`osc_tail`): for such `g` (continuous, `C²` off `0`) and a phase `ψ ∈ C³` with `λ ≤ ψ'`, `|ψ''| ≤ λ`, `|ψ'''| ≤ 2λ` on `[-T, T]`
(`T ≥ 1`), and any cut scale `ℓ ≥ 4`,
`|∫ g e^{iψ}| ≤ K (T^{-3/2} + ℓ^{-1-α} + λ^{-2}(ℓ^{1-α} + 1))`, `K` depending only on `α` and the constants of `g`.

The paper's five pieces are merged into three: `g = (1 - χ_*) g + (χ_* g - η h) + η h`, `h = g - g(0)`, `χ_*(τ) = χ(τ/T)`, `η(τ) = χ(ℓτ)`.
The first and last are estimated directly, the middle one (supported in `[-T, T]`, constant near `0`) by `two_ibp_phase`.

Status: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-! ### The cutoff -/

lemma zero_of_gt_one {h : ℝ → ℝ} (hc : Continuous h) (h0 : ∀ x, 1 < |x| → h x = 0) :
    ∀ x, 1 ≤ |x| → h x = 0 := by
  have hcl : IsClosed {x : ℝ | h x = 0} := isClosed_eq hc continuous_const
  have h1 : Ici (1 : ℝ) ⊆ {x : ℝ | h x = 0} := by
    have : Ioi (1 : ℝ) ⊆ {x : ℝ | h x = 0} := fun x hx => h0 x (by rw [abs_of_pos (by linarith [mem_Ioi.mp hx])]; exact hx)
    have := closure_minimal this hcl
    rwa [closure_Ioi] at this
  have h2 : Iic (-1 : ℝ) ⊆ {x : ℝ | h x = 0} := by
    have : Iio (-1 : ℝ) ⊆ {x : ℝ | h x = 0} := fun x hx => h0 x (by
      have hx' := mem_Iio.mp hx
      rw [abs_of_neg (by linarith)]; linarith)
    have := closure_minimal this hcl
    rwa [closure_Iio] at this
  intro x hx
  rcases le_abs'.mp hx with h | h
  · exact h2 h
  · exact h1 h

/-- A smooth cutoff `χ`: values in `[0,1]`, `χ = 1` on `[-1/2,1/2]`, and `χ`, `χ'`, `χ''` vanish for `|x| ≥ 1`. -/
lemma exists_cutoff : ∃ χ : ℝ → ℝ, ContDiff ℝ 2 χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
    (∀ x, |x| ≤ 1 / 2 → χ x = 1) ∧
    (∀ x, 1 ≤ |x| → χ x = 0 ∧ deriv χ x = 0 ∧ deriv (deriv χ) x = 0) ∧
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x, |deriv χ x| ≤ D ∧ |deriv (deriv χ) x| ≤ D := by
  let f : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hcd : ContDiff ℝ 2 (f : ℝ → ℝ) := f.contDiff
  have hcs : HasCompactSupport (f : ℝ → ℝ) := f.hasCompactSupport
  have hd1 : ContDiff ℝ 1 (deriv (f : ℝ → ℝ)) := hcd.iterate_deriv' 1 1
  have hd2 : Continuous (deriv (deriv (f : ℝ → ℝ))) := hd1.continuous_deriv le_rfl
  have hz0 : ∀ x, 1 < |x| → (f : ℝ → ℝ) x = 0 := fun x hx =>
    f.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hx.le)
  have hz1 : ∀ x, 1 < |x| → deriv (f : ℝ → ℝ) x = 0 := by
    intro x hx
    have : (f : ℝ → ℝ) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hx] with y hy using hz0 y hy
    rw [this.deriv_eq]; simp
  have hz2 : ∀ x, 1 < |x| → deriv (deriv (f : ℝ → ℝ)) x = 0 := by
    intro x hx
    have : deriv (f : ℝ → ℝ) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hx] with y hy using hz1 y hy
    rw [this.deriv_eq]; simp
  have e0 := zero_of_gt_one f.continuous hz0
  have e1 := zero_of_gt_one hd1.continuous hz1
  have e2 := zero_of_gt_one hd2 hz2
  obtain ⟨D1, hD1⟩ := hd1.continuous.bounded_above_of_compact_support hcs.deriv
  obtain ⟨D2, hD2⟩ := hd2.bounded_above_of_compact_support hcs.deriv.deriv
  refine ⟨f, hcd, fun x => ⟨f.nonneg, f.le_one⟩, fun x hx => f.one_of_mem_closedBall (by rw [mem_closedBall_zero_iff, Real.norm_eq_abs]; exact hx),
    fun x hx => ⟨e0 x hx, e1 x hx, e2 x hx⟩, max |D1| |D2|, by positivity, fun x => ?_⟩
  refine ⟨?_, ?_⟩
  · have := hD1 x; rw [Real.norm_eq_abs] at this
    exact this.trans ((le_abs_self _).trans (le_max_left _ _))
  · have := hD2 x; rw [Real.norm_eq_abs] at this
    exact this.trans ((le_abs_self _).trans (le_max_right _ _))

/-! ### Derivatives of the scaled cutoff -/

lemma hasDerivAt_cut {χ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) (s τ : ℝ) :
    HasDerivAt (fun x => χ (s * x)) (s * deriv χ (s * τ)) τ := by
  have h1 : HasDerivAt χ (deriv χ (s * τ)) (s * τ) :=
    ((hχ.differentiable (by norm_num)) (s * τ)).hasDerivAt
  have h2 := h1.comp τ ((hasDerivAt_id τ).const_mul s)
  refine (h2.congr_deriv ?_)
  simp [mul_comm]

lemma hasDerivAt_cut' {χ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) (s τ : ℝ) :
    HasDerivAt (fun x => s * deriv χ (s * x)) (s ^ 2 * deriv (deriv χ) (s * τ)) τ := by
  have hd : ContDiff ℝ 1 (deriv χ) := hχ.iterate_deriv' 1 1
  have h1 : HasDerivAt (deriv χ) (deriv (deriv χ) (s * τ)) (s * τ) :=
    ((hd.differentiable one_ne_zero) (s * τ)).hasDerivAt
  have h2 := (h1.comp τ ((hasDerivAt_id τ).const_mul s)).const_mul s
  refine (h2.congr_deriv ?_)
  simp [sq]; ring

lemma deriv_cut {χ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) (s : ℝ) :
    deriv (fun x => χ (s * x)) = fun x => s * deriv χ (s * x) :=
  funext fun x => (hasDerivAt_cut hχ s x).deriv

/-! ### The amplitude `a = χ_* g - η (g - g(0))` and its derivatives off `0` -/

/-- `a(τ) = χ(sτ) g(τ) - χ(ℓτ) (g(τ) - g(0))`. -/
noncomputable def oscAmp (χ : ℝ → ℝ) (g : ℝ → ℂ) (s ℓ : ℝ) (τ : ℝ) : ℂ :=
  χ (s * τ) • g τ - χ (ℓ * τ) • (g τ - g 0)

/-- The explicit first derivative of `oscAmp` off `0`. -/
noncomputable def oscAmp1 (χ : ℝ → ℝ) (g : ℝ → ℂ) (s ℓ : ℝ) (τ : ℝ) : ℂ :=
  (s * deriv χ (s * τ)) • g τ + χ (s * τ) • deriv g τ - (ℓ * deriv χ (ℓ * τ)) • (g τ - g 0) -
    χ (ℓ * τ) • deriv g τ

/-- The explicit second derivative of `oscAmp` off `0`. -/
noncomputable def oscAmp2 (χ : ℝ → ℝ) (g : ℝ → ℂ) (s ℓ : ℝ) (τ : ℝ) : ℂ :=
  (s ^ 2 * deriv (deriv χ) (s * τ)) • g τ + (2 * (s * deriv χ (s * τ))) • deriv g τ +
    χ (s * τ) • deriv (deriv g) τ - (ℓ ^ 2 * deriv (deriv χ) (ℓ * τ)) • (g τ - g 0) -
    (2 * (ℓ * deriv χ (ℓ * τ))) • deriv g τ - χ (ℓ * τ) • deriv (deriv g) τ

section deriv

variable {χ : ℝ → ℝ} {g : ℝ → ℂ}

lemma hasDerivAt_oscAmp (hχ : ContDiff ℝ 2 χ) (s ℓ : ℝ) {τ : ℝ} (hg1 : HasDerivAt g (deriv g τ) τ) :
    HasDerivAt (oscAmp χ g s ℓ) (oscAmp1 χ g s ℓ τ) τ := by
  have hu := hasDerivAt_cut hχ s τ
  have hv := hasDerivAt_cut hχ ℓ τ
  have h := (hu.smul hg1).sub ((hv.smul (hg1.sub_const (g 0))))
  refine h.congr_deriv ?_
  unfold oscAmp1
  simp only [smul_sub]
  abel

lemma hasDerivAt_oscAmp1 (hχ : ContDiff ℝ 2 χ) (s ℓ : ℝ) {τ : ℝ} (hg1 : HasDerivAt g (deriv g τ) τ)
    (hg2 : HasDerivAt (deriv g) (deriv (deriv g) τ) τ) :
    HasDerivAt (oscAmp1 χ g s ℓ) (oscAmp2 χ g s ℓ τ) τ := by
  have hu := hasDerivAt_cut hχ s τ
  have hv := hasDerivAt_cut hχ ℓ τ
  have hu' := hasDerivAt_cut' hχ s τ
  have hv' := hasDerivAt_cut' hχ ℓ τ
  have h := (((hu'.smul hg1).add (hu.smul hg2)).sub (hv'.smul (hg1.sub_const (g 0)))).sub (hv.smul hg2)
  refine h.congr_deriv ?_
  unfold oscAmp2
  module

lemma deriv_oscAmp (hχ : ContDiff ℝ 2 χ) (s ℓ : ℝ) (hd1 : ∀ x : ℝ, x ≠ 0 → HasDerivAt g (deriv g x) x) {τ : ℝ}
    (hτ : τ ≠ 0) : deriv (oscAmp χ g s ℓ) τ = oscAmp1 χ g s ℓ τ :=
  (hasDerivAt_oscAmp hχ s ℓ (hd1 τ hτ)).deriv

lemma deriv_deriv_oscAmp (hχ : ContDiff ℝ 2 χ) (s ℓ : ℝ) (hd1 : ∀ x : ℝ, x ≠ 0 → HasDerivAt g (deriv g x) x)
    (hd2 : ∀ x : ℝ, x ≠ 0 → HasDerivAt (deriv g) (deriv (deriv g) x) x) {τ : ℝ} (hτ : τ ≠ 0) :
    deriv (deriv (oscAmp χ g s ℓ)) τ = oscAmp2 χ g s ℓ τ := by
  have hev : deriv (oscAmp χ g s ℓ) =ᶠ[𝓝 τ] oscAmp1 χ g s ℓ := by
    filter_upwards [isOpen_ne.mem_nhds hτ] with x hx using deriv_oscAmp hχ s ℓ hd1 hx
  rw [hev.deriv_eq]
  exact (hasDerivAt_oscAmp1 hχ s ℓ (hd1 τ hτ) (hd2 τ hτ)).deriv

lemma oscAmp_eq_const (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 2 → χ x = 1) {s ℓ : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hℓ : 1 ≤ ℓ)
    {τ : ℝ} (hτ : |τ| < (2 * ℓ)⁻¹) : oscAmp χ g s ℓ τ = g 0 := by
  have hℓ0 : 0 < ℓ := by linarith
  have h1 : |s * τ| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hs0]
    have : (2 * ℓ)⁻¹ ≤ 1 / 2 := by
      rw [← one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    nlinarith [abs_nonneg τ]
  have h2 : |ℓ * τ| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hℓ0]
    have : ℓ * |τ| < ℓ * (2 * ℓ)⁻¹ := mul_lt_mul_of_pos_left hτ hℓ0
    have e : ℓ * (2 * ℓ)⁻¹ = 1 / 2 := by field_simp
    linarith
  unfold oscAmp
  rw [hχ1 _ h1, hχ1 _ h2]
  simp

lemma oscAmp_eq_zero (hχ0 : ∀ x : ℝ, 1 ≤ |x| → χ x = 0) {s ℓ τ : ℝ} (hs0 : 0 < s) (hℓ0 : 0 < ℓ)
    (h1 : 1 ≤ s * |τ|) (h2 : 1 ≤ ℓ * |τ|) : oscAmp χ g s ℓ τ = 0 := by
  unfold oscAmp
  rw [hχ0 _ (by rw [abs_mul, abs_of_pos hs0]; exact h1), hχ0 _ (by rw [abs_mul, abs_of_pos hℓ0]; exact h2)]
  simp

lemma oscAmp_contDiff (hχ : ContDiff ℝ 2 χ) (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 2 → χ x = 1)
    (hg : ContDiffOn ℝ 2 g {τ : ℝ | τ ≠ 0}) {s ℓ : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hℓ : 1 ≤ ℓ) :
    ContDiff ℝ 2 (oscAmp χ g s ℓ) := by
  have hℓ0 : 0 < ℓ := by linarith
  rw [contDiff_iff_contDiffAt]
  intro τ
  by_cases hτ : τ = 0
  · subst hτ
    have hev : oscAmp χ g s ℓ =ᶠ[𝓝 0] fun _ => g 0 := by
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds
        (show |(0 : ℝ)| < (2 * ℓ)⁻¹ by simp; positivity)] with x hx using oscAmp_eq_const hχ1 hs0 hs1 hℓ hx
    exact (contDiffAt_const).congr_of_eventuallyEq hev
  · have hgτ : ContDiffAt ℝ 2 g τ := hg.contDiffAt (isOpen_ne.mem_nhds hτ)
    have hu : ContDiffAt ℝ 2 (fun x : ℝ => χ (s * x)) τ :=
      (hχ.comp (contDiff_const.mul contDiff_id)).contDiffAt
    have hv : ContDiffAt ℝ 2 (fun x : ℝ => χ (ℓ * x)) τ :=
      (hχ.comp (contDiff_const.mul contDiff_id)).contDiffAt
    exact (hu.smul hgτ).sub (hv.smul (hgτ.sub contDiffAt_const))

end deriv

/-! ### Pointwise bounds of the amplitude -/

section bounds

variable {χ : ℝ → ℝ} {D : ℝ}

lemma cut1_le (hχ0 : ∀ x : ℝ, 1 ≤ |x| → deriv χ x = 0) (hD : ∀ x : ℝ, |deriv χ x| ≤ D) {ℓ τ : ℝ} (hℓ : 0 < ℓ)
    (hτ : τ ≠ 0) : |ℓ * deriv χ (ℓ * τ)| ≤ D / |τ| := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hτ0 : 0 < |τ| := abs_pos.mpr hτ
  by_cases h : 1 ≤ |ℓ * τ|
  · rw [hχ0 _ h]; simp; positivity
  · replace h := not_le.mp h
    rw [abs_mul, abs_of_pos hℓ] at h ⊢
    rw [le_div_iff₀ hτ0]
    calc ℓ * |deriv χ (ℓ * τ)| * |τ| = (ℓ * |τ|) * |deriv χ (ℓ * τ)| := by ring
      _ ≤ 1 * D := mul_le_mul h.le (hD _) (abs_nonneg _) zero_le_one
      _ = D := one_mul D

lemma cut2_le (hχ0 : ∀ x : ℝ, 1 ≤ |x| → deriv (deriv χ) x = 0) (hD : ∀ x : ℝ, |deriv (deriv χ) x| ≤ D)
    {ℓ τ : ℝ} (hℓ : 0 < ℓ) (hτ : τ ≠ 0) : |ℓ ^ 2 * deriv (deriv χ) (ℓ * τ)| ≤ D / |τ| ^ 2 := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hτ0 : 0 < |τ| := abs_pos.mpr hτ
  by_cases h : 1 ≤ |ℓ * τ|
  · rw [hχ0 _ h]; simp; positivity
  · replace h := not_le.mp h
    rw [abs_mul, abs_of_pos hℓ] at h
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ℓ ^ 2), le_div_iff₀ (by positivity)]
    have h2 : (ℓ * |τ|) ^ 2 ≤ 1 := by nlinarith [mul_pos hℓ hτ0]
    calc ℓ ^ 2 * |deriv (deriv χ) (ℓ * τ)| * |τ| ^ 2 = (ℓ * |τ|) ^ 2 * |deriv (deriv χ) (ℓ * τ)| := by ring
      _ ≤ 1 * D := mul_le_mul h2 (hD _) (abs_nonneg _) zero_le_one
      _ = D := one_mul D

lemma norm_smul_le_aux {r R B : ℝ} {z : ℂ} (hr : |r| ≤ R) (hz : ‖z‖ ≤ B) (hR : 0 ≤ R) : ‖r • z‖ ≤ R * B := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul hr hz (norm_nonneg _) hR

end bounds

section Fb

variable {α : ℝ} {χ : ℝ → ℝ} {D : ℝ} {g : ℝ → ℂ} {Cg : ℝ}

/-- The hypotheses on `g` of the tail lemma, bundled. -/
structure OscData (α : ℝ) (g : ℝ → ℂ) (Cg : ℝ) : Prop where
  cont : Continuous g
  c2 : ContDiffOn ℝ 2 g {τ : ℝ | τ ≠ 0}
  near : ∀ τ : ℝ, τ ≠ 0 → |τ| ≤ 1 →
    ‖g τ - g 0‖ ≤ Cg * |τ| ^ α ∧ ‖deriv g τ‖ ≤ Cg * |τ| ^ (α - 1) ∧ ‖deriv (deriv g) τ‖ ≤ Cg * |τ| ^ (α - 2)
  far : ∀ τ : ℝ, 1 / 2 ≤ |τ| →
    ‖g τ‖ ≤ Cg * (1 + |τ|) ^ (-(5 / 2 : ℝ)) ∧ ‖deriv g τ‖ ≤ Cg * (1 + |τ|) ^ (-(5 / 2 : ℝ)) ∧
      ‖deriv (deriv g) τ‖ ≤ Cg * (1 + |τ|) ^ (-(5 / 2 : ℝ))

lemma OscData.hd1 (h : OscData α g Cg) : ∀ x : ℝ, x ≠ 0 → HasDerivAt g (deriv g x) x := by
  intro x hx
  exact ((h.c2.contDiffAt (isOpen_ne.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt

lemma OscData.hd2 (h : OscData α g Cg) : ∀ x : ℝ, x ≠ 0 → HasDerivAt (deriv g) (deriv (deriv g) x) x := by
  intro x hx
  have h1 : ContDiffOn ℝ 1 (deriv g) {τ : ℝ | τ ≠ 0} := h.c2.deriv_of_isOpen isOpen_ne (by norm_num)
  exact ((h1.contDiffAt (isOpen_ne.mem_nhds hx)).differentiableAt one_ne_zero).hasDerivAt

lemma OscData.Cg_nonneg (h : OscData α g Cg) : 0 ≤ Cg := by
  have := (h.near 1 one_ne_zero (by simp)).1
  simp at this
  have h0 := norm_nonneg (g 1 - g 0)
  linarith

lemma OscData.norm_le (h : OscData α g Cg) (hα0 : 0 < α) (τ : ℝ) : ‖g τ‖ ≤ ‖g 0‖ + Cg := by
  have hC := h.Cg_nonneg
  by_cases hτ : τ = 0
  · subst hτ; linarith
  rcases le_total |τ| 1 with h1 | h1
  · have := (h.near τ hτ h1).1
    have h2 : |τ| ^ α ≤ 1 := Real.rpow_le_one (abs_nonneg _) h1 hα0.le
    calc ‖g τ‖ = ‖g 0 + (g τ - g 0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖g 0‖ + ‖g τ - g 0‖ := norm_add_le _ _
      _ ≤ ‖g 0‖ + Cg * |τ| ^ α := by linarith
      _ ≤ ‖g 0‖ + Cg := by nlinarith
  · have hτ2 : 1 / 2 ≤ |τ| := by linarith
    have := (h.far τ hτ2).1
    have h3 : (1 + |τ|) ^ (-(5 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg τ]) (by norm_num)
    nlinarith [norm_nonneg (g 0)]

lemma oscAmp_Fb_le (hα0 : 0 < α) (hα1 : α < 1) (hd : OscData α g Cg) (hχ01 : ∀ x : ℝ, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχ0 : ∀ x : ℝ, 1 ≤ |x| → χ x = 0 ∧ deriv χ x = 0 ∧ deriv (deriv χ) x = 0)
    (hD : ∀ x : ℝ, |deriv χ x| ≤ D ∧ |deriv (deriv χ) x| ≤ D) {s ℓ : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hℓ : 4 ≤ ℓ) {τ : ℝ} (hτ : τ ≠ 0) :
    ‖oscAmp2 χ g s ℓ τ‖ + 3 * ‖oscAmp1 χ g s ℓ τ‖ + 5 * ‖oscAmp χ g s ℓ τ‖ ≤
      (((4 * D + 5) * (‖g 0‖ + Cg) + (8 * D + 13) * Cg) + (6 * D + 9) * Cg) * |τ| ^ (α - 2) := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0).1
  have hCg := hd.Cg_nonneg
  have hBg : 0 ≤ ‖g 0‖ + Cg := by positivity
  have hℓ0 : 0 < ℓ := by linarith
  have ht0 : 0 < |τ| := abs_pos.mpr hτ
  have hu : |χ (s * τ)| ≤ 1 := by rw [abs_of_nonneg (hχ01 _).1]; exact (hχ01 _).2
  have hv : |χ (ℓ * τ)| ≤ 1 := by rw [abs_of_nonneg (hχ01 _).1]; exact (hχ01 _).2
  have hu1 : |s * deriv χ (s * τ)| ≤ D := by
    rw [abs_mul, abs_of_pos hs0]
    calc s * |deriv χ (s * τ)| ≤ 1 * D := mul_le_mul hs1 (hD _).1 (abs_nonneg _) zero_le_one
      _ = D := one_mul D
  have hu2 : |s ^ 2 * deriv (deriv χ) (s * τ)| ≤ D := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < s ^ 2)]
    calc s ^ 2 * |deriv (deriv χ) (s * τ)| ≤ 1 * D :=
          mul_le_mul (by nlinarith) (hD _).2 (abs_nonneg _) zero_le_one
      _ = D := one_mul D
  have hv1 := cut1_le (fun x hx => (hχ0 x hx).2.1) (fun x => (hD x).1) hℓ0 hτ
  have hv2 := cut2_le (fun x hx => (hχ0 x hx).2.2) (fun x => (hD x).2) hℓ0 hτ
  have hpos1 : 0 ≤ D * Cg * |τ| ^ (α - 2) := by positivity
  have hpos2 : 0 ≤ (‖g 0‖ + Cg) * |τ| ^ (α - 2) := by positivity
  have hpos3 : 0 ≤ D * (‖g 0‖ + Cg) * |τ| ^ (α - 2) := by positivity
  have hpos4 : 0 ≤ Cg * |τ| ^ (α - 2) := by positivity
  rcases le_or_gt |τ| 1 with h1 | h1
  · -- the region `0 < |τ| ≤ 1`
    obtain ⟨nh, ng1, ng2⟩ := hd.near τ hτ h1
    have ng := hd.norm_le hα0 τ
    have hα1 : |τ| ^ (α - 1) = |τ| ^ α / |τ| := Real.rpow_sub_one ht0.ne' α
    have hα2 : |τ| ^ (α - 2) = |τ| ^ (α - 1) / |τ| := by
      rw [← Real.rpow_sub_one ht0.ne']; ring_nf
    have htα : |τ| ^ α ≤ 1 := Real.rpow_le_one (abs_nonneg _) h1 hα0.le
    have ht12 : |τ| ^ (α - 1) ≤ |τ| ^ (α - 2) :=
      Real.rpow_le_rpow_of_exponent_ge ht0 h1 (by linarith)
    have h1t2 : 1 ≤ |τ| ^ (α - 2) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 h1 (by linarith)
    have hp1 : 0 ≤ |τ| ^ (α - 1) := by positivity
    have hp2 : 0 ≤ |τ| ^ (α - 2) := by positivity
    have hpα : 0 ≤ |τ| ^ α := by positivity
    have e1 : D / |τ| * (Cg * |τ| ^ α) = D * Cg * |τ| ^ (α - 1) := by rw [hα1]; field_simp
    have e2 : D / |τ| ^ 2 * (Cg * |τ| ^ α) = D * Cg * |τ| ^ (α - 2) := by
      rw [hα2, hα1]; field_simp
    have e3 : D / |τ| * (Cg * |τ| ^ (α - 1)) = D * Cg * |τ| ^ (α - 2) := by rw [hα2]; field_simp
    -- the four basic terms
    have b_ug : ‖χ (s * τ) • g τ‖ ≤ ‖g 0‖ + Cg := by
      have := norm_smul_le_aux hu ng zero_le_one; linarith
    have b_vh : ‖χ (ℓ * τ) • (g τ - g 0)‖ ≤ Cg := by
      have := norm_smul_le_aux hv nh zero_le_one
      nlinarith
    have N0 : ‖oscAmp χ g s ℓ τ‖ ≤ (‖g 0‖ + Cg) + Cg := by
      unfold oscAmp
      exact (norm_sub_le _ _).trans (add_le_add b_ug b_vh)
    have t1 : ‖(s * deriv χ (s * τ)) • g τ‖ ≤ D * (‖g 0‖ + Cg) := norm_smul_le_aux hu1 ng hD0
    have t2 : ‖χ (s * τ) • deriv g τ‖ ≤ Cg * |τ| ^ (α - 1) := by
      have := norm_smul_le_aux hu ng1 zero_le_one; linarith
    have t3 : ‖(ℓ * deriv χ (ℓ * τ)) • (g τ - g 0)‖ ≤ D * Cg * |τ| ^ (α - 1) := by
      have := norm_smul_le_aux hv1 nh (by positivity)
      rw [← e1]; exact this
    have t4 : ‖χ (ℓ * τ) • deriv g τ‖ ≤ Cg * |τ| ^ (α - 1) := by
      have := norm_smul_le_aux hv ng1 zero_le_one; linarith
    have N1 : ‖oscAmp1 χ g s ℓ τ‖ ≤ D * (‖g 0‖ + Cg) + Cg * |τ| ^ (α - 1) + D * Cg * |τ| ^ (α - 1)
        + Cg * |τ| ^ (α - 1) := by
      unfold oscAmp1
      calc _ ≤ ‖(s * deriv χ (s * τ)) • g τ + χ (s * τ) • deriv g τ - (ℓ * deriv χ (ℓ * τ)) • (g τ - g 0)‖ +
            ‖χ (ℓ * τ) • deriv g τ‖ := norm_sub_le _ _
        _ ≤ (‖(s * deriv χ (s * τ)) • g τ + χ (s * τ) • deriv g τ‖ + ‖(ℓ * deriv χ (ℓ * τ)) • (g τ - g 0)‖) +
            ‖χ (ℓ * τ) • deriv g τ‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ ((‖(s * deriv χ (s * τ)) • g τ‖ + ‖χ (s * τ) • deriv g τ‖) + ‖(ℓ * deriv χ (ℓ * τ)) • (g τ - g 0)‖) +
            ‖χ (ℓ * τ) • deriv g τ‖ := by gcongr; exact norm_add_le _ _
        _ ≤ _ := by gcongr
    have s1 : ‖(s ^ 2 * deriv (deriv χ) (s * τ)) • g τ‖ ≤ D * (‖g 0‖ + Cg) := norm_smul_le_aux hu2 ng hD0
    have s2 : ‖(2 * (s * deriv χ (s * τ))) • deriv g τ‖ ≤ 2 * D * (Cg * |τ| ^ (α - 1)) := by
      have h2 : |2 * (s * deriv χ (s * τ))| ≤ 2 * D := by
        rw [abs_mul, abs_two]; linarith
      have := norm_smul_le_aux h2 ng1 (by positivity)
      exact this
    have s3 : ‖χ (s * τ) • deriv (deriv g) τ‖ ≤ Cg * |τ| ^ (α - 2) := by
      have := norm_smul_le_aux hu ng2 zero_le_one; linarith
    have s4 : ‖(ℓ ^ 2 * deriv (deriv χ) (ℓ * τ)) • (g τ - g 0)‖ ≤ D * Cg * |τ| ^ (α - 2) := by
      have := norm_smul_le_aux hv2 nh (by positivity)
      rw [← e2]; exact this
    have s5 : ‖(2 * (ℓ * deriv χ (ℓ * τ))) • deriv g τ‖ ≤ 2 * (D * Cg * |τ| ^ (α - 2)) := by
      have h2 : |2 * (ℓ * deriv χ (ℓ * τ))| ≤ 2 * (D / |τ|) := by
        rw [abs_mul, abs_two]; linarith
      have := norm_smul_le_aux h2 ng1 (by positivity)
      calc _ ≤ 2 * (D / |τ|) * (Cg * |τ| ^ (α - 1)) := this
        _ = 2 * (D / |τ| * (Cg * |τ| ^ (α - 1))) := by ring
        _ = _ := by rw [e3]
    have s6 : ‖χ (ℓ * τ) • deriv (deriv g) τ‖ ≤ Cg * |τ| ^ (α - 2) := by
      have := norm_smul_le_aux hv ng2 zero_le_one; linarith
    have N2 : ‖oscAmp2 χ g s ℓ τ‖ ≤ D * (‖g 0‖ + Cg) + 2 * D * (Cg * |τ| ^ (α - 1)) + Cg * |τ| ^ (α - 2) +
        D * Cg * |τ| ^ (α - 2) + 2 * (D * Cg * |τ| ^ (α - 2)) + Cg * |τ| ^ (α - 2) := by
      unfold oscAmp2
      calc _ ≤ ‖(s ^ 2 * deriv (deriv χ) (s * τ)) • g τ + (2 * (s * deriv χ (s * τ))) • deriv g τ +
            χ (s * τ) • deriv (deriv g) τ - (ℓ ^ 2 * deriv (deriv χ) (ℓ * τ)) • (g τ - g 0) -
            (2 * (ℓ * deriv χ (ℓ * τ))) • deriv g τ‖ + ‖χ (ℓ * τ) • deriv (deriv g) τ‖ := norm_sub_le _ _
        _ ≤ (‖(s ^ 2 * deriv (deriv χ) (s * τ)) • g τ + (2 * (s * deriv χ (s * τ))) • deriv g τ +
            χ (s * τ) • deriv (deriv g) τ - (ℓ ^ 2 * deriv (deriv χ) (ℓ * τ)) • (g τ - g 0)‖ +
            ‖(2 * (ℓ * deriv χ (ℓ * τ))) • deriv g τ‖) + ‖χ (ℓ * τ) • deriv (deriv g) τ‖ := by
              gcongr; exact norm_sub_le _ _
        _ ≤ ((‖(s ^ 2 * deriv (deriv χ) (s * τ)) • g τ + (2 * (s * deriv χ (s * τ))) • deriv g τ +
            χ (s * τ) • deriv (deriv g) τ‖ + ‖(ℓ ^ 2 * deriv (deriv χ) (ℓ * τ)) • (g τ - g 0)‖) +
            ‖(2 * (ℓ * deriv χ (ℓ * τ))) • deriv g τ‖) + ‖χ (ℓ * τ) • deriv (deriv g) τ‖ := by
              gcongr; exact norm_sub_le _ _
        _ ≤ (((‖(s ^ 2 * deriv (deriv χ) (s * τ)) • g τ + (2 * (s * deriv χ (s * τ))) • deriv g τ‖ +
            ‖χ (s * τ) • deriv (deriv g) τ‖) + ‖(ℓ ^ 2 * deriv (deriv χ) (ℓ * τ)) • (g τ - g 0)‖) +
            ‖(2 * (ℓ * deriv χ (ℓ * τ))) • deriv g τ‖) + ‖χ (ℓ * τ) • deriv (deriv g) τ‖ := by
              gcongr; exact norm_add_le _ _
        _ ≤ ((((‖(s ^ 2 * deriv (deriv χ) (s * τ)) • g τ‖ + ‖(2 * (s * deriv χ (s * τ))) • deriv g τ‖) +
            ‖χ (s * τ) • deriv (deriv g) τ‖) + ‖(ℓ ^ 2 * deriv (deriv χ) (ℓ * τ)) • (g τ - g 0)‖) +
            ‖(2 * (ℓ * deriv χ (ℓ * τ))) • deriv g τ‖) + ‖χ (ℓ * τ) • deriv (deriv g) τ‖ := by
              gcongr; exact norm_add_le _ _
        _ ≤ _ := by gcongr
    have c1 : D * (‖g 0‖ + Cg) ≤ D * (‖g 0‖ + Cg) * |τ| ^ (α - 2) := le_mul_of_one_le_right (by positivity) h1t2
    have c2 : Cg * |τ| ^ (α - 1) ≤ Cg * |τ| ^ (α - 2) := mul_le_mul_of_nonneg_left ht12 hCg
    have c3 : D * Cg * |τ| ^ (α - 1) ≤ D * Cg * |τ| ^ (α - 2) := mul_le_mul_of_nonneg_left ht12 (by positivity)
    have c4 : (‖g 0‖ + Cg) ≤ (‖g 0‖ + Cg) * |τ| ^ (α - 2) := le_mul_of_one_le_right hBg h1t2
    have c5 : Cg ≤ Cg * |τ| ^ (α - 2) := le_mul_of_one_le_right hCg h1t2
    have c6 : D * (Cg * |τ| ^ (α - 1)) ≤ D * (Cg * |τ| ^ (α - 2)) :=
      mul_le_mul_of_nonneg_left c2 hD0
    linarith
  · -- the region `|τ| > 1`
    have hτ2 : 1 / 2 ≤ |τ| := by linarith
    obtain ⟨fg, fg1, fg2⟩ := hd.far τ hτ2
    have hw : (1 + |τ|) ^ (-(5 / 2 : ℝ)) ≤ |τ| ^ (α - 2) := by
      calc (1 + |τ|) ^ (-(5 / 2 : ℝ)) ≤ |τ| ^ (-(5 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos ht0 (by linarith) (by norm_num)
        _ ≤ |τ| ^ (α - 2) := Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
    have hw0 : 0 ≤ |τ| ^ (α - 2) := by positivity
    have hl1 : 1 ≤ ℓ * |τ| := by nlinarith
    have hz := hχ0 (ℓ * τ) (by rw [abs_mul, abs_of_pos hℓ0]; exact hl1)
    have hCw : Cg * (1 + |τ|) ^ (-(5 / 2 : ℝ)) ≤ Cg * |τ| ^ (α - 2) := mul_le_mul_of_nonneg_left hw hCg
    have n0 : ‖oscAmp χ g s ℓ τ‖ ≤ Cg * |τ| ^ (α - 2) := by
      unfold oscAmp
      rw [hz.1]
      simp only [zero_smul, sub_zero]
      have := norm_smul_le_aux hu fg zero_le_one; linarith
    have n1 : ‖oscAmp1 χ g s ℓ τ‖ ≤ D * (Cg * |τ| ^ (α - 2)) + Cg * |τ| ^ (α - 2) := by
      unfold oscAmp1
      rw [hz.1, hz.2.1]
      simp only [mul_zero, zero_smul, sub_zero]
      calc _ ≤ ‖(s * deriv χ (s * τ)) • g τ‖ + ‖χ (s * τ) • deriv g τ‖ := norm_add_le _ _
        _ ≤ D * (Cg * (1 + |τ|) ^ (-(5 / 2 : ℝ))) + 1 * (Cg * (1 + |τ|) ^ (-(5 / 2 : ℝ))) :=
          add_le_add (norm_smul_le_aux hu1 fg hD0) (norm_smul_le_aux hu fg1 zero_le_one)
        _ ≤ _ := by
          have : D * (Cg * (1 + |τ|) ^ (-(5 / 2 : ℝ))) ≤ D * (Cg * |τ| ^ (α - 2)) :=
            mul_le_mul_of_nonneg_left hCw hD0
          linarith
    have n2 : ‖oscAmp2 χ g s ℓ τ‖ ≤ D * (Cg * |τ| ^ (α - 2)) + 2 * D * (Cg * |τ| ^ (α - 2)) +
        Cg * |τ| ^ (α - 2) := by
      unfold oscAmp2
      rw [hz.1, hz.2.1, hz.2.2]
      simp only [mul_zero, zero_smul, sub_zero]
      calc _ ≤ ‖(s ^ 2 * deriv (deriv χ) (s * τ)) • g τ + (2 * (s * deriv χ (s * τ))) • deriv g τ‖ +
            ‖χ (s * τ) • deriv (deriv g) τ‖ := norm_add_le _ _
        _ ≤ (‖(s ^ 2 * deriv (deriv χ) (s * τ)) • g τ‖ + ‖(2 * (s * deriv χ (s * τ))) • deriv g τ‖) +
            ‖χ (s * τ) • deriv (deriv g) τ‖ := by gcongr; exact norm_add_le _ _
        _ ≤ (D * (Cg * (1 + |τ|) ^ (-(5 / 2 : ℝ))) + 2 * D * (Cg * (1 + |τ|) ^ (-(5 / 2 : ℝ)))) +
            1 * (Cg * (1 + |τ|) ^ (-(5 / 2 : ℝ))) := by
          refine add_le_add (add_le_add (norm_smul_le_aux hu2 fg hD0) ?_) (norm_smul_le_aux hu fg2 zero_le_one)
          have h2 : |2 * (s * deriv χ (s * τ))| ≤ 2 * D := by
            rw [abs_mul, abs_two]; linarith
          exact norm_smul_le_aux h2 fg1 (by positivity)
        _ ≤ _ := by
          have h3 : D * (Cg * (1 + |τ|) ^ (-(5 / 2 : ℝ))) ≤ D * (Cg * |τ| ^ (α - 2)) :=
            mul_le_mul_of_nonneg_left hCw hD0
          have h4 : 2 * D * (Cg * (1 + |τ|) ^ (-(5 / 2 : ℝ))) ≤ 2 * D * (Cg * |τ| ^ (α - 2)) :=
            mul_le_mul_of_nonneg_left hCw (by positivity)
          linarith
    linarith

end Fb

lemma norm_cexp_I_mul_aux (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := Complex.norm_exp_I_mul_ofReal x

/-! ### The two-integration-by-parts integrand and the weights -/

lemma ibp_integrand_le {lam p1 p2 p3 A0 A1 A2 : ℝ} (hlam : 0 < lam) (hp1 : lam ≤ p1) (hp2 : |p2| ≤ lam)
    (hp3 : |p3| ≤ 2 * lam) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) :
    A2 / p1 ^ 2 + 3 * A1 * |p2| / p1 ^ 3 + A0 * |p3| / p1 ^ 3 + 3 * A0 * p2 ^ 2 / p1 ^ 4 ≤
      (A2 + 3 * A1 + 5 * A0) / lam ^ 2 := by
  have hp0 : 0 < p1 := lt_of_lt_of_le hlam hp1
  have hl2 : 0 < lam ^ 2 := by positivity
  have h1 : A2 / p1 ^ 2 ≤ A2 / lam ^ 2 :=
    div_le_div_of_nonneg_left hA2 hl2 (pow_le_pow_left₀ hlam.le hp1 2)
  have h2 : 3 * A1 * |p2| / p1 ^ 3 ≤ 3 * A1 / lam ^ 2 := by
    calc 3 * A1 * |p2| / p1 ^ 3 ≤ 3 * A1 * lam / lam ^ 3 :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hp2 (by positivity)) (by positivity)
            (pow_le_pow_left₀ hlam.le hp1 3)
      _ = 3 * A1 / lam ^ 2 := by field_simp
  have h3 : A0 * |p3| / p1 ^ 3 ≤ 2 * A0 / lam ^ 2 := by
    calc A0 * |p3| / p1 ^ 3 ≤ A0 * (2 * lam) / lam ^ 3 :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hp3 hA0) (by positivity)
            (pow_le_pow_left₀ hlam.le hp1 3)
      _ = 2 * A0 / lam ^ 2 := by field_simp
  have h4 : 3 * A0 * p2 ^ 2 / p1 ^ 4 ≤ 3 * A0 / lam ^ 2 := by
    have hp2' : p2 ^ 2 ≤ lam ^ 2 := by
      have := sq_le_sq' (by linarith [abs_nonneg p2, neg_abs_le p2]) (abs_le.mp hp2).2
      simpa using this
    calc 3 * A0 * p2 ^ 2 / p1 ^ 4 ≤ 3 * A0 * lam ^ 2 / lam ^ 4 :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hp2' (by positivity)) (by positivity)
            (pow_le_pow_left₀ hlam.le hp1 4)
      _ = 3 * A0 / lam ^ 2 := by field_simp
  calc _ ≤ A2 / lam ^ 2 + 3 * A1 / lam ^ 2 + 2 * A0 / lam ^ 2 + 3 * A0 / lam ^ 2 := by linarith
    _ = _ := by ring

/-- `∫ (r + |τ|)^{-p} = r^{1-p} ∫ (1+|x|)^{-p}` and integrability, for `r > 0`, `p > 1`. -/
lemma shifted_weight {r p : ℝ} (hr : 0 < r) (hp : 1 < p) :
    Integrable (fun τ : ℝ => (r + |τ|) ^ (-p)) ∧
      ∫ τ : ℝ, (r + |τ|) ^ (-p) = r ^ (1 - p) * ∫ x : ℝ, (1 + |x|) ^ (-p) := by
  have hI : Integrable (fun x : ℝ => (1 + |x|) ^ (-p)) := by
    have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := p) (by simpa using hp)
    simpa using this
  have e : ∀ τ : ℝ, (r + |τ|) ^ (-p) = r ^ (-p) * (1 + |τ / r|) ^ (-p) := by
    intro τ
    rw [abs_div, abs_of_pos hr, ← Real.mul_rpow hr.le (by positivity)]
    congr 1; field_simp
  simp_rw [e]
  refine ⟨(hI.comp_div hr.ne').const_mul _, ?_⟩
  rw [integral_const_mul]
  have := Measure.integral_comp_div (fun x : ℝ => (1 + |x|) ^ (-p)) r
  simp only [abs_of_pos hr, smul_eq_mul] at this
  rw [this, ← mul_assoc]
  congr 1
  rw [Real.rpow_sub hr, Real.rpow_one, Real.rpow_neg hr.le]
  field_simp

/-! ### The three pieces -/

section pieces

variable {α : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {χ : ℝ → ℝ}

lemma integrable_weight_sq : Integrable (fun x : ℝ => (1 + |x|) ^ (-(2 : ℝ))) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
  simpa using this

/-- The piece `(1 - χ_*) g`, supported in `|τ| ≥ T/2`. -/
lemma osc_out_bound (hd : OscData α g Cg) (hχ01 : ∀ x : ℝ, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 2 → χ x = 1) {T : ℝ} (hT : 1 ≤ T) (ψ : ℝ → ℝ) :
    ‖∫ τ : ℝ, ((1 - χ (T⁻¹ * τ)) • g τ) * Complex.exp (Complex.I * (ψ τ : ℂ))‖ ≤
      Cg * (1 + T / 2) ^ (-(1 / 2 : ℝ)) * ∫ x : ℝ, (1 + |x|) ^ (-(2 : ℝ)) := by
  have hCg := hd.Cg_nonneg
  have hT0 : 0 < T := by linarith
  calc ‖∫ τ : ℝ, ((1 - χ (T⁻¹ * τ)) • g τ) * Complex.exp (Complex.I * (ψ τ : ℂ))‖
      ≤ ∫ τ : ℝ, ‖((1 - χ (T⁻¹ * τ)) • g τ) * Complex.exp (Complex.I * (ψ τ : ℂ))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ τ : ℝ, (Cg * (1 + T / 2) ^ (-(1 / 2 : ℝ))) * (1 + |τ|) ^ (-(2 : ℝ)) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun τ => norm_nonneg _)
          (integrable_weight_sq.const_mul _) (Eventually.of_forall fun τ => ?_)
        beta_reduce
        rw [norm_mul, norm_cexp_I_mul_aux, mul_one]
        have hM : 0 ≤ (Cg * (1 + T / 2) ^ (-(1 / 2 : ℝ))) * (1 + |τ|) ^ (-(2 : ℝ)) := by positivity
        by_cases hτ : |τ| < T / 2
        · have : χ (T⁻¹ * τ) = 1 := by
            apply hχ1
            rw [abs_mul, abs_of_pos (inv_pos.mpr hT0)]
            have : T⁻¹ * |τ| < T⁻¹ * (T / 2) := mul_lt_mul_of_pos_left hτ (inv_pos.mpr hT0)
            have e : T⁻¹ * (T / 2) = 1 / 2 := by field_simp
            linarith
          rw [this]; simpa using hM
        · replace hτ := not_lt.mp hτ
          have hτ2 : 1 / 2 ≤ |τ| := by linarith
          have hg := (hd.far τ hτ2).1
          have h1 : ‖(1 - χ (T⁻¹ * τ)) • g τ‖ ≤ ‖g τ‖ := by
            rw [norm_smul, Real.norm_eq_abs]
            have := hχ01 (T⁻¹ * τ)
            have h1' : |1 - χ (T⁻¹ * τ)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
            exact mul_le_of_le_one_left (norm_nonneg _) h1'
          have h2 : (1 + |τ|) ^ (-(5 / 2 : ℝ)) ≤ (1 + T / 2) ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-(2 : ℝ)) := by
            have e : (1 + |τ|) ^ (-(5 / 2 : ℝ)) = (1 + |τ|) ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-(2 : ℝ)) := by
              rw [← Real.rpow_add (by positivity)]; norm_num
            rw [e]
            exact mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)) (by positivity)
          calc ‖(1 - χ (T⁻¹ * τ)) • g τ‖ ≤ ‖g τ‖ := h1
            _ ≤ Cg * (1 + |τ|) ^ (-(5 / 2 : ℝ)) := hg
            _ ≤ Cg * ((1 + T / 2) ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-(2 : ℝ))) := mul_le_mul_of_nonneg_left h2 hCg
            _ = _ := by ring
    _ = _ := by rw [integral_const_mul]

/-- The piece `η (g - g(0))`, supported in `|τ| ≤ 1/ℓ`, estimated directly. -/
lemma osc_direct_bound (hα0 : 0 < α) (hd : OscData α g Cg) (hχ01 : ∀ x : ℝ, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχ0 : ∀ x : ℝ, 1 ≤ |x| → χ x = 0) {ℓ : ℝ} (hℓ : 4 ≤ ℓ) (ψ : ℝ → ℝ) :
    ‖∫ τ : ℝ, (χ (ℓ * τ) • (g τ - g 0)) * Complex.exp (Complex.I * (ψ τ : ℂ))‖ ≤
      Cg * (1 / ℓ) ^ α * (2 / ℓ) := by
  have hCg := hd.Cg_nonneg
  have hℓ0 : 0 < ℓ := by linarith
  have hsupp : ∀ τ : ℝ, τ ∉ Icc (-(1 / ℓ)) (1 / ℓ) →
      (χ (ℓ * τ) • (g τ - g 0)) * Complex.exp (Complex.I * (ψ τ : ℂ)) = 0 := by
    intro τ hτ
    have : 1 ≤ |ℓ * τ| := by
      rw [abs_mul, abs_of_pos hℓ0]
      have h2 : 1 / ℓ < |τ| := by
        by_contra hcon
        exact hτ (abs_le.mp (not_lt.mp hcon))
      have := mul_lt_mul_of_pos_left h2 hℓ0
      rw [mul_one_div_cancel hℓ0.ne'] at this
      exact this.le
    rw [hχ0 _ this]; simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (-(1 / ℓ)) (1 / ℓ))
    (f := fun τ : ℝ => (χ (ℓ * τ) • (g τ - g 0)) * Complex.exp (Complex.I * (ψ τ : ℂ)))
    (C := Cg * (1 / ℓ) ^ α) (by simp) (fun τ hτ => ?_)
  · refine h.trans (le_of_eq ?_)
    have hpos : 0 < 1 / ℓ := by positivity
    rw [Real.volume_real_Icc_of_le (by linarith)]
    ring
  · rw [norm_mul, norm_cexp_I_mul_aux, mul_one, norm_smul, Real.norm_eq_abs]
    have hτ1 : |τ| ≤ 1 / ℓ := abs_le.mpr hτ
    have h1ℓ : 1 / ℓ ≤ 1 := by rw [div_le_one hℓ0]; linarith
    have hχ : |χ (ℓ * τ)| ≤ 1 := by rw [abs_of_nonneg (hχ01 _).1]; exact (hχ01 _).2
    by_cases hτ0 : τ = 0
    · subst hτ0; simp; positivity
    · have hn := (hd.near τ hτ0 (hτ1.trans h1ℓ)).1
      have : |τ| ^ α ≤ (1 / ℓ) ^ α := Real.rpow_le_rpow (abs_nonneg _) hτ1 hα0.le
      calc |χ (ℓ * τ)| * ‖g τ - g 0‖ ≤ 1 * ‖g τ - g 0‖ := mul_le_mul_of_nonneg_right hχ (norm_nonneg _)
        _ ≤ Cg * |τ| ^ α := by linarith
        _ ≤ Cg * (1 / ℓ) ^ α := mul_le_mul_of_nonneg_left this hCg

/-- Global pointwise bound for the integrand of the integration by parts, in the shifted-weight form. -/
lemma oscAmp_Fb_global {D : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hd : OscData α g Cg) (hχ : ContDiff ℝ 2 χ)
    (hχ01 : ∀ x : ℝ, 0 ≤ χ x ∧ χ x ≤ 1) (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 2 → χ x = 1)
    (hχ0 : ∀ x : ℝ, 1 ≤ |x| → χ x = 0 ∧ deriv χ x = 0 ∧ deriv (deriv χ) x = 0)
    (hD : ∀ x : ℝ, |deriv χ x| ≤ D ∧ |deriv (deriv χ) x| ≤ D) {T ℓ : ℝ} (hT : 1 ≤ T) (hℓ : 4 ≤ ℓ) (x : ℝ) :
    ‖deriv (deriv (oscAmp χ g T⁻¹ ℓ)) x‖ + 3 * ‖deriv (oscAmp χ g T⁻¹ ℓ) x‖ + 5 * ‖oscAmp χ g T⁻¹ ℓ x‖ ≤
      ((((4 * D + 5) * (‖g 0‖ + Cg) + (8 * D + 13) * Cg) + (6 * D + 9) * Cg) * 2 ^ (2 - α) +
        5 * ‖g 0‖ * ℓ ^ (α - 2)) * ((2 * ℓ)⁻¹ + |x|) ^ (α - 2) := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0).1
  have hCg := hd.Cg_nonneg
  have hT0 : 0 < T := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hs0 : 0 < T⁻¹ := inv_pos.mpr hT0
  have hs1 : T⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hT
  set Cfb : ℝ := (((4 * D + 5) * (‖g 0‖ + Cg) + (8 * D + 13) * Cg) + (6 * D + 9) * Cg) with hCfb
  have hCfb0 : 0 ≤ Cfb := by positivity
  have hr0 : 0 < (2 * ℓ)⁻¹ := by positivity
  have hw0 : 0 < (2 * ℓ)⁻¹ + |x| := by positivity
  by_cases hx : |x| < (2 * ℓ)⁻¹
  · -- near the origin `a` is constant
    have hev : oscAmp χ g T⁻¹ ℓ =ᶠ[𝓝 x] fun _ => g 0 := by
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hx] with y hy
      exact oscAmp_eq_const hχ1 hs0 hs1 (by linarith) hy
    have hev1 : deriv (oscAmp χ g T⁻¹ ℓ) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hx] with y hy
      have : oscAmp χ g T⁻¹ ℓ =ᶠ[𝓝 y] fun _ => g 0 := by
        filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hy] with z hz
        exact oscAmp_eq_const hχ1 hs0 hs1 (by linarith) hz
      rw [this.deriv_eq]; simp
    have e0 : oscAmp χ g T⁻¹ ℓ x = g 0 := hev.self_of_nhds
    have e1 : deriv (oscAmp χ g T⁻¹ ℓ) x = 0 := hev1.self_of_nhds
    have e2 : deriv (deriv (oscAmp χ g T⁻¹ ℓ)) x = 0 := by rw [hev1.deriv_eq]; simp
    rw [e0, e1, e2]
    simp only [norm_zero, mul_zero, add_zero, zero_add]
    -- `1 ≤ ℓ^(α-2) (r0 + |x|)^(α-2)`
    have h1 : (ℓ⁻¹) ^ (α - 2) ≤ ((2 * ℓ)⁻¹ + |x|) ^ (α - 2) := by
      refine Real.rpow_le_rpow_of_nonpos hw0 ?_ (by linarith)
      have : (2 * ℓ)⁻¹ + |x| ≤ (2 * ℓ)⁻¹ + (2 * ℓ)⁻¹ := by linarith
      calc _ ≤ _ := this
        _ = ℓ⁻¹ := by field_simp; ring
    have h2 : ℓ ^ (α - 2) * (ℓ⁻¹) ^ (α - 2) = 1 := by
      rw [← Real.mul_rpow hℓ0.le (inv_nonneg.mpr hℓ0.le), mul_inv_cancel₀ hℓ0.ne', Real.one_rpow]
    have hpos : 0 ≤ 5 * ‖g 0‖ * ℓ ^ (α - 2) := by positivity
    have hp2 : 0 ≤ Cfb * 2 ^ (2 - α) * ((2 * ℓ)⁻¹ + |x|) ^ (α - 2) := by positivity
    calc 5 * ‖g 0‖ = 5 * ‖g 0‖ * (ℓ ^ (α - 2) * (ℓ⁻¹) ^ (α - 2)) := by rw [h2, mul_one]
      _ = (5 * ‖g 0‖ * ℓ ^ (α - 2)) * (ℓ⁻¹) ^ (α - 2) := by ring
      _ ≤ (5 * ‖g 0‖ * ℓ ^ (α - 2)) * ((2 * ℓ)⁻¹ + |x|) ^ (α - 2) := mul_le_mul_of_nonneg_left h1 hpos
      _ ≤ _ := by nlinarith
  · replace hx := not_lt.mp hx
    have hx0 : x ≠ 0 := by
      intro h; rw [h, abs_zero] at hx; exact absurd hx (not_le.mpr hr0)
    have hxpos : 0 < |x| := abs_pos.mpr hx0
    rw [deriv_oscAmp hχ T⁻¹ ℓ hd.hd1 hx0, deriv_deriv_oscAmp hχ T⁻¹ ℓ hd.hd1 hd.hd2 hx0]
    have h1 := oscAmp_Fb_le hα0 hα1 hd hχ01 hχ0 hD hs0 hs1 hℓ hx0
    have h2 : |x| ^ (α - 2) ≤ 2 ^ (2 - α) * ((2 * ℓ)⁻¹ + |x|) ^ (α - 2) := by
      have h3 : ((2 * ℓ)⁻¹ + |x|) ^ (α - 2) ≥ (2 * |x|) ^ (α - 2) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      rw [Real.mul_rpow (by norm_num) hxpos.le] at h3
      have e : (2 : ℝ) ^ (2 - α) * 2 ^ (α - 2) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; simp
      calc |x| ^ (α - 2) = (2 ^ (2 - α) * 2 ^ (α - 2)) * |x| ^ (α - 2) := by rw [e, one_mul]
        _ = 2 ^ (2 - α) * (2 ^ (α - 2) * |x| ^ (α - 2)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
    have hp : 0 ≤ 5 * ‖g 0‖ * ℓ ^ (α - 2) * ((2 * ℓ)⁻¹ + |x|) ^ (α - 2) := by positivity
    calc _ ≤ Cfb * |x| ^ (α - 2) := h1
      _ ≤ Cfb * (2 ^ (2 - α) * ((2 * ℓ)⁻¹ + |x|) ^ (α - 2)) := mul_le_mul_of_nonneg_left h2 hCfb0
      _ ≤ _ := by nlinarith

/-- The middle piece `a = χ_* g - η (g - g(0))`, by two integrations by parts. -/
lemma osc_ibp_bound {D : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hd : OscData α g Cg) (hχ : ContDiff ℝ 2 χ)
    (hχ01 : ∀ x : ℝ, 0 ≤ χ x ∧ χ x ≤ 1) (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 2 → χ x = 1)
    (hχ0 : ∀ x : ℝ, 1 ≤ |x| → χ x = 0 ∧ deriv χ x = 0 ∧ deriv (deriv χ) x = 0)
    (hD : ∀ x : ℝ, |deriv χ x| ≤ D ∧ |deriv (deriv χ) x| ≤ D) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 3 ψ)
    {T lam ℓ : ℝ} (hT : 1 ≤ T) (hℓ : 4 ≤ ℓ) (hlam : 0 < lam)
    (hp1 : ∀ τ : ℝ, |τ| ≤ T → lam ≤ deriv ψ τ) (hp2 : ∀ τ : ℝ, |τ| ≤ T → |deriv (deriv ψ) τ| ≤ lam)
    (hp3 : ∀ τ : ℝ, |τ| ≤ T → |deriv (deriv (deriv ψ)) τ| ≤ 2 * lam) :
    ‖∫ τ : ℝ, oscAmp χ g T⁻¹ ℓ τ * Complex.exp (Complex.I * (ψ τ : ℂ))‖ ≤
      (((((4 * D + 5) * (‖g 0‖ + Cg) + (8 * D + 13) * Cg) + (6 * D + 9) * Cg) * 2 ^ (2 - α) +
        5 * ‖g 0‖ * ℓ ^ (α - 2)) * ((2 * ℓ)⁻¹ ^ (α - 1) * ∫ x : ℝ, (1 + |x|) ^ (-(2 - α)))) / lam ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hs0 : 0 < T⁻¹ := inv_pos.mpr hT0
  have hs1 : T⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hT
  have ha := oscAmp_contDiff hχ hχ1 hd.c2 hs0 hs1 (by linarith : (1 : ℝ) ≤ ℓ)
  have hr0 : 0 < (2 * ℓ)⁻¹ := by positivity
  obtain ⟨hGi, hGint⟩ := shifted_weight hr0 (by linarith : 1 < 2 - α)
  have hd1 : ContDiff ℝ 1 (deriv (oscAmp χ g T⁻¹ ℓ)) := ha.iterate_deriv' 1 1
  have key := two_ibp_phase (a := oscAmp χ g T⁻¹ ℓ) (ψ := ψ) (u := -T) (v := T) (by linarith)
    (ha.of_le (by norm_num)) ∅ Set.countable_empty (fun x _ => (hd1.differentiable one_ne_zero) x)
    (hd1.continuous_deriv le_rfl).continuousOn.integrableOn_Icc
    (fun x hx => by
      have hxT : T < |x| := by
        by_contra hcon
        exact hx (abs_le.mp (not_lt.mp hcon))
      refine oscAmp_eq_zero (fun y hy => (hχ0 y hy).1) hs0 hℓ0 ?_ ?_
      · rw [← div_eq_inv_mul, le_div_iff₀ hT0]; linarith
      · nlinarith)
    hψ (fun x hx => lt_of_lt_of_le hlam (hp1 x (abs_le.mpr hx)))
  refine key.trans ?_
  set C' : ℝ := ((((4 * D + 5) * (‖g 0‖ + Cg) + (8 * D + 13) * Cg) + (6 * D + 9) * Cg) * 2 ^ (2 - α) +
        5 * ‖g 0‖ * ℓ ^ (α - 2)) with hC'
  have hC'0 : 0 ≤ C' := by
    have hCg := hd.Cg_nonneg
    have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0).1
    positivity
  have hGi' : Integrable (fun x : ℝ => C' * (((2 * ℓ)⁻¹ + |x|) ^ (-(2 - α))) / lam ^ 2) :=
    (hGi.const_mul C').div_const _
  calc ∫ x in Icc (-T) T, (‖deriv (deriv (oscAmp χ g T⁻¹ ℓ)) x‖ / deriv ψ x ^ 2
        + 3 * ‖deriv (oscAmp χ g T⁻¹ ℓ) x‖ * |deriv (deriv ψ) x| / deriv ψ x ^ 3
        + ‖oscAmp χ g T⁻¹ ℓ x‖ * |deriv (deriv (deriv ψ)) x| / deriv ψ x ^ 3
        + 3 * ‖oscAmp χ g T⁻¹ ℓ x‖ * deriv (deriv ψ) x ^ 2 / deriv ψ x ^ 4)
      ≤ ∫ x in Icc (-T) T, C' * (((2 * ℓ)⁻¹ + |x|) ^ (-(2 - α))) / lam ^ 2 := by
        refine integral_mono_of_nonneg ?_ hGi'.integrableOn ?_
        · refine ae_restrict_of_forall_mem measurableSet_Icc fun x hx => ?_
          have hxT : |x| ≤ T := abs_le.mpr hx
          have hpos : 0 < deriv ψ x := lt_of_lt_of_le hlam (hp1 x hxT)
          positivity
        · refine ae_restrict_of_forall_mem measurableSet_Icc fun x hx => ?_
          have hxT : |x| ≤ T := abs_le.mpr hx
          have := ibp_integrand_le hlam (hp1 x hxT) (hp2 x hxT) (hp3 x hxT) (norm_nonneg (oscAmp χ g T⁻¹ ℓ x))
            (norm_nonneg (deriv (oscAmp χ g T⁻¹ ℓ) x)) (norm_nonneg (deriv (deriv (oscAmp χ g T⁻¹ ℓ)) x))
          refine this.trans ?_
          rw [div_le_div_iff_of_pos_right (by positivity)]
          have hF := oscAmp_Fb_global hα0 hα1 hd hχ hχ01 hχ1 hχ0 hD hT hℓ x
          have e : ((2 * ℓ)⁻¹ + |x|) ^ (α - 2) = ((2 * ℓ)⁻¹ + |x|) ^ (-(2 - α)) := by congr 1; ring
          rw [e] at hF
          linarith
    _ ≤ ∫ x : ℝ, C' * (((2 * ℓ)⁻¹ + |x|) ^ (-(2 - α))) / lam ^ 2 :=
        setIntegral_le_integral hGi' (Eventually.of_forall fun x => by positivity)
    _ = _ := by
        rw [integral_div, integral_const_mul, hGint]
        have e : (2 * ℓ)⁻¹ ^ (1 - (2 - α)) = (2 * ℓ)⁻¹ ^ (α - 1) := by congr 1; ring
        rw [e]

end pieces

section main

variable {α : ℝ} {g : ℝ → ℂ} {Cg : ℝ}

lemma OscData.integrable (hα0 : 0 < α) (hd : OscData α g Cg) : Integrable g := by
  have hCg := hd.Cg_nonneg
  refine (integrable_weight_sq.const_mul ((‖g 0‖ + Cg) * (9 / 4) + Cg)).mono' hd.cont.aestronglyMeasurable
    (Eventually.of_forall fun τ => ?_)
  have hw : 0 < (1 + |τ|) ^ (-(2 : ℝ)) := by positivity
  have hB := hd.norm_le hα0 τ
  by_cases hτ : |τ| < 1 / 2
  · have h1 : (4 / 9 : ℝ) ≤ (1 + |τ|) ^ (-(2 : ℝ)) := by
      have : (3 / 2 : ℝ) ^ (-(2 : ℝ)) ≤ (1 + |τ|) ^ (-(2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
      have e : (3 / 2 : ℝ) ^ (-(2 : ℝ)) = 4 / 9 := by
        rw [Real.rpow_neg (by norm_num)]; norm_num
      rwa [e] at this
    have h0 : 0 ≤ ‖g 0‖ + Cg := by positivity
    nlinarith [norm_nonneg (g τ)]
  · have hτ2 : 1 / 2 ≤ |τ| := not_lt.mp hτ
    have hg := (hd.far τ hτ2).1
    have : (1 + |τ|) ^ (-(5 / 2 : ℝ)) ≤ (1 + |τ|) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg τ]) (by norm_num)
    have h0 : 0 ≤ ‖g 0‖ + Cg := by positivity
    nlinarith [mul_nonneg h0 hw.le]

lemma half_rpow_le {T : ℝ} (hT : 1 ≤ T) : (1 + T / 2) ^ (-(1 / 2 : ℝ)) ≤ 2 * T ^ (-(1 / 2 : ℝ)) := by
  have hT0 : 0 < T := by linarith
  have h1 : (1 + T / 2) ^ (-(1 / 2 : ℝ)) ≤ (T / 2) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  rw [Real.div_rpow hT0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at h1
  have h2 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
    calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  calc (1 + T / 2) ^ (-(1 / 2 : ℝ)) ≤ T ^ (-(1 / 2 : ℝ)) / ((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := h1
    _ = T ^ (-(1 / 2 : ℝ)) * (2 : ℝ) ^ (1 / 2 : ℝ) := by rw [div_inv_eq_mul]
    _ ≤ T ^ (-(1 / 2 : ℝ)) * 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 * T ^ (-(1 / 2 : ℝ)) := mul_comm _ _

/-- **Oscillatory tail lemma.**  For a continuous amplitude `g`, `C²` off the origin, with
`|∂^j(g - g(0))| ≤ C_g |τ|^{α-j}` on `0 < |τ| ≤ 1` and `|∂^j g| ≤ C_g (1+|τ|)^{-5/2}` on `|τ| ≥ 1/2` (`j ≤ 2`), `0 < α < 1`,
there is `K` (depending only on `α` and `g`) such that, for every phase `ψ ∈ C³` with `λ ≤ ψ'`, `|ψ''| ≤ λ`, `|ψ'''| ≤ 2λ` on `[-T, T]`
(`T ≥ 1`) and every `ℓ ≥ 4`: `|∫ g e^{iψ}| ≤ K (T^{-1/2} + ℓ^{-1-α} + ℓ^{1-α}/λ²)`. -/
theorem osc_tail (hα0 : 0 < α) (hα1 : α < 1) (hd : OscData α g Cg) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ψ : ℝ → ℝ} {T lam ℓ : ℝ}, ContDiff ℝ 3 ψ → 1 ≤ T → 4 ≤ ℓ → 0 < lam →
      (∀ τ : ℝ, |τ| ≤ T → lam ≤ deriv ψ τ) → (∀ τ : ℝ, |τ| ≤ T → |deriv (deriv ψ) τ| ≤ lam) →
      (∀ τ : ℝ, |τ| ≤ T → |deriv (deriv (deriv ψ)) τ| ≤ 2 * lam) →
      ‖∫ τ : ℝ, g τ * Complex.exp (Complex.I * (ψ τ : ℂ))‖ ≤
        K * (T ^ (-(1 / 2 : ℝ)) + ℓ ^ (-(1 + α)) + ℓ ^ (1 - α) / lam ^ 2) := by
  obtain ⟨χ, hχ, hχ01, hχ1, hχ0, D, hD0, hD⟩ := exists_cutoff
  have hCg := hd.Cg_nonneg
  set Cfb : ℝ := (((4 * D + 5) * (‖g 0‖ + Cg) + (8 * D + 13) * Cg) + (6 * D + 9) * Cg) with hCfb
  have hCfb0 : 0 ≤ Cfb := by positivity
  set C'' : ℝ := Cfb * 2 ^ (2 - α) + 5 * ‖g 0‖ with hC''
  have hC''0 : 0 ≤ C'' := by positivity
  set I2 : ℝ := ∫ x : ℝ, (1 + |x|) ^ (-(2 : ℝ)) with hI2
  set Ip : ℝ := ∫ x : ℝ, (1 + |x|) ^ (-(2 - α)) with hIp
  have hI2 : 0 ≤ I2 := integral_nonneg fun x => by positivity
  have hIp : 0 ≤ Ip := integral_nonneg fun x => by positivity
  refine ⟨Cg * 2 * I2 + 2 * Cg + 2 * C'' * Ip, by positivity, ?_⟩
  intro ψ T lam ℓ hψ hT hℓ hlam hp1 hp2 hp3
  have hT0 : 0 < T := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hs0 : 0 < T⁻¹ := inv_pos.mpr hT0
  have hs1 : T⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hT
  have ha := oscAmp_contDiff hχ hχ1 hd.c2 hs0 hs1 (by linarith : (1 : ℝ) ≤ ℓ)
  have hχc : Continuous χ := hχ.continuous
  have hψc : Continuous ψ := hψ.continuous
  have hE : Continuous fun τ : ℝ => Complex.exp (Complex.I * (ψ τ : ℂ)) := by fun_prop
  -- the three pieces
  set P1 : ℝ → ℂ := fun τ => ((1 - χ (T⁻¹ * τ)) • g τ) * Complex.exp (Complex.I * (ψ τ : ℂ)) with hP1
  set P2 : ℝ → ℂ := fun τ => oscAmp χ g T⁻¹ ℓ τ * Complex.exp (Complex.I * (ψ τ : ℂ)) with hP2
  set P3 : ℝ → ℂ := fun τ => (χ (ℓ * τ) • (g τ - g 0)) * Complex.exp (Complex.I * (ψ τ : ℂ)) with hP3
  have hsum : ∀ τ : ℝ, g τ * Complex.exp (Complex.I * (ψ τ : ℂ)) = P1 τ + P2 τ + P3 τ := by
    intro τ
    simp only [hP1, hP2, hP3, oscAmp]
    have : g τ = (1 - χ (T⁻¹ * τ)) • g τ + (χ (T⁻¹ * τ) • g τ - χ (ℓ * τ) • (g τ - g 0)) +
        χ (ℓ * τ) • (g τ - g 0) := by module
    conv_lhs => rw [this]
    ring
  have hi1 : Integrable P1 := by
    refine (hd.integrable hα0).norm.mono' ?_ (Eventually.of_forall fun τ => ?_)
    · exact ((continuous_const.sub (hχc.comp (continuous_const.mul continuous_id))).smul hd.cont |>.mul hE).aestronglyMeasurable
    · simp only [hP1]
      rw [norm_mul, norm_cexp_I_mul_aux, mul_one, norm_smul, Real.norm_eq_abs]
      have := hχ01 (T⁻¹ * τ)
      have h1' : |1 - χ (T⁻¹ * τ)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      exact mul_le_of_le_one_left (norm_nonneg _) h1'
  have hsupp2 : ∀ τ : ℝ, τ ∉ Icc (-T) T → P2 τ = 0 := by
    intro τ hτ
    have hxT : T < |τ| := by
      by_contra hcon
      exact hτ (abs_le.mp (not_lt.mp hcon))
    simp only [hP2]
    rw [oscAmp_eq_zero (fun y hy => (hχ0 y hy).1) hs0 hℓ0 (by rw [← div_eq_inv_mul, le_div_iff₀ hT0]; linarith)
      (by nlinarith)]
    simp
  have hc2 : Continuous P2 := (ha.continuous).mul hE
  have hi2 : Integrable P2 :=
    (hc2.continuousOn.integrableOn_Icc).integrable_of_forall_notMem_eq_zero hsupp2
  have hsupp3 : ∀ τ : ℝ, τ ∉ Icc (-(1 / ℓ)) (1 / ℓ) → P3 τ = 0 := by
    intro τ hτ
    have : 1 ≤ |ℓ * τ| := by
      rw [abs_mul, abs_of_pos hℓ0]
      have h2 : 1 / ℓ < |τ| := by
        by_contra hcon
        exact hτ (abs_le.mp (not_lt.mp hcon))
      have := mul_lt_mul_of_pos_left h2 hℓ0
      rw [mul_one_div_cancel hℓ0.ne'] at this
      exact this.le
    simp only [hP3]; rw [(hχ0 _ this).1]; simp
  have hc3 : Continuous P3 :=
    ((hχc.comp (continuous_const.mul continuous_id)).smul (hd.cont.sub continuous_const)).mul hE
  have hi3 : Integrable P3 :=
    (hc3.continuousOn.integrableOn_Icc).integrable_of_forall_notMem_eq_zero hsupp3
  have hsplit : ∫ τ : ℝ, g τ * Complex.exp (Complex.I * (ψ τ : ℂ)) = (∫ τ, P1 τ) + (∫ τ, P2 τ) + ∫ τ, P3 τ := by
    simp_rw [hsum]
    have h12 := integral_add hi1 hi2
    have h123 := integral_add (hi1.add hi2) hi3
    simp only [Pi.add_apply] at h12 h123
    rw [h123, h12]
  rw [hsplit]
  have b1 := osc_out_bound hd hχ01 hχ1 hT ψ
  have b2 := osc_ibp_bound hα0 hα1 hd hχ hχ01 hχ1 hχ0 hD hψ hT hℓ hlam hp1 hp2 hp3
  have b3 := osc_direct_bound hα0 hd hχ01 (fun x hx => (hχ0 x hx).1) hℓ ψ
  -- collect
  have c1 : Cg * (1 + T / 2) ^ (-(1 / 2 : ℝ)) * I2 ≤ (Cg * 2 * I2) * T ^ (-(1 / 2 : ℝ)) := by
    have := half_rpow_le hT
    calc Cg * (1 + T / 2) ^ (-(1 / 2 : ℝ)) * I2 ≤ Cg * (2 * T ^ (-(1 / 2 : ℝ))) * I2 := by gcongr
      _ = _ := by ring
  have c3 : Cg * (1 / ℓ) ^ α * (2 / ℓ) = 2 * Cg * ℓ ^ (-(1 + α)) := by
    rw [one_div, Real.inv_rpow hℓ0.le, ← Real.rpow_neg hℓ0.le, show -(1 + α) = -α + -1 by ring,
      Real.rpow_add hℓ0, Real.rpow_neg_one]
    field_simp
  have c2 : ((Cfb * 2 ^ (2 - α) + 5 * ‖g 0‖ * ℓ ^ (α - 2)) * ((2 * ℓ)⁻¹ ^ (α - 1) * Ip)) / lam ^ 2 ≤
      (2 * C'' * Ip) * (ℓ ^ (1 - α) / lam ^ 2) := by
    have hq : (2 * ℓ)⁻¹ ^ (α - 1) ≤ 2 * ℓ ^ (1 - α) := by
      rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), show -(α - 1) = 1 - α by ring,
        Real.mul_rpow (by norm_num) hℓ0.le]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      calc (2 : ℝ) ^ (1 - α) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have hl : ℓ ^ (α - 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have hC : Cfb * 2 ^ (2 - α) + 5 * ‖g 0‖ * ℓ ^ (α - 2) ≤ C'' := by
      rw [hC'']
      have : 5 * ‖g 0‖ * ℓ ^ (α - 2) ≤ 5 * ‖g 0‖ * 1 :=
        mul_le_mul_of_nonneg_left hl (by positivity)
      linarith
    have hpos : 0 ≤ Cfb * 2 ^ (2 - α) + 5 * ‖g 0‖ * ℓ ^ (α - 2) := by positivity
    calc _ = (Cfb * 2 ^ (2 - α) + 5 * ‖g 0‖ * ℓ ^ (α - 2)) * ((2 * ℓ)⁻¹ ^ (α - 1) * Ip) / lam ^ 2 := rfl
      _ ≤ C'' * ((2 * ℓ ^ (1 - α)) * Ip) / lam ^ 2 := by
          gcongr
      _ = _ := by ring
  have hTT : 0 ≤ T ^ (-(1 / 2 : ℝ)) := by positivity
  have hℓℓ : 0 ≤ ℓ ^ (-(1 + α)) := by positivity
  have hℓl : 0 ≤ ℓ ^ (1 - α) / lam ^ 2 := by positivity
  calc _ ≤ ‖∫ τ, P1 τ‖ + ‖∫ τ, P2 τ‖ + ‖∫ τ, P3 τ‖ := by
        refine (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _ |>.trans ?_)
        linarith [norm_add_le (∫ τ, P1 τ + ∫ τ, P2 τ) (∫ τ, P3 τ), norm_add_le (∫ τ, P1 τ) (∫ τ, P2 τ)]
    _ ≤ (Cg * 2 * I2) * T ^ (-(1 / 2 : ℝ)) + (2 * C'' * Ip) * (ℓ ^ (1 - α) / lam ^ 2) + 2 * Cg * ℓ ^ (-(1 + α)) := by
        have := b1.trans c1
        have := b3.trans_eq c3
        linarith
    _ ≤ _ := by
        have e1 : 0 ≤ Cg * 2 * I2 := by positivity
        have e2 : 0 ≤ 2 * C'' * Ip := by positivity
        nlinarith [mul_nonneg e1 hTT, mul_nonneg e2 hℓl, mul_nonneg hCg hℓℓ]

end main

/-- info: 'FormalResearch.SignUncertainty.osc_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms osc_tail

end FormalResearch.SignUncertainty
