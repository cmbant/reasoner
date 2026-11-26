module

public import Mathlib
public import FormalResearch.SignUncertainty.HankelHhat
public import FormalResearch.CohnElkies.MellinKernelHolomorphic
public import FormalResearch.SignUncertainty.HankelStripData
public import FormalResearch.SignUncertainty.CtBoasShift
public import FormalResearch.SignUncertainty.CtBoasStrip

/-!
# `ct:boas` Step 4: holomorphy and boundedness of `ĥ` on the strip, in the `Fh` convention

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:boas` Step 4 and `ct:hhat-strip`.
With `h = hankelHL c f` (the log-density of `dm` in `L = log π²ξ`), `Fh h z = ∫ h(s) e^{2πizs} ds` and
`ĥ(ζ) = hankelHhat c f ζ = ∫ e^{-cζL} h(L) dL` one has `Fh h z = ĥ(-2πi z / c)`.  Put
`hankelHcoord c f z := ĥ(-2πi z/c)`.  Then `Im z = cσ/(2π)` for `ζ = σ + iτ`, and, for `c > 3/2`,
`f ∈ 𝒜_c^ε`:

* `fh_hankelHL_eq`: `Fh h x = hankelHcoord c f x` for real `x`;
* `hankelHhat_continuousOn_strip`, `hankelHhat_differentiableOn_strip`: `ĥ` is continuous on
  `0 ≤ Re ζ ≤ 1/4` and holomorphic inside (from `hankelHhat_formula` and the holomorphy of its factors);
* `hankelHcoord_bound`: `‖H(z)‖ ≤ 3 M[f] e^{c π²/1280}` on `0 ≤ Im z ≤ c/(8π)`.

**Proved**, unconditional (`c > 3/2`, `ε = ±1`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Asymptotics

/-- `H(z) = ĥ(-2πi z/c)`: the paper's `ĥ` in the `Fh` coordinate (`Im z = c Re ζ/(2π)`). -/
noncomputable def hankelHcoord (c : ℝ) (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  hankelHhat c f (-(2 * (π : ℂ) * Complex.I * z) / (c : ℂ))

/-- `Fh (hankelHL c f) z = ĥ(-2πi z/c)`. -/
theorem fh_hankelHL_eq {c : ℝ} (hc : c ≠ 0) (f : ℝ → ℝ) (z : ℂ) :
    FormalResearch.SignUncertainty.CtBoasWindow.Fh (hankelHL c f) z = hankelHcoord c f z := by
  unfold FormalResearch.SignUncertainty.CtBoasWindow.Fh hankelHcoord hankelHhat
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have : -((c : ℂ) * (-(2 * (π : ℂ) * Complex.I * z) / (c : ℂ)) * (s : ℂ)) =
      2 * π * Complex.I * z * s := by field_simp
  show (hankelHL c f s : ℂ) * Complex.exp (2 * π * Complex.I * z * s) =
    Complex.exp (-((c : ℂ) * (-(2 * (π : ℂ) * Complex.I * z) / (c : ℂ)) * (s : ℂ))) * (hankelHL c f s : ℂ)
  rw [this, mul_comm]

/-- The log-density `h = hankelHL c f` is integrable on `ℝ` (substitution `ξ = e^L/π²` from `hf.int`). -/
theorem integrable_hankelHL {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    Integrable (hankelHL c f) := by
  have hpi : (0 : ℝ) < π ^ 2 := by positivity
  set φ : ℝ → ℝ := fun L => Real.exp L / π ^ 2 with hφ
  have himg : φ '' univ = Ioi 0 := by
    ext ξ
    simp only [mem_image, mem_univ, true_and, mem_Ioi, hφ]
    constructor
    · rintro ⟨L, rfl⟩; positivity
    · intro hξ
      refine ⟨Real.log (π ^ 2 * ξ), ?_⟩
      rw [Real.exp_log (by positivity)]; field_simp
  have hd : ∀ L ∈ (univ : Set ℝ), HasDerivWithinAt φ (Real.exp L / π ^ 2) univ L :=
    fun L _ => ((Real.hasDerivAt_exp L).div_const _).hasDerivWithinAt
  have hinj : InjOn φ univ := by
    intro a _ b _ hab
    simp only [hφ] at hab
    exact Real.exp_injective ((div_left_inj₀ hpi.ne').1 hab)
  have h1 : IntegrableOn (fun ξ : ℝ => f (c * ξ) * hankelRho0 c (c * ξ)) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff (fun Δ => f Δ * hankelRho0 c Δ) 0 hc).2
      (by simpa using hf.int)
    exact this
  have h2 : IntegrableOn (fun ξ : ℝ => c * (f (c * ξ) * hankelRho0 c (c * ξ))) (Ioi 0) := h1.const_mul c
  rw [← himg] at h2
  have h3 := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd hinj _).1 h2
  rw [integrableOn_univ] at h3
  refine h3.congr (ae_of_all _ fun L => ?_)
  have hp : 0 ≤ Real.exp L / π ^ 2 := by positivity
  simp only [hankelHL, hφ, smul_eq_mul, abs_of_nonneg hp]
  ring


/-- `ĥ` is continuous on `0 ≤ Re ζ ≤ 1/4`. -/
theorem hankelHhat_continuousOn_strip {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    ContinuousOn (hankelHhat c f) {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1 / 4} := by
  have hc0 : 0 < c := by linarith
  have e : ∀ ζ ∈ {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1 / 4}, hankelHhat c f ζ =
      (1 - ζ) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c ζ) * Complex.exp ((c : ℂ) * stripS0Tilde ζ) *
        hankelWtS c ε f ζ := fun ζ hζ => hankelHhat_formula hc hf hζ.1 (by linarith [hζ.2])
  refine ContinuousOn.congr ?_ e
  have hA : ContinuousOn (fun ζ : ℂ => (1 - ζ) ^ (-(1 / 2 : ℂ))) {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1 / 4} := by
    refine ContinuousOn.cpow_const (by fun_prop) (fun ζ hζ => ?_)
    left; simp; linarith [hζ.2]
  have hB : ContinuousOn (fun ζ : ℂ => Complex.exp (binetDiff c ζ)) {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1 / 4} :=
    Complex.continuous_exp.comp_continuousOn
      ((binetDiff_differentiableOn hc0).continuousOn.mono fun ζ hζ => by
        show ζ.re < 1; linarith [hζ.2])
  have hS : ContinuousOn (fun ζ : ℂ => Complex.exp ((c : ℂ) * stripS0Tilde ζ)) {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1 / 4} :=
    Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (FormalResearch.CohnElkies.differentiableOn_stripS0Tilde.continuousOn.mono fun ζ hζ => by
        show |ζ.re| < 1; rw [abs_lt]; constructor <;> linarith [hζ.1, hζ.2]))
  have hW := (hankelWtS_continuousOn hc hf).mono
    (fun ζ (hζ : ζ ∈ {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1 / 4}) =>
      (⟨hζ.1, by linarith [hζ.2]⟩ : 0 ≤ ζ.re ∧ ζ.re ≤ 1))
  exact ((hA.mul hB).mul hS).mul hW

/-- `ĥ` is holomorphic on `0 < Re ζ < 1/4`. -/
theorem hankelHhat_differentiableOn_strip {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    DifferentiableOn ℂ (hankelHhat c f) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1 / 4} := by
  have hc0 : 0 < c := by linarith
  have e : ∀ ζ ∈ {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1 / 4}, hankelHhat c f ζ =
      (1 - ζ) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c ζ) * Complex.exp ((c : ℂ) * stripS0Tilde ζ) *
        hankelWtS c ε f ζ := fun ζ hζ => hankelHhat_formula hc hf hζ.1.le (by linarith [hζ.2])
  refine DifferentiableOn.congr ?_ e
  have hA : DifferentiableOn ℂ (fun ζ : ℂ => (1 - ζ) ^ (-(1 / 2 : ℂ))) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1 / 4} := by
    refine DifferentiableOn.cpow (by fun_prop) (differentiableOn_const _) (fun ζ hζ => ?_)
    left; simp; linarith [hζ.2]
  have hB : DifferentiableOn ℂ (fun ζ : ℂ => Complex.exp (binetDiff c ζ)) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1 / 4} :=
    DifferentiableOn.cexp ((binetDiff_differentiableOn hc0).mono fun ζ hζ => by
        show ζ.re < 1; linarith [hζ.2])
  have hS : DifferentiableOn ℂ (fun ζ : ℂ => Complex.exp ((c : ℂ) * stripS0Tilde ζ)) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1 / 4} :=
    DifferentiableOn.cexp ((differentiableOn_const _).mul (FormalResearch.CohnElkies.differentiableOn_stripS0Tilde.mono fun ζ hζ => by
        show |ζ.re| < 1; rw [abs_lt]; constructor <;> linarith [hζ.1, hζ.2]))
  have hW := (hankelWtS_differentiableOn hc hf).mono
    (fun ζ (hζ : ζ ∈ {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1 / 4}) =>
      (⟨hζ.1, by linarith [hζ.2]⟩ : 0 < ζ.re ∧ ζ.re < 1))
  exact ((hA.mul hB).mul hS).mul hW

/-- `Re S̃₀(σ + iτ) ≤ π²σ³/20` for `0 ≤ σ ≤ 1/4` and all real `τ` (from `re_stripS0Tilde_le_aux` and, at
`τ = 0`, continuity in `τ`). -/
theorem re_stripS0Tilde_le_cubic {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1 / 4) (τ : ℝ) :
    (stripS0Tilde ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤ π ^ 2 * σ ^ 3 / 20 := by
  have key : ∀ t : ℝ, t ≠ 0 → (stripS0Tilde ((σ : ℂ) + (t : ℂ) * Complex.I)).re ≤ π ^ 2 * σ ^ 3 / 20 := by
    intro t ht
    refine (re_stripS0Tilde_le_aux hσ0 hσ ht).trans ?_
    have h1 : 0 ≤ σ * hankelEdgeM |t| := mul_nonneg hσ0 (hankelEdgeM_nonneg (abs_nonneg _))
    have hc : 1 ≤ Real.cosh (π * t / 2) ^ 2 := by
      have := Real.one_le_cosh (π * t / 2); nlinarith
    have h2 : π ^ 2 * σ ^ 3 / (20 * Real.cosh (π * t / 2) ^ 2) ≤ π ^ 2 * σ ^ 3 / 20 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
      linarith
    nlinarith
  by_cases hτ : τ = 0
  · subst hτ
    have hcont : ContinuousAt (fun t : ℝ => (stripS0Tilde ((σ : ℂ) + (t : ℂ) * Complex.I)).re) 0 := by
      have hd : DifferentiableAt ℂ stripS0Tilde ((σ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) :=
        FormalResearch.CohnElkies.differentiableAt_stripS0Tilde (by
          simp; rw [abs_lt]; constructor <;> linarith)
      have hfc : ContinuousAt (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) 0 := by fun_prop
      exact Complex.continuous_re.continuousAt.comp (hd.continuousAt.comp_of_eq hfc (by simp))
    exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun t (ht : t ∈ ({0}ᶜ : Set ℝ)) => key t ht)
  · exact key τ hτ

/-- `Re S̃₀(σ + iτ) ≤ π²/1280` for `0 ≤ σ ≤ 1/4`. -/
theorem re_stripS0Tilde_le_const {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1 / 4) (τ : ℝ) :
    (stripS0Tilde ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤ π ^ 2 / 1280 := by
  refine (re_stripS0Tilde_le_cubic hσ0 hσ τ).trans ?_
  have : π ^ 2 * σ ^ 3 ≤ π ^ 2 * (1 / 4) ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hσ0 hσ 3) (by positivity)
  nlinarith

/-- Bound for `H = ĥ(-2πi ·/c)` on the strip `0 ≤ Im z ≤ c/(8π)`:
`‖H(z)‖ ≤ 3 M[f] e^{cπ²/1280}`. -/
theorem hankelHcoord_bound {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {z : ℂ} (h0 : 0 ≤ z.im) (h1 : z.im ≤ c / (8 * π)) :
    ‖hankelHcoord c f z‖ ≤ 3 * hankelMass c f * Real.exp (c * (π ^ 2 / 1280)) := by
  have hc0 : 0 < c := by linarith
  set ζ : ℂ := -(2 * (π : ℂ) * Complex.I * z) / (c : ℂ) with hζ
  have hre : ζ.re = 2 * π * z.im / c := by
    simp only [hζ]
    rw [Complex.div_ofReal_re]
    simp [Complex.mul_re, Complex.mul_im]
  have hσ0 : 0 ≤ ζ.re := by rw [hre]; positivity
  have hσ1 : ζ.re ≤ 1 / 4 := by
    rw [hre, div_le_iff₀ hc0]
    have : z.im * (8 * π) ≤ c := by rwa [le_div_iff₀ (by positivity)] at h1
    nlinarith [Real.pi_pos]
  have hζe : ζ = ((ζ.re : ℝ) : ℂ) + ((ζ.im : ℝ) : ℂ) * Complex.I := (Complex.re_add_im ζ).symm
  have hb := hankelHhat_bound hc hf hε hσ0 hσ1 ζ.im
  rw [← hζe] at hb
  refine hb.trans ?_
  have hM := hankelMass_nonneg hc0 f
  have := re_stripS0Tilde_le_const hσ0 hσ1 ζ.im
  rw [← hζe] at this
  gcongr

/-- `Re(-2πi z/c) = 2π Im z / c`. -/
lemma re_hankelZeta {c : ℝ} (z : ℂ) :
    (-(2 * (π : ℂ) * Complex.I * z) / (c : ℂ)).re = 2 * π * z.im / c := by
  rw [Complex.div_ofReal_re]
  simp [Complex.mul_re, Complex.mul_im]

/-- `H = ĥ(-2πi·/c)` is continuous on `0 ≤ Im z ≤ a` for `a ≤ c/(8π)`. -/
theorem hankelHcoord_continuousOn {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) {a : ℝ}
    (ha : a ≤ c / (8 * π)) : ContinuousOn (hankelHcoord c f) {z : ℂ | 0 ≤ z.im ∧ z.im ≤ a} := by
  have hc0 : 0 < c := by linarith
  refine (hankelHhat_continuousOn_strip hc hf).comp (by fun_prop) ?_
  intro z hz
  show 0 ≤ _ ∧ _ ≤ 1 / 4
  rw [re_hankelZeta]
  refine ⟨by have := hz.1; positivity, ?_⟩
  rw [div_le_iff₀ hc0]
  have : a * (8 * π) ≤ c := by rwa [le_div_iff₀ (by positivity)] at ha
  nlinarith [Real.pi_pos, hz.2]

/-- `H` is holomorphic on `0 < Im z < a` for `a ≤ c/(8π)`. -/
theorem hankelHcoord_differentiableOn {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) {a : ℝ}
    (ha : a ≤ c / (8 * π)) : DifferentiableOn ℂ (hankelHcoord c f) {z : ℂ | 0 < z.im ∧ z.im < a} := by
  have hc0 : 0 < c := by linarith
  refine (hankelHhat_differentiableOn_strip hc hf).comp (by fun_prop) ?_
  intro z hz
  show 0 < _ ∧ _ < 1 / 4
  rw [re_hankelZeta]
  refine ⟨by have := hz.1; positivity, ?_⟩
  rw [div_lt_iff₀ hc0]
  have : a * (8 * π) ≤ c := by rwa [le_div_iff₀ (by positivity)] at ha
  nlinarith [Real.pi_pos, hz.2]

/-- info: 'FormalResearch.SignUncertainty.integrable_hankelHL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integrable_hankelHL

/-- info: 'FormalResearch.SignUncertainty.hankelHcoord_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelHcoord_continuousOn

/-- info: 'FormalResearch.SignUncertainty.hankelHcoord_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelHcoord_differentiableOn

/-- info: 'FormalResearch.SignUncertainty.hankelHcoord_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelHcoord_bound

/-- info: 'FormalResearch.SignUncertainty.re_stripS0Tilde_le_cubic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms re_stripS0Tilde_le_cubic

end FormalResearch.SignUncertainty
