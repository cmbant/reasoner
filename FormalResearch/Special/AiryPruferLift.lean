module

public import FormalResearch.Special.SturmAiryZeros

/-!
# The Prüfer angle of a real solution of `y'' = q y`

For a nontrivial real solution `(y, y')` of `y'' = q y` (`q` continuous), the point `(y', y)` of the
plane never vanishes, so it has a polar form `(y', y) = r (cos θ, sin θ)` with a continuously
differentiable **Prüfer angle** `θ` (`cot θ = y'/y`).  It satisfies

`θ' = cos² θ - q sin² θ`,

(`q x = x`: `θ' = cos² θ - x sin² θ`, the Airy Prüfer equation).

* `IsPruferLift q y y' θ`: `θ` is such a lift (a positive `r` with `y = r sin θ`, `y' = r cos θ`, and the
  Prüfer equation everywhere).
* `IsSol.exists_isPruferLift`: **existence of a `C¹` lift on all of `ℝ`**, normalised at any chosen
  point `t₀` to `θ t₀ = arg (y' t₀ + i y t₀) ∈ (-π, π]`.  Proof: with `w = y' + i y ≠ 0` one has
  `w' = a w` for the continuous `a = w'/w`; hence `w = w(t₀) exp ∫_{t₀}^x a`, and `θ = arg w(t₀) +
  Im ∫ a`, `r = |w(t₀)| exp Re ∫ a`; `Im a = cos² θ - q sin² θ`.  No Picard-Lindelöf is needed.
* `IsPruferLift.zero_iff`: `y x = 0 ↔ sin (θ x) = 0`; at a zero, `θ' = 1`
  (`IsPruferLift.hasDerivAt_eq_one_of_zero`).
* `IsPruferLift.contDiff_one`: `θ` is `C¹` (its derivative is continuous).

Uniqueness of the lift up to an additive `2πℤ` is in `SturmAiryPruferUnique`.  Not formalised: the
complex (Herglotz) form of the log-derivative.
-/

@[expose] public section

open Set Filter Topology

namespace FormalResearch.Special.SturmAiry

variable {q y y' : ℝ → ℝ}

/-- `θ` is a **Prüfer angle** of the solution `(y, y')` of `y'' = q y`:
`(y', y) = r (cos θ, sin θ)` with `r > 0`, and `θ` solves `θ' = cos² θ - q sin² θ` everywhere. -/
structure IsPruferLift (q y y' θ : ℝ → ℝ) : Prop where
  exists_r : ∃ r : ℝ → ℝ, (∀ x, 0 < r x) ∧ (∀ x, y x = r x * Real.sin (θ x)) ∧
    ∀ x, y' x = r x * Real.cos (θ x)
  hasDerivAt : ∀ x, HasDerivAt θ (Real.cos (θ x) ^ 2 - q x * Real.sin (θ x) ^ 2) x

namespace IsPruferLift

variable {θ : ℝ → ℝ}

theorem zero_iff (hθ : IsPruferLift q y y' θ) (x : ℝ) : y x = 0 ↔ Real.sin (θ x) = 0 := by
  obtain ⟨r, hr, hy, -⟩ := hθ.exists_r
  rw [hy x]
  exact ⟨fun h => (mul_eq_zero.1 h).resolve_left (hr x).ne', fun h => by rw [h, mul_zero]⟩

theorem zero_iff_exists_int (hθ : IsPruferLift q y y' θ) (x : ℝ) :
    y x = 0 ↔ ∃ k : ℤ, θ x = k * Real.pi := by
  rw [hθ.zero_iff, Real.sin_eq_zero_iff]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

/-- At a zero of `y`, the Prüfer angle has derivative `1`: zeros are crossed upward. -/
theorem hasDerivAt_eq_one_of_zero (hθ : IsPruferLift q y y' θ) {x : ℝ} (hx : y x = 0) :
    HasDerivAt θ 1 x := by
  have h := hθ.hasDerivAt x
  have hs := (hθ.zero_iff x).1 hx
  have : Real.cos (θ x) ^ 2 - q x * Real.sin (θ x) ^ 2 = 1 := by
    rw [hs]; nlinarith [Real.sin_sq_add_cos_sq (θ x), hs]
  rwa [this] at h

theorem continuous (hθ : IsPruferLift q y y' θ) : Continuous θ :=
  continuous_iff_continuousAt.2 fun x => (hθ.hasDerivAt x).continuousAt

/-- `θ` is `C¹`: its derivative `cos² θ - q sin² θ` is continuous when `q` is. -/
theorem contDiff_one (hq : Continuous q) (hθ : IsPruferLift q y y' θ) : ContDiff ℝ 1 θ := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (hθ.hasDerivAt x).differentiableAt, ?_⟩
  have : deriv θ = fun x => Real.cos (θ x) ^ 2 - q x * Real.sin (θ x) ^ 2 :=
    funext fun x => (hθ.hasDerivAt x).deriv
  rw [this]
  have := hθ.continuous
  fun_prop

end IsPruferLift

namespace IsSol

/-- **Existence of the Prüfer angle.**  A nontrivial real solution of `y'' = q y` (`q` continuous)
has a `C¹` Prüfer angle `θ : ℝ → ℝ`, `y = r sin θ`, `y' = r cos θ`, `θ' = cos² θ - q sin² θ`,
and `θ` may be normalised at any `t₀` by `θ t₀ = arg (y' t₀ + i y t₀)`. -/
theorem exists_isPruferLift (hq : Continuous q) (h : IsSol q y y') (hy : ∃ x, y x ≠ 0) (t₀ : ℝ) :
    ∃ θ : ℝ → ℝ, IsPruferLift q y y' θ ∧
      θ t₀ = Complex.arg ((y' t₀ : ℂ) + (y t₀ : ℂ) * Complex.I) := by
  have hyc := h.continuous
  have hyc' := h.continuous'
  set w : ℝ → ℂ := fun x => (y' x : ℂ) + (y x : ℂ) * Complex.I with hwdef
  have hw : ∀ x, HasDerivAt w (((q x * y x : ℝ) : ℂ) + (y' x : ℂ) * Complex.I) x := fun x =>
    ((h.hasDerivAt' x).ofReal_comp).add (((h.hasDerivAt x).ofReal_comp).mul_const Complex.I)
  have hw0 : ∀ x, w x ≠ 0 := by
    intro x hx
    have h1 : y' x = 0 := by simpa [hwdef] using congrArg Complex.re hx
    have h2 : y x = 0 := by simpa [hwdef] using congrArg Complex.im hx
    exact (h.data_ne_zero hq hy x).elim (fun h3 => h3 h2) (fun h3 => h3 h1)
  set a : ℝ → ℂ := fun x => (((q x * y x : ℝ) : ℂ) + (y' x : ℂ) * Complex.I) / w x with hadef
  have hwc : Continuous w := by simp only [hwdef]; fun_prop
  have hac : Continuous a := by
    refine Continuous.div ?_ hwc hw0
    fun_prop
  set L : ℝ → ℂ := fun x => ∫ t in t₀..x, a t with hLdef
  have hL : ∀ x, HasDerivAt L (a x) x := fun x =>
    (intervalIntegral.integral_hasStrictDerivAt_right (hac.intervalIntegrable t₀ x)
      (hac.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 x)) hac.continuousAt).hasDerivAt
  have hL0 : L t₀ = 0 := by simp [hLdef]
  -- `w * exp (-L)` is constant
  have hG : ∀ x, HasDerivAt (fun x => w x * Complex.exp (-L x)) 0 x := by
    intro x
    have := (hw x).mul (hL x).neg.cexp
    refine this.congr_deriv ?_
    have : (((q x * y x : ℝ) : ℂ) + (y' x : ℂ) * Complex.I) = a x * w x := by
      simp only [hadef]; field_simp [hw0 x]
    rw [this]
    ring
  have hconst : ∀ x, w x * Complex.exp (-L x) = w t₀ := by
    intro x
    have := is_const_of_deriv_eq_zero (fun x => (hG x).differentiableAt)
      (fun x => (hG x).deriv) x t₀
    simpa [hL0] using this
  have hwx : ∀ x, w x = w t₀ * Complex.exp (L x) := by
    intro x
    rw [← hconst x, mul_assoc, ← Complex.exp_add]
    simp
  -- polar data
  set θ₀ := Complex.arg (w t₀) with hθ₀
  set r₀ := ‖w t₀‖ with hr₀
  have hr₀pos : 0 < r₀ := norm_pos_iff.2 (hw0 t₀)
  have hpolar : w t₀ = r₀ * Complex.exp (θ₀ * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I (w t₀)).symm
  set θ : ℝ → ℝ := fun x => θ₀ + (L x).im with hθdef
  set r : ℝ → ℝ := fun x => r₀ * Real.exp (L x).re with hrdef
  have hrpos : ∀ x, 0 < r x := fun x => mul_pos hr₀pos (Real.exp_pos _)
  have hwpolar : ∀ x, w x = (r x : ℂ) * Complex.exp ((θ x : ℝ) * Complex.I) := by
    intro x
    have hLx : L x = ((L x).re : ℂ) + ((L x).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
    rw [hwx x, hpolar]
    simp only [hθdef, hrdef]
    conv_lhs => rw [hLx]
    rw [Complex.exp_add]
    push_cast
    rw [add_mul, Complex.exp_add, ← Complex.ofReal_exp]
    ring
  have hy'x : ∀ x, y' x = r x * Real.cos (θ x) := by
    intro x
    have := congrArg Complex.re (hwpolar x)
    simpa [hwdef, Complex.exp_ofReal_mul_I_re] using this
  have hyx : ∀ x, y x = r x * Real.sin (θ x) := by
    intro x
    have := congrArg Complex.im (hwpolar x)
    simpa [hwdef, Complex.exp_ofReal_mul_I_im] using this
  have hθ' : ∀ x, HasDerivAt θ (Real.cos (θ x) ^ 2 - q x * Real.sin (θ x) ^ 2) x := by
    intro x
    have h1 : HasDerivAt (fun x => (L x).im) (a x).im x :=
      (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hL x))
    have h2 := h1.const_add θ₀
    refine h2.congr_deriv ?_
    -- Im a = (y'² - q y²) / (y'² + y²)
    have hr := (hrpos x).ne'
    have key : (a x).im = (y' x ^ 2 - q x * y x ^ 2) / (y' x ^ 2 + y x ^ 2) := by
      simp only [hadef, hwdef]
      rw [Complex.div_im]
      simp [Complex.normSq_apply]
      field_simp
    rw [key, hy'x x, hyx x]
    have hsc := Real.sin_sq_add_cos_sq (θ x)
    have : (r x * Real.cos (θ x)) ^ 2 + (r x * Real.sin (θ x)) ^ 2 = r x ^ 2 := by
      nlinarith [hsc]
    rw [this]
    field_simp
  refine ⟨θ, ⟨⟨r, hrpos, hyx, hy'x⟩, hθ'⟩, ?_⟩
  simp [hθdef, hL0, hθ₀, hwdef]

end IsSol

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.exists_isPruferLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.exists_isPruferLift

/-- info: 'FormalResearch.Special.SturmAiry.IsPruferLift.hasDerivAt_eq_one_of_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsPruferLift.hasDerivAt_eq_one_of_zero

/-- info: 'FormalResearch.Special.SturmAiry.IsPruferLift.contDiff_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsPruferLift.contDiff_one

end FormalResearch.Special.SturmAiry
