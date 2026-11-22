/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.LinearGlobal
public import DLMFMathlib.Analysis.ODE.ParamHolomorphic
public import DLMFMathlib.Analysis.ODE.SturmComparison
public import DLMFMathlib.Analysis.ODE.SturmDeformation

/-!
# Spectra of separated Sturm–Liouville problems with an even potential

Let `V : ℝ → ℝ` be continuous, bounded and even, and let `L > 0`. For boundary types
`odd0 oddK : Bool` consider the eigenvalue problem `w'' = (V - h) w` on `ℝ` with `w(0) = 0`
(if `odd0`) or `w'(0) = 0` (otherwise) and `w(L) = 0` (if `oddK`) or `w'(L) = 0` (otherwise).
Its spectrum `ODE.separatedSpectrum V L odd0 oddK` is the set of `h` with a nonzero solution.

## Main results

* `ODE.isSturmLiouvilleSolution_eq_mul_basicSolution`: every solution satisfying the condition at
  `0` is a multiple of the basic solution `basicSolution V odd0 h` (data `(0, 1)` or `(1, 0)` at
  `0`); hence the eigenvalues are simple and
  `h ∈ separatedSpectrum ↔ sturmCharacteristic V L odd0 oddK h = 0`
  (`ODE.mem_separatedSpectrum_iff`).
* `ODE.neg_le_of_mem_separatedSpectrum`: the spectrum lies in `[-B, ∞)` if `|V| ≤ B` (energy
  identity).
* `ODE.separatedSpectrum_inter_Iio_finite`: the spectrum meets every `(-∞, c)` in a finite set,
  because `sturmCharacteristic` is the restriction to `ℝ` of an entire function
  (`ODE.differentiable_param_of_linear_ode`) that does not vanish identically.
* `ODE.not_bddAbove_separatedSpectrum`: the spectrum is unbounded above. The zero count of the basic
  solution (or of its derivative) on `[-L, L]` is locally constant in `h` as long as `h` is not
  an eigenvalue (`ODE.SturmDeformation.ncard_eq_of_isPreconnected`, using joint continuity in
  `(h, x)` from an energy estimate), while it tends to infinity by Sturm comparison with
  `sin(ω(x + L))`.
-/

@[expose] public noncomputable section

open Set Filter Topology

namespace ODE

variable {V : ℝ → ℝ} {L B h : ℝ}

/-- `w` solves `w'' = (V - h) w` on `ℝ`. -/
def IsSturmLiouvilleSolution (V : ℝ → ℝ) (h : ℝ) (w : ℝ → ℝ) : Prop :=
  Differentiable ℝ w ∧ ∀ x, HasDerivAt (deriv w) ((V x - h) * w x) x

/-- The separated boundary conditions at `0` and `L`. -/
def SatisfiesSeparatedBC (L : ℝ) (odd0 oddK : Bool) (w : ℝ → ℝ) : Prop :=
  (if odd0 then w 0 = 0 else deriv w 0 = 0) ∧ (if oddK then w L = 0 else deriv w L = 0)

/-- The spectrum of the separated problem. -/
def separatedSpectrum (V : ℝ → ℝ) (L : ℝ) (odd0 oddK : Bool) : Set ℝ :=
  {h | ∃ w, IsSturmLiouvilleSolution V h w ∧ SatisfiesSeparatedBC L odd0 oddK w ∧ w ≠ 0}

/-- Initial value at `0` of the basic solution. -/
def basicInitValue (odd0 : Bool) : ℝ := if odd0 then 0 else 1

/-- Initial slope at `0` of the basic solution. -/
def basicInitSlope (odd0 : Bool) : ℝ := if odd0 then 1 else 0

/-- Identity under the stated parameter and domain assumptions:
`∃ f : ℝ → ℝ, f 0 = basicInitValue odd0 ∧ deriv f 0 = basicInitSlope odd0 ∧ IsSturmLiouvilleSolution
V h f`. -/
lemma exists_isSturmLiouvilleSolution_initial (hV : Continuous V) (h : ℝ) (odd0 : Bool) :
    ∃ f : ℝ → ℝ, f 0 = basicInitValue odd0 ∧ deriv f 0 = basicInitSlope odd0 ∧
        IsSturmLiouvilleSolution V h f := by
  obtain ⟨f, f', h0, h1, hf⟩ := exists_linear_ode (𝕜 := ℝ) (E := ℝ) (p := fun _ => 0)
    (q := fun x => V x - h) continuous_const (hV.sub continuous_const) 0 (basicInitValue odd0)
    (basicInitSlope odd0)
  have hd : deriv f = f' := funext fun t => (hf t).1.deriv
  refine ⟨f, h0, hd ▸ h1, fun t => (hf t).1.differentiableAt, fun t => ?_⟩
  rw [hd]; simpa using (hf t).2

/-- The basic solution: data `(basicInitValue, basicInitSlope)` at `0`. -/
def basicSolution (V : ℝ → ℝ) (odd0 : Bool) (h : ℝ) : ℝ → ℝ :=
  open Classical in
  if hV : Continuous V then (exists_isSturmLiouvilleSolution_initial hV h odd0).choose else 0

/-- Identity under the stated parameter and domain assumptions:
`basicSolution V odd0 h 0 = basicInitValue odd0 ∧ deriv (basicSolution V odd0 h) 0 = basicInitSlope
odd0 ∧ IsSturmLiouvilleSolution V h (basicSolution V odd0 h)`. -/
theorem basicSolution_initial_and_isSol (hV : Continuous V) (odd0 : Bool) (h : ℝ) :
    basicSolution V odd0 h 0 = basicInitValue odd0 ∧ deriv (basicSolution V odd0 h) 0 =
        basicInitSlope odd0 ∧
      IsSturmLiouvilleSolution V h (basicSolution V odd0 h) := by
  rw [basicSolution, dite_eq_left hV]
  exact (exists_isSturmLiouvilleSolution_initial hV h odd0).choose_spec

/-- At `x`, the function `w` has derivative `(deriv w x)`. -/
theorem IsSturmLiouvilleSolution.hasDerivAt {w : ℝ → ℝ}
    (hw : IsSturmLiouvilleSolution V h w) (x : ℝ) :
    HasDerivAt w (deriv w x) x := (hw.1 x).hasDerivAt

/-- The function `w` is continuous. -/
theorem IsSturmLiouvilleSolution.continuous {w : ℝ → ℝ} (hw : IsSturmLiouvilleSolution V h w) :
    Continuous w :=
  hw.1.continuous

/-- The function `(deriv w)` is continuous. -/
theorem IsSturmLiouvilleSolution.continuous_deriv {w : ℝ → ℝ}
    (hw : IsSturmLiouvilleSolution V h w) : Continuous (deriv w) :=
  continuous_iff_continuousAt.2 fun x => (hw.2 x).continuousAt

/-- Uniqueness for the equation. -/
theorem isSturmLiouvilleSolution_eq_of_eq_of_deriv_eq (hV : Continuous V) {w₁ w₂ : ℝ → ℝ}
    (h₁ : IsSturmLiouvilleSolution V h w₁)
    (h₂ : IsSturmLiouvilleSolution V h w₂) {x₀ : ℝ} (e₀ : w₁ x₀ = w₂ x₀)
        (e₁ : deriv w₁ x₀ = deriv w₂ x₀) :
    w₁ = w₂ := by
  have := eq_of_linear_ode (𝕜 := ℝ) (E := ℝ) (t₀ := x₀) (p := fun _ => 0)
    (q := fun x => V x - h) continuous_const (hV.sub continuous_const)
    (f := w₁) (f' := deriv w₁) (g := w₂) (g' := deriv w₂)
    (fun t => ⟨h₁.hasDerivAt t, (h₁.2 t).congr_deriv (by simp)⟩)
    (fun t => ⟨h₂.hasDerivAt t, (h₂.2 t).congr_deriv (by simp)⟩) e₀ e₁
  exact this.1

/-- Identity under the stated parameter and domain assumptions:
`IsSturmLiouvilleSolution V h (fun x => c * w x)`. -/
theorem IsSturmLiouvilleSolution.const_mul {w : ℝ → ℝ}
    (hw : IsSturmLiouvilleSolution V h w) (c : ℝ) :
    IsSturmLiouvilleSolution V h (fun x => c * w x) := by
  have hd : deriv (fun x => c * w x) = fun x => c * deriv w x :=
    funext fun x => ((hw.hasDerivAt x).const_mul c).deriv
  refine ⟨fun x => ((hw.hasDerivAt x).const_mul c).differentiableAt, fun x => ?_⟩
  rw [hd]
  exact ((hw.2 x).const_mul c).congr_deriv (by ring)

/-- A solution vanishing to first order at a point is zero. -/
theorem isSturmLiouvilleSolution_eq_zero_of_eq_zero_of_deriv_eq_zero (hV : Continuous V) {w : ℝ → ℝ}
    (hw : IsSturmLiouvilleSolution V h w) {x₀ : ℝ}
    (e₀ : w x₀ = 0) (e₁ : deriv w x₀ = 0) : w = 0 := by
  have h0 : IsSturmLiouvilleSolution V h (0 : ℝ → ℝ) := ⟨differentiable_const 0, fun x => by
    simp⟩
  exact isSturmLiouvilleSolution_eq_of_eq_of_deriv_eq hV hw h0 (x₀ := x₀)
      (by simp [e₀]) (by simp [e₁])

/-- Every solution satisfying the condition at `0` is a multiple of the basic solution. -/
theorem isSturmLiouvilleSolution_eq_mul_basicSolution (hV : Continuous V) {odd0 : Bool} {w : ℝ → ℝ}
    (hw : IsSturmLiouvilleSolution V h w)
    (h0 : if odd0 then w 0 = 0 else deriv w 0 = 0) :
    w = fun x => (if odd0 then deriv w 0 else w 0) * basicSolution V odd0 h x := by
  obtain ⟨y0, y1, hy⟩ := basicSolution_initial_and_isSol hV odd0 h
  have hc := hy.const_mul (if odd0 then deriv w 0 else w 0)
  have hd : deriv (fun x => (if odd0 then deriv w 0 else w 0) * basicSolution V odd0 h x) 0 =
      (if odd0 then deriv w 0 else w 0) * deriv (basicSolution V odd0 h) 0 :=
    ((hy.hasDerivAt 0).const_mul _).deriv
  refine isSturmLiouvilleSolution_eq_of_eq_of_deriv_eq hV hw hc (x₀ := 0) ?_ ?_
  · cases odd0 <;> simp_all [basicInitValue]
  · rw [hd]; cases odd0 <;> simp_all [basicInitSlope]

/-- Nonvanishing under the stated hypotheses: `basicSolution V odd0 h ≠ 0`. -/
theorem basicSolution_ne_zero (hV : Continuous V) (odd0 : Bool) (h : ℝ) : basicSolution V
    odd0 h ≠ 0 := by
  intro h0
  obtain ⟨y0, y1, -⟩ := basicSolution_initial_and_isSol hV odd0 h
  rw [h0] at y0 y1
  cases odd0 <;> simp_all [basicInitValue, basicInitSlope]

/-- The characteristic function: `basicSolution(L)` or `p2lY'(L)`. -/
def sturmCharacteristic (V : ℝ → ℝ) (L : ℝ) (odd0 oddK : Bool) (h : ℝ) : ℝ :=
  if oddK then basicSolution V odd0 h L else deriv (basicSolution V odd0 h) L

/-- `h` is an eigenvalue iff the characteristic function vanishes. -/
theorem mem_separatedSpectrum_iff (hV : Continuous V) (odd0 oddK : Bool) :
    h ∈ separatedSpectrum V L odd0 oddK ↔ sturmCharacteristic V L odd0 oddK h = 0 := by
  obtain ⟨y0, y1, hy⟩ := basicSolution_initial_and_isSol hV odd0 h
  constructor
  · rintro ⟨w, hw, ⟨b0, bL⟩, hne⟩
    have he := isSturmLiouvilleSolution_eq_mul_basicSolution hV hw b0
    set c := if odd0 then deriv w 0 else w 0
    have hc : c ≠ 0 := by
      intro hc0
      apply hne
      rw [he, hc0]; funext x; simp
    have hdL : deriv w L = c * deriv (basicSolution V odd0 h) L := by
      conv_lhs => rw [he]
      exact ((hy.hasDerivAt L).const_mul c).deriv
    unfold sturmCharacteristic
    cases oddK
    · simp only [Bool.false_eq_true, ↓reduceIte] at bL ⊢
      rw [hdL] at bL
      exact (mul_eq_zero.1 bL).resolve_left hc
    · simp only [↓reduceIte] at bL ⊢
      rw [he] at bL
      exact (mul_eq_zero.1 bL).resolve_left hc
  · intro hG
    refine ⟨basicSolution V odd0 h, hy, ⟨?_, ?_⟩, basicSolution_ne_zero hV odd0 h⟩
    · cases odd0 <;> simp_all [basicInitValue, basicInitSlope]
    · unfold sturmCharacteristic at hG; cases oddK <;> simp_all

/-! ### Lower bound of the spectrum -/

/-- If `|V| ≤ B`, every eigenvalue is at least `-B` (energy identity for `w w'`). -/
private lemma neg_le_of_mem_separatedSpectrum (hV : Continuous V) (hB : ∀ x, |V x| ≤ B) (hL : 0 < L)
    {odd0 oddK : Bool} (hh : h ∈ separatedSpectrum V L odd0 oddK) : -B ≤ h := by
  by_contra hlt
  push Not at hlt
  obtain ⟨w, hw, ⟨b0, bL⟩, hne⟩ := hh
  have hpos : ∀ x, 0 < V x - h := fun x => by
    have := neg_abs_le (V x); linarith [hB x]
  set φ : ℝ → ℝ := fun x => w x * deriv w x
  have hφ : ∀ x, HasDerivAt φ (deriv w x ^ 2 + (V x - h) * w x ^ 2) x := fun x =>
    ((hw.hasDerivAt x).mul (hw.2 x)).congr_deriv (by ring)
  have hmono : Monotone φ := monotone_of_deriv_nonneg (fun x => (hφ x).differentiableAt)
    fun x => by rw [(hφ x).deriv]; have := hpos x; positivity
  have hφ0 : φ 0 = 0 := by simp only [φ]; cases odd0 <;> simp_all
  have hφL : φ L = 0 := by simp only [φ]; cases oddK <;> simp_all
  have hzero : ∀ x ∈ Ioo 0 L, φ x = 0 := fun x hx =>
    le_antisymm (hφL ▸ hmono hx.2.le) (hφ0 ▸ hmono hx.1.le)
  have hm : L / 2 ∈ Ioo 0 L := ⟨by linarith, by linarith⟩
  have hev : φ =ᶠ[𝓝 (L / 2)] fun _ => 0 := by
    filter_upwards [Ioo_mem_nhds hm.1 hm.2] with x hx using hzero x hx
  have hd0 := (hφ (L / 2)).unique ((hasDerivAt_const (L / 2) (0 : ℝ)).congr_of_eventuallyEq hev)
  have hp := hpos (L / 2)
  have h1 : w (L / 2) = 0 := by
    by_contra hw0
    have : 0 < (V (L / 2) - h) * w (L / 2) ^ 2 := by positivity
    nlinarith [sq_nonneg (deriv w (L / 2))]
  have h2 : deriv w (L / 2) = 0 := by
    rw [h1] at hd0; simpa using hd0
  exact hne (isSturmLiouvilleSolution_eq_zero_of_eq_zero_of_deriv_eq_zero hV hw h1 h2)

/-! ### The complex family and discreteness of the spectrum -/

/-- Identity under the stated parameter and domain assumptions:
`∃ F F' : ℝ → ℂ, F 0 = (basicInitValue odd0 : ℂ) ∧ F' 0 = (basicInitSlope odd0 : ℂ) ∧ ∀ t,
HasDerivAt F (F' t) t ∧ HasDerivAt F' (((fun _ => (0 : ℂ)) t + μ * (fun _ => (0 : ℂ)) t) * F' t +
((V t : ℂ) + μ * (fun _ => (-1 : ℂ)) t) * F t) t`. -/
lemma exists_complex_param_solution (hV : Continuous V) (odd0 : Bool) (μ : ℂ) :
    ∃ F F' : ℝ → ℂ, F 0 = (basicInitValue odd0 : ℂ) ∧ F' 0 = (basicInitSlope odd0 : ℂ) ∧ ∀ t,
      HasDerivAt F (F' t) t ∧
      HasDerivAt F' (((fun _ => (0 : ℂ)) t + μ * (fun _ => (0 : ℂ)) t) * F' t +
        ((V t : ℂ) + μ * (fun _ => (-1 : ℂ)) t) * F t) t := by
  obtain ⟨f, f', h0, h1, hf⟩ := exists_linear_ode (𝕜 := ℂ) (E := ℂ) (p := fun _ => 0)
    (q := fun t => (V t : ℂ) + μ * (-1)) continuous_const
    ((Complex.continuous_ofReal.comp hV).add continuous_const) 0 (basicInitValue odd0 : ℂ)
    (basicInitSlope odd0 : ℂ)
  exact ⟨f, f', h0, h1, fun t => ⟨(hf t).1, (hf t).2.congr_deriv (by simp)⟩⟩

/-- The complexified basic solution, as a function of `t` and the parameter `μ`. -/
def basicSolutionComplex (V : ℝ → ℝ) (odd0 : Bool) (t : ℝ) (μ : ℂ) : ℂ :=
  open Classical in
  if hV : Continuous V then (exists_complex_param_solution hV odd0 μ).choose t else 0

/-- The derivative of the complexified basic solution. -/
def basicSolutionComplexDeriv (V : ℝ → ℝ) (odd0 : Bool) (t : ℝ) (μ : ℂ) : ℂ :=
  open Classical in
  if hV : Continuous V then (exists_complex_param_solution hV odd0 μ).choose_spec.choose t else 0

/-- Identity under the stated parameter and domain assumptions:
`basicSolutionComplex V odd0 0 μ = (basicInitValue odd0 : ℂ) ∧ basicSolutionComplexDeriv V odd0 0 μ
= (basicInitSlope odd0 : ℂ) ∧ ∀ t, HasDerivAt (fun t => basicSolutionComplex V odd0 t μ)
(basicSolutionComplexDeriv V odd0 t μ) t ∧ HasDerivAt (fun t => basicSolutionComplexDeriv V odd0 t
μ) (((fun _ => (0 : ℂ)) t + μ * (fun _ => (0 : ℂ)) t) * basicSolutionComplexDeriv V odd0 t μ + ((V t
: ℂ) + μ * (fun _ => (-1 : ℂ)) t) * basicSolutionComplex V odd0 t μ) t`. -/
private lemma basicSolutionComplex_initial_and_hasDerivAt (hV : Continuous V)
    (odd0 : Bool) (μ : ℂ) :
    basicSolutionComplex V odd0 0 μ = (basicInitValue odd0 : ℂ) ∧
        basicSolutionComplexDeriv V odd0 0 μ = (basicInitSlope odd0 : ℂ) ∧ ∀ t,
      HasDerivAt (fun t => basicSolutionComplex V odd0 t μ)
          (basicSolutionComplexDeriv V odd0 t μ) t ∧
      HasDerivAt (fun t => basicSolutionComplexDeriv V odd0 t μ)
        (((fun _ => (0 : ℂ)) t + μ * (fun _ => (0 : ℂ)) t) * basicSolutionComplexDeriv V odd0 t μ +
          ((V t : ℂ) + μ * (fun _ => (-1 : ℂ)) t) * basicSolutionComplex V odd0 t μ) t := by
  simp only [basicSolutionComplex, basicSolutionComplexDeriv, dite_eq_left hV]
  exact (exists_complex_param_solution hV odd0 μ).choose_spec.choose_spec

/-- Differentiability of the indicated parameterized function:
`Differentiable ℂ (basicSolutionComplex V odd0 t) ∧ Differentiable ℂ (basicSolutionComplexDeriv V
odd0 t)`. -/
private lemma differentiable_basicSolutionComplex_and_basicSolutionComplexDeriv (hV : Continuous V)
    (odd0 : Bool) (t : ℝ) :
    Differentiable ℂ (basicSolutionComplex V odd0 t) ∧
        Differentiable ℂ (basicSolutionComplexDeriv V odd0 t) :=
  differentiable_param_of_linear_ode continuous_const continuous_const
    (Complex.continuous_ofReal.comp hV) continuous_const
    (fun μ t => (basicSolutionComplex_initial_and_hasDerivAt hV odd0 μ).2.2 t)
        (fun μ => (basicSolutionComplex_initial_and_hasDerivAt hV odd0 μ).1)
    (fun μ => (basicSolutionComplex_initial_and_hasDerivAt hV odd0 μ).2.1) t

/-- At real parameters the complex family is the basic solution. -/
private lemma basicSolutionComplex_ofReal_eq_basicSolution (hV : Continuous V)
    (odd0 : Bool) (h t : ℝ) :
    basicSolutionComplex V odd0 t h = (basicSolution V odd0 h t : ℂ) ∧
      basicSolutionComplexDeriv V odd0 t h = ((deriv (basicSolution V odd0 h) t : ℝ) : ℂ) := by
  obtain ⟨y0, y1, hy⟩ := basicSolution_initial_and_isSol hV odd0 h
  obtain ⟨F0, F1, hF⟩ := basicSolutionComplex_initial_and_hasDerivAt hV odd0 h
  have := eq_of_linear_ode (𝕜 := ℂ) (E := ℂ) (t₀ := 0) (p := fun _ => 0)
    (q := fun t => (V t : ℂ) + (h : ℂ) * (-1)) continuous_const
    ((Complex.continuous_ofReal.comp hV).add continuous_const)
    (f := fun t => basicSolutionComplex V odd0 t h)
        (f' := fun t => basicSolutionComplexDeriv V odd0 t h)
    (g := fun t => (basicSolution V odd0 h t : ℂ))
        (g' := fun t => ((deriv (basicSolution V odd0 h) t : ℝ) : ℂ))
    (fun t => ⟨(hF t).1, (hF t).2.congr_deriv (by simp)⟩)
    (fun t => ⟨(hy.hasDerivAt t).ofReal_comp, (hy.2 t).ofReal_comp.congr_deriv (by
      push_cast; simp only [smul_eq_mul]; ring)⟩)
    (by rw [F0, y0]) (by rw [F1, y1])
  exact ⟨congrFun this.1 t, congrFun this.2 t⟩

/-- Continuity of the indicated function:
`Continuous (fun h => basicSolution V odd0 h t) ∧ Continuous (fun h => deriv (basicSolution V odd0
h) t)`. -/
theorem continuous_basicSolution_param (hV : Continuous V) (odd0 : Bool) (t : ℝ) :
    Continuous (fun h => basicSolution V odd0 h t) ∧
        Continuous (fun h => deriv (basicSolution V odd0 h) t) := by
  have e : ∀ h, basicSolution V odd0 h t = (basicSolutionComplex V odd0 t h).re ∧
      deriv (basicSolution V odd0 h) t = (basicSolutionComplexDeriv V odd0 t h).re := fun h => by
    rw [(basicSolutionComplex_ofReal_eq_basicSolution hV odd0 h t).1,
        (basicSolutionComplex_ofReal_eq_basicSolution hV odd0 h t).2]; simp
  simp only [e]
  exact ⟨Complex.continuous_re.comp
      ((differentiable_basicSolutionComplex_and_basicSolutionComplexDeriv hV odd0
      t).1.continuous.comp
      Complex.continuous_ofReal),
    Complex.continuous_re.comp
        ((differentiable_basicSolutionComplex_and_basicSolutionComplexDeriv hV odd0
        t).2.continuous.comp
      Complex.continuous_ofReal)⟩

/-- The spectrum meets every half-line `(-∞, c)` in a finite set. -/
theorem separatedSpectrum_inter_Iio_finite (hV : Continuous V) (hB : ∀ x, |V x| ≤ B) (hL : 0 < L)
    (odd0 oddK : Bool) (c : ℝ) : (separatedSpectrum V L odd0 oddK ∩ Iio c).Finite := by
  set g : ℝ → ℂ := fun h => if oddK then basicSolutionComplex V odd0 L h else
      basicSolutionComplexDeriv V odd0 L h
  have hg : ∀ h, g h = (sturmCharacteristic V L odd0 oddK h : ℂ) := fun h => by
    simp only [g, sturmCharacteristic]; cases oddK <;>
        simp [basicSolutionComplex_ofReal_eq_basicSolution hV]
  have hgc : Differentiable ℂ
      (fun μ : ℂ => if oddK then basicSolutionComplex V odd0 L μ else
      basicSolutionComplexDeriv V odd0 L μ) :=
    by cases oddK <;> simp [differentiable_basicSolutionComplex_and_basicSolutionComplexDeriv hV]
  have hga : AnalyticOnNhd ℝ g univ := fun x _ =>
    ((hgc.analyticAt (x : ℂ)).restrictScalars (𝕜 := ℝ)).comp
      (Complex.ofRealCLM.analyticAt x)
  have hGc : Continuous (sturmCharacteristic V L odd0 oddK) := by
    unfold sturmCharacteristic; cases oddK <;> simp [continuous_basicSolution_param hV]
  set Z := {h | h ∈ Icc (-B - 1) c ∧ sturmCharacteristic V L odd0 oddK h = 0}
  have hsub : separatedSpectrum V L odd0 oddK ∩ Iio c ⊆ Z := fun h ⟨hh, hc⟩ =>
    ⟨⟨by linarith [neg_le_of_mem_separatedSpectrum hV hB hL hh], hc.le⟩,
        (mem_separatedSpectrum_iff hV odd0 oddK).1 hh⟩
  refine Finite.subset ?_ hsub
  by_contra hinf
  have hZc : IsCompact Z := isCompact_Icc.of_isClosed_subset
    (isClosed_Icc.inter (isClosed_singleton.preimage hGc)) fun x hx => hx.1
  obtain ⟨z, -, hz⟩ := exists_nhds_ne_inf_principal_neBot hZc hinf
  have hfreq : ∃ᶠ x in 𝓝[≠] z, g x = 0 := by
    rw [frequently_iff_neBot]
    refine hz.mono (inf_le_inf_left _ (principal_mono.2 fun x hx => ?_))
    simp only [mem_ofPred_eq, hg, hx.2, Complex.ofReal_zero]
  have h0 := hga.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (mem_univ z) hfreq (mem_univ (-B - 1))
  have hG : sturmCharacteristic V L odd0 oddK (-B - 1) = 0 := by
    rw [Pi.zero_apply, hg] at h0; exact_mod_cast h0
  have := neg_le_of_mem_separatedSpectrum hV hB hL ((mem_separatedSpectrum_iff hV odd0 oddK).2 hG)
  linarith

/-! ### Parity, energy bound, joint continuity -/

/-- The sign `±1` of the parity of the basic solution. -/
def paritySign (odd0 : Bool) : ℝ := if odd0 then -1 else 1

/-- For an even potential the basic solution is even (`odd0 = false`) or odd (`odd0 = true`). -/
private lemma basicSolution_neg_of_even (hV : Continuous V) (hVe : ∀ x, V (-x) = V x)
    (odd0 : Bool) (h x : ℝ) :
    basicSolution V odd0 h (-x) = paritySign odd0 * basicSolution V odd0 h x ∧
      deriv (basicSolution V odd0 h) (-x) =
          -(paritySign odd0 * deriv (basicSolution V odd0 h) x) := by
  obtain ⟨y0, y1, hy⟩ := basicSolution_initial_and_isSol hV odd0 h
  set Y := basicSolution V odd0 h
  set s := paritySign odd0
  have hs : s * s = 1 := by simp only [s, paritySign]; cases odd0 <;> norm_num
  set u : ℝ → ℝ := fun x => s * Y (-x)
  have hu1 : ∀ x, HasDerivAt u (-(s * deriv Y (-x))) x := fun x =>
    (((hy.hasDerivAt (-x)).comp x (hasDerivAt_neg x)).const_mul s).congr_deriv (by ring)
  have hdu : deriv u = fun x => -(s * deriv Y (-x)) := funext fun x => (hu1 x).deriv
  have hu : IsSturmLiouvilleSolution V h u := by
    refine ⟨fun x => (hu1 x).differentiableAt, fun x => ?_⟩
    rw [hdu]
    have := (((hy.2 (-x)).comp x (hasDerivAt_neg x)).const_mul s).neg
    refine this.congr_deriv ?_
    simp only [u, hVe]; ring
  have key := isSturmLiouvilleSolution_eq_of_eq_of_deriv_eq hV hu hy (x₀ := 0) (by
      simp only [u, neg_zero, y0, s, paritySign, basicInitValue]; cases odd0 <;> simp)
    (by rw [hdu]; simp only [neg_zero, y1, s, paritySign, basicInitSlope]; cases odd0 <;> simp)
  have e1 : ∀ x, Y (-x) = s * Y x := fun x => by
    have := congrFun key x
    simp only [u] at this
    calc Y (-x) = s * s * Y (-x) := by rw [hs, one_mul]
      _ = s * Y x := by rw [mul_assoc, this]
  refine ⟨e1 x, ?_⟩
  have := congrArg (fun f => f x) hdu
  rw [show u = Y from key] at this
  simp only at this
  calc deriv Y (-x) = s * s * deriv Y (-x) := by rw [hs, one_mul]
    _ = -(s * deriv Y x) := by rw [this]; ring

/-- Energy bound: `Y² + Y'² ≤ exp((1 + B + |h|)|x|)`. -/
private lemma basicSolution_sq_add_deriv_sq_le_exp (hV : Continuous V) (hB : ∀ x, |V x| ≤ B)
    (odd0 : Bool) (h x : ℝ) :
    basicSolution V odd0 h x ^ 2 + deriv (basicSolution V odd0 h) x ^ 2 ≤
        Real.exp ((1 + B + |h|) * |x|) := by
  obtain ⟨y0, y1, hy⟩ := basicSolution_initial_and_isSol hV odd0 h
  set Y := basicSolution V odd0 h
  set C := 1 + B + |h|
  set E : ℝ → ℝ := fun x => Y x ^ 2 + deriv Y x ^ 2
  have hE : ∀ x, HasDerivAt E (2 * Y x * deriv Y x * (1 + (V x - h))) x := fun x =>
    (((hy.hasDerivAt x).pow 2).add ((hy.2 x).pow 2)).congr_deriv (by simp; ring)
  have hE0 : E 0 = 1 := by simp only [E, y0, y1, basicInitValue, basicInitSlope];
                           cases odd0 <;> simp
  have hEd : ∀ x, |2 * Y x * deriv Y x * (1 + (V x - h))| ≤ C * E x := by
    intro x
    have h1 : |1 + (V x - h)| ≤ C := by
      have := abs_add_le 1 (V x - h)
      have := abs_sub (V x) h
      simp only [C]; rw [abs_one] at *; linarith [hB x]
    have h2 : |2 * Y x * deriv Y x| ≤ E x := by
      rw [abs_le]; constructor <;>
        nlinarith [sq_nonneg (Y x + deriv Y x), sq_nonneg (Y x - deriv Y x)]
    rw [abs_mul]
    calc |2 * Y x * deriv Y x| * |1 + (V x - h)| ≤ E x * C :=
          mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
      _ = C * E x := mul_comm _ _
  rcases le_total 0 x with hx | hx
  · set ψ : ℝ → ℝ := fun x => E x * Real.exp (-C * x)
    have hψ : ∀ x, HasDerivAt ψ ((2 * Y x * deriv Y x * (1 + (V x - h))) * Real.exp (-C * x) +
        E x * (Real.exp (-C * x) * (-C))) x := fun x =>
      (hE x).mul ((((hasDerivAt_id x).const_mul (-C)).exp).congr_deriv (by simp))
    have hanti : Antitone ψ := antitone_of_deriv_nonpos (fun x => (hψ x).differentiableAt)
      fun x => by
        rw [(hψ x).deriv]
        have := (le_abs_self _).trans (hEd x)
        have := Real.exp_pos (-C * x)
        nlinarith
    have := hanti hx
    simp only [ψ, mul_zero, Real.exp_zero, mul_one, hE0] at this
    rw [abs_of_nonneg hx]
    have he : Real.exp (-C * x) * Real.exp (C * x) = 1 := by
      rw [← Real.exp_add]; simp
    calc E x = E x * Real.exp (-C * x) * Real.exp (C * x) := by rw [mul_assoc, he, mul_one]
      _ ≤ 1 * Real.exp (C * x) := by gcongr
      _ = _ := one_mul _
  · set χ : ℝ → ℝ := fun x => E x * Real.exp (C * x)
    have hχ : ∀ x, HasDerivAt χ ((2 * Y x * deriv Y x * (1 + (V x - h))) * Real.exp (C * x) +
        E x * (Real.exp (C * x) * C)) x := fun x =>
      (hE x).mul ((((hasDerivAt_id x).const_mul C).exp).congr_deriv (by simp))
    have hmono : Monotone χ := monotone_of_deriv_nonneg (fun x => (hχ x).differentiableAt)
      fun x => by
        rw [(hχ x).deriv]
        have := (neg_abs_le _).trans' (neg_le_neg (hEd x))
        have := Real.exp_pos (C * x)
        nlinarith
    have := hmono hx
    simp only [χ, mul_zero, Real.exp_zero, mul_one, hE0] at this
    rw [abs_of_nonpos hx]
    have he : Real.exp (C * x) * Real.exp (C * -x) = 1 := by
      rw [← Real.exp_add]; simp
    calc E x = E x * Real.exp (C * x) * Real.exp (C * -x) := by rw [mul_assoc, he, mul_one]
      _ ≤ 1 * Real.exp (C * -x) := by gcongr
      _ = _ := one_mul _

/-- Estimate under the stated parameter and domain assumptions: `|a| ≤ 1 + a ^ 2`. -/
private lemma abs_le_one_add_sq (a : ℝ) : |a| ≤ 1 + a ^ 2 := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h]; nlinarith [sq_nonneg (a - 1)]
  · rw [abs_of_nonpos h]; nlinarith [sq_nonneg (a + 1)]

/-- Local uniform bounds for the basic solution and its derivative. -/
private lemma abs_basicSolution_le_and_abs_deriv_le (hV : Continuous V) (hB : ∀ x, |V x| ≤ B)
    (odd0 : Bool) {R X h x : ℝ}
    (hh : |h| ≤ R) (hx : |x| ≤ X) :
    |basicSolution V odd0 h x| ≤ 1 + Real.exp ((1 + B + R) * X) ∧
      |deriv (basicSolution V odd0 h) x| ≤ 1 + Real.exp ((1 + B + R) * X) := by
  have hE := basicSolution_sq_add_deriv_sq_le_exp hV hB odd0 h x
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hmono : Real.exp ((1 + B + |h|) * |x|) ≤ Real.exp ((1 + B + R) * X) :=
    Real.exp_le_exp.2 (mul_le_mul (by linarith) hx (abs_nonneg _) (by linarith [abs_nonneg h]))
  constructor
  · linarith [abs_le_one_add_sq (basicSolution V odd0 h x),
        sq_nonneg (deriv (basicSolution V odd0 h) x)]
  · linarith [abs_le_one_add_sq (deriv (basicSolution V odd0 h) x),
        sq_nonneg (basicSolution V odd0 h x)]

/-- Joint continuity from continuity in the parameter and a locally uniform derivative bound
in the variable. -/
private lemma continuous_uncurry_of_deriv_bound {f f' : ℝ → ℝ → ℝ}
    (hc : ∀ x, Continuous fun h => f h x)
    (hd : ∀ h x, HasDerivAt (f h) (f' h x) x)
    (hb : ∀ R X : ℝ, ∃ M, ∀ h x, |h| ≤ R → |x| ≤ X → |f' h x| ≤ M) :
    Continuous (Function.uncurry f) := by
  rw [Metric.continuous_iff]
  rintro ⟨h₀, x₀⟩ ε hε
  obtain ⟨M, hM⟩ := hb (|h₀| + 1) (|x₀| + 1)
  set M₁ := |M| + 1
  have hM₁ : 0 < M₁ := by positivity
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuous_iff.1 (hc x₀) h₀ (ε / 2) (by linarith)
  refine ⟨min (min δ₁ 1) (ε / (2 * M₁)), by positivity, ?_⟩
  rintro ⟨h, x⟩ hp
  rw [Prod.dist_eq, max_lt_iff] at hp
  obtain ⟨hph, hpx⟩ := hp
  simp only [Real.dist_eq] at hph hpx
  have hh1 : |h - h₀| < δ₁ := hph.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hh2 : |h - h₀| < 1 := hph.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hx2 : |x - x₀| < 1 := hpx.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hx3 : |x - x₀| < ε / (2 * M₁) := hpx.trans_le (min_le_right _ _)
  have hhR : |h| ≤ |h₀| + 1 := by
    have := abs_sub_abs_le_abs_sub h h₀; linarith
  set s := Icc (-(|x₀| + 1)) (|x₀| + 1)
  have hxs : x ∈ s := by
    have := abs_sub_abs_le_abs_sub x x₀
    exact abs_le.1 (by linarith)
  have hx0s : x₀ ∈ s := abs_le.1 (by linarith)
  have hmvt := (convex_Icc (-(|x₀| + 1)) (|x₀| + 1)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f h) (f' := f' h) (C := M₁) (fun y _ => (hd h y).hasDerivWithinAt)
    (fun y hy => by
      have := hM h y hhR (abs_le.2 hy)
      rw [Real.norm_eq_abs]; linarith [le_abs_self M]) hx0s hxs
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have h1 : |f h x - f h x₀| < ε / 2 := by
    calc |f h x - f h x₀| ≤ M₁ * |x - x₀| := hmvt
      _ < M₁ * (ε / (2 * M₁)) := by gcongr
      _ = ε / 2 := by field_simp
  have h2 : |f h x₀ - f h₀ x₀| < ε / 2 := by
    have := hδ₁' h (by rw [Real.dist_eq]; exact hh1)
    rwa [Real.dist_eq] at this
  rw [Real.dist_eq]
  simp only [Function.uncurry_apply_pair]
  calc |f h x - f h₀ x₀| = |(f h x - f h x₀) + (f h x₀ - f h₀ x₀)| := by ring_nf
    _ ≤ |f h x - f h x₀| + |f h x₀ - f h₀ x₀| := abs_add_le _ _
    _ < ε := by linarith

/-- Continuity of the indicated function: `Continuous (Function.uncurry (basicSolution V odd0)) ∧
Continuous (Function.uncurry fun h x => deriv (basicSolution V odd0 h) x)`. -/
theorem continuous_uncurry_basicSolution (hV : Continuous V) (hB : ∀ x, |V x| ≤ B) (odd0 : Bool) :
    Continuous (Function.uncurry (basicSolution V odd0)) ∧
      Continuous (Function.uncurry fun h x => deriv (basicSolution V odd0 h) x) := by
  have c1 : Continuous (Function.uncurry (basicSolution V odd0)) :=
    continuous_uncurry_of_deriv_bound (fun x => (continuous_basicSolution_param hV odd0 x).1)
      (fun h x => ((basicSolution_initial_and_isSol hV odd0 h).2.2).hasDerivAt x)
      fun R X => ⟨_, fun h x hh hx => (abs_basicSolution_le_and_abs_deriv_le hV hB odd0 hh hx).2⟩
  refine ⟨c1, continuous_uncurry_of_deriv_bound
      (fun x => (continuous_basicSolution_param hV odd0 x).2)
      (fun h x => ((basicSolution_initial_and_isSol hV odd0 h).2.2).2 x)
      fun R X => ⟨(B + R) * (1 + Real.exp ((1 + B + R) * X)), fun h x hh hx => ?_⟩⟩
  rw [abs_mul]
  have h1 : |V x - h| ≤ B + R := (abs_sub _ _).trans (add_le_add (hB x) hh)
  exact mul_le_mul h1 (abs_basicSolution_le_and_abs_deriv_le hV hB odd0 hh hx).1 (abs_nonneg _)
    ((abs_nonneg _).trans h1)

/-! ### Oscillation for large `h` and unboundedness of the spectrum -/

/-- For `h > B + ((N + 1)π/(2L))²`, a nonzero solution has `N + 1` zeros in `(-L, L)`, in
increasing order (Sturm comparison with `sin(ω(x + L))`, `ω = (N + 1)π/(2L)`). -/
private lemma isSturmLiouvilleSolution_exists_strictMono_zeros (hB : ∀ x, |V x| ≤ B) (hL : 0 < L)
    (N : ℕ) {w : ℝ → ℝ}
    (hw : IsSturmLiouvilleSolution V h w) (hh : B + ((N + 1) * Real.pi / (2 * L)) ^ 2 < h) :
    ∃ z : Fin (N + 1) → ℝ, StrictMono z ∧ (∀ j, z j ∈ Ioo (-L) L) ∧ ∀ j, w (z j) = 0 := by
  set ω := (N + 1) * Real.pi / (2 * L)
  have hω : 0 < ω := by positivity
  set a : ℕ → ℝ := fun j => -L + j * Real.pi / ω
  have ha : ∀ j : ℕ, ω * (a j + L) = j * Real.pi := fun j => by
    simp only [a]; field_simp; ring
  have haN : a (N + 1) = L := by
    simp only [a, ω]; push_cast; field_simp; ring
  have hamono : StrictMono a := fun i j hij => by
    simp only [a]
    have : (i : ℝ) < j := by exact_mod_cast hij
    have := Real.pi_pos
    have : (i : ℝ) * Real.pi / ω < j * Real.pi / ω := by gcongr
    linarith
  have hzero : ∀ j : ℕ, ∃ x ∈ Ioo (a j) (a (j + 1)), w x = 0 := by
    intro j
    have hab : a j < a (j + 1) := hamono (Nat.lt_succ_self j)
    refine sturm_comparison_strict (p := fun _ => 1) (q₁ := fun _ => ω ^ 2)
      (q₂ := fun x => h - V x) (u := fun x => Real.sin (ω * (x + L)))
      (u' := fun x => ω * Real.cos (ω * (x + L))) (v := w) (v' := deriv w) hab
      (fun x _ => ?_) (fun x _ => ?_) (fun x _ => hw.hasDerivAt x) (fun x _ => ?_)
      zero_le_one zero_le_one (fun x _ => ?_) ?_ ?_ (fun x hx => ?_)
    · have := ((hasDerivAt_id x).add_const L).const_mul ω |>.sin
      exact this.congr_deriv (by simp; ring)
    · have := (((hasDerivAt_id x).add_const L).const_mul ω |>.cos).const_mul ω
      simp only [one_mul]
      exact this.congr_deriv (by simp; ring)
    · simp only [one_mul]
      exact (hw.2 x).congr_deriv (by ring)
    · show ω ^ 2 < h - V x
      have := le_abs_self (V x); have := hB x; linarith
    · show Real.sin (ω * (a j + L)) = 0
      rw [ha]; exact Real.sin_nat_mul_pi j
    · show Real.sin (ω * (a (j + 1) + L)) = 0
      rw [ha]; exact_mod_cast Real.sin_nat_mul_pi (j + 1)
    · show Real.sin (ω * (x + L)) ≠ 0
      intro hs
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 hs
      have h1 : ω * (a j + L) < ω * (x + L) := by gcongr; exact hx.1
      have h2 : ω * (x + L) < ω * (a (j + 1) + L) := by gcongr; exact hx.2
      rw [ha, ← hn] at h1; rw [ha, ← hn] at h2
      have h1' : (j : ℝ) < n := lt_of_mul_lt_mul_right h1 Real.pi_pos.le
      have h2' : (n : ℝ) < ((j + 1 : ℕ) : ℝ) := lt_of_mul_lt_mul_right h2 Real.pi_pos.le
      have e1 : (j : ℤ) < n := by exact_mod_cast h1'
      have e2 : n < ((j + 1 : ℕ) : ℤ) := by exact_mod_cast h2'
      push_cast at e2
      omega
  choose z hz hz0 using hzero
  refine ⟨fun j => z j, Fin.strictMono_iff_lt_succ.2 fun j => ?_, fun j => ⟨?_, ?_⟩,
    fun j => hz0 j⟩
  · simp only [Fin.val_castSucc, Fin.val_succ]
    exact (hz j).2.trans (hz (j + 1)).1
  · have := hamono.monotone (Nat.zero_le (j : ℕ))
    have h0 : a 0 = -L := by simp [a]
    linarith [(hz j).1]
  · have := hamono.monotone (Nat.succ_le_of_lt j.2)
    linarith [(hz j).2]

/-- Simple zeros of a nonzero solution in a compact interval are finite in number. -/
theorem isSturmLiouvilleSolution_zeros_Icc_finite (hV : Continuous V) {w : ℝ → ℝ}
    (hw : IsSturmLiouvilleSolution V h w) (hne : w ≠ 0)
    (a b : ℝ) : {x | x ∈ Icc a b ∧ w x = 0}.Finite :=
  SturmDeformation.finite (fun x _ => hw.hasDerivAt x) fun _ _ h0 h1 =>
      hne (isSturmLiouvilleSolution_eq_zero_of_eq_zero_of_deriv_eq_zero hV hw h0 h1)

/-- Estimate under the stated parameter and domain assumptions: `n ≤ {x | P x}.ncard`. -/
theorem le_ncard_of_strictMono {P : ℝ → Prop} {n : ℕ} {z : Fin n → ℝ} (hz : StrictMono z)
    (hP : ∀ j, P (z j)) (hfin : {x | P x}.Finite) : n ≤ {x | P x}.ncard := by
  have := Set.ncard_le_ncard (s := range z) (t := {x | P x}) (by
    rintro _ ⟨j, rfl⟩; exact hP j) hfin
  rwa [Set.ncard_range_of_injective hz.injective, Nat.card_eq_fintype_card,
    Fintype.card_fin] at this

/-- The deformation argument: a family whose zero count on `[a, b]` is unbounded cannot have
nonvanishing values at `a` and `b` for all large parameters. -/
private lemma zero_count_deformation {Y Y' : ℝ → ℝ → ℝ} {H H₀ a b : ℝ}
    (hcY : Continuous (Function.uncurry Y)) (hcY' : Continuous (Function.uncurry Y'))
    (hd : ∀ h, H < h → ∀ x, HasDerivAt (Y h) (Y' h x) x)
    (hs : ∀ h, H < h → ∀ x, Y h x = 0 → Y' h x ≠ 0)
    (hmany : ∀ N : ℕ, ∃ h₀, ∀ h, h₀ ≤ h → N ≤ {x | x ∈ Icc a b ∧ Y h x = 0}.ncard)
    (hend : ∀ h, H₀ ≤ h → Y h a ≠ 0 ∧ Y h b ≠ 0) : False := by
  set t₁ := max H₀ H + 1
  have hsub : Ici t₁ ⊆ Ioi H := fun h hh => by
    simp only [mem_Ici, mem_Ioi] at hh ⊢; linarith [le_max_right H₀ H]
  obtain ⟨h₀, hh₀⟩ := hmany ({x | x ∈ Icc a b ∧ Y t₁ x = 0}.ncard + 1)
  have hc := SturmDeformation.ncard_eq_of_isPreconnected (Y := Y) (Y' := Y')
      (Λ := Ioi H) (U := univ)
    isOpen_Ioi isOpen_univ (subset_univ _) hcY.continuousOn hcY'.continuousOn
    (fun t ht x _ => hd t ht x) (fun t ht x _ => hs t ht x) isPreconnected_Ici hsub
    (fun t ht => hend t (by simp only [mem_Ici] at ht; linarith [le_max_left H₀ H]))
    (mem_Ici.2 le_rfl : t₁ ∈ Ici t₁) (le_max_left t₁ h₀ : t₁ ≤ max t₁ h₀)
  have := hh₀ (max t₁ h₀) (le_max_right _ _)
  omega

/-- **The spectrum is unbounded above.** -/
theorem not_bddAbove_separatedSpectrum (hV : Continuous V) (hB : ∀ x, |V x| ≤ B)
    (hVe : ∀ x, V (-x) = V x) (hL : 0 < L) (odd0 oddK : Bool) :
    ¬BddAbove (separatedSpectrum V L odd0 oddK) := by
  rintro ⟨H₀, hH₀⟩
  have hnot : ∀ h, H₀ + 1 ≤ h → sturmCharacteristic V L odd0 oddK h ≠ 0 := fun h hh hG => by
    have := hH₀ ((mem_separatedSpectrum_iff hV odd0 oddK).2 hG); linarith
  have hY := fun h => basicSolution_initial_and_isSol hV odd0 h
  have hsg : paritySign odd0 ≠ 0 := by unfold paritySign; cases odd0 <;> norm_num
  obtain ⟨c1, c2⟩ := continuous_uncurry_basicSolution hV hB odd0
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  cases oddK
  · -- zeros of `Y'` on `[-L, L]`
    refine zero_count_deformation (Y := fun h x => deriv (basicSolution V odd0 h) x)
      (Y' := fun h x => (V x - h) * basicSolution V odd0 h x) (H := B) (H₀ := H₀ + 1)
          (a := -L) (b := L)
      c2 ((hV.comp continuous_snd).sub continuous_fst |>.mul c1) (fun h _ x => (hY h).2.2.2 x)
      (fun h hh x h0 h1 => ?_) (fun N => ?_) (fun h hh => ?_)
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · have := le_abs_self (V x); linarith [hB x]
      · exact basicSolution_ne_zero hV odd0 h
            (isSturmLiouvilleSolution_eq_zero_of_eq_zero_of_deriv_eq_zero hV (hY h).2.2 h2 h0)
    · refine ⟨B + ((N + 1 + 1) * Real.pi / (2 * L)) ^ 2 + 1, fun h hh => ?_⟩
      obtain ⟨z, hz, hzI, hz0⟩ :=
          isSturmLiouvilleSolution_exists_strictMono_zeros hB hL (N + 1) (hY h).2.2 (by
        push_cast; linarith)
      have hrolle : ∀ j : Fin (N + 1), ∃ c ∈ Ioo (z j.castSucc) (z j.succ),
          deriv (basicSolution V odd0 h) c = 0 := fun j =>
        exists_hasDerivAt_eq_zero (hz Fin.castSucc_lt_succ)
          ((hY h).2.2.continuous.continuousOn) (by rw [hz0, hz0])
          fun x _ => (hY h).2.2.hasDerivAt x
      choose c hc hc0 using hrolle
      have hcm : StrictMono c := Fin.strictMono_iff_lt_succ.2 fun j =>
        (hc j.castSucc).2.trans (hc j.succ).1
      have hfin : {x | x ∈ Icc (-L) L ∧ deriv (basicSolution V odd0 h) x = 0}.Finite :=
        SturmDeformation.finite (fun x _ => (hY h).2.2.2 x) fun x _ h0 h1 => by
          rcases mul_eq_zero.1 h1 with h2 | h2
          · have := le_abs_self (V x)
            have : 0 ≤ ((N + 1 + 1) * Real.pi / (2 * L)) ^ 2 := sq_nonneg _
            linarith [hB x]
          · exact basicSolution_ne_zero hV odd0 h
                (isSturmLiouvilleSolution_eq_zero_of_eq_zero_of_deriv_eq_zero hV (hY h).2.2 h2 h0)
      have := le_ncard_of_strictMono (P := fun x => x ∈ Icc (-L) L ∧
        deriv (basicSolution V odd0 h) x = 0) hcm (fun j => ⟨⟨?_, ?_⟩, hc0 j⟩) hfin
      · omega
      · exact ((hzI j.castSucc).1.trans (hc j).1).le
      · exact ((hc j).2.trans (hzI j.succ).2).le
    · have hG := hnot h hh
      simp only [sturmCharacteristic, Bool.false_eq_true, ↓reduceIte] at hG
      refine ⟨?_, hG⟩
      rw [(basicSolution_neg_of_even hV hVe odd0 h L).2]
      exact neg_ne_zero.2 (mul_ne_zero hsg hG)
  · -- zeros of `Y` on `[-L, L]`
    refine zero_count_deformation (Y := basicSolution V odd0)
        (Y' := fun h x => deriv (basicSolution V odd0 h) x)
      (H := B) (H₀ := H₀ + 1) (a := -L) (b := L) c1 c2 (fun h _ x => (hY h).2.2.hasDerivAt x)
      (fun h _ x h0 h1 => basicSolution_ne_zero hV odd0 h
          (isSturmLiouvilleSolution_eq_zero_of_eq_zero_of_deriv_eq_zero hV (hY h).2.2 h0 h1))
      (fun N => ?_) (fun h hh => ?_)
    · refine ⟨B + ((N + 1) * Real.pi / (2 * L)) ^ 2 + 1, fun h hh => ?_⟩
      obtain ⟨z, hz, hzI, hz0⟩ :=
          isSturmLiouvilleSolution_exists_strictMono_zeros hB hL N (hY h).2.2 (by linarith)
      have := le_ncard_of_strictMono (P := fun x => x ∈ Icc (-L) L ∧ basicSolution V odd0 h x = 0)
        hz (fun j => ⟨Ioo_subset_Icc_self (hzI j), hz0 j⟩)
        (isSturmLiouvilleSolution_zeros_Icc_finite hV (hY h).2.2
            (basicSolution_ne_zero hV odd0 h) (-L) L)
      omega
    · have hG := hnot h hh
      simp only [sturmCharacteristic, ↓reduceIte] at hG
      refine ⟨?_, hG⟩
      rw [(basicSolution_neg_of_even hV hVe odd0 h L).1]
      exact mul_ne_zero hsg hG

/-! ### Enumeration of a discrete spectrum -/

section Enum

variable {S : Set ℝ}

/-- Estimate under the stated parameter and domain assumptions: `(S ∩ Iio s).ncard < (S ∩ Iio
t).ncard`. -/
private lemma ncard_inter_Iio_lt_of_mem (hfin : ∀ c, (S ∩ Iio c).Finite) {s t : ℝ} (hs : s ∈ S)
    (hst : s < t) :
    (S ∩ Iio s).ncard < (S ∩ Iio t).ncard :=
  Set.ncard_lt_ncard ⟨fun _ hx => ⟨hx.1, hx.2.trans hst⟩,
    fun h => (lt_irrefl s) (h ⟨hs, hst⟩).2⟩ (hfin t)

/-- Identity under the stated parameter and domain assumptions: `s = t`. -/
private lemma eq_of_ncard_inter_Iio_eq (hfin : ∀ c, (S ∩ Iio c).Finite) {s t : ℝ}
    (hs : s ∈ S) (ht : t ∈ S)
    (he : (S ∩ Iio s).ncard = (S ∩ Iio t).ncard) : s = t := by
  rcases lt_trichotomy s t with h | h | h
  · exact absurd he (ncard_inter_Iio_lt_of_mem hfin hs h).ne
  · exact h
  · exact absurd he (ncard_inter_Iio_lt_of_mem hfin ht h).ne'

/-- Every natural index occurs as the number of spectral values strictly below some value in the
discrete ordered spectrum. -/
private lemma exists_mem_ncard_inter_Iio_eq (hinf : ¬BddAbove S)
    (hfin : ∀ c, (S ∩ Iio c).Finite) (j : ℕ) :
    ∃ s ∈ S, (S ∩ Iio s).ncard = j := by
  -- the least element of `S ∩ Ioi c ∩ Iic t`
  have hmin : ∀ c : WithBot ℝ, ∃ s ∈ S, c < s ∧ ∀ x ∈ S, c < x → s ≤ x := by
    intro c
    obtain ⟨t, htS, hct⟩ : ∃ t ∈ S, c < t := by
      by_contra hno
      push Not at hno
      induction c with
      | bot => obtain ⟨t, ht⟩ := not_bddAbove_iff.1 hinf 0; exact absurd (hno t ht.1) (by simp)
      | coe c =>
        exact hinf ⟨c, fun t ht => by exact_mod_cast hno t ht⟩
    have hT : {x | x ∈ S ∧ c < x ∧ x ≤ t}.Finite :=
      (hfin (t + 1)).subset fun x hx => ⟨hx.1, show x < t + 1 by have := hx.2.2; linarith⟩
    obtain ⟨s, hs, hsmin⟩ := Set.exists_min_image _ id hT ⟨t, htS, hct, le_rfl⟩
    refine ⟨s, hs.1, hs.2.1, fun x hx hcx => ?_⟩
    rcases le_total x t with hxt | hxt
    · exact hsmin x ⟨hx, hcx, hxt⟩
    · exact hs.2.2.trans hxt
  induction j with
  | zero =>
    obtain ⟨s, hs, -, hsm⟩ := hmin ⊥
    refine ⟨s, hs, ?_⟩
    rw [Set.ncard_eq_zero (hfin s)]
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_empty_iff_false, iff_false, not_and, not_lt]
    exact fun hx => hsm x hx (WithBot.bot_lt_coe x)
  | succ j ih =>
    obtain ⟨s, hs, hsj⟩ := ih
    obtain ⟨s', hs', hss', hsm⟩ := hmin s
    have hss'' : s < s' := by exact_mod_cast hss'
    refine ⟨s', hs', ?_⟩
    have heq : S ∩ Iio s' = insert s (S ∩ Iio s) := by
      ext x
      simp only [mem_inter_iff, mem_Iio, mem_insert_iff]
      constructor
      · rintro ⟨hx, hxs'⟩
        rcases lt_trichotomy x s with h | h | h
        · exact Or.inr ⟨hx, h⟩
        · exact Or.inl h
        · exact absurd (hsm x hx (by exact_mod_cast h)) (not_le.2 hxs')
      · rintro (rfl | ⟨hx, hxs⟩)
        · exact ⟨hs, hss''⟩
        · exact ⟨hx, hxs.trans hss''⟩
    rw [heq, Set.ncard_insert_of_notMem (fun h : s ∈ S ∩ Iio s => lt_irrefl s h.2) (hfin s), hsj]

/-- **Enumeration of a discrete spectrum**: if `S ⊆ ℝ` is unbounded above and meets every
`(-∞, c)` in a finite set, then for each `j` there is exactly one `s ∈ S` with `j` points of
`S` below it, and any such enumeration is strictly increasing, exhausts `S` and tends to `∞`. -/
theorem discrete_spectrum_enumeration (hinf : ¬BddAbove S) (hfin : ∀ c, (S ∩ Iio c).Finite) :
    (∀ j : ℕ, ∃! s, s ∈ S ∧ (S ∩ Iio s).Finite ∧ (S ∩ Iio s).ncard = j) ∧
      ∀ e : ℕ → ℝ, (∀ j, e j ∈ S ∧ (S ∩ Iio (e j)).ncard = j) →
        StrictMono e ∧ S = range e ∧ Tendsto e atTop atTop := by
  refine ⟨fun j => ?_, fun e he => ?_⟩
  · obtain ⟨s, hs, hsj⟩ := exists_mem_ncard_inter_Iio_eq hinf hfin j
    exact ⟨s, ⟨hs, hfin s, hsj⟩, fun t ht =>
      eq_of_ncard_inter_Iio_eq hfin ht.1 hs (ht.2.2.trans hsj.symm)⟩
  have hmono : StrictMono e := by
    intro i j hij
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with h | h
    · have := ncard_inter_Iio_lt_of_mem hfin (he j).1 h
      rw [(he i).2, (he j).2] at this; omega
    · have := congrArg (fun x => (S ∩ Iio x).ncard) h
      simp only [(he i).2, (he j).2] at this; omega
  refine ⟨hmono, ?_, ?_⟩
  · ext s
    refine ⟨fun hs => ⟨(S ∩ Iio s).ncard, eq_of_ncard_inter_Iio_eq hfin (he _).1 hs (he _).2⟩, ?_⟩
    rintro ⟨j, rfl⟩
    exact (he j).1
  · refine tendsto_atTop_atTop.2 fun c => ?_
    by_contra hno
    push Not at hno
    have : (range e).Infinite := Set.infinite_range_of_injective hmono.injective
    exact this ((hfin c).subset (by
      rintro _ ⟨j, rfl⟩
      obtain ⟨i, hi, hci⟩ := hno j
      exact ⟨(he j).1, (hmono.monotone hi).trans_lt hci⟩))

end Enum

end ODE
