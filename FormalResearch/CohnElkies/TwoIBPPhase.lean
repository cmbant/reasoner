module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Two integrations by parts against a variable phase (Piece C, smooth part)

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `u1c:U3`(3), Step 1, Piece C,
item 2 ("The smooth part").

For `a ∈ C¹(ℝ)` vanishing off `[u, v]`, with `a'` differentiable off a countable set `s` and `a''`
integrable on `[u, v]`, and `ψ ∈ C³` with `ψ' > 0` on `[u, v]`:
`∫ a e^{iψ} = -∫ ((a/ψ')'/ψ')' e^{iψ}`, hence
`|∫ a e^{iψ}| ≤ ∫_{[u,v]} (|a''|/ψ'² + 3|a'||ψ''|/ψ'³ + |a||ψ'''|/ψ'³ + 3|a|ψ''²/ψ'⁴)`.
There are no boundary terms, since `a` and `a'` vanish at `u` and `v`. The second integration by
parts is taken off the countable set `s`, using `MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le`.
This is a standard two-integrations-by-parts estimate; the content is the bookkeeping of the expansion
and of the sign of `ψ'`.

Status: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped Real

namespace FormalResearch.CohnElkies

/-- An interval integral over `[u, v]` as the set integral over `Icc u v`. -/
lemma twoIbp_interval_eq_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u v : ℝ}
    (huv : u ≤ v) (f : ℝ → E) :
    ∫ x in u..v, f x = ∫ x in Icc u v, f x := by
  rw [intervalIntegral.integral_of_le huv, integral_Icc_eq_integral_Ioc]

/-- A continuous function vanishing to the left of `u` vanishes at `u`. -/
lemma twoIbp_eq_zero_of_left {f : ℝ → ℂ} {u : ℝ} (hf : Continuous f) (h : ∀ x < u, f x = 0) :
    f u = 0 := by
  have hc : IsClosed {x : ℝ | f x = 0} := isClosed_eq hf continuous_const
  have hsub : Iio u ⊆ {x : ℝ | f x = 0} := fun x hx => h x hx
  have hu : u ∈ closure (Iio u) := by
    rw [closure_Iio' Set.nonempty_Iio]; exact Set.mem_Iic.mpr le_rfl
  exact closure_minimal hsub hc hu

/-- A continuous function vanishing to the right of `v` vanishes at `v`. -/
lemma twoIbp_eq_zero_of_right {f : ℝ → ℂ} {v : ℝ} (hf : Continuous f) (h : ∀ x > v, f x = 0) :
    f v = 0 := by
  have hc : IsClosed {x : ℝ | f x = 0} := isClosed_eq hf continuous_const
  have hsub : Ioi v ⊆ {x : ℝ | f x = 0} := fun x hx => h x hx
  have hv : v ∈ closure (Ioi v) := by
    rw [closure_Ioi' Set.nonempty_Ioi]; exact Set.mem_Ici.mpr le_rfl
  exact closure_minimal hsub hc hv

/-- Division of a complex integrable function by a continuous nonvanishing one. -/
lemma twoIbp_integrableOn_div {f g : ℝ → ℂ} {u v : ℝ} (hf : IntegrableOn f (Icc u v))
    (hg : ContinuousOn g (Icc u v)) (hne : ∀ x ∈ Icc u v, g x ≠ 0) :
    IntegrableOn (fun x => f x / g x) (Icc u v) := by
  have h := hf.mul_continuousOn (hg.inv₀ hne) isCompact_Icc
  simpa only [div_eq_mul_inv, Pi.inv_apply] using h

/-- Division of a real integrable function by a continuous nonvanishing one. -/
lemma twoIbp_integrableOn_div_real {f g : ℝ → ℝ} {u v : ℝ} (hf : IntegrableOn f (Icc u v))
    (hg : ContinuousOn g (Icc u v)) (hne : ∀ x ∈ Icc u v, g x ≠ 0) :
    IntegrableOn (fun x => f x / g x) (Icc u v) := by
  have h := hf.mul_continuousOn (hg.inv₀ hne) isCompact_Icc
  simpa only [div_eq_mul_inv, Pi.inv_apply] using h

/-- Pointwise bound on the expanded `((a/ψ')'/ψ')'` with `ψ' > 0`. -/
lemma twoIbp_pointwise (A0 A1 A2 : ℂ) (r1 r2 r3 : ℝ) (hr : 0 < r1) :
    ‖A2 / (r1 : ℂ) ^ 2 - 3 * A1 * (r2 : ℂ) / (r1 : ℂ) ^ 3 - A0 * (r3 : ℂ) / (r1 : ℂ) ^ 3
        + 3 * A0 * (r2 : ℂ) ^ 2 / (r1 : ℂ) ^ 4‖
      ≤ ‖A2‖ / r1 ^ 2 + 3 * ‖A1‖ * |r2| / r1 ^ 3 + ‖A0‖ * |r3| / r1 ^ 3
        + 3 * ‖A0‖ * r2 ^ 2 / r1 ^ 4 := by
  have hc : ‖(r1 : ℂ)‖ = r1 := by rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
  have e1 : ‖A2 / (r1 : ℂ) ^ 2‖ = ‖A2‖ / r1 ^ 2 := by
    rw [norm_div, norm_pow, hc]
  have e2 : ‖3 * A1 * (r2 : ℂ) / (r1 : ℂ) ^ 3‖ = 3 * ‖A1‖ * |r2| / r1 ^ 3 := by
    simp only [norm_div, norm_mul, norm_pow, hc, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have e3 : ‖A0 * (r3 : ℂ) / (r1 : ℂ) ^ 3‖ = ‖A0‖ * |r3| / r1 ^ 3 := by
    simp only [norm_div, norm_mul, norm_pow, hc, Complex.norm_real, Real.norm_eq_abs]
  have e4 : ‖3 * A0 * (r2 : ℂ) ^ 2 / (r1 : ℂ) ^ 4‖ = 3 * ‖A0‖ * r2 ^ 2 / r1 ^ 4 := by
    simp only [norm_div, norm_mul, norm_pow, hc, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    norm_num
  have h1 := norm_add_le (A2 / (r1 : ℂ) ^ 2 - 3 * A1 * (r2 : ℂ) / (r1 : ℂ) ^ 3
      - A0 * (r3 : ℂ) / (r1 : ℂ) ^ 3) (3 * A0 * (r2 : ℂ) ^ 2 / (r1 : ℂ) ^ 4)
  have h2 := norm_sub_le (A2 / (r1 : ℂ) ^ 2 - 3 * A1 * (r2 : ℂ) / (r1 : ℂ) ^ 3)
      (A0 * (r3 : ℂ) / (r1 : ℂ) ^ 3)
  have h3 := norm_sub_le (A2 / (r1 : ℂ) ^ 2) (3 * A1 * (r2 : ℂ) / (r1 : ℂ) ^ 3)
  linarith

/-- Integration by parts against `e^{iψ}` on `[u, v]` with no boundary terms. If `F` is continuous on
`[u, v]`, differentiable off a countable set `s`, vanishes at `u` and `v`, and `F'` is interval
integrable, then `∫ F · (iψ') e^{iψ} = -∫ F' e^{iψ}`. The step off `s` is the countable-set
fundamental theorem of calculus applied to `F e^{iψ}`. -/
theorem twoIbp_ibp {F F' : ℝ → ℂ} {ψ : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v) {s : Set ℝ}
    (hs : s.Countable) (hψ : Differentiable ℝ ψ) (hψc : ContinuousOn (deriv ψ) (Icc u v))
    (hFc : ContinuousOn F (Icc u v)) (hFd : ∀ x ∈ Ioo u v \ s, HasDerivAt F (F' x) x)
    (hF'i : IntervalIntegrable F' volume u v) (hFu : F u = 0) (hFv : F v = 0) :
    ∫ x in u..v, F x * (Complex.I * ((deriv ψ x : ℝ) : ℂ) * Complex.exp (Complex.I * (ψ x : ℂ))) =
      -∫ x in u..v, F' x * Complex.exp (Complex.I * (ψ x : ℂ)) := by
  have hIcc : Set.uIcc u v = Icc u v := Set.uIcc_of_le huv
  have hE : ∀ x, HasDerivAt (fun y => Complex.exp (Complex.I * (ψ y : ℂ)))
      (Complex.I * ((deriv ψ x : ℝ) : ℂ) * Complex.exp (Complex.I * (ψ x : ℂ))) x := by
    intro x
    have h := (((hψ x).hasDerivAt).ofReal_comp.const_mul Complex.I).cexp
    convert h using 1
    ring
  have hEc : Continuous fun y : ℝ => Complex.exp (Complex.I * (ψ y : ℂ)) :=
    continuous_iff_continuousAt.2 fun x => (hE x).continuousAt
  have hψcc : ContinuousOn (fun x => ((deriv ψ x : ℝ) : ℂ)) (Icc u v) :=
    Complex.continuous_ofReal.comp_continuousOn hψc
  have hint1 : IntervalIntegrable (fun x => F x * (Complex.I * ((deriv ψ x : ℝ) : ℂ) *
      Complex.exp (Complex.I * (ψ x : ℂ)))) volume u v := by
    apply ContinuousOn.intervalIntegrable
    rw [hIcc]
    exact hFc.mul ((continuousOn_const.mul hψcc).mul hEc.continuousOn)
  have hint2 : IntervalIntegrable (fun x => F' x * Complex.exp (Complex.I * (ψ x : ℂ)))
      volume u v :=
    hF'i.mul_continuousOn hEc.continuousOn
  have hGd : ∀ x ∈ Ioo u v \ s, HasDerivAt (fun y => F y * Complex.exp (Complex.I * (ψ y : ℂ)))
      (F' x * Complex.exp (Complex.I * (ψ x : ℂ)) + F x * (Complex.I * ((deriv ψ x : ℝ) : ℂ) *
        Complex.exp (Complex.I * (ψ x : ℂ)))) x :=
    fun x hx => (hFd x hx).mul (hE x)
  have hGc : ContinuousOn (fun y => F y * Complex.exp (Complex.I * (ψ y : ℂ))) (Icc u v) :=
    hFc.mul hEc.continuousOn
  have hGi : IntervalIntegrable (fun x => F' x * Complex.exp (Complex.I * (ψ x : ℂ)) + F x *
      (Complex.I * ((deriv ψ x : ℝ) : ℂ) * Complex.exp (Complex.I * (ψ x : ℂ)))) volume u v :=
    hint2.add hint1
  have key : ∫ x in u..v, (F' x * Complex.exp (Complex.I * (ψ x : ℂ)) + F x *
      (Complex.I * ((deriv ψ x : ℝ) : ℂ) * Complex.exp (Complex.I * (ψ x : ℂ)))) =
      F v * Complex.exp (Complex.I * (ψ v : ℂ)) - F u * Complex.exp (Complex.I * (ψ u : ℂ)) :=
    MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
      (fun y => F y * Complex.exp (Complex.I * (ψ y : ℂ)))
      (fun x => F' x * Complex.exp (Complex.I * (ψ x : ℂ)) + F x *
        (Complex.I * ((deriv ψ x : ℝ) : ℂ) * Complex.exp (Complex.I * (ψ x : ℂ))))
      huv hs hGc hGd hGi
  have hsplit : ∫ x in u..v, (F' x * Complex.exp (Complex.I * (ψ x : ℂ)) + F x *
      (Complex.I * ((deriv ψ x : ℝ) : ℂ) * Complex.exp (Complex.I * (ψ x : ℂ)))) =
      (∫ x in u..v, F' x * Complex.exp (Complex.I * (ψ x : ℂ))) +
        ∫ x in u..v, F x * (Complex.I * ((deriv ψ x : ℝ) : ℂ) * Complex.exp (Complex.I * (ψ x : ℂ))) :=
    intervalIntegral.integral_add hint2 hint1
  have hv0 : F v * Complex.exp (Complex.I * (ψ v : ℂ)) - F u * Complex.exp (Complex.I * (ψ u : ℂ))
      = 0 := by
    rw [hFu, hFv]; ring
  linear_combination key - hsplit + hv0

/-- Two integrations by parts against `e^{iψ}` (Piece C, smooth part). Let `a ∈ C¹(ℝ)` vanish off
`[u, v]`, with `a'` differentiable off a countable set `s` and `a''` integrable on `[u, v]`, and let
`ψ ∈ C³` with `ψ' > 0` on `[u, v]`. Then `|∫ a e^{iψ}|` is bounded by the integral over `[u, v]` of
`|a''|/ψ'² + 3|a'||ψ''|/ψ'³ + |a||ψ'''|/ψ'³ + 3|a|ψ''²/ψ'⁴`. The proof uses
`∫ a e^{iψ} = -∫ ((a/ψ')'/ψ')' e^{iψ}`, with no boundary terms. Standard two-integrations-by-parts
estimate. -/
theorem two_ibp_phase {a : ℝ → ℂ} {ψ : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v)
    (ha : ContDiff ℝ 1 a) (s : Set ℝ) (hs : s.Countable) (ha2 : ∀ x ∉ s, DifferentiableAt ℝ (deriv a) x)
    (hint : IntegrableOn (deriv (deriv a)) (Set.Icc u v))
    (hsupp : ∀ x, x ∉ Set.Icc u v → a x = 0)
    (hψ : ContDiff ℝ 3 ψ) (hψ' : ∀ x ∈ Set.Icc u v, 0 < deriv ψ x) :
    ‖∫ x, a x * Complex.exp (Complex.I * ψ x)‖ ≤
      ∫ x in Set.Icc u v, (‖deriv (deriv a) x‖ / deriv ψ x ^ 2
        + 3 * ‖deriv a x‖ * |deriv (deriv ψ) x| / deriv ψ x ^ 3
        + ‖a x‖ * |deriv (deriv (deriv ψ)) x| / deriv ψ x ^ 3
        + 3 * ‖a x‖ * deriv (deriv ψ) x ^ 2 / deriv ψ x ^ 4) := by
  -- regularity of `a` and `ψ`
  have hadiff : Differentiable ℝ a := ha.differentiable (by norm_num)
  have hdac : Continuous (deriv a) := ha.continuous_deriv (by norm_num)
  have hψ1 : ContDiff ℝ 2 (deriv ψ) := hψ.deriv'
  have hψ2 : ContDiff ℝ 1 (deriv (deriv ψ)) := hψ1.deriv'
  have hψ3 : Continuous (deriv (deriv (deriv ψ))) :=
    (show ContDiff ℝ (0 + 1) (deriv (deriv ψ)) from hψ2).deriv'.continuous
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hψ1d : Differentiable ℝ (deriv ψ) := hψ1.differentiable (by norm_num)
  have hψ2d : Differentiable ℝ (deriv (deriv ψ)) := hψ2.differentiable (by norm_num)
  have hψ1c : Continuous (deriv ψ) := hψ1.continuous
  have hψ2c : Continuous (deriv (deriv ψ)) := hψ2.continuous
  have hψcc : Continuous fun x => ((deriv ψ x : ℝ) : ℂ) := Complex.continuous_ofReal.comp hψ1c
  have hψ2cc : Continuous fun x => ((deriv (deriv ψ) x : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hψ2c
  have hψ3cc : Continuous fun x => ((deriv (deriv (deriv ψ)) x : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hψ3
  have hne : ∀ x ∈ Icc u v, ((deriv ψ x : ℝ) : ℂ) ≠ 0 := fun x hx =>
    Complex.ofReal_ne_zero.mpr (hψ' x hx).ne'
  have hpow : ∀ n : ℕ, ∀ x ∈ Icc u v, ((deriv ψ x : ℝ) : ℂ) ^ n ≠ 0 := fun n x hx =>
    pow_ne_zero n (hne x hx)
  -- `a` and `a'` vanish at the endpoints
  have hzl : ∀ x < u, a x = 0 := fun x hx => hsupp x fun h => absurd h.1 (not_le.2 hx)
  have hzr : ∀ x > v, a x = 0 := fun x hx => hsupp x fun h => absurd h.2 (not_le.2 hx)
  have hau : a u = 0 := twoIbp_eq_zero_of_left ha.continuous hzl
  have hav : a v = 0 := twoIbp_eq_zero_of_right ha.continuous hzr
  have hda_zl : ∀ x < u, deriv a x = 0 := fun x hx => by
    have hev : a =ᶠ[𝓝 x] fun _ => (0 : ℂ) :=
      Filter.eventually_of_mem (isOpen_Iio.mem_nhds (show x ∈ Iio u from hx))
        (fun y hy => hzl y hy)
    rw [hev.deriv_eq]; simp
  have hda_zr : ∀ x > v, deriv a x = 0 := fun x hx => by
    have hev : a =ᶠ[𝓝 x] fun _ => (0 : ℂ) :=
      Filter.eventually_of_mem (isOpen_Ioi.mem_nhds (show x ∈ Ioi v from hx))
        (fun y hy => hzr y hy)
    rw [hev.deriv_eq]; simp
  have hdau : deriv a u = 0 := twoIbp_eq_zero_of_left hdac hda_zl
  have hdav : deriv a v = 0 := twoIbp_eq_zero_of_right hdac hda_zr
  -- the expanded second derivative `D'`, the derivative of `D = (a/ψ')'/ψ'`
  obtain ⟨D', hD'⟩ : ∃ D' : ℝ → ℂ, ∀ x, D' x = deriv (deriv a) x / ((deriv ψ x : ℝ) : ℂ) ^ 2
      - 3 * deriv a x * ((deriv (deriv ψ) x : ℝ) : ℂ) / ((deriv ψ x : ℝ) : ℂ) ^ 3
      - a x * ((deriv (deriv (deriv ψ)) x : ℝ) : ℂ) / ((deriv ψ x : ℝ) : ℂ) ^ 3
      + 3 * a x * ((deriv (deriv ψ) x : ℝ) : ℂ) ^ 2 / ((deriv ψ x : ℝ) : ℂ) ^ 4 :=
    ⟨fun x => deriv (deriv a) x / ((deriv ψ x : ℝ) : ℂ) ^ 2
      - 3 * deriv a x * ((deriv (deriv ψ) x : ℝ) : ℂ) / ((deriv ψ x : ℝ) : ℂ) ^ 3
      - a x * ((deriv (deriv (deriv ψ)) x : ℝ) : ℂ) / ((deriv ψ x : ℝ) : ℂ) ^ 3
      + 3 * a x * ((deriv (deriv ψ) x : ℝ) : ℂ) ^ 2 / ((deriv ψ x : ℝ) : ℂ) ^ 4, fun x => rfl⟩
  -- first integration by parts, `B = a/ψ'`
  have hBc : ContinuousOn (fun x => a x / ((deriv ψ x : ℝ) : ℂ)) (Icc u v) :=
    ha.continuous.continuousOn.div hψcc.continuousOn hne
  have hBd : ∀ x ∈ Ioo u v \ s, HasDerivAt (fun y => a y / ((deriv ψ y : ℝ) : ℂ))
      (deriv a x / ((deriv ψ x : ℝ) : ℂ) - a x * ((deriv (deriv ψ) x : ℝ) : ℂ) / ((deriv ψ x : ℝ) : ℂ) ^ 2) x := by
    intro x hx
    have hxI : x ∈ Icc u v := Ioo_subset_Icc_self hx.1
    have h1 : HasDerivAt a (deriv a x) x := (hadiff x).hasDerivAt
    have h2 : HasDerivAt (fun y => ((deriv ψ y : ℝ) : ℂ)) ((deriv (deriv ψ) x : ℝ) : ℂ) x :=
      (hψ1d x).hasDerivAt.ofReal_comp
    have h3 := HasDerivAt.div h1 h2 (hne x hxI)
    convert h3 using 1
    field_simp
  have hB'c : ContinuousOn (fun x => deriv a x / ((deriv ψ x : ℝ) : ℂ)
      - a x * ((deriv (deriv ψ) x : ℝ) : ℂ) / ((deriv ψ x : ℝ) : ℂ) ^ 2) (Icc u v) :=
    (hdac.continuousOn.div hψcc.continuousOn hne).sub
      ((ha.continuous.continuousOn.mul hψ2cc.continuousOn).div (hψcc.continuousOn.pow 2) (hpow 2))
  have hB'i : IntervalIntegrable (fun x => deriv a x / ((deriv ψ x : ℝ) : ℂ)
      - a x * ((deriv (deriv ψ) x : ℝ) : ℂ) / ((deriv ψ x : ℝ) : ℂ) ^ 2) volume u v :=
    hB'c.intervalIntegrable_of_Icc huv
  have hI1 : ∫ x in u..v, (a x / ((deriv ψ x : ℝ) : ℂ)) *
        (Complex.I * ((deriv ψ x : ℝ) : ℂ) * Complex.exp (Complex.I * (ψ x : ℂ))) =
      -∫ x in u..v, (deriv a x / ((deriv ψ x : ℝ) : ℂ)
        - a x * ((deriv (deriv ψ) x : ℝ) : ℂ) / ((deriv ψ x : ℝ) : ℂ) ^ 2) *
          Complex.exp (Complex.I * (ψ x : ℂ)) :=
    twoIbp_ibp huv hs hψd hψ1c.continuousOn hBc hBd hB'i (by simp [hau]) (by simp [hav])
  -- second integration by parts, `D = B'/ψ'`
  have hDc : ContinuousOn (fun x => deriv a x / ((deriv ψ x : ℝ) : ℂ) ^ 2
      - a x * ((deriv (deriv ψ) x : ℝ) : ℂ) / ((deriv ψ x : ℝ) : ℂ) ^ 3) (Icc u v) :=
    (hdac.continuousOn.div (hψcc.continuousOn.pow 2) (hpow 2)).sub
      ((ha.continuous.continuousOn.mul hψ2cc.continuousOn).div (hψcc.continuousOn.pow 3) (hpow 3))
  have hDd : ∀ x ∈ Ioo u v \ s, HasDerivAt (fun y => deriv a y / ((deriv ψ y : ℝ) : ℂ) ^ 2
      - a y * ((deriv (deriv ψ) y : ℝ) : ℂ) / ((deriv ψ y : ℝ) : ℂ) ^ 3) (D' x) x := by
    intro x hx
    have hxI : x ∈ Icc u v := Ioo_subset_Icc_self hx.1
    have h1 : HasDerivAt a (deriv a x) x := (hadiff x).hasDerivAt
    have h2 : HasDerivAt (fun y => ((deriv ψ y : ℝ) : ℂ)) ((deriv (deriv ψ) x : ℝ) : ℂ) x :=
      (hψ1d x).hasDerivAt.ofReal_comp
    have h3 : HasDerivAt (fun y => ((deriv (deriv ψ) y : ℝ) : ℂ)) ((deriv (deriv (deriv ψ)) x : ℝ) : ℂ) x :=
      (hψ2d x).hasDerivAt.ofReal_comp
    have h4 : HasDerivAt (deriv a) (deriv (deriv a) x) x := (ha2 x hx.2).hasDerivAt
    have t1 := HasDerivAt.div h4 (h2.pow 2) (pow_ne_zero 2 (hne x hxI))
    have t2 := HasDerivAt.div (h1.mul h3) (h2.pow 3) (pow_ne_zero 3 (hne x hxI))
    convert t1.sub t2 using 1
    rw [hD' x]
    norm_num
    field_simp
    ring
  have hsumI : IntegrableOn (fun x => deriv (deriv a) x / ((deriv ψ x : ℝ) : ℂ) ^ 2
      - 3 * deriv a x * ((deriv (deriv ψ) x : ℝ) : ℂ) / ((deriv ψ x : ℝ) : ℂ) ^ 3
      - a x * ((deriv (deriv (deriv ψ)) x : ℝ) : ℂ) / ((deriv ψ x : ℝ) : ℂ) ^ 3
      + 3 * a x * ((deriv (deriv ψ) x : ℝ) : ℂ) ^ 2 / ((deriv ψ x : ℝ) : ℂ) ^ 4) (Icc u v) := by
    have i1 := twoIbp_integrableOn_div hint (hψcc.continuousOn.pow 2) (hpow 2)
    have n2 : Continuous fun x => 3 * deriv a x * ((deriv (deriv ψ) x : ℝ) : ℂ) :=
      (continuous_const.mul hdac).mul hψ2cc
    have i2 := twoIbp_integrableOn_div (n2.continuousOn.integrableOn_compact isCompact_Icc)
      (hψcc.continuousOn.pow 3) (hpow 3)
    have n3 : Continuous fun x => a x * ((deriv (deriv (deriv ψ)) x : ℝ) : ℂ) :=
      ha.continuous.mul hψ3cc
    have i3 := twoIbp_integrableOn_div (n3.continuousOn.integrableOn_compact isCompact_Icc)
      (hψcc.continuousOn.pow 3) (hpow 3)
    have n4 : Continuous fun x => 3 * a x * ((deriv (deriv ψ) x : ℝ) : ℂ) ^ 2 :=
      (continuous_const.mul ha.continuous).mul (hψ2cc.pow 2)
    have i4 := twoIbp_integrableOn_div (n4.continuousOn.integrableOn_compact isCompact_Icc)
      (hψcc.continuousOn.pow 4) (hpow 4)
    exact ((i1.sub i2).sub i3).add i4
  have hD'Icc : IntegrableOn D' (Icc u v) :=
    hsumI.congr_fun (fun x _ => (hD' x).symm) measurableSet_Icc
  have hD'i : IntervalIntegrable D' volume u v :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le huv).mpr hD'Icc
  have hI2 : ∫ x in u..v, (deriv a x / ((deriv ψ x : ℝ) : ℂ) ^ 2
        - a x * ((deriv (deriv ψ) x : ℝ) : ℂ) / ((deriv ψ x : ℝ) : ℂ) ^ 3) *
        (Complex.I * ((deriv ψ x : ℝ) : ℂ) * Complex.exp (Complex.I * (ψ x : ℂ))) =
      -∫ x in u..v, D' x * Complex.exp (Complex.I * (ψ x : ℂ)) :=
    twoIbp_ibp huv hs hψd hψ1c.continuousOn hDc hDd hD'i (by simp [hdau, hau])
      (by simp [hdav, hav])
  -- the algebraic identities linking the two integrations by parts
  have hA : ∫ x in u..v, a x * Complex.exp (Complex.I * (ψ x : ℂ)) =
      (1 / Complex.I) * ∫ x in u..v, (a x / ((deriv ψ x : ℝ) : ℂ)) *
        (Complex.I * ((deriv ψ x : ℝ) : ℂ) * Complex.exp (Complex.I * (ψ x : ℂ))) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le huv] at hx
    have hx0 := hne x hx
    field_simp
  have hBpt : ∫ x in u..v, (deriv a x / ((deriv ψ x : ℝ) : ℂ)
        - a x * ((deriv (deriv ψ) x : ℝ) : ℂ) / ((deriv ψ x : ℝ) : ℂ) ^ 2) * Complex.exp (Complex.I * (ψ x : ℂ)) =
      (1 / Complex.I) * ∫ x in u..v, (deriv a x / ((deriv ψ x : ℝ) : ℂ) ^ 2
        - a x * ((deriv (deriv ψ) x : ℝ) : ℂ) / ((deriv ψ x : ℝ) : ℂ) ^ 3) *
        (Complex.I * ((deriv ψ x : ℝ) : ℂ) * Complex.exp (Complex.I * (ψ x : ℂ))) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le huv] at hx
    have hx0 := hne x hx
    field_simp
  have hmain : ∫ x in u..v, a x * Complex.exp (Complex.I * (ψ x : ℂ)) =
      -∫ x in u..v, D' x * Complex.exp (Complex.I * (ψ x : ℂ)) := by
    rw [hA, hI1, hBpt, hI2]
    have hI : (1 / Complex.I) ^ 2 = -1 := by
      rw [div_pow, Complex.I_sq]; norm_num
    linear_combination (∫ x in u..v, D' x * Complex.exp (Complex.I * (ψ x : ℂ))) * hI
  -- from the whole line to `[u, v]`
  have hL : ∫ x, a x * Complex.exp (Complex.I * (ψ x : ℂ)) =
      ∫ x in u..v, a x * Complex.exp (Complex.I * (ψ x : ℂ)) := by
    rw [twoIbp_interval_eq_Icc huv]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc u v)
      (f := fun x => a x * Complex.exp (Complex.I * (ψ x : ℂ)))
      (fun x hx => by rw [hsupp x hx, zero_mul])).symm
  have hEn : ∀ x, ‖Complex.exp (Complex.I * (ψ x : ℂ))‖ = 1 := fun x => by
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hpt : ∀ x ∈ Icc u v, ‖D' x‖ ≤ ‖deriv (deriv a) x‖ / deriv ψ x ^ 2
      + 3 * ‖deriv a x‖ * |deriv (deriv ψ) x| / deriv ψ x ^ 3
      + ‖a x‖ * |deriv (deriv (deriv ψ)) x| / deriv ψ x ^ 3
      + 3 * ‖a x‖ * deriv (deriv ψ) x ^ 2 / deriv ψ x ^ 4 := fun x hx => by
    rw [hD' x]
    exact twoIbp_pointwise (a x) (deriv a x) (deriv (deriv a) x) (deriv ψ x)
      (deriv (deriv ψ) x) (deriv (deriv (deriv ψ)) x) (hψ' x hx)
  have hRHS : IntegrableOn (fun x => ‖deriv (deriv a) x‖ / deriv ψ x ^ 2
      + 3 * ‖deriv a x‖ * |deriv (deriv ψ) x| / deriv ψ x ^ 3
      + ‖a x‖ * |deriv (deriv (deriv ψ)) x| / deriv ψ x ^ 3
      + 3 * ‖a x‖ * deriv (deriv ψ) x ^ 2 / deriv ψ x ^ 4) (Icc u v) := by
    have hreal : ∀ x ∈ Icc u v, deriv ψ x ≠ 0 := fun x hx => (hψ' x hx).ne'
    have hpowr : ∀ n : ℕ, ∀ x ∈ Icc u v, deriv ψ x ^ n ≠ 0 := fun n x hx =>
      pow_ne_zero n (hreal x hx)
    have j1 := twoIbp_integrableOn_div_real hint.norm (hψ1c.continuousOn.pow 2) (hpowr 2)
    have n2 : Continuous fun x => 3 * ‖deriv a x‖ * |deriv (deriv ψ) x| :=
      (continuous_const.mul hdac.norm).mul hψ2c.abs
    have j2 := twoIbp_integrableOn_div_real (n2.continuousOn.integrableOn_compact isCompact_Icc)
      (hψ1c.continuousOn.pow 3) (hpowr 3)
    have n3 : Continuous fun x => ‖a x‖ * |deriv (deriv (deriv ψ)) x| :=
      ha.continuous.norm.mul hψ3.abs
    have j3 := twoIbp_integrableOn_div_real (n3.continuousOn.integrableOn_compact isCompact_Icc)
      (hψ1c.continuousOn.pow 3) (hpowr 3)
    have n4 : Continuous fun x => 3 * ‖a x‖ * deriv (deriv ψ) x ^ 2 :=
      (continuous_const.mul ha.continuous.norm).mul (hψ2c.pow 2)
    have j4 := twoIbp_integrableOn_div_real (n4.continuousOn.integrableOn_compact isCompact_Icc)
      (hψ1c.continuousOn.pow 4) (hpowr 4)
    exact ((j1.add j2).add j3).add j4
  calc ‖∫ x, a x * Complex.exp (Complex.I * (ψ x : ℂ))‖
      = ‖∫ x in u..v, a x * Complex.exp (Complex.I * (ψ x : ℂ))‖ := by rw [hL]
    _ = ‖∫ x in u..v, D' x * Complex.exp (Complex.I * (ψ x : ℂ))‖ := by rw [hmain, norm_neg]
    _ ≤ ∫ x in u..v, ‖D' x * Complex.exp (Complex.I * (ψ x : ℂ))‖ :=
        intervalIntegral.norm_integral_le_integral_norm huv
    _ = ∫ x in u..v, ‖D' x‖ := by simp only [norm_mul, hEn, mul_one]
    _ = ∫ x in Icc u v, ‖D' x‖ := twoIbp_interval_eq_Icc huv _
    _ ≤ ∫ x in Icc u v, (‖deriv (deriv a) x‖ / deriv ψ x ^ 2
        + 3 * ‖deriv a x‖ * |deriv (deriv ψ) x| / deriv ψ x ^ 3
        + ‖a x‖ * |deriv (deriv (deriv ψ)) x| / deriv ψ x ^ 3
        + 3 * ‖a x‖ * deriv (deriv ψ) x ^ 2 / deriv ψ x ^ 4) :=
        integral_mono_of_nonneg
          ((ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ fun x _ => norm_nonneg _))
          hRHS
          ((ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ fun x hx => hpt x hx))

/-- info: 'FormalResearch.CohnElkies.two_ibp_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.two_ibp_phase

end FormalResearch.CohnElkies
