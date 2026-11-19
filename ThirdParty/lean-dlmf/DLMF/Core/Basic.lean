/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.SegmentPrimitive
public import Mathlib.Algebra.ContinuedFractions.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

/-!
# Shared conventions for convergence, primitives and branches

This file fixes the conventions shared by the special-function areas: improper integrals,
principal values, straight-segment primitives, sector filters, finite continued fractions,
ordered zeros and successively extracted asymptotic coefficients. The declarations live in the
namespace `DLMF.Core`; files that use them `open DLMF.Core`.

## Main definitions

* `HasIntegralAtTop`, `HasIntegralAtBot`, `HasIntegralWholeLine`: improper integrals on
  half-lines and on the whole line, including convergence.
* `improperAtTop`: the value of a convergent tail.
* `HasPrincipalValueIoi`: a symmetric principal value at an interior point of a half-line.
* `segmentIntegral`, `primitive`: integrals along straight complex segments and the primitive
  based at zero of an entire integrand.
* `sector`, `logSector`: uniform approach to infinity in a closed sector, on the principal sheet
  and on the logarithmic plane.
* `continuedFractionContinuants`, `continuedFractionTail`, `HasContinuedFraction`: finite continued
  fractions and their convergence.
* `oddProduct`: the odd product `1·3···(2n+1)`.
* `orderedZero`: a zero selected by the number of strictly closer zeros.
* `asymptoticCoeff`: coefficients extracted successively by limits at positive infinity.

## Main results

* `primitive_eq_sub`, `segmentIntegral_eq_sub`: an entire antiderivative evaluates segment
  integrals.
* `hasDerivAt_primitive`, `differentiable_primitive`: primitives of entire functions are
  entire, with the expected derivative.
* `hasSum_primitive_monomials`: a globally convergent monomial series may be integrated term by
  term along a straight segment.
* `primitive_ofReal`: the segment convention agrees with interval integration on the real axis.

## Implementation notes

Improper integrals assert limits of finite integrals. Logarithmic coordinates retain
continuation across cuts. Continued fractions assert convergence of finite truncations, rather
than an equality to a totalized infinite expression. Existence of an ordered zero, and of the
limits defining `asymptoticCoeff`, must be established by separate theorems.
-/

public noncomputable section
open Complex Filter Set MeasureTheory
open scoped Real Topology
namespace DLMF.Core

/-- Improper integral on a right half-line, including convergence. -/
@[expose]
def HasIntegralAtTop (f : ℝ → ℂ) (a : ℝ) (v : ℂ) : Prop :=
  Tendsto (fun R => ∫ t in a..R, f t) atTop (𝓝 v)
/-- Improper integral on a left half-line, including convergence. -/
@[expose]
def HasIntegralAtBot (f : ℝ → ℂ) (a : ℝ) (v : ℂ) : Prop :=
  Tendsto (fun R => ∫ t in R..a, f t) atBot (𝓝 v)
/-- Convergence of both tails separately. -/
@[expose]
def HasIntegralWholeLine (f : ℝ → ℂ) (v : ℂ) : Prop :=
  ∃ u w, HasIntegralAtBot f 0 u ∧ HasIntegralAtTop f 0 w ∧ u + w = v
/-- Value of a convergent tail, with convergence always asserted separately. -/
@[expose]
def improperAtTop (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  limUnder atTop (fun R => ∫ t in a..R, f t)
/-- Symmetric principal value at the interior point of a right half-line. -/
@[expose]
def HasPrincipalValueIoi (f : ℝ → ℂ) (a c : ℝ) (v : ℂ) : Prop :=
  a < c ∧
  (∀ ε > 0, HasIntegralAtTop f (c + ε) (improperAtTop f (c + ε))) ∧
  Tendsto (fun ε : ℝ => (∫ t in a..c-ε, f t) + improperAtTop f (c+ε))
    (𝓝[>] (0 : ℝ)) (𝓝 v)
/-- Straight complex segment with its Jacobian. -/
@[expose]
def segmentIntegral (f : ℂ → ℂ) (a b : ℂ) : ℂ :=
  (b-a) * ∫ t : ℝ in 0..1, f (a + t * (b-a))
/-- Primitive based at zero of an entire integrand. -/
@[expose]
def primitive (f : ℂ → ℂ) (z : ℂ) : ℂ := segmentIntegral f 0 z
/-- The straight-segment primitive equals any entire antiderivative minus its base value. -/
theorem primitive_eq_sub {f g : ℂ → ℂ}
    (hg : ∀ z, HasDerivAt g (f z) z) (z : ℂ) :
    primitive f z=g z-g 0 := by
  simpa [primitive, segmentIntegral] using Complex.mul_integral_comp_mul_eq_sub hg z

/-- An entire antiderivative evaluates the integral on any straight segment. -/
theorem segmentIntegral_eq_sub {f g : ℂ → ℂ}
    (hg : ∀ z, HasDerivAt g (f z) z) (a b : ℂ) :
    segmentIntegral f a b=g b-g a := by
  have hd (w : ℂ) : HasDerivAt (fun u => g (a+u)) (f (a+w)) w := by
    convert! (hg (a+w)).comp w ((hasDerivAt_id w).const_add a) using 1
    simp
  have h := Complex.mul_integral_comp_mul_eq_sub (f:=fun w=>f (a+w))
    hd (b-a)
  simpa [segmentIntegral] using h

/-- A globally convergent complex monomial series may be integrated along a straight segment.
Its norm summability on every real radius follows from the global `HasSum` hypothesis. -/
theorem hasSum_primitive_monomials {f : ℂ → ℂ} (c : ℕ → ℂ) (d : ℕ → ℕ)
    (hs : ∀ z, HasSum (fun n=>c n*z^(d n)) (f z))
    (z : ℂ) :
    HasSum (fun n=>c n*z^(d n+1)/(d n+1:ℂ)) (primitive f z) := by
  have hb (R : ℝ) (hR : 0 ≤ R) : Summable (fun n => ‖c n‖ * R ^ d n) := by
    simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hR] using
      (hs (R : ℂ)).summable.norm
  let F : ℕ → ℝ → ℂ := fun n t=>c n*((t:ℂ)*z)^(d n)
  let B : ℕ → ℝ → ℝ := fun n _=>‖c n‖*‖z‖^(d n)
  have hF (n : ℕ) : Continuous (F n) := by dsimp [F]; fun_prop
  have hi := intervalIntegral.hasSum_integral_of_dominated_convergence (μ:=volume) (a:=0) (b:=1) B
    (fun n=>(hF n).aestronglyMeasurable)
    (fun n=>ae_of_all _ fun t ht=>by
      have ht' : t∈Ioc (0:ℝ) 1 := by simpa using ht
      have ht1 : ‖(t:ℂ)‖≤1 := by
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht'.1]; exact ht'.2
      simp only [F,B,norm_mul,norm_pow]
      calc
        ‖c n‖*(‖(t:ℂ)‖*‖z‖)^(d n) ≤ ‖c n‖*(1*‖z‖)^(d n) := by gcongr
        _ = _ := by rw [one_mul])
    (ae_of_all _ fun _ _=>hb ‖z‖ (norm_nonneg _))
    (by dsimp only [B]; exact intervalIntegrable_const)
    (ae_of_all _ fun t _=>hs ((t:ℂ)*z))
  have hp (m : ℕ) : (∫ t : ℝ in 0..1, (t:ℂ)^m)=1/(m+1:ℂ) := by
    simp_rw [← Complex.ofReal_pow]
    rw [intervalIntegral.integral_ofReal,integral_pow]
    norm_num
  have he (n : ℕ) : z*(∫ t : ℝ in 0..1,F n t)=c n*z^(d n+1)/(d n+1:ℂ) := by
    simp only [F,mul_pow]
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_mul_const,hp,pow_succ]
    ring
  have h := hi.mul_left z
  simp_rw [he] at h
  simpa [primitive,segmentIntegral] using h

/-- Entire integrands have the expected derivative under the straight-segment convention. -/
theorem hasDerivAt_primitive {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    HasDerivAt (primitive f) (f z) z := by
  have he : primitive f = fun w => w*(∫ t : ℝ in 0..1, f (t*w)) := by
    funext w
    simp [primitive, segmentIntegral]
  rw [he]
  exact Complex.hasDerivAt_mul_integral_comp_mul hf z

/-- Straight-segment primitives of entire functions are entire. -/
theorem differentiable_primitive {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (primitive f) := fun z => (hasDerivAt_primitive hf z).differentiableAt

/-- Filling in a removable quotient at the origin does not change a segment integral. -/
theorem primitive_dslope_zero {f : ℂ → ℂ} (hf0 : f 0=0) (z : ℂ) :
    primitive (dslope f 0) z=primitive (fun t=>f t/t) z := by
  by_cases hz : z=0
  · subst z; simp [primitive,segmentIntegral]
  simp only [primitive,segmentIntegral,sub_zero,zero_add]
  congr 1
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ t : ℝ, t≠0 := by simp [MeasureTheory.ae_iff]
  filter_upwards [hne] with t ht _
  rw [dslope_of_ne _ (mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) hz),slope_def_field,hf0]
  simp

/-- The straight-segment convention agrees with interval integration on the real axis. -/
theorem primitive_ofReal (f : ℂ → ℂ) (x : ℝ) :
    primitive f x=∫ t : ℝ in 0..x, f t := by
  have h := intervalIntegral.smul_integral_comp_mul_right (fun t : ℝ => f t)
    (a:=0) (b:=1) x
  simpa [primitive, segmentIntegral, Complex.real_smul] using h

/-- The based primitive vanishes at its base point. -/
@[simp] theorem primitive_zero (f : ℂ → ℂ) : primitive f 0=0 := by
  simp [primitive, segmentIntegral]

/-- Uniform approach to infinity in a closed principal sector. -/
@[expose]
def sector (α : ℝ) : Filter ℂ :=
  comap norm atTop ⊓ 𝓟 {z : ℂ | z ≠ 0 ∧ |arg z| ≤ α}
/-- Uniform approach to infinity in a closed sector on the logarithmic plane. -/
@[expose]
def logSector (α : ℝ) : Filter ℂ :=
  comap (fun w : ℂ => Real.exp w.re) atTop ⊓ 𝓟 {w : ℂ | |w.im| ≤ α}
/-- Numerator, denominator and termination flag of a finite continued fraction.
Mathlib’s `GenContFract.nextConts` supplies the recurrence. Continuants avoid
nested division by an intermediate zero. A zero numerator
at a positive index terminates the fraction and freezes subsequent convergents. -/
@[expose]
def continuedFractionContinuants (a b : ℕ → ℂ) (k : ℕ) : ℕ → ℂ × ℂ × Bool
  | 0 => (0, 1, false)
  | 1 => (a k, b k, false)
  | n+2 =>
    let u := continuedFractionContinuants a b k (n+1)
    let v := continuedFractionContinuants a b k n
    if u.2.2 = true ∨ a (k+n+1) = 0 then (u.1, u.2.1, true)
    else
      let p := GenContFract.nextConts (a (k+n+1)) (b (k+n+1))
        ⟨v.1, v.2.1⟩ ⟨u.1, u.2.1⟩
      (p.a, p.b, false)
/-- Finite continued fraction as a ratio of continuants, with exact termination. -/
@[expose]
def continuedFractionTail (a b : ℕ → ℂ) (k N : ℕ) : ℂ :=
  let p := continuedFractionContinuants a b k N
  p.1/p.2.1
/-- Convergence of the specified finite continued fractions. -/
@[expose]
def HasContinuedFraction (a b : ℕ → ℂ) (v : ℂ) : Prop :=
  Tendsto (continuedFractionTail a b 0) atTop (𝓝 v)
/-- The odd product 1·3···(2n+1). -/
@[expose]
def oddProduct (n : ℕ) : ℂ := ∏ j ∈ Finset.range (n+1), (2*j+1 : ℂ)
/-- A zero chosen by the count of strictly closer zeros; existence is a theorem. -/
@[expose]
def orderedZero (f : ℂ → ℂ) (S : Set ℂ) (k : ℕ) : ℂ :=
  Classical.epsilon (fun z => z ∈ S ∧ f z = 0 ∧
    ({w : ℂ | w ∈ S ∧ f w = 0 ∧ ‖w‖ < ‖z‖} : Set ℂ).ncard = k-1)

/-- Coefficients extracted successively by limits at positive infinity.
Theorems asserting expansions must separately establish that these limits exist. -/
@[expose]
def asymptoticCoeff (f : ℝ → ℂ) : ℕ → ℂ
  | 0 => limUnder atTop f
  | n+1 => limUnder atTop (fun t : ℝ => (t : ℂ)^(n+1) *
      (f t-∑ j ∈ Finset.range (n+1), asymptoticCoeff f (n-j)*(t : ℂ)^(-((n-j : ℕ) : ℤ))))
termination_by n => n

end DLMF.Core
