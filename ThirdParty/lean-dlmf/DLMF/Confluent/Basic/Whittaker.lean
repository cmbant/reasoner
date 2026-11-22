/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.KummerProperties

/-!
# Whittaker functions: definitions and Whittaker's equation

Whittaker's functions `M_{κ,μ}` and `W_{κ,μ}` are the standard pair of solutions of
Whittaker's equation (DLMF §13.14, AAR §4.3), written in terms of Kummer's `M` and the
continued Tricomi `U`.

## Main definitions

* `whittakerM`: Whittaker's `M_{κ,μ}(z)` (DLMF 13.14.2).
* `regularizedWhittakerM`: `M_{κ,μ}` regularized in its second parameter, meaningful also at
  `1 + 2μ = -n`.
* `whittakerW`: Whittaker's principal-branch `W_{κ,μ}(z)` (DLMF 13.14.3).
* `whittakerMOnLog`: Whittaker M on the logarithmic argument plane.
* `whittakerWConnectionOnLog`: the noninteger-twice-order connection expression.
  The full-parameter function is `whittakerWContinuedOnLog` in `Basic.WhittakerLogarithmic`.

## Main results

* `whittakerM_ode`, `whittakerW_ode`: Whittaker's equation (DLMF 13.14.1).
* `analyticAt_whittakerM`: `M_{κ,μ}` is analytic on the slit plane.
* `whittakerW_eq_connection`: the connection formula for `W` (DLMF 13.14.33).
* `whittakerW_eq_kummerU`: the definition of `W` through Tricomi's `U` (DLMF 13.14.3).
* `regularizedWhittakerM_eq_div_Gamma`, `whittakerW_half_zero`: elementary values.

## Implementation notes

The `OnLog` definitions retain the logarithmic argument for monodromy; ordinary multiplication
of the complex argument by `exp (2πi)` would lose that information. The relations to Kummer's
functions, continuation, Wronskians and jumps are in `DLMF.Confluent.Whittaker`.
-/

public section

open Complex Filter
open scoped Real Topology
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent
/-- Whittaker's `M_{κ,μ}(z)`. -/
@[expose,
  dlmf 13.14.E2]
def whittakerM (κ μ z : ℂ) : ℂ :=
  exp (-z / 2) * z ^ (μ + 1 / 2) * kummerM (μ - κ + 1 / 2) (1 + 2 * μ) z

/-- Whittaker M regularized in its second parameter. This remains meaningful at
`1 + 2 * μ = -n`, where dividing the totalized ordinary M by Gamma would give zero. -/
@[expose]
def regularizedWhittakerM (κ μ z : ℂ) : ℂ :=
  exp (-z / 2) * z ^ (μ + 1 / 2) *
    regularizedHGFun {μ - κ + 1 / 2} {1 + 2 * μ} z

/-- Away from Gamma poles, regularized Whittaker M agrees with the ordinary quotient. -/
theorem regularizedWhittakerM_eq_div_Gamma {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -(k : ℂ)) :
    regularizedWhittakerM κ μ z = whittakerM κ μ z / Gamma (1 + 2 * μ) := by
  rw [whittakerM, kummerM_eq_mul_regularizedHGFun hμ]
  unfold regularizedWhittakerM
  field_simp [Gamma_ne_zero hμ]

/-- Whittaker's principal-branch W, defined through the continued Tricomi function. -/
@[expose,
  dlmf 13.14.E3]
def whittakerW (κ μ z : ℂ) : ℂ :=
  exp (-z / 2) * z ^ (1 / 2 + μ) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) z

/-- At `κ = 1/2` and `μ = 0`, the principal Whittaker function is `exp(-z/2) z^(1/2)`. -/
theorem whittakerW_half_zero (z : ℂ) :
    whittakerW (1 / 2) 0 z = exp (-z / 2) * z ^ (1 / 2 : ℂ) := by
  norm_num [whittakerW, kummerU_zero]

/-- Whittaker's M on the logarithmic argument plane, which records full turns around zero. -/
@[expose]
def whittakerMOnLog (κ μ w : ℂ) : ℂ :=
  exp (-exp w / 2) * exp ((μ + 1 / 2) * w) *
    kummerM (μ - κ + 1 / 2) (1 + 2 * μ) (exp w)

/-- Whittaker's W connection formula on the logarithmic argument plane.
It represents W when `2 * μ` is not an integer. -/
@[expose]
def whittakerWConnectionOnLog (κ μ w : ℂ) : ℂ :=
  Gamma (-2 * μ) / Gamma (1 / 2 - μ - κ) * whittakerMOnLog κ μ w +
    Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) * whittakerMOnLog κ (-μ) w


/-- The logarithmic connection expression in terms of the two Kummer solutions.
DLMF 13.14.33 applies to noninteger twice-order. -/
theorem whittakerWConnectionOnLog_def (κ μ w : ℂ) :
    whittakerWConnectionOnLog κ μ w =
      Gamma (-2 * μ) / Gamma (1 / 2 - μ - κ) * whittakerMOnLog κ μ w +
        Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) * whittakerMOnLog κ (-μ) w := rfl

/-- At order zero the raw totalized connection expression is zero.
The continued Whittaker W uses the whole parameter limit instead.
DLMF 13.14.33 is a noninteger-twice-order formula. -/
@[simp] theorem whittakerWConnectionOnLog_zero (κ w : ℂ) :
    whittakerWConnectionOnLog κ 0 w = 0 := by
  simp [whittakerWConnectionOnLog]

/-- Logarithmic derivative of the prefactor in Whittaker's `M`. -/
theorem hasDerivAt_whittakerPrefactor (r : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun w : ℂ => exp (-w / 2) * w ^ r)
      (exp (-z / 2) * z ^ r * (r / z - 1 / 2)) z := by
  have hd := (((hasDerivAt_id z).neg.div_const 2).cexp).mul
    ((hasDerivAt_id z).cpow_const (c := r) hz)
  convert! hd using 1
  simp only [id_eq, Pi.neg_apply, mul_one]
  rw [cpow_sub _ _ (slitPlane_ne_zero hz), cpow_one]
  field_simp
  ring

/-- Whittaker's equation (AAR §4.3). -/
@[dlmf 13.14.E1]
theorem whittakerM_ode {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    iteratedDeriv 2 (whittakerM κ μ) z +
      (-1 / 4 + κ / z + (1 / 4 - μ ^ 2) / z ^ 2) * whittakerM κ μ z = 0 := by
  let r := μ + 1 / 2
  let y := kummerM (μ - κ + 1 / 2) (1 + 2 * μ)
  let g := fun w : ℂ => exp (-w / 2) * w ^ r
  let q := fun w : ℂ => r / w - 1 / 2
  have hf := hasFPowerSeriesOnBall_kummerM (a := μ - κ + 1 / 2) hμ
  have hy (w : ℂ) : HasDerivAt y (deriv y w) w :=
    (hf.analyticAt_of_mem (y := w) (by simp)).differentiableAt.hasDerivAt
  have hy' : HasDerivAt (deriv y) (iteratedDeriv 2 y z) z := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      (hf.analyticAt_of_mem (y := z) (by simp)).deriv.differentiableAt.hasDerivAt
  have hg (w : ℂ) (hw : w ∈ slitPlane) : HasDerivAt g (g w * q w) w :=
    hasDerivAt_whittakerPrefactor r hw
  have hq : HasDerivAt q (-r / z ^ 2) z := by
    convert! ((hasDerivAt_const z r).div (hasDerivAt_id z) (slitPlane_ne_zero hz)).sub_const
      (1 / 2) using 1
    simp
  have hfirst (w : ℂ) (hw : w ∈ slitPlane) :
      deriv (whittakerM κ μ) w = g w * (deriv y w + q w * y w) := by
    have hd := (hg w hw).mul (hy w)
    change deriv (g * y) w = _
    rw [hd.deriv]
    ring
  have heq : deriv (whittakerM κ μ) =ᶠ[𝓝 z]
      (g * (deriv y + q * y)) :=
    Filter.eventually_of_mem (isOpen_slitPlane.mem_nhds hz) hfirst
  have hsecond := (hg z hz).mul (hy'.add (hq.mul (hy z)))
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero,
    heq.deriv_eq, hsecond.deriv]
  have hode := kummerM_ode (a := μ - κ + 1 / 2) (z := z) hμ
  change z * iteratedDeriv 2 y z + (1 + 2 * μ - z) * deriv y z -
    (μ - κ + 1 / 2) * y z = 0 at hode
  change _ + _ * (g z * y z) = 0
  dsimp [q, r]
  field_simp [slitPlane_ne_zero hz]
  linear_combination (16 * z * g z) * hode

/-- Whittaker's `M` is analytic away from the principal power's branch cut. -/
theorem analyticAt_whittakerM {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) : AnalyticAt ℂ (whittakerM κ μ) z := by
  unfold whittakerM
  apply AnalyticAt.mul
  · apply AnalyticAt.mul
    · fun_prop
    · exact analyticAt_id.cpow analyticAt_const hz
  · exact (hasFPowerSeriesOnBall_kummerM (a := μ - κ + 1 / 2) hμ).analyticAt_of_mem
      (by simp)

/-- The generic connection formula for W; the integer case uses continuation. -/
@[dlmf 13.14.E33]
theorem whittakerW_eq_connection {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℤ, 2 * μ ≠ k) :
    whittakerW κ μ z =
      Gamma (-2 * μ) / Gamma (1 / 2 - μ - κ) * whittakerM κ μ z +
        Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) * whittakerM κ (-μ) z := by
  have hb : ∀ k : ℤ, (1 : ℂ) + 2 * μ ≠ k := by
    intro k hk
    apply hμ (k - 1)
    push_cast
    linear_combination hk
  unfold whittakerW
  rw [kummerU_eq_connection _ _ _ hb]
  unfold kummerUConnection whittakerM
  symm
  have hz0 := slitPlane_ne_zero hz
  have h1b : (1 : ℂ) - (1 + 2 * μ) = -2 * μ := by ring
  have hb1 : (1 + 2 * μ : ℂ) - 1 = 2 * μ := by ring
  have hab : (1 / 2 + μ - κ : ℂ) - (1 + 2 * μ) + 1 = 1 / 2 - μ - κ := by ring
  have h2b : (2 : ℂ) - (1 + 2 * μ) = 1 - 2 * μ := by ring
  have hMμ : (μ : ℂ) - κ + 1 / 2 = 1 / 2 + μ - κ := by ring
  have hMμ' : (-μ : ℂ) - κ + 1 / 2 = 1 / 2 - μ - κ := by ring
  have hden : (1 : ℂ) + 2 * (-μ) = 1 - 2 * μ := by ring
  have hpow : z ^ (1 / 2 + μ) * z ^ (-2 * μ) = z ^ (1 / 2 - μ) := by
    rw [← cpow_add _ _ hz0]
    ring_nf
  simp only [h1b, hb1, hab, h2b, hMμ, hMμ', hden]
  rw [mul_add]
  have hswap :
      exp (-z / 2) * z ^ (1 / 2 + μ) *
          (Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) * z ^ (-2 * μ) *
            kummerM (1 / 2 - μ - κ) (1 - 2 * μ) z) =
        Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) *
          (exp (-z / 2) * z ^ (1 / 2 - μ) * kummerM (1 / 2 - μ - κ) (1 - 2 * μ) z) := by
    calc
      _ = Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) * exp (-z / 2) *
            (z ^ (1 / 2 + μ) * z ^ (-2 * μ)) *
            kummerM (1 / 2 - μ - κ) (1 - 2 * μ) z := by ring
      _ = _ := by rw [hpow]; ring
  rw [hswap]
  ring_nf

/-- Whittaker's `W` satisfies the same equation. -/
@[dlmf 13.14.E1]
theorem whittakerW_ode {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℤ, 2 * μ ≠ k) :
    iteratedDeriv 2 (whittakerW κ μ) z +
      (-1 / 4 + κ / z + (1 / 4 - μ ^ 2) / z ^ 2) * whittakerW κ μ z = 0 := by
  have hpos : ∀ k : ℕ, 1 + 2 * μ ≠ -k := by
    intro k hk
    apply hμ (-(k : ℤ) - 1)
    push_cast
    linear_combination hk
  have hneg : ∀ k : ℕ, 1 + 2 * (-μ) ≠ -k := by
    intro k hk
    apply hμ ((k : ℤ) + 1)
    push_cast
    linear_combination -hk
  have hp := whittakerM_ode (κ := κ) hz hpos
  have hn := whittakerM_ode (κ := κ) hz hneg
  have hap := (analyticAt_whittakerM (κ := κ) hz hpos).contDiffAt (n := 2)
  have han := (analyticAt_whittakerM (κ := κ) hz hneg).contDiffAt (n := 2)
  have heq : whittakerW κ μ =ᶠ[𝓝 z] (fun w =>
      Gamma (-2 * μ) / Gamma (1 / 2 - μ - κ) * whittakerM κ μ w +
        Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) * whittakerM κ (-μ) w) :=
    Filter.eventually_of_mem (isOpen_slitPlane.mem_nhds hz) fun w hw =>
      whittakerW_eq_connection hw hμ
  rw [heq.iteratedDeriv_eq 2, whittakerW_eq_connection hz hμ]
  rw [iteratedDeriv_fun_add (contDiffAt_const.mul hap) (contDiffAt_const.mul han),
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  linear_combination
    Gamma (-2 * μ) / Gamma (1 / 2 - μ - κ) * hp +
      Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) * hn

/-- The definition of W through the continued Tricomi function. -/
@[dlmf 13.14.E3]
theorem whittakerW_eq_kummerU {κ μ z : ℂ} :
    whittakerW κ μ z =
      exp (-z / 2) * z ^ (1 / 2 + μ) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) z := by
  rfl

/-- Compatibility spelling for the noninteger logarithmic connection expression. -/
@[deprecated whittakerWConnectionOnLog (since := "2026-11-14")]
noncomputable abbrev whittakerWOnLog (κ μ w : ℂ) : ℂ := whittakerWConnectionOnLog κ μ w

end DLMF.Confluent
