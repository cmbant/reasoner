/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.LiouvilleGreenExpansion

/-!
# Liouville–Green approximation with errors controlled from a finite endpoint

Following F. W. J. Olver, *Asymptotics and Special Functions*, Ch. 6, §2 and Ch. 10, §3, this
file treats the solutions of

`w'' = (k² A⁻⁴ + g) w`

that are characterized at a finite point `a₁` rather than at `+∞`. The setting is an open
order-connected set `S ∋ a₁` (an open interval, bounded or not), and all error bounds involve the
variation `V_{a₁,x}` of the error-control function over `[a₁, x]`. This complements the
recessive solutions of `DLMFMathlib.Analysis.ODE.LiouvilleGreen` and
`DLMFMathlib.Analysis.ODE.LiouvilleGreenExpansion`, whose errors are controlled from `+∞`.

## Main definitions

* `leftVolterraOp`: the Volterra operator `h ↦ ∫_{(a₁,x]} K x t ψ t h t dt` with a rank-two
  kernel `K x t = p₁ x q₁ t + p₂ x q₂ t`.

## Main results

* `exists_solution_expansion_dominant_exp_finite_endpoint`: the **dominant** exponential
  solution `A exp (u ξ) (∑ A_s/u^s + ε)` (Olver, Ch. 6, Thm. 2.1 and Ch. 10, Thm. 3.1 with
  reference point `a₁`).

## Implementation notes

The private supporting results include: the Volterra equation
`h x = σ x + ∫_{(a₁,x]} K x t ψ t h t dt`, solved by Picard iteration with the bound
`‖h - σ‖ ≤ B (exp (∫_{a₁}^x ρ) - 1)` (Olver, Ch. 6, Thm. 10.1, in the form used for finite
reference points); solutions `w = A E (P + ε)` with `‖ε‖ ≤ κ W exp (κ V)`, `W x = ∫_{a₁}^x ‖r‖`,
built from an arbitrary approximant `P` and from truncated Liouville–Green series; the
**oscillatory** solutions `A exp (-i u ξ) (∑ (-1)^s A_s/(iu)^s + ε)` controlled from a finite
point (Olver, Ch. 6, Thm. 2.2 and Ch. 10, §3); and constancy of Wronskians and the
two-dimensionality of the solution space on an open interval.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Ch. 6 and Ch. 10.
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace LiouvilleGreen

section Primitive

variable {E : Type*} [NormedAddCommGroup E]
variable {S : Set ℝ} {a₁ : ℝ}

/-- In an order-connected set containing `a₁`, the interval `[a₁, x]` lies in the set. -/
private lemma Icc_subset_of_ordConnected (hSc : S.OrdConnected) (ha : a₁ ∈ S) {x : ℝ} (hx : x ∈ S) :
    Icc a₁ x ⊆ S :=
  hSc.out ha hx

/-- `uIcc a₁ x ⊆ S` in an order-connected set. -/
private lemma uIcc_subset_of_ordConnected (hSc : S.OrdConnected) (ha : a₁ ∈ S)
    {x : ℝ} (hx : x ∈ S) :
    uIcc a₁ x ⊆ S :=
  hSc.uIcc_subset ha hx

/-- A function continuous on an order-connected `S ∋ a₁` is integrable on `(a₁, x]`. -/
private lemma integrableOn_Ioc_of_continuousOn {f : ℝ → E} (hSc : S.OrdConnected) (ha : a₁ ∈ S)
    (hf : ContinuousOn f S) {x : ℝ} (hx : x ∈ S) : IntegrableOn f (Ioc a₁ x) :=
  ((hf.mono (Icc_subset_of_ordConnected hSc ha hx)).integrableOn_compact isCompact_Icc).mono_set
    Ioc_subset_Icc_self

/-- The derivative of a primitive `y ↦ ∫_{a₁}^y f` at a point of an open order-connected set on
which `f` is continuous. -/
private lemma hasDerivAt_intervalIntegral_of_continuousOn [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hS : IsOpen S)
    (hSc : S.OrdConnected) (ha : a₁ ∈ S) (hf : ContinuousOn f S) {x : ℝ} (hx : x ∈ S) :
    HasDerivAt (fun y => ∫ t in a₁..y, f t) (f x) x :=
  intervalIntegral.integral_hasDerivAt_right
    ((hf.mono (uIcc_subset_of_ordConnected hSc ha hx)).intervalIntegrable)
    (hf.stronglyMeasurableAtFilter hS x hx) (hf.continuousAt (hS.mem_nhds hx))

/-- A primitive `y ↦ ∫_{(a₁, y]} f` of a function integrable on every `(a₁, x]`, `x ∈ S`, is
continuous on `S ∩ [a₁, ∞)` when `S` is open and order-connected. -/
private lemma continuousOn_setIntegral_Ioc [NormedSpace ℝ E] {f : ℝ → E} (hS : IsOpen S)
    (hf : ∀ x ∈ S, IntegrableOn f (Ioc a₁ x)) :
    ContinuousOn (fun y => ∫ t in Ioc a₁ y, f t) (S ∩ Ici a₁) := by
  intro y ⟨hyS, hy⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hS y hyS
  set b := y + ε / 2 with hb
  have hbS : b ∈ S := hball (by
    rw [Metric.mem_ball, Real.dist_eq, hb, show y + ε / 2 - y = ε / 2 by ring,
      abs_of_pos (by linarith)]
    linarith)
  have hyb : y < b := by rw [hb]; linarith
  have hab : a₁ ≤ b := le_trans (mem_Ici.1 hy) hyb.le
  have hprim : ContinuousOn (fun z => ∫ t in a₁..z, f t) (uIcc a₁ b) :=
    intervalIntegral.continuousOn_primitive_interval (by
      rw [uIcc_of_le hab]
      exact (integrableOn_Icc_iff_integrableOn_Ioc).2 (hf b hbS))
  rw [uIcc_of_le hab] at hprim
  have hcw : ContinuousWithinAt (fun z => ∫ t in Ioc a₁ z, f t) (Icc a₁ b) y :=
    (hprim y ⟨hy, hyb.le⟩).congr (fun z hz => (intervalIntegral.integral_of_le hz.1).symm)
      (intervalIntegral.integral_of_le hy).symm
  refine hcw.mono_of_mem_nhdsWithin ?_
  exact mem_nhdsWithin.2 ⟨Iio b, isOpen_Iio, hyb, fun z hz => ⟨hz.2.2, hz.1.le⟩⟩

end Primitive

section Head

variable {ρ : ℝ → ℝ} {S : Set ℝ} {a₁ : ℝ}

/-- The head integral `∫_{a₁}^x ρ` of a nonnegative function is nonnegative. -/
private lemma intervalIntegral_nonneg_of_nonneg_on (hρ0 : ∀ t ∈ S, a₁ < t → 0 ≤ ρ t)
    (hSc : S.OrdConnected) (ha : a₁ ∈ S)
    {x : ℝ} (hx : x ∈ S) (hax : a₁ ≤ x) : 0 ≤ ∫ t in a₁..x, ρ t :=
  by
  rw [intervalIntegral.integral_of_le hax]
  exact setIntegral_nonneg measurableSet_Ioc fun t ht =>
    hρ0 t (Icc_subset_of_ordConnected hSc ha hx (Ioc_subset_Icc_self ht)) ht.1

/-- The head integral `∫_{a₁}^x ρ` of a nonnegative function is monotone in `x`. -/
private lemma intervalIntegral_mono_upper_of_nonneg (hρ0 : ∀ t ∈ S, a₁ < t → 0 ≤ ρ t)
    (hSc : S.OrdConnected) (ha : a₁ ∈ S)
    (hρc : ContinuousOn ρ S) {x y : ℝ} (hy : y ∈ S) (hax : a₁ ≤ x) (hxy : x ≤ y) :
    ∫ t in a₁..x, ρ t ≤ ∫ t in a₁..y, ρ t := by
  have hxS : x ∈ S := Icc_subset_of_ordConnected hSc ha hy ⟨hax, hxy⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := x)
    ((hρc.mono (uIcc_subset_of_ordConnected hSc ha hxS)).intervalIntegrable)
    ((hρc.mono (hSc.uIcc_subset hxS hy)).intervalIntegrable)]
  have : 0 ≤ ∫ t in x..y, ρ t := by
    rw [intervalIntegral.integral_of_le hxy]
    exact setIntegral_nonneg measurableSet_Ioc fun t ht =>
      hρ0 t (Icc_subset_of_ordConnected hSc ha hy ⟨hax.trans ht.1.le, ht.2⟩)
          (lt_of_le_of_lt hax ht.1)
  linarith

/-- Integration against the head: if `Φ' = φ` and `R x = ∫_{a₁}^x ρ`, then
`∫_{(a₁,x]} ρ φ(R) = Φ(R x) - Φ 0`. -/
private lemma setIntegral_Ioc_mul_comp_primitive (hS : IsOpen S)
    (hSc : S.OrdConnected) (ha : a₁ ∈ S)
    (hρc : ContinuousOn ρ S) {Φ φ : ℝ → ℝ} (hΦ : ∀ s, HasDerivAt Φ (φ s) s)
    (hφ : Continuous φ) {x : ℝ} (hx : x ∈ S) (hax : a₁ ≤ x) :
    IntegrableOn (fun t => ρ t * φ (∫ s in a₁..t, ρ s)) (Ioc a₁ x) ∧
      ∫ t in Ioc a₁ x, ρ t * φ (∫ s in a₁..t, ρ s) = Φ (∫ s in a₁..x, ρ s) - Φ 0 := by
  set R : ℝ → ℝ := fun t => ∫ s in a₁..t, ρ s with hR
  have hRd : ∀ t ∈ S, HasDerivAt R (ρ t) t := fun t ht =>
    hasDerivAt_intervalIntegral_of_continuousOn hS hSc ha hρc ht
  have hsub := uIcc_subset_of_ordConnected hSc ha hx
  have hcont : ContinuousOn (fun t => ρ t * φ (R t)) (uIcc a₁ x) :=
    (hρc.mono hsub).mul (hφ.comp_continuousOn fun t ht =>
      (hRd t (hsub ht)).continuousAt.continuousWithinAt)
  have hii : IntervalIntegrable (fun t => ρ t * φ (R t)) volume a₁ x := hcont.intervalIntegrable
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hax).1 hii, ?_⟩
  rw [← intervalIntegral.integral_of_le hax,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => Φ (R t))
      (fun t ht => ((hΦ (R t)).comp t (hRd t (hsub ht))).congr_deriv (by ring)) hii]
  simp [hR]

/-- `∫_{(a₁,x]} ρ R^n / n! = R(x)^{n+1} / (n+1)!` for the head `R` of `ρ`. -/
private lemma setIntegral_Ioc_mul_primitive_pow_div_factorial (hS : IsOpen S)
    (hSc : S.OrdConnected) (ha : a₁ ∈ S)
    (hρc : ContinuousOn ρ S) (n : ℕ) {x : ℝ} (hx : x ∈ S) (hax : a₁ ≤ x) :
    IntegrableOn (fun t => ρ t * ((∫ s in a₁..t, ρ s) ^ n / n.factorial)) (Ioc a₁ x) ∧
      ∫ t in Ioc a₁ x, ρ t * ((∫ s in a₁..t, ρ s) ^ n / n.factorial) =
        (∫ s in a₁..x, ρ s) ^ (n + 1) / (n + 1).factorial := by
  have h := setIntegral_Ioc_mul_comp_primitive hS hSc ha hρc
    (Φ := fun s => s ^ (n + 1) / (n + 1).factorial) (φ := fun s => s ^ n / n.factorial)
    (fun s => by
      convert (hasDerivAt_pow (n + 1) s).div_const ((n + 1).factorial : ℝ) using 1
      rw [Nat.factorial_succ]
      push_cast
      field_simp)
    (by fun_prop) hx hax
  simpa using h

/-- `∫_{(a₁,x]} ρ exp(R) = exp(R x) - 1` for the head `R` of `ρ`. -/
private lemma setIntegral_Ioc_mul_exp_primitive (hS : IsOpen S) (hSc : S.OrdConnected) (ha : a₁ ∈ S)
    (hρc : ContinuousOn ρ S) {x : ℝ} (hx : x ∈ S) (hax : a₁ ≤ x) :
    IntegrableOn (fun t => ρ t * Real.exp (∫ s in a₁..t, ρ s)) (Ioc a₁ x) ∧
      ∫ t in Ioc a₁ x, ρ t * Real.exp (∫ s in a₁..t, ρ s) =
        Real.exp (∫ s in a₁..x, ρ s) - 1 := by
  have h := setIntegral_Ioc_mul_comp_primitive hS hSc ha hρc (Φ := Real.exp) (φ := Real.exp)
    (fun s => Real.hasDerivAt_exp s) Real.continuous_exp hx hax
  simpa using h

end Head

/-! ### Volterra equations controlled from a finite endpoint -/

section Volterra

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The Volterra operator controlled from the left endpoint `a₁`, with the rank-two kernel
`K x t = p₁ x q₁ t + p₂ x q₂ t` and weight `ψ`: `(L φ) x = ∫_{(a₁,x]} K x t ψ t φ t dt`. -/
noncomputable def leftVolterraOp (a₁ : ℝ) (p₁ p₂ q₁ q₂ ψ : ℝ → 𝕜) (φ : ℝ → 𝕜) (x : ℝ) : 𝕜 :=
  p₁ x * (∫ t in Ioc a₁ x, q₁ t * ψ t * φ t) + p₂ x * ∫ t in Ioc a₁ x, q₂ t * ψ t * φ t

variable {p₁ p₂ q₁ q₂ ψ : ℝ → 𝕜} {ρ : ℝ → ℝ} {S : Set ℝ} {a₁ : ℝ}

/-- `(a₁, x] ⊆ S ∩ (a₁, ∞)` for `x ∈ S`. -/
private lemma Ioc_subset_inter_Ioi_of_ordConnected (hSc : S.OrdConnected) (ha : a₁ ∈ S)
    {x : ℝ} (hx : x ∈ S) :
    Ioc a₁ x ⊆ S ∩ Ioi a₁ := by
  intro t ht
  exact ⟨Icc_subset_of_ordConnected hSc ha hx ⟨ht.1.le, ht.2⟩, ht.1⟩

/-- One Picard step for the Volterra operator controlled from `a₁`: if
`‖φ t‖ ≤ B t R(t)ⁿ / n!` with `R t = ∫_{a₁}^t ρ` and `B ≥ 0` nondecreasing, then
`‖(L φ) x‖ ≤ B x R(x)ⁿ⁺¹ / (n + 1)!`. -/
private lemma norm_leftVolterraOp_le_picard_step (hS : IsOpen S)
    (hSc : S.OrdConnected) (ha : a₁ ∈ S)
    (hp₁ : ContinuousOn p₁ S) (hp₂ : ContinuousOn p₂ S)
    (hq₁ : ContinuousOn (fun t => q₁ t * ψ t) S) (hq₂ : ContinuousOn (fun t => q₂ t * ψ t) S)
    (hρc : ContinuousOn ρ S)
    (hK : ∀ x ∈ S, ∀ t, a₁ < t → t ≤ x → ‖(p₁ x * q₁ t + p₂ x * q₂ t) * ψ t‖ ≤ ρ t)
    {B : ℝ → ℝ} (hB0 : ∀ t ∈ S, a₁ < t → 0 ≤ B t)
    (hBm : ∀ x ∈ S, ∀ t, a₁ < t → t ≤ x → B t ≤ B x)
    {φ : ℝ → 𝕜} (hφm : AEStronglyMeasurable φ (volume.restrict (S ∩ Ioi a₁))) (n : ℕ)
    (hφ : ∀ t ∈ S, a₁ < t → ‖φ t‖ ≤ B t * ((∫ s in a₁..t, ρ s) ^ n / n.factorial)) :
    (∀ x ∈ S, IntegrableOn (fun t => q₁ t * ψ t * φ t) (Ioc a₁ x)) ∧
    (∀ x ∈ S, IntegrableOn (fun t => q₂ t * ψ t * φ t) (Ioc a₁ x)) ∧
    AEStronglyMeasurable (leftVolterraOp a₁ p₁ p₂ q₁ q₂ ψ φ) (volume.restrict (S ∩ Ioi a₁)) ∧
    ∀ x ∈ S, a₁ < x → ‖leftVolterraOp a₁ p₁ p₂ q₁ q₂ ψ φ x‖ ≤
      B x * ((∫ s in a₁..x, ρ s) ^ (n + 1) / (n + 1).factorial) := by
  have hρ0 : ∀ t ∈ S, a₁ < t → 0 ≤ ρ t := fun t ht hat =>
    (norm_nonneg _).trans (hK t ht t hat le_rfl)
  have hφx : ∀ x ∈ S, ∀ t ∈ Ioc a₁ x,
      ‖φ t‖ ≤ B x * ((∫ s in a₁..x, ρ s) ^ n / n.factorial) := by
    intro x hx t ht
    have htS : t ∈ S := (Ioc_subset_inter_Ioi_of_ordConnected hSc ha hx ht).1
    have hR0 := intervalIntegral_nonneg_of_nonneg_on hρ0 hSc ha htS ht.1.le
    refine (hφ t htS ht.1).trans (mul_le_mul (hBm x hx t ht.1 ht.2) ?_ (by positivity)
      ((hB0 t htS ht.1).trans (hBm x hx t ht.1 ht.2)))
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hR0
      (intervalIntegral_mono_upper_of_nonneg hρ0 hSc ha hρc hx ht.1.le ht.2) n) (Nat.cast_nonneg _)
  have hint : ∀ {q : ℝ → 𝕜}, ContinuousOn (fun t => q t * ψ t) S →
      ∀ x ∈ S, IntegrableOn (fun t => q t * ψ t * φ t) (Ioc a₁ x) := by
    intro q hq x hx
    exact (integrableOn_Ioc_of_continuousOn hSc ha hq hx).mul_bdd
      (hφm.mono_measure (Measure.restrict_mono
          (Ioc_subset_inter_Ioi_of_ordConnected hSc ha hx) le_rfl))
      (ae_restrict_of_forall_mem measurableSet_Ioc (hφx x hx))
  have hi₁ := hint hq₁
  have hi₂ := hint hq₂
  refine ⟨hi₁, hi₂, ?_, ?_⟩
  · have hc : ContinuousOn (leftVolterraOp a₁ p₁ p₂ q₁ q₂ ψ φ) (S ∩ Ici a₁) :=
      ((hp₁.mono inter_subset_left).mul (continuousOn_setIntegral_Ioc hS hi₁)).add
        ((hp₂.mono inter_subset_left).mul (continuousOn_setIntegral_Ioc hS hi₂))
    exact (hc.mono (inter_subset_inter_right _ Ioi_subset_Ici_self)).aestronglyMeasurable
      (hS.measurableSet.inter measurableSet_Ioi)
  · intro x hx hax
    have heq : leftVolterraOp a₁ p₁ p₂ q₁ q₂ ψ φ x =
        ∫ t in Ioc a₁ x, (p₁ x * q₁ t + p₂ x * q₂ t) * ψ t * φ t := by
      rw [leftVolterraOp, ← integral_const_mul, ← integral_const_mul, ← integral_add
        ((hi₁ x hx).const_mul _) ((hi₂ x hx).const_mul _)]
      congr 1
      ext t
      ring
    have hb := setIntegral_Ioc_mul_primitive_pow_div_factorial hS hSc ha hρc n hx hax.le
    rw [heq, ← hb.2, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hb.1.const_mul (B x))
      (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
    have htS : t ∈ S := (Ioc_subset_inter_Ioi_of_ordConnected hSc ha hx ht).1
    rw [norm_mul]
    have hR0 := intervalIntegral_nonneg_of_nonneg_on hρ0 hSc ha htS ht.1.le
    calc ‖(p₁ x * q₁ t + p₂ x * q₂ t) * ψ t‖ * ‖φ t‖
        ≤ ρ t * (B t * ((∫ s in a₁..t, ρ s) ^ n / n.factorial)) :=
          mul_le_mul (hK x hx t ht.1 ht.2) (hφ t htS ht.1) (norm_nonneg _) (hρ0 t htS ht.1)
      _ ≤ ρ t * (B x * ((∫ s in a₁..t, ρ s) ^ n / n.factorial)) := by
          have := hρ0 t htS ht.1
          gcongr
          exact hBm x hx t ht.1 ht.2
      _ = B x * (ρ t * ((∫ s in a₁..t, ρ s) ^ n / n.factorial)) := by ring

/-- **Existence and bound for inhomogeneous Volterra equations controlled from a finite
endpoint** (Olver, *Asymptotics and Special Functions*, Ch. 6, Thm. 10.1, the form used in
Ch. 6, §2 for solutions characterized at a finite point `a₁`). Let `S` be open and
order-connected with `a₁ ∈ S`. If `‖K x t ψ t‖ ≤ ρ t` for `a₁ < t ≤ x`, `ρ` is continuous on
`S` and `‖σ t‖ ≤ B t` with `B` nondecreasing, then `h x = σ x + ∫_{(a₁,x]} K x t ψ t h t dt` has a
solution on `S ∩ (a₁, ∞)` with `‖h x - σ x‖ ≤ B x (exp (∫_{a₁}^x ρ) - 1)`. -/
private lemma exists_leftVolterra_solution_of_finite_endpoint (hS : IsOpen S)
    (hSc : S.OrdConnected) (ha : a₁ ∈ S)
    (hp₁ : ContinuousOn p₁ S) (hp₂ : ContinuousOn p₂ S)
    (hq₁ : ContinuousOn (fun t => q₁ t * ψ t) S) (hq₂ : ContinuousOn (fun t => q₂ t * ψ t) S)
    {σ : ℝ → 𝕜} {B : ℝ → ℝ} (hσm : AEStronglyMeasurable σ (volume.restrict (S ∩ Ioi a₁)))
    (hσ : ∀ t ∈ S, a₁ < t → ‖σ t‖ ≤ B t) (hBm : ∀ x ∈ S, ∀ t, a₁ < t → t ≤ x → B t ≤ B x)
    (hρc : ContinuousOn ρ S)
    (hK : ∀ x ∈ S, ∀ t, a₁ < t → t ≤ x → ‖(p₁ x * q₁ t + p₂ x * q₂ t) * ψ t‖ ≤ ρ t) :
    ∃ h : ℝ → 𝕜, AEStronglyMeasurable h (volume.restrict (S ∩ Ioi a₁)) ∧
      (∀ x ∈ S, a₁ < x → ‖h x - σ x‖ ≤ B x * (Real.exp (∫ s in a₁..x, ρ s) - 1)) ∧
      ∀ x ∈ S, a₁ < x → h x = σ x + leftVolterraOp a₁ p₁ p₂ q₁ q₂ ψ h x := by
  have hB0 : ∀ t ∈ S, a₁ < t → 0 ≤ B t := fun t ht hat => (norm_nonneg _).trans (hσ t ht hat)
  set L := leftVolterraOp a₁ p₁ p₂ q₁ q₂ ψ with hL
  set φ : ℕ → ℝ → 𝕜 := fun n => L^[n] σ with hφdef
  set R : ℝ → ℝ := fun t => ∫ s in a₁..t, ρ s with hR
  have hφ : ∀ n, AEStronglyMeasurable (φ n) (volume.restrict (S ∩ Ioi a₁)) ∧
      ∀ t ∈ S, a₁ < t → ‖φ n t‖ ≤ B t * (R t ^ n / n.factorial) := by
    intro n
    induction n with
    | zero => exact ⟨hσm, fun t ht hat => by simpa [φ] using hσ t ht hat⟩
    | succ n ih =>
      have hs := norm_leftVolterraOp_le_picard_step hS hSc ha hp₁ hp₂ hq₁ hq₂ hρc hK hB0
          hBm ih.1 n ih.2
      have hφs : φ (n + 1) = L (φ n) := Function.iterate_succ_apply' L n σ
      rw [hφs]
      exact ⟨hs.2.2.1, hs.2.2.2⟩
  have hstep : ∀ n, _ := fun n =>
      norm_leftVolterraOp_le_picard_step hS hSc ha hp₁ hp₂ hq₁ hq₂ hρc hK hB0 hBm
    (hφ n).1 n (hφ n).2
  have hρ0 : ∀ t ∈ S, a₁ < t → 0 ≤ ρ t := fun t ht hat =>
    (norm_nonneg _).trans (hK t ht t hat le_rfl)
  have hexp : ∀ x, HasSum (fun n => R x ^ n / n.factorial) (Real.exp (R x)) := fun x => by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (R x)
  have hsumm : ∀ x ∈ S, a₁ < x → Summable (fun n => φ n x) := fun x hx hax =>
    Summable.of_norm_bounded ((hexp x).summable.mul_left (B x)) fun n => (hφ n).2 x hx hax
  set H : ℝ → 𝕜 := fun x => ∑' n, φ n x with hH
  have hHm : AEStronglyMeasurable H (volume.restrict (S ∩ Ioi a₁)) :=
    aestronglyMeasurable_of_tendsto_ae atTop (f := fun N x => ∑ n ∈ Finset.range N, φ n x)
      (fun N => Finset.aestronglyMeasurable_fun_sum _ fun n _ => (hφ n).1)
      (ae_restrict_of_forall_mem (hS.measurableSet.inter measurableSet_Ioi) fun x hx =>
        (hsumm x hx.1 hx.2).hasSum.tendsto_sum_nat)
  have hHσ : ∀ x ∈ S, a₁ < x → H x - σ x = ∑' n, φ (n + 1) x := fun x hx hax => by
    show ∑' n, φ n x - σ x = _
    rw [(hsumm x hx hax).tsum_eq_zero_add]
    simp [φ]
  refine ⟨H, hHm, ?_, ?_⟩
  · intro x hx hax
    have hs1 : HasSum (fun n => B x * (R x ^ (n + 1) / (n + 1).factorial))
        (B x * (Real.exp (R x) - 1)) := by
      have := ((hasSum_nat_add_iff' 1).2 (hexp x)).mul_left (B x)
      simpa using this
    have hnb : ∀ n, ‖φ (n + 1) x‖ ≤ B x * (R x ^ (n + 1) / (n + 1).factorial) :=
      fun n => (hφ (n + 1)).2 x hx hax
    have hns : Summable fun n => ‖φ (n + 1) x‖ :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hnb hs1.summable
    rw [hHσ x hx hax]
    exact (norm_tsum_le_tsum_norm hns).trans (hns.tsum_le_tsum hnb hs1.summable |>.trans_eq
      hs1.tsum_eq)
  · intro x hx hax
    have hR0x := intervalIntegral_nonneg_of_nonneg_on hρ0 hSc ha hx hax.le
    -- interchange of sum and integral
    have hswap : ∀ {q : ℝ → 𝕜}, ContinuousOn (fun t => q t * ψ t) S →
        (∀ n, IntegrableOn (fun t => q t * ψ t * φ n t) (Ioc a₁ x)) →
        Summable (fun n => ∫ t in Ioc a₁ x, q t * ψ t * φ n t) ∧
        ∫ t in Ioc a₁ x, q t * ψ t * H t = ∑' n, ∫ t in Ioc a₁ x, q t * ψ t * φ n t := by
      intro q hq hF
      have hqi := integrableOn_Ioc_of_continuousOn hSc ha hq hx
      have hnorm : ∀ n, ∫ t in Ioc a₁ x, ‖q t * ψ t * φ n t‖ ≤
          (∫ t in Ioc a₁ x, ‖q t * ψ t‖) * (B x * (R x ^ n / n.factorial)) := by
        intro n
        rw [← integral_mul_const]
        refine setIntegral_mono_on (hF n).norm (hqi.norm.mul_const _) measurableSet_Ioc
          fun t ht => ?_
        have htS : t ∈ S := (Ioc_subset_inter_Ioi_of_ordConnected hSc ha hx ht).1
        rw [norm_mul]
        gcongr
        have hR0 := intervalIntegral_nonneg_of_nonneg_on hρ0 hSc ha htS ht.1.le
        refine ((hφ n).2 t htS ht.1).trans (mul_le_mul (hBm x hx t ht.1 ht.2)
          (div_le_div_of_nonneg_right (pow_le_pow_left₀ hR0
            (intervalIntegral_mono_upper_of_nonneg hρ0 hSc ha hρc hx ht.1.le ht.2) n)
                (Nat.cast_nonneg _))
          (by positivity) (hB0 x hx hax))
      have hsI : Summable fun n => ∫ t in Ioc a₁ x, ‖q t * ψ t * φ n t‖ :=
        Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hnorm
          (((hexp x).summable.mul_left (B x)).mul_left _)
      refine ⟨Summable.of_norm_bounded hsI fun n => norm_integral_le_integral_norm _, ?_⟩
      rw [integral_tsum_of_summable_integral_norm hF hsI]
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      have htS : t ∈ S := (Ioc_subset_inter_Ioi_of_ordConnected hSc ha hx ht).1
      simp only [hH]
      rw [tsum_mul_left]
    have h₁ := hswap hq₁ fun n => (hstep n).1 x hx
    have h₂ := hswap hq₂ fun n => (hstep n).2.1 x hx
    rw [← sub_eq_iff_eq_add', hHσ x hx hax, hL, leftVolterraOp, h₁.2, h₂.2, ← tsum_mul_left,
      ← tsum_mul_left, ← (h₁.1.mul_left _).tsum_add (h₂.1.mul_left _)]
    congr 1
    ext n
    exact congrFun (Function.iterate_succ_apply' L n σ) x

end Volterra

/-! ### Liouville–Green approximation with errors controlled from a finite endpoint -/

section Approx

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Liouville–Green approximation with an arbitrary approximant, errors controlled from a
finite endpoint** (Olver, *Asymptotics and Special Functions*, Ch. 6, §2 and Ch. 10, §3, the
solutions characterized at `a₁`). Let `S` be open and order-connected with `a₁ ∈ S`, let
`A ≠ 0` be twice differentiable on `S` and `E' = -k A⁻² E`, with `‖E‖` nondecreasing from `a₁`
and `‖(1 - E(t)²/E(x)²)/(2k)‖ ≤ κ` for `a₁ ≤ t ≤ x`. Let `P` be twice differentiable on `S` with
residual `r = A² P'' + 2 (A A' - k) P' + (A A'' - g A²) P`. Then `w'' = (k² A⁻⁴ + g) w` has a
solution `w = A E (P + ε)` on `S ∩ (a₁, ∞)` with

`‖ε x‖ ≤ κ W x exp (κ V x)`,   `‖A(x)² ε'(x)‖ ≤ W x exp (κ V x)`,

where `W x = ∫_{a₁}^x ‖r‖` and `V x = ∫_{a₁}^x ‖A A'' - g A²‖`. For `k = -u < 0`
(`E = exp (u ξ)`) this is the solution dominant at the right; for `k = ± i u` it is an
oscillatory solution with prescribed behaviour at `a₁`. -/
private lemma exists_solution_of_approx_finite_endpoint {S : Set ℝ} {a₁ κ : ℝ} {k : 𝕜}
    {A A' A'' E g P P' P'' : ℝ → 𝕜}
    (hS : IsOpen S) (hSc : S.OrdConnected) (ha : a₁ ∈ S) (hk : k ≠ 0) (hκ : 0 < κ)
    (hA : ∀ x ∈ S, A x ≠ 0)
    (hA' : ∀ x ∈ S, HasDerivAt A (A' x) x)
    (hA'' : ∀ x ∈ S, HasDerivAt A' (A'' x) x)
    (hA''c : ContinuousOn A'' S) (hgc : ContinuousOn g S)
    (hE0 : ∀ x ∈ S, E x ≠ 0)
    (hE : ∀ x ∈ S, HasDerivAt E (-(k * (A x ^ 2)⁻¹ * E x)) x)
    (hEle : ∀ x ∈ S, ∀ t, a₁ < t → t ≤ x → ‖E t‖ ≤ ‖E x‖)
    (hK : ∀ x ∈ S, ∀ t, a₁ < t → t ≤ x → ‖(1 - E t ^ 2 / E x ^ 2) / (2 * k)‖ ≤ κ)
    (hP : ∀ x ∈ S, HasDerivAt P (P' x) x) (hP' : ∀ x ∈ S, HasDerivAt P' (P'' x) x)
    (hP''c : ContinuousOn P'' S) :
    ∃ ε ε' w' : ℝ → 𝕜, ∀ x ∈ S, a₁ < x →
      HasDerivAt ε (ε' x) x ∧
      HasDerivAt (fun y => A y * E y * (P y + ε y)) (w' x) x ∧
      HasDerivAt w' ((k ^ 2 * (A x ^ 4)⁻¹ + g x) * (A x * E x * (P x + ε x))) x ∧
      ‖ε x‖ ≤ κ * (∫ t in a₁..x, ‖approxResidual k A A' A'' g P P' P'' t‖) *
        Real.exp (κ * ∫ t in a₁..x, ‖A t * A'' t - g t * A t ^ 2‖) ∧
      ‖A x ^ 2 * ε' x‖ ≤ (∫ t in a₁..x, ‖approxResidual k A A' A'' g P P' P'' t‖) *
        Real.exp (κ * ∫ t in a₁..x, ‖A t * A'' t - g t * A t ^ 2‖) := by
  set F' : ℝ → 𝕜 := fun t => A t * A'' t - g t * A t ^ 2 with hF'
  set r : ℝ → 𝕜 := approxResidual k A A' A'' g P P' P'' with hr
  have hAc : ContinuousOn A S := fun x hx => (hA' x hx).continuousAt.continuousWithinAt
  have hA'c : ContinuousOn A' S := fun x hx => (hA'' x hx).continuousAt.continuousWithinAt
  have hPc : ContinuousOn P S := fun x hx => (hP x hx).continuousAt.continuousWithinAt
  have hP'c : ContinuousOn P' S := fun x hx => (hP' x hx).continuousAt.continuousWithinAt
  have hEc : ContinuousOn E S := fun x hx => (hE x hx).continuousAt.continuousWithinAt
  have hF'c : ContinuousOn F' S := (hAc.mul hA''c).sub (hgc.mul (hAc.pow 2))
  have hrc : ContinuousOn r S :=
    continuousOn_approxResidual hAc hA'c hA''c hgc hPc hP'c hP''c

  have hp₂c : ContinuousOn (fun x => -(2 * k)⁻¹ * (E x ^ 2)⁻¹) S :=
    continuousOn_const.mul ((hEc.pow 2).inv₀ fun x hx => pow_ne_zero 2 (hE0 x hx))
  have hKψ : ∀ {ψ : ℝ → 𝕜}, ∀ x ∈ S, ∀ t, a₁ < t → t ≤ x →
      ‖((2 * k)⁻¹ * 1 + -(2 * k)⁻¹ * (E x ^ 2)⁻¹ * E t ^ 2) * ψ t‖ ≤ κ * ‖ψ t‖ := by
    intro ψ x hx t hat htx
    have heq : ((2 * k)⁻¹ * 1 + -(2 * k)⁻¹ * (E x ^ 2)⁻¹ * E t ^ 2) =
        (1 - E t ^ 2 / E x ^ 2) / (2 * k) := by ring
    rw [heq, norm_mul]
    exact mul_le_mul_of_nonneg_right (hK x hx t hat htx) (norm_nonneg _)
  have hmeas : MeasurableSet (S ∩ Ioi a₁) := hS.measurableSet.inter measurableSet_Ioi
  -- the forcing term
  have hσ := norm_leftVolterraOp_le_picard_step (𝕜 := 𝕜) hS hSc ha
    (p₁ := fun _ => (2 * k)⁻¹) (q₁ := fun _ => 1)
    (p₂ := fun x => -(2 * k)⁻¹ * (E x ^ 2)⁻¹) (q₂ := fun t => E t ^ 2) (ψ := r)
    (ρ := fun t => κ * ‖r t‖) (B := fun _ => 1)
    continuousOn_const hp₂c (by simpa using hrc) ((hEc.pow 2).mul hrc)
    (continuousOn_const.mul hrc.norm)
    (fun x hx t hat htx => hKψ x hx t hat htx) (fun _ _ _ => zero_le_one)
    (fun _ _ _ _ _ => le_rfl) (φ := fun _ => 1) aestronglyMeasurable_const 0 (fun _ _ _ => by simp)
  simp only [one_mul, zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at hσ
  set σ : ℝ → 𝕜 := leftVolterraOp a₁ (fun _ => (2 * k)⁻¹) (fun x => -(2 * k)⁻¹ * (E x ^ 2)⁻¹)
    (fun _ => 1) (fun t => E t ^ 2) r (fun _ => 1) with hσdef
  set ρ : ℝ → ℝ := fun t => κ * ‖F' t‖ with hρ
  have hρc : ContinuousOn ρ S := continuousOn_const.mul hF'c.norm
  have hρ0 : ∀ t, 0 ≤ ρ t := fun t => mul_nonneg hκ.le (norm_nonneg _)
  set B : ℝ → ℝ := fun x => ∫ t in a₁..x, κ * ‖r t‖ with hB
  have hBm : ∀ x ∈ S, ∀ t, a₁ < t → t ≤ x → B t ≤ B x := fun x hx t hat htx =>
    intervalIntegral_mono_upper_of_nonneg (fun _ _ _ => mul_nonneg hκ.le (norm_nonneg _)) hSc ha
      (continuousOn_const.mul hrc.norm) hx
      hat.le htx
  obtain ⟨h, hhm, hhb, hheq⟩ := exists_leftVolterra_solution_of_finite_endpoint (𝕜 := 𝕜) hS hSc ha
    (p₁ := fun _ => (2 * k)⁻¹) (q₁ := fun _ => 1)
    (p₂ := fun x => -(2 * k)⁻¹ * (E x ^ 2)⁻¹) (q₂ := fun t => E t ^ 2) (ψ := F')
    (ρ := ρ) (σ := σ) (B := B)
    continuousOn_const hp₂c (by simpa using hF'c) ((hEc.pow 2).mul hF'c) hσ.2.2.1
    (fun t ht hat => hσ.2.2.2 t ht hat) hBm hρc (fun x hx t hat htx => hKψ x hx t hat htx)
  set R : ℝ → ℝ := fun t => ∫ s in a₁..t, ρ s with hR
  have hRx : ∀ x, R x = κ * ∫ t in a₁..x, ‖F' t‖ := fun x =>
    intervalIntegral.integral_const_mul _ _
  have hBx : ∀ x, B x = κ * ∫ t in a₁..x, ‖r t‖ := fun x =>
    intervalIntegral.integral_const_mul _ _
  have hB0 : ∀ x ∈ S, a₁ ≤ x → 0 ≤ B x := fun x hx hax =>
    intervalIntegral_nonneg_of_nonneg_on
        (fun _ _ _ => mul_nonneg hκ.le (norm_nonneg _)) hSc ha hx hax
  have hhb' : ∀ t ∈ S, a₁ < t → ‖h t‖ ≤ B t * Real.exp (R t) := fun t ht hat => by
    have h1 := hhb t ht hat
    have h2 := hσ.2.2.2 t ht hat
    calc ‖h t‖ ≤ ‖σ t‖ + ‖h t - σ t‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ B t + B t * (Real.exp (R t) - 1) := add_le_add h2 h1
      _ = B t * Real.exp (R t) := by ring
  have hhbx : ∀ x ∈ S, ∀ t ∈ Ioc a₁ x, ‖h t‖ ≤ B x * Real.exp (R x) := fun x hx t ht => by
    have htS : t ∈ S := (Ioc_subset_inter_Ioi_of_ordConnected hSc ha hx ht).1
    exact (hhb' t htS ht.1).trans (mul_le_mul (hBm x hx t ht.1 ht.2)
      (Real.exp_le_exp.2 (intervalIntegral_mono_upper_of_nonneg (fun _ _ _ => hρ0 _) hSc ha hρc
          hx ht.1.le ht.2))
      (Real.exp_pos _).le (hB0 x hx (ht.1.le.trans ht.2)))
  have hmulb : ∀ {q : ℝ → 𝕜}, ContinuousOn (fun t => q t * F' t) S →
      ∀ x ∈ S, IntegrableOn (fun t => q t * F' t * h t) (Ioc a₁ x) := by
    intro q hq x hx
    exact (integrableOn_Ioc_of_continuousOn hSc ha hq hx).mul_bdd
      (hhm.mono_measure (Measure.restrict_mono
          (Ioc_subset_inter_Ioi_of_ordConnected hSc ha hx) le_rfl))
      (ae_restrict_of_forall_mem measurableSet_Ioc (hhbx x hx))
  have hJ₁i := hmulb (q := fun _ => 1) (by simpa using hF'c)
  have hJ₂i := hmulb (q := fun t => E t ^ 2) ((hEc.pow 2).mul hF'c)
  have hri' : ∀ x ∈ S, IntegrableOn r (Ioc a₁ x) := fun x hx =>
      integrableOn_Ioc_of_continuousOn hSc ha hrc hx
  have hEri : ∀ x ∈ S, IntegrableOn (fun t => E t ^ 2 * r t) (Ioc a₁ x) := fun x hx =>
    integrableOn_Ioc_of_continuousOn hSc ha ((hEc.pow 2).mul hrc) hx
  have hI₁i : ∀ x ∈ S, IntegrableOn (fun t => F' t * h t + r t) (Ioc a₁ x) := fun x hx =>
    ((hJ₁i x hx).add (hri' x hx)).congr_fun (fun t _ => by simp only [Pi.add_apply]; ring)
      measurableSet_Ioc
  have hI₂i : ∀ x ∈ S, IntegrableOn (fun t => E t ^ 2 * (F' t * h t + r t)) (Ioc a₁ x) :=
    fun x hx => ((hJ₂i x hx).add (hEri x hx)).congr_fun
      (fun t _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioc
  set I₁ : ℝ → 𝕜 := fun x => ∫ t in Ioc a₁ x, (F' t * h t + r t) with hI₁
  set I₂ : ℝ → 𝕜 := fun x => ∫ t in Ioc a₁ x, E t ^ 2 * (F' t * h t + r t) with hI₂
  have hheq' : ∀ x ∈ S, a₁ < x →
      h x = (2 * k)⁻¹ * I₁ x + -(2 * k)⁻¹ * (E x ^ 2)⁻¹ * I₂ x := by
    intro x hx hax
    have e1 : I₁ x = (∫ t in Ioc a₁ x, 1 * F' t * h t) + ∫ t in Ioc a₁ x, 1 * r t * 1 := by
      rw [← integral_add (hJ₁i x hx)
        ((hri' x hx).congr_fun (fun t _ => by simp) measurableSet_Ioc)]
      exact setIntegral_congr_fun measurableSet_Ioc (fun t _ => by ring)
    have e2 : I₂ x = (∫ t in Ioc a₁ x, E t ^ 2 * F' t * h t) +
        ∫ t in Ioc a₁ x, E t ^ 2 * r t * 1 := by
      rw [← integral_add (hJ₂i x hx)
        ((hEri x hx).congr_fun (fun t _ => by simp) measurableSet_Ioc)]
      exact setIntegral_congr_fun measurableSet_Ioc (fun t _ => by ring)
    rw [hheq x hx hax, hσdef, leftVolterraOp, leftVolterraOp, e1, e2]
    ring
  have hhc : ContinuousOn h (S ∩ Ioi a₁) :=
    (((continuousOn_const.mul (continuousOn_setIntegral_Ioc hS hI₁i)).add
      ((hp₂c.mono inter_subset_left).mul (continuousOn_setIntegral_Ioc hS hI₂i))).mono
      (inter_subset_inter_right _ Ioi_subset_Ici_self)).congr fun x hx => hheq' x hx.1 hx.2
  have hopen : IsOpen (S ∩ Ioi a₁) := hS.inter isOpen_Ioi
  -- derivatives of the primitives at interior points
  have hprimd : ∀ {f : ℝ → 𝕜}, ContinuousOn f (S ∩ Ioi a₁) →
      (∀ x ∈ S, IntegrableOn f (Ioc a₁ x)) → ∀ x ∈ S, a₁ < x →
      HasDerivAt (fun y => ∫ t in Ioc a₁ y, f t) (f x) x := by
    intro f hfc hfi x hx hax
    have hd : HasDerivAt (fun y => ∫ t in a₁..y, f t) (f x) x :=
      intervalIntegral.integral_hasDerivAt_right
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hax.le).2 (hfi x hx))
        (hfc.stronglyMeasurableAtFilter hopen x ⟨hx, hax⟩)
        (hfc.continuousAt (hopen.mem_nhds ⟨hx, hax⟩))
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hax] with y hy
    exact (intervalIntegral.integral_of_le hy.le).symm
  have hI₁d : ∀ x ∈ S, a₁ < x → HasDerivAt I₁ (F' x * h x + r x) x := fun x hx hax =>
    hprimd (((hF'c.mono inter_subset_left).mul hhc).add (hrc.mono inter_subset_left)) hI₁i x hx
      hax
  have hI₂d : ∀ x ∈ S, a₁ < x → HasDerivAt I₂ (E x ^ 2 * (F' x * h x + r x)) x :=
    fun x hx hax => hprimd (((hEc.pow 2).mono inter_subset_left).mul
      (((hF'c.mono inter_subset_left).mul hhc).add (hrc.mono inter_subset_left))) hI₂i x hx hax
  have hEinv : ∀ x ∈ S, HasDerivAt (fun y => (E y ^ 2)⁻¹)
      (-((2 : ℕ) * E x ^ (2 - 1) * -(k * (A x ^ 2)⁻¹ * E x)) / (E x ^ 2) ^ 2) x :=
    fun x hx => ((hE x hx).pow 2).inv (pow_ne_zero 2 (hE0 x hx))
  obtain ⟨ε', hε'def⟩ : ∃ ε' : ℝ → 𝕜, ε' = fun x => -((A x ^ 2)⁻¹ * (E x ^ 2)⁻¹ * I₂ x) :=
    ⟨_, rfl⟩
  have hεd : ∀ x ∈ S, a₁ < x → HasDerivAt h (ε' x) x := by
    intro x hx hax
    have := ((hasDerivAt_const x (2 * k)⁻¹).mul (hI₁d x hx hax)).add
      (((hasDerivAt_const x (-(2 * k)⁻¹)).mul (hEinv x hx)).mul (hI₂d x hx hax))
    refine (this.congr_deriv ?_).congr_of_eventuallyEq ?_
    · have := hA x hx
      have := hE0 x hx
      rw [hε'def]
      simp only [Pi.mul_apply]
      field_simp
      ring
    · filter_upwards [hopen.mem_nhds ⟨hx, hax⟩] with y hy using hheq' y hy.1 hy.2
  have hε'd : ∀ x ∈ S, a₁ < x → HasDerivAt ε'
      (-(2 * (A x * A' x - k)) * ε' x / A x ^ 2 - (F' x * h x + r x) / A x ^ 2) x := by
    intro x hx hax
    have := (((((hA' x hx).pow 2).inv (pow_ne_zero 2 (hA x hx))).mul (hEinv x hx)).mul
      (hI₂d x hx hax)).neg
    rw [hε'def]
    refine this.congr_deriv ?_
    have := hA x hx
    have := hE0 x hx
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply]
    field_simp
    ring
  refine ⟨h, ε', fun y => E y * ((A' y - k * (A y)⁻¹) * (P y + h y) + A y * (P' y + ε' y)),
    fun x hx hax => ⟨hεd x hx hax, ?_, ?_, ?_, ?_⟩⟩
  · refine (((hA' x hx).mul (hE x hx)).mul ((hP x hx).add (hεd x hx hax))).congr_deriv ?_
    have := hA x hx
    simp only [Pi.mul_apply, Pi.add_apply]
    field_simp
    ring
  · refine ((hE x hx).mul ((((hA'' x hx).sub (((hA' x hx).inv (hA x hx)).const_mul k)).mul
      ((hP x hx).add (hεd x hx hax))).add ((hA' x hx).mul ((hP' x hx).add
        (hε'd x hx hax))))).congr_deriv ?_
    have := hA x hx
    rw [hr, approxResidual, hF']
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.inv_apply]
    field_simp
    ring
  · calc ‖h x‖ ≤ B x * Real.exp (R x) := hhb' x hx hax
      _ = _ := by rw [hBx, hRx]
  · rw [← hRx]
    have hεx : A x ^ 2 * ε' x =
        -∫ t in Ioc a₁ x, (E x ^ 2)⁻¹ * (E t ^ 2 * (F' t * h t + r t)) := by
      have := hA x hx
      rw [integral_const_mul, hε'def]
      field_simp
      rfl
    have hexpt := setIntegral_Ioc_mul_exp_primitive hS hSc ha hρc hx hax.le
    have hEx : 0 < ‖E x‖ ^ 2 := by have := hE0 x hx; positivity
    have hWx' : ∫ t in a₁..x, ‖r t‖ = κ⁻¹ * B x := by rw [hBx]; field_simp
    have hWx : ∫ t in Ioc a₁ x, ‖r t‖ = κ⁻¹ * B x := by
      rw [← intervalIntegral.integral_of_le hax.le, hWx']
    have hbint : IntegrableOn (fun t => κ⁻¹ * B x * (ρ t * Real.exp (R t)) + ‖r t‖)
        (Ioc a₁ x) := (hexpt.1.const_mul _).add (hri' x hx).norm
    calc ‖A x ^ 2 * ε' x‖
        = ‖∫ t in Ioc a₁ x, (E x ^ 2)⁻¹ * (E t ^ 2 * (F' t * h t + r t))‖ := by
          rw [hεx, norm_neg]
      _ ≤ ∫ t in Ioc a₁ x, (κ⁻¹ * B x * (ρ t * Real.exp (R t)) + ‖r t‖) := by
          refine norm_integral_le_of_norm_le hbint
            (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
          have htS : t ∈ S := (Ioc_subset_inter_Ioi_of_ordConnected hSc ha hx ht).1
          have hle : ‖E t‖ ^ 2 ≤ ‖E x‖ ^ 2 := by
            have := hEle x hx t ht.1 ht.2
            gcongr
          have hht : ‖h t‖ ≤ B x * Real.exp (R t) :=
            (hhb' t htS ht.1).trans (mul_le_mul_of_nonneg_right
              (hBm x hx t ht.1 ht.2) (Real.exp_pos _).le)
          rw [norm_mul, norm_inv, norm_mul, norm_pow, norm_pow]
          calc (‖E x‖ ^ 2)⁻¹ * (‖E t‖ ^ 2 * ‖F' t * h t + r t‖)
              ≤ (‖E x‖ ^ 2)⁻¹ * (‖E x‖ ^ 2 * (‖F' t‖ * (B x * Real.exp (R t)) + ‖r t‖)) := by
                gcongr
                refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
                rw [norm_mul]
                gcongr
            _ = κ⁻¹ * B x * (ρ t * Real.exp (R t)) + ‖r t‖ := by
                have : ‖E x‖ ≠ 0 := norm_ne_zero_iff.2 (hE0 x hx)
                simp only [hρ]
                field_simp
      _ = (∫ t in a₁..x, ‖r t‖) * Real.exp (R x) := by
          rw [integral_add (hexpt.1.const_mul _) (hri' x hx).norm, integral_const_mul, hexpt.2,
            hWx, hWx']
          ring

/-- **Liouville–Green expansions with errors controlled from a finite endpoint** (Olver,
*Asymptotics and Special Functions*, Ch. 10, §3, with the error bounds referred to `a₁`). Under the
hypotheses of `exists_solution_of_approx_finite_endpoint`, let `A_0, …, A_n` satisfy `A_0' = 0` and
the recursion `A² A_s'' + 2 A A' A_s' + (A A'' - g A²) A_s = -2 A_{s+1}'` for `s < n`. Then
`w'' = (k² A⁻⁴ + g) w` has a solution `w = A E (∑_{s<n} (-1)^s A_s / k^s + ε)` on `S ∩ (a₁, ∞)` with
`‖ε x‖ ≤ 2 κ ‖k‖^{1-n} (∫_{a₁}^x ‖A_n'‖) exp (κ V x)`, `V x = ∫_{a₁}^x ‖A A'' - g A²‖`, and the
same bound for `‖A² ε'‖` without the factor `κ`. -/
private lemma exists_solution_expansion_finite_endpoint {S : Set ℝ} {a₁ κ : ℝ} {k : 𝕜}
    {A A' A'' E g : ℝ → 𝕜}
    (hS : IsOpen S) (hSc : S.OrdConnected) (ha : a₁ ∈ S) (hk : k ≠ 0) (hκ : 0 < κ)
    (hA : ∀ x ∈ S, A x ≠ 0)
    (hA' : ∀ x ∈ S, HasDerivAt A (A' x) x)
    (hA'' : ∀ x ∈ S, HasDerivAt A' (A'' x) x)
    (hA''c : ContinuousOn A'' S) (hgc : ContinuousOn g S)
    (hE0 : ∀ x ∈ S, E x ≠ 0)
    (hE : ∀ x ∈ S, HasDerivAt E (-(k * (A x ^ 2)⁻¹ * E x)) x)
    (hEle : ∀ x ∈ S, ∀ t, a₁ < t → t ≤ x → ‖E t‖ ≤ ‖E x‖)
    (hK : ∀ x ∈ S, ∀ t, a₁ < t → t ≤ x → ‖(1 - E t ^ 2 / E x ^ 2) / (2 * k)‖ ≤ κ)
    {n : ℕ} {As Ad Ad2 : ℕ → ℝ → 𝕜}
    (hAs : ∀ s < n, ∀ x ∈ S, HasDerivAt (As s) (Ad s x) x)
    (hAd : ∀ s < n, ∀ x ∈ S, HasDerivAt (Ad s) (Ad2 s x) x)
    (hAd2c : ∀ s < n, ContinuousOn (Ad2 s) S)
    (h0 : ∀ x ∈ S, Ad 0 x = 0)
    (hrec : ∀ s < n, ∀ x ∈ S, A x ^ 2 * Ad2 s x + 2 * A x * A' x * Ad s x +
      (A x * A'' x - g x * A x ^ 2) * As s x = -(2 * Ad (s + 1) x)) :
    ∃ ε ε' w' : ℝ → 𝕜, ∀ x ∈ S, a₁ < x →
      HasDerivAt ε (ε' x) x ∧
      HasDerivAt (fun y => A y * E y * (lgSeries k As n y + ε y)) (w' x) x ∧
      HasDerivAt w' ((k ^ 2 * (A x ^ 4)⁻¹ + g x) * (A x * E x * (lgSeries k As n x + ε x))) x ∧
      ‖ε x‖ ≤ κ * (2 * ‖k‖ / ‖k‖ ^ n * ∫ t in a₁..x, ‖Ad n t‖) *
        Real.exp (κ * ∫ t in a₁..x, ‖A t * A'' t - g t * A t ^ 2‖) ∧
      ‖A x ^ 2 * ε' x‖ ≤ (2 * ‖k‖ / ‖k‖ ^ n * ∫ t in a₁..x, ‖Ad n t‖) *
        Real.exp (κ * ∫ t in a₁..x, ‖A t * A'' t - g t * A t ^ 2‖) := by
  have hser : ∀ {c d : ℕ → ℝ → 𝕜}, (∀ s < n, ∀ x ∈ S, HasDerivAt (c s) (d s x) x) →
      ∀ x ∈ S, HasDerivAt (lgSeries k c n) (lgSeries k d n x) x := by
    intro c d hcd x hx
    unfold lgSeries
    exact HasDerivAt.fun_sum fun s hs =>
      ((hcd s (Finset.mem_range.1 hs) x hx).const_mul _).div_const _
  have hres : ∀ t ∈ S, ‖approxResidual k A A' A'' g (lgSeries k As n) (lgSeries k Ad n)
      (lgSeries k Ad2 n) t‖ = 2 * ‖k‖ / ‖k‖ ^ n * ‖Ad n t‖ := fun t ht => by
    rw [approxResidual_lgSeries hk (h0 t ht) (fun s hs => hrec s hs t ht)]
    simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one,
      RCLike.norm_ofNat]
    ring
  obtain ⟨ε, ε', w', H⟩ :=
      exists_solution_of_approx_finite_endpoint hS hSc ha hk hκ hA hA' hA'' hA''c hgc
    hE0 hE hEle hK (hser hAs) (hser hAd)
    (by
      unfold lgSeries
      exact continuousOn_finsetSum _ fun s hs =>
        (continuousOn_const.mul (hAd2c s (Finset.mem_range.1 hs))).div_const _)
  refine ⟨ε, ε', w', fun x hx hax => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := H x hx hax
  have hW : ∫ t in a₁..x, ‖approxResidual k A A' A'' g (lgSeries k As n) (lgSeries k Ad n)
      (lgSeries k Ad2 n) t‖ = 2 * ‖k‖ / ‖k‖ ^ n * ∫ t in a₁..x, ‖Ad n t‖ := by
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hax.le,
      intervalIntegral.integral_of_le hax.le]
    exact setIntegral_congr_fun measurableSet_Ioc fun t ht =>
      hres t (Icc_subset_of_ordConnected hSc ha hx (Ioc_subset_Icc_self ht))
  rw [hW] at h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

end Approx

/-! ### The real exponential (dominant) and oscillatory cases -/

section Real

/-- A function with nonnegative derivative on an order-connected open set is monotone there. -/
private lemma monotoneOn_of_hasDerivAt_nonneg_of_ordConnected {S : Set ℝ} (hSc : S.OrdConnected)
    {ξ d : ℝ → ℝ} (hξ : ∀ x ∈ S, HasDerivAt ξ (d x) x) (hd : ∀ x ∈ S, 0 ≤ d x) :
    MonotoneOn ξ S := by
  have hconv : Convex ℝ S := hSc.convex
  refine monotoneOn_of_deriv_nonneg hconv
    (fun x hx => (hξ x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hξ x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    (fun x hx => ?_)
  rw [(hξ x (interior_subset hx)).deriv]
  exact hd x (interior_subset hx)

/-- The dominant exponential Liouville–Green kernel: for `ξ' = A⁻²` and `u > 0`,
`E = exp (u ξ)` solves `E' = u A⁻² E`, `|E|` is nondecreasing and
`|(1 - E(t)²/E(x)²)/(-2u)| ≤ 1/(2u)` for `t ≤ x`. -/
private lemma dominant_exp_kernel_properties {S : Set ℝ} (hSc : S.OrdConnected) {u : ℝ}
    (hu : 0 < u) {A ξ : ℝ → ℝ} (hξ : ∀ x ∈ S, HasDerivAt ξ ((A x ^ 2)⁻¹) x) :
    (∀ x ∈ S, Real.exp (u * ξ x) ≠ 0) ∧
    (∀ x ∈ S, HasDerivAt (fun y => Real.exp (u * ξ y))
      (-(-u * (A x ^ 2)⁻¹ * Real.exp (u * ξ x))) x) ∧
    (∀ x ∈ S, ∀ t ∈ S, t ≤ x → ‖Real.exp (u * ξ t)‖ ≤ ‖Real.exp (u * ξ x)‖) ∧
    (∀ x ∈ S, ∀ t ∈ S, t ≤ x →
      ‖(1 - Real.exp (u * ξ t) ^ 2 / Real.exp (u * ξ x) ^ 2) / (2 * -u)‖ ≤ 1 / (2 * u)) := by
  have hmono := monotoneOn_of_hasDerivAt_nonneg_of_ordConnected hSc hξ (fun x _ => by positivity)
  have hEle : ∀ x ∈ S, ∀ t ∈ S, t ≤ x → Real.exp (u * ξ t) ≤ Real.exp (u * ξ x) :=
    fun x hx t ht htx => Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hmono ht hx htx) hu.le)
  refine ⟨fun x _ => (Real.exp_pos _).ne', fun x hx => ?_, fun x hx t ht htx => ?_,
    fun x hx t ht htx => ?_⟩
  · exact ((hξ x hx).const_mul u).exp.congr_deriv (by ring)
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.exp_pos _)]
    exact hEle x hx t ht htx
  · have hEx := Real.exp_pos (u * ξ x)
    have hEt := Real.exp_pos (u * ξ t)
    have h1 : Real.exp (u * ξ t) ^ 2 / Real.exp (u * ξ x) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      have := hEle x hx t ht htx
      gcongr
    have h0 : 0 < Real.exp (u * ξ t) ^ 2 / Real.exp (u * ξ x) ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - _),
      show |2 * -u| = 2 * u by rw [abs_of_neg (by linarith)]; ring]
    gcongr
    linarith

/-- **Liouville–Green expansions, dominant exponential case, errors controlled from a finite
endpoint** (Olver, *Asymptotics and Special Functions*, Ch. 6, Thm. 2.1 with the reference point
`a₁`, and Ch. 10, Thm. 3.1). Let `S` be open and order-connected with `a₁ ∈ S`, `A ≠ 0` twice
differentiable on `S`, `ξ' = A⁻²`, and let `A_0, …, A_n` satisfy `A_0' = 0` and
`A² A_s'' + 2 A A' A_s' + (A A'' - g A²) A_s = -2 A_{s+1}'`. Then for `u > 0` the equation
`w'' = (u² A⁻⁴ + g) w` has a solution `w = A exp (u ξ) (∑_{s<n} A_s / u^s + ε)` on
`S ∩ (a₁, ∞)` with

`|ε x| ≤ u^{-n} V_{a₁,x}(A_n) exp (V x / (2u))`,
`|A² ε'| ≤ 2u · u^{-n} V_{a₁,x}(A_n) exp (V x / (2u))`,

where `V_{a₁,x}(A_n) = ∫_{a₁}^x |A_n'|` and `V x = ∫_{a₁}^x |A A'' - g A²|`. Note that the series
is `lgSeries (-u) A_s = ∑ A_s / u^s`; the recessive companion is `∑ (-1)^s A_s / u^s`. -/
theorem exists_solution_expansion_dominant_exp_finite_endpoint {S : Set ℝ} {a₁ u : ℝ}
    (hS : IsOpen S)
    (hSc : S.OrdConnected) (ha : a₁ ∈ S) (hu : 0 < u) {A A' A'' ξ g : ℝ → ℝ}
    (hA : ∀ x ∈ S, A x ≠ 0)
    (hA' : ∀ x ∈ S, HasDerivAt A (A' x) x)
    (hA'' : ∀ x ∈ S, HasDerivAt A' (A'' x) x)
    (hA''c : ContinuousOn A'' S) (hgc : ContinuousOn g S)
    (hξ : ∀ x ∈ S, HasDerivAt ξ ((A x ^ 2)⁻¹) x)
    {n : ℕ} {As Ad Ad2 : ℕ → ℝ → ℝ}
    (hAs : ∀ s < n, ∀ x ∈ S, HasDerivAt (As s) (Ad s x) x)
    (hAd : ∀ s < n, ∀ x ∈ S, HasDerivAt (Ad s) (Ad2 s x) x)
    (hAd2c : ∀ s < n, ContinuousOn (Ad2 s) S)
    (h0 : ∀ x ∈ S, Ad 0 x = 0)
    (hrec : ∀ s < n, ∀ x ∈ S, A x ^ 2 * Ad2 s x + 2 * A x * A' x * Ad s x +
      (A x * A'' x - g x * A x ^ 2) * As s x = -(2 * Ad (s + 1) x)) :
    ∃ ε ε' w' : ℝ → ℝ, ∀ x ∈ S, a₁ < x →
      HasDerivAt ε (ε' x) x ∧
      HasDerivAt (fun y => A y * Real.exp (u * ξ y) * (lgSeries (-u) As n y + ε y)) (w' x) x ∧
      HasDerivAt w' ((u ^ 2 * (A x ^ 4)⁻¹ + g x) *
        (A x * Real.exp (u * ξ x) * (lgSeries (-u) As n x + ε x))) x ∧
      |ε x| ≤ (∫ t in a₁..x, |Ad n t|) / u ^ n *
        Real.exp ((∫ t in a₁..x, |A t * A'' t - g t * A t ^ 2|) / (2 * u)) ∧
      |A x ^ 2 * ε' x| ≤ 2 * u * ((∫ t in a₁..x, |Ad n t|) / u ^ n) *
        Real.exp ((∫ t in a₁..x, |A t * A'' t - g t * A t ^ 2|) / (2 * u)) := by
  obtain ⟨hE0, hE, hEle, hK⟩ := dominant_exp_kernel_properties hSc hu hξ
  obtain ⟨ε, ε', w', H⟩ := exists_solution_expansion_finite_endpoint (𝕜 := ℝ) hS hSc ha
    (κ := 1 / (2 * u)) (k := -u) (A := A) (A' := A') (A'' := A'')
    (E := fun y => Real.exp (u * ξ y)) (g := g)
    (neg_ne_zero.2 hu.ne') (by positivity) hA hA' hA'' hA''c hgc hE0 hE
    (fun x hx t hat htx => hEle x hx t (Icc_subset_of_ordConnected hSc ha hx ⟨hat.le, htx⟩) htx)
    (fun x hx t hat htx => hK x hx t (Icc_subset_of_ordConnected hSc ha hx ⟨hat.le, htx⟩) htx)
    hAs hAd hAd2c h0 hrec
  refine ⟨ε, ε', w', fun x hx hax => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := H x hx hax
  simp only [Real.norm_eq_abs, abs_neg, abs_of_pos hu] at h4 h5
  have hV : 1 / (2 * u) * ∫ t in a₁..x, |A t * A'' t - g t * A t ^ 2| =
      (∫ t in a₁..x, |A t * A'' t - g t * A t ^ 2|) / (2 * u) := by ring
  rw [hV] at h4 h5
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · simpa [neg_sq] using h3
  · convert h4 using 2
    field_simp
  · convert h5 using 2
    field_simp

/-- **Liouville–Green expansions, oscillatory case, errors controlled from a finite endpoint**
(Olver, *Asymptotics and Special Functions*, Ch. 6, Thm. 2.2 with the reference point `a₁`, and
Ch. 10, §3). Let `S` be open and order-connected with `a₁ ∈ S`, `A ≠ 0` real and twice
differentiable on `S`, `ξ' = A⁻²`, and let the complex coefficients `A_0, …, A_n` satisfy
`A_0' = 0` and `A² A_s'' + 2 A A' A_s' + (A A'' - g A²) A_s = -2 A_{s+1}'`. Then for real
`u ≠ 0` the equation `w'' = (-u² A⁻⁴ + g) w` has a complex solution
`w = A exp (-i u ξ) (∑_{s<n} (-1)^s A_s / (i u)^s + ε)` on `S ∩ (a₁, ∞)` with

`‖ε x‖ ≤ 2 |u|^{-n} V_{a₁,x}(A_n) exp (V x / |u|)`,
`‖A² ε'‖ ≤ 2 |u|^{1-n} V_{a₁,x}(A_n) exp (V x / |u|)`,

where `V_{a₁,x}(A_n) = ∫_{a₁}^x ‖A_n'‖` and `V x = ∫_{a₁}^x |A A'' - g A²|`. -/
lemma exists_solution_expansion_oscillatory_finite_endpoint {S : Set ℝ} {a₁ u : ℝ} -- PATCH: was `private lemma`; now public, proof unchanged
    (hS : IsOpen S)
    (hSc : S.OrdConnected) (ha : a₁ ∈ S) (hu : u ≠ 0) {A A' A'' ξ g : ℝ → ℝ}
    (hA : ∀ x ∈ S, A x ≠ 0)
    (hA' : ∀ x ∈ S, HasDerivAt A (A' x) x)
    (hA'' : ∀ x ∈ S, HasDerivAt A' (A'' x) x)
    (hA''c : ContinuousOn A'' S) (hgc : ContinuousOn g S)
    (hξ : ∀ x ∈ S, HasDerivAt ξ ((A x ^ 2)⁻¹) x)
    {n : ℕ} {As Ad Ad2 : ℕ → ℝ → ℂ}
    (hAs : ∀ s < n, ∀ x ∈ S, HasDerivAt (As s) (Ad s x) x)
    (hAd : ∀ s < n, ∀ x ∈ S, HasDerivAt (Ad s) (Ad2 s x) x)
    (hAd2c : ∀ s < n, ContinuousOn (Ad2 s) S)
    (h0 : ∀ x ∈ S, Ad 0 x = 0)
    (hrec : ∀ s < n, ∀ x ∈ S, (A x : ℂ) ^ 2 * Ad2 s x + 2 * (A x : ℂ) * (A' x : ℂ) * Ad s x +
      ((A x : ℂ) * (A'' x : ℂ) - (g x : ℂ) * (A x : ℂ) ^ 2) * As s x = -(2 * Ad (s + 1) x)) :
    ∃ ε ε' w' : ℝ → ℂ, ∀ x ∈ S, a₁ < x →
      HasDerivAt ε (ε' x) x ∧
      HasDerivAt (fun y => (A y : ℂ) * Complex.exp (-(Complex.I * u * ξ y)) *
        (lgSeries (Complex.I * u) As n y + ε y)) (w' x) x ∧
      HasDerivAt w' (((-(u ^ 2 * (A x ^ 4)⁻¹) + g x : ℝ) : ℂ) *
        ((A x : ℂ) * Complex.exp (-(Complex.I * u * ξ x)) *
          (lgSeries (Complex.I * u) As n x + ε x))) x ∧
      ‖ε x‖ ≤ 2 * (∫ t in a₁..x, ‖Ad n t‖) / |u| ^ n *
        Real.exp ((∫ t in a₁..x, |A t * A'' t - g t * A t ^ 2|) / |u|) ∧
      ‖(A x : ℂ) ^ 2 * ε' x‖ ≤ 2 * |u| * ((∫ t in a₁..x, ‖Ad n t‖) / |u| ^ n) *
        Real.exp ((∫ t in a₁..x, |A t * A'' t - g t * A t ^ 2|) / |u|) := by
  set E : ℝ → ℂ := fun y => Complex.exp (-(Complex.I * u * ξ y)) with hEdef
  have hEn : ∀ y, ‖E y‖ = 1 := fun y => by
    simp [hEdef, Complex.norm_exp]
  have hu' : 0 < |u| := abs_pos.2 hu
  have hnorm : ∀ t, ‖(A t : ℂ) * (A'' t : ℂ) - (g t : ℂ) * (A t : ℂ) ^ 2‖ =
      |A t * A'' t - g t * A t ^ 2| := fun t => by
    have : ((A t * A'' t - g t * A t ^ 2 : ℝ) : ℂ) =
        (A t : ℂ) * (A'' t : ℂ) - (g t : ℂ) * (A t : ℂ) ^ 2 := by push_cast; ring
    rw [← this, Complex.norm_real, Real.norm_eq_abs]
  obtain ⟨ε, ε', w', H⟩ := exists_solution_expansion_finite_endpoint (𝕜 := ℂ) hS hSc ha
    (κ := 1 / |u|) (k := Complex.I * u) (A := fun y => (A y : ℂ)) (A' := fun y => (A' y : ℂ))
    (A'' := fun y => (A'' y : ℂ)) (E := E) (g := fun y => (g y : ℂ))
    (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.2 hu)) (by positivity)
    (fun x hx => Complex.ofReal_ne_zero.2 (hA x hx))
    (fun x hx => (hA' x hx).ofReal_comp) (fun x hx => (hA'' x hx).ofReal_comp)
    (Complex.continuous_ofReal.comp_continuousOn hA''c)
    (Complex.continuous_ofReal.comp_continuousOn hgc)
    (fun x _ => by rw [← norm_ne_zero_iff, hEn]; exact one_ne_zero)
    (fun x hx => by
      have := (((hξ x hx).ofReal_comp.const_mul (Complex.I * u)).neg).cexp
      refine this.congr_deriv ?_
      simp only [hEdef, Pi.neg_apply]
      push_cast
      ring)
    (fun x _ t _ _ => by rw [hEn, hEn])
    (fun x _ t _ _ => by
      rw [norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
      have : ‖1 - E t ^ 2 / E x ^ 2‖ ≤ 2 := (norm_sub_le _ _).trans (by
        rw [norm_div, norm_pow, norm_pow, hEn, hEn]; norm_num)
      calc ‖1 - E t ^ 2 / E x ^ 2‖ / (‖(2 : ℂ)‖ * (1 * |u|)) ≤ 2 / (2 * (1 * |u|)) := by
            rw [Complex.norm_two]
            gcongr
        _ = 1 / |u| := by field_simp)
    hAs hAd hAd2c h0 hrec
  have hV : ∀ x, ∫ t in a₁..x, ‖(A t : ℂ) * (A'' t : ℂ) - (g t : ℂ) * (A t : ℂ) ^ 2‖ =
      ∫ t in a₁..x, |A t * A'' t - g t * A t ^ 2| := fun x => by
    congr 1
    ext t
    exact hnorm t
  refine ⟨ε, ε', w', fun x hx hax => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := H x hx hax
  rw [hV] at h4 h5
  have hk : ‖Complex.I * (u : ℂ)‖ = |u| := by
    rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
  rw [hk] at h4 h5
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · convert h3 using 2
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  · convert h4 using 1
    rw [show 1 / |u| * ∫ t in a₁..x, |A t * A'' t - g t * A t ^ 2| =
      (∫ t in a₁..x, |A t * A'' t - g t * A t ^ 2|) / |u| by ring]
    field_simp
  · convert h5 using 1
    rw [show 1 / |u| * ∫ t in a₁..x, |A t * A'' t - g t * A t ^ 2| =
      (∫ t in a₁..x, |A t * A'' t - g t * A t ^ 2|) / |u| by ring]
    field_simp

end Real

/-! ### Wronskians and the two-dimensional solution space -/

section Wronskian

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The **Wronskian** `w₁ w₂' - w₁' w₂` of two solutions of `w'' = q w` is constant on an open
preconnected set. -/
private lemma wronskian_eq_of_mem {S : Set ℝ} (hS : IsOpen S) (hSc : IsPreconnected S)
    {q w₁ w₁' w₂ w₂' : ℝ → 𝕜}
    (h₁ : ∀ x ∈ S, HasDerivAt w₁ (w₁' x) x) (h₁' : ∀ x ∈ S, HasDerivAt w₁' (q x * w₁ x) x)
    (h₂ : ∀ x ∈ S, HasDerivAt w₂ (w₂' x) x) (h₂' : ∀ x ∈ S, HasDerivAt w₂' (q x * w₂ x) x)
    {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    w₁ x * w₂' x - w₁' x * w₂ x = w₁ y * w₂' y - w₁' y * w₂ y := by
  have hd : ∀ z ∈ S, HasDerivAt (fun z => w₁ z * w₂' z - w₁' z * w₂ z) 0 z := fun z hz =>
    (((h₁ z hz).mul (h₂' z hz)).sub ((h₁' z hz).mul (h₂ z hz))).congr_deriv (by ring)
  exact hS.is_const_of_deriv_eq_zero hSc
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv) hx hy

/-- **The solution space is two-dimensional.** If `w₁`, `w₂` solve `w'' = q w` on an open
preconnected set `S` and their Wronskian does not vanish at one point of `S`, then every solution
`y` of the same equation is a linear combination `c₁ w₁ + c₂ w₂` on `S` (together with its
derivative). -/
private lemma eq_linear_combination_of_wronskian_ne_zero {S : Set ℝ} (hS : IsOpen S)
    (hSc : IsPreconnected S)
    {q y y' w₁ w₁' w₂ w₂' : ℝ → 𝕜}
    (hy : ∀ x ∈ S, HasDerivAt y (y' x) x) (hy' : ∀ x ∈ S, HasDerivAt y' (q x * y x) x)
    (h₁ : ∀ x ∈ S, HasDerivAt w₁ (w₁' x) x) (h₁' : ∀ x ∈ S, HasDerivAt w₁' (q x * w₁ x) x)
    (h₂ : ∀ x ∈ S, HasDerivAt w₂ (w₂' x) x) (h₂' : ∀ x ∈ S, HasDerivAt w₂' (q x * w₂ x) x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ S) (hW : w₁ x₀ * w₂' x₀ - w₁' x₀ * w₂ x₀ ≠ 0) :
    ∃ c₁ c₂ : 𝕜, ∀ x ∈ S, y x = c₁ * w₁ x + c₂ * w₂ x ∧ y' x = c₁ * w₁' x + c₂ * w₂' x := by
  set W := w₁ x₀ * w₂' x₀ - w₁' x₀ * w₂ x₀ with hWdef
  set c₁ := (y x₀ * w₂' x₀ - y' x₀ * w₂ x₀) / W
  set c₂ := (w₁ x₀ * y' x₀ - w₁' x₀ * y x₀) / W
  set Y : ℝ → 𝕜 := fun x => y x - c₁ * w₁ x - c₂ * w₂ x with hY
  set Y' : ℝ → 𝕜 := fun x => y' x - c₁ * w₁' x - c₂ * w₂' x with hY'
  have hYd : ∀ x ∈ S, HasDerivAt Y (Y' x) x := fun x hx =>
    (((hy x hx).sub ((h₁ x hx).const_mul c₁)).sub ((h₂ x hx).const_mul c₂))
  have hY'd : ∀ x ∈ S, HasDerivAt Y' (q x * Y x) x := fun x hx =>
    ((((hy' x hx).sub ((h₁' x hx).const_mul c₁)).sub ((h₂' x hx).const_mul c₂))).congr_deriv
      (by simp only [hY]; ring)
  have hY0 : Y x₀ = 0 := by
    simp only [hY, c₁, c₂]
    field_simp
    ring
  have hY'0 : Y' x₀ = 0 := by
    simp only [hY', c₁, c₂]
    field_simp
    ring
  refine ⟨c₁, c₂, fun x hx => ?_⟩
  have e1 := wronskian_eq_of_mem hS hSc hYd hY'd h₁ h₁' hx hx₀
  have e2 := wronskian_eq_of_mem hS hSc hYd hY'd h₂ h₂' hx hx₀
  have e3 := wronskian_eq_of_mem hS hSc h₁ h₁' h₂ h₂' hx hx₀
  rw [hY0, hY'0, zero_mul, zero_mul, sub_zero] at e1 e2
  rw [← hWdef] at e3
  have hYx : Y x = 0 := by
    have : Y x * W = 0 := by rw [← e3]; linear_combination w₁ x * e2 - w₂ x * e1
    exact (mul_eq_zero.1 this).resolve_right hW
  have hY'x : Y' x = 0 := by
    have : Y' x * W = 0 := by rw [← e3]; linear_combination w₁' x * e2 - w₂' x * e1
    exact (mul_eq_zero.1 this).resolve_right hW
  constructor
  · linear_combination hYx
  · linear_combination hY'x

end Wronskian

end LiouvilleGreen
