/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Power-series uniqueness for second-order linear ODEs

We consider the second-order linear equation

`f'' = p f' + q f`

near a point `x₀`, with smooth (or analytic) coefficients `p` and `q`, together with
uniqueness and existence on real intervals.

## Main results

* `iteratedDeriv_add_two_of_eventuallyEq`: differentiating the equation `n` times with the
  Leibniz rule expresses `f⁽ⁿ⁺²⁾(x₀)` through the lower derivatives of `f` and the derivatives
  of `p`, `q` at `x₀`. This is the recurrence for the Taylor coefficients obtained by
  substituting a power series.
* `iteratedDeriv_eq_of_eventuallyEq`: two smooth solutions with the same value and first
  derivative at `x₀` have the same derivatives of all orders at `x₀`.
* `eventuallyEq_of_eventuallyEq_ode`, `eqOn_of_ode`: for analytic solutions over any
  complete field of characteristic zero (`ℝ`, `ℂ`, …), the value and derivative at `x₀`
  determine the solution near `x₀`, and on every preconnected open set on which it is
  analytic and solves the equation.
* `eventually_ode_of_iteratedDeriv`: conversely, an analytic function whose derivatives at
  `x₀` satisfy the recurrence solves the equation near `x₀`.
* `iteratedDeriv_pow_mul_zero`: the `n`-th derivative of `x ^ m * g x` at `0`, the
  ingredient for polynomial coefficients.
* `eqOn_Icc_of_linear_ode`, `eqOn_of_linear_ode`, `eq_of_linear_ode`:
  real-variable uniqueness (Grönwall, via Mathlib's `ODE_solution_unique_of_mem_Icc`) for
  second-order equations on a compact interval, an open interval, or `ℝ`, with values in any
  normed space and coefficients in any normed field.
* `eqOn_Icc_of_linear_system`: the same for linear `2 × 2` first-order systems on `[a, b]`
  with one-sided derivatives at the endpoints and data prescribed at any `t₀ ∈ [a, b]`.
* `exists_hasDerivWithinAt_Icc_of_lipschitz`, `exists_linear_system_Icc`: global
  existence on `[a, b]` for globally Lipschitz fields with `v t 0 = 0` (via Mathlib's
  `IsPicardLindelof` on short subintervals and gluing), in particular for linear `2 × 2` systems.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace ODE

/-! ### The Taylor recurrence -/

section Recurrence

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸]
  {f g p q : 𝕜 → 𝔸} {x₀ : 𝕜}

/-- **Taylor recurrence** for `f'' = p f' + q f`: differentiating the equation `n` times at
`x₀` with the Leibniz rule gives
`f⁽ⁿ⁺²⁾(x₀) = ∑_{i ≤ n} C(n,i) (p⁽ⁱ⁾(x₀) f⁽ⁿ⁻ⁱ⁺¹⁾(x₀) + q⁽ⁱ⁾(x₀) f⁽ⁿ⁻ⁱ⁾(x₀))`. -/
theorem iteratedDeriv_add_two_of_eventuallyEq (hf : ContDiffAt 𝕜 ∞ f x₀)
    (hp : ContDiffAt 𝕜 ∞ p x₀) (hq : ContDiffAt 𝕜 ∞ q x₀)
    (hode : ∀ᶠ x in 𝓝 x₀, deriv (deriv f) x = p x * deriv f x + q x * f x) (n : ℕ) :
    iteratedDeriv (n + 2) f x₀ = ∑ i ∈ Finset.range (n + 1), (n.choose i : 𝔸) *
      (iteratedDeriv i p x₀ * iteratedDeriv (n - i + 1) f x₀ +
        iteratedDeriv i q x₀ * iteratedDeriv (n - i) f x₀) := by
  have hf' : ContDiffAt 𝕜 n (deriv f) x₀ := hf.derivWithin (by
    exact_mod_cast le_top)
  have hp' : ContDiffAt 𝕜 n p x₀ := hp.of_le (by exact_mod_cast le_top)
  have hq' : ContDiffAt 𝕜 n q x₀ := hq.of_le (by exact_mod_cast le_top)
  have hf'' : ContDiffAt 𝕜 n f x₀ := hf.of_le (by exact_mod_cast le_top)
  have hE : deriv (deriv f) =ᶠ[𝓝 x₀] fun x => p x * deriv f x + q x * f x := hode
  rw [iteratedDeriv_succ', iteratedDeriv_succ', hE.iteratedDeriv_eq n,
    iteratedDeriv_fun_add (hp'.mul hf') (hq'.mul hf''), iteratedDeriv_fun_mul hp' hf',
    iteratedDeriv_fun_mul hq' hf'', ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← iteratedDeriv_succ', mul_add, mul_assoc, mul_assoc]

/-- Two smooth solutions of `f'' = p f' + q f` with the same value and first derivative at `x₀`
have the same derivatives of all orders at `x₀`. -/
theorem iteratedDeriv_eq_of_eventuallyEq (hf : ContDiffAt 𝕜 ∞ f x₀) (hg : ContDiffAt 𝕜 ∞ g x₀)
    (hp : ContDiffAt 𝕜 ∞ p x₀) (hq : ContDiffAt 𝕜 ∞ q x₀)
    (hfode : ∀ᶠ x in 𝓝 x₀, deriv (deriv f) x = p x * deriv f x + q x * f x)
    (hgode : ∀ᶠ x in 𝓝 x₀, deriv (deriv g) x = p x * deriv g x + q x * g x)
    (h₀ : f x₀ = g x₀) (h₁ : deriv f x₀ = deriv g x₀) (n : ℕ) :
    iteratedDeriv n f x₀ = iteratedDeriv n g x₀ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simpa using h₀
    | 1, _ => simpa using h₁
    | k + 2, ih =>
      rw [iteratedDeriv_add_two_of_eventuallyEq hf hp hq hfode,
        iteratedDeriv_add_two_of_eventuallyEq hg hp hq hgode]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ih (k - i + 1) (by omega), ih (k - i) (by omega)]

/-- The `n`-th derivative of `x ^ m * g x` at `0` is `n (n-1) ⋯ (n-m+1) g⁽ⁿ⁻ᵐ⁾(0)`
(which vanishes for `n < m`). -/
theorem iteratedDeriv_pow_mul_zero {n : ℕ} {g : 𝕜 → 𝕜} (hg : ContDiffAt 𝕜 n g 0) (m : ℕ) :
    iteratedDeriv n (fun x => x ^ m * g x) 0 = n.descFactorial m * iteratedDeriv (n - m) g 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop : ContDiffAt 𝕜 n (fun x : 𝕜 => x ^ m) 0) hg]
  simp only [iteratedDeriv_fun_pow_zero]
  by_cases hm : m ≤ n
  · rw [Finset.sum_eq_single m]
    · simp [Nat.descFactorial_eq_factorial_mul_choose, mul_comm]
    · intro i _ hi; simp [hi]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Finset.sum_eq_zero]
    · simp
    · intro i hi
      have : i ≠ m := by have := Finset.mem_range.mp hi; omega
      simp [this]

end Recurrence

/-! ### Analytic solutions -/

section Analytic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
  {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸] [CompleteSpace 𝔸]
  {f g p q : 𝕜 → 𝔸} {x₀ : 𝕜}

/-- **Uniqueness of analytic solutions**: two analytic solutions of `f'' = p f' + q f` near `x₀`
with the same value and first derivative at `x₀` agree near `x₀`. -/
theorem eventuallyEq_of_eventuallyEq_ode (hf : AnalyticAt 𝕜 f x₀) (hg : AnalyticAt 𝕜 g x₀)
    (hp : ContDiffAt 𝕜 ∞ p x₀) (hq : ContDiffAt 𝕜 ∞ q x₀)
    (hfode : ∀ᶠ x in 𝓝 x₀, deriv (deriv f) x = p x * deriv f x + q x * f x)
    (hgode : ∀ᶠ x in 𝓝 x₀, deriv (deriv g) x = p x * deriv g x + q x * g x)
    (h₀ : f x₀ = g x₀) (h₁ : deriv f x₀ = deriv g x₀) : f =ᶠ[𝓝 x₀] g := by
  have hD := iteratedDeriv_eq_of_eventuallyEq hf.contDiffAt hg.contDiffAt hp hq hfode hgode h₀ h₁
  have htop : analyticOrderAt (f - g) x₀ = ⊤ := by
    refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf.sub hg)]
    intro i _
    rw [iteratedDeriv_sub hf.contDiffAt hg.contDiffAt, hD i, sub_self]
  filter_upwards [analyticOrderAt_eq_top.mp htop] with x hx
  simpa [sub_eq_zero] using hx

/-- **Uniqueness of analytic solutions** on a preconnected open set: two functions analytic on
`U` solving `f'' = p f' + q f` there, with the same value and first derivative at one point
`x₀ ∈ U`, agree on `U`. -/
theorem eqOn_of_ode {U : Set 𝕜} (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U) {x₀ : 𝕜} (hx₀ : x₀ ∈ U)
    (hp : ContDiffAt 𝕜 ∞ p x₀) (hq : ContDiffAt 𝕜 ∞ q x₀)
    (hfode : ∀ x ∈ U, deriv (deriv f) x = p x * deriv f x + q x * f x)
    (hgode : ∀ x ∈ U, deriv (deriv g) x = p x * deriv g x + q x * g x)
    (h₀ : f x₀ = g x₀) (h₁ : deriv f x₀ = deriv g x₀) : EqOn f g U :=
  hf.eqOn_of_preconnected_of_eventuallyEq hg hU' hx₀ <|
    eventuallyEq_of_eventuallyEq_ode (hf x₀ hx₀) (hg x₀ hx₀) hp hq
      (eventually_of_mem (hU.mem_nhds hx₀) hfode) (eventually_of_mem (hU.mem_nhds hx₀) hgode)
      h₀ h₁

/-- **Converse of the Taylor recurrence**: if `f`, `p`, `q` are analytic at `x₀` and the
derivatives of `f` at `x₀` satisfy the recurrence of
`ODE.iteratedDeriv_add_two_of_eventuallyEq`, then `f'' = p f' + q f` near `x₀`. -/
theorem eventually_ode_of_iteratedDeriv (hf : AnalyticAt 𝕜 f x₀) (hp : AnalyticAt 𝕜 p x₀)
    (hq : AnalyticAt 𝕜 q x₀)
    (hrec : ∀ n : ℕ, iteratedDeriv (n + 2) f x₀ = ∑ i ∈ Finset.range (n + 1), (n.choose i : 𝔸) *
      (iteratedDeriv i p x₀ * iteratedDeriv (n - i + 1) f x₀ +
        iteratedDeriv i q x₀ * iteratedDeriv (n - i) f x₀)) :
    ∀ᶠ x in 𝓝 x₀, deriv (deriv f) x = p x * deriv f x + q x * f x := by
  have hf1 : AnalyticAt 𝕜 (deriv f) x₀ := hf.deriv
  have hf2 : AnalyticAt 𝕜 (deriv (deriv f)) x₀ := hf1.deriv
  have hR : AnalyticAt 𝕜 (fun x => p x * deriv f x + q x * f x) x₀ :=
    (hp.mul hf1).add (hq.mul hf)
  have htop : analyticOrderAt (deriv (deriv f) - fun x => p x * deriv f x + q x * f x) x₀ = ⊤ := by
    refine ENat.eq_top_iff_forall_ge.mpr fun N => ?_
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf2.sub hR)]
    intro n _
    rw [iteratedDeriv_sub hf2.contDiffAt hR.contDiffAt, ← iteratedDeriv_succ',
        ← iteratedDeriv_succ',
      hrec n, iteratedDeriv_fun_add (hp.contDiffAt.mul hf1.contDiffAt)
          (hq.contDiffAt.mul hf.contDiffAt),
      iteratedDeriv_fun_mul hp.contDiffAt hf1.contDiffAt,
      iteratedDeriv_fun_mul hq.contDiffAt hf.contDiffAt, ← Finset.sum_add_distrib, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← iteratedDeriv_succ', mul_add, mul_assoc, mul_assoc]
  filter_upwards [analyticOrderAt_eq_top.mp htop] with x hx
  simpa [sub_eq_zero] using hx

end Analytic

/-! ### Real-variable uniqueness on intervals -/

section Real

variable {𝕜 : Type*} [NormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace 𝕜 E] {p q : ℝ → 𝕜} {f f' g g' : ℝ → E}

omit [NormedSpace ℝ E] in
/-- The first-order system `(y, y')' = (y', p y' + q y)` is Lipschitz in `(y, y')` with constant
`1 + P + Q` when `‖p t‖ ≤ P` and `‖q t‖ ≤ Q`. -/
theorem lipschitzWith_linear_ode_system {t P Q : ℝ} (hP : ‖p t‖ ≤ P) (hQ : ‖q t‖ ≤ Q) :
    LipschitzWith ⟨1 + P + Q, by linarith [norm_nonneg (p t), norm_nonneg (q t)]⟩
      (fun y : E × E => (y.2, p t • y.2 + q t • y.1)) := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  have h1 : dist y.1 z.1 ≤ dist y z := by rw [Prod.dist_eq]; exact le_max_left _ _
  have h2 : dist y.2 z.2 ≤ dist y z := by rw [Prod.dist_eq]; exact le_max_right _ _
  have hd := dist_nonneg (x := y) (y := z)
  have hp0 := norm_nonneg (p t)
  have hq0 := norm_nonneg (q t)
  rw [Prod.dist_eq]
  change _ ≤ (1 + P + Q) * dist y z
  refine max_le (by nlinarith) ?_
  calc dist (p t • y.2 + q t • y.1) (p t • z.2 + q t • z.1)
      ≤ dist (p t • y.2) (p t • z.2) + dist (q t • y.1) (q t • z.1) := dist_add_add_le _ _ _ _
    _ = ‖p t‖ * dist y.2 z.2 + ‖q t‖ * dist y.1 z.1 := by rw [dist_smul₀, dist_smul₀]
    _ ≤ (1 + P + Q) * dist y z := by nlinarith

/-- **Uniqueness for second-order linear ODEs on a compact interval**: let `p`, `q` be continuous
on `[c, d]` and let `f`, `g` (with derivatives `f'`, `g'`) solve `y'' = p y' + q y` on `[c, d]`.
If `f` and `g` have the same value and derivative at an interior point `t₀`, then `f = g` and
`f' = g'` on `[c, d]`. -/
theorem eqOn_Icc_of_linear_ode {c d t₀ : ℝ} (ht₀ : t₀ ∈ Ioo c d)
    (hp : ContinuousOn p (Icc c d)) (hq : ContinuousOn q (Icc c d))
    (hf : ∀ t ∈ Icc c d, HasDerivAt f (f' t) t ∧ HasDerivAt f' (p t • f' t + q t • f t) t)
    (hg : ∀ t ∈ Icc c d, HasDerivAt g (g' t) t ∧ HasDerivAt g' (p t • g' t + q t • g t) t)
    (h₀ : f t₀ = g t₀) (h₁ : f' t₀ = g' t₀) :
    EqOn f g (Icc c d) ∧ EqOn f' g' (Icc c d) := by
  obtain ⟨P, hP⟩ := isCompact_Icc.exists_bound_of_continuousOn hp
  obtain ⟨Q, hQ⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  have hP0 : 0 ≤ P := (norm_nonneg _).trans (hP t₀ (Ioo_subset_Icc_self ht₀))
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ t₀ (Ioo_subset_Icc_self ht₀))
  set v : ℝ → E × E → E × E := fun t y => (y.2, p t • y.2 + q t • y.1)
  have hv : ∀ t ∈ Ioo c d,
      LipschitzOnWith ⟨1 + P + Q, by linarith⟩ (v t) (univ : Set (E × E)) := fun t ht =>
    (lipschitzWith_linear_ode_system (hP t (Ioo_subset_Icc_self ht))
      (hQ t (Ioo_subset_Icc_self ht))).lipschitzOnWith
  have hF : ∀ t ∈ Icc c d, HasDerivAt (fun t => (f t, f' t)) (v t (f t, f' t)) t :=
    fun t ht => (hf t ht).1.prodMk (hf t ht).2
  have hG : ∀ t ∈ Icc c d, HasDerivAt (fun t => (g t, g' t)) (v t (g t, g' t)) t :=
    fun t ht => (hg t ht).1.prodMk (hg t ht).2
  have h := ODE_solution_unique_of_mem_Icc hv ht₀
    (fun t ht => (hF t ht).continuousAt.continuousWithinAt)
    (fun t ht => hF t (Ioo_subset_Icc_self ht)) (fun _ _ => mem_univ _)
    (fun t ht => (hG t ht).continuousAt.continuousWithinAt)
    (fun t ht => hG t (Ioo_subset_Icc_self ht)) (fun _ _ => mem_univ _)
    (by simp [h₀, h₁])
  exact ⟨fun t ht => congrArg Prod.fst (h ht), fun t ht => congrArg Prod.snd (h ht)⟩

/-- **Uniqueness for second-order linear ODEs on an interval**: let `I` be an open interval (an
open order-connected subset of `ℝ`), let `p`, `q` be continuous on `I`, and let `f`, `g` (with
derivatives `f'`, `g'`) solve `y'' = p y' + q y` on `I`. If `f` and `g` have the same value and
derivative at one point `t₀ ∈ I`, then `f = g` and `f' = g'` on `I`. -/
theorem eqOn_of_linear_ode {I : Set ℝ} (hI : IsOpen I) (hI' : I.OrdConnected) {t₀ : ℝ}
    (ht₀ : t₀ ∈ I) (hp : ContinuousOn p I) (hq : ContinuousOn q I)
    (hf : ∀ t ∈ I, HasDerivAt f (f' t) t ∧ HasDerivAt f' (p t • f' t + q t • f t) t)
    (hg : ∀ t ∈ I, HasDerivAt g (g' t) t ∧ HasDerivAt g' (p t • g' t + q t • g t) t)
    (h₀ : f t₀ = g t₀) (h₁ : f' t₀ = g' t₀) :
    EqOn f g I ∧ EqOn f' g' I := by
  have key : ∀ t ∈ I, f t = g t ∧ f' t = g' t := by
    intro t ht
    have hm : min t t₀ ∈ I := by rcases min_choice t t₀ with h | h <;> rw [h] <;> assumption
    have hM : max t t₀ ∈ I := by rcases max_choice t t₀ with h | h <;> rw [h] <;> assumption
    obtain ⟨ε, hε, hεI⟩ := Metric.isOpen_iff.mp hI _ hm
    obtain ⟨δ, hδ, hδI⟩ := Metric.isOpen_iff.mp hI _ hM
    have hc : min t t₀ - ε / 2 ∈ I := hεI (by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith)]; linarith)
    have hd : max t t₀ + δ / 2 ∈ I := hδI (by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]; linarith)
    have hsub : Icc (min t t₀ - ε / 2) (max t t₀ + δ / 2) ⊆ I := hI'.out hc hd
    have ht₀' : t₀ ∈ Ioo (min t t₀ - ε / 2) (max t t₀ + δ / 2) :=
      ⟨by linarith [min_le_right t t₀], by linarith [le_max_right t t₀]⟩
    have htt : t ∈ Icc (min t t₀ - ε / 2) (max t t₀ + δ / 2) :=
      ⟨by linarith [min_le_left t t₀], by linarith [le_max_left t t₀]⟩
    have h := eqOn_Icc_of_linear_ode ht₀' (hp.mono hsub) (hq.mono hsub)
      (fun s hs => hf s (hsub hs)) (fun s hs => hg s (hsub hs)) h₀ h₁
    exact ⟨h.1 htt, h.2 htt⟩
  exact ⟨fun t ht => (key t ht).1, fun t ht => (key t ht).2⟩

/-- **Uniqueness for second-order linear ODEs on `ℝ`**: with `p`, `q` continuous, two global
solutions of `y'' = p y' + q y` with the same value and derivative at one point coincide. -/
theorem eq_of_linear_ode {t₀ : ℝ} (hp : Continuous p) (hq : Continuous q)
    (hf : ∀ t, HasDerivAt f (f' t) t ∧ HasDerivAt f' (p t • f' t + q t • f t) t)
    (hg : ∀ t, HasDerivAt g (g' t) t ∧ HasDerivAt g' (p t • g' t + q t • g t) t)
    (h₀ : f t₀ = g t₀) (h₁ : f' t₀ = g' t₀) : f = g ∧ f' = g' := by
  have h := eqOn_of_linear_ode isOpen_univ ordConnected_univ (mem_univ t₀) hp.continuousOn
    hq.continuousOn (fun t _ => hf t) (fun t _ => hg t) h₀ h₁
  exact ⟨funext fun t => h.1 (mem_univ t), funext fun t => h.2 (mem_univ t)⟩

omit [NormedSpace ℝ E] in
/-- The linear system `(u, v)' = (a₁₁ u + a₁₂ v, a₂₁ u + a₂₂ v)` is Lipschitz in `(u, v)` with
constant `A₁₁ + A₁₂ + A₂₁ + A₂₂` when `‖aᵢⱼ t‖ ≤ Aᵢⱼ`. -/
theorem lipschitzWith_linear_system {a₁₁ a₁₂ a₂₁ a₂₂ : ℝ → 𝕜} {t A₁₁ A₁₂ A₂₁ A₂₂ : ℝ}
    (h₁₁ : ‖a₁₁ t‖ ≤ A₁₁) (h₁₂ : ‖a₁₂ t‖ ≤ A₁₂) (h₂₁ : ‖a₂₁ t‖ ≤ A₂₁) (h₂₂ : ‖a₂₂ t‖ ≤ A₂₂) :
    LipschitzWith ⟨A₁₁ + A₁₂ + A₂₁ + A₂₂, by
        linarith [norm_nonneg (a₁₁ t), norm_nonneg (a₁₂ t), norm_nonneg (a₂₁ t),
          norm_nonneg (a₂₂ t)]⟩
      (fun y : E × E => (a₁₁ t • y.1 + a₁₂ t • y.2, a₂₁ t • y.1 + a₂₂ t • y.2)) := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  have h1 : dist y.1 z.1 ≤ dist y z := by rw [Prod.dist_eq]; exact le_max_left _ _
  have h2 : dist y.2 z.2 ≤ dist y z := by rw [Prod.dist_eq]; exact le_max_right _ _
  have hd := dist_nonneg (x := y) (y := z)
  have n11 := norm_nonneg (a₁₁ t)
  have n12 := norm_nonneg (a₁₂ t)
  have n21 := norm_nonneg (a₂₁ t)
  have n22 := norm_nonneg (a₂₂ t)
  rw [Prod.dist_eq]
  change _ ≤ (A₁₁ + A₁₂ + A₂₁ + A₂₂) * dist y z
  have key : ∀ (b c : 𝕜) (B C : ℝ), ‖b‖ ≤ B → ‖c‖ ≤ C →
      dist (b • y.1 + c • y.2) (b • z.1 + c • z.2) ≤ (B + C) * dist y z := by
    intro b c B C hB hC
    have := norm_nonneg b
    have := norm_nonneg c
    calc dist (b • y.1 + c • y.2) (b • z.1 + c • z.2)
        ≤ dist (b • y.1) (b • z.1) + dist (c • y.2) (c • z.2) := dist_add_add_le _ _ _ _
      _ = ‖b‖ * dist y.1 z.1 + ‖c‖ * dist y.2 z.2 := by rw [dist_smul₀, dist_smul₀]
      _ ≤ (B + C) * dist y z := by nlinarith
  have k1 := key _ _ _ _ h₁₁ h₁₂
  have k2 := key _ _ _ _ h₂₁ h₂₂
  refine max_le ?_ ?_
  · nlinarith
  · nlinarith

/-- **Uniqueness for linear `2 × 2` systems on a compact interval**: let the coefficients `aᵢⱼ`
be continuous on `[a, b]` and let `(u, v)` and `(u₁, v₁)` solve
`u' = a₁₁ u + a₁₂ v`, `v' = a₂₁ u + a₂₂ v` on `[a, b]` (one-sided derivatives at the endpoints).
If the two solutions agree at some `t₀ ∈ [a, b]`, they agree on `[a, b]`. -/
theorem eqOn_Icc_of_linear_system {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    {a₁₁ a₁₂ a₂₁ a₂₂ : ℝ → 𝕜} (c₁₁ : ContinuousOn a₁₁ (Icc a b))
    (c₁₂ : ContinuousOn a₁₂ (Icc a b)) (c₂₁ : ContinuousOn a₂₁ (Icc a b))
    (c₂₂ : ContinuousOn a₂₂ (Icc a b)) {u v u₁ v₁ : ℝ → E}
    (huv : ∀ t ∈ Icc a b, HasDerivWithinAt u (a₁₁ t • u t + a₁₂ t • v t) (Icc a b) t ∧
      HasDerivWithinAt v (a₂₁ t • u t + a₂₂ t • v t) (Icc a b) t)
    (huv₁ : ∀ t ∈ Icc a b, HasDerivWithinAt u₁ (a₁₁ t • u₁ t + a₁₂ t • v₁ t) (Icc a b) t ∧
      HasDerivWithinAt v₁ (a₂₁ t • u₁ t + a₂₂ t • v₁ t) (Icc a b) t)
    (h₀ : u t₀ = u₁ t₀) (h₁ : v t₀ = v₁ t₀) :
    EqOn u u₁ (Icc a b) ∧ EqOn v v₁ (Icc a b) := by
  obtain ⟨A₁₁, hA₁₁⟩ := isCompact_Icc.exists_bound_of_continuousOn c₁₁
  obtain ⟨A₁₂, hA₁₂⟩ := isCompact_Icc.exists_bound_of_continuousOn c₁₂
  obtain ⟨A₂₁, hA₂₁⟩ := isCompact_Icc.exists_bound_of_continuousOn c₂₁
  obtain ⟨A₂₂, hA₂₂⟩ := isCompact_Icc.exists_bound_of_continuousOn c₂₂
  have hK : 0 ≤ A₁₁ + A₁₂ + A₂₁ + A₂₂ := by
    linarith [(norm_nonneg _).trans (hA₁₁ t₀ ht₀), (norm_nonneg _).trans (hA₁₂ t₀ ht₀),
      (norm_nonneg _).trans (hA₂₁ t₀ ht₀), (norm_nonneg _).trans (hA₂₂ t₀ ht₀)]
  set V : ℝ → E × E → E × E :=
    fun t y => (a₁₁ t • y.1 + a₁₂ t • y.2, a₂₁ t • y.1 + a₂₂ t • y.2)
  have hV : ∀ t ∈ Icc a b, LipschitzOnWith ⟨_, hK⟩ (V t) (univ : Set (E × E)) := fun t ht =>
    (lipschitzWith_linear_system (hA₁₁ t ht) (hA₁₂ t ht) (hA₂₁ t ht) (hA₂₂ t ht)).lipschitzOnWith
  have hF : ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun t => (u t, v t)) (V t (u t, v t)) (Icc a b) t :=
    fun t ht => (huv t ht).1.prodMk (huv t ht).2
  have hG : ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun t => (u₁ t, v₁ t)) (V t (u₁ t, v₁ t)) (Icc a b) t :=
    fun t ht => (huv₁ t ht).1.prodMk (huv₁ t ht).2
  have hFc : ContinuousOn (fun t => (u t, v t)) (Icc a b) := fun t ht =>
      (hF t ht).continuousWithinAt
  have hGc : ContinuousOn (fun t => (u₁ t, v₁ t)) (Icc a b) :=
    fun t ht => (hG t ht).continuousWithinAt
  have heq : (fun t => (u t, v t)) t₀ = (fun t => (u₁ t, v₁ t)) t₀ := by simp [h₀, h₁]
  have hL : EqOn (fun t => (u t, v t)) (fun t => (u₁ t, v₁ t)) (Icc a t₀) := by
    have hs : Icc a t₀ ⊆ Icc a b := Icc_subset_Icc_right ht₀.2
    refine ODE_solution_unique_of_mem_Icc_left (fun t ht => hV t (hs (Ioc_subset_Icc_self ht)))
      (hFc.mono hs) (fun t ht => ?_) (fun _ _ => mem_univ _) (hGc.mono hs) (fun t ht => ?_)
      (fun _ _ => mem_univ _) heq
    · exact (hF t (hs (Ioc_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (mem_of_superset (Icc_mem_nhdsLE_of_mem ht) hs)
    · exact (hG t (hs (Ioc_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (mem_of_superset (Icc_mem_nhdsLE_of_mem ht) hs)
  have hR : EqOn (fun t => (u t, v t)) (fun t => (u₁ t, v₁ t)) (Icc t₀ b) := by
    have hs : Icc t₀ b ⊆ Icc a b := Icc_subset_Icc_left ht₀.1
    refine ODE_solution_unique_of_mem_Icc_right (fun t ht => hV t (hs (Ico_subset_Icc_self ht)))
      (hFc.mono hs) (fun t ht => ?_) (fun _ _ => mem_univ _) (hGc.mono hs) (fun t ht => ?_)
      (fun _ _ => mem_univ _) heq
    · exact (hF t (hs (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (mem_of_superset (Icc_mem_nhdsGE_of_mem ht) hs)
    · exact (hG t (hs (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (mem_of_superset (Icc_mem_nhdsGE_of_mem ht) hs)
  have h := hL.union hR
  rw [Icc_union_Icc_eq_Icc ht₀.1 ht₀.2] at h
  exact ⟨fun t ht => congrArg Prod.fst (h ht), fun t ht => congrArg Prod.snd (h ht)⟩

end Real

/-! ### Global existence for linear equations on compact intervals -/

section Existence

open Metric
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- One step of the global existence argument: from any initial value at `s`, a solution of
`x' = v t x` exists on `[s, s']` provided `(s' - s) (M + 1) ≤ 1/2`. -/
theorem exists_hasDerivWithinAt_Icc_of_lipschitz_step {v : ℝ → E → E} {M : ℝ≥0} {s s' : ℝ}
    (hss : s ≤ s') (hh : (s' - s) * (M + 1) ≤ 1 / 2)
    (hlip : ∀ t ∈ Icc s s', LipschitzWith M (v t)) (h0 : ∀ t ∈ Icc s s', v t 0 = 0)
    (hcont : ∀ x, ContinuousOn (fun t => v t x) (Icc s s')) (y : E) :
    ∃ β : ℝ → E, β s = y ∧
      ∀ t ∈ Icc s s', HasDerivWithinAt β (v t (β t)) (Icc s s') t := by
  have hbd : ∀ t ∈ Icc s s', ∀ x, ‖v t x‖ ≤ M * ‖x‖ := fun t ht x => by
    have := (hlip t ht).dist_le_mul x 0
    rwa [h0 t ht, dist_zero_right, dist_zero_right] at this
  set R : ℝ≥0 := ⟨‖y‖ + 1, by positivity⟩
  set L : ℝ≥0 := ⟨M * (2 * ‖y‖ + 1), by positivity⟩
  have hP : IsPicardLindelof v (tmin := s) (tmax := s') ⟨s, le_rfl, hss⟩ y R 0 L M := by
    refine ⟨fun t ht => (hlip t ht).lipschitzOnWith, fun x _ => hcont x, fun t ht x hx => ?_, ?_⟩
    · refine (hbd t ht x).trans ?_
      have : ‖x‖ ≤ 2 * ‖y‖ + 1 := by
        have := norm_le_of_mem_closedBall hx
        change ‖x‖ ≤ ‖y‖ + (‖y‖ + 1) at this; linarith
      change (M:ℝ) * ‖x‖ ≤ M * (2 * ‖y‖ + 1)
      exact mul_le_mul_of_nonneg_left this M.2
    · change (M:ℝ) * (2 * ‖y‖ + 1) * max (s' - s) (s - s) ≤ (‖y‖ + 1) - 0
      rw [sub_self, max_eq_left (by linarith)]
      have hM := M.2
      have hy := norm_nonneg y
      nlinarith
  obtain ⟨β, hβ0, hβ⟩ := hP.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨β, hβ0, hβ⟩

/-- **Global existence for Lipschitz linear-growth fields** (in particular linear ODEs): if
`v t` is `M`-Lipschitz with `v t 0 = 0` for `t ∈ [a, b]` and continuous in `t`, then for every
initial value `x₀` there is a solution of `x' = v t x` on `[a, b]` with `x a = x₀`. -/
theorem exists_hasDerivWithinAt_Icc_of_lipschitz {v : ℝ → E → E} {M : ℝ≥0} {a b : ℝ}
    (hab : a ≤ b) (hlip : ∀ t ∈ Icc a b, LipschitzWith M (v t)) (h0 : ∀ t ∈ Icc a b, v t 0 = 0)
    (hcont : ∀ x, ContinuousOn (fun t => v t x) (Icc a b)) (x₀ : E) :
    ∃ α : ℝ → E, α a = x₀ ∧ ∀ t ∈ Icc a b, HasDerivWithinAt α (v t (α t)) (Icc a b) t := by
  set h : ℝ := 1 / (2 * (M + 1)) with hh
  have hpos : 0 < h := by positivity
  have hstep : h * (M + 1) = 1 / 2 := by rw [hh]; field_simp
  -- `c n = min b (a + n h)`
  have key : ∀ n : ℕ, ∃ α : ℝ → E, α a = x₀ ∧ ∀ t ∈ Icc a (min b (a + n * h)),
      HasDerivWithinAt α (v t (α t)) (Icc a (min b (a + n * h))) t := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun _ => x₀, rfl, fun t ht => ?_⟩
      have : Icc a (min b (a + ((0:ℕ):ℝ) * h)) = {a} := by
        simp [min_eq_right hab]
      rw [this] at ht ⊢
      rw [mem_singleton_iff.mp ht]
      rw [← hasDerivWithinAt_sdiff_singleton, sdiff_self]
      exact HasFDerivWithinAt.of_notMem_closure (by simp)
    | succ n ih =>
      obtain ⟨α, hα0, hα⟩ := ih
      set c := min b (a + n * h)
      set c' := min b (a + (n + 1 : ℕ) * h)
      have hac : a ≤ c := le_min hab (by nlinarith [n.cast_nonneg (α := ℝ)])
      have hcc : c ≤ c' := min_le_min le_rfl (by push_cast; nlinarith)
      have hcb : c' ≤ b := min_le_left _ _
      have hlen : (c' - c) * (M + 1) ≤ 1 / 2 := by
        have : c' - c ≤ h := by
          have h1 : c' ≤ a + (n + 1 : ℕ) * h := min_le_right _ _
          rcases le_total b (a + n * h) with hb | hb
          · have : c = b := min_eq_left hb
            linarith
          · have : c = a + n * h := min_eq_right hb
            push_cast at h1; linarith
        have hM : (0:ℝ) ≤ M + 1 := by positivity
        nlinarith
      have hsub : Icc c c' ⊆ Icc a b := Icc_subset_Icc hac hcb
      obtain ⟨β, hβ0, hβ⟩ := exists_hasDerivWithinAt_Icc_of_lipschitz_step hcc hlen
        (fun t ht => hlip t (hsub ht)) (fun t ht => h0 t (hsub ht))
        (fun x => (hcont x).mono hsub) (α c)
      refine ⟨fun t => if t ≤ c then α t else β t, by simp [hac, hα0], fun t ht => ?_⟩
      have e1 : ∀ s ∈ Icc a c, (fun t => if t ≤ c then α t else β t) s = α s :=
        fun s hs => by simp [hs.2]
      have e2 : ∀ s ∈ Icc c c', (fun t => if t ≤ c then α t else β t) s = β s := fun s hs => by
        by_cases hsc : s ≤ c
        · have : s = c := le_antisymm hsc hs.1
          simp [this, hβ0]
        · simp [hsc]
      rw [← Icc_union_Icc_eq_Icc hac hcc]
      refine HasDerivWithinAt.union ?_ ?_
      · by_cases htc : t ≤ c
        · have := (hα t ⟨ht.1, htc⟩).congr_of_mem e1 ⟨ht.1, htc⟩
          rwa [e1 t ⟨ht.1, htc⟩]
        · refine HasFDerivWithinAt.of_notMem_closure ?_
          rw [closure_Icc]; exact fun h' => htc h'.2
      · by_cases htc : c ≤ t
        · have := (hβ t ⟨htc, ht.2⟩).congr_of_mem e2 ⟨htc, ht.2⟩
          rwa [e2 t ⟨htc, ht.2⟩]
        · refine HasFDerivWithinAt.of_notMem_closure ?_
          rw [closure_Icc]; exact fun h' => htc h'.1
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / h)
  obtain ⟨α, hα0, hα⟩ := key n
  have hcb : min b (a + n * h) = b := min_eq_left (by
    have := (div_lt_iff₀ hpos).mp hn; linarith)
  rw [hcb] at hα
  exact ⟨α, hα0, hα⟩

/-- **Existence for linear `2 × 2` systems on a compact interval**: with coefficients `aᵢⱼ`
continuous on `[a, b]`, the system `u' = a₁₁ u + a₁₂ v`, `v' = a₂₁ u + a₂₂ v` has a solution on
`[a, b]` (one-sided derivatives at the endpoints) with any initial values at `a`. -/
theorem exists_linear_system_Icc {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E] {a b : ℝ}
    (hab : a ≤ b) {a₁₁ a₁₂ a₂₁ a₂₂ : ℝ → 𝕜} (c₁₁ : ContinuousOn a₁₁ (Icc a b))
    (c₁₂ : ContinuousOn a₁₂ (Icc a b)) (c₂₁ : ContinuousOn a₂₁ (Icc a b))
    (c₂₂ : ContinuousOn a₂₂ (Icc a b)) (u₀ v₀ : E) :
    ∃ u v : ℝ → E, u a = u₀ ∧ v a = v₀ ∧ ∀ t ∈ Icc a b,
      HasDerivWithinAt u (a₁₁ t • u t + a₁₂ t • v t) (Icc a b) t ∧
      HasDerivWithinAt v (a₂₁ t • u t + a₂₂ t • v t) (Icc a b) t := by
  obtain ⟨A₁₁, hA₁₁⟩ := isCompact_Icc.exists_bound_of_continuousOn c₁₁
  obtain ⟨A₁₂, hA₁₂⟩ := isCompact_Icc.exists_bound_of_continuousOn c₁₂
  obtain ⟨A₂₁, hA₂₁⟩ := isCompact_Icc.exists_bound_of_continuousOn c₂₁
  obtain ⟨A₂₂, hA₂₂⟩ := isCompact_Icc.exists_bound_of_continuousOn c₂₂
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hK : 0 ≤ A₁₁ + A₁₂ + A₂₁ + A₂₂ := by
    linarith [(norm_nonneg _).trans (hA₁₁ a ha), (norm_nonneg _).trans (hA₁₂ a ha),
      (norm_nonneg _).trans (hA₂₁ a ha), (norm_nonneg _).trans (hA₂₂ a ha)]
  set V : ℝ → E × E → E × E :=
    fun t y => (a₁₁ t • y.1 + a₁₂ t • y.2, a₂₁ t • y.1 + a₂₂ t • y.2)
  obtain ⟨α, hα0, hα⟩ := exists_hasDerivWithinAt_Icc_of_lipschitz (v := V) (M := ⟨_, hK⟩) hab
    (fun t ht => lipschitzWith_linear_system (hA₁₁ t ht) (hA₁₂ t ht) (hA₂₁ t ht) (hA₂₂ t ht))
    (fun t _ => by simp [V]) (fun x => by
      simp only [V]
      exact ((c₁₁.smul continuousOn_const).add (c₁₂.smul continuousOn_const)).prodMk
        ((c₂₁.smul continuousOn_const).add (c₂₂.smul continuousOn_const))) (u₀, v₀)
  exact ⟨fun t => (α t).1, fun t => (α t).2, by simp [hα0], by simp [hα0],
    fun t ht => ⟨(hα t ht).fst, (hα t ht).snd⟩⟩

end Existence

end ODE
