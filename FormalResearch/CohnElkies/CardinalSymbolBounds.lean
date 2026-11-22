module

public import FormalResearch.CohnElkies.CardinalPositiveAxis
public import FormalResearch.CohnElkies.StieltjesMixture
public import FormalResearch.CohnElkies.AirySymbolWKB
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Uniform Resolvent Symbol Bounds and End-to-End Theorem CR.4 (`CR.17`, `CR.20`–`CR.21`, `CR.14`)

Source: `CFT/sign_uncertainty/paper/ce_cardinal_resolvent.tex`, Theorem CR.4 Steps 2–4
(equations `(CR.17)`, `(CR.20)`, `(CR.21)`, and assembly with `cecw:W6` / `cardinal_symbol_decomp`).

## Main definitions
* `cohnAtSmooth`: smooth extension of `cohnAt` across the removable pole `a₁ + t = a`.
* `cohnAtGen`, `cohnBtGen`, `cohnCtGen`: `(1 - t ∂_t)`-transformed single-resolvent coefficients.
* `qMix`, `AMix`, `BMix`, `CMix`: probability mixtures over `t ∈ (0, ∞)`.

## Main results
* `cohnAtSmooth_eq_cohnAt`, `AMix_eq_integral_cohnAt`: agreement with `cohnAt` off `t = a - a₁`.
* `cardinal_CR17`, `cardinal_CR17_derivWithin`: uniform `(x ∂_x)^j (t ∂_t)^k` and `∂_x^j` bounds `(CR.17)`.
* `qMix_isWeightedSymbol`: `qMix Λ ∈ 𝒬₀` uniformly in `Λ` (`(CR.20)` differentiation).
* `cardinal_CR21_uniform`, `cardinal_CR21_of_measure`, `cardinal_CR21_dirac_nonvacuous`:
  `(CR.21)` weighted-symbol estimates and `CardinalResolventCoeffs`, with non-vacuity via `Measure.dirac 1`.
* `theorem_CR4_symbol_decomp`: end-to-end Theorem CR.4 / `(CR.14)` oscillatory symbol decomposition.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ContDiff Interval Real Topology
open FormalResearch.Asymptotics FormalResearch.Special

namespace FormalResearch.CohnElkies

/-! ### Smooth continuation and `(1 - t ∂_t)` mixture definitions -/

/-- Smooth extension of `cohnAt` across the removable singularity `airyZero 1 + t = a`. -/
noncomputable def cohnAtSmooth (a t x : ℝ) : ℝ :=
  (x - a) * (x + airyZero 1) / ((x + a) ^ 2 * (x + airyZero 1 + t)) +
    t / (x + airyZero 1 + t) ^ 2 * (a / (x + a) - cohnVSmooth a (airyZero 1 + t))

lemma cohnAtSmooth_eq_cohnAt {a t x : ℝ} (hza : airyZero 1 + t ≠ a) :
    cohnAtSmooth a t x = cohnAt a t x := by
  simp [cohnAtSmooth, cohnAt, cohnVSmooth, hza]

/-- `(1 - t ∂_t) A_t(x)` on `t > 0`. -/
noncomputable def cohnAtGen (a t x : ℝ) : ℝ :=
  cohnAtSmooth a t x - t * _root_.deriv (fun s => cohnAtSmooth a s x) t

/-- `(1 - t ∂_t) B_t(x)` on `t > 0`. -/
noncomputable def cohnBtGen (a t x : ℝ) : ℝ :=
  cohnBt a t x - t * _root_.deriv (fun s => cohnBt a s x) t

/-- `(1 - t ∂_t) C_t(x)` on `t > 0`. -/
noncomputable def cohnCtGen (a t x : ℝ) : ℝ :=
  cohnCt a t x - t * _root_.deriv (fun s => cohnCt a s x) t

/-- Mixture scalar envelope `q_Λ(x) = ∫_{(0,∞)} (2 w_t(x) - w_t(x)²) dΛ(t)` (`(CR.20)`). -/
noncomputable def qMix (Λ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), (2 * cohnWt t x - cohnWt t x ^ 2) ∂Λ

/-- Mixture `Ai(-x)²` coefficient `A_Λ(x)`. -/
noncomputable def AMix (a : ℝ) (Λ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), cohnAtGen a t x ∂Λ

/-- Mixture `Ai(-x) Ai'(-x)` coefficient `B_Λ(x)`. -/
noncomputable def BMix (a : ℝ) (Λ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), cohnBtGen a t x ∂Λ

/-- Mixture `Ai'(-x)²` coefficient `C_Λ(x)`. -/
noncomputable def CMix (a : ℝ) (Λ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), cohnCtGen a t x ∂Λ

/-- Whenever `Λ` has no atom at `a - a₁`, `AMix a Λ x` equals the `(1 - t ∂_t)` integral
of the raw coefficient `cohnAt`. -/
theorem AMix_eq_integral_cohnAt {a : ℝ} {Λ : Measure ℝ} (hAtom : Λ {a - airyZero 1} = 0)
    (x : ℝ) :
    AMix a Λ x =
      ∫ t in Set.Ioi (0 : ℝ), (cohnAt a t x - t * _root_.deriv (fun s => cohnAt a s x) t) ∂Λ := by
  refine integral_congr_ae ?_
  have hne : ∀ᵐ t ∂(Λ.restrict (Set.Ioi 0)), t ≠ a - airyZero 1 := by
    simp only [ae_iff, ne_eq, not_not]
    exact le_antisymm ((Measure.restrict_apply_le _ _).trans hAtom.le) bot_le
  filter_upwards [hne] with t ht
  have hza : airyZero 1 + t ≠ a := fun h => ht (by linarith)
  have hnhds : (fun s => cohnAtSmooth a s x) =ᶠ[𝓝 t] (fun s => cohnAt a s x) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr ht)] with s hs
    exact cohnAtSmooth_eq_cohnAt fun h => (Set.mem_compl_singleton_iff.mp hs) (by linarith)
  rw [cohnAtGen, cohnAtSmooth_eq_cohnAt hza, hnhds.deriv_eq]

/-! ### Two-parameter Euler derivative calculus and `IsXTBound` -/

/-- `t`-Euler differential operator `(t ∂_t)^k` applied in the first argument. -/
noncomputable def eulerDerivT (k : ℕ) (f : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  eulerDeriv k (fun s => f s x) t

/-- Two-parameter Euler operator `(x ∂_x)^j (t ∂_t)^k`. -/
noncomputable def eulerDerivXT (j k : ℕ) (f : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  eulerDeriv j (fun y => eulerDerivT k f t y) x

private noncomputable def derivX (f : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := _root_.deriv (fun y => f t y) x
private noncomputable def eulerDerivX1 (f : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := eulerDerivOp (fun y => f t y) x
private lemma eulerDeriv_succ (k : ℕ) (f : ℝ → ℝ) : eulerDeriv (k + 1) f = eulerDerivOp (eulerDeriv k f) := Function.iterate_succ_apply' eulerDerivOp k f
private lemma eulerDeriv_succ' (k : ℕ) (f : ℝ → ℝ) : eulerDeriv (k + 1) f = eulerDeriv k (eulerDerivOp f) := Function.iterate_succ_apply eulerDerivOp k f

private lemma eulerDeriv_zero_fn (m : ℕ) (x : ℝ) : eulerDeriv m (fun _ : ℝ => (0 : ℝ)) x = 0 := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    simp only [eulerDeriv_succ, eulerDerivOp]
    have hev : eulerDeriv m (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 x] fun _ => 0 := Filter.Eventually.of_forall ih
    rw [hev.deriv_eq, deriv_const, mul_zero]

private lemma eulerDeriv_const_succ (m : ℕ) (c x : ℝ) : eulerDeriv (m + 1) (fun _ : ℝ => c) x = 0 := by
  have h0 : (eulerDerivOp fun _ : ℝ => c) = fun _ => 0 := funext fun _ => by simp [eulerDerivOp]
  rw [eulerDeriv_succ', h0]; exact eulerDeriv_zero_fn m x

private lemma eulerDeriv_contDiffOn {U : Set ℝ} {f : ℝ → ℝ} (hU : IsOpen U) (hfU : ContDiffOn ℝ ∞ f U) (k : ℕ) : ContDiffOn ℝ ∞ (eulerDeriv k f) U := by
  induction k with | zero => exact hfU | succ k ih => rw [eulerDeriv_succ]; exact contDiffOn_id.mul (ih.deriv_of_isOpen hU (by simp))

private lemma eulerDeriv_congr_open {U : Set ℝ} {f g : ℝ → ℝ} (hU : IsOpen U) (hfg : Set.EqOn f g U) (k : ℕ) : Set.EqOn (eulerDeriv k f) (eulerDeriv k g) U := by
  induction k with
  | zero => exact hfg
  | succ k ih => intro x hx; simp only [eulerDeriv_succ, eulerDerivOp]; have hev : eulerDeriv k f =ᶠ[𝓝 x] eulerDeriv k g := Filter.eventually_of_mem (hU.mem_nhds hx) ih; rw [hev.deriv_eq]

private lemma eulerDeriv_add_open {U : Set ℝ} {f g : ℝ → ℝ} (hU : IsOpen U) (hfU : ContDiffOn ℝ ∞ f U) (hgU : ContDiffOn ℝ ∞ g U) (k : ℕ) :
    ∀ x ∈ U, eulerDeriv k (fun y => f y + g y) x = eulerDeriv k f x + eulerDeriv k g x := by
  induction k with
  | zero => intro _ _; rfl
  | succ k ih =>
    intro x hx; simp only [eulerDeriv_succ, eulerDerivOp]
    have hev : eulerDeriv k (fun y => f y + g y) =ᶠ[𝓝 x] (fun y => eulerDeriv k f y + eulerDeriv k g y) := Filter.eventually_of_mem (hU.mem_nhds hx) ih
    have df := (((eulerDeriv_contDiffOn hU hfU k).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
    have dg := (((eulerDeriv_contDiffOn hU hgU k).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
    rw [hev.deriv_eq, (df.fun_add dg).deriv]; ring

private lemma eulerDeriv_const_mul_open {U : Set ℝ} {f : ℝ → ℝ} (hU : IsOpen U) (hfU : ContDiffOn ℝ ∞ f U) (c : ℝ) (k : ℕ) :
    ∀ x ∈ U, eulerDeriv k (fun y => c * f y) x = c * eulerDeriv k f x := by
  induction k with
  | zero => intro _ _; rfl
  | succ k ih =>
    intro x hx; simp only [eulerDeriv_succ, eulerDerivOp]
    have hev : eulerDeriv k (fun y => c * f y) =ᶠ[𝓝 x] (fun y => c * eulerDeriv k f y) := Filter.eventually_of_mem (hU.mem_nhds hx) ih
    have df := (((eulerDeriv_contDiffOn hU hfU k).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
    rw [hev.deriv_eq, (df.const_mul c).deriv]; ring

private lemma eulerDeriv_sub_open {U : Set ℝ} {f g : ℝ → ℝ} (hU : IsOpen U) (hfU : ContDiffOn ℝ ∞ f U) (hgU : ContDiffOn ℝ ∞ g U) (k : ℕ) :
    ∀ x ∈ U, eulerDeriv k (fun y => f y - g y) x = eulerDeriv k f x - eulerDeriv k g x := fun x hx => by
  rw [eulerDeriv_congr_open hU (g := fun y => f y + (-1 : ℝ) * g y) (fun _ _ => by ring) k hx,
    eulerDeriv_add_open hU hfU (contDiffOn_const.mul hgU) k x hx, eulerDeriv_const_mul_open hU hgU (-1) k x hx]; ring

private lemma eulerDeriv_finset_sum_open {ι : Type*} (s : Finset ι) {U : Set ℝ} (hU : IsOpen U) (F : ι → ℝ → ℝ)
    (hF : ∀ i ∈ s, ContDiffOn ℝ ∞ (F i) U) (k : ℕ) : ∀ x ∈ U, eulerDeriv k (fun y => ∑ i ∈ s, F i y) x = ∑ i ∈ s, eulerDeriv k (F i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => intro x _; simp only [Finset.sum_empty]; exact eulerDeriv_zero_fn k x
  | insert a s ha ih =>
    intro x hx; have hFs : ∀ i ∈ s, ContDiffOn ℝ ∞ (F i) U := fun i hi => hF i (Finset.mem_insert_of_mem hi)
    rw [eulerDeriv_congr_open hU (g := fun y => F a y + ∑ i ∈ s, F i y) (fun _ _ => Finset.sum_insert ha) k hx,
      eulerDeriv_add_open hU (hF a (Finset.mem_insert_self a s)) (ContDiffOn.sum fun i hi => hFs i hi) k x hx, ih hFs x hx, Finset.sum_insert ha]

private lemma eulerDeriv_mul_open {U : Set ℝ} {f g : ℝ → ℝ} (hU : IsOpen U) (hfU : ContDiffOn ℝ ∞ f U) (hgU : ContDiffOn ℝ ∞ g U)
    (k : ℕ) : ∀ x ∈ U, eulerDeriv k (fun y => f y * g y) x = ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * eulerDeriv i f x * eulerDeriv (k - i) g x := by
  induction k with
  | zero => intro x _; simp [eulerDeriv]
  | succ k ih =>
    intro x hx; simp only [eulerDeriv_succ, eulerDerivOp]
    have hev : eulerDeriv k (fun y => f y * g y) =ᶠ[𝓝 x] fun y => ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * eulerDeriv i f y * eulerDeriv (k - i) g y :=
      Filter.eventually_of_mem (hU.mem_nhds hx) ih
    have hterm_hd : ∀ i ∈ Finset.range (k + 1), HasDerivAt (fun y => (k.choose i : ℝ) * eulerDeriv i f y * eulerDeriv (k - i) g y)
        ((k.choose i : ℝ) * _root_.deriv (eulerDeriv i f) x * eulerDeriv (k - i) g x + (k.choose i : ℝ) * eulerDeriv i f x * _root_.deriv (eulerDeriv (k - i) g) x) x :=
      fun i _ => (((((eulerDeriv_contDiffOn hU hfU i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt.const_mul _).fun_mul
        (((eulerDeriv_contDiffOn hU hgU (k - i)).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt).congr_deriv (by ring)
    rw [hev.deriv_eq, (HasDerivAt.fun_sum hterm_hd).deriv, Finset.mul_sum]
    have hsplit : ∑ i ∈ Finset.range (k + 1), x * ((k.choose i : ℝ) * _root_.deriv (eulerDeriv i f) x * eulerDeriv (k - i) g x +
          (k.choose i : ℝ) * eulerDeriv i f x * _root_.deriv (eulerDeriv (k - i) g) x) =
        (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * eulerDeriv (i + 1) f x * eulerDeriv (k + 1 - (i + 1)) g x) +
        (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * eulerDeriv i f x * eulerDeriv (k - i + 1) g x) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by simp only [eulerDeriv_succ, eulerDerivOp, Nat.succ_sub_succ]; ring
    have hs2 : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * eulerDeriv i f x * eulerDeriv (k - i + 1) g x =
        eulerDeriv 0 f x * eulerDeriv (k + 1) g x + ∑ i ∈ Finset.range k, (k.choose (i + 1) : ℝ) * eulerDeriv (i + 1) f x * eulerDeriv (k + 1 - (i + 1)) g x := by
      rw [Finset.sum_range_succ']; simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, add_comm]
      exact congrArg (_ + ·) (Finset.sum_congr rfl fun i hi => by have hik : i + 1 ≤ k := Finset.mem_range.mp hi; congr 2; omega)
    have hlast : ∑ i ∈ Finset.range (k + 1), (k.choose (i + 1) : ℝ) * eulerDeriv (i + 1) f x * eulerDeriv (k + 1 - (i + 1)) g x =
        ∑ i ∈ Finset.range k, (k.choose (i + 1) : ℝ) * eulerDeriv (i + 1) f x * eulerDeriv (k + 1 - (i + 1)) g x := by
      rw [Finset.sum_range_succ]; simp [Nat.choose_succ_self]
    rw [hsplit, hs2, ← hlast]; symm; rw [Finset.sum_range_succ']; simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
    rw [add_comm (eulerDeriv 0 f x * eulerDeriv (k + 1) g x)]
    have hcomb : ∑ i ∈ Finset.range (k + 1), ((k + 1).choose (i + 1) : ℝ) * eulerDeriv (i + 1) f x * eulerDeriv (k + 1 - (i + 1)) g x =
        (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * eulerDeriv (i + 1) f x * eulerDeriv (k + 1 - (i + 1)) g x) +
        (∑ i ∈ Finset.range (k + 1), (k.choose (i + 1) : ℝ) * eulerDeriv (i + 1) f x * eulerDeriv (k + 1 - (i + 1)) g x) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by rw [Nat.choose_succ_succ', Nat.cast_add]; ring
    rw [hcomb]; ring

private lemma iteratedDeriv_contDiffOn {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f U) (j : ℕ) : ContDiffOn ℝ ∞ (iteratedDeriv j f) U := by
  induction j with | zero => simpa using hf | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv_of_isOpen hU (by simp)

private lemma x_pow_mul_iteratedDeriv (j : ℕ) :
    ∃ c : ℕ → ℝ, ∀ {U : Set ℝ}, IsOpen U → ∀ {f : ℝ → ℝ}, ContDiffOn ℝ ∞ f U → ∀ x ∈ U,
      x ^ j * iteratedDeriv j f x = ∑ i ∈ Finset.range (j + 1), c i * eulerDeriv i f x := by
  induction j with
  | zero => exact ⟨fun _ => 1, fun {U} _ {f} _ x _ => by simp [eulerDeriv]⟩
  | succ j ih =>
    obtain ⟨c, hc⟩ := ih; let c' : ℕ → ℝ := fun i => (if i = 0 then 0 else c (i - 1)) - (if i ≤ j then (j : ℝ) * c i else 0)
    refine ⟨c', fun {U} hU {f} hf x hx => ?_⟩
    have hev : (fun y => y ^ j * iteratedDeriv j f y) =ᶠ[𝓝 x] (fun y => ∑ i ∈ Finset.range (j + 1), c i * eulerDeriv i f y) := Filter.eventually_of_mem (hU.mem_nhds hx) (hc hU hf)
    have hf' : HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f x) x := by
      rw [iteratedDeriv_succ]; exact (((iteratedDeriv_contDiffOn hU hf j).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
    have hmul_lhs : x * _root_.deriv (fun y => y ^ j * iteratedDeriv j f y) x = (j : ℝ) * (x ^ j * iteratedDeriv j f x) + x ^ (j + 1) * iteratedDeriv (j + 1) f x := by
      cases j with
      | zero => have hd : HasDerivAt (fun y : ℝ => y ^ 0 * iteratedDeriv 0 f y) (iteratedDeriv 1 f x) x := hf'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by simp); rw [hd.deriv]; simp
      | succ k =>
        have hp : HasDerivAt (fun y : ℝ => y ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * x ^ k) x := by simpa using hasDerivAt_pow (k + 1) x
        rw [(hp.fun_mul hf').deriv, pow_succ', pow_succ']; ring
    have hd_rhs : HasDerivAt (fun y => ∑ i ∈ Finset.range (j + 1), c i * eulerDeriv i f y) (∑ i ∈ Finset.range (j + 1), c i * _root_.deriv (eulerDeriv i f) x) x :=
      HasDerivAt.fun_sum fun i _ => ((((eulerDeriv_contDiffOn hU hf i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt).const_mul _
    have hmul_rhs : x * _root_.deriv (fun y => ∑ i ∈ Finset.range (j + 1), c i * eulerDeriv i f y) x = ∑ i ∈ Finset.range (j + 1), c i * eulerDeriv (i + 1) f x := by
      rw [hd_rhs.deriv, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp only [eulerDeriv_succ, eulerDerivOp]; ring
    have h1 : ∑ i ∈ Finset.range (j + 2), (if i = 0 then (0 : ℝ) else c (i - 1)) * eulerDeriv i f x = ∑ i ∈ Finset.range (j + 1), c i * eulerDeriv (i + 1) f x := by
      rw [Finset.sum_range_succ']; simp only [↓reduceIte, zero_mul, add_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.add_sub_cancel]
    have h2 : ∑ i ∈ Finset.range (j + 2), (if i ≤ j then (j : ℝ) * c i else 0) * eulerDeriv i f x = (j : ℝ) * ∑ i ∈ Finset.range (j + 1), c i * eulerDeriv i f x := by
      rw [Finset.sum_range_succ]; simp only [show ¬(j + 1 ≤ j) by omega, ↓reduceIte, zero_mul, add_zero, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i hi => by simp only [Nat.lt_succ_iff.mp (Finset.mem_range.mp hi), ↓reduceIte]; ring
    have hsub : x ^ (j + 1) * iteratedDeriv (j + 1) f x = (∑ i ∈ Finset.range (j + 1), c i * eulerDeriv (i + 1) f x) - (j : ℝ) * ∑ i ∈ Finset.range (j + 1), c i * eulerDeriv i f x := by
      rw [← hc hU hf x hx]; linarith [hmul_lhs, hmul_rhs, congrArg (x * ·) hev.deriv_eq]
    rw [hsub]; simp only [c', sub_mul, Finset.sum_sub_distrib, h1, h2]

private lemma iteratedDeriv_bound_of_eulerDeriv (j : ℕ) {A : ℕ → ℝ} (hA : ∀ i, 0 ≤ A i) :
    ∃ C ≥ 0, ∀ {U : Set ℝ}, IsOpen U → ∀ {f : ℝ → ℝ}, ContDiffOn ℝ ∞ f U →
      ∀ {x M : ℝ}, x ∈ U → 0 < x → 0 ≤ M → (∀ i ≤ j, |eulerDeriv i f x| ≤ A i * M) → |iteratedDeriv j f x| ≤ C * M * x ^ (-(j : ℝ)) := by
  obtain ⟨c, hc⟩ := x_pow_mul_iteratedDeriv j
  refine ⟨∑ i ∈ Finset.range (j + 1), |c i| * A i, Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hA i), fun {U} hU {f} hf {x M} hx hxpos _ hbd => ?_⟩
  have hxp : 0 < x ^ j := pow_pos hxpos j
  have h1 : |x ^ j * iteratedDeriv j f x| ≤ (∑ i ∈ Finset.range (j + 1), |c i| * A i) * M := by
    rw [hc hU hf x hx]
    calc |∑ i ∈ Finset.range (j + 1), c i * eulerDeriv i f x| ≤ ∑ i ∈ Finset.range (j + 1), |c i * eulerDeriv i f x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (j + 1), (|c i| * A i) * M := Finset.sum_le_sum fun i hi => by
          rw [abs_mul]; calc |c i| * |eulerDeriv i f x| ≤ |c i| * (A i * M) := mul_le_mul_of_nonneg_left (hbd i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) (abs_nonneg _)
            _ = _ := by ring
      _ = _ := (Finset.sum_mul _ _ _).symm
  rw [abs_mul, abs_of_pos hxp] at h1; rw [Real.rpow_neg hxpos.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hxp]; linarith

private lemma contDiffOn_sliceX {U_t U_x : Set ℝ} {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) (U_t ×ˢ U_x))
    {t : ℝ} (ht : t ∈ U_t) : ContDiffOn ℝ ∞ (fun y => f t y) U_x := hf.comp (contDiffOn_const.prodMk contDiffOn_id) fun _ hy => ⟨ht, hy⟩

private lemma contDiffOn_sliceT {U_t U_x : Set ℝ} {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) (U_t ×ˢ U_x))
    {x : ℝ} (hx : x ∈ U_x) : ContDiffOn ℝ ∞ (fun s => f s x) U_t := hf.comp (contDiffOn_id.prodMk contDiffOn_const) fun _ hs => ⟨hs, hx⟩

private lemma contDiffOn_derivX {U_t U_x : Set ℝ} (hUt : IsOpen U_t) (hUx : IsOpen U_x) {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) (U_t ×ˢ U_x)) : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => derivX f p.1 p.2) (U_t ×ˢ U_x) := by
  have hU := hUt.prod hUx
  refine ((hf.fderivWithin hU.uniqueDiffOn (by simp)).clm_apply (contDiffOn_const (c := ((0, 1) : ℝ × ℝ)))).congr fun p hp => ?_
  rw [fderivWithin_of_isOpen hU hp]
  have hd := (((hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt p.2
    (by simpa using (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv
  dsimp only [Function.comp_def] at hd; exact hd

private lemma contDiffOn_derivX_iterate {U_t U_x : Set ℝ} (hUt : IsOpen U_t) (hUx : IsOpen U_x) {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) (U_t ×ˢ U_x)) (j : ℕ) : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (derivX^[j] f) p.1 p.2) (U_t ×ˢ U_x) := by
  induction j generalizing f with | zero => exact hf | succ j ih => rw [Function.iterate_succ_apply]; exact ih (contDiffOn_derivX hUt hUx hf)

private lemma contDiffOn_eulerDerivT {U_t U_x : Set ℝ} (hUt : IsOpen U_t) (hUx : IsOpen U_x) {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) (U_t ×ˢ U_x)) (k : ℕ) : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => eulerDerivT k f p.1 p.2) (U_t ×ˢ U_x) := by
  induction k generalizing f with
  | zero => exact hf
  | succ k ih =>
    have hU := hUt.prod hUx
    have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => eulerDerivT 1 f p.1 p.2) (U_t ×ˢ U_x) := by
      refine (contDiffOn_fst.mul ((hf.fderivWithin hU.uniqueDiffOn (by simp)).clm_apply (contDiffOn_const (c := ((1, 0) : ℝ × ℝ))))).congr fun p hp => ?_
      rw [fderivWithin_of_isOpen hU hp]
      have hd := (((hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt p.1 (by simpa using (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv
      dsimp only [Function.comp_def] at hd; change p.1 * _root_.deriv (fun s => f s p.2) p.1 = p.1 * fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) p (1, 0); rw [hd]
    exact (ih h1).congr fun _ _ => by simp only [eulerDerivT, eulerDeriv_succ']; rfl

private lemma eulerDerivXT_congr_open {U_t U_x : Set ℝ} (hUt : IsOpen U_t) (hUx : IsOpen U_x) {f g : ℝ → ℝ → ℝ}
    (hfg : ∀ t ∈ U_t, ∀ x ∈ U_x, f t x = g t x) (j k : ℕ) : ∀ t ∈ U_t, ∀ x ∈ U_x, eulerDerivXT j k f t x = eulerDerivXT j k g t x :=
  fun _ ht _ hx => eulerDeriv_congr_open hUx (fun y hy => eulerDeriv_congr_open hUt (fun s hs => hfg s hs y hy) k ht) j hx

private lemma eulerDerivXT_const_pos {U_t U_x : Set ℝ} (_hUt : IsOpen U_t) (hUx : IsOpen U_x) (j k : ℕ)
    (_hjk : 0 < j + k) (c : ℝ) : ∀ t ∈ U_t, ∀ x ∈ U_x, eulerDerivXT j k (fun _ _ => c) t x = 0 := by
  intro t _ x hx; cases k with
  | zero => obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩; exact eulerDeriv_const_succ j' c x
  | succ k =>
    have heq : Set.EqOn (fun y => eulerDerivT (k + 1) (fun _ _ => c) t y) (fun _ => 0) U_x := fun _ _ => eulerDeriv_const_succ k c t
    change eulerDeriv j (fun y => eulerDerivT (k + 1) (fun _ _ => c) t y) x = 0; rw [eulerDeriv_congr_open hUx heq j hx, eulerDeriv_zero_fn j x]

private lemma eulerDerivXT_sub_open {U_t U_x : Set ℝ} (hUt : IsOpen U_t) (hUx : IsOpen U_x) {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) (U_t ×ˢ U_x)) (hg : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => g p.1 p.2) (U_t ×ˢ U_x))
    (j k : ℕ) : ∀ t ∈ U_t, ∀ x ∈ U_x, eulerDerivXT j k (fun s y => f s y - g s y) t x = eulerDerivXT j k f t x - eulerDerivXT j k g t x := fun t ht x hx => by
  have h1 : Set.EqOn (fun y => eulerDerivT k (fun s z => f s z - g s z) t y) (fun y => eulerDerivT k f t y - eulerDerivT k g t y) U_x :=
    fun y hy => eulerDeriv_sub_open hUt (contDiffOn_sliceT hf hy) (contDiffOn_sliceT hg hy) k t ht
  have h2 := eulerDeriv_sub_open hUx (contDiffOn_sliceX (contDiffOn_eulerDerivT hUt hUx hf k) ht) (contDiffOn_sliceX (contDiffOn_eulerDerivT hUt hUx hg k) ht) j x hx
  change eulerDeriv j (fun y => eulerDerivT k (fun s z => f s z - g s z) t y) x = _; rw [eulerDeriv_congr_open hUx h1 j hx, h2]; rfl

private lemma eulerDerivXT_neg_open {U_t U_x : Set ℝ} (hUt : IsOpen U_t) (hUx : IsOpen U_x) {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) (U_t ×ˢ U_x)) (j k : ℕ) :
    ∀ t ∈ U_t, ∀ x ∈ U_x, eulerDerivXT j k (fun s y => -f s y) t x = -eulerDerivXT j k f t x := fun t ht x hx => by
  rw [eulerDerivXT_congr_open hUt hUx (g := fun s y => 0 - f s y) (fun _ _ _ _ => by ring) j k t ht x hx, eulerDerivXT_sub_open hUt hUx contDiffOn_const hf j k t ht x hx]
  rcases eq_or_ne (j + k) 0 with h0 | hpos
  · obtain rfl : j = 0 := by omega
    obtain rfl : k = 0 := by omega
    simp [eulerDerivXT, eulerDerivT, eulerDeriv]
  · rw [eulerDerivXT_const_pos hUt hUx j k (Nat.pos_of_ne_zero hpos) 0 t ht x hx, zero_sub]

private lemma eulerDerivXT_mul_le_of_bound {U_t U_x : Set ℝ} (hUt : IsOpen U_t) (hUx : IsOpen U_x) {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) (U_t ×ˢ U_x)) (hg : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => g p.1 p.2) (U_t ×ˢ U_x))
    {j k : ℕ} {t x : ℝ} (ht : t ∈ U_t) (hx : x ∈ U_x) {A B : ℕ → ℕ → ℝ} {w₁ w₂ : ℝ}
    (hfbd : ∀ a ≤ j, ∀ b ≤ k, |eulerDerivXT a b f t x| ≤ A a b * w₁) (hgbd : ∀ a ≤ j, ∀ b ≤ k, |eulerDerivXT a b g t x| ≤ B a b * w₂) :
    |eulerDerivXT j k (fun s y => f s y * g s y) t x| ≤ (∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (k + 1), (j.choose a : ℝ) * (k.choose b : ℝ) * A a b * B (j - a) (k - b)) * (w₁ * w₂) := by
  have hmul_eq : eulerDerivXT j k (fun s y => f s y * g s y) t x =
      ∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (k + 1), (j.choose a : ℝ) * (k.choose b : ℝ) * eulerDerivXT a b f t x * eulerDerivXT (j - a) (k - b) g t x := by
    have hfg_t : Set.EqOn (fun y => eulerDerivT k (fun s z => f s z * g s z) t y) (fun y => ∑ b ∈ Finset.range (k + 1), (k.choose b : ℝ) * eulerDerivT b f t y * eulerDerivT (k - b) g t y) U_x :=
      fun y hy => eulerDeriv_mul_open hUt (contDiffOn_sliceT hf hy) (contDiffOn_sliceT hg hy) k t ht
    have hterm_cd : ∀ b ∈ Finset.range (k + 1), ContDiffOn ℝ ∞ (fun y => (k.choose b : ℝ) * eulerDerivT b f t y * eulerDerivT (k - b) g t y) U_x :=
      fun b _ => (contDiffOn_const.mul (contDiffOn_sliceX (contDiffOn_eulerDerivT hUt hUx hf b) ht)).mul (contDiffOn_sliceX (contDiffOn_eulerDerivT hUt hUx hg (k - b)) ht)
    change eulerDeriv j (fun y => eulerDerivT k (fun s z => f s z * g s z) t y) x = _
    rw [eulerDeriv_congr_open hUx hfg_t j hx, eulerDeriv_finset_sum_open _ hUx _ hterm_cd j x hx]
    have hterm_eq : ∀ b ∈ Finset.range (k + 1), eulerDeriv j (fun y => (k.choose b : ℝ) * eulerDerivT b f t y * eulerDerivT (k - b) g t y) x =
        ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) * (k.choose b : ℝ) * eulerDerivXT a b f t x * eulerDerivXT (j - a) (k - b) g t x := fun b _ => by
      have hf' := contDiffOn_sliceX (contDiffOn_eulerDerivT hUt hUx hf b) ht; have hg' := contDiffOn_sliceX (contDiffOn_eulerDerivT hUt hUx hg (k - b)) ht
      rw [eulerDeriv_congr_open hUx (g := fun y => (k.choose b : ℝ) * (eulerDerivT b f t y * eulerDerivT (k - b) g t y)) (fun _ _ => by ring) j hx,
        eulerDeriv_const_mul_open hUx (hf'.mul hg') _ j x hx, eulerDeriv_mul_open hUx hf' hg' j x hx, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by simp only [eulerDerivXT]; ring
    rw [Finset.sum_congr rfl hterm_eq, Finset.sum_comm]
  rw [hmul_eq]
  calc |∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (k + 1), (j.choose a : ℝ) * (k.choose b : ℝ) * eulerDerivXT a b f t x * eulerDerivXT (j - a) (k - b) g t x|
      ≤ ∑ a ∈ Finset.range (j + 1), |∑ b ∈ Finset.range (k + 1), (j.choose a : ℝ) * (k.choose b : ℝ) * eulerDerivXT a b f t x * eulerDerivXT (j - a) (k - b) g t x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (k + 1), ((j.choose a : ℝ) * (k.choose b : ℝ) * A a b * B (j - a) (k - b)) * (w₁ * w₂) := by
        refine Finset.sum_le_sum fun a ha => (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b hb => ?_)
        rw [abs_mul, abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
        have h1 := hfbd a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)) b (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))
        have h2 := hgbd (j - a) (Nat.sub_le j a) (k - b) (Nat.sub_le k b)
        calc (j.choose a : ℝ) * (k.choose b : ℝ) * |eulerDerivXT a b f t x| * |eulerDerivXT (j - a) (k - b) g t x|
            = ((j.choose a : ℝ) * (k.choose b : ℝ)) * (|eulerDerivXT a b f t x| * |eulerDerivXT (j - a) (k - b) g t x|) := by ring
          _ ≤ ((j.choose a : ℝ) * (k.choose b : ℝ)) * ((A a b * w₁) * (B (j - a) (k - b) * w₂)) := mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)) (by positivity)
          _ = _ := by ring
    _ = _ := by simp_rw [← Finset.sum_mul]

/-- Two-parameter Euler-derivative bound on `(0, ∞) × (x₁, ∞)`. -/
def IsXTBound (x₁ : ℝ) (w : ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioi x₁) ∧ ∀ j k : ℕ, ∃ C ≥ 0, ∀ t > 0, ∀ x > x₁, |eulerDerivXT j k f t x| ≤ C * w t x

private lemma IsXTBound.congr {x₁ : ℝ} {w f g : ℝ → ℝ → ℝ} (hf : IsXTBound x₁ w f) (hfg : ∀ t > 0, ∀ x > x₁, f t x = g t x) : IsXTBound x₁ w g :=
  ⟨hf.1.congr fun p hp => (hfg p.1 hp.1 p.2 hp.2).symm, fun j k => let ⟨C, hC, hbd⟩ := hf.2 j k; ⟨C, hC, fun t ht x hx => by rw [← eulerDerivXT_congr_open isOpen_Ioi isOpen_Ioi hfg j k t ht x hx]; exact hbd t ht x hx⟩⟩

private lemma IsXTBound.mono_bound {x₁ : ℝ} {w₁ w₂ f : ℝ → ℝ → ℝ} (hf : IsXTBound x₁ w₁ f) (hw : ∀ t > 0, ∀ x > x₁, w₁ t x ≤ w₂ t x) : IsXTBound x₁ w₂ f :=
  ⟨hf.1, fun j k => let ⟨Cj, hCj, hbd⟩ := hf.2 j k; ⟨Cj, hCj, fun t ht x hx => (hbd t ht x hx).trans (mul_le_mul_of_nonneg_left (hw t ht x hx) hCj)⟩⟩

private lemma IsXTBound.add {x₁ : ℝ} {w f g : ℝ → ℝ → ℝ} (hf : IsXTBound x₁ w f) (hg : IsXTBound x₁ w g) : IsXTBound x₁ w (fun t x => f t x + g t x) := by
  refine ⟨hf.1.add hg.1, fun j k => ?_⟩; obtain ⟨Cf, hCf, hfb⟩ := hf.2 j k; obtain ⟨Cg, hCg, hgb⟩ := hg.2 j k
  refine ⟨Cf + Cg, add_nonneg hCf hCg, fun t ht x hx => ?_⟩
  have h1 : Set.EqOn (fun y => eulerDerivT k (fun s z => f s z + g s z) t y) (fun y => eulerDerivT k f t y + eulerDerivT k g t y) (Set.Ioi x₁) :=
    fun y hy => eulerDeriv_add_open isOpen_Ioi (contDiffOn_sliceT hf.1 hy) (contDiffOn_sliceT hg.1 hy) k t ht
  have h2 := eulerDeriv_add_open isOpen_Ioi (contDiffOn_sliceX (contDiffOn_eulerDerivT isOpen_Ioi isOpen_Ioi hf.1 k) ht) (contDiffOn_sliceX (contDiffOn_eulerDerivT isOpen_Ioi isOpen_Ioi hg.1 k) ht) j x hx
  change |eulerDeriv j (fun y => eulerDerivT k (fun s z => f s z + g s z) t y) x| ≤ _; rw [eulerDeriv_congr_open isOpen_Ioi h1 j hx, h2]
  calc |eulerDerivXT j k f t x + eulerDerivXT j k g t x| ≤ |eulerDerivXT j k f t x| + |eulerDerivXT j k g t x| := abs_add_le _ _
    _ ≤ (Cf + Cg) * w t x := by linarith [hfb t ht x hx, hgb t ht x hx]

private lemma IsXTBound.const_mul {x₁ : ℝ} {w f : ℝ → ℝ → ℝ} (c : ℝ) (hf : IsXTBound x₁ w f) : IsXTBound x₁ w (fun t x => c * f t x) := by
  refine ⟨contDiffOn_const.mul hf.1, fun j k => ?_⟩; obtain ⟨C, hC, hbd⟩ := hf.2 j k; refine ⟨|c| * C, by positivity, fun t ht x hx => ?_⟩
  have h1 : Set.EqOn (fun y => eulerDerivT k (fun s z => c * f s z) t y) (fun y => c * eulerDerivT k f t y) (Set.Ioi x₁) :=
    fun y hy => eulerDeriv_const_mul_open isOpen_Ioi (contDiffOn_sliceT hf.1 hy) c k t ht
  have h2 := eulerDeriv_const_mul_open isOpen_Ioi (contDiffOn_sliceX (contDiffOn_eulerDerivT isOpen_Ioi isOpen_Ioi hf.1 k) ht) c j x hx
  change |eulerDeriv j (fun y => eulerDerivT k (fun s z => c * f s z) t y) x| ≤ _; rw [eulerDeriv_congr_open isOpen_Ioi h1 j hx, h2, abs_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left (hbd t ht x hx) (abs_nonneg c)

private lemma IsXTBound.sub {x₁ : ℝ} {w f g : ℝ → ℝ → ℝ} (hf : IsXTBound x₁ w f) (hg : IsXTBound x₁ w g) :
    IsXTBound x₁ w (fun t x => f t x - g t x) := (hf.add (hg.const_mul (-1))).congr fun _ _ _ _ => by ring

private lemma IsXTBound.mul {x₁ : ℝ} {w₁ w₂ f g : ℝ → ℝ → ℝ} (hf : IsXTBound x₁ w₁ f) (hg : IsXTBound x₁ w₂ g) :
    IsXTBound x₁ (fun t x => w₁ t x * w₂ t x) (fun t x => f t x * g t x) := by
  refine ⟨hf.1.mul hg.1, fun j k => ?_⟩; choose Cf hCf hfb using hf.2; choose Cg hCg hgb using hg.2
  refine ⟨∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (k + 1), (j.choose a : ℝ) * (k.choose b : ℝ) * Cf a b * Cg (j - a) (k - b),
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity [hCf a b, hCg (j - a) (k - b)],
    fun t ht x hx => eulerDerivXT_mul_le_of_bound isOpen_Ioi isOpen_Ioi hf.1 hg.1 ht hx (fun a _ b _ => hfb a b t ht x hx) (fun a _ b _ => hgb a b t ht x hx)⟩

private lemma IsXTBound.pureX_of_isSymbolOn {x₁ x₂ β : ℝ} (hx₁ : 0 < x₁) (hx₁₂ : x₁ < x₂) {g : ℝ → ℝ}
    (hgU : ContDiffOn ℝ ∞ g (Set.Ioi x₁)) (hg_sym : IsSymbolOn x₂ β g) : IsXTBound x₂ (fun _ x => x ^ (-β)) (fun _ x => g x) := by
  have hx₂ : 0 < x₂ := lt_trans hx₁ hx₁₂
  refine ⟨(hgU.mono (Set.Ioi_subset_Ioi hx₁₂.le)).comp contDiffOn_snd (fun p hp => hp.2), fun j k => ?_⟩; cases k with
  | zero => obtain ⟨C, hC, hbd⟩ := (isSymbolOn_eulerDeriv_iter (x₀ := x₂) hx₂ isOpen_Ioi (fun x hx => lt_of_lt_of_le hx₁₂ hx) hgU hg_sym j).abs_le
            exact ⟨C, hC, fun t _ x hx => by simpa [eulerDerivXT, eulerDerivT, eulerDeriv] using hbd x hx.le⟩
  | succ k =>
    refine ⟨0, le_rfl, fun t _ x hx => ?_⟩
    have heq : Set.EqOn (fun y => eulerDerivT (k + 1) (fun _ z => g z) t y) (fun _ => 0) (Set.Ioi x₂) := fun y _ => eulerDeriv_const_succ k (g y) t
    change |eulerDeriv j (fun y => eulerDerivT (k + 1) (fun _ z => g z) t y) x| ≤ _
    rw [eulerDeriv_congr_open isOpen_Ioi heq j hx, eulerDeriv_zero_fn j x, abs_zero]; exact mul_nonneg le_rfl (Real.rpow_nonneg (lt_trans hx₂ hx).le _)

private lemma IsXTBound.pureT {x₁ : ℝ} {F : ℝ → ℝ} (hFU : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hF_ed : ∀ k : ℕ, ∃ C ≥ 0, ∀ t > 0, |eulerDeriv k F t| ≤ C) : IsXTBound x₁ (fun _ _ => 1) (fun t _ => F t) := by
  refine ⟨hFU.comp contDiffOn_fst (fun p hp => hp.1), fun j k => ?_⟩; obtain ⟨C, hC, hbd⟩ := hF_ed k; cases j with
  | zero => exact ⟨C, hC, fun t ht _ _ => by simpa [eulerDerivXT, eulerDerivT, eulerDeriv] using hbd t ht⟩
  | succ j => refine ⟨0, le_rfl, fun t ht x _ => ?_⟩; change |eulerDeriv (j + 1) (fun _ : ℝ => eulerDeriv k F t) x| ≤ _; rw [eulerDeriv_const_succ j _ x]; simp

/-! ### Uniform bounds for `w_t`, `u`, `v`, `r`, and Step 2 (`(CR.17)`) -/

private lemma eulerDerivXT_succ_k {U_t U_x : Set ℝ} (hUt : IsOpen U_t) (hUx : IsOpen U_x) {f g : ℝ → ℝ → ℝ}
    (hg : ∀ t ∈ U_t, ∀ x ∈ U_x, eulerDerivT 1 f t x = g t x) (j k : ℕ) :
    ∀ t ∈ U_t, ∀ x ∈ U_x, eulerDerivXT j (k + 1) f t x = eulerDerivXT j k g t x :=
  fun t ht x hx => eulerDeriv_congr_open hUx (fun y hy => by
    change eulerDeriv (k + 1) (fun s => f s y) t = eulerDeriv k (fun s => g s y) t
    rw [eulerDeriv_succ']; exact eulerDeriv_congr_open hUt (fun s hs => hg s hs y hy) k ht) j hx

private lemma eulerDerivXT_succ_j_zero {U_t U_x : Set ℝ} (hUx : IsOpen U_x) {f g : ℝ → ℝ → ℝ}
    (hg : ∀ t ∈ U_t, ∀ x ∈ U_x, eulerDerivX1 f t x = g t x) (j : ℕ) :
    ∀ t ∈ U_t, ∀ x ∈ U_x, eulerDerivXT (j + 1) 0 f t x = eulerDerivXT j 0 g t x := fun t ht x hx => by
  change eulerDeriv (j + 1) (fun y => f t y) x = eulerDeriv j (fun y => g t y) x
  rw [eulerDeriv_succ']; exact eulerDeriv_congr_open hUx (fun y hy => hg t ht y hy) j hx

private lemma isXTBound_of_log_derivs {x₁ : ℝ} {w f ax at_ : ℝ → ℝ → ℝ}
    (hf_cd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioi x₁))
    (hbase : ∃ C₀ ≥ 0, ∀ t > 0, ∀ x > x₁, |f t x| ≤ C₀ * w t x)
    (hax : IsXTBound x₁ (fun _ _ => 1) ax) (hat : IsXTBound x₁ (fun _ _ => 1) at_)
    (hx1 : ∀ t ∈ Set.Ioi (0 : ℝ), ∀ x ∈ Set.Ioi x₁, eulerDerivX1 f t x = ax t x * f t x)
    (ht1 : ∀ t ∈ Set.Ioi (0 : ℝ), ∀ x ∈ Set.Ioi x₁, eulerDerivT 1 f t x = at_ t x * f t x) : IsXTBound x₁ w f := by
  choose Cax hCax_nn hCax using hax.2; choose Cat hCat_nn hCat using hat.2; obtain ⟨C₀, hC₀_nn, hC₀⟩ := hbase
  have hbound : ∀ n : ℕ, ∀ j k : ℕ, j + k ≤ n → ∃ C ≥ 0, ∀ t > 0, ∀ x > x₁, |eulerDerivXT j k f t x| ≤ C * w t x := by
    intro n; induction n with
    | zero =>
      intro j k hjk
      obtain rfl : j = 0 := by omega
      obtain rfl : k = 0 := by omega
      exact ⟨C₀, hC₀_nn, fun t ht x hx => by simpa [eulerDerivXT, eulerDerivT, eulerDeriv] using hC₀ t ht x hx⟩
    | succ n ih =>
      have ihc : ∀ a b : ℕ, ∃ C ≥ 0, a + b ≤ n → ∀ t > 0, ∀ x > x₁, |eulerDerivXT a b f t x| ≤ C * w t x :=
        fun a b => if hab : a + b ≤ n then let ⟨C, hC, hbd⟩ := ih a b hab; ⟨C, hC, fun _ => hbd⟩ else ⟨0, le_rfl, fun h => absurd h hab⟩
      choose Cf hCf_nn hCf using ihc; intro j k hjk; cases k with
      | zero =>
        cases j with
        | zero => exact ih 0 0 (by omega)
        | succ j =>
          refine ⟨∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) * Cax a 0 * Cf (j - a) 0,
            Finset.sum_nonneg fun a _ => by positivity [hCax_nn a 0, hCf_nn (j - a) 0], fun t ht x hx => ?_⟩
          rw [eulerDerivXT_succ_j_zero isOpen_Ioi hx1 j t ht x hx]
          simpa only [Nat.zero_add, Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul, Nat.sub_zero] using
            eulerDerivXT_mul_le_of_bound isOpen_Ioi isOpen_Ioi hax.1 hf_cd ht hx (j := j) (k := 0) (A := Cax) (B := Cf) (w₁ := 1) (w₂ := w t x)
              (fun a _ b hb => by obtain rfl : b = 0 := Nat.le_zero.mp hb; simpa only [mul_one] using hCax a 0 t ht x hx)
              (fun a _ b hb => by obtain rfl : b = 0 := Nat.le_zero.mp hb; exact hCf a 0 (by omega) t ht x hx)
      | succ k =>
        refine ⟨∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (k + 1), (j.choose a : ℝ) * (k.choose b : ℝ) * Cat a b * Cf (j - a) (k - b),
          Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity [hCat_nn a b, hCf_nn (j - a) (k - b)], fun t ht x hx => ?_⟩
        rw [eulerDerivXT_succ_k isOpen_Ioi isOpen_Ioi ht1 j k t ht x hx]
        simpa only [one_mul] using eulerDerivXT_mul_le_of_bound isOpen_Ioi isOpen_Ioi hat.1 hf_cd ht hx (j := j) (k := k) (A := Cat) (B := Cf)
          (w₁ := 1) (w₂ := w t x) (fun a _ b _ => by simpa only [mul_one] using hCat a b t ht x hx) (fun a _ b _ => hCf a b (by omega) t ht x hx)
  exact ⟨hf_cd, fun j k => hbound (j + k) j k le_rfl⟩

private lemma isXTBound_uv_of_shift (c : ℝ) {x₁ : ℝ} (hx₁ : 0 < x₁) (hc : 2 * |c| < x₁) :
    IsXTBound x₁ (fun _ _ => 1) (fun t x => x / (x + c + t)) ∧ IsXTBound x₁ (fun _ _ => 1) (fun t x => t / (x + c + t)) := by
  let D : ℝ → ℝ → ℝ := fun t x => x + c + t; let u : ℝ → ℝ → ℝ := fun t x => x / D t x; let v : ℝ → ℝ → ℝ := fun t x => t / D t x
  have hc_lt : |c| < x₁ / 2 := by linarith
  have hD_pos : ∀ t > 0, ∀ x > x₁, x / 2 + t < D t x := fun t _ x hx => by have := (abs_lt.mp hc_lt).1; dsimp [D]; linarith
  have hD_ne : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi x₁, D p.1 p.2 ≠ 0 := fun p hp => by
    have : 0 < p.2 / 2 + p.1 := by linarith [Set.mem_Ioi.mp hp.1, lt_trans hx₁ (Set.mem_Ioi.mp hp.2)]
    linarith [hD_pos p.1 hp.1 p.2 hp.2]
  have hu_cd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => u p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioi x₁) :=
    contDiffOn_snd.div ((contDiffOn_snd.add contDiffOn_const).add contDiffOn_fst) hD_ne
  have hv_cd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => v p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioi x₁) :=
    contDiffOn_fst.div ((contDiffOn_snd.add contDiffOn_const).add contDiffOn_fst) hD_ne
  have hu_t1 : ∀ t ∈ Set.Ioi (0 : ℝ), ∀ x ∈ Set.Ioi x₁, eulerDerivT 1 u t x = -(u t x * v t x) := fun t ht x hx => by
    have hD0 : x + c + t ≠ 0 := hD_ne (t, x) ⟨ht, hx⟩
    have hden : HasDerivAt (fun s => x + c + s) 1 t := by simpa using (hasDerivAt_id t).const_add (x + c)
    have hd : HasDerivAt (fun s => u s x) ((0 * D t x - x * 1) / D t x ^ 2) t := (hasDerivAt_const t x).div hden hD0
    simp only [eulerDerivT, eulerDeriv, Function.iterate_one, eulerDerivOp]; rw [hd.deriv]; dsimp [u, v, D]; field_simp [hD0]; ring
  have hv_t1 : ∀ t ∈ Set.Ioi (0 : ℝ), ∀ x ∈ Set.Ioi x₁, eulerDerivT 1 v t x = v t x * (1 - v t x) := fun t ht x hx => by
    have hD0 : x + c + t ≠ 0 := hD_ne (t, x) ⟨ht, hx⟩
    have hden : HasDerivAt (fun s => x + c + s) 1 t := by simpa using (hasDerivAt_id t).const_add (x + c)
    have hd : HasDerivAt (fun s => v s x) ((1 * D t x - t * 1) / D t x ^ 2) t := (hasDerivAt_id t).div hden hD0
    simp only [eulerDerivT, eulerDeriv, Function.iterate_one, eulerDerivOp]; rw [hd.deriv]; dsimp [v, D]; field_simp [hD0]
  have hu_x1 : ∀ t ∈ Set.Ioi (0 : ℝ), ∀ x ∈ Set.Ioi x₁, eulerDerivX1 u t x = u t x * (1 - u t x) := fun t ht x hx => by
    have hD0 : x + c + t ≠ 0 := hD_ne (t, x) ⟨ht, hx⟩
    have hden : HasDerivAt (fun y => y + c + t) 1 x := by simpa using ((hasDerivAt_id x).add_const c).add_const t
    have hd : HasDerivAt (fun y => u t y) ((1 * D t x - x * 1) / D t x ^ 2) x := (hasDerivAt_id x).div hden hD0
    simp only [eulerDerivX1, eulerDerivOp]; rw [hd.deriv]; dsimp [u, D]; field_simp [hD0]
  have hv_x1 : ∀ t ∈ Set.Ioi (0 : ℝ), ∀ x ∈ Set.Ioi x₁, eulerDerivX1 v t x = -(u t x * v t x) := fun t ht x hx => by
    have hD0 : x + c + t ≠ 0 := hD_ne (t, x) ⟨ht, hx⟩
    have hden : HasDerivAt (fun y => y + c + t) 1 x := by simpa using ((hasDerivAt_id x).add_const c).add_const t
    have hd : HasDerivAt (fun y => v t y) ((0 * D t x - t * 1) / D t x ^ 2) x := (hasDerivAt_const x t).div hden hD0
    simp only [eulerDerivX1, eulerDerivOp]; rw [hd.deriv]; dsimp [u, v, D]; field_simp [hD0]; ring
  have huv_bd0 : ∀ t > 0, ∀ x > x₁, 0 ≤ u t x ∧ u t x ≤ 2 ∧ 0 ≤ v t x ∧ v t x ≤ 1 := fun t ht x hx => by
    have hDp : 0 < D t x := by linarith [hD_pos t ht x hx]
    exact ⟨div_nonneg (lt_trans hx₁ hx).le hDp.le, (div_le_iff₀ hDp).mpr (by linarith [hD_pos t ht x hx]),
      div_nonneg ht.le hDp.le, (div_le_iff₀ hDp).mpr (by have := (abs_lt.mp hc_lt).1; dsimp [D]; linarith)⟩
  have hbound : ∀ n : ℕ, ∀ j k : ℕ, j + k ≤ n →
      ∃ Cu ≥ 0, ∃ Cv ≥ 0, ∀ t > 0, ∀ x > x₁, |eulerDerivXT j k u t x| ≤ Cu ∧ |eulerDerivXT j k v t x| ≤ Cv := by
    intro n; induction n with
    | zero =>
      intro j k hjk
      obtain rfl : j = 0 := by omega
      obtain rfl : k = 0 := by omega
      refine ⟨2, by norm_num, 1, zero_le_one, fun t ht x hx => ?_⟩
      obtain ⟨hu0, _, hv0, _⟩ := huv_bd0 t ht x hx
      simp only [eulerDerivXT, eulerDerivT, eulerDeriv, Function.iterate_zero, id_eq]
      exact ⟨by rwa [abs_of_nonneg hu0], by rwa [abs_of_nonneg hv0]⟩
    | succ n ih =>
      have ihc : ∀ a b : ℕ, ∃ Cu ≥ 0, ∃ Cv ≥ 0, a + b ≤ n → ∀ t > 0, ∀ x > x₁, |eulerDerivXT a b u t x| ≤ Cu ∧ |eulerDerivXT a b v t x| ≤ Cv :=
        fun a b => if hab : a + b ≤ n then let ⟨Cu, hCu, Cv, hCv, hbd⟩ := ih a b hab; ⟨Cu, hCu, Cv, hCv, fun _ => hbd⟩ else ⟨0, le_rfl, 0, le_rfl, fun h => absurd h hab⟩
      choose Cu hCu_nn Cv hCv_nn huv using ihc
      let C1mu : ℕ → ℕ → ℝ := fun a b => max 1 (Cu a b); let C1mv : ℕ → ℕ → ℝ := fun a b => max 1 (Cv a b)
      have h1m : ∀ {f : ℝ → ℝ → ℝ} {Cf : ℕ → ℕ → ℝ}, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioi x₁) →
          (∀ a b : ℕ, a + b ≤ n → ∀ t > 0, ∀ x > x₁, |eulerDerivXT a b f t x| ≤ Cf a b) → (∀ t > 0, ∀ x > x₁, |1 - f t x| ≤ 1) →
          ∀ a b : ℕ, a + b ≤ n → ∀ t > 0, ∀ x > x₁, |eulerDerivXT a b (fun s y => 1 - f s y) t x| ≤ max 1 (Cf a b) := by
        intro f Cf hfcd hCf hbase a b hab t ht x hx
        rw [eulerDerivXT_sub_open isOpen_Ioi isOpen_Ioi contDiffOn_const hfcd a b t ht x hx]
        rcases eq_or_ne (a + b) 0 with h0 | hpos
        · obtain rfl : a = 0 := by omega
          obtain rfl : b = 0 := by omega
          simpa [eulerDerivXT, eulerDerivT, eulerDeriv] using (hbase t ht x hx).trans (le_max_left _ _)
        · rw [eulerDerivXT_const_pos isOpen_Ioi isOpen_Ioi a b (Nat.pos_of_ne_zero hpos) 1 t ht x hx, zero_sub, abs_neg]
          exact (hCf a b hab t ht x hx).trans (le_max_right _ _)
      have h1mu := h1m hu_cd (fun a b hab t ht x hx => (huv a b hab t ht x hx).1) fun t ht x hx =>
        abs_le.mpr ⟨by linarith [(huv_bd0 t ht x hx).2.1], by linarith [(huv_bd0 t ht x hx).1]⟩
      have h1mv := h1m hv_cd (fun a b hab t ht x hx => (huv a b hab t ht x hx).2) fun t ht x hx =>
        abs_le.mpr ⟨by linarith [(huv_bd0 t ht x hx).2.2.2], by linarith [(huv_bd0 t ht x hx).2.2.1]⟩
      intro j k hjk; cases k with
      | zero =>
        cases j with
        | zero => exact ih 0 0 (by omega)
        | succ j =>
          refine ⟨∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) * Cu a 0 * C1mu (j - a) 0,
            Finset.sum_nonneg fun a _ => by positivity [hCu_nn a 0],
            ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) * Cu a 0 * Cv (j - a) 0,
            Finset.sum_nonneg fun a _ => by positivity [hCu_nn a 0, hCv_nn (j - a) 0], fun t ht x hx => ⟨?_, ?_⟩⟩
          · rw [eulerDerivXT_succ_j_zero isOpen_Ioi hu_x1 j t ht x hx]
            simpa only [Nat.zero_add, Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero] using
              eulerDerivXT_mul_le_of_bound isOpen_Ioi isOpen_Ioi hu_cd (contDiffOn_const.sub hu_cd) ht hx (f := u) (g := fun s y => 1 - u s y)
                (j := j) (k := 0) (A := Cu) (B := C1mu) (w₁ := 1) (w₂ := 1)
                (fun a _ b hb => by obtain rfl : b = 0 := Nat.le_zero.mp hb; simpa only [mul_one] using (huv a 0 (by omega) t ht x hx).1)
                (fun a _ b hb => by obtain rfl : b = 0 := Nat.le_zero.mp hb; simpa only [mul_one] using h1mu a 0 (by omega) t ht x hx)
          · rw [eulerDerivXT_succ_j_zero isOpen_Ioi hv_x1 j t ht x hx, eulerDerivXT_neg_open isOpen_Ioi isOpen_Ioi (hu_cd.mul hv_cd) j 0 t ht x hx, abs_neg]
            simpa only [Nat.zero_add, Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero] using
              eulerDerivXT_mul_le_of_bound isOpen_Ioi isOpen_Ioi hu_cd hv_cd ht hx (j := j) (k := 0) (A := Cu) (B := Cv) (w₁ := 1) (w₂ := 1)
                (fun a _ b hb => by obtain rfl : b = 0 := Nat.le_zero.mp hb; simpa only [mul_one] using (huv a 0 (by omega) t ht x hx).1)
                (fun a _ b hb => by obtain rfl : b = 0 := Nat.le_zero.mp hb; simpa only [mul_one] using (huv a 0 (by omega) t ht x hx).2)
      | succ k =>
        refine ⟨∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (k + 1), (j.choose a : ℝ) * (k.choose b : ℝ) * Cu a b * Cv (j - a) (k - b),
          Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity [hCu_nn a b, hCv_nn (j - a) (k - b)],
          ∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (k + 1), (j.choose a : ℝ) * (k.choose b : ℝ) * Cv a b * C1mv (j - a) (k - b),
          Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity [hCv_nn a b], fun t ht x hx => ⟨?_, ?_⟩⟩
        · rw [eulerDerivXT_succ_k isOpen_Ioi isOpen_Ioi hu_t1 j k t ht x hx, eulerDerivXT_neg_open isOpen_Ioi isOpen_Ioi (hu_cd.mul hv_cd) j k t ht x hx, abs_neg]
          simpa only [mul_one] using eulerDerivXT_mul_le_of_bound isOpen_Ioi isOpen_Ioi hu_cd hv_cd ht hx (j := j) (k := k) (A := Cu) (B := Cv)
            (w₁ := 1) (w₂ := 1) (fun a _ b _ => by simpa only [mul_one] using (huv a b (by omega) t ht x hx).1)
            (fun a _ b _ => by simpa only [mul_one] using (huv a b (by omega) t ht x hx).2)
        · rw [eulerDerivXT_succ_k isOpen_Ioi isOpen_Ioi hv_t1 j k t ht x hx]
          simpa only [mul_one] using eulerDerivXT_mul_le_of_bound isOpen_Ioi isOpen_Ioi hv_cd (contDiffOn_const.sub hv_cd) ht hx (j := j) (k := k)
            (A := Cv) (B := C1mv) (w₁ := 1) (w₂ := 1) (fun a _ b _ => by simpa only [mul_one] using (huv a b (by omega) t ht x hx).2)
            (fun a _ b _ => by simpa only [mul_one] using h1mv a b (by omega) t ht x hx)
  refine ⟨⟨hu_cd, fun j k => ?_⟩, ⟨hv_cd, fun j k => ?_⟩⟩
  · obtain ⟨Cu, hCu, _, _, hbd⟩ := hbound (j + k) j k le_rfl; exact ⟨Cu, hCu, fun t ht x hx => by simpa only [mul_one] using (hbd t ht x hx).1⟩
  · obtain ⟨_, _, Cv, hCv, hbd⟩ := hbound (j + k) j k le_rfl; exact ⟨Cv, hCv, fun t ht x hx => by simpa only [mul_one] using (hbd t ht x hx).2⟩

private lemma isXTBound_cohnWt {x₁ : ℝ} (hx₁ : 0 < x₁) : IsXTBound x₁ cohnWt cohnWt := by
  obtain ⟨hw_cd, hv_bd⟩ := isXTBound_uv_of_shift 0 hx₁ (by simpa using hx₁)
  have h1m : IsXTBound x₁ (fun _ _ => 1) (fun t x => t / (x + t)) := hv_bd.congr fun _ _ _ _ => by simp
  refine isXTBound_of_log_derivs (hw_cd.1.congr fun p _ => by simp [cohnWt])
    ⟨1, zero_le_one, fun t ht x hx => by rw [one_mul, abs_of_nonneg (cohnWt_nonneg ht.le (lt_trans hx₁ hx).le)]⟩
    h1m (h1m.const_mul (-1))
    (fun t ht x hx => by
      have hxt : x + t ≠ 0 := by linarith [Set.mem_Ioi.mp ht, lt_trans hx₁ (Set.mem_Ioi.mp hx)]
      have hd : HasDerivAt (fun y => cohnWt t y) ((1 * (x + t) - x * 1) / (x + t) ^ 2) x := (hasDerivAt_id x).div ((hasDerivAt_id x).add_const t) hxt
      simp only [eulerDerivX1, eulerDerivOp]; rw [hd.deriv]; dsimp [cohnWt]; field_simp [hxt]; ring)
    (fun t ht x hx => by
      have hxt : x + t ≠ 0 := by linarith [Set.mem_Ioi.mp ht, lt_trans hx₁ (Set.mem_Ioi.mp hx)]
      simp only [eulerDerivT, eulerDeriv, Function.iterate_one, eulerDerivOp]; rw [(cohnWt_hasDerivAt hxt).deriv]; dsimp [cohnWt]; field_simp [hxt])

private lemma isXTBound_r {x₁ : ℝ} (hx₁ : 0 < x₁) (ha₁ : 2 * |airyZero 1| < x₁) :
    IsXTBound x₁ (fun _ x => x ^ (-1 : ℝ)) (fun t x => (x + airyZero 1 + t)⁻¹) := by
  obtain ⟨hu_bd, hv_bd⟩ := isXTBound_uv_of_shift (airyZero 1) hx₁ ha₁
  let a₁ : ℝ := airyZero 1; let D : ℝ → ℝ → ℝ := fun t x => x + a₁ + t
  have hD_pos : ∀ t > 0, ∀ x > x₁, x / 2 + t < D t x := fun t _ x hx => by have := (abs_lt.mp (show |a₁| < x₁ / 2 by linarith)).1; dsimp [D]; linarith
  have hD_ne : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi x₁, D p.1 p.2 ≠ 0 := fun p hp => by
    have : 0 < p.2 / 2 + p.1 := by linarith [Set.mem_Ioi.mp hp.1, lt_trans hx₁ (Set.mem_Ioi.mp hp.2)]
    linarith [hD_pos p.1 hp.1 p.2 hp.2]
  refine isXTBound_of_log_derivs (((contDiffOn_snd.add contDiffOn_const).add contDiffOn_fst).inv hD_ne)
    ⟨2, by norm_num, fun t ht x hx => by
      have hDp : 0 < D t x := by linarith [hD_pos t ht x hx]
      rw [abs_of_nonneg (inv_nonneg.mpr hDp.le), Real.rpow_neg_one]
      calc (D t x)⁻¹ ≤ (x / 2)⁻¹ := inv_anti₀ (by linarith [lt_trans hx₁ hx]) (by linarith [hD_pos t ht x hx])
        _ = 2 * x⁻¹ := by ring⟩
    (hu_bd.const_mul (-1)) (hv_bd.const_mul (-1))
    (fun t ht x hx => by
      have hD0 : x + airyZero 1 + t ≠ 0 := hD_ne (t, x) ⟨ht, hx⟩
      have hd : HasDerivAt (fun y => (y + airyZero 1 + t)⁻¹) (-1 / (x + airyZero 1 + t) ^ 2) x :=
        (((hasDerivAt_id x).add_const (airyZero 1)).add_const t).inv hD0
      simp only [eulerDerivX1, eulerDerivOp]; rw [hd.deriv]; field_simp [hD0])
    (fun t ht x hx => by
      have hD0 : x + airyZero 1 + t ≠ 0 := hD_ne (t, x) ⟨ht, hx⟩
      have hd : HasDerivAt (fun s => (x + airyZero 1 + s)⁻¹) (-1 / (x + airyZero 1 + t) ^ 2) t :=
        ((hasDerivAt_id t).const_add (x + airyZero 1)).inv hD0
      simp only [eulerDerivT, eulerDeriv, Function.iterate_one, eulerDerivOp]; rw [hd.deriv]; field_simp [hD0])

private lemma isSymbolOn_inv_add_const {x₁ c : ℝ} (hx₁ : 0 < x₁) (hc : 2 * |c| < x₁) : IsSymbolOn x₁ 1 (fun x : ℝ => (x + c)⁻¹) := by
  have hcx : IsSymbolOn x₁ 0 (fun x : ℝ => c * x⁻¹) := ((IsSymbolOn.inv hx₁).const_mul c).mono_exp hx₁ zero_le_one
  have hG_cd : ContDiffOn ℝ ∞ (fun w : ℝ => (1 + w)⁻¹) (Set.Ioo (-(3 / 4 : ℝ)) (3 / 4)) :=
    ((contDiff_const.add contDiff_id).contDiffOn).inv fun w hw => by dsimp; linarith [hw.1]
  have hrange : ∀ x ≥ x₁, c * x⁻¹ ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := fun x hx =>
    abs_le.mp (by rw [abs_mul, abs_inv, abs_of_pos (lt_of_lt_of_le hx₁ hx), ← div_eq_mul_inv, div_le_iff₀ (lt_of_lt_of_le hx₁ hx)]; linarith)
  have hinv_shift : IsSymbolOn x₁ 0 (fun x : ℝ => (1 + c * x⁻¹)⁻¹) :=
    ((hcx.comp_sub_zero hx₁ le_rfl (a := -(3 / 4)) (a' := -(1 / 2)) (b' := 1 / 2) (b := 3 / 4) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hrange hG_cd).add_same (IsSymbolOn.const hx₁ le_rfl 1)).congr fun _ _ => by simp
  refine ((IsSymbolOn.inv hx₁).mul hx₁ hinv_shift |>.congr ?_).mono_exp hx₁ (by norm_num)
  intro x hx; have hx0 : x ≠ 0 := (lt_of_lt_of_le hx₁ hx).ne'
  have hc_lt : |c| < x₁ / 2 := by linarith
  have hxc0 : x + c ≠ 0 := by have := (abs_lt.mp hc_lt).1; linarith [Set.mem_Ici.mp hx]
  field_simp [hx0, hxc0]

private lemma cr17_bounds_on_open {a : ℝ} (ha : airyAi' a = 0) (ha1 : airyZero 1 < a)
    (hBesselRatio : ∀ z > 0, cohnM z = -Real.sqrt z * besselR ((2 / 3 : ℝ) * z ^ (3 / 2 : ℝ))) {x₂ : ℝ} (hx₂_dom : 2 * max |airyZero 1| |a| < x₂) :
    IsXTBound x₂ (fun t y => cohnWt t y * y ^ (-2 : ℝ)) (fun s y => cohnAtSmooth a s y - cohnWt s y / y) ∧
      IsXTBound x₂ (fun t y => cohnWt t y * y ^ (-3 : ℝ)) (fun s y => cohnBt a s y) ∧
      IsXTBound x₂ (fun t y => cohnWt t y * y ^ (-3 : ℝ)) (fun s y => cohnCt a s y - cohnWt s y / y ^ 2) := by
  have ha0 : a < 0 := by by_contra h; exact (airyAi'_neg (not_lt.mp h)).ne ha
  have hCR16 := cardinal_CR16 ha ha1 ha0 hBesselRatio
  have hCR16_cd := (cardinal_CR16_smooth ha ha1).mono Set.Ioi_subset_Ici_self
  have hCR16_ed : ∀ k : ℕ, ∃ C ≥ 0, ∀ t > 0, |eulerDeriv k (cohnCR16F a) t| ≤ C := fun k => by
    obtain ⟨C, hC, hbd⟩ := hCR16.1 k; refine ⟨C, hC, fun t ht => ?_⟩
    rw [eulerDeriv_congr_open isOpen_Ioi (g := fun s => s * cohnVSmooth a (airyZero 1 + s))
      (fun s hs => by simp [cohnCR16F, ne_of_gt (Set.mem_Ioi.mp hs)]) k ht]; exact hbd t ht
  let a₁ : ℝ := airyZero 1; set x₁ : ℝ := (x₂ + 2 * max |a₁| |a|) / 2
  have hx₁₂ : x₁ < x₂ := by dsimp [x₁]; linarith
  have hx₁_dom : 2 * max |a₁| |a| < x₁ := by dsimp [x₁]; linarith
  have hx₁_pos : 0 < x₁ := lt_of_le_of_lt (by positivity) hx₁_dom; have hx₂_pos : 0 < x₂ := lt_trans hx₁_pos hx₁₂
  have ha₁_dom : 2 * |a₁| < x₁ := lt_of_le_of_lt (by gcongr; exact le_max_left _ _) hx₁_dom
  have ha_dom : 2 * |a| < x₁ := lt_of_le_of_lt (by gcongr; exact le_max_right _ _) hx₁_dom
  have hxa_ne : ∀ y ∈ Set.Ioi x₁, y + a ≠ 0 := fun y hy => by have := (abs_lt.mp (show |a| < x₁ / 2 by linarith)).1; linarith [Set.mem_Ioi.mp hy]
  have hxa_inv_sym := isSymbolOn_inv_add_const hx₁_pos ha_dom
  have hxa_inv_cd : ContDiffOn ℝ ∞ (fun y : ℝ => (y + a)⁻¹) (Set.Ioi x₁) := (contDiffOn_id.add contDiffOn_const).inv hxa_ne
  have hy_inv_cd : ContDiffOn ℝ ∞ (fun y : ℝ => y⁻¹) (Set.Ioi x₁) := contDiffOn_id.inv fun y hy => (lt_trans hx₁_pos hy).ne'
  have hy_sym : IsSymbolOn x₁ (-1) (fun y : ℝ => y) := by simpa using IsSymbolOn.rpow hx₁_pos 1
  have hya₁_sym : IsSymbolOn x₁ (-1) (fun y : ℝ => y + a₁) := by simpa using hy_sym.add hx₁_pos (IsSymbolOn.const hx₁_pos (β := 0) le_rfl a₁)
  have hya_sub_sym : IsSymbolOn x₁ (-1) (fun y : ℝ => y - a) := by simpa using hy_sym.sub hx₁_pos (IsSymbolOn.const hx₁_pos (β := 0) le_rfl a)
  have hF_bd := IsXTBound.pureT (x₁ := x₂) hCR16_cd hCR16_ed; have hw_bd := isXTBound_cohnWt hx₂_pos
  obtain ⟨hu_bd, hv_bd⟩ := isXTBound_uv_of_shift a₁ hx₂_pos (lt_trans ha₁_dom hx₁₂)
  have hr_bd := isXTBound_r hx₂_pos (lt_trans ha₁_dom hx₁₂); have huv_bd := hu_bd.add hv_bd
  have hinv_x_bd := IsXTBound.pureX_of_isSymbolOn hx₁_pos hx₁₂ hy_inv_cd ((IsSymbolOn.inv hx₁_pos).mono_domain hx₁₂.le)
  have hxa_inv_bd := IsXTBound.pureX_of_isSymbolOn hx₁_pos hx₁₂ hxa_inv_cd (hxa_inv_sym.mono_domain hx₁₂.le)
  have hxa_inv2_sym : IsSymbolOn x₁ 2 (fun y : ℝ => (y + a)⁻¹ ^ 2) := by simpa using hxa_inv_sym.pow hx₁_pos 2
  have hxa_inv3_bd := IsXTBound.pureX_of_isSymbolOn hx₁_pos hx₁₂ (hxa_inv_cd.pow 3) (by simpa using (hxa_inv_sym.pow hx₁_pos 3).mono_domain hx₁₂.le)
  have hwy_bd : IsXTBound x₂ (fun t y => cohnWt t y * y ^ (-1 : ℝ)) (fun t y => cohnWt t y / y) := by simpa only [div_eq_mul_inv] using hw_bd.mul hinv_x_bd
  have hA1_sym : IsSymbolOn x₁ 1 (fun y : ℝ => ((a₁ - 3 * a) * y - (a * a₁ + a ^ 2)) * (y + a)⁻¹ ^ 2) := by
    have h := (hy_sym.const_mul (a₁ - 3 * a)).sub hx₁_pos (IsSymbolOn.const hx₁_pos (β := 0) le_rfl (a * a₁ + a ^ 2))
    rw [show min (-1 : ℝ) 0 = -1 by norm_num] at h; simpa only [show (-1 : ℝ) + 2 = 1 by norm_num] using h.mul hx₁_pos hxa_inv2_sym
  have hA1_bd := IsXTBound.pureX_of_isSymbolOn hx₁_pos hx₁₂ (((contDiffOn_const.mul contDiffOn_id).sub contDiffOn_const).mul (hxa_inv_cd.pow 2)) (hA1_sym.mono_domain hx₁₂.le)
  have hA2_sym : IsSymbolOn x₁ 0 (fun y : ℝ => (y - a) * (y + a₁) * (y + a)⁻¹ ^ 2) := by
    have hnum := hya_sub_sym.mul hx₁_pos hya₁_sym; rw [show (-1 : ℝ) + -1 = -2 by norm_num] at hnum
    simpa only [show (-2 : ℝ) + 2 = 0 by norm_num] using hnum.mul hx₁_pos hxa_inv2_sym
  have hA2_bd : IsXTBound x₂ (fun _ y => y ^ (-1 : ℝ)) (fun t y => a₁ * ((y - a) * (y + a₁) * (y + a)⁻¹ ^ 2) * (y + a₁ + t)⁻¹) :=
    (((IsXTBound.pureX_of_isSymbolOn hx₁_pos hx₁₂ (((contDiffOn_id.sub contDiffOn_const).mul (contDiffOn_id.add contDiffOn_const)).mul (hxa_inv_cd.pow 2))
      (hA2_sym.mono_domain hx₁₂.le)).const_mul a₁).mul hr_bd).mono_bound fun _ _ _ _ => by simp only [neg_zero, Real.rpow_zero, one_mul, le_rfl]
  have hA_t1 : IsXTBound x₂ (fun t y => cohnWt t y * y ^ (-2 : ℝ))
      (fun t y => (cohnWt t y / y) * (((a₁ - 3 * a) * y - (a * a₁ + a ^ 2)) * (y + a)⁻¹ ^ 2 - a₁ * ((y - a) * (y + a₁) * (y + a)⁻¹ ^ 2) * (y + a₁ + t)⁻¹)) :=
    (hwy_bd.mul (hA1_bd.sub hA2_bd)).mono_bound fun _ _ y hy => by have hy0 : 0 < y := lt_trans hx₂_pos hy; rw [mul_assoc, ← Real.rpow_add hy0]; norm_num
  have hA_t2 : IsXTBound x₂ (fun t y => cohnWt t y * y ^ (-2 : ℝ))
      (fun t y => a * (cohnWt t y * y⁻¹) * (y / (y + a₁ + t) + t / (y + a₁ + t)) * (t / (y + a₁ + t)) * (y + a)⁻¹) :=
    ((((hwy_bd.const_mul a).mul huv_bd).mul hv_bd).mul hxa_inv_bd).mono_bound fun _ _ y hy => by have hy0 : 0 < y := lt_trans hx₂_pos hy; rw [mul_one, mul_one, mul_assoc, ← Real.rpow_add hy0]; norm_num
  have hA_t3 : IsXTBound x₂ (fun t y => cohnWt t y * y ^ (-2 : ℝ))
      (fun t y => (cohnWt t y * y⁻¹) * (y / (y + a₁ + t) + t / (y + a₁ + t)) * (y + a₁ + t)⁻¹ * cohnCR16F a t) :=
    (((hwy_bd.mul huv_bd).mul hr_bd).mul hF_bd).mono_bound fun _ _ y hy => by have hy0 : 0 < y := lt_trans hx₂_pos hy; rw [mul_one, mul_one, mul_assoc, ← Real.rpow_add hy0]; norm_num
  have hA_full : IsXTBound x₂ (fun t y => cohnWt t y * y ^ (-2 : ℝ)) (fun s y => cohnAtSmooth a s y - cohnWt s y / y) := by
    refine ((hA_t1.add hA_t2).sub hA_t3).congr fun t ht y hy => ?_
    have hy0 : 0 < y := lt_trans hx₂_pos hy; have hyt0 : y + t ≠ 0 := by linarith
    have hya0 := hxa_ne y (Set.mem_Ioi.mpr (lt_trans hx₁₂ hy)); have hD0 : y + a₁ + t ≠ 0 := by have := (abs_lt.mp (show |a₁| < x₁ / 2 by linarith)).1; linarith [lt_trans hx₁₂ hy]
    dsimp only [cohnAtSmooth, cohnWt, cohnCR16F]; rw [show airyZero 1 = a₁ from rfl, show y / (y + a₁ + t) + t / (y + a₁ + t) = (y + t) / (y + a₁ + t) by ring]
    simp only [ht.ne', ↓reduceIte]; field_simp [hy0.ne', hyt0, hya0, hD0]; ring
  have hB1_bd : IsXTBound x₂ (fun _ y => y ^ (1 : ℝ)) (fun t y => (-2 * (y + a₁) ^ 2) * (y + a₁ + t)⁻¹) := by
    have hnum_sym : IsSymbolOn x₁ (-2) (fun y : ℝ => -2 * (y + a₁) ^ 2) := by simpa using (hya₁_sym.pow hx₁_pos 2).const_mul (-2)
    exact ((IsXTBound.pureX_of_isSymbolOn hx₁_pos hx₁₂ (contDiffOn_const.mul ((contDiffOn_id.add contDiffOn_const).pow 2))
      (hnum_sym.mono_domain hx₁₂.le)).mul hr_bd).mono_bound fun _ _ y hy => by have hy0 : 0 < y := lt_trans hx₂_pos hy; rw [neg_neg, ← Real.rpow_add hy0]; norm_num
  have hB2_bd : IsXTBound x₂ (fun _ y => y ^ (1 : ℝ)) (fun t y => (a - y - 2 * a₁) * (t / (y + a₁ + t))) := by
    have h1 := (IsSymbolOn.const hx₁_pos (β := 0) le_rfl a).sub hx₁_pos hy_sym; rw [show min (0 : ℝ) (-1) = -1 by norm_num] at h1
    have h2 := h1.sub hx₁_pos (IsSymbolOn.const hx₁_pos (β := 0) le_rfl (2 * a₁)); rw [show min (-1 : ℝ) 0 = -1 by norm_num] at h2
    exact ((IsXTBound.pureX_of_isSymbolOn hx₁_pos hx₁₂ ((contDiffOn_const.sub contDiffOn_id).sub contDiffOn_const) (h2.mono_domain hx₁₂.le)).mul hv_bd).mono_bound fun _ _ _ _ => by simp
  have hB_full : IsXTBound x₂ (fun t y => cohnWt t y * y ^ (-3 : ℝ)) (fun s y => cohnBt a s y) := by
    refine ((((hwy_bd.mul huv_bd).mul hxa_inv3_bd).mul (hB1_bd.add hB2_bd)).mono_bound fun _ _ y hy => by
      have hy0 : 0 < y := lt_trans hx₂_pos hy; rw [mul_one, mul_assoc, mul_assoc, ← Real.rpow_add hy0, ← Real.rpow_add hy0, show (-1 : ℝ) + (-3 + 1) = -3 by norm_num]).congr fun t _ y hy => ?_
    have hy0 : 0 < y := lt_trans hx₂_pos hy; have hyt0 : y + t ≠ 0 := by linarith
    have hya0 := hxa_ne y (Set.mem_Ioi.mpr (lt_trans hx₁₂ hy)); have hD0 : y + a₁ + t ≠ 0 := by have := (abs_lt.mp (show |a₁| < x₁ / 2 by linarith)).1; linarith [lt_trans hx₁₂ hy]
    dsimp only [cohnBt, cohnWt]; rw [show airyZero 1 = a₁ from rfl, show y / (y + a₁ + t) + t / (y + a₁ + t) = (y + t) / (y + a₁ + t) by ring]; field_simp [hy0.ne', hyt0, hya0, hD0]
  have hC1_sym : IsSymbolOn x₁ 2 (fun y : ℝ => ((a₁ - 2 * a) * y - a ^ 2) * y⁻¹ * (y + a)⁻¹ ^ 2) := by
    have h := (hy_sym.const_mul (a₁ - 2 * a)).sub hx₁_pos (IsSymbolOn.const hx₁_pos (β := 0) le_rfl (a ^ 2))
    rw [show min (-1 : ℝ) 0 = -1 by norm_num] at h; simpa only [show (-1 : ℝ) + 1 + 2 = 2 by norm_num] using (h.mul hx₁_pos (IsSymbolOn.inv hx₁_pos)).mul hx₁_pos hxa_inv2_sym
  have hC1_bd := IsXTBound.pureX_of_isSymbolOn hx₁_pos hx₁₂ ((((contDiffOn_const.mul contDiffOn_id).sub contDiffOn_const).mul hy_inv_cd).mul (hxa_inv_cd.pow 2)) (hC1_sym.mono_domain hx₁₂.le)
  have hC2_sym : IsSymbolOn x₁ 1 (fun y : ℝ => (y + a₁) * (y + a)⁻¹ ^ 2) := by
    simpa only [show (-1 : ℝ) + 2 = 1 by norm_num] using hya₁_sym.mul hx₁_pos hxa_inv2_sym
  have hC2_bd : IsXTBound x₂ (fun _ y => y ^ (-2 : ℝ)) (fun t y => a₁ * ((y + a₁) * (y + a)⁻¹ ^ 2) * (y + a₁ + t)⁻¹) :=
    (((IsXTBound.pureX_of_isSymbolOn hx₁_pos hx₁₂ ((contDiffOn_id.add contDiffOn_const).mul (hxa_inv_cd.pow 2))
      (hC2_sym.mono_domain hx₁₂.le)).const_mul a₁).mul hr_bd).mono_bound
      fun _ _ y hy => by have hy0 : 0 < y := lt_trans hx₂_pos hy; rw [← Real.rpow_add hy0]; norm_num
  have hC_full : IsXTBound x₂ (fun t y => cohnWt t y * y ^ (-3 : ℝ)) (fun s y => cohnCt a s y - cohnWt s y / y ^ 2) := by
    refine ((hwy_bd.mul (hC1_bd.sub hC2_bd)).mono_bound fun _ _ y hy => by
      have hy0 : 0 < y := lt_trans hx₂_pos hy; rw [mul_assoc, ← Real.rpow_add hy0, show (-1 : ℝ) + -2 = -3 by norm_num]).congr fun t _ y hy => ?_
    have hy0 : 0 < y := lt_trans hx₂_pos hy; have hyt0 : y + t ≠ 0 := by linarith
    have hya0 := hxa_ne y (Set.mem_Ioi.mpr (lt_trans hx₁₂ hy)); have hD0 : y + a₁ + t ≠ 0 := by have := (abs_lt.mp (show |a₁| < x₁ / 2 by linarith)).1; linarith [lt_trans hx₁₂ hy]
    dsimp only [cohnCt, cohnWt, id]; rw [show airyZero 1 = a₁ from rfl]; field_simp [hy0.ne', hyt0, hya0, hD0]; ring
  exact ⟨hA_full, hB_full, hC_full⟩

/-- **Theorem CR.4 Step 2, eq. `(CR.17)`:** Uniform two-parameter `(x ∂_x)^j (t ∂_t)^k` bounds
for `cohnAtSmooth - w_t / x`, `cohnBt`, and `cohnCt - w_t / x^2` for all `j, k : ℕ`,
`x ≥ x₀ > 2 max(|a₁|, |a|)`, and `t > 0`. -/
theorem cardinal_CR17 {a : ℝ} (ha : airyAi' a = 0) (ha1 : airyZero 1 < a)
    (hBesselRatio : ∀ z > 0, cohnM z = -Real.sqrt z * besselR ((2 / 3 : ℝ) * z ^ (3 / 2 : ℝ)))
    {x₀ : ℝ} (_hx₀_pos : 0 < x₀) (hx₀_dom : 2 * max |airyZero 1| |a| < x₀) :
    ∀ j k : ℕ,
      (∃ C ≥ 0, ∀ t > 0, ∀ x ≥ x₀, |eulerDerivXT j k (fun s y => cohnAtSmooth a s y - cohnWt s y / y) t x| ≤ C * cohnWt t x * x ^ (-2 : ℝ)) ∧
      (∃ C ≥ 0, ∀ t > 0, ∀ x ≥ x₀, |eulerDerivXT j k (fun s y => cohnBt a s y) t x| ≤ C * cohnWt t x * x ^ (-3 : ℝ)) ∧
      (∃ C ≥ 0, ∀ t > 0, ∀ x ≥ x₀, |eulerDerivXT j k (fun s y => cohnCt a s y - cohnWt s y / y ^ 2) t x| ≤ C * cohnWt t x * x ^ (-3 : ℝ)) := by
  set x₂ : ℝ := (x₀ + 2 * max |airyZero 1| |a|) / 2
  have hx₂_lt : x₂ < x₀ := by dsimp [x₂]; linarith
  obtain ⟨hA, hB, hC⟩ := cr17_bounds_on_open ha ha1 hBesselRatio (x₂ := x₂) (by dsimp [x₂]; linarith)
  intro j k; obtain ⟨CA, hCA, hAbd⟩ := hA.2 j k; obtain ⟨CB, hCB, hBbd⟩ := hB.2 j k; obtain ⟨CC, hCC, hCbd⟩ := hC.2 j k
  exact ⟨⟨CA, hCA, fun t ht x hx => by simpa [mul_assoc] using hAbd t ht x (lt_of_lt_of_le hx₂_lt hx)⟩,
    ⟨CB, hCB, fun t ht x hx => by simpa [mul_assoc] using hBbd t ht x (lt_of_lt_of_le hx₂_lt hx)⟩,
    ⟨CC, hCC, fun t ht x hx => by simpa [mul_assoc] using hCbd t ht x (lt_of_lt_of_le hx₂_lt hx)⟩⟩

private lemma isXTBound_two_sub_sq {x₂ : ℝ} (hx₂ : 0 < x₂) : IsXTBound x₂ cohnWt (fun t x => 2 * cohnWt t x - cohnWt t x ^ 2) := by
  have hw := isXTBound_cohnWt hx₂
  have hw1 : IsXTBound x₂ (fun _ _ => 1) cohnWt := (isXTBound_uv_of_shift 0 hx₂ (by simpa using hx₂)).1.congr fun _ _ _ _ => by simp [cohnWt]
  exact (hw.const_mul 2).sub (((hw.mul hw1).congr (g := fun t x => cohnWt t x ^ 2) fun _ _ _ _ => by ring).mono_bound fun _ _ _ _ => by rw [mul_one])

private lemma sub_wt_div_gen_eq {x₂ : ℝ} (hx₂_pos : 0 < x₂) {g : ℝ → ℝ → ℝ}
    (hg_cd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => g p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioi x₂)) {m : ℕ} {t y : ℝ} (ht : 0 < t) (hy : x₂ < y) :
    (g t y - t * _root_.deriv (fun s => g s y) t) - (2 * cohnWt t y - cohnWt t y ^ 2) / y ^ m =
      (g t y - cohnWt t y / y ^ m) - eulerDerivT 1 (fun s z => g s z - cohnWt s z / z ^ m) t y := by
  have hyt : y + t ≠ 0 := by linarith [lt_trans hx₂_pos hy]
  have hd : HasDerivAt (fun s => g s y - cohnWt s y / y ^ m)
      (_root_.deriv (fun s => g s y) t - _root_.deriv (fun s => cohnWt s y) t / y ^ m) t :=
    (((contDiffOn_sliceT hg_cd hy).contDiffAt (Ioi_mem_nhds ht)).differentiableAt (by simp)).hasDerivAt.sub
      ((cohnWt_hasDerivAt hyt).differentiableAt.hasDerivAt.div_const (y ^ m))
  simp only [eulerDerivT, eulerDeriv, Function.iterate_one, eulerDerivOp]; rw [hd.deriv, ← one_sub_t_mul_deriv_cohnWt hyt]; ring

private lemma cardinal_CR17_gen_deriv_open {a : ℝ} (ha : airyAi' a = 0) (ha1 : airyZero 1 < a)
    (hBesselRatio : ∀ z > 0, cohnM z = -Real.sqrt z * besselR ((2 / 3 : ℝ) * z ^ (3 / 2 : ℝ))) {x₂ : ℝ} (hx₂_dom : 2 * max |airyZero 1| |a| < x₂) :
    let U_x := Set.Ioi x₂
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => 2 * cohnWt p.1 p.2 - cohnWt p.1 p.2 ^ 2) (Set.Ioi 0 ×ˢ U_x) ∧
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => cohnAtGen a p.1 p.2 - (2 * cohnWt p.1 p.2 - cohnWt p.1 p.2 ^ 2) / p.2) (Set.Ioi 0 ×ˢ U_x) ∧
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => cohnBtGen a p.1 p.2) (Set.Ioi 0 ×ˢ U_x) ∧
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => cohnCtGen a p.1 p.2 - (2 * cohnWt p.1 p.2 - cohnWt p.1 p.2 ^ 2) / p.2 ^ 2) (Set.Ioi 0 ×ˢ U_x) ∧
    (∀ j : ℕ, ∃ C ≥ 0, ∀ t > 0, ∀ x > x₂, |iteratedDeriv j (fun y => 2 * cohnWt t y - cohnWt t y ^ 2) x| ≤ C * cohnWt t x * x ^ (-(j : ℝ))) ∧
    (∀ j : ℕ, ∃ C ≥ 0, ∀ t > 0, ∀ x > x₂, |iteratedDeriv j (fun y => cohnAtGen a t y - (2 * cohnWt t y - cohnWt t y ^ 2) / y) x| ≤ C * cohnWt t x * x ^ (-2 - (j : ℝ))) ∧
    (∀ j : ℕ, ∃ C ≥ 0, ∀ t > 0, ∀ x > x₂, |iteratedDeriv j (fun y => cohnBtGen a t y) x| ≤ C * cohnWt t x * x ^ (-3 - (j : ℝ))) ∧
    (∀ j : ℕ, ∃ C ≥ 0, ∀ t > 0, ∀ x > x₂, |iteratedDeriv j (fun y => cohnCtGen a t y - (2 * cohnWt t y - cohnWt t y ^ 2) / y ^ 2) x| ≤ C * cohnWt t x * x ^ (-3 - (j : ℝ))) := by
  have hx₂_pos : 0 < x₂ := lt_of_le_of_lt (by positivity) hx₂_dom
  obtain ⟨hA, hB, hC⟩ := cr17_bounds_on_open ha ha1 hBesselRatio hx₂_dom; have hQ := isXTBound_two_sub_sq hx₂_pos
  let fA : ℝ → ℝ → ℝ := fun s y => cohnAtSmooth a s y - cohnWt s y / y; let fC : ℝ → ℝ → ℝ := fun s y => cohnCt a s y - cohnWt s y / y ^ 2
  have hGen_cd : ∀ {f : ℝ → ℝ → ℝ}, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioi x₂) →
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2 - eulerDerivT 1 f p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioi x₂) := fun hf => hf.sub (contDiffOn_eulerDerivT isOpen_Ioi isOpen_Ioi hf 1)
  have hw_cd := (isXTBound_cohnWt hx₂_pos).1
  have hy_inv_cd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => p.2⁻¹) (Set.Ioi 0 ×ˢ Set.Ioi x₂) := contDiffOn_snd.inv fun p hp => (lt_trans hx₂_pos hp.2).ne'
  have hAt_cd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => cohnAtSmooth a p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioi x₂) := (hA.1.add (hw_cd.mul hy_inv_cd)).congr fun p _ => by dsimp [fA]; ring
  have hCt_cd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => cohnCt a p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioi x₂) := (hC.1.add (hw_cd.mul (hy_inv_cd.pow 2))).congr fun p _ => by dsimp [fC]; ring
  have hA_eq : ∀ t > 0, ∀ y > x₂, cohnAtGen a t y - (2 * cohnWt t y - cohnWt t y ^ 2) / y = fA t y - eulerDerivT 1 fA t y :=
    fun t ht y hy => by simpa only [pow_one, cohnAtGen] using sub_wt_div_gen_eq hx₂_pos hAt_cd (m := 1) ht hy
  have hC_eq : ∀ t > 0, ∀ y > x₂, cohnCtGen a t y - (2 * cohnWt t y - cohnWt t y ^ 2) / y ^ 2 = fC t y - eulerDerivT 1 fC t y :=
    fun t ht y hy => by simpa only [cohnCtGen] using sub_wt_div_gen_eq hx₂_pos hCt_cd (m := 2) ht hy
  have h_to_iter : ∀ {f : ℝ → ℝ → ℝ} {m : ℝ}, IsXTBound x₂ (fun t y => cohnWt t y * y ^ (-m)) f →
      ∀ j : ℕ, ∃ C ≥ 0, ∀ t > 0, ∀ x > x₂, |iteratedDeriv j (fun y => f t y - eulerDerivT 1 f t y) x| ≤ C * cohnWt t x * x ^ (-m - (j : ℝ)) := by
    intro f m hf j; choose C0 hC0 hbd0 using fun i => hf.2 i 0; choose C1 hC1 hbd1 using fun i => hf.2 i 1
    obtain ⟨C, hC, hiter⟩ := iteratedDeriv_bound_of_eulerDeriv j fun i => add_nonneg (hC0 i) (hC1 i)
    refine ⟨C, hC, fun t ht x hx => ?_⟩; have hxpos : 0 < x := lt_trans hx₂_pos hx
    have hf0_x := contDiffOn_sliceX hf.1 ht; have hf1_x := contDiffOn_sliceX (contDiffOn_eulerDerivT isOpen_Ioi isOpen_Ioi hf.1 1) ht
    have h1 := hiter isOpen_Ioi (hf0_x.sub hf1_x) hx hxpos (mul_nonneg (cohnWt_nonneg ht.le hxpos.le) (Real.rpow_nonneg hxpos.le _))
      fun i _ => by rw [eulerDeriv_sub_open isOpen_Ioi hf0_x hf1_x i x hx]
                    calc |eulerDerivXT i 0 f t x - eulerDerivXT i 1 f t x| ≤ |eulerDerivXT i 0 f t x| + |eulerDerivXT i 1 f t x| := abs_sub _ _
                      _ ≤ (C0 i + C1 i) * (cohnWt t x * x ^ (-m)) := by linarith [hbd0 i t ht x hx, hbd1 i t ht x hx]
    calc |iteratedDeriv j (fun y => f t y - eulerDerivT 1 f t y) x| ≤ C * (cohnWt t x * x ^ (-m)) * x ^ (-(j : ℝ)) := h1
      _ = C * cohnWt t x * x ^ (-m - (j : ℝ)) := by rw [mul_assoc, mul_assoc, ← Real.rpow_add hxpos, sub_eq_add_neg]; ring
  refine ⟨hQ.1, (hGen_cd hA.1).congr fun p hp => hA_eq p.1 hp.1 p.2 hp.2, hGen_cd hB.1, (hGen_cd hC.1).congr fun p hp => hC_eq p.1 hp.1 p.2 hp.2,
    ?_, ?_, fun j => h_to_iter hB j, ?_⟩
  · intro j; choose C0 hC0 hbd0 using fun i => hQ.2 i 0; obtain ⟨C, hC, hiter⟩ := iteratedDeriv_bound_of_eulerDeriv j hC0
    exact ⟨C, hC, fun t ht x hx => hiter isOpen_Ioi (contDiffOn_sliceX hQ.1 ht) hx (lt_trans hx₂_pos hx) (cohnWt_nonneg ht.le (lt_trans hx₂_pos hx).le) fun i _ => hbd0 i t ht x hx⟩
  · intro j; obtain ⟨C, hC, hbd⟩ := h_to_iter (f := fA) hA j; refine ⟨C, hC, fun t ht x hx => ?_⟩
    have hev : (fun y => cohnAtGen a t y - (2 * cohnWt t y - cohnWt t y ^ 2) / y) =ᶠ[𝓝 x] (fun y => fA t y - eulerDerivT 1 fA t y) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hx) fun y hy => hA_eq t ht y hy
    rw [hev.iteratedDeriv_eq]; exact hbd t ht x hx
  · intro j; obtain ⟨C, hC, hbd⟩ := h_to_iter (f := fC) hC j; refine ⟨C, hC, fun t ht x hx => ?_⟩
    have hev : (fun y => cohnCtGen a t y - (2 * cohnWt t y - cohnWt t y ^ 2) / y ^ 2) =ᶠ[𝓝 x] (fun y => fC t y - eulerDerivT 1 fC t y) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hx) fun y hy => hC_eq t ht y hy
    rw [hev.iteratedDeriv_eq]; exact hbd t ht x hx

/-- Ordinary `x`-derivative form of `(CR.17)` on `(1 - t ∂_t)`-transformed coefficients. -/
theorem cardinal_CR17_derivWithin {a : ℝ} (ha : airyAi' a = 0) (ha1 : airyZero 1 < a)
    (hBesselRatio : ∀ z > 0, cohnM z = -Real.sqrt z * besselR ((2 / 3 : ℝ) * z ^ (3 / 2 : ℝ)))
    {x₀ : ℝ} (_hx₀_pos : 0 < x₀) (hx₀_dom : 2 * max |airyZero 1| |a| < x₀) :
    ∀ j : ℕ,
      (∃ C ≥ 0, ∀ t > 0, ∀ x ≥ x₀, |iteratedDeriv j (fun y => 2 * cohnWt t y - cohnWt t y ^ 2) x| ≤ C * cohnWt t x * x ^ (-(j : ℝ))) ∧
      (∃ C ≥ 0, ∀ t > 0, ∀ x ≥ x₀, |iteratedDeriv j (fun y => cohnAtGen a t y - (2 * cohnWt t y - cohnWt t y ^ 2) / y) x| ≤ C * cohnWt t x * x ^ (-2 - (j : ℝ))) ∧
      (∃ C ≥ 0, ∀ t > 0, ∀ x ≥ x₀, |iteratedDeriv j (fun y => cohnBtGen a t y) x| ≤ C * cohnWt t x * x ^ (-3 - (j : ℝ))) ∧
      (∃ C ≥ 0, ∀ t > 0, ∀ x ≥ x₀, |iteratedDeriv j (fun y => cohnCtGen a t y - (2 * cohnWt t y - cohnWt t y ^ 2) / y ^ 2) x| ≤ C * cohnWt t x * x ^ (-3 - (j : ℝ))) := by
  set x₂ : ℝ := (x₀ + 2 * max |airyZero 1| |a|) / 2; have hx₂_lt : x₂ < x₀ := by dsimp [x₂]; linarith
  have h := cardinal_CR17_gen_deriv_open ha ha1 hBesselRatio (x₂ := x₂) (by dsimp [x₂]; linarith)
  intro j; obtain ⟨CQ, hCQ, hQbd⟩ := h.2.2.2.2.1 j; obtain ⟨CA, hCA, hAbd⟩ := h.2.2.2.2.2.1 j
  obtain ⟨CB, hCB, hBbd⟩ := h.2.2.2.2.2.2.1 j; obtain ⟨CC, hCC, hCbd⟩ := h.2.2.2.2.2.2.2 j
  exact ⟨⟨CQ, hCQ, fun t ht x hx => hQbd t ht x (lt_of_lt_of_le hx₂_lt hx)⟩, ⟨CA, hCA, fun t ht x hx => hAbd t ht x (lt_of_lt_of_le hx₂_lt hx)⟩,
    ⟨CB, hCB, fun t ht x hx => hBbd t ht x (lt_of_lt_of_le hx₂_lt hx)⟩, ⟨CC, hCC, fun t ht x hx => hCbd t ht x (lt_of_lt_of_le hx₂_lt hx)⟩⟩

/-! ### Parametric measure differentiation and Step 3 (`(CR.20)` & `(CR.21)`) -/

private lemma derivX_iterate (j : ℕ) (H : ℝ → ℝ → ℝ) (t x : ℝ) : (derivX^[j] H) t x = iteratedDeriv j (fun z => H t z) x := by
  induction j generalizing H x with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', iteratedDeriv_succ]; change _root_.deriv (fun y => (derivX^[j] H) t y) x = _; congr 1; funext y; exact ih H y

private lemma parametric_integral_hasDerivAt {Λ : Measure ℝ} [IsFiniteMeasure Λ] {U_x : Set ℝ} (hUx : IsOpen U_x) {G : ℝ → ℝ → ℝ}
    (hG_cd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => G p.1 p.2) (Set.Ioi 0 ×ˢ U_x)) (hG_bd : ∃ M₀ ≥ 0, ∀ y ∈ U_x, ∀ t > 0, |G t y| ≤ M₀)
    (hG'_bd : ∃ M₁ ≥ 0, ∀ y ∈ U_x, ∀ t > 0, |derivX G t y| ≤ M₁) :
    ∀ x ∈ U_x, HasDerivAt (fun y => ∫ t in Set.Ioi (0 : ℝ), G t y ∂Λ) (∫ t in Set.Ioi (0 : ℝ), derivX G t x ∂Λ) x := by
  intro x hx; obtain ⟨M₀, _, hbd₀⟩ := hG_bd; obtain ⟨M₁, _, hbd₁⟩ := hG'_bd; obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hUx x hx
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds x hδ)
    (Filter.eventually_of_mem (hUx.mem_nhds hx) fun y hy => (contDiffOn_sliceT hG_cd hy).continuousOn.aestronglyMeasurable measurableSet_Ioi)
    ((integrable_const M₀).mono' ((contDiffOn_sliceT hG_cd hx).continuousOn.aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by simpa [Real.norm_eq_abs] using hbd₀ x hx t ht))
    ((contDiffOn_sliceT (contDiffOn_derivX isOpen_Ioi hUx hG_cd) hx).continuousOn.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht y hy => by simpa [derivX, Real.norm_eq_abs] using hbd₁ y (hball hy) t ht)
    (integrable_const M₁)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht y hy =>
      (((contDiffOn_sliceX hG_cd ht).contDiffAt (hUx.mem_nhds (hball hy))).differentiableAt (by simp)).hasDerivAt)).2

private lemma parametric_integral_contDiffOn {Λ : Measure ℝ} [IsFiniteMeasure Λ] {U_x : Set ℝ} (hUx : IsOpen U_x) :
    ∀ n : ℕ, ∀ H : ℝ → ℝ → ℝ, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => H p.1 p.2) (Set.Ioi 0 ×ˢ U_x) →
      (∀ j : ℕ, ∃ M ≥ 0, ∀ y ∈ U_x, ∀ t > 0, |iteratedDeriv j (fun z => H t z) y| ≤ M) →
      ContDiffOn ℝ n (fun y => ∫ t in Set.Ioi (0 : ℝ), H t y ∂Λ) U_x := by
  intro n; induction n with
  | zero =>
    intro H hH_cd hH_bd; obtain ⟨M₀, hM₀, hbd₀⟩ := hH_bd 0; obtain ⟨M₁, hM₁, hbd₁⟩ := hH_bd 1
    have hd := parametric_integral_hasDerivAt (Λ := Λ) hUx hH_cd ⟨M₀, hM₀, by simpa using hbd₀⟩
      ⟨M₁, hM₁, fun y hy t ht => by simpa [derivX, iteratedDeriv_one] using hbd₁ y hy t ht⟩
    change ContDiffOn ℝ 0 _ U_x; rw [contDiffOn_zero]; exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  | succ n ih =>
    intro H hH_cd hH_bd; obtain ⟨M₀, hM₀, hbd₀⟩ := hH_bd 0; obtain ⟨M₁, hM₁, hbd₁⟩ := hH_bd 1
    have hd := parametric_integral_hasDerivAt (Λ := Λ) hUx hH_cd ⟨M₀, hM₀, by simpa using hbd₀⟩
      ⟨M₁, hM₁, fun y hy t ht => by simpa [derivX, iteratedDeriv_one] using hbd₁ y hy t ht⟩
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen hUx]
    refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, fun h => absurd h (by simp), ?_⟩
    exact (ih (derivX H) (contDiffOn_derivX isOpen_Ioi hUx hH_cd) fun j => by
      obtain ⟨M, hM, hbd⟩ := hH_bd (j + 1); refine ⟨M, hM, fun y hy t ht => ?_⟩
      have heq : (fun z => derivX H t z) = iteratedDeriv 1 (fun z => H t z) := funext fun z => by simp [derivX, iteratedDeriv_one]
      simpa [heq, ← iteratedDeriv_succ'] using hbd y hy t ht).congr fun x hx => (hd x hx).deriv

private lemma parametric_integral_iteratedDeriv {Λ : Measure ℝ} [IsFiniteMeasure Λ] {U_x : Set ℝ} (hUx : IsOpen U_x) :
    ∀ j : ℕ, ∀ H : ℝ → ℝ → ℝ, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => H p.1 p.2) (Set.Ioi 0 ×ˢ U_x) →
      (∀ m : ℕ, ∃ M ≥ 0, ∀ y ∈ U_x, ∀ t > 0, |iteratedDeriv m (fun z => H t z) y| ≤ M) →
      ∀ x ∈ U_x, iteratedDeriv j (fun y => ∫ t in Set.Ioi (0 : ℝ), H t y ∂Λ) x = ∫ t in Set.Ioi (0 : ℝ), iteratedDeriv j (fun z => H t z) x ∂Λ := by
  intro j; induction j with
  | zero => intro _ _ _ _ _; rfl
  | succ j ih =>
    intro H hH_cd hH_bd x hx; rw [iteratedDeriv_succ]
    have hev : iteratedDeriv j (fun y => ∫ t in Set.Ioi (0 : ℝ), H t y ∂Λ) =ᶠ[𝓝 x] (fun y => ∫ t in Set.Ioi (0 : ℝ), (derivX^[j] H) t y ∂Λ) :=
      Filter.eventually_of_mem (hUx.mem_nhds hx) fun y hy => by rw [ih H hH_cd hH_bd y hy]; simp [derivX_iterate]
    obtain ⟨Mj, hMj, hbdj⟩ := hH_bd j; obtain ⟨Mj1, hMj1, hbdj1⟩ := hH_bd (j + 1)
    have hsucc : ∀ t y, derivX (derivX^[j] H) t y = (derivX^[j + 1] H) t y := fun t y => Function.iterate_succ_apply' derivX j H ▸ rfl
    have hd := parametric_integral_hasDerivAt (Λ := Λ) hUx (contDiffOn_derivX_iterate isOpen_Ioi hUx hH_cd j)
      ⟨Mj, hMj, fun y hy t ht => by simpa [derivX_iterate] using hbdj y hy t ht⟩
      ⟨Mj1, hMj1, fun y hy t ht => by rw [hsucc, derivX_iterate]; exact hbdj1 y hy t ht⟩
    rw [hev.deriv_eq, (hd x hx).deriv]; exact congrArg _ (funext fun t => by rw [hsucc, derivX_iterate])

private lemma weighted_symbol_of_cr17_integrand {x₀ x₂ β : ℝ} (hx₂_pos : 0 < x₂) (hx₂_lt : x₂ < x₀) (_hβ : 0 ≤ β) {H : ℝ → ℝ → ℝ}
    (hH_cd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => H p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioi x₂))
    (hH_bd : ∀ j : ℕ, ∃ C ≥ 0, ∀ t > 0, ∀ x > x₂, |iteratedDeriv j (fun z => H t z) x| ≤ C * cohnWt t x * x ^ (-β - (j : ℝ))) :
    (∀ j : ℕ, ∃ C ≥ 0, ∀ (Λ : Measure ℝ), IsProbabilityMeasure Λ →
      ∀ x ≥ x₀, |iteratedDerivWithin j (fun y => ∫ t in Set.Ioi (0 : ℝ), H t y ∂Λ) (Set.Ici x₀) x| ≤ C * qMix Λ x * x ^ (-β - (j : ℝ))) ∧
    (∀ (Λ : Measure ℝ), IsProbabilityMeasure Λ → ContDiffOn ℝ ∞ (fun y => ∫ t in Set.Ioi (0 : ℝ), H t y ∂Λ) (Set.Ici x₀)) := by
  have hH_unif : ∀ j : ℕ, ∃ M ≥ 0, ∀ y ∈ Set.Ioi x₂, ∀ t > 0, |iteratedDeriv j (fun z => H t z) y| ≤ M := by
    intro j; obtain ⟨C, hC, hbd⟩ := hH_bd j; refine ⟨C * x₂ ^ (-β - (j : ℝ)), by positivity, fun y hy t ht => ?_⟩
    have hpow : y ^ (-β - (j : ℝ)) ≤ x₂ ^ (-β - (j : ℝ)) := Real.rpow_le_rpow_of_nonpos hx₂_pos (Set.mem_Ioi.mp hy).le (by linarith)
    have hypos : 0 < y := lt_trans hx₂_pos hy
    calc |iteratedDeriv j (fun z => H t z) y| ≤ C * cohnWt t y * y ^ (-β - (j : ℝ)) := hbd t ht y hy
      _ ≤ C * 1 * y ^ (-β - (j : ℝ)) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (cohnWt_le_one ht hypos.le) hC) (Real.rpow_nonneg hypos.le _)
      _ ≤ C * 1 * x₂ ^ (-β - (j : ℝ)) := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring
  have hI_cd : ∀ (Λ : Measure ℝ) [IsProbabilityMeasure Λ], ContDiffOn ℝ ∞ (fun y => ∫ t in Set.Ioi (0 : ℝ), H t y ∂Λ) (Set.Ioi x₂) :=
    fun Λ _ => contDiffOn_infty.mpr fun n => parametric_integral_contDiffOn isOpen_Ioi n H hH_cd hH_unif
  have hsub : Set.Ici x₀ ⊆ Set.Ioi x₂ := fun _ hy => lt_of_lt_of_le hx₂_lt hy
  refine ⟨fun j => ?_, fun Λ _ => (hI_cd Λ).mono hsub⟩
  obtain ⟨C, hC, hbd⟩ := hH_bd j; refine ⟨C, hC, fun Λ _ x hx => ?_⟩; have hxpos : 0 < x := lt_trans hx₂_pos (hsub hx)
  rw [iteratedDerivWithin_Ici_eq_iteratedDeriv_of_contDiffOn_open j isOpen_Ioi hsub (hI_cd Λ) hx, parametric_integral_iteratedDeriv isOpen_Ioi j H hH_cd hH_unif x (hsub hx)]
  let μ : Measure ℝ := Λ.restrict (Set.Ioi (0 : ℝ))
  have hw_cont : ContinuousOn (fun t => cohnWt t x) (Set.Ioi 0) := continuousOn_const.div (continuousOn_const.add continuousOn_id) fun t ht => by linarith [Set.mem_Ioi.mp ht]
  have hw_int : Integrable (fun t => cohnWt t x) μ := (integrable_const (1 : ℝ)).mono' (hw_cont.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by rw [Real.norm_of_nonneg (cohnWt_nonneg ht.le hxpos.le)]; exact cohnWt_le_one ht hxpos.le)
  have hq_int : Integrable (fun t => 2 * cohnWt t x - cohnWt t x ^ 2) μ := (integrable_const (2 : ℝ)).mono'
    (((continuousOn_const.mul hw_cont).sub (hw_cont.pow 2)).aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
      have hle := cohnWt_le_two_sub_sq ht hxpos.le; rw [Real.norm_of_nonneg ((cohnWt_nonneg ht.le hxpos.le).trans hle.1)]; exact hle.2.trans (by linarith [cohnWt_le_one ht hxpos.le]))
  have hw_le_q : ∫ t, cohnWt t x ∂μ ≤ qMix Λ x := integral_mono_of_nonneg (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => cohnWt_nonneg ht.le hxpos.le)
    hq_int (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (cohnWt_le_two_sub_sq ht hxpos.le).1)
  have hnorm_le : |∫ t, iteratedDeriv j (fun z => H t z) x ∂μ| ≤ ∫ t, (C * x ^ (-β - (j : ℝ))) * cohnWt t x ∂μ := by
    rw [← Real.norm_eq_abs]; exact (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
      (hw_int.const_mul _) (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by simpa [Real.norm_eq_abs, mul_assoc, mul_comm, mul_left_comm] using hbd t ht x (hsub hx)))
  calc |∫ t, iteratedDeriv j (fun z => H t z) x ∂μ| ≤ (C * x ^ (-β - (j : ℝ))) * ∫ t, cohnWt t x ∂μ := hnorm_le.trans_eq (integral_const_mul _ _)
    _ ≤ (C * x ^ (-β - (j : ℝ))) * qMix Λ x := mul_le_mul_of_nonneg_left hw_le_q (by positivity)
    _ = C * qMix Λ x * x ^ (-β - (j : ℝ)) := by ring

/-- **Eq. `(CR.20)` differentiation**: `qMix Λ ∈ 𝒬₀` on `[x₀, ∞)` for any `x₀ > 0`, with
constants independent of the probability measure `Λ` on `(0, ∞)`. -/
theorem qMix_isWeightedSymbol {x₀ : ℝ} (hx₀ : 0 < x₀) :
    (∀ j : ℕ, ∃ C ≥ 0, ∀ (Λ : Measure ℝ), IsProbabilityMeasure Λ → Λ (Set.Iic 0) = 0 →
      ∀ x ≥ x₀, |iteratedDerivWithin j (qMix Λ) (Set.Ici x₀) x| ≤ C * qMix Λ x * x ^ (-0 - (j : ℝ))) ∧
    (∀ (Λ : Measure ℝ), IsProbabilityMeasure Λ → Λ (Set.Iic 0) = 0 → IsWeightedSymbolOn x₀ 0 (qMix Λ) (qMix Λ)) := by
  set x₂ : ℝ := x₀ / 2; have hx₂_pos : 0 < x₂ := half_pos hx₀; have hQ := isXTBound_two_sub_sq hx₂_pos
  have hQ_iter : ∀ j : ℕ, ∃ C ≥ 0, ∀ t > 0, ∀ x > x₂, |iteratedDeriv j (fun y => 2 * cohnWt t y - cohnWt t y ^ 2) x| ≤ C * cohnWt t x * x ^ (-0 - (j : ℝ)) := by
    intro j; choose C0 hC0 hbd0 using fun i => hQ.2 i 0; obtain ⟨C, hC, hiter⟩ := iteratedDeriv_bound_of_eulerDeriv j hC0
    refine ⟨C, hC, fun t ht x hx => ?_⟩
    simpa [eulerDerivXT, eulerDerivT, eulerDeriv] using hiter isOpen_Ioi (contDiffOn_sliceX hQ.1 ht)
      hx (lt_trans hx₂_pos hx) (cohnWt_nonneg ht.le (lt_trans hx₂_pos hx).le) fun i _ => hbd0 i t ht x hx
  obtain ⟨hbd, hcd⟩ := weighted_symbol_of_cr17_integrand hx₂_pos (half_lt_self hx₀) le_rfl hQ.1 hQ_iter
  refine ⟨fun j => let ⟨C, hC, h⟩ := hbd j; ⟨C, hC, fun Λ hΛ _ x hx => h Λ hΛ x hx⟩,
    fun Λ hΛ _ => ⟨hcd Λ hΛ, fun j => let ⟨C, hC, h⟩ := hbd j; ⟨C, hC, fun x hx => h Λ hΛ x hx⟩⟩⟩

private lemma integral_sub_q_div_pow {x₂ : ℝ} (hx₂_pos : 0 < x₂) {G : ℝ → ℝ → ℝ} {m : ℕ}
    (hQ_cd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => 2 * cohnWt p.1 p.2 - cohnWt p.1 p.2 ^ 2) (Set.Ioi 0 ×ˢ Set.Ioi x₂))
    (hdiff_cd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => G p.1 p.2 - (2 * cohnWt p.1 p.2 - cohnWt p.1 p.2 ^ 2) / p.2 ^ m) (Set.Ioi 0 ×ˢ Set.Ioi x₂))
    (hdiff_bd : ∃ C ≥ 0, ∀ t > 0, ∀ y > x₂, |G t y - (2 * cohnWt t y - cohnWt t y ^ 2) / y ^ m| ≤ C * cohnWt t y * y ^ (-(m : ℝ) - 1))
    (Λ : Measure ℝ) [IsProbabilityMeasure Λ] {y : ℝ} (hy2 : x₂ < y) :
    (∫ t in Set.Ioi (0 : ℝ), G t y ∂Λ) - qMix Λ y / y ^ m = ∫ t in Set.Ioi (0 : ℝ), (G t y - (2 * cohnWt t y - cohnWt t y ^ 2) / y ^ m) ∂Λ := by
  have hypos : 0 < y := lt_trans hx₂_pos hy2; let μ := Λ.restrict (Set.Ioi (0 : ℝ)); obtain ⟨C, _, hC⟩ := hdiff_bd
  have hq_int : Integrable (fun t => 2 * cohnWt t y - cohnWt t y ^ 2) μ := (integrable_const (2 : ℝ)).mono'
    ((contDiffOn_sliceT (f := fun s z => 2 * cohnWt s z - cohnWt s z ^ 2) hQ_cd hy2).continuousOn.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
      have hle := cohnWt_le_two_sub_sq ht hypos.le; rw [Real.norm_of_nonneg ((cohnWt_nonneg ht.le hypos.le).trans hle.1)]; exact hle.2.trans (by linarith [cohnWt_le_one ht hypos.le]))
  have hdiff_int : Integrable (fun t => G t y - (2 * cohnWt t y - cohnWt t y ^ 2) / y ^ m) μ := (integrable_const (C * y ^ (-(m : ℝ) - 1))).mono'
    ((contDiffOn_sliceT (f := fun s z => G s z - (2 * cohnWt s z - cohnWt s z ^ 2) / z ^ m) hdiff_cd hy2).continuousOn.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
      rw [Real.norm_eq_abs]; calc |G t y - (2 * cohnWt t y - cohnWt t y ^ 2) / y ^ m| ≤ C * cohnWt t y * y ^ (-(m : ℝ) - 1) := hC t ht y hy2
        _ ≤ C * 1 * y ^ (-(m : ℝ) - 1) := by gcongr; exact cohnWt_le_one ht hypos.le
        _ = _ := by ring)
  have hG_int : Integrable (fun t => G t y) μ := by
    have heq : (fun t => G t y) = (fun t => (G t y - (2 * cohnWt t y - cohnWt t y ^ 2) / y ^ m) + (2 * cohnWt t y - cohnWt t y ^ 2) / y ^ m) := funext fun _ => by ring
    rw [heq]; exact hdiff_int.add (hq_int.div_const _)
  dsimp [qMix]; rw [← integral_div, ← integral_sub hG_int (hq_int.div_const _)]

/-- **Theorem CR.4 Step 3, eq. `(CR.21)` (uniform constants)**: for any `x₀ > 2 max(|a₁|, |a|)`,
the mixture coefficients `AMix a Λ`, `BMix a Λ`, `CMix a Λ` satisfy `(CR.21)` with constants
independent of the probability measure `Λ` on `(0, ∞)`. -/
theorem cardinal_CR21_uniform {a : ℝ} (ha : airyAi' a = 0) (ha1 : airyZero 1 < a)
    (hBesselRatio : ∀ z > 0, cohnM z = -Real.sqrt z * besselR ((2 / 3 : ℝ) * z ^ (3 / 2 : ℝ)))
    {x₀ : ℝ} (_hx₀_pos : 0 < x₀) (hx₀_dom : 2 * max |airyZero 1| |a| < x₀) :
    (∀ j : ℕ, ∃ C_A C_B C_C : ℝ, 0 ≤ C_A ∧ 0 ≤ C_B ∧ 0 ≤ C_C ∧
      ∀ (Λ : Measure ℝ), IsProbabilityMeasure Λ → Λ (Set.Iic 0) = 0 → ∀ x ≥ x₀,
        |iteratedDerivWithin j (fun y => AMix a Λ y - qMix Λ y / y) (Set.Ici x₀) x| ≤ C_A * qMix Λ x * x ^ (-2 - (j : ℝ)) ∧
        |iteratedDerivWithin j (BMix a Λ) (Set.Ici x₀) x| ≤ C_B * qMix Λ x * x ^ (-3 - (j : ℝ)) ∧
        |iteratedDerivWithin j (fun y => CMix a Λ y - qMix Λ y / y ^ 2) (Set.Ici x₀) x| ≤ C_C * qMix Λ x * x ^ (-3 - (j : ℝ))) ∧
    (∀ (Λ : Measure ℝ), IsProbabilityMeasure Λ → Λ (Set.Iic 0) = 0 →
      ContDiffOn ℝ ∞ (fun y => AMix a Λ y - qMix Λ y / y) (Set.Ici x₀) ∧
      ContDiffOn ℝ ∞ (BMix a Λ) (Set.Ici x₀) ∧ ContDiffOn ℝ ∞ (fun y => CMix a Λ y - qMix Λ y / y ^ 2) (Set.Ici x₀)) := by
  set x₂ : ℝ := (x₀ + 2 * max |airyZero 1| |a|) / 2; have hx₂_lt : x₂ < x₀ := by dsimp [x₂]; linarith
  have hx₂_dom : 2 * max |airyZero 1| |a| < x₂ := by dsimp [x₂]; linarith
  have hx₂_pos : 0 < x₂ := lt_of_le_of_lt (by positivity) hx₂_dom
  have h17 := cardinal_CR17_gen_deriv_open ha ha1 hBesselRatio hx₂_dom
  obtain ⟨hA_w, hA_int_cd⟩ := weighted_symbol_of_cr17_integrand hx₂_pos hx₂_lt (by norm_num) h17.2.1 h17.2.2.2.2.2.1
  obtain ⟨hB_w, hB_int_cd⟩ := weighted_symbol_of_cr17_integrand hx₂_pos hx₂_lt (by norm_num) h17.2.2.1 h17.2.2.2.2.2.2.1
  obtain ⟨hC_w, hC_int_cd⟩ := weighted_symbol_of_cr17_integrand hx₂_pos hx₂_lt (by norm_num) h17.2.2.2.1 h17.2.2.2.2.2.2.2
  have h12 : (-1 : ℝ) - 1 = -2 := by norm_num
  have h23 : (-2 : ℝ) - 1 = -3 := by norm_num
  have hsub_eq_A : ∀ (Λ : Measure ℝ) [IsProbabilityMeasure Λ], Set.EqOn (fun y => AMix a Λ y - qMix Λ y / y)
      (fun y => ∫ t in Set.Ioi (0 : ℝ), (cohnAtGen a t y - (2 * cohnWt t y - cohnWt t y ^ 2) / y) ∂Λ) (Set.Ici x₀) := by
    intro Λ _ y hy; obtain ⟨CA0, hCA0, hCA0_bd⟩ := h17.2.2.2.2.2.1 0; dsimp only [AMix]
    simpa only [pow_one] using integral_sub_q_div_pow hx₂_pos (m := 1) h17.1 (by simpa only [pow_one] using h17.2.1)
      ⟨CA0, hCA0, fun t ht z hz => by simpa only [iteratedDeriv_zero, Nat.cast_zero, sub_zero, Nat.cast_one, pow_one, h12] using hCA0_bd t ht z hz⟩
      Λ (lt_of_lt_of_le hx₂_lt hy)
  have hsub_eq_C : ∀ (Λ : Measure ℝ) [IsProbabilityMeasure Λ], Set.EqOn (fun y => CMix a Λ y - qMix Λ y / y ^ 2)
      (fun y => ∫ t in Set.Ioi (0 : ℝ), (cohnCtGen a t y - (2 * cohnWt t y - cohnWt t y ^ 2) / y ^ 2) ∂Λ) (Set.Ici x₀) := by
    intro Λ _ y hy; obtain ⟨CC0, hCC0, hCC0_bd⟩ := h17.2.2.2.2.2.2.2 0
    exact integral_sub_q_div_pow hx₂_pos (m := 2) h17.1 h17.2.2.2.1
      ⟨CC0, hCC0, fun t ht z hz => by simpa only [iteratedDeriv_zero, Nat.cast_zero, sub_zero, Nat.cast_ofNat, h23] using hCC0_bd t ht z hz⟩
      Λ (lt_of_lt_of_le hx₂_lt hy)
  refine ⟨fun j => ?_, fun Λ hΛ _ => ⟨(hA_int_cd Λ hΛ).congr fun y hy => hsub_eq_A Λ hy, hB_int_cd Λ hΛ, (hC_int_cd Λ hΛ).congr fun y hy => hsub_eq_C Λ hy⟩⟩
  obtain ⟨CA, hCA, hAbd⟩ := hA_w j; obtain ⟨CB, hCB, hBbd⟩ := hB_w j; obtain ⟨CC, hCC, hCbd⟩ := hC_w j
  exact ⟨CA, CB, CC, hCA, hCB, hCC, fun Λ hΛ _ x hx =>
    ⟨by rw [iteratedDerivWithin_congr (hsub_eq_A Λ) hx]; exact hAbd Λ hΛ x hx, hBbd Λ hΛ x hx,
      by rw [iteratedDerivWithin_congr (hsub_eq_C Λ) hx]; exact hCbd Λ hΛ x hx⟩⟩

/-- **Theorem CR.4 Step 3, eq. `(CR.21)` (packaged `CardinalResolventCoeffs`)**:
every probability measure `Λ` on `(0, ∞)` produces `CardinalResolventCoeffs x₀ (qMix Λ) (AMix a Λ) (BMix a Λ) (CMix a Λ)`. -/
theorem cardinal_CR21_of_measure {a : ℝ} (ha : airyAi' a = 0) (ha1 : airyZero 1 < a)
    (hBesselRatio : ∀ z > 0, cohnM z = -Real.sqrt z * besselR ((2 / 3 : ℝ) * z ^ (3 / 2 : ℝ)))
    {x₀ : ℝ} (hx₀ : 1 ≤ x₀) (hx₀_dom : 2 * max |airyZero 1| |a| < x₀)
    (Λ : Measure ℝ) [IsProbabilityMeasure Λ] (hΛ0 : Λ (Set.Iic 0) = 0) :
    CardinalResolventCoeffs x₀ (qMix Λ) (AMix a Λ) (BMix a Λ) (CMix a Λ) := by
  have hx₀_pos : 0 < x₀ := by linarith
  have h21 := cardinal_CR21_uniform ha ha1 hBesselRatio hx₀_pos hx₀_dom
  obtain ⟨hA_cd, hB_cd, hC_cd⟩ := h21.2 Λ inferInstance hΛ0
  refine ⟨hx₀, (qMix_isWeightedSymbol hx₀_pos).2 Λ inferInstance hΛ0,
    ⟨hA_cd, fun j => let ⟨CA, _, _, hCA, _, _, hbd⟩ := h21.1 j; ⟨CA, hCA, fun x hx => (hbd Λ inferInstance hΛ0 x hx).1⟩⟩,
    ⟨hB_cd, fun j => let ⟨_, CB, _, _, hCB, _, hbd⟩ := h21.1 j; ⟨CB, hCB, fun x hx => (hbd Λ inferInstance hΛ0 x hx).2.1⟩⟩,
    ⟨hC_cd, fun j => let ⟨_, _, CC, _, _, hCC, hbd⟩ := h21.1 j; ⟨CC, hCC, fun x hx => (hbd Λ inferInstance hΛ0 x hx).2.2⟩⟩⟩

/-- Non-vacuity of `cardinal_CR21_of_measure` instantiated at the largest zero `a = a₁'` of `Ai'`
and `Λ = Measure.dirac 1`. -/
theorem cardinal_CR21_dirac_nonvacuous
    (hBesselRatio : ∀ z > 0, cohnM z = -Real.sqrt z * besselR ((2 / 3 : ℝ) * z ^ (3 / 2 : ℝ))) :
    ∃ a x₀ : ℝ, airyZero 1 < a ∧ airyAi' a = 0 ∧ 1 ≤ x₀ ∧ 2 * max |airyZero 1| |a| < x₀ ∧
      CardinalResolventCoeffs x₀ (qMix (Measure.dirac 1)) (AMix a (Measure.dirac 1)) (BMix a (Measure.dirac 1)) (CMix a (Measure.dirac 1)) := by
  obtain ⟨a, ha1, _, ha, _⟩ := airyDeriv_largest_zero
  let x₀ : ℝ := max 1 (2 * max |airyZero 1| |a| + 1)
  have hx₀_dom : 2 * max |airyZero 1| |a| < x₀ := by have : 2 * max |airyZero 1| |a| + 1 ≤ x₀ := le_max_right _ _; linarith
  exact ⟨a, x₀, ha1, ha, le_max_left _ _, hx₀_dom,
    cardinal_CR21_of_measure ha ha1 hBesselRatio (le_max_left _ _) hx₀_dom (Measure.dirac 1) (by simp [Measure.dirac_apply'])⟩

/-! ### Step 4: End-to-end Theorem CR.4 / `(CR.14)` symbol decomposition -/

/-- **Theorem CR.4 (end-to-end `(CR.14)`):** Under the `W.1` Bessel ratio (`hBesselRatio`) and
`W.2` Nicholson (`hNicholson`) identities, for any `x₀ ≥ 1` with `x₀ > 2 max(|a₁|, |a|)` and any
probability measure `Λ` on `(0, ∞)`, there exist `D₀, D₁, D₂ ∈ 𝒬_{5/2}([x₀, ∞); q_Λ)` such that
`A_Λ(x) Ai(-x)² + B_Λ(x) Ai(-x) Ai'(-x) + C_Λ(x) Ai'(-x)² = q_Λ(x) / (π x^{3/2}) + D₀(x) + D₁(x) cos(2ϑ(x)) + D₂(x) sin(2ϑ(x))`. -/
theorem theorem_CR4_symbol_decomp
    (hBesselRatio : ∀ z > 0, cohnM z = -Real.sqrt z * besselR ((2 / 3 : ℝ) * z ^ (3 / 2 : ℝ)))
    (hNicholson : ∀ x > 0, airyAi (-x) ^ 2 + airyBi (-x) ^ 2 = nicholsonIntegral x)
    {a : ℝ} (ha : airyAi' a = 0) (ha1 : airyZero 1 < a)
    {x₀ : ℝ} (hx₀ : 1 ≤ x₀) (hx₀_dom : 2 * max |airyZero 1| |a| < x₀)
    (Λ : Measure ℝ) [IsProbabilityMeasure Λ] (hΛ0 : Λ (Set.Iic 0) = 0) :
    ∃ D₀ D₁ D₂ : ℝ → ℝ,
      IsWeightedSymbolOn x₀ (5 / 2) (qMix Λ) D₀ ∧ IsWeightedSymbolOn x₀ (5 / 2) (qMix Λ) D₁ ∧ IsWeightedSymbolOn x₀ (5 / 2) (qMix Λ) D₂ ∧
      ∀ x ≥ x₀,
        AMix a Λ x * airyAi (-x) ^ 2 + BMix a Λ x * airyAi (-x) * airyAi' (-x) + CMix a Λ x * airyAi' (-x) ^ 2 =
          qMix Λ x / (π * x ^ (3 / 2 : ℝ)) + D₀ x + D₁ x * Real.cos (2 * airyTheta0 x) + D₂ x * Real.sin (2 * airyTheta0 x) :=
  cardinal_symbol_decomp hNicholson (cardinal_CR21_of_measure ha ha1 hBesselRatio hx₀ hx₀_dom Λ hΛ0)

/-! ### Axiom verification -/

/-- info: 'FormalResearch.CohnElkies.cardinal_CR17' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinal_CR17

/-- info: 'FormalResearch.CohnElkies.qMix_isWeightedSymbol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.qMix_isWeightedSymbol

/-- info: 'FormalResearch.CohnElkies.cardinal_CR21_of_measure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinal_CR21_of_measure

/-- info: 'FormalResearch.CohnElkies.cardinal_CR21_dirac_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinal_CR21_dirac_nonvacuous

/-- info: 'FormalResearch.CohnElkies.theorem_CR4_symbol_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.theorem_CR4_symbol_decomp

end FormalResearch.CohnElkies
