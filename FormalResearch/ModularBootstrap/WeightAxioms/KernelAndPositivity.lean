module

public import FormalResearch.ModularBootstrap.WeightAxioms.BesselGeneral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Fixed-Weight Kernels, Positivity, Upper Bounds, and Threshold Window (Lemma 4(b), (d), (e))

Formalizes the real-variable and entire-kernel parts of Lemma 4 (`n1:L4`) in
`CFT/modular_bootstrap/paper/n1_super_virasoro.tex`:

* `kernelKC`, `cardyVC`: entire extensions of `Crossing.kernelK` and `FixedWeightProblem.cardyV`
  to `ℂ` (agreeing with `KalphaC` and `V_C` at `virasoroProblem`), together with the strip kernel
  domination `norm_kernelKC_strip_le` (`|K_α(t)| ≤ K_{c'/12}(t)` for `α = -c' b^2 / 3`,
  `|Im b| ≤ 1/2`).
* **Lemma 4(b)**: `cardyV_le_kernelK` (`V ≤ K_a` for `a ≥ S`), `cardyV_ge_peano_kernel` /
  `cardyV_ge_besselI_shift` (Peano lower bound `V ≥ (∏ μ_l) ∂_α^m K_{a - S}`), `cardyV_at_zero`,
  and `cardyV_log_convex` (midpoint and full convexity of `s ↦ log V(e^s)`).
* **Lemma 4(d)**: `cardyV_le_pow_mul_kernelK` (`V ≤ C t^m K_a`) and `kernelK_le_pow_mul_exp`
  (`K_a(t) ≤ (t/a)^{(w-1)/2} e^{4π√(a t)}`).
* **Lemma 4(e)**: `abs_le_radial_l1` (`sup |g| ≤ (2π)^w / (w-1)! ∫ |g| t^{w-1} dt`),
  `testClass_integral_le_cardyNorm`, and `testClass_sup_le_cardyNorm` (`‖g‖_∞ ≤ C₁ M[g]` with
  `C₁` depending only on `prob`, independent of `a ≥ S`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real Nat FourierTransform

namespace FormalResearch.ModularBootstrap.WeightAxioms

open Crossing Bessel

/-! ### Section 1: Entire extensions `kernelKC`, `cardyVC` and strip kernel domination -/

/-- Entire extension of `Crossing.kernelK w α t` to `α, t : ℂ`:
`K_α^{(w)}(t) = (2π t)^{w-1} S_{w-1}(4π^2 α t)`. -/
noncomputable def kernelKC (w : ℕ) (α t : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * t) ^ (w - 1) * besselSC (w - 1) (4 * (Real.pi : ℂ) ^ 2 * α * t)

/-- Entire extension of `prob.cardyV a t` to `t : ℂ`. -/
noncomputable def cardyVC (prob : FixedWeightProblem) (a : ℝ) (t : ℂ) : ℂ :=
  ∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card * kernelKC prob.w ((a - prob.shiftSum s : ℝ) : ℂ) t

lemma kernelKC_entire_t (w : ℕ) (α : ℂ) : Differentiable ℂ (kernelKC w α) := by
  unfold kernelKC
  have h1 : Differentiable ℂ (fun t : ℂ => (2 * (Real.pi : ℂ) * t) ^ (w - 1)) :=
    (differentiable_const _ |>.mul differentiable_id).pow (w - 1)
  have h2 : Differentiable ℂ (fun t : ℂ => besselSC (w - 1) (4 * (Real.pi : ℂ) ^ 2 * α * t)) :=
    (besselSC_entire (w - 1)).comp (differentiable_const _ |>.mul differentiable_id)
  exact h1.mul h2

lemma kernelKC_entire_alpha (w : ℕ) (t : ℂ) : Differentiable ℂ (fun α : ℂ => kernelKC w α t) := by
  unfold kernelKC
  have h2 : Differentiable ℂ (fun α : ℂ => besselSC (w - 1) (4 * (Real.pi : ℂ) ^ 2 * α * t)) :=
    (besselSC_entire (w - 1)).comp ((differentiable_const _ |>.mul differentiable_id).mul_const t)
  exact differentiable_const _ |>.mul h2

lemma cardyVC_entire (prob : FixedWeightProblem) (a : ℝ) : Differentiable ℂ (cardyVC prob a) := by
  unfold cardyVC
  refine Differentiable.fun_sum fun s _ => ?_
  exact (kernelKC_entire_t prob.w ((a - prob.shiftSum s : ℝ) : ℂ)).const_mul _

lemma kernelKC_ofReal (w : ℕ) (hw : 1 ≤ w) (α t : ℝ) :
    kernelKC w (α : ℂ) (t : ℂ) = (kernelK w α t : ℂ) := by
  unfold kernelKC kernelK
  rw [show 4 * (Real.pi : ℂ) ^ 2 * (α : ℂ) * (t : ℂ) = ((4 * Real.pi ^ 2 * α * t : ℝ) : ℂ) by
    push_cast; ring, besselSC_ofReal]
  have hs_eq : besselS (w - 1) (4 * Real.pi ^ 2 * α * t) = ∑' k : ℕ, kernelKTerm w α t k := by
    unfold besselS besselTerm kernelKTerm
    refine tsum_congr fun k => ?_
    have hk : k + (w - 1) = k + w - 1 := by omega
    rw [hk]
  rw [hs_eq]
  push_cast
  rfl

lemma cardyVC_ofReal (prob : FixedWeightProblem) (a t : ℝ) :
    cardyVC prob a (t : ℂ) = (prob.cardyV a t : ℂ) := by
  unfold cardyVC FixedWeightProblem.cardyV
  simp_rw [kernelKC_ofReal prob.w prob.hw]
  push_cast
  rfl

lemma kernelKC_one_eq (α t : ℂ) : kernelKC 1 α t = KalphaC α t := by
  unfold kernelKC KalphaC
  simp [besselSC]

lemma cardyVC_virasoro_eq (c' : ℝ) (t : ℂ) :
    cardyVC virasoroProblem (c' / 12) t = V_C (c' : ℂ) t := by
  unfold cardyVC V_C FixedWeightProblem.shiftSum virasoroProblem
  have huniv : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have h01 : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
  have hs01 : ∑ l ∈ ({0, 1} : Finset (Fin 2)), (![1, 1] : Fin 2 → ℝ) l = 2 := by
    rw [Finset.sum_pair (by decide)]; norm_num
  simp only [Finset.card_empty, pow_zero, one_mul, Finset.sum_empty, sub_zero,
    Finset.card_singleton, pow_one, neg_mul, Finset.sum_singleton, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, kernelKC_one_eq]
  rw [h01, hs01]
  push_cast
  ring

/-- Strip kernel domination (`n1_super_virasoro.tex`, Lemma 4(a)):
for `w ≥ 1`, `c' > 0`, `t ≥ 0`, and `|Im b| ≤ 1/2`,
`‖K_{-c' b² / 3}^{(w)}(t)‖ ≤ K_{c'/12}^{(w)}(t)`. -/
theorem norm_kernelKC_strip_le (w : ℕ) (hw : 1 ≤ w) {c' t : ℝ} (hc : 0 < c') (ht : 0 ≤ t)
    {b : ℂ} (hb : |b.im| ≤ 1 / 2) :
    ‖kernelKC w (-(c' : ℂ) * b ^ 2 / 3) (t : ℂ)‖ ≤ kernelK w (c' / 12) t := by
  unfold kernelKC
  let z : ℂ := 4 * (Real.pi : ℂ) * Complex.I * b * (Real.sqrt (c' * t / 3) : ℝ)
  have hz_sq : 4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * b ^ 2 / 3) * (t : ℂ) = z ^ 2 / 4 := by
    dsimp [z]
    have hsq : ((Real.sqrt (c' * t / 3) : ℝ) : ℂ) ^ 2 = ((c' * t / 3 : ℝ) : ℂ) := by
      exact_mod_cast Real.sq_sqrt (by positivity)
    calc 4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * b ^ 2 / 3) * (t : ℂ)
        = (4 * (Real.pi : ℂ) * Complex.I * b) ^ 2 * ((c' * t / 3 : ℝ) : ℂ) / 4 := by
          rw [mul_pow, mul_pow, mul_pow, Complex.I_sq]; push_cast; ring
      _ = (4 * (Real.pi : ℂ) * Complex.I * b) ^ 2 * ((Real.sqrt (c' * t / 3) : ℝ) : ℂ) ^ 2 / 4 := by
          rw [hsq]
      _ = (4 * (Real.pi : ℂ) * Complex.I * b * (Real.sqrt (c' * t / 3) : ℝ)) ^ 2 / 4 := by ring
  rw [hz_sq, norm_mul, norm_pow,
    show 2 * (Real.pi : ℂ) * (t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * t)]
  have hz_re : z.re = -(4 * Real.pi * b.im * Real.sqrt (c' * t / 3)) := by
    dsimp [z]
    simp [Complex.mul_re, Complex.mul_im]
  have hre_sq : z.re ^ 2 / 4 ≤ 4 * Real.pi ^ 2 * (c' / 12) * t := by
    rw [hz_re]
    have hsq : Real.sqrt (c' * t / 3) ^ 2 = c' * t / 3 := Real.sq_sqrt (by positivity)
    have hbim : b.im ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      rw [← sq_abs b.im]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    calc (-(4 * Real.pi * b.im * Real.sqrt (c' * t / 3))) ^ 2 / 4
        = 4 * Real.pi ^ 2 * b.im ^ 2 * (Real.sqrt (c' * t / 3) ^ 2) := by ring
      _ = 4 * Real.pi ^ 2 * (c' * t / 3) * b.im ^ 2 := by rw [hsq]; ring
      _ ≤ 4 * Real.pi ^ 2 * (c' * t / 3) * (1 / 2 : ℝ) ^ 2 := by
          exact mul_le_mul_of_nonneg_left hbim (by positivity)
      _ = 4 * Real.pi ^ 2 * (c' / 12) * t := by ring
  have hS_le : ‖besselSC (w - 1) (z ^ 2 / 4)‖ ≤ besselS (w - 1) (4 * Real.pi ^ 2 * (c' / 12) * t) :=
    (norm_besselSC_sq_div_four_le (w - 1) z).trans (besselS_mono (w - 1) (by positivity) hre_sq)
  have hK_eq : kernelK w (c' / 12) t =
      (2 * Real.pi * t) ^ (w - 1) * besselS (w - 1) (4 * Real.pi ^ 2 * (c' / 12) * t) := by
    unfold kernelK besselS besselTerm kernelKTerm
    congr 1
    refine tsum_congr fun k => ?_
    have hk : k + w - 1 = k + (w - 1) := by omega
    rw [hk]
  rw [hK_eq]
  exact mul_le_mul_of_nonneg_left hS_le (by positivity)

/-! ### Section 2: Lemma 4(b) & (d) — `V ≤ K_a`, Peano bounds, `V ≤ C t^m K_a`, and log-convexity -/

lemma listDiff_pow_le_pow (μs : List ℝ) (hμ : ∀ μ ∈ μs, 0 < μ) (k : ℕ) {a : ℝ}
    (ha : μs.sum ≤ a) :
    listDiff μs (fun α => α ^ k) a ≤ a ^ k := by
  induction μs generalizing a with
  | nil => simp [listDiff]
  | cons μ μs ih =>
    simp only [List.sum_cons, List.mem_cons, forall_eq_or_imp] at ha hμ
    rw [listDiff]
    have hnn : 0 ≤ listDiff μs (fun α => α ^ k) (a - μ) :=
      listDiff_pow_nonneg μs hμ.2 k (by linarith)
    have hle : listDiff μs (fun α => α ^ k) a ≤ a ^ k := ih hμ.2 (by linarith)
    linarith

lemma summable_cardyV_tsum (prob : FixedWeightProblem) {a : ℝ} (ha : prob.totalShift ≤ a)
    {t : ℝ} (ht : 0 ≤ t) :
    Summable fun k : ℕ =>
      ((4 * Real.pi ^ 2 * t) ^ k / ((k ! : ℝ) * ((k + prob.w - 1)! : ℝ))) *
        listDiff (List.ofFn prob.μ) (fun α => α ^ k) a := by
  have hsum_eq : (List.ofFn prob.μ).sum = prob.totalShift := by
    unfold FixedWeightProblem.totalShift; rw [List.sum_ofFn]
  have hμ_list : ∀ ν ∈ List.ofFn prob.μ, 0 < ν := by
    intro ν hν; rw [List.mem_ofFn] at hν; rcases hν with ⟨l, rfl⟩; exact prob.hμ l
  have hK_summ : Summable fun k : ℕ =>
      ((4 * Real.pi ^ 2 * t) ^ k / ((k ! : ℝ) * ((k + prob.w - 1)! : ℝ))) * a ^ k := by
    refine (summable_kernelKTerm prob.w a t).congr fun k => ?_
    unfold kernelKTerm
    rw [show 4 * Real.pi ^ 2 * a * t = (4 * Real.pi ^ 2 * t) * a by ring, mul_pow]
    ring
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hK_summ
  · exact mul_nonneg (div_nonneg (pow_nonneg (by positivity) k) (by positivity))
      (listDiff_pow_nonneg _ hμ_list k (hsum_eq.symm ▸ ha))
  · exact mul_le_mul_of_nonneg_left
      (listDiff_pow_le_pow _ hμ_list k (hsum_eq.symm ▸ ha))
      (div_nonneg (pow_nonneg (by positivity) k) (by positivity))

/-- **Lemma 4(b), upper comparison (`n1:L4`)**: for `a ≥ ∑ μ_l` (`c̃ ≥ 12 S`) and `t ≥ 0`,
`V(t) ≤ K_a^{(w)}(t)`. -/
theorem cardyV_le_kernelK (prob : FixedWeightProblem) {a : ℝ} (ha : prob.totalShift ≤ a)
    {t : ℝ} (ht : 0 ≤ t) :
    prob.cardyV a t ≤ kernelK prob.w a t := by
  have hsum_eq : (List.ofFn prob.μ).sum = prob.totalShift := by
    unfold FixedWeightProblem.totalShift; rw [List.sum_ofFn]
  have hμ_list : ∀ ν ∈ List.ofFn prob.μ, 0 < ν := by
    intro ν hν; rw [List.mem_ofFn] at hν; rcases hν with ⟨l, rfl⟩; exact prob.hμ l
  have hK_summ : Summable fun k : ℕ =>
      ((4 * Real.pi ^ 2 * t) ^ k / ((k ! : ℝ) * ((k + prob.w - 1)! : ℝ))) * a ^ k := by
    refine (summable_kernelKTerm prob.w a t).congr fun k => ?_
    unfold kernelKTerm
    rw [show 4 * Real.pi ^ 2 * a * t = (4 * Real.pi ^ 2 * t) * a by ring, mul_pow]
    ring
  have hK_eq : kernelK prob.w a t = (2 * Real.pi * t) ^ (prob.w - 1) *
      ∑' k : ℕ, ((4 * Real.pi ^ 2 * t) ^ k / ((k ! : ℝ) * ((k + prob.w - 1)! : ℝ))) * a ^ k := by
    unfold kernelK kernelKTerm
    congr 1
    refine tsum_congr fun k => ?_
    rw [show 4 * Real.pi ^ 2 * a * t = (4 * Real.pi ^ 2 * t) * a by ring, mul_pow]
    ring
  rw [prob.cardyV_eq_tsum, hK_eq]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by positivity) _)
  refine (summable_cardyV_tsum prob ha ht).tsum_le_tsum (fun k => ?_) hK_summ
  exact mul_le_mul_of_nonneg_left
    (listDiff_pow_le_pow _ hμ_list k (hsum_eq.symm ▸ ha))
    (div_nonneg (pow_nonneg (by positivity) k) (by positivity))

/-- Peano lower bound on iterated differences of `α ↦ α^k` (`k ≥ μs.length`). -/
lemma listDiff_pow_ge_prod (μs : List ℝ) (hμ : ∀ μ ∈ μs, 0 < μ) :
    ∀ (k : ℕ) (_hk : μs.length ≤ k) (a : ℝ) (_ha : μs.sum ≤ a),
      μs.prod * ((k ! : ℝ) / ((k - μs.length)! : ℝ)) * (a - μs.sum) ^ (k - μs.length) ≤
        listDiff μs (fun α => α ^ k) a := by
  induction μs with
  | nil =>
    intro k _ a ha
    simp only [List.length_nil, List.prod_nil, one_mul, Nat.sub_zero, List.sum_nil, sub_zero,
      listDiff]
    have hk_ne : (k ! : ℝ) ≠ 0 := by positivity
    rw [div_self hk_ne, one_mul]
  | cons μ μs ih =>
    intro k hk a ha
    simp only [List.length_cons, List.sum_cons, List.mem_cons, forall_eq_or_imp] at hk ha hμ
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk' : μs.length ≤ k' := by omega
    rw [listDiff_eq_integral μ μs (fun x => hasDerivAt_pow (k' + 1) x) (by fun_prop) a]
    have hcont : Continuous fun u : ℝ =>
        listDiff μs (fun x => ((k' + 1 : ℕ) : ℝ) * x ^ (k' + 1 - 1)) (a - u) :=
      (continuous_listDiff μs (by fun_prop)).comp (continuous_const.sub continuous_id)
    have hconst : ∫ _u in (0 : ℝ)..μ,
        μs.prod * (((k' + 1 : ℕ)! : ℝ) / ((k' - μs.length)! : ℝ)) *
          (a - (μ + μs.sum)) ^ (k' - μs.length) =
        (μ :: μs).prod * (((k' + 1)! : ℝ) / ((k' + 1 - (μs.length + 1))! : ℝ)) *
          (a - (μ + μs.sum)) ^ (k' + 1 - (μs.length + 1)) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, List.prod_cons,
        show k' + 1 - (μs.length + 1) = k' - μs.length by omega]
      ring
    rw [List.length_cons, List.sum_cons, ← hconst]
    refine intervalIntegral.integral_mono_on hμ.1.le intervalIntegrable_const
      (hcont.intervalIntegrable 0 μ) fun u hu => ?_
    have hfn : (fun x : ℝ => ((k' + 1 : ℕ) : ℝ) * x ^ (k' + 1 - 1)) =
        fun x => ((k' + 1 : ℕ) : ℝ) * (fun y => y ^ k') x := by
      ext x; simp
    rw [hfn, listDiff_const_mul]
    have hau : μs.sum ≤ a - u := by linarith [hu.2]
    have hih := ih hμ.2 k' hk' (a - u) hau
    have hpow_le : (a - (μ + μs.sum)) ^ (k' - μs.length) ≤ (a - u - μs.sum) ^ (k' - μs.length) :=
      pow_le_pow_left₀ (by linarith) (by linarith [hu.2]) _
    have hprod_nn : 0 ≤ μs.prod := List.prod_nonneg fun x hx => (hμ.2 x hx).le
    have hmul_ih := mul_le_mul_of_nonneg_left hih (by positivity : 0 ≤ ((k' + 1 : ℕ) : ℝ))
    have hfac : ((k' + 1 : ℕ) : ℝ) * (μs.prod * ((k' ! : ℝ) / ((k' - μs.length)! : ℝ)) *
          (a - u - μs.sum) ^ (k' - μs.length)) =
        μs.prod * (((k' + 1)! : ℝ) / ((k' - μs.length)! : ℝ)) *
          (a - u - μs.sum) ^ (k' - μs.length) := by
      rw [Nat.factorial_succ k', Nat.cast_mul]; ring
    calc μs.prod * (((k' + 1)! : ℝ) / ((k' - μs.length)! : ℝ)) *
          (a - (μ + μs.sum)) ^ (k' - μs.length)
        ≤ μs.prod * (((k' + 1)! : ℝ) / ((k' - μs.length)! : ℝ)) *
            (a - u - μs.sum) ^ (k' - μs.length) := by
          gcongr
      _ = ((k' + 1 : ℕ) : ℝ) * (μs.prod * ((k' ! : ℝ) / ((k' - μs.length)! : ℝ)) *
            (a - u - μs.sum) ^ (k' - μs.length)) := hfac.symm
      _ ≤ ((k' + 1 : ℕ) : ℝ) * listDiff μs (fun y => y ^ k') (a - u) := hmul_ih

/-- Peano upper bound on iterated differences of `α ↦ α^k` (`k ≥ μs.length`). -/
lemma listDiff_pow_le_prod (μs : List ℝ) (hμ : ∀ μ ∈ μs, 0 < μ) :
    ∀ (k : ℕ) (_hk : μs.length ≤ k) (a : ℝ) (_ha : μs.sum ≤ a),
      listDiff μs (fun α => α ^ k) a ≤
        μs.prod * ((k ! : ℝ) / ((k - μs.length)! : ℝ)) * a ^ (k - μs.length) := by
  induction μs with
  | nil =>
    intro k _ a _
    simp only [List.length_nil, List.prod_nil, one_mul, tsub_zero, listDiff]
    have hk_ne : (k ! : ℝ) ≠ 0 := by positivity
    rw [div_self hk_ne, one_mul]
  | cons μ μs ih =>
    intro k hk a ha
    simp only [List.length_cons, List.sum_cons, List.mem_cons, forall_eq_or_imp] at hk ha hμ
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk' : μs.length ≤ k' := by omega
    rw [listDiff_eq_integral μ μs (fun x => hasDerivAt_pow (k' + 1) x) (by fun_prop) a]
    have hcont : Continuous fun u : ℝ =>
        listDiff μs (fun x => ((k' + 1 : ℕ) : ℝ) * x ^ (k' + 1 - 1)) (a - u) :=
      (continuous_listDiff μs (by fun_prop)).comp (continuous_const.sub continuous_id)
    have hconst : ∫ _u in (0 : ℝ)..μ,
        μs.prod * (((k' + 1 : ℕ)! : ℝ) / ((k' - μs.length)! : ℝ)) * a ^ (k' - μs.length) =
        (μ :: μs).prod * (((k' + 1)! : ℝ) / ((k' + 1 - (μs.length + 1))! : ℝ)) *
          a ^ (k' + 1 - (μs.length + 1)) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, List.prod_cons,
        show k' + 1 - (μs.length + 1) = k' - μs.length by omega]
      ring
    rw [List.length_cons, ← hconst]
    refine intervalIntegral.integral_mono_on hμ.1.le (hcont.intervalIntegrable 0 μ)
      intervalIntegrable_const fun u hu => ?_
    have hfn : (fun x : ℝ => ((k' + 1 : ℕ) : ℝ) * x ^ (k' + 1 - 1)) =
        fun x => ((k' + 1 : ℕ) : ℝ) * (fun y => y ^ k') x := by
      ext x; simp
    rw [hfn, listDiff_const_mul]
    have hau : μs.sum ≤ a - u := by linarith [hu.2]
    have hau_nn : 0 ≤ a - u := by
      have : 0 ≤ μs.sum := List.sum_nonneg fun x hx => (hμ.2 x hx).le
      linarith
    have hih := ih hμ.2 k' hk' (a - u) hau
    have hpow_le : (a - u) ^ (k' - μs.length) ≤ a ^ (k' - μs.length) :=
      pow_le_pow_left₀ hau_nn (by linarith [hu.1]) _
    have hprod_nn : 0 ≤ μs.prod := List.prod_nonneg fun x hx => (hμ.2 x hx).le
    have hmul_ih := mul_le_mul_of_nonneg_left hih (by positivity : 0 ≤ ((k' + 1 : ℕ) : ℝ))
    have hfac : ((k' + 1 : ℕ) : ℝ) * (μs.prod * ((k' ! : ℝ) / ((k' - μs.length)! : ℝ)) *
          (a - u) ^ (k' - μs.length)) =
        μs.prod * (((k' + 1)! : ℝ) / ((k' - μs.length)! : ℝ)) * (a - u) ^ (k' - μs.length) := by
      rw [Nat.factorial_succ k', Nat.cast_mul]; ring
    calc ((k' + 1 : ℕ) : ℝ) * listDiff μs (fun y => y ^ k') (a - u)
        ≤ ((k' + 1 : ℕ) : ℝ) * (μs.prod * ((k' ! : ℝ) / ((k' - μs.length)! : ℝ)) *
            (a - u) ^ (k' - μs.length)) := hmul_ih
      _ = μs.prod * (((k' + 1)! : ℝ) / ((k' - μs.length)! : ℝ)) *
            (a - u) ^ (k' - μs.length) := hfac
      _ ≤ μs.prod * (((k' + 1)! : ℝ) / ((k' - μs.length)! : ℝ)) * a ^ (k' - μs.length) := by
          gcongr

/-- **Lemma 4(b)/(c) Peano lower bound**: for `a ≥ S` and `t ≥ 0`,
`V(t) ≥ (∏ μ_l) (4π² t)^m (2π t)^{w - 1} S_{w - 1 + m}(4π² (a - S) t)`. -/
theorem cardyV_ge_peano_kernel (prob : FixedWeightProblem) {a : ℝ} (ha : prob.totalShift ≤ a)
    {t : ℝ} (ht : 0 ≤ t) :
    (∏ l : Fin prob.m, prob.μ l) * (4 * Real.pi ^ 2 * t) ^ prob.m *
        (2 * Real.pi * t) ^ (prob.w - 1) *
        besselS (prob.w - 1 + prob.m) (4 * Real.pi ^ 2 * (a - prob.totalShift) * t) ≤
      prob.cardyV a t := by
  have hw := prob.hw
  have hsum_eq : (List.ofFn prob.μ).sum = prob.totalShift := by
    unfold FixedWeightProblem.totalShift; rw [List.sum_ofFn]
  have hprod_eq : (List.ofFn prob.μ).prod = ∏ l : Fin prob.m, prob.μ l := by
    rw [List.prod_ofFn]
  have hμ_list : ∀ ν ∈ List.ofFn prob.μ, 0 < ν := by
    intro ν hν; rw [List.mem_ofFn] at hν; rcases hν with ⟨l, rfl⟩; exact prob.hμ l
  have ha_sub_nn : 0 ≤ a - prob.totalShift := sub_nonneg.mpr ha
  have hS_summ : Summable fun j : ℕ =>
      (∏ l : Fin prob.m, prob.μ l) * (4 * Real.pi ^ 2 * t) ^ prob.m *
        besselTerm (prob.w - 1 + prob.m) (4 * Real.pi ^ 2 * (a - prob.totalShift) * t) j :=
    (summable_besselTerm (prob.w - 1 + prob.m) (by positivity)).mul_left _
  have hV_summ := summable_cardyV_tsum prob ha ht
  let g : ℕ → ℝ := fun k =>
    ((4 * Real.pi ^ 2 * t) ^ k / ((k ! : ℝ) * ((k + prob.w - 1)! : ℝ))) *
      listDiff (List.ofFn prob.μ) (fun α => α ^ k) a
  have hshift_summ : Summable (fun j : ℕ => g (j + prob.m)) :=
    (summable_nat_add_iff prob.m).mpr hV_summ
  have hsum_shift : ∑' k : ℕ, g k = ∑' j : ℕ, g (j + prob.m) := by
    have h0 : ∀ k < prob.m, g k = 0 := fun k hk => by
      dsimp [g]
      rw [listDiff_pow_lt_zero (List.ofFn prob.μ) (by simpa using hk) a, mul_zero]
    rw [← hV_summ.sum_add_tsum_nat_add prob.m, Finset.sum_eq_zero (fun k hk => h0 k (Finset.mem_range.mp hk)),
      zero_add]
  have hterm_le : ∀ j : ℕ,
      (∏ l : Fin prob.m, prob.μ l) * (4 * Real.pi ^ 2 * t) ^ prob.m *
          besselTerm (prob.w - 1 + prob.m) (4 * Real.pi ^ 2 * (a - prob.totalShift) * t) j ≤
        g (j + prob.m) := by
    intro j
    dsimp [g]
    have hge := listDiff_pow_ge_prod (List.ofFn prob.μ) hμ_list (j + prob.m)
      (by simp) a (hsum_eq.symm ▸ ha)
    simp only [List.length_ofFn, hprod_eq, hsum_eq, Nat.add_sub_cancel] at hge
    have hden_pos : (0 : ℝ) < (((j + prob.m)! : ℝ) * ((j + prob.m + prob.w - 1)! : ℝ)) := by
      positivity
    have hmul_ge := mul_le_mul_of_nonneg_left hge
      (div_nonneg (pow_nonneg (by positivity : 0 ≤ 4 * Real.pi ^ 2 * t) (j + prob.m)) hden_pos.le)
    refine le_trans (le_of_eq ?_) hmul_ge
    unfold besselTerm
    have hj_ne : (j ! : ℝ) ≠ 0 := by positivity
    have hjm_ne : ((j + prob.m)! : ℝ) ≠ 0 := by positivity
    have hk_eq : j + prob.m + prob.w - 1 = j + (prob.w - 1 + prob.m) := by omega
    have hexp : (4 * Real.pi ^ 2 * (a - prob.totalShift) * t) ^ j =
        (4 * Real.pi ^ 2 * t) ^ j * (a - prob.totalShift) ^ j := by
      rw [show 4 * Real.pi ^ 2 * (a - prob.totalShift) * t =
        (4 * Real.pi ^ 2 * t) * (a - prob.totalShift) by ring, mul_pow]
    rw [hk_eq, pow_add, hexp]
    field_simp [hj_ne, hjm_ne]
  have hle_tsum := hS_summ.tsum_le_tsum hterm_le hshift_summ
  rw [tsum_mul_left] at hle_tsum
  rw [prob.cardyV_eq_tsum]
  change (∏ l : Fin prob.m, prob.μ l) * (4 * Real.pi ^ 2 * t) ^ prob.m *
      (2 * Real.pi * t) ^ (prob.w - 1) *
      besselS (prob.w - 1 + prob.m) (4 * Real.pi ^ 2 * (a - prob.totalShift) * t) ≤
    (2 * Real.pi * t) ^ (prob.w - 1) * ∑' k : ℕ, g k
  rw [hsum_shift]
  have hmul := mul_le_mul_of_nonneg_left hle_tsum (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi * t) (prob.w - 1))
  unfold besselS
  linarith

/-- Bessel `I_{w - 1 + m}` lower bound (`n1:L4`(c)): for `a > S` and `t > 0`,
`(∏ μ_l) * (2π)^m * √(t / (a - S)) ^ (w - 1 + m) * I_{w - 1 + m}(4π √((a - S) t)) ≤ V(t)`. -/
theorem cardyV_ge_besselI_shift (prob : FixedWeightProblem) {a : ℝ} (ha : prob.totalShift < a)
    {t : ℝ} (ht : 0 < t) :
    (∏ l : Fin prob.m, prob.μ l) * (2 * Real.pi) ^ prob.m *
        Real.sqrt (t / (a - prob.totalShift)) ^ (prob.w - 1 + prob.m) *
        besselI (prob.w - 1 + prob.m) (4 * Real.pi * Real.sqrt ((a - prob.totalShift) * t)) ≤
      prob.cardyV a t := by
  have hpeano := cardyV_ge_peano_kernel prob ha.le ht.le
  refine le_trans ?_ hpeano
  have has_pos : 0 < a - prob.totalShift := sub_pos.mpr ha
  unfold besselI
  have harg : (4 * Real.pi * Real.sqrt ((a - prob.totalShift) * t)) ^ 2 / 4 =
      4 * Real.pi ^ 2 * (a - prob.totalShift) * t := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
  rw [harg]
  have hfac_eq : (2 * Real.pi) ^ prob.m * Real.sqrt (t / (a - prob.totalShift)) ^ (prob.w - 1 + prob.m) *
      (4 * Real.pi * Real.sqrt ((a - prob.totalShift) * t) / 2) ^ (prob.w - 1 + prob.m) =
      (4 * Real.pi ^ 2 * t) ^ prob.m * (2 * Real.pi * t) ^ (prob.w - 1) := by
    have hprod : Real.sqrt (t / (a - prob.totalShift)) *
        (4 * Real.pi * Real.sqrt ((a - prob.totalShift) * t) / 2) = 2 * Real.pi * t := by
      have h1 : Real.sqrt (t / (a - prob.totalShift)) * Real.sqrt ((a - prob.totalShift) * t) = t := by
        rw [← Real.sqrt_mul (by positivity),
          show t / (a - prob.totalShift) * ((a - prob.totalShift) * t) = t ^ 2 by
            field_simp [has_pos.ne'], Real.sqrt_sq ht.le]
      calc Real.sqrt (t / (a - prob.totalShift)) *
            (4 * Real.pi * Real.sqrt ((a - prob.totalShift) * t) / 2)
          = 2 * Real.pi * (Real.sqrt (t / (a - prob.totalShift)) * Real.sqrt ((a - prob.totalShift) * t)) := by
            ring
        _ = 2 * Real.pi * t := by rw [h1]
    rw [mul_assoc, ← mul_pow, hprod, pow_add]
    calc (2 * Real.pi) ^ prob.m * ((2 * Real.pi * t) ^ (prob.w - 1) * (2 * Real.pi * t) ^ prob.m)
        = ((2 * Real.pi) ^ prob.m * (2 * Real.pi * t) ^ prob.m) * (2 * Real.pi * t) ^ (prob.w - 1) := by ring
      _ = (4 * Real.pi ^ 2 * t) ^ prob.m * (2 * Real.pi * t) ^ (prob.w - 1) := by
          rw [← mul_pow]; congr 1; ring
  have heq : (∏ l : Fin prob.m, prob.μ l) * (2 * Real.pi) ^ prob.m *
        Real.sqrt (t / (a - prob.totalShift)) ^ (prob.w - 1 + prob.m) *
        ((4 * Real.pi * Real.sqrt ((a - prob.totalShift) * t) / 2) ^ (prob.w - 1 + prob.m) *
          besselS (prob.w - 1 + prob.m) (4 * Real.pi ^ 2 * (a - prob.totalShift) * t)) =
      (∏ l : Fin prob.m, prob.μ l) * (4 * Real.pi ^ 2 * t) ^ prob.m *
        (2 * Real.pi * t) ^ (prob.w - 1) *
        besselS (prob.w - 1 + prob.m) (4 * Real.pi ^ 2 * (a - prob.totalShift) * t) := by
    calc _ = (∏ l : Fin prob.m, prob.μ l) *
          ((2 * Real.pi) ^ prob.m * Real.sqrt (t / (a - prob.totalShift)) ^ (prob.w - 1 + prob.m) *
            (4 * Real.pi * Real.sqrt ((a - prob.totalShift) * t) / 2) ^ (prob.w - 1 + prob.m)) *
          besselS (prob.w - 1 + prob.m) (4 * Real.pi ^ 2 * (a - prob.totalShift) * t) := by ring
      _ = _ := by rw [hfac_eq]; ring
  exact heq.le

/-- **Lemma 4(b), value at `t = 0`**: `V(0) = 0` unless `m = 0` and `w = 1`. -/
theorem cardyV_at_zero (prob : FixedWeightProblem) (a : ℝ) :
    prob.cardyV a 0 = if prob.m = 0 ∧ prob.w = 1 then 1 else 0 := by
  have hw := prob.hw
  by_cases hw1 : prob.w = 1
  · by_cases hm0 : prob.m = 0
    · simp only [hm0, hw1, and_self, ↓reduceIte]
      unfold FixedWeightProblem.cardyV FixedWeightProblem.shiftSum kernelK
      have huniv : (Finset.univ : Finset (Finset (Fin prob.m))) = {∅} := by
        ext s
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        ext i
        exact (Fin.elim0 (hm0 ▸ i))
      rw [huniv, Finset.sum_singleton]
      simp only [Finset.card_empty, pow_zero, one_mul, Finset.sum_empty, sub_zero,
        mul_zero, kernelKTerm, hw1, Nat.sub_self]
      have htsum : (∑' k : ℕ, (if k = 0 then (1 : ℝ) else 0)) = 1 := tsum_ite_eq 0 1
      refine (tsum_congr fun k => ?_).trans htsum
      rcases k with _ | k <;> simp
    · simp only [hm0, false_and, ↓reduceIte]
      rw [prob.cardyV_eq_tsum, hw1, Nat.sub_self, pow_zero, one_mul]
      have hzero : (∑' k : ℕ, (4 * Real.pi ^ 2 * 0) ^ k / ((k ! : ℝ) * ((k + 1 - 1)! : ℝ)) *
          listDiff (List.ofFn prob.μ) (fun α => α ^ k) a) = 0 := by
        refine (tsum_congr fun k => ?_).trans tsum_zero
        rcases k with _ | k
        · have hlt : 0 < (List.ofFn prob.μ).length := by rw [List.length_ofFn]; omega
          rw [listDiff_pow_lt_zero (List.ofFn prob.μ) hlt a, mul_zero]
        · simp
      exact hzero
  · have hpos : 0 < prob.w - 1 := by omega
    rw [prob.cardyV_eq_tsum]
    simp [hw1, zero_pow hpos.ne']

/-- **Lemma 4(d), first bound (`n1:L4`)**: for `a ≥ S` and `t ≥ 0`,
`V(t) ≤ (∏ μ_l) (4π² t)^m K_a^{(w)}(t)`. -/
theorem cardyV_le_pow_mul_kernelK (prob : FixedWeightProblem) {a : ℝ} (ha : prob.totalShift ≤ a)
    {t : ℝ} (ht : 0 ≤ t) :
    prob.cardyV a t ≤ (∏ l : Fin prob.m, prob.μ l) * (4 * Real.pi ^ 2 * t) ^ prob.m * kernelK prob.w a t := by
  have hw := prob.hw
  have hsum_eq : (List.ofFn prob.μ).sum = prob.totalShift := by
    unfold FixedWeightProblem.totalShift; rw [List.sum_ofFn]
  have hprod_eq : (List.ofFn prob.μ).prod = ∏ l : Fin prob.m, prob.μ l := by
    rw [List.prod_ofFn]
  have hμ_list : ∀ ν ∈ List.ofFn prob.μ, 0 < ν := by
    intro ν hν; rw [List.mem_ofFn] at hν; rcases hν with ⟨l, rfl⟩; exact prob.hμ l
  have hV_summ := summable_cardyV_tsum prob ha ht
  let g : ℕ → ℝ := fun k =>
    ((4 * Real.pi ^ 2 * t) ^ k / ((k ! : ℝ) * ((k + prob.w - 1)! : ℝ))) *
      listDiff (List.ofFn prob.μ) (fun α => α ^ k) a
  have hshift_summ : Summable (fun j : ℕ => g (j + prob.m)) :=
    (summable_nat_add_iff prob.m).mpr hV_summ
  have hsum_shift : ∑' k : ℕ, g k = ∑' j : ℕ, g (j + prob.m) := by
    have h0 : ∀ k < prob.m, g k = 0 := fun k hk => by
      dsimp [g]
      rw [listDiff_pow_lt_zero (List.ofFn prob.μ) (by simpa using hk) a, mul_zero]
    rw [← hV_summ.sum_add_tsum_nat_add prob.m, Finset.sum_eq_zero (fun k hk => h0 k (Finset.mem_range.mp hk)),
      zero_add]
  have hK_summ : Summable fun j : ℕ =>
      (∏ l : Fin prob.m, prob.μ l) * (4 * Real.pi ^ 2 * t) ^ prob.m * kernelKTerm prob.w a t j :=
    (summable_kernelKTerm prob.w a t).mul_left _
  have hterm_le : ∀ j : ℕ, g (j + prob.m) ≤
      (∏ l : Fin prob.m, prob.μ l) * (4 * Real.pi ^ 2 * t) ^ prob.m * kernelKTerm prob.w a t j := by
    intro j
    dsimp [g]
    have hle := listDiff_pow_le_prod (List.ofFn prob.μ) hμ_list (j + prob.m)
      (by simp) a (hsum_eq.symm ▸ ha)
    simp only [List.length_ofFn, hprod_eq, Nat.add_sub_cancel] at hle
    have hden_pos : (0 : ℝ) < (((j + prob.m)! : ℝ) * ((j + prob.m + prob.w - 1)! : ℝ)) := by
      positivity
    have hmul_le := mul_le_mul_of_nonneg_left hle
      (div_nonneg (pow_nonneg (by positivity : 0 ≤ 4 * Real.pi ^ 2 * t) (j + prob.m)) hden_pos.le)
    refine hmul_le.trans ?_
    unfold kernelKTerm
    have hj_ne : (j ! : ℝ) ≠ 0 := by positivity
    have hjm_ne : ((j + prob.m)! : ℝ) ≠ 0 := by positivity
    have hfac_le : ((j + prob.w - 1)! : ℝ) ≤ ((j + prob.m + prob.w - 1)! : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have ha_nn : 0 ≤ a := prob.totalShift_nonneg.trans ha
    have hprod_nn : 0 ≤ ∏ l : Fin prob.m, prob.μ l := Finset.prod_nonneg fun l _ => (prob.hμ l).le
    have hnum_nn : 0 ≤ (∏ l : Fin prob.m, prob.μ l) * (4 * Real.pi ^ 2 * t) ^ prob.m *
        (4 * Real.pi ^ 2 * a * t) ^ j := by
      positivity
    have hrew : (4 * Real.pi ^ 2 * t) ^ (j + prob.m) / (((j + prob.m)! : ℝ) * ((j + prob.m + prob.w - 1)! : ℝ)) *
          ((∏ l : Fin prob.m, prob.μ l) * (((j + prob.m)! : ℝ) / (j ! : ℝ)) * a ^ j) =
        (∏ l : Fin prob.m, prob.μ l) * (4 * Real.pi ^ 2 * t) ^ prob.m *
          ((4 * Real.pi ^ 2 * a * t) ^ j / ((j ! : ℝ) * ((j + prob.m + prob.w - 1)! : ℝ))) := by
      rw [pow_add, mul_pow, mul_pow]
      field_simp [hj_ne, hjm_ne]
      ring
    rw [hrew]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hnum_pow_nn : 0 ≤ (4 * Real.pi ^ 2 * a * t) ^ j :=
      pow_nonneg (mul_nonneg (mul_nonneg (by positivity) ha_nn) ht) j
    have hden_pos1 : (0 : ℝ) < (j ! : ℝ) * ((j + prob.w - 1)! : ℝ) := by positivity
    exact div_le_div_of_nonneg_left hnum_pow_nn hden_pos1
      (mul_le_mul_of_nonneg_left hfac_le (by positivity))
  have hle_tsum := hshift_summ.tsum_le_tsum hterm_le hK_summ
  rw [tsum_mul_left] at hle_tsum
  rw [prob.cardyV_eq_tsum]
  change (2 * Real.pi * t) ^ (prob.w - 1) * ∑' k : ℕ, g k ≤ _
  rw [hsum_shift]
  have hmul := mul_le_mul_of_nonneg_left hle_tsum (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi * t) (prob.w - 1))
  unfold kernelK
  linarith

/-- **Lemma 4(d), second bound (`n1:L4`)**: for `w ≥ 1`, `a > 0`, `t ≥ 0`,
`K_a^{(w)}(t) ≤ (t/a)^{(w-1)/2} e^{4π √(a t)}`. -/
theorem kernelK_le_pow_mul_exp {w : ℕ} (hw : 1 ≤ w) {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    kernelK w a t ≤ Real.sqrt (t / a) ^ (w - 1) * Real.exp (4 * Real.pi * Real.sqrt (a * t)) := by
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · unfold kernelK
    by_cases hw1 : w = 1
    · subst hw1
      simp only [Nat.sub_self, pow_zero, one_mul, mul_zero, Real.sqrt_zero, Real.exp_zero, mul_one]
      have h0 : (∑' k : ℕ, kernelKTerm 1 a 0 k) = 1 := by
        have heq : (fun k : ℕ => kernelKTerm 1 a 0 k) = fun k => if k = 0 then 1 else 0 := by
          ext k; rcases k with _ | k <;> simp [kernelKTerm]
        rw [heq, tsum_ite_eq]
      exact h0.le
    · have hpos : 0 < w - 1 := by omega
      simp [zero_pow hpos.ne']
  · rw [Crossing.kernelK_eq_besselI hw ha ht_pos]
    have hle : besselI (w - 1) (4 * Real.pi * Real.sqrt (a * t)) ≤
        Real.exp (4 * Real.pi * Real.sqrt (a * t)) :=
      (Crossing.besselI_le_zero (w - 1) _).trans (besselI0_le_exp (by positivity))
    exact mul_le_mul_of_nonneg_left hle (pow_nonneg (Real.sqrt_nonneg _) _)

private lemma convexOn_univ_of_continuous_midpoint {f : ℝ → ℝ} (hcont : Continuous f)
    (hmid : ∀ s₁ s₂ : ℝ, f ((1 / 2 : ℝ) * s₁ + (1 / 2 : ℝ) * s₂) ≤ (1 / 2 : ℝ) * f s₁ + (1 / 2 : ℝ) * f s₂) :
    ConvexOn ℝ univ f := by
  have hdyad : ∀ n : ℕ, ∀ k : ℕ, k ≤ 2 ^ n → ∀ x y : ℝ,
      let t : ℝ := (k : ℝ) / (2 ^ n : ℝ)
      f ((1 - t) * x + t * y) ≤ (1 - t) * f x + t * f y := by
    intro n
    induction n with
    | zero =>
      intro k hk x y
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl <;> simp
    | succ n ih =>
      intro k hk x y
      dsimp only
      by_cases hk2 : k ≤ 2 ^ n
      · have harg : (1 - (k : ℝ) / (2 ^ (n + 1) : ℝ)) * x + ((k : ℝ) / (2 ^ (n + 1) : ℝ)) * y =
            (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * ((1 - (k : ℝ) / (2 ^ n : ℝ)) * x + ((k : ℝ) / (2 ^ n : ℝ)) * y) := by
          rw [pow_succ]; ring
        have hrhs : (1 - (k : ℝ) / (2 ^ (n + 1) : ℝ)) * f x + ((k : ℝ) / (2 ^ (n + 1) : ℝ)) * f y =
            (1 / 2 : ℝ) * f x + (1 / 2 : ℝ) * ((1 - (k : ℝ) / (2 ^ n : ℝ)) * f x + ((k : ℝ) / (2 ^ n : ℝ)) * f y) := by
          rw [pow_succ]; ring
        rw [harg, hrhs]
        exact (hmid _ _).trans (add_le_add_right (mul_le_mul_of_nonneg_left (ih k hk2 x y) (by norm_num)) _)
      · have hk' : k - 2 ^ n ≤ 2 ^ n := by omega
        have hk_ge : 2 ^ n ≤ k := by omega
        have h2pow : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by rw [pow_succ]; ring
        have h2ne : (2 : ℝ) ^ n ≠ 0 := by positivity
        have harg : (1 - (k : ℝ) / (2 ^ (n + 1) : ℝ)) * x + ((k : ℝ) / (2 ^ (n + 1) : ℝ)) * y =
            (1 / 2 : ℝ) * y + (1 / 2 : ℝ) * ((1 - ((k - 2 ^ n : ℕ) : ℝ) / (2 ^ n : ℝ)) * x +
              (((k - 2 ^ n : ℕ) : ℝ) / (2 ^ n : ℝ)) * y) := by
          rw [Nat.cast_sub hk_ge, h2pow]; push_cast; field_simp [h2ne]; ring
        have hrhs : (1 - (k : ℝ) / (2 ^ (n + 1) : ℝ)) * f x + ((k : ℝ) / (2 ^ (n + 1) : ℝ)) * f y =
            (1 / 2 : ℝ) * f y + (1 / 2 : ℝ) * ((1 - ((k - 2 ^ n : ℕ) : ℝ) / (2 ^ n : ℝ)) * f x +
              (((k - 2 ^ n : ℕ) : ℝ) / (2 ^ n : ℝ)) * f y) := by
          rw [Nat.cast_sub hk_ge, h2pow]; push_cast; field_simp [h2ne]; ring
        rw [harg, hrhs]
        exact (hmid _ _).trans (add_le_add_right (mul_le_mul_of_nonneg_left (ih (k - 2 ^ n) hk' x y) (by norm_num)) _)
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have h1a : b = 1 - a := by linarith
  subst h1a
  have hax : a ≤ 1 := by linarith
  have hbn : ∀ n : ℕ, ⌊(1 - a) * (2 ^ n : ℝ)⌋₊ ≤ 2 ^ n := fun n => by
    refine Nat.floor_le_of_le ?_
    have h1 : (1 - a) * (2 ^ n : ℝ) ≤ 1 * (2 ^ n : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    exact_mod_cast h1.trans_eq (one_mul _)
  let k : ℕ → ℕ := fun n => ⌊(1 - a) * (2 ^ n : ℝ)⌋₊
  let t : ℕ → ℝ := fun n => (k n : ℝ) / (2 ^ n : ℝ)
  have ht_le : ∀ n : ℕ, (1 - a) - 1 / (2 ^ n : ℝ) < t n := fun n => by
    dsimp [t, k]
    have h2 : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
    rw [lt_div_iff₀ h2, sub_mul, div_mul_cancel₀ _ h2.ne']
    linarith [Nat.lt_floor_add_one ((1 - a) * (2 ^ n : ℝ))]
  have ht_ge : ∀ n : ℕ, t n ≤ 1 - a := fun n => by
    dsimp [t, k]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mpr (Nat.floor_le (mul_nonneg hb (by positivity)))
  have ht_tend : Tendsto t atTop (𝓝 (1 - a)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds
      (fun n => (ht_le n).le) ht_ge
    have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (2 ^ n : ℝ)) atTop (𝓝 0) :=
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)).congr fun n =>
        one_div ((2 : ℝ) ^ n) |>.symm
    simpa using (tendsto_const_nhds (x := (1 - a))).sub hinv
  have hle_n : ∀ n : ℕ, f ((1 - t n) * x + t n * y) ≤ (1 - t n) * f x + t n * f y :=
    fun n => hdyad n (k n) (hbn n) x y
  have hL : Tendsto (fun n : ℕ => f ((1 - t n) * x + t n * y)) atTop
      (𝓝 (f ((1 - (1 - a)) * x + (1 - a) * y))) :=
    (hcont.tendsto _).comp (((tendsto_const_nhds.sub ht_tend).mul_const x).add (ht_tend.mul_const y))
  have hR : Tendsto (fun n : ℕ => (1 - t n) * f x + t n * f y) atTop
      (𝓝 ((1 - (1 - a)) * f x + (1 - a) * f y)) :=
    ((tendsto_const_nhds.sub ht_tend).mul_const (f x)).add (ht_tend.mul_const (f y))
  have hlim := le_of_tendsto_of_tendsto hL hR (Eventually.of_forall hle_n)
  simpa only [sub_sub_cancel, smul_eq_mul] using hlim

/-- **Lemma 4(b), log-convexity (`n1:L4`)**: for `a ≥ S`, `s ↦ log V(e^s)` is convex on `ℝ`. -/
theorem cardyV_log_convex (prob : FixedWeightProblem) {a : ℝ} (ha : prob.totalShift ≤ a) :
    ConvexOn ℝ univ (fun s : ℝ => Real.log (prob.cardyV a (Real.exp s))) := by
  have hcont : Continuous fun s : ℝ => Real.log (prob.cardyV a (Real.exp s)) := by
    refine Continuous.log ((continuous_cardyV prob a).comp Real.continuous_exp) fun s => ?_
    exact (prob.cardyV_pos ha (Real.exp_pos s)).ne'
  refine convexOn_univ_of_continuous_midpoint hcont fun s₁ s₂ => ?_
  have ht₁ : 0 < Real.exp s₁ := Real.exp_pos s₁
  have ht₂ : 0 < Real.exp s₂ := Real.exp_pos s₂
  have hmid_exp : Real.exp ((1 / 2 : ℝ) * s₁ + (1 / 2 : ℝ) * s₂) = Real.sqrt (Real.exp s₁ * Real.exp s₂) := by
    rw [Real.exp_add, Real.sqrt_mul ht₁.le, ← Real.exp_half, ← Real.exp_half]
    ring_nf
  have hV_sq : prob.cardyV a (Real.sqrt (Real.exp s₁ * Real.exp s₂)) ^ 2 ≤
      prob.cardyV a (Real.exp s₁) * prob.cardyV a (Real.exp s₂) := by
    have hsum_eq : (List.ofFn prob.μ).sum = prob.totalShift := by
      unfold FixedWeightProblem.totalShift; rw [List.sum_ofFn]
    have hμ_list : ∀ ν ∈ List.ofFn prob.μ, 0 < ν := by
      intro ν hν; rw [List.mem_ofFn] at hν; rcases hν with ⟨l, rfl⟩; exact prob.hμ l
    let c : ℕ → ℝ := fun k =>
      ((4 * Real.pi ^ 2) ^ k / ((k ! : ℝ) * ((k + prob.w - 1)! : ℝ))) *
        listDiff (List.ofFn prob.μ) (fun α => α ^ k) a
    have hc_nn : ∀ k, 0 ≤ c k := fun k =>
      mul_nonneg (div_nonneg (pow_nonneg (by positivity) k) (by positivity))
        (listDiff_pow_nonneg _ hμ_list k (hsum_eq.symm ▸ ha))
    have hV_form : ∀ t : ℝ, 0 ≤ t →
        prob.cardyV a t = (2 * Real.pi * t) ^ (prob.w - 1) * ∑' k : ℕ, c k * t ^ k := by
      intro t _
      rw [prob.cardyV_eq_tsum]
      congr 1
      refine tsum_congr fun k => ?_
      dsimp [c]; rw [mul_pow]; ring
    have hs_summ : ∀ t : ℝ, 0 ≤ t → Summable (fun k : ℕ => c k * t ^ k) := fun t ht => by
      refine (summable_cardyV_tsum prob ha ht).congr fun k => ?_
      dsimp [c]; rw [mul_pow]; ring
    let tm := Real.sqrt (Real.exp s₁ * Real.exp s₂)
    have htm_nn : 0 ≤ tm := Real.sqrt_nonneg _
    have htm_sq : tm ^ 2 = Real.exp s₁ * Real.exp s₂ := Real.sq_sqrt (by positivity)
    have hcs_fin : ∀ N : ℕ,
        (∑ k ∈ Finset.range N, c k * tm ^ k) ^ 2 ≤
          (∑ k ∈ Finset.range N, c k * Real.exp s₁ ^ k) *
          (∑ k ∈ Finset.range N, c k * Real.exp s₂ ^ k) := fun N => by
      have hterm : ∀ k ∈ Finset.range N,
          c k * tm ^ k = Real.sqrt (c k * Real.exp s₁ ^ k) * Real.sqrt (c k * Real.exp s₂ ^ k) := by
        intro k _
        rw [← Real.sqrt_mul (mul_nonneg (hc_nn k) (pow_nonneg ht₁.le k)),
          show (c k * Real.exp s₁ ^ k) * (c k * Real.exp s₂ ^ k) = (c k * tm ^ k) ^ 2 by
            rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul, htm_sq, mul_pow]; ring,
          Real.sqrt_sq (mul_nonneg (hc_nn k) (pow_nonneg htm_nn k))]
      rw [Finset.sum_congr rfl hterm]
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
        (fun k => Real.sqrt (c k * Real.exp s₁ ^ k))
        (fun k => Real.sqrt (c k * Real.exp s₂ ^ k))
      refine hcs.trans_eq ?_
      congr 1 <;> refine Finset.sum_congr rfl fun k _ => ?_
      · exact Real.sq_sqrt (mul_nonneg (hc_nn k) (pow_nonneg ht₁.le k))
      · exact Real.sq_sqrt (mul_nonneg (hc_nn k) (pow_nonneg ht₂.le k))
    have hcs_tsum : (∑' k : ℕ, c k * tm ^ k) ^ 2 ≤
        (∑' k : ℕ, c k * Real.exp s₁ ^ k) * (∑' k : ℕ, c k * Real.exp s₂ ^ k) := by
      have ht_m := (hs_summ tm htm_nn).hasSum.tendsto_sum_nat
      have ht_1 := (hs_summ (Real.exp s₁) ht₁.le).hasSum.tendsto_sum_nat
      have ht_2 := (hs_summ (Real.exp s₂) ht₂.le).hasSum.tendsto_sum_nat
      exact le_of_tendsto_of_tendsto (ht_m.pow 2) (ht_1.mul ht_2) (Eventually.of_forall hcs_fin)
    rw [hV_form tm htm_nn, hV_form (Real.exp s₁) ht₁.le, hV_form (Real.exp s₂) ht₂.le, mul_pow]
    have hpref : ((2 * Real.pi * tm) ^ (prob.w - 1)) ^ 2 =
        (2 * Real.pi * Real.exp s₁) ^ (prob.w - 1) * (2 * Real.pi * Real.exp s₂) ^ (prob.w - 1) := by
      rw [← pow_mul, mul_comm (prob.w - 1) 2, pow_mul, mul_pow, mul_pow, htm_sq, ← mul_pow,
        show (2 * Real.pi) ^ 2 * (Real.exp s₁ * Real.exp s₂) =
          (2 * Real.pi * Real.exp s₁) * (2 * Real.pi * Real.exp s₂) by ring,
        mul_pow]
    calc ((2 * Real.pi * tm) ^ (prob.w - 1)) ^ 2 * (∑' k : ℕ, c k * tm ^ k) ^ 2
        ≤ ((2 * Real.pi * tm) ^ (prob.w - 1)) ^ 2 *
            ((∑' k : ℕ, c k * Real.exp s₁ ^ k) * (∑' k : ℕ, c k * Real.exp s₂ ^ k)) := by
          exact mul_le_mul_of_nonneg_left hcs_tsum (sq_nonneg _)
      _ = ((2 * Real.pi * Real.exp s₁) ^ (prob.w - 1) * ∑' k : ℕ, c k * Real.exp s₁ ^ k) *
            ((2 * Real.pi * Real.exp s₂) ^ (prob.w - 1) * ∑' k : ℕ, c k * Real.exp s₂ ^ k) := by
          rw [hpref]; ring
  have hV_pos1 : 0 < prob.cardyV a (Real.exp s₁) := prob.cardyV_pos ha ht₁
  have hV_pos2 : 0 < prob.cardyV a (Real.exp s₂) := prob.cardyV_pos ha ht₂
  have hV_posm : 0 < prob.cardyV a (Real.sqrt (Real.exp s₁ * Real.exp s₂)) :=
    prob.cardyV_pos ha (Real.sqrt_pos.mpr (mul_pos ht₁ ht₂))
  rw [hmid_exp]
  have hlog := Real.log_le_log (sq_pos_of_pos hV_posm) hV_sq
  rw [Real.log_pow, Real.log_mul hV_pos1.ne' hV_pos2.ne'] at hlog
  simp only [Nat.cast_ofNat] at hlog ⊢
  linarith

/-! ### Section 3: Lemma 4(e) — Threshold window (`sup |g| ≤ C₁ M[g]` for general `w ≥ 1`) -/

/-- For any `g ∈ TestClass prob a g` and `t ≥ 0`:
`|g t| ≤ ((2π)^w / (w - 1)!) * ∫ s in Ioi 0, |g s| * s ^ (w - 1)`
(`n1_super_virasoro.tex`, Lemma 4(e)). -/
theorem abs_le_radial_l1 {prob : FixedWeightProblem} {a : ℝ} {g : ℝ → ℝ}
    (hg : TestClass prob a g) {t : ℝ} (ht : 0 ≤ t) :
    |g t| ≤ ((2 * Real.pi) ^ prob.w / ((prob.w - 1)! : ℝ)) *
      ∫ s in Ioi (0 : ℝ), |g s| * s ^ (prob.w - 1) := by
  have hw := prob.hw
  let i0 : Fin (2 * prob.w) := ⟨0, by omega⟩
  let x₀ : EuclideanSpace ℝ (Fin (2 * prob.w)) := EuclideanSpace.single i0 (Real.sqrt (2 * t))
  have hx₀ : ‖x₀‖ = Real.sqrt (2 * t) := by
    simp [x₀, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hfx : radialLift prob.w g x₀ = (g t : ℂ) := by
    simp only [radialLift, hx₀, Real.sq_sqrt (by linarith : 0 ≤ 2 * t)]
    congr 2; ring
  have hodd : 𝓕 (radialLift prob.w g) x₀ = -(radialLift prob.w g x₀) :=
    congrFun hg.fourier_odd x₀
  have h1 := Real.norm_fourier_le_integral_norm (radialLift prob.w g) x₀
  rw [hodd, norm_neg, hfx, Complex.norm_real, Real.norm_eq_abs] at h1
  refine h1.trans (le_of_eq ?_)
  have h2 : ∫ v : EuclideanSpace ℝ (Fin (2 * prob.w)), ‖radialLift prob.w g v‖ =
      ∫ v : EuclideanSpace ℝ (Fin (2 * prob.w)), (fun s => |g s|) (‖v‖ ^ 2 / 2) := by
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp [radialLift]
  have h3 := integral_radialLiftReal hw (fun s => |g s|)
  rw [h2, h3]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  ring

/-- **Lemma 4(e), `L¹` and `L^∞` bounds (`n1:L4`)**: for `a ≥ S` and `g ∈ TestClass prob a g`,
`∫₀^∞ |g| t^{w-1} dt ≤ C_int M[g]` and `sup_{t ≥ 0} |g(t)| ≤ C_1 M[g]`, with constants depending
only on `prob` (independent of `a`). -/
theorem testClass_window_bounds (prob : FixedWeightProblem) :
    ∃ C_int C_1 : ℝ, 0 < C_int ∧ 0 < C_1 ∧
      ∀ {a : ℝ} {g : ℝ → ℝ}, prob.totalShift ≤ a → TestClass prob a g →
        (∫ t in Ioi (0 : ℝ), |g t| * t ^ (prob.w - 1) ≤ C_int * prob.cardyNorm a g) ∧
        (∀ {t : ℝ}, 0 ≤ t → |g t| ≤ C_1 * prob.cardyNorm a g) := by
  have hw := prob.hw
  let K_w : ℝ := (2 * Real.pi) ^ prob.w / ((prob.w - 1)! : ℝ)
  have hKw_pos : 0 < K_w := by positivity
  let tStar : ℝ := ((prob.w : ℝ) / (2 * K_w)) ^ (1 / (prob.w : ℝ))
  have hw_pos : (0 : ℝ) < (prob.w : ℝ) := by exact_mod_cast (by omega : 0 < prob.w)
  have htStar_pos : 0 < tStar := Real.rpow_pos_of_pos (by positivity) _
  have htStar_pow : tStar ^ prob.w = (prob.w : ℝ) / (2 * K_w) := by
    dsimp [tStar]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have hmul : 1 / (prob.w : ℝ) * (prob.w : ℝ) = 1 := one_div_mul_cancel hw_pos.ne'
    rw [hmul, Real.rpow_one]
  let c_low : ℝ := (2 * Real.pi) ^ (prob.w - 1) * (4 * Real.pi ^ 2) ^ prob.m *
      (∏ l : Fin prob.m, prob.μ l) / (((prob.m + prob.w - 1)! : ℝ))
  have hprod_pos : 0 < ∏ l : Fin prob.m, prob.μ l := Finset.prod_pos fun l _ => prob.hμ l
  have hc_low_pos : 0 < c_low := by dsimp [c_low]; positivity
  let c_thr : ℝ := c_low * tStar ^ prob.m
  have hc_thr_pos : 0 < c_thr := by positivity
  let C_int : ℝ := 2 / c_thr
  let C_1 : ℝ := K_w * C_int
  refine ⟨C_int, C_1, by positivity, by positivity, fun {a g} ha hg => ?_⟩
  have hA_int : IntegrableOn (fun t : ℝ => |g t| * t ^ (prob.w - 1)) (Ioi 0) := by
    have h1 : IntegrableOn (fun t : ℝ => ‖t ^ (prob.w - 1) * g t‖) (Ioi 0) :=
      ((integrable_radialLift_iff hw g).1 hg.int_lift).norm
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
    dsimp only
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (mem_Ioi.mp ht).le _), mul_comm]
  set A : ℝ := ∫ t in Ioi (0 : ℝ), |g t| * t ^ (prob.w - 1) with hA_def
  have hA_nn : 0 ≤ A := setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg (abs_nonneg _) (pow_nonneg (mem_Ioi.mp ht).le _)
  have hsplit : A = (∫ t in Ioc 0 tStar, |g t| * t ^ (prob.w - 1)) +
      (∫ t in Ioi tStar, |g t| * t ^ (prob.w - 1)) := by
    rw [hA_def, ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hA_int.mono_set Ioc_subset_Ioi_self) (hA_int.mono_set (Ioi_subset_Ioi htStar_pos.le)),
      Ioc_union_Ioi_eq_Ioi htStar_pos.le]
  have hhead : ∫ t in Ioc 0 tStar, |g t| * t ^ (prob.w - 1) ≤ A / 2 := by
    have hdom : IntegrableOn (fun t : ℝ => (K_w * A) * t ^ (prob.w - 1)) (Ioc 0 tStar) :=
      ((by fun_prop : Continuous fun t : ℝ => (K_w * A) * t ^ (prob.w - 1)).continuousOn.integrableOn_Icc).mono_set
        Ioc_subset_Icc_self
    have hle1 : ∫ t in Ioc 0 tStar, |g t| * t ^ (prob.w - 1) ≤
        ∫ t in Ioc 0 tStar, (K_w * A) * t ^ (prob.w - 1) := by
      refine setIntegral_mono_on (hA_int.mono_set Ioc_subset_Ioi_self) hdom measurableSet_Ioc
        fun t ht => ?_
      have hsup := abs_le_radial_l1 hg ht.1.le
      exact mul_le_mul_of_nonneg_right hsup (pow_nonneg ht.1.le _)
    have heval : ∫ t in Ioc 0 tStar, (K_w * A) * t ^ (prob.w - 1) = A / 2 := by
      rw [integral_const_mul, ← intervalIntegral.integral_of_le htStar_pos.le, integral_pow]
      have hw_eq : prob.w - 1 + 1 = prob.w := Nat.sub_add_cancel hw
      have hw_cast : ((prob.w - 1 : ℕ) : ℝ) + 1 = (prob.w : ℝ) := by
        rw [Nat.cast_sub hw, Nat.cast_one]; ring
      rw [hw_eq, zero_pow (by omega : prob.w ≠ 0), sub_zero, hw_cast, htStar_pow]
      have hKw_ne : K_w ≠ 0 := hKw_pos.ne'
      have hwn_ne : ((prob.w : ℝ)) ≠ 0 := hw_pos.ne'
      field_simp [hKw_ne, hwn_ne]
    linarith
  have hV_ge : ∀ t ∈ Ioi tStar, c_thr * t ^ (prob.w - 1) ≤ prob.cardyV a t := fun t ht => by
    have ht0 : 0 ≤ t := (htStar_pos.trans ht).le
    have hlb := prob.cardyV_lower_bound ha ht0
    have hpow_eq : t ^ (prob.m + prob.w - 1) = t ^ prob.m * t ^ (prob.w - 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow_eq] at hlb
    have hm_le : tStar ^ prob.m ≤ t ^ prob.m :=
      pow_le_pow_left₀ htStar_pos.le (mem_Ioi.mp ht).le prob.m
    calc c_thr * t ^ (prob.w - 1)
        = c_low * tStar ^ prob.m * t ^ (prob.w - 1) := rfl
      _ ≤ c_low * (t ^ prob.m * t ^ (prob.w - 1)) := by
          have := mul_le_mul_of_nonneg_left hm_le hc_low_pos.le
          have := mul_le_mul_of_nonneg_right this (pow_nonneg ht0 (prob.w - 1))
          linarith
      _ ≤ prob.cardyV a t := hlb
  have htail : ∫ t in Ioi tStar, |g t| * t ^ (prob.w - 1) ≤ (1 / c_thr) * prob.cardyNorm a g := by
    have hMint := hg.int_cardy
    have hmono : ∫ t in Ioi tStar, |g t| * t ^ (prob.w - 1) ≤
        ∫ t in Ioi tStar, (1 / c_thr) * (|g t| * prob.cardyV a t) := by
      refine setIntegral_mono_on (hA_int.mono_set (Ioi_subset_Ioi htStar_pos.le))
        ((hMint.mono_set (Ioi_subset_Ioi htStar_pos.le)).const_mul _) measurableSet_Ioi
        fun t ht => ?_
      have hge := hV_ge t ht
      have hg0 : 0 ≤ |g t| := abs_nonneg _
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hc_thr_pos]
      nlinarith
    have hM_le : ∫ t in Ioi tStar, |g t| * prob.cardyV a t ≤ prob.cardyNorm a g := by
      unfold FixedWeightProblem.cardyNorm
      refine setIntegral_mono_set hMint ?_ (Ioi_subset_Ioi htStar_pos.le).eventuallyLE
      exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht =>
        mul_nonneg (abs_nonneg _) (prob.cardyV_nonneg ha (mem_Ioi.mp ht).le))
    rw [integral_const_mul] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_left hM_le (by positivity))
  have hA_le : A ≤ C_int * prob.cardyNorm a g := by
    have h1 : A ≤ A / 2 + (1 / c_thr) * prob.cardyNorm a g := by linarith [hsplit, hhead, htail]
    have h2 : C_int * prob.cardyNorm a g = 2 * ((1 / c_thr) * prob.cardyNorm a g) := by
      dsimp [C_int]; ring
    linarith
  refine ⟨hA_le, fun {t} ht => ?_⟩
  calc |g t| ≤ K_w * A := abs_le_radial_l1 hg ht
    _ ≤ K_w * (C_int * prob.cardyNorm a g) := mul_le_mul_of_nonneg_left hA_le hKw_pos.le
    _ = C_1 * prob.cardyNorm a g := by dsimp [C_1]; ring

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.norm_kernelKC_strip_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_kernelKC_strip_le

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.cardyV_le_kernelK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardyV_le_kernelK

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.cardyV_ge_besselI_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardyV_ge_besselI_shift

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.cardyV_log_convex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardyV_log_convex

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.testClass_window_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms testClass_window_bounds

end FormalResearch.ModularBootstrap.WeightAxioms
