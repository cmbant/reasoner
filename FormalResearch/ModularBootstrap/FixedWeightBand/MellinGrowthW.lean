module

public import FormalResearch.ModularBootstrap.WeightAxioms.KernelAndPositivity

/-!
# Polynomial Domination by the Cardy Kernel `V` at Weight `w` (growth input of `vlo:S1`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J2, Lemma S1 (`vlo:S1`), first half of
the proof: for every `r ≥ 0`, `t^r ≤ C_r V(t)` on `[1, ∞)`.

The paper obtains this from the Taylor term of order `k` of `K_a^{(w)}`.  Here it is derived directly
for `V = prob.cardyV a` with `prob.totalShift ≤ a` and `0 < a` (the second condition is automatic
unless `Q ≡ 1`), from the half-step Peano lower bound for iterated differences of `α ↦ α^k`:

* `listDiff_pow_ge_half`: for `Σ μ ≤ a` and `k ≥ #μ`,
  `Δ_μ(α^k)(a) ≥ (∏ μ / 2^{#μ}) · k!/(k - #μ)! · (a - Σμ / 2)^{k - #μ}` (positive for `a > 0`);
* `cardyV_ge_pow`: `V(t) ≥ c t^{w - 1 + m + j}` for every `j : ℕ`, `c > 0`;
* `PolyDom`, `polyDom_cardyV`: `V` dominates every real power on `[1, ∞)`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing Bessel WeightAxioms

/-- Half-step Peano lower bound for iterated differences of `α ↦ α^k` (`k ≥ μs.length`,
`Σ μs ≤ a`); positive when `a > 0`. -/
lemma listDiff_pow_ge_half (μs : List ℝ) (hμ : ∀ μ ∈ μs, 0 < μ) :
    ∀ (k : ℕ) (_hk : μs.length ≤ k) (a : ℝ) (_ha : μs.sum ≤ a),
      μs.prod / 2 ^ μs.length * ((k ! : ℝ) / ((k - μs.length)! : ℝ)) *
          (a - μs.sum / 2) ^ (k - μs.length) ≤
        listDiff μs (fun α => α ^ k) a := by
  induction μs with
  | nil =>
    intro k _ a ha
    simp only [List.length_nil, List.prod_nil, pow_zero, div_one, Nat.sub_zero, List.sum_nil,
      zero_div, sub_zero, listDiff]
    have hk_ne : (k ! : ℝ) ≠ 0 := by positivity
    rw [div_self hk_ne]; simp
  | cons μ μs ih =>
    intro k hk a ha
    simp only [List.length_cons, List.sum_cons, List.mem_cons, forall_eq_or_imp] at hk ha hμ
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk' : μs.length ≤ k' := by omega
    rw [listDiff_eq_integral μ μs (fun x => hasDerivAt_pow (k' + 1) x) (by fun_prop) a]
    have hcont : Continuous fun u : ℝ =>
        listDiff μs (fun x => ((k' + 1 : ℕ) : ℝ) * x ^ (k' + 1 - 1)) (a - u) :=
      (continuous_listDiff μs (by fun_prop)).comp (continuous_const.sub continuous_id)
    have hfn : (fun x : ℝ => ((k' + 1 : ℕ) : ℝ) * x ^ (k' + 1 - 1)) =
        fun x => ((k' + 1 : ℕ) : ℝ) * (fun y => y ^ k') x := by
      ext x; simp
    have hμ2 : 0 ≤ μ / 2 := by linarith [hμ.1]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hcont.intervalIntegrable 0 (μ / 2)) (hcont.intervalIntegrable (μ / 2) μ)
    have hsecond : 0 ≤ ∫ u in (μ / 2)..μ,
        listDiff μs (fun x => ((k' + 1 : ℕ) : ℝ) * x ^ (k' + 1 - 1)) (a - u) := by
      refine intervalIntegral.integral_nonneg (by linarith [hμ.1]) fun u hu => ?_
      rw [hfn, listDiff_const_mul]
      exact mul_nonneg (by positivity) (listDiff_pow_nonneg μs hμ.2 k' (by linarith [hu.2]))
    have hconst : ∫ _u in (0 : ℝ)..(μ / 2),
        ((k' + 1 : ℕ) : ℝ) * (μs.prod / 2 ^ μs.length * ((k' ! : ℝ) / ((k' - μs.length)! : ℝ)) *
          (a - (μ + μs.sum) / 2) ^ (k' - μs.length)) =
        (μ * μs.prod) / 2 ^ (μs.length + 1) *
          (((k' + 1)! : ℝ) / ((k' + 1 - (μs.length + 1))! : ℝ)) *
          (a - (μ + μs.sum) / 2) ^ (k' + 1 - (μs.length + 1)) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero,
        show k' + 1 - (μs.length + 1) = k' - μs.length by omega, Nat.factorial_succ, Nat.cast_mul]
      have h2 : (2 : ℝ) ^ (μs.length + 1) = 2 ^ μs.length * 2 := pow_succ _ _
      rw [h2]
      have hne : (2 : ℝ) ^ μs.length ≠ 0 := by positivity
      field_simp
    rw [List.length_cons, List.prod_cons, List.sum_cons, ← hconst]
    have hfirst : ∫ _u in (0 : ℝ)..(μ / 2),
        ((k' + 1 : ℕ) : ℝ) * (μs.prod / 2 ^ μs.length * ((k' ! : ℝ) / ((k' - μs.length)! : ℝ)) *
          (a - (μ + μs.sum) / 2) ^ (k' - μs.length)) ≤
        ∫ u in (0 : ℝ)..(μ / 2),
          listDiff μs (fun x => ((k' + 1 : ℕ) : ℝ) * x ^ (k' + 1 - 1)) (a - u) := by
      refine intervalIntegral.integral_mono_on hμ2 intervalIntegrable_const
        (hcont.intervalIntegrable 0 (μ / 2)) fun u hu => ?_
      rw [hfn, listDiff_const_mul]
      have hau : μs.sum ≤ a - u := by linarith [hu.2]
      have hih := ih hμ.2 k' hk' (a - u) hau
      have hsum_nn : 0 ≤ μs.sum := List.sum_nonneg fun x hx => (hμ.2 x hx).le
      have hbase : 0 ≤ a - (μ + μs.sum) / 2 := by linarith [hμ.1, hu.2]
      have hpow_le : (a - (μ + μs.sum) / 2) ^ (k' - μs.length) ≤
          (a - u - μs.sum / 2) ^ (k' - μs.length) :=
        pow_le_pow_left₀ hbase (by linarith [hu.2]) _
      have hprod_nn : 0 ≤ μs.prod / 2 ^ μs.length :=
        div_nonneg (List.prod_nonneg fun x hx => (hμ.2 x hx).le) (by positivity)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc μs.prod / 2 ^ μs.length * ((k' ! : ℝ) / ((k' - μs.length)! : ℝ)) *
            (a - (μ + μs.sum) / 2) ^ (k' - μs.length)
          ≤ μs.prod / 2 ^ μs.length * ((k' ! : ℝ) / ((k' - μs.length)! : ℝ)) *
            (a - u - μs.sum / 2) ^ (k' - μs.length) := by gcongr
        _ ≤ listDiff μs (fun y => y ^ k') (a - u) := hih
    linarith

/-- **Taylor-term lower bound for `V`** (paper, proof of `vlo:S1`): for `S ≤ a`, `0 < a` and every
`j : ℕ` there is `c > 0` with `c t^{w - 1 + (m + j)} ≤ V(t)` for all `t ≥ 0`. -/
theorem cardyV_ge_pow (prob : FixedWeightProblem) {a : ℝ} (ha : prob.totalShift ≤ a)
    (ha0 : 0 < a) (j : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
      c * t ^ ((prob.w - 1) + (prob.m + j)) ≤ prob.cardyV a t := by
  have hw := prob.hw
  have hsum_eq : (List.ofFn prob.μ).sum = prob.totalShift := by
    unfold FixedWeightProblem.totalShift; rw [List.sum_ofFn]
  have hprod_eq : (List.ofFn prob.μ).prod = ∏ l : Fin prob.m, prob.μ l := by
    rw [List.prod_ofFn]
  have hμ_list : ∀ ν ∈ List.ofFn prob.μ, 0 < ν := by
    intro ν hν; rw [List.mem_ofFn] at hν; rcases hν with ⟨l, rfl⟩; exact prob.hμ l
  have hprod_pos : 0 < ∏ l : Fin prob.m, prob.μ l := Finset.prod_pos fun l _ => prob.hμ l
  have hS_nn : 0 ≤ prob.totalShift := prob.totalShift_nonneg
  have hbase : 0 < a - prob.totalShift / 2 := by linarith
  let k : ℕ := prob.m + j
  let c : ℝ := (2 * Real.pi) ^ (prob.w - 1) * (4 * Real.pi ^ 2) ^ k *
    ((∏ l : Fin prob.m, prob.μ l) / 2 ^ prob.m) * (a - prob.totalShift / 2) ^ j /
      (((k + prob.w - 1)! : ℝ) * (j ! : ℝ))
  have hc_pos : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc_pos, fun t ht => ?_⟩
  have hterm_nn : ∀ i : ℕ, 0 ≤
      ((4 * Real.pi ^ 2 * t) ^ i / ((i ! : ℝ) * ((i + prob.w - 1)! : ℝ))) *
        listDiff (List.ofFn prob.μ) (fun α => α ^ i) a := fun i =>
    mul_nonneg (div_nonneg (pow_nonneg (by positivity) i) (by positivity))
      (listDiff_pow_nonneg _ hμ_list i (hsum_eq.symm ▸ ha))
  have hk_term := (summable_cardyV_tsum prob ha ht).le_tsum k (fun i _ => hterm_nn i)
  have hk_ge := listDiff_pow_ge_half (List.ofFn prob.μ) hμ_list k
    (by simp [k]) a (hsum_eq.symm ▸ ha)
  rw [List.length_ofFn, hprod_eq, hsum_eq, show k - prob.m = j by simp [k]] at hk_ge
  rw [prob.cardyV_eq_tsum]
  have h1 := mul_le_mul_of_nonneg_left hk_term
    (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi * t) (prob.w - 1))
  refine le_trans ?_ h1
  have h2 : (2 * Real.pi * t) ^ (prob.w - 1) *
      (((4 * Real.pi ^ 2 * t) ^ k / ((k ! : ℝ) * ((k + prob.w - 1)! : ℝ))) *
        ((∏ l : Fin prob.m, prob.μ l) / 2 ^ prob.m * ((k ! : ℝ) / (j ! : ℝ)) *
          (a - prob.totalShift / 2) ^ j)) ≤
      (2 * Real.pi * t) ^ (prob.w - 1) *
        (((4 * Real.pi ^ 2 * t) ^ k / ((k ! : ℝ) * ((k + prob.w - 1)! : ℝ))) *
          listDiff (List.ofFn prob.μ) (fun α => α ^ k) a) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk_ge ?_)
      (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi * t) (prob.w - 1))
    exact div_nonneg (pow_nonneg (by positivity) k) (by positivity)
  refine le_trans (le_of_eq ?_) h2
  dsimp [c]
  have hk_ne : (k ! : ℝ) ≠ 0 := by positivity
  have hkw_ne : ((k + prob.w - 1)! : ℝ) ≠ 0 := by positivity
  have hj_ne : (j ! : ℝ) ≠ 0 := by positivity
  rw [mul_pow, mul_pow, pow_add]
  field_simp
  ring

/-- `V` dominates every real power on `[1, ∞)` up to a constant: the property
`∀ r, ∃ C, ∀ t ≥ 1, t^r ≤ C V(t)` used for the Mellin tail. -/
def PolyDom (V : ℝ → ℝ) : Prop :=
  ∀ r : ℝ, ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → t ^ r ≤ C * V t

/-- **Growth input of `vlo:S1`**: for `S ≤ a`, `0 < a`, `V = prob.cardyV a` dominates every real
power on `[1, ∞)`. -/
theorem polyDom_cardyV (prob : FixedWeightProblem) {a : ℝ} (ha : prob.totalShift ≤ a)
    (ha0 : 0 < a) : PolyDom (prob.cardyV a) := by
  intro r
  obtain ⟨c, hc, hV⟩ := cardyV_ge_pow prob ha ha0 ⌈r⌉₊
  refine ⟨c⁻¹, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := by linarith
  have hn : r ≤ (((prob.w - 1) + (prob.m + ⌈r⌉₊) : ℕ) : ℝ) := by
    have h1 : r ≤ (⌈r⌉₊ : ℝ) := Nat.le_ceil r
    have h2 : (⌈r⌉₊ : ℝ) ≤ (((prob.w - 1) + (prob.m + ⌈r⌉₊) : ℕ) : ℝ) := by
      exact_mod_cast (by omega : ⌈r⌉₊ ≤ (prob.w - 1) + (prob.m + ⌈r⌉₊))
    linarith
  have h1 : t ^ r ≤ t ^ (((prob.w - 1) + (prob.m + ⌈r⌉₊) : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le ht hn
  rw [Real.rpow_natCast] at h1
  have h2 := hV t ht0
  refine h1.trans ?_
  exact (le_inv_mul_iff₀ hc).2 h2

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.polyDom_cardyV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeightBand.polyDom_cardyV

end FormalResearch.ModularBootstrap.FixedWeightBand
