module

public import FormalResearch.ModularBootstrap.Bessel.IntegralRep

/-!
# The Virasoro kernel `K_α` and `V = K_a - 2 K_{a-1} + K_{a-2}`: Lemma B (a)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Lemma B (`vlo:Bessel`), part (a), and
the first line of the proof of (d).

`besselK α t = I₀(4π √(α t)) = Σ_k (4π² α t)^k / (k!)²` and `besselV a t = K_a - 2 K_{a-1} + K_{a-2}`.
Main results (all `proved`):

* `besselV_hasSum`, `besselVCoeff_nonneg`, `besselVCoeff_two`: `V(t) = Σ_{k ≥ 2} v_k t^k` with
  `v_k = (4π²)^k/(k!)² [a^k - 2 (a-1)^k + (a-2)^k] ≥ 0` and `v_2 = 8π⁴`;
* `besselV_strictMonoOn`, `besselV_ge`: `V` is (strictly) increasing on `t ≥ 0` and `V(t) ≥ 8π⁴ t²`;
* `besselV_ge_besselS2`: the lower bound `V(t) ≥ (4π² t)² S₂(4π²(a-2)t)`, i.e.
  `V(t) ≥ 4π² t/(a-2) · I₂(4π √((a-2) t))` of the proof of (d);
* `besselV_le_two_mul`: `V ≤ 2 K_a` (needed for `WeaklyFeasibleTest.hV_le_two_Ka`).
-/

@[expose] public section

open Real Filter Topology Finset
open scoped Nat

namespace FormalResearch.ModularBootstrap.Bessel

/-- The Virasoro kernel `K_α(t) = I₀(4π √(α t))` of `vlo:Bessel`. -/
noncomputable def besselK (α t : ℝ) : ℝ := besselI0 (4 * π * √(α * t))

/-- `V = K_a - 2 K_{a-1} + K_{a-2}` of `vlo:Bessel`. -/
noncomputable def besselV (a t : ℝ) : ℝ := besselK a t - 2 * besselK (a - 1) t + besselK (a - 2) t

/-- Coefficients `v_k = (4π²)^k/(k!)² [a^k - 2(a-1)^k + (a-2)^k]` of `V`. -/
noncomputable def besselVCoeff (a : ℝ) (k : ℕ) : ℝ :=
  (4 * π ^ 2) ^ k / ((k ! : ℝ) ^ 2) * (a ^ k - 2 * (a - 1) ^ k + (a - 2) ^ k)

lemma besselK_eq_besselS {α t : ℝ} (h : 0 ≤ α * t) : besselK α t = besselS 0 (4 * π ^ 2 * (α * t)) := by
  unfold besselK
  rw [besselI0_eq]
  congr 1
  rw [mul_pow, Real.sq_sqrt h]
  ring

/-- Bessel series of `K_α`: `K_α(t) = Σ_k (4π²αt)^k/(k!)²`. -/
theorem besselK_hasSum {α t : ℝ} (h : 0 ≤ α * t) :
    HasSum (fun k : ℕ => (4 * π ^ 2 * (α * t)) ^ k / ((k ! : ℝ) ^ 2)) (besselK α t) := by
  rw [besselK_eq_besselS h]
  have := besselS_hasSum 0 (y := 4 * π ^ 2 * (α * t)) (by positivity)
  convert this using 1
  ext k
  simp [besselTerm, sq]

lemma besselK_nonneg {α t : ℝ} : 0 ≤ besselK α t := by
  unfold besselK; exact (zero_le_one.trans (one_le_besselI0 _))

lemma besselK_mono_alpha {α β t : ℝ} (ht : 0 ≤ t) (h : α ≤ β) :
    besselK α t ≤ besselK β t := by
  unfold besselK
  apply besselI0_mono (by positivity)
  gcongr

/-- Second difference of `x ↦ x^{n+2}` at `b ≥ 0` is at least the second derivative at `b`:
`(b+2)^{n+2} - 2 (b+1)^{n+2} + b^{n+2} ≥ (n+2)(n+1) b^n`. -/
lemma second_difference_pow_ge {b : ℝ} (hb : 0 ≤ b) (n : ℕ) :
    ((n : ℝ) + 2) * ((n : ℝ) + 1) * b ^ n ≤ (b + 2) ^ (n + 2) - 2 * (b + 1) ^ (n + 2) + b ^ (n + 2) := by
  have bern : ∀ x : ℝ, 0 ≤ x → ∀ m : ℕ, x ^ (m + 1) + ((m : ℝ) + 1) * x ^ m ≤ (x + 1) ^ (m + 1) := by
    intro x hx m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 : 0 ≤ x ^ m := by positivity
      have h2 : 0 ≤ (m : ℝ) := by positivity
      calc x ^ (m + 1 + 1) + (((m + 1 : ℕ) : ℝ) + 1) * x ^ (m + 1)
          ≤ (x + 1) * (x ^ (m + 1) + ((m : ℝ) + 1) * x ^ m) := by
            push_cast; rw [pow_succ, pow_succ x (m)]; nlinarith [mul_nonneg h1 hx, mul_nonneg h1 h2]
        _ ≤ (x + 1) * (x + 1) ^ (m + 1) := by gcongr
        _ = (x + 1) ^ (m + 1 + 1) := by ring
  induction n with
  | zero => simp; nlinarith
  | succ n ih =>
    have e0 := bern (b + 1) (by linarith) (n + 1)
    have e : (b + 1) ^ (n + 2) + ((n : ℝ) + 2) * (b + 1) ^ (n + 1) ≤ (b + 2) ^ (n + 2) := by
      have e3 : (b + 1 + 1) = b + 2 := by ring
      rw [e3] at e0
      push_cast at e0
      convert e0 using 3; ring
    have hp : 0 ≤ b ^ (n + 1) := by positivity
    have e2 : (b + 1) ^ (n + 1) ≥ b ^ (n + 1) := by gcongr; linarith
    have key : (b + 2) ^ (n + 1 + 2) - 2 * (b + 1) ^ (n + 1 + 2) + b ^ (n + 1 + 2)
        = b * ((b + 2) ^ (n + 2) - 2 * (b + 1) ^ (n + 2) + b ^ (n + 2)) +
          2 * ((b + 2) ^ (n + 2) - (b + 1) ^ (n + 2)) := by ring
    rw [key]
    push_cast
    have h1 := mul_le_mul_of_nonneg_left ih hb
    have hn : (0 : ℝ) ≤ (n : ℝ) + 2 := by positivity
    have h2 := mul_le_mul_of_nonneg_left e2 hn
    have hb1 : b ^ (n + 1) = b ^ n * b := pow_succ b n
    rw [hb1] at h2 ⊢
    nlinarith

lemma besselV_bracket_ge {a : ℝ} (ha : 2 ≤ a) (n : ℕ) :
    ((n : ℝ) + 2) * ((n : ℝ) + 1) * (a - 2) ^ n ≤
      a ^ (n + 2) - 2 * (a - 1) ^ (n + 2) + (a - 2) ^ (n + 2) := by
  have := second_difference_pow_ge (b := a - 2) (by linarith) n
  convert this using 2
  ring_nf

lemma besselVCoeff_zero (a : ℝ) : besselVCoeff a 0 = 0 := by
  simp [besselVCoeff]; norm_num

lemma besselVCoeff_one (a : ℝ) : besselVCoeff a 1 = 0 := by
  simp [besselVCoeff]; ring

/-- **Lemma B (a), `v_2 = 8π⁴`.** -/
theorem besselVCoeff_two (a : ℝ) : besselVCoeff a 2 = 8 * π ^ 4 := by
  simp [besselVCoeff, Nat.factorial]; ring

/-- **Lemma B (a), `v_k ≥ 0`** (convexity of `α^k`), for `a ≥ 2`. -/
theorem besselVCoeff_nonneg {a : ℝ} (ha : 2 ≤ a) (k : ℕ) : 0 ≤ besselVCoeff a k := by
  rcases k with _ | _ | n
  · simp [besselVCoeff_zero]
  · simp [besselVCoeff_one]
  · unfold besselVCoeff
    have h := besselV_bracket_ge ha n
    have hp : 0 ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) * (a - 2) ^ n := by
      have : 0 ≤ a - 2 := by linarith
      positivity
    have : 0 ≤ a ^ (n + 1 + 1) - 2 * (a - 1) ^ (n + 1 + 1) + (a - 2) ^ (n + 1 + 1) := by
      simpa using hp.trans h
    positivity

/-- The coefficient lower bound `v_{n+2} ≥ (4π²)^{n+2} (n+2)(n+1)(a-2)^n/((n+2)!)²`
(second difference of `α^{n+2}` dominates the second derivative at `a - 2`). -/
lemma besselVCoeff_add_two_ge {a : ℝ} (ha : 2 ≤ a) (n : ℕ) :
    (4 * π ^ 2) ^ (n + 2) / (((n + 2)! : ℝ) ^ 2) * (((n : ℝ) + 2) * ((n : ℝ) + 1) * (a - 2) ^ n)
      ≤ besselVCoeff a (n + 2) := by
  unfold besselVCoeff
  gcongr
  exact besselV_bracket_ge ha n

/-- **Lemma B (a), series form.** For `a ≥ 2` and `t ≥ 0`,
`V(t) = Σ_k v_k t^k`, with `v_k = (4π²)^k/(k!)² [a^k - 2(a-1)^k + (a-2)^k]`
(and `v_0 = v_1 = 0`). -/
theorem besselV_hasSum {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) :
    HasSum (fun k : ℕ => besselVCoeff a k * t ^ k) (besselV a t) := by
  have h0 := besselK_hasSum (α := a) (t := t) (by positivity)
  have h1 := besselK_hasSum (α := a - 1) (t := t) (mul_nonneg (by linarith) ht)
  have h2 := besselK_hasSum (α := a - 2) (t := t) (mul_nonneg (by linarith) ht)
  have h := (h0.sub (h1.mul_left 2)).add h2
  unfold besselV
  convert h using 1
  ext k
  unfold besselVCoeff
  have hp : ∀ α : ℝ, (4 * π ^ 2 * (α * t)) ^ k = (4 * π ^ 2) ^ k * α ^ k * t ^ k := by
    intro α; ring
  simp only [hp]
  ring

/-- **Lemma B (a): `V` is strictly increasing on `t ≥ 0`.** -/
theorem besselV_strictMonoOn {a : ℝ} (ha : 2 ≤ a) : StrictMonoOn (besselV a) (Set.Ici 0) := by
  intro s hs t ht hst
  have hs' : 0 ≤ s := hs
  have ht' : 0 ≤ t := ht
  refine hasSum_lt (f := fun k : ℕ => besselVCoeff a k * s ^ k)
    (g := fun k : ℕ => besselVCoeff a k * t ^ k) (i := 2) (fun k => ?_) ?_
    (besselV_hasSum ha hs') (besselV_hasSum ha ht')
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs' hst.le k) (besselVCoeff_nonneg ha k)
  · simp only [besselVCoeff_two]
    have : 0 < π ^ 4 := by positivity
    have h2 : s ^ 2 < t ^ 2 := by gcongr
    nlinarith

/-- **Lemma B (a): `V` is increasing** (`t ≥ 0`). -/
theorem besselV_monotoneOn {a : ℝ} (ha : 2 ≤ a) : MonotoneOn (besselV a) (Set.Ici 0) :=
  (besselV_strictMonoOn ha).monotoneOn

/-- **Lemma B (a): `V(t) ≥ 8π⁴ t²`** for `a ≥ 2`, `t ≥ 0`. -/
theorem besselV_ge {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) : 8 * π ^ 4 * t ^ 2 ≤ besselV a t := by
  have := le_hasSum (besselV_hasSum ha ht) 2 (fun j _ => mul_nonneg (besselVCoeff_nonneg ha j)
    (pow_nonneg ht j))
  rwa [besselVCoeff_two] at this

/-- The lower bound `V(t) ≥ (4π²t)² S₂(4π²(a-2)t)` from the proof of Lemma B (d); in terms of
`I₂`, `V(t) ≥ 4π²t/(a-2) · I₂(4π√((a-2)t))` (see `besselV_ge_besselI2`). -/
theorem besselV_ge_besselS2 {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) :
    (4 * π ^ 2 * t) ^ 2 * besselS 2 (4 * π ^ 2 * (a - 2) * t) ≤ besselV a t := by
  have hy : 0 ≤ 4 * π ^ 2 * (a - 2) * t := by
    have : 0 ≤ a - 2 := by linarith
    positivity
  have hS := (besselS_hasSum 2 hy).mul_left ((4 * π ^ 2 * t) ^ 2)
  have hV := besselV_hasSum ha ht
  rw [← hasSum_nat_add_iff' 2] at hV
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, besselVCoeff_zero, besselVCoeff_one,
    zero_mul, zero_add, sub_zero] at hV
  refine hasSum_le (fun n => ?_) hS hV
  have h := besselVCoeff_add_two_ge ha n
  have htn : 0 ≤ t ^ (n + 2) := by positivity
  have h2 := mul_le_mul_of_nonneg_right h htn
  refine le_trans (le_of_eq ?_) h2
  unfold besselTerm
  have h3 : ((n + 2)! : ℝ) = ((n : ℝ) + 2) * ((n : ℝ) + 1) * (n ! : ℝ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have hn : (n ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hy' : (4 * π ^ 2 * (a - 2) * t) ^ n = (4 * π ^ 2) ^ n * (a - 2) ^ n * t ^ n := by
    rw [mul_pow, mul_pow]
  rw [hy', h3]
  have : ((n : ℝ) + 2) ≠ 0 := by positivity
  have : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- `V(t) ≥ 4π² t/(a-2) · I₂(4π√((a-2) t))` (`vlo:Bessel` (d), the "triangular second-difference"
lower bound). -/
theorem besselV_ge_besselI2 {a t : ℝ} (ha : 2 < a) (ht : 0 ≤ t) :
    4 * π ^ 2 * t / (a - 2) * besselI 2 (4 * π * √((a - 2) * t)) ≤ besselV a t := by
  refine le_trans (le_of_eq ?_) (besselV_ge_besselS2 ha.le ht)
  have h : 0 ≤ (a - 2) * t := mul_nonneg (by linarith) ht
  unfold besselI
  have hs : √((a - 2) * t) ^ 2 = (a - 2) * t := Real.sq_sqrt h
  have h1 : (4 * π * √((a - 2) * t) / 2) ^ 2 = 4 * π ^ 2 * (a - 2) * t := by
    rw [div_pow, mul_pow, mul_pow, hs]; ring
  have h3 : (4 * π * √((a - 2) * t)) ^ 2 / 4 = 4 * π ^ 2 * (a - 2) * t := by
    rw [mul_pow, mul_pow, hs]; ring
  rw [h1, h3]
  have : a - 2 ≠ 0 := by linarith
  field_simp

/-- **`V ≤ 2 K_a`** for `t ≥ 0` (`WeaklyFeasibleTest.hV_le_two_Ka`). -/
theorem besselV_le_two_mul {a t : ℝ} (ht : 0 ≤ t) :
    besselV a t ≤ 2 * besselK a t := by
  unfold besselV
  have h1 : 0 ≤ besselK (a - 1) t := besselK_nonneg
  have h2 : besselK (a - 2) t ≤ besselK a t := besselK_mono_alpha ht (by linarith)
  linarith

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselV_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselV_hasSum

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselVCoeff_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselVCoeff_two

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselVCoeff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselVCoeff_nonneg

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselV_strictMonoOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselV_strictMonoOn

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselV_monotoneOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselV_monotoneOn

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselV_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselV_ge

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselV_ge_besselI2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselV_ge_besselI2

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselV_le_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselV_le_two_mul

end FormalResearch.ModularBootstrap.Bessel
