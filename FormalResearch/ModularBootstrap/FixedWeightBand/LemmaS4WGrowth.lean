module

public import FormalResearch.ModularBootstrap.FixedWeightBand.MellinConvergenceW
public import FormalResearch.ModularBootstrap.WeightAxioms.KernelAndPositivity
public import FormalResearch.CohnElkies.MellinKernel

/-!
# Growth of the Mellin Density in `Re z ≥ 1/2` at Weight `w` (growth step of `vlo:S4`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J2, Lemma S4 (`vlo:S4`), proof: "Put
`n = ⌈Re z⌉`.  The Taylor term of order `n` of `K_a^{(w)}` used in the proof of `vlo:S1` gives, for
`t ≥ 1`, `t^{Re z - 1} ≤ C_{c'} n! Γ(n+w) (4π² a)^{-n} V(t)`, while `∫₀¹ |g| t^{Re z - 1} dt ≤ 2 C_1 M[g]`
by `vlo:W1`; hence `|Mg(z)|/M[g] ≤ exp(O_{c'}((1+|z|) log(2+|z|)))`.  The gamma factor obeys the same
growth bound."

The `j`-dependence of the constant in `MellinGrowthW.cardyV_ge_pow` is existential, so the explicit
form is reproved here:

* `cardyV_ge_pow_explicit`: `V(t) ≥ c_j t^{w-1+m+j}` with
  `c_j = A E^j / ((m+j+w-1)! j!)`, `A = (2π)^{w-1}(4π²)^m (∏ μ)/2^m`, `E = 4π²(a - S/2)`
  (the Taylor term of order `m + j` of the `m`-fold difference, see `listDiff_pow_ge_half`);
* `rpow_le_exp_mul_cardyV`: `t^{r-1} ≤ exp(K (1+r)²) V(t)` for `t ≥ 1`, `r ≥ 0`;
* `norm_mellinMGW_le_exp`: `|m_g(z)| ≤ M[g] exp(K (1+|z|)²)` for `Re z ≥ 1/2`, every
  `g ∈ TestClass prob a`, with `K` depending only on `prob` and `a`.

Relation to the paper text: the paper obtains `t^{Re z-1} ≤ C_{c'} n! Γ(n+w) (4π² a)^{-n} V(t)` from the
Taylor term of order `n` of `K_a^{(w)}` and the comparison `V ≥ K_a^{(w)}/(C_K c'^{p_K})` (W2).  Here the
Taylor term is taken directly for the `m`-fold difference `V` (order `m + j`, via the half-step Peano
bound), which needs no W2 input; only constants change.  The growth proved is the cruder
`exp(K (1+|z|)²)` (from `n^n ≤ e^{n²}`) instead of `exp(O((1+|z|) log(2+|z|)))`, which still suffices on
the strip, where `|z| = O(1 + |Im ζ|²)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing Bessel WeightAxioms

/-! ### Section 1: Explicit Taylor-term lower bound for `V` -/

/-- **Explicit Taylor-term lower bound for `V`** (paper, proof of `vlo:S1`/`vlo:S4`): for `S ≤ a`,
`0 < a`, `j : ℕ` and `t ≥ 0`,
`A E^j / ((m+j+w-1)! j!) · t^{w-1+(m+j)} ≤ V(t)`. -/
theorem cardyV_ge_pow_explicit (prob : FixedWeightProblem) {a : ℝ} (ha : prob.totalShift ≤ a)
    (ha0 : 0 < a) (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ((2 * Real.pi) ^ (prob.w - 1) * (4 * Real.pi ^ 2) ^ prob.m *
        ((∏ l : Fin prob.m, prob.μ l) / 2 ^ prob.m)) *
      (4 * Real.pi ^ 2 * (a - prob.totalShift / 2)) ^ j /
        (((prob.m + j + prob.w - 1)! : ℝ) * (j ! : ℝ)) *
      t ^ ((prob.w - 1) + (prob.m + j)) ≤ prob.cardyV a t := by
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
  have hk_ne : (k ! : ℝ) ≠ 0 := by positivity
  have hkw_ne : ((k + prob.w - 1)! : ℝ) ≠ 0 := by positivity
  have hj_ne : (j ! : ℝ) ≠ 0 := by positivity
  have hk_eq : prob.m + j + prob.w - 1 = k + prob.w - 1 := rfl
  rw [hk_eq, mul_pow, mul_pow, mul_pow, pow_add, pow_add, mul_pow]
  field_simp
  ring

/-! ### Section 2: Polynomial domination with explicit growth of the constant -/

lemma factorial_mul_factorial_le_exp {N j : ℕ} (hj : j ≤ N) :
    ((N ! : ℝ) * (j ! : ℝ)) ≤ Real.exp (2 * (N : ℝ) ^ 2) := by
  have h1 : (j ! : ℝ) ≤ (N ! : ℝ) := by exact_mod_cast Nat.factorial_le hj
  have h2 : (N ! : ℝ) ≤ Real.exp ((N : ℝ) ^ 2) := by
    have h3 : (N ! : ℝ) ≤ ((N : ℝ)) ^ N := by exact_mod_cast Nat.factorial_le_pow N
    have h4 : (N : ℝ) ≤ Real.exp N := by
      have := Real.add_one_le_exp (N : ℝ)
      linarith
    have h5 : ((N : ℝ)) ^ N ≤ (Real.exp N) ^ N := by gcongr
    have h6 : (Real.exp N) ^ N = Real.exp ((N : ℝ) ^ 2) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    exact h3.trans (h5.trans_eq h6)
  calc (N ! : ℝ) * (j ! : ℝ) ≤ (N ! : ℝ) * (N ! : ℝ) := by
        gcongr
    _ ≤ Real.exp ((N : ℝ) ^ 2) * Real.exp ((N : ℝ) ^ 2) := by gcongr
    _ = Real.exp (2 * (N : ℝ) ^ 2) := by rw [← Real.exp_add]; congr 1; ring

lemma inv_le_exp_abs_log {x : ℝ} (hx : 0 < x) : x⁻¹ ≤ Real.exp |Real.log x| := by
  rw [← Real.exp_log (inv_pos.mpr hx), Real.log_inv]
  exact Real.exp_le_exp.mpr (neg_le_abs _)

/-- Arithmetic of the inverse Taylor constant: `F A⁻¹ (E⁻¹)^j ≤ exp(K (1+r)²)`. -/
lemma inv_coeff_le_exp {A E F q r : ℝ} {j : ℕ} (hA : 0 < A) (hE : 0 < E)
    (hF : F ≤ Real.exp (2 * q ^ 2 * (1 + r) ^ 2)) (hr1 : (1 : ℝ) ≤ (1 + r) ^ 2)
    (hj : (j : ℝ) ≤ (1 + r) ^ 2) :
    F * A⁻¹ * (E⁻¹) ^ j ≤
      Real.exp ((|Real.log A| + |Real.log E| + 2 * q ^ 2) * (1 + r) ^ 2) := by
  have hA_le : A⁻¹ ≤ Real.exp (|Real.log A| * (1 + r) ^ 2) :=
    (inv_le_exp_abs_log hA).trans (Real.exp_le_exp.mpr
      (le_mul_of_one_le_right (abs_nonneg _) hr1))
  have hE_le : (E⁻¹) ^ j ≤ Real.exp (|Real.log E| * (1 + r) ^ 2) := by
    have h1 : E⁻¹ ≤ Real.exp |Real.log E| := inv_le_exp_abs_log hE
    calc (E⁻¹) ^ j ≤ (Real.exp |Real.log E|) ^ j := by gcongr
      _ = Real.exp ((j : ℝ) * |Real.log E|) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (|Real.log E| * (1 + r) ^ 2) := by
          refine Real.exp_le_exp.mpr ?_
          calc (j : ℝ) * |Real.log E| ≤ (1 + r) ^ 2 * |Real.log E| :=
                mul_le_mul_of_nonneg_right hj (abs_nonneg _)
            _ = |Real.log E| * (1 + r) ^ 2 := mul_comm _ _
  calc F * A⁻¹ * (E⁻¹) ^ j
      ≤ Real.exp (2 * q ^ 2 * (1 + r) ^ 2) * Real.exp (|Real.log A| * (1 + r) ^ 2) *
          Real.exp (|Real.log E| * (1 + r) ^ 2) := by gcongr
    _ = Real.exp ((|Real.log A| + |Real.log E| + 2 * q ^ 2) * (1 + r) ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- **Polynomial domination of the tail with explicit growth** (`vlo:S4`, growth step): for
`S ≤ a`, `0 < a` there is `K ≥ 0` with `t^{r-1} ≤ exp(K (1+r)²) V(t)` for all `t ≥ 1`, `r ≥ 0`. -/
theorem rpow_le_exp_mul_cardyV (prob : FixedWeightProblem) {a : ℝ} (ha : prob.totalShift ≤ a)
    (ha0 : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {r : ℝ}, 0 ≤ r → ∀ {t : ℝ}, 1 ≤ t →
      t ^ (r - 1) ≤ Real.exp (K * (1 + r) ^ 2) * prob.cardyV a t := by
  have hw := prob.hw
  have hS_nn : 0 ≤ prob.totalShift := prob.totalShift_nonneg
  have hbase : 0 < a - prob.totalShift / 2 := by linarith
  have hP : 0 < ∏ l : Fin prob.m, prob.μ l := Finset.prod_pos fun l _ => prob.hμ l
  set A : ℝ := (2 * Real.pi) ^ (prob.w - 1) * (4 * Real.pi ^ 2) ^ prob.m *
    ((∏ l : Fin prob.m, prob.μ l) / 2 ^ prob.m) with hA_def
  have hA : 0 < A := by positivity
  set E : ℝ := 4 * Real.pi ^ 2 * (a - prob.totalShift / 2) with hE_def
  have hE : 0 < E := by positivity
  set q : ℝ := (prob.m : ℝ) + (prob.w : ℝ) + 1 with hq_def
  have hq1 : 1 ≤ q := by
    have : (0 : ℝ) ≤ prob.m := Nat.cast_nonneg _
    have : (1 : ℝ) ≤ prob.w := by exact_mod_cast hw
    linarith
  refine ⟨|Real.log A| + |Real.log E| + 2 * q ^ 2, by positivity, fun {r} hr {t} ht => ?_⟩
  have ht0 : 0 ≤ t := by linarith
  set j : ℕ := ⌈r⌉₊ with hj_def
  have hj_le : (j : ℝ) ≤ r + 1 := (Nat.ceil_lt_add_one hr).le
  have hr_le : r ≤ (j : ℝ) := Nat.le_ceil r
  set N : ℕ := prob.m + j + prob.w - 1 with hN_def
  have hjN : j ≤ N := by omega
  have hN : (N : ℝ) ≤ q * (1 + r) := by
    have h1 : (N : ℝ) ≤ ((prob.m + j + prob.w : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le _ _
    push_cast at h1
    have hm0 : (0 : ℝ) ≤ prob.m := Nat.cast_nonneg _
    have hw0 : (0 : ℝ) ≤ prob.w := Nat.cast_nonneg _
    have hr0 := hr
    nlinarith
  have hpow := cardyV_ge_pow_explicit prob ha ha0 j ht0
  set F : ℝ := ((N ! : ℝ) * (j ! : ℝ)) with hF_def
  have hF_pos : 0 < F := by positivity
  have hc_pos : 0 < A * E ^ j / F := by positivity
  have hexp_le : t ^ (r - 1) ≤ t ^ ((prob.w - 1) + (prob.m + j)) := by
    have hexp : r - 1 ≤ (((prob.w - 1) + (prob.m + j) : ℕ) : ℝ) := by
      have h2 : (j : ℝ) ≤ (((prob.w - 1) + (prob.m + j) : ℕ) : ℝ) := by
        exact_mod_cast (by omega : j ≤ (prob.w - 1) + (prob.m + j))
      linarith
    have := Real.rpow_le_rpow_of_exponent_le ht hexp
    rwa [Real.rpow_natCast] at this
  have h1 : t ^ (r - 1) ≤ (A * E ^ j / F)⁻¹ * prob.cardyV a t := by
    refine hexp_le.trans ?_
    rw [← div_eq_inv_mul, le_div_iff₀ hc_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc, F, N, A, E] using hpow
  refine h1.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (prob.cardyV_nonneg ha ht0)
  have hV0 : 0 ≤ prob.cardyV a t := prob.cardyV_nonneg ha ht0
  have hcinv : (A * E ^ j / F)⁻¹ = F * A⁻¹ * (E⁻¹) ^ j := by
    rw [inv_pow]
    field_simp
  rw [hcinv]
  have hr1 : (1 : ℝ) ≤ (1 + r) ^ 2 := by nlinarith
  have hjsq : (j : ℝ) ≤ (1 + r) ^ 2 := by nlinarith
  have hF_le : F ≤ Real.exp (2 * q ^ 2 * (1 + r) ^ 2) := by
    refine (factorial_mul_factorial_le_exp hjN).trans (Real.exp_le_exp.mpr ?_)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have h2 : (N : ℝ) ^ 2 ≤ (q * (1 + r)) ^ 2 := by gcongr
    calc 2 * (N : ℝ) ^ 2 ≤ 2 * (q * (1 + r)) ^ 2 := by gcongr
      _ = 2 * q ^ 2 * (1 + r) ^ 2 := by ring
  exact inv_coeff_le_exp hA hE hF_le hr1 hjsq

/-! ### Section 3: The factors `(2π)^z`, `1/Γ(z)` -/

lemma two_pi_lt_exp_two : 2 * Real.pi < Real.exp 2 := by
  have h1 := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  nlinarith [Real.pi_lt_d2]

lemma log_two_pi_le_two : Real.log (2 * Real.pi) ≤ 2 :=
  ((Real.log_lt_iff_lt_exp (by positivity)).mpr two_pi_lt_exp_two).le

lemma norm_two_pi_cpow_le {z : ℂ} (hz : 0 ≤ z.re) :
    ‖(2 * (Real.pi : ℂ)) ^ z‖ ≤ Real.exp (2 * ‖z‖) := by
  have h2pi_pos : 0 < 2 * Real.pi := by positivity
  rw [show (2 * (Real.pi : ℂ)) ^ z = ((2 * Real.pi : ℝ) : ℂ) ^ z by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos h2pi_pos, Real.rpow_def_of_pos h2pi_pos]
  refine Real.exp_le_exp.mpr ?_
  calc Real.log (2 * Real.pi) * z.re ≤ 2 * z.re :=
        mul_le_mul_of_nonneg_right log_two_pi_le_two hz
    _ ≤ 2 * ‖z‖ := by gcongr; exact Complex.re_le_norm z

/-- Growth of `1/Γ` in `Re z ≥ 1/2` (Stirling with the Binet remainder). -/
lemma norm_gamma_inv_le {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    ‖(Complex.Gamma z)⁻¹‖ ≤ Real.exp (9 * (1 + ‖z‖) ^ 2) := by
  have hz_pos : 0 < z.re := by linarith
  have hz_norm_ge : 1 / 2 ≤ ‖z‖ := hz.trans (Complex.re_le_norm z)
  have hz_norm_pos : 0 < ‖z‖ := by linarith
  have h2pi_pos : 0 < 2 * Real.pi := by positivity
  have hgam_eq := FormalResearch.CohnElkies.exp_stirling_add_binetRem_eq_gamma hz_pos
  have hbin_bd : ‖FormalResearch.Asymptotics.binetRem z‖ ≤ 4 := by
    rw [FormalResearch.CohnElkies.binetRem_eq_binetB hz_pos]
    calc ‖FormalResearch.Special.ComplexStirling.binetB z‖
        ≤ 2 / ‖z‖ := FormalResearch.Special.ComplexStirling.norm_binetB_le_div hz_pos
      _ ≤ 2 / (1 / 2) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hz_norm_ge
      _ = 4 := by norm_num
  have hlogz_bd : ‖Complex.log z‖ ≤ 5 + ‖z‖ := by
    have h1 : ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    rw [Complex.log_re, Complex.log_im] at h1
    have harg : |z.arg| ≤ Real.pi := Complex.abs_arg_le_pi z
    have hlog_abs : |Real.log ‖z‖| ≤ 1 + ‖z‖ := by
      rcases le_or_gt 1 ‖z‖ with hge1 | hlt1
      · rw [abs_of_nonneg (Real.log_nonneg hge1)]
        have := Real.log_le_sub_one_of_pos hz_norm_pos
        linarith
      · rw [abs_of_nonpos (Real.log_nonpos hz_norm_pos.le hlt1.le)]
        have hinv : Real.log ‖z‖⁻¹ ≤ Real.log 2 :=
          Real.log_le_log (inv_pos.mpr hz_norm_pos)
            (by rw [inv_le_comm₀ hz_norm_pos two_pos]; linarith)
        rw [Real.log_inv] at hinv
        have hlog2 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          linarith
        linarith
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    linarith
  have hgam_inv_norm : ‖(Complex.Gamma z)⁻¹‖ ≤
      Real.exp (‖(z - 1 / 2) * Complex.log z‖ + ‖z‖ + |Real.log (2 * Real.pi) / 2| + 4) := by
    rw [← hgam_eq, ← Complex.exp_neg, Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    rw [Complex.neg_re]
    have hre_le := Complex.abs_re_le_norm
      ((z - 1 / 2) * Complex.log z - z + ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) +
        FormalResearch.Asymptotics.binetRem z)
    have htri : ‖(z - 1 / 2) * Complex.log z - z + ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) +
          FormalResearch.Asymptotics.binetRem z‖ ≤
        ‖(z - 1 / 2) * Complex.log z‖ + ‖z‖ + |Real.log (2 * Real.pi) / 2| + 4 := by
      have ht1 := norm_add_le
        ((z - 1 / 2) * Complex.log z - z + ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ))
        (FormalResearch.Asymptotics.binetRem z)
      have ht2 := norm_add_le
        ((z - 1 / 2) * Complex.log z - z)
        ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ)
      have ht3 := norm_sub_le ((z - 1 / 2) * Complex.log z) z
      rw [Complex.norm_real, Real.norm_eq_abs] at ht2
      linarith
    linarith [(abs_le.mp hre_le).1]
  refine hgam_inv_norm.trans (Real.exp_le_exp.mpr ?_)
  have hz12 : ‖z - 1 / 2‖ ≤ ‖z‖ + 1 / 2 :=
    (norm_sub_le z (1 / 2 : ℂ)).trans (by norm_num)
  have hmul : ‖(z - 1 / 2) * Complex.log z‖ ≤ (‖z‖ + 1 / 2) * (5 + ‖z‖) := by
    rw [norm_mul]
    exact mul_le_mul hz12 hlogz_bd (norm_nonneg _) (by positivity)
  have hlog2pi_le : |Real.log (2 * Real.pi) / 2| ≤ 2 := by
    have hpos : 0 ≤ Real.log (2 * Real.pi) / 2 := by
      have : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      exact div_nonneg (Real.log_nonneg this) (by norm_num)
    rw [abs_of_nonneg hpos]
    linarith [log_two_pi_le_two]
  nlinarith [norm_nonneg z]

/-! ### Section 4: Growth of `m_g` in `Re z ≥ 1/2` -/

/-- **Growth of the Mellin density** (`vlo:S4`, growth step): for `S ≤ a`, `0 < a` there is `K ≥ 0`
(depending only on `prob` and `a`) with
`‖m_g(z)‖ ≤ M[g] exp(K (1 + ‖z‖)²)` for every `g ∈ TestClass prob a` and `Re z ≥ 1/2`. -/
theorem norm_mellinMGW_le_exp (prob : FixedWeightProblem) {a : ℝ} (ha : prob.totalShift ≤ a)
    (ha0 : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {g : ℝ → ℝ}, TestClass prob a g → ∀ {z : ℂ}, 1 / 2 ≤ z.re →
      ‖mellinMGW g z‖ ≤ prob.cardyNorm a g * Real.exp (K * (1 + ‖z‖) ^ 2) := by
  obtain ⟨C_int, C_1, hCint, hC1, hwin⟩ := testClass_window_bounds prob
  obtain ⟨K_t, hKt, htail⟩ := rpow_le_exp_mul_cardyV prob ha ha0
  refine ⟨11 + 2 * C_1 + K_t, by positivity, fun {g} hg {z} hz => ?_⟩
  have hM_nn : 0 ≤ prob.cardyNorm a g := prob.cardyNorm_nonneg ha g
  have hz_pos : 0 < z.re := by linarith
  have hz_norm : z.re ≤ ‖z‖ := Complex.re_le_norm z
  have hint_all := TestClass.integrableOn_mellin ha ha0 hg hz_pos
  have hint_head : IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioc 0 1) :=
    hint_all.mono_set Ioc_subset_Ioi_self
  have hint_tail : IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioi 1) :=
    hint_all.mono_set (Ioi_subset_Ioi zero_le_one)
  have hsplit : mellinTransformW g z =
      (∫ t in Ioc (0 : ℝ) 1, (g t : ℂ) * (t : ℂ) ^ (z - 1)) +
        (∫ t in Ioi (1 : ℝ), (g t : ℂ) * (t : ℂ) ^ (z - 1)) := by
    unfold mellinTransformW
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1),
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hint_head hint_tail]
  -- head: `∫₀¹ |g| t^{r-1} ≤ C_1 M / r ≤ 2 C_1 M`
  have hhead_bd : ‖∫ t in Ioc (0 : ℝ) 1, (g t : ℂ) * (t : ℂ) ^ (z - 1)‖ ≤
      2 * C_1 * prob.cardyNorm a g := by
    have h1 : ‖∫ t in Ioc (0 : ℝ) 1, (g t : ℂ) * (t : ℂ) ^ (z - 1)‖ ≤
        ∫ t in Ioc (0 : ℝ) 1, ‖(g t : ℂ) * (t : ℂ) ^ (z - 1)‖ :=
      norm_integral_le_integral_norm _
    have hrpow_int : IntegrableOn (fun t : ℝ => t ^ (z.re - 1)) (Ioc 0 1) :=
      integrableOn_rpow_sub_one_Ioc hz_pos
    have hrpow_val : ∫ t in Ioc (0 : ℝ) 1, t ^ (z.re - 1) = 1 / z.re := by
      rw [← intervalIntegral.integral_of_le zero_le_one,
        integral_rpow (Or.inl (by linarith : -1 < z.re - 1))]
      simp only [sub_add_cancel, Real.one_rpow, Real.zero_rpow hz_pos.ne', sub_zero, one_div]
    have h2 : ∫ t in Ioc (0 : ℝ) 1, ‖(g t : ℂ) * (t : ℂ) ^ (z - 1)‖ ≤
        ∫ t in Ioc (0 : ℝ) 1, (C_1 * prob.cardyNorm a g) * t ^ (z.re - 1) := by
      refine setIntegral_mono_on hint_head.norm (hrpow_int.const_mul _) measurableSet_Ioc
        fun t ht => ?_
      rw [norm_mellin_integrand_eq ht.1 z]
      exact mul_le_mul_of_nonneg_right ((hwin ha hg).2 ht.1.le) (Real.rpow_nonneg ht.1.le _)
    have h3 : ∫ t in Ioc (0 : ℝ) 1, (C_1 * prob.cardyNorm a g) * t ^ (z.re - 1) =
        (C_1 * prob.cardyNorm a g) / z.re := by
      rw [integral_const_mul, hrpow_val]; ring
    have h4 : (C_1 * prob.cardyNorm a g) / z.re ≤ 2 * C_1 * prob.cardyNorm a g := by
      rw [div_le_iff₀ hz_pos]
      have hnn : 0 ≤ C_1 * prob.cardyNorm a g := by positivity
      calc C_1 * prob.cardyNorm a g = 2 * C_1 * prob.cardyNorm a g * (1 / 2) := by ring
        _ ≤ 2 * C_1 * prob.cardyNorm a g * z.re := by gcongr
    linarith
  -- tail: `∫₁^∞ |g| t^{r-1} ≤ exp(K_t (1+r)²) M`
  have htail_bd : ‖∫ t in Ioi (1 : ℝ), (g t : ℂ) * (t : ℂ) ^ (z - 1)‖ ≤
      Real.exp (K_t * (1 + z.re) ^ 2) * prob.cardyNorm a g := by
    have h1 : ‖∫ t in Ioi (1 : ℝ), (g t : ℂ) * (t : ℂ) ^ (z - 1)‖ ≤
        ∫ t in Ioi (1 : ℝ), ‖(g t : ℂ) * (t : ℂ) ^ (z - 1)‖ :=
      norm_integral_le_integral_norm _
    have hdom : IntegrableOn (fun t : ℝ => Real.exp (K_t * (1 + z.re) ^ 2) *
        (|g t| * prob.cardyV a t)) (Ioi 1) :=
      (hg.int_cardy.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul _
    have h2 : ∫ t in Ioi (1 : ℝ), ‖(g t : ℂ) * (t : ℂ) ^ (z - 1)‖ ≤
        ∫ t in Ioi (1 : ℝ), Real.exp (K_t * (1 + z.re) ^ 2) *
          (|g t| * prob.cardyV a t) := by
      refine setIntegral_mono_on hint_tail.norm hdom measurableSet_Ioi fun t ht => ?_
      have ht1 : 1 ≤ t := (mem_Ioi.mp ht).le
      have ht0 : 0 < t := by linarith
      rw [norm_mellin_integrand_eq ht0 z]
      have hrp := htail hz_pos.le ht1
      calc |g t| * t ^ (z.re - 1)
          ≤ |g t| * (Real.exp (K_t * (1 + z.re) ^ 2) * prob.cardyV a t) := by gcongr
        _ = Real.exp (K_t * (1 + z.re) ^ 2) * (|g t| * prob.cardyV a t) := by ring
    have h3 : ∫ t in Ioi (1 : ℝ), Real.exp (K_t * (1 + z.re) ^ 2) *
          (|g t| * prob.cardyV a t) ≤
        Real.exp (K_t * (1 + z.re) ^ 2) * prob.cardyNorm a g := by
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      refine setIntegral_mono_set hg.int_cardy ?_
        (Eventually.of_forall (Ioi_subset_Ioi zero_le_one))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (abs_nonneg _) (prob.cardyV_nonneg ha (mem_Ioi.mp ht).le)
    linarith
  have hMg_bd : ‖mellinTransformW g z‖ ≤
      prob.cardyNorm a g * Real.exp ((2 * C_1 + K_t) * (1 + ‖z‖) ^ 2) := by
    have hsq1 : (1 : ℝ) ≤ (1 + ‖z‖) ^ 2 := by nlinarith [norm_nonneg z]
    have hre_sq : (1 + z.re) ^ 2 ≤ (1 + ‖z‖) ^ 2 := by gcongr
    have hE_ge : (1 : ℝ) ≤ Real.exp (K_t * (1 + z.re) ^ 2) := Real.one_le_exp (by positivity)
    have hE_le : Real.exp (K_t * (1 + z.re) ^ 2) ≤ Real.exp (K_t * (1 + ‖z‖) ^ 2) :=
      Real.exp_le_exp.mpr (by gcongr)
    have hC1_exp : 2 * C_1 + 1 ≤ Real.exp (2 * C_1 * (1 + ‖z‖) ^ 2) := by
      have h1 := Real.add_one_le_exp (2 * C_1)
      have h2 : Real.exp (2 * C_1) ≤ Real.exp (2 * C_1 * (1 + ‖z‖) ^ 2) :=
        Real.exp_le_exp.mpr (le_mul_of_one_le_right (by positivity) hsq1)
      linarith
    rw [hsplit]
    calc ‖(∫ t in Ioc (0 : ℝ) 1, (g t : ℂ) * (t : ℂ) ^ (z - 1)) +
            (∫ t in Ioi (1 : ℝ), (g t : ℂ) * (t : ℂ) ^ (z - 1))‖
        ≤ ‖∫ t in Ioc (0 : ℝ) 1, (g t : ℂ) * (t : ℂ) ^ (z - 1)‖ +
            ‖∫ t in Ioi (1 : ℝ), (g t : ℂ) * (t : ℂ) ^ (z - 1)‖ := norm_add_le _ _
      _ ≤ 2 * C_1 * prob.cardyNorm a g +
            Real.exp (K_t * (1 + ‖z‖) ^ 2) * prob.cardyNorm a g := by
          have h3 : Real.exp (K_t * (1 + z.re) ^ 2) * prob.cardyNorm a g ≤
              Real.exp (K_t * (1 + ‖z‖) ^ 2) * prob.cardyNorm a g :=
            mul_le_mul_of_nonneg_right hE_le hM_nn
          linarith
      _ = (2 * C_1 + Real.exp (K_t * (1 + ‖z‖) ^ 2)) * prob.cardyNorm a g := by ring
      _ ≤ ((2 * C_1 + 1) * Real.exp (K_t * (1 + ‖z‖) ^ 2)) * prob.cardyNorm a g := by
          gcongr
          have := Real.one_le_exp (x := K_t * (1 + ‖z‖) ^ 2) (by positivity)
          nlinarith
      _ ≤ (Real.exp (2 * C_1 * (1 + ‖z‖) ^ 2) * Real.exp (K_t * (1 + ‖z‖) ^ 2)) *
            prob.cardyNorm a g := by gcongr
      _ = prob.cardyNorm a g * Real.exp ((2 * C_1 + K_t) * (1 + ‖z‖) ^ 2) := by
          rw [← Real.exp_add]; ring_nf
  have hpi := norm_two_pi_cpow_le (z := z) hz_pos.le
  have hgam := norm_gamma_inv_le hz
  unfold mellinMGW
  rw [div_eq_mul_inv, norm_mul, norm_mul]
  have hsq1 : (1 : ℝ) ≤ (1 + ‖z‖) ^ 2 := by nlinarith [norm_nonneg z]
  have h2z : 2 * ‖z‖ ≤ 2 * (1 + ‖z‖) ^ 2 := by nlinarith [norm_nonneg z]
  calc ‖(2 * (Real.pi : ℂ)) ^ z‖ * ‖mellinTransformW g z‖ * ‖(Complex.Gamma z)⁻¹‖
      ≤ Real.exp (2 * ‖z‖) *
          (prob.cardyNorm a g * Real.exp ((2 * C_1 + K_t) * (1 + ‖z‖) ^ 2)) *
          Real.exp (9 * (1 + ‖z‖) ^ 2) := by gcongr
    _ = prob.cardyNorm a g * Real.exp (2 * ‖z‖ + (2 * C_1 + K_t) * (1 + ‖z‖) ^ 2 +
          9 * (1 + ‖z‖) ^ 2) := by
        rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ prob.cardyNorm a g * Real.exp ((11 + 2 * C_1 + K_t) * (1 + ‖z‖) ^ 2) := by
        gcongr
        nlinarith

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.norm_mellinMGW_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeightBand.norm_mellinMGW_le_exp

end FormalResearch.ModularBootstrap.FixedWeightBand
