module

public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.RingTheory.Binomial
public import Mathlib.Algebra.Polynomial.Smeval
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Power series of the Hankel Langer chart: Dirichlet eta coefficients (`lem:langer-chart`, (0))

Source: `CFT/sign_uncertainty/paper/langer_transport.tex`, Lemma 7.7b (0). The paper's `ηc j`
is `η_D(2j+2) = ∑_{n≥1} (-1)^{n-1} n^{-(2j+2)}`; here it is `etaC j`, written as the
alternating series `∑' n, (-1)^n * (1/(n+1)^(2j+2))` (the same series, reindexed from `n = 0`).

Contents and classes (all proved here; the Mathlib inputs are named in the proofs):
* `etaC_zero : etaC 0 = π²/12`, from `hasSum_zeta_two` by splitting into even and odd terms.
* `etaC_pos`, `etaC_lt_one`: `0 < etaC j < 1`, from the alternating-series partial-sum bounds.
  The exponent is `2j+2 ≥ 2` throughout. At exponent `1` the series is `log 2`, which is also in
  `(0,1)`, so the bounds themselves do not fail there; what needs exponent `≥ 2` is absolute
  convergence (`summable_inv_succ_pow`, the harmonic series diverges) and the value `π²/12`.
* `langerA k = (12/π²) etaC k / (k+1)` and `langerB k = (36/π²) etaC k / (2k+3)`, with
  `langerB 0 = 1`. For `k ≥ 1`: `0 < langerA k ≤ 6/π²` and `0 < langerB k ≤ 36/(5π²)`.
  These are the coefficients of `ε(z) = ∑_{j≥1} langerA j z^(2j)` in `(12/π²) g(z) = z²(1+ε(z))`
  and of `E(z) = ∑_{j≥0} langerB j z^(2j)` in `m(z)³ = z³E(z)`. The identities relating `g`, `ε`, `E`
  to `etaC` are NOT proved here (see below).
* Series bounds: `abs_eps_tsum_le`, `abs_E_sub_one_le` (general radius `r < 1`), and
  `abs_eps_le`, `abs_E_sub_one_le_035` (`‖z‖ ≤ 0.035`, giving `≤ 7.46·10⁻⁴` and `≤ 8.95·10⁻⁴`).
  Decimal constants `epsH_le`, `epsE_le` use `Real.pi_gt_d4`.
* `binomial_bound`: `‖(1+x)^α - 1‖ ≤ 1 - (1 - ‖x‖)^α` for `0 < α < 1`, `‖x‖ < 1`, principal power.
  Proved from `Complex.one_add_cpow_hasFPowerSeriesOnBall_zero` and the sign of the generalized
  binomial coefficients `Ring.choose α (m+1)`, which alternate with `m` (`choose_real_sign`).

Not proved here: the Langer series identity `g'(z) = π/sin(πz) - 1/z = 2∑ η_D(2j+2) z^(2j+1)`
(`hasDerivAt_gD_series` of the brief). The route is `π/sin(πz) = π cot(πz/2) - π cot(πz)` with
Mathlib's `cot_series_rep`, then the log-derivative of `tan`, then summation of the double series;
it was judged to exceed the brief's 300-line budget, so it is left open.
-/

@[expose] public section

open Finset Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- The Dirichlet eta value `η_D(2j+2)` as the alternating series
`∑_{n≥0} (-1)^n / (n+1)^(2j+2)`. -/
noncomputable def etaC (j : ℕ) : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1) ^ (2 * j + 2))

/-- `1/(n+1)^(2j+2)` is summable (exponent at least `2`). -/
lemma summable_inv_succ_pow (j : ℕ) :
    Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ (2 * j + 2)) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (show 1 < 2 * j + 2 by omega) :
      Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 * j + 2))
  simpa using h

lemma antitone_inv_succ_pow (j : ℕ) :
    Antitone (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ (2 * j + 2)) := by
  intro m n hmn
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  exact one_div_le_one_div_of_le (pow_pos hm _) (pow_le_pow_left₀ hm.le hmn' _)

lemma etaC_hasSum (j : ℕ) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1) ^ (2 * j + 2))) (etaC j) :=
  (summable_inv_succ_pow j).alternating.hasSum

/-- Partial sums of `etaC j` converge to it (alternating series test, from Mathlib). -/
lemma etaC_tendsto (j : ℕ) :
    Tendsto (fun N : ℕ => ∑ i ∈ range N, (-1 : ℝ) ^ i * (1 / ((i : ℝ) + 1) ^ (2 * j + 2)))
      atTop (𝓝 (etaC j)) :=
  (summable_inv_succ_pow j).tendsto_alternating_series_tsum

/-- The two-term and three-term bounds on `etaC j` for the exponent `2j+2 ≥ 2`. -/
lemma etaC_bounds (j : ℕ) :
    1 - 1 / (2 : ℝ) ^ (2 * j + 2) ≤ etaC j ∧
      etaC j ≤ 1 - 1 / (2 : ℝ) ^ (2 * j + 2) + 1 / (3 : ℝ) ^ (2 * j + 2) := by
  have hA := antitone_inv_succ_pow j
  have hT := etaC_tendsto j
  constructor
  · have := hA.alternating_series_le_tendsto hT 1
    norm_num [sum_range_succ] at this ⊢
    linarith
  · have := hA.tendsto_le_alternating_series hT 1
    norm_num [sum_range_succ] at this ⊢
    linarith

lemma etaC_pos (j : ℕ) : 0 < etaC j := by
  have h4 : (2 : ℝ) ^ 2 ≤ 2 ^ (2 * j + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hle : 1 / (2 : ℝ) ^ (2 * j + 2) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    norm_num at h4 ⊢
    linarith
  linarith [(etaC_bounds j).1]

lemma etaC_lt_one (j : ℕ) : etaC j < 1 := by
  have h : (1 : ℝ) / (3 : ℝ) ^ (2 * j + 2) < 1 / (2 : ℝ) ^ (2 * j + 2) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  linarith [(etaC_bounds j).2]

lemma hasSum_inv_succ_sq : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa using h

/-- `η_D(2) = π²/12`, from `ζ(2) = π²/6` by splitting the alternating series into even and odd
terms. -/
lemma etaC_zero : etaC 0 = π ^ 2 / 12 := by
  have hgs0 := hasSum_inv_succ_sq
  set g : ℕ → ℝ := fun n => (1 : ℝ) / ((n : ℝ) + 1) ^ 2 with hg
  have hgs : HasSum g (π ^ 2 / 6) := hgs0
  have hodd : HasSum (fun k : ℕ => g (2 * k + 1)) (π ^ 2 / 24) := by
    have h := hgs.mul_left (1 / 4 : ℝ)
    have e : (fun k : ℕ => g (2 * k + 1)) =
        fun k : ℕ => (1 / 4 : ℝ) * ((1 : ℝ) / ((k : ℝ) + 1) ^ 2) := by
      funext k
      simp only [hg]
      push_cast
      field_simp
      ring
    have e2 : π ^ 2 / 24 = 1 / 4 * (π ^ 2 / 6) := by ring
    rw [e, e2]
    exact h
  have hF : Summable (fun n : ℕ => (-1 : ℝ) ^ n * g n) := hgs.summable.alternating
  have heg : Summable (fun k : ℕ => g (2 * k)) :=
    hgs.summable.comp_injective (mul_right_injective₀ two_ne_zero)
  have hog : Summable (fun k : ℕ => g (2 * k + 1)) := hodd.summable
  have heF : Summable (fun k : ℕ => (-1 : ℝ) ^ (2 * k) * g (2 * k)) :=
    hF.comp_injective (mul_right_injective₀ two_ne_zero)
  have hoF : Summable (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) * g (2 * k + 1)) :=
    hF.comp_injective (fun a b (hab : 2 * a + 1 = 2 * b + 1) => by omega)
  have hsplitF : ∑' k : ℕ, (-1 : ℝ) ^ (2 * k) * g (2 * k)
      + ∑' k : ℕ, (-1 : ℝ) ^ (2 * k + 1) * g (2 * k + 1) = ∑' n : ℕ, (-1 : ℝ) ^ n * g n :=
    tsum_even_add_odd (f := fun n : ℕ => (-1 : ℝ) ^ n * g n) heF hoF
  have hsplitG : ∑' k : ℕ, g (2 * k) + ∑' k : ℕ, g (2 * k + 1) = ∑' n : ℕ, g n :=
    tsum_even_add_odd (f := g) heg hog
  have hE : ∑' k : ℕ, (-1 : ℝ) ^ (2 * k) * g (2 * k) = ∑' k : ℕ, g (2 * k) := by
    congr 1
    funext k
    rw [pow_mul]
    norm_num
  have hO : ∑' k : ℕ, (-1 : ℝ) ^ (2 * k + 1) * g (2 * k + 1) = -∑' k : ℕ, g (2 * k + 1) := by
    rw [← tsum_neg]
    congr 1
    funext k
    rw [pow_succ, pow_mul]
    norm_num
  have h0 : etaC 0 = ∑' n : ℕ, (-1 : ℝ) ^ n * g n := by
    simp only [etaC, hg]
  rw [h0, ← hsplitF, hE, hO, hgs.tsum_eq, hodd.tsum_eq] at *
  linarith

/-- `langerA k = (12/π²) η_D(2k+2)/(k+1)`: the coefficients of `ε` in `(12/π²) g(z) = z²(1+ε(z))`,
where `ε(z) = ∑_{j≥0} langerA (j+1) z^(2(j+1))`. -/
noncomputable def langerA (k : ℕ) : ℝ := 12 / π ^ 2 * (etaC k / ((k : ℝ) + 1))

/-- `langerB k = (36/π²) η_D(2k+2)/(2k+3)`: the coefficients of `E` in `m(z)³ = z³E(z)`, where
`E(z) = ∑_{j≥0} langerB j z^(2j)`. `langerB 0 = 1`. -/
noncomputable def langerB (k : ℕ) : ℝ := 36 / π ^ 2 * (etaC k / (2 * (k : ℝ) + 3))

lemma langerA_pos (k : ℕ) : 0 < langerA (k + 1) := by
  unfold langerA
  exact mul_pos (by positivity) (div_pos (etaC_pos _) (by positivity))

lemma langerA_le (k : ℕ) : langerA (k + 1) ≤ 6 / π ^ 2 := by
  unfold langerA
  have h1 := etaC_lt_one (k + 1)
  have h2 : etaC (k + 1) / (((k + 1 : ℕ) : ℝ) + 1) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    push_cast
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  calc 12 / π ^ 2 * (etaC (k + 1) / (((k + 1 : ℕ) : ℝ) + 1))
      ≤ 12 / π ^ 2 * (1 / 2) := by gcongr
    _ = 6 / π ^ 2 := by ring

lemma langerB_zero : langerB 0 = 1 := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  unfold langerB
  rw [etaC_zero]
  field_simp
  norm_num

lemma langerB_pos (k : ℕ) : 0 < langerB (k + 1) := by
  unfold langerB
  exact mul_pos (by positivity) (div_pos (etaC_pos _) (by positivity))

lemma langerB_le (k : ℕ) : langerB (k + 1) ≤ 36 / (5 * π ^ 2) := by
  unfold langerB
  have h1 := etaC_lt_one (k + 1)
  have h2 : etaC (k + 1) / (2 * ((k + 1 : ℕ) : ℝ) + 3) ≤ 1 / 5 := by
    rw [div_le_iff₀ (by positivity)]
    push_cast
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  calc 36 / π ^ 2 * (etaC (k + 1) / (2 * ((k + 1 : ℕ) : ℝ) + 3))
      ≤ 36 / π ^ 2 * (1 / 5) := by gcongr
    _ = 36 / (5 * π ^ 2) := by ring

/-- A tail of a power series in `z²` with coefficients in `[0, K]` is bounded by the geometric
sum: `‖∑_j c_j z^(2(j+1))‖ ≤ K r²/(1-r²)` for `‖z‖ ≤ r < 1`. -/
lemma summable_tail_terms {c : ℕ → ℝ} {K r : ℝ} (hc0 : ∀ j, 0 ≤ c j) (hcK : ∀ j, c j ≤ K)
    (hr0 : 0 ≤ r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ ≤ r) :
    Summable (fun j : ℕ => (c j : ℂ) * z ^ (2 * (j + 1))) ∧
      ‖∑' j : ℕ, (c j : ℂ) * z ^ (2 * (j + 1))‖ ≤ K * (r ^ 2 / (1 - r ^ 2)) := by
  have h0 : 0 ≤ r ^ 2 := sq_nonneg r
  have h1 : r ^ 2 < 1 := by nlinarith
  have hK : 0 ≤ K := (hc0 0).trans (hcK 0)
  have hterm : ∀ j : ℕ, ‖(c j : ℂ) * z ^ (2 * (j + 1))‖ ≤ K * r ^ 2 * (r ^ 2) ^ j := by
    intro j
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hc0 j)]
    have hz2 : ‖z‖ ^ (2 * (j + 1)) ≤ r ^ (2 * (j + 1)) :=
      pow_le_pow_left₀ (norm_nonneg _) hz _
    have hpow : r ^ (2 * (j + 1)) = r ^ 2 * (r ^ 2) ^ j := by ring
    calc c j * ‖z‖ ^ (2 * (j + 1)) ≤ c j * r ^ (2 * (j + 1)) :=
          mul_le_mul_of_nonneg_left hz2 (hc0 j)
      _ ≤ K * r ^ (2 * (j + 1)) := mul_le_mul_of_nonneg_right (hcK j) (by positivity)
      _ = K * r ^ 2 * (r ^ 2) ^ j := by rw [hpow]; ring
  have hgeo : Summable (fun j : ℕ => K * r ^ 2 * (r ^ 2) ^ j) :=
    (summable_geometric_of_lt_one h0 h1).mul_left _
  have hsn : Summable (fun j : ℕ => ‖(c j : ℂ) * z ^ (2 * (j + 1))‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hterm hgeo
  refine ⟨hsn.of_norm, ?_⟩
  calc ‖∑' j : ℕ, (c j : ℂ) * z ^ (2 * (j + 1))‖
      ≤ ∑' j : ℕ, ‖(c j : ℂ) * z ^ (2 * (j + 1))‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' j : ℕ, K * r ^ 2 * (r ^ 2) ^ j := Summable.tsum_le_tsum hterm hsn hgeo
    _ = K * (r ^ 2 / (1 - r ^ 2)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
        ring

lemma abs_eps_tsum_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖∑' j : ℕ, (langerA (j + 1) : ℂ) * z ^ (2 * (j + 1))‖ ≤ 6 / π ^ 2 * (r ^ 2 / (1 - r ^ 2)) :=
  (summable_tail_terms (c := fun j => langerA (j + 1)) (K := 6 / π ^ 2)
    (fun j => (langerA_pos j).le) (fun j => langerA_le j) hr0 hr1 hz).2

/-- The Langer `E` series minus its constant term. -/
lemma abs_E_sub_one_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖(∑' j : ℕ, (langerB j : ℂ) * z ^ (2 * j)) - 1‖ ≤ 36 / (5 * π ^ 2) * (r ^ 2 / (1 - r ^ 2)) := by
  have hs := (summable_tail_terms (c := fun j => langerB (j + 1)) (K := 36 / (5 * π ^ 2))
    (fun j => (langerB_pos j).le) (fun j => langerB_le j) hr0 hr1 hz)
  have hfull : Summable (fun j : ℕ => (langerB j : ℂ) * z ^ (2 * j)) :=
    (summable_nat_add_iff (f := fun j : ℕ => (langerB j : ℂ) * z ^ (2 * j)) 1).mp hs.1
  have h0 : (langerB 0 : ℂ) * z ^ (2 * 0) = 1 := by
    rw [langerB_zero]
    simp
  rw [hfull.tsum_eq_zero_add, h0, add_sub_cancel_left]
  exact hs.2

lemma epsH_le : 6 / π ^ 2 * ((0.035 : ℝ) ^ 2 / (1 - (0.035 : ℝ) ^ 2)) ≤ 7.46e-4 := by
  have hpi : (3.1415 : ℝ) < π := Real.pi_gt_d4
  have hpi2 : (3.1415 : ℝ) ^ 2 ≤ π ^ 2 := pow_le_pow_left₀ (by norm_num) hpi.le 2
  have h6 : 6 / π ^ 2 ≤ 6 / (3.1415 : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hpi2
  have hX : 0 ≤ (0.035 : ℝ) ^ 2 / (1 - (0.035 : ℝ) ^ 2) := by norm_num
  calc 6 / π ^ 2 * ((0.035 : ℝ) ^ 2 / (1 - (0.035 : ℝ) ^ 2))
      ≤ 6 / (3.1415 : ℝ) ^ 2 * ((0.035 : ℝ) ^ 2 / (1 - (0.035 : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right h6 hX
    _ ≤ 7.46e-4 := by norm_num

lemma epsE_le : 36 / (5 * π ^ 2) * ((0.035 : ℝ) ^ 2 / (1 - (0.035 : ℝ) ^ 2)) ≤ 8.95e-4 := by
  have hpi : (3.1415 : ℝ) < π := Real.pi_gt_d4
  have hpi2 : (3.1415 : ℝ) ^ 2 ≤ π ^ 2 := pow_le_pow_left₀ (by norm_num) hpi.le 2
  have h6 : 36 / (5 * π ^ 2) ≤ 36 / (5 * (3.1415 : ℝ) ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hX : 0 ≤ (0.035 : ℝ) ^ 2 / (1 - (0.035 : ℝ) ^ 2) := by norm_num
  calc 36 / (5 * π ^ 2) * ((0.035 : ℝ) ^ 2 / (1 - (0.035 : ℝ) ^ 2))
      ≤ 36 / (5 * (3.1415 : ℝ) ^ 2) * ((0.035 : ℝ) ^ 2 / (1 - (0.035 : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right h6 hX
    _ ≤ 8.95e-4 := by norm_num

/-- `‖ε(z)‖ ≤ 7.46·10⁻⁴` on `‖z‖ ≤ 0.035`. -/
lemma abs_eps_le {z : ℂ} (hz : ‖z‖ ≤ 0.035) :
    ‖∑' j : ℕ, (langerA (j + 1) : ℂ) * z ^ (2 * (j + 1))‖ ≤ 7.46e-4 :=
  (abs_eps_tsum_le (by norm_num) (by norm_num) hz).trans epsH_le

/-- `‖E(z) - 1‖ ≤ 8.95·10⁻⁴` on `‖z‖ ≤ 0.035`. -/
lemma abs_E_sub_one_le_035 {z : ℂ} (hz : ‖z‖ ≤ 0.035) :
    ‖(∑' j : ℕ, (langerB j : ℂ) * z ^ (2 * j)) - 1‖ ≤ 8.95e-4 :=
  (abs_E_sub_one_le (by norm_num) (by norm_num) hz).trans epsE_le

/-- The integer Pochhammer polynomial evaluated at a real point. -/
lemma smeval_descPochhammer_int (n : ℕ) (a : ℝ) :
    (descPochhammer ℤ n).smeval a = (descPochhammer ℝ n).eval a := by
  rw [← Polynomial.aeval_eq_smeval, Polynomial.aeval_def, ← Polynomial.eval_map,
    descPochhammer_map]

lemma choose_eq_real (α : ℝ) (n : ℕ) :
    Ring.choose α n = ((n.factorial : ℝ))⁻¹ * (descPochhammer ℝ n).eval α := by
  rw [Ring.choose_eq_smul, smeval_descPochhammer_int, smul_eq_mul]

lemma prod_sub_succ_sign {a : ℝ} (ha : a < 1) (m : ℕ) :
    0 ≤ (-1 : ℝ) ^ m * ∏ j ∈ range m, (a - ((j + 1 : ℕ) : ℝ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, pow_succ]
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
    have key := mul_nonneg ih (show (0 : ℝ) ≤ -(a - ((m + 1 : ℕ) : ℝ)) by linarith)
    nlinarith [key]

/-- For `0 < a < 1` and `m ≥ 0`, the generalized binomial coefficient `Ring.choose a (m+1)`
has sign `(-1)^m`: `(-1)^(m+1) · choose a (m+1) ≤ 0`. -/
lemma choose_real_sign {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (m : ℕ) :
    Ring.choose a (m + 1) * (-1 : ℝ) ^ (m + 1) ≤ 0 := by
  rw [choose_eq_real, descPochhammer_eval_eq_prod_range, prod_range_succ']
  have hP := prod_sub_succ_sign ha1 m
  have hf : (0 : ℝ) < ((m + 1).factorial : ℝ)⁻¹ := by positivity
  simp only [Nat.cast_zero, sub_zero]
  rw [pow_succ]
  nlinarith [mul_nonneg (mul_nonneg hf.le ha0.le) hP]

lemma hasSum_choose_complex {α : ℝ} {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => ((Ring.choose α n : ℝ) : ℂ) * x ^ n) ((1 + x) ^ (α : ℂ)) := by
  have hmem : x - 0 ∈ Metric.eball (0 : ℂ) 1 := by
    rw [sub_zero, Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_one, dist_zero_right]
    exact hx
  have h := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := (α : ℂ))).hasSum_sub hmem
  simp only [sub_zero] at h
  convert h using 1
  funext n
  rw [binomialSeries_apply, Complex.ofReal_choose, smul_eq_mul]
  simp

/-- **Binomial bound** (`Ring.choose` signs). For `0 < α < 1` and `‖x‖ < 1`, the principal
power satisfies `‖(1+x)^α - 1‖ ≤ 1 - (1 - ‖x‖)^α`. Proved from the binomial series
(`Complex.one_add_cpow_hasFPowerSeriesOnBall_zero`) and the sign of the coefficients
`Ring.choose α (m+1)` (Mathlib: `binomialSeries`). -/
theorem binomial_bound {x : ℂ} (hx : ‖x‖ < 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ‖(1 + x) ^ (α : ℂ) - 1‖ ≤ 1 - (1 - ‖x‖) ^ α := by
  have ht0 : 0 ≤ ‖x‖ := norm_nonneg x
  -- the real binomial series at `-‖x‖`
  have hR : HasSum (fun n : ℕ => Ring.choose α n * (-‖x‖) ^ n) ((1 - ‖x‖) ^ α) := by
    have hneg : ‖((-‖x‖ : ℝ) : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg ht0]
      exact hx
    have h := hasSum_choose_complex (α := α) hneg
    have e : (1 + ((-‖x‖ : ℝ) : ℂ)) ^ (α : ℂ) = (((1 - ‖x‖) ^ α : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ 1 - ‖x‖)]
      push_cast
      ring_nf
    rw [e] at h
    exact Complex.hasSum_ofReal.mp (by
      convert h using 1
      funext n
      push_cast
      ring)
  -- the coefficients of the tail have the sign that makes the norms summable
  have hS : HasSum (fun n : ℕ => -(Ring.choose α (n + 1) * (-‖x‖) ^ (n + 1)))
      (1 - (1 - ‖x‖) ^ α) := by
    have h1 := (hasSum_nat_add_iff' 1).mpr hR
    simp only [Finset.sum_range_one, Ring.choose_zero_right, pow_zero, mul_one] at h1
    convert h1.neg using 1
    ring
  have hterm : ∀ n : ℕ, ‖((Ring.choose α (n + 1) : ℝ) : ℂ) * x ^ (n + 1)‖ ≤
      -(Ring.choose α (n + 1) * (-‖x‖) ^ (n + 1)) := by
    intro n
    have hs := choose_real_sign hα0 hα1 n
    have habs : |Ring.choose α (n + 1)| = -(Ring.choose α (n + 1) * (-1) ^ (n + 1)) := by
      have h1 : |Ring.choose α (n + 1) * (-1) ^ (n + 1)| = |Ring.choose α (n + 1)| := by
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
      rw [← h1, abs_of_nonpos hs]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, habs, neg_pow]
    exact le_of_eq (by ring)
  have hC := (hasSum_nat_add_iff' 1).mpr (hasSum_choose_complex (α := α) hx)
  simp only [Finset.sum_range_one, Ring.choose_zero_right, Complex.ofReal_one, pow_zero,
    mul_one] at hC
  exact hC.norm_le_of_bounded hS hterm

/-- info: 'FormalResearch.SignUncertainty.etaC_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms etaC_zero

/-- info: 'FormalResearch.SignUncertainty.etaC_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms etaC_pos

/-- info: 'FormalResearch.SignUncertainty.etaC_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms etaC_lt_one

/-- info: 'FormalResearch.SignUncertainty.langerA_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langerA_pos

/-- info: 'FormalResearch.SignUncertainty.langerA_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langerA_le

/-- info: 'FormalResearch.SignUncertainty.langerB_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langerB_zero

/-- info: 'FormalResearch.SignUncertainty.langerB_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langerB_pos

/-- info: 'FormalResearch.SignUncertainty.langerB_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langerB_le

/-- info: 'FormalResearch.SignUncertainty.abs_eps_tsum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abs_eps_tsum_le

/-- info: 'FormalResearch.SignUncertainty.abs_E_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abs_E_sub_one_le

/-- info: 'FormalResearch.SignUncertainty.abs_eps_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abs_eps_le

/-- info: 'FormalResearch.SignUncertainty.abs_E_sub_one_le_035' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abs_E_sub_one_le_035

/-- info: 'FormalResearch.SignUncertainty.epsH_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms epsH_le

/-- info: 'FormalResearch.SignUncertainty.epsE_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms epsE_le

/-- info: 'FormalResearch.SignUncertainty.binomial_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms binomial_bound

/-- info: 'FormalResearch.SignUncertainty.etaC_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms etaC_hasSum

end FormalResearch.SignUncertainty
