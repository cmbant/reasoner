module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Concrete Crossing Setup at Fixed Chiral Weight `(H_w)`

Formalizes the concrete fixed-weight modular crossing problem (`CFT/modular_bootstrap/paper/`):
* `modular_bootstrap_main.tex`, Section `sec:setup` (reduced characters, `K_b`, `V`, `ρ_C`,
  `Ξ_β`, Hankel-odd test class `\overline{\mathcal A}`, `M[g]`, `g_vac`, `T_V`, `T_weak`, `Δ_best`).
* `n1_super_virasoro.tex`, Setting `(H_w)` and Lemma 4(b) (`n1:L4`).

## Conventions on the radial lift and Mathlib's Fourier transform

Mathlib's Fourier transform `𝓕 f ξ = ∫ x, exp (-2π i ⟪x, ξ⟫) • f x` on
`EuclideanSpace ℝ (Fin (2 * w))` is unitary on `L²(ℝ^{2w})` with `e^{-π ‖x‖²}` self-dual.
Setting `t = ‖x‖² / 2` (so `x_mathlib = x_paper / √(2π)` relative to the paper's `t = |x_paper|² / (4π)`
with the unitary transform `(2π)^{-w} ∫ e^{-i ⟪x_paper, ξ_paper⟫} f(x_paper) dx_paper`), the thermal
exponential `e^{-2π β t}` lifts to `e^{-π β ‖x‖²}`, whose Mathlib Fourier transform is
`β^{-w} e^{-π ‖ξ‖² / β} = β^{-w} e^{-2π (‖ξ‖² / 2) / β}`. Thus the Hankel-odd test class
`\overline{\mathcal A}_w` is defined directly by `𝓕 (radialLift w g) = -(radialLift w g)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform RealInnerProductSpace

namespace FormalResearch.ModularBootstrap.Crossing

/-! ### Section 1: Fixed-weight problem `(H_w)` and named instances -/

/-- Fixed-weight modular bootstrap setting `(H_w)`: integer chiral weight `w ≥ 1` and
positive null-state shifts `μ₁, …, μ_m > 0` forming `Q(q) = ∏ l, (1 - q ^ (μ l))`. -/
structure FixedWeightProblem where
  w : ℕ
  hw : 1 ≤ w
  m : ℕ
  μ : Fin m → ℝ
  hμ : ∀ l, 0 < μ l

/-- Subset sum of null shifts `r_s = ∑_{l ∈ s} μ_l`. -/
noncomputable def FixedWeightProblem.shiftSum (prob : FixedWeightProblem)
    (s : Finset (Fin prob.m)) : ℝ :=
  ∑ l ∈ s, prob.μ l

/-- Total null shift `S = ∑_{l=1}^m μ_l`. -/
noncomputable def FixedWeightProblem.totalShift (prob : FixedWeightProblem) : ℝ :=
  ∑ l : Fin prob.m, prob.μ l

lemma FixedWeightProblem.shiftSum_nonneg (prob : FixedWeightProblem) (s : Finset (Fin prob.m)) :
    0 ≤ prob.shiftSum s :=
  Finset.sum_nonneg fun l _ => (prob.hμ l).le

lemma FixedWeightProblem.shiftSum_le_totalShift (prob : FixedWeightProblem)
    (s : Finset (Fin prob.m)) :
    prob.shiftSum s ≤ prob.totalShift :=
  Finset.sum_le_univ_sum_of_nonneg fun l => (prob.hμ l).le

lemma FixedWeightProblem.totalShift_nonneg (prob : FixedWeightProblem) :
    0 ≤ prob.totalShift :=
  Finset.sum_nonneg fun l _ => (prob.hμ l).le

/-- Null-state polynomial `Q(q) = ∏_{l=1}^m (1 - q ^ (μ_l))`. -/
noncomputable def FixedWeightProblem.nullPoly (prob : FixedWeightProblem) (q : ℝ) : ℝ :=
  ∏ l : Fin prob.m, (1 - q ^ prob.μ l)

lemma FixedWeightProblem.nullPoly_eq_sum (prob : FixedWeightProblem) {q : ℝ} (hq : 0 ≤ q) :
    prob.nullPoly q =
      ∑ s : Finset (Fin prob.m), (-1 : ℝ) ^ s.card * q ^ prob.shiftSum s := by
  unfold FixedWeightProblem.nullPoly FixedWeightProblem.shiftSum
  have h1 : (∏ l : Fin prob.m, (1 - q ^ prob.μ l)) =
      ∏ l ∈ (Finset.univ : Finset (Fin prob.m)), ((-q ^ prob.μ l) + 1) :=
    Finset.prod_congr rfl fun l _ => by ring
  rw [h1, Finset.prod_add]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Finset.prod_const_one, mul_one]
  rw [show (∏ i ∈ s, -q ^ prob.μ i) = ∏ i ∈ s, (-1 : ℝ) * q ^ prob.μ i from
    Finset.prod_congr rfl fun i _ => by ring]
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  congr 1
  rcases eq_or_lt_of_le hq with rfl | hq_pos
  · by_cases hs : s.Nonempty
    · obtain ⟨i₀, hi₀⟩ := hs
      have hsum_pos : 0 < ∑ i ∈ s, prob.μ i :=
        Finset.sum_pos' (fun i _ => (prob.hμ i).le) ⟨i₀, hi₀, prob.hμ i₀⟩
      rw [Real.zero_rpow hsum_pos.ne']
      exact Finset.prod_eq_zero hi₀ (Real.zero_rpow (prob.hμ i₀).ne')
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
      simp
  · exact (Real.rpow_sum_of_pos hq_pos prob.μ s).symm

lemma FixedWeightProblem.nullPoly_pos (prob : FixedWeightProblem) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) : 0 < prob.nullPoly q := by
  unfold FixedWeightProblem.nullPoly
  refine Finset.prod_pos fun l _ => sub_pos.mpr ?_
  rcases eq_or_lt_of_le hq0 with rfl | _hq_pos
  · rw [Real.zero_rpow (prob.hμ l).ne']; exact zero_lt_one
  · exact Real.rpow_lt_one hq0 hq1 (prob.hμ l)

lemma FixedWeightProblem.nullPoly_le_one (prob : FixedWeightProblem) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : prob.nullPoly q ≤ 1 := by
  unfold FixedWeightProblem.nullPoly
  have hterm : ∀ l : Fin prob.m, 0 ≤ 1 - q ^ prob.μ l ∧ 1 - q ^ prob.μ l ≤ 1 := fun l =>
    ⟨sub_nonneg.mpr (Real.rpow_le_one hq0 hq1 (prob.hμ l).le),
     sub_le_self _ (Real.rpow_nonneg hq0 _)⟩
  induction (Finset.univ : Finset (Fin prob.m)) using Finset.cons_induction with
  | empty => simp
  | cons a s _ha ih =>
    rw [Finset.prod_cons]
    have ha' := hterm a
    have hs' : 0 ≤ ∏ x ∈ s, (1 - q ^ prob.μ x) :=
      Finset.prod_nonneg fun x _ => (hterm x).1
    nlinarith

/-- Spinless Virasoro problem: `w = 1`, `Q(q) = (1 - q)^2` (`μ = ![1, 1]`). -/
def virasoroProblem : FixedWeightProblem where
  w := 1
  hw := le_rfl
  m := 2
  μ := ![1, 1]
  hμ := fun l => by fin_cases l <;> norm_num

@[simp] lemma virasoroProblem_w : virasoroProblem.w = 1 := rfl
@[simp] lemma virasoroProblem_m : virasoroProblem.m = 2 := rfl

lemma virasoroProblem_totalShift : virasoroProblem.totalShift = 2 := by
  unfold FixedWeightProblem.totalShift virasoroProblem
  simp [Fin.sum_univ_two]; norm_num

lemma virasoroProblem_nullPoly (q : ℝ) :
    virasoroProblem.nullPoly q = (1 - q) ^ 2 := by
  unfold FixedWeightProblem.nullPoly virasoroProblem
  simp [Fin.prod_univ_two, pow_two]

/-- `N = 1` NS super-Virasoro problem: `w = 1`, `Q(q) = (1 - q^{1/2})^2` (`μ = ![1/2, 1/2]`). -/
noncomputable def n1SuperVirasoroProblem : FixedWeightProblem where
  w := 1
  hw := le_rfl
  m := 2
  μ := ![1 / 2, 1 / 2]
  hμ := fun l => by fin_cases l <;> norm_num

lemma n1SuperVirasoroProblem_totalShift : n1SuperVirasoroProblem.totalShift = 1 := by
  unfold FixedWeightProblem.totalShift n1SuperVirasoroProblem
  simp [Fin.sum_univ_two]; norm_num

/-! ### Section 2: Bessel kernels `K_α` and Laplace identity -/

/-- Power-series term of `K_α(t)` at weight `w ≥ 1`:
`(4π² α t)^k / (k! (k + w - 1)!)`. -/
noncomputable def kernelKTerm (w : ℕ) (α t : ℝ) (k : ℕ) : ℝ :=
  (4 * π ^ 2 * α * t) ^ k / ((k.factorial : ℝ) * ((k + w - 1).factorial : ℝ))

/-- Fixed-weight vacuum kernel `K_α(t) = (2π t)^{w-1} ∑_{k ≥ 0} (4π² α t)^k / (k! (k+w-1)!)`.
Equals `(t/α)^{(w-1)/2} I_{w-1}(4π √(α t))` for `α, t > 0` and extends smoothly to all `α, t ∈ ℝ`. -/
noncomputable def kernelK (w : ℕ) (α t : ℝ) : ℝ :=
  (2 * π * t) ^ (w - 1) * ∑' k : ℕ, kernelKTerm w α t k

lemma summable_kernelKTerm (w : ℕ) (α t : ℝ) : Summable (kernelKTerm w α t) := by
  have hexp : Summable (fun k : ℕ => |4 * π ^ 2 * α * t| ^ k / (k.factorial : ℝ)) :=
    Real.summable_pow_div_factorial _
  refine hexp.of_norm_bounded fun k => ?_
  unfold kernelKTerm
  have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have hfac2_pos : (0 : ℝ) < ((k + w - 1).factorial : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (mul_pos hfac_pos hfac2_pos)]
  refine div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg _) k) hfac_pos ?_
  have hfac : (1 : ℝ) ≤ ((k + w - 1).factorial : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
  nlinarith

lemma kernelK_eq_gamma {w : ℕ} (hw : 1 ≤ w) (α t : ℝ) :
    kernelK w α t =
      (2 * π * t) ^ (w - 1) *
        ∑' k : ℕ, (4 * π ^ 2 * α * t) ^ k / ((k.factorial : ℝ) * Real.Gamma ((k + w : ℕ) : ℝ)) := by
  unfold kernelK kernelKTerm
  congr 1
  refine tsum_congr fun k => ?_
  have hkw : k + w = (k + w - 1) + 1 := by omega
  rw [hkw, Nat.cast_add, Nat.cast_one, Real.Gamma_nat_eq_factorial, add_tsub_cancel_right]

lemma kernelK_nonneg {w : ℕ} {α t : ℝ} (hα : 0 ≤ α) (ht : 0 ≤ t) :
    0 ≤ kernelK w α t := by
  unfold kernelK
  refine mul_nonneg (pow_nonneg (by positivity) _) (tsum_nonneg fun k => ?_)
  unfold kernelKTerm
  positivity

lemma kernelK_mono_alpha {w : ℕ} {α₁ α₂ t : ℝ} (hα₁ : 0 ≤ α₁) (hα : α₁ ≤ α₂) (ht : 0 ≤ t) :
    kernelK w α₁ t ≤ kernelK w α₂ t := by
  unfold kernelK
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by positivity) _)
  refine (summable_kernelKTerm w α₁ t).tsum_le_tsum (fun k => ?_) (summable_kernelKTerm w α₂ t)
  unfold kernelKTerm
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by gcongr) k

lemma continuous_kernelK (w : ℕ) (α : ℝ) : Continuous (kernelK w α) := by
  unfold kernelK
  refine (by fun_prop : Continuous fun t : ℝ => (2 * π * t) ^ (w - 1)).mul ?_
  refine continuous_iff_continuousAt.mpr fun t₀ => ?_
  let R : ℝ := |t₀| + 1
  let M : ℕ → ℝ := fun k => (4 * π ^ 2 * |α| * R) ^ k / (k.factorial : ℝ)
  have hM : Summable M := Real.summable_pow_div_factorial _
  have hcont_unif : ContinuousOn (fun t => ∑' k : ℕ, kernelKTerm w α t k) (Icc (-R) R) := by
    refine continuousOn_tsum (fun k => (by unfold kernelKTerm; fun_prop :
        Continuous (fun t => kernelKTerm w α t k)).continuousOn) hM ?_
    intro k t ht
    unfold kernelKTerm
    have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) := by positivity
    have hfac2_pos : (0 : ℝ) < ((k + w - 1).factorial : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (mul_pos hfac_pos hfac2_pos)]
    have hfac : (1 : ℝ) ≤ ((k + w - 1).factorial : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
    have h1 : |4 * π ^ 2 * α * t| ≤ 4 * π ^ 2 * |α| * R := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < (4 : ℝ)),
        abs_of_pos (sq_pos_of_pos Real.pi_pos)]
      exact mul_le_mul_of_nonneg_left (abs_le.mpr ht) (by positivity)
    calc |4 * π ^ 2 * α * t| ^ k / ((k.factorial : ℝ) * ((k + w - 1).factorial : ℝ))
        ≤ (4 * π ^ 2 * |α| * R) ^ k / ((k.factorial : ℝ) * ((k + w - 1).factorial : ℝ)) := by
          gcongr
      _ ≤ (4 * π ^ 2 * |α| * R) ^ k / (k.factorial : ℝ) := by
          refine div_le_div_of_nonneg_left (pow_nonneg (by positivity) k) hfac_pos ?_
          nlinarith
  have hmem : t₀ ∈ Ioo (-R) R := by
    dsimp [R]
    exact ⟨by linarith [neg_abs_le t₀], by linarith [le_abs_self t₀]⟩
  exact hcont_unif.continuousAt (Icc_mem_nhds hmem.1 hmem.2)

private lemma integrableOn_pow_mul_exp_neg_mul_Ioi (n : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-(r * t))) (Ioi 0) := by
  have hdom_int : IntegrableOn (fun t : ℝ =>
      ((n.factorial : ℝ) * (2 / r) ^ n) * Real.exp (-(r / 2) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -(r / 2) < 0) 0).const_mul _
  refine hdom_int.mono' ((by fun_prop : Continuous fun t : ℝ =>
      t ^ n * Real.exp (-(r * t))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht0 _) (Real.exp_pos _).le)]
  have hpow_le : (r / 2 * t) ^ n / (n.factorial : ℝ) ≤ Real.exp (r / 2 * t) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    exact (Real.summable_pow_div_factorial (r / 2 * t)).le_tsum n
      fun k _ => div_nonneg (pow_nonneg (by positivity) k) (by positivity)
  have h1 : t ^ n ≤ (n.factorial : ℝ) * (2 / r) ^ n * Real.exp (r / 2 * t) := by
    have hmul := mul_le_mul_of_nonneg_left hpow_le (show 0 ≤ (n.factorial : ℝ) * (2 / r) ^ n by positivity)
    have hcancel : (2 / r) ^ n * (r / 2) ^ n = 1 := by
      rw [← mul_pow, show (2 / r) * (r / 2) = 1 by field_simp [hr.ne'], one_pow]
    calc t ^ n = t ^ n * 1 := (mul_one _).symm
      _ = t ^ n * ((2 / r) ^ n * (r / 2) ^ n) := by rw [hcancel]
      _ = (n.factorial : ℝ) * (2 / r) ^ n * ((r / 2 * t) ^ n / (n.factorial : ℝ)) := by
          rw [mul_pow]; field_simp
      _ ≤ (n.factorial : ℝ) * (2 / r) ^ n * Real.exp (r / 2 * t) := hmul
  calc t ^ n * Real.exp (-(r * t))
      ≤ ((n.factorial : ℝ) * (2 / r) ^ n * Real.exp (r / 2 * t)) * Real.exp (-(r * t)) := by
        gcongr
    _ = ((n.factorial : ℝ) * (2 / r) ^ n) * Real.exp (-(r / 2) * t) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- **Laplace transform of `K_α`** (`n1_super_virasoro.tex`, eq. before Lemma 4):
`2π ∫₀^∞ K_α(t) e^{-2π β t} dt = β^{-w} e^{2π α / β}` for all `w ≥ 1`, `α ∈ ℝ`, `β > 0`. -/
theorem kernelK_laplace {w : ℕ} (hw : 1 ≤ w) (α : ℝ) {β : ℝ} (hβ : 0 < β) :
    IntegrableOn (fun t => kernelK w α t * Real.exp (-2 * π * β * t)) (Ioi 0) ∧
      2 * π * ∫ t in Ioi 0, kernelK w α t * Real.exp (-2 * π * β * t) =
        β ^ (-(w : ℝ)) * Real.exp (2 * π * α / β) := by
  let r : ℝ := 2 * π * β
  have hr : 0 < r := by positivity
  let F : ℕ → ℝ → ℝ := fun k t =>
    (2 * π * t) ^ (w - 1) * kernelKTerm w α t k * Real.exp (-(r * t))
  have hF_eq : ∀ t : ℝ, kernelK w α t * Real.exp (-2 * π * β * t) = ∑' k : ℕ, F k t := by
    intro t
    unfold kernelK
    rw [show -2 * π * β * t = -(r * t) by dsimp [r]; ring, mul_assoc, ← tsum_mul_right,
      ← tsum_mul_left]
    refine tsum_congr fun k => by dsimp [F]; ring
  have hF_int_norm : ∀ k : ℕ, IntegrableOn (F k) (Ioi 0) ∧
      ∫ t in Ioi 0, F k t =
        (2 * π)⁻¹ * β ^ (-(w : ℝ)) * ((2 * π * α / β) ^ k / (k.factorial : ℝ)) ∧
      ∫ t in Ioi 0, ‖F k t‖ =
        (2 * π)⁻¹ * β ^ (-(w : ℝ)) * ((2 * π * |α| / β) ^ k / (k.factorial : ℝ)) := by
    intro k
    have hkw_pos : (0 : ℝ) < (k + w : ℕ) := by positivity
    have hkw_sub : k + w - 1 + 1 = k + w := by omega
    have hgam : Real.Gamma ((k + w : ℕ) : ℝ) = ((k + w - 1).factorial : ℝ) := by
      rw [← hkw_sub, Nat.cast_add, Nat.cast_one, Real.Gamma_nat_eq_factorial, add_tsub_cancel_right]
    have hpow_eq : ∀ t ∈ Ioi (0 : ℝ),
        t ^ (((k + w : ℕ) : ℝ) - 1) * Real.exp (-(r * t)) = t ^ (k + w - 1) * Real.exp (-(r * t)) := by
      intro t _ht
      rw [← Real.rpow_natCast t (k + w - 1)]
      congr 2
      have hkw1 : (k + w - 1 : ℕ) + 1 = k + w := by omega
      have hcast : ((k + w : ℕ) : ℝ) - 1 = ((k + w - 1 : ℕ) : ℝ) := by
        rw [← hkw1]; push_cast; ring
      exact hcast
    have hbase_int : IntegrableOn (fun t : ℝ => t ^ (k + w - 1) * Real.exp (-(r * t))) (Ioi 0) :=
      integrableOn_pow_mul_exp_neg_mul_Ioi (k + w - 1) hr
    have hbase_val : ∫ t in Ioi 0, t ^ (k + w - 1) * Real.exp (-(r * t)) =
        (1 / r) ^ (k + w) * ((k + w - 1).factorial : ℝ) := by
      rw [← setIntegral_congr_fun measurableSet_Ioi hpow_eq,
        Real.integral_rpow_mul_exp_neg_mul_Ioi hkw_pos hr, hgam, Real.rpow_natCast]
    let c_k : ℝ := (2 * π) ^ (w - 1) * (4 * π ^ 2 * α) ^ k /
      ((k.factorial : ℝ) * ((k + w - 1).factorial : ℝ))
    have hF_form : ∀ t : ℝ, F k t = c_k * (t ^ (k + w - 1) * Real.exp (-(r * t))) := by
      intro t
      dsimp [F, c_k]; unfold kernelKTerm
      rw [mul_pow, mul_pow]
      have hkw : (w - 1) + k = k + w - 1 := by omega
      rw [← hkw, pow_add]
      ring
    have hF_on : IntegrableOn (F k) (Ioi 0) :=
      IntegrableOn.congr_fun (hbase_int.const_mul c_k) (fun t _ => (hF_form t).symm) measurableSet_Ioi
    have hbw : (1 / r) ^ w = (2 * π) ^ (-((w : ℕ) : ℝ)) * β ^ (-(w : ℝ)) := by
      dsimp [r]
      rw [← Real.rpow_natCast (1 / (2 * π * β)) w, one_div, Real.inv_rpow (by positivity),
        Real.mul_rpow (by positivity) hβ.le, mul_inv, ← Real.rpow_neg (by positivity),
        ← Real.rpow_neg hβ.le]
    have h2pi : (2 * π) ^ (w - 1) * (2 * π) ^ (-((w : ℕ) : ℝ)) = (2 * π)⁻¹ := by
      rw [← Real.rpow_natCast (2 * π) (w - 1), ← Real.rpow_add (by positivity)]
      have hw1 : w - 1 + 1 = w := Nat.sub_add_cancel hw
      have hsub : ((w - 1 : ℕ) : ℝ) + -((w : ℕ) : ℝ) = -1 := by
        calc ((w - 1 : ℕ) : ℝ) + -((w : ℕ) : ℝ)
            = ((w - 1 : ℕ) : ℝ) - ((w - 1 + 1 : ℕ) : ℝ) := by rw [hw1]; ring
          _ = -1 := by push_cast; ring
      rw [hsub, Real.rpow_neg_one]
    have hfac_ne : ((k + w - 1).factorial : ℝ) ≠ 0 := by positivity
    have hval : ∫ t in Ioi 0, F k t =
        (2 * π)⁻¹ * β ^ (-(w : ℝ)) * ((2 * π * α / β) ^ k / (k.factorial : ℝ)) := by
      rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hF_form t), integral_const_mul,
        hbase_val]
      dsimp [c_k]
      rw [pow_add]
      have hr_cancel : 4 * π ^ 2 * α * (1 / r) = 2 * π * α / β := by
        dsimp [r]; field_simp [Real.pi_pos.ne', hβ.ne']; ring
      calc (2 * π) ^ (w - 1) * (4 * π ^ 2 * α) ^ k /
            ((k.factorial : ℝ) * ((k + w - 1).factorial : ℝ)) *
            ((1 / r) ^ k * (1 / r) ^ w * ((k + w - 1).factorial : ℝ))
          = ((2 * π) ^ (w - 1) * (1 / r) ^ w) *
              (((4 * π ^ 2 * α * (1 / r)) ^ k) / (k.factorial : ℝ)) *
              (((k + w - 1).factorial : ℝ) / ((k + w - 1).factorial : ℝ)) := by
            rw [mul_pow]; ring
        _ = ((2 * π) ^ (w - 1) * (2 * π) ^ (-((w : ℕ) : ℝ))) * β ^ (-(w : ℝ)) *
              ((2 * π * α / β) ^ k / (k.factorial : ℝ)) * 1 := by
            rw [hbw, div_self hfac_ne, hr_cancel]; ring
        _ = (2 * π)⁻¹ * β ^ (-(w : ℝ)) * ((2 * π * α / β) ^ k / (k.factorial : ℝ)) := by
            rw [mul_one, h2pi]
    have hnorm : ∫ t in Ioi 0, ‖F k t‖ =
        (2 * π)⁻¹ * β ^ (-(w : ℝ)) * ((2 * π * |α| / β) ^ k / (k.factorial : ℝ)) := by
      have hnorm_form : ∀ t ∈ Ioi (0 : ℝ),
          ‖F k t‖ = |c_k| * (t ^ (k + w - 1) * Real.exp (-(r * t))) := by
        intro t ht
        rw [hF_form t, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (mul_nonneg (pow_nonneg (mem_Ioi.mp ht).le _) (Real.exp_pos _).le)]
      rw [setIntegral_congr_fun measurableSet_Ioi hnorm_form, integral_const_mul, hbase_val]
      have hc_abs : |c_k| = (2 * π) ^ (w - 1) * (4 * π ^ 2 * |α|) ^ k /
          ((k.factorial : ℝ) * ((k + w - 1).factorial : ℝ)) := by
        dsimp [c_k]
        rw [abs_div, abs_mul, abs_pow, abs_pow, abs_of_pos (by positivity : 0 < 2 * π),
          abs_of_pos (by positivity : 0 < (k.factorial : ℝ) * ((k + w - 1).factorial : ℝ)),
          show |4 * π ^ 2 * α| = 4 * π ^ 2 * |α| by
            rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * π ^ 2)]]
      have hr_cancel : 4 * π ^ 2 * |α| * (1 / r) = 2 * π * |α| / β := by
        dsimp [r]; field_simp [Real.pi_pos.ne', hβ.ne']; ring
      rw [hc_abs, pow_add]
      calc (2 * π) ^ (w - 1) * (4 * π ^ 2 * |α|) ^ k /
            ((k.factorial : ℝ) * ((k + w - 1).factorial : ℝ)) *
            ((1 / r) ^ k * (1 / r) ^ w * ((k + w - 1).factorial : ℝ))
          = ((2 * π) ^ (w - 1) * (1 / r) ^ w) *
              (((4 * π ^ 2 * |α| * (1 / r)) ^ k) / (k.factorial : ℝ)) *
              (((k + w - 1).factorial : ℝ) / ((k + w - 1).factorial : ℝ)) := by
            rw [mul_pow]; ring
        _ = ((2 * π) ^ (w - 1) * (2 * π) ^ (-((w : ℕ) : ℝ))) * β ^ (-(w : ℝ)) *
              ((2 * π * |α| / β) ^ k / (k.factorial : ℝ)) * 1 := by
            rw [hbw, div_self hfac_ne, hr_cancel]; ring
        _ = (2 * π)⁻¹ * β ^ (-(w : ℝ)) * ((2 * π * |α| / β) ^ k / (k.factorial : ℝ)) := by
            rw [mul_one, h2pi]
    exact ⟨hF_on, hval, hnorm⟩
  have hsum_norm : Summable (fun k : ℕ => ∫ t in Ioi 0, ‖F k t‖) := by
    simp_rw [fun k => (hF_int_norm k).2.2]
    exact (Real.summable_pow_div_factorial (2 * π * |α| / β)).mul_left _
  have hint_tsum : IntegrableOn (fun t => ∑' k : ℕ, F k t) (Ioi 0) := by
    have hF_meas : ∀ k, AEStronglyMeasurable (F k) (volume.restrict (Ioi 0)) :=
      fun k => (hF_int_norm k).1.1
    have htsum_enorm : ∑' k : ℕ, ∫⁻ t in Ioi 0, ‖F k t‖ₑ ≠ ⊤ := by
      have heq : ∀ k : ℕ, ∫⁻ t in Ioi 0, ‖F k t‖ₑ = ENNReal.ofReal (∫ t in Ioi 0, ‖F k t‖) :=
        fun k => (ofReal_integral_norm_eq_lintegral_eNorm (hF_int_norm k).1).symm
      simp_rw [heq]
      have hnn : Summable (fun k : ℕ => (∫ t in Ioi 0, ‖F k t‖).toNNReal) :=
        NNReal.summable_coe.1 (by
          refine hsum_norm.congr fun k => ?_
          exact (Real.coe_toNNReal _ (setIntegral_nonneg measurableSet_Ioi fun _ _ => norm_nonneg _)).symm)
      simpa only [ENNReal.ofReal] using ENNReal.tsum_coe_ne_top_iff_summable.2 hnn
    refine ⟨AEStronglyMeasurable.tsum hF_meas, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have hle : ∫⁻ t in Ioi 0, ENNReal.ofReal ‖∑' k : ℕ, F k t‖ ≤
        ∑' k : ℕ, ∫⁻ t in Ioi 0, ‖F k t‖ₑ := by
      calc ∫⁻ t in Ioi 0, ENNReal.ofReal ‖∑' k : ℕ, F k t‖
          = ∫⁻ t in Ioi 0, ‖∑' k : ℕ, F k t‖ₑ := by
              refine lintegral_congr fun t => ?_
              rw [Real.eNorm_eq_ofReal_abs, Real.norm_eq_abs]
        _ ≤ ∫⁻ t in Ioi 0, ∑' k : ℕ, ‖F k t‖ₑ :=
            lintegral_mono fun t => eNorm_tsum_le_tsum_eNorm
        _ = ∑' k : ℕ, ∫⁻ t in Ioi 0, ‖F k t‖ₑ := lintegral_tsum fun k => (hF_meas k).eNorm
    exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr htsum_enorm)
  have hint_main : IntegrableOn (fun t => kernelK w α t * Real.exp (-2 * π * β * t)) (Ioi 0) :=
    hint_tsum.congr_fun (fun t _ => (hF_eq t).symm) measurableSet_Ioi
  refine ⟨hint_main, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hF_eq t)]
  rw [← integral_tsum_of_summable_integral_norm (fun k => (hF_int_norm k).1) hsum_norm]
  simp_rw [fun k => (hF_int_norm k).2.1]
  rw [tsum_mul_left]
  have hexp_eq : (∑' k : ℕ, (2 * π * α / β) ^ k / (k.factorial : ℝ)) = Real.exp (2 * π * α / β) := by
    rw [Real.exp_eq_exp_ℝ, congrFun (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)) (2 * π * α / β)]
  rw [hexp_eq]
  have h2pi_ne : (2 * π) ≠ 0 := by positivity
  field_simp [h2pi_ne]

/-! ### Section 3: Iterated differences, Cardy weight `V`, and Lemma 4(b) (`n1:L4`) -/

/-- Iterated backward difference `Δ_{μ_1} ⋯ Δ_{μ_m} f(x)`. -/
def listDiff : List ℝ → (ℝ → ℝ) → ℝ → ℝ
  | [], f, x => f x
  | μ :: μs, f, x => listDiff μs f x - listDiff μs f (x - μ)

lemma listDiff_const_mul (μs : List ℝ) (c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    listDiff μs (fun y => c * f y) x = c * listDiff μs f x := by
  induction μs generalizing x with
  | nil => rfl
  | cons μ μs ih =>
    simp only [listDiff, ih]
    ring

lemma listDiff_tsum {ι : Type*} (μs : List ℝ) (F : ι → ℝ → ℝ)
    (hsum : ∀ x, Summable (fun i => F i x)) (x : ℝ) :
    listDiff μs (fun y => ∑' i, F i y) x = ∑' i, listDiff μs (F i) x := by
  induction μs generalizing x with
  | nil => rfl
  | cons μ μs ih =>
    simp only [listDiff]
    have hsum' : ∀ (νs : List ℝ) (y : ℝ), Summable (fun i => listDiff νs (F i) y) := by
      intro νs
      induction νs with
      | nil => exact hsum
      | cons ν νs ihν => intro y; exact (ihν y).sub (ihν (y - ν))
    rw [ih x, ih (x - μ), ← (hsum' μs x).tsum_sub (hsum' μs (x - μ))]

lemma hasDerivAt_listDiff (μs : List ℝ) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (x : ℝ) :
    HasDerivAt (listDiff μs f) (listDiff μs f' x) x := by
  induction μs generalizing x with
  | nil => exact hf x
  | cons μ μs ih =>
    have h1 := ih x
    have h2 := ((ih (x - μ)).comp x ((hasDerivAt_id x).sub_const μ)).congr_deriv (mul_one _)
    exact h1.sub h2

lemma continuous_listDiff (μs : List ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (listDiff μs f) := by
  induction μs with
  | nil => exact hf
  | cons μ μs ih => exact ih.sub (ih.comp (continuous_id.sub continuous_const))

lemma listDiff_eq_integral (μ : ℝ) (μs : List ℝ) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') (x : ℝ) :
    listDiff (μ :: μs) f x = ∫ u in (0 : ℝ)..μ, listDiff μs f' (x - u) := by
  have hd : ∀ u ∈ uIcc (0 : ℝ) μ,
      HasDerivAt (fun v : ℝ => -listDiff μs f (x - v)) (listDiff μs f' (x - u)) u := by
    intro u _
    have hcomp := (hasDerivAt_listDiff μs hf (x - u)).comp u ((hasDerivAt_id u).const_sub x)
    exact hcomp.neg.congr_deriv (by ring)
  have hc : Continuous fun u : ℝ => listDiff μs f' (x - u) :=
    (continuous_listDiff μs hf').comp (continuous_const.sub continuous_id)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 μ)
  simp only [sub_zero] at hint
  rw [hint, listDiff]
  ring

private lemma listDiff_const_eq_zero : ∀ (νs : List ℝ) (y : ℝ), νs ≠ [] →
    listDiff νs (fun _ => (1 : ℝ)) y = 0
  | [], _, h => absurd rfl h
  | [_], _, _ => by simp [listDiff]
  | ν :: ν' :: νs, y, _ => by
    have ih1 := listDiff_const_eq_zero (ν' :: νs) y (List.cons_ne_nil _ _)
    have ih2 := listDiff_const_eq_zero (ν' :: νs) (y - ν) (List.cons_ne_nil _ _)
    change listDiff (ν' :: νs) (fun _ => (1 : ℝ)) y -
        listDiff (ν' :: νs) (fun _ => (1 : ℝ)) (y - ν) = 0
    rw [ih1, ih2, sub_self]

lemma listDiff_pow_nonneg (μs : List ℝ) (hμ : ∀ μ ∈ μs, 0 < μ) (k : ℕ) {a : ℝ}
    (ha : μs.sum ≤ a) :
    0 ≤ listDiff μs (fun x => x ^ k) a := by
  induction μs generalizing k a with
  | nil =>
    simp only [listDiff, List.sum_nil] at ha ⊢
    exact pow_nonneg ha k
  | cons μ μs ih =>
    simp only [List.sum_cons, List.mem_cons, forall_eq_or_imp] at ha hμ
    rcases k with _ | k
    · simp only [pow_zero]
      rw [listDiff_const_eq_zero (μ :: μs) a (List.cons_ne_nil _ _)]
    · rw [listDiff_eq_integral μ μs (fun x => hasDerivAt_pow (k + 1) x) (by fun_prop) a]
      refine intervalIntegral.integral_nonneg hμ.1.le fun u hu => ?_
      have hfn : (fun x : ℝ => ((k + 1 : ℕ) : ℝ) * x ^ (k + 1 - 1)) =
          fun x => ((k + 1 : ℕ) : ℝ) * (fun y => y ^ k) x := by
        ext x; simp
      rw [hfn, listDiff_const_mul]
      exact mul_nonneg (by positivity) (ih hμ.2 k (by linarith [hu.2]))

lemma listDiff_pow_lt_zero (μs : List ℝ) {k : ℕ} (hk : k < μs.length) (a : ℝ) :
    listDiff μs (fun x => x ^ k) a = 0 := by
  induction μs generalizing k a with
  | nil => simp at hk
  | cons μ μs ih =>
    rcases k with _ | k
    · simp only [pow_zero]
      exact listDiff_const_eq_zero (μ :: μs) a (List.cons_ne_nil _ _)
    · rw [listDiff_eq_integral μ μs (fun x => hasDerivAt_pow (k + 1) x) (by fun_prop) a]
      have hz : ∀ u ∈ uIcc (0 : ℝ) μ,
          listDiff μs (fun x => ((k + 1 : ℕ) : ℝ) * x ^ (k + 1 - 1)) (a - u) = 0 := by
        intro u _
        have hk' : k < μs.length := by simpa using hk
        have hfn : (fun x : ℝ => ((k + 1 : ℕ) : ℝ) * x ^ (k + 1 - 1)) =
            fun x => ((k + 1 : ℕ) : ℝ) * (fun y => y ^ k) x := by
          ext x; simp
        rw [hfn, listDiff_const_mul, ih hk' (a - u), mul_zero]
      rw [intervalIntegral.integral_congr hz, intervalIntegral.integral_zero]

lemma listDiff_pow_length (μs : List ℝ) (a : ℝ) :
    listDiff μs (fun x => x ^ μs.length) a = (μs.length.factorial : ℝ) * μs.prod := by
  induction μs generalizing a with
  | nil => simp [listDiff]
  | cons μ μs ih =>
    rw [show (μ :: μs).length = μs.length + 1 from rfl,
      listDiff_eq_integral μ μs (fun x => hasDerivAt_pow (μs.length + 1) x) (by fun_prop) a]
    simp only [List.prod_cons, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have heq : ∀ u : ℝ,
        listDiff μs (fun x => ((μs.length : ℝ) + 1) * x ^ (μs.length + 1 - 1)) (a - u) =
          ((μs.length : ℝ) + 1) * ((μs.length.factorial : ℝ) * μs.prod) := by
      intro u
      have hfn : (fun x : ℝ => ((μs.length : ℝ) + 1) * x ^ (μs.length + 1 - 1)) =
          fun x => ((μs.length : ℝ) + 1) * (fun y => y ^ μs.length) x := by
        ext x; simp
      rw [hfn, listDiff_const_mul, ih (a - u)]
    simp_rw [heq, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    ring

/-- Cardy vacuum kernel `V(t) = ∑_s (-1)^{#s} K_{a - r_s}(t)`. -/
noncomputable def FixedWeightProblem.cardyV (prob : FixedWeightProblem) (a t : ℝ) : ℝ :=
  ∑ s : Finset (Fin prob.m), (-1 : ℝ) ^ s.card * kernelK prob.w (a - prob.shiftSum s) t

/-- Cardy reference density `ρ_C(t) = 2π V(t)`. -/
noncomputable def FixedWeightProblem.cardyDensity (prob : FixedWeightProblem) (a t : ℝ) : ℝ :=
  2 * π * prob.cardyV a t

lemma virasoro_cardyV_eq (a t : ℝ) :
    virasoroProblem.cardyV a t =
      kernelK 1 a t - 2 * kernelK 1 (a - 1) t + kernelK 1 (a - 2) t := by
  unfold FixedWeightProblem.cardyV FixedWeightProblem.shiftSum virasoroProblem
  have huniv : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [huniv]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have h01 : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
  have hs01 : ∑ l ∈ ({0, 1} : Finset (Fin 2)), (![1, 1] : Fin 2 → ℝ) l = 2 := by
    rw [Finset.sum_pair (by decide)]; norm_num
  simp only [Finset.card_empty, pow_zero, one_mul, Finset.sum_empty, sub_zero,
    Finset.card_singleton, pow_one, neg_mul, Finset.sum_singleton, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [h01, hs01]
  norm_num; ring

lemma continuous_cardyV (prob : FixedWeightProblem) (a : ℝ) :
    Continuous (prob.cardyV a) := by
  unfold FixedWeightProblem.cardyV
  refine continuous_finsetSum _ fun s _ => continuous_const.mul (continuous_kernelK prob.w _)

private lemma listDiff_ofFn_eq_sum {m : ℕ} (μ : Fin m → ℝ) (F : ℝ → ℝ) (a : ℝ) :
    listDiff (List.ofFn μ) F a =
      ∑ s : Finset (Fin m), (-1 : ℝ) ^ s.card * F (a - ∑ l ∈ s, μ l) := by
  induction m generalizing a with
  | zero =>
    have huniv : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by decide
    rw [huniv]
    simp [listDiff]
  | succ m ih =>
    rw [List.ofFn_succ, listDiff, ih (fun i => μ i.succ) a, ih (fun i => μ i.succ) (a - μ 0)]
    let e : (Finset (Fin m) ⊕ Finset (Fin m)) ≃ Finset (Fin (m + 1)) :=
      { toFun := Sum.elim (Finset.map (Fin.succEmb m))
          (fun s => insert 0 (Finset.map (Fin.succEmb m) s))
        invFun := fun s =>
          if 0 ∈ s then Sum.inr ((s.erase 0).preimage Fin.succ (Fin.succ_injective m).injOn)
          else Sum.inl (s.preimage Fin.succ (Fin.succ_injective m).injOn)
        left_inv := fun x => by
          rcases x with s | s
          · dsimp only [Sum.elim_inl]
            have h0 : (0 : Fin (m + 1)) ∉ s.map (Fin.succEmb m) := by simp
            simp only [h0, ↓reduceIte]
            congr 1; ext i; simp
          · dsimp only [Sum.elim_inr]
            have h0 : (0 : Fin (m + 1)) ∈ insert 0 (s.map (Fin.succEmb m)) :=
              Finset.mem_insert_self _ _
            simp only [h0, ↓reduceIte, Finset.erase_insert (by simp : (0 : Fin (m + 1)) ∉ s.map (Fin.succEmb m))]
            congr 1; ext i; simp
        right_inv := fun s => by
          by_cases h0 : (0 : Fin (m + 1)) ∈ s
          · dsimp only
            simp only [h0, ↓reduceIte, Sum.elim_inr]
            ext i
            rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
            · simp [h0]
            · simp [Fin.succ_ne_zero]
          · dsimp only
            simp only [h0, ↓reduceIte, Sum.elim_inl]
            ext i
            rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
            · simp [h0]
            · simp }
    have he_l (s : Finset (Fin m)) : e (Sum.inl s) = Finset.map (Fin.succEmb m) s := rfl
    have he_r (s : Finset (Fin m)) : e (Sum.inr s) = insert 0 (Finset.map (Fin.succEmb m) s) := rfl
    rw [← Equiv.sum_comp e, Fintype.sum_sum_type, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun s _ => ?_
      rw [he_l, Finset.card_map, Finset.sum_map]
      simp [Fin.succEmb]
    · refine Finset.sum_congr rfl fun s _ => ?_
      have h0 : (0 : Fin (m + 1)) ∉ s.map (Fin.succEmb m) := by simp
      rw [he_r, Finset.card_insert_of_notMem h0, Finset.card_map, Finset.sum_insert h0, Finset.sum_map,
        pow_succ', neg_one_mul]
      simp only [Fin.coe_succEmb]
      ring_nf

lemma FixedWeightProblem.cardyV_eq_listDiff (prob : FixedWeightProblem) (a t : ℝ) :
    prob.cardyV a t = listDiff (List.ofFn prob.μ) (fun α => kernelK prob.w α t) a := by
  rw [listDiff_ofFn_eq_sum]
  rfl

lemma FixedWeightProblem.cardyV_eq_tsum (prob : FixedWeightProblem) (a t : ℝ) :
    prob.cardyV a t =
      (2 * π * t) ^ (prob.w - 1) *
        ∑' k : ℕ, ((4 * π ^ 2 * t) ^ k / ((k.factorial : ℝ) * ((k + prob.w - 1).factorial : ℝ))) *
          listDiff (List.ofFn prob.μ) (fun α => α ^ k) a := by
  rw [prob.cardyV_eq_listDiff]
  have hfn : (fun α => kernelK prob.w α t) =
      fun α => (2 * π * t) ^ (prob.w - 1) * ∑' k : ℕ,
        ((4 * π ^ 2 * t) ^ k / ((k.factorial : ℝ) * ((k + prob.w - 1).factorial : ℝ))) * α ^ k := by
    ext α
    unfold kernelK kernelKTerm
    congr 1
    refine tsum_congr fun k => by rw [show 4 * π ^ 2 * α * t = (4 * π ^ 2 * t) * α by ring, mul_pow]; ring
  rw [hfn, listDiff_const_mul, listDiff_tsum]
  · congr 1
    refine tsum_congr fun k => ?_
    rw [listDiff_const_mul]
  · intro α
    have hs := summable_kernelKTerm prob.w α t
    refine hs.congr fun k => ?_
    unfold kernelKTerm
    rw [show 4 * π ^ 2 * α * t = (4 * π ^ 2 * t) * α by ring, mul_pow]; ring

/-- **Lemma 4(b) positivity & lower bound (`n1:L4`)**: for `a ≥ ∑ μ_l` (`c̃ ≥ 12 S`) and `t ≥ 0`:
`V(t) ≥ c_{w,Q} t^{m + w - 1}` (in particular `V(t) ≥ 0`, and `V(t) > 0` for `t > 0`). -/
theorem FixedWeightProblem.cardyV_lower_bound (prob : FixedWeightProblem)
    {a : ℝ} (ha : prob.totalShift ≤ a) {t : ℝ} (ht : 0 ≤ t) :
    ((2 * π) ^ (prob.w - 1) * (4 * π ^ 2) ^ prob.m * (∏ l : Fin prob.m, prob.μ l) /
        ((prob.m + prob.w - 1).factorial : ℝ)) * t ^ (prob.m + prob.w - 1) ≤
      prob.cardyV a t := by
  have hw := prob.hw
  have hsum_eq : (List.ofFn prob.μ).sum = prob.totalShift := by
    unfold FixedWeightProblem.totalShift
    rw [List.sum_ofFn]
  have hμ_list : ∀ ν ∈ List.ofFn prob.μ, 0 < ν := by
    intro ν hν
    rw [List.mem_ofFn] at hν
    rcases hν with ⟨l, rfl⟩
    exact prob.hμ l
  have hprod_eq : (List.ofFn prob.μ).prod = ∏ l : Fin prob.m, prob.μ l := by
    rw [List.prod_ofFn]
  have hterm_nn : ∀ k : ℕ, 0 ≤
      ((4 * π ^ 2 * t) ^ k / ((k.factorial : ℝ) * ((k + prob.w - 1).factorial : ℝ))) *
        listDiff (List.ofFn prob.μ) (fun α => α ^ k) a := fun k =>
    mul_nonneg (div_nonneg (pow_nonneg (by positivity) k) (by positivity))
      (listDiff_pow_nonneg _ hμ_list k (hsum_eq.symm ▸ ha))
  have hsumm : Summable fun k : ℕ =>
      ((4 * π ^ 2 * t) ^ k / ((k.factorial : ℝ) * ((k + prob.w - 1).factorial : ℝ))) *
        listDiff (List.ofFn prob.μ) (fun α => α ^ k) a := by
    have hlin : ∀ α : ℝ, Summable fun k : ℕ =>
        ((4 * π ^ 2 * t) ^ k / ((k.factorial : ℝ) * ((k + prob.w - 1).factorial : ℝ))) * α ^ k := by
      intro α
      refine (summable_kernelKTerm prob.w α t).congr fun k => ?_
      unfold kernelKTerm
      rw [show 4 * π ^ 2 * α * t = (4 * π ^ 2 * t) * α by ring, mul_pow]; ring
    have hsum_fn : (fun k : ℕ =>
        ((4 * π ^ 2 * t) ^ k / ((k.factorial : ℝ) * ((k + prob.w - 1).factorial : ℝ))) *
          listDiff (List.ofFn prob.μ) (fun α => α ^ k) a) =
        fun k => ∑ s : Finset (Fin prob.m), (-1 : ℝ) ^ s.card *
          (((4 * π ^ 2 * t) ^ k / ((k.factorial : ℝ) * ((k + prob.w - 1).factorial : ℝ))) *
            (a - ∑ l ∈ s, prob.μ l) ^ k) := by
      ext k
      rw [listDiff_ofFn_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => by ring
    rw [hsum_fn]
    exact summable_sum fun s _ => (hlin (a - ∑ l ∈ s, prob.μ l)).mul_left _
  have hm_term := hsumm.le_tsum prob.m (fun k _ => hterm_nn k)
  have hm_val : listDiff (List.ofFn prob.μ) (fun α => α ^ prob.m) a =
      (prob.m.factorial : ℝ) * ∏ l : Fin prob.m, prob.μ l := by
    have h1 := listDiff_pow_length (List.ofFn prob.μ) a
    rw [List.length_ofFn, hprod_eq] at h1
    exact h1
  rw [hm_val] at hm_term
  rw [prob.cardyV_eq_tsum]
  have h1 := mul_le_mul_of_nonneg_left hm_term (pow_nonneg (by positivity : 0 ≤ 2 * π * t) (prob.w - 1))
  have hpow_t : t ^ (prob.w - 1) * t ^ prob.m = t ^ (prob.m + prob.w - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hm_ne : (prob.m.factorial : ℝ) ≠ 0 := by positivity
  have hlhs_eq : ((2 * π) ^ (prob.w - 1) * (4 * π ^ 2) ^ prob.m * (∏ l : Fin prob.m, prob.μ l) /
        ((prob.m + prob.w - 1).factorial : ℝ)) * t ^ (prob.m + prob.w - 1) =
      (2 * π * t) ^ (prob.w - 1) *
        ((4 * π ^ 2 * t) ^ prob.m / ((prob.m.factorial : ℝ) * ((prob.m + prob.w - 1).factorial : ℝ)) *
          ((prob.m.factorial : ℝ) * ∏ l : Fin prob.m, prob.μ l)) := by
    rw [← hpow_t, mul_pow, mul_pow, mul_pow]
    field_simp [hm_ne]
    ring
  exact hlhs_eq.le.trans h1

lemma FixedWeightProblem.cardyV_nonneg (prob : FixedWeightProblem)
    {a : ℝ} (ha : prob.totalShift ≤ a) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ prob.cardyV a t := by
  have hprod_pos : 0 < ∏ l : Fin prob.m, prob.μ l := Finset.prod_pos fun l _ => prob.hμ l
  have hlb := prob.cardyV_lower_bound ha ht
  have hc_nn : 0 ≤ ((2 * π) ^ (prob.w - 1) * (4 * π ^ 2) ^ prob.m * (∏ l : Fin prob.m, prob.μ l) /
      ((prob.m + prob.w - 1).factorial : ℝ)) * t ^ (prob.m + prob.w - 1) := by
    positivity
  exact hc_nn.trans hlb

lemma FixedWeightProblem.cardyV_pos (prob : FixedWeightProblem)
    {a : ℝ} (ha : prob.totalShift ≤ a) {t : ℝ} (ht : 0 < t) :
    0 < prob.cardyV a t := by
  have hprod_pos : 0 < ∏ l : Fin prob.m, prob.μ l := Finset.prod_pos fun l _ => prob.hμ l
  have hlb := prob.cardyV_lower_bound ha ht.le
  have hc_pos : 0 < ((2 * π) ^ (prob.w - 1) * (4 * π ^ 2) ^ prob.m * (∏ l : Fin prob.m, prob.μ l) /
      ((prob.m + prob.w - 1).factorial : ℝ)) * t ^ (prob.m + prob.w - 1) := by
    positivity
  exact hc_pos.trans_le hlb

lemma FixedWeightProblem.cardyV_div_pow_mono (prob : FixedWeightProblem)
    {a : ℝ} (ha : prob.totalShift ≤ a) {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht₁₂ : t₁ ≤ t₂) :
    prob.cardyV a t₁ / t₁ ^ (prob.w - 1) ≤ prob.cardyV a t₂ / t₂ ^ (prob.w - 1) := by
  have ht₂ : 0 < t₂ := ht₁.trans_le ht₁₂
  have hsum_eq : (List.ofFn prob.μ).sum = prob.totalShift := by
    unfold FixedWeightProblem.totalShift; rw [List.sum_ofFn]
  have hμ_list : ∀ ν ∈ List.ofFn prob.μ, 0 < ν := by
    intro ν hν; rw [List.mem_ofFn] at hν; rcases hν with ⟨l, rfl⟩; exact prob.hμ l
  have hdiv : ∀ t : ℝ, 0 < t → prob.cardyV a t / t ^ (prob.w - 1) =
      (2 * π) ^ (prob.w - 1) * ∑' k : ℕ,
        ((4 * π ^ 2 * t) ^ k / ((k.factorial : ℝ) * ((k + prob.w - 1).factorial : ℝ))) *
          listDiff (List.ofFn prob.μ) (fun α => α ^ k) a := by
    intro t ht
    rw [prob.cardyV_eq_tsum, mul_pow]
    have hpow_ne : t ^ (prob.w - 1) ≠ 0 := (pow_pos ht _).ne'
    field_simp [hpow_ne]
  rw [hdiv t₁ ht₁, hdiv t₂ ht₂]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsumm : ∀ t : ℝ, Summable fun k : ℕ =>
      ((4 * π ^ 2 * t) ^ k / ((k.factorial : ℝ) * ((k + prob.w - 1).factorial : ℝ))) *
        listDiff (List.ofFn prob.μ) (fun α => α ^ k) a := by
    intro t
    have hsum_fn : (fun k : ℕ =>
        ((4 * π ^ 2 * t) ^ k / ((k.factorial : ℝ) * ((k + prob.w - 1).factorial : ℝ))) *
          listDiff (List.ofFn prob.μ) (fun α => α ^ k) a) =
        fun k => ∑ s : Finset (Fin prob.m), (-1 : ℝ) ^ s.card *
          (((4 * π ^ 2 * t) ^ k / ((k.factorial : ℝ) * ((k + prob.w - 1).factorial : ℝ))) *
            (a - ∑ l ∈ s, prob.μ l) ^ k) := by
      ext k; rw [listDiff_ofFn_eq_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by ring
    rw [hsum_fn]
    refine summable_sum fun s _ => ((summable_kernelKTerm prob.w (a - ∑ l ∈ s, prob.μ l) t).congr
      fun k => ?_).mul_left _
    unfold kernelKTerm
    rw [show 4 * π ^ 2 * (a - ∑ l ∈ s, prob.μ l) * t = (4 * π ^ 2 * t) * (a - ∑ l ∈ s, prob.μ l) by ring,
      mul_pow]
    ring
  refine (hsumm t₁).tsum_le_tsum (fun k => ?_) (hsumm t₂)
  refine mul_le_mul_of_nonneg_right ?_ (listDiff_pow_nonneg _ hμ_list k (hsum_eq.symm ▸ ha))
  refine div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by gcongr) k) (by positivity)

lemma FixedWeightProblem.cardyV_le_two_pow_kernelK (prob : FixedWeightProblem)
    {a : ℝ} (ha : prob.totalShift ≤ a) {t : ℝ} (ht : 0 ≤ t) :
    prob.cardyV a t ≤ (2 ^ prob.m : ℝ) * kernelK prob.w a t := by
  unfold FixedWeightProblem.cardyV
  calc ∑ s : Finset (Fin prob.m), (-1 : ℝ) ^ s.card * kernelK prob.w (a - prob.shiftSum s) t
      ≤ ∑ _s : Finset (Fin prob.m), kernelK prob.w a t := by
        refine Finset.sum_le_sum fun s _ => ?_
        have ha_s : 0 ≤ a - prob.shiftSum s := by
          linarith [prob.shiftSum_le_totalShift s]
        have hmono : kernelK prob.w (a - prob.shiftSum s) t ≤ kernelK prob.w a t :=
          kernelK_mono_alpha ha_s (by linarith [prob.shiftSum_nonneg s]) ht
        have hnn : 0 ≤ kernelK prob.w (a - prob.shiftSum s) t := kernelK_nonneg ha_s ht
        rcases neg_one_pow_eq_or ℝ s.card with h | h <;> rw [h]
        · linarith
        · linarith
    _ = (2 ^ prob.m : ℝ) * kernelK prob.w a t := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

lemma virasoro_cardyV_le_two_Ka {a : ℝ} (ha : 2 ≤ a) {t : ℝ} (ht : 0 ≤ t) :
    virasoroProblem.cardyV a t ≤ 2 * kernelK 1 a t := by
  rw [virasoro_cardyV_eq]
  have h1 : 0 ≤ kernelK 1 (a - 1) t := kernelK_nonneg (by linarith) ht
  have h2 : kernelK 1 (a - 2) t ≤ kernelK 1 a t := kernelK_mono_alpha (by linarith) (by linarith) ht
  linarith

theorem FixedWeightProblem.cardyV_laplace (prob : FixedWeightProblem)
    (a : ℝ) {β : ℝ} (hβ : 0 < β) :
    IntegrableOn (fun t => prob.cardyV a t * Real.exp (-2 * π * β * t)) (Ioi 0) ∧
      2 * π * ∫ t in Ioi 0, prob.cardyV a t * Real.exp (-2 * π * β * t) =
        β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) * prob.nullPoly (Real.exp (-2 * π / β)) := by
  have hsum : (fun t => prob.cardyV a t * Real.exp (-2 * π * β * t)) =
      fun t => ∑ s : Finset (Fin prob.m),
        (-1 : ℝ) ^ s.card * (kernelK prob.w (a - prob.shiftSum s) t * Real.exp (-2 * π * β * t)) := by
    ext t
    unfold FixedWeightProblem.cardyV
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => by ring
  have hterm : ∀ s : Finset (Fin prob.m),
      IntegrableOn (fun t => (-1 : ℝ) ^ s.card *
        (kernelK prob.w (a - prob.shiftSum s) t * Real.exp (-2 * π * β * t))) (Ioi 0) :=
    fun s => (kernelK_laplace prob.hw (a - prob.shiftSum s) hβ).1.const_mul _
  refine ⟨?_, ?_⟩
  · rw [hsum]
    exact integrable_finsetSum _ fun s _ => hterm s
  · rw [hsum, integral_finsetSum _ fun s _ => hterm s, Finset.mul_sum]
    have hval : ∀ s : Finset (Fin prob.m),
        2 * π * ∫ t in Ioi 0, (-1 : ℝ) ^ s.card *
          (kernelK prob.w (a - prob.shiftSum s) t * Real.exp (-2 * π * β * t)) =
          β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) *
            ((-1 : ℝ) ^ s.card * (Real.exp (-2 * π / β)) ^ prob.shiftSum s) := by
      intro s
      rw [integral_const_mul, mul_left_comm, (kernelK_laplace prob.hw (a - prob.shiftSum s) hβ).2,
        ← Real.exp_mul, show (-2 * π / β) * prob.shiftSum s = -(2 * π * prob.shiftSum s / β) by ring,
        show 2 * π * (a - prob.shiftSum s) / β = 2 * π * a / β + -(2 * π * prob.shiftSum s / β) by
          ring,
        Real.exp_add]
      ring
    simp_rw [hval, ← Finset.mul_sum]
    rw [prob.nullPoly_eq_sum (Real.exp_pos _).le]

/-! ### Section 4: Radial lift, Hankel-odd test class `\overline{\mathcal A}_w`, and thermal differences -/

/-- Radial lift of `g : ℝ → ℝ` to `EuclideanSpace ℝ (Fin (2 * w))` via `t = ‖x‖² / 2`. -/
noncomputable def radialLift (w : ℕ) (g : ℝ → ℝ) (x : EuclideanSpace ℝ (Fin (2 * w))) : ℂ :=
  ((g (‖x‖ ^ 2 / 2) : ℝ) : ℂ)

/-- Real radial lift `x ↦ g (‖x‖² / 2)` on `EuclideanSpace ℝ (Fin (2 * w))`. -/
noncomputable def radialLiftReal (w : ℕ) (g : ℝ → ℝ) (x : EuclideanSpace ℝ (Fin (2 * w))) : ℝ :=
  g (‖x‖ ^ 2 / 2)

lemma radialLift_eq_ofReal (w : ℕ) (g : ℝ → ℝ) (x : EuclideanSpace ℝ (Fin (2 * w))) :
    radialLift w g x = ((radialLiftReal w g x : ℝ) : ℂ) := rfl

lemma radialLift_add (w : ℕ) (g₁ g₂ : ℝ → ℝ) :
    radialLift w (fun t => g₁ t + g₂ t) = fun x => radialLift w g₁ x + radialLift w g₂ x := by
  ext x; simp [radialLift]

lemma radialLift_smul (w : ℕ) (c : ℝ) (g : ℝ → ℝ) :
    radialLift w (fun t => c * g t) = fun x => (c : ℂ) • radialLift w g x := by
  ext x; simp [radialLift, smul_eq_mul]

lemma integrable_radialLift_iff_real (w : ℕ) (g : ℝ → ℝ) :
    Integrable (radialLift w g) ↔ Integrable (radialLiftReal w g) :=
  ⟨fun h => Complex.reCLM.integrable_comp h, fun h => Complex.ofRealCLM.integrable_comp h⟩

/-- Radial change of variables on `EuclideanSpace ℝ (Fin (2 * w))` (`w ≥ 1`) with `t = ‖x‖² / 2`:
`∫ x, h (‖x‖² / 2) = ((2 * π) ^ w / (w - 1)!) * ∫ t in Ioi 0, t ^ (w - 1) * h t`. -/
lemma integral_radialLiftReal {w : ℕ} (hw : 1 ≤ w) (h : ℝ → ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin (2 * w)), h (‖x‖ ^ 2 / 2) =
      ((2 * π) ^ w / ((w - 1).factorial : ℝ)) * ∫ t in Ioi 0, t ^ (w - 1) * h t := by
  have : Nontrivial (EuclideanSpace ℝ (Fin (2 * w))) := by
    have : Nonempty (Fin (2 * w)) := ⟨⟨0, by omega⟩⟩
    exact inferInstance
  have hrad := MeasureTheory.integral_fun_norm_addHaar
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin (2 * w))))) (fun r : ℝ => h (r ^ 2 / 2))
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * w))) = 2 * w :=
    finrank_euclideanSpace_fin
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin (2 * w)))).real (Metric.ball 0 1) =
      π ^ w / (w.factorial : ℝ) := by
    rw [Measure.real, InnerProductSpace.volume_ball_of_dim_even (k := w) hdim, ENNReal.ofReal_one,
      one_pow, one_mul, ENNReal.toReal_ofReal (by positivity)]
  rw [hdim, hvol] at hrad
  let φ : ℝ → ℝ := fun r => r ^ 2 / 2
  have himg : φ '' Ioi 0 = Ioi 0 := by
    ext t; simp only [Set.mem_image, Set.mem_Ioi, φ]
    constructor
    · rintro ⟨r, hr, rfl⟩; positivity
    · intro ht
      refine ⟨Real.sqrt (2 * t), Real.sqrt_pos.mpr (by positivity), ?_⟩
      rw [Real.sq_sqrt (by positivity)]; ring
  have hcov := integral_image_eq_integral_abs_deriv_smul (f := φ) (f' := fun r => r)
    measurableSet_Ioi
    (fun r _ => (((hasDerivAt_pow 2 r).div_const 2).congr_deriv (by ring)).hasDerivWithinAt)
    (fun r₁ hr₁ r₂ hr₂ heq => by
      have hr₁p : 0 < r₁ := Set.mem_Ioi.mp hr₁
      have hr₂p : 0 < r₂ := Set.mem_Ioi.mp hr₂
      have hsq : r₁ ^ 2 = r₂ ^ 2 := by dsimp [φ] at heq; linarith
      nlinarith)
    (fun t : ℝ => t ^ (w - 1) * h t)
  rw [himg] at hcov
  have hcov' : ∫ t in Ioi 0, t ^ (w - 1) * h t =
      (2 : ℝ) ^ (w - 1) * (1 / (2 : ℝ) ^ (2 * (w - 1))) *
        ∫ r in Ioi 0, r ^ (2 * w - 1) * h (r ^ 2 / 2) := by
    rw [hcov, ← integral_const_mul]
    have hconst_eq : ((2 : ℝ) ^ (w - 1))⁻¹ = (2 : ℝ) ^ (w - 1) * (1 / (2 : ℝ) ^ (2 * (w - 1))) := by
      have h2ne : (2 : ℝ) ≠ 0 := two_ne_zero
      rw [show 2 * (w - 1) = (w - 1) + (w - 1) by omega, pow_add]
      field_simp
    rw [← hconst_eq]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hrp : 0 < r := Set.mem_Ioi.mp hr
    rw [abs_of_pos hrp, smul_eq_mul]
    dsimp [φ]
    rw [div_pow, ← pow_mul, show 2 * (w - 1) = 2 * w - 2 by omega]
    have hpow_r : r * r ^ (2 * w - 2) = r ^ (2 * w - 1) := by
      rw [← pow_succ', show 2 * w - 2 + 1 = 2 * w - 1 by omega]
    calc r * ((r ^ (2 * w - 2) / 2 ^ (w - 1)) * h (r ^ 2 / 2))
        = (2 ^ (w - 1))⁻¹ * (r * r ^ (2 * w - 2) * h (r ^ 2 / 2)) := by ring
      _ = (2 ^ (w - 1))⁻¹ * (r ^ (2 * w - 1) * h (r ^ 2 / 2)) := by rw [hpow_r]
  rw [hrad, hcov']
  simp only [nsmul_eq_mul, smul_eq_mul]
  have hw_fac : (w.factorial : ℝ) = (w : ℝ) * ((w - 1).factorial : ℝ) := by
    have : w = (w - 1) + 1 := (Nat.sub_add_cancel hw).symm
    conv_lhs => rw [this, Nat.factorial_succ, Nat.cast_mul]
    have hcast : ((w - 1 + 1 : ℕ) : ℝ) = (w : ℝ) := by exact_mod_cast this.symm
    rw [hcast]
  have h2w : (2 : ℝ) ^ w = 2 * (2 : ℝ) ^ (w - 1) := by
    have : w = (w - 1) + 1 := (Nat.sub_add_cancel hw).symm
    conv_lhs => rw [this, pow_succ']
  have h2mul : 2 * (w - 1) = (w - 1) + (w - 1) := by omega
  have hwn : (w : ℝ) ≠ 0 := by exact_mod_cast (by omega : w ≠ 0)
  have hfacn : ((w - 1).factorial : ℝ) ≠ 0 := by positivity
  rw [hw_fac, mul_pow, h2w, h2mul, pow_add]
  push_cast
  field_simp [hwn, hfacn]

lemma integrable_radialLift_iff {w : ℕ} (hw : 1 ≤ w) (g : ℝ → ℝ) :
    Integrable (radialLift w g) ↔ IntegrableOn (fun t : ℝ => t ^ (w - 1) * g t) (Ioi 0) := by
  rw [integrable_radialLift_iff_real]
  have : Nontrivial (EuclideanSpace ℝ (Fin (2 * w))) := by
    have : Nonempty (Fin (2 * w)) := ⟨⟨0, by omega⟩⟩
    exact inferInstance
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * w))) = 2 * w :=
    finrank_euclideanSpace_fin
  have hrad := MeasureTheory.integrable_fun_norm_addHaar
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin (2 * w))))) (f := fun r : ℝ => g (r ^ 2 / 2))
  rw [hdim] at hrad
  change Integrable (fun x : EuclideanSpace ℝ (Fin (2 * w)) => g (‖x‖ ^ 2 / 2)) ↔ _
  rw [hrad]
  let φ : ℝ → ℝ := fun r => r ^ 2 / 2
  have himg : φ '' Ioi 0 = Ioi 0 := by
    ext t; simp only [Set.mem_image, Set.mem_Ioi, φ]
    constructor
    · rintro ⟨r, hr, rfl⟩; positivity
    · intro ht; refine ⟨Real.sqrt (2 * t), Real.sqrt_pos.mpr (by positivity), ?_⟩
      rw [Real.sq_sqrt (by positivity)]; ring
  have hcov := integrableOn_image_iff_integrableOn_abs_deriv_smul (f := φ) (f' := fun r => r)
    measurableSet_Ioi
    (fun r _ => (((hasDerivAt_pow 2 r).div_const 2).congr_deriv (by ring)).hasDerivWithinAt)
    (fun r₁ hr₁ r₂ hr₂ heq => by
      have hr₁p : 0 < r₁ := Set.mem_Ioi.mp hr₁
      have hr₂p : 0 < r₂ := Set.mem_Ioi.mp hr₂
      have hsq : r₁ ^ 2 = r₂ ^ 2 := by dsimp [φ] at heq; linarith
      nlinarith)
    (fun t : ℝ => t ^ (w - 1) * g t)
  rw [himg] at hcov
  rw [hcov]
  have heq : EqOn (fun r : ℝ => r ^ (2 * w - 1) • g (r ^ 2 / 2))
      (fun r : ℝ => (2 : ℝ) ^ (w - 1) * (|r| • (φ r ^ (w - 1) * g (φ r)))) (Ioi 0) := by
    intro r hr
    have hrp : 0 < r := Set.mem_Ioi.mp hr
    dsimp only [φ]
    rw [abs_of_pos hrp, smul_eq_mul, smul_eq_mul, div_pow, ← pow_mul,
      show 2 * (w - 1) = 2 * w - 2 by omega]
    have hpow_r : r * r ^ (2 * w - 2) = r ^ (2 * w - 1) := by
      rw [← pow_succ', show 2 * w - 2 + 1 = 2 * w - 1 by omega]
    calc r ^ (2 * w - 1) * g (r ^ 2 / 2)
        = (r * r ^ (2 * w - 2)) * g (r ^ 2 / 2) := by rw [hpow_r]
      _ = 2 ^ (w - 1) * (r * (r ^ (2 * w - 2) / 2 ^ (w - 1) * g (r ^ 2 / 2))) := by
          field_simp
  have heq_iff : IntegrableOn (fun r : ℝ => r ^ (2 * w - 1) • g (r ^ 2 / 2)) (Ioi 0) ↔
      IntegrableOn (fun r : ℝ => (2 : ℝ) ^ (w - 1) *
        (|r| • (φ r ^ (w - 1) * g (φ r)))) (Ioi 0) :=
    integrableOn_congr_fun heq measurableSet_Ioi
  rw [heq_iff, IntegrableOn, integrable_const_mul_iff (Ne.isUnit (by positivity : (2 : ℝ) ^ (w - 1) ≠ 0))]
  rfl

/-- Thermal difference function `Ξ_β(t) = e^{-2π β t} - β^{-w} e^{-2π t / β}`. -/
noncomputable def thermalDiff (w : ℕ) (β t : ℝ) : ℝ :=
  Real.exp (-2 * π * β * t) - β ^ (-(w : ℝ)) * Real.exp (-2 * π * t / β)

/-- Concrete Hankel-odd test class `\overline{\mathcal A}_w` at vacuum shift `a`:
real functions `g` continuous on `[0, ∞)` whose radial lift `x ↦ g(‖x‖²/2)` on `ℝ^{2w}` is
integrable and Fourier-odd (`𝓕 (radialLift w g) = -(radialLift w g)`), with finite Cardy norm
`M[g] = ∫₀^∞ |g(t)| V(t) dt < ∞`. -/
structure TestClass (prob : FixedWeightProblem) (a : ℝ) (g : ℝ → ℝ) : Prop where
  cont : ContinuousOn g (Ici 0)
  int_lift : Integrable (radialLift prob.w g)
  fourier_odd : 𝓕 (radialLift prob.w g) = -(radialLift prob.w g)
  int_cardy : IntegrableOn (fun t => |g t| * prob.cardyV a t) (Ioi 0)

/-- Cardy norm `M[g] = ∫₀^∞ |g(t)| V(t) dt`. -/
noncomputable def FixedWeightProblem.cardyNorm (prob : FixedWeightProblem) (a : ℝ)
    (g : ℝ → ℝ) : ℝ :=
  ∫ t in Ioi 0, |g t| * prob.cardyV a t

/-- Vacuum pairing `g_vac = -2π ∫₀^∞ g(t) V(t) dt`. -/
noncomputable def FixedWeightProblem.gVac (prob : FixedWeightProblem) (a : ℝ)
    (g : ℝ → ℝ) : ℝ :=
  -2 * π * ∫ t in Ioi 0, g t * prob.cardyV a t

lemma FixedWeightProblem.cardyNorm_nonneg (prob : FixedWeightProblem) {a : ℝ}
    (ha : prob.totalShift ≤ a) (g : ℝ → ℝ) :
    0 ≤ prob.cardyNorm a g := by
  unfold FixedWeightProblem.cardyNorm
  exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg (abs_nonneg _) (prob.cardyV_nonneg ha (mem_Ioi.mp ht).le)

private lemma fourier_add_fn {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {f₁ f₂ : V → ℂ} (h₁ : Integrable f₁) (h₂ : Integrable f₂) :
    𝓕 (fun x => f₁ x + f₂ x) = 𝓕 f₁ + 𝓕 f₂ := by
  ext w
  simp only [Real.fourier_eq, Pi.add_apply]
  have hi1 : Integrable (fun v : V => 𝐞 (-⟪v, w⟫) • f₁ v) :=
    (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (L := innerₗ V) continuous_inner w).2 h₁
  have hi2 : Integrable (fun v : V => 𝐞 (-⟪v, w⟫) • f₂ v) :=
    (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (L := innerₗ V) continuous_inner w).2 h₂
  simp_rw [smul_add]
  exact integral_add hi1 hi2

private lemma fourier_smul_fn {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (c : ℂ) (f : V → ℂ) :
    𝓕 (fun x => c • f x) = c • 𝓕 f := by
  ext w
  simp only [Real.fourier_eq, Pi.smul_apply]
  simp_rw [smul_comm _ c]
  exact integral_smul c _

lemma TestClass.add {prob : FixedWeightProblem} {a : ℝ} {g₁ g₂ : ℝ → ℝ}
    (h₁ : TestClass prob a g₁) (h₂ : TestClass prob a g₂) :
    TestClass prob a (fun t => g₁ t + g₂ t) where
  cont := h₁.cont.add h₂.cont
  int_lift := (h₁.int_lift.add h₂.int_lift).congr (Eventually.of_forall fun x => by simp [radialLift])
  fourier_odd := by
    rw [radialLift_add, fourier_add_fn h₁.int_lift h₂.int_lift, h₁.fourier_odd, h₂.fourier_odd]
    ext x; simp only [Pi.add_apply, Pi.neg_apply]; ring
  int_cardy := by
    refine (h₁.int_cardy.norm.add h₂.int_cardy.norm).mono'
      (((h₁.cont.add h₂.cont).abs.mul (continuous_cardyV prob a).continuousOn).mono
        Ioi_subset_Ici_self |>.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_abs]
    calc |g₁ t + g₂ t| * |prob.cardyV a t|
        ≤ (|g₁ t| + |g₂ t|) * |prob.cardyV a t| := by gcongr; exact abs_add_le _ _
      _ = |g₁ t| * |prob.cardyV a t| + |g₂ t| * |prob.cardyV a t| := by ring

lemma TestClass.smul {prob : FixedWeightProblem} {a : ℝ} (c : ℝ) {g : ℝ → ℝ}
    (h : TestClass prob a g) :
    TestClass prob a (fun t => c * g t) where
  cont := continuousOn_const.mul h.cont
  int_lift := (h.int_lift.smul (c : ℂ)).congr (Eventually.of_forall fun x => by simp [radialLift])
  fourier_odd := by
    rw [radialLift_smul, fourier_smul_fn, h.fourier_odd]
    ext x; simp
  int_cardy := by
    have heq : (fun t => |c * g t| * prob.cardyV a t) = fun t => |c| * (|g t| * prob.cardyV a t) := by
      ext t; rw [abs_mul, mul_assoc]
    rw [heq]
    exact h.int_cardy.const_mul |c|

private lemma fourier_radial_exp (w : ℕ) {β : ℝ} (hβ : 0 < β) :
    Integrable (radialLift w (fun t => Real.exp (-2 * π * β * t))) ∧
      𝓕 (radialLift w (fun t => Real.exp (-2 * π * β * t))) =
        ((β ^ (-(w : ℝ)) : ℝ) : ℂ) • radialLift w (fun t => Real.exp (-2 * π * t / β)) := by
  have hb : 0 < ((π * β : ℝ) : ℂ).re := by simp [Real.pi_pos, hβ]
  have hlift : radialLift w (fun t => Real.exp (-2 * π * β * t)) =
      fun x : EuclideanSpace ℝ (Fin (2 * w)) =>
        Complex.exp (-((π * β : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2) := by
    ext x
    simp only [radialLift]
    rw [Complex.ofReal_exp]
    congr 1; push_cast; ring
  have hint : Integrable (radialLift w (fun t => Real.exp (-2 * π * β * t))) := by
    rw [hlift]
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0
      (0 : EuclideanSpace ℝ (Fin (2 * w)))
  refine ⟨hint, ?_⟩
  ext ξ
  rw [hlift, fourier_gaussian_innerProductSpace hb ξ]
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * w))) / 2 : ℂ) = (w : ℂ) := by
    rw [finrank_euclideanSpace_fin]
    push_cast; ring
  rw [hdim]
  have hpi : ((π : ℝ) : ℂ) / ((π * β : ℝ) : ℂ) = ((β⁻¹ : ℝ) : ℂ) := by
    have hp : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hbc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
    push_cast; field_simp
  rw [hpi, show (w : ℂ) = ((w : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (by positivity : 0 ≤ β⁻¹), Real.inv_rpow hβ.le,
    ← Real.rpow_neg hβ.le]
  simp only [Pi.smul_apply, smul_eq_mul, radialLift]
  rw [Complex.ofReal_exp]
  congr 2; push_cast
  have hpi_ne : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hb_ne : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
  field_simp

/-- Every thermal difference `Ξ_β` (`β > 0`) belongs to `\overline{\mathcal A}_w` when `a ≥ ∑ μ_l`. -/
theorem thermalDiff_mem_TestClass (prob : FixedWeightProblem) {a : ℝ} (ha : prob.totalShift ≤ a)
    {β : ℝ} (hβ : 0 < β) :
    TestClass prob a (thermalDiff prob.w β) where
  cont := by
    unfold thermalDiff
    fun_prop
  int_lift := by
    have h1 := (fourier_radial_exp prob.w hβ).1
    have h2 := (fourier_radial_exp prob.w (inv_pos.mpr hβ)).1
    have heq : radialLift prob.w (thermalDiff prob.w β) =
        fun x => radialLift prob.w (fun t => Real.exp (-2 * π * β * t)) x -
          ((β ^ (-(prob.w : ℝ)) : ℝ) : ℂ) •
            radialLift prob.w (fun t => Real.exp (-2 * π * β⁻¹ * t)) x := by
      ext x
      simp only [radialLift, thermalDiff, smul_eq_mul, div_eq_mul_inv]
      push_cast; ring
    rw [heq]
    exact h1.sub (Integrable.smul ((β ^ (-(prob.w : ℝ)) : ℝ) : ℂ) h2)
  fourier_odd := by
    have h1 := fourier_radial_exp prob.w hβ
    have h2 := fourier_radial_exp prob.w (inv_pos.mpr hβ)
    let c : ℂ := -((β ^ (-(prob.w : ℝ)) : ℝ) : ℂ)
    let f₁ := radialLift prob.w (fun t => Real.exp (-2 * π * β * t))
    let f₂ := radialLift prob.w (fun t => Real.exp (-2 * π * β⁻¹ * t))
    have heq : radialLift prob.w (thermalDiff prob.w β) = fun x => f₁ x + c • f₂ x := by
      ext x
      simp only [f₁, f₂, c, radialLift, thermalDiff, smul_eq_mul, div_eq_mul_inv]
      push_cast; ring
    have hadd : 𝓕 (fun x => f₁ x + c • f₂ x) = 𝓕 f₁ + 𝓕 (c • f₂) :=
      fourier_add_fn h1.1 (h2.1.smul c)
    have hsmul : 𝓕 (c • f₂) = c • 𝓕 f₂ := fourier_smul_fn c f₂
    rw [heq, hadd, hsmul]
    rw [h1.2, h2.2]
    ext x
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    have hbw : ((β⁻¹ ^ (-(prob.w : ℝ)) : ℝ) : ℂ) * ((β ^ (-(prob.w : ℝ)) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, Real.inv_rpow hβ.le, Real.rpow_neg hβ.le, inv_inv,
        mul_inv_cancel₀ (Real.rpow_pos_of_pos hβ _).ne']
      simp
    have hexp : radialLift prob.w (fun t => Real.exp (-2 * π * t / β⁻¹)) x =
        radialLift prob.w (fun t => Real.exp (-2 * π * β * t)) x := by
      simp only [radialLift, div_inv_eq_mul]
      congr 2; ring
    have hexp2 : radialLift prob.w (fun t => Real.exp (-2 * π * t / β)) x =
        radialLift prob.w (fun t => Real.exp (-2 * π * β⁻¹ * t)) x := by
      simp only [radialLift, div_eq_mul_inv]
      congr 2; ring
    rw [hexp, hexp2]
    linear_combination -radialLift prob.w (fun t => Real.exp (-2 * π * β * t)) x * hbw
  int_cardy := by
    have h1 := (prob.cardyV_laplace a hβ).1
    have h2 := (prob.cardyV_laplace a (inv_pos.mpr hβ)).1
    have hsum : IntegrableOn (fun t =>
        (Real.exp (-2 * π * β * t) + β ^ (-(prob.w : ℝ)) * Real.exp (-2 * π * β⁻¹ * t)) *
          prob.cardyV a t) (Ioi 0) := by
      have heq : (fun t => (Real.exp (-2 * π * β * t) + β ^ (-(prob.w : ℝ)) * Real.exp (-2 * π * β⁻¹ * t)) *
          prob.cardyV a t) = fun t => prob.cardyV a t * Real.exp (-2 * π * β * t) +
          β ^ (-(prob.w : ℝ)) * (prob.cardyV a t * Real.exp (-2 * π * β⁻¹ * t)) := by
        ext t; ring
      rw [heq]
      exact h1.add (h2.const_mul _)
    refine hsum.mono'
      (((by unfold thermalDiff; fun_prop : Continuous (thermalDiff prob.w β)).abs.mul
        (continuous_cardyV prob a)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hV : 0 ≤ prob.cardyV a t := prob.cardyV_nonneg ha (mem_Ioi.mp ht).le
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hV)]
    unfold thermalDiff
    have htri : |Real.exp (-2 * π * β * t) - β ^ (-(prob.w : ℝ)) * Real.exp (-2 * π * t / β)| ≤
        Real.exp (-2 * π * β * t) + β ^ (-(prob.w : ℝ)) * Real.exp (-2 * π * β⁻¹ * t) := by
      calc |Real.exp (-2 * π * β * t) - β ^ (-(prob.w : ℝ)) * Real.exp (-2 * π * t / β)|
          ≤ |Real.exp (-2 * π * β * t)| + |β ^ (-(prob.w : ℝ)) * Real.exp (-2 * π * t / β)| :=
            abs_sub _ _
        _ = Real.exp (-2 * π * β * t) + β ^ (-(prob.w : ℝ)) * Real.exp (-2 * π * β⁻¹ * t) := by
            rw [abs_of_pos (Real.exp_pos _), abs_of_pos (mul_pos (Real.rpow_pos_of_pos hβ _)
              (Real.exp_pos _)), div_eq_mul_inv]
            ring_nf
    exact mul_le_mul_of_nonneg_right htri hV

lemma FixedWeightProblem.gVac_thermalDiff (prob : FixedWeightProblem) (a : ℝ) {β : ℝ}
    (hβ : 0 < β) :
    prob.gVac a (thermalDiff prob.w β) =
      Real.exp (2 * π * a * β) * prob.nullPoly (Real.exp (-2 * π * β)) -
        β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) * prob.nullPoly (Real.exp (-2 * π / β)) := by
  unfold FixedWeightProblem.gVac thermalDiff
  have h1 := prob.cardyV_laplace a hβ
  have h2 := prob.cardyV_laplace a (inv_pos.mpr hβ)
  have heq : (fun t => (Real.exp (-2 * π * β * t) - β ^ (-(prob.w : ℝ)) * Real.exp (-2 * π * t / β)) *
      prob.cardyV a t) = fun t => prob.cardyV a t * Real.exp (-2 * π * β * t) -
      β ^ (-(prob.w : ℝ)) * (prob.cardyV a t * Real.exp (-2 * π * β⁻¹ * t)) := by
    ext t; rw [div_eq_mul_inv]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => congrFun heq t),
    integral_sub h1.1 (h2.1.const_mul _), integral_const_mul]
  have h2' : 2 * π * ∫ t in Ioi 0, prob.cardyV a t * Real.exp (-2 * π * β⁻¹ * t) =
      β ^ (prob.w : ℝ) * (Real.exp (2 * π * a * β) * prob.nullPoly (Real.exp (-2 * π * β))) := by
    rw [h2.2]
    have hinv_pow : (β⁻¹) ^ (-(prob.w : ℝ)) = β ^ (prob.w : ℝ) := by
      rw [Real.inv_rpow hβ.le, Real.rpow_neg hβ.le, inv_inv]
    rw [hinv_pow, div_inv_eq_mul, show -2 * π / β⁻¹ = -2 * π * β by rw [div_inv_eq_mul], mul_assoc]
  have hbw_mul : β ^ (-(prob.w : ℝ)) * β ^ (prob.w : ℝ) = 1 := by
    rw [← Real.rpow_add hβ, neg_add_cancel, Real.rpow_zero]
  have hrearr : -2 * π * ((∫ t in Ioi 0, prob.cardyV a t * Real.exp (-2 * π * β * t)) -
        β ^ (-(prob.w : ℝ)) * ∫ t in Ioi 0, prob.cardyV a t * Real.exp (-2 * π * β⁻¹ * t)) =
      β ^ (-(prob.w : ℝ)) * (2 * π * ∫ t in Ioi 0, prob.cardyV a t * Real.exp (-2 * π * β⁻¹ * t)) -
        2 * π * ∫ t in Ioi 0, prob.cardyV a t * Real.exp (-2 * π * β * t) := by ring
  rw [hrearr, h2', h1.2, ← mul_assoc, hbw_mul, one_mul]

lemma FixedWeightProblem.gVac_add (prob : FixedWeightProblem) {a : ℝ} {g₁ g₂ : ℝ → ℝ}
    (h₁ : TestClass prob a g₁) (h₂ : TestClass prob a g₂) :
    prob.gVac a (fun t => g₁ t + g₂ t) = prob.gVac a g₁ + prob.gVac a g₂ := by
  have hint : ∀ g, TestClass prob a g → IntegrableOn (fun t => g t * prob.cardyV a t) (Ioi 0) :=
    fun g hg => hg.int_cardy.norm.mono'
      ((hg.cont.mul (continuous_cardyV prob a).continuousOn).mono Ioi_subset_Ici_self
        |>.aestronglyMeasurable measurableSet_Ioi)
      (Eventually.of_forall fun t => by simp [Real.norm_eq_abs])
  unfold FixedWeightProblem.gVac
  have heq : (fun t => (g₁ t + g₂ t) * prob.cardyV a t) =
      fun t => g₁ t * prob.cardyV a t + g₂ t * prob.cardyV a t := by ext t; ring
  rw [heq, integral_add (hint g₁ h₁) (hint g₂ h₂)]
  ring

lemma FixedWeightProblem.gVac_smul (prob : FixedWeightProblem) {a : ℝ} (c : ℝ) {g : ℝ → ℝ}
    (_h : TestClass prob a g) :
    prob.gVac a (fun t => c * g t) = c * prob.gVac a g := by
  unfold FixedWeightProblem.gVac
  have heq : (fun t => c * g t * prob.cardyV a t) = fun t => c * (g t * prob.cardyV a t) := by
    ext t; ring
  rw [heq, integral_const_mul]
  ring

/-! ### Section 5: Feasibility, thresholds `T_V`, `T_weak`, `Δ_best`, and admissible measures/spectra -/

/-- Strict feasibility of `g ∈ \overline{\mathcal A}_w` at gap `T > 0`:
`g_vac > 0` and `g ≥ 0` on `[T, ∞)`. -/
def FixedWeightProblem.IsFeasible (prob : FixedWeightProblem) (a T : ℝ) (g : ℝ → ℝ) : Prop :=
  TestClass prob a g ∧ 0 < prob.gVac a g ∧ ∀ t ≥ T, 0 ≤ g t

/-- Weak feasibility of `g ∈ \overline{\mathcal A}_w` at gap `T > 0`:
`g ≠ 0` on `[0, ∞)`, `g_vac ≥ 0`, and `g ≥ 0` on `[T, ∞)`. -/
def FixedWeightProblem.IsWeaklyFeasible (prob : FixedWeightProblem) (a T : ℝ) (g : ℝ → ℝ) : Prop :=
  TestClass prob a g ∧ (∃ t ≥ 0, g t ≠ 0) ∧ 0 ≤ prob.gVac a g ∧ ∀ t ≥ T, 0 ≤ g t

lemma FixedWeightProblem.IsFeasible.isWeaklyFeasible {prob : FixedWeightProblem}
    {a T : ℝ} {g : ℝ → ℝ} (h : prob.IsFeasible a T g) :
    prob.IsWeaklyFeasible a T g := by
  refine ⟨h.1, ?_, h.2.1.le, h.2.2⟩
  by_contra hzero
  push Not at hzero
  have hvac0 : prob.gVac a g = 0 := by
    unfold FixedWeightProblem.gVac
    have heq : EqOn (fun t => g t * prob.cardyV a t) (fun _ => 0) (Ioi 0) := fun t ht => by
      simp [hzero t (mem_Ioi.mp ht).le]
    rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_zero, mul_zero]
  linarith [h.2.1]

/-- Optimal LP gap threshold `T_V(c̃) = inf {T > 0 : ∃ g ∈ \overline{\mathcal A}_w, g_vac > 0, g|_{[T,∞)} ≥ 0}`. -/
noncomputable def FixedWeightProblem.T_V (prob : FixedWeightProblem) (cTilde : ℝ) : ℝ :=
  sInf {T : ℝ | 0 < T ∧ ∃ g, prob.IsFeasible (cTilde / 12) T g}

/-- Weak LP gap threshold `T_weak(c̃) = inf {T > 0 : ∃ g ∈ \overline{\mathcal A}_w, g ≢ 0, g_vac ≥ 0, g|_{[T,∞)} ≥ 0}`. -/
noncomputable def FixedWeightProblem.T_weak (prob : FixedWeightProblem) (cTilde : ℝ) : ℝ :=
  sInf {T : ℝ | 0 < T ∧ ∃ g, prob.IsWeaklyFeasible (cTilde / 12) T g}

/-- Optimal primary dimension gap `Δ_best(c̃) = c̃ / 12 + T_V(c̃)`. -/
noncomputable def FixedWeightProblem.Delta_best (prob : FixedWeightProblem) (cTilde : ℝ) : ℝ :=
  cTilde / 12 + prob.T_V cTilde

/-- Every fixed-weight problem with `c̃ ≥ 12 ∑ μ_l` admits a strictly feasible test, built from
two thermal differences `-Ξ_{β₂} + A Ξ_{β₁}`. -/
theorem FixedWeightProblem.feasible_nonempty (prob : FixedWeightProblem)
    {cTilde : ℝ} (hc : 12 * prob.totalShift ≤ cTilde) :
    {T : ℝ | 0 < T ∧ ∃ g, prob.IsFeasible (cTilde / 12) T g}.Nonempty := by
  let a : ℝ := cTilde / 12
  have ha : prob.totalShift ≤ a := by dsimp [a]; linarith
  have ha_nn : 0 ≤ a := prob.totalShift_nonneg.trans ha
  have hQ_lim : Tendsto (fun β : ℝ => prob.nullPoly (Real.exp (-2 * π * β))) atTop (𝓝 1) := by
    unfold FixedWeightProblem.nullPoly
    have hprod : Tendsto (fun β : ℝ => ∏ l : Fin prob.m, (1 - (Real.exp (-2 * π * β)) ^ prob.μ l))
        atTop (𝓝 (∏ _l : Fin prob.m, (1 - (0 : ℝ)))) := by
      refine tendsto_finsetProd _ fun l _ => tendsto_const_nhds.sub ?_
      have h0 : Tendsto (fun β : ℝ => Real.exp (-2 * π * β)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp <| by
          convert tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (mul_pos two_pos Real.pi_pos))
            using 1
          ext β; dsimp [id]; ring
      have hrp : Tendsto (fun β : ℝ => (Real.exp (-2 * π * β)) ^ prob.μ l) atTop (𝓝 ((0 : ℝ) ^ prob.μ l)) :=
        (Real.continuousAt_rpow_const 0 (prob.μ l) (Or.inr (prob.hμ l).le)).tendsto.comp h0
      simpa [Real.zero_rpow (prob.hμ l).ne'] using hrp
    simpa using hprod
  obtain ⟨β₀, hβ₀⟩ := (hQ_lim.eventually (le_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).exists_forall_of_atTop
  let β₁ : ℝ := max 4 β₀
  have hβ₁_ge4 : 4 ≤ β₁ := le_max_left _ _
  have hβ₁_pos : 0 < β₁ := by linarith
  have hβ₁_gt1 : 1 < β₁ := by linarith
  have hQ₁ : 1 / 2 ≤ prob.nullPoly (Real.exp (-2 * π * β₁)) :=
    hβ₀ β₁ (le_max_right _ _)
  have hvac₁_pos : 0 < prob.gVac a (thermalDiff prob.w β₁) := by
    rw [prob.gVac_thermalDiff a hβ₁_pos]
    have hQ₂_le : prob.nullPoly (Real.exp (-2 * π / β₁)) ≤ 1 :=
      prob.nullPoly_le_one (Real.exp_pos _).le (Real.exp_le_one_iff.mpr
        (div_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) hβ₁_pos.le))
    have hbw_le : β₁ ^ (-(prob.w : ℝ)) ≤ 1 / 4 := by
      rw [Real.rpow_neg hβ₁_pos.le, one_div]
      have hpow : (4 : ℝ) ≤ β₁ ^ (prob.w : ℝ) := by
        calc (4 : ℝ) = (4 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 4).symm
          _ ≤ β₁ ^ (1 : ℝ) := Real.rpow_le_rpow (by norm_num) hβ₁_ge4 zero_le_one
          _ ≤ β₁ ^ (prob.w : ℝ) := Real.rpow_le_rpow_of_exponent_le hβ₁_gt1.le
              (by exact_mod_cast prob.hw)
      exact inv_anti₀ (by norm_num) hpow
    have hexp_le : Real.exp (2 * π * a / β₁) ≤ Real.exp (2 * π * a * β₁) := by
      refine Real.exp_le_exp.mpr ?_
      rw [div_eq_mul_inv]
      have hinv : β₁⁻¹ ≤ β₁ := (inv_le_one_of_one_le₀ hβ₁_gt1.le).trans hβ₁_gt1.le
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    have h1 : Real.exp (2 * π * a * β₁) * (1 / 2) ≤
        Real.exp (2 * π * a * β₁) * prob.nullPoly (Real.exp (-2 * π * β₁)) :=
      mul_le_mul_of_nonneg_left hQ₁ (Real.exp_pos _).le
    have h2 : β₁ ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β₁) *
        prob.nullPoly (Real.exp (-2 * π / β₁)) ≤
        (1 / 4) * Real.exp (2 * π * a * β₁) := by
      have hsub_le : β₁ ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β₁) ≤
          (1 / 4) * Real.exp (2 * π * a * β₁) :=
        mul_le_mul hbw_le hexp_le (Real.exp_pos _).le (by norm_num)
      calc β₁ ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β₁) *
            prob.nullPoly (Real.exp (-2 * π / β₁))
          ≤ β₁ ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β₁) * 1 :=
            mul_le_mul_of_nonneg_left hQ₂_le (mul_nonneg (Real.rpow_nonneg hβ₁_pos.le _)
              (Real.exp_pos _).le)
        _ = β₁ ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β₁) := mul_one _
        _ ≤ (1 / 4) * Real.exp (2 * π * a * β₁) := hsub_le
    linarith [Real.exp_pos (2 * π * a * β₁)]
  let β₂ : ℝ := 2 * β₁
  have hβ₂_pos : 0 < β₂ := by positivity
  let A : ℝ := (|prob.gVac a (thermalDiff prob.w β₂)| + 1) / prob.gVac a (thermalDiff prob.w β₁)
  have hA_pos : 0 < A := div_pos (by positivity) hvac₁_pos
  let g : ℝ → ℝ := fun t => -thermalDiff prob.w β₂ t + A * thermalDiff prob.w β₁ t
  have hg_mem : TestClass prob a g := by
    have h1 := (thermalDiff_mem_TestClass prob ha hβ₂_pos).smul (-1)
    have h2 := (thermalDiff_mem_TestClass prob ha hβ₁_pos).smul A
    have hadd := h1.add h2
    refine ⟨hadd.cont.congr (fun t _ => by simp [g]), ?_, ?_, ?_⟩
    · exact hadd.int_lift.congr (Eventually.of_forall fun x => by simp [radialLift, g])
    · have heq : radialLift prob.w g =
          radialLift prob.w (fun t => (-1) * thermalDiff prob.w β₂ t + A * thermalDiff prob.w β₁ t) := by
        ext x; simp [radialLift, g]
      rw [heq, hadd.fourier_odd]
    · exact hadd.int_cardy.congr_fun (fun t _ => by simp [g]) measurableSet_Ioi
  have hg_vac : 0 < prob.gVac a g := by
    have h1 := (thermalDiff_mem_TestClass prob ha hβ₂_pos).smul (-1)
    have h2 := (thermalDiff_mem_TestClass prob ha hβ₁_pos).smul A
    have heq : g = fun t => (-1) * thermalDiff prob.w β₂ t + A * thermalDiff prob.w β₁ t := by
      ext t; ring
    rw [heq, prob.gVac_add h1 h2, prob.gVac_smul (-1) (thermalDiff_mem_TestClass prob ha hβ₂_pos),
      prob.gVac_smul A (thermalDiff_mem_TestClass prob ha hβ₁_pos)]
    have hA_mul : A * prob.gVac a (thermalDiff prob.w β₁) =
        |prob.gVac a (thermalDiff prob.w β₂)| + 1 :=
      div_mul_cancel₀ _ hvac₁_pos.ne'
    have hneg_abs := le_abs_self (prob.gVac a (thermalDiff prob.w β₂))
    calc -1 * prob.gVac a (thermalDiff prob.w β₂) + A * prob.gVac a (thermalDiff prob.w β₁)
        = -prob.gVac a (thermalDiff prob.w β₂) + (|prob.gVac a (thermalDiff prob.w β₂)| + 1) := by
          rw [hA_mul]; ring
      _ ≥ 1 := by linarith
      _ > 0 := zero_lt_one
  let c₀ : ℝ := π / β₁
  have hc₀_pos : 0 < c₀ := by positivity
  let B : ℝ := β₂ ^ (prob.w : ℝ) * (1 + A * β₁ ^ (-(prob.w : ℝ)))
  have hB_pos : 0 < B := by positivity
  let T : ℝ := max 1 (Real.log B / c₀)
  have hT_pos : 0 < T := by positivity
  refine ⟨T, hT_pos, g, hg_mem, hg_vac, fun t ht => ?_⟩
  have ht_ge1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht_nn : 0 ≤ t := by linarith
  have hlog_le : Real.log B ≤ c₀ * t := by
    have h1 : Real.log B / c₀ ≤ t := (le_max_right _ _).trans ht
    have h2 := (div_le_iff₀ hc₀_pos).mp h1
    linarith
  have hB_le : B ≤ Real.exp (c₀ * t) := by
    have := Real.exp_le_exp.mpr hlog_le
    rwa [Real.exp_log hB_pos] at this
  have hexp_diff : Real.exp (-2 * π * t / β₂) = Real.exp (c₀ * t) * Real.exp (-2 * π * t / β₁) := by
    rw [← Real.exp_add]; congr 1; dsimp [c₀, β₂]; ring
  have hbw_mul : β₂ ^ (-(prob.w : ℝ)) * β₂ ^ (prob.w : ℝ) = 1 := by
    rw [← Real.rpow_add hβ₂_pos, neg_add_cancel, Real.rpow_zero]
  have hdom : (1 + A * β₁ ^ (-(prob.w : ℝ))) * Real.exp (-2 * π * t / β₁) ≤
      β₂ ^ (-(prob.w : ℝ)) * Real.exp (-2 * π * t / β₂) := by
    rw [hexp_diff]
    calc (1 + A * β₁ ^ (-(prob.w : ℝ))) * Real.exp (-2 * π * t / β₁)
        = β₂ ^ (-(prob.w : ℝ)) * B * Real.exp (-2 * π * t / β₁) := by
          dsimp [B]; rw [← mul_assoc, hbw_mul, one_mul]
      _ ≤ β₂ ^ (-(prob.w : ℝ)) * Real.exp (c₀ * t) * Real.exp (-2 * π * t / β₁) := by
          gcongr
      _ = β₂ ^ (-(prob.w : ℝ)) * (Real.exp (c₀ * t) * Real.exp (-2 * π * t / β₁)) := by ring
  have hexp_b₂ : Real.exp (-2 * π * β₂ * t) ≤ Real.exp (-2 * π * t / β₁) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : 1 / β₁ ≤ β₂ := by
      have : 1 / β₁ ≤ 1 := div_le_one_of_le₀ hβ₁_gt1.le hβ₁_pos.le
      linarith [show (1 : ℝ) ≤ β₂ by linarith]
    have h2 : 2 * π * t / β₁ ≤ 2 * π * β₂ * t := by
      rw [div_eq_mul_inv, show 2 * π * β₂ * t = (2 * π * t) * β₂ by ring,
        show 2 * π * t * β₁⁻¹ = (2 * π * t) * (1 / β₁) by ring]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [show -2 * π * β₂ * t = -(2 * π * β₂ * t) by ring,
      show -2 * π * t / β₁ = -(2 * π * t / β₁) by ring]
    linarith
  have hA_exp : 0 ≤ A * Real.exp (-2 * π * β₁ * t) := by positivity
  dsimp [g]; unfold thermalDiff
  linarith

theorem FixedWeightProblem.T_weak_le_T_V (prob : FixedWeightProblem)
    {cTilde : ℝ} (hc : 12 * prob.totalShift ≤ cTilde) :
    prob.T_weak cTilde ≤ prob.T_V cTilde := by
  unfold FixedWeightProblem.T_weak FixedWeightProblem.T_V
  refine csInf_le_csInf ?_ (prob.feasible_nonempty hc) ?_
  · exact ⟨0, fun T hT => hT.1.le⟩
  · rintro T ⟨hT, g, hg⟩
    exact ⟨hT, g, hg.isWeaklyFeasible⟩

/-- Positive crossing measure on `[0, ∞)` with finite Laplace transform at every `β > 0`
and obeying reduced crossing against `ρ_C(t) = 2π V(t)`. -/
structure AdmissibleCrossingMeasure (prob : FixedWeightProblem) (a : ℝ) where
  ν : Measure ℝ
  supp_nonneg : ν (Iio 0) = 0
  finite_laplace : ∀ {β : ℝ}, 0 < β → IntegrableOn (fun t => Real.exp (-2 * π * β * t)) (Ici 0) ν
  crossing : ∀ {β : ℝ}, 0 < β →
    ∫ t in Ici 0, thermalDiff prob.w β t ∂ν =
      ∫ t in Ioi 0, thermalDiff prob.w β t * prob.cardyDensity a t

/-- Admissible discrete spectrum `(t_n, d_n)` with `d_n > 0`, `t_n > -a`, finite `Zhat(β)`,
and modular `S` invariance `Zhat(β) = β^{-w} Zhat(1/β)` (`Theorem FW-C`). -/
structure AdmissibleSpectrum (prob : FixedWeightProblem) (a : ℝ) where
  ι : Type*
  [countable_ι : Countable ι]
  t : ι → ℝ
  d : ι → ℝ
  hd_pos : ∀ n, 0 < d n
  ht_gt : ∀ n, -a < t n
  locally_finite : ∀ R : ℝ, Set.Finite {n : ι | t n ≤ R}
  summable_thermal : ∀ {β : ℝ}, 0 < β → Summable fun n => d n * Real.exp (-2 * π * β * t n)
  crossing : ∀ {β : ℝ}, 0 < β →
    Real.exp (2 * π * a * β) * prob.nullPoly (Real.exp (-2 * π * β)) +
        ∑' n, d n * Real.exp (-2 * π * β * t n) =
      β ^ (-(prob.w : ℝ)) *
        (Real.exp (2 * π * a / β) * prob.nullPoly (Real.exp (-2 * π / β)) +
          ∑' n, d n * Real.exp (-2 * π * (t n) / β))

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Crossing.kernelK_laplace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.kernelK_laplace

/-- info: 'FormalResearch.ModularBootstrap.Crossing.FixedWeightProblem.cardyV_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.FixedWeightProblem.cardyV_lower_bound

/-- info: 'FormalResearch.ModularBootstrap.Crossing.thermalDiff_mem_TestClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.thermalDiff_mem_TestClass

/-- info: 'FormalResearch.ModularBootstrap.Crossing.FixedWeightProblem.feasible_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.FixedWeightProblem.feasible_nonempty

/-- info: 'FormalResearch.ModularBootstrap.Crossing.FixedWeightProblem.T_weak_le_T_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.FixedWeightProblem.T_weak_le_T_V

end FormalResearch.ModularBootstrap.Crossing
