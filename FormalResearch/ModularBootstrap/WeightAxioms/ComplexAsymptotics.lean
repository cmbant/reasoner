module

public import FormalResearch.ModularBootstrap.WeightAxioms.KernelAndPositivity
public import FormalResearch.ModularBootstrap.Constants

/-!
# Complex and Real Cardy Asymptotics and Comparison Bounds (Lemma 4(c), (f))

Formalizes parts (c) and (f) of Lemma 4 (`n1:L4`) in `CFT/modular_bootstrap/paper/n1_super_virasoro.tex`
for every `prob : FixedWeightProblem`:

* `nullPolyExpC`: entire extension `Q_*(b) = ∏ l, (1 - exp(-4π μ_l b))` of `x ↦ Q(e^{-4π x})`,
  zero-free on `{b : ℂ | 0 < b.re}`, and bounded between positive constants on `[x₀, ∞)` (`x₀ > 0`).
* **Lemma 4(f)**:
  - `cardyV_asymptotic_real`: uniformly for `x ≥ x₀` (`x₀ > 0`) and `c' ≥ c₀`,
    `|V(c' x² / 3) / ((2x)^{w-1} as(c' L(x))) - Q(e^{-4π x})| ≤ C_{x₀} / c'`;
  - `cardyErrC_bound_on_box`: uniform `O(1 / c')` bound on `{b : ℂ | m₀ ≤ b.re ∧ |b.im| ≤ b.re ∧ ‖b‖ ≤ M₀}`;
  - `cardyComplexExpansion`: for every compact `I ⊂ (0, ∞)`, uniform `O_I(1 / c')` bound on a complex
    `δ`-neighbourhood of `I` together with Cauchy `O_I(1 / c')` bounds on every derivative
    `∂_b^n cardyErrC` on `I` (in particular on `closedBall (xiStar : ℂ) 0.1`);
  - `cardyV_lobe_ratio_bounds`: `x^{w-1} t^{-1/2} e^{c' L(x)} / V(t) ≍ x^{-1/2}` on `x ≥ ξ_*/2`.
* **Lemma 4(c)**:
  - `cardyV_ge_band_mul_kernelK`: `c_band * K_a^{(w)}(t) ≤ V(t)` on `[ξ̄ c', ∞)` (and `x ≥ ξ_*/2`);
  - `kernelK_le_mul_cardyV_gen`: `K_a^{(w)}(t) ≤ C_K c'^{m} V(t)` on `[4/c', ∞)` (hence also
    `≤ C_K c'^{2m} V(t)` and `≤ C (1 + c'^m) max(1, t^{-m}) V(t)`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.WeightAxioms

open Crossing Bessel ComplexBessel

/-! ### Section 1: Complex null product `Q_*(b) = Q(e^{-4π b})` -/

/-- Entire holomorphic extension `Q_*(b) = ∏ l, (1 - exp(-4π μ_l b))` of `x ↦ prob.nullPoly (exp(-4π x))`. -/
noncomputable def nullPolyExpC (prob : FixedWeightProblem) (b : ℂ) : ℂ :=
  ∏ l : Fin prob.m, (1 - Complex.exp (-4 * (Real.pi : ℂ) * (prob.μ l : ℂ) * b))

lemma nullPolyExpC_entire (prob : FixedWeightProblem) : Differentiable ℂ (nullPolyExpC prob) := by
  unfold nullPolyExpC
  refine Differentiable.fun_finsetProd fun l _ => ?_
  fun_prop

lemma nullPolyExpC_ofReal (prob : FixedWeightProblem) (x : ℝ) :
    nullPolyExpC prob (x : ℂ) = (prob.nullPoly (Real.exp (-4 * Real.pi * x)) : ℂ) := by
  unfold nullPolyExpC FixedWeightProblem.nullPoly
  push_cast
  refine Finset.prod_congr rfl fun l _ => ?_
  have hrpow : (Real.exp (-4 * Real.pi * x)) ^ prob.μ l =
      Real.exp (-4 * Real.pi * prob.μ l * x) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1; ring
  rw [hrpow, Complex.ofReal_exp]
  congr 1; push_cast; ring

lemma nullPolyExpC_ne_zero (prob : FixedWeightProblem) {b : ℂ} (hb : 0 < b.re) :
    nullPolyExpC prob b ≠ 0 := by
  unfold nullPolyExpC
  rw [Finset.prod_ne_zero_iff]
  intro l _ h0
  have heq : Complex.exp (-4 * (Real.pi : ℂ) * (prob.μ l : ℂ) * b) = 1 := sub_eq_zero.mp h0 |>.symm
  have hnorm : ‖Complex.exp (-4 * (Real.pi : ℂ) * (prob.μ l : ℂ) * b)‖ = 1 := by rw [heq, norm_one]
  rw [Complex.norm_exp] at hnorm
  have hre : (-4 * (Real.pi : ℂ) * (prob.μ l : ℂ) * b).re = -4 * Real.pi * prob.μ l * b.re := by
    have h1 : (-4 * (Real.pi : ℂ) * (prob.μ l : ℂ) : ℂ) =
        ((-4 * Real.pi * prob.μ l : ℝ) : ℂ) := by push_cast; ring
    rw [h1, Complex.re_ofReal_mul]
  rw [hre] at hnorm
  have hneg : -4 * Real.pi * prob.μ l * b.re < 0 := by
    have hμ := prob.hμ l
    exact mul_neg_of_neg_of_pos (by nlinarith [Real.pi_pos] : -4 * Real.pi * prob.μ l < 0) hb
  have hlt : Real.exp (-4 * Real.pi * prob.μ l * b.re) < 1 := Real.exp_lt_one_iff.mpr hneg
  linarith

lemma nullPoly_antitone_on_Icc' (prob : FixedWeightProblem) {q₁ q₂ : ℝ}
    (hq₁ : 0 ≤ q₁) (hq₁₂ : q₁ ≤ q₂) (hq₂ : q₂ ≤ 1) :
    prob.nullPoly q₂ ≤ prob.nullPoly q₁ := by
  unfold FixedWeightProblem.nullPoly
  have hterm : ∀ l : Fin prob.m,
      0 ≤ 1 - q₂ ^ prob.μ l ∧ 1 - q₂ ^ prob.μ l ≤ 1 - q₁ ^ prob.μ l := fun l =>
    ⟨sub_nonneg.mpr (Real.rpow_le_one (hq₁.trans hq₁₂) hq₂ (prob.hμ l).le),
     sub_le_sub_left (Real.rpow_le_rpow hq₁ hq₁₂ (prob.hμ l).le) 1⟩
  induction (Finset.univ : Finset (Fin prob.m)) using Finset.cons_induction with
  | empty => simp
  | cons a s _ha ih =>
    rw [Finset.prod_cons, Finset.prod_cons]
    have ha' := hterm a
    have hs₂ : 0 ≤ ∏ x ∈ s, (1 - q₂ ^ prob.μ x) :=
      Finset.prod_nonneg fun x _ => (hterm x).1
    exact mul_le_mul ha'.2 ih hs₂ (ha'.1.trans ha'.2)

lemma nullPoly_exp_bounds (prob : FixedWeightProblem) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    0 < prob.nullPoly (Real.exp (-4 * Real.pi * x₀)) ∧
      ∀ {x : ℝ}, x₀ ≤ x →
        prob.nullPoly (Real.exp (-4 * Real.pi * x₀)) ≤ prob.nullPoly (Real.exp (-4 * Real.pi * x)) ∧
        prob.nullPoly (Real.exp (-4 * Real.pi * x)) ≤ 1 := by
  have hq0_pos : 0 < Real.exp (-4 * Real.pi * x₀) := Real.exp_pos _
  have hq0_lt1 : Real.exp (-4 * Real.pi * x₀) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  refine ⟨prob.nullPoly_pos hq0_pos.le hq0_lt1, fun {x} hx => ?_⟩
  have hqx_pos : 0 ≤ Real.exp (-4 * Real.pi * x) := (Real.exp_pos _).le
  have hqx_le : Real.exp (-4 * Real.pi * x) ≤ Real.exp (-4 * Real.pi * x₀) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  exact ⟨nullPoly_antitone_on_Icc' prob hqx_pos hqx_le hq0_lt1.le,
    prob.nullPoly_le_one hqx_pos (hqx_le.trans hq0_lt1.le)⟩

/-! ### Section 2: Exact term identity and elementary factor bounds -/

private lemma kernelKC_shift_eq_besselIC (w : ℕ) (_hw : 1 ≤ w) {c' r : ℝ}
    (hc' : 0 < c') (hr : 12 * r / c' ≤ 1 / 2) (b : ℂ) :
    let rad : ℝ := Real.sqrt (1 - 12 * r / c')
    let z₀ : ℂ := (c' : ℂ) * tipL b
    kernelKC w ((c' / 12 - r : ℝ) : ℂ) ((c' : ℂ) * b ^ 2 / 3) =
      (2 * b) ^ (w - 1) * ((rad ^ (-((w - 1 : ℕ) : ℤ)) : ℝ) : ℂ) * besselIC (w - 1) ((rad : ℂ) * z₀) := by
  intro rad z₀
  have hrad_pos : 0 < rad := Real.sqrt_pos.mpr (by linarith)
  have hrad_sq : rad ^ 2 = 1 - 12 * r / c' := Real.sq_sqrt (by linarith)
  unfold kernelKC besselIC
  have hz_sq : ((rad : ℂ) * z₀) ^ 2 / 4 =
      4 * (Real.pi : ℂ) ^ 2 * ((c' / 12 - r : ℝ) : ℂ) * ((c' : ℂ) * b ^ 2 / 3) := by
    have hrad_c : (rad : ℂ) ^ 2 = ((1 - 12 * r / c' : ℝ) : ℂ) := by exact_mod_cast hrad_sq
    rw [mul_pow, hrad_c]
    dsimp [z₀]; unfold tipL
    push_cast
    field_simp [hc'.ne']
    ring
  rw [hz_sq]
  have hrad_inv : ((rad ^ (-((w - 1 : ℕ) : ℤ)) : ℝ) : ℂ) * (rad : ℂ) ^ (w - 1) = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, zpow_neg, zpow_natCast,
      inv_mul_cancel₀ (pow_ne_zero _ hrad_pos.ne')]
    rfl
  have hpref : (2 * b) ^ (w - 1) * ((rad ^ (-((w - 1 : ℕ) : ℤ)) : ℝ) : ℂ) * (((rad : ℂ) * z₀) / 2) ^ (w - 1) =
      (2 * (Real.pi : ℂ) * ((c' : ℂ) * b ^ 2 / 3)) ^ (w - 1) := by
    have hzs : ((rad : ℂ) * z₀) / 2 = (rad : ℂ) * ((c' : ℂ) * (Real.pi : ℂ) * b / 3) := by
      dsimp [z₀]; unfold tipL; push_cast; ring
    rw [hzs]
    nth_rw 2 [mul_pow]
    calc (2 * b) ^ (w - 1) * ((rad ^ (-((w - 1 : ℕ) : ℤ)) : ℝ) : ℂ) *
          ((rad : ℂ) ^ (w - 1) * ((c' : ℂ) * (Real.pi : ℂ) * b / 3) ^ (w - 1))
        = (((rad ^ (-((w - 1 : ℕ) : ℤ)) : ℝ) : ℂ) * (rad : ℂ) ^ (w - 1)) *
            ((2 * b) ^ (w - 1) * ((c' : ℂ) * (Real.pi : ℂ) * b / 3) ^ (w - 1)) := by ring
      _ = 1 * (2 * b * ((c' : ℂ) * (Real.pi : ℂ) * b / 3)) ^ (w - 1) := by
          rw [hrad_inv, ← mul_pow]
      _ = (2 * (Real.pi : ℂ) * ((c' : ℂ) * b ^ 2 / 3)) ^ (w - 1) := by ring
  calc (2 * (Real.pi : ℂ) * ((c' : ℂ) * b ^ 2 / 3)) ^ (w - 1) *
        besselSC (w - 1) (4 * (Real.pi : ℂ) ^ 2 * ((c' / 12 - r : ℝ) : ℂ) * ((c' : ℂ) * b ^ 2 / 3))
      = ((2 * b) ^ (w - 1) * ((rad ^ (-((w - 1 : ℕ) : ℤ)) : ℝ) : ℂ) * (((rad : ℂ) * z₀) / 2) ^ (w - 1)) *
          besselSC (w - 1) (4 * (Real.pi : ℂ) ^ 2 * ((c' / 12 - r : ℝ) : ℂ) * ((c' : ℂ) * b ^ 2 / 3)) := by
          rw [hpref]
    _ = _ := by ring

private lemma rad_neg_pow_bounds (k : ℕ) {rad u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2)
    (hrad : rad = Real.sqrt (1 - u)) :
    (1 : ℝ) / 2 < rad ∧ rad ≤ 1 ∧
      1 ≤ rad ^ (-((k : ℝ) + 1 / 2)) ∧
      rad ^ (-((k : ℝ) + 1 / 2)) ≤ 2 ^ (k + 1) ∧
      |rad ^ (-((k : ℝ) + 1 / 2)) - 1| ≤ ((k : ℝ) + 1) * 2 ^ (k + 1) * u := by
  have h1u : 1 / 2 ≤ 1 - u := by linarith
  have hrad_pos : 0 < rad := by rw [hrad]; exact Real.sqrt_pos.mpr (by linarith)
  have hrad_gt_half : 1 / 2 < rad := by
    rw [hrad, show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by norm_num [Real.sqrt_div, Real.sqrt_one]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hrad_le1 : rad ≤ 1 := by rw [hrad]; exact Real.sqrt_le_one.mpr (by linarith)
  have hrad_ge1 : 1 ≤ rad ^ (-((k : ℝ) + 1 / 2)) := by
    rw [Real.rpow_neg hrad_pos.le, one_le_inv₀ (Real.rpow_pos_of_pos hrad_pos _)]
    exact Real.rpow_le_one hrad_pos.le hrad_le1 (by positivity)
  have hrad_inv_le : rad⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hrad_pos (by positivity)]; linarith
  have hrad_pow_le_nat : rad ^ (-((k : ℝ) + 1 / 2)) ≤ rad ^ (-((k + 1 : ℕ) : ℝ)) := by
    rw [Real.rpow_neg hrad_pos.le, Real.rpow_neg hrad_pos.le]
    refine inv_anti₀ (Real.rpow_pos_of_pos hrad_pos _) ?_
    exact Real.rpow_le_rpow_of_exponent_ge hrad_pos hrad_le1 (by push_cast; linarith)
  have hrad_nat_eq : rad ^ (-((k + 1 : ℕ) : ℝ)) = (rad⁻¹) ^ (k + 1) := by
    rw [Real.rpow_neg hrad_pos.le, Real.rpow_natCast, inv_pow]
  have hrad_ub : rad ^ (-((k : ℝ) + 1 / 2)) ≤ 2 ^ (k + 1) := by
    refine hrad_pow_le_nat.trans ?_
    rw [hrad_nat_eq]
    exact pow_le_pow_left₀ (by positivity) hrad_inv_le (k + 1)
  have hgeom : 1 - rad ^ (k + 1) ≤ ((k : ℝ) + 1) * (1 - rad) := by
    have h := geom_sum_mul_neg rad (k + 1)
    have hsum_le : ∑ i ∈ Finset.range (k + 1), rad ^ i ≤ (k : ℝ) + 1 := by
      calc ∑ i ∈ Finset.range (k + 1), rad ^ i
          ≤ ∑ _i ∈ Finset.range (k + 1), (1 : ℝ) := by
            refine Finset.sum_le_sum fun i _ => pow_le_one₀ hrad_pos.le hrad_le1
        _ = (k : ℝ) + 1 := by simp
    have h1mr : 0 ≤ 1 - rad := sub_nonneg.mpr hrad_le1
    have hid : 1 - rad ^ (k + 1) = (1 - rad) * ∑ i ∈ Finset.range (k + 1), rad ^ i := by
      linarith
    rw [hid]
    calc (1 - rad) * ∑ i ∈ Finset.range (k + 1), rad ^ i
        ≤ (1 - rad) * ((k : ℝ) + 1) := mul_le_mul_of_nonneg_left hsum_le h1mr
      _ = ((k : ℝ) + 1) * (1 - rad) := by ring
  have h1mr_le_u : 1 - rad ≤ u := by
    have hsq : rad ^ 2 = 1 - u := by rw [hrad, Real.sq_sqrt (by linarith)]
    have hprod : (1 + rad) * (1 - rad) = u := by linarith
    have h1r : 1 ≤ 1 + rad := by linarith
    calc 1 - rad ≤ (1 + rad) * (1 - rad) := le_mul_of_one_le_left (sub_nonneg.mpr hrad_le1) h1r
      _ = u := hprod
  have herr_le : |rad ^ (-((k : ℝ) + 1 / 2)) - 1| ≤ ((k : ℝ) + 1) * 2 ^ (k + 1) * u := by
    rw [abs_of_nonneg (sub_nonneg.mpr hrad_ge1)]
    have hpow_pos : 0 < rad ^ (k + 1) := pow_pos hrad_pos _
    have h1 : rad ^ (-((k : ℝ) + 1 / 2)) - 1 ≤ (rad⁻¹) ^ (k + 1) - 1 := by linarith [hrad_pow_le_nat, hrad_nat_eq]
    have h2 : (rad⁻¹) ^ (k + 1) - 1 = (1 - rad ^ (k + 1)) * (rad⁻¹) ^ (k + 1) := by
      rw [inv_pow]; field_simp [hpow_pos.ne']
    have h3 : (rad⁻¹) ^ (k + 1) ≤ 2 ^ (k + 1) := pow_le_pow_left₀ (by positivity) hrad_inv_le _
    calc rad ^ (-((k : ℝ) + 1 / 2)) - 1
        ≤ (1 - rad ^ (k + 1)) * (rad⁻¹) ^ (k + 1) := by linarith [h1, h2]
      _ ≤ (((k : ℝ) + 1) * (1 - rad)) * 2 ^ (k + 1) := by
          exact mul_le_mul hgeom h3 (by positivity) (by positivity)
      _ ≤ (((k : ℝ) + 1) * u) * 2 ^ (k + 1) := by gcongr
      _ = ((k : ℝ) + 1) * 2 ^ (k + 1) * u := by ring
  exact ⟨hrad_gt_half, hrad_le1, hrad_ge1, hrad_ub, herr_le⟩

private lemma eta_bounds {r c' : ℝ} (_hc' : 0 < c') (_hr : 0 ≤ r) (hu : 12 * r / c' ≤ 1 / 2) :
    let rad := Real.sqrt (1 - 12 * r / c')
    let η := 1 - rad - 6 * r / c'
    0 ≤ η ∧ η ≤ 36 * r ^ 2 / c' ^ 2 := by
  intro rad η
  have h1u : 1 / 2 ≤ 1 - 12 * r / c' := by linarith
  have hrad_pos : 0 < rad := Real.sqrt_pos.mpr (by linarith)
  have hrad_sq : rad ^ 2 = 1 - 12 * r / c' := Real.sq_sqrt (by linarith)
  have h6 : 6 * r / c' ≤ 1 / 4 := by
    have : 6 * r / c' = (12 * r / c') / 2 := by ring
    linarith
  have h1_sub_6 : 0 ≤ 1 - 6 * r / c' := by linarith
  have hη_nn : 0 ≤ η := by
    have hsq : rad ^ 2 ≤ (1 - 6 * r / c') ^ 2 := by
      have hid : 1 - 12 * r / c' = 1 - 2 * (6 * r / c') := by ring
      rw [hrad_sq, hid]
      nlinarith [sq_nonneg (6 * r / c')]
    have hle := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq h1_sub_6, Real.sqrt_sq hrad_pos.le] at hle
    dsimp [η]; linarith
  have hη_le : η ≤ 36 * r ^ 2 / c' ^ 2 := by
    have hrad_gt : 1 / 2 ≤ rad := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by norm_num [Real.sqrt_div, Real.sqrt_one]]
      exact Real.sqrt_le_sqrt (by linarith)
    have hsum_ge1 : (1 : ℝ) ≤ (1 - 6 * r / c') + rad := by linarith
    have hdiff_sq : ((1 - 6 * r / c') + rad) * η = (6 * r / c') ^ 2 := by
      dsimp [η]; linear_combination -hrad_sq
    have hsq_le : (6 * r / c') ^ 2 = 36 * r ^ 2 / c' ^ 2 := by rw [div_pow]; ring
    nlinarith
  exact ⟨hη_nn, hη_le⟩

/-! ### Section 3: Complex Cardy asymptotic on boxes and compact intervals (`n1:L4`(f)) -/

/-- Complex bracket error:
`cardyErrC prob c' b = V(c' b^2 / 3) / ((2 b)^{w-1} as(c' L(b))) - Q_*(b)`. -/
noncomputable def cardyErrC (prob : FixedWeightProblem) (c' : ℝ) (b : ℂ) : ℂ :=
  cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) /
      ((2 * b) ^ (prob.w - 1) * asC ((c' : ℂ) * tipL b)) -
    nullPolyExpC prob b

lemma cardyErrC_differentiableOn (prob : FixedWeightProblem) {c' : ℝ} (hc' : 0 < c') :
    DifferentiableOn ℂ (cardyErrC prob c') {b : ℂ | 0 < b.re} := by
  intro b hb
  have hb_ne : b ≠ 0 := by
    intro h; change 0 < b.re at hb; rw [h, Complex.zero_re] at hb; exact lt_irrefl 0 hb
  have hV : DifferentiableAt ℂ
      (fun w : ℂ => cardyVC prob (c' / 12) ((c' : ℂ) * w ^ 2 / 3)) b :=
    (cardyVC_entire prob (c' / 12)).differentiableAt.comp b
      (((differentiableAt_id.pow 2).const_mul (c' : ℂ)).div_const 3)
  have harg_re : 0 < (2 * (Real.pi : ℂ) * ((c' : ℂ) * tipL b)).re := by
    have heq : 2 * (Real.pi : ℂ) * ((c' : ℂ) * tipL b) =
        ((4 * Real.pi ^ 2 * c' / 3 : ℝ) : ℂ) * b := by
      unfold tipL; push_cast; ring
    rw [heq, Complex.re_ofReal_mul]
    exact mul_pos (by positivity) hb
  have harg_slit : 2 * (Real.pi : ℂ) * ((c' : ℂ) * tipL b) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl harg_re)
  have harg_diff : DifferentiableAt ℂ
      (fun w : ℂ => 2 * (Real.pi : ℂ) * ((c' : ℂ) * tipL w)) b := by
    unfold tipL; fun_prop
  have hcpow_diff : DifferentiableAt ℂ
      (fun w : ℂ => (2 * (Real.pi : ℂ) * ((c' : ℂ) * tipL w)) ^ (1 / 2 : ℂ)) b :=
    harg_diff.cpow (differentiableAt_const (1 / 2 : ℂ)) harg_slit
  have hcpow_ne : (2 * (Real.pi : ℂ) * ((c' : ℂ) * tipL b)) ^ (1 / 2 : ℂ) ≠ 0 := by
    refine Complex.cpow_ne_zero_iff.mpr (Or.inl ?_)
    intro h0; rw [h0, Complex.zero_re] at harg_re; exact lt_irrefl 0 harg_re
  have has_diff : DifferentiableAt ℂ (fun w : ℂ => asC ((c' : ℂ) * tipL w)) b := by
    unfold asC
    unfold tipL at hcpow_diff hcpow_ne ⊢
    have hexp_diff : DifferentiableAt ℂ
        (fun w : ℂ => Complex.exp ((c' : ℂ) * (((2 * Real.pi / 3 : ℝ) : ℂ) * w))) b := by
      fun_prop
    exact hexp_diff.div hcpow_diff hcpow_ne
  have has_ne : asC ((c' : ℂ) * tipL b) ≠ 0 := by
    unfold asC; exact div_ne_zero (Complex.exp_ne_zero _) hcpow_ne
  have hden_diff : DifferentiableAt ℂ
      (fun w : ℂ => (2 * w) ^ (prob.w - 1) * asC ((c' : ℂ) * tipL w)) b :=
    ((differentiableAt_id.const_mul 2).pow (prob.w - 1)).mul has_diff
  have hden_ne : (2 * b) ^ (prob.w - 1) * asC ((c' : ℂ) * tipL b) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (mul_ne_zero two_ne_zero hb_ne)) has_ne
  exact ((hV.div hden_diff hden_ne).sub (nullPolyExpC_entire prob b)).differentiableWithinAt

private lemma norm_exp_sub_one_le_of_re_nonpos'' {w : ℂ} (hw : w.re ≤ 0) :
    ‖Complex.exp w - 1‖ ≤ 2 * ‖w‖ := by
  by_cases h1 : ‖w‖ ≤ 1
  · exact Complex.norm_exp_sub_one_le h1
  · have : 1 ≤ ‖w‖ := le_of_not_ge h1
    have hexp_le : ‖Complex.exp w‖ ≤ 1 := by
      rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr hw
    calc ‖Complex.exp w - 1‖ ≤ ‖Complex.exp w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; linarith
      _ = 2 := by norm_num
      _ ≤ 2 * ‖w‖ := by linarith

/-- Uniform complex bracket error bound for `cardyErrC` on sectorial boxes
`{b : ℂ | m₀ ≤ b.re ∧ |b.im| ≤ b.re ∧ ‖b‖ ≤ M₀}` (`0 < m₀`). -/
theorem cardyErrC_bound_on_box (prob : FixedWeightProblem) {m₀ M₀ : ℝ}
    (hm : 0 < m₀) (hM : 0 ≤ M₀) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {b : ℂ}, m₀ ≤ b.re → |b.im| ≤ b.re → ‖b‖ ≤ M₀ →
        ‖cardyErrC prob c' b‖ ≤ C / c' := by
  have hw := prob.hw
  obtain ⟨C_I, hCI_nn, hI_bd⟩ := besselIC_sector_asymptotic_of_re_pos (prob.w - 1)
    (κ := 1 / Real.sqrt 2) (by positivity)
  let S : ℝ := prob.totalShift
  have hS_nn : 0 ≤ S := prob.totalShift_nonneg
  let k : ℕ := prob.w - 1
  let c₀ : ℝ := max (max 1 (24 * S)) (6 / m₀)
  let C_s : ℝ := 2 ^ (k + 2) * C_I / m₀ + 12 * ((k : ℝ) + 1) * 2 ^ (k + 1) * S + 605 * S ^ 2 * M₀
  let C : ℝ := (2 ^ prob.m : ℝ) * C_s
  refine ⟨C, c₀, by dsimp [C, C_s]; positivity, le_max_left _ _, fun {c'} hc' {b} hm_b him_b hM_b => ?_⟩
  have hc1 : 1 ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hc')
  have hcS : 24 * S ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans hc')
  have hc6m : 6 / m₀ ≤ c' := (le_max_right _ _).trans hc'
  have hc'_pos : 0 < c' := by linarith
  have hb_pos : 0 < b.re := lt_of_lt_of_le hm hm_b
  have hb_ne : b ≠ 0 := by intro h; rw [h, Complex.zero_re] at hb_pos; exact lt_irrefl 0 hb_pos
  let z₀ : ℂ := (c' : ℂ) * tipL b
  have hz₀_eq : z₀ = ((c' * (2 * Real.pi / 3) : ℝ) : ℂ) * b := by
    dsimp [z₀]; unfold tipL; push_cast; ring
  have hc2pi3_pos : 0 < c' * (2 * Real.pi / 3) := by positivity
  have hz₀_re : z₀.re = (c' * (2 * Real.pi / 3)) * b.re := by
    rw [hz₀_eq, Complex.re_ofReal_mul]
  have hz₀_im : z₀.im = (c' * (2 * Real.pi / 3)) * b.im := by
    rw [hz₀_eq, Complex.im_ofReal_mul]
  have hz₀_norm_le : ‖z₀‖ ≤ c' * (2.1 * M₀) := by
    rw [hz₀_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc2pi3_pos]
    have h2pi3_le : 2 * Real.pi / 3 ≤ 2.1 := by nlinarith [Real.pi_lt_d4]
    calc c' * (2 * Real.pi / 3) * ‖b‖ ≤ c' * 2.1 * M₀ :=
          mul_le_mul (mul_le_mul_of_nonneg_left h2pi3_le hc'_pos.le) hM_b (norm_nonneg _)
            (by positivity)
      _ = c' * (2.1 * M₀) := by ring
  have hz₀_re_ge : 2 * c' * m₀ ≤ z₀.re := by
    rw [hz₀_re]
    have h2pi3_ge : 2 ≤ 2 * Real.pi / 3 := by nlinarith [Real.pi_gt_d4]
    calc 2 * c' * m₀ = c' * 2 * m₀ := by ring
      _ ≤ (c' * (2 * Real.pi / 3)) * m₀ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2pi3_ge hc'_pos.le) hm.le
      _ ≤ (c' * (2 * Real.pi / 3)) * b.re := by gcongr
  have hz₀_pos : 0 < z₀.re := lt_of_lt_of_le (by positivity) hz₀_re_ge
  have hz₀_ne : z₀ ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz₀_pos; exact lt_irrefl 0 hz₀_pos
  have hpi_ne : (2 * (Real.pi : ℂ) * z₀) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) hz₀_ne
  have has0_ne : asC z₀ ≠ 0 := by
    unfold asC
    exact div_ne_zero (Complex.exp_ne_zero _) (Complex.cpow_ne_zero_iff.mpr (Or.inl hpi_ne))
  have hs_bound : ∀ s : Finset (Fin prob.m), ∃ err_s : ℂ,
      kernelKC prob.w ((c' / 12 - prob.shiftSum s : ℝ) : ℂ) ((c' : ℂ) * b ^ 2 / 3) =
        (2 * b) ^ k * asC z₀ * (Complex.exp (-4 * (Real.pi : ℂ) * (prob.shiftSum s : ℂ) * b) + err_s) ∧
      ‖err_s‖ ≤ C_s / c' := by
    intro s
    set r : ℝ := prob.shiftSum s
    have hr_nn : 0 ≤ r := prob.shiftSum_nonneg s
    have hr_le : r ≤ S := prob.shiftSum_le_totalShift s
    have hu_nn : 0 ≤ 12 * r / c' := by positivity
    have hu_le : 12 * r / c' ≤ 1 / 2 := by
      rw [div_le_iff₀ hc'_pos]; linarith
    let rad : ℝ := Real.sqrt (1 - 12 * r / c')
    obtain ⟨hrad_gt, hrad_le1, hrad_ge1, hrad_ub, hrad_err⟩ :=
      rad_neg_pow_bounds k hu_nn hu_le rfl
    have hrad_pos : 0 < rad := by linarith
    let zs : ℂ := (rad : ℂ) * z₀
    have hK_eq := kernelKC_shift_eq_besselIC prob.w hw hc'_pos hu_le b
    dsimp only at hK_eq
    change kernelKC prob.w ((c' / 12 - r : ℝ) : ℂ) ((c' : ℂ) * b ^ 2 / 3) =
        (2 * b) ^ k * ((rad ^ (-(k : ℤ)) : ℝ) : ℂ) * besselIC k zs at hK_eq
    have hzs_pos : 0 < zs.re := by
      dsimp [zs]; rw [Complex.re_ofReal_mul]; exact mul_pos hrad_pos hz₀_pos
    have hzs_sec : (1 / Real.sqrt 2) * ‖zs‖ ≤ zs.re := by
      have hnorm_sq : ‖zs‖ ^ 2 ≤ 2 * zs.re ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        have him : |zs.im| ≤ zs.re := by
          dsimp [zs]; rw [Complex.re_ofReal_mul, Complex.im_ofReal_mul, abs_mul,
            abs_of_pos hrad_pos, hz₀_im, hz₀_re, abs_mul, abs_of_pos hc2pi3_pos]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left him_b hc2pi3_pos.le) hrad_pos.le
        nlinarith [abs_le.mp him]
      rw [one_div_mul_eq_div, div_le_iff₀ (Real.sqrt_pos.mpr zero_lt_two)]
      have h1 := Real.sqrt_le_sqrt hnorm_sq
      rwa [Real.sqrt_sq (norm_nonneg zs), Real.sqrt_mul zero_le_two,
        Real.sqrt_sq hzs_pos.le, mul_comm] at h1
    have hzs_norm : m₀ * c' ≤ ‖zs‖ := by
      have hzs_re_eq : zs.re = rad * z₀.re := Complex.re_ofReal_mul rad z₀
      calc m₀ * c' = (1 / 2 : ℝ) * (2 * c' * m₀) := by ring
        _ ≤ rad * z₀.re := mul_le_mul hrad_gt.le hz₀_re_ge (by positivity) hrad_pos.le
        _ = zs.re := hzs_re_eq.symm
        _ ≤ |zs.re| := le_abs_self _
        _ ≤ ‖zs‖ := Complex.abs_re_le_norm zs
    have hI_z := hI_bd zs hzs_pos hzs_sec
    have has_ratio : asC zs = asC z₀ *
        (((rad ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-((1 - rad : ℝ) : ℂ) * z₀)) := by
      unfold asC
      have hden : (2 * (Real.pi : ℂ) * zs) ^ (1 / 2 : ℂ) =
          ((Real.sqrt rad : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * z₀) ^ (1 / 2 : ℂ) := by
        rw [show 2 * (Real.pi : ℂ) * zs = (rad : ℂ) * (2 * (Real.pi : ℂ) * z₀) by dsimp [zs]; ring,
          ofReal_mul_cpow hrad_pos (2 * (Real.pi : ℂ) * z₀) (1 / 2 : ℂ),
          show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
          ← Complex.ofReal_cpow hrad_pos.le, ← Real.sqrt_eq_rpow]
      have hexp_zs : Complex.exp zs =
          Complex.exp z₀ * Complex.exp (-((1 - rad : ℝ) : ℂ) * z₀) := by
        rw [← Complex.exp_add]; congr 1; dsimp [zs]; push_cast; ring
      have hsqrt_inv : ((Real.sqrt rad : ℝ) : ℂ)⁻¹ = ((rad ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
        rw [Real.sqrt_eq_rpow, ← Complex.ofReal_inv, ← Real.rpow_neg hrad_pos.le]
      rw [hden, hexp_zs, ← hsqrt_inv]
      have hsqrt_c : ((Real.sqrt rad : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hrad_pos).ne'
      have h2pi_c : (2 * (Real.pi : ℂ) * z₀) ^ (1 / 2 : ℂ) ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr (Or.inl hpi_ne)
      field_simp [hsqrt_c, h2pi_c]
    obtain ⟨hη_nn, hη_le⟩ := eta_bounds hc'_pos hr_nn hu_le
    let η : ℝ := 1 - rad - 6 * r / c'
    let δ : ℂ := (η : ℂ) * z₀
    have hδ_re : (-δ).re ≤ 0 := by
      rw [show (-δ).re = -(η * z₀.re) by dsimp [δ]; simp]
      exact neg_nonpos.mpr (mul_nonneg (by dsimp [η]; exact hη_nn) hz₀_pos.le)
    have hδ_norm : ‖-δ‖ ≤ 302.4 * S ^ 2 * M₀ / c' := by
      rw [norm_neg]; dsimp [δ]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hη_nn]
      have hη_S : η ≤ 144 * S ^ 2 / c' ^ 2 := hη_le.trans (by gcongr; norm_num)
      calc η * ‖z₀‖ ≤ (144 * S ^ 2 / c' ^ 2) * (c' * (2.1 * M₀)) :=
            mul_le_mul hη_S hz₀_norm_le (norm_nonneg _) (by positivity)
        _ = 302.4 * S ^ 2 * M₀ / c' := by field_simp [hc'_pos.ne']; ring
    have hexp_split : Complex.exp (-((1 - rad : ℝ) : ℂ) * z₀) =
        Complex.exp (-4 * (Real.pi : ℂ) * (r : ℂ) * b) * Complex.exp (-δ) := by
      rw [← Complex.exp_add]; congr 1
      dsimp [δ, η]; rw [hz₀_eq]; push_cast; field_simp [hc'_pos.ne']; ring
    have hmain_norm : ‖Complex.exp (-4 * (Real.pi : ℂ) * (r : ℂ) * b)‖ ≤ 1 := by
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      have h1 : (-4 * (Real.pi : ℂ) * (r : ℂ) * b).re = -4 * Real.pi * r * b.re := by
        have h2 : (-4 * (Real.pi : ℂ) * (r : ℂ) : ℂ) = ((-4 * Real.pi * r : ℝ) : ℂ) := by
          push_cast; ring
        rw [h2, Complex.re_ofReal_mul]
      rw [h1, show -4 * Real.pi * r * b.re = -(4 * Real.pi * r * b.re) by ring]
      exact neg_nonpos.mpr (by positivity)
    have hrad_comb : rad ^ (-(k : ℤ)) * rad ^ (-(1 / 2 : ℝ)) = rad ^ (-((k : ℝ) + 1 / 2)) := by
      rw [← Real.rpow_intCast rad (-(k : ℤ)), ← Real.rpow_add hrad_pos]
      congr 1; push_cast; ring
    let mainFac : ℂ := Complex.exp (-4 * (Real.pi : ℂ) * (r : ℂ) * b)
    let asympFac : ℂ := ((rad ^ (-((k : ℝ) + 1 / 2)) : ℝ) : ℂ) * Complex.exp (-((1 - rad : ℝ) : ℂ) * z₀)
    let diff1 : ℂ := ((rad ^ (-(k : ℤ)) : ℝ) : ℂ) * (besselIC k zs - asC zs)
    let err_s : ℂ := diff1 / asC z₀ + (asympFac - mainFac)
    refine ⟨err_s, ?_, ?_⟩
    · have has_mul : asC z₀ * asympFac = ((rad ^ (-(k : ℤ)) : ℝ) : ℂ) * asC zs := by
        rw [has_ratio]
        dsimp [asympFac]
        rw [← hrad_comb]
        push_cast; ring
      rw [hK_eq]
      calc (2 * b) ^ k * ((rad ^ (-(k : ℤ)) : ℝ) : ℂ) * besselIC k zs
          = (2 * b) ^ k * (diff1 + ((rad ^ (-(k : ℤ)) : ℝ) : ℂ) * asC zs) := by
              dsimp [diff1]; ring
        _ = (2 * b) ^ k * (diff1 + asC z₀ * asympFac) := by rw [has_mul]
        _ = (2 * b) ^ k * asC z₀ * (mainFac + err_s) := by
            dsimp [err_s, mainFac]; field_simp [has0_ne]; ring
    · have hrad_k_le : rad ^ (-(k : ℤ)) ≤ 2 ^ k := by
        rw [zpow_neg, zpow_natCast, ← inv_pow]
        exact pow_le_pow_left₀ (by positivity) (by rw [inv_le_comm₀ hrad_pos (by positivity)]; linarith) k
      have has_rel : ‖asC zs‖ / ‖asC z₀‖ ≤ 2 := by
        rw [has_ratio, norm_mul, norm_mul, mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr has0_ne)]
        have hr12 : rad ^ (-(1 / 2 : ℝ)) ≤ 2 := by
          rw [Real.rpow_neg hrad_pos.le, ← Real.sqrt_eq_rpow,
            inv_le_comm₀ (Real.sqrt_pos.mpr hrad_pos) (by positivity)]
          linarith [show (1 / 2 : ℝ) ≤ Real.sqrt rad from by
            have h14 : (1 / 4 : ℝ) ≤ rad := by linarith
            calc (1 / 2 : ℝ) = Real.sqrt (1 / 4) := by norm_num [Real.sqrt_div, Real.sqrt_one]
              _ ≤ Real.sqrt rad := Real.sqrt_le_sqrt h14]
        have hexp_le : ‖Complex.exp (-((1 - rad : ℝ) : ℂ) * z₀)‖ ≤ 1 := by
          rw [Complex.norm_exp, Real.exp_le_one_iff,
            show (-((1 - rad : ℝ) : ℂ) * z₀).re = -(1 - rad) * z₀.re by
              rw [show -((1 - rad : ℝ) : ℂ) = ((-(1 - rad) : ℝ) : ℂ) by push_cast; rfl,
                Complex.re_ofReal_mul]]
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by linarith)) hz₀_pos.le
        calc ‖((rad ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ * ‖Complex.exp (-((1 - rad : ℝ) : ℂ) * z₀)‖
            ≤ 2 * 1 := by
              rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hrad_pos.le _)]
              exact mul_le_mul hr12 hexp_le (norm_nonneg _) (by norm_num)
          _ = 2 := mul_one 2
      have hterm1 : ‖diff1 / asC z₀‖ ≤ (2 ^ (k + 2) * C_I / m₀) / c' := by
        dsimp [diff1]
        rw [norm_div, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (zpow_nonneg hrad_pos.le _)]
        calc rad ^ (-(k : ℤ)) * ‖besselIC k zs - asC zs‖ / ‖asC z₀‖
            ≤ 2 ^ k * ((C_I / ‖zs‖) * ‖asC zs‖) / ‖asC z₀‖ := by
              gcongr
          _ = 2 ^ k * (C_I / ‖zs‖) * (‖asC zs‖ / ‖asC z₀‖) := by ring
          _ ≤ 2 ^ k * (C_I / (m₀ * c')) * 2 := by
              have hm_pos : 0 < m₀ * c' := mul_pos hm hc'_pos
              exact mul_le_mul
                (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hCI_nn hm_pos hzs_norm) (by positivity))
                has_rel (by positivity) (by positivity)
          _ = (2 ^ (k + 1) * C_I / m₀) / c' := by
              rw [pow_succ]; ring
          _ ≤ (2 ^ (k + 2) * C_I / m₀) / c' := by
              have hpow_le : (2 : ℝ) ^ (k + 1) ≤ 2 ^ (k + 2) :=
                pow_le_pow_right₀ (by norm_num) (by omega)
              gcongr
      have hterm2 : ‖asympFac - mainFac‖ ≤
          (12 * ((k : ℝ) + 1) * 2 ^ (k + 1) * S + 605 * S ^ 2 * M₀) / c' := by
        have hid : asympFac - mainFac =
            (((rad ^ (-((k : ℝ) + 1 / 2)) : ℝ) : ℂ) - 1) * (mainFac * Complex.exp (-δ)) +
              mainFac * (Complex.exp (-δ) - 1) := by
          dsimp [asympFac, mainFac]; rw [hexp_split]; ring
        have hexp_δ_le1 : ‖Complex.exp (-δ)‖ ≤ 1 := by
          rw [Complex.norm_exp, Real.exp_le_one_iff]; exact hδ_re
        have hexp_δ_sub : ‖Complex.exp (-δ) - 1‖ ≤ 605 * S ^ 2 * M₀ / c' := by
          calc ‖Complex.exp (-δ) - 1‖ ≤ 2 * ‖-δ‖ := norm_exp_sub_one_le_of_re_nonpos'' hδ_re
            _ ≤ 2 * (302.4 * S ^ 2 * M₀ / c') := by gcongr
            _ = 604.8 * S ^ 2 * M₀ / c' := by ring
            _ ≤ 605 * S ^ 2 * M₀ / c' := by gcongr; norm_num
        have hrad_c : ‖((rad ^ (-((k : ℝ) + 1 / 2)) : ℝ) : ℂ) - 1‖ ≤
            (12 * ((k : ℝ) + 1) * 2 ^ (k + 1) * S) / c' := by
          rw [show (((rad ^ (-((k : ℝ) + 1 / 2)) : ℝ) : ℂ) - 1) =
              ((rad ^ (-((k : ℝ) + 1 / 2)) - 1 : ℝ) : ℂ) by push_cast; rfl,
            Complex.norm_real, Real.norm_eq_abs]
          calc |rad ^ (-((k : ℝ) + 1 / 2)) - 1|
              ≤ ((k : ℝ) + 1) * 2 ^ (k + 1) * (12 * r / c') := hrad_err
            _ ≤ ((k : ℝ) + 1) * 2 ^ (k + 1) * (12 * S / c') := by gcongr
            _ = (12 * ((k : ℝ) + 1) * 2 ^ (k + 1) * S) / c' := by ring
        rw [hid]
        calc ‖(((rad ^ (-((k : ℝ) + 1 / 2)) : ℝ) : ℂ) - 1) * (mainFac * Complex.exp (-δ)) +
                mainFac * (Complex.exp (-δ) - 1)‖
            ≤ ‖(((rad ^ (-((k : ℝ) + 1 / 2)) : ℝ) : ℂ) - 1)‖ * (‖mainFac‖ * ‖Complex.exp (-δ)‖) +
                ‖mainFac‖ * ‖Complex.exp (-δ) - 1‖ := by
              refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
              · rw [norm_mul, norm_mul]
              · rw [norm_mul]
          _ ≤ ((12 * ((k : ℝ) + 1) * 2 ^ (k + 1) * S) / c') * (1 * 1) +
                1 * (605 * S ^ 2 * M₀ / c') := by gcongr
          _ = (12 * ((k : ℝ) + 1) * 2 ^ (k + 1) * S + 605 * S ^ 2 * M₀) / c' := by ring
      calc ‖err_s‖ ≤ ‖diff1 / asC z₀‖ + ‖asympFac - mainFac‖ := norm_add_le _ _
        _ ≤ (2 ^ (k + 2) * C_I / m₀) / c' +
              (12 * ((k : ℝ) + 1) * 2 ^ (k + 1) * S + 605 * S ^ 2 * M₀) / c' :=
            add_le_add hterm1 hterm2
        _ = C_s / c' := by dsimp [C_s]; ring
  choose err herr_eq herr_bd using hs_bound
  have hQ_sum : nullPolyExpC prob b =
      ∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card *
        Complex.exp (-4 * (Real.pi : ℂ) * (prob.shiftSum s : ℂ) * b) := by
    have heq : nullPolyExpC prob b =
        (nullPolyExpC prob b) := rfl
    unfold nullPolyExpC FixedWeightProblem.shiftSum
    have h1 : (∏ l : Fin prob.m, (1 - Complex.exp (-4 * (Real.pi : ℂ) * (prob.μ l : ℂ) * b))) =
        ∏ l ∈ (Finset.univ : Finset (Fin prob.m)),
          (-Complex.exp (-4 * (Real.pi : ℂ) * (prob.μ l : ℂ) * b) + 1) :=
      Finset.prod_congr rfl fun l _ => by ring
    rw [h1, Finset.prod_add]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Finset.prod_const_one, mul_one]
    rw [show (∏ i ∈ s, -Complex.exp (-4 * (Real.pi : ℂ) * (prob.μ i : ℂ) * b)) =
        ∏ i ∈ s, (-1 : ℂ) * Complex.exp (-4 * (Real.pi : ℂ) * (prob.μ i : ℂ) * b) from
      Finset.prod_congr rfl fun i _ => by ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    congr 1
    rw [← Complex.exp_sum]
    congr 1
    rw [← Finset.sum_mul]
    congr 1
    rw [← Finset.mul_sum]
    push_cast; rfl
  have hV_eq : cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) =
      (2 * b) ^ k * asC z₀ * (nullPolyExpC prob b + ∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card * err s) := by
    unfold cardyVC
    simp_rw [herr_eq]
    rw [hQ_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  have hden_ne : (2 * b) ^ k * asC z₀ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (mul_ne_zero two_ne_zero hb_ne)) has0_ne
  have herr_eq_sum : cardyErrC prob c' b =
      ∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card * err s := by
    unfold cardyErrC
    rw [show ((c' : ℂ) * tipL b) = z₀ from rfl, show prob.w - 1 = k from rfl, hV_eq]
    rw [mul_div_cancel_left₀ _ hden_ne]
    ring
  rw [herr_eq_sum]
  calc ‖∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card * err s‖
      ≤ ∑ s : Finset (Fin prob.m), ‖(-1 : ℂ) ^ s.card * err s‖ := norm_sum_le _ _
    _ = ∑ s : Finset (Fin prob.m), ‖err s‖ := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    _ ≤ ∑ _s : Finset (Fin prob.m), C_s / c' := Finset.sum_le_sum fun s _ => herr_bd s
    _ = C / c' := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
          nsmul_eq_mul, ← mul_div_assoc]
        dsimp [C]; push_cast; rfl

/-- **Lemma 4(f), complex-neighbourhood & Cauchy derivative bounds (`n1:L4`)**:
for every compact `I ⊂ (0, ∞)`, there exist `δ > 0`, `C ≥ 0`, and `c₀ ≥ max 1 (24 S)` such that
for all `c' ≥ c₀`:
* `‖cardyErrC prob c' b‖ ≤ C / c'` on the `δ`-neighbourhood of `I`, and
* for each `n : ℕ`, `∃ C_n, ∀ c' ≥ c₀, ∀ x ∈ I, ‖iteratedDeriv n (cardyErrC prob c') x‖ ≤ C_n / c'`. -/
theorem cardyComplexExpansion (prob : FixedWeightProblem) (I : Set ℝ)
    (hI_cpct : IsCompact I) (hI_sub : I ⊆ Ioi 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C c₀ : ℝ, 0 ≤ C ∧ max 1 (24 * prob.totalShift) ≤ c₀ ∧
      (∀ {c' : ℝ}, c₀ ≤ c' → ∀ b : ℂ, (∃ x ∈ I, ‖b - (x : ℂ)‖ < δ) →
        ‖cardyErrC prob c' b‖ ≤ C / c') ∧
      ∀ n : ℕ, ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ {c' : ℝ}, c₀ ≤ c' → ∀ x ∈ I,
        ‖iteratedDeriv n (cardyErrC prob c') (x : ℂ)‖ ≤ Cn / c' := by
  by_cases hne : I.Nonempty
  · obtain ⟨m₀, hm₀_mem, hm₀_min⟩ := hI_cpct.exists_isMinOn hne continuousOn_id
    obtain ⟨M₀, hM₀_mem, hM₀_max⟩ := hI_cpct.exists_isMaxOn hne continuousOn_id
    have hm₀_pos : 0 < m₀ := hI_sub hm₀_mem
    have hm₀_le_M₀ : m₀ ≤ M₀ := hm₀_min hM₀_mem
    let δ : ℝ := m₀ / 2
    let m : ℝ := m₀ / 2
    let M : ℝ := M₀ + m₀ / 2
    obtain ⟨C, c₀, hC_nn, hc₀_ge, hbox⟩ :=
      cardyErrC_bound_on_box prob (m₀ := m) (M₀ := M) (by positivity) (by dsimp [M]; linarith)
    refine ⟨δ, by positivity, C, c₀, hC_nn, hc₀_ge, ?_, ?_⟩
    · intro c' hc' b ⟨x, hx_mem, hbx⟩
      have hx_lo : m₀ ≤ x := hm₀_min hx_mem
      have hx_hi : x ≤ M₀ := hM₀_max hx_mem
      have hre_sub : |b.re - x| ≤ ‖b - (x : ℂ)‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (b - (x : ℂ))
      have him_sub : |b.im| ≤ ‖b - (x : ℂ)‖ := by
        simpa [Complex.sub_im] using Complex.abs_im_le_norm (b - (x : ℂ))
      have hb_re : m ≤ b.re := by
        have := (abs_lt.mp (hre_sub.trans_lt hbx)).1
        dsimp [m, δ] at *; linarith
      have hb_im : |b.im| ≤ b.re := by
        have := him_sub.trans_lt hbx
        dsimp [m, δ] at *; linarith
      have hb_norm : ‖b‖ ≤ M := by
        have hx_norm : ‖(x : ℂ)‖ = x := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hI_sub hx_mem)]
        calc ‖b‖ = ‖(b - (x : ℂ)) + (x : ℂ)‖ := by ring_nf
          _ ≤ ‖b - (x : ℂ)‖ + ‖(x : ℂ)‖ := norm_add_le _ _
          _ ≤ δ + x := add_le_add hbx.le hx_norm.le
          _ ≤ M := by dsimp [δ, M]; linarith
      exact hbox hc' hb_re hb_im hb_norm
    · intro n
      let r : ℝ := δ / 2
      have hr_pos : 0 < r := by positivity
      refine ⟨n ! * C / r ^ n, by positivity, fun {c'} hc' x hx_mem => ?_⟩
      have hc'_pos : 0 < c' := lt_of_lt_of_le (by linarith [le_max_left (1 : ℝ) (24 * prob.totalShift)]) (hc₀_ge.trans hc')
      have hx_pos : 0 < x := hI_sub hx_mem
      have hx_lo : m₀ ≤ x := hm₀_min hx_mem
      have hcl_sub : closedBall (x : ℂ) r ⊆ {w : ℂ | 0 < w.re} := by
        intro w hw
        have hdist : ‖w - (x : ℂ)‖ ≤ r := by simpa [Complex.dist_eq] using mem_closedBall.mp hw
        have hre_sub : |w.re - x| ≤ ‖w - (x : ℂ)‖ := by
          simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - (x : ℂ))
        have := (abs_le.mp (hre_sub.trans hdist)).1
        change 0 < w.re
        dsimp [r, δ] at *; linarith
      have hdiff_cl : DiffContOnCl ℂ (cardyErrC prob c') (ball (x : ℂ) r) :=
        ⟨(cardyErrC_differentiableOn prob hc'_pos).mono
            (Metric.ball_subset_closedBall.trans hcl_sub),
          ((cardyErrC_differentiableOn prob hc'_pos).continuousOn).mono
            (closure_ball_subset_closedBall.trans hcl_sub)⟩
      have hsphere : ∀ w ∈ sphere (x : ℂ) r, ‖cardyErrC prob c' w‖ ≤ C / c' := by
        intro w hw
        have hdist : ‖w - (x : ℂ)‖ = r := by simpa [Complex.dist_eq] using mem_sphere.mp hw
        have hw_re : m ≤ w.re := by
          have hre_sub : |w.re - x| ≤ ‖w - (x : ℂ)‖ := by
            simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - (x : ℂ))
          have := (abs_le.mp (hre_sub.trans hdist.le)).1
          dsimp [m, r, δ] at *; linarith
        have hw_im : |w.im| ≤ w.re := by
          have him_sub : |w.im| ≤ ‖w - (x : ℂ)‖ := by
            simpa [Complex.sub_im] using Complex.abs_im_le_norm (w - (x : ℂ))
          have := him_sub.trans hdist.le
          dsimp [m, r, δ] at *; linarith
        have hw_norm : ‖w‖ ≤ M := by
          have hx_hi : x ≤ M₀ := hM₀_max hx_mem
          have hx_norm : ‖(x : ℂ)‖ = x := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos]
          calc ‖w‖ = ‖(w - (x : ℂ)) + (x : ℂ)‖ := by ring_nf
            _ ≤ ‖w - (x : ℂ)‖ + ‖(x : ℂ)‖ := norm_add_le _ _
            _ ≤ r + x := add_le_add hdist.le hx_norm.le
            _ ≤ M := by dsimp [r, δ, M]; linarith
        exact hbox hc' hw_re hw_im hw_norm
      have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr_pos
        hdiff_cl hsphere
      calc ‖iteratedDeriv n (cardyErrC prob c') (x : ℂ)‖
          ≤ (n ! : ℝ) * (C / c') / r ^ n := hcauchy
        _ = ((n ! : ℝ) * C / r ^ n) / c' := by ring
  · rw [not_nonempty_iff_eq_empty] at hne
    subst hne
    exact ⟨1, one_pos, 0, max 1 (24 * prob.totalShift), le_rfl, le_rfl,
      fun _ _ ⟨_, hx, _⟩ => False.elim hx, fun _ => ⟨0, le_rfl, fun _ _ hx => False.elim hx⟩⟩

/-- **Lemma 4(f), real uniform asymptote (`n1:L4`)**: for every `x₀ > 0`, uniformly in `x ≥ x₀`
(including `x → ∞`) and `c' ≥ max 1 (24 S)`:
`|V(c' x² / 3) / ((2x)^{w-1} as(c' L(x))) - Q(e^{-4π x})| ≤ C_{x₀} / c'`. -/
theorem cardyV_asymptotic_real (prob : FixedWeightProblem) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c' x : ℝ}, max 1 (24 * prob.totalShift) ≤ c' → x₀ ≤ x →
      |prob.cardyV (c' / 12) (c' * x ^ 2 / 3) /
          ((2 * x) ^ (prob.w - 1) * besselAs (c' * (2 * Real.pi * x / 3))) -
        prob.nullPoly (Real.exp (-4 * Real.pi * x))| ≤ C / c' := by
  have hw := prob.hw
  obtain ⟨C_I, hCI_nn, hI_bd⟩ := besselI_asymptotic_real (prob.w - 1)
  let S : ℝ := prob.totalShift
  have hS_nn : 0 ≤ S := prob.totalShift_nonneg
  let k : ℕ := prob.w - 1
  let C_s : ℝ := 2 ^ (k + 2) * C_I / (2 * Real.pi * x₀ / 3) +
    12 * ((k : ℝ) + 1) * 2 ^ (k + 1) * S + 12 * S
  let C : ℝ := (2 ^ prob.m : ℝ) * C_s
  refine ⟨C, by dsimp [C, C_s]; positivity, fun {c' x} hc' hx => ?_⟩
  have hc1 : 1 ≤ c' := (le_max_left _ _).trans hc'
  have hcS : 24 * S ≤ c' := (le_max_right _ _).trans hc'
  have hc'_pos : 0 < c' := by linarith
  have hx_pos : 0 < x := lt_of_lt_of_le hx₀ hx
  let z₀ : ℝ := c' * (2 * Real.pi * x / 3)
  have hz₀_pos : 0 < z₀ := by dsimp [z₀]; positivity
  have hAs_pos : 0 < besselAs z₀ := besselAs_pos hz₀_pos
  have hden_pos : 0 < (2 * x) ^ k * besselAs z₀ := by positivity
  have hs_bound : ∀ s : Finset (Fin prob.m), ∃ err_s : ℝ,
      kernelK prob.w (c' / 12 - prob.shiftSum s) (c' * x ^ 2 / 3) =
        (2 * x) ^ k * besselAs z₀ * (Real.exp (-4 * Real.pi * prob.shiftSum s * x) + err_s) ∧
      |err_s| ≤ C_s / c' := by
    intro s
    set r : ℝ := prob.shiftSum s
    have hr_nn : 0 ≤ r := prob.shiftSum_nonneg s
    have hr_le : r ≤ S := prob.shiftSum_le_totalShift s
    have hu_nn : 0 ≤ 12 * r / c' := by positivity
    have hu_le : 12 * r / c' ≤ 1 / 2 := by rw [div_le_iff₀ hc'_pos]; linarith
    let rad : ℝ := Real.sqrt (1 - 12 * r / c')
    obtain ⟨hrad_gt, hrad_le1, hrad_ge1, hrad_ub, hrad_err⟩ :=
      rad_neg_pow_bounds k hu_nn hu_le rfl
    have hrad_pos : 0 < rad := by linarith
    have hK_c := kernelKC_shift_eq_besselIC prob.w hw hc'_pos hu_le (x : ℂ)
    dsimp only at hK_c
    rw [show ((c' : ℂ) * (x : ℂ) ^ 2 / 3) = ((c' * x ^ 2 / 3 : ℝ) : ℂ) by push_cast; ring,
      kernelKC_ofReal prob.w hw] at hK_c
    have hzs_c : (rad : ℂ) * ((c' : ℂ) * tipL (x : ℂ)) = ((rad * z₀ : ℝ) : ℂ) := by
      unfold tipL; dsimp [z₀]; push_cast; ring
    rw [hzs_c, besselIC_ofReal] at hK_c
    have hK_r : kernelK prob.w (c' / 12 - r) (c' * x ^ 2 / 3) =
        (2 * x) ^ k * rad ^ (-(k : ℤ)) * besselI k (rad * z₀) := by
      have hc2 : ((kernelK prob.w (c' / 12 - r) (c' * x ^ 2 / 3) : ℝ) : ℂ) =
          (((2 * x) ^ k * rad ^ (-(k : ℤ)) * besselI k (rad * z₀) : ℝ) : ℂ) := by
        simpa [k] using hK_c
      exact Complex.ofReal_inj.mp hc2
    have hzs_pos : 0 < rad * z₀ := mul_pos hrad_pos hz₀_pos
    have hI := hI_bd hzs_pos
    set ε_I := besselI k (rad * z₀) / besselAs (rad * z₀) - 1
    have hAs_zs_pos : 0 < besselAs (rad * z₀) := besselAs_pos hzs_pos
    have hI_eq : besselI k (rad * z₀) = besselAs (rad * z₀) * (1 + ε_I) := by
      dsimp [ε_I]; field_simp [hAs_zs_pos.ne']; ring
    have has_ratio : besselAs (rad * z₀) = besselAs z₀ *
        (rad ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 - rad) * z₀)) := by
      unfold besselAs
      have hsq : Real.sqrt (2 * Real.pi * (rad * z₀)) =
          Real.sqrt (2 * Real.pi * z₀) * Real.sqrt rad := by
        rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
      have hexp : Real.exp (rad * z₀) = Real.exp z₀ * Real.exp (-(1 - rad) * z₀) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hsq, hexp, Real.sqrt_eq_rpow rad, Real.rpow_neg hrad_pos.le]
      field_simp [(Real.rpow_pos_of_pos hrad_pos _).ne', (Real.sqrt_pos.mpr (by positivity : 0 < 2 * Real.pi * z₀)).ne']
    obtain ⟨hη_nn, hη_le⟩ := eta_bounds hc'_pos hr_nn hu_le
    let η : ℝ := 1 - rad - 6 * r / c'
    let δ : ℝ := η * z₀
    have hexp_split : Real.exp (-(1 - rad) * z₀) =
        Real.exp (-4 * Real.pi * r * x) * Real.exp (-δ) := by
      rw [← Real.exp_add]; congr 1; dsimp [δ, η, z₀]; field_simp [hc'_pos.ne']; ring
    have hδ_nn : 0 ≤ δ := mul_nonneg hη_nn hz₀_pos.le
    have hδ_exp_le : Real.exp (-4 * Real.pi * r * x) * |Real.exp (-δ) - 1| ≤ 12 * S / c' := by
      by_cases hr0 : r = 0
      · have hη0 : η = 0 := by dsimp [η, rad]; rw [hr0]; simp
        have hδ0 : δ = 0 := by dsimp [δ]; rw [hη0, zero_mul]
        rw [hδ0, neg_zero, Real.exp_zero, sub_self, abs_zero, mul_zero]; positivity
      · have hr_pos : 0 < r := lt_of_le_of_ne hr_nn (Ne.symm hr0)
        have h1 : |Real.exp (-δ) - 1| ≤ δ := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))]
          linarith [Real.add_one_le_exp (-δ)]
        have hδ_le : δ ≤ 24 * Real.pi * r ^ 2 * x / c' := by
          dsimp [δ, z₀]
          calc η * (c' * (2 * Real.pi * x / 3))
              ≤ (36 * r ^ 2 / c' ^ 2) * (c' * (2 * Real.pi * x / 3)) := by
                exact mul_le_mul_of_nonneg_right hη_le (by positivity)
            _ = 24 * Real.pi * r ^ 2 * x / c' := by field_simp [hc'_pos.ne']; ring
        have hxe : (4 * Real.pi * r * x) * Real.exp (-4 * Real.pi * r * x) ≤ 1 := by
          have := mul_exp_neg_le_one (y := 4 * Real.pi * r * x) (by positivity)
          simpa [neg_mul] using this
        calc Real.exp (-4 * Real.pi * r * x) * |Real.exp (-δ) - 1|
            ≤ Real.exp (-4 * Real.pi * r * x) * δ := by gcongr
          _ ≤ Real.exp (-4 * Real.pi * r * x) * (24 * Real.pi * r ^ 2 * x / c') := by gcongr
          _ = (6 * r / c') * ((4 * Real.pi * r * x) * Real.exp (-4 * Real.pi * r * x)) := by ring
          _ ≤ (6 * r / c') * 1 := by gcongr
          _ = 6 * r / c' := mul_one _
          _ ≤ 12 * S / c' := by gcongr; linarith
    have hrad_comb : rad ^ (-(k : ℤ)) * rad ^ (-(1 / 2 : ℝ)) = rad ^ (-((k : ℝ) + 1 / 2)) := by
      rw [← Real.rpow_intCast rad (-(k : ℤ)), ← Real.rpow_add hrad_pos]
      congr 1; push_cast; ring
    let mainFac : ℝ := Real.exp (-4 * Real.pi * r * x)
    let asympFac : ℝ := rad ^ (-((k : ℝ) + 1 / 2)) * Real.exp (-(1 - rad) * z₀)
    let diff1 : ℝ := rad ^ (-(k : ℤ)) * (besselI k (rad * z₀) - besselAs (rad * z₀))
    let err_s : ℝ := diff1 / besselAs z₀ + (asympFac - mainFac)
    refine ⟨err_s, ?_, ?_⟩
    · have has_mul : besselAs z₀ * asympFac = rad ^ (-(k : ℤ)) * besselAs (rad * z₀) := by
        rw [has_ratio]
        dsimp [asympFac]
        rw [← hrad_comb]
        ring
      rw [hK_r]
      calc (2 * x) ^ k * rad ^ (-(k : ℤ)) * besselI k (rad * z₀)
          = (2 * x) ^ k * (diff1 + rad ^ (-(k : ℤ)) * besselAs (rad * z₀)) := by
              dsimp [diff1]; ring
        _ = (2 * x) ^ k * (diff1 + besselAs z₀ * asympFac) := by rw [has_mul]
        _ = (2 * x) ^ k * besselAs z₀ * (mainFac + err_s) := by
            dsimp [err_s, mainFac]; field_simp [hAs_pos.ne']; ring
    · have hrad_k_le : rad ^ (-(k : ℤ)) ≤ 2 ^ k := by
        rw [zpow_neg, zpow_natCast, ← inv_pow]
        exact pow_le_pow_left₀ (by positivity) (by rw [inv_le_comm₀ hrad_pos (by positivity)]; linarith) k
      have has_rel : besselAs (rad * z₀) / besselAs z₀ ≤ 2 := by
        rw [has_ratio, mul_div_cancel_left₀ _ hAs_pos.ne']
        have hr12 : rad ^ (-(1 / 2 : ℝ)) ≤ 2 := by
          rw [Real.rpow_neg hrad_pos.le, ← Real.sqrt_eq_rpow,
            inv_le_comm₀ (Real.sqrt_pos.mpr hrad_pos) (by positivity)]
          linarith [show (1 / 2 : ℝ) ≤ Real.sqrt rad from by
            have h14 : (1 / 4 : ℝ) ≤ rad := by linarith
            calc (1 / 2 : ℝ) = Real.sqrt (1 / 4) := by norm_num [Real.sqrt_div, Real.sqrt_one]
              _ ≤ Real.sqrt rad := Real.sqrt_le_sqrt h14]
        have hexp_le : Real.exp (-(1 - rad) * z₀) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by linarith)) hz₀_pos.le
        calc rad ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 - rad) * z₀)
            ≤ 2 * 1 := mul_le_mul hr12 hexp_le (Real.exp_pos _).le (by norm_num)
          _ = 2 := mul_one 2
      have hzs_lo : (2 * Real.pi * x₀ / 3) * c' / 2 ≤ rad * z₀ := by
        have h1 : (2 * Real.pi * x₀ / 3) * c' ≤ z₀ := by
          dsimp [z₀]
          calc (2 * Real.pi * x₀ / 3) * c' = c' * (2 * Real.pi * x₀ / 3) := by ring
            _ ≤ c' * (2 * Real.pi * x / 3) := by gcongr
        have h2 : (2 * Real.pi * x₀ / 3) * c' / 2 ≤ (1 / 2 : ℝ) * z₀ := by linarith
        exact h2.trans (mul_le_mul_of_nonneg_right hrad_gt.le hz₀_pos.le)
      have hterm1 : |diff1 / besselAs z₀| ≤ (2 ^ (k + 2) * C_I / (2 * Real.pi * x₀ / 3)) / c' := by
        dsimp [diff1]
        rw [abs_div, abs_mul, abs_of_nonneg (zpow_nonneg hrad_pos.le _),
          abs_of_pos hAs_pos]
        have hI_diff : |besselI k (rad * z₀) - besselAs (rad * z₀)| ≤
            C_I / (rad * z₀) * besselAs (rad * z₀) := by
          have hid_I : besselI k (rad * z₀) - besselAs (rad * z₀) =
              (besselI k (rad * z₀) / besselAs (rad * z₀) - 1) * besselAs (rad * z₀) := by
            field_simp [hAs_zs_pos.ne']
          rw [hid_I, abs_mul, abs_of_pos hAs_zs_pos]
          exact mul_le_mul_of_nonneg_right hI hAs_zs_pos.le
        have hradz_pos : 0 < rad * z₀ := hzs_pos
        have hz_half : (2 * Real.pi * x₀ / 3) * c' / 2 > 0 := by positivity
        calc rad ^ (-(k : ℤ)) * |besselI k (rad * z₀) - besselAs (rad * z₀)| / besselAs z₀
            ≤ 2 ^ k * (C_I / (rad * z₀) * besselAs (rad * z₀)) / besselAs z₀ := by
              gcongr
          _ = 2 ^ k * (C_I / (rad * z₀)) * (besselAs (rad * z₀) / besselAs z₀) := by ring
          _ ≤ 2 ^ k * (C_I / ((2 * Real.pi * x₀ / 3) * c' / 2)) * 2 := by
              gcongr
          _ = (2 ^ (k + 2) * C_I / (2 * Real.pi * x₀ / 3)) / c' := by
              rw [show (2 : ℝ) ^ (k + 2) = 2 ^ k * 4 by rw [pow_add]; norm_num]
              field_simp [hc'_pos.ne', Real.pi_pos.ne', hx₀.ne']
              ring
      have hterm2 : |asympFac - mainFac| ≤
          (12 * ((k : ℝ) + 1) * 2 ^ (k + 1) * S + 12 * S) / c' := by
        have hid : asympFac - mainFac =
            (rad ^ (-((k : ℝ) + 1 / 2)) - 1) * (mainFac * Real.exp (-δ)) +
              mainFac * (Real.exp (-δ) - 1) := by
          dsimp [asympFac, mainFac]; rw [hexp_split]; ring
        have hmain_nn : 0 ≤ mainFac := (Real.exp_pos _).le
        have hmain_le1 : mainFac ≤ 1 := by
          dsimp [mainFac]; rw [Real.exp_le_one_iff,
            show -4 * Real.pi * r * x = -(4 * Real.pi * r * x) by ring]
          exact neg_nonpos.mpr (by positivity)
        have hexp_δ_le1 : Real.exp (-δ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        have hrad_c : |rad ^ (-((k : ℝ) + 1 / 2)) - 1| ≤
            (12 * ((k : ℝ) + 1) * 2 ^ (k + 1) * S) / c' := by
          calc |rad ^ (-((k : ℝ) + 1 / 2)) - 1|
              ≤ ((k : ℝ) + 1) * 2 ^ (k + 1) * (12 * r / c') := hrad_err
            _ ≤ ((k : ℝ) + 1) * 2 ^ (k + 1) * (12 * S / c') := by gcongr
            _ = (12 * ((k : ℝ) + 1) * 2 ^ (k + 1) * S) / c' := by ring
        rw [hid]
        calc |(rad ^ (-((k : ℝ) + 1 / 2)) - 1) * (mainFac * Real.exp (-δ)) +
                mainFac * (Real.exp (-δ) - 1)|
            ≤ |(rad ^ (-((k : ℝ) + 1 / 2)) - 1) * (mainFac * Real.exp (-δ))| +
                |mainFac * (Real.exp (-δ) - 1)| := abs_add_le _ _
          _ = |rad ^ (-((k : ℝ) + 1 / 2)) - 1| * (mainFac * Real.exp (-δ)) +
                mainFac * |Real.exp (-δ) - 1| := by
              simp only [abs_mul, abs_of_nonneg hmain_nn, abs_of_nonneg (Real.exp_pos (-δ)).le]
          _ ≤ (12 * ((k : ℝ) + 1) * 2 ^ (k + 1) * S / c') * (1 * 1) + 12 * S / c' := by
              have h1m : mainFac * Real.exp (-δ) ≤ 1 * 1 :=
                mul_le_mul hmain_le1 hexp_δ_le1 (Real.exp_pos _).le zero_le_one
              have h2m : mainFac * |Real.exp (-δ) - 1| ≤ 12 * S / c' := by
                simpa [mainFac] using hδ_exp_le
              exact add_le_add
                (mul_le_mul hrad_c h1m (mul_nonneg hmain_nn (Real.exp_pos _).le) (by positivity))
                h2m
          _ = (12 * ((k : ℝ) + 1) * 2 ^ (k + 1) * S + 12 * S) / c' := by ring
      calc |err_s| ≤ |diff1 / besselAs z₀| + |asympFac - mainFac| := abs_add_le _ _
        _ ≤ (2 ^ (k + 2) * C_I / (2 * Real.pi * x₀ / 3)) / c' +
              (12 * ((k : ℝ) + 1) * 2 ^ (k + 1) * S + 12 * S) / c' := add_le_add hterm1 hterm2
        _ = C_s / c' := by dsimp [C_s]; ring
  choose err herr_eq herr_bd using hs_bound
  have hQ_sum : prob.nullPoly (Real.exp (-4 * Real.pi * x)) =
      ∑ s : Finset (Fin prob.m), (-1 : ℝ) ^ s.card *
        Real.exp (-4 * Real.pi * prob.shiftSum s * x) := by
    unfold FixedWeightProblem.nullPoly FixedWeightProblem.shiftSum
    have h1 : (∏ l : Fin prob.m, (1 - Real.exp (-4 * Real.pi * x) ^ prob.μ l)) =
        ∏ l ∈ (Finset.univ : Finset (Fin prob.m)),
          (-Real.exp (-4 * Real.pi * x) ^ prob.μ l + 1) :=
      Finset.prod_congr rfl fun l _ => by ring
    rw [h1, Finset.prod_add]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Finset.prod_const_one, mul_one]
    rw [show (∏ i ∈ s, -Real.exp (-4 * Real.pi * x) ^ prob.μ i) =
        ∏ i ∈ s, (-1 : ℝ) * Real.exp (-4 * Real.pi * x) ^ prob.μ i from
      Finset.prod_congr rfl fun i _ => by ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    congr 1
    have hpow : ∀ i : Fin prob.m, Real.exp (-4 * Real.pi * x) ^ prob.μ i =
        Real.exp (-4 * Real.pi * prob.μ i * x) := fun i => by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]; congr 1; ring
    have hexp_prod : (∏ i ∈ s, Real.exp (-4 * Real.pi * x) ^ prob.μ i) =
        Real.exp (-4 * Real.pi * (∑ l ∈ s, prob.μ l) * x) := by
      simp_rw [hpow]
      rw [← Real.exp_sum]
      congr 1
      calc ∑ l ∈ s, -4 * Real.pi * prob.μ l * x
          = ∑ l ∈ s, (-4 * Real.pi * x) * prob.μ l := Finset.sum_congr rfl fun l _ => by ring
        _ = (-4 * Real.pi * x) * ∑ l ∈ s, prob.μ l := by rw [← Finset.mul_sum]
        _ = -4 * Real.pi * (∑ l ∈ s, prob.μ l) * x := by ring
    exact hexp_prod
  have hV_eq : prob.cardyV (c' / 12) (c' * x ^ 2 / 3) =
      (2 * x) ^ k * besselAs z₀ *
        (prob.nullPoly (Real.exp (-4 * Real.pi * x)) +
          ∑ s : Finset (Fin prob.m), (-1 : ℝ) ^ s.card * err s) := by
    unfold FixedWeightProblem.cardyV
    simp_rw [herr_eq]
    rw [hQ_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [hV_eq, mul_div_cancel_left₀ _ hden_pos.ne', add_sub_cancel_left]
  calc |∑ s : Finset (Fin prob.m), (-1 : ℝ) ^ s.card * err s|
      ≤ ∑ s : Finset (Fin prob.m), |(-1 : ℝ) ^ s.card * err s| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s : Finset (Fin prob.m), |err s| := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    _ ≤ ∑ _s : Finset (Fin prob.m), C_s / c' := Finset.sum_le_sum fun s _ => herr_bd s
    _ = C / c' := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
          nsmul_eq_mul, ← mul_div_assoc]
        dsimp [C]; push_cast; rfl

/-- **Lemma 4(f), lobe ratio (`n1:L4`)**: for `x ≥ x₀ > 0` and `c' ≥ c₀` large enough,
`x^{w-1} t^{-1/2} e^{c' L(x)} / V(t) ≍ x^{-1/2}` (`t = c' x^2 / 3`, `L(x) = 2π x / 3`). -/
theorem cardyV_lobe_ratio_bounds (prob : FixedWeightProblem) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ∃ c₁ c₂ c₀ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ {c' x : ℝ}, c₀ ≤ c' → x₀ ≤ x →
        let t := c' * x ^ 2 / 3
        let ratio := x ^ (prob.w - 1) * t ^ (-(1 / 2 : ℝ)) *
          Real.exp (c' * (2 * Real.pi * x / 3)) / prob.cardyV (c' / 12) t
        c₁ * x ^ (-(1 / 2 : ℝ)) ≤ ratio ∧ ratio ≤ c₂ * x ^ (-(1 / 2 : ℝ)) := by
  have hw := prob.hw
  obtain ⟨C, hC_nn, h_as⟩ := cardyV_asymptotic_real prob hx₀
  obtain ⟨hq0_pos, hq_bds⟩ := nullPoly_exp_bounds prob hx₀
  set q₀ : ℝ := prob.nullPoly (Real.exp (-4 * Real.pi * x₀))
  let c₀ : ℝ := max (max 1 (24 * prob.totalShift)) (2 * C / q₀)
  let K : ℝ := 2 * Real.pi / 2 ^ (prob.w - 1)
  have hK_pos : 0 < K := by positivity
  refine ⟨2 * K / 3, 2 * K / q₀, c₀, by positivity, by positivity, le_max_left _ _,
    fun {c' x} hc' hx => ?_⟩
  have hcm : max 1 (24 * prob.totalShift) ≤ c' := (le_max_left _ _).trans hc'
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by linarith [le_max_left (1 : ℝ) (24 * prob.totalShift)]) hcm
  have hCc' : C / c' ≤ q₀ / 2 := by
    have h2 : 2 * C / q₀ ≤ c' := (le_max_right _ _).trans hc'
    rw [div_le_div_iff₀ hc'_pos zero_lt_two]
    have hmul := mul_le_mul_of_nonneg_left h2 hq0_pos.le
    rw [mul_div_cancel₀ _ hq0_pos.ne'] at hmul
    linarith
  have hx_pos : 0 < x := lt_of_lt_of_le hx₀ hx
  let z₀ : ℝ := c' * (2 * Real.pi * x / 3)
  have hz₀_pos : 0 < z₀ := by dsimp [z₀]; positivity
  have hAs_pos : 0 < besselAs z₀ := besselAs_pos hz₀_pos
  have hden_pos : 0 < (2 * x) ^ (prob.w - 1) * besselAs z₀ := by positivity
  have h_err := h_as hcm hx
  have hq_lo : q₀ ≤ prob.nullPoly (Real.exp (-4 * Real.pi * x)) := (hq_bds hx).1
  have hq_hi : prob.nullPoly (Real.exp (-4 * Real.pi * x)) ≤ 1 := (hq_bds hx).2
  have hdiv_lo : q₀ / 2 ≤ prob.cardyV (c' / 12) (c' * x ^ 2 / 3) /
      ((2 * x) ^ (prob.w - 1) * besselAs z₀) := by
    linarith [(abs_le.mp h_err).1]
  have hdiv_hi : prob.cardyV (c' / 12) (c' * x ^ 2 / 3) /
      ((2 * x) ^ (prob.w - 1) * besselAs z₀) ≤ 3 / 2 := by
    have hq_le1 : prob.nullPoly (Real.exp (-4 * Real.pi * x)) ≤ 1 := hq_hi
    have hq0_le1 : q₀ ≤ 1 := (hq_bds le_rfl).2
    linarith [(abs_le.mp h_err).2]
  have hV_lo : (q₀ / 2) * ((2 * x) ^ (prob.w - 1) * besselAs z₀) ≤
      prob.cardyV (c' / 12) (c' * x ^ 2 / 3) :=
    (le_div_iff₀ hden_pos).mp hdiv_lo
  have hV_hi : prob.cardyV (c' / 12) (c' * x ^ 2 / 3) ≤
      (3 / 2) * ((2 * x) ^ (prob.w - 1) * besselAs z₀) :=
    (div_le_iff₀ hden_pos).mp hdiv_hi
  have hV_pos : 0 < prob.cardyV (c' / 12) (c' * x ^ 2 / 3) :=
    lt_of_lt_of_le (by positivity) hV_lo
  have hid : x ^ (prob.w - 1) * (c' * x ^ 2 / 3) ^ (-(1 / 2 : ℝ)) *
      Real.exp (c' * (2 * Real.pi * x / 3)) =
      K * x ^ (-(1 / 2 : ℝ)) * ((2 * x) ^ (prob.w - 1) * besselAs z₀) := by
    have hsq_t : (c' * x ^ 2 / 3) ^ (-(1 / 2 : ℝ)) = Real.sqrt 3 / (Real.sqrt c' * x) := by
      rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
        Real.sqrt_div (by positivity), Real.sqrt_mul hc'_pos.le,
        Real.sqrt_sq hx_pos.le, inv_div]
    have hAs_eq : besselAs z₀ =
        Real.exp (c' * (2 * Real.pi * x / 3)) / (2 * Real.pi * Real.sqrt c' * Real.sqrt x / Real.sqrt 3) := by
      unfold besselAs
      have hsq : Real.sqrt (2 * Real.pi * z₀) =
          2 * Real.pi * Real.sqrt c' * Real.sqrt x / Real.sqrt 3 := by
        dsimp [z₀]
        have h1 : 2 * Real.pi * (c' * (2 * Real.pi * x / 3)) =
            (2 * Real.pi) ^ 2 * c' * x / 3 := by ring
        rw [h1, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      rw [hsq]
    have hxrpow : x ^ (-(1 / 2 : ℝ)) * Real.sqrt x = 1 := by
      rw [Real.rpow_neg hx_pos.le, ← Real.sqrt_eq_rpow,
        inv_mul_cancel₀ (Real.sqrt_pos.mpr hx_pos).ne']
    have hsqx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx_pos.le
    rw [hsq_t, hAs_eq, mul_pow]
    dsimp [K]
    have h2ne : (2 : ℝ) ^ (prob.w - 1) ≠ 0 := by positivity
    have hpi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hsq3_ne : Real.sqrt 3 ≠ 0 := by positivity
    have hsqc_ne : Real.sqrt c' ≠ 0 := by positivity
    have hsqx_ne : Real.sqrt x ≠ 0 := by positivity
    have hx_inv_x : x ^ (-(1 / 2 : ℝ)) * x = Real.sqrt x := by
      calc x ^ (-(1 / 2 : ℝ)) * x = x ^ (-(1 / 2 : ℝ)) * (Real.sqrt x * Real.sqrt x) := by rw [hsqx]
        _ = (x ^ (-(1 / 2 : ℝ)) * Real.sqrt x) * Real.sqrt x := by ring
        _ = Real.sqrt x := by rw [hxrpow, one_mul]
    have hpow_fac : (2 * Real.pi / 2 ^ (prob.w - 1)) * x ^ (-(1 / 2 : ℝ)) *
        ((2 ^ (prob.w - 1) * x ^ (prob.w - 1)) *
          (Real.exp (c' * (2 * Real.pi * x / 3)) / (2 * Real.pi * Real.sqrt c' * Real.sqrt x / Real.sqrt 3))) =
        x ^ (prob.w - 1) * (Real.sqrt 3 / (Real.sqrt c' * x)) * Real.exp (c' * (2 * Real.pi * x / 3)) := by
      field_simp [h2ne, hpi_ne, hsq3_ne, hsqc_ne, hsqx_ne, hx_pos.ne']
      exact hx_inv_x
    exact hpow_fac.symm
  dsimp only
  rw [hid]
  have h1 : (2 * K / 3) * x ^ (-(1 / 2 : ℝ)) ≤
      K * x ^ (-(1 / 2 : ℝ)) * ((2 * x) ^ (prob.w - 1) * besselAs z₀) /
        prob.cardyV (c' / 12) (c' * x ^ 2 / 3) := by
    rw [le_div_iff₀ hV_pos]
    calc (2 * K / 3) * x ^ (-(1 / 2 : ℝ)) * prob.cardyV (c' / 12) (c' * x ^ 2 / 3)
        ≤ (2 * K / 3) * x ^ (-(1 / 2 : ℝ)) * ((3 / 2) * ((2 * x) ^ (prob.w - 1) * besselAs z₀)) :=
          mul_le_mul_of_nonneg_left hV_hi (by positivity)
      _ = K * x ^ (-(1 / 2 : ℝ)) * ((2 * x) ^ (prob.w - 1) * besselAs z₀) := by ring
  have h2 : K * x ^ (-(1 / 2 : ℝ)) * ((2 * x) ^ (prob.w - 1) * besselAs z₀) /
        prob.cardyV (c' / 12) (c' * x ^ 2 / 3) ≤
      (2 * K / q₀) * x ^ (-(1 / 2 : ℝ)) := by
    rw [div_le_iff₀ hV_pos]
    calc K * x ^ (-(1 / 2 : ℝ)) * ((2 * x) ^ (prob.w - 1) * besselAs z₀)
        = (2 * K / q₀) * x ^ (-(1 / 2 : ℝ)) * ((q₀ / 2) * ((2 * x) ^ (prob.w - 1) * besselAs z₀)) := by
          field_simp [hq0_pos.ne']
      _ ≤ (2 * K / q₀) * x ^ (-(1 / 2 : ℝ)) * prob.cardyV (c' / 12) (c' * x ^ 2 / 3) :=
          mul_le_mul_of_nonneg_left hV_lo (by positivity)
  exact ⟨h1, h2⟩

/-! ### Section 4: Comparison bounds on `[ξ̄ c', ∞)` and `[4 / c', ∞)` (`n1:L4`(c)) -/

/-- **Lemma 4(c), upper band (`n1:L4`)**: there exist `c_band > 0` and `c₀ ≥ max 1 (24 S)` such that
for all `c' ≥ c₀` and `t ≥ xiBar * c'`, `c_band * K_{c'/12}^{(w)}(t) ≤ V(t)`. -/
theorem cardyV_ge_band_mul_kernelK (prob : FixedWeightProblem) :
    ∃ c_band c₀ : ℝ, 0 < c_band ∧ max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ {c' t : ℝ}, c₀ ≤ c' → xiBar * c' ≤ t →
        c_band * kernelK prob.w (c' / 12) t ≤ prob.cardyV (c' / 12) t := by
  have hw := prob.hw
  have hxi_pos : 0 < xiStar := xiStar_pos
  obtain ⟨C_V, _, hV_as⟩ := cardyV_asymptotic_real prob hxi_pos
  obtain ⟨C_I, _, hI_as⟩ := besselI_asymptotic_real (prob.w - 1)
  obtain ⟨hq0_pos, hq_bds⟩ := nullPoly_exp_bounds prob hxi_pos
  set q₀ : ℝ := prob.nullPoly (Real.exp (-4 * Real.pi * xiStar))
  let L₀ : ℝ := 2 * Real.pi * xiStar / 3
  have hL0_pos : 0 < L₀ := by positivity
  let c₀ : ℝ := max (max 1 (24 * prob.totalShift)) (max (2 * C_V / q₀) (2 * C_I / L₀))
  refine ⟨q₀ / 3, c₀, by positivity, le_max_left _ _, fun {c' t} hc' ht => ?_⟩
  have hcm : max 1 (24 * prob.totalShift) ≤ c' := (le_max_left _ _).trans hc'
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by linarith [le_max_left (1 : ℝ) (24 * prob.totalShift)]) hcm
  let x : ℝ := Real.sqrt (3 * t / c')
  have hx_ge : xiStar ≤ x := by
    dsimp [x]
    rw [Real.le_sqrt' (by positivity), le_div_iff₀ hc'_pos]
    have hxib : xiStar ^ 2 = 3 * xiBar := by unfold xiBar; ring
    nlinarith [ht, hxib]
  have hx_pos : 0 < x := hxi_pos.trans_le hx_ge
  have ht_pos : 0 < t := lt_of_lt_of_le (mul_pos (by unfold xiBar; positivity) hc'_pos) ht
  have ht_eq : c' * x ^ 2 / 3 = t := by
    dsimp [x]; rw [Real.sq_sqrt (by positivity)]; field_simp [hc'_pos.ne']
  let z₀ : ℝ := c' * (2 * Real.pi * x / 3)
  have hz₀_pos : 0 < z₀ := by dsimp [z₀]; positivity
  have hAs_pos : 0 < besselAs z₀ := besselAs_pos hz₀_pos
  have hden_pos : 0 < (2 * x) ^ (prob.w - 1) * besselAs z₀ := by positivity
  have h_V := hV_as hcm hx_ge
  rw [ht_eq] at h_V
  have hCV : C_V / c' ≤ q₀ / 2 := by
    have h2 : 2 * C_V / q₀ ≤ c' := (le_max_left _ _).trans ((le_max_right _ _).trans hc')
    rw [div_le_div_iff₀ hc'_pos zero_lt_two]
    have := mul_le_mul_of_nonneg_left h2 hq0_pos.le
    rw [mul_div_cancel₀ _ hq0_pos.ne'] at this
    linarith
  have hV_lo : (q₀ / 2) * ((2 * x) ^ (prob.w - 1) * besselAs z₀) ≤ prob.cardyV (c' / 12) t := by
    have h1 : q₀ - C_V / c' ≤ prob.cardyV (c' / 12) t / ((2 * x) ^ (prob.w - 1) * besselAs z₀) := by
      linarith [(abs_le.mp h_V).1, (hq_bds hx_ge).1]
    exact (le_div_iff₀ hden_pos).mp (by linarith)
  have hK_eq : kernelK prob.w (c' / 12) t = (2 * x) ^ (prob.w - 1) * besselI (prob.w - 1) z₀ := by
    have ha_pos : 0 < c' / 12 := by linarith
    rw [kernelK_eq_besselI hw ha_pos ht_pos]
    have hta : Real.sqrt (t / (c' / 12)) = 2 * x := by
      dsimp [x]
      rw [show t / (c' / 12) = 4 * (3 * t / c') by field_simp; ring,
        Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by norm_num]
    have harg : 4 * Real.pi * Real.sqrt ((c' / 12) * t) = z₀ := by
      dsimp [z₀, x]
      rw [show (c' / 12) * t = (c' / 6) ^ 2 * (3 * t / c') by field_simp [hc'_pos.ne']; ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
      ring
    rw [hta, harg]
  have hCI : C_I / z₀ ≤ 1 / 2 := by
    have hz₀_ge : L₀ * c' ≤ z₀ := by
      dsimp [z₀, L₀]
      calc (2 * Real.pi * xiStar / 3) * c' = c' * (2 * Real.pi * xiStar / 3) := by ring
        _ ≤ c' * (2 * Real.pi * x / 3) := by gcongr
    have h2 : 2 * C_I / L₀ ≤ c' := (le_max_right _ _).trans ((le_max_right _ _).trans hc')
    have h1 : C_I ≤ (1 / 2) * (L₀ * c') := by
      have := mul_le_mul_of_nonneg_left h2 hL0_pos.le
      rw [mul_div_cancel₀ _ hL0_pos.ne'] at this
      linarith
    exact (div_le_iff₀ hz₀_pos).mpr (h1.trans (mul_le_mul_of_nonneg_left hz₀_ge (by norm_num)))
  have hI_ub : besselI (prob.w - 1) z₀ ≤ (3 / 2) * besselAs z₀ := by
    have hbd := hI_as hz₀_pos
    have hsub := (abs_le.mp hbd).2
    have hsub2 : besselI (prob.w - 1) z₀ / besselAs z₀ ≤ 3 / 2 := by linarith
    exact (div_le_iff₀ hAs_pos).mp hsub2
  have hK_ub : kernelK prob.w (c' / 12) t ≤ (3 / 2) * ((2 * x) ^ (prob.w - 1) * besselAs z₀) := by
    rw [hK_eq]
    calc (2 * x) ^ (prob.w - 1) * besselI (prob.w - 1) z₀
        ≤ (2 * x) ^ (prob.w - 1) * ((3 / 2) * besselAs z₀) :=
          mul_le_mul_of_nonneg_left hI_ub (by positivity)
      _ = (3 / 2) * ((2 * x) ^ (prob.w - 1) * besselAs z₀) := by ring
  calc (q₀ / 3) * kernelK prob.w (c' / 12) t
      ≤ (q₀ / 3) * ((3 / 2) * ((2 * x) ^ (prob.w - 1) * besselAs z₀)) :=
        mul_le_mul_of_nonneg_left hK_ub (by positivity)
    _ = (q₀ / 2) * ((2 * x) ^ (prob.w - 1) * besselAs z₀) := by ring
    _ ≤ prob.cardyV (c' / 12) t := hV_lo

private lemma besselS_le_exp_sqrt (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    besselS k u ≤ Real.exp (2 * Real.sqrt u) := by
  have h1 := besselS_sq_div_four_le_exp k (u := 2 * Real.sqrt u) (by positivity)
  have harg : (2 * Real.sqrt u) ^ 2 / 4 = u := by
    rw [mul_pow, Real.sq_sqrt hu]; ring
  rw [harg] at h1
  exact h1.trans (div_le_self (Real.exp_pos _).le (by exact_mod_cast Nat.factorial_pos k))

/-- **Lemma 4(c), full range `[4/c', ∞)` (`n1:L4`)**: there exist `C_K > 0` and
`c₀ ≥ max 1 (24 S)` such that for all `c' ≥ c₀` and `t ≥ 4 / c'`,
`K_{c'/12}^{(w)}(t) ≤ C_K * c' ^ m * V(t)`. -/
theorem kernelK_le_mul_cardyV_gen (prob : FixedWeightProblem) :
    ∃ C_K c₀ : ℝ, 0 < C_K ∧ max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ {c' t : ℝ}, c₀ ≤ c' → 4 / c' ≤ t →
        kernelK prob.w (c' / 12) t ≤ C_K * c' ^ (prob.m : ℝ) * prob.cardyV (c' / 12) t := by
  have hw := prob.hw
  let S : ℝ := prob.totalShift
  obtain ⟨c_band, c₀_band, hcb_pos, hcb_ge, hband⟩ := cardyV_ge_band_mul_kernelK prob
  obtain ⟨C_I_w, _, hI_w⟩ := besselI_asymptotic_real (prob.w - 1)
  obtain ⟨C_I_wm, _, hI_wm⟩ := besselI_asymptotic_real (prob.w - 1 + prob.m)
  let R₀ : ℝ := max 1 (max (2 * C_I_w) (2 * C_I_wm))
  have hR0_pos : 0 < R₀ := by positivity
  let C_R : ℝ := 24 * (R₀ / (4 * Real.pi)) ^ 2
  have hCR_pos : 0 < C_R := by positivity
  let P : ℝ := ∏ l : Fin prob.m, prob.μ l
  have hP_pos : 0 < P := Finset.prod_pos fun l _ => prob.hμ l
  let C_low : ℝ := ((prob.m + prob.w - 1)! : ℝ) / (P * (16 * Real.pi ^ 2) ^ prob.m) *
      Real.exp (4 * Real.pi * Real.sqrt (C_R / 12))
  let C_mid : ℝ := 3 / (P * (2 * Real.pi) ^ prob.m) *
      (Real.sqrt 2 ^ (prob.w - 1) * (1 / Real.sqrt 48) ^ prob.m) *
      Real.exp (4 * Real.pi * S * Real.sqrt (12 * xiBar))
  let C_hi : ℝ := 1 / c_band
  let C_K : ℝ := max C_hi (max C_low C_mid)
  refine ⟨C_K, c₀_band, by positivity, hcb_ge, fun {c' t} hc' ht => ?_⟩
  have hcm : max 1 (24 * S) ≤ c' := hcb_ge.trans hc'
  have hc1 : 1 ≤ c' := (le_max_left _ _).trans hcm
  have hcS : 24 * S ≤ c' := (le_max_right _ _).trans hcm
  have hc'_pos : 0 < c' := by linarith
  have ht_pos : 0 < t := lt_of_lt_of_le (div_pos (by norm_num) hc'_pos) ht
  have ha_pos : 0 < c' / 12 := by linarith
  have ha_S_ge : c' / 24 ≤ c' / 12 - S := by linarith
  have ha_S_pos : 0 < c' / 12 - S := by linarith
  have hc_rpow : (1 : ℝ) ≤ c' ^ (prob.m : ℝ) := by
    rw [Real.rpow_natCast]; exact one_le_pow₀ hc1
  have hV_nn : 0 ≤ prob.cardyV (c' / 12) t :=
    prob.cardyV_nonneg (by change S ≤ c' / 12; linarith) ht_pos.le
  by_cases htop : xiBar * c' ≤ t
  · have h1 := hband hc' htop
    have hK_le : kernelK prob.w (c' / 12) t ≤ C_hi * prob.cardyV (c' / 12) t := by
      dsimp [C_hi]; rw [one_div_mul_eq_div, le_div_iff₀ hcb_pos]; linarith
    calc kernelK prob.w (c' / 12) t
        ≤ C_hi * prob.cardyV (c' / 12) t := hK_le
      _ ≤ C_K * (1 * prob.cardyV (c' / 12) t) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hV_nn
      _ ≤ C_K * (c' ^ (prob.m : ℝ) * prob.cardyV (c' / 12) t) := by
          gcongr
      _ = C_K * c' ^ (prob.m : ℝ) * prob.cardyV (c' / 12) t := by ring
  · push Not at htop
    by_cases hmid : C_R / c' ≤ t
    · let z₀ : ℝ := 4 * Real.pi * Real.sqrt ((c' / 12) * t)
      let z₁ : ℝ := 4 * Real.pi * Real.sqrt ((c' / 12 - S) * t)
      have hz₀_pos : 0 < z₀ := by dsimp [z₀]; positivity
      have hz₁_pos : 0 < z₁ := by dsimp [z₁]; positivity
      have hz₁_le_z₀ : z₁ ≤ z₀ := by
        dsimp [z₁, z₀]; gcongr; linarith [prob.totalShift_nonneg]
      have hz₁_ge_R0 : R₀ ≤ z₁ := by
        dsimp [z₁]
        have h1 : (R₀ / (4 * Real.pi)) ^ 2 ≤ (c' / 12 - S) * t := by
          have := mul_le_mul_of_nonneg_left hmid (show 0 ≤ c' / 24 by positivity)
          have heq : (c' / 24) * (C_R / c') = (R₀ / (4 * Real.pi)) ^ 2 := by
            dsimp [C_R]; field_simp [hc'_pos.ne']
          have hle : (c' / 24) * t ≤ (c' / 12 - S) * t := by gcongr
          linarith
        have h2 := Real.sqrt_le_sqrt h1
        rw [Real.sqrt_sq (by positivity)] at h2
        rw [← div_le_iff₀' (by positivity : 0 < 4 * Real.pi)]
        exact h2
      have hR0_le_z₀ : R₀ ≤ z₀ := hz₁_ge_R0.trans hz₁_le_z₀
      have hI_w_bd := hI_w hz₀_pos
      have hI_wm_bd := hI_wm hz₁_pos
      have hCw : C_I_w / z₀ ≤ 1 / 2 := by
        have h1 : 2 * C_I_w ≤ z₀ := (le_max_left _ _).trans ((le_max_right _ _).trans hR0_le_z₀)
        rw [div_le_iff₀ hz₀_pos]; linarith
      have hCwm : C_I_wm / z₁ ≤ 1 / 2 := by
        have h1 : 2 * C_I_wm ≤ z₁ := (le_max_right _ _).trans ((le_max_right _ _).trans hz₁_ge_R0)
        rw [div_le_iff₀ hz₁_pos]; linarith
      have hAs0_pos : 0 < besselAs z₀ := besselAs_pos hz₀_pos
      have hAs1_pos : 0 < besselAs z₁ := besselAs_pos hz₁_pos
      have hI₀_ub : besselI (prob.w - 1) z₀ ≤ (3 / 2) * besselAs z₀ := by
        have hsub : besselI (prob.w - 1) z₀ / besselAs z₀ ≤ 3 / 2 := by
          linarith [(abs_le.mp hI_w_bd).2]
        exact (div_le_iff₀ hAs0_pos).mp hsub
      have hI₁_lb : (1 / 2) * besselAs z₁ ≤ besselI (prob.w - 1 + prob.m) z₁ := by
        have hsub : 1 / 2 ≤ besselI (prob.w - 1 + prob.m) z₁ / besselAs z₁ := by
          linarith [(abs_le.mp hI_wm_bd).1]
        exact (le_div_iff₀ hAs1_pos).mp hsub
      have hK_eq := kernelK_eq_besselI hw ha_pos ht_pos
      have hV_lb := cardyV_ge_besselI_shift prob (show S < c' / 12 by linarith) ht_pos
      have hAs_ratio : besselAs z₀ ≤ Real.exp (4 * Real.pi * S * Real.sqrt (12 * xiBar)) * besselAs z₁ := by
        rw [← div_le_iff₀ hAs1_pos]
        unfold besselAs
        have hrt : Real.sqrt (2 * Real.pi * z₁) ≤ Real.sqrt (2 * Real.pi * z₀) :=
          Real.sqrt_le_sqrt (by gcongr)
        have hexp_diff : z₀ - z₁ ≤ 4 * Real.pi * S * Real.sqrt (12 * xiBar) := by
          dsimp [z₀, z₁]
          have hsum_ge : Real.sqrt ((c' / 12) * t) ≤ Real.sqrt ((c' / 12) * t) + Real.sqrt ((c' / 12 - S) * t) :=
            le_add_of_nonneg_right (Real.sqrt_nonneg _)
          have hdiff_sq : (Real.sqrt ((c' / 12) * t) + Real.sqrt ((c' / 12 - S) * t)) *
              (Real.sqrt ((c' / 12) * t) - Real.sqrt ((c' / 12 - S) * t)) = S * t := by
            rw [← sq_sub_sq, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]; ring
          have hdiff_nn : 0 ≤ Real.sqrt ((c' / 12) * t) - Real.sqrt ((c' / 12 - S) * t) := by
            exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by gcongr; linarith [prob.totalShift_nonneg]))
          have hratio : Real.sqrt ((c' / 12) * t) - Real.sqrt ((c' / 12 - S) * t) ≤
              S * Real.sqrt (t / (c' / 12)) := by
            have hmul_sq : Real.sqrt ((c' / 12) * t) * Real.sqrt (t / (c' / 12)) = t := by
              rw [← Real.sqrt_mul (by positivity),
                show (c' / 12) * t * (t / (c' / 12)) = t ^ 2 by field_simp [ha_pos.ne'],
                Real.sqrt_sq ht_pos.le]
            have hstep := mul_le_mul_of_nonneg_right hsum_ge hdiff_nn
            rw [hdiff_sq] at hstep
            have hle_St : Real.sqrt ((c' / 12) * t) *
                (Real.sqrt ((c' / 12) * t) - Real.sqrt ((c' / 12 - S) * t)) ≤ S * t := by
              have hnonneg : 0 ≤ Real.sqrt ((c' / 12 - S) * t) *
                  (Real.sqrt ((c' / 12) * t) - Real.sqrt ((c' / 12 - S) * t)) :=
                mul_nonneg (Real.sqrt_nonneg _) hdiff_nn
              have hsplit : (Real.sqrt ((c' / 12) * t) + Real.sqrt ((c' / 12 - S) * t)) *
                  (Real.sqrt ((c' / 12) * t) - Real.sqrt ((c' / 12 - S) * t)) =
                  Real.sqrt ((c' / 12) * t) * (Real.sqrt ((c' / 12) * t) - Real.sqrt ((c' / 12 - S) * t)) +
                    Real.sqrt ((c' / 12 - S) * t) * (Real.sqrt ((c' / 12) * t) - Real.sqrt ((c' / 12 - S) * t)) := by ring
              linarith
            refine le_of_mul_le_mul_left ?_ (Real.sqrt_pos.mpr (by positivity : 0 < (c' / 12) * t))
            calc Real.sqrt ((c' / 12) * t) * (Real.sqrt ((c' / 12) * t) - Real.sqrt ((c' / 12 - S) * t))
                ≤ S * t := hle_St
              _ = S * (Real.sqrt ((c' / 12) * t) * Real.sqrt (t / (c' / 12))) := by rw [hmul_sq]
              _ = Real.sqrt ((c' / 12) * t) * (S * Real.sqrt (t / (c' / 12))) := by ring
          have hta_le : Real.sqrt (t / (c' / 12)) ≤ Real.sqrt (12 * xiBar) := by
            refine Real.sqrt_le_sqrt ?_
            rw [div_le_iff₀ ha_pos]
            calc t ≤ xiBar * c' := htop.le
              _ = 12 * xiBar * (c' / 12) := by ring
          calc 4 * Real.pi * Real.sqrt ((c' / 12) * t) - 4 * Real.pi * Real.sqrt ((c' / 12 - S) * t)
              = 4 * Real.pi * (Real.sqrt ((c' / 12) * t) - Real.sqrt ((c' / 12 - S) * t)) := by ring
            _ ≤ 4 * Real.pi * (S * Real.sqrt (t / (c' / 12))) :=
                mul_le_mul_of_nonneg_left hratio (by positivity)
            _ ≤ 4 * Real.pi * (S * Real.sqrt (12 * xiBar)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hta_le prob.totalShift_nonneg)
                  (by positivity)
            _ = 4 * Real.pi * S * Real.sqrt (12 * xiBar) := by ring
        have hden1 : (0 : ℝ) < Real.sqrt (2 * Real.pi * z₁) := Real.sqrt_pos.mpr (by positivity)
        rw [div_div_div_comm, ← Real.exp_sub]
        calc Real.exp (z₀ - z₁) / (Real.sqrt (2 * Real.pi * z₀) / Real.sqrt (2 * Real.pi * z₁))
            ≤ Real.exp (z₀ - z₁) / 1 := by gcongr; exact (one_le_div hden1).mpr hrt
          _ = Real.exp (z₀ - z₁) := div_one _
          _ ≤ Real.exp (4 * Real.pi * S * Real.sqrt (12 * xiBar)) := Real.exp_le_exp.mpr hexp_diff
      have hpow_fac : Real.sqrt (t / (c' / 12)) ^ (prob.w - 1) ≤
          Real.sqrt 2 ^ (prob.w - 1) * (1 / Real.sqrt 48) ^ prob.m * c' ^ (prob.m : ℝ) *
            Real.sqrt (t / (c' / 12 - S)) ^ (prob.w - 1 + prob.m) := by
        have h1 : t / (c' / 12) ≤ 2 * (t / (c' / 12 - S)) := by
          rw [← mul_div_assoc, div_le_div_iff₀ ha_pos ha_S_pos]
          nlinarith [ht_pos, prob.totalShift_nonneg]
        have hsqrt_le : Real.sqrt (t / (c' / 12)) ≤ Real.sqrt 2 * Real.sqrt (t / (c' / 12 - S)) := by
          rw [← Real.sqrt_mul (by norm_num)]; exact Real.sqrt_le_sqrt h1
        have hp_w : Real.sqrt (t / (c' / 12)) ^ (prob.w - 1) ≤
            Real.sqrt 2 ^ (prob.w - 1) * Real.sqrt (t / (c' / 12 - S)) ^ (prob.w - 1) := by
          calc Real.sqrt (t / (c' / 12)) ^ (prob.w - 1)
              ≤ (Real.sqrt 2 * Real.sqrt (t / (c' / 12 - S))) ^ (prob.w - 1) :=
                pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_le _
            _ = Real.sqrt 2 ^ (prob.w - 1) * Real.sqrt (t / (c' / 12 - S)) ^ (prob.w - 1) := by
                rw [mul_pow]
        have hp_m : (1 : ℝ) ≤ (1 / Real.sqrt 48) ^ prob.m * c' ^ (prob.m : ℝ) *
            Real.sqrt (t / (c' / 12 - S)) ^ prob.m := by
          have hlow : 1 / Real.sqrt 48 * c' * Real.sqrt (t / (c' / 12 - S)) ≥ 1 := by
            have h48_le : (48 / c' ^ 2 : ℝ) ≤ t / (c' / 12 - S) := by
              rw [div_le_div_iff₀ (by positivity) ha_S_pos]
              have h48 : (48 : ℝ) * (c' / 12 - S) ≤ 4 * c' := by linarith [prob.totalShift_nonneg]
              calc 48 * (c' / 12 - S) ≤ 4 * c' := h48
                _ = (4 / c') * c' ^ 2 := by field_simp [hc'_pos.ne']
                _ ≤ t * c' ^ 2 := mul_le_mul_of_nonneg_right ht (sq_nonneg _)
            have hsqrt_low : Real.sqrt 48 / c' ≤ Real.sqrt (t / (c' / 12 - S)) := by
              nth_rw 1 [← Real.sqrt_sq hc'_pos.le]
              rw [← Real.sqrt_div (by positivity)]
              exact Real.sqrt_le_sqrt h48_le
            have h11 : 1 = 1 / Real.sqrt 48 * c' * (Real.sqrt 48 / c') := by
              field_simp [hc'_pos.ne', (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 48)).ne']
            calc (1 : ℝ) = 1 / Real.sqrt 48 * c' * (Real.sqrt 48 / c') := h11
              _ ≤ 1 / Real.sqrt 48 * c' * Real.sqrt (t / (c' / 12 - S)) := by gcongr
          rw [Real.rpow_natCast, ← mul_pow, ← mul_pow]
          exact one_le_pow₀ hlow
        rw [pow_add]
        calc Real.sqrt (t / (c' / 12)) ^ (prob.w - 1)
            ≤ Real.sqrt 2 ^ (prob.w - 1) * Real.sqrt (t / (c' / 12 - S)) ^ (prob.w - 1) * 1 := by
              rw [mul_one]; exact hp_w
          _ ≤ Real.sqrt 2 ^ (prob.w - 1) * Real.sqrt (t / (c' / 12 - S)) ^ (prob.w - 1) *
                ((1 / Real.sqrt 48) ^ prob.m * c' ^ (prob.m : ℝ) *
                  Real.sqrt (t / (c' / 12 - S)) ^ prob.m) := by
              exact mul_le_mul_of_nonneg_left hp_m (by positivity)
          _ = _ := by ring
      have hK_le_mid : kernelK prob.w (c' / 12) t ≤ C_mid * c' ^ (prob.m : ℝ) * prob.cardyV (c' / 12) t := by
        have hV_term : P * (2 * Real.pi) ^ prob.m * Real.sqrt (t / (c' / 12 - S)) ^ (prob.w - 1 + prob.m) *
              besselAs z₁ ≤ 2 * prob.cardyV (c' / 12) t := by
          calc P * (2 * Real.pi) ^ prob.m * Real.sqrt (t / (c' / 12 - S)) ^ (prob.w - 1 + prob.m) *
                besselAs z₁
              = 2 * (P * (2 * Real.pi) ^ prob.m * Real.sqrt (t / (c' / 12 - S)) ^ (prob.w - 1 + prob.m) *
                  ((1 / 2) * besselAs z₁)) := by ring
            _ ≤ 2 * (P * (2 * Real.pi) ^ prob.m * Real.sqrt (t / (c' / 12 - S)) ^ (prob.w - 1 + prob.m) *
                  besselI (prob.w - 1 + prob.m) z₁) := by
                gcongr
            _ ≤ 2 * prob.cardyV (c' / 12) t := by gcongr
        have hP2pi : (0 : ℝ) < P * (2 * Real.pi) ^ prob.m := by positivity
        calc kernelK prob.w (c' / 12) t
            = Real.sqrt (t / (c' / 12)) ^ (prob.w - 1) * besselI (prob.w - 1) z₀ := hK_eq
          _ ≤ Real.sqrt (t / (c' / 12)) ^ (prob.w - 1) * ((3 / 2) * besselAs z₀) := by gcongr
          _ ≤ (Real.sqrt 2 ^ (prob.w - 1) * (1 / Real.sqrt 48) ^ prob.m * c' ^ (prob.m : ℝ) *
                Real.sqrt (t / (c' / 12 - S)) ^ (prob.w - 1 + prob.m)) *
                ((3 / 2) * (Real.exp (4 * Real.pi * S * Real.sqrt (12 * xiBar)) * besselAs z₁)) := by
              refine mul_le_mul hpow_fac (mul_le_mul_of_nonneg_left hAs_ratio (by norm_num))
                (by positivity) (by positivity)
          _ = (3 / 2) / (P * (2 * Real.pi) ^ prob.m) *
                (Real.sqrt 2 ^ (prob.w - 1) * (1 / Real.sqrt 48) ^ prob.m) *
                Real.exp (4 * Real.pi * S * Real.sqrt (12 * xiBar)) * c' ^ (prob.m : ℝ) *
                (P * (2 * Real.pi) ^ prob.m * Real.sqrt (t / (c' / 12 - S)) ^ (prob.w - 1 + prob.m) *
                  besselAs z₁) := by
              field_simp [hP2pi.ne']
          _ ≤ (3 / 2) / (P * (2 * Real.pi) ^ prob.m) *
                (Real.sqrt 2 ^ (prob.w - 1) * (1 / Real.sqrt 48) ^ prob.m) *
                Real.exp (4 * Real.pi * S * Real.sqrt (12 * xiBar)) * c' ^ (prob.m : ℝ) *
                (2 * prob.cardyV (c' / 12) t) := by
              gcongr
          _ = C_mid * c' ^ (prob.m : ℝ) * prob.cardyV (c' / 12) t := by
              dsimp [C_mid]; ring
      calc kernelK prob.w (c' / 12) t
          ≤ C_mid * c' ^ (prob.m : ℝ) * prob.cardyV (c' / 12) t := hK_le_mid
        _ ≤ C_K * c' ^ (prob.m : ℝ) * prob.cardyV (c' / 12) t := by
            have hCK : C_mid ≤ C_K := (le_max_right _ _).trans (le_max_right _ _)
            gcongr
    · push Not at hmid
      have hK_ub : kernelK prob.w (c' / 12) t ≤
          (2 * Real.pi * t) ^ (prob.w - 1) * Real.exp (4 * Real.pi * Real.sqrt (C_R / 12)) := by
        unfold kernelK
        have hs_eq : (∑' j : ℕ, kernelKTerm prob.w (c' / 12) t j) =
            besselS (prob.w - 1) (4 * Real.pi ^ 2 * (c' / 12) * t) := by
          unfold besselS besselTerm kernelKTerm
          refine tsum_congr fun j => ?_
          rw [show j + prob.w - 1 = j + (prob.w - 1) by omega]
        rw [hs_eq]
        have hs_exp : besselS (prob.w - 1) (4 * Real.pi ^ 2 * (c' / 12) * t) ≤
            Real.exp (4 * Real.pi * Real.sqrt ((c' / 12) * t)) := by
          have h1 := besselS_le_exp_sqrt (prob.w - 1) (by positivity : 0 ≤ 4 * Real.pi ^ 2 * (c' / 12) * t)
          have harg : 2 * Real.sqrt (4 * Real.pi ^ 2 * (c' / 12) * t) =
              4 * Real.pi * Real.sqrt ((c' / 12) * t) := by
            rw [show 4 * Real.pi ^ 2 * (c' / 12) * t = (2 * Real.pi) ^ 2 * ((c' / 12) * t) by ring,
              Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
            ring
          rwa [harg] at h1
        have hsqrt_ub : Real.sqrt ((c' / 12) * t) ≤ Real.sqrt (C_R / 12) := by
          refine Real.sqrt_le_sqrt ?_
          calc (c' / 12) * t ≤ (c' / 12) * (C_R / c') := by gcongr
            _ = C_R / 12 := by field_simp [hc'_pos.ne']
        have hexp_ub : Real.exp (4 * Real.pi * Real.sqrt ((c' / 12) * t)) ≤
            Real.exp (4 * Real.pi * Real.sqrt (C_R / 12)) :=
          Real.exp_le_exp.mpr (by gcongr)
        exact mul_le_mul_of_nonneg_left (hs_exp.trans hexp_ub) (by positivity)
      have hV_lb := prob.cardyV_lower_bound (by change S ≤ c' / 12; linarith) ht_pos.le
      have hV_lb' : (P * (4 * Real.pi ^ 2) ^ prob.m / ((prob.m + prob.w - 1)! : ℝ)) *
            t ^ prob.m * (2 * Real.pi * t) ^ (prob.w - 1) ≤ prob.cardyV (c' / 12) t := by
        have hpow_t : t ^ (prob.m + prob.w - 1) = t ^ prob.m * t ^ (prob.w - 1) := by
          rw [← pow_add]; congr 1; omega
        rw [hpow_t] at hV_lb
        refine le_trans ?_ hV_lb
        rw [mul_pow]
        dsimp [P]
        ring_nf
        exact le_rfl
      have h4ct : (4 : ℝ) ^ prob.m ≤ t ^ prob.m * c' ^ (prob.m : ℝ) := by
        have h1 : 4 ≤ t * c' := by rw [div_le_iff₀ hc'_pos] at ht; exact ht
        rw [Real.rpow_natCast, ← mul_pow]
        exact pow_le_pow_left₀ (by positivity) h1 prob.m
      have hK_le_low : kernelK prob.w (c' / 12) t ≤ C_low * c' ^ (prob.m : ℝ) * prob.cardyV (c' / 12) t := by
        have hfac_pos : 0 < P * (16 * Real.pi ^ 2) ^ prob.m := by positivity
        have h_eq : (16 * Real.pi ^ 2) ^ prob.m = 4 ^ prob.m * (4 * Real.pi ^ 2) ^ prob.m := by
          rw [← mul_pow]; congr 1; ring
        calc kernelK prob.w (c' / 12) t
            ≤ (2 * Real.pi * t) ^ (prob.w - 1) * Real.exp (4 * Real.pi * Real.sqrt (C_R / 12)) := hK_ub
          _ = (((prob.m + prob.w - 1)! : ℝ) / (P * (16 * Real.pi ^ 2) ^ prob.m) *
                Real.exp (4 * Real.pi * Real.sqrt (C_R / 12))) * 4 ^ prob.m *
                ((P * (4 * Real.pi ^ 2) ^ prob.m / ((prob.m + prob.w - 1)! : ℝ)) *
                  (2 * Real.pi * t) ^ (prob.w - 1)) := by
              rw [h_eq]; field_simp [hP_pos.ne', Real.pi_pos.ne']
          _ ≤ C_low * (t ^ prob.m * c' ^ (prob.m : ℝ)) *
                ((P * (4 * Real.pi ^ 2) ^ prob.m / ((prob.m + prob.w - 1)! : ℝ)) *
                  (2 * Real.pi * t) ^ (prob.w - 1)) := by
              dsimp [C_low]
              gcongr
          _ = C_low * c' ^ (prob.m : ℝ) *
                ((P * (4 * Real.pi ^ 2) ^ prob.m / ((prob.m + prob.w - 1)! : ℝ)) *
                  t ^ prob.m * (2 * Real.pi * t) ^ (prob.w - 1)) := by ring
          _ ≤ C_low * c' ^ (prob.m : ℝ) * prob.cardyV (c' / 12) t := by gcongr
      calc kernelK prob.w (c' / 12) t
          ≤ C_low * c' ^ (prob.m : ℝ) * prob.cardyV (c' / 12) t := hK_le_low
        _ ≤ C_K * c' ^ (prob.m : ℝ) * prob.cardyV (c' / 12) t := by
            have hCK : C_low ≤ C_K := (le_max_left _ _).trans (le_max_right _ _)
            gcongr

/-- **Lemma 4(c), paper-stated `(1 + c'^m) max(1, t^{-m})` and `p_K = 2m` bounds (`n1:L4`)**. -/
theorem kernelK_le_mul_cardyV_n1 (prob : FixedWeightProblem) :
    ∃ C_K c₀ : ℝ, 0 < C_K ∧ max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ {c' t : ℝ}, c₀ ≤ c' → 4 / c' ≤ t →
        kernelK prob.w (c' / 12) t ≤ C_K * c' ^ (2 * prob.m : ℝ) * prob.cardyV (c' / 12) t ∧
        kernelK prob.w (c' / 12) t ≤
          C_K * (1 + c' ^ (prob.m : ℝ)) * max 1 (t ^ (-(prob.m : ℝ))) * prob.cardyV (c' / 12) t := by
  obtain ⟨C_K, c₀, hCK, hc₀, hbd⟩ := kernelK_le_mul_cardyV_gen prob
  refine ⟨C_K, c₀, hCK, hc₀, fun {c' t} hc' ht => ?_⟩
  have hcm : max 1 (24 * prob.totalShift) ≤ c' := hc₀.trans hc'
  have hc1 : 1 ≤ c' := (le_max_left _ _).trans hcm
  have hc'_pos : 0 < c' := lt_of_lt_of_le zero_lt_one hc1
  have hV_nn : 0 ≤ prob.cardyV (c' / 12) t :=
    prob.cardyV_nonneg (by linarith [(le_max_right (1 : ℝ) (24 * prob.totalShift)).trans hcm])
      (lt_of_lt_of_le (div_pos (by norm_num) hc'_pos) ht).le
  have h0 := hbd hc' ht
  refine ⟨?_, ?_⟩
  · have hpow : c' ^ (prob.m : ℝ) ≤ c' ^ (2 * prob.m : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hc1 (by linarith [show (0 : ℝ) ≤ (prob.m : ℝ) by positivity])
    calc kernelK prob.w (c' / 12) t
        ≤ C_K * c' ^ (prob.m : ℝ) * prob.cardyV (c' / 12) t := h0
      _ ≤ C_K * c' ^ (2 * prob.m : ℝ) * prob.cardyV (c' / 12) t := by gcongr
  · have h1 : c' ^ (prob.m : ℝ) ≤ (1 + c' ^ (prob.m : ℝ)) * max 1 (t ^ (-(prob.m : ℝ))) := by
      calc c' ^ (prob.m : ℝ)
          ≤ (1 + c' ^ (prob.m : ℝ)) * 1 := by linarith
        _ ≤ (1 + c' ^ (prob.m : ℝ)) * max 1 (t ^ (-(prob.m : ℝ))) :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    calc kernelK prob.w (c' / 12) t
        ≤ C_K * c' ^ (prob.m : ℝ) * prob.cardyV (c' / 12) t := h0
      _ ≤ C_K * ((1 + c' ^ (prob.m : ℝ)) * max 1 (t ^ (-(prob.m : ℝ)))) * prob.cardyV (c' / 12) t := by
          gcongr
      _ = C_K * (1 + c' ^ (prob.m : ℝ)) * max 1 (t ^ (-(prob.m : ℝ))) * prob.cardyV (c' / 12) t := by
          ring

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.cardyComplexExpansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardyComplexExpansion

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.cardyV_asymptotic_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardyV_asymptotic_real

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.cardyV_lobe_ratio_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardyV_lobe_ratio_bounds

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.cardyV_ge_band_mul_kernelK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardyV_ge_band_mul_kernelK

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.kernelK_le_mul_cardyV_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernelK_le_mul_cardyV_gen

end FormalResearch.ModularBootstrap.WeightAxioms
