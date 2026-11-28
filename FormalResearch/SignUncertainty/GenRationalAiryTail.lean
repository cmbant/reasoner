module

public import FormalResearch.SignUncertainty.Gt1NegTail
public import FormalResearch.SignUncertainty.ConvSourceEdgeTail
public import FormalResearch.SignUncertainty.AiryCauchyBounds
public import FormalResearch.SignUncertainty.AiryRationalSeeds
public import FormalResearch.Special.AiryPwsPW

/-!
# `GT.1`, `U.2`, Imaginary-Axis Bounds, and `ConvTailData` for Generalized Rational–Airy Seeds (`u1c_o1_upper.tex`, `(e22)`–`(e23)`)

For every `F : ℂ → ℂ` with `HasGenRationalAiryCoeffs F β₀₀ β₁₁` (`F ∈ ℛ_Ai^gen`), setting `X(u) := Re F(u)`:

* `inAiryClass_to_airyClassG`: `InAiryClass F → AiryClassG F`;
* `genRational_cutoff_schwartz`: for every `F` with `InAiryClass F`, `x₀ ≥ 1`, and cutoff `χ`,
  `u ↦ F(u) χ(u / x₀)` is `C^{13}` and obeys the `(1 + |u|)^5` Schwartz seminorm bounds of `AiryTailSymbolSeed`
  via repeated `deriv_inAiryClass_bound` on `[0, ∞)` and compactness on `[-2 x₀, 0]`;
* `genRational_symBd_rat`: `P(-w)/Q(-w)` restricts on `(2(R_*+2), ∞)` to a `SymBd 12` symbol of the
  indicated decay order (`symBd_of_sector`);
* `genRational_airytailSymbolSeed`: `(e22)`–`(e23)` + `symBd_negAmp*` + `SymBd` algebra assemble an
  `AiryTailSymbolSeed` with `seed.F = X`;
* `gt1Bounds_of_genRational`: `Gt1Bounds` for `liftW X δ₀ m`, uniform in `δ₀ ∈ [0, 2]` (`m ≥ 3`);
* `imagAxisBounds_of_gt1` & `imagAxisBounds_of_genRational`: `(e27)` `ImagAxisBounds (airyTwistedLaplaceC X)`
  by rescaling `Gt1Bounds` at `δ₀ = 0, m = 3`;
* `hasU2_of_airyClassG_gt1` & `hasU2_of_genRational`: `HasU2 X` via `airyTwistedLaplaceC_regularity`
  and Phragmén–Lindelöf (`pl_halfPlane_decay`);
* `convTailData_of_genRational`: `ConvTailData X δ₀ m c` for all `m ≥ 3`, `δ₀ ∈ [0, 2]`, `c ≥ 8`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric Polynomial
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.CohnElkies

/-! ### Section 1: Conversion `InAiryClass → AiryClassG` and Schwartz right/cutoff bounds -/

/-- Any `F` in `InAiryClass` belongs to `AiryClassG`. -/
lemma inAiryClass_to_airyClassG {F : ℂ → ℂ} (hF : InAiryClass F) : AiryClassG F where
  differentiable := hF.1
  integrable := hF.2.1
  bound := by
    obtain ⟨C, ν, hC, hb⟩ := hF.2.2.1
    refine ⟨C, Nat.ceil (max ν 0), hC, fun z => ?_⟩
    have h1z : 1 ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
    have hνN : ν ≤ (Nat.ceil (max ν 0) : ℝ) := (le_max_left ν 0).trans (Nat.le_ceil _)
    have hrpow : (1 + ‖z‖) ^ ν ≤ (1 + ‖z‖) ^ Nat.ceil (max ν 0) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le h1z hνN
    exact (hb z).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrpow hC) (airyEnv_pos z).le)

lemma deriv_iterated_inAiryClass_bound {F : ℂ → ℂ} (hF : InAiryClass F) :
    ∀ k : ℕ, ∃ Ck νk : ℝ, 0 ≤ Ck ∧ ∀ z : ℂ, ‖iteratedDeriv k F z‖ ≤ Ck * (1 + ‖z‖) ^ νk * airyEnv z := by
  intro k
  induction k with
  | zero =>
    obtain ⟨C, ν, hC, hb⟩ := hF.2.2.1
    exact ⟨C, ν, hC, fun z => by simpa using hb z⟩
  | succ k ih =>
    obtain ⟨Ck, νk, hCk, hk⟩ := ih
    have hdiff : Differentiable ℂ (iteratedDeriv k F) :=
      (hF.1.contDiff (n := (k + 1 : ℕ))).differentiable_iteratedDeriv' k
    refine ⟨Ck * 4 ^ |νk| * Real.exp 40, νk + 1 / 2, by positivity, fun z => ?_⟩
    rw [iteratedDeriv_succ]
    exact deriv_inAiryClass_bound hdiff hCk hk z

lemma rpow_mul_exp_neg_rpow32_bounded (ν : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ, 0 ≤ u → (1 + u) ^ ν * Real.exp (-r * u ^ (3 / 2 : ℝ)) ≤ B := by
  let N : ℕ := Nat.ceil (max ν 0)
  have hνN : ν ≤ (N : ℝ) := (le_max_left ν 0).trans (Nat.le_ceil _)
  let B₁ : ℝ := 2 ^ N
  let B₂ : ℝ := 2 ^ N * ((N.factorial : ℝ) / r ^ N)
  refine ⟨max B₁ B₂, le_trans (by positivity) (le_max_left B₁ B₂), fun u hu => ?_⟩
  have h1u : 1 ≤ 1 + u := by linarith
  have hpow : (1 + u) ^ ν ≤ (1 + u) ^ N := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le h1u hνN
  have hexp_le1 : Real.exp (-r * u ^ (3 / 2 : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.rpow_nonneg hu (3 / 2 : ℝ)])
  by_cases hu1 : u ≤ 1
  · have hp : (1 + u) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    calc (1 + u) ^ ν * Real.exp (-r * u ^ (3 / 2 : ℝ))
        ≤ (1 + u) ^ N * 1 := mul_le_mul hpow hexp_le1 (Real.exp_pos _).le (by positivity)
      _ ≤ 2 ^ N := by linarith
      _ ≤ max B₁ B₂ := le_max_left _ _
  · push Not at hu1
    have hp : (1 + u) ^ N ≤ 2 ^ N * u ^ N := by
      calc (1 + u) ^ N ≤ (2 * u) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
        _ = 2 ^ N * u ^ N := mul_pow 2 u N
    have hu_le : u ≤ u ^ (3 / 2 : ℝ) := by
      calc u = u ^ (1 : ℝ) := (Real.rpow_one u).symm
        _ ≤ u ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1.le (by norm_num)
    have hexp_le2 : Real.exp (-r * u ^ (3 / 2 : ℝ)) ≤ Real.exp (-r * u) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hgt := gt1d_pow_le_exp hr N hu
    calc (1 + u) ^ ν * Real.exp (-r * u ^ (3 / 2 : ℝ))
        ≤ (2 ^ N * u ^ N) * Real.exp (-r * u) :=
          mul_le_mul (hpow.trans hp) hexp_le2 (Real.exp_pos _).le (by positivity)
      _ = 2 ^ N * (u ^ N * Real.exp (-r * u)) := by ring
      _ ≤ 2 ^ N * (((N.factorial : ℝ) / r ^ N) * Real.exp (r * u) * Real.exp (-r * u)) := by gcongr
      _ = B₂ := by
          have he1 : Real.exp (r * u) * Real.exp (-r * u) = 1 := by rw [← Real.exp_add]; simp
          rw [mul_assoc, he1, mul_one]
      _ ≤ max B₁ B₂ := le_max_right _ _

/-- For any `F` in `InAiryClass`, `x₀ ≥ 1`, and smooth cutoff `χ`, `u ↦ F(u) χ(u / x₀)` is `C^{13}`
with weighted `(1 + |u|)^5` Schwartz seminorm bounds through order `12`. -/
theorem genRational_cutoff_schwartz {F : ℂ → ℂ} (hF : InAiryClass F) {x₀ : ℝ} (hx₀ : 1 ≤ x₀) (χ : AiryCutoff) :
    let X : ℝ → ℝ := fun u => (F (u : ℂ)).re
    ContDiff ℝ (13 : ℕ) (fun u => (X u : ℂ) * (χ.val (u / x₀) : ℂ)) ∧
    ∃ S : ℝ, 0 ≤ S ∧ ∀ k : ℕ, k ≤ 12 → ∀ u : ℝ,
      (1 + |u|) ^ 5 * ‖iteratedDeriv k (fun t => (X t : ℂ) * (χ.val (t / x₀) : ℂ)) u‖ ≤ S := by
  intro X
  have hx₀_pos : 0 < x₀ := by linarith
  have hX_cd : ContDiff ℝ (⊤ : ℕ∞) X := (contDiff_re_of_differentiable hF.1).1
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => χ.val (t / x₀)) :=
    χ.contDiff.comp (contDiff_id.div_const x₀)
  let g : ℝ → ℂ := fun t => (X t : ℂ) * (χ.val (t / x₀) : ℂ)
  have hg_top : ContDiff ℝ (⊤ : ℕ∞) g :=
    (Complex.ofRealCLM.contDiff.comp hX_cd).mul (Complex.ofRealCLM.contDiff.comp hψ)
  refine ⟨hg_top.of_le (by norm_cast), ?_⟩
  have hk_bound : ∀ k : ℕ, ∃ Sk : ℝ, 0 ≤ Sk ∧ ∀ u : ℝ,
      (1 + |u|) ^ 5 * ‖iteratedDeriv k g u‖ ≤ Sk := by
    intro k
    obtain ⟨Ck, νk, hCk, hFk⟩ := deriv_iterated_inAiryClass_bound hF k
    obtain ⟨Bk, hBk, hBku⟩ := rpow_mul_exp_neg_rpow32_bounded (νk + 5) (r := 4 / 3) (by norm_num)
    have hcont_k : Continuous fun u : ℝ => (1 + |u|) ^ 5 * ‖iteratedDeriv k g u‖ := by
      have hid := hg_top.continuous_iteratedDeriv k (by exact_mod_cast (ENat.natCast_lt_top k).le)
      fun_prop
    obtain ⟨M_cp, hM_cp⟩ := (isCompact_Icc (a := -(2 * x₀)) (b := 0)).exists_bound_of_continuousOn
      hcont_k.continuousOn
    refine ⟨max (Ck * Bk) (max M_cp 0), le_trans (by positivity) (le_max_left _ _), fun u => ?_⟩
    rcases lt_or_ge u (-(2 * x₀)) with hlt | hge
    · have hzero : g =ᶠ[𝓝 u] fun _ => (0 : ℂ) := by
        filter_upwards [isOpen_Iio.mem_nhds hlt] with t (ht : t < -(2 * x₀))
        have ht2 : t / x₀ ≤ -2 := (div_le_iff₀ hx₀_pos).mpr (by linarith)
        simp [g, χ.eq_zero _ ht2]
      rw [hzero.iteratedDeriv_eq]
      simp
    · rcases le_or_gt u 0 with hu0 | hu_pos
      · have h1 := hM_cp u ⟨hge, hu0⟩
        rw [Real.norm_of_nonneg (by positivity)] at h1
        exact h1.trans ((le_max_left _ _).trans (le_max_right _ _))
      · have hpos_eq : g =ᶠ[𝓝 u] fun t => (X t : ℂ) := by
          filter_upwards [isOpen_Ioi.mem_nhds hu_pos] with t (ht : 0 < t)
          have ht1 : -1 ≤ t / x₀ := (le_div_iff₀ hx₀_pos).mpr (by linarith)
          simp [g, χ.eq_one _ ht1]
        rw [hpos_eq.iteratedDeriv_eq, gt1d_iteratedDeriv_ofReal hX_cd k]
        dsimp [X]
        rw [iteratedDeriv_re_of_differentiable hF.1 k u, Complex.norm_real, Real.norm_eq_abs]
        have hF_bd := (Complex.abs_re_le_norm (iteratedDeriv k F (u : ℂ))).trans (hFk (u : ℂ))
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos, airyEnv_ofReal_nonneg hu_pos.le] at hF_bd
        have h1u_pos : 0 < 1 + u := by linarith
        have hadd : (1 + u) ^ (5 : ℝ) * (1 + u) ^ νk = (1 + u) ^ (νk + 5) := by
          rw [← Real.rpow_add h1u_pos]; ring_nf
        have h15 : (1 + |u|) ^ 5 = (1 + u) ^ (5 : ℝ) := by
          rw [abs_of_pos hu_pos, ← Real.rpow_natCast]; norm_num
        calc (1 + |u|) ^ 5 * |(iteratedDeriv k F (u : ℂ)).re|
            ≤ (1 + u) ^ (5 : ℝ) * (Ck * (1 + u) ^ νk * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ))) := by
              rw [h15]; exact mul_le_mul_of_nonneg_left hF_bd (by positivity)
          _ = Ck * ((1 + u) ^ (νk + 5) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ))) := by
              rw [← hadd]; ring
          _ ≤ Ck * Bk := mul_le_mul_of_nonneg_left (hBku u hu_pos.le) hCk
          _ ≤ _ := le_max_left _ _
  have hk_ex : ∀ k ∈ Finset.range 13, ∃ Sk : ℝ, 0 ≤ Sk ∧ ∀ u : ℝ,
      (1 + |u|) ^ 5 * ‖iteratedDeriv k g u‖ ≤ Sk := fun k _ => hk_bound k
  choose Sk hSk0 hSk using hk_bound
  refine ⟨∑ k ∈ Finset.range 13, Sk k, Finset.sum_nonneg fun k _ => hSk0 k, ?_⟩
  intro k hk u
  exact (hSk k u).trans (Finset.single_le_sum (f := Sk) (fun j _ => hSk0 j)
    (Finset.mem_range.mpr (by omega)))

/-! ### Section 2: Symbol bounds for rational coefficients and `AiryTailSymbolSeed` -/

lemma differentiable_aeval_complex (P : ℝ[X]) :
    Differentiable ℂ (fun z : ℂ => Polynomial.aeval z P) := by
  have h : (fun z : ℂ => Polynomial.aeval z P) =
      fun z => ∑ i ∈ Finset.range (P.natDegree + 1), ((P.coeff i : ℝ) : ℂ) * z ^ i := by
    ext z; simp [Polynomial.aeval_eq_sum_range]
  rw [h]; fun_prop

lemma aeval_neg_ne_zero_of_sector {Q : ℝ[X]} {R_star x₀ : ℝ} (hx₀ : 2 * (R_star + 2) ≤ x₀)
    (hQ : ∀ z : ℂ, Polynomial.aeval z Q = 0 → z.im = 0 ∧ ‖z‖ ≤ R_star)
    {w : ℂ} (hw : x₀ / 2 < w.re) :
    Polynomial.aeval (-w) Q ≠ 0 := by
  intro h0
  have hle := (hQ (-w) h0).2
  rw [norm_neg] at hle
  have hre : R_star + 2 < w.re := by linarith
  linarith [hre.trans_le (Complex.re_le_norm w)]

lemma symBd_neg_rat (P Q : ℝ[X]) {R_star : ℝ} (hR4 : 4 ≤ R_star)
    (hQ : ∀ z : ℂ, Polynomial.aeval z Q = 0 → z.im = 0 ∧ ‖z‖ ≤ R_star)
    {β M : ℝ} (hM : 0 ≤ M)
    (hbd : ∀ w : ℂ, R_star + 2 ≤ ‖w‖ → ‖Polynomial.aeval (-w) P / Polynomial.aeval (-w) Q‖ ≤ M * ‖w‖ ^ (-β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      SymBd 12 (2 * (R_star + 2)) β C (fun x : ℝ => Polynomial.aeval (-(x : ℂ)) P / Polynomial.aeval (-(x : ℂ)) Q) := by
  obtain ⟨Kc, hKc, hsym⟩ := symBd_of_sector 12 β
  let x₀ : ℝ := 2 * (R_star + 2)
  have hx₀ : 0 < x₀ := by dsimp [x₀]; linarith
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => Polynomial.aeval (-w) P / Polynomial.aeval (-w) Q)
      {w : ℂ | x₀ / 2 < w.re ∧ |w.im| < w.re / 2} := by
    intro w hw
    have hne : Polynomial.aeval (-w) Q ≠ 0 := aeval_neg_ne_zero_of_sector (le_rfl : 2 * (R_star + 2) ≤ x₀) hQ hw.1
    exact (((differentiable_aeval_complex P).comp differentiable_neg w).div
      ((differentiable_aeval_complex Q).comp differentiable_neg w) hne).differentiableWithinAt
  have hsec : ∀ w : ℂ, x₀ / 2 < w.re → |w.im| < w.re / 2 →
      ‖Polynomial.aeval (-w) P / Polynomial.aeval (-w) Q‖ ≤ M * ‖w‖ ^ (-β) := fun w hw _ => by
    apply hbd w
    have hre : R_star + 2 ≤ w.re := by dsimp [x₀] at hw; linarith
    exact hre.trans (Complex.re_le_norm w)
  exact ⟨Kc * M, mul_nonneg hKc hM, hsym hx₀ hM hdiff hsec⟩

/-- Negative-tail `AiryTailSymbolSeed` for every `F` satisfying `HasGenRationalAiryCoeffs F β₀₀ β₁₁`. -/
theorem genRational_airytailSymbolSeed {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF : HasGenRationalAiryCoeffs F β₀₀ β₁₁) (χ : AiryCutoff) :
    ∃ x₀ S M : ℝ, 2 ≤ x₀ ∧ 0 ≤ S ∧ 0 ≤ M ∧
      ∃ seed : AiryTailSymbolSeed x₀ χ S M, seed.F = fun u : ℝ => (F (u : ℂ)).re := by
  obtain ⟨hIn, R_star, C, P00, Q00, P01, Q01, P11, Q11, hR4, hC0, _, _, _, hQ00, hQ01, hQ11, hrep, hasym⟩ := hF
  let X : ℝ → ℝ := fun u => (F (u : ℂ)).re
  let x₀ : ℝ := 2 * (R_star + 2)
  have hx0_ge12 : 12 ≤ x₀ := by dsimp [x₀]; linarith
  have hx0_pos : 0 < x₀ := by linarith
  have hx0_1 : 1 ≤ x₀ := by linarith
  have hx0_2 : 2 ≤ x₀ := by linarith
  let r00 : ℝ → ℂ := fun x => Polynomial.aeval (-(x : ℂ)) P00 / Polynomial.aeval (-(x : ℂ)) Q00
  let r01 : ℝ → ℂ := fun x => Polynomial.aeval (-(x : ℂ)) P01 / Polynomial.aeval (-(x : ℂ)) Q01
  let r11 : ℝ → ℂ := fun x => Polynomial.aeval (-(x : ℂ)) P11 / Polynomial.aeval (-(x : ℂ)) Q11
  have hr00_bd : ∀ w : ℂ, R_star + 2 ≤ ‖w‖ →
      ‖Polynomial.aeval (-w) P00 / Polynomial.aeval (-w) Q00‖ ≤ (|β₀₀| + C) * ‖w‖ ^ (-1 : ℝ) := fun w hw => by
    have hw1 : 1 ≤ ‖w‖ := by linarith
    have hb : ‖Polynomial.aeval (-w) P00 / Polynomial.aeval (-w) Q00 - (β₀₀ : ℂ) * w⁻¹‖ ≤ C * ‖w‖ ^ (-2 : ℝ) :=
      (hasym w hw).1
    have htri : ‖Polynomial.aeval (-w) P00 / Polynomial.aeval (-w) Q00‖ ≤
        |β₀₀| * ‖w‖ ^ (-1 : ℝ) + ‖Polynomial.aeval (-w) P00 / Polynomial.aeval (-w) Q00 - (β₀₀ : ℂ) * w⁻¹‖ := by
      calc ‖Polynomial.aeval (-w) P00 / Polynomial.aeval (-w) Q00‖
          = ‖(β₀₀ : ℂ) * w⁻¹ + (Polynomial.aeval (-w) P00 / Polynomial.aeval (-w) Q00 - (β₀₀ : ℂ) * w⁻¹)‖ := by ring_nf
        _ ≤ ‖(β₀₀ : ℂ) * w⁻¹‖ + ‖Polynomial.aeval (-w) P00 / Polynomial.aeval (-w) Q00 - (β₀₀ : ℂ) * w⁻¹‖ := norm_add_le _ _
        _ = |β₀₀| * ‖w‖ ^ (-1 : ℝ) + _ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_inv, ← Real.rpow_neg_one ‖w‖]
    have hpow : ‖w‖ ^ (-2 : ℝ) ≤ ‖w‖ ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hw1 (by norm_num)
    calc ‖Polynomial.aeval (-w) P00 / Polynomial.aeval (-w) Q00‖
        ≤ |β₀₀| * ‖w‖ ^ (-1 : ℝ) + C * ‖w‖ ^ (-2 : ℝ) := htri.trans (add_le_add (le_refl _) hb)
      _ ≤ |β₀₀| * ‖w‖ ^ (-1 : ℝ) + C * ‖w‖ ^ (-1 : ℝ) := by gcongr
      _ = (|β₀₀| + C) * ‖w‖ ^ (-1 : ℝ) := by ring
  have hr11_bd : ∀ w : ℂ, R_star + 2 ≤ ‖w‖ →
      ‖Polynomial.aeval (-w) P11 / Polynomial.aeval (-w) Q11‖ ≤ (|β₁₁| + C) * ‖w‖ ^ (-2 : ℝ) := fun w hw => by
    have hw1 : 1 ≤ ‖w‖ := by linarith
    have hb : ‖Polynomial.aeval (-w) P11 / Polynomial.aeval (-w) Q11 - (β₁₁ : ℂ) * (w ^ 2)⁻¹‖ ≤ C * ‖w‖ ^ (-3 : ℝ) :=
      (hasym w hw).2.2
    have htri : ‖Polynomial.aeval (-w) P11 / Polynomial.aeval (-w) Q11‖ ≤
        |β₁₁| * ‖w‖ ^ (-2 : ℝ) + ‖Polynomial.aeval (-w) P11 / Polynomial.aeval (-w) Q11 - (β₁₁ : ℂ) * (w ^ 2)⁻¹‖ := by
      calc ‖Polynomial.aeval (-w) P11 / Polynomial.aeval (-w) Q11‖
          = ‖(β₁₁ : ℂ) * (w ^ 2)⁻¹ + (Polynomial.aeval (-w) P11 / Polynomial.aeval (-w) Q11 - (β₁₁ : ℂ) * (w ^ 2)⁻¹)‖ := by ring_nf
        _ ≤ ‖(β₁₁ : ℂ) * (w ^ 2)⁻¹‖ + ‖Polynomial.aeval (-w) P11 / Polynomial.aeval (-w) Q11 - (β₁₁ : ℂ) * (w ^ 2)⁻¹‖ := norm_add_le _ _
        _ = |β₁₁| * ‖w‖ ^ (-2 : ℝ) + _ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_inv, norm_pow,
              ← Real.rpow_natCast ‖w‖ 2, show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num,
              ← Real.rpow_neg (norm_nonneg w)]
    have hpow : ‖w‖ ^ (-3 : ℝ) ≤ ‖w‖ ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hw1 (by norm_num)
    calc ‖Polynomial.aeval (-w) P11 / Polynomial.aeval (-w) Q11‖
        ≤ |β₁₁| * ‖w‖ ^ (-2 : ℝ) + C * ‖w‖ ^ (-3 : ℝ) := htri.trans (add_le_add (le_refl _) hb)
      _ ≤ |β₁₁| * ‖w‖ ^ (-2 : ℝ) + C * ‖w‖ ^ (-2 : ℝ) := by gcongr
      _ = (|β₁₁| + C) * ‖w‖ ^ (-2 : ℝ) := by ring
  obtain ⟨M00, hM00_nn, hsym00⟩ := symBd_neg_rat P00 Q00 hR4 hQ00 (by positivity) hr00_bd
  obtain ⟨M01, hM01_nn, hsym01⟩ := symBd_neg_rat P01 Q01 hR4 hQ01 hC0 (fun w hw => (hasym w hw).2.1)
  obtain ⟨M11, hM11_nn, hsym11⟩ := symBd_neg_rat P11 Q11 hR4 hQ11 (by positivity) hr11_bd
  obtain ⟨MA, -, hAP⟩ := symBd_negAmpP hx0_2
  obtain ⟨MB, -, hAM⟩ := symBd_negAmpM hx0_2
  obtain ⟨MA', -, hAP'⟩ := symBd_negAmpP' hx0_2
  obtain ⟨MB', -, hAM'⟩ := symBd_negAmpM' hx0_2
  let aP : ℝ → ℂ := fun x => negAmpP (x : ℂ)
  let aM : ℝ → ℂ := fun x => negAmpM (x : ℂ)
  let aP' : ℝ → ℂ := fun x => negAmpP' (x : ℂ)
  let aM' : ℝ → ℂ := fun x => negAmpM' (x : ℂ)
  have sym_b0 := SymBd.add hx0_pos
    ((SymBd.const_mul (2 : ℂ) (SymBd.mul hx0_pos hsym00 (SymBd.mul hx0_pos hAP hAM))).mono_order hx0_1
      (by norm_num : (3 / 2 : ℝ) ≤ 1 + (1 / 4 + 1 / 4)))
    (SymBd.add hx0_pos
      ((SymBd.mul hx0_pos hsym01 (SymBd.add hx0_pos (SymBd.mul hx0_pos hAP hAM') (SymBd.mul hx0_pos hAM hAP'))).mono_order
        hx0_1 (by norm_num : (3 / 2 : ℝ) ≤ 2 + (1 / 4 + -(1 / 4))))
      ((SymBd.const_mul (2 : ℂ) (SymBd.mul hx0_pos hsym11 (SymBd.mul hx0_pos hAP' hAM'))).mono_order hx0_1
        (by norm_num : (3 / 2 : ℝ) ≤ 2 + (-(1 / 4) + -(1 / 4)))))
  have sym_bPos := SymBd.add hx0_pos
    ((SymBd.mul hx0_pos hsym00 (SymBd.mul hx0_pos hAM hAM)).mono_order hx0_1
      (by norm_num : (3 / 2 : ℝ) ≤ 1 + (1 / 4 + 1 / 4)))
    (SymBd.add hx0_pos
      ((SymBd.mul hx0_pos hsym01 (SymBd.mul hx0_pos hAM hAM')).mono_order hx0_1
        (by norm_num : (3 / 2 : ℝ) ≤ 2 + (1 / 4 + -(1 / 4))))
      ((SymBd.mul hx0_pos hsym11 (SymBd.mul hx0_pos hAM' hAM')).mono_order hx0_1
        (by norm_num : (3 / 2 : ℝ) ≤ 2 + (-(1 / 4) + -(1 / 4)))))
  have sym_bNeg := SymBd.add hx0_pos
    ((SymBd.mul hx0_pos hsym00 (SymBd.mul hx0_pos hAP hAP)).mono_order hx0_1
      (by norm_num : (3 / 2 : ℝ) ≤ 1 + (1 / 4 + 1 / 4)))
    (SymBd.add hx0_pos
      ((SymBd.mul hx0_pos hsym01 (SymBd.mul hx0_pos hAP hAP')).mono_order hx0_1
        (by norm_num : (3 / 2 : ℝ) ≤ 2 + (1 / 4 + -(1 / 4))))
      ((SymBd.mul hx0_pos hsym11 (SymBd.mul hx0_pos hAP' hAP')).mono_order hx0_1
        (by norm_num : (3 / 2 : ℝ) ≤ 2 + (-(1 / 4) + -(1 / 4)))))
  have n0 := SymBd.nonneg' hx0_pos sym_b0
  have n1 := SymBd.nonneg' hx0_pos sym_bPos
  have n2 := SymBd.nonneg' hx0_pos sym_bNeg
  let b₀ : ℝ → ℂ := fun x =>
    2 * (r00 x * (aP x * aM x)) + (r01 x * (aP x * aM' x + aM x * aP' x) + 2 * (r11 x * (aP' x * aM' x)))
  let bPos : ℝ → ℂ := fun x =>
    r00 x * (aM x * aM x) + (r01 x * (aM x * aM' x) + r11 x * (aM' x * aM' x))
  let bNeg : ℝ → ℂ := fun x =>
    r00 x * (aP x * aP x) + (r01 x * (aP x * aP' x) + r11 x * (aP' x * aP' x))
  let symM0 : ℝ := ‖(2 : ℂ)‖ * (2 ^ 12 * M00 * (2 ^ 12 * MA * MB)) +
    (2 ^ 12 * M01 * (2 ^ 12 * MA * MB' + 2 ^ 12 * MB * MA') + ‖(2 : ℂ)‖ * (2 ^ 12 * M11 * (2 ^ 12 * MA' * MB')))
  let symM1 : ℝ := 2 ^ 12 * M00 * (2 ^ 12 * MB * MB) +
    (2 ^ 12 * M01 * (2 ^ 12 * MB * MB') + 2 ^ 12 * M11 * (2 ^ 12 * MB' * MB'))
  let symM2 : ℝ := 2 ^ 12 * M00 * (2 ^ 12 * MA * MA) +
    (2 ^ 12 * M01 * (2 ^ 12 * MA * MA') + 2 ^ 12 * M11 * (2 ^ 12 * MA' * MA'))
  have hb0_bd : SymBd 12 x₀ (3 / 2) symM0 b₀ := sym_b0
  have hbPos_bd : SymBd 12 x₀ (3 / 2) symM1 bPos := sym_bPos
  have hbNeg_bd : SymBd 12 x₀ (3 / 2) symM2 bNeg := sym_bNeg
  obtain ⟨hschw_cd, S, hS0, hschw_bd⟩ := genRational_cutoff_schwartz hIn hx0_1 χ
  let M : ℝ := symM0 + symM1 + symM2
  refine ⟨x₀, S, M, hx0_2, hS0, by positivity,
    { F := X
      continuous := (contDiff_re_of_differentiable hIn.1).1.continuous
      schwartz_cd := hschw_cd
      schwartz_bd := hschw_bd
      b₀ := b₀
      bPos := bPos
      bNeg := bNeg
      sym_cd := ⟨hb0_bd.cd, hbPos_bd.cd, hbNeg_bd.cd⟩
      sym_bd := fun k hk x hx => ⟨(hb0_bd.bd k hk x hx).trans (by dsimp [M]; linarith),
        (hbPos_bd.bd k hk x hx).trans (by dsimp [M]; linarith),
        (hbNeg_bd.bd k hk x hx).trans (by dsimp [M]; linarith)⟩
      tail_eq := fun x hx => ?_ }, rfl⟩
  have hx_pos : 0 < x := by linarith
  have hgt : R_star < ‖((-x : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hx_pos]; dsimp [x₀] at hx; linarith
  have hrep_x := hrep ((-x : ℝ) : ℂ) hgt
  have hreal_F : (X (-x) : ℂ) = F ((-x : ℝ) : ℂ) :=
    Complex.ext rfl (hIn.2.2.2 (-x)).symm
  have hneg_cast : ((-x : ℝ) : ℂ) = -(x : ℂ) := by push_cast; ring
  have hE : cexp (Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ)) : ℂ)) *
      cexp (-(Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ)) : ℂ))) = 1 :=
    exp_mul_exp_neg _
  have hEp : cexp (Complex.I * (((4 / 3 * x ^ (3 / 2 : ℝ) : ℝ)) : ℂ)) =
      cexp (Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ)) : ℂ)) *
      cexp (Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ)) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hEn : cexp (Complex.I * (((-1 : ℝ) * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)) =
      cexp (-(Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ)) : ℂ))) *
      cexp (-(Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ)) : ℂ))) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hreal_F, hrep_x, airyAiC_ofReal, deriv_airyAiC_ofReal, ai_real_split hx_pos.le, aip_real_split hx_pos.le]
  rw [hneg_cast, hEp, hEn]
  dsimp only [r00, r01, r11, b₀, bPos, bNeg, aP, aM, aP', aM']
  linear_combination (2 * r00 x * aP x * aM x + r01 x * (aP x * aM' x + aM x * aP' x) +
    2 * r11 x * aP' x * aM' x) * hE

/-- `GT.1` bounds for `liftW X δ₀ m` (`X = Re F`), uniform in `δ₀ ∈ [0, 2]`, for every `m ≥ 3`
and every `F` satisfying `HasGenRationalAiryCoeffs F β₀₀ β₁₁`. -/
theorem gt1Bounds_of_genRational {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ} (hF : HasGenRationalAiryCoeffs F β₀₀ β₁₁)
    {m : ℕ} (hm : 3 ≤ m) :
    ∃ A > 0, ∀ {δ₀ : ℝ}, δ₀ ∈ Icc (0 : ℝ) 2 →
      Gt1Bounds A (liftW (fun u => (F (u : ℂ)).re) δ₀ m) := by
  obtain ⟨x₀, S, M, hx2, hS0, hM0, seed, hseed⟩ := genRational_airytailSymbolSeed hF AiryCutoff.standard
  obtain ⟨C, hC, hlift⟩ := gt1Bounds_liftW_of_seed m hm (by linarith : 1 ≤ x₀) AiryCutoff.standard
  refine ⟨C * (S + M) + 1, by positivity, fun hδ => ?_⟩
  have h := (hlift seed hδ).mono (B := C * (S + M) + 1) (by linarith)
  rwa [hseed] at h

/-! ### Section 3: `ImagAxisBounds`, `HasU2`, and `ConvTailData` -/

private lemma ceCs_lt_two : ceCs < 2 := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have h3 : Real.pi ^ 2 / 3 < 2 ^ 3 := by nlinarith [Real.pi_pos]
  calc ceCs = (Real.pi ^ 2 / 3) ^ (1 / 3 : ℝ) := rfl
    _ < (2 ^ 3 : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_lt_rpow (by positivity) h3 (by norm_num)
    _ = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

private lemma liftW_zero_eq (X : ℝ → ℝ) (v : ℝ) :
    liftW X 0 3 v = airyTwistedLaplaceC X (((ceCs * v : ℝ) : ℂ) * Complex.I) := by
  unfold liftW liftSymbol liftMultiplier
  have h0 : (((ceCs : ℝ) * 0 / (3 : ℕ) : ℝ) : ℂ) * ((v : ℂ) * Complex.I) = 0 := by simp
  rw [h0, bsplineE1_zero, one_pow, one_mul]
  congr 1; push_cast; ring

/-- Any `X : ℝ → ℝ` whose unsmoothed symbol `liftW X 0 3` obeys `Gt1Bounds AW` satisfies `(e27)` `ImagAxisBounds`. -/
theorem imagAxisBounds_of_gt1 {X : ℝ → ℝ} {AW : ℝ} (hG : Gt1Bounds AW (liftW X 0 3)) :
    ImagAxisBounds (airyTwistedLaplaceC X) := by
  obtain ⟨W1, W2, W3, hd, ha, hb, hW0, hH⟩ := hG
  have hAW0 : 0 ≤ AW := (norm_nonneg _).trans hW0
  obtain ⟨hb_hi, _, _⟩ := gt1_hyp hAW0 ha hb hW0 hH
  have hcs := ceCs_pos
  have hcs2 := ceCs_lt_two
  let g1 : ℝ → ℂ := fun ω => ((ceCs⁻¹ : ℝ) : ℂ) * W1 (ω / ceCs)
  let g2 : ℝ → ℂ := fun ω => ((ceCs⁻¹ ^ 2 : ℝ) : ℂ) * W2 (ω / ceCs)
  have hlin : ∀ ω : ℝ, HasDerivAt (fun t : ℝ => t / ceCs) ceCs⁻¹ ω := fun ω => by
    simpa using (hasDerivAt_id ω).div_const ceCs
  have hT_eq : (fun ω : ℝ => airyTwistedLaplaceC X ((ω : ℂ) * Complex.I)) = fun ω => liftW X 0 3 (ω / ceCs) := by
    ext ω; rw [liftW_zero_eq]; congr 1; push_cast; field_simp [hcs.ne']
  have h1 : ∀ ω : ℝ, 1 < |ω| → HasDerivAt (fun ω : ℝ => airyTwistedLaplaceC X ((ω : ℂ) * Complex.I)) (g1 ω) ω :=
    fun ω hω => by
      have hs0 : ω / ceCs ≠ 0 := div_ne_zero (abs_pos.mp (by linarith)) hcs.ne'
      rw [hT_eq]
      have hhd := (hd (ω / ceCs) hs0).1.scomp ω (hlin ω)
      exact hhd.congr_deriv rfl
  have h2 : ∀ ω : ℝ, 1 < |ω| → HasDerivAt g1 (g2 ω) ω := fun ω hω => by
    have hs0 : ω / ceCs ≠ 0 := div_ne_zero (abs_pos.mp (by linarith)) hcs.ne'
    have hcomp := (hd (ω / ceCs) hs0).2.1.scomp ω (hlin ω)
    exact (hcomp.const_mul ((ceCs⁻¹ : ℝ) : ℂ)).congr_deriv (by dsimp [g2]; push_cast; ring)
  let A' : ℝ := max 1 (2 * AW)
  have hA'0 : 0 ≤ A' := by positivity
  let C : ℝ := A' * max (ceCs ^ (5 / 2 : ℝ)) (max (ceCs⁻¹ * ceCs ^ (7 / 2 : ℝ)) (ceCs⁻¹ ^ 2 * ceCs ^ (9 / 2 : ℝ))) + 1
  refine ⟨g1, g2, h1, h2, C, by positivity, fun ω hω => ?_⟩
  have hω_pos : 0 < |ω| := by linarith
  have hs_abs : |ω / ceCs| = |ω| / ceCs := by rw [abs_div, abs_of_pos hcs]
  have hs_half : 1 / 2 ≤ |ω / ceCs| := by rw [hs_abs, le_div_iff₀ hcs]; linarith
  obtain ⟨b0, b1, b2, _⟩ := hb_hi (ω / ceCs) hs_half
  rw [hs_abs] at b0 b1 b2
  have hrpow : ∀ p : ℝ, (|ω| / ceCs) ^ (-p) = ceCs ^ p * |ω| ^ (-p) := fun p => by
    rw [Real.rpow_neg (by positivity), Real.div_rpow hω_pos.le hcs.le, inv_div, div_eq_mul_inv,
      Real.rpow_neg hω_pos.le, mul_comm]
  rw [hrpow (5 / 2)] at b0; rw [hrpow (7 / 2)] at b1; rw [hrpow (9 / 2)] at b2
  have heq : airyTwistedLaplaceC X ((ω : ℂ) * Complex.I) = liftW X 0 3 (ω / ceCs) := congrFun hT_eq ω
  have hP5 : 0 ≤ |ω| ^ (-(5 / 2 : ℝ)) := by positivity
  have hP7 : 0 ≤ |ω| ^ (-(7 / 2 : ℝ)) := by positivity
  have hP9 : 0 ≤ |ω| ^ (-(9 / 2 : ℝ)) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]; refine b0.trans ?_
    have hm1 : ceCs ^ (5 / 2 : ℝ) ≤ max (ceCs ^ (5 / 2 : ℝ)) (max (ceCs⁻¹ * ceCs ^ (7 / 2 : ℝ)) (ceCs⁻¹ ^ 2 * ceCs ^ (9 / 2 : ℝ))) := le_max_left _ _
    calc A' * (ceCs ^ (5 / 2 : ℝ) * |ω| ^ (-(5 / 2 : ℝ))) = A' * ceCs ^ (5 / 2 : ℝ) * |ω| ^ (-(5 / 2 : ℝ)) := by ring
      _ ≤ C * |ω| ^ (-(5 / 2 : ℝ)) := mul_le_mul_of_nonneg_right (by dsimp [C]; nlinarith) hP5
  · dsimp [g1]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcs)]
    have hm2 : ceCs⁻¹ * ceCs ^ (7 / 2 : ℝ) ≤ max (ceCs ^ (5 / 2 : ℝ)) (max (ceCs⁻¹ * ceCs ^ (7 / 2 : ℝ)) (ceCs⁻¹ ^ 2 * ceCs ^ (9 / 2 : ℝ))) :=
      (le_max_left _ _).trans (le_max_right _ _)
    calc ceCs⁻¹ * ‖W1 (ω / ceCs)‖ ≤ ceCs⁻¹ * (A' * (ceCs ^ (7 / 2 : ℝ) * |ω| ^ (-(7 / 2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left b1 (inv_nonneg.mpr hcs.le)
      _ = A' * (ceCs⁻¹ * ceCs ^ (7 / 2 : ℝ)) * |ω| ^ (-(7 / 2 : ℝ)) := by ring
      _ ≤ C * |ω| ^ (-(7 / 2 : ℝ)) := mul_le_mul_of_nonneg_right (by dsimp [C]; nlinarith) hP7
  · dsimp [g2]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hm3 : ceCs⁻¹ ^ 2 * ceCs ^ (9 / 2 : ℝ) ≤ max (ceCs ^ (5 / 2 : ℝ)) (max (ceCs⁻¹ * ceCs ^ (7 / 2 : ℝ)) (ceCs⁻¹ ^ 2 * ceCs ^ (9 / 2 : ℝ))) :=
      (le_max_right _ _).trans (le_max_right _ _)
    calc ceCs⁻¹ ^ 2 * ‖W2 (ω / ceCs)‖ ≤ ceCs⁻¹ ^ 2 * (A' * (ceCs ^ (9 / 2 : ℝ) * |ω| ^ (-(9 / 2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left b2 (sq_nonneg _)
      _ = A' * (ceCs⁻¹ ^ 2 * ceCs ^ (9 / 2 : ℝ)) * |ω| ^ (-(9 / 2 : ℝ)) := by ring
      _ ≤ C * |ω| ^ (-(9 / 2 : ℝ)) := mul_le_mul_of_nonneg_right (by dsimp [C]; nlinarith) hP9

/-- `(e27)` `ImagAxisBounds` for any `F` satisfying `HasGenRationalAiryCoeffs F β₀₀ β₁₁`. -/
theorem imagAxisBounds_of_genRational {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ} (hF : HasGenRationalAiryCoeffs F β₀₀ β₁₁) :
    ImagAxisBounds (airyTwistedLaplaceC (fun u => (F (u : ℂ)).re)) := by
  obtain ⟨A, -, hG⟩ := gt1Bounds_of_genRational hF (by norm_num : 3 ≤ 3)
  exact imagAxisBounds_of_gt1 (hG ⟨le_rfl, by norm_num⟩)

/-- `HasU2` for `X = Re F` when `F ∈ InAiryClass` and `liftW X 0 3` has `Gt1Bounds` (Phragmén–Lindelöf). -/
theorem hasU2_of_inAiryClass_gt1 {F : ℂ → ℂ} (hF : InAiryClass F) {AW : ℝ}
    (hG : Gt1Bounds AW (liftW (fun u => (F (u : ℂ)).re) 0 3)) :
    HasU2 (fun u => (F (u : ℂ)).re) := by
  let X : ℝ → ℝ := fun u => (F (u : ℂ)).re
  have hX_cont : Continuous X := (contDiff_re_of_differentiable hF.1).1.continuous
  have hX_int : Integrable X := by
    have hre := Complex.reCLM.integrable_comp hF.2.1
    simpa [X, Complex.reCLM_apply] using hre
  obtain ⟨C₀, ν₀, hC₀, hbd⟩ := hF.2.2.1
  obtain ⟨B₀, hB₀, hBku⟩ := rpow_mul_exp_neg_rpow32_bounded ν₀ (r := 2 / 3) (by norm_num)
  have hX_tail : ∀ u : ℝ, 0 ≤ u → |X u| ≤ (C₀ * B₀ + 1) * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := fun u hu => by
    have hF_bd := (Complex.abs_re_le_norm (F (u : ℂ))).trans (hbd (u : ℂ))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu, airyEnv_ofReal_nonneg hu] at hF_bd
    have hexp : Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) =
        Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hexp] at hF_bd
    calc |X u| ≤ C₀ * ((1 + u) ^ ν₀ * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ))) *
          Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by linarith
      _ ≤ (C₀ * B₀) * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by
          gcongr; exact hBku u hu
      _ ≤ (C₀ * B₀ + 1) * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by
          gcongr; linarith
  have hreg := airyTwistedLaplaceC_regularity hX_cont hX_int (by positivity) hX_tail
  refine ⟨hreg.1, hreg.2.2.1, ?_⟩
  obtain ⟨W1, W2, W3, hd, ha, hb, hW0, hH⟩ := hG
  have hAW0 : 0 ≤ AW := (norm_nonneg _).trans hW0
  have hcs := ceCs_pos
  have hcs1 : 1 < ceCs := ceCs_one_lt
  have hF_real : ∀ u : ℝ, F (u : ℂ) = (X u : ℂ) := fun u => by
    apply Complex.ext <;> simp [X, hF.2.2.2 u]
  let D : ℝ := max (2 * AW * (1 + ceCs) ^ (5 / 2 : ℝ)) (AW * ceCs ^ (5 / 2 : ℝ) * 2 ^ (5 / 2 : ℝ)) + 1
  have hD_pos : 0 < D := by positivity
  have hbd_real : ∀ ξ : ℝ, ‖airyFtilde F (ξ : ℂ)‖ * (1 + |ξ|) ^ (5 / 2 : ℝ) ≤ D := fun ξ => by
    have hEq : airyFtilde F (ξ : ℂ) = liftW X 0 3 (-ξ / ceCs) := by
      have h1 : (ξ : ℂ) = Complex.I * (-((ξ : ℂ) * Complex.I)) := by ring_nf; simp
      rw [h1, ← airyTwistedLaplaceC_eq_airyFtilde X hF_real, liftW_zero_eq]
      congr 1; push_cast; field_simp [hcs.ne']
    rw [hEq]
    have hsn : |-ξ / ceCs| = |ξ| / ceCs := by rw [abs_div, abs_neg, abs_of_pos hcs]
    by_cases hle : |ξ| ≤ ceCs
    · have hs1 : |-ξ / ceCs| ≤ 1 := by rw [hsn, div_le_one hcs]; exact hle
      have hW_le : ‖liftW X 0 3 (-ξ / ceCs)‖ ≤ 2 * AW := by
        rcases eq_or_lt_of_le (abs_nonneg (-ξ / ceCs)) with hs0 | hs0
        · have hz : -ξ / ceCs = 0 := abs_eq_zero.mp hs0.symm
          rw [hz]; linarith
        · have hdiff := hH (-ξ / ceCs) hs0 hs1
          have hr1 : |-ξ / ceCs| ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one (abs_nonneg _) hs1 (by norm_num)
          have hAWr : AW * |-ξ / ceCs| ^ (1 / 2 : ℝ) ≤ AW := mul_le_of_le_one_right hAW0 hr1
          have htri : ‖liftW X 0 3 (-ξ / ceCs)‖ ≤ ‖liftW X 0 3 0‖ + ‖liftW X 0 3 (-ξ / ceCs) - liftW X 0 3 0‖ := by
            simpa [norm_sub_rev] using norm_le_norm_add_norm_sub (liftW X 0 3 0) (liftW X 0 3 (-ξ / ceCs))
          linarith
      have h1xi : (1 + |ξ|) ^ (5 / 2 : ℝ) ≤ (1 + ceCs) ^ (5 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      calc ‖liftW X 0 3 (-ξ / ceCs)‖ * (1 + |ξ|) ^ (5 / 2 : ℝ)
          ≤ (2 * AW) * (1 + ceCs) ^ (5 / 2 : ℝ) := mul_le_mul hW_le h1xi (by positivity) (by positivity)
        _ ≤ D := by dsimp [D]; linarith [le_max_left (2 * AW * (1 + ceCs) ^ (5 / 2 : ℝ)) (AW * ceCs ^ (5 / 2 : ℝ) * 2 ^ (5 / 2 : ℝ))]
    · push Not at hle
      have hs1 : 1 ≤ |-ξ / ceCs| := by rw [hsn, le_div_iff₀ hcs]; linarith
      have hxi1 : 1 ≤ |ξ| := (by linarith : 1 ≤ ceCs).trans hle.le
      have hW_le := (hb (-ξ / ceCs) hs1).1
      rw [hsn] at hW_le
      have h12 : 1 + |ξ| ≤ 2 * |ξ| := by linarith
      have h1pow : (1 + |ξ|) ^ (5 / 2 : ℝ) ≤ 2 ^ (5 / 2 : ℝ) * |ξ| ^ (5 / 2 : ℝ) := by
        rw [← Real.mul_rpow (by norm_num) (abs_nonneg ξ)]
        exact Real.rpow_le_rpow (by positivity) h12 (by norm_num)
      have hinv : (|ξ| / ceCs) ^ (-(5 / 2 : ℝ)) * |ξ| ^ (5 / 2 : ℝ) = ceCs ^ (5 / 2 : ℝ) := by
        rw [Real.div_rpow (abs_nonneg ξ) hcs.le, Real.rpow_neg (abs_nonneg ξ), Real.rpow_neg hcs.le]
        have hxi_ne : |ξ| ^ (5 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
        have hcs_ne : ceCs ^ (5 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hcs _).ne'
        field_simp
      calc ‖liftW X 0 3 (-ξ / ceCs)‖ * (1 + |ξ|) ^ (5 / 2 : ℝ)
          ≤ (AW * (|ξ| / ceCs) ^ (-(5 / 2 : ℝ))) * (2 ^ (5 / 2 : ℝ) * |ξ| ^ (5 / 2 : ℝ)) :=
            mul_le_mul hW_le h1pow (by positivity) (by positivity)
        _ = AW * ((|ξ| / ceCs) ^ (-(5 / 2 : ℝ)) * |ξ| ^ (5 / 2 : ℝ)) * 2 ^ (5 / 2 : ℝ) := by ring
        _ = AW * ceCs ^ (5 / 2 : ℝ) * 2 ^ (5 / 2 : ℝ) := by rw [hinv]
        _ ≤ D := by dsimp [D]; linarith [le_max_right (2 * AW * (1 + ceCs) ^ (5 / 2 : ℝ)) (AW * ceCs ^ (5 / 2 : ℝ) * 2 ^ (5 / 2 : ℝ))]
  let hG_cl := inAiryClass_to_airyClassG hF
  obtain ⟨A_p, M_p, hAp, hpoly⟩ := airyFtilde_poly hG_cl
  refine ⟨2 ^ (5 / 4 : ℝ) * D + 1, by positivity, fun w hw => ?_⟩
  let ζ : ℂ := Complex.I * ((ceCs : ℂ) * w)
  have hζ_im : 0 ≤ ζ.im := by simp [ζ, Complex.mul_re, mul_nonneg hcs.le hw]
  have hpl := pl_halfPlane_decay (m := 5 / 2) (by norm_num) hAp (airyFtilde_diffContOnCl hG_cl) hpoly hbd_real hζ_im
  have hnorm_le : ‖1 + w‖ ≤ 1 + ‖ζ‖ := by
    have h1 : ‖w‖ ≤ ‖ζ‖ := by
      simp only [ζ, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcs]
      exact le_mul_of_one_le_left (norm_nonneg w) hcs1.le
    calc ‖1 + w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_add_le _ _
      _ = 1 + ‖w‖ := by simp
      _ ≤ 1 + ‖ζ‖ := by linarith
  have h1w_pos : 0 < ‖1 + w‖ := by
    have hre : (1 : ℝ) ≤ (1 + w).re := by simp [hw]
    exact lt_of_lt_of_le one_pos (hre.trans (Complex.re_le_norm _))
  have hrpow_le : ‖1 + w‖ ^ (5 / 2 : ℝ) ≤ (1 + ‖ζ‖) ^ (5 / 2 : ℝ) :=
    Real.rpow_le_rpow h1w_pos.le hnorm_le (by norm_num)
  have h254 : (2 : ℝ) ^ ((5 / 2 : ℝ) / 2) = 2 ^ (5 / 4 : ℝ) := by norm_num
  rw [h254] at hpl
  rw [airyTwistedLaplaceC_eq_airyFtilde X hF_real]
  calc ‖airyFtilde F ζ‖
      ≤ (2 ^ (5 / 4 : ℝ) * D) / (1 + ‖ζ‖) ^ (5 / 2 : ℝ) := by
        rw [le_div_iff₀ (by positivity)]; exact hpl
    _ ≤ (2 ^ (5 / 4 : ℝ) * D) / ‖1 + w‖ ^ (5 / 2 : ℝ) := by gcongr
    _ = (2 ^ (5 / 4 : ℝ) * D) * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
        rw [Real.rpow_neg h1w_pos.le, div_eq_mul_inv]
    _ ≤ (2 ^ (5 / 4 : ℝ) * D + 1) * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by gcongr; linarith

/-- `HasU2` for `X = Re F` for every `F` satisfying `HasGenRationalAiryCoeffs F β₀₀ β₁₁`. -/
theorem hasU2_of_genRational {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ} (hF : HasGenRationalAiryCoeffs F β₀₀ β₁₁) :
    HasU2 (fun u => (F (u : ℂ)).re) := by
  obtain ⟨A, -, hG⟩ := gt1Bounds_of_genRational hF (by norm_num : 3 ≤ 3)
  exact hasU2_of_inAiryClass_gt1 hF.1 (hG ⟨le_rfl, by norm_num⟩)

/-- `ConvTailData` for `X = Re F` for every `F ∈ ℛ_Ai^gen`, `m ≥ 3`, `δ₀ ∈ [0, 2]`, `c ≥ 8`. -/
theorem convTailData_of_genRational {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ} (hF : HasGenRationalAiryCoeffs F β₀₀ β₁₁)
    {m : ℕ} (hm : 3 ≤ m) {δ₀ : ℝ} (hδ : δ₀ ∈ Icc (0 : ℝ) 2) {c : ℝ} (hc : 8 ≤ c) :
    ConvTailData (fun u => (F (u : ℂ)).re) δ₀ m c := by
  obtain ⟨A, -, hG⟩ := gt1Bounds_of_genRational hF hm
  exact convTailData_of_gt1 (hasU2_of_genRational hF) hδ.1 (hG hδ) hc

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.SignUncertainty.genRational_cutoff_schwartz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.SignUncertainty.genRational_cutoff_schwartz
/-- info: 'FormalResearch.SignUncertainty.genRational_airytailSymbolSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.SignUncertainty.genRational_airytailSymbolSeed
/-- info: 'FormalResearch.SignUncertainty.gt1Bounds_of_genRational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.SignUncertainty.gt1Bounds_of_genRational
/-- info: 'FormalResearch.SignUncertainty.imagAxisBounds_of_gt1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.SignUncertainty.imagAxisBounds_of_gt1
/-- info: 'FormalResearch.SignUncertainty.imagAxisBounds_of_genRational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.SignUncertainty.imagAxisBounds_of_genRational
/-- info: 'FormalResearch.SignUncertainty.hasU2_of_genRational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.SignUncertainty.hasU2_of_genRational
/-- info: 'FormalResearch.SignUncertainty.convTailData_of_genRational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.SignUncertainty.convTailData_of_genRational

end FormalResearch.SignUncertainty
