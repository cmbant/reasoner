module

public import FormalResearch.SignUncertainty.UctSeedEdgeV
public import FormalResearch.SignUncertainty.UctSeedEdgeE
public import FormalResearch.SignUncertainty.UctSeedEdgeZT

/-!
# `W^seed` edge trace: assembly of (M3) (F2a)

The edge trace `g(τ) = W^seed(iτ)` is `Y(τ)·v(aτ)` where `Y = T(a)⁻¹ Z_ε(iτ) e^{-h(iτ)} T(a(1-iτ))` is `C²` with
`|Y|,|Y'|,|Y''| ≤ C(1+|τ|)^{10}e^{-π|τ|}` (`Env2`, from `UctSeedEdgeE`, `UctSeedEdgeZT`) and `v(q) = T(iq)` is the Airy factor
of `UctSeedEdgeV`.  This file proves the Leibniz bookkeeping: `edge_prod_fields`.
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtOuter

lemma poly_exp_le_n (n : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 0 ≤ x → (1 + x) ^ n * Real.exp (-(π * x)) ≤ M := by
  refine ⟨2 ^ n * (1 + (Nat.factorial n : ℝ) / π ^ n), by positivity, fun x hx => ?_⟩
  have hπ := Real.pi_pos
  have h1 : (π * x) ^ n / (Nat.factorial n : ℝ) ≤ Real.exp (π * x) :=
    Real.pow_div_factorial_le_exp _ (by positivity) n
  have hE : 0 < Real.exp (π * x) := Real.exp_pos _
  have hf : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
  have h2 : x ^ n * Real.exp (-(π * x)) ≤ (Nat.factorial n : ℝ) / π ^ n := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hE (by positivity)]
    rw [div_le_iff₀ hf] at h1
    calc x ^ n * π ^ n = (π * x) ^ n := by ring
      _ ≤ Real.exp (π * x) * (Nat.factorial n : ℝ) := h1
      _ = (Nat.factorial n : ℝ) * Real.exp (π * x) := by ring
  have h3 : Real.exp (-(π * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h4 : (1 + x) ^ n ≤ 2 ^ n * (1 + x ^ n) := by
    have hxn : 0 ≤ x ^ n := by positivity
    rcases le_or_gt x 1 with h | h
    · have : (1 + x) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) n]
    · have : (1 + x) ^ n ≤ (2 * x) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      rw [mul_pow] at this
      nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) n]
  have h5 : 0 ≤ Real.exp (-(π * x)) := (Real.exp_pos _).le
  calc (1 + x) ^ n * Real.exp (-(π * x)) ≤ 2 ^ n * (1 + x ^ n) * Real.exp (-(π * x)) :=
        mul_le_mul_of_nonneg_right h4 h5
    _ = 2 ^ n * (Real.exp (-(π * x)) + x ^ n * Real.exp (-(π * x))) := by ring
    _ ≤ 2 ^ n * (1 + (Nat.factorial n : ℝ) / π ^ n) := by gcongr

/-- Leibniz formulas for `Y · V` at points of an open set `S` where `V` is `C²` and `Y` is globally `C²`. -/
lemma prod_deriv {Y V : ℝ → ℂ} {S : Set ℝ} (hS : IsOpen S) (hY : ContDiff ℝ 2 Y) (hV : ContDiffOn ℝ 2 V S)
    {τ : ℝ} (hτ : τ ∈ S) :
    deriv (fun t => Y t * V t) τ = deriv Y τ * V τ + Y τ * deriv V τ ∧
    deriv (deriv (fun t => Y t * V t)) τ =
      deriv (deriv Y) τ * V τ + 2 * (deriv Y τ * deriv V τ) + Y τ * deriv (deriv V) τ := by
  have hYd : Differentiable ℝ Y := hY.differentiable (by norm_num)
  have hY2 : ContDiff ℝ ((1 : ℕ) + 1) Y := by simpa [one_add_one_eq_two] using hY
  have hYd1 : Differentiable ℝ (deriv Y) :=
    (((contDiff_succ_iff_deriv (𝕜 := ℝ)).mp hY2).2.2).differentiable (by norm_num)
  have hVd : ∀ t ∈ S, DifferentiableAt ℝ V t := fun t ht =>
    (hV.differentiableOn (by norm_num) t ht).differentiableAt (hS.mem_nhds ht)
  have hV1 : ContDiffOn ℝ 1 (deriv V) S := hV.deriv_of_isOpen hS (by norm_num)
  have hVd1 : ∀ t ∈ S, DifferentiableAt ℝ (deriv V) t := fun t ht =>
    (hV1.differentiableOn (by norm_num) t ht).differentiableAt (hS.mem_nhds ht)
  have hform : ∀ t ∈ S, deriv (fun t => Y t * V t) t = deriv Y t * V t + Y t * deriv V t := fun t ht =>
    deriv_mul (hYd t) (hVd t ht)
  have h1 := hform τ hτ
  refine ⟨h1, ?_⟩
  have hev : deriv (fun t => Y t * V t) =ᶠ[𝓝 τ] fun t => deriv Y t * V t + Y t * deriv V t := by
    filter_upwards [hS.mem_nhds hτ] with t ht using hform t ht
  rw [hev.deriv_eq]
  have e2 : deriv (fun t => deriv Y t * V t) τ = deriv (deriv Y) τ * V τ + deriv Y τ * deriv V τ :=
    (HasDerivAt.mul (hYd1 τ).hasDerivAt (hVd τ hτ).hasDerivAt).deriv
  have e3 : deriv (fun t => Y t * deriv V t) τ = deriv Y τ * deriv V τ + Y τ * deriv (deriv V) τ :=
    (HasDerivAt.mul (hYd τ).hasDerivAt (hVd1 τ hτ).hasDerivAt).deriv
  have e : deriv (fun t => deriv Y t * V t + Y t * deriv V t) τ =
      deriv (fun t => deriv Y t * V t) τ + deriv (fun t => Y t * deriv V t) τ :=
    (HasDerivAt.add (((hYd1 τ).mul (hVd τ hτ)).hasDerivAt) (((hYd τ).mul (hVd1 τ hτ)).hasDerivAt)).deriv
  rw [e, e2, e3]
  ring


lemma deriv_V (δ a : ℝ) (τ : ℝ) : deriv (fun t : ℝ => seedV δ (a * t)) τ = a • deriv (seedV δ) (a * τ) :=
  deriv_comp_mul_left a (seedV δ) τ

lemma deriv_deriv_V (δ a : ℝ) (τ : ℝ) :
    deriv (deriv (fun t : ℝ => seedV δ (a * t))) τ = a • (a • deriv (deriv (seedV δ)) (a * τ)) := by
  have : deriv (fun t : ℝ => seedV δ (a * t)) = fun x => a • deriv (seedV δ) (a * x) := funext (deriv_V δ a)
  rw [this]
  have h := deriv_const_smul_field (𝕜 := ℝ) (x := τ) a (fun x => deriv (seedV δ) (a * x))
  have h' : deriv (fun x => a • deriv (seedV δ) (a * x)) τ = a • deriv (fun x => deriv (seedV δ) (a * x)) τ := h
  rw [h', deriv_comp_mul_left a (deriv (seedV δ)) τ]

lemma rpow_half_le_of_le_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : t ≤ t ^ (1 / 2 : ℝ) := by
  rcases h0.eq_or_lt with rfl | hs
  · simp
  · have : t ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) = t := by rw [← Real.rpow_add hs]; norm_num
    have h3 : t ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one h0 h1 (by norm_num)
    nlinarith [Real.rpow_nonneg h0 (1 / 2 : ℝ)]

lemma one_le_rpow_neg_half {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) : 1 ≤ t ^ ((1 / 2 : ℝ) - 1) := by
  have : (1 / 2 : ℝ) - 1 = -(1 / 2) := by norm_num
  rw [this, Real.rpow_neg h0.le]
  exact one_le_inv_iff₀.mpr ⟨Real.rpow_pos_of_pos h0 _, Real.rpow_le_one h0.le h1 (by norm_num)⟩

lemma one_le_rpow_neg_three_half {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) : 1 ≤ t ^ ((1 / 2 : ℝ) - 2) := by
  have : (1 / 2 : ℝ) - 2 = -(3 / 2) := by norm_num
  rw [this, Real.rpow_neg h0.le]
  exact one_le_inv_iff₀.mpr ⟨Real.rpow_pos_of_pos h0 _, Real.rpow_le_one h0.le h1 (by norm_num)⟩

lemma rpow_neg_half_le_neg_three_half {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) :
    t ^ ((1 / 2 : ℝ) - 1) ≤ t ^ ((1 / 2 : ℝ) - 2) :=
  Real.rpow_le_rpow_of_exponent_ge h0 h1 (by norm_num)


theorem edge_prod_c2 {Y : ℝ → ℂ} {P : ℝ → ℝ} (hY : Env2 Y P) {δ a : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ 2 (fun t : ℝ => Y t * seedV δ (a * t)) {τ : ℝ | τ ≠ 0} := by
  have hVc : ContDiffOn ℝ 2 (fun t : ℝ => seedV δ (a * t)) {τ : ℝ | τ ≠ 0} :=
    (seedV_contDiffOn δ 2).comp (contDiff_const.mul contDiff_id).contDiffOn
      (fun τ hτ => mul_ne_zero ha.ne' hτ)
  exact hY.1.contDiffOn.mul hVc

/-- Derivative bounds of `V(τ) = v(aτ)` on `0 < |τ| ≤ 1`. -/
lemma V_deriv_bounds {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {a : ℝ} (ha : 0 < a) :
    ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ τ : ℝ, τ ≠ 0 → |τ| ≤ 1 →
      ‖deriv (seedV δ) (a * τ)‖ ≤ Cu * |τ| ^ ((1 / 2 : ℝ) - 1) ∧
        ‖deriv (deriv (seedV δ)) (a * τ)‖ ≤ Cu * |τ| ^ ((1 / 2 : ℝ) - 2) := by
  obtain ⟨Cn, hCn0, hCn⟩ := seedV_near hδ0 hδ1
  have hq0 : 0 < min 2 (a / 2) := lt_min (by norm_num) (by positivity)
  obtain ⟨Cf, hCf0, hCf⟩ := seedV_far δ hq0
  refine ⟨max (Cn * a ^ ((1 / 2 : ℝ) - 1)) (max (Cn * a ^ ((1 / 2 : ℝ) - 2)) Cf), by positivity, fun τ hτ hτ1 => ?_⟩
  have hy : 0 < |τ| := abs_pos.mpr hτ
  have hmul : |a * τ| = a * |τ| := by rw [abs_mul, abs_of_pos ha]
  have h1 := one_le_rpow_neg_half hy hτ1
  have h2 := one_le_rpow_neg_three_half hy hτ1
  have hne : a * τ ≠ 0 := mul_ne_zero ha.ne' hτ
  have c1 : 0 ≤ Cn * a ^ ((1 / 2 : ℝ) - 1) := by positivity
  have c2 : 0 ≤ Cn * a ^ ((1 / 2 : ℝ) - 2) := by positivity
  rcases le_or_gt |a * τ| 2 with hq | hq
  · obtain ⟨-, n1, n2⟩ := hCn (a * τ) hne hq
    rw [hmul, Real.mul_rpow ha.le hy.le] at n1 n2
    constructor
    · calc _ ≤ Cn * (a ^ ((1 / 2 : ℝ) - 1) * |τ| ^ ((1 / 2 : ℝ) - 1)) := n1
        _ = (Cn * a ^ ((1 / 2 : ℝ) - 1)) * |τ| ^ ((1 / 2 : ℝ) - 1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · calc _ ≤ Cn * (a ^ ((1 / 2 : ℝ) - 2) * |τ| ^ ((1 / 2 : ℝ) - 2)) := n2
        _ = (Cn * a ^ ((1 / 2 : ℝ) - 2)) * |τ| ^ ((1 / 2 : ℝ) - 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) (by positivity)
  · have hqq : min 2 (a / 2) ≤ |a * τ| := (min_le_left _ _).trans hq.le
    obtain ⟨-, f1, f2⟩ := hCf (a * τ) hqq
    have hCf' : Cf ≤ max (Cn * a ^ ((1 / 2 : ℝ) - 1)) (max (Cn * a ^ ((1 / 2 : ℝ) - 2)) Cf) :=
      (le_max_right _ _).trans (le_max_right _ _)
    constructor
    · calc _ ≤ Cf := f1
        _ = Cf * 1 := (mul_one _).symm
        _ ≤ Cf * |τ| ^ ((1 / 2 : ℝ) - 1) := mul_le_mul_of_nonneg_left h1 hCf0
        _ ≤ _ := mul_le_mul_of_nonneg_right hCf' (by positivity)
    · calc _ ≤ Cf := f2
        _ = Cf * 1 := (mul_one _).symm
        _ ≤ Cf * |τ| ^ ((1 / 2 : ℝ) - 2) := mul_le_mul_of_nonneg_left h2 hCf0
        _ ≤ _ := mul_le_mul_of_nonneg_right hCf' (by positivity)


lemma env2_near_const {Y : ℝ → ℂ} {CY : ℝ}
    (hY : Env2 Y (fun τ => CY * ((1 + |τ|) ^ 10 * Real.exp (-(π * |τ|))))) :
    0 ≤ CY ∧ ∀ τ : ℝ, |τ| ≤ 1 → ‖Y τ‖ ≤ CY * 1024 ∧ ‖deriv Y τ‖ ≤ CY * 1024 ∧ ‖deriv (deriv Y) τ‖ ≤ CY * 1024 := by
  have h0 := (hY.2 0).1
  simp only [abs_zero, add_zero, one_pow, neg_zero, mul_zero, Real.exp_zero, mul_one] at h0
  have hCY : 0 ≤ CY := (norm_nonneg _).trans h0
  refine ⟨hCY, fun τ hτ => ?_⟩
  have h1 : (1 + |τ|) ^ 10 ≤ 2 ^ 10 := pow_le_pow_left₀ (by linarith [abs_nonneg τ]) (by linarith) 10
  have h2 : Real.exp (-(π * |τ|)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg τ, Real.pi_pos])
  have h3 : CY * ((1 + |τ|) ^ 10 * Real.exp (-(π * |τ|))) ≤ CY * 1024 := by
    have : (1 + |τ|) ^ 10 * Real.exp (-(π * |τ|)) ≤ 1024 := by
      have h4 := Real.exp_pos (-(π * |τ|))
      calc (1 + |τ|) ^ 10 * Real.exp (-(π * |τ|)) ≤ 2 ^ 10 * 1 := mul_le_mul h1 h2 h4.le (by positivity)
        _ = 1024 := by norm_num
    exact mul_le_mul_of_nonneg_left this hCY
  obtain ⟨a1, a2, a3⟩ := hY.2 τ
  exact ⟨a1.trans h3, a2.trans h3, a3.trans h3⟩

theorem edge_prod_near {Y : ℝ → ℂ} {CY : ℝ}
    (hY : Env2 Y (fun τ => CY * ((1 + |τ|) ^ 10 * Real.exp (-(π * |τ|))))) {δ a : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ha : 0 < a) :
    ∃ C : ℝ, ∀ τ : ℝ, τ ≠ 0 → |τ| ≤ 1 →
      ‖Y τ * seedV δ (a * τ) - Y 0 * seedV δ (a * 0)‖ ≤ C * |τ| ^ (1 / 2 : ℝ) ∧
      ‖deriv (fun t : ℝ => Y t * seedV δ (a * t)) τ‖ ≤ C * |τ| ^ ((1 / 2 : ℝ) - 1) ∧
      ‖deriv (deriv (fun t : ℝ => Y t * seedV δ (a * t))) τ‖ ≤ C * |τ| ^ ((1 / 2 : ℝ) - 2) := by
  obtain ⟨hCY, hP⟩ := env2_near_const hY
  obtain ⟨Cu, hCu0, hCu⟩ := V_deriv_bounds hδ0 hδ1 ha
  obtain ⟨CT, hCT0, hCT⟩ := seedT_holder hδ0 hδ1
  obtain ⟨B, hB⟩ := seedT_bound δ
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by simp))
  set P1 : ℝ := CY * 1024 with hP1
  have hP10 : 0 ≤ P1 := by positivity
  have hS : IsOpen {τ : ℝ | τ ≠ 0} := isOpen_ne
  have hVc : ContDiffOn ℝ 2 (fun t : ℝ => seedV δ (a * t)) {τ : ℝ | τ ≠ 0} :=
    (seedV_contDiffOn δ 2).comp (contDiff_const.mul contDiff_id).contDiffOn
      (fun τ hτ => mul_ne_zero ha.ne' hτ)
  have hVb : ∀ τ : ℝ, ‖seedV δ (a * τ)‖ ≤ B := fun τ => hB _ (by simp [seedV])
  refine ⟨max (P1 * CT * a ^ (1 / 2 : ℝ) + P1 * B) (max (P1 * B + P1 * (a * Cu))
    (P1 * B + 2 * (P1 * (a * Cu)) + P1 * (a * (a * Cu)))), fun τ hτ hτ1 => ?_⟩
  have hy : 0 < |τ| := abs_pos.mpr hτ
  have h1 := one_le_rpow_neg_half hy hτ1
  have h2 := one_le_rpow_neg_three_half hy hτ1
  have h12 := rpow_neg_half_le_neg_three_half hy hτ1
  have hhalf := rpow_half_le_of_le_one hy.le hτ1
  have hpos1 : 0 ≤ |τ| ^ (1 / 2 : ℝ) := Real.rpow_nonneg hy.le _
  obtain ⟨pD1, pD2⟩ := prod_deriv hS hY.1 hVc hτ
  obtain ⟨y0, y1, y2⟩ := hP τ hτ1
  obtain ⟨v1, v2⟩ := hCu τ hτ hτ1
  have hdV : ‖deriv (fun t : ℝ => seedV δ (a * t)) τ‖ ≤ a * (Cu * |τ| ^ ((1 / 2 : ℝ) - 1)) := by
    rw [deriv_V, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left v1 ha.le
  have hddV : ‖deriv (deriv (fun t : ℝ => seedV δ (a * t))) τ‖ ≤ a * (a * (Cu * |τ| ^ ((1 / 2 : ℝ) - 2))) := by
    rw [deriv_deriv_V, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left v2 ha.le) ha.le
  have hVb' := hVb τ
  have hy0 := y0
  refine ⟨?_, ?_, ?_⟩
  · -- value
    have hVh : ‖seedV δ (a * τ) - seedV δ (a * 0)‖ ≤ CT * (a ^ (1 / 2 : ℝ) * |τ| ^ (1 / 2 : ℝ)) := by
      have := hCT (((a * τ : ℝ) : ℂ) * Complex.I) (by simp)
      have hn : ‖((a * τ : ℝ) : ℂ) * Complex.I‖ = a * |τ| := by simp [abs_mul, abs_of_pos ha]
      rw [hn, Real.mul_rpow ha.le hy.le] at this
      have e : seedV δ (a * 0) = seedT δ 0 := by simp [seedV]
      rw [e]
      exact this
    have hYm : ‖Y τ - Y 0‖ ≤ P1 * |τ| := by
      have := Convex.norm_image_sub_le_of_norm_deriv_le (f := Y) (s := Icc (-1 : ℝ) 1) (C := P1)
        (fun x _ => hY.differentiable x)
        (fun x hx => (hP x (abs_le.mpr hx)).2.1) (convex_Icc _ _) (by simp : (0 : ℝ) ∈ Icc (-1 : ℝ) 1)
        (by simp [abs_le.mp hτ1] : τ ∈ Icc (-1 : ℝ) 1)
      simpa using this
    have e : Y τ * seedV δ (a * τ) - Y 0 * seedV δ (a * 0) =
        Y τ * (seedV δ (a * τ) - seedV δ (a * 0)) + (Y τ - Y 0) * seedV δ (a * 0) := by ring
    rw [e]
    have hV0 : ‖seedV δ (a * 0)‖ ≤ B := hVb 0
    calc _ ≤ ‖Y τ‖ * ‖seedV δ (a * τ) - seedV δ (a * 0)‖ + ‖Y τ - Y 0‖ * ‖seedV δ (a * 0)‖ :=
          (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
      _ ≤ P1 * (CT * (a ^ (1 / 2 : ℝ) * |τ| ^ (1 / 2 : ℝ))) + (P1 * |τ|) * B := by gcongr
      _ ≤ P1 * (CT * (a ^ (1 / 2 : ℝ) * |τ| ^ (1 / 2 : ℝ))) + (P1 * |τ| ^ (1 / 2 : ℝ)) * B := by gcongr
      _ = (P1 * CT * a ^ (1 / 2 : ℝ) + P1 * B) * |τ| ^ (1 / 2 : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hpos1
  · rw [pD1]
    have hcc : P1 * B + P1 * (a * Cu) ≤ max (P1 * CT * a ^ (1 / 2 : ℝ) + P1 * B) (max (P1 * B + P1 * (a * Cu))
        (P1 * B + 2 * (P1 * (a * Cu)) + P1 * (a * (a * Cu)))) := (le_max_left _ _).trans (le_max_right _ _)
    have hAB : 0 ≤ P1 * B := mul_nonneg hP10 hB0
    have hAC : 0 ≤ P1 * (a * Cu) := mul_nonneg hP10 (mul_nonneg ha.le hCu0)
    calc _ ≤ ‖deriv Y τ‖ * ‖seedV δ (a * τ)‖ + ‖Y τ‖ * ‖deriv (fun t : ℝ => seedV δ (a * t)) τ‖ :=
          (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
      _ ≤ P1 * B + P1 * (a * (Cu * |τ| ^ ((1 / 2 : ℝ) - 1))) := by gcongr
      _ ≤ (P1 * B + P1 * (a * Cu)) * |τ| ^ ((1 / 2 : ℝ) - 1) := by
          have := mul_le_mul_of_nonneg_left h1 hAB
          nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hcc (Real.rpow_nonneg hy.le _)
  · rw [pD2]
    have e2 : ‖(2 : ℂ)‖ = 2 := by simp
    have hcc : P1 * B + 2 * (P1 * (a * Cu)) + P1 * (a * (a * Cu)) ≤
        max (P1 * CT * a ^ (1 / 2 : ℝ) + P1 * B) (max (P1 * B + P1 * (a * Cu))
        (P1 * B + 2 * (P1 * (a * Cu)) + P1 * (a * (a * Cu)))) := (le_max_right _ _).trans (le_max_right _ _)
    have hAB : 0 ≤ P1 * B := mul_nonneg hP10 hB0
    have hAC : 0 ≤ P1 * (a * Cu) := mul_nonneg hP10 (mul_nonneg ha.le hCu0)
    have hAA : 0 ≤ P1 * (a * (a * Cu)) := mul_nonneg hP10 (mul_nonneg ha.le (mul_nonneg ha.le hCu0))
    have hn : ‖deriv (deriv Y) τ * seedV δ (a * τ) + 2 * (deriv Y τ * deriv (fun t : ℝ => seedV δ (a * t)) τ) +
        Y τ * deriv (deriv (fun t : ℝ => seedV δ (a * t))) τ‖ ≤
        ‖deriv (deriv Y) τ‖ * ‖seedV δ (a * τ)‖ +
        2 * (‖deriv Y τ‖ * ‖deriv (fun t : ℝ => seedV δ (a * t)) τ‖) +
        ‖Y τ‖ * ‖deriv (deriv (fun t : ℝ => seedV δ (a * t))) τ‖ := by
      refine (norm_add₃_le).trans ?_
      rw [norm_mul, norm_mul, norm_mul, norm_mul, e2]
    calc _ ≤ _ := hn
      _ ≤ P1 * B + 2 * (P1 * (a * (Cu * |τ| ^ ((1 / 2 : ℝ) - 1)))) +
          P1 * (a * (a * (Cu * |τ| ^ ((1 / 2 : ℝ) - 2)))) := by gcongr
      _ ≤ (P1 * B + 2 * (P1 * (a * Cu)) + P1 * (a * (a * Cu))) * |τ| ^ ((1 / 2 : ℝ) - 2) := by
          have e1 := mul_le_mul_of_nonneg_left h2 hAB
          have e3 := mul_le_mul_of_nonneg_left h12 hAC
          have e4 := mul_le_mul_of_nonneg_left (le_refl (|τ| ^ ((1 / 2 : ℝ) - 2))) hAA
          nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hcc (Real.rpow_nonneg hy.le _)


lemma env_far_le {CY : ℝ} (hCY : 0 ≤ CY) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : ℝ, 1 / 2 ≤ |τ| →
      CY * ((1 + |τ|) ^ 10 * Real.exp (-(π * |τ|))) ≤ M * (1 + |τ|) ^ (-(2 : ℝ)) := by
  obtain ⟨M, hM0, hM⟩ := poly_exp_le_n 12
  refine ⟨CY * M, mul_nonneg hCY hM0, fun τ _ => ?_⟩
  have hx : 0 < 1 + |τ| := by positivity
  rw [rpow_neg_two_eq hx.le]
  have h := hM |τ| (abs_nonneg τ)
  have e : (1 + |τ|) ^ 10 * Real.exp (-(π * |τ|)) =
      ((1 + |τ|) ^ 12 * Real.exp (-(π * |τ|))) * (1 / (1 + |τ|) ^ 2) := by
    field_simp
  rw [e, ← mul_assoc]
  have : 0 ≤ 1 / (1 + |τ|) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h this, mul_nonneg hCY this]

theorem edge_prod_far {Y : ℝ → ℂ} {CY : ℝ}
    (hY : Env2 Y (fun τ => CY * ((1 + |τ|) ^ 10 * Real.exp (-(π * |τ|))))) {δ a : ℝ}
    (ha : 0 < a) :
    ∃ C : ℝ, ∀ τ : ℝ, 1 / 2 ≤ |τ| →
      ‖Y τ * seedV δ (a * τ)‖ ≤ C * (1 + |τ|) ^ (-(2 : ℝ)) ∧
      ‖deriv (fun t : ℝ => Y t * seedV δ (a * t)) τ‖ ≤ C * (1 + |τ|) ^ (-(2 : ℝ)) ∧
      ‖deriv (deriv (fun t : ℝ => Y t * seedV δ (a * t))) τ‖ ≤ C * (1 + |τ|) ^ (-(2 : ℝ)) := by
  obtain ⟨hCY, -⟩ := env2_near_const hY
  obtain ⟨M, hM0, hM⟩ := env_far_le hCY
  have hq0 : 0 < min 2 (a / 2) := lt_min (by norm_num) (by positivity)
  obtain ⟨Cf, hCf0, hCf⟩ := seedV_far δ hq0
  have hS : IsOpen {τ : ℝ | τ ≠ 0} := isOpen_ne
  have hVc : ContDiffOn ℝ 2 (fun t : ℝ => seedV δ (a * t)) {τ : ℝ | τ ≠ 0} :=
    (seedV_contDiffOn δ 2).comp (contDiff_const.mul contDiff_id).contDiffOn
      (fun τ hτ => mul_ne_zero ha.ne' hτ)
  refine ⟨M * (Cf * (1 + a) ^ 2), fun τ hτ => ?_⟩
  have hτ0 : τ ≠ 0 := by
    intro h; rw [h] at hτ; simp at hτ; linarith
  have hqq : min 2 (a / 2) ≤ |a * τ| := by
    rw [abs_mul, abs_of_pos ha]
    exact (min_le_right _ _).trans (by nlinarith)
  obtain ⟨f0, f1, f2⟩ := hCf (a * τ) hqq
  obtain ⟨pD1, pD2⟩ := prod_deriv hS hY.1 hVc hτ0
  obtain ⟨y0, y1, y2⟩ := hY.2 τ
  have hP := hM τ hτ
  have hPn : 0 ≤ M * (1 + |τ|) ^ (-(2 : ℝ)) := by positivity
  set P := CY * ((1 + |τ|) ^ 10 * Real.exp (-(π * |τ|))) with hPdef
  have hP0 : 0 ≤ P := (norm_nonneg _).trans y0
  have hdV : ‖deriv (fun t : ℝ => seedV δ (a * t)) τ‖ ≤ a * Cf := by
    rw [deriv_V, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left f1 ha.le
  have hddV : ‖deriv (deriv (fun t : ℝ => seedV δ (a * t))) τ‖ ≤ a * (a * Cf) := by
    rw [deriv_deriv_V, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left f2 ha.le) ha.le
  have e2 : ‖(2 : ℂ)‖ = 2 := by simp
  have hC1 : 0 ≤ Cf * (1 + a) ^ 2 := by positivity
  have key : P * (Cf * (1 + a) ^ 2) ≤ M * (Cf * (1 + a) ^ 2) * (1 + |τ|) ^ (-(2 : ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_right hP hC1]
  have hA1 : P * Cf ≤ P * (Cf * (1 + a) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hP0
    nlinarith [sq_nonneg a, mul_nonneg ha.le hCf0, mul_nonneg (mul_nonneg ha.le ha.le) hCf0]
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_mul]
    calc _ ≤ P * Cf := mul_le_mul y0 f0 (norm_nonneg _) hP0
      _ ≤ _ := hA1.trans key
  · rw [pD1]
    calc _ ≤ ‖deriv Y τ‖ * ‖seedV δ (a * τ)‖ + ‖Y τ‖ * ‖deriv (fun t : ℝ => seedV δ (a * t)) τ‖ :=
          (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
      _ ≤ P * Cf + P * (a * Cf) := by gcongr
      _ ≤ P * (Cf * (1 + a) ^ 2) := by
          have : 0 ≤ P * (a * Cf) := by positivity
          nlinarith [mul_nonneg hP0 (mul_nonneg ha.le hCf0), mul_nonneg hP0 (mul_nonneg (mul_nonneg ha.le ha.le) hCf0),
            mul_nonneg hP0 hCf0]
      _ ≤ _ := key
  · rw [pD2]
    have hn : ‖deriv (deriv Y) τ * seedV δ (a * τ) + 2 * (deriv Y τ * deriv (fun t : ℝ => seedV δ (a * t)) τ) +
        Y τ * deriv (deriv (fun t : ℝ => seedV δ (a * t))) τ‖ ≤
        ‖deriv (deriv Y) τ‖ * ‖seedV δ (a * τ)‖ +
        2 * (‖deriv Y τ‖ * ‖deriv (fun t : ℝ => seedV δ (a * t)) τ‖) +
        ‖Y τ‖ * ‖deriv (deriv (fun t : ℝ => seedV δ (a * t))) τ‖ := by
      refine (norm_add₃_le).trans ?_
      rw [norm_mul, norm_mul, norm_mul, norm_mul, e2]
    calc _ ≤ _ := hn
      _ ≤ P * Cf + 2 * (P * (a * Cf)) + P * (a * (a * Cf)) := by gcongr
      _ = P * (Cf * (1 + a) ^ 2) := by ring
      _ ≤ _ := key

/-- info: 'FormalResearch.SignUncertainty.edge_prod_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edge_prod_near

/-- info: 'FormalResearch.SignUncertainty.edge_prod_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edge_prod_far

/-- info: 'FormalResearch.SignUncertainty.edge_prod_c2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edge_prod_c2

end FormalResearch.SignUncertainty
