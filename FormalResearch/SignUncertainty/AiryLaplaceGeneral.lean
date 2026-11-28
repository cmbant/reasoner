module

public import FormalResearch.SignUncertainty.AiryRationalSeeds
public import FormalResearch.Special.AiryAsymSector
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Positive-Axis Airy Laplace Asymptotic (`lem:airy-laplace-general` (2))

Proves the large-height asymptotic of `\mathscr{L}_y(H) = e^{-y^3/12} \int_{\mathbb{R}} H(u) e^{yu}\,du`
(`lem:airy-laplace-general` (2) of `ce_shells.tex`): if `H ∈ L^1(ℝ)` and
`H(u) = e^{-4u^{3/2}/3} (C u^{-p} + O(u^{-p-δ}))` for `u ≥ U`, then
`y^{2p - 1/2} \mathscr{L}_y(H) → C 2^{2p} √π` as `y → ∞`.

Specialized to `F ∈ \mathcal{R}_{\mathrm{Ai}}^{\mathrm{gen}}` (`HasGenRationalAiryCoeffs F β₀₀ β₁₁`),
we deduce `F(u) = e^{-4u^{3/2}/3} ((\beta_+(F)/(4π)) u^{-3/2} + O(u^{-2}))` on `[R_* + 2, ∞)` and hence
`y^{5/2} \mathscr{L}_y(\operatorname{Re} F) → \beta_+(F) \cdot (2/√π)` as `y → ∞`, with the tail lower
and upper bounds needed by `lem:ce-dual-line`.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped Real Polynomial

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-! ### Gaussian domination and integral evaluation for `lem:airy-laplace-general` (2) -/

private lemma abs_pow_mul_exp_neg_div_six_le (k : ℕ) (s : ℝ) :
    |s| ^ k * Real.exp (-(1 / 6 : ℝ) * s ^ 2) ≤ (6 : ℝ) ^ k * (Nat.factorial k : ℝ) + 1 := by
  have h1 : (1 / 6 * s ^ 2) ^ k / (Nat.factorial k : ℝ) ≤ Real.exp (1 / 6 * s ^ 2) :=
    Real.pow_div_factorial_le_exp _ (by positivity) k
  have hfac_pos : (0 : ℝ) < Nat.factorial k := by positivity
  have hsq : |s| ^ (2 * k) * Real.exp (-(1 / 6 : ℝ) * s ^ 2) ≤ (6 : ℝ) ^ k * (Nat.factorial k : ℝ) := by
    have hpow : (1 / 6 * s ^ 2) ^ k = (6 : ℝ)⁻¹ ^ k * |s| ^ (2 * k) := by
      rw [mul_pow, pow_mul, sq_abs, one_div]
    rw [hpow, div_le_iff₀ hfac_pos] at h1
    rw [show -(1 / 6 : ℝ) * s ^ 2 = -(1 / 6 * s ^ 2) by ring, Real.exp_neg]
    have hexp_pos : 0 < Real.exp (1 / 6 * s ^ 2) := Real.exp_pos _
    rw [← div_eq_mul_inv, div_le_iff₀ hexp_pos]
    calc |s| ^ (2 * k) = (6 : ℝ) ^ k * ((6 : ℝ)⁻¹ ^ k * |s| ^ (2 * k)) := by
          rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow, one_mul]
      _ ≤ (6 : ℝ) ^ k * (Real.exp (1 / 6 * s ^ 2) * (Nat.factorial k : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (6 : ℝ) ^ k * (Nat.factorial k : ℝ) * Real.exp (1 / 6 * s ^ 2) := by ring
  rcases le_or_gt |s| 1 with hs1 | hs1
  · calc |s| ^ k * Real.exp (-(1 / 6 : ℝ) * s ^ 2) ≤ 1 * 1 :=
          mul_le_mul (pow_le_one₀ (abs_nonneg _) hs1)
            (Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg s])) (Real.exp_pos _).le zero_le_one
      _ ≤ (6 : ℝ) ^ k * (Nat.factorial k : ℝ) + 1 :=
          by linarith only [(by positivity : (0 : ℝ) ≤ (6 : ℝ) ^ k * (Nat.factorial k : ℝ))]
  · have hle : |s| ^ k ≤ |s| ^ (2 * k) := pow_le_pow_right₀ hs1.le (by omega)
    calc |s| ^ k * Real.exp (-(1 / 6 : ℝ) * s ^ 2)
        ≤ |s| ^ (2 * k) * Real.exp (-(1 / 6 : ℝ) * s ^ 2) :=
          mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
      _ ≤ (6 : ℝ) ^ k * (Nat.factorial k : ℝ) + 1 := by linarith only [hsq]

private lemma integrable_one_add_abs_rpow_mul_exp_neg (m : ℝ) (hm : 0 ≤ m) :
    Integrable (fun s : ℝ => (1 + |s|) ^ m * Real.exp (-(2 / 3 : ℝ) * s ^ 2)) := by
  let k : ℕ := Nat.ceil m
  have hmk : m ≤ (k : ℝ) := Nat.le_ceil m
  let M : ℝ := (6 : ℝ) ^ k * (Nat.factorial k : ℝ) + 1
  let B : ℝ := (2 : ℝ) ^ k * (1 + M)
  have hdom : Integrable (fun s : ℝ => B * Real.exp (-(1 / 2 : ℝ) * s ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul B
  refine hdom.mono' (by fun_prop : Continuous fun s : ℝ =>
      (1 + |s|) ^ m * Real.exp (-(2 / 3 : ℝ) * s ^ 2)).aestronglyMeasurable
    (ae_of_all _ fun s => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have h1s : 1 ≤ 1 + |s| := by linarith only [abs_nonneg s]
  have hrpow : (1 + |s|) ^ m ≤ (1 + |s|) ^ k := by
    rw [← Real.rpow_natCast (1 + |s|) k]
    exact Real.rpow_le_rpow_of_exponent_le h1s hmk
  have hadd : (1 + |s|) ^ k ≤ (2 : ℝ) ^ k * (1 + |s| ^ k) := by
    rcases le_or_gt |s| 1 with hs1 | hs1
    · calc (1 + |s|) ^ k ≤ (2 : ℝ) ^ k := pow_le_pow_left₀ (by positivity) (by linarith only [hs1]) k
        _ ≤ (2 : ℝ) ^ k * (1 + |s| ^ k) :=
            le_mul_of_one_le_right (by positivity) (by linarith only [pow_nonneg (abs_nonneg s) k])
    · calc (1 + |s|) ^ k ≤ (2 * |s|) ^ k := pow_le_pow_left₀ (by positivity) (by linarith only [hs1]) k
        _ = (2 : ℝ) ^ k * |s| ^ k := mul_pow 2 |s| k
        _ ≤ (2 : ℝ) ^ k * (1 + |s| ^ k) :=
            mul_le_mul_of_nonneg_left (by linarith only) (by positivity)
  have hexp_split : Real.exp (-(2 / 3 : ℝ) * s ^ 2) =
      Real.exp (-(1 / 6 : ℝ) * s ^ 2) * Real.exp (-(1 / 2 : ℝ) * s ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hk_bd : (1 + |s| ^ k) * Real.exp (-(1 / 6 : ℝ) * s ^ 2) ≤ 1 + M := by
    have h0 : Real.exp (-(1 / 6 : ℝ) * s ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg s])
    have hk' := abs_pow_mul_exp_neg_div_six_le k s
    calc (1 + |s| ^ k) * Real.exp (-(1 / 6 : ℝ) * s ^ 2)
        = Real.exp (-(1 / 6 : ℝ) * s ^ 2) + |s| ^ k * Real.exp (-(1 / 6 : ℝ) * s ^ 2) := by ring
      _ ≤ 1 + M := add_le_add h0 hk'
  calc (1 + |s|) ^ m * Real.exp (-(2 / 3 : ℝ) * s ^ 2)
      ≤ ((2 : ℝ) ^ k * (1 + |s| ^ k)) * Real.exp (-(2 / 3 : ℝ) * s ^ 2) :=
        mul_le_mul_of_nonneg_right (hrpow.trans hadd) (Real.exp_pos _).le
    _ = (2 : ℝ) ^ k * ((1 + |s| ^ k) * Real.exp (-(1 / 6 : ℝ) * s ^ 2)) *
          Real.exp (-(1 / 2 : ℝ) * s ^ 2) := by rw [hexp_split]; ring
    _ ≤ B * Real.exp (-(1 / 2 : ℝ) * s ^ 2) := by
        dsimp [B]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk_bd (by positivity))
          (Real.exp_pos _).le

private lemma airyLaplace_saddle_identity (y t : ℝ) :
    y * t ^ 2 - (4 / 3 : ℝ) * t ^ 3 - y ^ 3 / 12 =
      -(4 / 3 : ℝ) * (t - y / 2) ^ 2 * (t + y / 4) := by ring

private lemma airyLaplace_shift_map_facts {y : ℝ} (hy : 0 < y) :
    let a := -(1 / 4 : ℝ) * y ^ (3 / 2 : ℝ)
    let φ : ℝ → ℝ := fun s => (y / 2 + s / √y) ^ 2
    let φ' : ℝ → ℝ := fun s => 2 * (y / 2 + s / √y) / √y
    (∀ s ∈ Ioi a, HasDerivWithinAt φ (φ' s) (Ioi a) s) ∧
    InjOn φ (Ioi a) ∧
    φ '' Ioi a = Ioi (y ^ 2 / 16) ∧
    (∀ s ∈ Ioi a, y / 4 < y / 2 + s / √y ∧ 0 < φ' s ∧ y ^ 2 / 16 < φ s) := by
  intro a φ φ'
  have hy32 : y * √y = y ^ (3 / 2 : ℝ) := by
    calc y * √y = y ^ (1 : ℝ) * y ^ (1 / 2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = y ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hy]; norm_num
  have hsqrt_pos : 0 < √y := Real.sqrt_pos.mpr hy
  have ht_gt : ∀ s ∈ Ioi a, y / 4 < y / 2 + s / √y := fun s hs => by
    have hsa : -(1 / 4 : ℝ) * y ^ (3 / 2 : ℝ) < s := hs
    have hdiv : -(y / 4) < s / √y := by
      rw [lt_div_iff₀ hsqrt_pos]
      linarith only [hsa, hy32]
    linarith only [hdiv]
  have hderiv : ∀ s ∈ Ioi a, HasDerivWithinAt φ (φ' s) (Ioi a) s := fun s _ => by
    have h1 : HasDerivAt (fun x : ℝ => y / 2 + x / √y) (1 / √y) s := by
      simpa using ((hasDerivAt_id s).div_const √y).const_add (y / 2)
    exact ((h1.pow 2).congr_deriv (by dsimp [φ']; ring)).hasDerivWithinAt
  have hinj : InjOn φ (Ioi a) := by
    intro s₁ hs₁ s₂ hs₂ heq
    have h1 := ht_gt s₁ hs₁
    have h2 := ht_gt s₂ hs₂
    have heq' : (y / 2 + s₁ / √y) ^ 2 = (y / 2 + s₂ / √y) ^ 2 := heq
    have hsq : y / 2 + s₁ / √y = y / 2 + s₂ / √y := by
      nlinarith only [heq', h1, h2, hy]
    have : s₁ / √y = s₂ / √y := by linarith only [hsq]
    exact (div_left_inj₀ hsqrt_pos.ne').mp this
  have himg : φ '' Ioi a = Ioi (y ^ 2 / 16) := by
    ext u
    constructor
    · rintro ⟨s, hs, rfl⟩
      have h1 := ht_gt s hs
      change y ^ 2 / 16 < (y / 2 + s / √y) ^ 2
      nlinarith only [h1, hy]
    · intro hu
      have hu' : y ^ 2 / 16 < u := hu
      have hu0 : 0 < u := lt_trans (by positivity) hu'
      have hru : y / 4 < √u := by
        rw [← Real.sqrt_sq (by linarith only [hy] : 0 ≤ y / 4)]
        exact Real.sqrt_lt_sqrt (by positivity) (by linarith only [hu'])
      refine ⟨√y * (√u - y / 2), ?_, ?_⟩
      · change a < √y * (√u - y / 2)
        have : -(y / 4) < √u - y / 2 := by linarith only [hru]
        calc a = √y * -(y / 4) := by dsimp [a]; rw [← hy32]; ring
          _ < √y * (√u - y / 2) := mul_lt_mul_of_pos_left this hsqrt_pos
      · dsimp [φ]
        rw [mul_div_cancel_left₀ _ hsqrt_pos.ne']
        ring_nf
        exact Real.sq_sqrt hu0.le
  refine ⟨hderiv, hinj, himg, fun s hs => ?_⟩
  have h1 := ht_gt s hs
  have h2 : 0 < φ' s := by dsimp [φ']; exact div_pos (by linarith only [h1, hy]) hsqrt_pos
  have h3 : y ^ 2 / 16 < φ s := by dsimp [φ]; nlinarith only [h1, hy]
  exact ⟨h1, h2, h3⟩

private lemma rpow_one_sub_two_p_le {q p s : ℝ} (hq_lo : 1 / 4 < q) (hq_hi : q ≤ 1 + |s|) :
    q ^ (1 - 2 * p) ≤ max ((4 : ℝ) ^ (2 * p - 1)) 1 * (1 + |s|) ^ (|1 - 2 * p|) := by
  have hq0 : 0 < q := by linarith only [hq_lo]
  have h1s : 1 ≤ 1 + |s| := by linarith only [abs_nonneg s]
  rcases le_or_gt 0 (1 - 2 * p) with hge | hlt
  · have h1 : q ^ (1 - 2 * p) ≤ (1 + |s|) ^ (1 - 2 * p) :=
      Real.rpow_le_rpow hq0.le hq_hi hge
    have h2 : (1 + |s|) ^ (1 - 2 * p) ≤ (1 + |s|) ^ (|1 - 2 * p|) :=
      Real.rpow_le_rpow_of_exponent_le h1s (le_abs_self _)
    calc q ^ (1 - 2 * p) ≤ 1 * (1 + |s|) ^ (|1 - 2 * p|) := by linarith only [h1, h2]
      _ ≤ max ((4 : ℝ) ^ (2 * p - 1)) 1 * (1 + |s|) ^ (|1 - 2 * p|) := by
          gcongr; exact le_max_right _ _
  · have h1 : q ^ (1 - 2 * p) ≤ (1 / 4 : ℝ) ^ (1 - 2 * p) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hq_lo.le hlt.le
    have hinv : (1 / 4 : ℝ) ^ (1 - 2 * p) = (4 : ℝ) ^ (2 * p - 1) := by
      rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
      congr 1; ring
    have h1s_pow : 1 ≤ (1 + |s|) ^ (|1 - 2 * p|) := Real.one_le_rpow h1s (abs_nonneg _)
    calc q ^ (1 - 2 * p) ≤ (4 : ℝ) ^ (2 * p - 1) := h1.trans_eq hinv
      _ ≤ max ((4 : ℝ) ^ (2 * p - 1)) 1 * (1 + |s|) ^ (|1 - 2 * p|) :=
          (le_max_left _ _).trans (le_mul_of_one_le_right
            (le_trans zero_le_one (le_max_right _ _)) h1s_pow)

private lemma shifted_gauss_saddle_bounds {y p δ s : ℝ} (hy1 : 1 ≤ y) (hδ : 0 < δ)
    (hs : -(1 / 4 : ℝ) * y ^ (3 / 2 : ℝ) < s) :
    let t := y / 2 + s / √y
    let u := t ^ 2
    0 < y ∧ 0 < t ∧ 0 < u ∧ y / 4 < t ∧ y ^ 2 / 16 < u ∧
    u ^ (-δ) ≤ 4 ^ (2 * δ) * y ^ (-(2 * δ)) ∧
    y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) * u ^ (-p) = 2 * (t / y) ^ (1 - 2 * p) ∧
    (t / y) ^ (1 - 2 * p) ≤ max ((4 : ℝ) ^ (2 * p - 1)) 1 * (1 + |s|) ^ (|1 - 2 * p|) ∧
    Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (y * u - y ^ 3 / 12) =
      Real.exp (-s ^ 2 - (4 / 3 : ℝ) * s ^ 3 / y ^ (3 / 2 : ℝ)) ∧
    Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (y * u - y ^ 3 / 12) ≤
      Real.exp (-(2 / 3 : ℝ) * s ^ 2) := by
  have hy0 : 0 < y := by linarith only [hy1]
  have hsqrt_pos : 0 < √y := Real.sqrt_pos.mpr hy0
  have hy32_pos : 0 < y ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hy0 _
  have hy_sqrt : y * √y = y ^ (3 / 2 : ℝ) := by
    calc y * √y = y ^ (1 : ℝ) * y ^ (1 / 2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = y ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hy0]; norm_num
  set t : ℝ := y / 2 + s / √y
  set u : ℝ := t ^ 2
  have ht_lo : y / 4 < t := by
    have hdiv : -(y / 4) < s / √y := by
      rw [lt_div_iff₀ hsqrt_pos]
      linarith only [hs, hy_sqrt]
    dsimp [t]; linarith only [hdiv]
  have ht0 : 0 < t := by linarith only [hy0, ht_lo]
  have hu0 : 0 < u := by positivity
  have hu_lo : y ^ 2 / 16 < u := by dsimp [u]; nlinarith only [ht_lo, hy0]
  have hu_δ : u ^ (-δ) ≤ 4 ^ (2 * δ) * y ^ (-(2 * δ)) := by
    have hpow2 : (y / 4) ^ 2 ≤ u := by
      dsimp [u]; exact pow_le_pow_left₀ (by positivity) ht_lo.le 2
    have h1 : u ^ (-δ) ≤ ((y / 4) ^ 2) ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hpow2 (by linarith only [hδ])
    refine h1.trans_eq ?_
    rw [← Real.rpow_natCast (y / 4) 2, ← Real.rpow_mul (by positivity),
      Real.div_rpow hy0.le (by norm_num),
      show ((2 : ℕ) : ℝ) * -δ = -(2 * δ) by ring,
      div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), neg_neg, mul_comm]
  have hup : u ^ (-p) = t ^ (-2 * p) := by
    dsimp [u]; rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht0.le]; congr 1; ring
  have hy_fac : y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) * u ^ (-p) = 2 * (t / y) ^ (1 - 2 * p) := by
    rw [hup]
    have h1 : y ^ (2 * p - 1 / 2 : ℝ) / √y = y ^ (2 * p - 1 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hy0]; congr 1; ring
    have h2 : t * t ^ (-2 * p) = t ^ (1 - 2 * p) := by
      nth_rw 1 [← Real.rpow_one t]; rw [← Real.rpow_add ht0]; congr 1; ring
    have h3 : (t / y) ^ (1 - 2 * p) = t ^ (1 - 2 * p) * y ^ (2 * p - 1 : ℝ) := by
      rw [Real.div_rpow ht0.le hy0.le, div_eq_mul_inv, ← Real.rpow_neg hy0.le]
      congr 2; ring
    rw [h3]
    calc y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) * t ^ (-2 * p)
        = 2 * (t * t ^ (-2 * p)) * (y ^ (2 * p - 1 / 2 : ℝ) / √y) := by ring
      _ = 2 * t ^ (1 - 2 * p) * y ^ (2 * p - 1 : ℝ) := by rw [h1, h2]
      _ = 2 * (t ^ (1 - 2 * p) * y ^ (2 * p - 1 : ℝ)) := by ring
  have hq_lo : 1 / 4 < t / y := by rw [lt_div_iff₀ hy0]; linarith only [ht_lo]
  have hq_hi : t / y ≤ 1 + |s| := by
    have hy32 : 1 ≤ y * √y := by
      have : 1 ≤ √y := Real.one_le_sqrt.mpr hy1
      nlinarith only [hy1, this]
    have hsy : |s| / (y * √y) ≤ |s| := div_le_self (abs_nonneg s) hy32
    calc t / y = 1 / 2 + s / (y * √y) := by
          dsimp [t]; field_simp [hy0.ne', hsqrt_pos.ne']
      _ ≤ 1 / 2 + |s| / (y * √y) := by gcongr; exact le_abs_self _
      _ ≤ 1 + |s| := by linarith only [hsy]
  have hq_bd := rpow_one_sub_two_p_le (p := p) hq_lo hq_hi
  have hu32 : u ^ (3 / 2 : ℝ) = t ^ 3 := by
    dsimp [u]
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht0.le,
      show (2 : ℕ) * (3 / 2 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hexp_eq : Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (y * u - y ^ 3 / 12) =
      Real.exp (-s ^ 2 - (4 / 3 : ℝ) * s ^ 3 / y ^ (3 / 2 : ℝ)) := by
    rw [← Real.exp_add, hu32]
    dsimp [u]
    rw [show -(4 / 3 : ℝ) * t ^ 3 + (y * t ^ 2 - y ^ 3 / 12) =
        y * t ^ 2 - (4 / 3 : ℝ) * t ^ 3 - y ^ 3 / 12 by ring, airyLaplace_saddle_identity y t]
    congr 1
    have h1 : t - y / 2 = s / √y := by dsimp [t]; ring
    have h2 : t + y / 4 = 3 * y / 4 + s / √y := by dsimp [t]; ring
    rw [h1, h2, div_pow, Real.sq_sqrt hy0.le, ← hy_sqrt]
    field_simp [hy0.ne', hsqrt_pos.ne']
    ring
  have hexp_le : Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (y * u - y ^ 3 / 12) ≤
      Real.exp (-(2 / 3 : ℝ) * s ^ 2) := by
    rw [← Real.exp_add, hu32]
    dsimp [u]
    rw [show -(4 / 3 : ℝ) * t ^ 3 + (y * t ^ 2 - y ^ 3 / 12) =
        y * t ^ 2 - (4 / 3 : ℝ) * t ^ 3 - y ^ 3 / 12 by ring, airyLaplace_saddle_identity y t]
    refine Real.exp_le_exp.mpr ?_
    have hsq_eq : (t - y / 2) ^ 2 = s ^ 2 / y := by
      dsimp [t]; rw [add_sub_cancel_left, div_pow, Real.sq_sqrt hy0.le]
    have hty : y / 2 ≤ t + y / 4 := by linarith only [ht_lo]
    rw [hsq_eq]
    have hmul : (4 / 3 : ℝ) * (s ^ 2 / y) * (y / 2) ≤ (4 / 3 : ℝ) * (s ^ 2 / y) * (t + y / 4) :=
      mul_le_mul_of_nonneg_left hty (by positivity)
    have hid : (4 / 3 : ℝ) * (s ^ 2 / y) * (y / 2) = (2 / 3 : ℝ) * s ^ 2 := by
      field_simp [hy0.ne']; ring
    linarith only [hmul, hid]
  exact ⟨hy0, ht0, hu0, ht_lo, hu_lo, hu_δ, hy_fac, hq_bd, hexp_eq, hexp_le⟩

/-- **Lemma `lem:airy-laplace-general` (2)** (`ce_shells.tex`): large-height asymptotic of the Airy
Laplace transform `\mathscr{L}_y(H)` when `H ∈ L^1(ℝ)` and `H(u) = e^{-4u^{3/2}/3}(C u^{-p} + O(u^{-p-δ}))`
as `u → +∞`. -/
theorem airyLaplace_tendsto_of_asymptotic (H : ℝ → ℝ)
    (hH_int : Integrable H)
    (p δ C : ℝ) (hδ : 0 < δ)
    (U : ℝ) (hU : 1 ≤ U) (R_err : ℝ) (hR : 0 ≤ R_err)
    (hH_asymp : ∀ u : ℝ, U ≤ u →
      |H u - Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * (C * u ^ (-p))| ≤
        R_err * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * u ^ (-p - δ)) :
    Tendsto (fun y : ℝ => y ^ (2 * p - 1 / 2 : ℝ) * airyLaplace H y) atTop
      (𝓝 (C * 2 ^ (2 * p) * √π)) := by
  let Y₀ : ℝ := max (4 * √U + 4) 1
  have hU_le_Y0 : ∀ y : ℝ, Y₀ ≤ y → U ≤ y ^ 2 / 16 ∧ 1 ≤ y ∧ 0 < y := fun y hy => by
    have h1 : 1 ≤ y := (le_max_right _ _).trans hy
    have h4u : 4 * √U ≤ y := by linarith only [(le_max_left _ _).trans hy]
    have hsu : √U ≤ y / 4 := by linarith only [h4u]
    have hU0 : 0 ≤ U := by linarith only [hU]
    have hsq : U ≤ y ^ 2 / 16 := by
      calc U = √U ^ 2 := (Real.sq_sqrt hU0).symm
        _ ≤ (y / 4) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsu 2
        _ = y ^ 2 / 16 := by ring
    exact ⟨hsq, h1, by linarith only [h1]⟩
  let G_int : ℝ → ℝ → ℝ := fun y s =>
    if -(1 / 4 : ℝ) * y ^ (3 / 2 : ℝ) < s then
      let t := y / 2 + s / √y
      let u := t ^ 2
      y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) *
        (H u * Real.exp (y * u - y ^ 3 / 12))
    else 0
  let M_dom : ℝ := 2 * (|C| + R_err * (4 : ℝ) ^ (2 * δ)) * max ((4 : ℝ) ^ (2 * p - 1)) 1
  let dom : ℝ → ℝ := fun s => M_dom * (1 + |s|) ^ (|1 - 2 * p|) * Real.exp (-(2 / 3 : ℝ) * s ^ 2)
  have hdom_int : Integrable dom :=
    (integrable_one_add_abs_rpow_mul_exp_neg (|1 - 2 * p|) (abs_nonneg _)).const_mul M_dom |>.congr
      (ae_of_all _ fun s => by dsimp [dom]; ring)
  have hG_facts : ∀ y : ℝ, Y₀ ≤ y →
      IntegrableOn (fun u : ℝ => H u * Real.exp (y * u - y ^ 3 / 12)) (Ioi (y ^ 2 / 16)) ∧
      y ^ (2 * p - 1 / 2 : ℝ) *
        ∫ u in Ioi (y ^ 2 / 16), H u * Real.exp (y * u - y ^ 3 / 12) = ∫ s : ℝ, G_int y s ∧
      Integrable (G_int y) ∧
      ∀ s : ℝ, |G_int y s| ≤ dom s := by
    intro y hy
    obtain ⟨hUy, hy1, hy0⟩ := hU_le_Y0 y hy
    have hsqrt_pos : 0 < √y := Real.sqrt_pos.mpr hy0
    let a : ℝ := -(1 / 4 : ℝ) * y ^ (3 / 2 : ℝ)
    let φ : ℝ → ℝ := fun s => (y / 2 + s / √y) ^ 2
    let φ' : ℝ → ℝ := fun s => 2 * (y / 2 + s / √y) / √y
    obtain ⟨hφ_deriv, hφ_inj, hφ_img, hφ_pt⟩ := airyLaplace_shift_map_facts hy0
    -- Majorant on `Ioi (y^2 / 16)`: `B_u * u^{-p} * exp(y u - 4/3 u^{3/2} - y^3/12)` (continuous!).
    let B_u : ℝ := |C| + R_err * 4 ^ (2 * δ)
    let maj : ℝ → ℝ := fun u =>
      B_u * u ^ (-p) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (y * u - y ^ 3 / 12)
    have hmaj_cont : ContinuousOn maj (Ioi (y ^ 2 / 16)) := by
      refine ContinuousOn.mul ?_ (by fun_prop)
      refine ContinuousOn.mul ?_ (by fun_prop)
      refine ContinuousOn.mul continuousOn_const ?_
      exact ContinuousOn.rpow_const continuousOn_id fun u hu => Or.inl (lt_trans (by positivity) hu).ne'
    have hmaj_pull_bd : ∀ s ∈ Ioi a, |φ' s * maj (φ s)| ≤ (y ^ (2 * p - 1 / 2 : ℝ))⁻¹ * dom s := by
      intro s hs
      have hs_bds := shifted_gauss_saddle_bounds (p := p) hy1 hδ hs
      have ht_lo : y / 4 < y / 2 + s / √y := hs_bds.2.2.2.1
      have hfac := hs_bds.2.2.2.2.2.2.1
      have hq_bd := hs_bds.2.2.2.2.2.2.2.1
      have hexp_le := hs_bds.2.2.2.2.2.2.2.2.2
      have ht0 : 0 < y / 2 + s / √y := by linarith only [hy0, ht_lo]
      have hφ'0 : 0 ≤ φ' s := div_nonneg (by positivity) hsqrt_pos.le
      have hmaj0 : 0 ≤ maj (φ s) := by
        dsimp [maj, B_u, φ]
        positivity
      rw [abs_of_nonneg (mul_nonneg hφ'0 hmaj0)]
      have hy_inv : 0 < (y ^ (2 * p - 1 / 2 : ℝ))⁻¹ := by positivity
      calc φ' s * maj (φ s)
          = (y ^ (2 * p - 1 / 2 : ℝ))⁻¹ *
              (B_u * (y ^ (2 * p - 1 / 2 : ℝ) * (2 * (y / 2 + s / √y) / √y) * (φ s) ^ (-p)) *
              (Real.exp (-(4 / 3 : ℝ) * (φ s) ^ (3 / 2 : ℝ)) * Real.exp (y * (φ s) - y ^ 3 / 12))) := by
                dsimp [maj, φ, φ']; field_simp [(Real.rpow_pos_of_pos hy0 _).ne']
        _ = (y ^ (2 * p - 1 / 2 : ℝ))⁻¹ *
              (B_u * (2 * ((y / 2 + s / √y) / y) ^ (1 - 2 * p)) *
              (Real.exp (-(4 / 3 : ℝ) * (φ s) ^ (3 / 2 : ℝ)) * Real.exp (y * (φ s) - y ^ 3 / 12))) := by
                rw [hfac]
        _ ≤ (y ^ (2 * p - 1 / 2 : ℝ))⁻¹ *
              (B_u * (2 * (max ((4 : ℝ) ^ (2 * p - 1)) 1 * (1 + |s|) ^ (|1 - 2 * p|))) *
              Real.exp (-(2 / 3 : ℝ) * s ^ 2)) := by
                gcongr
        _ = (y ^ (2 * p - 1 / 2 : ℝ))⁻¹ * dom s := by
                dsimp [dom, M_dom, B_u]; ring
    have hmaj_pull_int : IntegrableOn (fun s => |φ' s| • maj (φ s)) (Ioi a) := by
      refine (hdom_int.const_mul (y ^ (2 * p - 1 / 2 : ℝ))⁻¹).integrableOn.mono' ?_ ?_
      · have hcont : ContinuousOn (fun s => |φ' s| • maj (φ s)) (Ioi a) := by
          have h1 : ContinuousOn (fun s : ℝ => |φ' s|) (Ioi a) := ContinuousOn.abs (by fun_prop)
          have h2 : ContinuousOn (fun s : ℝ => maj (φ s)) (Ioi a) :=
            hmaj_cont.comp (by fun_prop) fun s hs => by rw [← hφ_img]; exact mem_image_of_mem φ hs
          exact (h1.mul h2).congr fun s _ => smul_eq_mul _ _
        exact hcont.aestronglyMeasurable measurableSet_Ioi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hφ'0 : 0 < φ' s := (hφ_pt s hs).2.1
        rw [smul_eq_mul, abs_of_pos hφ'0, Real.norm_eq_abs]
        exact hmaj_pull_bd s hs
    have hmaj_int : IntegrableOn maj (Ioi (y ^ 2 / 16)) := by
      rw [← hφ_img]
      exact (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
        hφ_deriv hφ_inj maj).2 hmaj_pull_int
    have h_u_int : IntegrableOn (fun u : ℝ => H u * Real.exp (y * u - y ^ 3 / 12)) (Ioi (y ^ 2 / 16)) := by
      refine hmaj_int.mono' ?_ ?_
      · exact (hH_int.aestronglyMeasurable.mul (by fun_prop : Continuous fun u : ℝ =>
            Real.exp (y * u - y ^ 3 / 12)).aestronglyMeasurable).restrict
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have huU : U ≤ u := le_trans hUy (le_of_lt hu)
        have hu0 : 0 < u := lt_trans (by positivity) hu
        have haH := hH_asymp u huU
        have htri := abs_sub_abs_le_abs_sub (H u)
          (Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * (C * u ^ (-p)))
        have hmain : |Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * (C * u ^ (-p))| =
            |C| * u ^ (-p) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by
          rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.rpow_pos_of_pos hu0 _)]
          ring
        have herr : u ^ (-p - δ) = u ^ (-δ) * u ^ (-p) := by
          rw [← Real.rpow_add hu0]; congr 1; ring
        have hu_δ : u ^ (-δ) ≤ 4 ^ (2 * δ) := by
          have hy4 : (1 / 16 : ℝ) ≤ u := by
            have hy4' : 1 ≤ y ^ 2 := by nlinarith only [hy1]
            linarith only [hu.out, hy4']
          have h1 : u ^ (-δ) ≤ (1 / 16 : ℝ) ^ (-δ) :=
            Real.rpow_le_rpow_of_nonpos (by norm_num) hy4 (by linarith only [hδ])
          refine h1.trans_eq ?_
          rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_neg,
            show (16 : ℝ) = (4 : ℝ) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast (4 : ℝ) 2,
            ← Real.rpow_mul (by norm_num), show ((2 : ℕ) : ℝ) * δ = 2 * δ by ring]
        rw [herr] at haH
        have hHu_le : |H u| ≤ B_u * u ^ (-p) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by
          have hle1 : |H u| ≤ (|C| + R_err * u ^ (-δ)) * u ^ (-p) *
              Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by
            linarith only [htri, haH, hmain]
          refine hle1.trans ?_
          dsimp [B_u]
          gcongr
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right hHu_le (Real.exp_pos _).le
    have h_s_intOn : IntegrableOn
        (fun s => |φ' s| • (H (φ s) * Real.exp (y * φ s - y ^ 3 / 12))) (Ioi a) := by
      have h' := h_u_int
      rw [← hφ_img] at h'
      exact (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
        hφ_deriv hφ_inj _).1 h'
    have h_cov : ∫ u in Ioi (y ^ 2 / 16), H u * Real.exp (y * u - y ^ 3 / 12) =
        ∫ s in Ioi a, |φ' s| • (H (φ s) * Real.exp (y * φ s - y ^ 3 / 12)) := by
      rw [← hφ_img]
      exact integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hφ_deriv hφ_inj _
    have hG_eq : G_int y = (Ioi a).indicator (fun s =>
        y ^ (2 * p - 1 / 2 : ℝ) * (|φ' s| • (H (φ s) * Real.exp (y * φ s - y ^ 3 / 12)))) := by
      ext s
      by_cases hs : a < s
      · have hφ'0 : 0 < φ' s := (hφ_pt s hs).2.1
        have hmem : s ∈ Ioi a := hs
        rw [indicator_of_mem hmem, smul_eq_mul, abs_of_pos hφ'0]
        dsimp only [G_int]
        split_ifs with h_lt
        · dsimp only [φ, φ']; ring
        · exact absurd hs h_lt
      · have hmem : s ∉ Ioi a := hs
        rw [indicator_of_notMem hmem]
        dsimp only [G_int]
        split_ifs with h_lt
        · exact absurd h_lt hs
        · rfl
    have hG_int : Integrable (G_int y) := by
      rw [hG_eq, integrable_indicator_iff measurableSet_Ioi]
      exact h_s_intOn.const_mul _
    have h_int_eq : y ^ (2 * p - 1 / 2 : ℝ) *
        ∫ u in Ioi (y ^ 2 / 16), H u * Real.exp (y * u - y ^ 3 / 12) = ∫ s : ℝ, G_int y s := by
      rw [h_cov, hG_eq, integral_indicator measurableSet_Ioi, ← integral_const_mul]
    refine ⟨h_u_int, h_int_eq, hG_int, fun s => ?_⟩
    by_cases hs : a < s
    · dsimp only [G_int]
      simp only [show -(1 / 4 : ℝ) * y ^ (3 / 2 : ℝ) < s from hs, ↓reduceIte]
      have hs_bds := @shifted_gauss_saddle_bounds y p δ s hy1 hδ hs
      set t : ℝ := y / 2 + s / √y
      set u : ℝ := t ^ 2
      have ht_pos : 0 < t := hs_bds.2.1
      have hu_pos : 0 < u := hs_bds.2.2.1
      have hpos_pre : 0 ≤ y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) := by positivity
      have huU : U ≤ u := le_trans hUy hs_bds.2.2.2.2.1.le
      have hu0 : 0 < u := hs_bds.2.2.1
      have haH := hH_asymp u huU
      have htri := abs_sub_abs_le_abs_sub (H u)
        (Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * (C * u ^ (-p)))
      have hmain : |Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * (C * u ^ (-p))| =
          |C| * u ^ (-p) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by
        rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.rpow_pos_of_pos hu0 _)]
        ring
      have herr : u ^ (-p - δ) = u ^ (-δ) * u ^ (-p) := by
        rw [← Real.rpow_add hu0]; congr 1; ring
      rw [herr] at haH
      have hHu_bd : |H u| ≤
          (|C| + R_err * u ^ (-δ)) * u ^ (-p) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by
        have hle1 : |H u| ≤ |C| * u ^ (-p) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) +
            R_err * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * (u ^ (-δ) * u ^ (-p)) := by
          linarith only [htri, haH, hmain]
        exact hle1.trans_eq (by ring)
      have hy_neg_le1 : y ^ (-(2 * δ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1 (by linarith only [hδ])
      have hu_δ1 : u ^ (-δ) ≤ 4 ^ (2 * δ) := by
        calc u ^ (-δ) ≤ 4 ^ (2 * δ) * y ^ (-(2 * δ)) := hs_bds.2.2.2.2.2.1
          _ ≤ 4 ^ (2 * δ) * 1 := by gcongr
          _ = 4 ^ (2 * δ) := mul_one _
      calc |y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) * (H u * Real.exp (y * u - y ^ 3 / 12))|
          = y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) * |H u| * Real.exp (y * u - y ^ 3 / 12) := by
              rw [abs_mul, abs_of_nonneg hpos_pre, abs_mul, abs_of_pos (Real.exp_pos _)]; ring
        _ ≤ y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) *
              ((|C| + R_err * u ^ (-δ)) * u ^ (-p) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ))) *
              Real.exp (y * u - y ^ 3 / 12) := by gcongr
        _ = (|C| + R_err * u ^ (-δ)) *
              (y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) * u ^ (-p)) *
              (Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (y * u - y ^ 3 / 12)) := by ring
        _ ≤ (|C| + R_err * (4 : ℝ) ^ (2 * δ)) *
              (2 * (max ((4 : ℝ) ^ (2 * p - 1)) 1 * (1 + |s|) ^ (|1 - 2 * p|))) *
              Real.exp (-(2 / 3 : ℝ) * s ^ 2) := by
                rw [hs_bds.2.2.2.2.2.2.1]
                refine mul_le_mul (mul_le_mul
                  (add_le_add le_rfl (mul_le_mul_of_nonneg_left hu_δ1 hR))
                  (mul_le_mul_of_nonneg_left hs_bds.2.2.2.2.2.2.2.1 zero_le_two)
                  (by positivity) (by positivity))
                  hs_bds.2.2.2.2.2.2.2.2.2 (by positivity) (by positivity)
        _ = dom s := by dsimp [dom, M_dom]; ring
    · dsimp only [G_int]
      simp only [show ¬ -(1 / 4 : ℝ) * y ^ (3 / 2 : ℝ) < s from hs, ↓reduceIte, abs_zero]
      have hm0 : 0 ≤ M_dom := by
        dsimp [M_dom]
        exact mul_nonneg (mul_nonneg zero_le_two
          (add_nonneg (abs_nonneg C) (mul_nonneg hR (Real.rpow_nonneg (by norm_num) _))))
          (le_trans zero_le_one (le_max_right _ _))
      have hr1 : 0 ≤ (1 + |s|) ^ |1 - 2 * p| :=
        Real.rpow_nonneg (by linarith only [abs_nonneg s]) _
      dsimp [dom]
      exact mul_nonneg (mul_nonneg hm0 hr1) (Real.exp_pos (-(2 / 3 : ℝ) * s ^ 2)).le
  -- Convergence of the `Ioi (y^2/16)` piece via dominated convergence.
  have h_ptwise : ∀ s : ℝ, Tendsto (fun y : ℝ => G_int y s) atTop (𝓝 (C * 2 ^ (2 * p) * Real.exp (-s ^ 2))) := by
    intro s
    have h_ev : ∀ᶠ y : ℝ in atTop, Y₀ ≤ y ∧ -(1 / 4 : ℝ) * y ^ (3 / 2 : ℝ) < s := by
      have h1 : ∀ᶠ y : ℝ in atTop, Y₀ ≤ y := eventually_ge_atTop Y₀
      have h2 : ∀ᶠ y : ℝ in atTop, (4 * (|s| + 1)) ^ 2 ≤ y := eventually_ge_atTop _
      filter_upwards [h1, h2] with y hy hy_s
      refine ⟨hy, ?_⟩
      have hy1 : 1 ≤ y := (le_max_right _ _).trans hy
      have hy0 : 0 < y := by linarith only [hy1]
      have h4s : 4 * (|s| + 1) ≤ √y := by
        rw [← Real.sqrt_sq (by positivity : 0 ≤ 4 * (|s| + 1))]
        exact Real.sqrt_le_sqrt hy_s
      have hy32 : √y ≤ y ^ (3 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
      have hquarter : |s| + 1 ≤ (1 / 4 : ℝ) * y ^ (3 / 2 : ℝ) := by linarith only [h4s, hy32]
      linarith only [hquarter, neg_abs_le s]
    -- Split `G_int y s = main_term y s + err_term y s`.
    let mainT : ℝ → ℝ := fun y =>
      2 * C * (1 / 2 + s / y ^ (3 / 2 : ℝ)) ^ (1 - 2 * p) *
        Real.exp (-s ^ 2 - (4 / 3 : ℝ) * s ^ 3 / y ^ (3 / 2 : ℝ))
    have hmain_lim : Tendsto mainT atTop (𝓝 (C * 2 ^ (2 * p) * Real.exp (-s ^ 2))) := by
      have hy32_atTop : Tendsto (fun y : ℝ => y ^ (3 / 2 : ℝ)) atTop atTop :=
        tendsto_rpow_atTop (by norm_num)
      have hdiv_zero : Tendsto (fun y : ℝ => s / y ^ (3 / 2 : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hy32_atTop
      have hbase_lim : Tendsto (fun y : ℝ => 1 / 2 + s / y ^ (3 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := by
        simpa using tendsto_const_nhds.add hdiv_zero
      have hrpow_lim : Tendsto (fun y : ℝ => (1 / 2 + s / y ^ (3 / 2 : ℝ)) ^ (1 - 2 * p)) atTop
          (𝓝 ((1 / 2 : ℝ) ^ (1 - 2 * p))) :=
        (ContinuousAt.rpow_const (continuousAt_id) (Or.inl (by norm_num : (1 / 2 : ℝ) ≠ 0))).tendsto.comp hbase_lim
      have hexp_lim : Tendsto (fun y : ℝ => Real.exp (-s ^ 2 - (4 / 3 : ℝ) * s ^ 3 / y ^ (3 / 2 : ℝ))) atTop
          (𝓝 (Real.exp (-s ^ 2))) := by
        have harg : Tendsto (fun y : ℝ => -s ^ 2 - (4 / 3 : ℝ) * s ^ 3 / y ^ (3 / 2 : ℝ)) atTop (𝓝 (-s ^ 2)) := by
          simpa using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hy32_atTop)
        exact Real.continuous_exp.continuousAt.tendsto.comp harg
      have hprod := (hrpow_lim.const_mul (2 * C)).mul hexp_lim
      have h2p : (1 / 2 : ℝ) ^ (1 - 2 * p) = (2 : ℝ) ^ (2 * p - 1) := by
        rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
        congr 1; ring
      have h2m : (2 : ℝ) * (2 : ℝ) ^ (2 * p - 1) = (2 : ℝ) ^ (2 * p) := by
        nth_rw 1 [← Real.rpow_one (2 : ℝ)]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1; ring
      have hval : 2 * C * (1 / 2 : ℝ) ^ (1 - 2 * p) * Real.exp (-s ^ 2) =
          C * (2 : ℝ) ^ (2 * p) * Real.exp (-s ^ 2) := by
        rw [h2p]; calc 2 * C * (2 : ℝ) ^ (2 * p - 1) * Real.exp (-s ^ 2)
            = C * ((2 : ℝ) * (2 : ℝ) ^ (2 * p - 1)) * Real.exp (-s ^ 2) := by ring
          _ = C * (2 : ℝ) ^ (2 * p) * Real.exp (-s ^ 2) := by rw [h2m]
      rwa [hval] at hprod
    have herr_lim : Tendsto (fun y : ℝ =>
        R_err * (4 : ℝ) ^ (2 * δ) * y ^ (-(2 * δ)) *
          (2 * (max ((4 : ℝ) ^ (2 * p - 1)) 1 * (1 + |s|) ^ (|1 - 2 * p|))) *
          Real.exp (-(2 / 3 : ℝ) * s ^ 2)) atTop (𝓝 0) := by
      have hy_zero : Tendsto (fun y : ℝ => y ^ (-(2 * δ))) atTop (𝓝 0) :=
        tendsto_rpow_neg_atTop (by positivity : 0 < 2 * δ)
      have h1 := ((hy_zero.const_mul (R_err * (4 : ℝ) ^ (2 * δ))).mul_const
        (2 * (max ((4 : ℝ) ^ (2 * p - 1)) 1 * (1 + |s|) ^ (|1 - 2 * p|)))).mul_const
        (Real.exp (-(2 / 3 : ℝ) * s ^ 2))
      simpa only [zero_mul, mul_zero] using h1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa only [sub_zero] using hmain_lim.sub herr_lim)
      (by simpa only [add_zero] using hmain_lim.add herr_lim) ?_ ?_
    · filter_upwards [h_ev] with y ⟨hyY, hs⟩
      simp only [G_int, hs, ↓reduceIte]
      have hy1 : 1 ≤ y := (le_max_right _ _).trans hyY
      have hy0 : 0 < y := by linarith only [hy1]
      have hs_bds := @shifted_gauss_saddle_bounds y p δ s hy1 hδ hs
      set t : ℝ := y / 2 + s / √y
      set u : ℝ := t ^ 2
      have ht_pos : 0 < t := hs_bds.2.1
      have hu_pos : 0 < u := hs_bds.2.2.1
      have hsqrt_pos : 0 < √y := Real.sqrt_pos.mpr hy0
      have hy_sqrt : y * √y = y ^ (3 / 2 : ℝ) := by
        calc y * √y = y ^ (1 : ℝ) * y ^ (1 / 2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
          _ = y ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hy0]; norm_num
      have hqt_eq : t / y = 1 / 2 + s / y ^ (3 / 2 : ℝ) := by
        dsimp [t]; rw [← hy_sqrt]; field_simp [hy0.ne', hsqrt_pos.ne']
      have huU : U ≤ u := le_trans (hU_le_Y0 y hyY).1 hs_bds.2.2.2.2.1.le
      have hpos_pre : 0 ≤ y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) := by positivity
      have hdiff_H : |y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) * (H u * Real.exp (y * u - y ^ 3 / 12)) -
          mainT y| ≤ R_err * (4 : ℝ) ^ (2 * δ) * y ^ (-(2 * δ)) *
          (2 * (max ((4 : ℝ) ^ (2 * p - 1)) 1 * (1 + |s|) ^ (|1 - 2 * p|))) *
          Real.exp (-(2 / 3 : ℝ) * s ^ 2) := by
        have hmain_eq : mainT y = y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) *
            (Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * (C * u ^ (-p)) * Real.exp (y * u - y ^ 3 / 12)) := by
          dsimp [mainT]
          rw [← hqt_eq, show 2 * C * (t / y) ^ (1 - 2 * p) = C * (2 * (t / y) ^ (1 - 2 * p)) by ring,
            ← hs_bds.2.2.2.2.2.2.1, ← hs_bds.2.2.2.2.2.2.2.2.1]
          ring
        rw [hmain_eq, show y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) * (H u * Real.exp (y * u - y ^ 3 / 12)) -
            y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) *
              (Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * (C * u ^ (-p)) * Real.exp (y * u - y ^ 3 / 12)) =
            (y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y)) *
              (H u - Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * (C * u ^ (-p))) *
              Real.exp (y * u - y ^ 3 / 12) by ring]
        rw [abs_mul, abs_mul, abs_of_nonneg hpos_pre, abs_of_pos (Real.exp_pos _)]
        have haH := hH_asymp u huU
        have herr_split : u ^ (-p - δ) = u ^ (-δ) * u ^ (-p) := by
          rw [← Real.rpow_add hs_bds.2.2.1]; congr 1; ring
        rw [herr_split] at haH
        calc y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) *
              |H u - Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * (C * u ^ (-p))| *
              Real.exp (y * u - y ^ 3 / 12)
            ≤ y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) *
                (R_err * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * (u ^ (-δ) * u ^ (-p))) *
                Real.exp (y * u - y ^ 3 / 12) := by gcongr
          _ = R_err * u ^ (-δ) * (y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) * u ^ (-p)) *
                (Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (y * u - y ^ 3 / 12)) := by ring
          _ ≤ R_err * ((4 : ℝ) ^ (2 * δ) * y ^ (-(2 * δ))) *
                (2 * (max ((4 : ℝ) ^ (2 * p - 1)) 1 * (1 + |s|) ^ (|1 - 2 * p|))) *
                Real.exp (-(2 / 3 : ℝ) * s ^ 2) := by
                rw [hs_bds.2.2.2.2.2.2.1]
                exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hs_bds.2.2.2.2.2.1 hR)
                  (mul_le_mul_of_nonneg_left hs_bds.2.2.2.2.2.2.2.1 zero_le_two)
                  (by positivity) (by positivity))
                  hs_bds.2.2.2.2.2.2.2.2.2 (by positivity) (by positivity)
          _ = _ := by ring
      exact (abs_le.mp hdiff_H).1 |> fun h => by linarith only [h]
    · filter_upwards [h_ev] with y ⟨hyY, hs⟩
      simp only [G_int, hs, ↓reduceIte]
      have hy1 : 1 ≤ y := (le_max_right _ _).trans hyY
      have hy0 : 0 < y := by linarith only [hy1]
      have hs_bds := @shifted_gauss_saddle_bounds y p δ s hy1 hδ hs
      set t : ℝ := y / 2 + s / √y
      set u : ℝ := t ^ 2
      have ht_pos : 0 < t := hs_bds.2.1
      have hu_pos : 0 < u := hs_bds.2.2.1
      have hsqrt_pos : 0 < √y := Real.sqrt_pos.mpr hy0
      have hy_sqrt : y * √y = y ^ (3 / 2 : ℝ) := by
        calc y * √y = y ^ (1 : ℝ) * y ^ (1 / 2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
          _ = y ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hy0]; norm_num
      have hqt_eq : t / y = 1 / 2 + s / y ^ (3 / 2 : ℝ) := by
        dsimp [t]; rw [← hy_sqrt]; field_simp [hy0.ne', hsqrt_pos.ne']
      have huU : U ≤ u := le_trans (hU_le_Y0 y hyY).1 hs_bds.2.2.2.2.1.le
      have hpos_pre : 0 ≤ y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) := by positivity
      have hmain_eq : mainT y = y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) *
          (Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * (C * u ^ (-p)) * Real.exp (y * u - y ^ 3 / 12)) := by
        dsimp [mainT]
        rw [← hqt_eq, show 2 * C * (t / y) ^ (1 - 2 * p) = C * (2 * (t / y) ^ (1 - 2 * p)) by ring,
          ← hs_bds.2.2.2.2.2.2.1, ← hs_bds.2.2.2.2.2.2.2.2.1]
        ring
      have haH := hH_asymp u huU
      have herr_split : u ^ (-p - δ) = u ^ (-δ) * u ^ (-p) := by
        rw [← Real.rpow_add hs_bds.2.2.1]; congr 1; ring
      rw [herr_split] at haH
      have hdiff_H : |y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) * (H u * Real.exp (y * u - y ^ 3 / 12)) -
          mainT y| ≤ R_err * (4 : ℝ) ^ (2 * δ) * y ^ (-(2 * δ)) *
          (2 * (max ((4 : ℝ) ^ (2 * p - 1)) 1 * (1 + |s|) ^ (|1 - 2 * p|))) *
          Real.exp (-(2 / 3 : ℝ) * s ^ 2) := by
        rw [hmain_eq, show y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) * (H u * Real.exp (y * u - y ^ 3 / 12)) -
            y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) *
              (Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * (C * u ^ (-p)) * Real.exp (y * u - y ^ 3 / 12)) =
            (y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y)) *
              (H u - Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * (C * u ^ (-p))) *
              Real.exp (y * u - y ^ 3 / 12) by ring]
        rw [abs_mul, abs_mul, abs_of_nonneg hpos_pre, abs_of_pos (Real.exp_pos _)]
        calc y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) *
              |H u - Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * (C * u ^ (-p))| *
              Real.exp (y * u - y ^ 3 / 12)
            ≤ y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) *
                (R_err * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * (u ^ (-δ) * u ^ (-p))) *
                Real.exp (y * u - y ^ 3 / 12) := by gcongr
          _ = R_err * u ^ (-δ) * (y ^ (2 * p - 1 / 2 : ℝ) * (2 * t / √y) * u ^ (-p)) *
                (Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (y * u - y ^ 3 / 12)) := by ring
          _ ≤ R_err * ((4 : ℝ) ^ (2 * δ) * y ^ (-(2 * δ))) *
                (2 * (max ((4 : ℝ) ^ (2 * p - 1)) 1 * (1 + |s|) ^ (|1 - 2 * p|))) *
                Real.exp (-(2 / 3 : ℝ) * s ^ 2) := by
                rw [hs_bds.2.2.2.2.2.2.1]
                exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hs_bds.2.2.2.2.2.1 hR)
                  (mul_le_mul_of_nonneg_left hs_bds.2.2.2.2.2.2.2.1 zero_le_two)
                  (by positivity) (by positivity))
                  hs_bds.2.2.2.2.2.2.2.2.2 (by positivity) (by positivity)
          _ = _ := by ring
      exact (abs_le.mp hdiff_H).2 |> fun h => by linarith only [h]
  have h_main_int_lim : Tendsto (fun y : ℝ => ∫ s : ℝ, G_int y s) atTop
      (𝓝 (∫ s : ℝ, C * 2 ^ (2 * p) * Real.exp (-s ^ 2))) :=
    tendsto_integral_filter_of_dominated_convergence dom
      (eventually_ge_atTop Y₀ |>.mono fun y hy => (hG_facts y hy).2.2.1.aestronglyMeasurable)
      (eventually_ge_atTop Y₀ |>.mono fun y hy => ae_of_all _ fun s => by
        rw [Real.norm_eq_abs]; exact (hG_facts y hy).2.2.2 s)
      hdom_int (ae_of_all _ h_ptwise)
  have h_gauss_eval : ∫ s : ℝ, C * 2 ^ (2 * p) * Real.exp (-s ^ 2) = C * 2 ^ (2 * p) * √π := by
    rw [integral_const_mul, show (fun s : ℝ => Real.exp (-s ^ 2)) = fun s => Real.exp (-(1 : ℝ) * s ^ 2) by
      ext s; ring_nf, integral_gaussian, div_one]
  -- Left piece `u ≤ y^2 / 16`: `‖H u * exp(y u - y^3/12)‖ ≤ |H u| * exp(-y^3/48)`.
  let L1 : ℝ := ∫ u : ℝ, |H u|
  have h_tail_lim : Tendsto (fun y : ℝ => y ^ (2 * p - 1 / 2 : ℝ) *
      ∫ u in Iic (y ^ 2 / 16), H u * Real.exp (y * u - y ^ 3 / 12)) atTop (𝓝 0) := by
    have h_zero : Tendsto (fun y : ℝ => y ^ (2 * p - 1 / 2 : ℝ) * (L1 * Real.exp (-y / 48))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun y : ℝ => y ^ (2 * p - 1 / 2 : ℝ) * Real.exp (-(1 / 48 : ℝ) * y)) atTop (𝓝 0) :=
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ (1 / 48) (by norm_num)
      have h2 := h1.const_mul L1
      rw [mul_zero] at h2
      exact h2.congr fun y => by rw [show -(1 / 48 : ℝ) * y = -y / 48 by ring]; ring
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ h_zero
    filter_upwards [eventually_ge_atTop Y₀] with y hy
    obtain ⟨_, hy1, hy0⟩ := hU_le_Y0 y hy
    have h_iic_int : IntegrableOn (fun u : ℝ => H u * Real.exp (y * u - y ^ 3 / 12)) (Iic (y ^ 2 / 16)) := by
      refine (hH_int.norm.const_mul (Real.exp (-y ^ 3 / 48))).integrableOn.mono' ?_ ?_
      · exact (hH_int.aestronglyMeasurable.mul (by fun_prop : Continuous fun u : ℝ =>
            Real.exp (y * u - y ^ 3 / 12)).aestronglyMeasurable).restrict
      · filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
        simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        rw [mul_comm]
        gcongr
        have : y * u - y ^ 3 / 12 ≤ -y ^ 3 / 48 := by
          have : y * u ≤ y * (y ^ 2 / 16) := mul_le_mul_of_nonneg_left hu.out hy0.le
          linarith only [this]
        exact this
    have hnorm : ‖y ^ (2 * p - 1 / 2 : ℝ) * ∫ u in Iic (y ^ 2 / 16), H u * Real.exp (y * u - y ^ 3 / 12)‖ =
        y ^ (2 * p - 1 / 2 : ℝ) * ‖∫ u in Iic (y ^ 2 / 16), H u * Real.exp (y * u - y ^ 3 / 12)‖ := by
      rw [norm_mul, Real.norm_of_nonneg (by positivity)]
    rw [hnorm]
    have hint_bd : ‖∫ u in Iic (y ^ 2 / 16), H u * Real.exp (y * u - y ^ 3 / 12)‖ ≤
        L1 * Real.exp (-y / 48) := by
      calc ‖∫ u in Iic (y ^ 2 / 16), H u * Real.exp (y * u - y ^ 3 / 12)‖
          ≤ ∫ u in Iic (y ^ 2 / 16), ‖H u * Real.exp (y * u - y ^ 3 / 12)‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ u in Iic (y ^ 2 / 16), |H u * Real.exp (y * u - y ^ 3 / 12)| := by
            simp only [Real.norm_eq_abs]
        _ ≤ ∫ u in Iic (y ^ 2 / 16), |H u| * Real.exp (-y / 48) := by
            refine setIntegral_mono_on ?_ (hH_int.abs.mul_const _).integrableOn measurableSet_Iic fun u hu => ?_
            · exact h_iic_int.abs
            · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
              gcongr
              have h1 : y * u ≤ y * (y ^ 2 / 16) := mul_le_mul_of_nonneg_left hu hy0.le
              have hy2 : 1 ≤ y ^ 2 := by nlinarith only [hy1]
              have h2 : y ≤ y ^ 3 := by nlinarith only [hy1, hy2]
              linarith only [h1, h2]
        _ ≤ ∫ u : ℝ, |H u| * Real.exp (-y / 48) :=
            setIntegral_le_integral (hH_int.abs.mul_const _) (ae_of_all _ fun _ => by positivity)
        _ = L1 * Real.exp (-y / 48) := by
            rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_left hint_bd (by positivity)
  have h_ioi_lim : Tendsto (fun y : ℝ => y ^ (2 * p - 1 / 2 : ℝ) *
      ∫ u in Ioi (y ^ 2 / 16), H u * Real.exp (y * u - y ^ 3 / 12)) atTop
      (𝓝 (C * 2 ^ (2 * p) * √π)) := by
    rw [h_gauss_eval] at h_main_int_lim
    exact h_main_int_lim.congr' (eventually_ge_atTop Y₀ |>.mono fun y hy => (hG_facts y hy).2.1.symm)
  have h_sum_lim : Tendsto (fun y : ℝ =>
      (y ^ (2 * p - 1 / 2 : ℝ) * ∫ u in Iic (y ^ 2 / 16), H u * Real.exp (y * u - y ^ 3 / 12)) +
      (y ^ (2 * p - 1 / 2 : ℝ) * ∫ u in Ioi (y ^ 2 / 16), H u * Real.exp (y * u - y ^ 3 / 12))) atTop
      (𝓝 (0 + C * 2 ^ (2 * p) * √π)) :=
    h_tail_lim.add h_ioi_lim
  rw [zero_add] at h_sum_lim
  refine h_sum_lim.congr' ?_
  filter_upwards [eventually_ge_atTop Y₀] with y hy
  obtain ⟨_, _, hy0⟩ := hU_le_Y0 y hy
  have h_iic : IntegrableOn (fun u : ℝ => H u * Real.exp (y * u - y ^ 3 / 12)) (Iic (y ^ 2 / 16)) := by
    refine (hH_int.norm.const_mul (Real.exp (-y ^ 3 / 48))).integrableOn.mono' ?_ ?_
    · exact (hH_int.aestronglyMeasurable.mul (by fun_prop : Continuous fun u : ℝ =>
          Real.exp (y * u - y ^ 3 / 12)).aestronglyMeasurable).restrict
    · filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      rw [mul_comm]
      gcongr
      have hu' : u ≤ y ^ 2 / 16 := hu
      have : y * u ≤ y * (y ^ 2 / 16) := mul_le_mul_of_nonneg_left hu' hy0.le
      linarith only [this]
  have h_ioi := (hG_facts y hy).1
  have h_split : ∫ u : ℝ, H u * Real.exp (y * u - y ^ 3 / 12) =
      (∫ u in Iic (y ^ 2 / 16), H u * Real.exp (y * u - y ^ 3 / 12)) +
      (∫ u in Ioi (y ^ 2 / 16), H u * Real.exp (y * u - y ^ 3 / 12)) := by
    have hu := MeasureTheory.setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi h_iic h_ioi
    rw [Set.Iic_union_Ioi, setIntegral_univ] at hu
    exact hu
  dsimp [airyLaplace]
  rw [show Real.exp (-(y ^ 3) / 12) * ∫ u : ℝ, H u * Real.exp (y * u) =
      ∫ u : ℝ, H u * Real.exp (y * u - y ^ 3 / 12) by
    rw [← integral_const_mul]
    congr 1; ext u
    rw [show y * u - y ^ 3 / 12 = -(y ^ 3) / 12 + y * u by ring, Real.exp_add]; ring]
  rw [h_split, mul_add]

/-! ### Positive-axis asymptotic for `HasGenRationalAiryCoeffs` -/

private lemma airyAiLead_ofReal_pos {u : ℝ} (hu : 0 < u) :
    airyAiLead (u : ℂ) =
      ((1 / (2 * √π * u ^ (1 / 4 : ℝ)) * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) : ℝ) : ℂ) := by
  unfold airyAiLead airyLead
  have hc12 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hu_c : ((u : ℂ) ^ (1 / 2 : ℂ)) = ((√u : ℝ) : ℂ) := by
    rw [hc12, ← Complex.ofReal_cpow hu.le, ← Real.sqrt_eq_rpow]
  have hsqrt_pos : 0 < √u := Real.sqrt_pos.mpr hu
  have hpow3 : ((√u : ℝ) : ℂ) ^ 3 = ((u ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
    norm_cast
    calc √u ^ 3 = (u ^ (1 / 2 : ℝ)) ^ 3 := by rw [Real.sqrt_eq_rpow]
      _ = u ^ (3 / 2 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]; norm_num
  have hexp : Complex.exp (-(2 / 3 : ℂ) * ((√u : ℝ) : ℂ) ^ 3) =
      ((Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [hpow3, show -(2 / 3 : ℂ) * ((u ^ (3 / 2 : ℝ) : ℝ) : ℂ) =
      ((-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_exp]
  have hdiv : ((π : ℂ) / ((√u : ℝ) : ℂ)) ^ (1 / 2 : ℂ) =
      ((√π / u ^ (1 / 4 : ℝ) : ℝ) : ℂ) := by
    rw [hc12, ← Complex.ofReal_div, ← Complex.ofReal_cpow (by positivity)]
    congr 1
    rw [Real.div_rpow Real.pi_pos.le hsqrt_pos.le, ← Real.sqrt_eq_rpow,
      Real.sqrt_eq_rpow u, ← Real.rpow_mul hu.le]
    norm_num
  rw [hu_c, hexp, hdiv,
    show (1 / (2 * (π : ℂ))) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring]
  norm_cast
  have hsq : √π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  field_simp [Real.pi_pos.ne', (Real.sqrt_pos.mpr Real.pi_pos).ne',
    (Real.rpow_pos_of_pos hu (1 / 4 : ℝ)).ne']
  rw [hsq]

private lemma airyAiDerivLead_ofReal_pos {u : ℝ} (hu : 0 < u) :
    airyAiDerivLead (u : ℂ) =
      ((-((u ^ (1 / 2 : ℝ)) *
        (1 / (2 * √π * u ^ (1 / 4 : ℝ)) * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)))) : ℝ) : ℂ) := by
  unfold airyAiDerivLead
  have hu_c : ((u : ℂ) ^ (1 / 2 : ℂ)) = ((u ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hu.le]
  rw [hu_c, airyAiLead_ofReal_pos hu]
  push_cast; ring

/-- Positive-axis Airy–WKB asymptotic `(eq:ce-beta-plus)` for any `HasGenRationalAiryCoeffs F β₀₀ β₁₁`:
for `u ≥ R_* + 2`, `F(u) = e^{-4u^{3/2}/3} ((β_+(F)/(4π)) u^{-3/2} + O(u^{-2}))`. -/
theorem HasGenRationalAiryCoeffs.pos_axis_asymptotic {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF : HasGenRationalAiryCoeffs F β₀₀ β₁₁) :
    ∃ U R_err : ℝ, 1 ≤ U ∧ 0 ≤ R_err ∧ ∀ u : ℝ, U ≤ u →
      |(F (u : ℂ)).re - Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) *
        ((airyBetaPlus F / (4 * π)) * u ^ (-(3 / 2 : ℝ)))| ≤
          R_err * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * u ^ (-2 : ℝ) := by
  have hbplus : airyBetaPlus F = -β₀₀ + β₁₁ := (HasGenRationalAiryCoeffs.beta_eq hF).2.2.2
  obtain ⟨_, R_star, C, P00, Q00, P01, Q01, P11, Q11, hR4, hC0, _, _, _, hQ00, hQ01, hQ11,
    hrep, hasym⟩ := hF
  set U : ℝ := R_star + 2
  have hU6 : 6 ≤ U := by dsimp [U]; linarith only [hR4]
  have hU1 : 1 ≤ U := by linarith only [hU6]
  let R_err : ℝ := (6 * C + |β₀₀| + |β₁₁| + 1) / (4 * π) + 1
  refine ⟨U, R_err, hU1, by positivity, fun u hu => ?_⟩
  have hu1 : 1 ≤ u := le_trans hU1 hu
  have hu0 : 0 < u := by linarith only [hu1]
  have hnu : ‖(u : ℂ)‖ = u := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0]
  have hnneg : ‖((-u : ℝ) : ℂ)‖ = u := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hu0]
  have hgt : R_star < ‖(u : ℂ)‖ := by rw [hnu]; dsimp [U] at hu; linarith only [hu]
  have hge : R_star + 2 ≤ ‖((-u : ℝ) : ℂ)‖ := by rw [hnneg]; exact hu
  have hFu := hrep (u : ℂ) hgt
  obtain ⟨hb00, hb01, hb11⟩ := hasym ((-u : ℝ) : ℂ) hge
  have hneg_eq : -((-u : ℝ) : ℂ) = (u : ℂ) := by push_cast; ring
  rw [hneg_eq] at hb00 hb01 hb11
  have hdiv_real : ∀ P Q : ℝ[X], (∀ z : ℂ, Polynomial.aeval z Q = 0 → z.im = 0 ∧ ‖z‖ ≤ R_star) →
      Polynomial.aeval (u : ℂ) P / Polynomial.aeval (u : ℂ) Q =
        (((Polynomial.eval u P / Polynomial.eval u Q : ℝ)) : ℂ) := fun P Q _ => by
    change Polynomial.aeval (algebraMap ℝ ℂ u) P / Polynomial.aeval (algebraMap ℝ ℂ u) Q = _
    rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
      Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
    push_cast; rfl
  set r00 : ℝ := P00.eval u / Q00.eval u
  set r01 : ℝ := P01.eval u / Q01.eval u
  set r11 : ℝ := P11.eval u / Q11.eval u
  have hFu_re : (F (u : ℂ)).re = r00 * airyAi u ^ 2 + r01 * (airyAi u * airyAi' u) +
      r11 * airyAi' u ^ 2 := by
    rw [hFu, hdiv_real P00 Q00 hQ00, hdiv_real P01 Q01 hQ01, hdiv_real P11 Q11 hQ11,
      airyAiC_ofReal, deriv_airyAiC_ofReal]
    have hcast : (((r00 * airyAi u ^ 2 + r01 * (airyAi u * airyAi' u) +
        r11 * airyAi' u ^ 2 : ℝ) : ℂ)) =
        (r00 : ℂ) * (airyAi u : ℂ) ^ 2 + (r01 : ℂ) * ((airyAi u : ℂ) * (airyAi' u : ℂ)) +
        (r11 : ℂ) * (airyAi' u : ℂ) ^ 2 := by push_cast; ring
    rw [← hcast, Complex.ofReal_re]
  have hr00 : |r00 + β₀₀ * u⁻¹| ≤ C * u ^ (-2 : ℝ) := by
    have h1 : (β₀₀ : ℂ) * ((-u : ℝ) : ℂ)⁻¹ = ((-β₀₀ * u⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [hdiv_real P00 Q00 hQ00, h1, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      hnneg] at hb00
    simpa [sub_neg_eq_add, neg_mul] using hb00
  have hr01 : |r01| ≤ C * u ^ (-2 : ℝ) := by
    rw [hdiv_real P01 Q01 hQ01, Complex.norm_real, Real.norm_eq_abs, hnneg] at hb01
    exact hb01
  have hr11 : |r11 - β₁₁ * u ^ (-2 : ℝ)| ≤ C * u ^ (-3 : ℝ) := by
    have h1 : (β₁₁ : ℂ) * (((-u : ℝ) : ℂ) ^ 2)⁻¹ = ((β₁₁ * u ^ (-2 : ℝ) : ℝ) : ℂ) := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hu0.le, Real.rpow_natCast]
      push_cast; ring
    rw [hdiv_real P11 Q11 hQ11, h1, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      hnneg] at hb11
    exact hb11
  set L_u : ℝ := 1 / (2 * √π * u ^ (1 / 4 : ℝ)) * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ))
  have hLu_pos : 0 < L_u := by positivity
  have hsec_re : (2 * (1 : ℝ) ^ 2 - 1) * ‖(u : ℂ)‖ ≤ ((u : ℂ)).re := by
    rw [hnu, Complex.ofReal_re]; nlinarith only [hu0]
  have hAi_err : |airyAi u - L_u| ≤ (5 / 48 : ℝ) * u ^ (-(3 / 2 : ℝ)) * L_u := by
    have h := airyAiC_sector_asymptotic (z := (u : ℂ)) (s := 1) one_pos (by rw [hnu]; exact hu0) hsec_re
    rw [airyAiC_ofReal, airyAiLead_ofReal_pos hu0, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, hnu] at h
    have hnL : ‖((1 / (2 * √π * u ^ (1 / 4 : ℝ)) * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) : ℝ) : ℂ)‖ = L_u := by
      rw [Complex.norm_real, Real.norm_of_nonneg hLu_pos.le]
    rw [hnL] at h
    refine h.trans_eq ?_
    rw [Real.sqrt_one, one_pow, mul_one, one_mul, div_eq_mul_inv, ← Real.rpow_neg hu0.le]
  have hAi'_err : |airyAi' u + u ^ (1 / 2 : ℝ) * L_u| ≤
      (17 / 48 : ℝ) * u ^ (-(3 / 2 : ℝ)) * (u ^ (1 / 2 : ℝ) * L_u) := by
    have h := deriv_airyAiC_sector_asymptotic (z := (u : ℂ)) (s := 1) one_pos le_rfl
      (by rw [hnu]; exact hu0) hsec_re
    rw [deriv_airyAiC_ofReal, airyAiDerivLead_ofReal_pos hu0, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, sub_neg_eq_add, hnu] at h
    have hnL' : ‖((-((u ^ (1 / 2 : ℝ)) * (1 / (2 * √π * u ^ (1 / 4 : ℝ)) *
        Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)))) : ℝ) : ℂ)‖ = u ^ (1 / 2 : ℝ) * L_u := by
      rw [Complex.norm_real, norm_neg, Real.norm_of_nonneg (mul_nonneg (by positivity) hLu_pos.le)]
    rw [hnL'] at h
    refine h.trans_eq ?_
    rw [Real.sqrt_one, one_pow, mul_one, one_mul, div_eq_mul_inv, ← Real.rpow_neg hu0.le]
  have hu32_le1 : u ^ (-(3 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu1 (by norm_num)
  have hAi_bd : |airyAi u| ≤ (53 / 48 : ℝ) * L_u := by
    have htri := abs_add_le (airyAi u - L_u) L_u
    rw [sub_add_cancel, abs_of_pos hLu_pos] at htri
    nlinarith only [htri, hAi_err, hu32_le1, hLu_pos]
  have hAi'_bd : |airyAi' u| ≤ (65 / 48 : ℝ) * (u ^ (1 / 2 : ℝ) * L_u) := by
    have htri := abs_add_le (airyAi' u + u ^ (1 / 2 : ℝ) * L_u) (-(u ^ (1 / 2 : ℝ) * L_u))
    rw [add_neg_cancel_right, abs_neg, abs_of_pos (mul_pos (by positivity) hLu_pos)] at htri
    have h1 : (17 / 48 : ℝ) * u ^ (-(3 / 2 : ℝ)) * (u ^ (1 / 2 : ℝ) * L_u) ≤
        (17 / 48 : ℝ) * 1 * (u ^ (1 / 2 : ℝ) * L_u) := by gcongr
    linarith only [htri, hAi'_err, h1]
  have hAi_sq : |airyAi u ^ 2 - L_u ^ 2| ≤ (1 / 3 : ℝ) * u ^ (-(3 / 2 : ℝ)) * L_u ^ 2 := by
    rw [show airyAi u ^ 2 - L_u ^ 2 = (airyAi u - L_u) * (airyAi u + L_u) by ring, abs_mul]
    have hsum : |airyAi u + L_u| ≤ (101 / 48 : ℝ) * L_u := by
      have htri := abs_add_le (airyAi u) L_u
      rw [abs_of_pos hLu_pos] at htri
      linarith only [htri, hAi_bd]
    calc |airyAi u - L_u| * |airyAi u + L_u|
        ≤ ((5 / 48 : ℝ) * u ^ (-(3 / 2 : ℝ)) * L_u) * ((101 / 48 : ℝ) * L_u) :=
          mul_le_mul hAi_err hsum (abs_nonneg _) (by positivity)
      _ = (505 / 2304 : ℝ) * (u ^ (-(3 / 2 : ℝ)) * L_u ^ 2) := by ring
      _ ≤ (1 / 3 : ℝ) * (u ^ (-(3 / 2 : ℝ)) * L_u ^ 2) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (1 / 3 : ℝ) * u ^ (-(3 / 2 : ℝ)) * L_u ^ 2 := by ring
  have hAi'_sq : |airyAi' u ^ 2 - u * L_u ^ 2| ≤ u ^ (-(3 / 2 : ℝ)) * (u * L_u ^ 2) := by
    have hu_sq : (u ^ (1 / 2 : ℝ) * L_u) ^ 2 = u * L_u ^ 2 := by
      rw [mul_pow, ← Real.rpow_natCast (u ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hu0.le,
        show (1 / 2 : ℝ) * (2 : ℕ) = 1 by norm_num, Real.rpow_one]
    rw [← hu_sq, show airyAi' u ^ 2 - (u ^ (1 / 2 : ℝ) * L_u) ^ 2 =
        (airyAi' u + u ^ (1 / 2 : ℝ) * L_u) * (airyAi' u - u ^ (1 / 2 : ℝ) * L_u) by ring, abs_mul]
    have hsub : |airyAi' u - u ^ (1 / 2 : ℝ) * L_u| ≤ (113 / 48 : ℝ) * (u ^ (1 / 2 : ℝ) * L_u) := by
      have htri := abs_sub_le (airyAi' u) 0 (u ^ (1 / 2 : ℝ) * L_u)
      rw [sub_zero, zero_sub, abs_neg, abs_of_pos (mul_pos (by positivity) hLu_pos)] at htri
      linarith only [htri, hAi'_bd]
    calc |airyAi' u + u ^ (1 / 2 : ℝ) * L_u| * |airyAi' u - u ^ (1 / 2 : ℝ) * L_u|
        ≤ ((17 / 48 : ℝ) * u ^ (-(3 / 2 : ℝ)) * (u ^ (1 / 2 : ℝ) * L_u)) *
            ((113 / 48 : ℝ) * (u ^ (1 / 2 : ℝ) * L_u)) :=
          mul_le_mul hAi'_err hsub (abs_nonneg _) (by positivity)
      _ = (1921 / 2304 : ℝ) * (u ^ (-(3 / 2 : ℝ)) * (u ^ (1 / 2 : ℝ) * L_u) ^ 2) := by ring
      _ ≤ 1 * (u ^ (-(3 / 2 : ℝ)) * (u ^ (1 / 2 : ℝ) * L_u) ^ 2) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = u ^ (-(3 / 2 : ℝ)) * (u ^ (1 / 2 : ℝ) * L_u) ^ 2 := one_mul _
  set E_u : ℝ := Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ))
  have hE_pos : 0 < E_u := Real.exp_pos _
  have hLu_sq : L_u ^ 2 = (4 * π)⁻¹ * u ^ (-(1 / 2 : ℝ)) * E_u := by
    dsimp [L_u, E_u]
    have hu14 : (u ^ (1 / 4 : ℝ)) ^ 2 = u ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast (u ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hu0.le]
      norm_num
    rw [mul_pow, one_div, inv_pow, mul_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le, hu14,
      ← Real.exp_nat_mul,
      show ((2 : ℕ) : ℝ) * (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) = -(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ) by ring,
      Real.rpow_neg hu0.le]
    ring
  have hr00_abs : |r00| ≤ (|β₀₀| + C) * u⁻¹ := by
    have htri := abs_add_le (r00 + β₀₀ * u⁻¹) (-(β₀₀ * u⁻¹))
    rw [add_neg_cancel_right, abs_neg, abs_mul, abs_of_pos (inv_pos.mpr hu0)] at htri
    have hu2_le : u ^ (-2 : ℝ) ≤ u⁻¹ :=
      (Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num : (-2 : ℝ) ≤ -1)).trans_eq (Real.rpow_neg_one u)
    nlinarith only [htri, hr00, hu2_le, hC0]
  have hr11_abs : |r11| ≤ (|β₁₁| + C) * u ^ (-2 : ℝ) := by
    have htri := abs_add_le (r11 - β₁₁ * u ^ (-2 : ℝ)) (β₁₁ * u ^ (-2 : ℝ))
    rw [sub_add_cancel, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hu0 _)] at htri
    have hu3_le : u ^ (-3 : ℝ) ≤ u ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
    nlinarith only [htri, hr11, hu3_le, hC0]
  -- Bound the three terms of `F(u) - β_+(F)/(4π) * u^{-3/2} * E_u`.
  have hT00 : |r00 * airyAi u ^ 2 - (-β₀₀ / (4 * π)) * u ^ (-(3 / 2 : ℝ)) * E_u| ≤
      (C + |β₀₀| + C) * u ^ (-2 : ℝ) * ((4 * π)⁻¹ * E_u) := by
    have hid1 : (-β₀₀ / (4 * π)) * u ^ (-(3 / 2 : ℝ)) * E_u = (-β₀₀ * u⁻¹) * L_u ^ 2 := by
      rw [hLu_sq, show u ^ (-(3 / 2 : ℝ)) = u⁻¹ * u ^ (-(1 / 2 : ℝ)) by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hu0]; congr 1; ring]
      ring
    have hid2 : r00 * airyAi u ^ 2 - (-β₀₀ * u⁻¹) * L_u ^ 2 =
        (r00 + β₀₀ * u⁻¹) * L_u ^ 2 + r00 * (airyAi u ^ 2 - L_u ^ 2) := by ring
    rw [hid1, hid2]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos (sq_pos_of_pos hLu_pos)]
    have hA : |r00 + β₀₀ * u⁻¹| * L_u ^ 2 ≤ C * u ^ (-2 : ℝ) * ((4 * π)⁻¹ * E_u) := by
      rw [hLu_sq]
      have h12 : u ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu1 (by norm_num)
      calc |r00 + β₀₀ * u⁻¹| * ((4 * π)⁻¹ * u ^ (-(1 / 2 : ℝ)) * E_u)
          ≤ (C * u ^ (-2 : ℝ)) * ((4 * π)⁻¹ * 1 * E_u) := by gcongr
        _ = C * u ^ (-2 : ℝ) * ((4 * π)⁻¹ * E_u) := by ring
    have hB : |r00| * |airyAi u ^ 2 - L_u ^ 2| ≤ (|β₀₀| + C) * u ^ (-2 : ℝ) * ((4 * π)⁻¹ * E_u) := by
      have hpow : u⁻¹ * u ^ (-(3 / 2 : ℝ)) * u ^ (-(1 / 2 : ℝ)) = u ^ (-3 : ℝ) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hu0, ← Real.rpow_add hu0]; congr 1; ring
      have hu3_le : u ^ (-3 : ℝ) ≤ u ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
      calc |r00| * |airyAi u ^ 2 - L_u ^ 2|
          ≤ ((|β₀₀| + C) * u⁻¹) * ((1 / 3 : ℝ) * u ^ (-(3 / 2 : ℝ)) * L_u ^ 2) :=
            mul_le_mul hr00_abs hAi_sq (abs_nonneg _) (by positivity)
        _ = (1 / 3 : ℝ) * (|β₀₀| + C) * (u⁻¹ * u ^ (-(3 / 2 : ℝ)) * u ^ (-(1 / 2 : ℝ))) * ((4 * π)⁻¹ * E_u) := by
            rw [hLu_sq]; ring
        _ ≤ 1 * (|β₀₀| + C) * u ^ (-2 : ℝ) * ((4 * π)⁻¹ * E_u) := by
            rw [hpow]; gcongr; norm_num
        _ = (|β₀₀| + C) * u ^ (-2 : ℝ) * ((4 * π)⁻¹ * E_u) := by ring
    linarith only [hA, hB]
  have hT01 : |r01 * (airyAi u * airyAi' u)| ≤ (2 * C) * u ^ (-2 : ℝ) * ((4 * π)⁻¹ * E_u) := by
    rw [abs_mul, abs_mul]
    have hprod : |airyAi u| * |airyAi' u| ≤ 2 * u ^ (1 / 2 : ℝ) * L_u ^ 2 := by
      calc |airyAi u| * |airyAi' u|
          ≤ ((53 / 48 : ℝ) * L_u) * ((65 / 48 : ℝ) * (u ^ (1 / 2 : ℝ) * L_u)) :=
            mul_le_mul hAi_bd hAi'_bd (abs_nonneg _) (by positivity)
        _ = (3445 / 2304 : ℝ) * u ^ (1 / 2 : ℝ) * L_u ^ 2 := by ring
        _ ≤ 2 * u ^ (1 / 2 : ℝ) * L_u ^ 2 := by gcongr; norm_num
    have hpow : u ^ (-2 : ℝ) * u ^ (1 / 2 : ℝ) * u ^ (-(1 / 2 : ℝ)) = u ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hu0, ← Real.rpow_add hu0]; congr 1; ring
    calc |r01| * (|airyAi u| * |airyAi' u|)
        ≤ (C * u ^ (-2 : ℝ)) * (2 * u ^ (1 / 2 : ℝ) * L_u ^ 2) :=
          mul_le_mul hr01 hprod (by positivity) (by positivity)
      _ = 2 * C * (u ^ (-2 : ℝ) * u ^ (1 / 2 : ℝ) * u ^ (-(1 / 2 : ℝ))) * ((4 * π)⁻¹ * E_u) := by
          rw [hLu_sq]; ring
      _ = (2 * C) * u ^ (-2 : ℝ) * ((4 * π)⁻¹ * E_u) := by rw [hpow]
  have hT11 : |r11 * airyAi' u ^ 2 - (β₁₁ / (4 * π)) * u ^ (-(3 / 2 : ℝ)) * E_u| ≤
      (C + |β₁₁| + C) * u ^ (-2 : ℝ) * ((4 * π)⁻¹ * E_u) := by
    have hid1 : (β₁₁ / (4 * π)) * u ^ (-(3 / 2 : ℝ)) * E_u = (β₁₁ * u ^ (-2 : ℝ)) * (u * L_u ^ 2) := by
      rw [hLu_sq]
      have hpow : u ^ (-2 : ℝ) * u * u ^ (-(1 / 2 : ℝ)) = u ^ (-(3 / 2 : ℝ)) := by
        nth_rw 2 [← Real.rpow_one u]
        rw [← Real.rpow_add hu0, ← Real.rpow_add hu0]; congr 1; ring
      calc (β₁₁ / (4 * π)) * u ^ (-(3 / 2 : ℝ)) * E_u
          = β₁₁ * u ^ (-(3 / 2 : ℝ)) * ((4 * π)⁻¹ * E_u) := by ring
        _ = β₁₁ * (u ^ (-2 : ℝ) * u * u ^ (-(1 / 2 : ℝ))) * ((4 * π)⁻¹ * E_u) := by rw [hpow]
        _ = (β₁₁ * u ^ (-2 : ℝ)) * (u * ((4 * π)⁻¹ * u ^ (-(1 / 2 : ℝ)) * E_u)) := by ring
    have hid2 : r11 * airyAi' u ^ 2 - (β₁₁ * u ^ (-2 : ℝ)) * (u * L_u ^ 2) =
        (r11 - β₁₁ * u ^ (-2 : ℝ)) * (u * L_u ^ 2) + r11 * (airyAi' u ^ 2 - u * L_u ^ 2) := by ring
    rw [hid1, hid2]
    refine (abs_add_le _ _).trans ?_
    have hA : |(r11 - β₁₁ * u ^ (-2 : ℝ)) * (u * L_u ^ 2)| ≤ C * u ^ (-2 : ℝ) * ((4 * π)⁻¹ * E_u) := by
      rw [abs_mul, abs_of_pos (mul_pos hu0 (sq_pos_of_pos hLu_pos))]
      have hpow : u ^ (-3 : ℝ) * u * u ^ (-(1 / 2 : ℝ)) = u ^ (-(5 / 2 : ℝ)) := by
        nth_rw 2 [← Real.rpow_one u]
        rw [← Real.rpow_add hu0, ← Real.rpow_add hu0]; congr 1; ring
      have hu52 : u ^ (-(5 / 2 : ℝ)) ≤ u ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
      calc |r11 - β₁₁ * u ^ (-2 : ℝ)| * (u * L_u ^ 2)
          ≤ (C * u ^ (-3 : ℝ)) * (u * ((4 * π)⁻¹ * u ^ (-(1 / 2 : ℝ)) * E_u)) := by
            rw [hLu_sq]; gcongr
        _ = C * (u ^ (-3 : ℝ) * u * u ^ (-(1 / 2 : ℝ))) * ((4 * π)⁻¹ * E_u) := by ring
        _ ≤ C * u ^ (-2 : ℝ) * ((4 * π)⁻¹ * E_u) := by rw [hpow]; gcongr
    have hB : |r11 * (airyAi' u ^ 2 - u * L_u ^ 2)| ≤
        (|β₁₁| + C) * u ^ (-2 : ℝ) * ((4 * π)⁻¹ * E_u) := by
      rw [abs_mul]
      have hpow : u ^ (-2 : ℝ) * u ^ (-(3 / 2 : ℝ)) * u * u ^ (-(1 / 2 : ℝ)) = u ^ (-3 : ℝ) := by
        nth_rw 3 [← Real.rpow_one u]
        rw [← Real.rpow_add hu0, ← Real.rpow_add hu0, ← Real.rpow_add hu0]; congr 1; ring
      have hu3 : u ^ (-3 : ℝ) ≤ u ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
      calc |r11| * |airyAi' u ^ 2 - u * L_u ^ 2|
          ≤ ((|β₁₁| + C) * u ^ (-2 : ℝ)) * (u ^ (-(3 / 2 : ℝ)) * (u * L_u ^ 2)) :=
            mul_le_mul hr11_abs hAi'_sq (abs_nonneg _) (by positivity)
        _ = (|β₁₁| + C) * (u ^ (-2 : ℝ) * u ^ (-(3 / 2 : ℝ)) * u * u ^ (-(1 / 2 : ℝ))) * ((4 * π)⁻¹ * E_u) := by
            rw [hLu_sq]; ring
        _ ≤ (|β₁₁| + C) * u ^ (-2 : ℝ) * ((4 * π)⁻¹ * E_u) := by rw [hpow]; gcongr
    linarith only [hA, hB]
  rw [hbplus, hFu_re]
  rw [show E_u * ((-β₀₀ + β₁₁) / (4 * π) * u ^ (-(3 / 2 : ℝ))) =
      (-β₀₀ / (4 * π)) * u ^ (-(3 / 2 : ℝ)) * E_u + (β₁₁ / (4 * π)) * u ^ (-(3 / 2 : ℝ)) * E_u by ring,
    show r00 * airyAi u ^ 2 + r01 * (airyAi u * airyAi' u) + r11 * airyAi' u ^ 2 -
      ((-β₀₀ / (4 * π)) * u ^ (-(3 / 2 : ℝ)) * E_u + (β₁₁ / (4 * π)) * u ^ (-(3 / 2 : ℝ)) * E_u) =
      (r00 * airyAi u ^ 2 - (-β₀₀ / (4 * π)) * u ^ (-(3 / 2 : ℝ)) * E_u) +
      r01 * (airyAi u * airyAi' u) +
      (r11 * airyAi' u ^ 2 - (β₁₁ / (4 * π)) * u ^ (-(3 / 2 : ℝ)) * E_u) by ring]
  have htri : |(r00 * airyAi u ^ 2 - (-β₀₀ / (4 * π)) * u ^ (-(3 / 2 : ℝ)) * E_u) +
        r01 * (airyAi u * airyAi' u) +
        (r11 * airyAi' u ^ 2 - (β₁₁ / (4 * π)) * u ^ (-(3 / 2 : ℝ)) * E_u)| ≤
      |r00 * airyAi u ^ 2 - (-β₀₀ / (4 * π)) * u ^ (-(3 / 2 : ℝ)) * E_u| +
        |r01 * (airyAi u * airyAi' u)| +
        |r11 * airyAi' u ^ 2 - (β₁₁ / (4 * π)) * u ^ (-(3 / 2 : ℝ)) * E_u| :=
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  refine htri.trans ?_
  calc |r00 * airyAi u ^ 2 - (-β₀₀ / (4 * π)) * u ^ (-(3 / 2 : ℝ)) * E_u| +
        |r01 * (airyAi u * airyAi' u)| +
        |r11 * airyAi' u ^ 2 - (β₁₁ / (4 * π)) * u ^ (-(3 / 2 : ℝ)) * E_u|
      ≤ (C + |β₀₀| + C) * u ^ (-2 : ℝ) * ((4 * π)⁻¹ * E_u) +
        (2 * C) * u ^ (-2 : ℝ) * ((4 * π)⁻¹ * E_u) +
        (C + |β₁₁| + C) * u ^ (-2 : ℝ) * ((4 * π)⁻¹ * E_u) := add_le_add (add_le_add hT00 hT01) hT11
    _ = ((6 * C + |β₀₀| + |β₁₁|) / (4 * π)) * E_u * u ^ (-2 : ℝ) := by ring
    _ ≤ R_err * E_u * u ^ (-2 : ℝ) := by
        gcongr
        dsimp [R_err]
        linarith only [div_le_div_of_nonneg_right (by linarith only [hC0, abs_nonneg β₀₀, abs_nonneg β₁₁] :
          6 * C + |β₀₀| + |β₁₁| ≤ 6 * C + |β₀₀| + |β₁₁| + 1) (by positivity : 0 ≤ 4 * π)]

/-- Large-height Laplace asymptotic for `F ∈ \mathcal{R}_{\mathrm{Ai}}^{\mathrm{gen}}`:
`y^{5/2} \mathscr{L}_y(\operatorname{Re} F) → \beta_+(F) \cdot (2 / √π)` as `y → ∞`. -/
theorem airyLaplace_genRational_tendsto {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF : HasGenRationalAiryCoeffs F β₀₀ β₁₁) :
    Tendsto (fun y : ℝ => y ^ (5 / 2 : ℝ) * airyLaplace (fun u => (F (u : ℂ)).re) y) atTop
      (𝓝 (airyBetaPlus F * (2 / √π))) := by
  have hF_in : InAiryClass F := hF.1
  have hF_re_int : Integrable (fun u : ℝ => (F (u : ℂ)).re) :=
    Complex.reCLM.integrable_comp hF_in.2.1
  obtain ⟨U, R_err, hU, hR, hasym⟩ := hF.pos_axis_asymptotic
  have hlim := airyLaplace_tendsto_of_asymptotic (fun u => (F (u : ℂ)).re) hF_re_int
    (3 / 2) (1 / 2) (airyBetaPlus F / (4 * π)) (by norm_num) U hU R_err hR
    (fun u hu => (hasym u hu).trans_eq (by rw [show -(3 / 2 : ℝ) - 1 / 2 = (-2 : ℝ) by norm_num]))
  have hp_eq : (2 * (3 / 2 : ℝ) - 1 / 2 : ℝ) = 5 / 2 := by norm_num
  have hval_eq : (airyBetaPlus F / (4 * π)) * 2 ^ (2 * (3 / 2 : ℝ)) * √π =
      airyBetaPlus F * (2 / √π) := by
    rw [show (2 * (3 / 2 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hsq : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
    field_simp [Real.pi_pos.ne', (Real.sqrt_pos.mpr Real.pi_pos).ne']
    rw [show √π ^ 2 = √π * √π from sq _, hsq]; ring
  simpa only [hp_eq, hval_eq] using hlim

/-- Positive-tail lower bound for `F ∈ \mathcal{R}_{\mathrm{Ai}}^{\mathrm{gen}}` with `0 < \beta_+(F)`:
`d₀ (1 + y)^{-5/2} ≤ \mathscr{L}_y(\operatorname{Re} F)` for large `y`. -/
theorem HasGenRationalAiryCoeffs.airyLaplace_tail_pos_of_betaPlus_pos {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF : HasGenRationalAiryCoeffs F β₀₀ β₁₁) (hb : 0 < airyBetaPlus F) :
    ∃ y₀ c₀ : ℝ, 0 < y₀ ∧ 0 < c₀ ∧ ∀ y : ℝ, y₀ ≤ y →
      c₀ * (1 + y) ^ (-(5 / 2 : ℝ)) ≤ airyLaplace (fun u => (F (u : ℂ)).re) y := by
  have hlim := airyLaplace_genRational_tendsto hF
  have hL_pos : 0 < airyBetaPlus F * (2 / √π) := by positivity
  have hev := (hlim.eventually (Ioi_mem_nhds (by linarith only [hL_pos] :
    airyBetaPlus F * (2 / √π) / 2 < airyBetaPlus F * (2 / √π))))
  rw [eventually_atTop] at hev
  obtain ⟨Y, hY⟩ := hev
  refine ⟨max Y 1, airyBetaPlus F * (2 / √π) / 2, by positivity, by positivity, fun y hy => ?_⟩
  have hy1 : 1 ≤ y := (le_max_right _ _).trans hy
  have hy0 : 0 < y := by linarith only [hy1]
  have hy_bd := hY y ((le_max_left _ _).trans hy)
  have h_inv_mul : airyBetaPlus F * (2 / √π) / 2 * y ^ (-(5 / 2 : ℝ)) ≤
      airyLaplace (fun u => (F (u : ℂ)).re) y := by
    have hmul := mul_le_mul_of_nonneg_right hy_bd.le (Real.rpow_nonneg hy0.le (-(5 / 2 : ℝ)))
    have hid : y ^ (5 / 2 : ℝ) * airyLaplace (fun u => (F (u : ℂ)).re) y * y ^ (-(5 / 2 : ℝ)) =
        airyLaplace (fun u => (F (u : ℂ)).re) y := by
      rw [mul_comm (y ^ (5 / 2 : ℝ)), mul_assoc, ← Real.rpow_add hy0,
        show (5 / 2 : ℝ) + -(5 / 2 : ℝ) = 0 by norm_num, Real.rpow_zero, mul_one]
    linarith only [hmul, hid]
  have h_simpler : (1 + y) ^ (-(5 / 2 : ℝ)) ≤ y ^ (-(5 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hy0 (by linarith only) (by norm_num)
  calc (airyBetaPlus F * (2 / √π) / 2) * (1 + y) ^ (-(5 / 2 : ℝ))
      ≤ (airyBetaPlus F * (2 / √π) / 2) * y ^ (-(5 / 2 : ℝ)) := by gcongr
    _ ≤ airyLaplace (fun u => (F (u : ℂ)).re) y := h_inv_mul

/-- info: 'FormalResearch.SignUncertainty.airyLaplace_tendsto_of_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyLaplace_tendsto_of_asymptotic

/-- info: 'FormalResearch.SignUncertainty.airyLaplace_genRational_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyLaplace_genRational_tendsto

/-- info: 'FormalResearch.SignUncertainty.HasGenRationalAiryCoeffs.airyLaplace_tail_pos_of_betaPlus_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasGenRationalAiryCoeffs.airyLaplace_tail_pos_of_betaPlus_pos

end FormalResearch.SignUncertainty

