module

public import FormalResearch.Special.AiryRatioBounds
public import FormalResearch.Special.AiryBiReal
public import FormalResearch.Special.AiryValues

/-!
# The combinations `N = P·Ai + Q·Ai'`, `M = P·Bi + Q·Bi'`: algebra and the upper bound for `M - iN`

Setting of the CFT/PR240 notes (`GENERAL_THEOREMS.md` Lemma 1.0 and Lemma 1.0′ for constant `P, Q`; the Clark functions
`ψ_α = cos α Ai - sin α Ai'` are `P = cos α`, `Q = -sin α`): for real constants `P`, `Q`

* `airyNC P Q = P Ai + Q Ai'`, `airyMC P Q = P Bi + Q Bi'` (entire; real on `ℝ`), `airyNC'`, `airyMC'` their
  derivatives (`Ai'' = z Ai`);
* **Wronskian** `airyNC_wronskian`: `N M' - N' M = (P² - z Q²)/π` (`D = P² - z Q²`, the weight function of the Clark
  summation), hence at a zero `t` of `N`: `N'(t) M(t) = -D(t)/π` (`airyNC_mul_airyMC_at_zero`);
* **connection formula** for the derivative (DLMF 9.2.11 differentiated): `Bi' - i Ai' = 2 ε̄ ω² Ai'(ω² z)`
  (`airyBiC'_sub_I_mul`), hence `M - iN = 2 ε̄ (P Ai(ω² z) + Q ω² Ai'(ω² z))` (`airyMC_sub_I_mul`);
* **upper bound** (`airyMC_sub_I_mul_sq_le`): for `Im u ≥ 0`,
  `‖M(u) - i N(u)‖² e(u) ≤ 4 (3|P| + 5|Q|)² (1 + ‖u‖)^{1/2}` (from the envelopes (E1), (E1′) at `ω² u`, where
  `e(ω² u) = e(u)^{-1}`);
* conjugation symmetry `conj (N u) = N (conj u)`, `conj (M u) = M (conj u)` (`P`, `Q` real).

All proved (axiom-checked below).  The lower bound for `N` on good circles is `AiryCft2ComboBounds`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- `N = P Ai + Q Ai'` (`P`, `Q` real constants). -/
noncomputable def airyNC (P Q : ℝ) (z : ℂ) : ℂ := (P : ℂ) * airyAiC z + (Q : ℂ) * deriv airyAiC z

/-- `M = P Bi + Q Bi'`. -/
noncomputable def airyMC (P Q : ℝ) (z : ℂ) : ℂ := (P : ℂ) * airyBiC z + (Q : ℂ) * airyBiC' z

/-- `N' = P Ai' + Q z Ai`. -/
noncomputable def airyNC' (P Q : ℝ) (z : ℂ) : ℂ := (P : ℂ) * deriv airyAiC z + (Q : ℂ) * (z * airyAiC z)

/-- `M' = P Bi' + Q z Bi`. -/
noncomputable def airyMC' (P Q : ℝ) (z : ℂ) : ℂ := (P : ℂ) * airyBiC' z + (Q : ℂ) * (z * airyBiC z)

/-- The weight function `D = P² - z Q²`. -/
noncomputable def airyDC (P Q : ℝ) (z : ℂ) : ℂ := (P : ℂ) ^ 2 - z * (Q : ℂ) ^ 2

lemma hasDerivAt_airyNC (P Q : ℝ) (z : ℂ) : HasDerivAt (airyNC P Q) (airyNC' P Q z) z := by
  have h1 : HasDerivAt airyAiC (deriv airyAiC z) z := differentiable_airyAiC.differentiableAt.hasDerivAt
  have h2 := hasDerivAt_deriv_airyAiC z
  exact (h1.const_mul (P : ℂ)).add (h2.const_mul (Q : ℂ))

lemma hasDerivAt_airyMC (P Q : ℝ) (z : ℂ) : HasDerivAt (airyMC P Q) (airyMC' P Q z) z := by
  have h := isAirySol_airyBiC z
  exact (h.1.const_mul (P : ℂ)).add (h.2.const_mul (Q : ℂ))

lemma differentiable_airyNC (P Q : ℝ) : Differentiable ℂ (airyNC P Q) :=
  fun z => (hasDerivAt_airyNC P Q z).differentiableAt

lemma differentiable_airyMC (P Q : ℝ) : Differentiable ℂ (airyMC P Q) :=
  fun z => (hasDerivAt_airyMC P Q z).differentiableAt

lemma deriv_airyNC (P Q : ℝ) (z : ℂ) : deriv (airyNC P Q) z = airyNC' P Q z :=
  (hasDerivAt_airyNC P Q z).deriv

/-- **Wronskian**: `N M' - N' M = (P² - z Q²)/π`. -/
theorem airyNC_wronskian (P Q : ℝ) (z : ℂ) :
    airyNC P Q z * airyMC' P Q z - airyNC' P Q z * airyMC P Q z = airyDC P Q z * ((1 / π : ℝ) : ℂ) := by
  have hW := airyAiC_wronskian_airyBiC_eq z
  unfold airyNC airyMC' airyNC' airyMC airyDC
  linear_combination ((P : ℂ) ^ 2 - z * (Q : ℂ) ^ 2) * hW

/-- At a zero `t` of `N`: `N'(t) M(t) = -D(t)/π`. -/
theorem airyNC_mul_airyMC_at_zero {P Q : ℝ} {t : ℂ} (h : airyNC P Q t = 0) :
    airyNC' P Q t * airyMC P Q t = -(airyDC P Q t * ((1 / π : ℝ) : ℂ)) := by
  have := airyNC_wronskian P Q t
  rw [h, zero_mul, zero_sub] at this
  linear_combination -this

/-! ### Conjugation -/

lemma conj_airyNC (P Q : ℝ) (z : ℂ) : (starRingEnd ℂ) (airyNC P Q z) = airyNC P Q ((starRingEnd ℂ) z) := by
  unfold airyNC
  rw [map_add, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, conj_airyAiC, conj_deriv_airyAiC]

lemma conj_airyMC (P Q : ℝ) (z : ℂ) : (starRingEnd ℂ) (airyMC P Q z) = airyMC P Q ((starRingEnd ℂ) z) := by
  unfold airyMC
  rw [map_add, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, conj_airyBiC, conj_airyBiC']

/-! ### Connection formula for the derivative -/

/-- `Bi'(z) - i Ai'(z) = 2 ε̄ ω² Ai'(ω² z)` (derivative of DLMF 9.2.11). -/
theorem airyBiC'_sub_I_mul (z : ℂ) :
    airyBiC' z - I * deriv airyAiC z =
      2 * (starRingEnd ℂ) airyEps * (airyOmega ^ 2 * deriv airyAiC (airyOmega ^ 2 * z)) := by
  have hr := airyAiC_rotation_deriv z
  rw [airyOmega_pow_four] at hr
  have h1 := airy_I_mul_omega
  have h2 := airy_I_mul_omega_sq
  have h3 : I * airyOmega = (starRingEnd ℂ) airyEps * airyOmega ^ 2 := by
    have : I * airyOmega = I * airyOmega ^ 4 := by rw [airyOmega_pow_four]
    rw [this, show airyOmega ^ 4 = airyOmega ^ 2 * airyOmega ^ 2 by ring, ← mul_assoc, h2]
  unfold airyBiC'
  linear_combination (-I) * hr + (deriv airyAiC (airyOmega * z) * airyOmega) * h1 +
    deriv airyAiC (airyOmega ^ 2 * z) * h3

/-- `M - iN = 2 ε̄ (P Ai(ω² z) + Q ω² Ai'(ω² z))`. -/
theorem airyMC_sub_I_mul (P Q : ℝ) (z : ℂ) :
    airyMC P Q z - I * airyNC P Q z =
      2 * (starRingEnd ℂ) airyEps *
        ((P : ℂ) * airyAiC (airyOmega ^ 2 * z) + (Q : ℂ) * (airyOmega ^ 2 * deriv airyAiC (airyOmega ^ 2 * z))) := by
  have h1 := airyBiC_sub_I_mul_airyAiC z
  have h2 := airyBiC'_sub_I_mul z
  unfold airyMC airyNC
  linear_combination (P : ℂ) * h1 + (Q : ℂ) * h2

/-- Conjugate version: `M + iN = 2 ε (P Ai(ω z) + Q ω Ai'(ω z))`, in the form we use (conjugation of the previous). -/
theorem airyMC_add_I_mul_conj (P Q : ℝ) (z : ℂ) :
    ‖airyMC P Q z + I * airyNC P Q z‖ = ‖airyMC P Q ((starRingEnd ℂ) z) - I * airyNC P Q ((starRingEnd ℂ) z)‖ := by
  have : airyMC P Q ((starRingEnd ℂ) z) - I * airyNC P Q ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (airyMC P Q z + I * airyNC P Q z) := by
    rw [map_add, map_mul, Complex.conj_I, conj_airyMC, conj_airyNC]; ring
  rw [this, Complex.norm_conj]

/-! ### The upper bound -/

/-- **Upper bound for `M - iN` in the closed upper half plane**:
`‖M(u) - i N(u)‖² e(u) ≤ 4 (3|P| + 5|Q|)² (1 + ‖u‖)^{1/2}`. -/
theorem airyMC_sub_I_mul_sq_le (P Q : ℝ) {u : ℂ} (hu : 0 ≤ u.im) :
    ‖airyMC P Q u - I * airyNC P Q u‖ ^ 2 * airyEnv u ≤
      4 * (3 * |P| + 5 * |Q|) ^ 2 * (1 + ‖u‖) ^ (1 / 2 : ℝ) := by
  set w : ℂ := airyOmega ^ 2 * u with hw
  have hwn : ‖w‖ = ‖u‖ := by rw [hw, norm_mul, norm_airyOmega_sq, one_mul]
  have hre : (w ^ (3 / 2 : ℂ)).re = -(u ^ (3 / 2 : ℂ)).re := re_cpow_three_halves_omega_sq hu
  set s : ℝ := Real.exp ((2 / 3) * (u ^ (3 / 2 : ℂ)).re) with hs
  have hs0 : 0 < s := Real.exp_pos _
  have hss : s ^ 2 * airyEnv u = 1 := by
    rw [hs, airyEnv, ← Real.exp_nat_mul, ← Real.exp_add]
    rw [← Real.exp_zero]; congr 1; push_cast; ring
  have hE := airyAiC_envelope w
  have hD := airyAiC_deriv_envelope w
  rw [hre, hwn] at hE hD
  have e1 : Real.exp (-(2 / 3) * -(u ^ (3 / 2 : ℂ)).re) = s := by rw [hs]; congr 1; ring
  rw [e1] at hE hD
  set p : ℝ := (1 + ‖u‖) ^ (1 / 4 : ℝ) with hp
  have hp1 : 1 ≤ p := by
    rw [hp]; exact Real.one_le_rpow (by linarith [norm_nonneg u]) (by norm_num)
  have hp0 : (0 : ℝ) < p := by linarith
  have hq1 : (1 + ‖u‖) ^ (-(1 / 4) : ℝ) ≤ 1 := rpow_neg_quarter_le_one u
  have hA : ‖airyAiC w‖ ≤ 3 * s := by
    refine hE.trans ?_
    have := mul_le_mul_of_nonneg_right hq1 hs0.le
    nlinarith
  have hB : ‖deriv airyAiC w‖ ≤ 5 * p * s := hD
  have hnum : ‖airyMC P Q u - I * airyNC P Q u‖ ≤ 2 * ((3 * |P| + 5 * |Q|) * (p * s)) := by
    rw [airyMC_sub_I_mul, norm_mul, norm_mul, Complex.norm_two, norm_conj_airyEps, mul_one]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_airyOmega, one_pow, one_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |P| * ‖airyAiC w‖ ≤ |P| * (p * (3 * s)) := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      nlinarith
    have h2 : |Q| * ‖deriv airyAiC w‖ ≤ |Q| * (5 * p * s) :=
      mul_le_mul_of_nonneg_left hB (abs_nonneg _)
    nlinarith
  have hp2 : p ^ 2 = (1 + ‖u‖) ^ (1 / 2 : ℝ) := by
    rw [hp, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith [norm_nonneg u])]; norm_num
  calc ‖airyMC P Q u - I * airyNC P Q u‖ ^ 2 * airyEnv u
      ≤ (2 * ((3 * |P| + 5 * |Q|) * (p * s))) ^ 2 * airyEnv u := by
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnum 2) (airyEnv_pos u).le
    _ = 4 * (3 * |P| + 5 * |Q|) ^ 2 * p ^ 2 * (s ^ 2 * airyEnv u) := by ring
    _ = _ := by rw [hss, hp2]; ring

/-- info: 'FormalResearch.Special.airyNC_wronskian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyNC_wronskian

/-- info: 'FormalResearch.Special.airyMC_sub_I_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyMC_sub_I_mul

/-- info: 'FormalResearch.Special.airyMC_sub_I_mul_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyMC_sub_I_mul_sq_le

end FormalResearch.Special
