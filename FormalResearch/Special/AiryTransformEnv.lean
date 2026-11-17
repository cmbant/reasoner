module

public import FormalResearch.Special.AiryEnvCalculus
public import FormalResearch.Special.AiryRatioBounds
public import FormalResearch.Special.AiryKernelOpComplex

/-!
# The integral `κ(z) = ∫_0^∞ |Ai(z+t)|² dt = K(z, z̄)` is bounded by `C (1+|z|) e(z)`

`e(z) = exp(-(4/3) Re z^{3/2})` (`airyEnv`).  For `z ∈ ℂ`, `s ≥ 2|z| + 2` and `t ≥ 0`
(`airyEnv_shift_le`): `e(z+t) ≤ e(z)` for `t ≤ s` and `e(z+t) ≤ e(z) exp(-2(t-s))` for `t ≥ s`;
the first from the shift inequality (E3, `airyEnv_add_real_le`) at `z`; the second from (E3) at `z + s`, where
`Re √(z+s) ≥ 1` (because `Re(z+s) ≥ |z| + 2 ≥ 1`).  With the squared envelope `‖Ai(w)‖² ≤ 9 e(w)`
(`airyAiC_norm_sq_le`) this gives

`κ(z) := ∫_0^∞ ‖Ai(z+t)‖² dt ≤ 9 e(z) (s + 1/2) = 9 e(z) (2‖z‖ + 5/2)` (`airyKappa_le`)

(and integrability of the integrand on `(0,∞)`).  This is a (non-sharp, polynomial `1+|z|` instead of `(1+|z|)^{1/2}`)
form of the growth bound `K(z,z̄) ≲ (1+|z|)^{1/2} e(z)` listed as not formalised in `AiryKernelOpComplex`; it is
all that Theorem Q (`airyQ_hasSum_unc`, any real growth exponent `ν`) needs.  Numerical check (scipy, `z ∈ {-20, -5+i,
3+2i, -10+10i, 0}`): `κ(z) ≤ 9 e(z)(2|z|+5/2)` with slack `≥ 2.7` throughout; `max e(z+t)/(e(z) g(t)) = 0.99996`
over `2·10⁵` random `(z,t)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- **Shifted envelope**: for `s ≥ 2‖z‖ + 2` and `t ≥ 0`,
`e(z+t) ≤ e(z) · (1 if t ≤ s, exp(-2(t-s)) if t > s)`. -/
lemma airyEnv_shift_le (z : ℂ) {s : ℝ} (hs : 2 * ‖z‖ + 2 ≤ s) {t : ℝ} (ht : 0 ≤ t) :
    airyEnv (z + t) ≤ airyEnv z * (if t ≤ s then 1 else Real.exp (-2 * (t - s))) := by
  have hz := airySqrtRe_nonneg z
  have h1 : ∀ τ : ℝ, 0 ≤ τ → airyEnv (z + τ) ≤ airyEnv z := by
    intro τ hτ
    refine (airyEnv_add_real_le z τ).trans ?_
    have : Real.exp (-2 * τ * airySqrtRe z) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    nlinarith [airyEnv_pos z]
  rcases le_or_gt t s with hts | hts
  · simp only [hts, ↓reduceIte, mul_one]; exact h1 t ht
  · simp only [not_le.mpr hts, ↓reduceIte]
    have hs0 : 0 ≤ s := by nlinarith [norm_nonneg z]
    have hzs : z + (t : ℂ) = (z + (s : ℂ)) + ((t - s : ℝ) : ℂ) := by push_cast; ring
    rw [hzs]
    refine (airyEnv_add_real_le (z + (s : ℂ)) (t - s)).trans ?_
    have ha1 : 1 ≤ airySqrtRe (z + (s : ℂ)) := by
      have e1 := airySqrtRe_sq_sub (z + (s : ℂ))
      have hre : (z + (s : ℂ)).re = z.re + s := by simp
      rw [hre] at e1
      have hz2 : -‖z‖ ≤ z.re := by
        have := Complex.abs_re_le_norm z
        linarith [neg_abs_le z.re]
      have h0 := airySqrtRe_nonneg (z + (s : ℂ))
      nlinarith [sq_nonneg ((z + (s : ℂ)) ^ (1 / 2 : ℂ)).im]
    have hexp : Real.exp (-2 * (t - s) * airySqrtRe (z + (s : ℂ))) ≤ Real.exp (-2 * (t - s)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc airyEnv (z + (s : ℂ)) * Real.exp (-2 * (t - s) * airySqrtRe (z + (s : ℂ)))
        ≤ airyEnv z * Real.exp (-2 * (t - s)) :=
          mul_le_mul (h1 s hs0) hexp (Real.exp_pos _).le (airyEnv_pos z).le

/-- `κ(z) = ∫_0^∞ ‖Ai(z+t)‖² dt` (`= K(z, z̄)`). -/
noncomputable def airyKappa (z : ℂ) : ℝ := ∫ t : ℝ in Ioi (0 : ℝ), ‖airyAiC (z + (t : ℂ))‖ ^ 2

/-- The explicit majorant `9 e(z) · (1 if t ≤ s, exp(-2(t-s)) if t > s)`. -/
noncomputable def airyKB (z : ℂ) (s t : ℝ) : ℝ :=
  9 * airyEnv z * (if t ≤ s then 1 else Real.exp (-2 * (t - s)))

lemma airyAiC_sq_le_airyKB (z : ℂ) {s : ℝ} (hs : 2 * ‖z‖ + 2 ≤ s) {t : ℝ} (ht : 0 ≤ t) :
    ‖airyAiC (z + t)‖ ^ 2 ≤ airyKB z s t := by
  have h1 := airyAiC_norm_sq_le (z + t)
  have h2 : (1 + ‖z + (t : ℂ)‖) ^ (-(1 / 2) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg (z + (t : ℂ))]) (by norm_num)
  have h3 := airyEnv_pos (z + t)
  have h4 := airyEnv_shift_le z hs ht
  have h5 : 9 * (1 + ‖z + (t : ℂ)‖) ^ (-(1 / 2) : ℝ) * airyEnv (z + t) ≤ 9 * airyEnv (z + t) := by
    nlinarith
  unfold airyKB
  nlinarith

lemma integrableOn_airyKB (z : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    IntegrableOn (airyKB z s) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi hs]
  refine IntegrableOn.union ?_ ?_
  · have : IntegrableOn (fun _ : ℝ => 9 * airyEnv z) (Ioc 0 s) := integrableOn_const (by simp)
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioc
    simp only [airyKB, ht.2, ↓reduceIte, mul_one]
  · have h : IntegrableOn (fun t : ℝ => (9 * airyEnv z * Real.exp (2 * s)) * Real.exp (-2 * t))
        (Ioi s) := (integrableOn_exp_mul_Ioi (a := -2) (by norm_num) s).const_mul _
    refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht' : ¬ t ≤ s := not_le.mpr ht
    simp only [airyKB, ht', ↓reduceIte]
    rw [show Real.exp (-2 * (t - s)) = Real.exp (2 * s) * Real.exp (-2 * t) by
      rw [← Real.exp_add]; congr 1; ring]
    ring

lemma integral_airyKB (z : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    ∫ t in Ioi 0, airyKB z s t = 9 * airyEnv z * (s + 1 / 2) := by
  rw [← Ioc_union_Ioi_eq_Ioi hs]
  have hI := integrableOn_airyKB z hs
  rw [← Ioc_union_Ioi_eq_Ioi hs] at hI
  rw [setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi (hI.mono_set subset_union_left)
    (hI.mono_set subset_union_right)]
  have e1 : ∫ t in Ioc 0 s, airyKB z s t = ∫ t in Ioc 0 s, 9 * airyEnv z := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    simp only [airyKB, ht.2, ↓reduceIte, mul_one]
  have e2 : ∫ t in Ioi s, airyKB z s t =
      ∫ t in Ioi s, (9 * airyEnv z * Real.exp (2 * s)) * Real.exp (-2 * t) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : ¬ t ≤ s := not_le.mpr ht
    simp only [airyKB, ht', ↓reduceIte]
    rw [show Real.exp (-2 * (t - s)) = Real.exp (2 * s) * Real.exp (-2 * t) by
      rw [← Real.exp_add]; congr 1; ring]
    ring
  rw [e1, e2, integral_const_mul (9 * airyEnv z * Real.exp (2 * s)),
    integral_exp_mul_Ioi (by norm_num) s]
  simp only [setIntegral_const, Real.volume_real_Ioc, smul_eq_mul]
  rw [max_eq_left (by linarith)]
  have : Real.exp (2 * s) * (-Real.exp (-2 * s) / -2) = 1 / 2 := by
    rw [neg_div_neg_eq, mul_div_assoc', ← Real.exp_add]
    simp
  rw [← mul_assoc, mul_assoc (9 * airyEnv z), this]
  ring

lemma integrableOn_airyAiC_sq (z : ℂ) :
    IntegrableOn (fun t : ℝ => ‖airyAiC (z + t)‖ ^ 2) (Ioi 0) := by
  have hs : 0 ≤ 2 * ‖z‖ + 2 := by positivity
  refine (integrableOn_airyKB z hs).mono' ?_ ?_
  · exact ((differentiable_airyAiC.continuous.comp
      (continuous_const.add Complex.continuous_ofReal)).norm.pow 2).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact airyAiC_sq_le_airyKB z le_rfl (le_of_lt ht)

/-- **Growth of `κ`**: `κ(z) ≤ 9 e(z) (2‖z‖ + 5/2) ≤ 23 (1+‖z‖) e(z)`. -/
theorem airyKappa_le (z : ℂ) : airyKappa z ≤ 9 * airyEnv z * (2 * ‖z‖ + 5 / 2) := by
  have hs : 0 ≤ 2 * ‖z‖ + 2 := by positivity
  unfold airyKappa
  calc ∫ t : ℝ in Ioi (0 : ℝ), ‖airyAiC (z + (t : ℂ))‖ ^ 2 ≤ ∫ t in Ioi (0 : ℝ), airyKB z (2 * ‖z‖ + 2) t := by
        refine setIntegral_mono_on (integrableOn_airyAiC_sq z) (integrableOn_airyKB z hs)
          measurableSet_Ioi fun t ht => airyAiC_sq_le_airyKB z le_rfl (le_of_lt ht)
    _ = 9 * airyEnv z * (2 * ‖z‖ + 2 + 1 / 2) := integral_airyKB z hs
    _ = _ := by ring

/-- Polynomial form of the growth bound: `κ(z) ≤ 23 (1+‖z‖) e(z)`. -/
theorem airyKappa_le' (z : ℂ) : airyKappa z ≤ 23 * (1 + ‖z‖) * airyEnv z := by
  have := airyKappa_le z
  have h := airyEnv_pos z
  nlinarith [norm_nonneg z]

lemma airyKappa_nonneg (z : ℂ) : 0 ≤ airyKappa z :=
  setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg (‖airyAiC (z + (t : ℂ))‖)

/-- info: 'FormalResearch.Special.airyKappa_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKappa_le

/-- info: 'FormalResearch.Special.airyKappa_le'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKappa_le'

end FormalResearch.Special
