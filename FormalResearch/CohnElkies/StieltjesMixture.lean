module

public import FormalResearch.CohnElkies.ResolventAverage
public import FormalResearch.CohnElkies.ClosedResolvent
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Stieltjes mixture identities and positive single-resolvent average (CR.2, CR.6b–CR.9, CR.19–CR.20)

Source: `CFT/sign_uncertainty/paper/ce_cardinal_resolvent.tex`:
Corollary CR.2 (`cecr:CR2`, equations `(CR.6b)`, `(CR.7)`, `(CR.8)`, `(CR.9)`) and the positive Stieltjes
single-resolvent mixture identities `(CR.19)`–`(CR.20)` in the proof of Theorem CR.4.

**Statements proved:**

* `(CR.19a)`: `cohnWt t x = x / (x + t)`, `cohnWt_le_two_sub_sq` (`w_t ≤ 2 w_t - w_t^2 ≤ 2 w_t`),
  `two_mul_cohnWt_sub_sq_eq` (`2 w_t - w_t^2 = 1 - (t / (x + t))^2`), and `one_sub_t_mul_deriv_cohnWt`
  (`(1 - t ∂_t) w_t = 2 w_t - w_t^2`).
* `(CR.8)`: `cohnG2_nonneg` and `cohnG2_le_cohnT`:
  `0 ≤ G_{s,t;h}(u) = ∑' n, c_n² L_n(u)² / ((1 + s h E_n)(1 + t h E_n)) ≤ T(u)` for `0 ≤ s, t, h`.
* `(CR.6b)`: `cohnG2_eq_offDiag` (`(s G_{sh}(u) - t G_{th}(u)) / (s - t)` for `s ≠ t`) and
  `cohnG_smul_hasDerivAt` (`HasDerivAt (fun s => s * G_{sh}(u)) (G_{s₀,s₀;h}(u)) s₀` for `s₀ > 0`).
* `(CR.20)`: `stieltjesQ_eq_mixture`: for any probability measure `μ` supported on `(0, ∞)` with Stieltjes
  transform `φ(y) = ∫ (1 + s y)⁻¹ dμ(s)`, `q_μ(h x) = 1 - φ(h x)^2` equals the triple integral
  `∫_{(0,∞)²} ∫₀¹ (2 w_t(x) - w_t(x)^2) dω d(μ × μ)(s, r)` where `t = (h (ω s + (1 - ω) r))⁻¹`.
* **Corollary CR.2 (`(CR.7)`, `(CR.9)`)**: `cohnS_eq_sub_doubleIntegral`
  (`S_h(u) = T(u) - ∬ G_{s,t;h}(u) dμ(s) dμ(t)`) and `cohnG2_eq_three_airy` (explicit `Ai²`, `Ai Ai'`,
  `Ai'²` coefficient representation on `s ≠ t` away from `z = a`, free of `u`-Airy-zero poles).
-/

@[expose] public section

open Filter Topology Set MeasureTheory intervalIntegral
open FormalResearch.Special

namespace FormalResearch.CohnElkies

/-! ### Weight function `w_t(x) = x / (x + t)` and `(CR.19a)` -/

/-- `w_t(x) = x / (x + t)` from Theorem CR.4 `(CR.19a)`. -/
noncomputable def cohnWt (t x : ℝ) : ℝ := x / (x + t)

lemma cohnWt_nonneg {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) : 0 ≤ cohnWt t x :=
  div_nonneg hx (add_nonneg hx ht)

lemma cohnWt_le_one {t x : ℝ} (ht : 0 < t) (hx : 0 ≤ x) : cohnWt t x ≤ 1 :=
  div_le_one_of_le₀ (le_add_of_nonneg_right ht.le) (by linarith)

lemma two_mul_cohnWt_sub_sq_eq {t x : ℝ} (hxt : x + t ≠ 0) :
    2 * cohnWt t x - cohnWt t x ^ 2 = 1 - (t / (x + t)) ^ 2 := by
  unfold cohnWt
  field_simp
  ring

lemma cohnWt_le_two_sub_sq {t x : ℝ} (ht : 0 < t) (hx : 0 ≤ x) :
    cohnWt t x ≤ 2 * cohnWt t x - cohnWt t x ^ 2 ∧
      2 * cohnWt t x - cohnWt t x ^ 2 ≤ 2 * cohnWt t x := by
  have hw0 : 0 ≤ cohnWt t x := cohnWt_nonneg ht.le hx
  have hw1 : cohnWt t x ≤ 1 := cohnWt_le_one ht hx
  refine ⟨?_, by linarith [sq_nonneg (cohnWt t x)]⟩
  nlinarith

lemma cohnWt_hasDerivAt {t x : ℝ} (hxt : x + t ≠ 0) :
    HasDerivAt (fun s => cohnWt s x) (-(x / (x + t) ^ 2)) t := by
  unfold cohnWt
  have hden : HasDerivAt (fun s => x + s) 1 t := (hasDerivAt_id t).const_add x
  have hd : HasDerivAt (fun s => x / (x + s)) ((0 * (x + t) - x * 1) / (x + t) ^ 2) t :=
    (hasDerivAt_const t x).div hden hxt
  convert hd using 1
  ring

/-- **Eq. `(CR.19a)` (differential form):** `(1 - t ∂_t) w_t(x) = 2 w_t(x) - w_t(x)² = 1 - (t/(x+t))²`. -/
theorem one_sub_t_mul_deriv_cohnWt {t x : ℝ} (hxt : x + t ≠ 0) :
    cohnWt t x - t * deriv (fun s => cohnWt s x) t = 2 * cohnWt t x - cohnWt t x ^ 2 := by
  rw [(cohnWt_hasDerivAt hxt).deriv]
  unfold cohnWt
  field_simp
  ring

/-! ### Double resolvent `G_{s,t;h}(u)` and `(CR.8)` -/

/-- The unweighted diagonal sum `T(u) = ∑_n c_n² L_n(u)²` (`(CR.3)`). -/
noncomputable def cohnT (a u : ℝ) : ℝ :=
  ∑' n : ℕ, cohnC a n ^ 2 * cohnL n u ^ 2

/-- The double resolvent `G_{s,t;h}(u) = ∑_n c_n² L_n(u)² / ((1 + s h E_n)(1 + t h E_n))` (`(CR.8)`). -/
noncomputable def cohnG2 (a h s t u : ℝ) : ℝ :=
  ∑' n : ℕ, cohnC a n ^ 2 * cohnL n u ^ 2 / ((1 + s * h * cohnE n) * (1 + t * h * cohnE n))

lemma cohnE_nonneg (n : ℕ) : 0 ≤ cohnE n := by
  unfold cohnE
  have h : airyZero (n + 1) ≤ airyZero 1 := airyZero_anti (le_refl 1) (Nat.le_add_left 1 n)
  linarith

lemma one_add_mul_cohnE_pos {q : ℝ} (hq : 0 ≤ q) (n : ℕ) : 0 < 1 + q * cohnE n := by
  linarith [mul_nonneg hq (cohnE_nonneg n)]

lemma one_le_one_add_mul_cohnE {q : ℝ} (hq : 0 ≤ q) (n : ℕ) : 1 ≤ 1 + q * cohnE n := by
  linarith [mul_nonneg hq (cohnE_nonneg n)]

lemma summable_cohnT {a u : ℝ} (ha : airyAi' a = 0) (hua : u ≠ a) :
    Summable (fun n : ℕ => cohnC a n ^ 2 * cohnL n u ^ 2) :=
  (unweightedDiagonal_hasSum ha hua).summable

lemma cohnT_eq {a u : ℝ} (ha : airyAi' a = 0) (hua : u ≠ a) :
    cohnT a u = (airyAi' u ^ 2 - (a + u) * airyAi u ^ 2) / (u - a) ^ 2 +
      2 * airyAi u * airyAi' u / (u - a) ^ 3 :=
  (unweightedDiagonal_hasSum ha hua).tsum_eq

lemma summable_cohnG_of_nonneg {a q u : ℝ} (ha : airyAi' a = 0) (hua : u ≠ a) (hq : 0 ≤ q) :
    Summable (fun n : ℕ => cohnC a n ^ 2 * cohnL n u ^ 2 / (1 + q * cohnE n)) := by
  refine (summable_cohnT ha hua).of_nonneg_of_le
    (fun n => div_nonneg (by positivity) (one_add_mul_cohnE_pos hq n).le)
    (fun n => div_le_self (by positivity) (one_le_one_add_mul_cohnE hq n))

lemma summable_cohnG2 {a h s t u : ℝ} (ha : airyAi' a = 0) (hua : u ≠ a)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hh : 0 ≤ h) :
    Summable (fun n : ℕ =>
      cohnC a n ^ 2 * cohnL n u ^ 2 / ((1 + s * h * cohnE n) * (1 + t * h * cohnE n))) := by
  have h1 : ∀ n : ℕ, 1 ≤ (1 + s * h * cohnE n) * (1 + t * h * cohnE n) := fun n => by
    nlinarith [one_le_one_add_mul_cohnE (mul_nonneg hs hh) n,
      one_le_one_add_mul_cohnE (mul_nonneg ht hh) n]
  exact (summable_cohnT ha hua).of_nonneg_of_le
    (fun n => div_nonneg (by positivity) (by linarith [h1 n]))
    (fun n => div_le_self (by positivity) (h1 n))

/-- **Eq. `(CR.8)` (nonnegativity and bound):** `0 ≤ G_{s,t;h}(u) ≤ T(u)` for `s, t, h ≥ 0`. -/
theorem cohnG2_nonneg (a h s t u : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hh : 0 ≤ h) :
    0 ≤ cohnG2 a h s t u := by
  unfold cohnG2
  refine tsum_nonneg fun n => ?_
  have hden : 0 < (1 + s * h * cohnE n) * (1 + t * h * cohnE n) :=
    mul_pos (one_add_mul_cohnE_pos (mul_nonneg hs hh) n) (one_add_mul_cohnE_pos (mul_nonneg ht hh) n)
  exact div_nonneg (by positivity) hden.le

/-- **Eq. `(CR.8)` (domination by `T`):** `G_{s,t;h}(u) ≤ T(u)`. -/
theorem cohnG2_le_cohnT {a h s t u : ℝ} (ha : airyAi' a = 0) (hua : u ≠ a)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hh : 0 ≤ h) :
    cohnG2 a h s t u ≤ cohnT a u := by
  unfold cohnG2 cohnT
  refine (summable_cohnG2 ha hua hs ht hh).tsum_le_tsum (fun n => ?_) (summable_cohnT ha hua)
  have h1 : 1 ≤ (1 + s * h * cohnE n) * (1 + t * h * cohnE n) := by
    nlinarith [one_le_one_add_mul_cohnE (mul_nonneg hs hh) n,
      one_le_one_add_mul_cohnE (mul_nonneg ht hh) n]
  exact div_le_self (by positivity) h1

/-! ### Difference-quotient & derivative formula `(CR.6b)` -/

/-- **Eq. `(CR.6b)` (off the diagonal `s ≠ t`):**
`G_{s,t;h}(u) = (s G_{sh}(u) - t G_{th}(u)) / (s - t)`. -/
theorem cohnG2_eq_offDiag {a h s t u : ℝ} (ha : airyAi' a = 0) (hua : u ≠ a)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hh : 0 ≤ h) (hst : s ≠ t) :
    cohnG2 a h s t u = (s * cohnG a (s * h) u - t * cohnG a (t * h) u) / (s - t) := by
  have hsSum := (summable_cohnG_of_nonneg ha hua (mul_nonneg hs hh)).mul_left s
  have htSum := (summable_cohnG_of_nonneg ha hua (mul_nonneg ht hh)).mul_left t
  have hst' : s - t ≠ 0 := sub_ne_zero.mpr hst
  have heq : ∀ n : ℕ,
      (s * (cohnC a n ^ 2 * cohnL n u ^ 2 / (1 + s * h * cohnE n)) -
        t * (cohnC a n ^ 2 * cohnL n u ^ 2 / (1 + t * h * cohnE n))) / (s - t) =
      cohnC a n ^ 2 * cohnL n u ^ 2 / ((1 + s * h * cohnE n) * (1 + t * h * cohnE n)) := by
    intro n
    have h1 : 1 + s * h * cohnE n ≠ 0 := (one_add_mul_cohnE_pos (mul_nonneg hs hh) n).ne'
    have h2 : 1 + t * h * cohnE n ≠ 0 := (one_add_mul_cohnE_pos (mul_nonneg ht hh) n).ne'
    have hfrac : (s / (1 + s * h * cohnE n) - t / (1 + t * h * cohnE n)) / (s - t) =
        1 / ((1 + s * h * cohnE n) * (1 + t * h * cohnE n)) := by
      rw [div_sub_div _ _ h1 h2, div_div,
        div_eq_div_iff (mul_ne_zero (mul_ne_zero h1 h2) hst') (mul_ne_zero h1 h2)]
      ring
    calc (s * (cohnC a n ^ 2 * cohnL n u ^ 2 / (1 + s * h * cohnE n)) -
            t * (cohnC a n ^ 2 * cohnL n u ^ 2 / (1 + t * h * cohnE n))) / (s - t)
        = (cohnC a n ^ 2 * cohnL n u ^ 2) *
            ((s / (1 + s * h * cohnE n) - t / (1 + t * h * cohnE n)) / (s - t)) := by ring
      _ = (cohnC a n ^ 2 * cohnL n u ^ 2) *
            (1 / ((1 + s * h * cohnE n) * (1 + t * h * cohnE n))) := by rw [hfrac]
      _ = _ := by ring
  unfold cohnG2 cohnG
  rw [← tsum_congr heq, tsum_div_const, hsSum.tsum_sub htSum]
  simp only [tsum_mul_left]

/-- **Eq. `(CR.6b)` (diagonal derivative):** `HasDerivAt (fun s => s * G_{sh}(u)) (G_{s₀,s₀;h}(u)) s₀`. -/
theorem cohnG_smul_hasDerivAt {a h s₀ u : ℝ} (ha : airyAi' a = 0) (hua : u ≠ a)
    (hs₀ : 0 < s₀) (hh : 0 ≤ h) :
    HasDerivAt (fun s => s * cohnG a (s * h) u) (cohnG2 a h s₀ s₀ u) s₀ := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hsub : (fun s => slope (fun s => s * cohnG a (s * h) u) s₀ s) =ᶠ[𝓝[≠] s₀]
      (fun s => cohnG2 a h s s₀ u) := by
    have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝[≠] s₀ :=
      nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hs₀)
    filter_upwards [hmem, self_mem_nhdsWithin] with s (hs : 0 < s) (hne : s ≠ s₀)
    rw [slope_def_field, cohnG2_eq_offDiag ha hua hs.le hs₀.le hh hne]
  refine (Tendsto.congr' hsub.symm ?_)
  refine tendsto_tsum_of_dominated_convergence (summable_cohnT ha hua) ?_ ?_
  · intro n
    have hpos : 0 < (1 + s₀ * h * cohnE n) * (1 + s₀ * h * cohnE n) :=
      mul_pos (one_add_mul_cohnE_pos (mul_nonneg hs₀.le hh) n)
        (one_add_mul_cohnE_pos (mul_nonneg hs₀.le hh) n)
    have hcont : ContinuousAt (fun s =>
        cohnC a n ^ 2 * cohnL n u ^ 2 / ((1 + s * h * cohnE n) * (1 + s₀ * h * cohnE n))) s₀ := by
      refine ContinuousAt.div continuousAt_const ?_ hpos.ne'
      fun_prop
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  · have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝[≠] s₀ :=
      nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hs₀)
    filter_upwards [hmem] with s (hs : 0 < s) n
    have h1 : 1 ≤ (1 + s * h * cohnE n) * (1 + s₀ * h * cohnE n) := by
      nlinarith [one_le_one_add_mul_cohnE (mul_nonneg hs.le hh) n,
        one_le_one_add_mul_cohnE (mul_nonneg hs₀.le hh) n]
    rw [Real.norm_of_nonneg (div_nonneg (by positivity) (by linarith))]
    exact div_le_self (by positivity) h1

/-! ### Stieltjes mixture identities `(CR.20)` and Corollary CR.2 `(CR.7)`, `(CR.9)` -/

/-- The Stieltjes transform `φ_μ(x) = ∫ (1 + s x)⁻¹ dμ(s)` for a measure `μ` on `(0, ∞)`. -/
noncomputable def stieltjesPhi (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ s : ℝ, (1 + s * x)⁻¹ ∂μ

/-- `q_μ(x) = 1 - φ_μ(x)^2`. -/
noncomputable def stieltjesQ (μ : Measure ℝ) (x : ℝ) : ℝ :=
  1 - stieltjesPhi μ x ^ 2

/-- The exact moving source `S_h(u) = ∑_n c_n² (1 - φ(h E_n)²) L_n(u)²` (`cecr:CR2`). -/
noncomputable def cohnS (a : ℝ) (φ : ℝ → ℝ) (h u : ℝ) : ℝ :=
  ∑' n : ℕ, cohnC a n ^ 2 * (1 - φ (h * cohnE n) ^ 2) * cohnL n u ^ 2

private lemma ae_prod_pos_of_ae_pos (μ : Measure ℝ) [SFinite μ]
    (hsupp : ∀ᵐ s ∂μ, 0 < s) : ∀ᵐ p : ℝ × ℝ ∂(μ.prod μ), 0 < p.1 ∧ 0 < p.2 := by
  have hs : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd)
  rw [Measure.ae_prod_iff_ae_ae hs]
  filter_upwards [hsupp] with s hs_pos
  filter_upwards [hsupp] with t ht_pos
  exact ⟨hs_pos, ht_pos⟩

private lemma integrable_inv_one_add_mul (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ s ∂μ, 0 < s) {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun s : ℝ => (1 + s * x)⁻¹) μ := by
  refine (integrable_const (1 : ℝ)).mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [hsupp] with s hs
  have hden : 1 ≤ 1 + s * x := by linarith [mul_nonneg hs.le hx]
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (by linarith))]
  exact inv_le_one_of_one_le₀ hden

/-- **Eq. `(CR.20)`:** For a probability measure `μ` supported on `(0, ∞)` and `h, x > 0`,
`1 - φ_μ(h x)² = ∬_{(0,∞)²} ∫₀¹ (2 w_t(x) - w_t(x)²) dω d(μ × μ)(s, r)` with `t = (h (ω s + (1 - ω) r))⁻¹`. -/
theorem stieltjesQ_eq_mixture (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ s ∂μ, 0 < s) {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    stieltjesQ μ (h * x) =
      ∫ p : ℝ × ℝ, (∫ ω in (0 : ℝ)..1,
        2 * cohnWt ((h * (ω * p.1 + (1 - ω) * p.2))⁻¹) x -
          cohnWt ((h * (ω * p.1 + (1 - ω) * p.2))⁻¹) x ^ 2) ∂(μ.prod μ) := by
  have hprod_pos : ∀ᵐ p : ℝ × ℝ ∂(μ.prod μ), 0 < p.1 ∧ 0 < p.2 :=
    ae_prod_pos_of_ae_pos μ hsupp
  have hI : Integrable (fun s : ℝ => (1 + s * (h * x))⁻¹) μ :=
    integrable_inv_one_add_mul μ hsupp (mul_pos hh hx).le
  have hsq : stieltjesPhi μ (h * x) ^ 2 =
      ∫ p : ℝ × ℝ, (1 + p.1 * (h * x))⁻¹ * (1 + p.2 * (h * x))⁻¹ ∂(μ.prod μ) := by
    rw [sq, stieltjesPhi, ← integral_prod_mul (f := fun s : ℝ => (1 + s * (h * x))⁻¹)
      (g := fun s : ℝ => (1 + s * (h * x))⁻¹)]
  have hprod_int : Integrable (fun p : ℝ × ℝ => (1 + p.1 * (h * x))⁻¹ * (1 + p.2 * (h * x))⁻¹)
      (μ.prod μ) := hI.mul_prod hI
  have hsub_eq : (∫ _ : ℝ × ℝ, (1 : ℝ) ∂(μ.prod μ)) -
      ∫ p : ℝ × ℝ, (1 + p.1 * (h * x))⁻¹ * (1 + p.2 * (h * x))⁻¹ ∂(μ.prod μ) =
      ∫ p : ℝ × ℝ, (1 - (1 + p.1 * (h * x))⁻¹ * (1 + p.2 * (h * x))⁻¹) ∂(μ.prod μ) :=
    (MeasureTheory.integral_sub (integrable_const _) hprod_int).symm
  have hdiff : (1 : ℝ) - stieltjesPhi μ (h * x) ^ 2 =
      ∫ p : ℝ × ℝ, (1 - (1 + p.1 * (h * x))⁻¹ * (1 + p.2 * (h * x))⁻¹) ∂(μ.prod μ) := by
    rw [hsq, ← hsub_eq]
    simp
  rw [stieltjesQ, hdiff]
  refine integral_congr_ae ?_
  filter_upwards [hprod_pos] with p ⟨hp1, hp2⟩
  have h1s : 0 < 1 + p.1 * h * x := by positivity
  have h1r : 0 < 1 + p.2 * h * x := by positivity
  have hCR18 := resolvent_product_eq_integral p.1 p.2 h x h1s h1r
  have hsub : 1 - (1 + p.1 * (h * x))⁻¹ * (1 + p.2 * (h * x))⁻¹ =
      ∫ ω in (0 : ℝ)..1, (1 - 1 / (1 + h * (ω * p.1 + (1 - ω) * p.2) * x) ^ 2) := by
    have hconst : (∫ _ in (0 : ℝ)..1, (1 : ℝ)) = 1 := by simp
    have hi_inv : IntervalIntegrable (fun ω => 1 / (1 + h * (ω * p.1 + (1 - ω) * p.2) * x) ^ 2) volume 0 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      intro ω hω
      refine ContinuousAt.continuousWithinAt (ContinuousAt.div continuousAt_const ?_ ?_)
      · fun_prop
      · rw [Set.uIcc_of_le zero_le_one] at hω
        have : 0 < ω * p.1 + (1 - ω) * p.2 := by
          rcases eq_or_lt_of_le hω.1 with rfl | h0
          · simp [hp2]
          · linarith [mul_pos h0 hp1, mul_nonneg (by linarith [hω.2] : 0 ≤ 1 - ω) hp2.le]
        exact ne_of_gt (sq_pos_of_pos (by positivity))
    calc 1 - (1 + p.1 * (h * x))⁻¹ * (1 + p.2 * (h * x))⁻¹
        = (∫ _ in (0 : ℝ)..1, (1 : ℝ)) -
            ∫ ω in (0 : ℝ)..1, 1 / (1 + h * (ω * p.1 + (1 - ω) * p.2) * x) ^ 2 := by
          have hinv : (1 + p.1 * (h * x))⁻¹ * (1 + p.2 * (h * x))⁻¹ =
              1 / ((1 + p.1 * h * x) * (1 + p.2 * h * x)) := by
            rw [← one_div, ← one_div, one_div_mul_one_div,
              show 1 + p.1 * (h * x) = 1 + p.1 * h * x by ring,
              show 1 + p.2 * (h * x) = 1 + p.2 * h * x by ring]
          rw [hinv, hconst, ← hCR18]
      _ = ∫ ω in (0 : ℝ)..1, (1 - 1 / (1 + h * (ω * p.1 + (1 - ω) * p.2) * x) ^ 2) :=
          (intervalIntegral.integral_sub intervalIntegrable_const hi_inv).symm
  rw [hsub]
  refine integral_congr fun ω hω => ?_
  rw [Set.uIcc_of_le zero_le_one] at hω
  have hcomb : 0 < ω * p.1 + (1 - ω) * p.2 := by
    rcases eq_or_lt_of_le hω.1 with rfl | h0
    · simp [hp2]
    · linarith [mul_pos h0 hp1, mul_nonneg (by linarith [hω.2] : 0 ≤ 1 - ω) hp2.le]
  set t : ℝ := (h * (ω * p.1 + (1 - ω) * p.2))⁻¹
  have hxt : x + t ≠ 0 := by positivity
  rw [two_mul_cohnWt_sub_sq_eq hxt]
  have ht_ne : h * (ω * p.1 + (1 - ω) * p.2) ≠ 0 := (mul_pos hh hcomb).ne'
  have hratio : t / (x + t) = 1 / (1 + h * (ω * p.1 + (1 - ω) * p.2) * x) := by
    dsimp [t]
    field_simp
    ring
  rw [hratio, div_pow, one_pow]

private lemma cohnG2_term_measurable (c e h : ℝ) :
    Measurable (fun p : ℝ × ℝ => c / ((1 + p.1 * h * e) * (1 + p.2 * h * e))) :=
  measurable_const.div
    (((measurable_const.add ((measurable_fst.mul measurable_const).mul measurable_const)).mul
      (measurable_const.add ((measurable_snd.mul measurable_const).mul measurable_const))))

/-- **Corollary CR.2 (`cecr:CR2`, eq. `(CR.7)`):**
`S_h(u) = T(u) - ∬_{(0,∞)²} G_{s,t;h}(u) dμ(s) dμ(t)`. -/
theorem cohnS_eq_sub_doubleIntegral {a h u : ℝ} (ha : airyAi' a = 0) (hua : u ≠ a)
    (hh : 0 ≤ h) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsupp : ∀ᵐ s ∂μ, 0 < s) :
    Integrable (fun p : ℝ × ℝ => cohnG2 a h p.1 p.2 u) (μ.prod μ) ∧
      cohnS a (stieltjesPhi μ) h u =
        cohnT a u - ∫ p : ℝ × ℝ, cohnG2 a h p.1 p.2 u ∂(μ.prod μ) := by
  have hprod_pos : ∀ᵐ p : ℝ × ℝ ∂(μ.prod μ), 0 < p.1 ∧ 0 < p.2 :=
    ae_prod_pos_of_ae_pos μ hsupp
  have hae_le : ∀ᵐ p : ℝ × ℝ ∂(μ.prod μ), ‖cohnG2 a h p.1 p.2 u‖ ≤ cohnT a u := by
    filter_upwards [hprod_pos] with p hp
    rw [Real.norm_of_nonneg (cohnG2_nonneg a h p.1 p.2 u hp.1.le hp.2.le hh)]
    exact cohnG2_le_cohnT ha hua hp.1.le hp.2.le hh
  have hmeasG2 : AEStronglyMeasurable (fun p : ℝ × ℝ => cohnG2 a h p.1 p.2 u) (μ.prod μ) := by
    refine aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (f := fun N p => ∑ n ∈ Finset.range N,
        (cohnC a n ^ 2 * cohnL n u ^ 2) / ((1 + p.1 * h * cohnE n) * (1 + p.2 * h * cohnE n)))
      (fun N => (Finset.measurable_sum (Finset.range N) fun n _ =>
        cohnG2_term_measurable (cohnC a n ^ 2 * cohnL n u ^ 2) (cohnE n) h).aestronglyMeasurable) ?_
    filter_upwards [hprod_pos] with p hp
    exact (summable_cohnG2 ha hua hp.1.le hp.2.le hh).hasSum.tendsto_sum_nat
  have hIntG2 : Integrable (fun p : ℝ × ℝ => cohnG2 a h p.1 p.2 u) (μ.prod μ) :=
    (integrable_const (cohnT a u)).mono' hmeasG2 hae_le
  refine ⟨hIntG2, ?_⟩
  let F : ℕ → ℝ × ℝ → ℝ := fun n p =>
    cohnC a n ^ 2 * cohnL n u ^ 2 / ((1 + p.1 * h * cohnE n) * (1 + p.2 * h * cohnE n))
  have hF_int : ∀ n : ℕ, Integrable (F n) (μ.prod μ) := by
    intro n
    have h1 := (integrable_inv_one_add_mul μ hsupp (mul_nonneg hh (cohnE_nonneg n)))
    have hprod := h1.mul_prod h1
    refine (hprod.const_mul (cohnC a n ^ 2 * cohnL n u ^ 2)).congr (ae_of_all _ fun p => ?_)
    dsimp [F]
    have hden1 : 1 + p.1 * (h * cohnE n) = 1 + p.1 * h * cohnE n := by ring
    have hden2 : 1 + p.2 * (h * cohnE n) = 1 + p.2 * h * cohnE n := by ring
    rw [hden1, hden2, div_eq_mul_inv, mul_inv]
  have hF_sum : Summable (fun n : ℕ => ∫ p : ℝ × ℝ, ‖F n p‖ ∂(μ.prod μ)) := by
    refine (summable_cohnT ha hua).of_nonneg_of_le
      (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_)
    calc ∫ p : ℝ × ℝ, ‖F n p‖ ∂(μ.prod μ)
        ≤ ∫ _ : ℝ × ℝ, cohnC a n ^ 2 * cohnL n u ^ 2 ∂(μ.prod μ) := by
          refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (integrable_const _) ?_
          filter_upwards [hprod_pos] with p hp
          have h1 : 1 ≤ (1 + p.1 * h * cohnE n) * (1 + p.2 * h * cohnE n) := by
            nlinarith [one_le_one_add_mul_cohnE (mul_nonneg hp.1.le hh) n,
              one_le_one_add_mul_cohnE (mul_nonneg hp.2.le hh) n]
          have hpos : 0 ≤ F n p := by dsimp [F]; exact div_nonneg (by positivity) (by linarith)
          rw [Real.norm_of_nonneg hpos]
          dsimp [F]
          exact div_le_self (by positivity) h1
      _ = cohnC a n ^ 2 * cohnL n u ^ 2 := by simp
  have hF_enorm : ∑' n : ℕ, ∫⁻ p : ℝ × ℝ, ‖F n p‖ₑ ∂(μ.prod μ) ≠ ⊤ := by
    have heq : (fun n : ℕ => ∫⁻ p : ℝ × ℝ, ‖F n p‖ₑ ∂(μ.prod μ)) =
        fun n : ℕ => ENNReal.ofReal (∫ p : ℝ × ℝ, ‖F n p‖ ∂(μ.prod μ)) :=
      funext fun n => (ofReal_integral_norm_eq_lintegral_enorm (hF_int n)).symm
    rw [heq, ← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun _ => norm_nonneg _) hF_sum]
    exact ENNReal.ofReal_ne_top
  have hswap := integral_tsum (fun n => (hF_int n).aestronglyMeasurable) hF_enorm
  have hInt_F : ∀ n : ℕ, ∫ p : ℝ × ℝ, F n p ∂(μ.prod μ) =
      cohnC a n ^ 2 * stieltjesPhi μ (h * cohnE n) ^ 2 * cohnL n u ^ 2 := by
    intro n
    have hmul : (fun p : ℝ × ℝ => F n p) = fun p : ℝ × ℝ =>
        (cohnC a n ^ 2 * cohnL n u ^ 2) *
          ((1 + p.1 * (h * cohnE n))⁻¹ * (1 + p.2 * (h * cohnE n))⁻¹) := by
      funext p
      dsimp [F]
      have hden1 : 1 + p.1 * (h * cohnE n) = 1 + p.1 * h * cohnE n := by ring
      have hden2 : 1 + p.2 * (h * cohnE n) = 1 + p.2 * h * cohnE n := by ring
      rw [hden1, hden2, div_eq_mul_inv, mul_inv]
    rw [hmul, MeasureTheory.integral_const_mul,
      integral_prod_mul (f := fun s => (1 + s * (h * cohnE n))⁻¹)
        (g := fun s => (1 + s * (h * cohnE n))⁻¹), ← sq]
    change (cohnC a n ^ 2 * cohnL n u ^ 2) * (stieltjesPhi μ (h * cohnE n) ^ 2) = _
    ring
  have hTSum := summable_cohnT ha hua
  have hPhiSum : Summable (fun n : ℕ =>
      cohnC a n ^ 2 * stieltjesPhi μ (h * cohnE n) ^ 2 * cohnL n u ^ 2) := by
    refine hF_sum.congr fun n => ?_
    rw [← hInt_F n]
    refine integral_congr_ae ?_
    filter_upwards [hprod_pos] with p hp
    have hpos : 0 ≤ F n p := by
      dsimp [F]
      exact div_nonneg (by positivity) (mul_pos (one_add_mul_cohnE_pos (mul_nonneg hp.1.le hh) n)
        (one_add_mul_cohnE_pos (mul_nonneg hp.2.le hh) n)).le
    exact Real.norm_of_nonneg hpos
  have hS_eq : cohnS a (stieltjesPhi μ) h u =
      cohnT a u - ∑' n : ℕ, cohnC a n ^ 2 * stieltjesPhi μ (h * cohnE n) ^ 2 * cohnL n u ^ 2 := by
    unfold cohnS cohnT
    rw [← hTSum.tsum_sub hPhiSum]
    congr 1; funext n; ring
  rw [hS_eq]
  simp_rw [← hInt_F]
  rw [← hswap]
  rfl

/-! ### Exact three-Airy-function coefficient decomposition `(CR.9)` -/

/-- The `Ai(u)²` rational coefficient in `G_q(u)` (`cecr:CR.2`). -/
noncomputable def closedResolventCoeffA (a q u : ℝ) : ℝ :=
  let z := airyZero 1 + q⁻¹
  q⁻¹ * (cohnM z / ((z - a) ^ 2 * (z - u) ^ 2)
    + (2 * a * u - a * z - u * z) / ((u - a) ^ 2 * (z - a) * (z - u)))

/-- The `Ai(u) Ai'(u)` rational coefficient in `G_q(u)` (`cecr:CR.2`). -/
noncomputable def closedResolventCoeffB (a q u : ℝ) : ℝ :=
  let z := airyZero 1 + q⁻¹
  q⁻¹ * ((a - 3 * u + 2 * z) / ((u - a) ^ 3 * (z - u) ^ 2))

/-- The `Ai'(u)²` rational coefficient in `G_q(u)` (`cecr:CR.2`). -/
noncomputable def closedResolventCoeffC (a q u : ℝ) : ℝ :=
  let z := airyZero 1 + q⁻¹
  q⁻¹ * (1 / ((u - a) ^ 2 * (z - u)))

lemma closedResolventRHS_eq_three_airy (a q u : ℝ) :
    closedResolventRHS a q u =
      closedResolventCoeffA a q u * airyAi u ^ 2 +
        closedResolventCoeffB a q u * (airyAi u * airyAi' u) +
        closedResolventCoeffC a q u * airyAi' u ^ 2 := by
  unfold closedResolventRHS closedResolventCoeffA closedResolventCoeffB closedResolventCoeffC
  ring

/-- The three-Airy-function coefficients of `G_{s,t;h}(u)` off the diagonal `s ≠ t` (`(CR.9)`). -/
noncomputable def cohnG2CoeffA (a h s t u : ℝ) : ℝ :=
  (s * closedResolventCoeffA a (s * h) u - t * closedResolventCoeffA a (t * h) u) / (s - t)

noncomputable def cohnG2CoeffB (a h s t u : ℝ) : ℝ :=
  (s * closedResolventCoeffB a (s * h) u - t * closedResolventCoeffB a (t * h) u) / (s - t)

noncomputable def cohnG2CoeffC (a h s t u : ℝ) : ℝ :=
  (s * closedResolventCoeffC a (s * h) u - t * closedResolventCoeffC a (t * h) u) / (s - t)

/-- **Eq. `(CR.9)` (double-resolvent three-Airy decomposition):**
For `s ≠ t`, `s, t, h > 0`, `z_s ≠ a`, `z_t ≠ a`, `u ∉ {a, z_s, z_t}` (in particular `u < a_1`),
`G_{s,t;h}(u) = A_{s,t;h}(u) Ai(u)² + B_{s,t;h}(u) Ai(u) Ai'(u) + C_{s,t;h}(u) Ai'(u)²`,
with coefficients `cohnG2CoeffA/B/C` free of `u`-Airy-zero poles. -/
theorem cohnG2_eq_three_airy {a h s t u : ℝ} (ha : airyAi' a = 0) (hs : 0 < s) (ht : 0 < t)
    (hh : 0 < h) (hst : s ≠ t)
    (hzs : airyZero 1 + (s * h)⁻¹ ≠ a) (hzt : airyZero 1 + (t * h)⁻¹ ≠ a)
    (hua : u ≠ a) (huzs : u ≠ airyZero 1 + (s * h)⁻¹) (huzt : u ≠ airyZero 1 + (t * h)⁻¹) :
    cohnG2 a h s t u =
      cohnG2CoeffA a h s t u * airyAi u ^ 2 +
        cohnG2CoeffB a h s t u * (airyAi u * airyAi' u) +
        cohnG2CoeffC a h s t u * airyAi' u ^ 2 := by
  rw [cohnG2_eq_offDiag ha hua hs.le ht.le hh.le hst,
    cohnG_eq ha (mul_pos hs hh) hzs hua huzs,
    cohnG_eq ha (mul_pos ht hh) hzt hua huzt,
    closedResolventRHS_eq_three_airy, closedResolventRHS_eq_three_airy]
  unfold cohnG2CoeffA cohnG2CoeffB cohnG2CoeffC
  ring

/-- info: 'FormalResearch.CohnElkies.one_sub_t_mul_deriv_cohnWt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_sub_t_mul_deriv_cohnWt

/-- info: 'FormalResearch.CohnElkies.cohnG2_le_cohnT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cohnG2_le_cohnT

/-- info: 'FormalResearch.CohnElkies.cohnG_smul_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cohnG_smul_hasDerivAt

/-- info: 'FormalResearch.CohnElkies.stieltjesQ_eq_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stieltjesQ_eq_mixture

/-- info: 'FormalResearch.CohnElkies.cohnS_eq_sub_doubleIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cohnS_eq_sub_doubleIntegral

/-- info: 'FormalResearch.CohnElkies.cohnG2_eq_three_airy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cohnG2_eq_three_airy

end FormalResearch.CohnElkies