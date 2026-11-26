/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Non-stationary integration by parts near the edge (`fct:edge-ibp`, Lemma FCT.5a)

Formalizes **Lemma FCT.5a** (`fct:edge-ibp`) of Paper I
(`CFT/sign_uncertainty/paper/constant_terms_five.tex`, lines 524–537):
- Part (1) *(Removing an edge cutoff)*: for `n ≥ 1`, `0 ≤ j < n`, and a smooth cutoff
  `ψ₀ ∈ C_c^∞((-2, 2))` with `ψ₀ ≡ 1` on `[-1, 1]`, the Abel-regularised integral
  `lim_{ε ↓ 0} ∫_ℝ (1 - ψ₀(τ/r)) (λ + iτ)^{-1/2} τ^j e^{icuτ - ετ²} dτ` exists and is bounded by
  `C_{n,j,ψ₀} (cu)^{-n} r^{j + 1/2 - n}` uniformly in `c > 0`, `u > 0`, `λ ≥ 0`, `0 < r ≤ 1`.
- Part (2) *(Shoulder)*: for `a ∈ C^n(ℝ, ℂ)` vanishing for `|τ| < r`, real `Φ` of class `C^{n+1}`
  on `{|τ| > r}` with `|Φ'| ≥ κ u` and `|Φ^{(k+1)}| ≤ K_k w^{-k} |Φ'|` (`w(τ) = min(|τ|, 1)`),
  and `|a^{(k)}(τ)| ≤ A w(τ)^{-k} |τ|^{-1/2} (1 + |τ|)^{-2}`, one has
  `‖∫_ℝ a(τ) e^{icΦ(τ)} dτ‖ ≤ C(n, κ, K) A (cu)^{-n} r^{1/2 - n}`.

Note on scope: the paper states `c ≥ 1` and `ψ₀` even; neither is needed (the proof works for all
`c > 0` and any `ψ₀ ∈ C_c^∞((-2, 2))` with `ψ₀ ≡ 1` on `[-1, 1]`).
-/

public section

namespace FormalResearch.SignUncertainty.FctEdgeIbp

open scoped Topology
open MeasureTheory Set Filter Complex

/-- The edge weight `w(τ) = min(|τ|, 1)`. -/
def edgeW (τ : ℝ) : ℝ := min |τ| 1

lemma edgeW_pos {τ : ℝ} (hτ : τ ≠ 0) : 0 < edgeW τ :=
  lt_min (abs_pos.mpr hτ) one_pos

lemma edgeW_le_abs (τ : ℝ) : edgeW τ ≤ |τ| := min_le_left _ _

lemma edgeW_le_one (τ : ℝ) : edgeW τ ≤ 1 := min_le_right _ _

lemma edgeW_neg (τ : ℝ) : edgeW (-τ) = edgeW τ := by simp [edgeW]

lemma edgeW_ge_r {r τ : ℝ} (hr1 : r ≤ 1) (hτ : r ≤ |τ|) : r ≤ edgeW τ :=
  le_min hτ hr1

/-! ### Small calculus and measure helpers -/

private lemma integral_Iio_neg_eq_Ioi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (f : ℝ → E) :
    ∫ τ in Iio (-r), f τ = ∫ τ in Ioi r, f (-τ) := by
  rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_neg_eq_self (fun τ => (Ioi r).indicator (fun s => f (-s)) τ)]
  congr 1; ext τ
  by_cases h : τ < -r
  · have h1 : τ ∈ Iio (-r) := h
    have h2 : -τ ∈ Ioi r := by simp [mem_Ioi]; linarith
    simp [h1, h2]
  · have h1 : τ ∉ Iio (-r) := h
    have h2 : -τ ∉ Ioi r := by simp [mem_Ioi]; linarith
    simp [h1, h2]

private lemma integrableOn_Iio_neg_iff_Ioi {E : Type*} [NormedAddCommGroup E]
    (r : ℝ) (f : ℝ → E) :
    IntegrableOn f (Iio (-r)) ↔ IntegrableOn (fun τ => f (-τ)) (Ioi r) := by
  rw [← integrable_indicator_iff measurableSet_Iio, ← integrable_indicator_iff measurableSet_Ioi]
  have heq : (Iio (-r)).indicator f = fun τ => (Ioi r).indicator (fun s => f (-s)) (-τ) := by
    ext τ
    by_cases h : τ < -r
    · have h1 : τ ∈ Iio (-r) := h
      have h2 : -τ ∈ Ioi r := by simp [mem_Ioi]; linarith
      simp [h1, h2]
    · have h1 : τ ∉ Iio (-r) := h
      have h2 : -τ ∉ Ioi r := by simp [mem_Ioi]; linarith
      simp [h1, h2]
  rw [heq]
  exact ⟨fun h => by simpa using h.comp_neg, fun h => h.comp_neg⟩

private lemma iteratedDeriv_comp_const_mul (k : ℕ) (f : ℝ → ℝ) (a : ℝ) :
    ∀ x : ℝ, iteratedDeriv k (fun t => f (a * t)) x = a ^ k * iteratedDeriv k f (a * x) := by
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [iteratedDeriv_succ, show iteratedDeriv k (fun t => f (a * t)) =
        fun t => a ^ k * iteratedDeriv k f (a * t) from funext ih,
      deriv_const_mul_field']
    dsimp only
    rw [deriv_comp_mul_left a (iteratedDeriv k f) x, ← iteratedDeriv_succ, pow_succ]
    ring

private lemma iteratedDeriv_ofReal_comp (k : ℕ) (f : ℝ → ℝ) :
    ∀ x : ℝ, iteratedDeriv k (fun t : ℝ => (f t : ℂ)) x = ((iteratedDeriv k f x : ℝ) : ℂ) := by
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [iteratedDeriv_succ, iteratedDeriv_succ,
      show iteratedDeriv k (fun t : ℝ => (f t : ℂ)) = fun t => ((iteratedDeriv k f t : ℝ) : ℂ) from funext ih]
    by_cases hd : DifferentiableAt ℝ (iteratedDeriv k f) x
    · exact (hd.hasDerivAt.ofReal_comp).deriv
    · have hdC : ¬ DifferentiableAt ℝ (fun t : ℝ => ((iteratedDeriv k f t : ℝ) : ℂ)) x := fun h =>
        hd (Complex.reCLM.differentiableAt.comp x h)
      rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hdC, Complex.ofReal_zero]

private lemma iteratedDeriv_const_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (c : E) (x : ℝ) :
    iteratedDeriv (k + 1) (fun _ : ℝ => c) x = 0 := by
  rw [iteratedDeriv_succ', deriv_const', show (fun _ : ℝ => (0 : E)) = 0 from rfl, iteratedDeriv_const_zero]

private lemma descFactorial_le_factorial_local (d k : ℕ) (hk : k ≤ d) :
    d.descFactorial k ≤ d.factorial := by
  have hmul : ∀ m ≤ d, d.descFactorial m * (d - m).factorial = d.factorial := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [Nat.descFactorial_succ]
      have h1 : d - m = (d - (m + 1)) + 1 := by omega
      have hfac : (d - m).factorial = (d - m) * (d - (m + 1)).factorial := by
        conv_lhs => rw [h1, Nat.factorial_succ, ← h1]
      calc (d - m) * d.descFactorial m * (d - (m + 1)).factorial
          = d.descFactorial m * ((d - m) * (d - (m + 1)).factorial) := by ring
        _ = d.descFactorial m * (d - m).factorial := by rw [← hfac]
        _ = d.factorial := ih (by omega)
  have h := hmul k hk
  exact Nat.le_of_mul_le_mul_right (by rw [h]; exact Nat.le_mul_of_pos_right _ (Nat.factorial_pos _))
    (Nat.factorial_pos _)

private lemma contDiffOn_iteratedDeriv_of_isOpen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set ℝ} (hs : IsOpen s) {f : ℝ → E} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) :
    ∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv k f) s := by
  intro k
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv_of_isOpen hs (by simp)

private lemma tendsto_finset_sum_local {ι α E : Type*} [NormedAddCommGroup E]
    {F : Filter α} (s : Finset ι) {f : ι → α → E} {a : ι → E}
    (h : ∀ i ∈ s, Tendsto (f i) F (𝓝 (a i))) :
    Tendsto (fun x => ∑ i ∈ s, f i x) F (𝓝 (∑ i ∈ s, a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tendsto_const_nhds]
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-! ### Elementary `L¹` integral bounds on `(r, ∞)` -/

lemma integrableOn_rpow_Ioi_lt_neg_one {r s : ℝ} (hr : 0 < r) (hs : s < -1) :
    IntegrableOn (fun t : ℝ => t ^ s) (Ioi r) ∧
    ∫ t in Ioi r, t ^ s = -(r ^ (s + 1)) / (s + 1) := by
  have hint := integrableOn_Ioi_rpow_of_lt hs hr
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_rpow_of_lt hs hr]

lemma integral_rpow_Ioi_bound {r s : ℝ} (hr : 0 < r) (hs : s < -1) :
    ∫ t in Ioi r, t ^ s = r ^ (s + 1) / (-(s + 1)) := by
  rw [(integrableOn_rpow_Ioi_lt_neg_one hr hs).2, neg_div, div_neg]

lemma integrableOn_shoulder_weight {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    IntegrableOn (fun t : ℝ => edgeW t ^ (-(n : ℤ)) * t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-2 : ℤ)) (Ioi r) ∧
    ∫ t in Ioi r, edgeW t ^ (-(n : ℤ)) * t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-2 : ℤ) ≤
      (2 / ((n : ℝ) - 1 / 2) + 1) * r ^ (1 / 2 - (n : ℝ)) := by
  -- Split `Ioi r = Ioc r 1 ∪ Ioi 1`
  have hs_lt : -(n : ℝ) - 1 / 2 < -1 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hpow_int := integrableOn_rpow_Ioi_lt_neg_one hr0 hs_lt
  have hinv2_int := integrableOn_rpow_Ioi_lt_neg_one (r := 1) one_pos (s := -2) (by norm_num)
  have hcont : ContinuousOn (fun t : ℝ => edgeW t ^ (-(n : ℤ)) * t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-2 : ℤ)) (Ioi r) := by
    have hw : ContinuousOn edgeW (Ioi r) := (continuous_abs.min continuous_const).continuousOn
    refine ((hw.zpow₀ _ fun t ht => Or.inl (edgeW_pos (hr0.trans ht).ne').ne').mul
      (continuousOn_id.rpow_const fun t ht => Or.inl (hr0.trans ht).ne')).mul
      ((continuousOn_const.add continuousOn_id).zpow₀ _ fun t ht => Or.inl (by
        have : 0 < t := hr0.trans ht; show (1 : ℝ) + t ≠ 0; linarith))
  have h01 : IntegrableOn (fun t : ℝ => edgeW t ^ (-(n : ℤ)) * t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-2 : ℤ)) (Ioc r 1) ∧
      ∫ t in Ioc r 1, edgeW t ^ (-(n : ℤ)) * t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-2 : ℤ) ≤
        r ^ (1 / 2 - (n : ℝ)) / ((n : ℝ) - 1 / 2) := by
    have hpt : ∀ t ∈ Ioc r 1,
        ‖edgeW t ^ (-(n : ℤ)) * t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-2 : ℤ)‖ ≤ t ^ (-(n : ℝ) - 1 / 2) := by
      intro t ht
      have ht0 : 0 < t := hr0.trans ht.1
      have hw_eq : edgeW t = t := by
        simp only [edgeW, abs_of_pos ht0, min_eq_left ht.2]
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        have := edgeW_pos ht0.ne'
        have := Real.rpow_pos_of_pos ht0 (-(1 / 2 : ℝ))
        positivity)]
      rw [hw_eq]
      have h1t : (1 + t) ^ (-2 : ℤ) ≤ 1 := by
        rw [zpow_neg, show (1 + t) ^ (2 : ℤ) = (1 + t) ^ 2 by norm_cast]
        exact inv_le_one_of_one_le₀ (by nlinarith)
      have hpow_eq : t ^ (-(n : ℤ)) * t ^ (-(1 / 2 : ℝ)) = t ^ (-(n : ℝ) - 1 / 2) := by
        rw [← Real.rpow_intCast t (-(n : ℤ)), ← Real.rpow_add ht0]
        congr 1; push_cast; ring
      calc t ^ (-(n : ℤ)) * t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-2 : ℤ)
          ≤ t ^ (-(n : ℤ)) * t ^ (-(1 / 2 : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left h1t (mul_nonneg (zpow_nonneg ht0.le _) (Real.rpow_nonneg ht0.le _))
        _ = t ^ (-(n : ℝ) - 1 / 2) := by rw [mul_one, hpow_eq]
    have hint : IntegrableOn (fun t : ℝ => edgeW t ^ (-(n : ℤ)) * t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-2 : ℤ)) (Ioc r 1) :=
      (hpow_int.1.mono_set Ioc_subset_Ioi_self).mono'
        ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
        (ae_restrict_of_forall_mem measurableSet_Ioc hpt)
    refine ⟨hint, ?_⟩
    have hle1 : ∫ t in Ioc r 1, edgeW t ^ (-(n : ℤ)) * t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-2 : ℤ) ≤
        ∫ t in Ioc r 1, t ^ (-(n : ℝ) - 1 / 2) :=
      setIntegral_mono_on hint (hpow_int.1.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc fun t ht => by
        have h := hpt t ht
        rw [Real.norm_eq_abs] at h
        exact (le_abs_self _).trans h
    have hle2 : ∫ t in Ioc r 1, t ^ (-(n : ℝ) - 1 / 2) ≤ ∫ t in Ioi r, t ^ (-(n : ℝ) - 1 / 2) :=
      setIntegral_mono_set hpow_int.1
        (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => Real.rpow_nonneg (hr0.trans ht).le _)
        (Filter.Eventually.of_forall Ioc_subset_Ioi_self)
    have heq : ∫ t in Ioi r, t ^ (-(n : ℝ) - 1 / 2) = r ^ (1 / 2 - (n : ℝ)) / ((n : ℝ) - 1 / 2) := by
      rw [hpow_int.2, neg_div, ← div_neg]
      congr 1
      · congr 1; ring
      · ring
    linarith
  have h1inf : IntegrableOn (fun t : ℝ => edgeW t ^ (-(n : ℤ)) * t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-2 : ℤ)) (Ioi 1) ∧
      ∫ t in Ioi 1, edgeW t ^ (-(n : ℤ)) * t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-2 : ℤ) ≤ 1 := by
    have hpt : ∀ t ∈ Ioi (1 : ℝ),
        ‖edgeW t ^ (-(n : ℤ)) * t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-2 : ℤ)‖ ≤ t ^ (-2 : ℝ) := by
      intro t ht
      have ht1 : 1 ≤ t := (mem_Ioi.mp ht).le
      have ht0 : 0 < t := zero_lt_one.trans ht
      have hw_eq : edgeW t = 1 := by simp only [edgeW, abs_of_pos ht0, min_eq_right ht1]
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        have := edgeW_pos ht0.ne'
        have := Real.rpow_pos_of_pos ht0 (-(1 / 2 : ℝ))
        positivity), hw_eq, one_zpow, one_mul]
      have htr : t ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num)
      have h1t : (1 + t) ^ (-2 : ℤ) ≤ t ^ (-2 : ℝ) := by
        rw [zpow_neg, show (1 + t) ^ (2 : ℤ) = (1 + t) ^ 2 by norm_cast,
          show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast]
        exact inv_anti₀ (sq_pos_of_pos ht0) (by nlinarith)
      calc t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-2 : ℤ)
          ≤ 1 * (1 + t) ^ (-2 : ℤ) := mul_le_mul_of_nonneg_right htr (zpow_nonneg (by linarith) _)
        _ = (1 + t) ^ (-2 : ℤ) := one_mul _
        _ ≤ t ^ (-2 : ℝ) := h1t
    have hint : IntegrableOn (fun t : ℝ => edgeW t ^ (-(n : ℤ)) * t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-2 : ℤ)) (Ioi 1) :=
      hinv2_int.1.mono'
        ((hcont.mono (fun t (ht : t ∈ Ioi 1) => lt_of_le_of_lt hr1 ht)).aestronglyMeasurable measurableSet_Ioi)
        (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
    refine ⟨hint, ?_⟩
    have hle := setIntegral_mono_on hint hinv2_int.1 measurableSet_Ioi fun t ht => by
      have h := hpt t ht; rw [Real.norm_eq_abs] at h; exact (le_abs_self _).trans h
    rw [hinv2_int.2] at hle
    exact hle.trans (by norm_num)
  have hunion : Ioc r 1 ∪ Ioi 1 = Ioi r := Ioc_union_Ioi_eq_Ioi hr1
  have hint_all : IntegrableOn (fun t : ℝ => edgeW t ^ (-(n : ℤ)) * t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-2 : ℤ)) (Ioi r) := by
    rw [← hunion]; exact h01.1.union h1inf.1
  refine ⟨hint_all, ?_⟩
  rw [← hunion, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h01.1 h1inf.1]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hr_ge1 : 1 ≤ r ^ (1 / 2 - (n : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr0 hr1 (by linarith)
  have hn_pos : (0 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
  have h1_le : r ^ (1 / 2 - (n : ℝ)) / ((n : ℝ) - 1 / 2) ≤ (2 / ((n : ℝ) - 1 / 2)) * r ^ (1 / 2 - (n : ℝ)) := by
    rw [show r ^ (1 / 2 - (n : ℝ)) / ((n : ℝ) - 1 / 2) = (1 / ((n : ℝ) - 1 / 2)) * r ^ (1 / 2 - (n : ℝ)) by ring]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by norm_num) hn_pos.le) (Real.rpow_nonneg hr0.le _)
  linarith

/-! ### Integration by parts on `(r, ∞)` -/

lemma tendsto_setIntegral_Ioi_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} {f : ℝ → E} (hf : IntegrableOn f (Ioi r)) :
    Tendsto (fun a : ℝ => ∫ t in Ioi a, f t) (𝓝[>] r) (𝓝 (∫ t in Ioi r, f t)) := by
  have hdom : Tendsto (fun a : ℝ => ∫ t : ℝ, (Ioi a).indicator f t) (𝓝[>] r)
      (𝓝 (∫ t : ℝ, (Ioi r).indicator f t)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖(Ioi r).indicator f t‖) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with a ha
      have hm := (integrable_indicator_iff measurableSet_Ioi).mpr hf
      exact (hm.aestronglyMeasurable.indicator (s := Ioi a) measurableSet_Ioi).congr
        (Filter.Eventually.of_forall fun t => by
          by_cases h1 : t ∈ Ioi r <;> by_cases h2 : t ∈ Ioi a
          · simp [h1, h2]
          · simp [h2]
          · exact absurd (lt_trans ha h2) h1
          · simp [h2])
    · filter_upwards [self_mem_nhdsWithin] with a ha
      refine Filter.Eventually.of_forall fun t => ?_
      by_cases h2 : t ∈ Ioi a
      · have h1 : t ∈ Ioi r := lt_trans ha h2
        simp [h1, h2]
      · simp [h2]
    · exact ((integrable_indicator_iff measurableSet_Ioi).mpr hf).norm
    · refine Filter.Eventually.of_forall fun t => ?_
      by_cases ht : r < t
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT ht] with a ha
        have h1 : t ∈ Ioi r := ht
        have h2 : t ∈ Ioi a := ha.2
        simp [h1, h2]
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with a ha
        have h1 : t ∉ Ioi r := ht
        have h2 : t ∉ Ioi a := fun h => ht (lt_trans ha h)
        simp [h1, h2]
  simpa only [integral_indicator measurableSet_Ioi] using hdom

/-- Single step of oscillatory integration by parts on `(r, ∞)`:
`∫_{r}^∞ g(τ) e^{icΦ(τ)} dτ = ∫_{r}^∞ (-∂_τ(g / (ic Φ')))(τ) e^{icΦ(τ)} dτ`. -/
lemma ibp_osc_Ioi {r c : ℝ} (hc : c ≠ 0) {g : ℝ → ℂ} {Φ : ℝ → ℝ}
    (hg_diff : ∀ τ ∈ Ioi r, DifferentiableAt ℝ g τ)
    (hΦ_diff : ∀ τ ∈ Ioi r, DifferentiableAt ℝ Φ τ)
    (hΦ'_diff : ∀ τ ∈ Ioi r, DifferentiableAt ℝ (deriv Φ) τ)
    (hΦ'_ne : ∀ τ ∈ Ioi r, deriv Φ τ ≠ 0)
    (hg_int : IntegrableOn (fun τ : ℝ => g τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) (Ioi r))
    (hDg_int : IntegrableOn (fun τ : ℝ =>
      (-deriv (fun s => g s / (Complex.I * (c : ℂ) * ((deriv Φ s : ℝ) : ℂ))) τ) *
        Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) (Ioi r))
    (hlim_r : Tendsto (fun τ : ℝ => g τ / (Complex.I * (c : ℂ) * ((deriv Φ τ : ℝ) : ℂ))) (𝓝[>] r) (𝓝 0))
    (hlim_top : Tendsto (fun τ : ℝ => g τ / (Complex.I * (c : ℂ) * ((deriv Φ τ : ℝ) : ℂ))) atTop (𝓝 0)) :
    ∫ τ in Ioi r, g τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ)) =
      ∫ τ in Ioi r, (-deriv (fun s => g s / (Complex.I * (c : ℂ) * ((deriv Φ s : ℝ) : ℂ))) τ) *
        Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ)) := by
  let q : ℝ → ℂ := fun τ => g τ / (Complex.I * (c : ℂ) * ((deriv Φ τ : ℝ) : ℂ))
  let E : ℝ → ℂ := fun τ => Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))
  have hE_norm : ∀ τ : ℝ, ‖E τ‖ = 1 := fun τ => by
    simp only [E, show Complex.I * ((c * Φ τ : ℝ) : ℂ) = ((c * Φ τ : ℝ) : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I]
  have hq_diff : ∀ τ ∈ Ioi r, DifferentiableAt ℝ q τ := by
    intro τ hτ
    have hden : DifferentiableAt ℝ (fun s => Complex.I * (c : ℂ) * ((deriv Φ s : ℝ) : ℂ)) τ :=
      (Complex.ofRealCLM.differentiableAt.comp τ (hΦ'_diff τ hτ)).const_mul _
    have hden_ne : Complex.I * (c : ℂ) * ((deriv Φ τ : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hc))
        (Complex.ofReal_ne_zero.mpr (hΦ'_ne τ hτ))
    exact (hg_diff τ hτ).div hden hden_ne
  have hE_deriv : ∀ τ ∈ Ioi r, HasDerivAt E (Complex.I * (c : ℂ) * ((deriv Φ τ : ℝ) : ℂ) * E τ) τ := by
    intro τ hτ
    have h1 : HasDerivAt (fun s => ((c * Φ s : ℝ) : ℂ)) (((c * deriv Φ τ : ℝ) : ℂ)) τ :=
      ((hΦ_diff τ hτ).hasDerivAt.const_mul c).ofReal_comp
    have h2 : HasDerivAt (fun s => Complex.I * ((c * Φ s : ℝ) : ℂ)) (Complex.I * ((c * deriv Φ τ : ℝ) : ℂ)) τ :=
      h1.const_mul Complex.I
    refine (h2.cexp).congr_deriv ?_
    simp only [E]; push_cast; ring
  have hF_deriv : ∀ τ ∈ Ioi r,
      HasDerivAt (fun s => q s * E s) (deriv q τ * E τ + g τ * E τ) τ := by
    intro τ hτ
    have h1 := (hq_diff τ hτ).hasDerivAt.mul (hE_deriv τ hτ)
    refine h1.congr_deriv ?_
    have hden_ne : Complex.I * (c : ℂ) * ((deriv Φ τ : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hc))
        (Complex.ofReal_ne_zero.mpr (hΦ'_ne τ hτ))
    have hq_mul : q τ * (Complex.I * (c : ℂ) * ((deriv Φ τ : ℝ) : ℂ) * E τ) = g τ * E τ := by
      simp only [q]
      rw [← mul_assoc, div_mul_cancel₀ _ hden_ne]
    rw [hq_mul]
  -- On `(a, ∞)` for any `a > r`, `∫_a^∞ (q' E + g E) = -q(a) E(a)`
  have hIoi_a : ∀ a ∈ Ioi r,
      (∫ τ in Ioi a, deriv q τ * E τ) + (∫ τ in Ioi a, g τ * E τ) = -(q a * E a) := by
    intro a ha
    have hsub : Ioi a ⊆ Ioi r := fun τ hτ => ha.trans hτ
    have hg_a : IntegrableOn (fun τ => g τ * E τ) (Ioi a) := hg_int.mono_set hsub
    have hq'_a : IntegrableOn (fun τ => deriv q τ * E τ) (Ioi a) := by
      have := (hDg_int.mono_set hsub).neg
      refine this.congr_fun (fun τ _ => by simp only [Pi.neg_apply, q, E, neg_mul, neg_neg]) measurableSet_Ioi
    have hsum_a : IntegrableOn (fun τ => deriv q τ * E τ + g τ * E τ) (Ioi a) := hq'_a.add hg_a
    have hFTC : ∀ b : ℝ, a ≤ b →
        ∫ τ in a..b, (deriv q τ * E τ + g τ * E τ) = q b * E b - q a * E a := by
      intro b hab
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun s => q s * E s) (f' := fun τ => deriv q τ * E τ + g τ * E τ)
        (fun τ hτ => ?_) ?_
      · rw [uIcc_of_le hab] at hτ
        exact hF_deriv τ (lt_of_lt_of_le ha hτ.1)
      · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
          (hsum_a.mono_set Ioc_subset_Ioi_self)
    have hlim_int : Tendsto (fun b : ℝ => ∫ τ in a..b, (deriv q τ * E τ + g τ * E τ)) atTop
        (𝓝 (∫ τ in Ioi a, (deriv q τ * E τ + g τ * E τ))) :=
      intervalIntegral_tendsto_integral_Ioi a hsum_a tendsto_id
    have hlim_qE : Tendsto (fun b : ℝ => q b * E b) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h1 : (fun b : ℝ => ‖q b * E b‖) = fun b => ‖q b‖ := by
        ext b; rw [norm_mul, hE_norm, mul_one]
      rw [h1]
      exact tendsto_zero_iff_norm_tendsto_zero.mp hlim_top
    have hlim_rhs : Tendsto (fun b : ℝ => q b * E b - q a * E a) atTop (𝓝 (-(q a * E a))) := by
      simpa using hlim_qE.sub_const (q a * E a)
    have heq_sum : ∫ τ in Ioi a, (deriv q τ * E τ + g τ * E τ) = -(q a * E a) := by
      refine tendsto_nhds_unique hlim_int (hlim_rhs.congr' ?_)
      filter_upwards [eventually_ge_atTop a] with b hab
      exact (hFTC b hab).symm
    rw [← heq_sum, integral_add hq'_a hg_a]
  -- Now let `a → r⁺`
  have hlim_lhs : Tendsto (fun a : ℝ => (∫ τ in Ioi a, deriv q τ * E τ) + (∫ τ in Ioi a, g τ * E τ))
      (𝓝[>] r) (𝓝 ((∫ τ in Ioi r, deriv q τ * E τ) + (∫ τ in Ioi r, g τ * E τ))) := by
    have hq'_r : IntegrableOn (fun τ => deriv q τ * E τ) (Ioi r) := by
      have := hDg_int.neg
      refine this.congr_fun (fun τ _ => by simp only [Pi.neg_apply, q, E, neg_mul, neg_neg]) measurableSet_Ioi
    exact (tendsto_setIntegral_Ioi_right hq'_r).add (tendsto_setIntegral_Ioi_right hg_int)
  have hlim_rhs : Tendsto (fun a : ℝ => -(q a * E a)) (𝓝[>] r) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 : (fun a : ℝ => ‖-(q a * E a)‖) = fun a => ‖q a‖ := by
      ext a; rw [norm_neg, norm_mul, hE_norm, mul_one]
    rw [h1]
    exact tendsto_zero_iff_norm_tendsto_zero.mp hlim_r
  have hsum_zero : (∫ τ in Ioi r, deriv q τ * E τ) + (∫ τ in Ioi r, g τ * E τ) = 0 := by
    refine tendsto_nhds_unique hlim_lhs (hlim_rhs.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact (hIoi_a a ha).symm
  have hneg : ∫ τ in Ioi r, (-deriv q τ) * E τ = -(∫ τ in Ioi r, deriv q τ * E τ) := by
    simp_rw [neg_mul]
    exact integral_neg _
  rw [hneg]
  exact eq_neg_of_add_eq_zero_right hsum_zero

/-! ### Derivative bounds for `1 / Φ'` via Leibniz rule -/

private def invDerivB (K : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => ∑ j ∈ Finset.range (k + 1), ((k + 1).choose (j + 1) : ℝ) * K (j + 1) * invDerivB K (k - j)

lemma iteratedDeriv_inv_deriv_bound {n : ℕ} {K : ℕ → ℝ} (hK_nn : ∀ k, 0 ≤ K k) :
    ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k) ∧
      ∀ {r : ℝ} {Φ : ℝ → ℝ}, 0 < r → r ≤ 1 →
        ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Φ {τ : ℝ | r < |τ|} →
        (∀ τ, r < |τ| → deriv Φ τ ≠ 0) →
        (∀ k, 1 ≤ k → k ≤ n → ∀ τ, r < |τ| →
          |iteratedDeriv (k + 1) Φ τ| ≤ K k * edgeW τ ^ (-(k : ℤ)) * |deriv Φ τ|) →
        ∀ k ≤ n, ∀ τ, r < |τ| →
          |iteratedDeriv k (fun s => (deriv Φ s)⁻¹) τ| ≤
            B k * edgeW τ ^ (-(k : ℤ)) / |deriv Φ τ| := by
  have hB_nn : ∀ k, 0 ≤ invDerivB K k := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      cases k with
      | zero => simp [invDerivB]
      | succ k =>
        simp only [invDerivB]
        refine Finset.sum_nonneg fun j hj => ?_
        have hlt : k - j < k + 1 := by omega
        have := ih (k - j) hlt
        have := hK_nn (j + 1)
        positivity
  refine ⟨invDerivB K, hB_nn, fun {r Φ} hr0 hr1 hΦ_cd hΦ'_ne hΦ_bd k hk => ?_⟩
  have hopen : IsOpen {τ : ℝ | r < |τ|} := isOpen_lt continuous_const continuous_abs
  have hΦ'_cd : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (deriv Φ) {τ : ℝ | r < |τ|} :=
    hΦ_cd.deriv_of_isOpen hopen (m := (n : ℕ)) (by norm_cast)
  have hinv_cd : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun s => (deriv Φ s)⁻¹) {τ : ℝ | r < |τ|} :=
    hΦ'_cd.inv fun τ hτ => hΦ'_ne τ hτ
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro τ hτ
    have hw_pos : 0 < edgeW τ := edgeW_pos (by intro h; rw [h, abs_zero] at hτ; linarith)
    have hd_pos : 0 < |deriv Φ τ| := abs_pos.mpr (hΦ'_ne τ hτ)
    cases k with
    | zero =>
      simp only [iteratedDeriv_zero, invDerivB, Nat.cast_zero, neg_zero, zpow_zero, mul_one, abs_inv, one_div]
      exact le_rfl
    | succ k =>
      have hk_le : k + 1 ≤ n := hk
      have hprod_eq : (fun s => deriv Φ s * (deriv Φ s)⁻¹) =ᶠ[𝓝 τ] (fun _ => (1 : ℝ)) := by
        filter_upwards [hopen.mem_nhds hτ] with s hs
        exact mul_inv_cancel₀ (hΦ'_ne s hs)
      have hleib : iteratedDeriv (k + 1) (fun s => deriv Φ s * (deriv Φ s)⁻¹) τ = 0 := by
        rw [hprod_eq.iteratedDeriv_eq (k + 1), iteratedDeriv_const_succ]
      have hΦ'_at : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (deriv Φ) τ :=
        (hΦ'_cd.contDiffAt (hopen.mem_nhds hτ)).of_le (by exact_mod_cast hk_le)
      have hinv_at : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun s => (deriv Φ s)⁻¹) τ :=
        (hinv_cd.contDiffAt (hopen.mem_nhds hτ)).of_le (by exact_mod_cast hk_le)
      rw [show (fun s => deriv Φ s * (deriv Φ s)⁻¹) = deriv Φ * (fun s => (deriv Φ s)⁻¹) from rfl,
        iteratedDeriv_mul hΦ'_at hinv_at, Finset.sum_range_succ'] at hleib
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero, Nat.sub_zero] at hleib
      have hisol : deriv Φ τ * iteratedDeriv (k + 1) (fun s => (deriv Φ s)⁻¹) τ =
          -(∑ j ∈ Finset.range (k + 1),
            ((k + 1).choose (j + 1) : ℝ) * iteratedDeriv (j + 1) (deriv Φ) τ *
              iteratedDeriv (k - j) (fun s => (deriv Φ s)⁻¹) τ) := by
        have hsub : ∀ j ∈ Finset.range (k + 1), k + 1 - (j + 1) = k - j := fun _ _ => by omega
        have heq_sum : ∑ j ∈ Finset.range (k + 1),
            ((k + 1).choose (j + 1) : ℝ) * iteratedDeriv (j + 1) (deriv Φ) τ *
              iteratedDeriv (k + 1 - (j + 1)) (fun s => (deriv Φ s)⁻¹) τ =
            ∑ j ∈ Finset.range (k + 1),
              ((k + 1).choose (j + 1) : ℝ) * iteratedDeriv (j + 1) (deriv Φ) τ *
                iteratedDeriv (k - j) (fun s => (deriv Φ s)⁻¹) τ :=
          Finset.sum_congr rfl fun j hj => by rw [hsub j hj]
        rw [heq_sum] at hleib
        linarith
      have habs := congrArg abs hisol
      rw [abs_mul, abs_neg] at habs
      have hsum_le : |∑ j ∈ Finset.range (k + 1),
          ((k + 1).choose (j + 1) : ℝ) * iteratedDeriv (j + 1) (deriv Φ) τ *
            iteratedDeriv (k - j) (fun s => (deriv Φ s)⁻¹) τ| ≤
          invDerivB K (k + 1) * edgeW τ ^ (-((k + 1 : ℕ) : ℤ)) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        simp only [invDerivB, Finset.sum_mul]
        refine Finset.sum_le_sum fun j hj => ?_
        have hj_lt : j < k + 1 := Finset.mem_range.mp hj
        have h1 : |iteratedDeriv (j + 1) (deriv Φ) τ| ≤
            K (j + 1) * edgeW τ ^ (-((j + 1 : ℕ) : ℤ)) * |deriv Φ τ| := by
          rw [← iteratedDeriv_succ']
          exact hΦ_bd (j + 1) (by omega) (by omega) τ hτ
        have h2 : |iteratedDeriv (k - j) (fun s => (deriv Φ s)⁻¹) τ| ≤
            invDerivB K (k - j) * edgeW τ ^ (-((k - j : ℕ) : ℤ)) / |deriv Φ τ| :=
          ih (k - j) (by omega) (by omega) τ hτ
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        have hpow_mul : edgeW τ ^ (-((j + 1 : ℕ) : ℤ)) * edgeW τ ^ (-((k - j : ℕ) : ℤ)) =
            edgeW τ ^ (-((k + 1 : ℕ) : ℤ)) := by
          rw [← zpow_add₀ hw_pos.ne']
          congr 1; omega
        calc ((k + 1).choose (j + 1) : ℝ) * |iteratedDeriv (j + 1) (deriv Φ) τ| *
              |iteratedDeriv (k - j) (fun s => (deriv Φ s)⁻¹) τ|
            ≤ ((k + 1).choose (j + 1) : ℝ) * (K (j + 1) * edgeW τ ^ (-((j + 1 : ℕ) : ℤ)) * |deriv Φ τ|) *
              (invDerivB K (k - j) * edgeW τ ^ (-((k - j : ℕ) : ℤ)) / |deriv Φ τ|) := by
                have := hK_nn (j + 1); have := hB_nn (k - j)
                gcongr
          _ = ((k + 1).choose (j + 1) : ℝ) * K (j + 1) * invDerivB K (k - j) *
                (edgeW τ ^ (-((j + 1 : ℕ) : ℤ)) * edgeW τ ^ (-((k - j : ℕ) : ℤ))) := by
                field_simp [hd_pos.ne']
          _ = ((k + 1).choose (j + 1) : ℝ) * K (j + 1) * invDerivB K (k - j) * edgeW τ ^ (-((k + 1 : ℕ) : ℤ)) := by
                rw [hpow_mul]
      rw [le_div_iff₀ hd_pos, mul_comm _ |deriv Φ τ|, habs]
      exact hsum_le

/-! ### Part (2): Shoulder estimate -/

/-- One step of the shoulder IBP operator `g ↦ -∂_τ(g / (i c Φ'))` preserves smoothness,
boundary vanishing at `±r`, and multiplies the symbol bound by `C / (c κ u w(τ))`. -/
private lemma shoulder_ibp_step {m : ℕ} {B : ℕ → ℝ} (hB_nn : ∀ k, 0 ≤ B k)
    {r c u κ A : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hc : 0 < c) (hu : 0 < u) (hκ : 0 < κ) (hA : 0 ≤ A)
    {p : ℕ} {g : ℝ → ℂ} {Φ : ℝ → ℝ}
    (hg_cd : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) g {τ : ℝ | r < |τ|})
    (hg_bd : ∀ k ≤ m + 1, ∀ τ, r < |τ| →
      ‖iteratedDeriv k g τ‖ ≤ A * edgeW τ ^ (-((k + p : ℕ) : ℤ)) * |τ| ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-2 : ℤ))
    (hg_lim_r : ∀ k ≤ m, Tendsto (iteratedDeriv k g) (𝓝[>] r) (𝓝 0))
    (hg_lim_nr : ∀ k ≤ m, Tendsto (iteratedDeriv k g) (𝓝[<] (-r)) (𝓝 0))
    (hΦ_cd : ContDiffOn ℝ ((m + 2 : ℕ) : WithTop ℕ∞) Φ {τ : ℝ | r < |τ|})
    (hΦ'_lb : ∀ τ, r < |τ| → κ * u ≤ |deriv Φ τ|)
    (hinv_bd : ∀ k ≤ m + 1, ∀ τ, r < |τ| →
      |iteratedDeriv k (fun s => (deriv Φ s)⁻¹) τ| ≤ B k * edgeW τ ^ (-(k : ℤ)) / |deriv Φ τ|) :
    let Dg : ℝ → ℂ := fun τ => -deriv (fun s => g s / (Complex.I * (c : ℂ) * ((deriv Φ s : ℝ) : ℂ))) τ
    ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) Dg {τ : ℝ | r < |τ|} ∧
    (∀ k ≤ m, ∀ τ, r < |τ| →
      ‖iteratedDeriv k Dg τ‖ ≤
        (∑ j ∈ Finset.range (k + 2), ((k + 1).choose j : ℝ) * B (k + 1 - j)) *
        (A / (c * κ * u)) * edgeW τ ^ (-((k + (p + 1) : ℕ) : ℤ)) *
        |τ| ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-2 : ℤ)) ∧
    (∀ k < m, Tendsto (iteratedDeriv k Dg) (𝓝[>] r) (𝓝 0)) ∧
    (∀ k < m, Tendsto (iteratedDeriv k Dg) (𝓝[<] (-r)) (𝓝 0)) ∧
    (∫ τ in Ioi r, g τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) =
      (∫ τ in Ioi r, Dg τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) ∧
    (∫ τ in Iio (-r), g τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) =
      (∫ τ in Iio (-r), Dg τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) := by
  intro Dg
  have hopen : IsOpen {τ : ℝ | r < |τ|} := isOpen_lt continuous_const continuous_abs
  have hΦ'_ne : ∀ τ, r < |τ| → deriv Φ τ ≠ 0 := fun τ hτ =>
    abs_pos.mp (lt_of_lt_of_le (mul_pos hκ hu) (hΦ'_lb τ hτ))
  have hΦ'_cd : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (deriv Φ) {τ : ℝ | r < |τ|} :=
    hΦ_cd.deriv_of_isOpen hopen (m := (m + 1 : ℕ)) (by norm_cast)
  have hinv_cd : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun s => (deriv Φ s)⁻¹) {τ : ℝ | r < |τ|} :=
    hΦ'_cd.inv hΦ'_ne
  have hinvC_cd : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun s => (((deriv Φ s)⁻¹ : ℝ) : ℂ)) {τ : ℝ | r < |τ|} :=
    (Complex.ofRealCLM.contDiff.of_le le_top).comp_contDiffOn hinv_cd
  have hq_eq : EqOn (fun s => g s / (Complex.I * (c : ℂ) * ((deriv Φ s : ℝ) : ℂ)))
      (fun s => (Complex.I * (c : ℂ))⁻¹ * (g s * (((deriv Φ s)⁻¹ : ℝ) : ℂ))) {τ : ℝ | r < |τ|} := by
    intro s _; push_cast; ring
  have hq_cd : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞)
      (fun s => g s / (Complex.I * (c : ℂ) * ((deriv Φ s : ℝ) : ℂ))) {τ : ℝ | r < |τ|} :=
    (contDiffOn_const.mul (hg_cd.mul hinvC_cd)).congr hq_eq
  have hDg_cd : ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) Dg {τ : ℝ | r < |τ|} :=
    (hq_cd.deriv_of_isOpen hopen (m := (m : ℕ)) (by norm_cast)).neg
  -- Compute `iteratedDeriv k Dg τ` on `{r < |τ|}` via Leibniz rule
  have hDg_deriv_eq : ∀ k ≤ m, ∀ τ, r < |τ| →
      iteratedDeriv k Dg τ = -(Complex.I * (c : ℂ))⁻¹ *
        ∑ j ∈ Finset.range (k + 2), ((k + 1).choose j : ℝ) *
          iteratedDeriv j g τ * ((iteratedDeriv (k + 1 - j) (fun s => (deriv Φ s)⁻¹) τ : ℝ) : ℂ) := by
    intro k hk τ hτ
    have hD_ev : Dg =ᶠ[𝓝 τ] (fun s => -(Complex.I * (c : ℂ))⁻¹ * deriv (fun u => g u * (((deriv Φ u)⁻¹ : ℝ) : ℂ)) s) := by
      filter_upwards [hopen.mem_nhds hτ] with s hs
      have hq_ev : (fun u => g u / (Complex.I * (c : ℂ) * ((deriv Φ u : ℝ) : ℂ))) =ᶠ[𝓝 s]
          (fun u => (Complex.I * (c : ℂ))⁻¹ * (g u * (((deriv Φ u)⁻¹ : ℝ) : ℂ))) :=
        Filter.eventually_of_mem (hopen.mem_nhds hs) hq_eq
      simp only [Dg, hq_ev.deriv_eq, deriv_const_mul_field', neg_mul]
    rw [hD_ev.iteratedDeriv_eq k, iteratedDeriv_const_mul_field, ← iteratedDeriv_succ']
    have hg_at : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) g τ :=
      (hg_cd.contDiffAt (hopen.mem_nhds hτ)).of_le (by exact_mod_cast Nat.succ_le_succ hk)
    have hi_at : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun s => (((deriv Φ s)⁻¹ : ℝ) : ℂ)) τ :=
      (hinvC_cd.contDiffAt (hopen.mem_nhds hτ)).of_le (by exact_mod_cast Nat.succ_le_succ hk)
    rw [show (fun u => g u * (((deriv Φ u)⁻¹ : ℝ) : ℂ)) = g * (fun u => (((deriv Φ u)⁻¹ : ℝ) : ℂ)) from rfl,
      iteratedDeriv_mul hg_at hi_at]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iteratedDeriv_ofReal_comp (k + 1 - j) (fun s => (deriv Φ s)⁻¹) τ]
    push_cast; ring
  have hDg_bd : ∀ k ≤ m, ∀ τ, r < |τ| →
      ‖iteratedDeriv k Dg τ‖ ≤
        (∑ j ∈ Finset.range (k + 2), ((k + 1).choose j : ℝ) * B (k + 1 - j)) *
        (A / (c * κ * u)) * edgeW τ ^ (-((k + (p + 1) : ℕ) : ℤ)) *
        |τ| ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-2 : ℤ) := by
    intro k hk τ hτ
    have hw_pos : 0 < edgeW τ := edgeW_pos (by intro h; rw [h, abs_zero] at hτ; linarith)
    rw [hDg_deriv_eq k hk τ hτ, norm_mul, norm_neg, norm_inv, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hc.le)).trans ?_
    rw [Finset.mul_sum]
    simp only [Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj_le : j ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _)]
    have h1 := hg_bd j (by omega) τ hτ
    have h2 := hinv_bd (k + 1 - j) (by omega) τ hτ
    have h2' : |iteratedDeriv (k + 1 - j) (fun s => (deriv Φ s)⁻¹) τ| ≤
        B (k + 1 - j) * edgeW τ ^ (-((k + 1 - j : ℕ) : ℤ)) / (κ * u) :=
      h2.trans (div_le_div_of_nonneg_left (mul_nonneg (hB_nn _) (zpow_nonneg hw_pos.le _))
        (mul_pos hκ hu) (hΦ'_lb τ hτ))
    have hpow : edgeW τ ^ (-((j + p : ℕ) : ℤ)) * edgeW τ ^ (-((k + 1 - j : ℕ) : ℤ)) =
        edgeW τ ^ (-((k + (p + 1) : ℕ) : ℤ)) := by
      rw [← zpow_add₀ hw_pos.ne']; congr 1; omega
    calc c⁻¹ * (((k + 1).choose j : ℝ) * ‖iteratedDeriv j g τ‖ *
          |iteratedDeriv (k + 1 - j) (fun s => (deriv Φ s)⁻¹) τ|)
        ≤ c⁻¹ * (((k + 1).choose j : ℝ) *
            (A * edgeW τ ^ (-((j + p : ℕ) : ℤ)) * |τ| ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-2 : ℤ)) *
            (B (k + 1 - j) * edgeW τ ^ (-((k + 1 - j : ℕ) : ℤ)) / (κ * u))) := by
              have := hB_nn (k + 1 - j); gcongr
      _ = ((k + 1).choose j : ℝ) * B (k + 1 - j) * (A / (c * κ * u)) *
            (edgeW τ ^ (-((j + p : ℕ) : ℤ)) * edgeW τ ^ (-((k + 1 - j : ℕ) : ℤ))) *
            |τ| ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-2 : ℤ) := by
              field_simp [hc.ne', hκ.ne', hu.ne']
      _ = ((k + 1).choose j : ℝ) * B (k + 1 - j) * (A / (c * κ * u)) *
            edgeW τ ^ (-((k + (p + 1) : ℕ) : ℤ)) * |τ| ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-2 : ℤ) := by
              rw [hpow]
  -- Boundary vanishing at `r⁺` and `(-r)⁻` for `k < m`
  have hlim_aux : ∀ {s0 : ℝ} {F : Filter ℝ},
      (∀ᶠ τ in F, r < |τ|) →
      (∀ k ≤ m, Tendsto (iteratedDeriv k g) F (𝓝 0)) →
      ∀ k < m, Tendsto (iteratedDeriv k Dg) F (𝓝 0) := by
    intro s0 F hF_mem hF_lim k hk
    rw [tendsto_zero_iff_norm_tendsto_zero]
    let M_k : ℝ := ∑ j ∈ Finset.range (k + 2),
      ((k + 1).choose j : ℝ) * (B (k + 1 - j) * r ^ (-((k + 1 - j : ℕ) : ℤ)) / (κ * u))
    have hdom : Tendsto (fun τ : ℝ =>
        c⁻¹ * ∑ j ∈ Finset.range (k + 2),
          ((k + 1).choose j : ℝ) * ‖iteratedDeriv j g τ‖ *
            (B (k + 1 - j) * r ^ (-((k + 1 - j : ℕ) : ℤ)) / (κ * u))) F (𝓝 0) := by
      have hsum : Tendsto (fun τ : ℝ => ∑ j ∈ Finset.range (k + 2),
          ((k + 1).choose j : ℝ) * ‖iteratedDeriv j g τ‖ *
            (B (k + 1 - j) * r ^ (-((k + 1 - j : ℕ) : ℤ)) / (κ * u))) F (𝓝 0) := by
        have h := tendsto_finset_sum_local (Finset.range (k + 2))
          (f := fun j τ => ((k + 1).choose j : ℝ) * ‖iteratedDeriv j g τ‖ *
            (B (k + 1 - j) * r ^ (-((k + 1 - j : ℕ) : ℤ)) / (κ * u)))
          (a := fun _ => (0 : ℝ)) fun j hj => by
          have hj_le : j ≤ m := by have := Finset.mem_range.mp hj; omega
          have h1 : Tendsto (fun τ => ‖iteratedDeriv j g τ‖) F (𝓝 0) :=
            tendsto_zero_iff_norm_tendsto_zero.mp (hF_lim j hj_le)
          have h2 := (h1.const_mul ((k + 1).choose j : ℝ)).mul_const
            (B (k + 1 - j) * r ^ (-((k + 1 - j : ℕ) : ℤ)) / (κ * u))
          simpa using h2
        simpa only [Finset.sum_const_zero] using h
      simpa using hsum.const_mul c⁻¹
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hdom
    filter_upwards [hF_mem] with τ hτ
    rw [hDg_deriv_eq k hk.le τ hτ, norm_mul, norm_neg, norm_inv, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)) (inv_nonneg.mpr hc.le)
    have hj_le : j ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _)]
    have h2 := hinv_bd (k + 1 - j) (by omega) τ hτ
    have hw_ge : r ≤ edgeW τ := edgeW_ge_r hr1 hτ.le
    have hw_pow : edgeW τ ^ (-((k + 1 - j : ℕ) : ℤ)) ≤ r ^ (-((k + 1 - j : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
      exact inv_anti₀ (pow_pos hr0 _) (pow_le_pow_left₀ hr0.le hw_ge _)
    have h2' : |iteratedDeriv (k + 1 - j) (fun s => (deriv Φ s)⁻¹) τ| ≤
        B (k + 1 - j) * r ^ (-((k + 1 - j : ℕ) : ℤ)) / (κ * u) := by
      calc |iteratedDeriv (k + 1 - j) (fun s => (deriv Φ s)⁻¹) τ|
          ≤ B (k + 1 - j) * edgeW τ ^ (-((k + 1 - j : ℕ) : ℤ)) / |deriv Φ τ| := h2
        _ ≤ B (k + 1 - j) * r ^ (-((k + 1 - j : ℕ) : ℤ)) / (κ * u) :=
            div_le_div₀ (by have := hB_nn (k + 1 - j); positivity)
              (mul_le_mul_of_nonneg_left hw_pow (hB_nn _)) (mul_pos hκ hu) (hΦ'_lb τ hτ)
    gcongr
  have hDg_lim_r : ∀ k < m, Tendsto (iteratedDeriv k Dg) (𝓝[>] r) (𝓝 0) :=
    hlim_aux (s0 := r) (by filter_upwards [self_mem_nhdsWithin] with τ hτ; rw [abs_of_pos (hr0.trans hτ)]; exact hτ) hg_lim_r
  have hDg_lim_nr : ∀ k < m, Tendsto (iteratedDeriv k Dg) (𝓝[<] (-r)) (𝓝 0) :=
    hlim_aux (s0 := -r) (by
      filter_upwards [self_mem_nhdsWithin] with τ hτ
      have hτ_lt : τ < -r := hτ
      rw [abs_of_neg (by linarith)]; linarith) hg_lim_nr
  -- Integrability of `g E` and `Dg E` on `Ioi r` and `Iio (-r)`
  have hInt_Ioi : ∀ {h : ℝ → ℂ} {M : ℝ} {q_pow : ℕ}, 0 ≤ M →
      ContinuousOn h (Ioi r) →
      (∀ τ, r < τ → ‖h τ‖ ≤ M * edgeW τ ^ (-(q_pow : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) →
      IntegrableOn (fun τ : ℝ => h τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) (Ioi r) := by
    intro h M q_pow hM hh_cont hh_bd
    have hE_cont : ContinuousOn (fun τ : ℝ => Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) (Ioi r) := by
      have hΦ_c : ContinuousOn Φ (Ioi r) :=
        hΦ_cd.continuousOn.mono fun τ (hτ : r < τ) => by rw [mem_ofPred_eq, abs_of_pos (hr0.trans hτ)]; exact hτ
      exact Complex.continuous_exp.comp_continuousOn
        (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hΦ_c)))
    have hdom_int := (integrableOn_shoulder_weight (n := max q_pow 1) (le_max_right _ _) hr0 hr1).1.const_mul M
    refine hdom_int.mono' ((hh_cont.mul hE_cont).aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_)
    have hτ0 : 0 < τ := hr0.trans hτ
    rw [norm_mul, show Complex.I * ((c * Φ τ : ℝ) : ℂ) = ((c * Φ τ : ℝ) : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    have hw_le1 : edgeW τ ≤ 1 := edgeW_le_one τ
    have hw_pos : 0 < edgeW τ := edgeW_pos hτ0.ne'
    have hpow_le : edgeW τ ^ (-(q_pow : ℤ)) ≤ edgeW τ ^ (-((max q_pow 1 : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
      exact inv_anti₀ (pow_pos hw_pos _) (pow_le_pow_of_le_one hw_pos.le hw_le1 (le_max_left _ _))
    calc ‖h τ‖
        ≤ M * edgeW τ ^ (-(q_pow : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) := hh_bd τ hτ
      _ ≤ M * (edgeW τ ^ (-((max q_pow 1 : ℕ) : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) := by
          rw [← mul_assoc, ← mul_assoc]
          have := Real.rpow_nonneg hτ0.le (-(1 / 2 : ℝ))
          have : 0 ≤ (1 + τ) ^ (-2 : ℤ) := zpow_nonneg (by linarith) _
          gcongr
  have hg_int_pos : IntegrableOn (fun τ => g τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) (Ioi r) :=
    hInt_Ioi hA (hg_cd.continuousOn.mono fun τ (hτ : r < τ) => by rw [mem_ofPred_eq, abs_of_pos (hr0.trans hτ)]; exact hτ)
      fun τ hτ => by
        have h := hg_bd 0 (Nat.zero_le _) τ (by rw [abs_of_pos (hr0.trans hτ)]; exact hτ)
        simpa [abs_of_pos (hr0.trans hτ)] using h
  have hDg_int_pos : IntegrableOn (fun τ => Dg τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) (Ioi r) :=
    hInt_Ioi (M := (∑ j ∈ Finset.range 2, ((1 : ℕ).choose j : ℝ) * B (1 - j)) * (A / (c * κ * u)))
      (q_pow := p + 1)
      (mul_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hB_nn _)) (by positivity))
      (hDg_cd.continuousOn.mono fun τ (hτ : r < τ) => by rw [mem_ofPred_eq, abs_of_pos (hr0.trans hτ)]; exact hτ)
      fun τ hτ => by
        have h := hDg_bd 0 (Nat.zero_le _) τ (by rw [abs_of_pos (hr0.trans hτ)]; exact hτ)
        simpa [abs_of_pos (hr0.trans hτ)] using h
  -- Apply `ibp_osc_Ioi` on `Ioi r`
  have hpos_ibp : (∫ τ in Ioi r, g τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) =
      (∫ τ in Ioi r, Dg τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) := by
    refine ibp_osc_Ioi hc.ne'
      (fun τ hτ => (hg_cd.contDiffAt (hopen.mem_nhds (by rw [mem_ofPred_eq, abs_of_pos (hr0.trans hτ)]; exact hτ))).differentiableAt (by simp))
      (fun τ hτ => (hΦ_cd.contDiffAt (hopen.mem_nhds (by rw [mem_ofPred_eq, abs_of_pos (hr0.trans hτ)]; exact hτ))).differentiableAt (by simp))
      (fun τ hτ => (hΦ'_cd.contDiffAt (hopen.mem_nhds (by rw [mem_ofPred_eq, abs_of_pos (hr0.trans hτ)]; exact hτ))).differentiableAt (by simp))
      (fun τ hτ => hΦ'_ne τ (by rw [abs_of_pos (hr0.trans hτ)]; exact hτ))
      hg_int_pos hDg_int_pos ?_ ?_
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      have h1 : Tendsto (fun τ : ℝ => ‖g τ‖ / (c * κ * u)) (𝓝[>] r) (𝓝 0) := by
        simpa using (tendsto_zero_iff_norm_tendsto_zero.mp (hg_lim_r 0 (Nat.zero_le _))).div_const (c * κ * u)
      refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ h1
      filter_upwards [self_mem_nhdsWithin] with τ hτ
      rw [norm_div, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hc, mul_assoc]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
        (mul_le_mul_of_nonneg_left (hΦ'_lb τ (by rw [abs_of_pos (hr0.trans hτ)]; exact hτ)) hc.le)
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      have h1 : Tendsto (fun τ : ℝ => (A / (c * (κ * u))) * τ ^ (-2 : ℝ)) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (show (0 : ℝ) < 2 by norm_num)).const_mul (A / (c * (κ * u)))
      refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ h1
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with τ hτ1
      have hτr : r < |τ| := by rw [abs_of_pos (zero_lt_one.trans hτ1)]; exact lt_of_le_of_lt hr1 hτ1
      have hτ0 : 0 < τ := zero_lt_one.trans hτ1
      have hg0 := hg_bd 0 (Nat.zero_le _) τ hτr
      simp only [iteratedDeriv_zero, zero_add, abs_of_pos hτ0] at hg0
      have hw1 : edgeW τ = 1 := by simp [edgeW, abs_of_pos hτ0, hτ1.le]
      rw [hw1, one_zpow, mul_one] at hg0
      have htr : τ ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ1.le (by norm_num)
      have h1t : (1 + τ) ^ (-2 : ℤ) ≤ τ ^ (-2 : ℝ) := by
        rw [zpow_neg, show (1 + τ) ^ (2 : ℤ) = (1 + τ) ^ 2 by norm_cast,
          show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hτ0.le, Real.rpow_natCast]
        exact inv_anti₀ (sq_pos_of_pos hτ0) (by nlinarith)
      rw [norm_div, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hc]
      calc ‖g τ‖ / (c * |deriv Φ τ|)
          ≤ (A * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) / (c * (κ * u)) :=
            div_le_div₀ (by positivity) hg0 (by positivity) (mul_le_mul_of_nonneg_left (hΦ'_lb τ hτr) hc.le)
        _ ≤ (A * 1 * τ ^ (-2 : ℝ)) / (c * (κ * u)) := by
            have : 0 ≤ (1 + τ) ^ (-2 : ℤ) := zpow_nonneg (by linarith) _
            gcongr
        _ = (A / (c * (κ * u))) * τ ^ (-2 : ℝ) := by ring
  -- Symmetrically on `Iio (-r)` by reflection `τ ↦ -τ`
  have hneg_ibp : (∫ τ in Iio (-r), g τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) =
      (∫ τ in Iio (-r), Dg τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) := by
    let g_ : ℝ → ℂ := fun τ => g (-τ)
    let Φ_ : ℝ → ℝ := fun τ => Φ (-τ)
    have hIio_eq : ∀ f : ℝ → ℂ, ∫ τ in Iio (-r), f τ = ∫ τ in Ioi r, f (-τ) :=
      fun f => integral_Iio_neg_eq_Ioi r f
    rw [hIio_eq, hIio_eq]
    have hΦ'_neg : ∀ τ, deriv Φ_ τ = -deriv Φ (-τ) := fun τ => deriv_comp_neg Φ τ
    have hDg_neg : ∀ τ ∈ Ioi r,
        -deriv (fun s => g_ s / (Complex.I * (c : ℂ) * ((deriv Φ_ s : ℝ) : ℂ))) τ = Dg (-τ) := by
      intro τ hτ
      have heq : (fun s => g_ s / (Complex.I * (c : ℂ) * ((deriv Φ_ s : ℝ) : ℂ))) =
          -(fun s => g (-s) / (Complex.I * (c : ℂ) * ((deriv Φ (-s) : ℝ) : ℂ))) := by
        ext s; simp only [Pi.neg_apply, g_, hΦ'_neg, Complex.ofReal_neg, mul_neg, div_neg]
      rw [heq, deriv.neg, deriv_comp_neg (fun s => g s / (Complex.I * (c : ℂ) * ((deriv Φ s : ℝ) : ℂ))) τ]
      simp only [Dg, neg_neg]
    have hg_int_neg : IntegrableOn (fun τ => g_ τ * Complex.exp (Complex.I * ((c * Φ_ τ : ℝ) : ℂ))) (Ioi r) := by
      have hΦ_c : ContinuousOn Φ_ (Ioi r) :=
        (hΦ_cd.continuousOn.comp continuous_neg.continuousOn fun τ (hτ : r < τ) => by
          rw [mem_ofPred_eq, abs_neg, abs_of_pos (hr0.trans hτ)]; exact hτ)
      have hg_c : ContinuousOn g_ (Ioi r) :=
        (hg_cd.continuousOn.comp continuous_neg.continuousOn fun τ (hτ : r < τ) => by
          rw [mem_ofPred_eq, abs_neg, abs_of_pos (hr0.trans hτ)]; exact hτ)
      have hE_c : ContinuousOn (fun τ : ℝ => Complex.exp (Complex.I * ((c * Φ_ τ : ℝ) : ℂ))) (Ioi r) :=
        Complex.continuous_exp.comp_continuousOn
          (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hΦ_c)))
      have hdom := (integrableOn_shoulder_weight (n := max p 1) (le_max_right _ _) hr0 hr1).1.const_mul A
      refine hdom.mono' ((hg_c.mul hE_c).aestronglyMeasurable measurableSet_Ioi)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_)
      have hτ0 : 0 < τ := hr0.trans hτ
      rw [norm_mul, show Complex.I * ((c * Φ_ τ : ℝ) : ℂ) = ((c * Φ_ τ : ℝ) : ℂ) * Complex.I by ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      have h := hg_bd 0 (Nat.zero_le _) (-τ) (by rw [abs_neg, abs_of_pos hτ0]; exact hτ)
      simp only [iteratedDeriv_zero, zero_add, edgeW_neg, abs_neg, abs_of_pos hτ0] at h
      have hw_pos : 0 < edgeW τ := edgeW_pos hτ0.ne'
      have hpow_le : edgeW τ ^ (-(p : ℤ)) ≤ edgeW τ ^ (-((max p 1 : ℕ) : ℤ)) := by
        rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
        exact inv_anti₀ (pow_pos hw_pos _) (pow_le_pow_of_le_one hw_pos.le (edgeW_le_one τ) (le_max_left _ _))
      calc ‖g_ τ‖ ≤ A * edgeW τ ^ (-(p : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) := h
        _ ≤ A * (edgeW τ ^ (-((max p 1 : ℕ) : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) := by
            rw [← mul_assoc, ← mul_assoc]
            have := Real.rpow_nonneg hτ0.le (-(1 / 2 : ℝ))
            have : 0 ≤ (1 + τ) ^ (-2 : ℤ) := zpow_nonneg (by linarith) _
            gcongr
    have hDg_int_neg : IntegrableOn (fun τ => Dg (-τ) * Complex.exp (Complex.I * ((c * Φ_ τ : ℝ) : ℂ))) (Ioi r) := by
      have hΦ_c : ContinuousOn Φ_ (Ioi r) :=
        (hΦ_cd.continuousOn.comp continuous_neg.continuousOn fun τ (hτ : r < τ) => by
          rw [mem_ofPred_eq, abs_neg, abs_of_pos (hr0.trans hτ)]; exact hτ)
      have hD_c : ContinuousOn (fun τ => Dg (-τ)) (Ioi r) :=
        (hDg_cd.continuousOn.comp continuous_neg.continuousOn fun τ (hτ : r < τ) => by
          rw [mem_ofPred_eq, abs_neg, abs_of_pos (hr0.trans hτ)]; exact hτ)
      have hE_c : ContinuousOn (fun τ : ℝ => Complex.exp (Complex.I * ((c * Φ_ τ : ℝ) : ℂ))) (Ioi r) :=
        Complex.continuous_exp.comp_continuousOn
          (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hΦ_c)))
      let M_d := (∑ j ∈ Finset.range 2, ((1 : ℕ).choose j : ℝ) * B (1 - j)) * (A / (c * κ * u))
      have hdom := (integrableOn_shoulder_weight (n := p + 1) (by omega) hr0 hr1).1.const_mul M_d
      refine hdom.mono' ((hD_c.mul hE_c).aestronglyMeasurable measurableSet_Ioi)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_)
      have hτ0 : 0 < τ := hr0.trans hτ
      rw [norm_mul, show Complex.I * ((c * Φ_ τ : ℝ) : ℂ) = ((c * Φ_ τ : ℝ) : ℂ) * Complex.I by ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      have h := hDg_bd 0 (Nat.zero_le _) (-τ) (by rw [abs_neg, abs_of_pos hτ0]; exact hτ)
      simp only [iteratedDeriv_zero, zero_add, edgeW_neg, abs_neg, abs_of_pos hτ0] at h
      simpa [M_d, mul_assoc] using h
    have hstep := ibp_osc_Ioi (r := r) (c := c) hc.ne' (g := g_) (Φ := Φ_)
      (fun τ hτ => ((hg_cd.contDiffAt (hopen.mem_nhds (by rw [mem_ofPred_eq, abs_neg, abs_of_pos (hr0.trans hτ)]; exact hτ))).differentiableAt (by simp)).comp τ differentiableAt_id.neg)
      (fun τ hτ => ((hΦ_cd.contDiffAt (hopen.mem_nhds (by rw [mem_ofPred_eq, abs_neg, abs_of_pos (hr0.trans hτ)]; exact hτ))).differentiableAt (by simp)).comp τ differentiableAt_id.neg)
      (fun τ hτ => by
        rw [show deriv Φ_ = fun s => -deriv Φ (-s) from funext hΦ'_neg]
        exact (((hΦ'_cd.contDiffAt (hopen.mem_nhds (by show r < |-τ|; rw [abs_neg, abs_of_pos (hr0.trans hτ)]; exact hτ))).differentiableAt (by simp)).comp τ differentiableAt_id.neg).neg)
      (fun τ hτ => by rw [hΦ'_neg]; exact neg_ne_zero.mpr (hΦ'_ne (-τ) (by rw [abs_neg, abs_of_pos (hr0.trans hτ)]; exact hτ)))
      hg_int_neg
      (hDg_int_neg.congr_fun (fun τ hτ => by rw [hDg_neg τ hτ]) measurableSet_Ioi)
      ?_ ?_
    · rw [hstep]
      exact setIntegral_congr_fun measurableSet_Ioi fun τ hτ => by rw [hDg_neg τ hτ]
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      have hneg_map : Tendsto (fun τ : ℝ => -τ) (𝓝[>] r) (𝓝[<] (-r)) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨continuous_neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
          by filter_upwards [self_mem_nhdsWithin] with τ hτ; exact neg_lt_neg hτ⟩
      have h1 : Tendsto (fun τ : ℝ => ‖g (-τ)‖ / (c * κ * u)) (𝓝[>] r) (𝓝 0) := by
        simpa using (tendsto_zero_iff_norm_tendsto_zero.mp ((hg_lim_nr 0 (Nat.zero_le _)).comp hneg_map)).div_const (c * κ * u)
      refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ h1
      filter_upwards [self_mem_nhdsWithin] with τ hτ
      rw [norm_div, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hc, mul_assoc, hΦ'_neg, abs_neg]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
        (mul_le_mul_of_nonneg_left (hΦ'_lb (-τ) (by rw [abs_neg, abs_of_pos (hr0.trans hτ)]; exact hτ)) hc.le)
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      have h1 : Tendsto (fun τ : ℝ => (A / (c * (κ * u))) * τ ^ (-2 : ℝ)) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (show (0 : ℝ) < 2 by norm_num)).const_mul (A / (c * (κ * u)))
      refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ h1
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with τ hτ1
      have hτ0 : 0 < τ := zero_lt_one.trans hτ1
      have hτr : r < |-τ| := by rw [abs_neg, abs_of_pos hτ0]; exact lt_of_le_of_lt hr1 hτ1
      have hg0 := hg_bd 0 (Nat.zero_le _) (-τ) hτr
      simp only [iteratedDeriv_zero, zero_add, edgeW_neg, abs_neg, abs_of_pos hτ0] at hg0
      have hw1 : edgeW τ = 1 := by simp [edgeW, abs_of_pos hτ0, hτ1.le]
      rw [hw1, one_zpow, mul_one] at hg0
      have htr : τ ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ1.le (by norm_num)
      have h1t : (1 + τ) ^ (-2 : ℤ) ≤ τ ^ (-2 : ℝ) := by
        rw [zpow_neg, show (1 + τ) ^ (2 : ℤ) = (1 + τ) ^ 2 by norm_cast,
          show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hτ0.le, Real.rpow_natCast]
        exact inv_anti₀ (sq_pos_of_pos hτ0) (by nlinarith)
      rw [norm_div, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hc, hΦ'_neg, abs_neg]
      calc ‖g (-τ)‖ / (c * |deriv Φ (-τ)|)
          ≤ (A * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) / (c * (κ * u)) :=
            div_le_div₀ (by positivity) hg0 (by positivity) (mul_le_mul_of_nonneg_left (hΦ'_lb (-τ) hτr) hc.le)
        _ ≤ (A * 1 * τ ^ (-2 : ℝ)) / (c * (κ * u)) := by
            have : 0 ≤ (1 + τ) ^ (-2 : ℤ) := zpow_nonneg (by linarith) _
            gcongr
        _ = (A / (c * (κ * u))) * τ ^ (-2 : ℝ) := by ring
  exact ⟨hDg_cd, hDg_bd, hDg_lim_r, hDg_lim_nr, hpos_ibp, hneg_ibp⟩

/-- **Lemma FCT.5a (`fct:edge-ibp`), Part (2) (Shoulder)**
(`constant_terms_five.tex`, lines 524–537).

Note: the paper states `|Φ^{(k+1)}(τ)| ≤ K_k w(τ)^{-k} |Φ'(τ)|` for `1 ≤ k ≤ n - 1`, which is an
off-by-one typo (for `n = 1` it is vacuous and false for `Φ(τ) = uτ + (u/(2cu)) sin(cuτ)`). The
corrected range `1 ≤ k ≤ n` matches the paper's own hypothesis `Φ ∈ C^{n+1}`. -/
theorem fct_edge_ibp_shoulder {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {K : ℕ → ℝ} (hK_nn : ∀ k, 0 ≤ K k) :
    ∃ C ≥ 0, ∀ {c u r A : ℝ} {a : ℝ → ℂ} {Φ : ℝ → ℝ},
      0 < c → 0 < u → 0 < r → r ≤ 1 → 0 ≤ A →
      ContDiff ℝ (n : ℕ) a →
      (∀ τ : ℝ, |τ| < r → a τ = 0) →
      (∀ k ≤ n, ∀ τ : ℝ, r < |τ| →
        ‖iteratedDeriv k a τ‖ ≤ A * edgeW τ ^ (-(k : ℤ)) * |τ| ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-2 : ℤ)) →
      ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Φ {τ : ℝ | r < |τ|} →
      (∀ τ : ℝ, r < |τ| → κ * u ≤ |deriv Φ τ|) →
      (∀ k, 1 ≤ k → k ≤ n → ∀ τ : ℝ, r < |τ| →
        |iteratedDeriv (k + 1) Φ τ| ≤ K k * edgeW τ ^ (-(k : ℤ)) * |deriv Φ τ|) →
      Integrable (fun τ : ℝ => a τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) ∧
      ‖∫ τ : ℝ, a τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))‖ ≤
        C * A * ((c * u) ^ n)⁻¹ * r ^ (1 / 2 - (n : ℝ)) := by
  obtain ⟨B, hB_nn, hinv⟩ := iteratedDeriv_inv_deriv_bound (n := n) hK_nn
  -- Define step-multiplier constant `M_m` by recursion on `m`
  let stepC : ℕ → ℝ := fun k => ∑ j ∈ Finset.range (k + 2), ((k + 1).choose j : ℝ) * B (k + 1 - j)
  have hstepC_nn : ∀ k, 0 ≤ stepC k := fun k =>
    Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hB_nn _)
  let M_step : ℕ → ℝ := fun m => ∏ i ∈ Finset.range m, (∑ k ∈ Finset.range (n + 1), stepC k)
  have hM_nn : ∀ m, 0 ≤ M_step m := fun m =>
    Finset.prod_nonneg fun _ _ => Finset.sum_nonneg fun k _ => hstepC_nn k
  let C_tot : ℝ := 2 * M_step n * (κ ^ n)⁻¹ * (2 / ((n : ℝ) - 1 / 2) + 1)
  have hC_nn : 0 ≤ C_tot := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have : (0 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
    have := hM_nn n
    positivity
  refine ⟨C_tot, hC_nn, fun {c u r A a Φ} hc hu hr0 hr1 hA ha_cd ha_zero ha_bd hΦ_cd hΦ'_lb hΦ_bd => ?_⟩
  have hΦ'_ne : ∀ τ, r < |τ| → deriv Φ τ ≠ 0 := fun τ hτ => abs_pos.mp (lt_of_lt_of_le (mul_pos hκ hu) (hΦ'_lb τ hτ))
  have hinv_bd : ∀ k ≤ n, ∀ τ, r < |τ| →
      |iteratedDeriv k (fun s => (deriv Φ s)⁻¹) τ| ≤ B k * edgeW τ ^ (-(k : ℤ)) / |deriv Φ τ| :=
    hinv hr0 hr1 hΦ_cd hΦ'_ne hΦ_bd
  -- Boundary vanishing of `iteratedDeriv k a` at `±r` for `k ≤ n`
  have ha_lim_r : ∀ k ≤ n, Tendsto (iteratedDeriv k a) (𝓝[>] r) (𝓝 0) := by
    intro k hk
    have hcont : Continuous (iteratedDeriv k a) := ha_cd.continuous_iteratedDeriv k (by exact_mod_cast hk)
    have hzero_r : iteratedDeriv k a r = 0 := by
      have hlim_left : Tendsto (iteratedDeriv k a) (𝓝[<] r) (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsLT (by linarith : -r < r)] with τ hτ
        have hev : a =ᶠ[𝓝 τ] (0 : ℝ → ℂ) :=
          Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hτ) fun s hs => ha_zero s (abs_lt.mpr hs)
        rw [hev.iteratedDeriv_eq k, iteratedDeriv_const_zero]
      exact tendsto_nhds_unique (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hlim_left
    rw [← hzero_r]; exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ha_lim_nr : ∀ k ≤ n, Tendsto (iteratedDeriv k a) (𝓝[<] (-r)) (𝓝 0) := by
    intro k hk
    have hcont : Continuous (iteratedDeriv k a) := ha_cd.continuous_iteratedDeriv k (by exact_mod_cast hk)
    have hzero_nr : iteratedDeriv k a (-r) = 0 := by
      have hlim_right : Tendsto (iteratedDeriv k a) (𝓝[>] (-r)) (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT (by linarith : -r < r)] with τ hτ
        have hev : a =ᶠ[𝓝 τ] (0 : ℝ → ℂ) :=
          Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hτ) fun s hs => ha_zero s (abs_lt.mpr hs)
        rw [hev.iteratedDeriv_eq k, iteratedDeriv_const_zero]
      exact tendsto_nhds_unique (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hlim_right
    rw [← hzero_nr]; exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  -- Induction on `m ≤ n`: after `m` steps we get `g_m` with `n - m` derivatives and same integrals on `Ioi r`, `Iio (-r)`
  have hind : ∀ m ≤ n, ∃ g : ℝ → ℂ,
      ContDiffOn ℝ ((n - m : ℕ) : WithTop ℕ∞) g {τ : ℝ | r < |τ|} ∧
      (∀ k ≤ n - m, ∀ τ, r < |τ| →
        ‖iteratedDeriv k g τ‖ ≤ M_step m * A * ((c * κ * u) ^ m)⁻¹ *
          edgeW τ ^ (-((k + m : ℕ) : ℤ)) * |τ| ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-2 : ℤ)) ∧
      (∀ k < n - m, Tendsto (iteratedDeriv k g) (𝓝[>] r) (𝓝 0)) ∧
      (∀ k < n - m, Tendsto (iteratedDeriv k g) (𝓝[<] (-r)) (𝓝 0)) ∧
      (∫ τ in Ioi r, a τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) =
        (∫ τ in Ioi r, g τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) ∧
      (∫ τ in Iio (-r), a τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) =
        (∫ τ in Iio (-r), g τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨a, ha_cd.contDiffOn, ?_, fun k hk => ha_lim_r k hk.le, fun k hk => ha_lim_nr k hk.le, rfl, rfl⟩
      intro k hk τ hτ
      simpa [M_step] using ha_bd k hk τ hτ
    | succ m ih =>
      intro hm
      obtain ⟨g, hg_cd, hg_bd, hg_lr, hg_lnr, hpos, hneg⟩ := ih (by omega)
      have hnm : n - m = (n - (m + 1)) + 1 := by omega
      rw [hnm] at hg_cd hg_bd hg_lr hg_lnr
      -- Need `hg_lr` and `hg_lnr` for `k ≤ n - (m + 1)`, which is `k < (n - (m + 1)) + 1`!
      have hstep := shoulder_ibp_step (m := n - (m + 1)) (B := B) hB_nn
        hr0 hr1 hc hu hκ (mul_nonneg (mul_nonneg (hM_nn m) hA) (by positivity))
        (p := m) (g := g) (Φ := Φ) hg_cd hg_bd
        (fun k hk => hg_lr k (Nat.lt_succ_of_le hk))
        (fun k hk => hg_lnr k (Nat.lt_succ_of_le hk))
        (hΦ_cd.of_le (by exact_mod_cast (show (n - (m + 1)) + 2 ≤ n + 1 by omega)))
        hΦ'_lb (fun k hk => hinv_bd k (by omega))
      obtain ⟨hDg_cd, hDg_bd, hDg_lr, hDg_lnr, hDg_pos, hDg_neg⟩ := hstep
      refine ⟨fun τ => -deriv (fun s => g s / (Complex.I * (c : ℂ) * ((deriv Φ s : ℝ) : ℂ))) τ,
        hDg_cd, ?_, hDg_lr, hDg_lnr, hpos.trans hDg_pos, hneg.trans hDg_neg⟩
      intro k hk τ hτ
      have hbd := hDg_bd k hk τ hτ
      have hle_sum : stepC k ≤ ∑ i ∈ Finset.range (n + 1), stepC i :=
        Finset.single_le_sum (f := stepC) (fun i _ => hstepC_nn i) (Finset.mem_range.mpr (by omega))
      have hM_succ : M_step (m + 1) = M_step m * (∑ i ∈ Finset.range (n + 1), stepC i) := by
        simp [M_step, pow_succ]
      have hτ_pos : 0 < |τ| := hr0.trans hτ
      have hw_pos : 0 < edgeW τ := edgeW_pos (abs_pos.mp hτ_pos)
      calc ‖iteratedDeriv k (fun τ => -deriv (fun s => g s / (Complex.I * (c : ℂ) * ((deriv Φ s : ℝ) : ℂ))) τ) τ‖
          ≤ stepC k * (M_step m * A * ((c * κ * u) ^ m)⁻¹ / (c * κ * u)) *
              edgeW τ ^ (-((k + (m + 1) : ℕ) : ℤ)) * |τ| ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-2 : ℤ) := hbd
        _ ≤ (∑ i ∈ Finset.range (n + 1), stepC i) * (M_step m * A * ((c * κ * u) ^ m)⁻¹ / (c * κ * u)) *
              edgeW τ ^ (-((k + (m + 1) : ℕ) : ℤ)) * |τ| ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-2 : ℤ) := by
              have := hM_nn m
              have := Real.rpow_nonneg hτ_pos.le (-(1 / 2 : ℝ))
              have : 0 ≤ (1 + |τ|) ^ (-2 : ℤ) := zpow_nonneg (by linarith) _
              have : 0 ≤ edgeW τ ^ (-((k + (m + 1) : ℕ) : ℤ)) := zpow_nonneg hw_pos.le _
              gcongr
        _ = M_step (m + 1) * A * ((c * κ * u) ^ (m + 1))⁻¹ *
              edgeW τ ^ (-((k + (m + 1) : ℕ) : ℤ)) * |τ| ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-2 : ℤ) := by
              rw [hM_succ, pow_succ]; field_simp [hc.ne', hκ.ne', hu.ne']
  -- Integrability of `a * E` on `ℝ`
  have haE_int_pos : IntegrableOn (fun τ => a τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) (Ioi r) := by
    have hΦ_c : ContinuousOn Φ (Ioi r) :=
      hΦ_cd.continuousOn.mono fun τ (hτ : r < τ) => by rw [mem_ofPred_eq, abs_of_pos (hr0.trans hτ)]; exact hτ
    have hE_c : ContinuousOn (fun τ : ℝ => Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) (Ioi r) :=
      Complex.continuous_exp.comp_continuousOn
        (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hΦ_c)))
    have hdom := (integrableOn_shoulder_weight (n := 1) le_rfl hr0 hr1).1.const_mul A
    refine hdom.mono' ((ha_cd.continuous.continuousOn.mul hE_c).aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_)
    have hτ0 : 0 < τ := hr0.trans hτ
    rw [norm_mul, show Complex.I * ((c * Φ τ : ℝ) : ℂ) = ((c * Φ τ : ℝ) : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    have h := ha_bd 0 (Nat.zero_le _) τ (by rw [abs_of_pos hτ0]; exact hτ)
    simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one, abs_of_pos hτ0] at h
    have hw_pos : 0 < edgeW τ := edgeW_pos hτ0.ne'
    have h1_le : 1 ≤ edgeW τ ^ (-1 : ℤ) := by
      rw [zpow_neg_one]; exact one_le_inv₀ hw_pos |>.mpr (edgeW_le_one τ)
    calc ‖a τ‖ ≤ A * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) := h
      _ ≤ A * (edgeW τ ^ (-(1 : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) := by
          have hrp : 0 ≤ τ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hτ0.le (-(1 / 2 : ℝ))
          have h1p : 0 ≤ (1 + τ) ^ (-2 : ℤ) := zpow_nonneg (by linarith) _
          have hprod : 0 ≤ A * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) := mul_nonneg hA (mul_nonneg hrp h1p)
          nlinarith
  have haE_int_neg : IntegrableOn (fun τ => a τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) (Iio (-r)) := by
    rw [integrableOn_Iio_neg_iff_Ioi]
    have hΦ_c : ContinuousOn (fun τ => Φ (-τ)) (Ioi r) :=
      hΦ_cd.continuousOn.comp continuous_neg.continuousOn fun τ (hτ : r < τ) => by
        rw [mem_ofPred_eq, abs_neg, abs_of_pos (hr0.trans hτ)]; exact hτ
    have hE_c : ContinuousOn (fun τ : ℝ => Complex.exp (Complex.I * ((c * Φ (-τ) : ℝ) : ℂ))) (Ioi r) :=
      Complex.continuous_exp.comp_continuousOn
        (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hΦ_c)))
    have hdom := (integrableOn_shoulder_weight (n := 1) le_rfl hr0 hr1).1.const_mul A
    refine hdom.mono' (((ha_cd.continuous.comp continuous_neg).continuousOn.mul hE_c).aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_)
    have hτ0 : 0 < τ := hr0.trans hτ
    rw [norm_mul, show Complex.I * ((c * Φ (-τ) : ℝ) : ℂ) = ((c * Φ (-τ) : ℝ) : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    have h := ha_bd 0 (Nat.zero_le _) (-τ) (by rw [abs_neg, abs_of_pos hτ0]; exact hτ)
    simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one, abs_neg, abs_of_pos hτ0] at h
    have hw_pos : 0 < edgeW τ := edgeW_pos hτ0.ne'
    have h1_le : 1 ≤ edgeW τ ^ (-1 : ℤ) := by
      rw [zpow_neg_one]; exact one_le_inv₀ hw_pos |>.mpr (edgeW_le_one τ)
    calc ‖a (-τ)‖ ≤ A * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ) := h
      _ ≤ A * (edgeW τ ^ (-(1 : ℤ)) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) := by
          have hrp : 0 ≤ τ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hτ0.le (-(1 / 2 : ℝ))
          have h1p : 0 ≤ (1 + τ) ^ (-2 : ℤ) := zpow_nonneg (by linarith) _
          have hprod : 0 ≤ A * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ (-2 : ℤ)) := mul_nonneg hA (mul_nonneg hrp h1p)
          nlinarith
  have haE_zero_mid : EqOn (fun τ => a τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) 0 (Icc (-r) r) := by
    intro τ hτ
    have hcont : Continuous a := ha_cd.continuous
    have ha0 : a τ = 0 := by
      rcases eq_or_lt_of_le hτ.1 with hEq | h1
      · rw [← hEq]
        have := ha_lim_nr 0 (Nat.zero_le _)
        have h2 := (hcont.continuousAt (x := -r)).tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (-r)))
        simpa using tendsto_nhds_unique h2 this
      · rcases eq_or_lt_of_le hτ.2 with hEq | h2
        · rw [hEq]
          have := ha_lim_r 0 (Nat.zero_le _)
          have h3 := (hcont.continuousAt (x := r)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi r))
          simpa using tendsto_nhds_unique h3 this
        · exact ha_zero τ (abs_lt.mpr ⟨h1, h2⟩)
    simp [ha0]
  have haE_int_mid : IntegrableOn (fun τ => a τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) (Icc (-r) r) :=
    (integrableOn_zero (μ := volume) (s := Icc (-r) r)).congr_fun (fun τ hτ => (haE_zero_mid hτ).symm) measurableSet_Icc
  have huniv : Iio (-r) ∪ Icc (-r) r ∪ Ioi r = univ := by
    ext τ; simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi, mem_univ, iff_true]
    by_cases h1 : τ < -r
    · exact Or.inl (Or.inl h1)
    · by_cases h2 : τ ≤ r
      · exact Or.inl (Or.inr ⟨not_lt.mp h1, h2⟩)
      · exact Or.inr (not_le.mp h2)
  have haE_int : Integrable (fun τ => a τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) := by
    rw [← integrableOn_univ, ← huniv]
    exact (haE_int_neg.union haE_int_mid).union haE_int_pos
  refine ⟨haE_int, ?_⟩
  -- Split `∫_ℝ = ∫_{Iio (-r)} + ∫_{Ioi r}` and apply `hind n le_rfl`
  have hsplit : ∫ τ : ℝ, a τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ)) =
      (∫ τ in Iio (-r), a τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) +
      (∫ τ in Ioi r, a τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) := by
    have hdisj1 : Disjoint (Iio (-r) ∪ Icc (-r) r) (Ioi r) := by
      rw [disjoint_left]; intro x hx1 hx2
      rcases hx1 with h1 | h2
      · linarith [mem_Iio.mp h1, mem_Ioi.mp hx2]
      · linarith [(mem_Icc.mp h2).2, mem_Ioi.mp hx2]
    have hdisj2 : Disjoint (Iio (-r)) (Icc (-r) r) := by
      rw [disjoint_left]; intro x hx1 hx2; linarith [mem_Iio.mp hx1, (mem_Icc.mp hx2).1]
    rw [← setIntegral_univ, ← huniv,
      setIntegral_union hdisj1 measurableSet_Ioi (haE_int_neg.union haE_int_mid) haE_int_pos,
      setIntegral_union hdisj2 measurableSet_Icc haE_int_neg haE_int_mid]
    have hmid0 : ∫ τ in Icc (-r) r, a τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ)) = 0 := by
      rw [setIntegral_congr_fun measurableSet_Icc haE_zero_mid]; simp
    rw [hmid0, add_zero]
  obtain ⟨g, hg_cd, hg_bd, _, _, hpos, hneg⟩ := hind n le_rfl
  rw [hsplit, hpos, hneg]
  have hw_int := integrableOn_shoulder_weight hn hr0 hr1
  have hM_tot : 0 ≤ M_step n * A * ((c * κ * u) ^ n)⁻¹ := by have := hM_nn n; positivity
  have hΦ_c_pos : ContinuousOn Φ (Ioi r) :=
    hΦ_cd.continuousOn.mono fun τ (hτ : r < τ) => by rw [mem_ofPred_eq, abs_of_pos (hr0.trans hτ)]; exact hτ
  have hE_c_pos : ContinuousOn (fun τ : ℝ => Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) (Ioi r) :=
    Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hΦ_c_pos)))
  have hg_c_pos : ContinuousOn g (Ioi r) :=
    hg_cd.continuousOn.mono fun τ (hτ : r < τ) => by rw [mem_ofPred_eq, abs_of_pos (hr0.trans hτ)]; exact hτ
  have hbd_pos : ‖∫ τ in Ioi r, g τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))‖ ≤
      M_step n * A * ((c * κ * u) ^ n)⁻¹ * ((2 / ((n : ℝ) - 1 / 2) + 1) * r ^ (1 / 2 - (n : ℝ))) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hint_g : IntegrableOn (fun τ => ‖g τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))‖) (Ioi r) :=
      ((hw_int.1.const_mul (M_step n * A * ((c * κ * u) ^ n)⁻¹)).mono'
        ((hg_c_pos.mul hE_c_pos).aestronglyMeasurable measurableSet_Ioi)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => by
          have hτ0 : 0 < τ := hr0.trans hτ
          change ‖g τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))‖ ≤ _
          rw [norm_mul, show Complex.I * ((c * Φ τ : ℝ) : ℂ) = ((c * Φ τ : ℝ) : ℂ) * Complex.I by ring,
            Complex.norm_exp_ofReal_mul_I, mul_one]
          have h := hg_bd 0 (Nat.zero_le _) τ (by rw [abs_of_pos hτ0]; exact hτ)
          simpa [abs_of_pos hτ0, mul_assoc] using h)).norm
    have hle := setIntegral_mono_on hint_g
      (hw_int.1.const_mul (M_step n * A * ((c * κ * u) ^ n)⁻¹)) measurableSet_Ioi fun τ hτ => by
        have hτ0 : 0 < τ := hr0.trans hτ
        rw [norm_mul, show Complex.I * ((c * Φ τ : ℝ) : ℂ) = ((c * Φ τ : ℝ) : ℂ) * Complex.I by ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]
        have h := hg_bd 0 (Nat.zero_le _) τ (by rw [abs_of_pos hτ0]; exact hτ)
        simpa [abs_of_pos hτ0, mul_assoc] using h
    rw [integral_const_mul] at hle
    exact hle.trans (mul_le_mul_of_nonneg_left hw_int.2 hM_tot)
  have hbd_neg : ‖∫ τ in Iio (-r), g τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))‖ ≤
      M_step n * A * ((c * κ * u) ^ n)⁻¹ * ((2 / ((n : ℝ) - 1 / 2) + 1) * r ^ (1 / 2 - (n : ℝ))) := by
    rw [integral_Iio_neg_eq_Ioi]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hΦ_c_neg : ContinuousOn (fun τ => Φ (-τ)) (Ioi r) :=
      hΦ_cd.continuousOn.comp continuous_neg.continuousOn fun τ (hτ : r < τ) => by
        rw [mem_ofPred_eq, abs_neg, abs_of_pos (hr0.trans hτ)]; exact hτ
    have hE_c_neg : ContinuousOn (fun τ : ℝ => Complex.exp (Complex.I * ((c * Φ (-τ) : ℝ) : ℂ))) (Ioi r) :=
      Complex.continuous_exp.comp_continuousOn
        (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hΦ_c_neg)))
    have hg_c_neg : ContinuousOn (fun τ => g (-τ)) (Ioi r) :=
      hg_cd.continuousOn.comp continuous_neg.continuousOn fun τ (hτ : r < τ) => by
        rw [mem_ofPred_eq, abs_neg, abs_of_pos (hr0.trans hτ)]; exact hτ
    have hint_g : IntegrableOn (fun τ => ‖g (-τ) * Complex.exp (Complex.I * ((c * Φ (-τ) : ℝ) : ℂ))‖) (Ioi r) :=
      ((hw_int.1.const_mul (M_step n * A * ((c * κ * u) ^ n)⁻¹)).mono'
        ((hg_c_neg.mul hE_c_neg).aestronglyMeasurable measurableSet_Ioi)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => by
          have hτ0 : 0 < τ := hr0.trans hτ
          change ‖g (-τ) * Complex.exp (Complex.I * ((c * Φ (-τ) : ℝ) : ℂ))‖ ≤ _
          rw [norm_mul, show Complex.I * ((c * Φ (-τ) : ℝ) : ℂ) = ((c * Φ (-τ) : ℝ) : ℂ) * Complex.I by ring,
            Complex.norm_exp_ofReal_mul_I, mul_one]
          have h := hg_bd 0 (Nat.zero_le _) (-τ) (by rw [abs_neg, abs_of_pos hτ0]; exact hτ)
          simpa [edgeW_neg, abs_neg, abs_of_pos hτ0, mul_assoc] using h)).norm
    have hle := setIntegral_mono_on hint_g
      (hw_int.1.const_mul (M_step n * A * ((c * κ * u) ^ n)⁻¹)) measurableSet_Ioi fun τ hτ => by
        have hτ0 : 0 < τ := hr0.trans hτ
        rw [norm_mul, show Complex.I * ((c * Φ (-τ) : ℝ) : ℂ) = ((c * Φ (-τ) : ℝ) : ℂ) * Complex.I by ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]
        have h := hg_bd 0 (Nat.zero_le _) (-τ) (by rw [abs_neg, abs_of_pos hτ0]; exact hτ)
        simpa [edgeW_neg, abs_neg, abs_of_pos hτ0, mul_assoc] using h
    rw [integral_const_mul] at hle
    exact hle.trans (mul_le_mul_of_nonneg_left hw_int.2 hM_tot)
  have hsum_bd := (norm_add_le _ _).trans (add_le_add hbd_neg hbd_pos)
  have hpow_eq : ((c * κ * u) ^ n)⁻¹ = (κ ^ n)⁻¹ * ((c * u) ^ n)⁻¹ := by
    rw [show c * κ * u = κ * (c * u) by ring, mul_pow, mul_inv]
  calc ‖(∫ τ in Iio (-r), g τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) +
          (∫ τ in Ioi r, g τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ)))‖
      ≤ 2 * (M_step n * A * ((c * κ * u) ^ n)⁻¹ * ((2 / ((n : ℝ) - 1 / 2) + 1) * r ^ (1 / 2 - (n : ℝ)))) := by linarith
    _ = C_tot * A * ((c * u) ^ n)⁻¹ * r ^ (1 / 2 - (n : ℝ)) := by
        simp only [C_tot, hpow_eq]; ring

/-! ### Part (1): Removing an edge cutoff -/

/-- Complex power norm `‖z ^ (s : ℂ)‖ = ‖z‖ ^ s` for `z ≠ 0` and real exponent `s`. -/
private lemma norm_cpow_ofReal_of_ne_zero {z : ℂ} (hz : z ≠ 0) (s : ℝ) :
    ‖z ^ (s : ℂ)‖ = ‖z‖ ^ s := by
  rw [Complex.cpow_def_of_ne_zero hz, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.log_re, Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]

/-- Derivative formula for `τ ↦ (lam + i τ)^α` on `τ ≠ 0`. -/
private lemma iteratedDeriv_cpow_add_I_mul (lam : ℝ) (α : ℂ) (k : ℕ) :
    ∀ τ : ℝ, τ ≠ 0 →
      iteratedDeriv k (fun s : ℝ => ((lam : ℂ) + (s : ℂ) * Complex.I) ^ α) τ =
        (∏ i ∈ Finset.range k, (α - (i : ℂ))) * Complex.I ^ k *
          ((lam : ℂ) + (τ : ℂ) * Complex.I) ^ (α - (k : ℂ)) := by
  induction k generalizing α with
  | zero => intro τ _; simp
  | succ k ih =>
    intro τ hτ
    have hopen : IsOpen {s : ℝ | s ≠ 0} := isOpen_ne
    have hderiv_ev : deriv (fun s : ℝ => ((lam : ℂ) + (s : ℂ) * Complex.I) ^ α) =ᶠ[𝓝 τ]
        (fun s : ℝ => α * Complex.I * ((lam : ℂ) + (s : ℂ) * Complex.I) ^ (α - 1)) := by
      filter_upwards [hopen.mem_nhds hτ] with s hs
      have hslit : (lam : ℂ) + (s : ℂ) * Complex.I ∈ Complex.slitPlane := by
        right; simp [hs]
      have hlin : HasDerivAt (fun t : ℝ => (lam : ℂ) + (t : ℂ) * Complex.I) Complex.I s := by
        have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
        simpa using (h1.mul_const Complex.I).const_add (lam : ℂ)
      have hcpow : HasDerivAt (fun z : ℂ => z ^ α) (α * ((lam : ℂ) + (s : ℂ) * Complex.I) ^ (α - 1))
          ((lam : ℂ) + (s : ℂ) * Complex.I) := by
        simpa using (hasDerivAt_id ((lam : ℂ) + (s : ℂ) * Complex.I)).cpow_const hslit
      have hd := ((hcpow.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s hlin).deriv
      change deriv ((fun z : ℂ => z ^ α) ∘ fun t : ℝ => (lam : ℂ) + (t : ℂ) * Complex.I) s = _
      rw [hd]
      change Complex.I * (α * ((lam : ℂ) + (s : ℂ) * Complex.I) ^ (α - 1)) = _
      ring
    rw [iteratedDeriv_succ', hderiv_ev.iteratedDeriv_eq k, iteratedDeriv_const_mul_field, ih (α - 1) τ hτ]
    have hprod : ∏ i ∈ Finset.range (k + 1), (α - (i : ℂ)) =
        α * ∏ i ∈ Finset.range k, (α - 1 - (i : ℂ)) := by
      rw [Finset.prod_range_succ']
      simp only [Nat.cast_zero, sub_zero, mul_comm _ α]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      push_cast; ring
    have hexp : α - 1 - (k : ℂ) = α - ((k + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hprod, hexp, pow_succ]; ring

private lemma contDiffOn_cpow_add_I_mul (lam : ℝ) (α : ℂ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => ((lam : ℂ) + (s : ℂ) * Complex.I) ^ α) {s : ℝ | s ≠ 0} := by
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => z ^ α) Complex.slitPlane := fun z hz =>
    ((hasDerivAt_id z).cpow_const hz).differentiableAt.differentiableWithinAt
  have hcd_slit : ContDiffOn ℂ (⊤ : ℕ∞) (fun z : ℂ => z ^ α) Complex.slitPlane :=
    (hdiff.contDiffOn Complex.isOpen_slitPlane).of_le le_top
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (lam : ℂ) + (t : ℂ) * Complex.I) :=
    contDiff_const.add ((Complex.ofRealCLM.contDiff.of_le le_top).mul contDiff_const)
  exact (hcd_slit.restrict_scalars ℝ).comp hlin.contDiffOn fun s hs => by
    right; simp [mem_ofPred_eq.mp hs]

private lemma continuous_poly_eval (P : Polynomial ℝ) : Continuous (fun x : ℝ => P.eval x) := by
  have heq : (fun x : ℝ => P.eval x) = fun x => ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * x ^ i := by
    ext x; exact Polynomial.eval_eq_sum_range x
  rw [heq]
  have hsum : ∀ s : Finset ℕ, Continuous (fun x : ℝ => ∑ i ∈ s, P.coeff i * x ^ i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [continuous_const]
    | insert a s ha ih =>
      simp_rw [Finset.sum_insert ha]
      exact (continuous_const.mul (continuous_pow a)).add ih
  exact hsum _

/-- Derivative of `t ↦ exp (-t²)` is a polynomial times `exp (-t²)`. -/
private lemma exists_poly_iteratedDeriv_gauss (k : ℕ) :
    ∃ P : Polynomial ℝ, ∀ x : ℝ,
      iteratedDeriv k (fun t : ℝ => Real.exp (-(t ^ 2))) x = P.eval x * Real.exp (-(x ^ 2)) := by
  induction k with
  | zero => exact ⟨1, fun x => by simp⟩
  | succ k ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨Polynomial.derivative P - 2 * Polynomial.X * P, fun x => ?_⟩
    rw [iteratedDeriv_succ, show iteratedDeriv k (fun t : ℝ => Real.exp (-(t ^ 2))) =
        fun t => P.eval t * Real.exp (-(t ^ 2)) from funext hP]
    have hdP : HasDerivAt (fun t => P.eval t) ((Polynomial.derivative P).eval x) x := Polynomial.hasDerivAt P x
    have hdE : HasDerivAt (fun t : ℝ => Real.exp (-(t ^ 2))) (-(2 * x) * Real.exp (-(x ^ 2))) x := by
      have h1 : HasDerivAt (fun t : ℝ => -(t ^ 2)) (-(2 * x)) x := by
        have h : HasDerivAt (fun t : ℝ => (-1 : ℝ) * t ^ 2) (-(2 * x)) x :=
          ((hasDerivAt_pow 2 x).const_mul (-1 : ℝ)).congr_deriv (by ring)
        simpa [neg_one_mul] using h
      simpa [mul_comm] using h1.exp
    have hd := (hdP.mul hdE).deriv
    rw [show (fun t => P.eval t * Real.exp (-(t ^ 2))) = (fun t => P.eval t) * (fun t => Real.exp (-(t ^ 2))) from rfl, hd]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    ring

/-- Polynomial times Gaussian is bounded on `ℝ`. -/
private lemma exists_bound_poly_mul_gauss (P : Polynomial ℝ) (m : ℕ) :
    ∃ G ≥ 0, ∀ x : ℝ, |x| ^ m * |P.eval x| * Real.exp (-(x ^ 2)) ≤ G := by
  let f : ℝ → ℝ := fun x => |x| ^ m * |P.eval x| * Real.exp (-(x ^ 2))
  have hf_cont : Continuous f := by
    have h1 : Continuous (fun x : ℝ => P.eval x) := continuous_poly_eval P
    have h2 : Continuous (fun x : ℝ => Real.exp (-(x ^ 2))) := by fun_prop
    exact ((continuous_abs.pow m).mul h1.abs).mul h2
  -- Bound `|P.eval x| ≤ C_P * (1 + |x|)^d`, and `e^{x^2} ≥ (x^2)^N / N!` for `N = m + d + 1`
  let d := P.natDegree
  let C_P : ℝ := ∑ i ∈ Finset.range (d + 1), |P.coeff i|
  have hP_bd : ∀ x : ℝ, |P.eval x| ≤ C_P * max 1 (|x| ^ d) := by
    intro x
    rw [Polynomial.eval_eq_sum_range]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simp only [C_P, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [abs_mul, abs_pow]
    have hi_le : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hpow : |x| ^ i ≤ max 1 (|x| ^ d) := by
      by_cases h1 : |x| ≤ 1
      · exact (pow_le_one₀ (abs_nonneg x) h1).trans (le_max_left _ _)
      · exact (pow_le_pow_right₀ (le_of_not_ge h1) hi_le).trans (le_max_right _ _)
    exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
  let N := m + d + 1
  have hfar : ∀ x : ℝ, 1 ≤ |x| → f x ≤ C_P * (N.factorial : ℝ) := by
    intro x hx1
    have hpos : 0 < |x| := lt_of_lt_of_le one_pos hx1
    have hmax : max 1 (|x| ^ d) = |x| ^ d := max_eq_right (one_le_pow₀ hx1)
    have hexp : (x ^ 2) ^ N / (N.factorial : ℝ) ≤ Real.exp (x ^ 2) := by
      have h := Real.sum_le_exp_of_nonneg (sq_nonneg x) (N + 1)
      have hterm : (x ^ 2) ^ N / (N.factorial : ℝ) ≤
          ∑ i ∈ Finset.range (N + 1), (x ^ 2) ^ i / (i.factorial : ℝ) :=
        Finset.single_le_sum (f := fun i => (x ^ 2) ^ i / (i.factorial : ℝ))
          (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self N))
      exact hterm.trans h
    have hexp_inv : Real.exp (-(x ^ 2)) ≤ (N.factorial : ℝ) / |x| ^ (2 * N) := by
      rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos _) (pow_pos hpos _), one_mul]
      have hsq : (x ^ 2) ^ N = |x| ^ (2 * N) := by rw [← sq_abs, ← pow_mul]
      rw [← hsq, mul_comm]
      exact (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos N))).mp hexp
    have hpow_le : |x| ^ (m + d) ≤ |x| ^ (2 * N) := pow_le_pow_right₀ hx1 (by omega)
    calc f x = |x| ^ m * |P.eval x| * Real.exp (-(x ^ 2)) := rfl
      _ ≤ |x| ^ m * (C_P * |x| ^ d) * ((N.factorial : ℝ) / |x| ^ (2 * N)) := by
          have h1 := hP_bd x; rw [hmax] at h1
          have hCP_nn : 0 ≤ C_P := Finset.sum_nonneg fun _ _ => abs_nonneg _
          gcongr
      _ = C_P * (N.factorial : ℝ) * (|x| ^ (m + d) / |x| ^ (2 * N)) := by
          rw [pow_add]; ring
      _ ≤ C_P * (N.factorial : ℝ) * 1 := by
          have hCP_nn : 0 ≤ C_P := Finset.sum_nonneg fun _ _ => abs_nonneg _
          have hdiv1 : |x| ^ (m + d) / |x| ^ (2 * N) ≤ 1 := (div_le_one (pow_pos hpos _)).mpr hpow_le
          gcongr
      _ = C_P * (N.factorial : ℝ) := mul_one _
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf_cont.continuousOn (s := Icc (-1) 1))
  refine ⟨max (max M 0) (C_P * (N.factorial : ℝ)), le_trans (le_max_right M 0) (le_max_left _ _), fun x => ?_⟩
  by_cases hx1 : |x| ≤ 1
  · have h1 := hM x (abs_le.mp hx1)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
    exact h1.trans ((le_max_left M 0).trans (le_max_left _ _))
  · exact (hfar x (le_of_not_ge hx1)).trans (le_max_right _ _)

/-- Uniform derivative bound `|∂^k e^{-ε τ²}| ≤ G_k |τ|^{-k}` for all `ε > 0`, `τ ≠ 0`,
plus pointwise limit as `ε ↓ 0` and rapid decay as `|τ| → ∞`. -/
private lemma gauss_reg_bounds (k : ℕ) :
    ∃ G ≥ 0, (∀ ε : ℝ, 0 < ε → ∀ τ : ℝ, τ ≠ 0 →
      |iteratedDeriv k (fun t : ℝ => Real.exp (-(ε * t ^ 2))) τ| ≤ G * |τ| ^ (-(k : ℤ))) ∧
    (∀ τ : ℝ, Tendsto (fun ε : ℝ => iteratedDeriv k (fun t : ℝ => Real.exp (-(ε * t ^ 2))) τ)
      (𝓝[>] (0 : ℝ)) (𝓝 (if k = 0 then 1 else 0))) ∧
    (∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ C_m ≥ 0, ∀ τ : ℝ, 1 ≤ |τ| →
      |iteratedDeriv k (fun t : ℝ => Real.exp (-(ε * t ^ 2))) τ| ≤ C_m * |τ| ^ (-(m : ℤ))) := by
  obtain ⟨P, hP⟩ := exists_poly_iteratedDeriv_gauss k
  obtain ⟨G, hG, hG_bd⟩ := exists_bound_poly_mul_gauss P k
  have hscale : ∀ ε : ℝ, 0 < ε → ∀ τ : ℝ,
      iteratedDeriv k (fun t : ℝ => Real.exp (-(ε * t ^ 2))) τ =
        (Real.sqrt ε) ^ k * P.eval (Real.sqrt ε * τ) * Real.exp (-(ε * τ ^ 2)) := by
    intro ε hε τ
    have heq : (fun t : ℝ => Real.exp (-(ε * t ^ 2))) =
        fun t => (fun u => Real.exp (-(u ^ 2))) (Real.sqrt ε * t) := by
      ext t; congr 2; rw [mul_pow, Real.sq_sqrt hε.le]
    rw [heq, iteratedDeriv_comp_const_mul k (fun u => Real.exp (-(u ^ 2))) (Real.sqrt ε) τ,
      hP (Real.sqrt ε * τ), mul_pow, Real.sq_sqrt hε.le]
    ring
  refine ⟨G, hG, ?_, ?_, ?_⟩
  · intro ε hε τ hτ
    rw [hscale ε hε τ, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.sqrt_pos.mpr hε),
      abs_of_pos (Real.exp_pos _), zpow_neg, zpow_natCast, ← div_eq_mul_inv,
      le_div_iff₀ (pow_pos (abs_pos.mpr hτ) k)]
    have h1 := hG_bd (Real.sqrt ε * τ)
    rw [abs_mul, abs_of_pos (Real.sqrt_pos.mpr hε), mul_pow, mul_pow, Real.sq_sqrt hε.le] at h1
    linarith
  · intro τ
    have hsqrt0 : Tendsto (fun ε : ℝ => Real.sqrt ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa using ((Real.continuous_sqrt.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds)
    have hlim : Tendsto (fun ε : ℝ => (Real.sqrt ε) ^ k * P.eval (Real.sqrt ε * τ) * Real.exp (-(ε * τ ^ 2)))
        (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) ^ k * P.eval (0 * τ) * Real.exp (-(0 * τ ^ 2)))) := by
      refine ((hsqrt0.pow k).mul (((continuous_poly_eval P).continuousAt.tendsto).comp (hsqrt0.mul_const τ))).mul ?_
      exact Real.continuous_exp.continuousAt.tendsto.comp
        (((tendsto_id.mono_left nhdsWithin_le_nhds).mul_const (τ ^ 2)).neg)
    have hval : (0 : ℝ) ^ k * P.eval (0 * τ) * Real.exp (-(0 * τ ^ 2)) = if k = 0 then 1 else 0 := by
      cases k with
      | zero =>
        have hP0 : P.eval 0 = 1 := by
          have := hP 0; simp at this; exact this.symm
        simp [hP0]
      | succ k => simp
    rw [hval] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hscale ε hε τ).symm
  · intro ε hε m
    obtain ⟨Gm, hGm, hGm_bd⟩ := exists_bound_poly_mul_gauss P m
    refine ⟨(Real.sqrt ε) ^ k / (Real.sqrt ε) ^ m * Gm, by positivity, fun τ hτ1 => ?_⟩
    have hτ0 : 0 < |τ| := lt_of_lt_of_le one_pos hτ1
    rw [hscale ε hε τ, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.sqrt_pos.mpr hε),
      abs_of_pos (Real.exp_pos _), zpow_neg, zpow_natCast, ← div_eq_mul_inv,
      le_div_iff₀ (pow_pos hτ0 m)]
    have h1 := hGm_bd (Real.sqrt ε * τ)
    rw [abs_mul, abs_of_pos (Real.sqrt_pos.mpr hε), mul_pow, mul_pow, Real.sq_sqrt hε.le] at h1
    have hsq_pos : 0 < (Real.sqrt ε) ^ m := pow_pos (Real.sqrt_pos.mpr hε) m
    have h2 : |τ| ^ m * |P.eval (Real.sqrt ε * τ)| * Real.exp (-(ε * τ ^ 2)) ≤ Gm / (Real.sqrt ε) ^ m := by
      rw [le_div_iff₀ hsq_pos]; linarith
    calc Real.sqrt ε ^ k * |P.eval (Real.sqrt ε * τ)| * Real.exp (-(ε * τ ^ 2)) * |τ| ^ m
        = Real.sqrt ε ^ k * (|τ| ^ m * |P.eval (Real.sqrt ε * τ)| * Real.exp (-(ε * τ ^ 2))) := by ring
      _ ≤ Real.sqrt ε ^ k * (Gm / (Real.sqrt ε) ^ m) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Real.sqrt ε ^ k / Real.sqrt ε ^ m * Gm := by ring

/-- **Lemma FCT.5a (`fct:edge-ibp`), Part (1) (Removing an edge cutoff)**
(`constant_terms_five.tex`, lines 524–537). -/
theorem fct_edge_ibp_cutoff {n j : ℕ} (_hn : 1 ≤ n) (hjn : j < n)
    {ψ₀ : ℝ → ℝ} (hψ_cd : ContDiff ℝ (⊤ : ℕ∞) ψ₀)
    (hψ_one : ∀ t : ℝ, |t| ≤ 1 → ψ₀ t = 1)
    (hψ_zero : ∀ t : ℝ, 2 ≤ |t| → ψ₀ t = 0) :
    ∃ C ≥ 0, ∀ {c u r lam : ℝ}, 0 < c → 0 < u → 0 < r → r ≤ 1 → 0 ≤ lam →
      ∃ I : ℂ,
        Tendsto (fun ε : ℝ =>
          ∫ τ : ℝ, ((1 - ψ₀ (τ / r) : ℝ) : ℂ) * ((lam : ℂ) + (τ : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
            (τ : ℂ) ^ j * Complex.exp (Complex.I * ((c * u * τ : ℝ) : ℂ) - ((ε * τ ^ 2 : ℝ) : ℂ)))
          (𝓝[>] (0 : ℝ)) (𝓝 I) ∧
        ‖I‖ ≤ C * ((c * u) ^ n)⁻¹ * r ^ ((j : ℝ) + 1 / 2 - (n : ℝ)) := by
  -- 1. Uniform derivative bounds for the 4 factors (independent of `c, u, r, lam, ε`)
  -- Factor 1: `f1(τ) = 1 - ψ₀(τ/r)`
  have hM1 : ∀ k : ℕ, ∃ M ≥ 0, ∀ {r : ℝ}, 0 < r → ∀ τ : ℝ, τ ≠ 0 →
      |iteratedDeriv k (fun t : ℝ => 1 - ψ₀ (t / r)) τ| ≤ M * |τ| ^ (-(k : ℤ)) := by
    intro k
    have hcont : Continuous (iteratedDeriv k ψ₀) := hψ_cd.continuous_iteratedDeriv k (by simp)
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont.continuousOn (s := Icc (-2) 2))
    cases k with
    | zero =>
      refine ⟨1 + max M 0, by positivity, fun {r} hr0 τ _ => ?_⟩
      simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one]
      by_cases h2 : |τ / r| ≤ 2
      · have h1 := hM (τ / r) (abs_le.mp h2)
        rw [Real.norm_eq_abs, iteratedDeriv_zero] at h1
        have htri := abs_sub (1 : ℝ) (ψ₀ (τ / r))
        rw [abs_one] at htri
        linarith [le_max_left M 0]
      · rw [hψ_zero (τ / r) (le_of_not_ge h2), sub_zero, abs_one]
        linarith [le_max_right M 0]
    | succ k =>
      refine ⟨2 ^ (k + 1) * max M 0, by positivity, fun {r} hr0 τ hτ => ?_⟩
      have hder : iteratedDeriv (k + 1) (fun t : ℝ => 1 - ψ₀ (t / r)) τ =
          -(r⁻¹ ^ (k + 1) * iteratedDeriv (k + 1) ψ₀ (τ / r)) := by
        have h1 : (fun t : ℝ => 1 - ψ₀ (t / r)) = (fun _ => (1 : ℝ)) - (fun t => ψ₀ (r⁻¹ * t)) := by
          ext t; simp [div_eq_inv_mul]
        have hsub : iteratedDeriv (k + 1) ((fun _ : ℝ => (1 : ℝ)) - (fun t : ℝ => ψ₀ (r⁻¹ * t))) τ =
            iteratedDeriv (k + 1) (fun _ : ℝ => (1 : ℝ)) τ - iteratedDeriv (k + 1) (fun t : ℝ => ψ₀ (r⁻¹ * t)) τ :=
          iteratedDeriv_sub (contDiffAt_const.of_le (WithTop.coe_le_coe.mpr le_top))
            ((hψ_cd.comp (contDiff_const.mul contDiff_id)).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
        rw [h1, hsub, iteratedDeriv_const_succ, zero_sub,
          iteratedDeriv_comp_const_mul (k + 1) ψ₀ r⁻¹ τ, div_eq_inv_mul]
      rw [hder, abs_neg, abs_mul, abs_pow, abs_of_pos (inv_pos.mpr hr0)]
      by_cases h2 : |τ / r| < 2
      · have h1 := hM (τ / r) (abs_le.mp h2.le)
        rw [Real.norm_eq_abs] at h1
        have hτ_le : |τ| ≤ 2 * r := by
          rw [abs_div, abs_of_pos hr0, div_lt_iff₀ hr0] at h2; linarith
        have hr_inv : r⁻¹ ≤ 2 * |τ|⁻¹ := by
          rw [inv_le_iff_one_le_mul₀ hr0]
          have : 1 ≤ 2 * r / |τ| := (one_le_div (abs_pos.mpr hτ)).mpr hτ_le
          linarith [show 2 * |τ|⁻¹ * r = 2 * r / |τ| by ring]
        have hpow : r⁻¹ ^ (k + 1) ≤ 2 ^ (k + 1) * |τ| ^ (-((k + 1 : ℕ) : ℤ)) := by
          calc r⁻¹ ^ (k + 1) ≤ (2 * |τ|⁻¹) ^ (k + 1) :=
                pow_le_pow_left₀ (inv_nonneg.mpr hr0.le) hr_inv (k + 1)
            _ = 2 ^ (k + 1) * |τ| ^ (-((k + 1 : ℕ) : ℤ)) := by
                rw [mul_pow, zpow_neg, zpow_natCast, inv_pow]
        calc r⁻¹ ^ (k + 1) * |iteratedDeriv (k + 1) ψ₀ (τ / r)|
            ≤ (2 ^ (k + 1) * |τ| ^ (-((k + 1 : ℕ) : ℤ))) * max M 0 :=
              mul_le_mul hpow (h1.trans (le_max_left M 0)) (abs_nonneg _) (by positivity)
          _ = 2 ^ (k + 1) * max M 0 * |τ| ^ (-((k + 1 : ℕ) : ℤ)) := by ring
      · -- `2 ≤ |τ / r|`: `iteratedDeriv (k + 1) ψ₀ (τ / r) = 0` by continuity from `|t| > 2`
        have hge2 : 2 ≤ |τ / r| := not_lt.mp h2
        have hzero_der : iteratedDeriv (k + 1) ψ₀ (τ / r) = 0 := by
          rcases le_or_gt 0 (τ / r) with hnn | hneg
          · have h2le : 2 ≤ τ / r := by rwa [abs_of_nonneg hnn] at hge2
            have hlim : Tendsto (iteratedDeriv (k + 1) ψ₀) (𝓝[>] (τ / r)) (𝓝 0) := by
              refine tendsto_const_nhds.congr' ?_
              filter_upwards [self_mem_nhdsWithin] with y hy
              have hev : ψ₀ =ᶠ[𝓝 y] (0 : ℝ → ℝ) :=
                Filter.eventually_of_mem (isOpen_Ioi.mem_nhds (lt_of_le_of_lt h2le hy)) fun s hs =>
                  hψ_zero s (by rw [abs_of_pos (by linarith [mem_Ioi.mp hs])]; linarith [mem_Ioi.mp hs])
              rw [hev.iteratedDeriv_eq (k + 1), iteratedDeriv_const_zero]
            exact tendsto_nhds_unique (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hlim
          · have h2le : τ / r ≤ -2 := by rw [abs_of_neg hneg] at hge2; linarith
            have hlim : Tendsto (iteratedDeriv (k + 1) ψ₀) (𝓝[<] (τ / r)) (𝓝 0) := by
              refine tendsto_const_nhds.congr' ?_
              filter_upwards [self_mem_nhdsWithin] with y hy
              have hev : ψ₀ =ᶠ[𝓝 y] (0 : ℝ → ℝ) :=
                Filter.eventually_of_mem (isOpen_Iio.mem_nhds (lt_of_lt_of_le hy h2le)) fun s hs =>
                  hψ_zero s (by rw [abs_of_neg (by linarith [mem_Iio.mp hs])]; linarith [mem_Iio.mp hs])
              rw [hev.iteratedDeriv_eq (k + 1), iteratedDeriv_const_zero]
            exact tendsto_nhds_unique (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hlim
        rw [hzero_der, abs_zero, mul_zero]; positivity
  choose M1 hM1_nn hM1_bd using hM1
  -- Factor 2: `f2(τ) = (lam + i τ)^{-1/2}`
  let M2 : ℕ → ℝ := fun k => ‖∏ i ∈ Finset.range k, (-(1 / 2 : ℂ) - (i : ℂ))‖
  have hM2_bd : ∀ k : ℕ, ∀ {lam : ℝ}, 0 ≤ lam → ∀ τ : ℝ, τ ≠ 0 →
      ‖iteratedDeriv k (fun s : ℝ => ((lam : ℂ) + (s : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))) τ‖ ≤
        M2 k * |τ| ^ (-(1 / 2 : ℝ) - (k : ℝ)) := by
    intro k lam _ τ hτ
    rw [iteratedDeriv_cpow_add_I_mul lam (-(1 / 2 : ℂ)) k τ hτ, norm_mul, norm_mul, norm_pow,
      Complex.norm_I, one_pow, mul_one]
    have hne : (lam : ℂ) + (τ : ℂ) * Complex.I ≠ 0 := fun h => by
      have := congrArg Complex.im h; simp at this; exact hτ this
    have hexp : (-(1 / 2 : ℂ) - (k : ℂ)) = ((-(1 / 2 : ℝ) - (k : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [hexp, norm_cpow_ofReal_of_ne_zero hne]
    have hge : |τ| ≤ ‖(lam : ℂ) + (τ : ℂ) * Complex.I‖ := by
      have := Complex.abs_im_le_norm ((lam : ℂ) + (τ : ℂ) * Complex.I)
      simpa using this
    have hrpow : ‖(lam : ℂ) + (τ : ℂ) * Complex.I‖ ^ (-(1 / 2 : ℝ) - (k : ℝ)) ≤ |τ| ^ (-(1 / 2 : ℝ) - (k : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (abs_pos.mpr hτ) hge (by linarith [Nat.cast_nonneg (α := ℝ) k])
    exact mul_le_mul_of_nonneg_left hrpow (norm_nonneg _)
  -- Factor 3: `f3(τ) = τ^j`
  have hM3_bd : ∀ k : ℕ, ∀ τ : ℝ, τ ≠ 0 →
      ‖iteratedDeriv k (fun s : ℝ => (s : ℂ) ^ j) τ‖ ≤ (j.factorial : ℝ) * |τ| ^ ((j : ℝ) - (k : ℝ)) := by
    have hpow_der : ∀ (k d : ℕ) (τ : ℝ),
        iteratedDeriv k (fun s : ℝ => (s : ℂ) ^ d) τ =
          if k ≤ d then ((d.descFactorial k : ℝ) : ℂ) * (τ : ℂ) ^ (d - k) else 0 := by
      intro k
      induction k with
      | zero => intro d τ; simp
      | succ k ih =>
        intro d τ
        rw [iteratedDeriv_succ']
        have hd : deriv (fun s : ℝ => (s : ℂ) ^ d) = fun s : ℝ => ((d : ℝ) : ℂ) * (s : ℂ) ^ (d - 1) := by
          ext s
          have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
          have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ d) (((d : ℝ) : ℂ) * (s : ℂ) ^ (d - 1)) s :=
            (h1.pow d).congr_deriv (by push_cast; ring)
          exact h2.deriv
        rw [hd, iteratedDeriv_const_mul_field, ih (d - 1) τ]
        cases d with
        | zero => simp
        | succ d =>
          simp only [Nat.add_sub_cancel]
          by_cases hk : k ≤ d
          · have hk1 : k + 1 ≤ d + 1 := Nat.succ_le_succ hk
            simp only [hk, hk1, ↓reduceIte]
            rw [Nat.succ_descFactorial_succ]
            push_cast; ring
          · have hk1 : ¬ (k + 1 ≤ d + 1) := by omega
            simp [hk, hk1]
    intro k τ hτ
    rw [hpow_der k j τ]
    split_ifs with hk
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        norm_pow, Complex.norm_real, Real.norm_eq_abs]
      have hdesc : (j.descFactorial k : ℝ) ≤ (j.factorial : ℝ) := by
        exact_mod_cast descFactorial_le_factorial_local j k hk
      have hpow_eq : |τ| ^ (j - k) = |τ| ^ ((j : ℝ) - (k : ℝ)) := by
        rw [← Real.rpow_natCast, Nat.cast_sub hk]
      rw [hpow_eq]
      exact mul_le_mul_of_nonneg_right hdesc (Real.rpow_nonneg (abs_nonneg τ) _)
    · rw [norm_zero]; positivity
  -- Factor 4: Gaussian regulator
  choose G4 hG4_nn hG4_bd hG4_lim hG4_far using gauss_reg_bounds
  -- Combine the 3 non-Gaussian factors `a0 = f1 * f2 * f3`
  let C12 : ℕ → ℝ := fun k => ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * M1 i * M2 (k - i)
  let C123 : ℕ → ℝ := fun k => ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C12 i * (j.factorial : ℝ)
  let C_tot_sym : ℕ → ℝ := fun k => ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C123 i * G4 (k - i)
  have hC12_nn : ∀ k, 0 ≤ C12 k := fun k => Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hM1_nn i)) (norm_nonneg _)
  have hC123_nn : ∀ k, 0 ≤ C123 k := fun k => Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC12_nn i)) (Nat.cast_nonneg _)
  have hC_sym_nn : ∀ k, 0 ≤ C_tot_sym k := fun k => Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC123_nn i)) (hG4_nn _)
  have hdenom_pos : (0 : ℝ) < (n : ℝ) - (j : ℝ) - 1 / 2 := by
    have : (j : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hjn
    linarith
  refine ⟨2 * C_tot_sym n / ((n : ℝ) - (j : ℝ) - 1 / 2), div_nonneg (mul_nonneg zero_le_two (hC_sym_nn n)) hdenom_pos.le,
    fun {c u r lam} hc hu hr0 hr1 hlam => ?_⟩
  let f1 : ℝ → ℂ := fun τ => ((1 - ψ₀ (τ / r) : ℝ) : ℂ)
  let f2 : ℝ → ℂ := fun τ => ((lam : ℂ) + (τ : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))
  let f3 : ℝ → ℂ := fun τ => (τ : ℂ) ^ j
  let a0 : ℝ → ℂ := fun τ => f1 τ * f2 τ * f3 τ
  let g_eps : ℝ → ℝ → ℂ := fun ε τ => ((Real.exp (-(ε * τ ^ 2)) : ℝ) : ℂ)
  let a_eps : ℝ → ℝ → ℂ := fun ε τ => a0 τ * g_eps ε τ
  let E : ℝ → ℂ := fun τ => Complex.exp (Complex.I * ((c * u * τ : ℝ) : ℂ))
  have hopen : IsOpen {τ : ℝ | τ ≠ 0} := isOpen_ne
  have hf1_cd : ContDiff ℝ (⊤ : ℕ∞) f1 :=
    (Complex.ofRealCLM.contDiff.of_le le_top).comp
      (contDiff_const.sub (hψ_cd.comp (contDiff_id.div_const r)))
  have hf2_cd : ContDiffOn ℝ (⊤ : ℕ∞) f2 {τ : ℝ | τ ≠ 0} := contDiffOn_cpow_add_I_mul lam (-(1 / 2 : ℂ))
  have hf3_cd : ContDiff ℝ (⊤ : ℕ∞) f3 := (Complex.ofRealCLM.contDiff.of_le le_top).pow j
  have ha0_cd : ContDiffOn ℝ (⊤ : ℕ∞) a0 {τ : ℝ | τ ≠ 0} :=
    (hf1_cd.contDiffOn.mul hf2_cd).mul hf3_cd.contDiffOn
  have hge_cd : ∀ ε : ℝ, ContDiff ℝ (⊤ : ℕ∞) (g_eps ε) := fun ε =>
    (Complex.ofRealCLM.contDiff.of_le le_top).comp (Real.contDiff_exp.comp ((contDiff_const.mul (contDiff_id.pow 2)).neg))
  -- Derivative bound for `a0` on `τ ≠ 0`
  have ha0_bd : ∀ k : ℕ, ∀ τ : ℝ, τ ≠ 0 →
      ‖iteratedDeriv k a0 τ‖ ≤ C123 k * |τ| ^ ((j : ℝ) - 1 / 2 - (k : ℝ)) := by
    have hf12_bd : ∀ k : ℕ, ∀ τ : ℝ, τ ≠ 0 →
        ‖iteratedDeriv k (fun s => f1 s * f2 s) τ‖ ≤ C12 k * |τ| ^ (-(1 / 2 : ℝ) - (k : ℝ)) := by
      intro k τ hτ
      have h1_at : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) f1 τ := hf1_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      have h2_at : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) f2 τ :=
        (hf2_cd.contDiffAt (hopen.mem_nhds hτ)).of_le (WithTop.coe_le_coe.mpr le_top)
      rw [show (fun s => f1 s * f2 s) = f1 * f2 from rfl, iteratedDeriv_mul h1_at h2_at]
      refine (norm_sum_le _ _).trans ?_
      simp only [C12, Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      have hi_le : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      have h1 : ‖iteratedDeriv i f1 τ‖ ≤ M1 i * |τ| ^ (-(i : ℤ)) := by
        rw [show iteratedDeriv i f1 τ = ((iteratedDeriv i (fun t => 1 - ψ₀ (t / r)) τ : ℝ) : ℂ) from
            iteratedDeriv_ofReal_comp i (fun t => 1 - ψ₀ (t / r)) τ,
          Complex.norm_real, Real.norm_eq_abs]
        exact hM1_bd i hr0 τ hτ
      have h2 := hM2_bd (k - i) hlam τ hτ
      have hpow : |τ| ^ (-(i : ℤ)) * |τ| ^ (-(1 / 2 : ℝ) - ((k - i : ℕ) : ℝ)) = |τ| ^ (-(1 / 2 : ℝ) - (k : ℝ)) := by
        rw [← Real.rpow_intCast |τ| (-(i : ℤ)), ← Real.rpow_add (abs_pos.mpr hτ)]
        congr 1; rw [Nat.cast_sub hi_le]; push_cast; ring
      calc (k.choose i : ℝ) * ‖iteratedDeriv i f1 τ‖ * ‖iteratedDeriv (k - i) f2 τ‖
          ≤ (k.choose i : ℝ) * (M1 i * |τ| ^ (-(i : ℤ))) * (M2 (k - i) * |τ| ^ (-(1 / 2 : ℝ) - ((k - i : ℕ) : ℝ))) := by
            have := hM1_nn i; gcongr
        _ = (k.choose i : ℝ) * M1 i * M2 (k - i) * (|τ| ^ (-(i : ℤ)) * |τ| ^ (-(1 / 2 : ℝ) - ((k - i : ℕ) : ℝ))) := by ring
        _ = (k.choose i : ℝ) * M1 i * M2 (k - i) * |τ| ^ (-(1 / 2 : ℝ) - (k : ℝ)) := by rw [hpow]
    intro k τ hτ
    have h12_at : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) (fun s => f1 s * f2 s) τ :=
      ((hf1_cd.contDiffOn.mul hf2_cd).contDiffAt (hopen.mem_nhds hτ)).of_le (WithTop.coe_le_coe.mpr le_top)
    have h3_at : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) f3 τ := hf3_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    rw [show a0 = (fun s => f1 s * f2 s) * f3 from rfl, iteratedDeriv_mul h12_at h3_at]
    refine (norm_sum_le _ _).trans ?_
    simp only [C123, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi_le : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    have h1 := hf12_bd i τ hτ
    have h2 := hM3_bd (k - i) τ hτ
    have hpow : |τ| ^ (-(1 / 2 : ℝ) - (i : ℝ)) * |τ| ^ ((j : ℝ) - ((k - i : ℕ) : ℝ)) =
        |τ| ^ ((j : ℝ) - 1 / 2 - (k : ℝ)) := by
      rw [← Real.rpow_add (abs_pos.mpr hτ)]
      congr 1; rw [Nat.cast_sub hi_le]; ring
    calc (k.choose i : ℝ) * ‖iteratedDeriv i (fun s => f1 s * f2 s) τ‖ * ‖iteratedDeriv (k - i) f3 τ‖
        ≤ (k.choose i : ℝ) * (C12 i * |τ| ^ (-(1 / 2 : ℝ) - (i : ℝ))) *
            ((j.factorial : ℝ) * |τ| ^ ((j : ℝ) - ((k - i : ℕ) : ℝ))) := by
          have := hC12_nn i; gcongr
      _ = (k.choose i : ℝ) * C12 i * (j.factorial : ℝ) *
            (|τ| ^ (-(1 / 2 : ℝ) - (i : ℝ)) * |τ| ^ ((j : ℝ) - ((k - i : ℕ) : ℝ))) := by ring
      _ = (k.choose i : ℝ) * C12 i * (j.factorial : ℝ) * |τ| ^ ((j : ℝ) - 1 / 2 - (k : ℝ)) := by rw [hpow]
  -- Uniform derivative bound for `a_eps ε` on `τ ≠ 0`
  have ha_eps_bd : ∀ k : ℕ, ∀ ε : ℝ, 0 < ε → ∀ τ : ℝ, τ ≠ 0 →
      ‖iteratedDeriv k (a_eps ε) τ‖ ≤ C_tot_sym k * |τ| ^ ((j : ℝ) - 1 / 2 - (k : ℝ)) := by
    intro k ε hε τ hτ
    have h0_at : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) a0 τ :=
      (ha0_cd.contDiffAt (hopen.mem_nhds hτ)).of_le (WithTop.coe_le_coe.mpr le_top)
    have h4_at : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) (g_eps ε) τ :=
      (hge_cd ε).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    rw [show a_eps ε = a0 * g_eps ε from rfl, iteratedDeriv_mul h0_at h4_at]
    refine (norm_sum_le _ _).trans ?_
    simp only [C_tot_sym, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi_le : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    have h1 := ha0_bd i τ hτ
    have h4 : ‖iteratedDeriv (k - i) (g_eps ε) τ‖ ≤ G4 (k - i) * |τ| ^ (-((k - i : ℕ) : ℤ)) := by
      rw [show iteratedDeriv (k - i) (g_eps ε) τ =
          ((iteratedDeriv (k - i) (fun t => Real.exp (-(ε * t ^ 2))) τ : ℝ) : ℂ) from
            iteratedDeriv_ofReal_comp (k - i) (fun t => Real.exp (-(ε * t ^ 2))) τ,
        Complex.norm_real, Real.norm_eq_abs]
      exact hG4_bd (k - i) ε hε τ hτ
    have hpow : |τ| ^ ((j : ℝ) - 1 / 2 - (i : ℝ)) * |τ| ^ (-((k - i : ℕ) : ℤ)) =
        |τ| ^ ((j : ℝ) - 1 / 2 - (k : ℝ)) := by
      rw [← Real.rpow_intCast |τ| (-((k - i : ℕ) : ℤ)), ← Real.rpow_add (abs_pos.mpr hτ)]
      congr 1; rw [Nat.cast_sub hi_le]; push_cast; ring
    calc (k.choose i : ℝ) * ‖iteratedDeriv i a0 τ‖ * ‖iteratedDeriv (k - i) (g_eps ε) τ‖
        ≤ (k.choose i : ℝ) * (C123 i * |τ| ^ ((j : ℝ) - 1 / 2 - (i : ℝ))) *
            (G4 (k - i) * |τ| ^ (-((k - i : ℕ) : ℤ))) := by
          have := hC123_nn i; have := hG4_nn (k - i); gcongr
      _ = (k.choose i : ℝ) * C123 i * G4 (k - i) *
            (|τ| ^ ((j : ℝ) - 1 / 2 - (i : ℝ)) * |τ| ^ (-((k - i : ℕ) : ℤ))) := by ring
      _ = (k.choose i : ℝ) * C123 i * G4 (k - i) * |τ| ^ ((j : ℝ) - 1 / 2 - (k : ℝ)) := by rw [hpow]
  -- Rapid decay of `iteratedDeriv k (a_eps ε)` for fixed `ε > 0`
  have ha_eps_far : ∀ k : ℕ, ∀ ε : ℝ, 0 < ε → ∃ M ≥ 0, ∀ τ : ℝ, 1 ≤ |τ| →
      ‖iteratedDeriv k (a_eps ε) τ‖ ≤ M * |τ| ^ (-2 : ℝ) := by
    intro k ε hε
    have hC_far : ∀ i : ℕ, ∃ C_i ≥ 0, ∀ τ : ℝ, 1 ≤ |τ| →
        ‖iteratedDeriv (k - i) (g_eps ε) τ‖ ≤ C_i * |τ| ^ (-((j + 2 : ℕ) : ℤ)) := by
      intro i
      obtain ⟨Ci, hCi, hbd⟩ := hG4_far (k - i) ε hε (j + 2)
      refine ⟨Ci, hCi, fun τ hτ1 => ?_⟩
      rw [show iteratedDeriv (k - i) (g_eps ε) τ =
          ((iteratedDeriv (k - i) (fun t => Real.exp (-(ε * t ^ 2))) τ : ℝ) : ℂ) from
            iteratedDeriv_ofReal_comp (k - i) (fun t => Real.exp (-(ε * t ^ 2))) τ,
        Complex.norm_real, Real.norm_eq_abs]
      exact hbd τ hτ1
    choose C_f hCf_nn hCf_bd using hC_far
    refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C123 i * C_f i,
      Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC123_nn i)) (hCf_nn i),
      fun τ hτ1 => ?_⟩
    have hτ_ne : τ ≠ 0 := abs_pos.mp (lt_of_lt_of_le one_pos hτ1)
    have h0_at : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) a0 τ :=
      (ha0_cd.contDiffAt (hopen.mem_nhds hτ_ne)).of_le (WithTop.coe_le_coe.mpr le_top)
    have h4_at : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) (g_eps ε) τ :=
      (hge_cd ε).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    rw [show a_eps ε = a0 * g_eps ε from rfl, iteratedDeriv_mul h0_at h4_at]
    refine (norm_sum_le _ _).trans ?_
    simp only [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    have h1 := ha0_bd i τ hτ_ne
    have h4 := hCf_bd i τ hτ1
    have hpow : |τ| ^ ((j : ℝ) - 1 / 2 - (i : ℝ)) * |τ| ^ (-((j + 2 : ℕ) : ℤ)) ≤ |τ| ^ (-2 : ℝ) := by
      rw [← Real.rpow_intCast |τ| (-((j + 2 : ℕ) : ℤ)), ← Real.rpow_add (lt_of_lt_of_le one_pos hτ1)]
      exact Real.rpow_le_rpow_of_exponent_le hτ1 (by push_cast; linarith)
    calc (k.choose i : ℝ) * ‖iteratedDeriv i a0 τ‖ * ‖iteratedDeriv (k - i) (g_eps ε) τ‖
        ≤ (k.choose i : ℝ) * (C123 i * |τ| ^ ((j : ℝ) - 1 / 2 - (i : ℝ))) *
            (C_f i * |τ| ^ (-((j + 2 : ℕ) : ℤ))) := by
          have := hC123_nn i; have := hCf_nn i; gcongr
      _ = (k.choose i : ℝ) * C123 i * C_f i *
            (|τ| ^ ((j : ℝ) - 1 / 2 - (i : ℝ)) * |τ| ^ (-((j + 2 : ℕ) : ℤ))) := by ring
      _ ≤ (k.choose i : ℝ) * C123 i * C_f i * |τ| ^ (-2 : ℝ) := by
          have := hC123_nn i; have := hCf_nn i; gcongr
  -- Pointwise convergence `iteratedDeriv n (a_eps ε) τ → iteratedDeriv n a0 τ` as `ε ↓ 0`
  have ha_eps_lim : ∀ τ : ℝ, τ ≠ 0 →
      Tendsto (fun ε : ℝ => iteratedDeriv n (a_eps ε) τ) (𝓝[>] (0 : ℝ)) (𝓝 (iteratedDeriv n a0 τ)) := by
    intro τ hτ
    have hsum : Tendsto (fun ε : ℝ => ∑ i ∈ Finset.range (n + 1),
        ((n.choose i : ℝ) : ℂ) * iteratedDeriv i a0 τ * iteratedDeriv (n - i) (g_eps ε) τ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∑ i ∈ Finset.range (n + 1),
          ((n.choose i : ℝ) : ℂ) * iteratedDeriv i a0 τ * (if n - i = 0 then (1 : ℂ) else 0))) := by
      refine tendsto_finset_sum_local _ fun i _ => ?_
      have h1 : Tendsto (fun ε : ℝ => iteratedDeriv (n - i) (g_eps ε) τ)
          (𝓝[>] (0 : ℝ)) (𝓝 (if n - i = 0 then (1 : ℂ) else 0)) := by
        have hr := hG4_lim (n - i) τ
        have hC := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
        have hval : ((if n - i = 0 then (1 : ℝ) else 0 : ℝ) : ℂ) = if n - i = 0 then 1 else 0 := by
          split_ifs <;> simp
        rw [hval] at hC
        refine hC.congr fun ε => ?_
        exact (iteratedDeriv_ofReal_comp (n - i) (fun t => Real.exp (-(ε * t ^ 2))) τ).symm
      exact h1.const_mul _
    have hval_sum : ∑ i ∈ Finset.range (n + 1),
        ((n.choose i : ℝ) : ℂ) * iteratedDeriv i a0 τ * (if n - i = 0 then (1 : ℂ) else 0) =
        iteratedDeriv n a0 τ := by
      rw [Finset.sum_eq_single n]
      · simp
      · intro i hi hne
        have : n - i ≠ 0 := by have := Finset.mem_range.mp hi; omega
        simp [this]
      · intro hnot; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) hnot
    rw [hval_sum] at hsum
    refine hsum.congr fun ε => ?_
    have h0_at : ContDiffAt ℝ ((n : ℕ) : WithTop ℕ∞) a0 τ :=
      (ha0_cd.contDiffAt (hopen.mem_nhds hτ)).of_le (WithTop.coe_le_coe.mpr le_top)
    have h4_at : ContDiffAt ℝ ((n : ℕ) : WithTop ℕ∞) (g_eps ε) τ :=
      (hge_cd ε).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    rw [show a_eps ε = a0 * g_eps ε from rfl, iteratedDeriv_mul h0_at h4_at]
    rfl
  -- Vanishing of `a_eps ε` and its derivatives on `(-r, r)` (hence limit 0 at `r⁺` and `(-r)⁻`)
  have ha_eps_zero_mid : ∀ ε : ℝ, ∀ τ : ℝ, |τ| ≤ r → a_eps ε τ = 0 := by
    intro ε τ hτ
    have h1 : |τ / r| ≤ 1 := by rw [abs_div, abs_of_pos hr0, div_le_one hr0]; exact hτ
    simp [a_eps, a0, f1, hψ_one (τ / r) h1]
  have ha_eps_lim_r : ∀ k : ℕ, ∀ ε : ℝ, Tendsto (iteratedDeriv k (a_eps ε)) (𝓝[>] r) (𝓝 0) := by
    intro k ε
    have hcont : ContinuousOn (iteratedDeriv k (a_eps ε)) {τ : ℝ | τ ≠ 0} :=
      (contDiffOn_iteratedDeriv_of_isOpen hopen (ha0_cd.mul (hge_cd ε).contDiffOn) k).continuousOn
    have hcont_r : ContinuousAt (iteratedDeriv k (a_eps ε)) r :=
      hcont.continuousAt (hopen.mem_nhds hr0.ne')
    have h0_r : iteratedDeriv k (a_eps ε) r = 0 := by
      have hlim_l : Tendsto (iteratedDeriv k (a_eps ε)) (𝓝[<] r) (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsLT hr0] with τ hτ
        have hev : a_eps ε =ᶠ[𝓝 τ] (0 : ℝ → ℂ) :=
          Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hτ) fun s hs =>
            ha_eps_zero_mid ε s (by rw [abs_of_pos hs.1]; exact hs.2.le)
        rw [hev.iteratedDeriv_eq k, iteratedDeriv_const_zero]
      exact tendsto_nhds_unique (hcont_r.tendsto.mono_left nhdsWithin_le_nhds) hlim_l
    rw [← h0_r]; exact hcont_r.tendsto.mono_left nhdsWithin_le_nhds
  have ha_eps_lim_nr : ∀ k : ℕ, ∀ ε : ℝ, Tendsto (iteratedDeriv k (a_eps ε)) (𝓝[<] (-r)) (𝓝 0) := by
    intro k ε
    have hcont : ContinuousOn (iteratedDeriv k (a_eps ε)) {τ : ℝ | τ ≠ 0} :=
      (contDiffOn_iteratedDeriv_of_isOpen hopen (ha0_cd.mul (hge_cd ε).contDiffOn) k).continuousOn
    have hcont_nr : ContinuousAt (iteratedDeriv k (a_eps ε)) (-r) :=
      hcont.continuousAt (hopen.mem_nhds (neg_ne_zero.mpr hr0.ne'))
    have h0_nr : iteratedDeriv k (a_eps ε) (-r) = 0 := by
      have hlim_r : Tendsto (iteratedDeriv k (a_eps ε)) (𝓝[>] (-r)) (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT (show -r < 0 by linarith)] with τ hτ
        have hev : a_eps ε =ᶠ[𝓝 τ] (0 : ℝ → ℂ) :=
          Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hτ) fun s hs =>
            ha_eps_zero_mid ε s (by rw [abs_of_neg hs.2]; linarith [hs.1])
        rw [hev.iteratedDeriv_eq k, iteratedDeriv_const_zero]
      exact tendsto_nhds_unique (hcont_nr.tendsto.mono_left nhdsWithin_le_nhds) hlim_r
    rw [← h0_nr]; exact hcont_nr.tendsto.mono_left nhdsWithin_le_nhds
  -- Integrability of `iteratedDeriv k (a_eps ε) * E` on `Ioi r` and `Iio (-r)` for fixed `ε > 0`
  have hint_eps_pos : ∀ k : ℕ, ∀ ε : ℝ, 0 < ε →
      IntegrableOn (fun τ => iteratedDeriv k (a_eps ε) τ * E τ) (Ioi r) := by
    intro k ε hε
    obtain ⟨M, hM, hfar⟩ := ha_eps_far k ε hε
    have hcont_all : ContinuousOn (iteratedDeriv k (a_eps ε)) {τ : ℝ | τ ≠ 0} :=
      (contDiffOn_iteratedDeriv_of_isOpen hopen (ha0_cd.mul (hge_cd ε).contDiffOn) k).continuousOn
    have hcont : ContinuousOn (fun τ => iteratedDeriv k (a_eps ε) τ * E τ) (Ioi r) := by
      have h1 : ContinuousOn (iteratedDeriv k (a_eps ε)) (Ioi r) :=
        hcont_all.mono fun τ (hτ : r < τ) => (hr0.trans hτ).ne'
      have h2 : Continuous E := by unfold E; fun_prop
      exact h1.mul h2.continuousOn
    have h01 : IntegrableOn (fun τ => iteratedDeriv k (a_eps ε) τ * E τ) (Ioc r 1) := by
      have h1 : ContinuousOn (fun τ => iteratedDeriv k (a_eps ε) τ * E τ) (Icc r 1) := by
        have ha_c : ContinuousOn (iteratedDeriv k (a_eps ε)) (Icc r 1) :=
          hcont_all.mono fun τ (hτ : τ ∈ Icc r 1) => (lt_of_lt_of_le hr0 hτ.1).ne'
        have hE_c : Continuous E := by unfold E; fun_prop
        exact ha_c.mul hE_c.continuousOn
      exact h1.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have h1inf : IntegrableOn (fun τ => iteratedDeriv k (a_eps ε) τ * E τ) (Ioi 1) := by
      have hinv2 := (integrableOn_rpow_Ioi_lt_neg_one (r := 1) one_pos (s := -2) (by norm_num)).1.const_mul M
      refine hinv2.mono' ((hcont.mono (fun τ (hτ : τ ∈ Ioi 1) => lt_of_le_of_lt hr1 hτ)).aestronglyMeasurable measurableSet_Ioi)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_)
      have hτ1 : 1 ≤ τ := (mem_Ioi.mp hτ).le
      have hτ0 : 0 < τ := zero_lt_one.trans hτ
      rw [norm_mul, show E τ = Complex.exp (((c * u * τ : ℝ) : ℂ) * Complex.I) by simp only [E]; congr 1; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      have h := hfar τ (by rw [abs_of_pos hτ0]; exact hτ1)
      simpa [abs_of_pos hτ0] using h
    rw [← Ioc_union_Ioi_eq_Ioi hr1]
    exact h01.union h1inf
  have hint_eps_neg : ∀ k : ℕ, ∀ ε : ℝ, 0 < ε →
      IntegrableOn (fun τ => iteratedDeriv k (a_eps ε) τ * E τ) (Iio (-r)) := by
    intro k ε hε
    rw [integrableOn_Iio_neg_iff_Ioi]
    obtain ⟨M, hM, hfar⟩ := ha_eps_far k ε hε
    have hcont_all : ContinuousOn (iteratedDeriv k (a_eps ε)) {τ : ℝ | τ ≠ 0} :=
      (contDiffOn_iteratedDeriv_of_isOpen hopen (ha0_cd.mul (hge_cd ε).contDiffOn) k).continuousOn
    have hcont : ContinuousOn (fun τ => iteratedDeriv k (a_eps ε) (-τ) * E (-τ)) (Ioi r) := by
      have h1 : ContinuousOn (fun τ => iteratedDeriv k (a_eps ε) (-τ)) (Ioi r) :=
        hcont_all.comp continuous_neg.continuousOn fun τ (hτ : r < τ) => neg_ne_zero.mpr (hr0.trans hτ).ne'
      have h2 : Continuous (fun τ => E (-τ)) := by unfold E; fun_prop
      exact h1.mul h2.continuousOn
    have h01 : IntegrableOn (fun τ => iteratedDeriv k (a_eps ε) (-τ) * E (-τ)) (Ioc r 1) := by
      have ha_c : ContinuousOn (fun τ => iteratedDeriv k (a_eps ε) (-τ)) (Icc r 1) :=
        hcont_all.comp continuous_neg.continuousOn fun τ (hτ : τ ∈ Icc r 1) => neg_ne_zero.mpr (lt_of_lt_of_le hr0 hτ.1).ne'
      have hE_c : Continuous (fun τ => E (-τ)) := by unfold E; fun_prop
      exact (ha_c.mul hE_c.continuousOn).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have h1inf : IntegrableOn (fun τ => iteratedDeriv k (a_eps ε) (-τ) * E (-τ)) (Ioi 1) := by
      have hinv2 := (integrableOn_rpow_Ioi_lt_neg_one (r := 1) one_pos (s := -2) (by norm_num)).1.const_mul M
      refine hinv2.mono' ((hcont.mono (fun τ (hτ : τ ∈ Ioi 1) => lt_of_le_of_lt hr1 hτ)).aestronglyMeasurable measurableSet_Ioi)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_)
      have hτ1 : 1 ≤ τ := (mem_Ioi.mp hτ).le
      have hτ0 : 0 < τ := zero_lt_one.trans hτ
      rw [norm_mul, show E (-τ) = Complex.exp (((c * u * (-τ) : ℝ) : ℂ) * Complex.I) by simp only [E]; congr 1; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      have h := hfar (-τ) (by rw [abs_neg, abs_of_pos hτ0]; exact hτ1)
      simpa [abs_neg, abs_of_pos hτ0] using h
    rw [← Ioc_union_Ioi_eq_Ioi hr1]
    exact h01.union h1inf
  -- `n`-fold IBP for `Φ(τ) = u * τ` on `Ioi r` and `Iio (-r)` for fixed `ε > 0`
  have hibp_n : ∀ ε : ℝ, 0 < ε →
      ∫ τ : ℝ, a_eps ε τ * E τ =
        (-(Complex.I * ((c * u : ℝ) : ℂ))⁻¹) ^ n *
          ((∫ τ in Iio (-r), iteratedDeriv n (a_eps ε) τ * E τ) +
           (∫ τ in Ioi r, iteratedDeriv n (a_eps ε) τ * E τ)) := by
    intro ε hε
    have hΦ_deriv : ∀ τ : ℝ, deriv (fun s : ℝ => u * s) τ = u := fun τ => by
      simp
    have hstep_pos : ∀ k : ℕ,
        ∫ τ in Ioi r, iteratedDeriv k (a_eps ε) τ * E τ =
          -(Complex.I * ((c * u : ℝ) : ℂ))⁻¹ *
            ∫ τ in Ioi r, iteratedDeriv (k + 1) (a_eps ε) τ * E τ := by
      intro k
      have hcd_k : ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv k (a_eps ε)) {τ : ℝ | τ ≠ 0} :=
        contDiffOn_iteratedDeriv_of_isOpen hopen (ha0_cd.mul (hge_cd ε).contDiffOn) k
      have hD_eq : ∀ τ ∈ Ioi r,
          -deriv (fun s => iteratedDeriv k (a_eps ε) s / (Complex.I * (c : ℂ) * ((deriv (fun t => u * t) s : ℝ) : ℂ))) τ =
            -(Complex.I * ((c * u : ℝ) : ℂ))⁻¹ * iteratedDeriv (k + 1) (a_eps ε) τ := by
        intro τ _
        simp_rw [hΦ_deriv]
        have heq_f : (fun s => iteratedDeriv k (a_eps ε) s / (Complex.I * (c : ℂ) * (u : ℂ))) =
            fun s => (Complex.I * (c : ℂ) * (u : ℂ))⁻¹ * iteratedDeriv k (a_eps ε) s := by
          ext s; rw [div_eq_inv_mul]
        rw [heq_f, deriv_const_mul_field', ← iteratedDeriv_succ]
        push_cast; ring
      have h1 := ibp_osc_Ioi (r := r) (c := c) hc.ne' (g := iteratedDeriv k (a_eps ε)) (Φ := fun s => u * s)
        (fun τ hτ => (hcd_k.contDiffAt (hopen.mem_nhds (hr0.trans hτ).ne')).differentiableAt (by simp))
        (fun τ _ => differentiableAt_id.const_mul u)
        (fun τ _ => (differentiableAt_const u).congr_of_eventuallyEq (Filter.Eventually.of_forall hΦ_deriv))
        (fun τ _ => by rw [hΦ_deriv]; exact hu.ne')
        (by simpa [E, mul_assoc] using hint_eps_pos k ε hε)
        (by
          have hI : IntegrableOn (fun τ => -(Complex.I * ((c * u : ℝ) : ℂ))⁻¹ *
              (iteratedDeriv (k + 1) (a_eps ε) τ * E τ)) (Ioi r) :=
            (hint_eps_pos (k + 1) ε hε).const_mul (-(Complex.I * ((c * u : ℝ) : ℂ))⁻¹)
          refine hI.congr_fun (fun τ hτ => ?_) measurableSet_Ioi
          have hE : E τ = Complex.exp (Complex.I * ((c * (u * τ) : ℝ) : ℂ)) := by
            simp only [E]; congr 1; push_cast; ring
          dsimp only
          rw [hD_eq τ hτ, mul_assoc, hE])
        (by
          simp_rw [hΦ_deriv]
          simpa using (ha_eps_lim_r k ε).div_const (Complex.I * (c : ℂ) * (u : ℂ)))
        (by
          simp_rw [hΦ_deriv]
          obtain ⟨M, hM, hfar⟩ := ha_eps_far k ε hε
          rw [tendsto_zero_iff_norm_tendsto_zero]
          have hdom : Tendsto (fun τ : ℝ => (M / (c * u)) * τ ^ (-2 : ℝ)) atTop (𝓝 0) := by
            simpa using (tendsto_rpow_neg_atTop (show (0 : ℝ) < 2 by norm_num)).const_mul (M / (c * u))
          refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hdom
          filter_upwards [eventually_gt_atTop (1 : ℝ)] with τ hτ1
          have hτ0 : 0 < τ := zero_lt_one.trans hτ1
          rw [norm_div, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hc, abs_of_pos hu]
          have h := hfar τ (by rw [abs_of_pos hτ0]; exact hτ1.le)
          rw [abs_of_pos hτ0] at h
          calc ‖iteratedDeriv k (a_eps ε) τ‖ / (c * u) ≤ (M * τ ^ (-2 : ℝ)) / (c * u) :=
                div_le_div_of_nonneg_right h (by positivity)
            _ = M / (c * u) * τ ^ (-2 : ℝ) := by ring)
      have h1' : ∫ τ in Ioi r, iteratedDeriv k (a_eps ε) τ * E τ =
          ∫ τ in Ioi r, (-(Complex.I * ((c * u : ℝ) : ℂ))⁻¹ * iteratedDeriv (k + 1) (a_eps ε) τ) * E τ := by
        have hE_eq : ∀ τ, Complex.exp (Complex.I * ((c * (u * τ) : ℝ) : ℂ)) = E τ := fun τ => by
          simp only [E]; congr 1; push_cast; ring
        simp_rw [hE_eq] at h1
        exact h1.trans (setIntegral_congr_fun measurableSet_Ioi fun τ hτ => by rw [hD_eq τ hτ])
      rw [h1']
      simp_rw [mul_assoc]
      exact integral_const_mul _ _
    have hstep_neg : ∀ k : ℕ,
        ∫ τ in Iio (-r), iteratedDeriv k (a_eps ε) τ * E τ =
          -(Complex.I * ((c * u : ℝ) : ℂ))⁻¹ *
            ∫ τ in Iio (-r), iteratedDeriv (k + 1) (a_eps ε) τ * E τ := by
      intro k
      rw [integral_Iio_neg_eq_Ioi, integral_Iio_neg_eq_Ioi]
      have hcd_k : ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv k (a_eps ε)) {τ : ℝ | τ ≠ 0} :=
        contDiffOn_iteratedDeriv_of_isOpen hopen (ha0_cd.mul (hge_cd ε).contDiffOn) k
      have hΦn_deriv : ∀ τ : ℝ, deriv (fun s : ℝ => -(u * s)) τ = -u := fun τ => by
        simp
      have hD_eq : ∀ τ ∈ Ioi r,
          -deriv (fun s => iteratedDeriv k (a_eps ε) (-s) / (Complex.I * (c : ℂ) * ((deriv (fun t => -(u * t)) s : ℝ) : ℂ))) τ =
            -(Complex.I * ((c * u : ℝ) : ℂ))⁻¹ * iteratedDeriv (k + 1) (a_eps ε) (-τ) := by
        intro τ _
        simp_rw [hΦn_deriv]
        have heq_f : (fun s => iteratedDeriv k (a_eps ε) (-s) / (Complex.I * (c : ℂ) * ((-u : ℝ) : ℂ))) =
            fun s => (Complex.I * (c : ℂ) * ((-u : ℝ) : ℂ))⁻¹ * iteratedDeriv k (a_eps ε) (-s) := by
          ext s; rw [div_eq_inv_mul]
        rw [heq_f, deriv_const_mul_field']
        dsimp only
        rw [deriv_comp_neg (iteratedDeriv k (a_eps ε)) τ, ← iteratedDeriv_succ]
        push_cast; ring
      have hneg_map : Tendsto (fun τ : ℝ => -τ) (𝓝[>] r) (𝓝[<] (-r)) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨continuous_neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
          by filter_upwards [self_mem_nhdsWithin] with τ hτ; exact neg_lt_neg hτ⟩
      have h1 := ibp_osc_Ioi (r := r) (c := c) hc.ne' (g := fun s => iteratedDeriv k (a_eps ε) (-s))
        (Φ := fun s => -(u * s))
        (fun τ hτ => ((hcd_k.contDiffAt (hopen.mem_nhds (neg_ne_zero.mpr (hr0.trans hτ).ne'))).differentiableAt (by simp)).comp τ differentiableAt_id.neg)
        (fun τ _ => (differentiableAt_id.const_mul u).neg)
        (fun τ _ => (differentiableAt_const (-u)).congr_of_eventuallyEq (Filter.Eventually.of_forall hΦn_deriv))
        (fun τ _ => by rw [hΦn_deriv]; exact neg_ne_zero.mpr hu.ne')
        (by
          have := (integrableOn_Iio_neg_iff_Ioi r (fun τ => iteratedDeriv k (a_eps ε) τ * E τ)).mp (hint_eps_neg k ε hε)
          refine this.congr_fun (fun τ _ => by simp only [E]; congr 2; push_cast; ring) measurableSet_Ioi)
        (by
          have hI : IntegrableOn (fun τ => -(Complex.I * ((c * u : ℝ) : ℂ))⁻¹ *
              (iteratedDeriv (k + 1) (a_eps ε) (-τ) * E (-τ))) (Ioi r) :=
            ((integrableOn_Iio_neg_iff_Ioi r (fun τ => iteratedDeriv (k + 1) (a_eps ε) τ * E τ)).mp
              (hint_eps_neg (k + 1) ε hε)).const_mul (-(Complex.I * ((c * u : ℝ) : ℂ))⁻¹)
          refine hI.congr_fun (fun τ hτ => ?_) measurableSet_Ioi
          have hE : E (-τ) = Complex.exp (Complex.I * ((c * -(u * τ) : ℝ) : ℂ)) := by
            simp only [E]; congr 1; push_cast; ring
          dsimp only
          rw [hD_eq τ hτ, mul_assoc, hE])
        (by
          simp_rw [hΦn_deriv]
          simpa using ((ha_eps_lim_nr k ε).comp hneg_map).div_const (Complex.I * (c : ℂ) * ((-u : ℝ) : ℂ)))
        (by
          simp_rw [hΦn_deriv]
          obtain ⟨M, hM, hfar⟩ := ha_eps_far k ε hε
          rw [tendsto_zero_iff_norm_tendsto_zero]
          have hdom : Tendsto (fun τ : ℝ => (M / (c * u)) * τ ^ (-2 : ℝ)) atTop (𝓝 0) := by
            simpa using (tendsto_rpow_neg_atTop (show (0 : ℝ) < 2 by norm_num)).const_mul (M / (c * u))
          refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hdom
          filter_upwards [eventually_gt_atTop (1 : ℝ)] with τ hτ1
          have hτ0 : 0 < τ := zero_lt_one.trans hτ1
          rw [norm_div, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hc, abs_neg, abs_of_pos hu]
          have h := hfar (-τ) (by rw [abs_neg, abs_of_pos hτ0]; exact hτ1.le)
          rw [abs_neg, abs_of_pos hτ0] at h
          calc ‖iteratedDeriv k (a_eps ε) (-τ)‖ / (c * u) ≤ (M * τ ^ (-2 : ℝ)) / (c * u) :=
                div_le_div_of_nonneg_right h (by positivity)
            _ = M / (c * u) * τ ^ (-2 : ℝ) := by ring)
      have h1' : ∫ τ in Ioi r, iteratedDeriv k (a_eps ε) (-τ) * E (-τ) =
          ∫ τ in Ioi r, (-(Complex.I * ((c * u : ℝ) : ℂ))⁻¹ * iteratedDeriv (k + 1) (a_eps ε) (-τ)) * E (-τ) := by
        have hE_eq : ∀ τ, Complex.exp (Complex.I * ((c * -(u * τ) : ℝ) : ℂ)) = E (-τ) := fun τ => by
          simp only [E]; congr 1; push_cast; ring
        simp_rw [hE_eq] at h1
        exact h1.trans (setIntegral_congr_fun measurableSet_Ioi fun τ hτ => by rw [hD_eq τ hτ])
      rw [h1']
      simp_rw [mul_assoc]
      exact integral_const_mul _ _
    have hiter_pos : ∀ m : ℕ,
        ∫ τ in Ioi r, a_eps ε τ * E τ =
          (-(Complex.I * ((c * u : ℝ) : ℂ))⁻¹) ^ m * ∫ τ in Ioi r, iteratedDeriv m (a_eps ε) τ * E τ := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [ih, hstep_pos m, pow_succ]; ring
    have hiter_neg : ∀ m : ℕ,
        ∫ τ in Iio (-r), a_eps ε τ * E τ =
          (-(Complex.I * ((c * u : ℝ) : ℂ))⁻¹) ^ m * ∫ τ in Iio (-r), iteratedDeriv m (a_eps ε) τ * E τ := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [ih, hstep_neg m, pow_succ]; ring
    -- Split `∫_ℝ = ∫_{Iio (-r)} + ∫_{Ioi r}`
    have huniv : Iio (-r) ∪ Icc (-r) r ∪ Ioi r = univ := by
      ext τ; simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi, mem_univ, iff_true]
      by_cases h1 : τ < -r
      · exact Or.inl (Or.inl h1)
      · by_cases h2 : τ ≤ r
        · exact Or.inl (Or.inr ⟨not_lt.mp h1, h2⟩)
        · exact Or.inr (not_le.mp h2)
    have hmid0 : EqOn (fun τ => a_eps ε τ * E τ) 0 (Icc (-r) r) := fun τ hτ => by
      simp [ha_eps_zero_mid ε τ (abs_le.mpr hτ)]
    have hmid_int : IntegrableOn (fun τ => a_eps ε τ * E τ) (Icc (-r) r) :=
      (integrableOn_zero (μ := volume) (s := Icc (-r) r)).congr_fun (fun τ hτ => (hmid0 hτ).symm) measurableSet_Icc
    have hdisj1 : Disjoint (Iio (-r) ∪ Icc (-r) r) (Ioi r) := by
      rw [disjoint_left]; intro x hx1 hx2
      rcases hx1 with h1 | h2
      · linarith [mem_Iio.mp h1, mem_Ioi.mp hx2]
      · linarith [(mem_Icc.mp h2).2, mem_Ioi.mp hx2]
    have hdisj2 : Disjoint (Iio (-r)) (Icc (-r) r) := by
      rw [disjoint_left]; intro x hx1 hx2; linarith [mem_Iio.mp hx1, (mem_Icc.mp hx2).1]
    have h0_neg : IntegrableOn (fun τ => a_eps ε τ * E τ) (Iio (-r)) := by
      simpa using hint_eps_neg 0 ε hε
    have h0_pos : IntegrableOn (fun τ => a_eps ε τ * E τ) (Ioi r) := by
      simpa using hint_eps_pos 0 ε hε
    have hsplit : ∫ τ : ℝ, a_eps ε τ * E τ =
        (∫ τ in Iio (-r), a_eps ε τ * E τ) + (∫ τ in Ioi r, a_eps ε τ * E τ) := by
      rw [← setIntegral_univ, ← huniv,
        setIntegral_union hdisj1 measurableSet_Ioi (h0_neg.union hmid_int) h0_pos,
        setIntegral_union hdisj2 measurableSet_Icc h0_neg hmid_int]
      have h0 : ∫ τ in Icc (-r) r, a_eps ε τ * E τ = 0 := by
        rw [setIntegral_congr_fun measurableSet_Icc hmid0]; simp
      rw [h0, add_zero]
    rw [hsplit, hiter_neg n, hiter_pos n, mul_add]
  -- Pass to the limit `ε ↓ 0` by dominated convergence on `Ioi r` and `Iio (-r)`
  have hs_lt : (j : ℝ) - 1 / 2 - (n : ℝ) < -1 := by
    have : (j : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hjn
    linarith
  have hdom_int := integrableOn_rpow_Ioi_lt_neg_one hr0 hs_lt
  have hdom_pos : Tendsto (fun ε : ℝ => ∫ τ in Ioi r, iteratedDeriv n (a_eps ε) τ * E τ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ τ in Ioi r, iteratedDeriv n a0 τ * E τ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun τ : ℝ => C_tot_sym n * τ ^ ((j : ℝ) - 1 / 2 - (n : ℝ))) ?_ ?_ (hdom_int.1.const_mul _) ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hint_eps_pos n ε hε).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_
      have hτ0 : 0 < τ := hr0.trans hτ
      rw [norm_mul, show E τ = Complex.exp (((c * u * τ : ℝ) : ℂ) * Complex.I) by simp only [E]; congr 1; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      have h := ha_eps_bd n ε hε τ hτ0.ne'
      rwa [abs_of_pos hτ0] at h
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_
      exact (ha_eps_lim τ (hr0.trans hτ).ne').mul_const (E τ)
  have hdom_neg : Tendsto (fun ε : ℝ => ∫ τ in Iio (-r), iteratedDeriv n (a_eps ε) τ * E τ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ τ in Iio (-r), iteratedDeriv n a0 τ * E τ)) := by
    simp_rw [integral_Iio_neg_eq_Ioi]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun τ : ℝ => C_tot_sym n * τ ^ ((j : ℝ) - 1 / 2 - (n : ℝ))) ?_ ?_ (hdom_int.1.const_mul _) ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact ((integrableOn_Iio_neg_iff_Ioi r (fun τ => iteratedDeriv n (a_eps ε) τ * E τ)).mp
        (hint_eps_neg n ε hε)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_
      have hτ0 : 0 < τ := hr0.trans hτ
      rw [norm_mul, show E (-τ) = Complex.exp (((c * u * (-τ) : ℝ) : ℂ) * Complex.I) by simp only [E]; congr 1; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      have h := ha_eps_bd n ε hε (-τ) (neg_ne_zero.mpr hτ0.ne')
      rwa [abs_neg, abs_of_pos hτ0] at h
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_
      exact (ha_eps_lim (-τ) (neg_ne_zero.mpr (hr0.trans hτ).ne')).mul_const (E (-τ))
  let I : ℂ := (-(Complex.I * ((c * u : ℝ) : ℂ))⁻¹) ^ n *
    ((∫ τ in Iio (-r), iteratedDeriv n a0 τ * E τ) + (∫ τ in Ioi r, iteratedDeriv n a0 τ * E τ))
  refine ⟨I, ?_, ?_⟩
  · have hlim := (hdom_neg.add hdom_pos).const_mul ((-(Complex.I * ((c * u : ℝ) : ℂ))⁻¹) ^ n)
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← hibp_n ε hε]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only [a_eps, a0, f1, f2, f3, g_eps, E]
    rw [Complex.exp_sub, Complex.ofReal_exp, Complex.ofReal_neg, Complex.exp_neg, ← div_eq_mul_inv]
    ring
  · -- Norm bound on `I`
    have hlim_norm_pos : ‖∫ τ in Ioi r, iteratedDeriv n a0 τ * E τ‖ ≤
        C_tot_sym n * (r ^ ((j : ℝ) + 1 / 2 - (n : ℝ)) / ((n : ℝ) - (j : ℝ) - 1 / 2)) := by
      refine le_of_tendsto (hdom_pos.norm) ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      refine (norm_integral_le_integral_norm _).trans ?_
      have hle := setIntegral_mono_on (hint_eps_pos n ε hε).norm (hdom_int.1.const_mul (C_tot_sym n))
        measurableSet_Ioi fun τ hτ => by
          have hτ0 : 0 < τ := hr0.trans hτ
          rw [norm_mul, show E τ = Complex.exp (((c * u * τ : ℝ) : ℂ) * Complex.I) by simp only [E]; congr 1; ring,
            Complex.norm_exp_ofReal_mul_I, mul_one]
          have h := ha_eps_bd n ε hε τ hτ0.ne'
          rwa [abs_of_pos hτ0] at h
      rw [integral_const_mul, hdom_int.2] at hle
      have heq : -(r ^ ((j : ℝ) - 1 / 2 - (n : ℝ) + 1)) / ((j : ℝ) - 1 / 2 - (n : ℝ) + 1) =
          r ^ ((j : ℝ) + 1 / 2 - (n : ℝ)) / ((n : ℝ) - (j : ℝ) - 1 / 2) := by
        rw [neg_div, ← div_neg]
        congr 1
        · congr 1; ring
        · ring
      rwa [heq] at hle
    have hlim_norm_neg : ‖∫ τ in Iio (-r), iteratedDeriv n a0 τ * E τ‖ ≤
        C_tot_sym n * (r ^ ((j : ℝ) + 1 / 2 - (n : ℝ)) / ((n : ℝ) - (j : ℝ) - 1 / 2)) := by
      refine le_of_tendsto (hdom_neg.norm) ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [integral_Iio_neg_eq_Ioi]
      refine (norm_integral_le_integral_norm _).trans ?_
      have hint_n := ((integrableOn_Iio_neg_iff_Ioi r (fun τ => iteratedDeriv n (a_eps ε) τ * E τ)).mp
        (hint_eps_neg n ε hε)).norm
      have hle := setIntegral_mono_on hint_n (hdom_int.1.const_mul (C_tot_sym n))
        measurableSet_Ioi fun τ hτ => by
          have hτ0 : 0 < τ := hr0.trans hτ
          rw [norm_mul, show E (-τ) = Complex.exp (((c * u * (-τ) : ℝ) : ℂ) * Complex.I) by simp only [E]; congr 1; ring,
            Complex.norm_exp_ofReal_mul_I, mul_one]
          have h := ha_eps_bd n ε hε (-τ) (neg_ne_zero.mpr hτ0.ne')
          rwa [abs_neg, abs_of_pos hτ0] at h
      rw [integral_const_mul, hdom_int.2] at hle
      have heq : -(r ^ ((j : ℝ) - 1 / 2 - (n : ℝ) + 1)) / ((j : ℝ) - 1 / 2 - (n : ℝ) + 1) =
          r ^ ((j : ℝ) + 1 / 2 - (n : ℝ)) / ((n : ℝ) - (j : ℝ) - 1 / 2) := by
        rw [neg_div, ← div_neg]
        congr 1
        · congr 1; ring
        · ring
      rwa [heq] at hle
    have hpref_norm : ‖(-(Complex.I * ((c * u : ℝ) : ℂ))⁻¹) ^ n‖ = ((c * u) ^ n)⁻¹ := by
      rw [norm_pow, norm_neg, norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (mul_pos hc hu), inv_pow]
    simp only [I]
    rw [norm_mul, hpref_norm]
    calc ((c * u) ^ n)⁻¹ * ‖(∫ τ in Iio (-r), iteratedDeriv n a0 τ * E τ) +
            (∫ τ in Ioi r, iteratedDeriv n a0 τ * E τ)‖
        ≤ ((c * u) ^ n)⁻¹ * (2 * (C_tot_sym n * (r ^ ((j : ℝ) + 1 / 2 - (n : ℝ)) / ((n : ℝ) - (j : ℝ) - 1 / 2)))) := by
          have := (norm_add_le _ _).trans (add_le_add hlim_norm_neg hlim_norm_pos)
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 * C_tot_sym n / ((n : ℝ) - (j : ℝ) - 1 / 2) * ((c * u) ^ n)⁻¹ * r ^ ((j : ℝ) + 1 / 2 - (n : ℝ)) := by
          ring

/-- **Lemma FCT.5a (`fct:edge-ibp`)** (`constant_terms_five.tex`, lines 524–537):
Non-stationary integration by parts near the edge, bundling:
- Part (1): Removing an edge cutoff (`fct_edge_ibp_cutoff`), with Abel regularisation `e^{-ετ²}`,
  uniform in `c > 0`, `u > 0`, `λ ≥ 0`, `0 < r ≤ 1`.
- Part (2): Shoulder estimate (`fct_edge_ibp_shoulder`), uniform in `c > 0`, `u > 0`, `0 < r ≤ 1`,
  `A ≥ 0`, `a`, `Φ`. -/
theorem fct_edge_ibp {n : ℕ} (hn : 1 ≤ n) :
    -- (1) Removing an edge cutoff
    (∀ (j : ℕ), j < n →
      ∀ {ψ₀ : ℝ → ℝ}, ContDiff ℝ (⊤ : ℕ∞) ψ₀ →
        (∀ t : ℝ, |t| ≤ 1 → ψ₀ t = 1) →
        (∀ t : ℝ, 2 ≤ |t| → ψ₀ t = 0) →
        ∃ C ≥ 0, ∀ {c u r lam : ℝ}, 0 < c → 0 < u → 0 < r → r ≤ 1 → 0 ≤ lam →
          ∃ I : ℂ,
            Tendsto (fun ε : ℝ =>
              ∫ τ : ℝ, ((1 - ψ₀ (τ / r) : ℝ) : ℂ) * ((lam : ℂ) + (τ : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
                (τ : ℂ) ^ j * Complex.exp (Complex.I * ((c * u * τ : ℝ) : ℂ) - ((ε * τ ^ 2 : ℝ) : ℂ)))
              (𝓝[>] (0 : ℝ)) (𝓝 I) ∧
            ‖I‖ ≤ C * ((c * u) ^ n)⁻¹ * r ^ ((j : ℝ) + 1 / 2 - (n : ℝ))) ∧
    -- (2) Shoulder
    (∀ {κ : ℝ} {K : ℕ → ℝ}, 0 < κ → (∀ k, 0 ≤ K k) →
      ∃ C ≥ 0, ∀ {c u r A : ℝ} {a : ℝ → ℂ} {Φ : ℝ → ℝ},
        0 < c → 0 < u → 0 < r → r ≤ 1 → 0 ≤ A →
        ContDiff ℝ (n : ℕ) a →
        (∀ τ : ℝ, |τ| < r → a τ = 0) →
        (∀ k ≤ n, ∀ τ : ℝ, r < |τ| →
          ‖iteratedDeriv k a τ‖ ≤ A * edgeW τ ^ (-(k : ℤ)) * |τ| ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-2 : ℤ)) →
        ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Φ {τ : ℝ | r < |τ|} →
        (∀ τ : ℝ, r < |τ| → κ * u ≤ |deriv Φ τ|) →
        (∀ k, 1 ≤ k → k ≤ n → ∀ τ : ℝ, r < |τ| →
          |iteratedDeriv (k + 1) Φ τ| ≤ K k * edgeW τ ^ (-(k : ℤ)) * |deriv Φ τ|) →
        Integrable (fun τ : ℝ => a τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))) ∧
        ‖∫ τ : ℝ, a τ * Complex.exp (Complex.I * ((c * Φ τ : ℝ) : ℂ))‖ ≤
          C * A * ((c * u) ^ n)⁻¹ * r ^ (1 / 2 - (n : ℝ))) :=
  ⟨fun _ hjn {_} hcd h1 h0 => fct_edge_ibp_cutoff hn hjn hcd h1 h0,
   fun hκ hK => fct_edge_ibp_shoulder hn hκ hK⟩

/-- info: 'FormalResearch.SignUncertainty.FctEdgeIbp.fct_edge_ibp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.FctEdgeIbp.fct_edge_ibp

end FormalResearch.SignUncertainty.FctEdgeIbp
