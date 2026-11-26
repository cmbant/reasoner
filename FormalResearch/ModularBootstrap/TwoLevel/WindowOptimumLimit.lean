module

public import FormalResearch.ModularBootstrap.TwoLevel.WindowOptimum
public import FormalResearch.ModularBootstrap.TwoLevel.WindowOptimumClark

/-!
# The window optimum reaches the two-level curve (`virasoro_two_level.tex`, Proposition 2.3 `gt:2.3`, qualitative part)

With `z_k = clarkNode α k`, `a_k = airyZero k` and `w_n` the weights of `WindowOptimum`, the window weight factors as
`w_n = r(z_n) P_n²`, `r(x) = -(x - z₁)/((x - a₁)²(x - a₂)²(cot²α - x))`, `P_n = ∏_{k=3}^K (z_n - z_k)/(z_n - a_k)`
(`windowWeight_eq`).  The abstract tail bound `NodeHyp.term_bound` then gives
`z₂ - u₂*(K) ≤ C_α K^{-1/15}` for `K` large (`clarkNode_sub_windowOptimum_le`), so

* `u₂*(K) < z₂` and `u₂*(K) → z₂` as `K → ∞` (`windowOptimum_lt`, `tendsto_windowOptimum`),
* `inf_K c_* |u₂*(K)| = c_* |z₂|` for every `c_* ≥ 0` (`isGLB_window_amplitude`), the Clark-node form of
  `inf_K A₂^{win}(K) = A₂^*(A₁)`.

Not covered: the rate `K^{-1/3} log K`.
-/

@[expose] public section

open Filter Topology Finset

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty

/-- `r(x) = -(x - z₁)/((x - a₁)²(x - a₂)²(cot²α - x))`. -/
noncomputable def windowRate (α : ℝ) (x : ℝ) : ℝ :=
  -(x - clarkNode α 1) / ((x - airyZero 1) ^ 2 * (x - airyZero 2) ^ 2 * (cotC α ^ 2 - x))

/-- `P_n = ∏_{k=3}^K (z_n - z_k)/(z_n - a_k)`. -/
noncomputable def windowRatio (α : ℝ) (K n : ℕ) : ℝ :=
  ∏ k ∈ Icc 3 K, (clarkNode α n - clarkNode α k) / (clarkNode α n - airyZero k)

lemma windowDr_split (K : ℕ) (hK : 2 ≤ K) (x : ℝ) :
    windowDr K x = (x - airyZero 1) * (x - airyZero 2) * ∏ k ∈ Icc 3 K, (x - airyZero k) := by
  unfold windowDr
  have e1 : Icc 1 K = insert 1 (Icc 2 K) := (Finset.insert_Icc_add_one_left_eq_Icc (by omega : 1 ≤ K)).symm
  have e2 : Icc 2 K = insert 2 (Icc 3 K) := (Finset.insert_Icc_add_one_left_eq_Icc (by omega : 2 ≤ K)).symm
  rw [e1, Finset.prod_insert (by simp), e2, Finset.prod_insert (by simp)]
  ring

lemma windowWeight_eq (α : ℝ) {K : ℕ} (hK : 3 ≤ K) {n : ℕ} (hS : n = 2 ∨ K < n) :
    windowWeight α K n = windowRate α (clarkNode α n) * windowRatio α K n ^ 2 := by
  have hn : 1 ≤ n := by rcases hS with h | h <;> omega
  unfold windowWeight windowRate windowRatio
  rw [ite_eq_left hS, windowDr_split K (by omega)]
  have h1 : clarkNode α n - airyZero 1 ≠ 0 := sub_ne_zero.mpr (clarkNode_ne_airyZero α hn le_rfl)
  have h2 : clarkNode α n - airyZero 2 ≠ 0 := sub_ne_zero.mpr (clarkNode_ne_airyZero α hn (by norm_num))
  have h3 : ∏ k ∈ Icc 3 K, (clarkNode α n - airyZero k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k hk =>
      sub_ne_zero.mpr (clarkNode_ne_airyZero α hn (by have := (Finset.mem_Icc.mp hk).1; omega)))
  have h4 : cotC α ^ 2 - clarkNode α n ≠ 0 := (cot_sq_sub_pos α hn).ne'
  rw [Finset.prod_div_distrib, div_pow, Finset.prod_pow]
  field_simp

lemma windowRate_two_pos (α : ℝ) : 0 < windowRate α (clarkNode α 2) := by
  unfold windowRate
  have h1 : clarkNode α 2 - airyZero 1 ≠ 0 := sub_ne_zero.mpr (clarkNode_ne_airyZero α (by norm_num) le_rfl)
  have h2 : clarkNode α 2 - airyZero 2 ≠ 0 :=
    sub_ne_zero.mpr (clarkNode_ne_airyZero α (by norm_num) (by norm_num))
  have h3 := cot_sq_sub_pos α (n := 2) (by norm_num)
  have h4 := clarkNode_two_lt_one α
  apply div_pos (by linarith)
  positivity


lemma rate_ineq {x q1 q2 p1 p2 c b0 : ℝ} (hb0 : 0 < b0) (hp : p1 < p2) (hp2 : 0 < p2)
    (hq2 : q2 < p2) (hc : 0 ≤ c) (hx : b0 ≤ x - p2) :
    (x - q1) / ((x - p1) ^ 2 * (x - p2) ^ 2 * (c + x)) * (x - q2) ≤
      ((1 + |q1| / p2) * (1 + (p2 - q2) / b0)) * ((x - p2) ^ 3)⁻¹ := by
  set B := x - p2 with hB
  have hBpos : 0 < B := lt_of_lt_of_le hb0 hx
  have hxp : p2 ≤ x := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le hp2 hxp
  have hcx : 0 < c + x := by linarith
  have hB1 : B ≤ x - p1 := by rw [hB]; linarith
  have h1 : (x - q1) / (c + x) ≤ 1 + |q1| / p2 := by
    rw [div_le_iff₀ hcx]
    have : |q1| ≤ |q1| / p2 * x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hp2]
      exact mul_le_mul_of_nonneg_left hxp (abs_nonneg _)
    have : -q1 ≤ |q1| := neg_le_abs q1
    nlinarith [div_nonneg (abs_nonneg q1) hp2.le]
  have h2 : x - q2 ≤ B * (1 + (p2 - q2) / b0) := by
    have : p2 - q2 ≤ B * ((p2 - q2) / b0) := by
      rw [← mul_div_assoc, le_div_iff₀ hb0]
      nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hq2.le)]
    nlinarith
  have hden : B ^ 2 ≤ (x - p1) ^ 2 := pow_le_pow_left₀ hBpos.le hB1 2
  have e : (x - q1) / ((x - p1) ^ 2 * (x - p2) ^ 2 * (c + x)) * (x - q2) =
      ((x - q1) / (c + x)) * (x - q2) / ((x - p1) ^ 2 * B ^ 2) := by
    rw [← hB]; field_simp
  rw [e]
  have hC1 : 0 ≤ 1 + |q1| / p2 := by positivity
  have hnum : (x - q1) / (c + x) * (x - q2) ≤ (1 + |q1| / p2) * (B * (1 + (p2 - q2) / b0)) := by
    refine mul_le_mul h1 h2 ?_ hC1
    linarith
  have hpos : 0 < B ^ 2 * B ^ 2 := by positivity
  calc (x - q1) / (c + x) * (x - q2) / ((x - p1) ^ 2 * B ^ 2)
      ≤ (1 + |q1| / p2) * (B * (1 + (p2 - q2) / b0)) / (B ^ 2 * B ^ 2) := by
        apply div_le_div₀ (by positivity) hnum hpos
        exact mul_le_mul_of_nonneg_right hden (by positivity)
    _ = ((1 + |q1| / p2) * (1 + (p2 - q2) / b0)) * (B ^ 3)⁻¹ := by
        field_simp


lemma absTerm_eq (α : ℝ) (K n : ℕ) :
    absTerm (fun k => -airyZero k) (fun k => -clarkNode α k) K n =
      ((airyZero 2 - clarkNode α n) ^ 3)⁻¹ * windowRatio α K n ^ 2 * ((windowRatio α K 2)⁻¹) ^ 2 := by
  have hI : Ioc 2 K = Icc 3 K := by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  have e1 : ∀ k, (-clarkNode α n - -clarkNode α k) / (-clarkNode α n - -airyZero k) =
      (clarkNode α n - clarkNode α k) / (clarkNode α n - airyZero k) := by
    intro k
    rw [show -clarkNode α n - -clarkNode α k = -(clarkNode α n - clarkNode α k) by ring,
      show -clarkNode α n - -airyZero k = -(clarkNode α n - airyZero k) by ring, neg_div_neg_eq]
  have e2 : ∀ k, (-clarkNode α k - -clarkNode α 2) / (-airyZero k - -clarkNode α 2) =
      (clarkNode α 2 - clarkNode α k) / (clarkNode α 2 - airyZero k) := by
    intro k
    rw [show -clarkNode α k - -clarkNode α 2 = clarkNode α 2 - clarkNode α k by ring,
      show -airyZero k - -clarkNode α 2 = clarkNode α 2 - airyZero k by ring]
  unfold absTerm windowRatio
  beta_reduce
  rw [hI]
  simp only [e1, e2]
  rw [show -clarkNode α n - -airyZero 2 = airyZero 2 - clarkNode α n by ring]

/-- The constant `(1 + |z₁|/|a₂|)(1 + (z₂ - a₂)/(a₂ - a₃))` of the rate bound. -/
noncomputable def windowRateConst (α : ℝ) : ℝ :=
  (1 + |clarkNode α 1| / (-airyZero 2)) *
    (1 + (clarkNode α 2 - airyZero 2) / (airyZero 2 - airyZero 3))

lemma windowRatio_two_ne (α : ℝ) {K : ℕ} : windowRatio α K 2 ≠ 0 := by
  unfold windowRatio
  refine Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)
  have hk3 := (Finset.mem_Icc.mp hk).1
  have h1 : clarkNode α 2 - clarkNode α k ≠ 0 := by
    have := clarkNode_lt_of_lt (n := 2) (m := k) (by norm_num) (by omega) α
    linarith
  exact div_ne_zero h1 (sub_ne_zero.mpr (clarkNode_ne_airyZero α (by norm_num) (by omega)))

lemma windowTerm_div_le (α : ℝ) {k0 : ℕ} (h : NodeHyp (fun k => -airyZero k) (fun k => -clarkNode α k) k0)
    {K : ℕ} (hK : max k0 8 ≤ K) (i : ℕ) :
    windowWeight α K (K + 1 + i) * (clarkNode α 2 - clarkNode α (K + 1 + i)) / windowWeight α K 2 ≤
      windowRateConst α / windowRate α (clarkNode α 2) *
        (NodeHyp.absConst (fun k => -airyZero k) (fun k => -clarkNode α k) k0 * (K : ℝ) ^ (-(1 / 15) : ℝ) *
          ((i : ℝ) + 1) ^ (-(6 / 5) : ℝ)) := by
  have h3 := h.k0_ge
  have hK3 : 3 ≤ K := by have := le_max_right k0 8; omega
  set n := K + 1 + i with hn
  have hKn : K < n := by omega
  set r2 := windowRate α (clarkNode α 2) with hr2
  have hr2pos : 0 < r2 := windowRate_two_pos α
  have hV := windowRatio_two_ne α (K := K)
  have hwn := windowWeight_eq α hK3 (Or.inr hKn : n = 2 ∨ K < n)
  have hw2 := windowWeight_eq α hK3 (Or.inl rfl : (2 : ℕ) = 2 ∨ K < 2)
  have hp12 : -airyZero 1 < -airyZero 2 := h.mono 1 le_rfl
  have hp23 : -airyZero 2 < -airyZero 3 := h.mono 2 (by norm_num)
  have hp2 : 0 < -airyZero 2 := h.pos 2 (by norm_num)
  have hq2 : -clarkNode α 2 < -airyZero 2 := h.int_hi 2 le_rfl
  have hq3 : -airyZero 3 < -clarkNode α n := h.q_gt_p (k := 3) (n := n) (by norm_num) (by omega)
  have hrate := rate_ineq (x := -clarkNode α n) (q1 := -clarkNode α 1) (q2 := -clarkNode α 2)
    (p1 := -airyZero 1) (p2 := -airyZero 2) (c := cotC α ^ 2)
    (b0 := airyZero 2 - airyZero 3) (by linarith) hp12 hp2 hq2 (sq_nonneg _) (by linarith)
  have e : windowRate α (clarkNode α n) * (clarkNode α 2 - clarkNode α n) =
      (-clarkNode α n - -clarkNode α 1) /
          ((-clarkNode α n - -airyZero 1) ^ 2 * (-clarkNode α n - -airyZero 2) ^ 2 *
            (cotC α ^ 2 + -clarkNode α n)) * (-clarkNode α n - -clarkNode α 2) := by
    unfold windowRate; ring
  have e3 : -clarkNode α n - -airyZero 2 = airyZero 2 - clarkNode α n := by ring
  have habs : |-clarkNode α 1| = |clarkNode α 1| := abs_neg _
  rw [e3, habs] at hrate
  have hrate' : windowRate α (clarkNode α n) * (clarkNode α 2 - clarkNode α n) ≤
      windowRateConst α * ((airyZero 2 - clarkNode α n) ^ 3)⁻¹ := by
    rw [e, e3]
    refine hrate.trans (le_of_eq ?_)
    unfold windowRateConst
    rw [show -airyZero 2 - -clarkNode α 2 = clarkNode α 2 - airyZero 2 by ring]
  have hbpos : 0 < airyZero 2 - airyZero 3 := by linarith
  have hCnn : 0 ≤ windowRateConst α := by
    unfold windowRateConst
    have : 0 < clarkNode α 2 - airyZero 2 := by
      have := airyZero_lt_airyClarkNode (n := 2) (by norm_num) (Real.cos α / Real.sin α)
      simp only [clarkNode, airyClarkAngleNode]; linarith
    positivity
  have hfin := h.term_bound hK i
  rw [absTerm_eq] at hfin
  have hPn := sq_nonneg (windowRatio α K n)
  have hV2 : 0 < windowRatio α K 2 ^ 2 := by positivity
  calc windowWeight α K n * (clarkNode α 2 - clarkNode α n) / windowWeight α K 2
      = (windowRate α (clarkNode α n) * (clarkNode α 2 - clarkNode α n)) * windowRatio α K n ^ 2 /
          (r2 * windowRatio α K 2 ^ 2) := by rw [hwn, hw2]; ring
    _ ≤ (windowRateConst α * ((airyZero 2 - clarkNode α n) ^ 3)⁻¹) * windowRatio α K n ^ 2 /
          (r2 * windowRatio α K 2 ^ 2) := by
        gcongr
    _ = windowRateConst α / r2 * (((airyZero 2 - clarkNode α n) ^ 3)⁻¹ * windowRatio α K n ^ 2 *
          ((windowRatio α K 2)⁻¹) ^ 2) := by
        field_simp
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left hfin (div_nonneg hCnn hr2pos.le)


lemma windowTail_term_zero (α : ℝ) {K : ℕ} {i : ℕ} (hi : i < K) :
    windowWeight α K (i + 1) * (clarkNode α 2 - clarkNode α (i + 1)) = 0 := by
  by_cases h2 : i + 1 = 2
  · rw [h2]; simp
  · have hS : ¬(i + 1 = 2 ∨ K < i + 1) := by omega
    unfold windowWeight; rw [ite_eq_right hS]; simp

lemma summable_shift_rpow : Summable (fun i : ℕ => ((i : ℝ) + 1) ^ (-(6 / 5) : ℝ)) := by
  have := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by norm_num : (-(6 / 5) : ℝ) < -1))
  simpa using this

/-- The constant of the tail bound `z₂ - u₂*(K) ≤ C K^{-1/15}`. -/
noncomputable def windowTailConst (α : ℝ) (k0 : ℕ) : ℝ :=
  windowRateConst α / windowRate α (clarkNode α 2) *
    NodeHyp.absConst (fun k => -airyZero k) (fun k => -clarkNode α k) k0 *
      ∑' i : ℕ, ((i : ℝ) + 1) ^ (-(6 / 5) : ℝ)

lemma windowTail_div_le {α : ℝ} (hα : Real.sin α ≠ 0) {k0 : ℕ}
    (h : NodeHyp (fun k => -airyZero k) (fun k => -clarkNode α k) k0) {K : ℕ} (hK : max k0 8 ≤ K) :
    windowTail α K / windowWeight α K 2 ≤ windowTailConst α k0 * (K : ℝ) ^ (-(1 / 15) : ℝ) := by
  have hK3 : 3 ≤ K := by have := h.k0_ge; have := le_max_right k0 8; omega
  have hT := windowTail_hasSum hα hK3
  have h1 := (hasSum_nat_add_iff' K).2 hT
  rw [Finset.sum_eq_zero (fun i hi => windowTail_term_zero α (Finset.mem_range.mp hi)), sub_zero] at h1
  have h2 := h1.div_const (windowWeight α K 2)
  set X := windowRateConst α / windowRate α (clarkNode α 2) *
    NodeHyp.absConst (fun k => -airyZero k) (fun k => -clarkNode α k) k0 * (K : ℝ) ^ (-(1 / 15) : ℝ) with hX
  have h3 := (summable_shift_rpow.hasSum).mul_left X
  refine le_trans (hasSum_le (fun i => ?_) h2 h3) (le_of_eq ?_)
  · have e : i + K + 1 = K + 1 + i := by omega
    have := windowTerm_div_le α h hK i
    simp only [e]
    calc _ ≤ _ := this
      _ = _ := by rw [hX]; ring
  · unfold windowTailConst; rw [hX]; ring

theorem exists_clarkNode_sub_windowOptimum_le {α : ℝ} (hα : Real.sin α ≠ 0) :
    ∃ C : ℝ, ∃ k1 : ℕ, ∀ K : ℕ, k1 ≤ K →
      clarkNode α 2 - windowOptimum α K ≤ C * (K : ℝ) ^ (-(1 / 15) : ℝ) := by
  obtain ⟨k0, h⟩ := exists_clark_nodeHyp α
  refine ⟨windowTailConst α k0, max k0 8, fun K hK => ?_⟩
  have hK3 : 3 ≤ K := by have := h.k0_ge; have := le_max_right k0 8; omega
  exact (windowOptimum_sub_le hα hK3).trans (windowTail_div_le hα h hK)

/-- **`u₂*(K) → z₂`** as `K → ∞` (`gt:2.3`, qualitative part). -/
theorem tendsto_windowOptimum {α : ℝ} (hα : Real.sin α ≠ 0) :
    Tendsto (windowOptimum α) atTop (𝓝 (clarkNode α 2)) := by
  obtain ⟨C, k1, hC⟩ := exists_clarkNode_sub_windowOptimum_le hα
  have hr : Tendsto (fun K : ℕ => (K : ℝ) ^ (-(1 / 15) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 15)).comp tendsto_natCast_atTop_atTop
  have hlow : Tendsto (fun K : ℕ => clarkNode α 2 - C * (K : ℝ) ^ (-(1 / 15) : ℝ)) atTop
      (𝓝 (clarkNode α 2)) := by
    simpa using (tendsto_const_nhds (x := clarkNode α 2)).sub (hr.const_mul C)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop k1] with K hK
    linarith [hC K hK]
  · filter_upwards [eventually_ge_atTop 3] with K hK
    exact (windowOptimum_lt hα hK).le

lemma clarkNode_two_lt_zero (α : ℝ) : clarkNode α 2 < 0 := by
  have := airyClarkNode_lt_airyZero (n := 2) (by norm_num) (Real.cos α / Real.sin α)
  have h1 := airyZero_neg 1
  simp only [clarkNode, airyClarkAngleNode]
  simpa using this.trans h1

/-- `|z₂| < |u₂*(K)|` for `K ≥ 3`. -/
theorem abs_clarkNode_two_lt_abs_windowOptimum {α : ℝ} (hα : Real.sin α ≠ 0) {K : ℕ} (hK : 3 ≤ K) :
    |clarkNode α 2| < |windowOptimum α K| := by
  have h1 := windowOptimum_lt hα hK
  have h2 := clarkNode_two_lt_zero α
  rw [abs_of_neg h2, abs_of_neg (h1.trans h2)]
  linarith

/-- **The window optimum reaches the two-level curve** (`gt:2.3`, qualitative part): for every `c_* ≥ 0`, the
amplitudes `c_* |u₂*(K)|`, `K ≥ 3`, have greatest lower bound `c_* |z₂(α)|`; this is
`inf_K A₂^{win}(K) = A₂^*(A₁)` with `A₂^{win}(K) = c_* |u₂*(K)|` and `A₂^*` written in the Clark-node
normalisation `c_* |z₂(α)|`.  Together with `windowOptimum_lt` (`u₂*(K) < z₂`, strict for `c_* > 0` after
`abs_clarkNode_two_lt_abs_windowOptimum`) this is the qualitative content of `gt:2.3`; the rate
`K^{-1/3} log K` is not covered. -/
theorem isGLB_window_amplitude {α : ℝ} (hα : Real.sin α ≠ 0) {cStar : ℝ} (hc : 0 ≤ cStar) :
    IsGLB {x : ℝ | ∃ K : ℕ, 3 ≤ K ∧ x = cStar * |windowOptimum α K|} (cStar * |clarkNode α 2|) := by
  constructor
  · rintro x ⟨K, hK, rfl⟩
    exact mul_le_mul_of_nonneg_left (abs_clarkNode_two_lt_abs_windowOptimum hα hK).le hc
  · intro L hL
    have hlim : Tendsto (fun K : ℕ => cStar * |windowOptimum α K|) atTop
        (𝓝 (cStar * |clarkNode α 2|)) :=
      ((tendsto_windowOptimum hα).abs).const_mul cStar
    exact ge_of_tendsto hlim (eventually_atTop.2 ⟨3, fun K hK => hL ⟨K, hK, rfl⟩⟩)

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.tendsto_windowOptimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_windowOptimum

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.isGLB_window_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isGLB_window_amplitude

end FormalResearch.ModularBootstrap.TwoLevel
