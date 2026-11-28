module

public import FormalResearch.SignUncertainty.HankelBootArc
public import FormalResearch.SignUncertainty.HankelBootLineGen
public import FormalResearch.SignUncertainty.HankelQuantC1Multilevel
public import FormalResearch.SignUncertainty.CeTerminalDeflation
public import FormalResearch.SignUncertainty.HankelThresholds
public import FormalResearch.Special.AiryPolyQuad

/-!
# Multilevel `(P, Q)` Nodes, Weights, Quadrature/Arc Bound, and `Q = 0` Base Case (`R2c`)

Supports the all-level lower bound `HbMultilevelLower D` (`HankelBootMultilevel.lean`):

* `hbMultilevelLower_Q_eq_zero`: when `D.Q = 0`, `D.S = {D.tm}` with `D.tm = airyZero 1`, so
  `HbMultilevelLower D` reduces immediately to `hb_thresholds_lower`.
* `airyPQ_good_circle_real`: real-window good circles for `N = P Ai + Q Ai'` (`Q ≠ 0`).
* `hbZerosInDisc`, `hbZeroGapBelow`: finite zero sets of `N` in `‖z‖ ≤ R` and the positive gap
  below `D.tm` to any smaller zero of `N`.
* `hbWeight`, `hbTopWeights`, `hbWeightSumConst`: positive node weights `D(t)/N'(t)²`,
  sum of upper-site weights `W_top`, and the `O(R^{3/2})` total-weight-sum bound (`C_α(D)`).
* `hankelBootMultilevelNodes`, `hankelBootMultilevel_nodes_lb`,
  `hankelBootMultilevel_nodes_theta`, `hankelBootMultilevel_arc`: `(B2_HB)`, the `θ`-secant lower
  bound, and the `(P, Q)` quadrature-arc estimate (`(28/5)` scaling of `virasoroArcCov` and
  `hankelArcUncConst`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric Polynomial
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.ModularBootstrap.ConcreteBootstrap

/-! ### Case `D.Q = 0` reduction to `hb_thresholds_lower` -/

/-- When `D.Q = 0`, `D.S = {D.tm}` and `D.tm = airyZero 1`. -/
lemma shellHBData_tm_eq_a1_of_Q_eq_zero (D : ShellHBData) (hQ : D.Q = 0) :
    D.tm = airyZero 1 := by
  have hcard1 : D.S.card = 1 := by
    rcases D.m_eq with ⟨_, h1⟩ | ⟨hne, _⟩
    · exact h1
    · exact absurd hQ hne
  have hS_eq : D.S = {D.tm} := by
    rw [Finset.card_eq_one] at hcard1
    obtain ⟨a, ha⟩ := hcard1
    have htm_in : D.tm ∈ ({a} : Finset ℝ) := ha ▸ D.tm_mem
    rw [Finset.mem_singleton] at htm_in
    rw [ha, htm_in]
  obtain ⟨p₀, hp₀, _hP⟩ := airyPQHB_eq_C_of_Q_eq_zero (hQ ▸ D.hHB)
  have ha1_ge : airyZero 1 ≤ D.tm := by
    by_contra hlt
    push Not at hlt
    have ha1_notS : airyZero 1 ∉ D.S := by
      rw [hS_eq, Finset.mem_singleton]; exact ne_of_gt hlt
    have hNa1 : airyPQN D.P D.Q (airyZero 1 : ℂ) = 0 := by
      rw [airyPQN_ofReal, _hP, hQ]
      simp [airyAi_airyZero 1]
    have hlt' := D.S_top (airyZero 1) hNa1 ha1_notS D.tm D.tm_mem
    linarith
  exact le_antisymm D.tm_le_airyZero_one ha1_ge

/-- When `D.Q = 0`, `HbMultilevelLower D` follows immediately from `hb_thresholds_lower`. -/
theorem hbMultilevelLower_Q_eq_zero (D : ShellHBData) (hQ : D.Q = 0) : HbMultilevelLower D := by
  obtain ⟨C, c₀, hlow⟩ := hb_thresholds_lower
  intro R_off _
  refine ⟨C, c₀, fun c hc ε hε r _ T f hf => ?_⟩
  have hbtm : hbModel D c = c / π ^ 2 + airyOrderCoeff * c ^ (1 / 3 : ℝ) := by
    have htm : D.tm = airyZero 1 := shellHBData_tm_eq_a1_of_Q_eq_zero D hQ
    have hA : airyOrderCoeff = -airyZero 1 / hankelBeta1 := by
      unfold airyOrderCoeff; rw [abs_of_neg (airyZero_neg 1)]
    unfold hbModel
    rw [htm, hA]
    ring
  rw [hbtm]
  exact hlow c hc ε hε T f hf.toIsHankelFeasible

/-! ### Finite zero sets and node weights (`D.Q ≠ 0`) -/

/-- Finite set of zeros of `N = D.P Ai + D.Q Ai'` in `closedBall 0 R`. -/
noncomputable def hbZerosInDisc (D : ShellHBData) (R : ℝ) : Finset ℂ :=
  (airyPQ_zeros_finite D.hHB R).toFinset

lemma mem_hbZerosInDisc (D : ShellHBData) {R : ℝ} {z : ℂ} :
    z ∈ hbZerosInDisc D R ↔ airyPQN D.P D.Q z = 0 ∧ ‖z‖ ≤ R :=
  Set.Finite.mem_toFinset _

/-- There exists `η_cap > 0` separating `D.tm` from every strictly smaller real zero of `N`. -/
lemma hbZeroGapBelow_exists (D : ShellHBData) :
    ∃ η_cap : ℝ, 0 < η_cap ∧ ∀ x : ℝ, airyPQN D.P D.Q (x : ℂ) = 0 → x < D.tm → x + η_cap ≤ D.tm := by
  classical
  let R₀ : ℝ := |D.tm| + 1
  let Z : Finset ℂ := (hbZerosInDisc D R₀).filter (fun z => z.re < D.tm)
  by_cases hZ : Z.Nonempty
  · let M : ℝ := (Z.image Complex.re).max' (hZ.image Complex.re)
    have hM_lt : M < D.tm := by
      have hmem : M ∈ Z.image Complex.re := Finset.max'_mem _ _
      rw [Finset.mem_image] at hmem
      obtain ⟨z, hz, hzm⟩ := hmem
      rw [← hzm]
      exact (Finset.mem_filter.mp hz).2
    refine ⟨min (1 / 2) ((D.tm - M) / 2), lt_min (by norm_num) (half_pos (sub_pos.mpr hM_lt)), ?_⟩
    intro x hx hxtm
    by_cases hxR : ‖(x : ℂ)‖ ≤ R₀
    · have hzZ : (x : ℂ) ∈ Z :=
        Finset.mem_filter.mpr ⟨(mem_hbZerosInDisc D).mpr ⟨hx, hxR⟩, by simpa using hxtm⟩
      have hxM : x ≤ M := by
        have hmem : x ∈ Z.image Complex.re :=
          Finset.mem_image.mpr ⟨(x : ℂ), hzZ, Complex.ofReal_re x⟩
        exact Finset.le_max' _ _ hmem
      linarith [min_le_right (1 / 2 : ℝ) ((D.tm - M) / 2)]
    · rw [Complex.norm_real, Real.norm_eq_abs, not_le] at hxR
      have hx_neg : x < -R₀ := by
        rcases le_or_gt x 0 with hx0 | hx0
        · rw [abs_of_nonpos hx0] at hxR; linarith
        · rw [abs_of_pos hx0] at hxR
          have : D.tm ≤ |D.tm| := le_abs_self D.tm
          linarith
      have h_le : x + 1 / 2 ≤ D.tm := by
        have : -|D.tm| ≤ D.tm := neg_abs_le D.tm
        dsimp [R₀] at hx_neg; linarith
      linarith [min_le_left (1 / 2 : ℝ) ((D.tm - M) / 2)]
  · refine ⟨1 / 2, by norm_num, fun x hx hxtm => ?_⟩
    by_cases hxR : ‖(x : ℂ)‖ ≤ R₀
    · exfalso; apply hZ
      exact ⟨(x : ℂ), Finset.mem_filter.mpr ⟨(mem_hbZerosInDisc D).mpr ⟨hx, hxR⟩, by simpa using hxtm⟩⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, not_le] at hxR
      have hx_neg : x < -R₀ := by
        rcases le_or_gt x 0 with hx0 | hx0
        · rw [abs_of_nonpos hx0] at hxR; linarith
        · rw [abs_of_pos hx0] at hxR
          have : D.tm ≤ |D.tm| := le_abs_self D.tm
          linarith
      have : -|D.tm| ≤ D.tm := neg_abs_le D.tm
      dsimp [R₀] at hx_neg; linarith

/-- Uniform gap `> 0` below `D.tm` separating `D.tm` from all smaller real zeros of `N`. -/
noncomputable def hbZeroGapBelow (D : ShellHBData) : ℝ :=
  Classical.choose (hbZeroGapBelow_exists D)

lemma hbZeroGapBelow_pos (D : ShellHBData) : 0 < hbZeroGapBelow D :=
  (Classical.choose_spec (hbZeroGapBelow_exists D)).1

lemma hbZeroGapBelow_spec (D : ShellHBData) {x : ℝ} (hx : airyPQN D.P D.Q (x : ℂ) = 0)
    (hxtm : x < D.tm) : x + hbZeroGapBelow D ≤ D.tm :=
  (Classical.choose_spec (hbZeroGapBelow_exists D)).2 x hx hxtm

/-- The positive quadrature weight `D(z) / N'(z)²` at a real zero `z` of `N`. -/
noncomputable def hbWeight (D : ShellHBData) (z : ℂ) : ℝ :=
  (airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2).re

lemma hbWeight_eq_real (D : ShellHBData) {x : ℝ} (hx : airyPQN D.P D.Q (x : ℂ) = 0) :
    hbWeight D (x : ℂ) = airyPQDr D.P D.Q x / (airyPQN' D.P D.Q (x : ℂ)).re ^ 2 ∧
    0 < hbWeight D (x : ℂ) := by
  obtain ⟨hD, hN'⟩ := hb_zero_weight_pos_all D hx
  have hNim := airyPQN'_im_ofReal D.P D.Q x
  let nr : ℝ := (airyPQN' D.P D.Q (x : ℂ)).re
  have hN'_eq : airyPQN' D.P D.Q (x : ℂ) = (nr : ℂ) := Complex.ext rfl hNim
  have hDeq : airyPQD D.P D.Q (x : ℂ) = ((airyPQDr D.P D.Q x : ℝ) : ℂ) := airyPQD_ofReal D.P D.Q x
  have hw : hbWeight D (x : ℂ) = airyPQDr D.P D.Q x / nr ^ 2 := by
    unfold hbWeight
    rw [hDeq, hN'_eq, ← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]
  exact ⟨hw, hw ▸ div_pos hD (sq_pos_of_ne_zero hN')⟩

lemma hbWeight_nonneg_of_zero (D : ShellHBData) {z : ℂ} (hz : airyPQN D.P D.Q z = 0) :
    0 ≤ hbWeight D z := by
  have hzr := airyPQ_zero_eq_ofReal D.hHB hz
  rw [hzr]
  exact (hbWeight_eq_real D (hzr ▸ hz)).2.le

lemma hbWeight_real_of_zero (D : ShellHBData) {z : ℂ} (hz : airyPQN D.P D.Q z = 0) :
    airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2 = ((hbWeight D z : ℝ) : ℂ) := by
  have hzr := airyPQ_zero_eq_ofReal D.hHB hz
  rw [hzr] at hz ⊢
  obtain ⟨hw, _⟩ := hbWeight_eq_real D hz
  have hNim := airyPQN'_im_ofReal D.P D.Q z.re
  let nr : ℝ := (airyPQN' D.P D.Q (z.re : ℂ)).re
  have hN'_eq : airyPQN' D.P D.Q (z.re : ℂ) = (nr : ℂ) := Complex.ext rfl hNim
  have hDeq : airyPQD D.P D.Q (z.re : ℂ) = ((airyPQDr D.P D.Q z.re : ℝ) : ℂ) := airyPQD_ofReal _ _ _
  have hw' : hbWeight D (z.re : ℂ) = airyPQDr D.P D.Q z.re / nr ^ 2 := hw
  rw [hw', hDeq, hN'_eq, ← Complex.ofReal_pow, ← Complex.ofReal_div]

/-- Sum of node weights over the upper prescribed sites `t ∈ D.S.erase D.tm`. -/
noncomputable def hbTopWeights (D : ShellHBData) : ℝ :=
  ∑ t ∈ D.S.erase D.tm, hbWeight D (t : ℂ)

lemma hbTopWeights_nonneg (D : ShellHBData) : 0 ≤ hbTopWeights D :=
  Finset.sum_nonneg fun _t ht =>
    (hbWeight_eq_real D (D.S_zero (Finset.mem_erase.mp ht).2)).2.le

/-- `O(R^{3/2})` bound on `∑_{|z|≤R, N(z)=0} ‖D(z)/N'(z)²‖` for `D` with `D.Q ≠ 0`. -/
lemma hbWeightSumConst_exists (D : ShellHBData) (hQ : D.Q ≠ 0) :
    ∃ C_α : ℝ, 0 < C_α ∧ ∀ R : ℝ, 1 ≤ R →
      ∑ z ∈ hbZerosInDisc D R, ‖airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2‖ ≤
        C_α * R ^ (3 / 2 : ℝ) := by
  classical
  obtain ⟨T₀, _, hT₀⟩ := airyPQ_weight_norm_le D.hHB hQ
  obtain ⟨T₁, _, hT₁⟩ := airyPQ_far_ex hQ
  obtain ⟨T_s, hTs_ge1, hTs⟩ := airyPQ_no_zero_sector D.P D.Q (Or.inr hQ)
  let T_cut : ℝ := max (max T₀ T₁) T_s
  have hT_ge1 : 1 ≤ T_cut := hTs_ge1.trans (le_max_right _ _)
  let C_near : ℝ := ∑ z ∈ hbZerosInDisc D T_cut, ‖airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2‖
  have hC_near_nn : 0 ≤ C_near := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let C_α : ℝ := C_near + 2646 * π ^ 2 + 1
  refine ⟨C_α, by positivity, fun R hR => ?_⟩
  let S_near := (hbZerosInDisc D R).filter (fun z => -T_cut ≤ z.re)
  let S_far := (hbZerosInDisc D R).filter (fun z => z.re < -T_cut)
  have hsplit : ∑ z ∈ hbZerosInDisc D R, ‖airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2‖ =
      (∑ z ∈ S_near, ‖airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2‖) +
      ∑ z ∈ S_far, ‖airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2‖ :=
    (Finset.sum_filter_add_sum_filter_not (hbZerosInDisc D R) (fun z => -T_cut ≤ z.re)
      (fun z => ‖airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2‖)).symm.trans (by
      congr 2; ext z; simp only [Finset.mem_filter, not_le, S_far])
  have hS_near_sub : S_near ⊆ hbZerosInDisc D T_cut := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hz0, _⟩ := (mem_hbZerosInDisc D).mp hz.1
    have hzr := airyPQ_zero_eq_ofReal D.hHB hz0
    have hz_ub : z.re ≤ T_cut := by
      by_contra hgt
      push Not at hgt
      have hpos : 0 < z.re := by linarith
      have hnorm : T_s ≤ ‖z‖ := by
        rw [hzr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
        exact (le_max_right _ _).trans hgt.le
      have hsec : -(‖z‖ / 2) ≤ z.re := by linarith [norm_nonneg z]
      exact hTs z hnorm hsec hz0
    refine (mem_hbZerosInDisc D).mpr ⟨hz0, ?_⟩
    rw [hzr, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨hz.2, hz_ub⟩
  have hnear_le : ∑ z ∈ S_near, ‖airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2‖ ≤ C_near :=
    Finset.sum_le_sum_of_subset_of_nonneg hS_near_sub (fun _ _ _ => norm_nonneg _)
  have hfar_term : ∀ z ∈ S_far, ‖airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2‖ ≤ 882 * π ^ 2 := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hz0, _⟩ := (mem_hbZerosInDisc D).mp hz.1
    have hzr := airyPQ_zero_eq_ofReal D.hHB hz0
    have hT0_le : z.re ≤ -T₀ := by linarith [(le_max_left T₀ T₁).trans (le_max_left _ T_s)]
    have hle := hT₀ z.re hT0_le (hzr ▸ hz0)
    have hsq1 : 1 ≤ √(-z.re) := Real.one_le_sqrt.mpr (by linarith)
    have hinv1 : 1 / √(-z.re) ≤ 1 := div_le_one_of_le₀ hsq1 (by positivity)
    rw [hzr]
    exact hle.trans (mul_le_of_le_one_right (by positivity) hinv1)
  have hfar_inj : Set.InjOn (fun z : ℂ => airyNIdx z.re) (S_far : Set ℂ) := by
    intro z₁ hz₁ z₂ hz₂ hidx
    rw [Finset.mem_coe, Finset.mem_filter] at hz₁ hz₂
    obtain ⟨h10, _⟩ := (mem_hbZerosInDisc D).mp hz₁.1
    obtain ⟨h20, _⟩ := (mem_hbZerosInDisc D).mp hz₂.1
    have hr1 := airyPQ_zero_eq_ofReal D.hHB h10
    have hr2 := airyPQ_zero_eq_ofReal D.hHB h20
    have hT1 : ∀ t : ℝ, t ≤ -T_cut → D.Q.eval t ≠ 0 := fun t ht =>
      hT₁ t (ht.trans (neg_le_neg ((le_max_right T₀ T₁).trans (le_max_left _ T_s))))
    have heq := airyPQ_injOn_far D.hHB hT1 hz₁.2.le hz₂.2.le (hr1 ▸ h10) (hr2 ▸ h20) hidx
    rw [hr1, hr2, heq]
  let N_ub : ℕ := ⌈R ^ (3 / 2 : ℝ)⌉₊ + 1
  have hfar_img : ∀ z ∈ S_far, airyNIdx z.re ∈ Finset.range N_ub := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hz0, hzR⟩ := (mem_hbZerosInDisc D).mp hz.1
    have hzr := airyPQ_zero_eq_ofReal D.hHB hz0
    have hQne : D.Q.eval z.re ≠ 0 :=
      hT₁ z.re (by linarith [(le_max_right T₀ T₁).trans (le_max_left _ T_s)])
    have hAi_ne := airyPQ_airyAi_ne hQne (hzr ▸ hz0)
    have hz1 : z.re ≤ -1 := by linarith
    have hgr := airyPQ_root_growth hAi_ne hz1
    have hR_ge_z : -z.re ≤ R := by
      have habs : |z.re| ≤ R := by
        calc |z.re| = ‖(z.re : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
          _ = ‖z‖ := by rw [← hzr]
          _ ≤ R := hzR
      linarith [(abs_le.mp habs).1]
    have hsqrt_le : √(-z.re) ≤ √R := Real.sqrt_le_sqrt hR_ge_z
    have hpow6 : (√(-z.re)) ^ 6 ≤ (√R) ^ 6 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_le 6
    have hR6 : (√R) ^ 6 = (R ^ (3 / 2 : ℝ)) ^ 2 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul (by linarith), ← Real.rpow_mul (by linarith)]
      norm_num
    rw [hR6] at hpow6
    have hsq_le : ((airyNIdx z.re : ℝ) + 1) ^ 2 ≤ (R ^ (3 / 2 : ℝ)) ^ 2 := hgr.trans hpow6
    have hidx_le : (airyNIdx z.re : ℝ) + 1 ≤ R ^ (3 / 2 : ℝ) :=
      (abs_le_of_sq_le_sq' hsq_le (by positivity)).2
    have hidx_lt : (airyNIdx z.re : ℝ) < (⌈R ^ (3 / 2 : ℝ)⌉₊ : ℝ) + 1 := by
      linarith [Nat.le_ceil (R ^ (3 / 2 : ℝ))]
    rw [Finset.mem_range]
    exact_mod_cast hidx_lt
  have hcard : (S_far.card : ℝ) ≤ 3 * R ^ (3 / 2 : ℝ) := by
    have hc1 : S_far.card ≤ N_ub := by
      calc S_far.card ≤ (Finset.range N_ub).card :=
            Finset.card_le_card_of_injOn (fun z : ℂ => airyNIdx z.re)
              (fun z hz => hfar_img z (Finset.mem_coe.mp hz)) hfar_inj
        _ = N_ub := Finset.card_range N_ub
    have hc2 : (S_far.card : ℝ) ≤ R ^ (3 / 2 : ℝ) + 2 := by
      have hceil : (⌈R ^ (3 / 2 : ℝ)⌉₊ : ℝ) < R ^ (3 / 2 : ℝ) + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      have hc1' : (S_far.card : ℝ) ≤ (⌈R ^ (3 / 2 : ℝ)⌉₊ : ℝ) + 1 := by exact_mod_cast hc1
      linarith
    have h1R : (1 : ℝ) ≤ R ^ (3 / 2 : ℝ) := Real.one_le_rpow hR (by norm_num)
    linarith
  have hfar_le : ∑ z ∈ S_far, ‖airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2‖ ≤
      2646 * π ^ 2 * R ^ (3 / 2 : ℝ) := by
    calc ∑ z ∈ S_far, ‖airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2‖
        ≤ ∑ _z ∈ S_far, (882 * π ^ 2 : ℝ) := Finset.sum_le_sum hfar_term
      _ = (S_far.card : ℝ) * (882 * π ^ 2) := by simp
      _ ≤ (3 * R ^ (3 / 2 : ℝ)) * (882 * π ^ 2) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2646 * π ^ 2 * R ^ (3 / 2 : ℝ) := by ring
  have h1R : (1 : ℝ) ≤ R ^ (3 / 2 : ℝ) := Real.one_le_rpow hR (by norm_num)
  calc ∑ z ∈ hbZerosInDisc D R, ‖airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2‖
      ≤ C_near + 2646 * π ^ 2 * R ^ (3 / 2 : ℝ) := by linarith
    _ ≤ C_near * R ^ (3 / 2 : ℝ) + 2646 * π ^ 2 * R ^ (3 / 2 : ℝ) + R ^ (3 / 2 : ℝ) := by
        nlinarith [hC_near_nn]
    _ = C_α * R ^ (3 / 2 : ℝ) := by dsimp [C_α]; ring

/-- Uniform constant `C_α(D) > 0` for `hbWeightSumConst_exists` (junk value `1` if `D.Q = 0`). -/
noncomputable def hbWeightSumConst (D : ShellHBData) : ℝ :=
  if hQ : D.Q ≠ 0 then Classical.choose (hbWeightSumConst_exists D hQ) else 1

lemma hbWeightSumConst_pos (D : ShellHBData) : 0 < hbWeightSumConst D := by
  unfold hbWeightSumConst
  split_ifs with hQ
  · exact (Classical.choose_spec (hbWeightSumConst_exists D hQ)).1
  · exact one_pos

lemma hbWeightSumConst_spec (D : ShellHBData) (hQ : D.Q ≠ 0) {R : ℝ} (hR : 1 ≤ R) :
    ∑ z ∈ hbZerosInDisc D R, ‖airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2‖ ≤
      hbWeightSumConst D * R ^ (3 / 2 : ℝ) := by
  unfold hbWeightSumConst
  split_ifs
  exact (Classical.choose_spec (hbWeightSumConst_exists D hQ)).2 R hR

/-! ### Multilevel node sum, `(B2_HB)`, and `θ`-secant bound -/

/-- The finite node sum `∑_{|z|≤R, N(z)=0} Re (f_{k,ℓ}(z) D(z) / N'(z)²)` for `(D.P, D.Q)`. -/
noncomputable def hankelBootMultilevelNodes (D : ShellHBData) (c : ℝ) (f : ℝ → ℝ)
    (R ℓ : ℝ) (k : ℕ) : ℝ :=
  ∑ z ∈ hbZerosInDisc D R,
    (hankelBootShifted c f R ℓ k z * (airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2)).re

lemma hb_node_term_eq (D : ShellHBData) {c R ℓ : ℝ} (f : ℝ → ℝ) (k : ℕ) {z : ℂ}
    (hz : airyPQN D.P D.Q z = 0) :
    (hankelBootShifted c f R ℓ k z * (airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2)).re =
      (1 + z.re / R) ^ (k + 1) * hankelPsiR c f (z.re + ℓ) * hbWeight D z := by
  have hzr := airyPQ_zero_eq_ofReal D.hHB hz
  have hwt := hbWeight_real_of_zero D hz
  conv_lhs => rw [hzr]
  rw [hzr] at hwt
  rw [hwt, mul_comm, Complex.re_ofReal_mul, mul_comm, hankelBoot_shifted_re, ← hzr]

lemma hb_node_pow_upper {M_S R x : ℝ} (hM : 0 ≤ M_S) (hR5 : max M_S 5 ≤ R)
    (hxR : -R ≤ x) (hxM : x ≤ M_S) {k : ℕ} (hkR : (k : ℝ) ≤ R / 5) :
    0 ≤ (1 + x / R) ^ (k + 1) ∧ (1 + x / R) ^ (k + 1) ≤ Real.exp (M_S + 1) := by
  have hR_pos : 0 < R := by linarith [le_max_right M_S 5]
  have hdiv : -1 ≤ x / R := by rw [le_div_iff₀ hR_pos]; linarith
  have hb0 : 0 ≤ 1 + x / R := by linarith
  refine ⟨pow_nonneg hb0 _, ?_⟩
  rcases le_or_gt x 0 with hx0 | hx0
  · have h1 : 1 + x / R ≤ 1 := by
      have : x / R ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx0 hR_pos.le
      linarith
    exact (pow_le_one₀ hb0 h1).trans (Real.one_le_exp (by linarith))
  · have h_exp : 1 + x / R ≤ Real.exp (x / R) := by linarith [Real.add_one_le_exp (x / R)]
    have hpow : (1 + x / R) ^ (k + 1) ≤ Real.exp (((k : ℝ) + 1) * (x / R)) := by
      calc (1 + x / R) ^ (k + 1) ≤ (Real.exp (x / R)) ^ (k + 1) := pow_le_pow_left₀ hb0 h_exp _
        _ = Real.exp (((k : ℝ) + 1) * (x / R)) := by rw [← Real.exp_nat_mul]; push_cast; ring
    have hMR : M_S / R ≤ 1 := div_le_one_of_le₀ ((le_max_left M_S 5).trans hR5) hR_pos.le
    have h_arg : ((k : ℝ) + 1) * (x / R) ≤ M_S + 1 := by
      calc ((k : ℝ) + 1) * (x / R) ≤ (R / 5 + 1) * (M_S / R) :=
            mul_le_mul (by linarith) (div_le_div_of_nonneg_right hxM hR_pos.le)
              (div_nonneg hx0.le hR_pos.le) (by linarith)
        _ = M_S / 5 + M_S / R := by field_simp
        _ ≤ M_S + 1 := by linarith
    exact hpow.trans (Real.exp_le_exp.mpr h_arg)

lemma hb_one_add_mul_le_pow (n : ℕ) {a : ℝ} (ha : -1 ≤ a) :
    1 + (n : ℝ) * a ≤ (1 + a) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1a : 0 ≤ 1 + a := by linarith
    have hk : 0 ≤ (k : ℝ) * a ^ 2 := mul_nonneg (Nat.cast_nonneg k) (sq_nonneg a)
    calc 1 + ((k + 1 : ℕ) : ℝ) * a ≤ 1 + (k : ℝ) * a + a + (k : ℝ) * a ^ 2 := by
          push_cast; linarith
      _ = (1 + (k : ℝ) * a) * (1 + a) := by ring
      _ ≤ (1 + a) ^ k * (1 + a) := mul_le_mul_of_nonneg_right ih h1a
      _ = (1 + a) ^ (k + 1) := (pow_succ _ _).symm

lemma hb_node_pow_ge_half {R x : ℝ} (k : ℕ) (hR : 2 * ((k : ℝ) + 1) * (-x) ≤ R) (hx : x < 0) :
    (1 / 2 : ℝ) ≤ (1 + x / R) ^ (k + 1) := by
  have hneg : 0 < -x := neg_pos.mpr hx
  have h2k : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by positivity
  have hR_pos : 0 < R := lt_of_lt_of_le (mul_pos h2k hneg) hR
  have h_div_neg : -(1 / 2 : ℝ) ≤ ((k : ℝ) + 1) * (x / R) := by
    rw [neg_le]
    calc -(((k : ℝ) + 1) * (x / R)) = ((k : ℝ) + 1) * (-x) / R := by ring
      _ ≤ 1 / 2 := (div_le_iff₀ hR_pos).mpr (by linarith)
  have ha : -1 ≤ x / R := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
    have hdiv_np : x / R ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx.le hR_pos.le
    nlinarith
  have hber := hb_one_add_mul_le_pow (k + 1) ha
  push_cast at hber
  linarith

/-- Mean-value bound on real intervals inside the Langer disc. -/
lemma hb_psiR_mv_sub {c ε : ℝ} {f : ℝ → ℝ} (hc0 : 0 < c) (hf : IsHankelEigenfn c ε f)
    {a b C1 : ℝ} (hab : a ≤ b) (ha : -langerRadius c ≤ a) (hb : b ≤ langerRadius c)
    (hder : ∀ x ∈ Icc a b, ‖deriv (hankelPsi c f) (x : ℂ)‖ ≤ C1) :
    |(hankelPsi c f (b : ℂ)).re - (hankelPsi c f (a : ℂ)).re| ≤ C1 * (b - a) :=
  hankelBoot_psi_mv_sub (analyticOnNhd_hankelPsi hc0 hf) hab ha hb C1 hder

private lemma hb_zeros_re_abs_le (D : ShellHBData) {R : ℝ} {z : ℂ}
    (hz0 : airyPQN D.P D.Q z = 0) (hzR : ‖z‖ ≤ R) : |z.re| ≤ R := by
  have hzr := airyPQ_zero_eq_ofReal D.hHB hz0
  calc |z.re| = ‖(z.re : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖z‖ := by rw [← hzr]
    _ ≤ R := hzR

private lemma hb_node_upper_site_re_lb (D : ShellHBData) {c ε R D_1 ℓ s u_s : ℝ}
    {f : ℝ → ℝ} (hc0 : 0 < c) (hfe : IsHankelEigenfn c ε f) (hD1 : D_1 * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 4)
    (hℓ0 : 0 ≤ ℓ) (hℓ_lb : D_1 * c ^ (-(1 / 3 : ℝ)) ≤ ℓ) (hℓ_half : ℓ ≤ 1 / 2)
    (hR_S : D.S.sup' D.S_nonempty (fun x => |x|) + 1 ≤ R) (hRA : R + 1 ≤ langerRadius c)
    (hsS : s ∈ D.S)
    (hu_diff : |u_s - s| ≤ D_1 * c ^ (-(1 / 3 : ℝ)))
    (hu_A : |u_s| ≤ langerRadius c)
    (hu_sign : -hankelRinf c ≤ hankelPsiR c f u_s)
    {C1_q : ℝ} (hder : ∀ x ∈ Icc (s - 1 / 2) (s + 1 / 2), ‖deriv (hankelPsi c f) (x : ℂ)‖ ≤ C1_q) :
    -(hankelRinf c + 2 * C1_q * ℓ) ≤ hankelPsiR c f (s + ℓ) := by
  have hC1_nn : 0 ≤ C1_q := (norm_nonneg _).trans (hder s ⟨by linarith, by linarith⟩)
  have hs_M : |s| ≤ D.S.sup' D.S_nonempty (fun x => |x|) := Finset.le_sup' (fun x => |x|) hsS
  let a' : ℝ := min u_s (s + ℓ)
  let b' : ℝ := max u_s (s + ℓ)
  have hsℓ_A : |s + ℓ| ≤ langerRadius c := by
    rw [abs_le]
    have hs_abs := abs_le.mp hs_M
    exact ⟨by linarith only [hs_abs.1, hℓ0, hR_S, hRA], by linarith only [hs_abs.2, hℓ_half, hR_S, hRA]⟩
  have h_lo : -langerRadius c ≤ a' := le_min (abs_le.mp hu_A).1 (abs_le.mp hsℓ_A).1
  have h_hi : b' ≤ langerRadius c := max_le (abs_le.mp hu_A).2 (abs_le.mp hsℓ_A).2
  have h_in_half : ∀ x ∈ Icc a' b', x ∈ Icc (s - 1 / 2) (s + 1 / 2) := fun x hx => by
    have hda : |u_s - s| ≤ 1 / 2 := hu_diff.trans (by linarith only [hD1])
    have ha1 : s - 1 / 2 ≤ a' := le_min (by linarith only [(abs_le.mp hda).1]) (by linarith only [hℓ0])
    have hb1 : b' ≤ s + 1 / 2 := max_le (by linarith only [(abs_le.mp hda).2]) (by linarith only [hℓ_half])
    exact ⟨ha1.trans hx.1, hx.2.trans hb1⟩
  have hmv := hb_psiR_mv_sub hc0 hfe (le_trans (min_le_left _ _) (le_max_left _ _)) h_lo h_hi
    (fun x hx => hder x (h_in_half x hx))
  have hgap : |s + ℓ - u_s| ≤ 2 * ℓ := by
    have h1 : |s + ℓ - u_s| ≤ ℓ + D_1 * c ^ (-(1 / 3 : ℝ)) := by
      calc |s + ℓ - u_s| = |ℓ + (s - u_s)| := by ring_nf
        _ ≤ |ℓ| + |s - u_s| := abs_add_le _ _
        _ = ℓ + |u_s - s| := by rw [abs_of_nonneg hℓ0, abs_sub_comm]
        _ ≤ ℓ + D_1 * c ^ (-(1 / 3 : ℝ)) := by linarith only [hu_diff]
    linarith only [h1, hℓ_lb]
  have hlen : b' - a' ≤ 2 * ℓ := by
    have hmax_min : b' - a' = |s + ℓ - u_s| := by
      dsimp [a', b']; rw [max_sub_min_eq_abs, abs_sub_comm]
    linarith only [hmax_min, hgap]
  have hdiff_mv : |(hankelPsi c f ((s + ℓ : ℝ) : ℂ)).re - (hankelPsi c f (u_s : ℂ)).re| ≤
      2 * C1_q * ℓ := by
    have hmul : C1_q * (b' - a') ≤ 2 * C1_q * ℓ := by
      have := mul_le_mul_of_nonneg_left hlen hC1_nn
      linarith only [this]
    rcases le_total u_s (s + ℓ) with h | h
    · dsimp [a', b'] at hmul
      rw [min_eq_left h, max_eq_right h] at hmv hmul
      exact hmv.trans hmul
    · dsimp [a', b'] at hmul
      rw [min_eq_right h, max_eq_left h] at hmv hmul
      rw [abs_sub_comm] at hmv
      exact hmv.trans hmul
  have hlo := (abs_le.mp hdiff_mv).1
  change -hankelRinf c ≤ (hankelPsi c f (u_s : ℂ)).re at hu_sign
  show -(hankelRinf c + 2 * C1_q * ℓ) ≤ (hankelPsi c f ((s + ℓ : ℝ) : ℂ)).re
  linarith only [hlo, hu_sign]

/-- Lower bound for `hankelBootMultilevelNodes` (`(B2_HB)` for general `D : ShellHBData` with `D.Q ≠ 0`). -/
theorem hankelBootMultilevel_nodes_lb (D : ShellHBData) (hQ : D.Q ≠ 0) {c ε T u_T R D_1 : ℝ}
    {f : ℝ → ℝ} {u_site : ℝ → ℝ}
    (hD1 : 0 ≤ D_1) (hc : 3e6 ≤ c) (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1)
    (hM : hankelMass c f = 1) (hT : c * hankelXi c u_T = T)
    (htm_uT : D.tm < u_T)
    (hB2 : QuantC1MultilevelB2Holds D (shellHBQuantData D).1.1 (shellHBQuantData D).1.2.1
      (shellHBQuantData D).1.2.2 (hbZeroGapBelow D) (hankelPsi c f) u_T)
    (huA : |u_T| ≤ langerRadius c)
    (hR_S : max (D.S.sup' D.S_nonempty (fun s => |s|) + 1) 10 ≤ R)
    (hRA : R + 1 ≤ langerRadius c)
    (hsites : ∀ t ∈ D.S.erase D.tm, |u_site t - t| ≤ D_1 * c ^ (-(1 / 3 : ℝ)) ∧
      |u_site t| ≤ langerRadius c ∧ -hankelRinf c ≤ hankelPsiR c f (u_site t))
    {ℓ : ℝ} (hℓ_lb : D_1 * c ^ (-(1 / 3 : ℝ)) ≤ ℓ)
    (hℓ_ub : ℓ ≤ min (shellHBQuantData D).1.1 (min (hbZeroGapBelow D) 1))
    {k : ℕ} (hkR : (k : ℝ) ≤ R / 5)
    (hD1_small : D_1 * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 4) :
    let M_S := D.S.sup' D.S_nonempty (fun s => |s|)
    let C1_q := (shellHBQuantData D).1.2.2
    let M_pow := Real.exp (M_S + 1);
    -(2 * (M_pow * C1_q) * (hbWeight D (D.tm : ℂ) + hbTopWeights D)) * ℓ -
        M_pow * hbWeightSumConst D * R ^ (3 / 2 : ℝ) * hankelRinf c ≤
      hankelBootMultilevelNodes D c f R ℓ k := by
  intro M_S C1_q M_pow
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hfe hε hM
  have hC1_pos : 0 < C1_q := (shellHBQuantData D).2.2.2.2.1
  have hδ_le_q : (shellHBQuantData D).1.1 ≤ 1 / 4 := (shellHBQuantData D).2.2.1
  have hM_S_nn : 0 ≤ M_S := le_trans (abs_nonneg D.tm) (Finset.le_sup' (fun s => |s|) D.tm_mem)
  have hMpow_ge1 : 1 ≤ M_pow := Real.one_le_exp (by linarith)
  have hR10 : 10 ≤ R := (le_max_right _ _).trans hR_S
  have hR_pos : 0 < R := by linarith
  have hR_ge1 : 1 ≤ R := by linarith
  have hR5 : max M_S 5 ≤ R :=
    (max_le_max (by linarith : M_S ≤ M_S + 1) (by norm_num : (5 : ℝ) ≤ 10)).trans hR_S
  have hℓ0 : 0 ≤ ℓ := (mul_nonneg hD1 (Real.rpow_nonneg hc0.le _)).trans hℓ_lb
  have hℓ_delta : ℓ ≤ (shellHBQuantData D).1.1 := hℓ_ub.trans (min_le_left _ _)
  have hℓ_gap : ℓ ≤ hbZeroGapBelow D := hℓ_ub.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hℓ_q : ℓ ≤ 1 / 4 := hℓ_delta.trans hδ_le_q
  have hS_sub : D.S.image (fun t : ℝ => (t : ℂ)) ⊆ hbZerosInDisc D R := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨t, htS, rfl⟩ := hz
    refine (mem_hbZerosInDisc D).mpr ⟨D.S_zero htS, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 : |t| ≤ M_S := Finset.le_sup' (fun s => |s|) htS
    linarith [(le_max_left _ (10 : ℝ)).trans hR_S]
  have hterm_lb : ∀ z ∈ hbZerosInDisc D R,
      -(if z.re ∈ D.S then 2 * (M_pow * C1_q) * hbWeight D z * ℓ else 0) -
        M_pow * hbWeight D z * hankelRinf c ≤
      (hankelBootShifted c f R ℓ k z * (airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2)).re := by
    intro z hz
    obtain ⟨hz0, hzR⟩ := (mem_hbZerosInDisc D).mp hz
    have hzr := airyPQ_zero_eq_ofReal D.hHB hz0
    have hzw : 0 ≤ hbWeight D z := hbWeight_nonneg_of_zero D hz0
    have hz_abs : |z.re| ≤ R := hb_zeros_re_abs_le D hz0 hzR
    have hz_M : z.re ≤ M_S := by
      by_cases hzS : z.re ∈ D.S
      · exact (abs_le.mp (Finset.le_sup' (fun s => |s|) hzS)).2
      · have hlt := D.S_top z.re (hzr ▸ hz0) hzS D.tm D.tm_mem
        linarith only [hlt, le_abs_self D.tm, Finset.le_sup' (fun s => |s|) D.tm_mem]
    have hpow_bd := hb_node_pow_upper hM_S_nn hR5 (abs_le.mp hz_abs).1 hz_M hkR
    rw [hb_node_term_eq D f k hz0]
    by_cases hzS : z.re ∈ D.S
    · simp only [hzS, reduceIte]
      have hre_psi : -(hankelRinf c + 2 * C1_q * ℓ) ≤ hankelPsiR c f (z.re + ℓ) := by
        by_cases hztm : z.re = D.tm
        · rw [hztm]
          have htm_M : |D.tm| ≤ M_S := Finset.le_sup' (fun s => |s|) D.tm_mem
          have htm_A : |D.tm| ≤ langerRadius c := by linarith only [htm_M, (le_max_left _ (10 : ℝ)).trans hR_S, hRA]
          have htmℓ_A : D.tm + ℓ ≤ langerRadius c := by
            linarith only [(abs_le.mp htm_M).2, (le_max_left _ (10 : ℝ)).trans hR_S, hRA, hℓ_q]
          have hsign : -hankelRinf c ≤ hankelPsiR c f D.tm :=
            hankelBoot_psi_ge_gen hc hf hε hM hT huA (by linarith only [hRA]) (abs_le.mp htm_A).1 htm_uT.le
          have hder : ∀ x ∈ Icc D.tm (D.tm + ℓ), ‖deriv (hankelPsi c f) (x : ℂ)‖ ≤ C1_q := fun x hx =>
            hB2.deriv_norm_le D.tm D.tm_mem x ⟨by linarith only [hx.1, hℓ0], by linarith only [hx.2, hℓ_q]⟩
          have hmv := hb_psiR_mv_sub hc0 hfe (by linarith only [hℓ0] : D.tm ≤ D.tm + ℓ)
            (abs_le.mp htm_A).1 htmℓ_A hder
          have hlo := (abs_le.mp hmv).1
          change -hankelRinf c ≤ (hankelPsi c f (D.tm : ℂ)).re at hsign
          show _ ≤ (hankelPsi c f ((D.tm + ℓ : ℝ) : ℂ)).re
          have hnn : 0 ≤ C1_q * ℓ := mul_nonneg hC1_pos.le hℓ0
          linarith only [hlo, hsign, hnn]
        · have hz_erase : z.re ∈ D.S.erase D.tm := Finset.mem_erase.mpr ⟨hztm, hzS⟩
          obtain ⟨hu_diff, hu_A, hu_sign⟩ := hsites z.re hz_erase
          exact hb_node_upper_site_re_lb D hc0 hfe hD1_small hℓ0 hℓ_lb (by linarith only [hℓ_q])
            ((le_max_left _ (10 : ℝ)).trans hR_S) hRA hzS hu_diff hu_A hu_sign
            (fun x hx => hB2.deriv_norm_le z.re hzS x hx)
      have h_mul1' : -(M_pow * (hankelRinf c + 2 * C1_q * ℓ)) ≤
          (1 + z.re / R) ^ (k + 1) * hankelPsiR c f (z.re + ℓ) := by
        have hpos_b : 0 ≤ hankelRinf c + 2 * C1_q * ℓ := by positivity
        have h1 : -(M_pow * (hankelRinf c + 2 * C1_q * ℓ)) ≤
            -((1 + z.re / R) ^ (k + 1) * (hankelRinf c + 2 * C1_q * ℓ)) := by
          have := mul_le_mul_of_nonneg_right hpow_bd.2 hpos_b
          linarith only [this]
        have h2 : -((1 + z.re / R) ^ (k + 1) * (hankelRinf c + 2 * C1_q * ℓ)) ≤
            (1 + z.re / R) ^ (k + 1) * hankelPsiR c f (z.re + ℓ) := by
          rw [← mul_neg]; exact mul_le_mul_of_nonneg_left hre_psi hpow_bd.1
        linarith only [h1, h2]
      have h_fin := mul_le_mul_of_nonneg_right h_mul1' hzw
      linarith only [h_fin]
    · simp only [hzS, reduceIte, neg_zero, zero_sub]
      have hz_lt : z.re < D.tm := D.S_top z.re (hzr ▸ hz0) hzS D.tm D.tm_mem
      have hgap := hbZeroGapBelow_spec D (hzr ▸ hz0) hz_lt
      have hzℓ_le : z.re + ℓ ≤ u_T := by linarith only [hgap, hℓ_gap, htm_uT]
      have hzℓ_A : |z.re + ℓ| ≤ langerRadius c := by
        have hℓ1 : ℓ ≤ 1 := hℓ_ub.trans ((min_le_right _ _).trans (min_le_right _ _))
        rw [abs_le]
        exact ⟨by linarith only [(abs_le.mp hz_abs).1, hℓ0, hRA], by linarith only [(abs_le.mp hz_abs).2, hℓ1, hRA]⟩
      have hsign : -hankelRinf c ≤ hankelPsiR c f (z.re + ℓ) :=
        hankelBoot_psi_ge_gen hc hf hε hM hT huA (by linarith only [hRA]) (abs_le.mp hzℓ_A).1 hzℓ_le
      have h1 : -(M_pow * hankelRinf c) ≤ (1 + z.re / R) ^ (k + 1) * hankelPsiR c f (z.re + ℓ) := by
        have ha1 : -(M_pow * hankelRinf c) ≤ -((1 + z.re / R) ^ (k + 1) * hankelRinf c) := by
          have := mul_le_mul_of_nonneg_right hpow_bd.2 hr
          linarith only [this]
        have ha2 : -((1 + z.re / R) ^ (k + 1) * hankelRinf c) ≤
            (1 + z.re / R) ^ (k + 1) * hankelPsiR c f (z.re + ℓ) := by
          rw [← mul_neg]; exact mul_le_mul_of_nonneg_left hsign hpow_bd.1
        linarith only [ha1, ha2]
      have h_fin := mul_le_mul_of_nonneg_right h1 hzw
      linarith only [h_fin]
  have hsum_lb := Finset.sum_le_sum hterm_lb
  rw [Finset.sum_sub_distrib] at hsum_lb
  have h_ell_sum : ∑ z ∈ hbZerosInDisc D R,
      (if z.re ∈ D.S then 2 * (M_pow * C1_q) * hbWeight D z * ℓ else 0) =
      2 * (M_pow * C1_q) * (hbWeight D (D.tm : ℂ) + hbTopWeights D) * ℓ := by
    have hinj : ∀ a ∈ D.S, ∀ b ∈ D.S, (a : ℂ) = (b : ℂ) → a = b := fun _ _ _ _ h => Complex.ofReal_injective h
    have hsub : ∀ z ∈ hbZerosInDisc D R,
        (if z.re ∈ D.S then 2 * (M_pow * C1_q) * hbWeight D z * ℓ else 0) =
        (if z ∈ D.S.image (fun t : ℝ => (t : ℂ)) then 2 * (M_pow * C1_q) * hbWeight D z * ℓ else 0) := by
      intro z hz
      obtain ⟨hz0, _⟩ := (mem_hbZerosInDisc D).mp hz
      have hzr := airyPQ_zero_eq_ofReal D.hHB hz0
      have hiff : z.re ∈ D.S ↔ z ∈ D.S.image (fun t : ℝ => (t : ℂ)) := by
        constructor
        · intro ht; rw [Finset.mem_image]; exact ⟨z.re, ht, hzr.symm⟩
        · intro ht; rw [Finset.mem_image] at ht; obtain ⟨t, htS, htz⟩ := ht
          have heq : t = z.re := by simpa using congrArg Complex.re htz
          rwa [← heq]
      simp [hiff]
    rw [Finset.sum_congr rfl hsub, ← Finset.sum_filter]
    have hfilt : (hbZerosInDisc D R).filter (fun z => z ∈ D.S.image (fun t : ℝ => (t : ℂ))) =
        D.S.image (fun t : ℝ => (t : ℂ)) := by
      ext z; simp only [Finset.mem_filter, and_iff_right_iff_imp]
      intro hz; exact hS_sub hz
    rw [hfilt, Finset.sum_image hinj]
    have hsum_w : ∑ t ∈ D.S, hbWeight D (t : ℂ) = hbWeight D (D.tm : ℂ) + hbTopWeights D := by
      unfold hbTopWeights
      exact (Finset.add_sum_erase D.S (fun t => hbWeight D (t : ℂ)) D.tm_mem).symm
    calc ∑ t ∈ D.S, 2 * (M_pow * C1_q) * hbWeight D (t : ℂ) * ℓ
        = 2 * (M_pow * C1_q) * (∑ t ∈ D.S, hbWeight D (t : ℂ)) * ℓ := by
          rw [Finset.mul_sum, Finset.sum_mul]
      _ = _ := by rw [hsum_w]
  have h_rinf_sum : ∑ z ∈ hbZerosInDisc D R, M_pow * hbWeight D z * hankelRinf c ≤
      M_pow * hbWeightSumConst D * R ^ (3 / 2 : ℝ) * hankelRinf c := by
    have hweq : ∀ z ∈ hbZerosInDisc D R, hbWeight D z =
        ‖airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2‖ := fun z hz => by
      obtain ⟨hz0, _⟩ := (mem_hbZerosInDisc D).mp hz
      rw [hbWeight_real_of_zero D hz0, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hbWeight_nonneg_of_zero D hz0)]
    calc ∑ z ∈ hbZerosInDisc D R, M_pow * hbWeight D z * hankelRinf c
        = M_pow * hankelRinf c * ∑ z ∈ hbZerosInDisc D R, hbWeight D z := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
      _ = M_pow * hankelRinf c * ∑ z ∈ hbZerosInDisc D R, ‖airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2‖ := by
          rw [Finset.sum_congr rfl hweq]
      _ ≤ M_pow * hankelRinf c * (hbWeightSumConst D * R ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hbWeightSumConst_spec D hQ hR_ge1) (mul_nonneg (by linarith) hr)
      _ = M_pow * hbWeightSumConst D * R ^ (3 / 2 : ℝ) * hankelRinf c := by ring
  unfold hankelBootMultilevelNodes
  rw [Finset.sum_neg_distrib, h_ell_sum] at hsum_lb
  linarith only [hsum_lb, h_rinf_sum]

/-- Theta-secant bound (`P_theta_bound` precursor) at fixed `k_0` for `D : ShellHBData` with `D.Q ≠ 0`. -/
theorem hankelBootMultilevel_nodes_theta (D : ShellHBData) (hQ : D.Q ≠ 0) {c ε T u_T R D_1 θ : ℝ}
    {f : ℝ → ℝ} {u_site : ℝ → ℝ}
    (hD1 : 0 ≤ D_1) (hc : 3e6 ≤ c) (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1)
    (hM : hankelMass c f = 1) (hT : c * hankelXi c u_T = T)
    (htm_uT : D.tm < u_T)
    (hB2 : QuantC1MultilevelB2Holds D (shellHBQuantData D).1.1 (shellHBQuantData D).1.2.1
      (shellHBQuantData D).1.2.2 (hbZeroGapBelow D) (hankelPsi c f) u_T)
    (huA : |u_T| ≤ langerRadius c)
    (hR_S : max (D.S.sup' D.S_nonempty (fun s => |s|) + 1) 10 ≤ R)
    (hRA : R + 1 ≤ langerRadius c)
    (hsites : ∀ t ∈ D.S.erase D.tm, |u_site t - t| ≤ D_1 * c ^ (-(1 / 3 : ℝ)) ∧
      |u_site t| ≤ langerRadius c ∧ -hankelRinf c ≤ hankelPsiR c f (u_site t))
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2)
    (hℓ_lb : D_1 * c ^ (-(1 / 3 : ℝ)) ≤ θ * (u_T - D.tm))
    (hℓ_ub : θ * (u_T - D.tm) ≤ min (shellHBQuantData D).1.1 (min (hbZeroGapBelow D) 1))
    {k₀ : ℕ} (hk0R : (k₀ : ℝ) ≤ R / 5)
    (hR_tm : 2 * ((k₀ : ℝ) + 1) * (-D.tm) ≤ R)
    (hD1_small : D_1 * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 4) :
    let M_S := D.S.sup' D.S_nonempty (fun s => |s|)
    let C1_q := (shellHBQuantData D).1.2.2
    let κ_q := (shellHBQuantData D).1.2.1
    let M_pow := Real.exp (M_S + 1);
    (κ_q * hbWeight D (D.tm : ℂ) / 2 - 2 * (M_pow * C1_q) * hbTopWeights D * θ) * (u_T - D.tm) -
        M_pow * hbWeightSumConst D * R ^ (3 / 2 : ℝ) * hankelRinf c ≤
      hankelBootMultilevelNodes D c f R (θ * (u_T - D.tm)) k₀ := by
  intro M_S C1_q κ_q M_pow
  set ℓ := θ * (u_T - D.tm)
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hfe hε hM
  have hδ_le_q : (shellHBQuantData D).1.1 ≤ 1 / 4 := (shellHBQuantData D).2.2.1
  have hκ_pos : 0 < κ_q := (shellHBQuantData D).2.2.2.1
  have hC1_pos : 0 < C1_q := (shellHBQuantData D).2.2.2.2.1
  have hM_S_nn : 0 ≤ M_S := le_trans (abs_nonneg D.tm) (Finset.le_sup' (fun s => |s|) D.tm_mem)
  have hMpow_ge1 : 1 ≤ M_pow := Real.one_le_exp (by linarith)
  have hR10 : 10 ≤ R := (le_max_right _ _).trans hR_S
  have hR_pos : 0 < R := by linarith
  have hR_ge1 : 1 ≤ R := by linarith
  have hR5 : max M_S 5 ≤ R :=
    (max_le_max (by linarith : M_S ≤ M_S + 1) (by norm_num : (5 : ℝ) ≤ 10)).trans hR_S
  have hℓ0 : 0 ≤ ℓ := (mul_nonneg hD1 (Real.rpow_nonneg hc0.le _)).trans hℓ_lb
  have hℓ_delta : ℓ ≤ (shellHBQuantData D).1.1 := hℓ_ub.trans (min_le_left _ _)
  have hℓ_gap : ℓ ≤ hbZeroGapBelow D := hℓ_ub.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hS_sub : D.S.image (fun t : ℝ => (t : ℂ)) ⊆ hbZerosInDisc D R := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨t, htS, rfl⟩ := hz
    refine (mem_hbZerosInDisc D).mpr ⟨D.S_zero htS, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 : |t| ≤ M_S := Finset.le_sup' (fun s => |s|) htS
    linarith [(le_max_left _ (10 : ℝ)).trans hR_S]
  have hAn : AnalyticOnNhd ℂ (hankelPsi c f) (closedBall (0 : ℂ) (langerRadius c)) :=
    analyticOnNhd_hankelPsi hc0 hfe
  have htm_neg : D.tm < 0 := lt_of_le_of_lt D.tm_le_airyZero_one (airyZero_neg 1)
  have htm_term_lb :
      (κ_q * hbWeight D (D.tm : ℂ) / 2) * (u_T - D.tm) - M_pow * hbWeight D (D.tm : ℂ) * hankelRinf c ≤
      (hankelBootShifted c f R ℓ k₀ (D.tm : ℂ) *
        (airyPQD D.P D.Q (D.tm : ℂ) / airyPQN' D.P D.Q (D.tm : ℂ) ^ 2)).re := by
    have hwt_pos : 0 < hbWeight D (D.tm : ℂ) := (hbWeight_eq_real D (D.S_zero D.tm_mem)).2
    have htmℓ_le_uT : D.tm + ℓ ≤ u_T := by
      have : ℓ ≤ u_T - D.tm := by nlinarith [hθ1, htm_uT]
      linarith
    have huT_sub_δ : u_T - D.tm ≤ (shellHBQuantData D).1.1 := hB2.uT_sub_le.trans (min_le_left _ _)
    have htm_A : |D.tm| ≤ langerRadius c := by
      have : |D.tm| ≤ M_S := Finset.le_sup' (fun s => |s|) D.tm_mem
      linarith [(le_max_left _ (10 : ℝ)).trans hR_S]
    have hftc : (hankelPsi c f (u_T : ℂ)).re - (hankelPsi c f ((D.tm + ℓ : ℝ) : ℂ)).re =
        ∫ x in (D.tm + ℓ)..u_T, (deriv (hankelPsi c f) (x : ℂ)).re := by
      have hda : ∀ x ∈ uIcc (D.tm + ℓ) u_T,
          HasDerivAt (fun t : ℝ => (hankelPsi c f (t : ℂ)).re)
            (deriv (hankelPsi c f) (x : ℂ)).re x := fun x hx => by
        have hx' : x ∈ Icc (D.tm + ℓ) u_T := (Set.uIcc_of_le htmℓ_le_uT) ▸ hx
        have hx_ball : (x : ℂ) ∈ closedBall (0 : ℂ) (langerRadius c) := by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_le]
          exact ⟨by linarith [hx'.1, (abs_le.mp htm_A).1], by linarith [hx'.2, (abs_le.mp huA).2]⟩
        exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hAn (x : ℂ) hx_ball).differentiableAt.hasDerivAt.comp_ofReal
      have hcont : ContinuousOn (fun x : ℝ => (deriv (hankelPsi c f) (x : ℂ)).re)
          (Icc (D.tm + ℓ) u_T) := by
        refine Complex.continuous_re.comp_continuousOn ?_
        refine hAn.deriv.continuousOn.comp continuous_ofReal.continuousOn fun x hx => ?_
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [hx.1, (abs_le.mp htm_A).1], by linarith [hx.2, (abs_le.mp huA).2]⟩
      exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hda
        ((Set.uIcc_of_le htmℓ_le_uT ▸ hcont).intervalIntegrable)).symm
    have h_int_slope : ∫ x in (D.tm + ℓ)..u_T, (deriv (hankelPsi c f) (x : ℂ)).re ≤
        ∫ _ in (D.tm + ℓ)..u_T, -2 * κ_q := by
      have hcont : ContinuousOn (fun x : ℝ => (deriv (hankelPsi c f) (x : ℂ)).re)
          (Icc (D.tm + ℓ) u_T) := by
        refine Complex.continuous_re.comp_continuousOn ?_
        refine hAn.deriv.continuousOn.comp continuous_ofReal.continuousOn fun x hx => ?_
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [hx.1, (abs_le.mp htm_A).1], by linarith [hx.2, (abs_le.mp huA).2]⟩
      exact intervalIntegral.integral_mono_on htmℓ_le_uT (hcont.intervalIntegrable_of_Icc htmℓ_le_uT)
        intervalIntegrable_const fun x hx =>
        hB2.deriv_re_le x ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [intervalIntegral.integral_const, smul_eq_mul] at h_int_slope
    have h_sec : κ_q * (u_T - D.tm) ≤ (hankelPsi c f ((D.tm + ℓ : ℝ) : ℂ)).re -
        (hankelPsi c f (u_T : ℂ)).re := by
      have hlen : (1 / 2 : ℝ) * (u_T - D.tm) ≤ u_T - (D.tm + ℓ) := by
        have : u_T - (D.tm + ℓ) = (1 - θ) * (u_T - D.tm) := by dsimp [ℓ]; ring
        rw [this]; nlinarith [htm_uT]
      have h1 : (u_T - (D.tm + ℓ)) * (-2 * κ_q) ≤ (1 / 2 * (u_T - D.tm)) * (-2 * κ_q) := by
        nlinarith [hκ_pos]
      linarith
    have h_uT_sign : -hankelRinf c ≤ (hankelPsi c f (u_T : ℂ)).re :=
      hankelBoot_psi_ge_gen hc hf hε hM hT huA (by linarith) (abs_le.mp huA).1 le_rfl
    have h_psi_tm : κ_q * (u_T - D.tm) - hankelRinf c ≤ hankelPsiR c f (D.tm + ℓ) := by
      show _ ≤ (hankelPsi c f ((D.tm + ℓ : ℝ) : ℂ)).re
      linarith
    have hw_half : (1 / 2 : ℝ) ≤ (1 + D.tm / R) ^ (k₀ + 1) :=
      hb_node_pow_ge_half k₀ hR_tm htm_neg
    have htm_M : |D.tm| ≤ M_S := Finset.le_sup' (fun s => |s|) D.tm_mem
    have hpow_bd := hb_node_pow_upper hM_S_nn hR5 (by linarith [(abs_le.mp htm_M).1, (le_max_left _ (10 : ℝ)).trans hR_S])
      (abs_le.mp htm_M).2 hk0R
    have h_pow_u1 : (1 + D.tm / R) ^ (k₀ + 1) ≤ 1 := by
      have h1 : 1 + D.tm / R ≤ 1 := by
        have : D.tm / R ≤ 0 := div_nonpos_of_nonpos_of_nonneg htm_neg.le hR_pos.le
        linarith
      have hge1 : -1 ≤ D.tm / R := by rw [le_div_iff₀ hR_pos]; linarith [(abs_le.mp htm_M).1, (le_max_left _ (10 : ℝ)).trans hR_S]
      exact pow_le_one₀ (by linarith) h1
    have h_prod_lb : (1 / 2 : ℝ) * (κ_q * (u_T - D.tm)) - hankelRinf c ≤
        (1 + D.tm / R) ^ (k₀ + 1) * hankelPsiR c f (D.tm + ℓ) := by
      have hA : (1 + D.tm / R) ^ (k₀ + 1) * (κ_q * (u_T - D.tm) - hankelRinf c) ≤
          (1 + D.tm / R) ^ (k₀ + 1) * hankelPsiR c f (D.tm + ℓ) :=
        mul_le_mul_of_nonneg_left h_psi_tm hpow_bd.1
      have hsub_uT : 0 ≤ u_T - D.tm := (sub_pos.mpr htm_uT).le
      have hκu_nn : 0 ≤ κ_q * (u_T - D.tm) := mul_nonneg hκ_pos.le hsub_uT
      have hw_diff_nn : 0 ≤ (1 + D.tm / R) ^ (k₀ + 1) - 1 / 2 := by linarith only [hw_half]
      have h1_diff_nn : 0 ≤ 1 - (1 + D.tm / R) ^ (k₀ + 1) := by linarith only [h_pow_u1]
      have h_mul_k := mul_nonneg hw_diff_nn hκu_nn
      have h_mul_r := mul_nonneg h1_diff_nn hr
      linarith only [hA, h_mul_k, h_mul_r]
    rw [hb_node_term_eq D f k₀ (D.S_zero D.tm_mem), Complex.ofReal_re]
    have h_mul := mul_le_mul_of_nonneg_right h_prod_lb hwt_pos.le
    have hwr_nn : 0 ≤ hbWeight D (D.tm : ℂ) * hankelRinf c := mul_nonneg hwt_pos.le hr
    have hr1 : hbWeight D (D.tm : ℂ) * hankelRinf c ≤ M_pow * hbWeight D (D.tm : ℂ) * hankelRinf c := by
      have h := mul_le_mul_of_nonneg_right hMpow_ge1 hwr_nn
      linarith only [h]
    linarith only [h_mul, hr1]
  have hother_lb : ∀ z ∈ (hbZerosInDisc D R).erase (D.tm : ℂ),
      -(if z.re ∈ D.S.erase D.tm then 2 * (M_pow * C1_q) * hbWeight D z * ℓ else 0) -
        M_pow * hbWeight D z * hankelRinf c ≤
      (hankelBootShifted c f R ℓ k₀ z * (airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2)).re := by
    intro z hz
    rw [Finset.mem_erase] at hz
    obtain ⟨hz_ne_tm, hz_in⟩ := hz
    obtain ⟨hz0, hzR⟩ := (mem_hbZerosInDisc D).mp hz_in
    have hzr := airyPQ_zero_eq_ofReal D.hHB hz0
    have hzw : 0 ≤ hbWeight D z := hbWeight_nonneg_of_zero D hz0
    have hz_abs : |z.re| ≤ R := hb_zeros_re_abs_le D hz0 hzR
    have hz_re_ne : z.re ≠ D.tm := fun h => hz_ne_tm (by rw [hzr, h])
    have hz_M : z.re ≤ M_S := by
      by_cases hzS : z.re ∈ D.S
      · exact (abs_le.mp (Finset.le_sup' (fun s => |s|) hzS)).2
      · have hlt := D.S_top z.re (hzr ▸ hz0) hzS D.tm D.tm_mem
        linarith only [hlt, le_abs_self D.tm, Finset.le_sup' (fun s => |s|) D.tm_mem]
    have hpow_bd := hb_node_pow_upper hM_S_nn hR5 (abs_le.mp hz_abs).1 hz_M hk0R
    rw [hb_node_term_eq D f k₀ hz0]
    by_cases hzS : z.re ∈ D.S.erase D.tm
    · simp only [hzS, reduceIte]
      have hzS' : z.re ∈ D.S := (Finset.mem_erase.mp hzS).2
      obtain ⟨hu_diff, hu_A, hu_sign⟩ := hsites z.re hzS
      have hre_psi := hb_node_upper_site_re_lb D hc0 hfe hD1_small hℓ0 hℓ_lb
        (by linarith only [hℓ_delta, hδ_le_q]) ((le_max_left _ (10 : ℝ)).trans hR_S) hRA hzS'
        hu_diff hu_A hu_sign (fun x hx => hB2.deriv_norm_le z.re hzS' x hx)
      have h_mul1 : -(M_pow * (hankelRinf c + 2 * C1_q * ℓ)) ≤
          (1 + z.re / R) ^ (k₀ + 1) * hankelPsiR c f (z.re + ℓ) := by
        have hpos_b : 0 ≤ hankelRinf c + 2 * C1_q * ℓ := by positivity
        have h1 : -(M_pow * (hankelRinf c + 2 * C1_q * ℓ)) ≤
            -((1 + z.re / R) ^ (k₀ + 1) * (hankelRinf c + 2 * C1_q * ℓ)) := by
          have := mul_le_mul_of_nonneg_right hpow_bd.2 hpos_b
          linarith only [this]
        have h2 : -((1 + z.re / R) ^ (k₀ + 1) * (hankelRinf c + 2 * C1_q * ℓ)) ≤
            (1 + z.re / R) ^ (k₀ + 1) * hankelPsiR c f (z.re + ℓ) := by
          rw [← mul_neg]; exact mul_le_mul_of_nonneg_left hre_psi hpow_bd.1
        linarith only [h1, h2]
      have h_fin := mul_le_mul_of_nonneg_right h_mul1 hzw
      linarith only [h_fin]
    · simp only [hzS, reduceIte, neg_zero, zero_sub]
      have hz_not_S : z.re ∉ D.S := fun h => hzS (Finset.mem_erase.mpr ⟨hz_re_ne, h⟩)
      have hz_lt : z.re < D.tm := D.S_top z.re (hzr ▸ hz0) hz_not_S D.tm D.tm_mem
      have hgap := hbZeroGapBelow_spec D (hzr ▸ hz0) hz_lt
      have hzℓ_le : z.re + ℓ ≤ u_T := by linarith only [hgap, hℓ_gap, htm_uT]
      have hzℓ_A : |z.re + ℓ| ≤ langerRadius c := by
        have hℓ1 : ℓ ≤ 1 := hℓ_ub.trans ((min_le_right _ _).trans (min_le_right _ _))
        rw [abs_le]
        exact ⟨by linarith only [(abs_le.mp hz_abs).1, hℓ0, hRA], by linarith only [(abs_le.mp hz_abs).2, hℓ1, hRA]⟩
      have hsign : -hankelRinf c ≤ hankelPsiR c f (z.re + ℓ) :=
        hankelBoot_psi_ge_gen hc hf hε hM hT huA (by linarith only [hRA]) (abs_le.mp hzℓ_A).1 hzℓ_le
      have h1 : -(M_pow * hankelRinf c) ≤ (1 + z.re / R) ^ (k₀ + 1) * hankelPsiR c f (z.re + ℓ) := by
        have ha1 : -(M_pow * hankelRinf c) ≤ -((1 + z.re / R) ^ (k₀ + 1) * hankelRinf c) := by
          have := mul_le_mul_of_nonneg_right hpow_bd.2 hr
          linarith only [this]
        have ha2 : -((1 + z.re / R) ^ (k₀ + 1) * hankelRinf c) ≤
            (1 + z.re / R) ^ (k₀ + 1) * hankelPsiR c f (z.re + ℓ) := by
          rw [← mul_neg]; exact mul_le_mul_of_nonneg_left hsign hpow_bd.1
        linarith only [ha1, ha2]
      have h_fin := mul_le_mul_of_nonneg_right h1 hzw
      linarith only [h_fin]
  have htm_mem_disc : (D.tm : ℂ) ∈ hbZerosInDisc D R := hS_sub (Finset.mem_image.mpr ⟨D.tm, D.tm_mem, rfl⟩)
  have hsplit : hankelBootMultilevelNodes D c f R ℓ k₀ =
      (hankelBootShifted c f R ℓ k₀ (D.tm : ℂ) *
        (airyPQD D.P D.Q (D.tm : ℂ) / airyPQN' D.P D.Q (D.tm : ℂ) ^ 2)).re +
      ∑ z ∈ (hbZerosInDisc D R).erase (D.tm : ℂ),
        (hankelBootShifted c f R ℓ k₀ z * (airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2)).re := by
    unfold hankelBootMultilevelNodes
    exact (Finset.add_sum_erase (hbZerosInDisc D R) _ htm_mem_disc).symm
  have hsum_other := Finset.sum_le_sum hother_lb
  rw [Finset.sum_sub_distrib] at hsum_other
  have h_top_sum : ∑ z ∈ (hbZerosInDisc D R).erase (D.tm : ℂ),
      (if z.re ∈ D.S.erase D.tm then 2 * (M_pow * C1_q) * hbWeight D z * ℓ else 0) =
      2 * (M_pow * C1_q) * hbTopWeights D * ℓ := by
    have hinj : ∀ a ∈ D.S.erase D.tm, ∀ b ∈ D.S.erase D.tm, (a : ℂ) = (b : ℂ) → a = b :=
      fun _ _ _ _ h => Complex.ofReal_injective h
    have hsub : ∀ z ∈ (hbZerosInDisc D R).erase (D.tm : ℂ),
        (if z.re ∈ D.S.erase D.tm then 2 * (M_pow * C1_q) * hbWeight D z * ℓ else 0) =
        (if z ∈ (D.S.erase D.tm).image (fun t : ℝ => (t : ℂ)) then
          2 * (M_pow * C1_q) * hbWeight D z * ℓ else 0) := by
      intro z hz
      obtain ⟨_, hz_in⟩ := Finset.mem_erase.mp hz
      obtain ⟨hz0, _⟩ := (mem_hbZerosInDisc D).mp hz_in
      have hzr := airyPQ_zero_eq_ofReal D.hHB hz0
      have hiff : z.re ∈ D.S.erase D.tm ↔ z ∈ (D.S.erase D.tm).image (fun t : ℝ => (t : ℂ)) := by
        constructor
        · intro ht; rw [Finset.mem_image]; exact ⟨z.re, ht, hzr.symm⟩
        · intro ht; rw [Finset.mem_image] at ht; obtain ⟨t, htS, htz⟩ := ht
          have heq : t = z.re := by simpa using congrArg Complex.re htz
          rwa [← heq]
      exact if_congr hiff rfl rfl
    rw [Finset.sum_congr rfl hsub, ← Finset.sum_filter]
    have hfilt : ((hbZerosInDisc D R).erase (D.tm : ℂ)).filter
          (fun z => z ∈ (D.S.erase D.tm).image (fun t : ℝ => (t : ℂ))) =
        (D.S.erase D.tm).image (fun t : ℝ => (t : ℂ)) := by
      ext z; simp only [Finset.mem_filter, and_iff_right_iff_imp, Finset.mem_erase, Finset.mem_image]
      rintro ⟨t, ht, rfl⟩
      exact ⟨fun h => ht.1 (Complex.ofReal_injective h),
        hS_sub (Finset.mem_image.mpr ⟨t, ht.2, rfl⟩)⟩
    rw [hfilt, Finset.sum_image hinj]
    unfold hbTopWeights
    rw [Finset.mul_sum, Finset.sum_mul]
  have h_rinf_all : M_pow * hbWeight D (D.tm : ℂ) * hankelRinf c +
      ∑ z ∈ (hbZerosInDisc D R).erase (D.tm : ℂ), M_pow * hbWeight D z * hankelRinf c ≤
      M_pow * hbWeightSumConst D * R ^ (3 / 2 : ℝ) * hankelRinf c := by
    have h_add : M_pow * hbWeight D (D.tm : ℂ) * hankelRinf c +
        ∑ z ∈ (hbZerosInDisc D R).erase (D.tm : ℂ), M_pow * hbWeight D z * hankelRinf c =
        ∑ z ∈ hbZerosInDisc D R, M_pow * hbWeight D z * hankelRinf c :=
      Finset.add_sum_erase (hbZerosInDisc D R) (fun z => M_pow * hbWeight D z * hankelRinf c) htm_mem_disc
    rw [h_add]
    have hweq : ∀ z ∈ hbZerosInDisc D R, hbWeight D z =
        ‖airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2‖ := fun z hz => by
      obtain ⟨hz0, _⟩ := (mem_hbZerosInDisc D).mp hz
      rw [hbWeight_real_of_zero D hz0, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hbWeight_nonneg_of_zero D hz0)]
    calc ∑ z ∈ hbZerosInDisc D R, M_pow * hbWeight D z * hankelRinf c
        = M_pow * hankelRinf c * ∑ z ∈ hbZerosInDisc D R, hbWeight D z := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
      _ = M_pow * hankelRinf c * ∑ z ∈ hbZerosInDisc D R, ‖airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2‖ := by
          rw [Finset.sum_congr rfl hweq]
      _ ≤ M_pow * hankelRinf c * (hbWeightSumConst D * R ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hbWeightSumConst_spec D hQ hR_ge1) (mul_nonneg (by linarith) hr)
      _ = M_pow * hbWeightSumConst D * R ^ (3 / 2 : ℝ) * hankelRinf c := by ring
  have h_ell_mul : 2 * (M_pow * C1_q) * hbTopWeights D * ℓ =
      (2 * (M_pow * C1_q) * hbTopWeights D * θ) * (u_T - D.tm) := by
    dsimp [ℓ]; ring
  rw [Finset.sum_neg_distrib, h_top_sum] at hsum_other
  linarith only [hsplit, htm_term_lb, hsum_other, h_rinf_all, h_ell_mul]

/-- info: 'FormalResearch.SignUncertainty.hbMultilevelLower_Q_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hbMultilevelLower_Q_eq_zero

/-- info: 'FormalResearch.SignUncertainty.hankelBootMultilevel_nodes_lb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBootMultilevel_nodes_lb

/-- info: 'FormalResearch.SignUncertainty.hankelBootMultilevel_nodes_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBootMultilevel_nodes_theta

end FormalResearch.SignUncertainty
