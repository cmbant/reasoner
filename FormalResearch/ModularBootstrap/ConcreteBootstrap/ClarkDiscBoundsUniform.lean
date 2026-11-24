module

public import FormalResearch.ModularBootstrap.ConcreteBootstrap.ClarkDiscBounds
public import FormalResearch.SignUncertainty.ClarkTwoNode

/-!
# Uniform good circles and the Clark node list on a good circle

`Lemma 1.0` / `Lemma 1.0′` (`gt:1.0`, `gt:1.0p`) for the Clark functions `ψ_α = cos α Ai - sin α Ai'`, with the
dependence on `α` made explicit, and the `CftCircleData` of `ψ_α` on a good circle with the nodes `z_n(α)`:

* `clark_good_circle_at`: for `Q ≠ 0` and a radius `r` with `64 (1 + P²/Q²) ≤ r` and `(2/3) r^{3/2} = 3π/4 + mπ`,
  on the whole circle `‖u‖ = r`: `(Q²/(256π)) √r e(u) ≤ ‖N(u)‖²`, `‖M/N ∓ i‖ e ≤ 40 √π (3|P| + 5|Q|)/|Q|`
  on the upper/lower half.  The radii do not depend on `(P, Q)`.
* `clark_good_circle_uniform`: for `|sin α| ≥ σ > 0`, with `(P, Q) = (cos α, -sin α)`: one radius `r_k ∈ [k, k + 1]` for
  every `k ≥ k₀(σ) = ⌈64 (1 + σ⁻²)⌉`, the same for all such `α`, with the common ratio bound `C₀(σ) = 320 √π/σ`
  and `σ²/(256π) √r e ≤ ‖ψ_α‖²`.
* `exists_abs_sin_lower_bound`: a compact set of angles with `sin α ≠ 0` has `|sin α| ≥ σ > 0`;
  `abs_sin_ge_of_abs_cot_le`: in the parameter `c = cot α`, `|c| ≤ Λ` gives `|sin α| ≥ (1 + Λ²)^{-1/2}`.
* `clark_circleData`: if `z_1(α) < R` and `ψ_α ≠ 0` on `‖u‖ = R`, there is `N` with
  `CftCircleData ψ_α (z_n(α))_{n} (Icc 1 N) R` (the nodes inside the disc are `z_1(α) > ⋯ > z_N(α)`).
* `clark_defect_ball_split_uniform`: the combination (`Lemma 1.0′` + `lem:hb-quadrature`): constants uniform in `α`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set intervalIntegral
open scoped Real

namespace FormalResearch.ModularBootstrap.ConcreteBootstrap

open FormalResearch.Special FormalResearch.SignUncertainty

/-- **Good circle of explicit radius** for `N = P Ai + Q Ai'` (`Q ≠ 0`): the lower bound and the ratio bounds on the circle
`‖u‖ = r`, `(2/3) r^{3/2} = 3π/4 + mπ`, `64 (1 + P²/Q²) ≤ r`. -/
theorem clark_good_circle_at (P Q : ℝ) (hQ : Q ≠ 0) {r : ℝ} (hrk : 64 * (1 + P ^ 2 / Q ^ 2) ≤ r) (m : ℕ)
    (hm : 2 / 3 * r ^ (3 / 2 : ℝ) = 3 * π / 4 + m * π) :
    ∀ u : ℂ, ‖u‖ = r →
      Q ^ 2 / (256 * π) * √r * airyEnv u ≤ ‖airyNC P Q u‖ ^ 2 ∧
      (0 ≤ u.im → ‖airyMC P Q u / airyNC P Q u - I‖ * airyEnv u ≤
        40 * √π * (3 * |P| + 5 * |Q|) / |Q|) ∧
      (u.im ≤ 0 → ‖airyMC P Q u / airyNC P Q u + I‖ * airyEnv u ≤
        40 * √π * (3 * |P| + 5 * |Q|) / |Q|) := by
  have hQ0 : 0 < |Q| := abs_pos.mpr hQ
  have hK0 : 0 ≤ 3 * |P| + 5 * |Q| := by positivity
  have hr64 : (64 : ℝ) ≤ r := by
    have : 0 ≤ P ^ 2 / Q ^ 2 := by positivity
    linarith
  have hrpos : 0 < r := by linarith
  have hsr : 8 ≤ √r := Real.le_sqrt_of_sq_le (by nlinarith)
  have hPQ := airyC2_abs_le_of_sq hrk hQ
  intro u hu
  have hlow : ∀ v : ℂ, ‖v‖ = r →
      Q ^ 2 / (256 * π) * √r * airyEnv v ≤ ‖airyNC P Q v‖ ^ 2 := by
    intro v hv
    have henv := airyEnv_pos v
    by_cases hcase : -(‖v‖ / 2) ≤ v.re
    · have := airyNC_sector_ge P Q hcase (by rw [hv]; linarith) (by rw [hv]; exact hPQ)
      rw [hv] at this
      refine le_trans ?_ this
      have : Q ^ 2 / (256 * π) * √r * airyEnv v ≤ Q ^ 2 * √r * airyEnv v / (16 * π) := by
        have hh : 0 ≤ Q ^ 2 * √r * airyEnv v := by positivity
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg hh Real.pi_pos.le]
      exact this
    · have hlt : v.re < -(‖v‖ / 2) := not_le.mp hcase
      set q : ℂ := (-v) ^ (1 / 2 : ℂ) with hqdef
      have hq : NegSector q := NegSector_of_re_lt hlt
      have hq2 : q ^ 2 = -v := cpow_half_sq _
      have hqn : ‖q‖ ^ 2 = r := by rw [hqdef, norm_cpow_half_sq, norm_neg, hv]
      have hq3 : ‖q‖ ^ 3 = r ^ (3 / 2 : ℝ) := by
        rw [hqdef, airyNorm_cpow_half_pow_three, norm_neg, hv]
      have hqs : ‖q‖ = √r := by rw [← hqn, Real.sqrt_sq (norm_nonneg _)]
      have := airyNC_neg_sq_ge P Q hq m (by rw [hq3]; exact hm) (by rw [hqs]; linarith)
        (by rw [hqs]; exact hPQ)
      have e : -(q ^ 2) = v := by rw [hq2, neg_neg]
      rw [e, hqs] at this
      refine le_trans (le_of_eq ?_) this
      ring
  have hL := hlow u hu
  have hup : ∀ v : ℂ, ‖v‖ = r → 0 ≤ v.im →
      ‖airyMC P Q v / airyNC P Q v - I‖ * airyEnv v ≤ 40 * √π * (3 * |P| + 5 * |Q|) / |Q| := by
    intro v hv hvi
    have hLv := hlow v hv
    have hen := airyEnv_pos v
    have hsr0 : 0 < √r := Real.sqrt_pos.mpr hrpos
    have hN2 : 0 < ‖airyNC P Q v‖ ^ 2 := by
      refine lt_of_lt_of_le ?_ hLv
      positivity
    have hN : 0 < ‖airyNC P Q v‖ := by
      rcases (norm_nonneg (airyNC P Q v)).lt_or_eq with h | h
      · exact h
      · rw [← h] at hN2; simp at hN2
    have hne : airyNC P Q v ≠ 0 := norm_pos_iff.mp hN
    have hnum := airyMC_sub_I_mul_sq_le P Q hvi
    rw [hv] at hnum
    have e : airyMC P Q v / airyNC P Q v - I = (airyMC P Q v - I * airyNC P Q v) / airyNC P Q v := by
      field_simp
    rw [e, norm_div]
    have h1r : (1 + r) ^ (1 / 2 : ℝ) ≤ 3 / 2 * √r := by
      have : (1 + r) ^ (1 / 2 : ℝ) = √(1 + r) := (Real.sqrt_eq_rpow _).symm
      rw [this]
      have : √(1 + r) ≤ √(2 * r) := Real.sqrt_le_sqrt (by linarith)
      refine this.trans ?_
      rw [Real.sqrt_mul (by norm_num)]
      have : √2 ≤ 3 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
      exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
    have hnum' : ‖airyMC P Q v - I * airyNC P Q v‖ ^ 2 * airyEnv v ≤
        4 * (3 * |P| + 5 * |Q|) ^ 2 * (3 / 2 * √r) :=
      hnum.trans (by gcongr)
    exact airyC2_ratio_le hN hen hsr0 hnum' hLv hK0 hQ0
  refine ⟨hL, fun hi => hup u hu hi, fun hi => ?_⟩
  have hci : 0 ≤ ((starRingEnd ℂ) u).im := by simpa using hi
  have hcu : ‖(starRingEnd ℂ) u‖ = r := by rw [Complex.norm_conj, hu]
  have h := hup ((starRingEnd ℂ) u) hcu hci
  have e : ‖airyMC P Q u / airyNC P Q u + I‖ =
      ‖airyMC P Q ((starRingEnd ℂ) u) / airyNC P Q ((starRingEnd ℂ) u) - I‖ := by
    have : airyMC P Q ((starRingEnd ℂ) u) / airyNC P Q ((starRingEnd ℂ) u) - I =
        (starRingEnd ℂ) (airyMC P Q u / airyNC P Q u + I) := by
      rw [map_add, map_div₀, conj_airyMC, conj_airyNC, Complex.conj_I]; ring
    rw [this, Complex.norm_conj]
  rw [e, ← airyEnv_conj u]
  exact h

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.clark_good_circle_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clark_good_circle_at

/-- A compact set of angles on which `sin α ≠ 0` has `|sin α| ≥ σ` for some `σ > 0`. -/
theorem exists_abs_sin_lower_bound {K : Set ℝ} (hK : IsCompact K) (hne : ∀ α ∈ K, Real.sin α ≠ 0) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ α ∈ K, σ ≤ |Real.sin α| := by
  rcases K.eq_empty_or_nonempty with rfl | hK0
  · exact ⟨1, one_pos, fun α hα => absurd hα (Set.notMem_empty α)⟩
  obtain ⟨α₀, hα₀, hmin⟩ := hK.exists_isMinOn hK0 (Real.continuous_sin.abs.continuousOn)
  exact ⟨|Real.sin α₀|, abs_pos.mpr (hne α₀ hα₀), fun α hα => hmin hα⟩

/-- In the parameter `c = cot α` of `Ai' - c Ai`: `|cot α| ≤ Λ` gives `|sin α| ≥ (1 + Λ²)^{-1/2}`. -/
theorem abs_sin_ge_of_abs_cot_le {α Λ : ℝ} (hα : Real.sin α ≠ 0) (h : |Real.cos α / Real.sin α| ≤ Λ) :
    1 / √(1 + Λ ^ 2) ≤ |Real.sin α| := by
  have hs2 : 0 < Real.sin α ^ 2 := by positivity
  have hΛ : (Real.cos α / Real.sin α) ^ 2 ≤ Λ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hone : 1 = Real.sin α ^ 2 * (1 + (Real.cos α / Real.sin α) ^ 2) := by
    field_simp; linarith [Real.sin_sq_add_cos_sq α]
  have h1 : 1 ≤ Real.sin α ^ 2 * (1 + Λ ^ 2) := by
    calc (1 : ℝ) = Real.sin α ^ 2 * (1 + (Real.cos α / Real.sin α) ^ 2) := hone
      _ ≤ Real.sin α ^ 2 * (1 + Λ ^ 2) := by gcongr
  have hpos : 0 < 1 + Λ ^ 2 := by positivity
  rw [← Real.sqrt_sq_eq_abs]
  refine Real.le_sqrt_of_sq_le ?_
  rw [div_pow, Real.sq_sqrt hpos.le, div_le_iff₀ hpos]
  linarith

/-- **Good circles for the Clark functions, uniform in `α`** (`gt:1.0`, `gt:1.0′` for constant pairs
`(P, Q) = (cos α, -sin α)`, `|sin α| ≥ σ`): one radius `r ∈ [k, k + 1]` for all such `α`, on which
`(σ²/(256π)) √r e ≤ ‖ψ_α‖²` and `‖M/N ∓ i‖ e ≤ C₀ = 320 √π/σ` on the half circles; `k₀ = ⌈64 (1 + σ⁻²)⌉`. -/
theorem clark_good_circle_uniform {σ : ℝ} (hσ : 0 < σ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ k₀ : ℕ, 10 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∃ r : ℝ, (k : ℝ) ≤ r ∧ r ≤ k + 1 ∧
      ∀ α : ℝ, σ ≤ |Real.sin α| → ∀ u : ℂ, ‖u‖ = r →
        σ ^ 2 / (256 * π) * √r * airyEnv u ≤ ‖airyNC (Real.cos α) (-Real.sin α) u‖ ^ 2 ∧
        (0 ≤ u.im → ‖airyMC (Real.cos α) (-Real.sin α) u / airyNC (Real.cos α) (-Real.sin α) u - I‖ *
          airyEnv u ≤ C₀) ∧
        (u.im ≤ 0 → ‖airyMC (Real.cos α) (-Real.sin α) u / airyNC (Real.cos α) (-Real.sin α) u + I‖ *
          airyEnv u ≤ C₀) := by
  have hk0 : 10 ≤ ⌈64 * (1 + (σ ^ 2)⁻¹)⌉₊ := by
    have : (64 : ℝ) ≤ 64 * (1 + (σ ^ 2)⁻¹) := by
      have : 0 ≤ (σ ^ 2)⁻¹ := by positivity
      linarith
    have h2 : (64 : ℝ) ≤ ⌈64 * (1 + (σ ^ 2)⁻¹)⌉₊ := this.trans (Nat.le_ceil _)
    exact_mod_cast (by linarith : (10 : ℝ) ≤ ⌈64 * (1 + (σ ^ 2)⁻¹)⌉₊)
  refine ⟨320 * √π / σ, by positivity, ⌈64 * (1 + (σ ^ 2)⁻¹)⌉₊, hk0, fun k hk => ?_⟩
  have hk64 : 64 * (1 + (σ ^ 2)⁻¹) ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hk10 : 10 ≤ k := by
    have : (64 : ℝ) ≤ k := by
      have : 0 ≤ (σ ^ 2)⁻¹ := by positivity
      linarith
    exact_mod_cast (by linarith : (10 : ℝ) ≤ k)
  obtain ⟨r, hr1, hr2, m, hm⟩ := airyC2_radius_exists k hk10 (c := 3 * π / 4) (by positivity)
    (by linarith [Real.pi_pos])
  refine ⟨r, hr1, hr2, fun α hα u hu => ?_⟩
  have hsin : Real.sin α ≠ 0 := fun h => by rw [h, abs_zero] at hα; linarith
  have hQ : -Real.sin α ≠ 0 := neg_ne_zero.mpr hsin
  have hQ2 : σ ^ 2 ≤ (-Real.sin α) ^ 2 := by
    rw [neg_sq, ← sq_abs (Real.sin α)]
    exact pow_le_pow_left₀ hσ.le hα 2
  have hP2 : Real.cos α ^ 2 ≤ 1 := Real.cos_sq_le_one α
  have hratio : Real.cos α ^ 2 / (-Real.sin α) ^ 2 ≤ (σ ^ 2)⁻¹ := by
    rw [div_eq_mul_inv]
    have hs2 : 0 < σ ^ 2 := by positivity
    calc Real.cos α ^ 2 * ((-Real.sin α) ^ 2)⁻¹ ≤ 1 * ((-Real.sin α) ^ 2)⁻¹ := by
          gcongr
      _ ≤ (σ ^ 2)⁻¹ := by
          rw [one_mul]; exact inv_anti₀ hs2 hQ2
  have hrk : 64 * (1 + Real.cos α ^ 2 / (-Real.sin α) ^ 2) ≤ r := by
    have : 64 * (1 + Real.cos α ^ 2 / (-Real.sin α) ^ 2) ≤ 64 * (1 + (σ ^ 2)⁻¹) := by linarith
    linarith
  obtain ⟨hL, hup, hlo⟩ := clark_good_circle_at (Real.cos α) (-Real.sin α) hQ hrk m hm u hu
  have hCb : 40 * √π * (3 * |Real.cos α| + 5 * |-Real.sin α|) / |-Real.sin α| ≤ 320 * √π / σ := by
    have hc1 : |Real.cos α| ≤ 1 := Real.abs_cos_le_one α
    have hs1 : |-Real.sin α| ≤ 1 := by rw [abs_neg]; exact Real.abs_sin_le_one α
    have hsa : σ ≤ |-Real.sin α| := by rw [abs_neg]; exact hα
    have hsp : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
    rw [div_le_div_iff₀ (by linarith) hσ]
    have h8 : 3 * |Real.cos α| + 5 * |-Real.sin α| ≤ 8 := by linarith
    have : 40 * √π * (3 * |Real.cos α| + 5 * |-Real.sin α|) ≤ 40 * √π * 8 := by gcongr
    calc 40 * √π * (3 * |Real.cos α| + 5 * |-Real.sin α|) * σ
        ≤ 40 * √π * 8 * |-Real.sin α| := by
          calc 40 * √π * (3 * |Real.cos α| + 5 * |-Real.sin α|) * σ
              ≤ 40 * √π * 8 * σ := by gcongr
            _ ≤ 40 * √π * 8 * |-Real.sin α| := by gcongr
      _ = 320 * √π * |-Real.sin α| := by ring
  refine ⟨?_, fun hi => (hup hi).trans hCb, fun hi => (hlo hi).trans hCb⟩
  refine le_trans ?_ hL
  have hnn : 0 ≤ √r * airyEnv u := mul_nonneg (Real.sqrt_nonneg _) (airyEnv_pos u).le
  calc σ ^ 2 / (256 * π) * √r * airyEnv u = σ ^ 2 / (256 * π) * (√r * airyEnv u) := by ring
    _ ≤ (-Real.sin α) ^ 2 / (256 * π) * (√r * airyEnv u) := by gcongr
    _ = (-Real.sin α) ^ 2 / (256 * π) * √r * airyEnv u := by ring

/-- **The nodes `z_n(α)` inside a good circle** (`Step 4` of `wone:ftlfw`): if `z_1(α) < R` and `ψ_α ≠ 0` on
`‖u‖ = R`, there is `N` with `n ≤ N ↔ z_n(α) > -R` (`n ≥ 1`) and the `CftCircleData` of `ψ_α = N_α` with the
nodes `z_1(α) > ⋯ > z_N(α)` (the zeros of `ψ_α` in `‖z‖ ≤ R`, all simple). -/
theorem clark_circleData {α R : ℝ} (hα : Real.sin α ≠ 0) (hR : 0 < R) (hR1 : clarkNode α 1 < R)
    (hgood : ∀ u : ℂ, ‖u‖ = R → airyNC (Real.cos α) (-Real.sin α) u ≠ 0) :
    ∃ N : ℕ, (∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -R < clarkNode α n)) ∧
      CftCircleData (airyNC (Real.cos α) (-Real.sin α)) (fun n => (clarkNode α n : ℂ))
        (Finset.Icc 1 N) R := by
  classical
  have hQ : -Real.sin α ≠ 0 := neg_ne_zero.mpr hα
  have hz : ∀ n : ℕ, 1 ≤ n → airyNC (Real.cos α) (-Real.sin α) (clarkNode α n : ℂ) = 0 := fun n hn => by
    rw [← psiClark_eq_airyNC]; exact clarkNode_zero hα hn
  have hanti : ∀ {m n : ℕ}, 1 ≤ m → m ≤ n → clarkNode α n ≤ clarkNode α m := by
    intro m n hm hmn
    rcases hmn.lt_or_eq with h | h
    · exact (clarkNode_lt_of_lt hm h α).le
    · rw [h]
  have hex : ∃ k : ℕ, ¬ (-R < clarkNode α (k + 1)) := by
    obtain ⟨n, hn2, hn⟩ := airyZero_exists_abs_ge R
    refine ⟨n, fun h => ?_⟩
    have h1 := airyClarkNode_lt_airyZero (n := n + 1) (by omega) (Real.cos α / Real.sin α)
    have h2 : clarkNode α (n + 1) < airyZero n := by
      rw [Nat.add_sub_cancel] at h1
      exact h1
    linarith
  refine ⟨Nat.find hex, fun n hn => ?_, ?_⟩
  · constructor
    · intro hnN
      have := Nat.find_min hex (show n - 1 < Nat.find hex by omega)
      rw [Nat.sub_add_cancel hn] at this
      exact not_not.mp this
    · intro hlt
      by_contra hnN
      have h1 : Nat.find hex + 1 ≤ n := by omega
      have h2 := hanti (by omega) h1
      have h3 := Nat.find_spec hex
      exact h3 (lt_of_lt_of_le hlt h2)
  · set N := Nat.find hex with hNdef
    have hN : ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -R < clarkNode α n) := by
      intro n hn
      constructor
      · intro hnN
        have := Nat.find_min hex (show n - 1 < Nat.find hex by omega)
        rw [Nat.sub_add_cancel hn] at this
        exact not_not.mp this
      · intro hlt
        by_contra hnN
        have h1 : Nat.find hex + 1 ≤ n := by omega
        have h2 := hanti (by omega) h1
        have h3 := Nat.find_spec hex
        exact h3 (lt_of_lt_of_le hlt h2)
    refine ⟨differentiable_airyNC _ _, hR, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi j hj hij
      have hi' := Finset.mem_Icc.mp hi
      have hj' := Finset.mem_Icc.mp hj
      have hij' : clarkNode α i = clarkNode α j := Complex.ofReal_injective hij
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := clarkNode_lt_of_lt hi'.1 h α; linarith
      · have := clarkNode_lt_of_lt hj'.1 h α; linarith
    · intro i hi
      have hi' := Finset.mem_Icc.mp hi
      have h1 := (hN i hi'.1).mp hi'.2
      have h2 : clarkNode α i ≤ clarkNode α 1 := hanti le_rfl hi'.1
      rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]
      exact ⟨h1, by linarith⟩
    · intro i hi
      exact hz i (Finset.mem_Icc.mp hi).1
    · intro i hi
      have hzi := hz i (Finset.mem_Icc.mp hi).1
      rw [deriv_airyNC]
      exact (airyNC_zero_weight_pos _ _ hQ hzi).2
    · intro w hw h0
      have h0' : psiClark α w = 0 := by rw [psiClark_eq_airyNC]; exact h0
      obtain ⟨n, hn, rfl⟩ := (psiClark_zero_iff hα w).mp h0'
      refine ⟨n, Finset.mem_Icc.mpr ⟨hn, ?_⟩, rfl⟩
      rw [Complex.norm_real, Real.norm_eq_abs] at hw
      have hge : -R ≤ clarkNode α n := (abs_le.mp hw).1
      have hne : -R ≠ clarkNode α n := by
        intro h
        apply hgood (clarkNode α n : ℂ)
        · rw [Complex.norm_real, Real.norm_eq_abs, ← h, abs_neg, abs_of_pos hR]
        · exact hz n hn
      exact (hN n hn).mpr (lt_of_le_of_ne hge hne)

/-- **Integral-split defect bound for the Clark nodes, uniform in `α`** (`Step 4` of `wone:ftlfw`): for every `σ > 0`
there are `C₀`, `k₀` such that for `k ≥ k₀` the radius `r ∈ [k, k + 1]` (the same for all `α` with `|sin α| ≥ σ`)
satisfies: for `f` holomorphic on `ball 0 R'` (`r < R'`) with `‖f‖/e ≤ B(θ)` on the circle `‖u‖ = r`, and `S` the set
of the zeros of `ψ_α` in `‖z‖ ≤ r`,
`‖Σ_{t ∈ S} f(t)/K(t,t) - ∫_{-r}^{r} f‖ ≤ (C₀/2) r ∫_{-π}^{π} B`. -/
theorem clark_defect_ball_split_uniform {σ : ℝ} (hσ : 0 < σ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ k₀ : ℕ, 10 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∃ r : ℝ, (k : ℝ) ≤ r ∧ r ≤ k + 1 ∧
      ∀ α : ℝ, σ ≤ |Real.sin α| → ∀ {R' : ℝ}, r < R' → ∀ {f : ℂ → ℂ}, DifferentiableOn ℂ f (ball 0 R') →
        ∀ S : Finset ℂ, (∀ z : ℂ, z ∈ S ↔ airyNC (Real.cos α) (-Real.sin α) z = 0 ∧ ‖z‖ ≤ r) →
        ∀ {B : ℝ → ℝ}, IntervalIntegrable B volume (-π) π →
        (∀ θ ∈ Icc (-π) π, ‖f (circleMap 0 r θ)‖ / airyEnv (circleMap 0 r θ) ≤ B θ) →
        ‖(∑ t ∈ S, f t / (deriv airyAiC t ^ 2 - t * airyAiC t ^ 2)) - ∫ x in (-r)..r, f (x : ℂ)‖ ≤
          (C₀ / 2 * r) * ∫ θ in (-π)..π, B θ := by
  obtain ⟨C₀, hC₀, k₀, hk₀, h⟩ := clark_good_circle_uniform hσ
  refine ⟨C₀, hC₀, k₀, hk₀, fun k hk => ?_⟩
  obtain ⟨r, hr1, hr2, hr⟩ := h k hk
  have hk10 : (10 : ℝ) ≤ k := by exact_mod_cast hk₀.trans hk
  have hr0 : 0 < r := by linarith
  refine ⟨r, hr1, hr2, fun α hα R' hrR' f hf S hS B hB hBb => ?_⟩
  have hsin : Real.sin α ≠ 0 := fun h => by rw [h, abs_zero] at hα; linarith
  have hQ : -Real.sin α ≠ 0 := neg_ne_zero.mpr hsin
  have hN : ∀ u : ℂ, ‖u‖ = r → airyNC (Real.cos α) (-Real.sin α) u ≠ 0 := by
    intro u hu h0
    have h1 := (hr α hα u hu).1
    rw [h0, norm_zero] at h1
    have : 0 < σ ^ 2 / (256 * π) * √r * airyEnv u := by
      have := airyEnv_pos u
      have : 0 < √r := Real.sqrt_pos.mpr hr0
      positivity
    linarith
  have h := clark_defect_ball_split (Real.cos α) (-Real.sin α) hQ hr0 hrR' hf hN
    (fun w hw hi => (hr α hα w hw).2.1 hi) (fun w hw hi => (hr α hα w hw).2.2 hi) S hS hB hBb
  have hsum : ∑ t ∈ S, f t * (airyDC (Real.cos α) (-Real.sin α) t /
      airyNC' (Real.cos α) (-Real.sin α) t ^ 2) =
      ∑ t ∈ S, f t / (deriv airyAiC t ^ 2 - t * airyAiC t ^ 2) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [airyNC_weight_eq_inv_K _ _ hQ ((hS t).mp ht).1]
    ring
  rw [hsum] at h
  exact h

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.clark_good_circle_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clark_good_circle_uniform

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.clark_circleData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clark_circleData

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.clark_defect_ball_split_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clark_defect_ball_split_uniform

end FormalResearch.ModularBootstrap.ConcreteBootstrap
