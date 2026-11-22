module

public import FormalResearch.ModularBootstrap.TipFront.ComplexPoissonJensen

/-!
# General-`δ` Version of Lemma G (`lower_o1_two_edge.tex`, Lemma `vlo:Gap`)

Proves the unconditional deep-lobe exponential suppression estimate for **every** cutoff
`x₀ ∈ [0, ξ_*)` (`δ = ξ_* - x₀ ∈ (0, ξ_*]`):

* `lemmaGap_of_lemmaPJInput_at`: for any real-slice data `rs` and majorant `U` obeying
  `(G-deficit)`, `LemmaPJInput rs c_PJ C_PJ U` implies exponential suppression on
  `[0, c' x₀² / 3]` for every `x₀ ∈ Ico 0 xiStar` with decay rate `κ = 1.114 * (ξ_* - x₀)^{3/2}`.
* `lemmaG_of_cut`: unconditional corollary for `virasoroProblem` (using
  `PoissonJensen.stripPoissonJensen` and `majorantReal_g_deficit`).
* `lemmaG_general_delta`: unconditional **Lemma G (`vlo:Gap`)** for every `δ ∈ Ioo 0 xiStar`
  (cutoff `x₀ = ξ_* - δ`).
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology
open scoped Interval

namespace FormalResearch.ModularBootstrap.TipFront

open PoissonJensen Crossing Integration

/-- **General-cutoff Lemma G from Lemma PJ (`vlo:Gap`)**: for any `x₀ ∈ [0, ξ_*)`, any
`rs` and `U` obeying `(G-deficit)` and `LemmaPJInput rs c_PJ C_PJ U`, there exist
`c_gap ≥ max c_PJ 24`, `C_gap > 0`, and `κ_gap = 1.114 * (xiStar - x₀)^{3/2} > 0`
giving exponential suppression on `[0, c' x₀² / 3]`. -/
theorem lemmaGap_of_lemmaPJInput_at (rs : RealSliceData) (U : ℝ → ℝ) {c_PJ C_PJ : ℝ}
    (hc_PJ : 1 ≤ c_PJ)
    (hdef : ∀ x ∈ Ico 0 xiStar, U x + (2 * π / 3) * x ≤ -slitDeficit (xiStar - x))
    (hPJ : LemmaPJInput rs c_PJ C_PJ U)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ico (0 : ℝ) xiStar) :
    ∃ c_gap C_gap κ_gap : ℝ, max c_PJ 24 ≤ c_gap ∧ 0 < C_gap ∧ 0 < κ_gap ∧
      ∀ {c' : ℝ}, c_gap ≤ c' → ∀ {g : ℝ → ℝ}, TestClass virasoroProblem (c' / 12) g →
        ∫ t in (0 : ℝ)..(c' * x₀ ^ 2 / 3), |g t| * virasoroProblem.cardyV (c' / 12) t ≤
          C_gap * Real.exp (-κ_gap * c') * virasoroProblem.cardyNorm (c' / 12) g := by
  obtain ⟨C_M1, C_M2, hCM1, hprop⟩ := proposition_M rs (C_PJ := C_PJ) hc_PJ
  set δ₀ : ℝ := xiStar - x₀ with hδ₀def
  have hδ₀ : 0 < δ₀ := sub_pos.mpr hx₀.2
  set κ₀ : ℝ := 2.228 * δ₀ ^ ((3 : ℝ) / 2) with hκ₀def
  have hκ₀ : 0 < κ₀ := by positivity
  obtain ⟨C₄, hC₄, hC₄le⟩ := exists_rpow_le_mul_exp (p := C_M1 + 1) (κ := κ₀ / 2) (by positivity)
  refine ⟨max c_PJ 24, (2 / δ₀) * Real.exp C_M2 * C₄, κ₀ / 2, le_rfl, ?_, by positivity, ?_⟩
  · have hC4_pos : 0 < C₄ := by
      have := hC₄le 1 le_rfl
      simp only [Real.one_rpow] at this
      have hexp_pos : 0 < Real.exp (κ₀ / 2 * 1) := Real.exp_pos _
      nlinarith
    positivity
  · intro c' hc' g hg
    have hc24 : (24 : ℝ) ≤ c' := (le_max_right _ _).trans hc'
    have hcPJ : c_PJ ≤ c' := (le_max_left _ _).trans hc'
    have hc1 : 1 ≤ c' := by linarith
    have hc0 : 0 < c' := by linarith
    have ha : (2 : ℝ) ≤ c' / 12 := by linarith
    have hshift : virasoroProblem.totalShift ≤ c' / 12 := by
      rw [virasoroProblem_totalShift]; exact ha
    have hMnn : 0 ≤ virasoroProblem.cardyNorm (c' / 12) g := virasoroProblem.cardyNorm_nonneg hshift g
    set M : ℝ := virasoroProblem.cardyNorm (c' / 12) g
    set t₀ : ℝ := c' * x₀ ^ 2 / 3 with ht₀
    have ht₀nn : 0 ≤ t₀ := by positivity
    have hrhs_nn : 0 ≤ (2 / δ₀) * Real.exp C_M2 * C₄ * Real.exp (-(κ₀ / 2) * c') * M := by
      positivity
    by_cases hz : ∃ t ≥ 0, g t ≠ 0
    swap
    · push Not at hz
      have : ∫ t in (0 : ℝ)..t₀, |g t| * virasoroProblem.cardyV (c' / 12) t = 0 := by
        rw [intervalIntegral.integral_of_le ht₀nn]
        refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
        rw [hz t ht.1.le]; simp
      rw [this]; exact hrhs_nn
    have hMpos : 0 < M := cardyNorm_pos_of_nonzero hshift hg hz
    have hbound := hprop hcPJ hMpos (fun x hx hne => hPJ hcPJ hg hMpos x hx hne)
    set B : ℝ := (2 / δ₀) * Real.exp C_M2 * c' ^ C_M1 * Real.exp (-κ₀ * c') * M with hB
    have hBnn : 0 ≤ B := by positivity
    have key : ∀ x ∈ Icc (0 : ℝ) x₀,
        |g (c' * x ^ 2 / 3)| * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) ≤ B := by
      intro x hx
      have hxξ : x ∈ Ico 0 xiStar := ⟨hx.1, lt_of_le_of_lt hx.2 hx₀.2⟩
      have hV0 : 0 ≤ virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) :=
        virasoroProblem.cardyV_nonneg hshift (by positivity)
      by_cases h0 : g (c' * x ^ 2 / 3) = 0
      · rw [h0, abs_zero, zero_mul]; exact hBnn
      have hlog := hbound x hxξ h0
      have hδx : δ₀ ≤ xiStar - x := by rw [hδ₀def]; linarith [hx.2]
      have hδxpos : 0 < xiStar - x := lt_of_lt_of_le hδ₀ hδx
      have hlogc : 0 ≤ Real.log c' := Real.log_nonneg hc1
      have hsqrt1 : Real.sqrt (xiStar - x) ≤ 1 := by
        rw [Real.sqrt_le_one]; linarith [xiStar_lt_one, hx.1]
      have hterm1 : C_M1 * Real.sqrt (xiStar - x) * Real.log c' ≤ C_M1 * Real.log c' := by
        have := mul_le_mul_of_nonneg_left hsqrt1 hCM1
        nlinarith [mul_le_mul_of_nonneg_right this hlogc]
      have hterm2 : Real.log (1 / (xiStar - x)) ≤ Real.log (1 / δ₀) :=
        Real.log_le_log (by positivity) (one_div_le_one_div_of_le hδ₀ hδx)
      have hlog' : Real.log |g (c' * x ^ 2 / 3)| ≤
          c' * U x + Real.log M + C_M1 * Real.log c' + Real.log (1 / δ₀) + C_M2 := by
        linarith
      have hg_le : |g (c' * x ^ 2 / 3)| ≤
          M * c' ^ C_M1 * (1 / δ₀) * Real.exp C_M2 * Real.exp (c' * U x) := by
        have := Real.exp_le_exp.mpr hlog'
        rw [Real.exp_log (abs_pos.mpr h0)] at this
        refine this.trans_eq ?_
        have hpow_c : Real.exp (C_M1 * Real.log c') = c' ^ C_M1 := by
          rw [Real.rpow_def_of_pos hc0, mul_comm]
        rw [show c' * U x + Real.log M + C_M1 * Real.log c' + Real.log (1 / δ₀) + C_M2 =
            (c' * U x) + Real.log M + (C_M1 * Real.log c') + Real.log (1 / δ₀) + C_M2 by ring,
          Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hMpos,
          Real.exp_log (by positivity), hpow_c]
        ring
      have hV_le : virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) ≤
          2 * Real.exp (c' * ((2 * π / 3) * x)) := by
        have h := cardyV_le_two_exp ha (t := c' * x ^ 2 / 3) (by positivity)
        have hsq : c' / 12 * (c' * x ^ 2 / 3) = (c' * x / 6) ^ 2 := by ring
        rw [hsq, Real.sqrt_sq (by have := hx.1; positivity)] at h
        have e : 4 * π * (c' * x / 6) = c' * ((2 * π / 3) * x) := by ring
        rwa [e] at h
      have hdef' : c' * U x + c' * ((2 * π / 3) * x) ≤ -(κ₀ * c') := by
        have h1 := hdef x hxξ
        have h2 := slitDeficit_ge (δ := xiStar - x) hδxpos.le (by linarith [hx.1])
        have h3 : δ₀ ^ ((3 : ℝ) / 2) ≤ (xiStar - x) ^ ((3 : ℝ) / 2) :=
          Real.rpow_le_rpow hδ₀.le hδx (by norm_num)
        have h4 : κ₀ ≤ slitDeficit (xiStar - x) := by
          refine le_trans ?_ h2
          rw [hκ₀def]; gcongr
        have h5 : U x + (2 * π / 3) * x ≤ -κ₀ := by linarith
        have := mul_le_mul_of_nonneg_left h5 hc0.le
        linarith
      calc |g (c' * x ^ 2 / 3)| * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3)
          ≤ (M * c' ^ C_M1 * (1 / δ₀) * Real.exp C_M2 * Real.exp (c' * U x)) *
              (2 * Real.exp (c' * ((2 * π / 3) * x))) := by gcongr
        _ = (2 / δ₀) * Real.exp C_M2 * c' ^ C_M1 * M *
              Real.exp (c' * U x + c' * ((2 * π / 3) * x)) := by rw [Real.exp_add]; ring
        _ ≤ (2 / δ₀) * Real.exp C_M2 * c' ^ C_M1 * M * Real.exp (-(κ₀ * c')) := by gcongr
        _ = B := by rw [hB, show -κ₀ * c' = -(κ₀ * c') by ring]; ring
    have hint : ‖∫ t in (0 : ℝ)..t₀, |g t| * virasoroProblem.cardyV (c' / 12) t‖ ≤ B * |t₀ - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
      rw [uIoc_of_le ht₀nn] at ht
      have hV0 : 0 ≤ virasoroProblem.cardyV (c' / 12) t :=
        virasoroProblem.cardyV_nonneg hshift ht.1.le
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hV0)]
      set x : ℝ := Real.sqrt (3 * t / c') with hx
      have hx2 : x ^ 2 = 3 * t / c' := Real.sq_sqrt (by have := ht.1; positivity)
      have htx : c' * x ^ 2 / 3 = t := by rw [hx2]; field_simp
      have hxle : x ≤ x₀ := by
        rw [hx, Real.sqrt_le_left hx₀.1, div_le_iff₀ hc0]
        have := ht.2; rw [ht₀] at this; nlinarith
      have := key x ⟨Real.sqrt_nonneg _, hxle⟩
      rwa [htx] at this
    have hle1 : |t₀ - 0| ≤ c' := by
      have hx₀_lt1 : x₀ < 1 := hx₀.2.trans xiStar_lt_one
      have hx₀_sq : x₀ ^ 2 ≤ 3 := by nlinarith [hx₀.1]
      rw [sub_zero, abs_of_nonneg ht₀nn, ht₀]
      nlinarith
    have hfin : B * c' ≤ (2 / δ₀) * Real.exp C_M2 * C₄ * Real.exp (-(κ₀ / 2) * c') * M := by
      have hc'pow : c' ^ C_M1 * c' ≤ C₄ * Real.exp (κ₀ / 2 * c') := by
        rw [← Real.rpow_add_one hc0.ne']; exact hC₄le c' hc1
      have e : B * c' = (2 / δ₀) * Real.exp C_M2 * (c' ^ C_M1 * c') * Real.exp (-κ₀ * c') * M := by
        rw [hB]; ring
      have e2 : (2 / δ₀) * Real.exp C_M2 * (c' ^ C_M1 * c') * Real.exp (-κ₀ * c') * M ≤
          (2 / δ₀) * Real.exp C_M2 * (C₄ * Real.exp (κ₀ / 2 * c')) * Real.exp (-κ₀ * c') * M := by
        gcongr
      have e3 : Real.exp (κ₀ / 2 * c') * Real.exp (-κ₀ * c') = Real.exp (-(κ₀ / 2) * c') := by
        rw [← Real.exp_add]; congr 1; ring
      calc B * c' = _ := e
        _ ≤ _ := e2
        _ = (2 / δ₀) * Real.exp C_M2 * C₄ *
              (Real.exp (κ₀ / 2 * c') * Real.exp (-κ₀ * c')) * M := by ring
        _ = _ := by rw [e3]
    calc ∫ t in (0 : ℝ)..t₀, |g t| * virasoroProblem.cardyV (c' / 12) t
        ≤ ‖∫ t in (0 : ℝ)..t₀, |g t| * virasoroProblem.cardyV (c' / 12) t‖ := le_abs_self _
      _ ≤ B * |t₀ - 0| := hint
      _ ≤ B * c' := by gcongr
      _ ≤ _ := hfin

/-- Unconditional **Lemma G** (`vlo:Gap`) for every cutoff `x₀ ∈ [0, ξ_*)`. -/
theorem lemmaG_of_cut {x₀ : ℝ} (hx₀ : x₀ ∈ Ico (0 : ℝ) xiStar) :
    ∃ c_gap C_gap κ_gap : ℝ, 24 ≤ c_gap ∧ 0 < C_gap ∧ 0 < κ_gap ∧
      ∀ {c' : ℝ}, c_gap ≤ c' → ∀ {g : ℝ → ℝ}, TestClass virasoroProblem (c' / 12) g →
        ∫ t in (0 : ℝ)..(c' * x₀ ^ 2 / 3), |g t| * virasoroProblem.cardyV (c' / 12) t ≤
          C_gap * Real.exp (-κ_gap * c') * virasoroProblem.cardyNorm (c' / 12) g := by
  obtain ⟨c_PJ, C_PJ, hc_PJ, hPJ⟩ := PoissonJensen.stripPoissonJensen
  obtain ⟨c_gap, C_gap, κ_gap, hc_max, hC, hκ, hbd⟩ :=
    lemmaGap_of_lemmaPJInput_at realSliceData majorantReal hc_PJ
      (fun _ hx => majorantReal_g_deficit hx) hPJ hx₀
  exact ⟨c_gap, C_gap, κ_gap, (le_max_right c_PJ 24).trans hc_max, hC, hκ, hbd⟩

/-- Unconditional general-`δ` **Lemma G** (`lower_o1_two_edge.tex`, Lemma `vlo:Gap`):
for every `δ ∈ (0, ξ_*)`, the deep-lobe mass on `[0, c' (ξ_* - δ)^2 / 3]` is exponentially
suppressed for `c' ≥ c_gap(δ)`. -/
theorem lemmaG_general_delta {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) xiStar) :
    ∃ c_gap C_gap κ_gap : ℝ, 24 ≤ c_gap ∧ 0 < C_gap ∧ 0 < κ_gap ∧
      ∀ {c' : ℝ}, c_gap ≤ c' → ∀ {g : ℝ → ℝ}, TestClass virasoroProblem (c' / 12) g →
        ∫ t in (0 : ℝ)..(c' * (xiStar - δ) ^ 2 / 3), |g t| * virasoroProblem.cardyV (c' / 12) t ≤
          C_gap * Real.exp (-κ_gap * c') * virasoroProblem.cardyNorm (c' / 12) g :=
  lemmaG_of_cut ⟨by linarith [hδ.2], by linarith [hδ.1]⟩

/--
info: 'FormalResearch.ModularBootstrap.TipFront.lemmaG_general_delta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms lemmaG_general_delta

end FormalResearch.ModularBootstrap.TipFront
