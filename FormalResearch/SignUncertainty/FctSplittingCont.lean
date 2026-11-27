/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSplittingConj

/-!
# Continuity of `Φ̂_c` on the closed strip and the corner bound `Φ̂_c = O(ζ³)` (`fct:splitting` (3))

Paper I (`constant_terms_five.tex`), `fct:splitting` (3) (`(fct:edge-factor)`, continuity of `Ψ_c`, `Φ_c`, `Φ̂_c` up to `Re ζ = 0`, and `Φ̂_c(0) = 0`).

The paper obtains continuity at the corner from the factorisation `(fct:edge-factor)` `Φ̂_c = ζ³ 𝔰_c`.  Here only the *bound* `|Φ̂_c| ≤ M |ζ|³` is needed, and it follows from
three elementary facts with no smoothness of `𝔰_c`:

* `‖Ψ_c(ζ)‖ ≤ M ‖ζ‖^{1/2}` (`fctPsi_near_zero`: `‖K₀A_ε(t)‖ ≲ ‖t‖^{-1/2}` integrated along `t = sζ`),
* `‖(H_*/G_ε)(ζ)‖⁻¹ ≲ ‖ζ‖^{5/2}` (`ctHG_inv_near_zero`: the numerator `Z_ε e^{-h}` of `H_*/G_ε` is zero-free on `0 ≤ Re ζ < 1/2`) and `D_{τ₁}` zero-free (it is an exponential),
* `|F_-(ζ)| ≤ K B ‖ζ‖³` (`fctCauchy_norm_le_cubic`: the factor `ζ³` of `K_sp`).

* `fctPsi_continuousOn`: `Ψ_c` continuous on `{0 ≤ Re ζ < 1, ζ ≠ 0}` (dominated convergence in the segment integral with the dominating function `s^{-1/2}`).
* `fctPhiC_continuousOn_left`, `fctPhiWarp_continuousOn`, `fctPhiHatAt_continuousOn`: continuity on `S̄`.
* `fctPhiHatAt_cubic`: `‖Φ̂_c(ζ)‖ ≤ M ‖ζ‖³` on `S̄ ∩ {‖ζ‖ ≤ 1}`.
* `fctPhiHat_cont_cubic`: both clauses for `fctPhiHat h`, from `FctDescentStmt h` (`K₄ ≥ 1`).

Class: proved from `FctDescentStmt` (named input).
-/
@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

section Psi

variable {K4 ε c L1 α : ℝ}

/-- A uniform corner bound `‖K₀A_ε(t)‖ ≤ C ‖t‖^{-1/2}` on `{0 ≤ Re t ≤ ρ, ‖t‖ ≤ R, t ≠ 0}` (`ρ < 1`): the corner bound `fctWarpKA_near_zero` near `0` and
continuity on the compact remainder. -/
lemma fctWarpKA_bound_loc (hc : 0 < c) (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B) {ρ R : ℝ} (hρ : ρ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℂ, 0 ≤ t.re → t.re ≤ ρ → ‖t‖ ≤ R → t ≠ 0 →
      ‖fctWarpKA K4 ε c L1 α t‖ ≤ C * ‖t‖ ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨r, M, hr, hM, hnear⟩ := fctWarpKA_near_zero (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDb
  set K : Set ℂ := (({t : ℂ | 0 ≤ t.re} ∩ {t : ℂ | t.re ≤ ρ}) ∩ Metric.closedBall (0 : ℂ) R) ∩ {t : ℂ | r ≤ ‖t‖} with hK
  have hKcl : IsClosed K :=
    (((isClosed_le continuous_const Complex.continuous_re).inter (isClosed_le Complex.continuous_re continuous_const)).inter
      Metric.isClosed_closedBall).inter (isClosed_le continuous_const continuous_norm)
  have hKc : IsCompact K :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hKcl (fun t ht => ht.1.2)
  have hcont : ContinuousOn (fctWarpKA K4 ε c L1 α) K :=
    (fctWarpKA_continuousOn hc hDc).mono fun t ht =>
      ⟨ht.1.1.1, by linarith [(show t.re ≤ ρ from ht.1.1.2)], fun h => by have := ht.2; rw [h] at this; simp at this; linarith⟩
  obtain ⟨B1, hB1⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨max M (|B1| * R ^ (1 / 2 : ℝ)), le_max_of_le_left hM, fun t h0 h1 h2 ht => ?_⟩
  have htn : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hp : 0 ≤ ‖t‖ ^ (-(1 / 2 : ℝ)) := by positivity
  by_cases hb : ‖t‖ ≤ r
  · exact (hnear t h0 (by linarith) ht hb).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
  · have hrt : r ≤ ‖t‖ := (not_le.mp hb).le
    have hmem : t ∈ K := ⟨⟨⟨h0, h1⟩, by simpa using h2⟩, hrt⟩
    refine (hB1 t hmem).trans ?_
    have hle : ‖t‖ ^ (1 / 2 : ℝ) ≤ R ^ (1 / 2 : ℝ) := Real.rpow_le_rpow htn.le h2 (by norm_num)
    have hq : 0 < ‖t‖ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos htn _
    rw [Real.rpow_neg htn.le]
    have h3 : (1 : ℝ) ≤ R ^ (1 / 2 : ℝ) * (‖t‖ ^ (1 / 2 : ℝ))⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hq]; linarith
    calc B1 ≤ |B1| := le_abs_self _
      _ ≤ |B1| * (R ^ (1 / 2 : ℝ) * (‖t‖ ^ (1 / 2 : ℝ))⁻¹) := by nlinarith [abs_nonneg B1]
      _ = |B1| * R ^ (1 / 2 : ℝ) * (‖t‖ ^ (1 / 2 : ℝ))⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- The set `{0 ≤ Re ζ < 1, ζ ≠ 0}` on which `Ψ_c` is continuous. -/
def psiDom : Set ℂ := {t : ℂ | 0 ≤ t.re ∧ t.re < 1 ∧ t ≠ 0}

lemma smul_mem_psiDom {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) {ζ : ℂ} (hζ : ζ ∈ psiDom) : (s : ℂ) * ζ ∈ psiDom := by
  obtain ⟨h0, h1, h2⟩ := hζ
  refine ⟨?_, ?_, mul_ne_zero (Complex.ofReal_ne_zero.mpr hs0.ne') h2⟩
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]; positivity
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]; nlinarith

/-- **Continuity of the segment integral of `Ψ_c` up to the left edge** (`ζ ≠ 0`): dominated convergence with the dominating function `C s^{-1/2}`. -/
lemma fctPsi_integral_continuousOn (hc : 0 < c) (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B) :
    ContinuousOn (fun ζ : ℂ => ∫ s in (0 : ℝ)..1, fctWarpKA K4 ε c L1 α ((s : ℂ) * ζ)) psiDom := by
  intro ζ0 hζ0
  obtain ⟨h00, h01, h02⟩ := hζ0
  have hn0 : 0 < ‖ζ0‖ := norm_pos_iff.mpr h02
  obtain ⟨C, hC0, hC⟩ := fctWarpKA_bound_loc (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDc hDb
    (ρ := (1 + ζ0.re) / 2) (R := ‖ζ0‖ + 1) (by linarith)
  have hKA := fctWarpKA_continuousOn (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDc
  have hev : ∀ᶠ ζ in 𝓝[psiDom] ζ0, ‖ζ0‖ / 2 < ‖ζ‖ ∧ ‖ζ‖ < ‖ζ0‖ + 1 ∧ ζ.re < (1 + ζ0.re) / 2 := by
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    have h1 : ∀ᶠ ζ in 𝓝 ζ0, ‖ζ0‖ / 2 < ‖ζ‖ :=
      (continuous_norm.continuousAt.eventually (lt_mem_nhds (by linarith : ‖ζ0‖ / 2 < ‖ζ0‖)))
    have h2 : ∀ᶠ ζ in 𝓝 ζ0, ‖ζ‖ < ‖ζ0‖ + 1 :=
      (continuous_norm.continuousAt.eventually (gt_mem_nhds (by linarith : ‖ζ0‖ < ‖ζ0‖ + 1)))
    have h3 : ∀ᶠ ζ in 𝓝 ζ0, ζ.re < (1 + ζ0.re) / 2 :=
      (Complex.continuous_re.continuousAt.eventually (gt_mem_nhds (by linarith : ζ0.re < (1 + ζ0.re) / 2)))
    filter_upwards [h1, h2, h3] with ζ a b c using ⟨a, b, c⟩
  set C' : ℝ := C * (‖ζ0‖ / 2) ^ (-(1 / 2 : ℝ)) with hC'
  refine intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun s => C' * s ^ (-(1 / 2 : ℝ))) ?_ ?_ ?_ ?_
  · refine eventually_nhdsWithin_of_forall fun ζ hζ => ?_
    rw [Set.uIoc_of_le zero_le_one]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    exact hKA.comp (by fun_prop : Continuous fun s : ℝ => (s : ℂ) * ζ).continuousOn
      (fun s hs => smul_mem_psiDom hs.1 hs.2 hζ)
  · filter_upwards [hev, self_mem_nhdsWithin] with ζ ⟨a, b, d⟩ hζ
    refine Filter.Eventually.of_forall fun s hs => ?_
    rw [Set.uIoc_of_le zero_le_one] at hs
    obtain ⟨hs0, hs1⟩ := hs
    have hζ0' : 0 ≤ ζ.re := hζ.1
    have hsn : ‖(s : ℂ) * ζ‖ = s * ‖ζ‖ := by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    have hre : ((s : ℂ) * ζ).re = s * ζ.re := by simp
    have hb := hC ((s : ℂ) * ζ) (by rw [hre]; positivity) (by rw [hre]; nlinarith) (by rw [hsn]; nlinarith [norm_nonneg ζ])
      (smul_mem_psiDom hs0 hs1 hζ).2.2
    refine hb.trans ?_
    rw [hsn, Real.mul_rpow hs0.le (norm_nonneg ζ)]
    have h1 : ‖ζ‖ ^ (-(1 / 2 : ℝ)) ≤ (‖ζ0‖ / 2) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) a.le (by norm_num)
    have h2 : 0 ≤ s ^ (-(1 / 2 : ℝ)) := by positivity
    calc C * (s ^ (-(1 / 2 : ℝ)) * ‖ζ‖ ^ (-(1 / 2 : ℝ))) = C * s ^ (-(1 / 2 : ℝ)) * ‖ζ‖ ^ (-(1 / 2 : ℝ)) := by ring
      _ ≤ C * s ^ (-(1 / 2 : ℝ)) * (‖ζ0‖ / 2) ^ (-(1 / 2 : ℝ)) := by gcongr
      _ = _ := by rw [hC']; ring
  · exact (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul C'
  · refine Filter.Eventually.of_forall fun s hs => ?_
    rw [Set.uIoc_of_le zero_le_one] at hs
    exact (hKA (s * ζ0) (smul_mem_psiDom hs.1 hs.2 ⟨h00, h01, h02⟩)).comp
      (by fun_prop : Continuous fun ζ : ℂ => (s : ℂ) * ζ).continuousWithinAt
      (fun ζ hζ => smul_mem_psiDom hs.1 hs.2 hζ)

/-- **`Ψ_c` is continuous on `{0 ≤ Re ζ < 1, ζ ≠ 0}`** (up to the left edge). -/
theorem fctPsi_continuousOn (hc : 0 < c) (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B) :
    ContinuousOn (fctPsi K4 ε c L1 α) psiDom := by
  have hK0 : ContinuousOn (fun ζ : ℂ => mellinK0 c ζ (fctXi1 L1)) psiDom :=
    (differentiableOn_mellinK0 hc _).continuousOn.mono fun t ht => by
      show |t.re| < 1
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2.1]
  unfold fctPsi
  exact (hK0.inv₀ fun t ht => mellinK0_ne_zero c ht.2.1 _).mul
    (continuousOn_id.mul (fctPsi_integral_continuousOn (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDc hDb))

/-- **Corner bound for `Ψ_c`**: `‖Ψ_c(ζ)‖ ≤ M ‖ζ‖^{1/2}` for `0 ≤ Re ζ < 1`, `ζ ≠ 0`, `‖ζ‖ ≤ r` (integrate `‖K₀A_ε(sζ)‖ ≲ (s‖ζ‖)^{-1/2}`). -/
lemma fctPsi_near_zero (hc : 0 < c) (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧ ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re < 1 → ζ ≠ 0 → ‖ζ‖ ≤ r →
      ‖fctPsi K4 ε c L1 α ζ‖ ≤ M * ‖ζ‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨r0, M1, hr0, hM1, hnear⟩ := fctWarpKA_near_zero (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDb
  have hball : ∀ t : ℂ, ‖t‖ ≤ 1 / 2 → |t.re| < 1 := fun t ht => by
    have : |t.re| ≤ ‖t‖ := Complex.abs_re_le_norm t
    linarith
  have hK0c : ContinuousOn (fun ζ : ℂ => (mellinK0 c ζ (fctXi1 L1))⁻¹) (Metric.closedBall (0 : ℂ) (1 / 2)) :=
    ((differentiableOn_mellinK0 hc _).continuousOn.mono fun t ht => hball t (by simpa using ht)).inv₀
      fun t ht => mellinK0_ne_zero c (by have := hball t (by simpa using ht); rw [abs_lt] at this; exact this.2) _
  obtain ⟨B0, hB0⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn hK0c
  refine ⟨min r0 (1 / 2), 2 * |B0| * M1, lt_min hr0 (by norm_num), by positivity, fun ζ h0 h1 hζ hr => ?_⟩
  have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  have hr1 : ‖ζ‖ ≤ r0 := hr.trans (min_le_left _ _)
  have hr2 : ‖ζ‖ ≤ 1 / 2 := hr.trans (min_le_right _ _)
  have hint : ‖∫ s in (0 : ℝ)..1, mellinK0 c ((s : ℂ) * ζ) (fctXi1 L1) * fctWarpA K4 ε c L1 α ((s : ℂ) * ζ)‖ ≤
      M1 * ‖ζ‖ ^ (-(1 / 2 : ℝ)) * 2 := by
    have := intervalIntegral.norm_integral_le_of_norm_le (a := 0) (b := 1) (zero_le_one)
      (f := fun s : ℝ => mellinK0 c ((s : ℂ) * ζ) (fctXi1 L1) * fctWarpA K4 ε c L1 α ((s : ℂ) * ζ))
      (g := fun s : ℝ => M1 * ‖ζ‖ ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ))) ?_
      ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul _)
    · refine this.trans (le_of_eq ?_)
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
      norm_num
    · refine Filter.Eventually.of_forall fun s hs => ?_
      obtain ⟨hs0, hs1⟩ := hs
      have hsn : ‖(s : ℂ) * ζ‖ = s * ‖ζ‖ := by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
      have hre : ((s : ℂ) * ζ).re = s * ζ.re := by simp
      have hb := hnear ((s : ℂ) * ζ) (by rw [hre]; positivity) (by rw [hre]; nlinarith)
        (mul_ne_zero (Complex.ofReal_ne_zero.mpr hs0.ne') hζ) (by rw [hsn]; nlinarith)
      refine hb.trans (le_of_eq ?_)
      rw [hsn, Real.mul_rpow hs0.le hn.le]; ring
  have hK0b : ‖(mellinK0 c ζ (fctXi1 L1))⁻¹‖ ≤ |B0| :=
    (hB0 ζ (by simpa using hr2)).trans (le_abs_self _)
  unfold fctPsi
  rw [norm_mul, norm_mul]
  have hp : ‖ζ‖ * ‖ζ‖ ^ (-(1 / 2 : ℝ)) = ‖ζ‖ ^ (1 / 2 : ℝ) := by
    have := Real.rpow_add hn 1 (-(1 / 2 : ℝ))
    rw [Real.rpow_one] at this
    rw [← this]; norm_num
  calc ‖(mellinK0 c ζ (fctXi1 L1))⁻¹‖ * (‖ζ‖ * ‖∫ s in (0 : ℝ)..1, mellinK0 c ((s : ℂ) * ζ) (fctXi1 L1) * fctWarpA K4 ε c L1 α ((s : ℂ) * ζ)‖)
      ≤ |B0| * (‖ζ‖ * (M1 * ‖ζ‖ ^ (-(1 / 2 : ℝ)) * 2)) := by gcongr
    _ = 2 * |B0| * M1 * ‖ζ‖ ^ (1 / 2 : ℝ) := by rw [← hp]; ring

end Psi

/-- A function vanishing at `0` with `‖f ζ‖ ≤ M ‖ζ‖³` near `0` on `s` is continuous within `s` at `0`. -/
lemma continuousWithinAt_zero_of_cubic {f : ℂ → ℂ} {s : Set ℂ} (h0 : f 0 = 0) {r M : ℝ} (hr : 0 < r)
    (hb : ∀ ζ ∈ s, ‖ζ‖ ≤ r → ‖f ζ‖ ≤ M * ‖ζ‖ ^ 3) : ContinuousWithinAt f s 0 := by
  unfold ContinuousWithinAt
  rw [h0]
  refine squeeze_zero_norm' (a := fun ζ : ℂ => M * ‖ζ‖ ^ 3) ?_ ?_
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Metric.closedBall_mem_nhds (0 : ℂ) hr), self_mem_nhdsWithin]
      with ζ h1 h2 using hb ζ h2 (by simpa using h1)
  · have : Tendsto (fun ζ : ℂ => M * ‖ζ‖ ^ 3) (𝓝 0) (𝓝 (M * ‖(0 : ℂ)‖ ^ 3)) :=
      ((continuous_const.mul (continuous_norm.pow 3)).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds

section PhiC

variable {K4 ε c L1 α : ℝ}

/-- `D_{τ₁} = exp g_D` is zero-free. -/
lemma fctDcompAt_ne_zero (ζ : ℂ) : fctDcompAt K4 c α ζ ≠ 0 := Complex.exp_ne_zero _

/-- **`(H_*/G_ε)⁻¹ = O(‖ζ‖^{5/2})` at the corner**: `Z_ε e^{-h}` is zero-free and continuous on `S̄ ∩ {‖ζ‖ ≤ 1/4}`. -/
lemma ctHG_inv_near_zero (ε : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ ζ ∈ closedStrip, ζ ≠ 0 → ‖ζ‖ ≤ 1 / 4 →
    ‖(ctHG ε ζ)⁻¹‖ ≤ M * ‖ζ‖ ^ (5 / 2 : ℝ) := by
  have hZ : ContinuousOn (uctSeedZ ε) closedStrip :=
    (differentiableOn_uctSeedZ ε).continuousOn.mono fun ζ (hζ : ζ ∈ closedStrip) =>
      (⟨by linarith [hζ.1], by linarith [hζ.2]⟩ : -1 < ζ.re ∧ ζ.re < 2)
  have hH : ContinuousOn outerHbar closedStrip := continuousOn_outerHbar
  have hcl : IsClosed closedStrip :=
    (isClosed_le continuous_const Complex.continuous_re).inter (isClosed_le Complex.continuous_re continuous_const)
  set K : Set ℂ := closedStrip ∩ Metric.closedBall (0 : ℂ) (1 / 4) with hK
  have hKc : IsCompact K := (isCompact_closedBall (0 : ℂ) (1 / 4)).inter_left hcl
  have hre : ∀ ζ ∈ K, 0 ≤ ζ.re ∧ ζ.re < 1 / 2 := fun ζ hζ => by
    have : ζ.re ≤ ‖ζ‖ := Complex.re_le_norm ζ
    have h2 : ‖ζ‖ ≤ 1 / 4 := by simpa using hζ.2
    exact ⟨hζ.1.1, by linarith⟩
  have hf : ContinuousOn (fun ζ => uctSeedZ ε ζ * Complex.exp (-outerHbar ζ)) K :=
    (hZ.mul hH.neg.cexp).mono Set.inter_subset_left
  have h1ζ : ∀ ζ ∈ K, 0 < ‖1 - ζ‖ := fun ζ hζ => by
    have h2 : ‖ζ‖ ≤ 1 / 4 := by simpa using hζ.2
    have := norm_sub_norm_le (1 : ℂ) ζ
    simp at this
    linarith
  have hg : ContinuousOn (fun ζ : ℂ => ‖1 - ζ‖ ^ (5 / 2 : ℝ) * ‖uctSeedZ ε ζ * Complex.exp (-outerHbar ζ)‖⁻¹) K := by
    refine ContinuousOn.mul ?_ (hf.norm.inv₀ fun ζ hζ => norm_ne_zero_iff.mpr
      (uctSeedZ_mul_exp_ne_zero ε (hre ζ hζ).1 (hre ζ hζ).2))
    exact ContinuousOn.rpow_const (continuous_norm.comp_continuousOn (continuousOn_const.sub continuousOn_id))
      fun ζ hζ => Or.inl (h1ζ ζ hζ).ne'
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hg
  refine ⟨|M|, abs_nonneg _, fun ζ hζ hζ0 hb => ?_⟩
  have hmem : ζ ∈ K := ⟨hζ, by simpa using hb⟩
  have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
  have h1ne : 1 - ζ ≠ 0 := norm_pos_iff.mp (h1ζ ζ hmem)
  rw [norm_inv, ctHG_norm_eq ε hζ0 h1ne, inv_div]
  have := hM ζ hmem
  rw [Real.norm_of_nonneg (by positivity)] at this
  calc ‖ζ‖ ^ (5 / 2 : ℝ) * ‖1 - ζ‖ ^ (5 / 2 : ℝ) / ‖uctSeedZ ε ζ * Complex.exp (-outerHbar ζ)‖
      = ‖ζ‖ ^ (5 / 2 : ℝ) * (‖1 - ζ‖ ^ (5 / 2 : ℝ) * ‖uctSeedZ ε ζ * Complex.exp (-outerHbar ζ)‖⁻¹) := by ring
    _ ≤ ‖ζ‖ ^ (5 / 2 : ℝ) * |M| := by
        gcongr
        exact this.trans (le_abs_self _)
    _ = _ := by ring

lemma fctPhiC_zero : fctPhiC K4 ε c L1 α 0 = 0 := by simp [fctPhiC, fctPsi]

/-- **`Φ_c = O(‖ζ‖³)` at the corner** (`fct:splitting` (3), `Φ_c = ζ³ c 𝔟_c/(η D_{τ₁})`, here without smoothness):
`‖Ψ_c‖ ≲ ‖ζ‖^{1/2}`, `‖(H_*/G_ε)⁻¹‖ ≲ ‖ζ‖^{5/2}`, `D_{τ₁}⁻¹` bounded. -/
lemma fctPhiC_near_zero (hc : 0 < c) (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧ ∀ ζ ∈ closedStrip, ‖ζ‖ ≤ r → ‖fctPhiC K4 ε c L1 α ζ‖ ≤ M * ‖ζ‖ ^ 3 := by
  obtain ⟨r0, MΨ, hr0, hMΨ, hΨ⟩ := fctPsi_near_zero (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDb
  obtain ⟨MH, hMH, hH⟩ := ctHG_inv_near_zero ε
  have hcl : IsClosed closedStrip :=
    (isClosed_le continuous_const Complex.continuous_re).inter (isClosed_le Complex.continuous_re continuous_const)
  have hKc : IsCompact (closedStrip ∩ Metric.closedBall (0 : ℂ) (1 / 4)) :=
    (isCompact_closedBall (0 : ℂ) (1 / 4)).inter_left hcl
  obtain ⟨MD, hMD⟩ := hKc.exists_bound_of_continuousOn
    ((hDc.inv₀ fun ζ _ => fctDcompAt_ne_zero ζ).mono (Set.inter_subset_left (t := Metric.closedBall (0 : ℂ) (1 / 4))))
  refine ⟨min r0 (1 / 4), c * MΨ * |MD| * MH, lt_min hr0 (by norm_num), by positivity, fun ζ hζ hr => ?_⟩
  by_cases hz : ζ = 0
  · subst hz; simp [fctPhiC_zero]
  have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr hz
  have hr1 : ‖ζ‖ ≤ r0 := hr.trans (min_le_left _ _)
  have hr2 : ‖ζ‖ ≤ 1 / 4 := hr.trans (min_le_right _ _)
  have hre : ζ.re < 1 := by have := Complex.re_le_norm ζ; linarith
  have h1 := hΨ ζ hζ.1 hre hz hr1
  have h2 := hH ζ hζ hz hr2
  have h3 : ‖(fctDcompAt K4 c α ζ)⁻¹‖ ≤ |MD| := (hMD ζ ⟨hζ, by simpa using hr2⟩).trans (le_abs_self _)
  have hp : ‖ζ‖ ^ (1 / 2 : ℝ) * ‖ζ‖ ^ (5 / 2 : ℝ) = ‖ζ‖ ^ 3 := by
    rw [← Real.rpow_add hn]; norm_num
  unfold fctPhiC
  rw [div_eq_mul_inv, mul_inv, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
  calc c * ‖fctPsi K4 ε c L1 α ζ‖ * (‖(fctDcompAt K4 c α ζ)⁻¹‖ * ‖(ctHG ε ζ)⁻¹‖)
      ≤ c * (MΨ * ‖ζ‖ ^ (1 / 2 : ℝ)) * (|MD| * (MH * ‖ζ‖ ^ (5 / 2 : ℝ))) := by gcongr
    _ = c * MΨ * |MD| * MH * (‖ζ‖ ^ (1 / 2 : ℝ) * ‖ζ‖ ^ (5 / 2 : ℝ)) := by ring
    _ = _ := by rw [hp]

/-- **`Φ_c` is continuous on `S̄ ∩ {Re ζ < 7/16}`** (`fct:splitting` (3), `Φ_c(0) = 0`). -/
theorem fctPhiC_continuousOn_left (hc : 0 < c) (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B) :
    ContinuousOn (fctPhiC K4 ε c L1 α) {ζ : ℂ | ζ ∈ closedStrip ∧ ζ.re < 7 / 16} := by
  obtain ⟨r, M, hr, hM, hb⟩ := fctPhiC_near_zero (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDc hDb
  intro ζ hζ
  by_cases hz : ζ = 0
  · subst hz
    exact continuousWithinAt_zero_of_cubic fctPhiC_zero hr (fun ζ hζ hn => hb ζ hζ.1 hn)
  have hs : ContinuousOn (fctPhiC K4 ε c L1 α) {ζ : ℂ | ζ ∈ closedStrip ∧ ζ.re < 7 / 16 ∧ ζ ≠ 0} := by
    have hpsi := fctPsi_continuousOn (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDc hDb
    have hpsi' : ContinuousOn (fctPsi K4 ε c L1 α) {ζ : ℂ | ζ ∈ closedStrip ∧ ζ.re < 7 / 16 ∧ ζ ≠ 0} :=
      hpsi.mono fun t (ht : t ∈ {ζ : ℂ | ζ ∈ closedStrip ∧ ζ.re < 7 / 16 ∧ ζ ≠ 0}) =>
        (⟨ht.1.1, by linarith [ht.2.1], ht.2.2⟩ : 0 ≤ t.re ∧ t.re < 1 ∧ t ≠ 0)
    have hD' : ContinuousOn (fctDcompAt K4 c α) {ζ : ℂ | ζ ∈ closedStrip ∧ ζ.re < 7 / 16 ∧ ζ ≠ 0} :=
      hDc.mono fun t (ht : t ∈ {ζ : ℂ | ζ ∈ closedStrip ∧ ζ.re < 7 / 16 ∧ ζ ≠ 0}) => ht.1
    have hH' : ContinuousOn (ctHG ε) {ζ : ℂ | ζ ∈ closedStrip ∧ ζ.re < 7 / 16 ∧ ζ ≠ 0} :=
      (ctHG_continuousOn ε).mono fun t (ht : t ∈ {ζ : ℂ | ζ ∈ closedStrip ∧ ζ.re < 7 / 16 ∧ ζ ≠ 0}) =>
        (⟨ht.1, ht.2.2, fun h => by have := ht.2.1; rw [h] at this; simp at this; linarith⟩ :
          t ∈ closedStrip ∧ t ≠ 0 ∧ t ≠ 1)
    refine (continuousOn_const.mul hpsi').div (hD'.mul hH') fun t ht => ?_
    exact mul_ne_zero (fctDcompAt_ne_zero t) (ctHG_ne_zero_of_closed_band ε ht.1.1 (by linarith [ht.2.1]) ht.2.2)
  have hnhds : {ζ : ℂ | ζ ∈ closedStrip ∧ ζ.re < 7 / 16 ∧ ζ ≠ 0} ∈ 𝓝[{ζ : ℂ | ζ ∈ closedStrip ∧ ζ.re < 7 / 16}] ζ := by
    have : ∀ᶠ w in 𝓝 ζ, w ≠ 0 := isOpen_ne.mem_nhds hz
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds this] with w h1 h2 using ⟨h1.1, h1.2, h2⟩
  exact (hs ζ ⟨hζ.1, hζ.2, hz⟩).mono_of_mem_nhdsWithin hnhds

end PhiC

section Hat

variable {K4 ε c L1 α B : ℝ}

/-- **`Φ^warp_c` is continuous on `S̄`** (`fct:splitting` (3)): on `Re ζ < 7/16` it is `Φ_c - F_-` (`Φ_c` continuous up to the left edge, `F_-` holomorphic across it),
on `Re ζ > 0` it is holomorphic. -/
theorem fctPhiWarp_continuousOn (hc : 0 < c) (hDh : DifferentiableOn ℂ (fctDcompAt K4 c α) strip)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B)
    (hF : ∀ σ y : ℝ, 3 / 8 ≤ σ → σ ≤ 7 / 16 → ‖fctFint K4 ε c L1 α ((σ : ℂ) + y * Complex.I)‖ ≤ B) :
    ContinuousOn (fctPhiWarp K4 ε c L1 α) closedStrip := by
  have hU : IsOpen {ζ : ℂ | -1 < ζ.re ∧ ζ.re < 7 / 16} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
  have hC7 := (fctCauchy_differentiableOn (ε := ε) (L1 := L1) (α := α) hc hDc (σ := 7 / 16) (by norm_num) le_rfl
    (fun y => hF _ y (by norm_num) le_rfl) hU (fun w (hw : -1 < w.re ∧ w.re < 7 / 16) => ⟨hw.1, hw.2.ne⟩)).continuousOn
  have hA : ContinuousOn (fctPhiWarp K4 ε c L1 α) {ζ : ℂ | ζ ∈ closedStrip ∧ ζ.re < 7 / 16} := by
    have : ContinuousOn (fun ζ => fctPhiC K4 ε c L1 α ζ - fctCauchy K4 ε c L1 α (7 / 16) ζ)
        {ζ : ℂ | ζ ∈ closedStrip ∧ ζ.re < 7 / 16} :=
      (fctPhiC_continuousOn_left hc hDc hDb).sub
        (hC7.mono fun t (ht : t ∈ {ζ : ℂ | ζ ∈ closedStrip ∧ ζ.re < 7 / 16}) => (⟨by linarith [ht.1.1], ht.2⟩ : -1 < t.re ∧ t.re < 7 / 16))
    refine this.congr fun ζ hζ => ?_
    simp only [fctPhiWarp, hζ.2, ↓reduceIte]
  have hhol := fctPhiWarp_differentiableOn hc hDh hDc hDb hF
  intro ζ hζ
  by_cases hlt : ζ.re < 7 / 16
  · refine (hA ζ ⟨hζ, hlt⟩).mono_of_mem_nhdsWithin ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds hlt)] with w h1 h2 using ⟨h1, h2⟩
  · have hpos : 0 < ζ.re := by have := not_lt.mp hlt; linarith
    exact ((hhol.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hpos)).continuousAt).continuousWithinAt

/-- `q₁` is continuous on `S̄`. -/
lemma fctQ1_continuousOn : ContinuousOn fctQ1 closedStrip := by
  intro ζ hζ
  have : ζ + 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith [hζ.1]
  unfold fctQ1
  refine ContinuousAt.continuousWithinAt ?_
  exact (DifferentiableAt.continuousAt (by fun_prop (disch := exact pow_ne_zero 4 this)))

/-- **`Φ̂_c` is continuous on the closed strip `S̄`** (the `cont` clause of `SplittingData`; the corner `ζ = 0` is covered by `fctPhiC_near_zero`). -/
theorem fctPhiHatAt_continuousOn (hc : 0 < c) (hDh : DifferentiableOn ℂ (fctDcompAt K4 c α) strip)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B)
    (hF : ∀ σ y : ℝ, 3 / 8 ≤ σ → σ ≤ 7 / 16 → ‖fctFint K4 ε c L1 α ((σ : ℂ) + y * Complex.I)‖ ≤ B) :
    ContinuousOn (fctPhiHatAt K4 ε c L1 α) closedStrip := by
  unfold fctPhiHatAt
  exact ((fctPhiWarp_continuousOn hc hDh hDc hDb hF).div_const _).add (continuousOn_const.mul fctQ1_continuousOn)

/-- `q₁ = ζ³ · 16(1-ζ)/(ζ+1)⁴`, so `‖q₁(ζ)‖ ≤ M ‖ζ‖³` on `S̄ ∩ {‖ζ‖ ≤ 1/4}`. -/
lemma fctQ1_cubic : ∃ M : ℝ, 0 ≤ M ∧ ∀ ζ ∈ closedStrip, ‖ζ‖ ≤ 1 / 4 → ‖fctQ1 ζ‖ ≤ M * ‖ζ‖ ^ 3 := by
  have hcl : IsClosed closedStrip :=
    (isClosed_le continuous_const Complex.continuous_re).inter (isClosed_le Complex.continuous_re continuous_const)
  have hKc : IsCompact (closedStrip ∩ Metric.closedBall (0 : ℂ) (1 / 4)) :=
    (isCompact_closedBall (0 : ℂ) (1 / 4)).inter_left hcl
  have hne : ∀ ζ ∈ closedStrip, ζ + 1 ≠ 0 := fun ζ hζ h => by
    have := congrArg Complex.re h; simp at this; linarith [hζ.1]
  have hg : ContinuousOn (fun ζ : ℂ => 16 * (1 - ζ) / (ζ + 1) ^ 4) (closedStrip ∩ Metric.closedBall (0 : ℂ) (1 / 4)) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun ζ hζ => pow_ne_zero 4 (hne ζ hζ.1)
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hg
  refine ⟨|M|, abs_nonneg _, fun ζ hζ hb => ?_⟩
  have := hM ζ ⟨hζ, by simpa using hb⟩
  have e : fctQ1 ζ = ζ ^ 3 * (16 * (1 - ζ) / (ζ + 1) ^ 4) := by unfold fctQ1; ring
  rw [e, norm_mul, norm_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (this.trans (le_abs_self _)) (by positivity)

/-- **`Φ̂_c = O(‖ζ‖³)` on `S̄ ∩ {‖ζ‖ ≤ 1}`** (`(fct:edge-factor)`, the corner bound of `SplittingData`): near `0` from `Φ_c = O(ζ³)`, `F_- = O(ζ³)`, `q₁ = O(ζ³)`; on the rest of the
compact set `S̄ ∩ {‖ζ‖ ≤ 1}` from continuity. -/
theorem fctPhiHatAt_cubic (hc : 0 < c) (hDh : DifferentiableOn ℂ (fctDcompAt K4 c α) strip)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B)
    (hF : ∀ σ y : ℝ, 3 / 8 ≤ σ → σ ≤ 7 / 16 → ‖fctFint K4 ε c L1 α ((σ : ℂ) + y * Complex.I)‖ ≤ B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ζ ∈ closedStrip, ‖ζ‖ ≤ 1 → ‖fctPhiHatAt K4 ε c L1 α ζ‖ ≤ M * ‖ζ‖ ^ 3 := by
  obtain ⟨r, MΦ, hr, hMΦ, hΦ⟩ := fctPhiC_near_zero (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDc hDb
  obtain ⟨KC, hKC0, hKC⟩ := fctCauchy_norm_le_cubic (σ := 7 / 16) (by norm_num) le_rfl
  obtain ⟨MQ, hMQ0, hMQ⟩ := fctQ1_cubic
  have hB : 0 ≤ B := (norm_nonneg _).trans (hF (3 / 8) 0 le_rfl (by norm_num))
  have hFl : ∀ y : ℝ, ‖fctFint K4 ε c L1 α (((7 / 16 : ℝ) : ℂ) + y * Complex.I)‖ ≤ B := fun y => hF _ y (by norm_num) le_rfl
  set r1 : ℝ := min r (1 / 4) with hr1
  have hr1pos : 0 < r1 := lt_min hr (by norm_num)
  set M0 : ℝ := ‖(fctNcC K4 ε c L1 α)⁻¹‖ * (MΦ + KC * B) + ‖fctBetaC K4 ε c L1 α‖ * MQ with hM0
  have hM0nn : 0 ≤ M0 := by positivity
  have hnear : ∀ ζ ∈ closedStrip, ‖ζ‖ ≤ r1 → ‖fctPhiHatAt K4 ε c L1 α ζ‖ ≤ M0 * ‖ζ‖ ^ 3 := by
    intro ζ hζ hb
    have hb1 : ‖ζ‖ ≤ r := hb.trans (min_le_left _ _)
    have hb2 : ‖ζ‖ ≤ 1 / 4 := hb.trans (min_le_right _ _)
    have hre : ζ.re < 7 / 16 := by have := Complex.re_le_norm ζ; linarith
    have hW : fctPhiWarp K4 ε c L1 α ζ = fctPhiC K4 ε c L1 α ζ - fctCauchy K4 ε c L1 α (7 / 16) ζ := by
      simp only [fctPhiWarp, hre, ↓reduceIte]
    have h1 := hΦ ζ hζ hb1
    have h2 := hKC K4 ε c L1 α B hB hFl ζ hb2
    have h3 := hMQ ζ hζ hb2
    have h2' : ‖fctCauchy K4 ε c L1 α (7 / 16) ζ‖ ≤ KC * B * ‖ζ‖ ^ 3 := by simpa using h2
    unfold fctPhiHatAt
    refine (norm_add_le _ _).trans ?_
    rw [div_eq_mul_inv, norm_mul, norm_mul, hW]
    have h4 : ‖fctPhiC K4 ε c L1 α ζ - fctCauchy K4 ε c L1 α (7 / 16) ζ‖ ≤ (MΦ + KC * B) * ‖ζ‖ ^ 3 :=
      (norm_sub_le _ _).trans (by nlinarith [h1, h2'])
    calc ‖fctPhiC K4 ε c L1 α ζ - fctCauchy K4 ε c L1 α (7 / 16) ζ‖ * ‖(fctNcC K4 ε c L1 α)⁻¹‖ +
          ‖fctBetaC K4 ε c L1 α‖ * ‖fctQ1 ζ‖
        ≤ (MΦ + KC * B) * ‖ζ‖ ^ 3 * ‖(fctNcC K4 ε c L1 α)⁻¹‖ + ‖fctBetaC K4 ε c L1 α‖ * (MQ * ‖ζ‖ ^ 3) := by gcongr
      _ = _ := by rw [hM0]; ring
  have hcl : IsClosed closedStrip :=
    (isClosed_le continuous_const Complex.continuous_re).inter (isClosed_le Complex.continuous_re continuous_const)
  have hKc : IsCompact (closedStrip ∩ Metric.closedBall (0 : ℂ) 1) := (isCompact_closedBall (0 : ℂ) 1).inter_left hcl
  obtain ⟨B1, hB1⟩ := hKc.exists_bound_of_continuousOn
    ((fctPhiHatAt_continuousOn hc hDh hDc hDb hF).mono (Set.inter_subset_left (t := Metric.closedBall (0 : ℂ) 1)))
  refine ⟨max M0 (|B1| / r1 ^ 3), le_max_of_le_left hM0nn, fun ζ hζ hb => ?_⟩
  by_cases hs : ‖ζ‖ ≤ r1
  · exact (hnear ζ hζ hs).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hrs : r1 ≤ ‖ζ‖ := (not_le.mp hs).le
    have h1 := hB1 ζ ⟨hζ, by simpa using hb⟩
    have h2 : r1 ^ 3 ≤ ‖ζ‖ ^ 3 := pow_le_pow_left₀ hr1pos.le hrs 3
    have h3 : 0 < r1 ^ 3 := by positivity
    refine h1.trans ((le_abs_self _).trans ?_)
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    rw [div_mul_eq_mul_div, le_div_iff₀ h3]
    nlinarith [abs_nonneg B1]

end Hat

/-- **Continuity of `Φ̂_c` on `S̄` and the corner bound `Φ̂_c = O(‖ζ‖³)`** (`fct:splitting` (3), the `cont` clause and the `O(ζ³)` clause of `SplittingData`), from the descent
bound `(fct:F-38-bnd)` (`K₄ ≥ 1`). -/
theorem fctPhiHat_cont_cubic {K4 : ℝ} (hK4 : 1 ≤ K4) {h : FctWarpSolveStmt K4} (hD : FctDescentStmt h) :
    ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ContinuousOn (fctPhiHat h ε c) closedStrip ∧
        ∃ M : ℝ, 0 ≤ M ∧ ∀ ζ ∈ closedStrip, ‖ζ‖ ≤ 1 → ‖fctPhiHat h ε c ζ‖ ≤ M * ‖ζ‖ ^ 3 := by
  obtain ⟨c₀, B, hB⟩ := fctSplitting_setup hK4 hD
  refine ⟨c₀, fun ε c hε hc => ?_⟩
  obtain ⟨hc0, hDh, hDc, hDb, hF, -⟩ := hB ε c hε hc
  exact ⟨fctPhiHatAt_continuousOn hc0 hDh hDc hDb hF, fctPhiHatAt_cubic hc0 hDh hDc hDb hF⟩

/-- info: 'FormalResearch.SignUncertainty.fctPhiHat_cont_cubic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctPhiHat_cont_cubic

/-- info: 'FormalResearch.SignUncertainty.fctPsi_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctPsi_continuousOn

end FormalResearch.SignUncertainty
