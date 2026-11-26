module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasFarField

/-!
# `ct:sigma-prime`: the Lipschitz bound of the Gaussian step `𝔰_far(Δ(L))`

`constant_terms_lower.tex`, proof of `ct:boas` Step 5 (e), `(ct:sigma-prime)`: `σ(L) = 1 - 𝔰_far(Δ(L))`, `Δ(L) = c e^L/π²`,
`∂_Lσ = -Δ 𝔰_far'(Δ)` with `𝔰_far' = G_{W_far}(· - Δ_far)`.  Derivative-free form used by `taper_hlip`
(`CtDyadicTaper`, hypothesis `hσ`):

* `sFar_eq_Iio`: `𝔰_far(Δ) = ∫_{y < Δ - D} G_W(y) dy`;
* `sFar_sub_le`: `0 ≤ 𝔰_far(Δ) - 𝔰_far(Δ') ≤ g (Δ - Δ')` for `Δ' ≤ Δ` if `G_W ≤ g` on `[Δ' - D, Δ - D]`;
* `sFar_lipschitz_log`: for `L, L₀ ≤ Rt`, `|𝔰_far(Δ(L)) - 𝔰_far(Δ(L₀))| ≤ sigLip c Rt |L - L₀|` with
  `sigLip c Rt = Δ(Rt)·G_W(max(0, D - Δ(Rt)))` (the `Gaussian` factor `e^{-(Δ-Δ_far)²/(2W²)}` of `(ct:sigma-prime)` at the point of
  `(-∞, Rt]` nearest to `Δ_far`, times `Δ(Rt)`).

**Proved**, unconditional.  The bound of `s_j = sigLip·W_j` (`ct:sigma-prime`, the two cases of block position) is not done here.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtBoasWindow

lemma gaussK_nonneg' (W y : ℝ) (hW : 0 < W) : 0 ≤ gaussK W y := by unfold gaussK; positivity

/-- `𝔰_far(Δ) = ∫_{y < Δ - D} G_W(y) dy`. -/
lemma sFar_eq_Iio (c Δ : ℝ) : sFar c Δ = ∫ y in Iio (Δ - farD c), gaussK (farW c) y := by
  unfold sFar
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Iio]
  rw [← integral_sub_left_eq_self (fun x => (Iio (Δ - farD c)).indicator (gaussK (farW c)) x) volume Δ]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  by_cases hx : x ∈ Ioi (farD c)
  · have : Δ - x ∈ Iio (Δ - farD c) := by simp only [mem_Ioi, mem_Iio] at *; linarith
    simp [Set.indicator_of_mem hx, Set.indicator_of_mem this]
  · have : Δ - x ∉ Iio (Δ - farD c) := by simp only [mem_Ioi, mem_Iio, not_lt] at *; linarith
    simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem this]

/-- **Lipschitz bound of `𝔰_far`**: `Δ' ≤ Δ` and `G_W ≤ g` on `[Δ' - D, Δ - D]` give
`𝔰_far(Δ) - 𝔰_far(Δ') ≤ g (Δ - Δ')` (and `𝔰_far` is nondecreasing). -/
lemma sFar_sub_le {c : ℝ} (hc : 1 < c) {Δ' Δ g : ℝ} (hΔ : Δ' ≤ Δ)
    (hg : ∀ t ∈ Icc (Δ' - farD c) (Δ - farD c), gaussK (farW c) t ≤ g) :
    0 ≤ sFar c Δ - sFar c Δ' ∧ sFar c Δ - sFar c Δ' ≤ g * (Δ - Δ') := by
  have hW : 0 < farW c := by unfold farW; linarith
  have hint : Integrable (gaussK (farW c)) := integrable_gaussK hW
  rw [sFar_eq_Iio, sFar_eq_Iio]
  have hU : Iio (Δ - farD c) = Iio (Δ' - farD c) ∪ Ico (Δ' - farD c) (Δ - farD c) := by
    ext x; simp only [mem_Iio, mem_union, mem_Ico]
    constructor
    · intro h; by_cases h' : x < Δ' - farD c
      · exact Or.inl h'
      · exact Or.inr ⟨not_lt.1 h', h⟩
    · rintro (h | h)
      · linarith
      · exact h.2
  have hd : Disjoint (Iio (Δ' - farD c)) (Ico (Δ' - farD c) (Δ - farD c)) := by
    rw [Set.disjoint_left]; intro x h1 h2; simp only [mem_Iio, mem_Ico] at h1 h2; linarith [h2.1]
  rw [hU, setIntegral_union hd measurableSet_Ico hint.integrableOn hint.integrableOn]
  have h0 : 0 ≤ ∫ y in Ico (Δ' - farD c) (Δ - farD c), gaussK (farW c) y :=
    setIntegral_nonneg measurableSet_Ico fun y _ => gaussK_nonneg' _ _ hW
  have h1 : ∫ y in Ico (Δ' - farD c) (Δ - farD c), gaussK (farW c) y ≤ g * (Δ - Δ') := by
    have := setIntegral_mono_on (μ := volume) (s := Ico (Δ' - farD c) (Δ - farD c))
      hint.integrableOn (integrableOn_const (by simp)) measurableSet_Ico
      (fun t ht => hg t ⟨ht.1, ht.2.le⟩)
    rw [setIntegral_const] at this
    simpa [Real.volume_real_Ico, hΔ, mul_comm] using this
  constructor <;> linarith

/-- `Δ(L) = c e^L/π²`; `sigLip c Rt = Δ(Rt)·G_{W_far}(max(0, D - Δ(Rt)))`. -/
noncomputable def sigLip (c Rt : ℝ) : ℝ :=
  c * (Real.exp Rt / π ^ 2) * gaussK (farW c) (max 0 (farD c - c * (Real.exp Rt / π ^ 2)))

lemma sigLip_nonneg {c : ℝ} (hc : 1 < c) (Rt : ℝ) : 0 ≤ sigLip c Rt := by
  have hW : 0 < farW c := by unfold farW; linarith
  unfold sigLip
  have := gaussK_nonneg' (farW c) (max 0 (farD c - c * (Real.exp Rt / π ^ 2))) hW
  positivity

/-- **`(ct:sigma-prime)` in Lipschitz form**: for `L, L₀ ≤ Rt`,
`|𝔰_far(Δ(L)) - 𝔰_far(Δ(L₀))| ≤ sigLip c Rt · |L - L₀|`. -/
theorem sFar_lipschitz_log {c : ℝ} (hc : 1 < c) {Rt L L0 : ℝ} (hL : L ≤ Rt) (hL0 : L0 ≤ Rt) :
    |sFar c (c * (Real.exp L / π ^ 2)) - sFar c (c * (Real.exp L0 / π ^ 2))| ≤ sigLip c Rt * |L - L0| := by
  have hW : 0 < farW c := by unfold farW; linarith
  have hπ : 0 < π ^ 2 := by positivity
  have hc0 : 0 < c := by linarith
  have key : ∀ {L L0 : ℝ}, L ≤ Rt → L0 ≤ L →
      0 ≤ sFar c (c * (Real.exp L / π ^ 2)) - sFar c (c * (Real.exp L0 / π ^ 2)) ∧
      sFar c (c * (Real.exp L / π ^ 2)) - sFar c (c * (Real.exp L0 / π ^ 2)) ≤ sigLip c Rt * (L - L0) := by
    intro L L0 hL hle
    have hΔle : c * (Real.exp L0 / π ^ 2) ≤ c * (Real.exp L / π ^ 2) := by
      gcongr
    have hΔR : c * (Real.exp L / π ^ 2) ≤ c * (Real.exp Rt / π ^ 2) := by gcongr
    set g := gaussK (farW c) (max 0 (farD c - c * (Real.exp Rt / π ^ 2))) with hg
    have hgt : ∀ t ∈ Icc (c * (Real.exp L0 / π ^ 2) - farD c) (c * (Real.exp L / π ^ 2) - farD c),
        gaussK (farW c) t ≤ g := by
      intro t ht
      have ht2 : t ≤ c * (Real.exp Rt / π ^ 2) - farD c := by linarith [ht.2]
      set m := max 0 (farD c - c * (Real.exp Rt / π ^ 2)) with hm
      have hm0 : 0 ≤ m := le_max_left _ _
      have hmt : m ^ 2 ≤ t ^ 2 := by
        rcases le_or_gt 0 t with h | h
        · have : m = 0 := by
            rw [hm]; apply max_eq_left; linarith
          rw [this]; nlinarith [sq_nonneg t]
        · have : m ≤ -t := max_le (by linarith) (by linarith)
          nlinarith
      unfold gaussK; rw [hg]; unfold gaussK
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Real.exp_le_exp.2
      have : 0 ≤ 1 / (2 * farW c ^ 2) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hmt this]
    obtain ⟨h0, h1⟩ := sFar_sub_le hc hΔle hgt
    refine ⟨h0, h1.trans ?_⟩
    unfold sigLip
    rw [← hg]
    have hg0 : 0 ≤ g := gaussK_nonneg' _ _ hW
    have he : Real.exp L - Real.exp L0 ≤ Real.exp Rt * (L - L0) := by
      have h1 := Real.add_one_le_exp (L0 - L)
      have h2 : Real.exp (L0 - L) = Real.exp L0 / Real.exp L := by rw [Real.exp_sub]
      have h3 : Real.exp L - Real.exp L0 ≤ Real.exp L * (L - L0) := by
        have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos L).le
        have e : Real.exp L * Real.exp (L0 - L) = Real.exp L0 := by rw [← Real.exp_add]; ring_nf
        nlinarith [e]
      exact h3.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hL) (by linarith))
    calc g * (c * (Real.exp L / π ^ 2) - c * (Real.exp L0 / π ^ 2))
        = g * (c / π ^ 2) * (Real.exp L - Real.exp L0) := by ring
      _ ≤ g * (c / π ^ 2) * (Real.exp Rt * (L - L0)) :=
          mul_le_mul_of_nonneg_left he (mul_nonneg hg0 (by positivity))
      _ = c * (Real.exp Rt / π ^ 2) * g * (L - L0) := by ring
  rcases le_total L0 L with h | h
  · obtain ⟨h1, h2⟩ := key hL h
    rw [abs_of_nonneg h1, abs_of_nonneg (by linarith)]; exact h2
  · obtain ⟨h1, h2⟩ := key hL0 h
    rw [abs_sub_comm, abs_of_nonneg h1, abs_sub_comm, abs_of_nonneg (by linarith)]; exact h2

/-- info: 'FormalResearch.SignUncertainty.sFar_lipschitz_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sFar_lipschitz_log

end FormalResearch.SignUncertainty
