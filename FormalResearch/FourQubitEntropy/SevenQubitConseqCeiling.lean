import FormalResearch.FourQubitEntropy.SevenQubitConseqSpectrum
import FormalResearch.FourQubitEntropy.SevenQubitConseqChord
import FormalResearch.FourQubitEntropy.SevenQubitConseqNumerics

/-!
# `thm:seven-entropy-global-ceiling` (conditional on `SevenPurityBound`)

Every pure seven-qubit state has mean three-qubit von Neumann entropy
`E₃(ψ) ≤ (99 + g₈(455/1572) + g₈(641/3144))/35 < 2.97354` bits
(`seven_qubit_entropy_global_upper.tex`, CE-1).  Here entropies are in nats, so the statement reads
`E₃ ≤ (99 ln 2 + g₈(455/1572) + g₈(641/3144))/35 < 2.97354 · ln 2`.

Proof, as in the paper.  With `e_S = 8 tr ρ_S² - 1` and `R = ∑ e_S ≥ R₀ = 255/131`
(`cor_sevenpauli`), rescale `e'_S = (R₀/R) e_S`, so `∑ e'_S = R₀`, `0 ≤ e'_S ≤ M = (R₀+2)/3`
(`cut_compat`).  The cut entropy is `≤ g₈(p_S) ≤ g₈((1+e'_S)/8)` (envelope and monotonicity of `g₈`),
`g₈` is convex on the relevant range, and the chord form of Karamata (`chord_reduction`) with
`c = R₀ - M = 248/393` gives `∑ ≤ 33 g₈(1/8) + g₈((1+M)/8) + g₈((1+c)/8)`.
-/

open Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitConseq

open FormalResearch.FourQubitEntropy.SevenQubitIco

/-- `E₃`: mean von Neumann entropy (nats) of the 35 three-qubit marginals. -/
noncomputable def meanEntropy3 (ψ : BitString → ℂ) : ℝ :=
  (∑ m ∈ tripleMasks, cutEntropy (maskCut 3 4 m) ψ) / 35

theorem g8_at_eighth : g8 (1 / 8) = 3 * Real.log 2 := by
  unfold g8 tOf Gsp
  have : Real.sqrt (7 * (8 * (1 / 8) - 1)) = 0 := by norm_num
  rw [this]
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h8' : Real.log (1 / 8) = -(3 * Real.log 2) := by rw [one_div, Real.log_inv, h8]
  norm_num [Real.negMulLog]
  rw [h8']
  ring

/-- Convexity of `e ↦ g₈((1+e)/8)` on `[0, 517/393]`. -/
theorem hfun_convex : ConvexOn ℝ (Set.Icc 0 (517 / 393)) (fun e => g8 ((1 + e) / 8)) := by
  refine ⟨convex_Icc 0 _, ?_⟩
  intro x hx y hy a b ha hb hab
  have mem : ∀ z ∈ Set.Icc (0 : ℝ) (517 / 393), (1 + z) / 8 ∈ Set.Icc (1 / 8 : ℝ) (107 / 289) :=
    fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have := g8_convexOn.2 (mem x hx) (mem y hy) ha hb hab
  simp only [smul_eq_mul] at this ⊢
  have e : (1 + (a * x + b * y)) / 8 = a * ((1 + x) / 8) + b * ((1 + y) / 8) := by
    have : b = 1 - a := by linarith
    subst this; ring
  rw [e]; exact this

theorem entropy_global_ceiling (h : SevenPurityBound) (ψ : BitString → ℂ) (hψ : UnitVec ψ) :
    meanEntropy3 ψ ≤ (99 * Real.log 2 + g8 (455 / 1572) + g8 (641 / 3144)) / 35 := by
  have hR : 255 / 131 ≤ excessSum ψ := by
    have h1 := h ψ hψ
    rw [excessSum_eq]; linarith
  set R := excessSum ψ with hRdef
  have hRpos : 0 < R := by linarith
  set α : ℝ := (255 / 131) / R with hα
  have hα0 : 0 < α := by positivity
  have hα1 : α ≤ 1 := by rw [hα, div_le_one hRpos]; exact hR
  set e' : (Fin 7 → Bool) → ℝ := fun m => α * excess m ψ with he'
  have hmem : ∀ m ∈ tripleMasks, weight m = 3 := fun m hm => (Finset.mem_filter.1 hm).2
  have he0 : ∀ m ∈ tripleMasks, 0 ≤ e' m := fun m hm =>
    mul_nonneg hα0.le (excess_nonneg m (hmem m hm) ψ hψ)
  have heM : ∀ m ∈ tripleMasks, e' m ≤ 517 / 393 := by
    intro m hm
    have hc := cut_compat m (hmem m hm) ψ hψ
    have hx := excess_nonneg m (hmem m hm) ψ hψ
    simp only [he']
    have h1 : α * excess m ψ ≤ α * ((R + 2) / 3) :=
      mul_le_mul_of_nonneg_left (by linarith) hα0.le
    have h2 : α * R = 255 / 131 := by rw [hα]; field_simp
    nlinarith
  have hsum : ∑ m ∈ tripleMasks, e' m = 248 / 393 + 517 / 393 := by
    simp only [he']
    rw [← Finset.mul_sum]
    have : ∑ m ∈ tripleMasks, excess m ψ = R := rfl
    rw [this, hα]; field_simp; norm_num
  have hchord := chord_reduction tripleMasks e' (fun e => g8 ((1 + e) / 8)) (by norm_num)
    (by norm_num) hfun_convex he0 heM hsum
  -- termwise bound
  have hterm : ∀ m ∈ tripleMasks,
      cutEntropy (maskCut 3 4 m) ψ ≤ g8 ((1 + e' m) / 8) := by
    intro m hm
    have hb := maskCut_bijective_three m (hmem m hm)
    have hp := cutPurity_mem _ hb ψ hψ
    have h1 := cutEntropy_le _ hb ψ hψ
    have hx := excess_nonneg m (hmem m hm) ψ hψ
    have hex : excess m ψ = 8 * cutPurity (maskCut 3 4 m) ψ - 1 := rfl
    have hle : (1 + e' m) / 8 ≤ cutPurity (maskCut 3 4 m) ψ := by
      simp only [he']
      nlinarith
    have hge : 1 / 8 ≤ (1 + e' m) / 8 := by linarith [he0 m hm]
    have := g8_antitoneOn ⟨hge, by linarith [hp.2]⟩ ⟨hp.1, hp.2⟩ hle
    exact h1.trans this
  have hsumle : ∑ m ∈ tripleMasks, cutEntropy (maskCut 3 4 m) ψ ≤
      ∑ m ∈ tripleMasks, g8 ((1 + e' m) / 8) := Finset.sum_le_sum hterm
  have hcard : (tripleMasks.card : ℝ) = 35 := by rw [tripleMasks_card]; norm_num
  rw [hcard] at hchord
  have e0 : g8 ((1 + 0) / 8) = 3 * Real.log 2 := by norm_num; exact g8_at_eighth
  have eM : g8 ((1 + 517 / 393) / 8) = g8 (455 / 1572) := by norm_num
  have ec : g8 ((1 + 248 / 393) / 8) = g8 (641 / 3144) := by norm_num
  simp only [e0, eM, ec] at hchord
  unfold meanEntropy3
  apply div_le_div_of_nonneg_right _ (by norm_num)
  linarith

/-- **`thm:seven-entropy-global-ceiling`** (conditional on the sharp purity bound): the mean
three-qubit entropy of every pure seven-qubit state is below `2.97354` bits. -/
theorem entropy_global_ceiling_lt (h : SevenPurityBound) (ψ : BitString → ℂ) (hψ : UnitVec ψ) :
    meanEntropy3 ψ < 297354 / 100000 * Real.log 2 := by
  have h1 := entropy_global_ceiling h ψ hψ
  have h2 := g8_sum_lt
  linarith

end FormalResearch.FourQubitEntropy.SevenQubitConseq
