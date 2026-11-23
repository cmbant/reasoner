module

public import FormalResearch.SignUncertainty.MellinGrowth
public import FormalResearch.SignUncertainty.MellinHGrowth
public import FormalResearch.SignUncertainty.MellinMajorantHId
public import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# The Mellin majorant (`gt:7.4(2)`)

For `c > 3/2`, `ε = ±1`, `f ∈ 𝒜_c^ε` and `0 ≤ Re ζ < 1`,
`|M̃_f(c(1-ζ))| ≤ M[f] |1+ζ|^{1/2} exp(c Re ℋ(ζ) + 1/(6c))` (`norm_mellinStrip_le_majorant`), where
`ℋ = hInt` (identified with `stripH` by `hInt_eq_stripH`).

Proof: `Fm(ζ) = M̃_f(c(1-ζ))` for `Re ζ ≤ 1/2` and `ε M̃_f(cζ)` for `Re ζ > 1/2` is continuous on the closed strip
`0 ≤ Re ζ ≤ 1` and holomorphic inside (reflection). `W = Fm e^{-cℋ̂} (1+ζ)^{-1/2}` is bounded by
`M[f] e^{1/(6c)}` on both edges (the `Γ`-ratio bound `gamma_ratio_edge_le`, `re_hInt_imag`, and
`ℋ̂(1-ζ) = ℋ̂(ζ)` for the right edge), has growth `exp(B exp(3|Im ζ|))` (`MellinGrowth`, `MellinHGrowth`),
`3 < π`, and Phragmén–Lindelöf (`PhragmenLindelof.vertical_strip`) gives the bound inside.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `M̃_f` is continuous on `0 < Re z ≤ c`. -/
theorem continuousOn_mellinStrip {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    ContinuousOn (mellinStrip f) {z : ℂ | 0 < z.re ∧ z.re ≤ c} := by
  have h2pi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have h1 : ContinuousOn (fun z : ℂ => ((2 * Real.pi : ℝ) : ℂ) ^ z) {z | 0 < z.re ∧ z.re ≤ c} :=
    (Continuous.const_cpow continuous_id (Or.inl h2pi)).continuousOn
  have h2 : ContinuousOn (fun z : ℂ => (Complex.Gamma z)⁻¹) {z | 0 < z.re ∧ z.re ≤ c} := by
    intro z hz
    have hz0 : 0 < z.re := hz.1
    have hne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz0
    have hd : DifferentiableAt ℂ Complex.Gamma z := by
      apply Complex.differentiableAt_Gamma
      intro m hm
      have := congrArg Complex.re hm
      simp at this
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact (hd.continuousAt.inv₀ hne).continuousWithinAt
  have e : mellinStrip f = fun z => ((2 * Real.pi : ℝ) : ℂ) ^ z * (Complex.Gamma z)⁻¹ *
      mellinRaw f z := by
    funext z; simp [mellinStrip, div_eq_mul_inv]
  rw [e]
  exact (h1.mul h2).mul (continuousOn_mellinRaw hc hf)

/-- `Fm(ζ) = M̃_f(c(1-ζ))` for `Re ζ ≤ 1/2` and `ε M̃_f(cζ)` for `Re ζ > 1/2`. -/
noncomputable def mellinFm (c ε : ℝ) (f : ℝ → ℝ) (ζ : ℂ) : ℂ :=
  if ζ.re ≤ 1 / 2 then mellinStrip f ((c : ℂ) * (1 - ζ)) else (ε : ℂ) * mellinStrip f ((c : ℂ) * ζ)

/-- The function to which Phragmén–Lindelöf is applied. -/
noncomputable def mellinW (c ε : ℝ) (f : ℝ → ℝ) (ζ : ℂ) : ℂ :=
  mellinFm c ε f ζ * Complex.exp (-((c : ℂ) * hInt ζ)) * ((1 + ζ) ^ (1 / 2 : ℂ))⁻¹

theorem mellinFm_eq {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) {ζ : ℂ}
    (hζ0 : 0 ≤ ζ.re) (hζ1 : ζ.re < 1) : mellinFm c ε f ζ = mellinStrip f ((c : ℂ) * (1 - ζ)) := by
  unfold mellinFm
  by_cases h : ζ.re ≤ 1 / 2
  · rw [if_pos h]
  · rw [if_neg h]
    have hre : ((c : ℂ) * ζ).re = c * ζ.re := by simp
    have := mellinStrip_reflection hc hf (z := (c : ℂ) * ζ) (by rw [hre]; nlinarith)
      (by rw [hre]; nlinarith)
    rw [show (c : ℂ) * (1 - ζ) = (c : ℂ) - (c : ℂ) * ζ by ring, this]

theorem continuousOn_mellinFm {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    ContinuousOn (mellinFm c ε f) {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} := by
  have hc0 : 0 < c := by linarith
  have hcont := continuousOn_mellinStrip hc0 hf
  set A : Set ℂ := {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1 / 2} with hA
  set B : Set ℂ := {ζ : ℂ | 1 / 2 ≤ ζ.re ∧ ζ.re ≤ 1} with hB
  have hAB : {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} = A ∪ B := by
    ext ζ; simp only [hA, hB, mem_setOf_eq, mem_union]
    constructor
    · rintro ⟨h0, h1⟩
      rcases le_total ζ.re (1 / 2) with h | h
      · exact Or.inl ⟨h0, h⟩
      · exact Or.inr ⟨h, h1⟩
    · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩) <;> constructor <;> linarith
  have hAc : IsClosed A := by
    have : A = Complex.re ⁻¹' Icc 0 (1 / 2) := by ext; simp [hA]
    rw [this]; exact isClosed_Icc.preimage Complex.continuous_re
  have hBc : IsClosed B := by
    have : B = Complex.re ⁻¹' Icc (1 / 2) 1 := by ext; simp [hB]
    rw [this]; exact isClosed_Icc.preimage Complex.continuous_re
  rw [hAB]
  refine ContinuousOn.union_of_isClosed ?_ ?_ hAc hBc
  · have h1 : ContinuousOn (fun ζ : ℂ => mellinStrip f ((c : ℂ) * (1 - ζ))) A := by
      refine hcont.comp (by fun_prop) ?_
      intro ζ hζ
      have hre : ((c : ℂ) * (1 - ζ)).re = c * (1 - ζ.re) := by simp
      show 0 < ((c : ℂ) * (1 - ζ)).re ∧ ((c : ℂ) * (1 - ζ)).re ≤ c
      rw [hre]
      constructor <;> nlinarith [hζ.1, hζ.2]
    refine h1.congr fun ζ hζ => ?_
    unfold mellinFm
    rw [if_pos hζ.2]
  · have h1 : ContinuousOn (fun ζ : ℂ => (ε : ℂ) * mellinStrip f ((c : ℂ) * ζ)) B := by
      refine continuousOn_const.mul (hcont.comp (by fun_prop) ?_)
      intro ζ hζ
      have hre : ((c : ℂ) * ζ).re = c * ζ.re := by simp
      show 0 < ((c : ℂ) * ζ).re ∧ ((c : ℂ) * ζ).re ≤ c
      rw [hre]
      constructor <;> nlinarith [hζ.1, hζ.2]
    refine h1.congr fun ζ hζ => ?_
    by_cases h : ζ.re ≤ 1 / 2
    · have hζh : ζ.re = 1 / 2 := le_antisymm h hζ.1
      have hre : ((c : ℂ) * ζ).re = c * ζ.re := by simp
      have := mellinStrip_reflection hc hf (z := (c : ℂ) * ζ) (by rw [hre, hζh]; nlinarith)
        (by rw [hre, hζh]; nlinarith)
      simp only [mellinFm, if_pos h]
      rw [show (c : ℂ) * (1 - ζ) = (c : ℂ) - (c : ℂ) * ζ by ring, this]
    · unfold mellinFm
      rw [if_neg h]

theorem differentiableOn_mellinFm {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ}
    (hf : IsHankelEigenfn c ε f) :
    DifferentiableOn ℂ (mellinFm c ε f) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} := by
  have hc0 : 0 < c := by linarith
  have hd := differentiableOn_mellinStrip hc0 hf
  have h1 : DifferentiableOn ℂ (fun ζ : ℂ => mellinStrip f ((c : ℂ) * (1 - ζ)))
      {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} := by
    refine hd.comp (by fun_prop) ?_
    intro ζ hζ
    have hre : ((c : ℂ) * (1 - ζ)).re = c * (1 - ζ.re) := by simp
    show 0 < ((c : ℂ) * (1 - ζ)).re ∧ ((c : ℂ) * (1 - ζ)).re < c
    rw [hre]
    constructor <;> nlinarith [hζ.1, hζ.2]
  exact h1.congr fun ζ hζ => mellinFm_eq hc hf hζ.1.le hζ.2

theorem differentiableOn_hInt : DifferentiableOn ℂ hInt hStrip := fun z hz =>
  (hasDerivAt_hInt hz).differentiableAt.differentiableWithinAt

lemma closedStrip_subset : {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} ⊆ hStrip := fun ζ hζ =>
  ⟨by linarith [hζ.1], by linarith [hζ.2]⟩

lemma one_add_mem_slitPlane {ζ : ℂ} (hζ : 0 ≤ ζ.re) : 1 + ζ ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))

lemma one_add_ne_zero {ζ : ℂ} (hζ : 0 ≤ ζ.re) : 1 + ζ ≠ 0 := fun h => by
  have := congrArg Complex.re h; simp at this; linarith

lemma sqrt_cpow_ne_zero {ζ : ℂ} (hζ : 0 ≤ ζ.re) : (1 + ζ) ^ (1 / 2 : ℂ) ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (one_add_ne_zero hζ))

lemma differentiableAt_sqrt_inv {ζ : ℂ} (hζ : 0 ≤ ζ.re) :
    DifferentiableAt ℂ (fun w : ℂ => ((1 + w) ^ (1 / 2 : ℂ))⁻¹) ζ := by
  have h1 : DifferentiableAt ℂ (fun w : ℂ => (1 + w) ^ (1 / 2 : ℂ)) ζ :=
    ((differentiableAt_const (1 : ℂ)).add differentiableAt_id).cpow (differentiableAt_const _)
      (one_add_mem_slitPlane hζ)
  exact h1.inv (sqrt_cpow_ne_zero hζ)

theorem diffContOnCl_mellinW {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    DiffContOnCl ℂ (mellinW c ε f) (Complex.re ⁻¹' Ioo (0 : ℝ) 1) := by
  have hS : closure (Complex.re ⁻¹' Ioo (0 : ℝ) 1) ⊆ {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} := by
    refine closure_minimal ?_ ?_
    · intro ζ hζ; exact ⟨hζ.1.le, hζ.2.le⟩
    · have : {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} = Complex.re ⁻¹' Icc 0 1 := by ext; simp
      rw [this]; exact isClosed_Icc.preimage Complex.continuous_re
  constructor
  · intro ζ hζ
    have hζ' : 0 < ζ.re ∧ ζ.re < 1 := hζ
    refine DifferentiableAt.differentiableWithinAt ?_
    have hopen : {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} ∈ 𝓝 ζ := by
      refine IsOpen.mem_nhds ?_ hζ'
      exact (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have h1 : DifferentiableAt ℂ (mellinFm c ε f) ζ :=
      (differentiableOn_mellinFm hc hf).differentiableAt hopen
    have hmem : ζ ∈ hStrip := ⟨by linarith [hζ'.1], by linarith [hζ'.2]⟩
    have h2 : DifferentiableAt ℂ hInt ζ := (hasDerivAt_hInt hmem).differentiableAt
    exact (h1.mul (((differentiableAt_const _).mul h2).neg.cexp)).mul
      (differentiableAt_sqrt_inv hζ'.1.le)
  · refine ContinuousOn.mono ?_ hS
    have h1 := continuousOn_mellinFm hc hf
    have h2 : ContinuousOn (fun ζ : ℂ => Complex.exp (-((c : ℂ) * hInt ζ)))
        {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} :=
      (continuousOn_const.mul (differentiableOn_hInt.continuousOn.mono closedStrip_subset)).neg.cexp
    have h3 : ContinuousOn (fun ζ : ℂ => ((1 + ζ) ^ (1 / 2 : ℂ))⁻¹)
        {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} := fun ζ hζ =>
      (differentiableAt_sqrt_inv hζ.1).continuousAt.continuousWithinAt
    exact (h1.mul h2).mul h3

/-- info: 'FormalResearch.SignUncertainty.continuousOn_mellinStrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuousOn_mellinStrip

/-- info: 'FormalResearch.SignUncertainty.mellinFm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mellinFm_eq

/-- info: 'FormalResearch.SignUncertainty.continuousOn_mellinFm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuousOn_mellinFm

/-- info: 'FormalResearch.SignUncertainty.differentiableOn_mellinFm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms differentiableOn_mellinFm

/-- info: 'FormalResearch.SignUncertainty.diffContOnCl_mellinW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diffContOnCl_mellinW

end FormalResearch.SignUncertainty
