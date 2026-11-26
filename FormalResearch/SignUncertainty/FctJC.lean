/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctClaimGPert
public import FormalResearch.SignUncertainty.FctJetInt

/-!
# `JC k U f b`: `C^k` with jet bound (F2a, `fct:comp-cfu`)

`JC k U f b := ContDiffOn ℝ k f U ∧ JB k U f b`, with the closure lemmas of `FctJet` bundled so that smoothness is carried
along: sum, scalar multiple, product, evaluation, constants and continuous linear maps, composition (also with pairs and
with the first coordinate of a product), reciprocal, derivative, `ε`-linear composition, parametric integral.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace FormalResearch.SignUncertainty

/-- `C^k` on `U` with all iterated derivatives of order `≤ k` bounded by `b`. -/
def JC {Y V : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (k : ℕ) (U : Set Y) (f : Y → V) (b : ℝ) : Prop :=
  ContDiffOn ℝ k f U ∧ JB k U f b

section JC
variable {Y V W : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {k : ℕ} {U : Set Y}

lemma JC.mono {f : Y → V} {b b' : ℝ} (h : JC k U f b) (hb : b ≤ b') : JC k U f b' := ⟨h.1, h.2.mono hb⟩

lemma JC.mono_order {k' : ℕ} {f : Y → V} {b : ℝ} (h : JC k U f b) (hk : k' ≤ k) : JC k' U f b :=
  ⟨h.1.of_le (by exact_mod_cast hk), h.2.mono_order hk⟩

lemma JC.add (hU : UniqueDiffOn ℝ U) {f g : Y → V} {b b' : ℝ} (hf : JC k U f b) (hg : JC k U g b') :
    JC k U (fun y => f y + g y) (b + b') := ⟨hf.1.add hg.1, JB.add hU hf.1 hg.1 hf.2 hg.2⟩

lemma JC.neg (hU : UniqueDiffOn ℝ U) {f : Y → V} {b : ℝ} (hf : JC k U f b) : JC k U (fun y => -f y) b :=
  ⟨hf.1.neg, JB.neg hU hf.2⟩

lemma JC.sub (hU : UniqueDiffOn ℝ U) {f g : Y → V} {b b' : ℝ} (hf : JC k U f b) (hg : JC k U g b') :
    JC k U (fun y => f y - g y) (b + b') := by
  have := hf.add hU (hg.neg hU)
  simpa [sub_eq_add_neg] using this

lemma JC.const_smul (hU : UniqueDiffOn ℝ U) (a : ℝ) {f : Y → V} {b : ℝ} (hf : JC k U f b) :
    JC k U (fun y => a • f y) (|a| * b) := ⟨hf.1.const_smul a, JB.const_smul hU hf.1 a hf.2⟩

lemma JC.const (hU : UniqueDiffOn ℝ U) (v : V) : JC k U (fun _ : Y => v) ‖v‖ :=
  ⟨contDiffOn_const, JB.const hU v⟩

lemma JC.smul (hU : UniqueDiffOn ℝ U) {f : Y → ℝ} {g : Y → V} {b b' : ℝ} (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (hf : JC k U f b) (hg : JC k U g b') : JC k U (fun y => f y • g y) (2 ^ k * b * b') :=
  ⟨hf.1.smul hg.1, JB.smul_mul hU hb hb' hf.1 hg.1 hf.2 hg.2⟩

lemma JC.mul (hU : UniqueDiffOn ℝ U) {f g : Y → ℝ} {b b' : ℝ} (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (hf : JC k U f b) (hg : JC k U g b') : JC k U (fun y => f y * g y) (2 ^ k * b * b') := by
  have := hf.smul hU hb hb' hg
  simpa [smul_eq_mul] using this

lemma JC.clm_apply (hU : UniqueDiffOn ℝ U) {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : Y → Z →L[ℝ] W} {g : Y → Z} {b b' : ℝ} (hb : 0 ≤ b) (hb' : 0 ≤ b') (hf : JC k U f b)
    (hg : JC k U g b') : JC k U (fun y => f y (g y)) (2 ^ k * b * b') :=
  ⟨hf.1.clm_apply hg.1, JB.clm_apply hU hb hb' hf.1 hg.1 hf.2 hg.2⟩

lemma JC.clm_apply_const (hU : UniqueDiffOn ℝ U) {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : Y → Z →L[ℝ] W} {b : ℝ} (hf : JC k U f b) (c : Z) : JC k U (fun y => f y c) (‖c‖ * b) :=
  ⟨hf.1.clm_apply contDiffOn_const, JB.clm_apply_const hU hf.1 c hf.2⟩

lemma JC.clm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {U : Set X} (hU : UniqueDiffOn ℝ U)
    (L : X →L[ℝ] V) {M : ℝ} (hL : ‖L‖ ≤ M) (h0 : ∀ x ∈ U, ‖L x‖ ≤ M) : JC k U (fun x => L x) M :=
  ⟨L.contDiff.contDiffOn, JB.clm hU L hL h0⟩

lemma JC.inv (hU : UniqueDiffOn ℝ U) {f : Y → ℝ} {m b : ℝ} (hm : 0 < m) (hmin : ∀ y ∈ U, m ≤ f y)
    (hf : JC k U f b) :
    JC k U (fun y => (f y)⁻¹) (k.factorial * (k.factorial * (max 1 m⁻¹) ^ (k + 1)) * (max 1 b) ^ k) :=
  ⟨hf.1.inv fun y hy => (lt_of_lt_of_le hm (hmin y hy)).ne', JB.inv hU hm hf.1 hmin hf.2⟩

lemma JC.congr {f g : Y → V} {b : ℝ} (h : JC k U f b) (hfg : ∀ y ∈ U, f y = g y) : JC k U g b :=
  ⟨h.1.congr fun y hy => (hfg y hy).symm, h.2.congr hfg⟩

lemma JC.comp (hU : UniqueDiffOn ℝ U) {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {t : Set X}
    (ht : UniqueDiffOn ℝ t) {g : X → W} {f : Y → X} {C b : ℝ} (hC0 : 0 ≤ C) (hg : JC k t g C)
    (hf : JC k U f b) (hst : MapsTo f U t) :
    JC k U (fun y => g (f y)) (k.factorial * C * (max 1 b) ^ k) :=
  ⟨hg.1.comp hf.1 hst, JB.comp hU ht hg.1 hf.1 hst hC0 (fun y hy i hi => hg.2 i hi _ (hst hy))
    (fun i _ hi y hy => hf.2 i hi y hy)⟩

/-- Composition `g(u(y), w(y))` where only the derivatives (orders `≥ 1`) of `u`, `w` are controlled
(so that coordinate projections are allowed). -/
lemma JC.comp_pair (hU : UniqueDiffOn ℝ U) {X1 X2 : Type*} [NormedAddCommGroup X1] [NormedSpace ℝ X1]
    [NormedAddCommGroup X2] [NormedSpace ℝ X2] {t : Set (X1 × X2)} (ht : UniqueDiffOn ℝ t) {g : X1 × X2 → W}
    {u : Y → X1} {w : Y → X2} {C b1 b2 : ℝ} (hC0 : 0 ≤ C) (hg : JC k t g C) (hu : ContDiffOn ℝ k u U)
    (hw : ContDiffOn ℝ k w U)
    (hu1 : ∀ i, 1 ≤ i → i ≤ k → ∀ y ∈ U, ‖iteratedFDerivWithin ℝ i u U y‖ ≤ b1)
    (hw1 : ∀ i, 1 ≤ i → i ≤ k → ∀ y ∈ U, ‖iteratedFDerivWithin ℝ i w U y‖ ≤ b2)
    (hst : MapsTo (fun y => (u y, w y)) U t) :
    JC k U (fun y => g (u y, w y)) (k.factorial * C * (max 1 (max b1 b2)) ^ k) :=
  ⟨hg.1.comp (hu.prodMk hw) hst,
    JB.comp hU ht hg.1 (hu.prodMk hw) hst hC0 (fun y hy i hi => hg.2 i hi _ (hst hy))
      (norm_iteratedFDerivWithin_pair_le hU hu hw hu1 hw1)⟩

lemma JC.comp_clm (hU : UniqueDiffOn ℝ U) {X' : Type*} [NormedAddCommGroup X'] [NormedSpace ℝ X'] {t : Set X'}
    (ht : UniqueDiffOn ℝ t) (L : Y →L[ℝ] X') (hL : ‖L‖ ≤ 1) {g : X' → W} {b : ℝ} (hb0 : 0 ≤ b)
    (hg : JC k t g b) (hst : MapsTo L U t) : JC k U (fun x => g (L x)) (k.factorial * b) :=
  ⟨hg.1.comp L.contDiff.contDiffOn hst, JB.comp_clm hU ht L hL hb0 hg.1 hst hg.2⟩

/-- A function of the first coordinate. -/
lemma JC.comp_fst {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {Ω : Set P} {T : Set X} (hΩ : UniqueDiffOn ℝ Ω) (hUd : UniqueDiffOn ℝ (Ω ×ˢ T))
    {g : P → W} {b : ℝ} (hb0 : 0 ≤ b) (hg : JC k Ω g b) :
    JC k (Ω ×ˢ T) (fun q : P × X => g q.1) (k.factorial * b) :=
  JC.comp_clm hUd hΩ (ContinuousLinearMap.fst ℝ P X)
    (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => by simpa using norm_fst_le p) hb0 hg
    (fun q hq => hq.1)

lemma JC.succ_fderiv (hU : IsOpen U) {j : ℕ} {f : Y → V} {b : ℝ} (h : JC (j + 1) U f b) :
    JC j U (fun y => fderiv ℝ f y) b :=
  ⟨h.1.fderiv_of_isOpen hU (by exact_mod_cast le_rfl),
    (h.2.succ_fderivWithin hU.uniqueDiffOn).congr fun y hy => fderivWithin_of_isOpen hU hy⟩

/-- Derivative in the last coordinate direction. -/
lemma JC.deriv_snd {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {U : Set (P × ℝ)}
    {j : ℕ} {f : P × ℝ → ℝ} {b : ℝ} (hU : IsOpen U) (h : JC (j + 1) U f b) :
    JC j U (fun q => fderiv ℝ f q (0, 1)) b := by
  have hn : ‖((0 : P), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have := (h.succ_fderiv hU).clm_apply_const hU.uniqueDiffOn ((0 : P), (1 : ℝ))
  rwa [hn, one_mul] at this

lemma JC.snd {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {U : Set (P × ℝ)} (hU : UniqueDiffOn ℝ U)
    {M : ℝ} (hM : 1 ≤ M) (h0 : ∀ p ∈ U, |p.2| ≤ M) : JC k U (fun p : P × ℝ => p.2) M :=
  ⟨contDiffOn_snd, JB.snd hU hM h0⟩

lemma JC.integral01 {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup V]
    [NormedSpace ℝ V] {O : Set P} (hO : IsOpen O) {f : P → ℝ → V} {b : ℝ}
    (h : JC k (O ×ˢ Icc (0 : ℝ) 1) (fun p : P × ℝ => f p.1 p.2) b) :
    JC k O (fun y => ∫ σ in Icc (0 : ℝ) 1, f y σ) b :=
  JB.integral01 hO h.1 h.2

lemma JC.comp_small {j : ℕ} (hU : UniqueDiffOn ℝ U) {T : Set ℝ} (hT : IsOpen T) (hTc : Convex ℝ T)
    (h0T : (0 : ℝ) ∈ T) {g : ℝ → ℝ} {Cg : ℝ} (hgb : JC (j + 1) T g Cg) {f : Y → ℝ} {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (hCg0 : 0 ≤ Cg) (hfb : JC (j + 1) U f ε) (hfT : MapsTo f U T) :
    JC (j + 1) U (fun y => g (f y) - g 0) ((1 + 2 ^ j * j.factorial) * Cg * ε) :=
  ⟨(hgb.1.comp hfb.1 hfT).sub contDiffOn_const,
    JB.comp_small hU hT hTc h0T hgb.1 hgb.2 hε0 hε1 hCg0 hfb.1 hfb.2 hfT⟩

end JC
end FormalResearch.SignUncertainty
