/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# `C^k`-jet bounds on a set (F2a, `fct:comp-cfu`)

`JB k U f b` says `‖D^i f(y)‖ ≤ b` (iterated Fréchet derivative within `U`) for all `i ≤ k`, `y ∈ U`.  This is the `C^k` norm used for the scaled chart of `fct:comp-cfu`
(the paper's sup of all partial derivatives of total order `≤ k` is comparable to it, with constants depending only on `k` and the dimension of the parameter space).
Closure lemmas (sum, scalar multiple, product, evaluation of a linear-map-valued function, composition, reciprocal) are the Leibniz and Faà di Bruno bounds of Mathlib.
Sets `U` carry `UniqueDiffOn ℝ U`; for open sets `iteratedFDerivWithin = iteratedFDeriv`.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace FormalResearch.SignUncertainty

variable {Y V W : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Bound for all iterated derivatives (within `U`) of order `≤ k`. -/
def JB (k : ℕ) (U : Set Y) (f : Y → V) (b : ℝ) : Prop :=
  ∀ i ≤ k, ∀ y ∈ U, ‖iteratedFDerivWithin ℝ i f U y‖ ≤ b

variable {k : ℕ} {U : Set Y}

lemma JB.mono {f : Y → V} {b b' : ℝ} (h : JB k U f b) (hb : b ≤ b') : JB k U f b' :=
  fun i hi y hy => (h i hi y hy).trans hb

lemma JB.mono_order {k' : ℕ} {f : Y → V} {b : ℝ} (h : JB k U f b) (hk : k' ≤ k) : JB k' U f b :=
  fun i hi y hy => h i (hi.trans hk) y hy

lemma JB.nonneg {f : Y → V} {b : ℝ} (h : JB k U f b) {y : Y} (hy : y ∈ U) : 0 ≤ b :=
  (norm_nonneg _).trans (h 0 (Nat.zero_le _) y hy)

lemma JB.add (hU : UniqueDiffOn ℝ U) {f g : Y → V} {b b' : ℝ} (hf : ContDiffOn ℝ k f U) (hg : ContDiffOn ℝ k g U)
    (h : JB k U f b) (h' : JB k U g b') : JB k U (fun y => f y + g y) (b + b') := by
  intro i hi y hy
  have := iteratedFDerivWithin_add_apply (𝕜 := ℝ) (i := i) (f := f) (g := g)
    ((hf y hy).of_le (by exact_mod_cast hi)) ((hg y hy).of_le (by exact_mod_cast hi)) hU hy
  have e : (fun y => f y + g y) = f + g := rfl
  rw [e, this]
  exact (norm_add_le _ _).trans (add_le_add (h i hi y hy) (h' i hi y hy))

lemma JB.neg (hU : UniqueDiffOn ℝ U) {f : Y → V} {b : ℝ} (h : JB k U f b) : JB k U (fun y => -f y) b := by
  intro i hi y hy
  have e : (fun y => -f y) = -f := rfl
  rw [e, iteratedFDerivWithin_neg_apply hU hy, norm_neg]
  exact h i hi y hy

lemma JB.const_smul (hU : UniqueDiffOn ℝ U) {f : Y → V} {b : ℝ} (hf : ContDiffOn ℝ k f U) (a : ℝ) (h : JB k U f b) :
    JB k U (fun y => a • f y) (|a| * b) := by
  intro i hi y hy
  have := iteratedFDerivWithin_const_smul_apply (𝕜 := ℝ) (i := i) (a := a) (f := f)
    ((hf y hy).of_le (by exact_mod_cast hi)) hU hy
  have e : (fun y => a • f y) = a • f := rfl
  rw [e, this, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (h i hi y hy) (abs_nonneg _)

lemma JB.const (hU : UniqueDiffOn ℝ U) (v : V) : JB k U (fun _ : Y => v) ‖v‖ := by
  intro i hi y hy
  cases i with
  | zero => simp [iteratedFDerivWithin_zero_eq_comp]
  | succ n =>
    have : iteratedFDerivWithin ℝ (n + 1) (fun _ : Y => v) U y = 0 := by
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hU contDiffAt_const hy, iteratedFDeriv_const_of_ne (by omega)]
      rfl
    rw [this, norm_zero]; exact norm_nonneg _

lemma sum_choose_le {n k : ℕ} (hn : n ≤ k) {b b' : ℝ} (hb : 0 ≤ b) (hb' : 0 ≤ b') :
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * b * b' ≤ 2 ^ k * b * b' := by
  have h1 : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * b * b' = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) * b * b' := by
    rw [Finset.sum_mul, Finset.sum_mul]
  have h2 : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [h1, h2]
  have : (2 : ℝ) ^ n ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hn
  gcongr

lemma JB.smul_mul (hU : UniqueDiffOn ℝ U) {f : Y → ℝ} {g : Y → V} {b b' : ℝ} (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (hf : ContDiffOn ℝ k f U) (hg : ContDiffOn ℝ k g U) (h : JB k U f b) (h' : JB k U g b') :
    JB k U (fun y => f y • g y) (2 ^ k * b * b') := by
  intro n hn y hy
  have hB : ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V)‖ ≤ 1 := ContinuousLinearMap.opNorm_lsmul_le
  have := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V).norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
    (f := f) (g := g) (N := k) hf hg hU hy (by exact_mod_cast hn) hB
  simp only [ContinuousLinearMap.lsmul_apply] at this
  refine this.trans ((Finset.sum_le_sum fun i hi => ?_).trans (sum_choose_le hn hb hb'))
  have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
  gcongr
  · exact h i (hi'.trans hn) y hy
  · exact h' (n - i) ((Nat.sub_le _ _).trans hn) y hy

lemma JB.clm_apply (hU : UniqueDiffOn ℝ U) {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {f : Y → Z →L[ℝ] W} {g : Y → Z}
    {b b' : ℝ} (hb : 0 ≤ b) (hb' : 0 ≤ b') (hf : ContDiffOn ℝ k f U) (hg : ContDiffOn ℝ k g U) (h : JB k U f b)
    (h' : JB k U g b') : JB k U (fun y => f y (g y)) (2 ^ k * b * b') := by
  intro n hn y hy
  have := norm_iteratedFDerivWithin_clm_apply hf hg hU hy (by exact_mod_cast hn)
  refine this.trans ((Finset.sum_le_sum fun i hi => ?_).trans (sum_choose_le hn hb hb'))
  have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
  gcongr
  · exact h i (hi'.trans hn) y hy
  · exact h' (n - i) ((Nat.sub_le _ _).trans hn) y hy

lemma JB.comp (hU : UniqueDiffOn ℝ U) {t : Set V} (ht : UniqueDiffOn ℝ t) {g : V → W} {f : Y → V} {C b : ℝ}
    (hg : ContDiffOn ℝ k g t) (hf : ContDiffOn ℝ k f U) (hst : MapsTo f U t) (hC0 : 0 ≤ C)
    (hC : ∀ y ∈ U, ∀ i ≤ k, ‖iteratedFDerivWithin ℝ i g t (f y)‖ ≤ C)
    (hb : ∀ i, 1 ≤ i → i ≤ k → ∀ y ∈ U, ‖iteratedFDerivWithin ℝ i f U y‖ ≤ b) :
    JB k U (g ∘ f) (k.factorial * C * (max 1 b) ^ k) := by
  intro n hn y hy
  have hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin ℝ i f U y‖ ≤ (max 1 b) ^ i := by
    intro i hi1 hin
    refine (hb i hi1 (hin.trans hn) y hy).trans ?_
    calc b ≤ max 1 b := le_max_right _ _
      _ = (max 1 b) ^ 1 := (pow_one _).symm
      _ ≤ (max 1 b) ^ i := pow_le_pow_right₀ (le_max_left _ _) hi1
  have := norm_iteratedFDerivWithin_comp_le (n := n) (N := k) hg hf (by exact_mod_cast hn) ht hU hst hy
    (fun i hi => hC y hy i (hi.trans hn)) hD
  refine this.trans ?_
  have hD1 : (1 : ℝ) ≤ max 1 b := le_max_left _ _
  have h1 : (max 1 b) ^ n ≤ (max 1 b) ^ k := pow_le_pow_right₀ hD1 hn
  have h2 : (n.factorial : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hn
  have h3 : 0 ≤ (max 1 b) ^ n := by positivity
  calc (n.factorial : ℝ) * C * (max 1 b) ^ n ≤ k.factorial * C * (max 1 b) ^ k := by gcongr

lemma norm_iteratedFDeriv_inv (i : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedFDeriv ℝ i (Inv.inv : ℝ → ℝ) x‖ = i.factorial * (x ^ (i + 1))⁻¹ := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_inv]
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast]
  rw [Real.norm_eq_abs, abs_of_pos (by positivity), show (-1 - (i : ℤ)) = -((i + 1 : ℕ) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast]

lemma JB.inv (hU : UniqueDiffOn ℝ U) {f : Y → ℝ} {m b : ℝ} (hm : 0 < m) (hf : ContDiffOn ℝ k f U)
    (hmin : ∀ y ∈ U, m ≤ f y) (hb : JB k U f b) :
    JB k U (fun y => (f y)⁻¹) (k.factorial * (k.factorial * (max 1 m⁻¹) ^ (k + 1)) * (max 1 b) ^ k) := by
  have ht : IsOpen (Ioi (m / 2)) := isOpen_Ioi
  have hsub : Ioi (m / 2) ⊆ ({0}ᶜ : Set ℝ) := fun x hx => by
    have : m / 2 < x := hx
    exact fun h0 => by rw [mem_singleton_iff] at h0; linarith [h0]
  have hg : ContDiffOn ℝ k (Inv.inv : ℝ → ℝ) (Ioi (m / 2)) := (contDiffOn_inv ℝ).mono hsub
  have hst : MapsTo f U (Ioi (m / 2)) := fun y hy => by
    have := hmin y hy
    show m / 2 < f y
    linarith
  have hC0 : 0 ≤ (k.factorial : ℝ) * (max 1 m⁻¹) ^ (k + 1) := by positivity
  refine JB.comp hU ht.uniqueDiffOn (g := Inv.inv) hg hf hst hC0 (fun y hy i hi => ?_) (fun i _ hi => hb i hi)
  rw [iteratedFDerivWithin_of_isOpen i ht (hst hy), norm_iteratedFDeriv_inv i (by have := hmin y hy; linarith)]
  have hx := hmin y hy
  have hx0 : 0 < f y := by linarith
  have h1 : (f y ^ (i + 1))⁻¹ ≤ (max 1 m⁻¹) ^ (k + 1) := by
    rw [← inv_pow]
    calc (f y)⁻¹ ^ (i + 1) ≤ (max 1 m⁻¹) ^ (i + 1) := by
          gcongr
          exact (inv_anti₀ hm hx).trans (le_max_right _ _)
      _ ≤ (max 1 m⁻¹) ^ (k + 1) := pow_le_pow_right₀ (le_max_left _ _) (by omega)
  have h2 : (i.factorial : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hi
  calc (i.factorial : ℝ) * (f y ^ (i + 1))⁻¹ ≤ k.factorial * (max 1 m⁻¹) ^ (k + 1) := by gcongr

lemma JB.congr {f g : Y → V} {b : ℝ} (h : JB k U f b) (hfg : ∀ y ∈ U, f y = g y) :
    JB k U g b := by
  intro i hi y hy
  rw [← iteratedFDerivWithin_congr (n := i) (fun z hz => hfg z hz) hy]
  exact h i hi y hy

lemma JB.clm_apply_const (hU : UniqueDiffOn ℝ U) {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : Y → Z →L[ℝ] W} {b : ℝ} (hf : ContDiffOn ℝ k f U) (c : Z) (h : JB k U f b) :
    JB k U (fun y => f y c) (‖c‖ * b) := by
  intro n hn y hy
  have := norm_iteratedFDerivWithin_clm_apply_const (c := c) ((hf y hy).of_le (by exact_mod_cast hn)) hU hy
    (le_refl _)
  exact this.trans (mul_le_mul_of_nonneg_left (h n hn y hy) (norm_nonneg _))

lemma JB.clm_comp_left (hU : UniqueDiffOn ℝ U) (T : V →L[ℝ] W) {f : Y → V} {b : ℝ} (hf : ContDiffOn ℝ k f U)
    (h : JB k U f b) : JB k U (fun y => T (f y)) (‖T‖ * b) := by
  intro n hn y hy
  have := T.norm_iteratedFDerivWithin_comp_left (n := n) (N := k) (hf y hy) hU hy (by exact_mod_cast hn)
  exact this.trans (mul_le_mul_of_nonneg_left (h n hn y hy) (norm_nonneg _))

/-- Derivative of a `JB (j+1)` function is `JB j`. -/
lemma JB.succ_fderivWithin (hU : UniqueDiffOn ℝ U) {f : Y → V} {b : ℝ} {j : ℕ} (h : JB (j + 1) U f b) :
    JB j U (fderivWithin ℝ f U) b := by
  intro i hi y hy
  rw [norm_iteratedFDerivWithin_fderivWithin hU hy]
  exact h (i + 1) (by omega) y hy

lemma JB.of_fderivWithin (hU : UniqueDiffOn ℝ U) {f : Y → V} {b0 b1 : ℝ} {j : ℕ}
    (h0 : ∀ y ∈ U, ‖f y‖ ≤ b0) (h : JB j U (fderivWithin ℝ f U) b1) : JB (j + 1) U f (max b0 b1) := by
  intro i hi y hy
  cases i with
  | zero =>
    have : ‖iteratedFDerivWithin ℝ 0 f U y‖ = ‖f y‖ := by simp [iteratedFDerivWithin_zero_eq_comp]
    rw [this]; exact (h0 y hy).trans (le_max_left _ _)
  | succ n =>
    rw [← norm_iteratedFDerivWithin_fderivWithin hU hy]
    exact (h n (by omega) y hy).trans (le_max_right _ _)

lemma norm_iteratedFDerivWithin_id_le (hU : UniqueDiffOn ℝ U) {i : ℕ} (hi : 1 ≤ i) {y : Y} (hy : y ∈ U) :
    ‖iteratedFDerivWithin ℝ i (id : Y → Y) U y‖ ≤ 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  rw [← norm_iteratedFDerivWithin_fderivWithin hU hy]
  have h1 : JB n U (fun _ : Y => ContinuousLinearMap.id ℝ Y) ‖ContinuousLinearMap.id ℝ Y‖ := JB.const hU _
  have h2 : JB n U (fderivWithin ℝ (id : Y → Y) U) ‖ContinuousLinearMap.id ℝ Y‖ :=
    h1.congr fun z hz => (fderivWithin_id (hU.uniqueDiffWithinAt hz)).symm
  exact (h2 n le_rfl y hy).trans ContinuousLinearMap.norm_id_le

/-- Orders `≥ 1` of the graph map `y ↦ (y, w y)`. -/
lemma norm_iteratedFDerivWithin_graph_le (hU : UniqueDiffOn ℝ U) {w : Y → ℝ} (hw : ContDiffOn ℝ k w U) {b : ℝ}
    (hb : ∀ i, 1 ≤ i → i ≤ k → ∀ y ∈ U, ‖iteratedFDerivWithin ℝ i w U y‖ ≤ b) :
    ∀ i, 1 ≤ i → i ≤ k → ∀ y ∈ U, ‖iteratedFDerivWithin ℝ i (fun y => (y, w y)) U y‖ ≤ max 1 b := by
  intro i hi1 hik y hy
  have e := iteratedFDerivWithin_prodMk (f := (id : Y → Y)) (g := w) (n := k) (s := U) (x := y)
    contDiffWithinAt_id (hw y hy) hU hy (i := i) (by exact_mod_cast hik)
  have e' : iteratedFDerivWithin ℝ i (fun y => (y, w y)) U y =
      (iteratedFDerivWithin ℝ i (id : Y → Y) U y).prod (iteratedFDerivWithin ℝ i w U y) := e
  rw [e', ContinuousMultilinearMap.opNorm_prod]
  exact max_le_max (norm_iteratedFDerivWithin_id_le hU hi1 hy) (hb i hi1 hik y hy)

lemma norm_iteratedFDerivWithin_clm_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {U : Set X}
    (hU : UniqueDiffOn ℝ U) (L : X →L[ℝ] V) {i : ℕ} (hi : 1 ≤ i) {x : X} (hx : x ∈ U) :
    ‖iteratedFDerivWithin ℝ i (fun x => L x) U x‖ ≤ ‖L‖ := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  rw [← norm_iteratedFDerivWithin_fderivWithin hU hx]
  have h1 : JB n U (fun _ : X => L) ‖L‖ := JB.const hU _
  have h2 : JB n U (fderivWithin ℝ (fun x => L x) U) ‖L‖ :=
    h1.congr fun z hz => (L.fderivWithin (hU.uniqueDiffWithinAt hz)).symm
  exact h2 n le_rfl x hx

/-- A continuous linear map has `JB` bound `M` if `M` bounds its norm and its values on `U`. -/
lemma JB.clm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {U : Set X} (hU : UniqueDiffOn ℝ U)
    (L : X →L[ℝ] V) {M : ℝ} (hL : ‖L‖ ≤ M) (h0 : ∀ x ∈ U, ‖L x‖ ≤ M) : JB k U (fun x => L x) M := by
  intro i hi x hx
  cases i with
  | zero => simpa [iteratedFDerivWithin_zero_eq_comp] using h0 x hx
  | succ n => exact (norm_iteratedFDerivWithin_clm_le hU L (by omega) hx).trans hL

lemma JB.snd {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {U : Set (P × ℝ)} (hU : UniqueDiffOn ℝ U)
    {M : ℝ} (hM : 1 ≤ M) (h0 : ∀ p ∈ U, |p.2| ≤ M) : JB k U (fun p : P × ℝ => p.2) M :=
  JB.clm hU (ContinuousLinearMap.snd ℝ P ℝ)
    ((ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun p => by
      simpa using (norm_snd_le p).trans (by nlinarith [norm_nonneg p]))) (fun p hp => by simpa using h0 p hp)

lemma JB.comp_inl {P Z : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] {U : Set P} (hU : UniqueDiffOn ℝ U) {A : P → (Y × Z) →L[ℝ] ℝ} {b : ℝ} (hb0 : 0 ≤ b)
    (hA : ContDiffOn ℝ k A U) (h : JB k U A b) :
    JB k U (fun p => (A p).comp (ContinuousLinearMap.inl ℝ Y Z)) b := by
  have h1 := JB.clm_comp_left hU (ContinuousLinearMap.precomp ℝ (ContinuousLinearMap.inl ℝ Y Z) :
    ((Y × Z) →L[ℝ] ℝ) →L[ℝ] (Y →L[ℝ] ℝ)) hA h
  have hn : ‖(ContinuousLinearMap.precomp ℝ (ContinuousLinearMap.inl ℝ Y Z) :
      ((Y × Z) →L[ℝ] ℝ) →L[ℝ] (Y →L[ℝ] ℝ))‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    simp only [ContinuousLinearMap.precomp_apply, one_mul]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have : ‖ContinuousLinearMap.inl ℝ Y Z‖ ≤ 1 := ContinuousLinearMap.norm_inl_le_one ℝ Y Z
    nlinarith [norm_nonneg f, norm_nonneg (ContinuousLinearMap.inl ℝ Y Z)]
  exact h1.mono (mul_le_of_le_one_left hb0 hn)

/-- Composition with a continuous linear map of norm `≤ 1`. -/
lemma JB.comp_clm {X X' : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup X']
    [NormedSpace ℝ X'] {U : Set X} {t : Set X'} (hU : UniqueDiffOn ℝ U) (ht : UniqueDiffOn ℝ t) (L : X →L[ℝ] X')
    (hL : ‖L‖ ≤ 1) {g : X' → W} {b : ℝ} (hb0 : 0 ≤ b) (hg : ContDiffOn ℝ k g t) (hst : MapsTo L U t)
    (hb : JB k t g b) : JB k U (fun x => g (L x)) (k.factorial * b) := by
  have h := JB.comp (k := k) hU ht (g := g) (f := fun x => L x) (C := b) (b := 1) hg
    (L.contDiff.contDiffOn) hst hb0 (fun y hy i hi => hb i hi _ (hst hy))
    (fun i hi1 _ y hy => (norm_iteratedFDerivWithin_clm_le hU L hi1 hy).trans hL)
  exact h.mono (le_of_eq (by simp))

/-- Orders `≥ 1` of a pair of functions. -/
lemma norm_iteratedFDerivWithin_pair_le {V1 V2 : Type*} [NormedAddCommGroup V1] [NormedSpace ℝ V1]
    [NormedAddCommGroup V2] [NormedSpace ℝ V2] (hU : UniqueDiffOn ℝ U) {u : Y → V1} {w : Y → V2}
    (hu : ContDiffOn ℝ k u U) (hw : ContDiffOn ℝ k w U) {b1 b2 : ℝ}
    (h1 : ∀ i, 1 ≤ i → i ≤ k → ∀ y ∈ U, ‖iteratedFDerivWithin ℝ i u U y‖ ≤ b1)
    (h2 : ∀ i, 1 ≤ i → i ≤ k → ∀ y ∈ U, ‖iteratedFDerivWithin ℝ i w U y‖ ≤ b2) :
    ∀ i, 1 ≤ i → i ≤ k → ∀ y ∈ U, ‖iteratedFDerivWithin ℝ i (fun y => (u y, w y)) U y‖ ≤ max b1 b2 := by
  intro i hi1 hik y hy
  have e := iteratedFDerivWithin_prodMk (f := u) (g := w) (n := k) (s := U) (x := y)
    (hu y hy) (hw y hy) hU hy (i := i) (by exact_mod_cast hik)
  have e' : iteratedFDerivWithin ℝ i (fun y => (u y, w y)) U y =
      (iteratedFDerivWithin ℝ i u U y).prod (iteratedFDerivWithin ℝ i w U y) := e
  rw [e', ContinuousMultilinearMap.opNorm_prod]
  exact max_le_max (h1 i hi1 hik y hy) (h2 i hi1 hik y hy)

/-- `ε`-linear composition: if `f` is `ε`-small in `JB (j+1)` and `g` has bounded `JB (j+1)` jets on an open interval `T ∋ 0`
containing the range of `f`, then `g ∘ f - g 0` is `C ε` in `JB (j+1)`, `C = (1 + 2^j j!) C_g` (for `ε ≤ 1`). -/
lemma JB.comp_small {j : ℕ} {U : Set Y} (hU : UniqueDiffOn ℝ U) {T : Set ℝ} (hT : IsOpen T) (hTc : Convex ℝ T)
    (h0T : (0 : ℝ) ∈ T) {g : ℝ → ℝ} {Cg : ℝ} (hg : ContDiffOn ℝ (j + 1) g T) (hgb : JB (j + 1) T g Cg)
    {f : Y → ℝ} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hCg0 : 0 ≤ Cg) (hf : ContDiffOn ℝ (j + 1) f U) (hfb : JB (j + 1) U f ε)
    (hfT : MapsTo f U T) :
    JB (j + 1) U (fun y => g (f y) - g 0) ((1 + 2 ^ j * j.factorial) * Cg * ε) := by
  have hTd : UniqueDiffOn ℝ T := hT.uniqueDiffOn
  -- derivative of g as a function
  have hg1 : ContDiffOn ℝ j (fun x => fderiv ℝ g x 1) T :=
    (hg.fderiv_of_isOpen hT (by exact_mod_cast le_rfl : (j : ℕ∞ω) + 1 ≤ (j + 1 : ℕ))).clm_apply contDiffOn_const
  have hg1b : JB j T (fun x => fderiv ℝ g x 1) Cg := by
    have h1 : JB j T (fderiv ℝ g) Cg := (hgb.succ_fderivWithin hTd).congr fun p hp => fderivWithin_of_isOpen hT hp
    have h2 := JB.clm_apply_const hTd (hg.fderiv_of_isOpen hT (by exact_mod_cast le_rfl : (j : ℕ∞ω) + 1 ≤ (j + 1 : ℕ))) (1 : ℝ) h1
    simpa using h2
  have hfj : ContDiffOn ℝ j f U := hf.of_le (by exact_mod_cast Nat.le_succ j)
  have hDf : JB j U (fderivWithin ℝ f U) ε := hfb.succ_fderivWithin hU
  have hDfc : ContDiffOn ℝ j (fderivWithin ℝ f U) U :=
    hf.fderivWithin hU (by exact_mod_cast le_rfl : (j : ℕ∞ω) + 1 ≤ (j + 1 : ℕ))
  -- g' ∘ f
  have hcomp := JB.comp hU hTd (g := fun x => fderiv ℝ g x 1) hg1 hfj hfT hCg0
    (fun y hy i hi => hg1b i hi _ (hfT hy)) (b := 1) (fun i hi1 hij y hy => by
      have := hfb i (by omega) y hy
      exact this.trans hε1)
  have hcompc : ContDiffOn ℝ j ((fun x => fderiv ℝ g x 1) ∘ f) U := hg1.comp hfj hfT
  have hprod := JB.smul_mul hU (by positivity) hε0 hcompc hDfc hcomp hDf
  -- the derivative of the composite
  have hderiv : ∀ y ∈ U, fderivWithin ℝ (fun y => g (f y) - g 0) U y =
      ((fun x => fderiv ℝ g x 1) ∘ f) y • fderivWithin ℝ f U y := by
    intro y hy
    have hk0 : ((j + 1 : ℕ) : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hgat : DifferentiableAt ℝ g (f y) :=
      ((hg.contDiffAt (hT.mem_nhds (hfT hy))).differentiableAt (by exact_mod_cast hk0))
    have hgd : HasDerivAt g (fderiv ℝ g (f y) 1) (f y) := by
      have := hgat.hasDerivAt
      exact this
    have hfd : HasFDerivWithinAt f (fderivWithin ℝ f U y) U y :=
      ((hf y hy).differentiableWithinAt (by exact_mod_cast hk0)).hasFDerivWithinAt
    have := (hgd.comp_hasFDerivWithinAt y hfd).sub_const (g 0)
    exact this.fderivWithin (hU.uniqueDiffWithinAt hy)
  have hfin := hprod.congr (g := fderivWithin ℝ (fun y => g (f y) - g 0) U) fun y hy => (hderiv y hy).symm
  have h0 : ∀ y ∈ U, ‖g (f y) - g 0‖ ≤ Cg * ε := by
    intro y hy
    have hk0 : ((j + 1 : ℕ) : ℕ∞ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hdiff : ∀ x ∈ T, DifferentiableAt ℝ g x := fun x hx =>
      (hg.contDiffAt (hT.mem_nhds hx)).differentiableAt (by exact_mod_cast hk0)
    have hbd : ∀ x ∈ T, ‖deriv g x‖ ≤ Cg := fun x hx => by
      have := hg1b 0 (Nat.zero_le _) x hx
      have h' : ‖(fderiv ℝ g x) 1‖ ≤ Cg := by simpa [iteratedFDerivWithin_zero_eq_comp] using this
      exact h'
    have h1 := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbd hTc h0T (hfT hy)
    have h2 : ‖f y‖ ≤ ε := by
      have := hfb 0 (Nat.zero_le _) y hy
      simpa [iteratedFDerivWithin_zero_eq_comp] using this
    calc ‖g (f y) - g 0‖ ≤ Cg * ‖f y - 0‖ := h1
      _ ≤ Cg * ε := by rw [sub_zero]; exact mul_le_mul_of_nonneg_left h2 hCg0
  have := JB.of_fderivWithin hU h0 hfin
  refine this.mono (max_le ?_ ?_)
  · nlinarith [mul_nonneg hCg0 hε0, mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 2 ^ j * j.factorial) hCg0) hε0]
  · simp only [max_self, one_pow, mul_one]
    nlinarith [mul_nonneg hCg0 hε0]

/-- info: 'FormalResearch.SignUncertainty.JB.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms JB.comp

/-- info: 'FormalResearch.SignUncertainty.JB.inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms JB.inv

/-- info: 'FormalResearch.SignUncertainty.JB.add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms JB.add

/-- info: 'FormalResearch.SignUncertainty.JB.smul_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms JB.smul_mul

/-- info: 'FormalResearch.SignUncertainty.JB.clm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms JB.clm_apply

/-- info: 'FormalResearch.SignUncertainty.JB.succ_fderivWithin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms JB.succ_fderivWithin

/-- info: 'FormalResearch.SignUncertainty.JB.of_fderivWithin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms JB.of_fderivWithin

/-- info: 'FormalResearch.SignUncertainty.JB.comp_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms JB.comp_inl

/-- info: 'FormalResearch.SignUncertainty.JB.snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms JB.snd

/-- info: 'FormalResearch.SignUncertainty.norm_iteratedFDerivWithin_graph_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_iteratedFDerivWithin_graph_le

/-- info: 'FormalResearch.SignUncertainty.JB.comp_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms JB.comp_small

/-- info: 'FormalResearch.SignUncertainty.JB.comp_clm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms JB.comp_clm

/-- info: 'FormalResearch.SignUncertainty.JB.clm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms JB.clm

/-- info: 'FormalResearch.SignUncertainty.norm_iteratedFDerivWithin_pair_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_iteratedFDerivWithin_pair_le

end FormalResearch.SignUncertainty
