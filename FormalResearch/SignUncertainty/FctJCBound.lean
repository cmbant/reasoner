/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctJC

/-!
# Uniform bound towers for the `JC` calculus (F2a, `fct:comp-cfu`)

A universal one-step bound function `Φb`: every output bound of a single operation of the `JC` calculus (sums, products,
compositions, orders `≤ 18`) is `≤ Φb (max inputs)`.  `JCΦ k U f β m` says `JC k U f (Φb^[m] β)`; the wrappers `JCΦ.*` let
a chain of operations be written with an explicit stage number, so that the resulting bound depends only on the base bound `β`
and not on the data (uniformity in the parameter box).

Class: proved.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace FormalResearch.SignUncertainty

/-- A universal bound function: every one-step output bound of the `JC` calculus (orders `≤ 18`) is `≤ Φb (max inputs)`. -/
noncomputable def Φb (β : ℝ) : ℝ := (Nat.factorial 18 : ℝ) * 2 ^ 18 * (max 1 β) ^ 19

lemma Φb_ge (β : ℝ) : max 1 β ≤ Φb β := by
  have h1 : (1 : ℝ) ≤ Nat.factorial 18 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero 18)
  have h2 : (1 : ℝ) ≤ 2 ^ 18 := one_le_pow₀ (by norm_num)
  have h3 : max 1 β ≤ (max 1 β) ^ 19 := by
    have := le_max_left (1 : ℝ) β
    calc max 1 β = (max 1 β) ^ 1 := (pow_one _).symm
      _ ≤ (max 1 β) ^ 19 := pow_le_pow_right₀ this (by norm_num)
  unfold Φb
  have h4 : (1 : ℝ) ≤ (Nat.factorial 18 : ℝ) * 2 ^ 18 := by nlinarith
  calc max 1 β ≤ (max 1 β) ^ 19 := h3
    _ = 1 * (max 1 β) ^ 19 := (one_mul _).symm
    _ ≤ _ := by gcongr

lemma Φb_ge2 (β : ℝ) : 2 * max 1 β ≤ Φb β := by
  have h1 : (2 : ℝ) ≤ Nat.factorial 18 := by
    have : 2 ≤ Nat.factorial 18 := by
      calc 2 = Nat.factorial 2 := by decide
        _ ≤ Nat.factorial 18 := Nat.factorial_le (by norm_num)
    exact_mod_cast this
  have h2 : (1 : ℝ) ≤ 2 ^ 18 := one_le_pow₀ (by norm_num)
  have h3 : max 1 β ≤ (max 1 β) ^ 19 := by
    have := le_max_left (1 : ℝ) β
    calc max 1 β = (max 1 β) ^ 1 := (pow_one _).symm
      _ ≤ (max 1 β) ^ 19 := pow_le_pow_right₀ this (by norm_num)
  unfold Φb
  have hm : 0 ≤ max 1 β := le_trans zero_le_one (le_max_left _ _)
  calc 2 * max 1 β ≤ Nat.factorial 18 * 1 * max 1 β := by nlinarith
    _ ≤ Nat.factorial 18 * 2 ^ 18 * max 1 β := by gcongr
    _ ≤ _ := by gcongr

lemma Φb_mono : Monotone Φb := fun a b hab => by
  unfold Φb; gcongr

lemma Φb_nonneg (β : ℝ) : 0 ≤ Φb β := (le_trans (le_max_left 1 β |> fun h => by linarith) (Φb_ge β))

lemma Φb_iter_mono {m m' : ℕ} (h : m ≤ m') (β : ℝ) : Φb^[m] β ≤ Φb^[m'] β := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (by rw [Function.iterate_succ_apply']; exact (le_max_right 1 _).trans (Φb_ge _))

lemma Φb_iter_ge (m : ℕ) (β : ℝ) : β ≤ Φb^[m] β := by
  simpa using Φb_iter_mono (Nat.zero_le m) β


section Stage
variable {Y V W : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {k : ℕ} {U : Set Y}

/-- `JC` with the bound given as a `Φb`-tower of stage `m` over the base bound `β`. -/
def JCΦ (k : ℕ) (U : Set Y) (f : Y → V) (β : ℝ) (m : ℕ) : Prop := JC k U f (Φb^[m] β)

lemma JCΦ.mono_m {f : Y → V} {β : ℝ} {m m' : ℕ} (h : JCΦ k U f β m) (hm : m ≤ m') : JCΦ k U f β m' :=
  JC.mono h (Φb_iter_mono hm β)

lemma JCΦ.congr {f g : Y → V} {β : ℝ} {m : ℕ} (h : JCΦ k U f β m) (hfg : ∀ y ∈ U, f y = g y) : JCΦ k U g β m :=
  JC.congr h hfg

lemma JCΦ.mono_order {k' : ℕ} {f : Y → V} {β : ℝ} {m : ℕ} (h : JCΦ k U f β m) (hk : k' ≤ k) : JCΦ k' U f β m :=
  JC.mono_order h hk

lemma Φb_step {x β : ℝ} {a m : ℕ} (hx : x ≤ Φb^[a] β) (h : a + 1 ≤ m) : Φb x ≤ Φb^[m] β :=
  (Φb_mono hx).trans (by rw [← Function.iterate_succ_apply' Φb a β]; exact Φb_iter_mono h β)

lemma Φb_iter_nonneg {β : ℝ} (hβ : 0 ≤ β) (m : ℕ) : 0 ≤ Φb^[m] β := hβ.trans (Φb_iter_ge m β)

lemma max_le_iter {x y β : ℝ} {a b m : ℕ} (hx : x ≤ Φb^[a] β) (hy : y ≤ Φb^[b] β) (ha : a ≤ m) (hb : b ≤ m) :
    max x y ≤ Φb^[m] β := max_le (hx.trans (Φb_iter_mono ha β)) (hy.trans (Φb_iter_mono hb β))

lemma mul_le_Φb {k : ℕ} (hk : k ≤ 18) {b b' : ℝ} (hb : 0 ≤ b) (hb' : 0 ≤ b') : 2 ^ k * b * b' ≤ Φb (max b b') := by
  have hm : max b b' ≤ max 1 (max b b') := le_max_right _ _
  have hm0 : 0 ≤ max b b' := le_max_of_le_left hb
  have h1 : (1 : ℝ) ≤ Nat.factorial 18 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero 18)
  have h2 : (2 : ℝ) ^ k ≤ 2 ^ 18 := pow_le_pow_right₀ (by norm_num) hk
  have h3 : b * b' ≤ (max 1 (max b b')) ^ 19 := by
    have hM : 1 ≤ max 1 (max b b') := le_max_left _ _
    calc b * b' ≤ max b b' * max b b' := by gcongr <;> simp
      _ ≤ (max 1 (max b b')) * (max 1 (max b b')) := by gcongr
      _ = (max 1 (max b b')) ^ 2 := (sq _).symm
      _ ≤ (max 1 (max b b')) ^ 19 := pow_le_pow_right₀ hM (by norm_num)
  unfold Φb
  calc 2 ^ k * b * b' = 2 ^ k * (b * b') := by ring
    _ ≤ 2 ^ 18 * (max 1 (max b b')) ^ 19 := by gcongr
    _ = 1 * 2 ^ 18 * (max 1 (max b b')) ^ 19 := by ring
    _ ≤ _ := by gcongr

lemma add_le_Φb {b b' : ℝ} : b + b' ≤ Φb (max b b') := by
  have := Φb_ge2 (max b b')
  have h1 : b ≤ max b b' := le_max_left _ _
  have h2 : b' ≤ max b b' := le_max_right _ _
  have h3 : max b b' ≤ max 1 (max b b') := le_max_right _ _
  linarith

lemma fact_mul_le_Φb {k : ℕ} (hk : k ≤ 18) {b : ℝ} (hb : 0 ≤ b) : (k.factorial : ℝ) * b ≤ Φb b := by
  have h1 : (k.factorial : ℝ) ≤ Nat.factorial 18 := by exact_mod_cast Nat.factorial_le hk
  have h2 : b ≤ max 1 b := le_max_right _ _
  have h3 : (1 : ℝ) ≤ max 1 b := le_max_left _ _
  have h4 : max 1 b ≤ (max 1 b) ^ 19 := by
    calc max 1 b = (max 1 b) ^ 1 := (pow_one _).symm
      _ ≤ (max 1 b) ^ 19 := pow_le_pow_right₀ h3 (by norm_num)
  unfold Φb
  have h5 : (1 : ℝ) ≤ 2 ^ 18 := one_le_pow₀ (by norm_num)
  calc (k.factorial : ℝ) * b ≤ (Nat.factorial 18 : ℝ) * (max 1 b) ^ 19 := by gcongr; exact h2.trans h4
    _ = (Nat.factorial 18 : ℝ) * 1 * (max 1 b) ^ 19 := by ring
    _ ≤ _ := by gcongr

lemma comp_le_Φb {k : ℕ} (hk : k ≤ 18) {C b : ℝ} (hC : 0 ≤ C) : (k.factorial : ℝ) * C * (max 1 b) ^ k ≤ Φb (max C b) := by
  have h1 : (k.factorial : ℝ) ≤ Nat.factorial 18 := by exact_mod_cast Nat.factorial_le hk
  have hM : (1 : ℝ) ≤ max 1 (max C b) := le_max_left _ _
  have h2 : (max 1 b) ^ k ≤ (max 1 (max C b)) ^ 18 := by
    calc (max 1 b) ^ k ≤ (max 1 (max C b)) ^ k := by
          gcongr; exact le_max_right C b
      _ ≤ _ := pow_le_pow_right₀ hM hk
  have h3 : C ≤ max 1 (max C b) := (le_max_left _ _).trans (le_max_right _ _)
  unfold Φb
  have h5 : (1 : ℝ) ≤ 2 ^ 18 := one_le_pow₀ (by norm_num)
  have hf0 : (0 : ℝ) ≤ Nat.factorial 18 := by positivity
  calc (k.factorial : ℝ) * C * (max 1 b) ^ k ≤ (Nat.factorial 18 : ℝ) * (max 1 (max C b)) * (max 1 (max C b)) ^ 18 :=
        mul_le_mul (mul_le_mul h1 h3 hC hf0) h2 (by positivity) (by positivity)
    _ = (Nat.factorial 18 : ℝ) * 1 * (max 1 (max C b)) ^ 19 := by ring
    _ ≤ _ := by gcongr

lemma comp_pair_le_Φb {k : ℕ} (hk : k ≤ 18) {C b1 b2 : ℝ} (hC : 0 ≤ C) :
    (k.factorial : ℝ) * C * (max 1 (max b1 b2)) ^ k ≤ Φb (max C (max b1 b2)) := comp_le_Φb hk hC


variable {β : ℝ} {a b m : ℕ}

lemma JCΦ.add (hU : UniqueDiffOn ℝ U) {f g : Y → ℝ} (hf : JCΦ k U f β a) (hg : JCΦ k U g β b)
    (h : max a b + 1 ≤ m) : JCΦ k U (fun y => f y + g y) β m := by
  refine JC.mono (JC.add hU hf hg) ?_
  exact add_le_Φb.trans (Φb_step (max_le_iter le_rfl le_rfl (le_max_left a b) (le_max_right a b)) h)

lemma JCΦ.sub (hU : UniqueDiffOn ℝ U) {f g : Y → ℝ} (hf : JCΦ k U f β a) (hg : JCΦ k U g β b)
    (h : max a b + 1 ≤ m) : JCΦ k U (fun y => f y - g y) β m := by
  refine JC.mono (JC.sub hU hf hg) ?_
  exact add_le_Φb.trans (Φb_step (max_le_iter le_rfl le_rfl (le_max_left a b) (le_max_right a b)) h)

lemma JCΦ.mul (hU : UniqueDiffOn ℝ U) (hβ : 0 ≤ β) (hk : k ≤ 18) {f g : Y → ℝ} (hf : JCΦ k U f β a)
    (hg : JCΦ k U g β b) (h : max a b + 1 ≤ m) : JCΦ k U (fun y => f y * g y) β m := by
  refine JC.mono (JC.mul hU (Φb_iter_nonneg hβ a) (Φb_iter_nonneg hβ b) hf hg) ?_
  exact (mul_le_Φb hk (Φb_iter_nonneg hβ a) (Φb_iter_nonneg hβ b)).trans
    (Φb_step (max_le_iter le_rfl le_rfl (le_max_left a b) (le_max_right a b)) h)

lemma JCΦ.const (hU : UniqueDiffOn ℝ U) {c : ℝ} {m : ℕ} (hc : |c| ≤ Φb^[m] β) : JCΦ k U (fun _ : Y => c) β m := by
  refine JC.mono (JC.const hU c) ?_
  rw [Real.norm_eq_abs]
  exact hc

lemma JCΦ.integral01 {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {O : Set P} (hO : IsOpen O)
    {f : P → ℝ → ℝ} (h : JCΦ k (O ×ˢ Icc (0 : ℝ) 1) (fun p : P × ℝ => f p.1 p.2) β m) :
    JCΦ k O (fun y => ∫ σ in Icc (0 : ℝ) 1, f y σ) β m := JC.integral01 hO h

lemma JCΦ.deriv_snd {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {U : Set (P × ℝ)}
    {j : ℕ} {f : P × ℝ → ℝ} (hU : IsOpen U) (h : JCΦ (j + 1) U f β m) :
    JCΦ j U (fun q => fderiv ℝ f q (0, 1)) β m := JC.deriv_snd hU h

lemma JCΦ.snd {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {U : Set (P × ℝ)} (hU : UniqueDiffOn ℝ U)
    (hβ : 1 ≤ β) (h0 : ∀ p ∈ U, |p.2| ≤ β) (m : ℕ) : JCΦ k U (fun p : P × ℝ => p.2) β m :=
  JC.mono (JC.snd hU hβ h0) (Φb_iter_ge m β)

lemma JCΦ.comp_clm (hU : UniqueDiffOn ℝ U) {X' : Type*} [NormedAddCommGroup X'] [NormedSpace ℝ X'] {t : Set X'}
    (ht : UniqueDiffOn ℝ t) (hβ : 0 ≤ β) (hk : k ≤ 18) (L : Y →L[ℝ] X') (hL : ‖L‖ ≤ 1) {g : X' → ℝ}
    (hg : JCΦ k t g β a) (hst : MapsTo L U t) (h : a + 1 ≤ m) : JCΦ k U (fun x => g (L x)) β m :=
  JC.mono (JC.comp_clm hU ht L hL (Φb_iter_nonneg hβ a) hg hst)
    ((fact_mul_le_Φb hk (Φb_iter_nonneg hβ a)).trans (Φb_step le_rfl h))

lemma JCΦ.comp_pair (hU : UniqueDiffOn ℝ U) {X1 X2 : Type*} [NormedAddCommGroup X1] [NormedSpace ℝ X1]
    [NormedAddCommGroup X2] [NormedSpace ℝ X2] {t : Set (X1 × X2)} (ht : UniqueDiffOn ℝ t) (hβ : 0 ≤ β)
    (hk : k ≤ 18) {g : X1 × X2 → ℝ} {u : Y → X1} {w : Y → X2} {a1 a2 a3 : ℕ} (hg : JCΦ k t g β a1)
    (hu : ContDiffOn ℝ k u U) (hw : ContDiffOn ℝ k w U)
    (hu1 : ∀ i, 1 ≤ i → i ≤ k → ∀ y ∈ U, ‖iteratedFDerivWithin ℝ i u U y‖ ≤ Φb^[a2] β)
    (hw1 : ∀ i, 1 ≤ i → i ≤ k → ∀ y ∈ U, ‖iteratedFDerivWithin ℝ i w U y‖ ≤ Φb^[a3] β)
    (hst : MapsTo (fun y => (u y, w y)) U t) (h : max a1 (max a2 a3) + 1 ≤ m) :
    JCΦ k U (fun y => g (u y, w y)) β m := by
  refine JC.mono (JC.comp_pair hU ht (Φb_iter_nonneg hβ a1) hg hu hw hu1 hw1 hst) ?_
  refine (comp_pair_le_Φb hk (Φb_iter_nonneg hβ a1)).trans (Φb_step ?_ h)
  exact max_le (Φb_iter_mono (le_max_left _ _) β) (max_le (Φb_iter_mono (le_trans (le_max_left a2 a3)
    (le_max_right a1 _)) β) (Φb_iter_mono (le_trans (le_max_right a2 a3) (le_max_right a1 _)) β))

end Stage
/-- info: 'FormalResearch.SignUncertainty.JCΦ.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms JCΦ.mul

/-- info: 'FormalResearch.SignUncertainty.JCΦ.comp_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms JCΦ.comp_pair

/-- info: 'FormalResearch.SignUncertainty.Φb_iter_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Φb_iter_mono

end FormalResearch.SignUncertainty
