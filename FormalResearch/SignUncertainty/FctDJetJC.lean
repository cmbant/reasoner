/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctDJetBase
public import FormalResearch.SignUncertainty.FctJCBound

/-!
# Stage-bounded composition with a function of one variable (F2a, `(fct:dJ-jets)`)

`JCΦ.comp1`: composition of a stage-bounded `JC` function of one variable on a set `t` with a stage-bounded function
`U → ℝ` mapping into `t`; `rpowΦ`: `x ↦ x^r` (`-1 ≤ r ≤ 1`) on `(m, M)` is stage `1` when `max 1 m⁻¹, max 1 M ≤ β`; `JCΦ.rpow_comp`:
the power `f^r` of a stage-bounded function with values in `(m, M)`.

Class: proved, no hypotheses beyond those stated.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace FormalResearch.SignUncertainty
section DJetJC
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {k : ℕ} {U : Set Y} {β : ℝ} {a1 a2 m : ℕ}

lemma JCΦ.comp1 (hU : UniqueDiffOn ℝ U) {t : Set ℝ} (ht : UniqueDiffOn ℝ t) (hβ : 0 ≤ β) (hk : k ≤ 18)
    {g : ℝ → ℝ} {f : Y → ℝ} (hg : JCΦ k t g β a1) (hf : JCΦ k U f β a2) (hst : MapsTo f U t)
    (h : max a1 a2 + 1 ≤ m) : JCΦ k U (fun y => g (f y)) β m := by
  refine JC.mono (JC.comp hU ht (Φb_iter_nonneg hβ a1) hg hf hst) ?_
  refine (comp_le_Φb hk (Φb_iter_nonneg hβ a1)).trans (Φb_step ?_ h)
  exact max_le_iter le_rfl le_rfl (le_max_left a1 a2) (le_max_right a1 a2)

lemma rpowΦ {r m' M : ℝ} (hk : k ≤ 16) (hr1 : -1 ≤ r) (hr2 : r ≤ 1) (hm : 0 < m') (hmβ : max 1 m'⁻¹ ≤ β)
    (hMβ : max 1 M ≤ β) : JCΦ k (Ioo m' M) (fun x : ℝ => x ^ r) β 1 := by
  refine JC.mono (rpow_jc k hr1 hr2 hm) ?_
  have hR : (1 : ℝ) ≤ max 1 m'⁻¹ := le_max_left _ _
  have hβ1 : (1 : ℝ) ≤ β := hR.trans hmβ
  have h1 : (k.factorial : ℝ) ≤ Nat.factorial 18 := by exact_mod_cast Nat.factorial_le (by omega)
  have h2 : max 1 M * max 1 m'⁻¹ ≤ β * β := mul_le_mul hMβ hmβ (by positivity) (by linarith)
  have h3 : (max 1 m'⁻¹) ^ k ≤ β ^ k := by gcongr
  have h4 : β * β * β ^ k ≤ β ^ 19 := by
    calc β * β * β ^ k = β ^ (k + 2) := by ring
      _ ≤ β ^ 19 := pow_le_pow_right₀ hβ1 (by omega)
  have h5 : (1 : ℝ) ≤ 2 ^ 18 := one_le_pow₀ (by norm_num)
  have hf0 : (0 : ℝ) ≤ Nat.factorial 18 := by positivity
  simp only [Function.iterate_one, Φb]
  rw [max_eq_right hβ1]
  calc (k.factorial : ℝ) * (max 1 M * max 1 m'⁻¹) * (max 1 m'⁻¹) ^ k
      ≤ (Nat.factorial 18 : ℝ) * (β * β) * β ^ k :=
        mul_le_mul (mul_le_mul h1 h2 (by positivity) hf0) h3 (by positivity) (by positivity)
    _ = (Nat.factorial 18 : ℝ) * 1 * (β * β * β ^ k) := by ring
    _ ≤ (Nat.factorial 18 : ℝ) * 2 ^ 18 * β ^ 19 := by
        have : (Nat.factorial 18 : ℝ) * 1 ≤ (Nat.factorial 18 : ℝ) * 2 ^ 18 := by gcongr
        calc (Nat.factorial 18 : ℝ) * 1 * (β * β * β ^ k) ≤ (Nat.factorial 18 : ℝ) * 2 ^ 18 * (β * β * β ^ k) := by
              gcongr
          _ ≤ _ := by gcongr

lemma JCΦ.rpow_comp (hU : UniqueDiffOn ℝ U) (hβ : 0 ≤ β) (hk : k ≤ 16) {r m' M : ℝ} (hr1 : -1 ≤ r) (hr2 : r ≤ 1)
    (hm : 0 < m') (hmβ : max 1 m'⁻¹ ≤ β) (hMβ : max 1 M ≤ β) {f : Y → ℝ} (hf : JCΦ k U f β a2)
    (hst : MapsTo f U (Ioo m' M)) (h : max 1 a2 + 1 ≤ m) : JCΦ k U (fun y => f y ^ r) β m :=
  JCΦ.comp1 hU isOpen_Ioo.uniqueDiffOn hβ (by omega) (rpowΦ hk hr1 hr2 hm hmβ hMβ) hf hst h

/-- info: 'FormalResearch.SignUncertainty.JCΦ.comp1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms JCΦ.comp1

/-- info: 'FormalResearch.SignUncertainty.rpowΦ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rpowΦ

end DJetJC
end FormalResearch.SignUncertainty
