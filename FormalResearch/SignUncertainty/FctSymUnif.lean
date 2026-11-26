/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSymChain
public import FormalResearch.SignUncertainty.FctSymInv

/-!
# Uniform symbol classes: one constant sequence `K` for a whole family of parameters (calculus for `fct:bump-sym-check`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (`fct:bump-sym-check`): every bound holds "with `C_r`
independent of `c`".

`USym H S w f` says: there is one sequence `K` such that for **every** parameter `p` satisfying `H p`, `f p ∈ SymW (S p) (w p) K`.  The
closure lemmas (`add`, `mul`, `smul`, `of_le`, `union`, `mono_set`, `congr`, `comp_smooth`) are the `SymW` ones applied pointwise in `p`;
the constant sequence of the result is built from those of the inputs only, so uniformity is carried by the types.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Finset
open scoped ContDiff

namespace FormalResearch.SignUncertainty.FctSym

/-- `f p ∈ SymW (S p) (w p) K` for all admissible `p` with one `K`. -/
def USym {P : Type*} (H : P → Prop) (S : P → Set ℝ) (w : P → ℝ → ℝ) (f : P → ℝ → ℝ) : Prop :=
  ∃ K : ℕ → ℝ, ∀ p, H p → SymW (S p) (w p) K (f p)

namespace USym

variable {P : Type*} {H : P → Prop} {S S' : P → Set ℝ} {w w' : P → ℝ → ℝ} {f g : P → ℝ → ℝ}

lemma mono_set (h : USym H S w f) (hS : ∀ p, H p → S' p ⊆ S p) : USym H S' w f := by
  obtain ⟨K, hK⟩ := h
  exact ⟨K, fun p hp => (hK p hp).mono_set (hS p hp)⟩

lemma of_le (h : USym H S w f) (hw : ∀ p, H p → ∀ x ∈ S p, w p x ≤ w' p x) : USym H S w' f := by
  obtain ⟨K, hK⟩ := h
  exact ⟨K, fun p hp => (hK p hp).of_le (hw p hp) (fun _ => le_rfl)⟩

lemma congr (h : USym H S w f) {U : P → Set ℝ} (hU : ∀ p, H p → IsOpen (U p)) (hSU : ∀ p, H p → S p ⊆ U p)
    {g : P → ℝ → ℝ} (hfg : ∀ p, H p → EqOn (f p) (g p) (U p)) : USym H S w g := by
  obtain ⟨K, hK⟩ := h
  exact ⟨K, fun p hp => (hK p hp).congr (hU p hp) (hSU p hp) (hfg p hp)⟩

lemma add (hf : USym H S w f) (hg : USym H S w g) : USym H S w (fun p x => f p x + g p x) := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨K', hK'⟩ := hg
  exact ⟨fun r => K r + K' r, fun p hp => (hK p hp).add (hK' p hp)⟩

lemma smul (a : P → ℝ) (hf : USym H S w f) : USym H S (fun p x => |a p| * w p x) (fun p x => a p * f p x) := by
  obtain ⟨K, hK⟩ := hf
  exact ⟨K, fun p hp => (hK p hp).smul (a p)⟩

lemma mul {w₂ : P → ℝ → ℝ} (hf : USym H S w f) (hg : USym H S w₂ g) :
    USym H S (fun p x => w p x * w₂ p x) (fun p x => f p x * g p x) := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨K', hK'⟩ := hg
  exact ⟨SymW.Kmul K K', fun p hp => (hK p hp).mul (hK' p hp)⟩

lemma union (hf : USym H S w f) (hg : USym H S' w f) : USym H (fun p => S p ∪ S' p) w f := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨K', hK'⟩ := hg
  exact ⟨fun r => max (K r) (K' r), fun p hp => (hK p hp).union (hK' p hp)⟩

lemma const (hS : ∀ p, H p → ∀ x ∈ S p, 0 < x) (a : P → ℝ) : USym H S (fun p _ => |a p|) (fun p _ => a p) :=
  ⟨SymW.Kone, fun p hp => SymW.const (hS p hp) (a p)⟩

/-- Uniform composition with a smooth function (see `SymW.comp_smooth`): `Φ`, `V`, `P_j`, `B`, `L` do not depend on `p`. -/
lemma comp_smooth (hf : USym H S w f) {Φ : ℝ → ℝ} {V : Set ℝ} {Pj : ℕ → ℝ} {B L : ℝ} (hV : IsOpen V)
    (hΦ : ContDiffOn ℝ ∞ Φ V) (hfV : ∀ p, H p → ∀ x ∈ S p, f p x ∈ V)
    (hP : ∀ p, H p → ∀ j x, x ∈ S p → |iteratedDeriv j Φ (f p x)| ≤ Pj j) (hP0 : ∀ j, 0 ≤ Pj j)
    (hwB : ∀ p, H p → ∀ x ∈ S p, w p x ≤ B) (hL : 0 ≤ L) (h0 : ∀ p, H p → ∀ x ∈ S p, |Φ (f p x)| ≤ L * w p x) :
    USym H S w (fun p x => Φ (f p x)) := by
  obtain ⟨K, hK⟩ := hf
  exact ⟨compK L Pj (fun k => K (k + 1)) B, fun p hp =>
    SymW.comp_smooth (hK p hp) hV hΦ (hfV p hp) (hP p hp) hP0 (hwB p hp) hL (h0 p hp)⟩

end USym

end FormalResearch.SignUncertainty.FctSym
