/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctNPiece

/-!
# Generic transfer: a `t`-symbol `g` gives the `L`-symbol `g(τ₀(L̃)) - c₀` of class `(M, -1, 0)` (`fct:bump-sym-check`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (b): the factors `r₀(t)`, `e^{v(t)}`, `1 + Δ_curv(t)` at `t = τ₀(L̃)`,
`∂_L = m'(t)^{-1} ∂_t`.

`tTransfer_usym`: let `g` be `C^∞` on `(0, ∞)`, `c₀, γ ∈ ℝ` constants, with the `t`-bounds, for all `j` and `t > 0`,

* (S2) `|t^j ∂_t^j (g - c₀)(t)| ≤ P_j min(t², 1)` (`g = c₀ + O(t²)` at `0`),
* (L8) `|t^j ∂_t^j (g - γ)(t)| ≤ P_j min(1, t^{-8})` (`g → γ` at `∞`),

`|γ - c₀| ≤ Γ`.  Then `x ↦ g(τ₀(x - s)) - c₀ ∈ SymW [x₀, ∞) (pw M (-1) 0)` for `x₀ ≤ 1/2`, `|s| ≤ x₀/2`, with `M, K` depending only on `P, Γ`
(`USym`: one constant sequence for all `g, c₀, γ, s, x₀`).

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Filter Topology Finset
open scoped ContDiff Real

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

/-- Parameters of the transfer: the profile `g`, its limits `c₀` (at `0`) and `γ` (at `∞`), the shift `s` and the left end `x₀`. -/
structure GPar where
  g : ℝ → ℝ
  c₀ : ℝ
  γ : ℝ
  s : ℝ
  x₀ : ℝ
  tmin : ℝ

/-- Admissibility for the `t`-bounds `P` and the jump bound `Γ`. -/
def GHyp (P : ℕ → ℝ) (Γ : ℝ) (p : GPar) : Prop :=
  ContDiffOn ℝ ∞ p.g (Ioi 0) ∧ 0 < p.x₀ ∧ p.x₀ ≤ 1 / 2 ∧ |p.s| ≤ p.x₀ / 2 ∧ |p.γ - p.c₀| ≤ Γ ∧
  p.tmin ≤ tau0 (p.x₀ / 2) ∧
  (∀ j : ℕ, ∀ t : ℝ, p.tmin ≤ t → |t ^ j * iteratedDeriv j (fun u => p.g u - p.c₀) t| ≤ P j * min (t ^ 2) 1) ∧
  (∀ j : ℕ, ∀ t : ℝ, p.tmin ≤ t → |t ^ j * iteratedDeriv j (fun u => p.g u - p.γ) t| ≤ P j * min 1 ((t ^ 8)⁻¹))

lemma GHyp.s_le {P Γ} {p : GPar} (h : GHyp P Γ p) : |p.s| ≤ 1 / 4 := h.2.2.2.1.trans (by linarith [h.2.2.1])

/-- Small regime `x ≤ 1/2`: `g(τ₀(x - s)) - c₀ ∈ SymW` of weight `Θ x`. -/
theorem gblock_small (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) (Γ : ℝ) : ∃ Θ : ℝ, 0 ≤ Θ ∧
    USym (GHyp P Γ) (fun p => Icc p.x₀ (1 / 2)) (fun _ x => Θ * x) (fun p x => p.g (tau0 (x - p.s)) - p.c₀) := by
  obtain ⟨A, hA0, hcomp⟩ := comp_tau0_shift
  obtain ⟨Cu, hCu, hsq⟩ := tau0_sq_le
  set Θ : ℝ := max 2 (3 / 2 * Cu) with hΘ
  have hΘ2 : 2 ≤ Θ := le_max_left _ _
  refine ⟨Θ, by linarith, fun r => chainM P (fun j => (j : ℝ)) A 1 r 0, fun p hp => ?_⟩
  have hs4 := GHyp.s_le hp
  obtain ⟨hg, hx₀, hx₀h, hs, hΓ, htm, hS2, hL8⟩ := hp
  have hgc : ContDiffOn ℝ ∞ (fun u => p.g u - p.c₀) (Ioi 0) := hg.sub contDiffOn_const
  set om : ℝ → ℝ := fun x => min 1 (Θ * x) with hom
  have hbase : ∀ j, ∀ x, p.x₀ ≤ x → |tau0 (x - p.s) ^ j * iteratedDeriv j (fun u => p.g u - p.c₀) (tau0 (x - p.s))| ≤
      P j * om x := by
    intro j x hx
    have hx0 : 0 < x := lt_of_lt_of_le hx₀ hx
    have hxs : 0 < x - p.s := by linarith [(abs_le.mp hs).2]
    have hxt : p.tmin ≤ tau0 (x - p.s) :=
      htm.trans (tau0_mono (by linarith) (by linarith [(abs_le.mp hs).2]))
    refine (hS2 j _ hxt).trans (mul_le_mul_of_nonneg_left ?_ (hP j))
    refine le_min (min_le_right _ _) ?_
    rcases le_or_gt (x - p.s) 1 with h | h
    · refine (min_le_left _ _).trans ?_
      have h2 := hsq (x - p.s) ⟨hxs, h⟩
      have h3 : x - p.s ≤ 3 / 2 * x := by linarith [(abs_le.mp hs).1]
      calc tau0 (x - p.s) ^ 2 ≤ Cu * (x - p.s) := h2
        _ ≤ Cu * (3 / 2 * x) := mul_le_mul_of_nonneg_left h3 hCu.le
        _ = 3 / 2 * Cu * x := by ring
        _ ≤ Θ * x := mul_le_mul_of_nonneg_right (le_max_right _ _) hx0.le
    · refine (min_le_right _ _).trans ?_
      have hx34 : 3 / 4 < x := by linarith [(abs_le.mp hs4).1]
      nlinarith
  have hb := hcomp (x₀ := p.x₀) (s := p.s) (g := fun u => p.g u - p.c₀) (om := om) (P := P) hx₀ hs hgc hP
    (fun x hx' => by simp only [hom]; exact le_min zero_le_one (mul_nonneg (by linarith) (by linarith))) hbase
  refine ⟨fun x hx => lt_of_lt_of_le hx₀ hx.1, ?_, fun r => chainM_nonneg hP r 0, fun x hx => ?_, fun r x hx => ?_⟩
  · refine ⟨Ioi p.s, isOpen_Ioi, fun x hx => ?_, ?_⟩
    · exact mem_Ioi.mpr (by linarith [(abs_le.mp hs).2, hx.1])
    · exact hgc.comp (contDiffOn_tau0.comp (contDiffOn_id.sub contDiffOn_const) (fun y hy => sub_pos.mpr hy))
        (fun x hx => tau0_pos (sub_pos.mpr hx))
  · exact mul_nonneg (by linarith) (lt_of_lt_of_le hx₀ hx.1).le
  · have hx0 : 0 < x := lt_of_lt_of_le hx₀ hx.1
    have := hb r x hx.1
    refine this.trans ?_
    rw [lamL_eq_inv hx0 (hx.2.trans (by norm_num)), inv_pow]
    have hM := chainM_nonneg (κ := fun j : ℕ => (j : ℝ)) (A := A) (B := 1) hP r 0
    have : om x ≤ Θ * x := min_le_right _ _
    have hinv : 0 ≤ (x ^ r)⁻¹ := by positivity
    calc chainM P (fun j => (j : ℝ)) A 1 r 0 * om x * (x ^ r)⁻¹
        ≤ chainM P (fun j => (j : ℝ)) A 1 r 0 * (Θ * x) * (x ^ r)⁻¹ := by gcongr


/-- Large regime `x ≥ 1/2`: `g(τ₀(x - s)) - γ ∈ SymW` of weight `1`. -/
theorem gblock_large (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) (Γ : ℝ) :
    USym (GHyp P Γ) (fun _ => Ici (1 / 2 : ℝ)) (fun _ _ => 1) (fun p x => p.g (tau0 (x - p.s)) - p.γ) := by
  obtain ⟨A, hA0, hcomp⟩ := comp_tau0_shift
  have hγ := gammaTau_pos
  refine ⟨fun r => chainM P (fun j => (j : ℝ)) A 1 r 0 * 2 ^ r * ((gammaTau⁻¹) ^ 8 * (r.factorial : ℝ)), fun p hp => ?_⟩
  have hs4 := GHyp.s_le hp
  obtain ⟨hg, hx₀, hx₀h, hs, hΓ, htm, hS2, hL8⟩ := hp
  have hgc : ContDiffOn ℝ ∞ (fun u => p.g u - p.γ) (Ioi 0) := hg.sub contDiffOn_const
  set om : ℝ → ℝ := fun x => ((gammaTau * Real.exp (x / 2))⁻¹) ^ 8 with hom
  have hbase : ∀ j, ∀ x, (1 / 2 : ℝ) ≤ x → |tau0 (x - p.s) ^ j * iteratedDeriv j (fun u => p.g u - p.γ) (tau0 (x - p.s))| ≤
      P j * om x := by
    intro j x hx
    have hxs : 0 < x - p.s := by linarith [(abs_le.mp hs4).2]
    have hxt : p.tmin ≤ tau0 (x - p.s) :=
      htm.trans (tau0_mono (by linarith) (by linarith [(abs_le.mp hs4).2]))
    refine (hL8 j _ hxt).trans (mul_le_mul_of_nonneg_left ?_ (hP j))
    refine (min_le_right _ _).trans ?_
    have hτ := tau0_ge_gamma hx hs4
    have hE : 0 < gammaTau * Real.exp (x / 2) := by positivity
    rw [← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr (tau0_pos hxs).le) (inv_anti₀ hE hτ) 8
  have hb := hcomp (x₀ := 1 / 2) (s := p.s) (g := fun u => p.g u - p.γ) (om := om) (P := P)
    (by norm_num) (by linarith [hs4]) hgc hP (fun x _ => by simp only [hom]; positivity) hbase
  refine ⟨fun x hx => by have : (1 / 2 : ℝ) ≤ x := hx; linarith, ?_, fun r => ?_, fun x _ => zero_le_one, fun r x hx => ?_⟩
  · refine ⟨Ioi p.s, isOpen_Ioi, fun x hx => ?_, ?_⟩
    · have : (1 / 2 : ℝ) ≤ x := hx
      exact mem_Ioi.mpr (by linarith [(abs_le.mp hs4).2])
    · exact hgc.comp (contDiffOn_tau0.comp (contDiffOn_id.sub contDiffOn_const) (fun y hy => sub_pos.mpr hy))
        (fun x hx => tau0_pos (sub_pos.mpr hx))
  · have := chainM_nonneg (κ := fun j : ℕ => (j : ℝ)) (A := A) (B := 1) hP r 0
    positivity
  · have hx' : (1 / 2 : ℝ) ≤ x := hx
    have hx0 : 0 < x := by linarith
    refine (hb r x hx').trans ?_
    have hl : lamL x ^ r ≤ 2 ^ r := pow_le_pow_left₀ (lamL_nonneg x) (lamL_le_two hx') r
    have hM := chainM_nonneg (κ := fun j : ℕ => (j : ℝ)) (A := A) (B := 1) hP r 0
    have hom0 : 0 ≤ om x := by simp only [hom]; positivity
    have hom2 : om x ≤ (gammaTau⁻¹) ^ 8 * (r.factorial : ℝ) * (x ^ r)⁻¹ := om2_decay hx' r
    calc chainM P (fun j => (j : ℝ)) A 1 r 0 * om x * lamL x ^ r
        ≤ chainM P (fun j => (j : ℝ)) A 1 r 0 * ((gammaTau⁻¹) ^ 8 * (r.factorial : ℝ) * (x ^ r)⁻¹) * 2 ^ r :=
          mul_le_mul (mul_le_mul_of_nonneg_left hom2 hM) hl (pow_nonneg (lamL_nonneg x) r) (by positivity)
      _ = _ := by ring

/-- **The `t`-to-`L` transfer** (see the module docstring). -/
theorem tTransfer_usym (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) (Γ : ℝ) (hΓ : 0 ≤ Γ) : ∃ M : ℝ, 0 ≤ M ∧
    USym (GHyp P Γ) (fun p => Ici p.x₀) (fun _ => pw M (-1) 0) (fun p x => p.g (tau0 (x - p.s)) - p.c₀) := by
  obtain ⟨Θ, hΘ, hsm⟩ := gblock_small P hP Γ
  have hlg := gblock_large P hP Γ
  set M : ℝ := Θ + 2 * (Γ + 1) with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨M, hM0, ?_⟩
  have s1 := hsm.of_le (w' := fun _ => pw M (-1) 0) (fun p hp x hx => by
    have hx0 : 0 < x := lt_of_lt_of_le hp.2.1 hx.1
    rw [pw_neg_one_zero_of_le (hx.2.trans (by norm_num))]
    nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * (Γ + 1)) hx0.le])
  have l1 : USym (GHyp P Γ) (fun _ => Ici (1 / 2 : ℝ)) (fun _ _ => Γ + 1)
      (fun p x => p.g (tau0 (x - p.s)) - p.c₀) := by
    have a1 := hlg.of_le (w' := fun _ _ => Γ + 1) (fun p hp x hx => by linarith)
    have a2 := (USym.const (H := GHyp P Γ) (S := fun _ => Ici (1 / 2 : ℝ)) (fun p _ x hx => by
      have : (1 / 2 : ℝ) ≤ x := hx
      linarith) (fun p => p.γ - p.c₀)).of_le (w' := fun _ _ => Γ + 1) (fun p hp x hx => by
        have := hp.2.2.2.2.1
        linarith)
    exact (a1.add a2).congr (U := fun _ => univ) (fun _ _ => isOpen_univ) (fun _ _ => subset_univ _)
      (fun p hp x hx => by simp only; ring)
  have l2 := l1.of_le (w' := fun _ => pw M (-1) 0) (fun p hp x hx => by
    have hx' : (1 / 2 : ℝ) ≤ x := hx
    refine le_trans ?_ (pw_ge_half hM0 hx')
    rw [hM]; linarith)
  refine (s1.union l2).mono_set (fun p hp x hx => ?_)
  rcases le_or_gt x (1 / 2) with h | h
  · exact Or.inl ⟨hx, h⟩
  · exact Or.inr h.le

/-- info: 'FormalResearch.SignUncertainty.FctSym.tTransfer_usym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tTransfer_usym

end FormalResearch.SignUncertainty.FctSym
