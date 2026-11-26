/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctBumpSymCheck
public import FormalResearch.SignUncertainty.FctMainHankelDefs

/-!
# The field `bump_profile` of `FctMainHankelInputs` from `fct:bump-sym-check` (F2a)

`FctMainHankelInputs.bump_profile` says: for every `K₁ > 0` and all large `c`, the physical bump `B_c^ε` of `(fct:B-physical)` is a
`BumpProfile (3/2) δ M α β K` (smooth, supported in `[3δ_L/2, ∞)`, symbol bounds of order `α` on `[3δ_L/2, 1]` and `β ≥ 3/2` on
`[1, ∞)`), the hypothesis under which `ctWbump (B_c^ε)` is admissible (`ctWbump_stripAdmissFull`).

`bump_profile_field` proves exactly that statement for the bump *defined* by `(fct:B-physical)` (`physBump`), from the symbol-class
inputs of Lemma FCT.7b (a)-(b) (`physBump_profile`, the constants are uniform in `c` by `FctBumpSymCheck`, but the field needs
only per-`c` constants).  The inputs are the named paper facts, supplied per `(ε, c)`:

* `hsize`: the scales, `δ_L ≍ c^{-1/2}` (`3δ_L/2 ≤ 1`), `|θ₁^ε|/c ≤ 3δ_L/4`, `|L₁| ≤ 3δ_L/4`, `|L₁ − s| ≤ 3δ_L/2` and
  `(5π²/96) c^{-2} (3δ_L/2)^{-3} ≤ 1`: for large `c`, `L₁ = O(c^{-2/3})` (`fct:warp-asymp` (1)), `s = θ₁^ε/c`, `c^{-2}δ_L^{-3} ≍ c^{-1/2}`;
* `hR`: with `O = I_osc^{warp}` and `F = (L̃/(L − L₁)) I_fl(L̃)`, the quotient `O/F − 1` is a symbol of class `(M_R, -1, 0)` on
  `[3δ_L/2, ∞)` (Lemma 7b (b): `fct:comp-D` (1), `(fct:th-tail)`, `fct:phikill` (1), super-exponential decay of `I_osc`);
* `hT`: `τ₀⁴ I_fl` is of class `(M_T, -1/2, 3/2)` on `[3δ_L/2, 6δ_L]` (`m(t) = t² n₂(t²)`, `fct:comp-D`).

None of these is the field; the field is a consequence of the symbol calculus (`FctSymCal`) applied to the explicit factors
`χ`, `γ(L̃)`, `L̃/(L − L₁)`, `I_fl(L̃)`, `η`.

Class: proved under the explicit hypotheses `hsize`, `hR`, `hT` (the instantiated `fct:comp-D` datum is not yet in Lean).
-/

@[expose] public section

open Set
open scoped ContDiff Real
open FormalResearch.CohnElkies

namespace FormalResearch.SignUncertainty.FctSym

open SymW

lemma physF_pos {s L1 x x₀ : ℝ} (hx₀ : 0 < x₀) (hs : |s| ≤ x₀ / 2) (hL1 : |L1| ≤ x₀ / 2) (hx : x₀ ≤ x) :
    0 < physF s L1 x := by
  have h1 : 0 < x - s := by linarith [(abs_le.mp hs).2]
  have h2 : 0 < x - L1 := by linarith [(abs_le.mp hL1).2]
  unfold physF uctIfl
  have := uctAlphaFl_pos
  have := Real.rpow_pos_of_pos h1 (-(3 / 2 : ℝ))
  positivity

/-- **`bump_profile` of `FctMainHankelInputs`** from Lemma FCT.7b (`fct:bump-sym-check`): if `Bphys ε c K₁` is the bump
`(fct:B-physical)` (`physBump`, `H₀ = H_*`) built from the warp envelope `O`, then for every `K₁ > 0` and all large `c` it is a
`BumpProfile (3/2) δ M α β K` with `3δ ≤ 2` and `3/2 ≤ β`.  The inputs `hsize`, `hR`, `hT` are described in the module docstring. -/
theorem bump_profile_field {χ : ℝ → ℝ} (hχ : IsCutoff χ) {Bphys : ℝ → ℝ → ℝ → ℝ → ℝ} (δf sf L1f nf : ℝ → ℝ → ℝ) (K4 : ℝ)
    (Of : ℝ → ℝ → ℝ → ℝ)
    (hdef : ∀ ε c K1 : ℝ, Bphys ε c K1 = physBump χ (nf ε c) c (δf ε c) (sf ε c) K1 K4 (Of ε c)
      (physF (sf ε c) (L1f ε c)) (fun L => tau0 L ^ 4 * uctIfl L))
    (hsize : ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      0 < δf ε c ∧ 3 / 2 * δf ε c ≤ 1 ∧ |sf ε c| ≤ 3 / 2 * δf ε c / 2 ∧ |L1f ε c| ≤ 3 / 2 * δf ε c / 2 ∧
        |L1f ε c - sf ε c| ≤ 3 / 2 * δf ε c ∧
        (5 * π ^ 2 / 96) * c⁻¹ ^ 2 * (3 / 2 * δf ε c) ^ (-3 : ℝ) ≤ 1)
    (hR : ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → ∃ (MR : ℝ) (KR : ℕ → ℝ), 0 ≤ MR ∧
      SymW (Ici (3 / 2 * δf ε c)) (pw MR (-1) 0) KR
        (fun x => Of ε c x / physF (sf ε c) (L1f ε c) x - 1))
    (hT : ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → ∃ (MT : ℝ) (KT : ℕ → ℝ), 0 ≤ MT ∧
      SymW (Icc (3 / 2 * δf ε c) (6 * δf ε c)) (pw MT (-(1 / 2)) (3 / 2)) KT (fun L => tau0 L ^ 4 * uctIfl L)) :
    ∀ K1 : ℝ, 0 < K1 → ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ∃ (δ M α β : ℝ) (K : ℕ → ℝ), 0 < δ ∧ 3 / 2 * δ ≤ 1 ∧ 3 / 2 ≤ β ∧ 0 ≤ M ∧
        BumpProfile (3 / 2) δ M α β K (Bphys ε c K1) := by
  intro K1 _
  obtain ⟨c₁, h1⟩ := hsize
  obtain ⟨c₂, h2⟩ := hR
  obtain ⟨c₃, h3⟩ := hT
  refine ⟨max c₁ (max c₂ c₃), fun ε c hε hc => ?_⟩
  have hc1 : c₁ ≤ c := (le_max_left _ _).trans hc
  have hc2 : c₂ ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hc3 : c₃ ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  obtain ⟨hδ, hδ1, hs, hL1, hLs, hsmall⟩ := h1 ε c hε hc1
  obtain ⟨MR, KR, hMR, hR'⟩ := h2 ε c hε hc2
  obtain ⟨MT, KT, hMT, hT'⟩ := h3 ε c hε hc3
  set δ := δf ε c with hδdef
  set s := sf ε c
  set L1 := L1f ε c
  have hx0 : 0 < 3 / 2 * δ := by positivity
  have hFsym := physF_sym hx0 hs hL1 hLs
  obtain ⟨Kχ, hKχ⟩ := hχ.exists_bound
  set F := physF s L1
  -- `O = F R` on the support
  set R : ℝ → ℝ := fun x => Of ε c x / F x
  have hR1 : SymW (Ici (3 / 2 * δ)) (pw MR (-1) 0) KR (fun x => R x - 1) := hR'
  have hBeq : Bphys ε c K1 = physBump χ (nf ε c) c δ s K1 K4 (fun x => F x * R x) F (fun L => tau0 L ^ 4 * uctIfl L) := by
    rw [hdef]
    funext x
    by_cases hx : 3 / 2 * δ ≤ x
    · have hpos : F x ≠ 0 := (physF_pos hx0 hs hL1 hx).ne'
      simp only [physBump, R]
      rw [mul_div_cancel₀ _ hpos]
    · have hx3 : x / (3 * δ) ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith [not_le.mp hx]
      have hx3' : x / (3 * δf ε c) ≤ 1 / 2 := hx3
      simp only [physBump, hχ.zero _ hx3', hχ.zero _ hx3]; ring
  have hprof := physBump_profile hχ hKχ (n := nf ε c) (c := c) (δ := δ) (s := s) (K1 := K1) (K4 := K4)
    (MΦ := |uctAlphaFl|) (MR := MR) (MT := MT) (F := F) (R := R) (T4 := fun L => tau0 L ^ 4 * uctIfl L)
    hδ hs hsmall (abs_nonneg _) hMR hMT hFsym hR1 hT'
  rw [hBeq]
  exact ⟨δ, _, 7 / 2, 3 / 2, _, hδ, hδ1, le_rfl,
    mul_nonneg (abs_nonneg _) (by
      have := abs_nonneg K1
      positivity), hprof⟩

end FormalResearch.SignUncertainty.FctSym
