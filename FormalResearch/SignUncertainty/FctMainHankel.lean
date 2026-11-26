/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.StripAdmiss
public import FormalResearch.SignUncertainty.CtLower
public import FormalResearch.SignUncertainty.HankelThresholds

/-!
# `fct:main-hankel`: the five-term upper bound for the Hankel thresholds (F2a skeleton)

Paper I, Theorem FCT.1 (`constant_terms_five.tex`, label `fct:main-hankel`; part of `thm:ct-upper` (i)):
there are `c₀, C₊ > 0` with `T_c^ε ≤ Δ₅^ε(c) + C₊ c^{-3/4}` for `ε = ±1` and all real `c ≥ c₀`.

**Statement.** `fct_main_hankel`, with `hankelT ε c = T_c^ε` (`Radii.lean`) and the five-term expansion `ctDelta5`
(`CtLower.lean`, `(eq:ct-delta5)` of `general_theorems.tex`; the constants `κ_ε`, `c₁^Langer`, `d₂^{*,ε}` are `CtLower`'s).

**Proof (the deliverable).** The paper's proof of `fct:main-hankel` (`fct:s4-proof`) in four steps, all proved here from the fields of
`FctMainHankelInputs`:

1. *The lift* (`hankel_feasible_of_strip`, proved from `uct_admiss_full`): a strip multiplier `W̃` with `(M1)`-`(M3)` at `α = 1/2`,
   `W̃(1-ζ) = ε W̃(ζ)`, `Re W̃(0) < 0` and `f_W = admissF c W̃ ≥ 0` on `[T, ∞)` gives `IsHankelFeasible c ε T f_W`.
2. *The witness* `W̃_c^ε = W̃^warp - d W̃_{g₁} + η₀ W̃^fl + W̃^bump` (`(fct:Wtot-hankel)`), `d = K_d c^{-13/12}`,
   `η₀ = K₀ c^{-4/3}`.
3. *Vacuum* (`Step 1` of the paper): `Re W̃(0) = -k d + η₀ Re W̃^fl(0) + Re W̃^bump(0) < 0` by the choice
   `K_d = (C₀ + b₂ K₁)/k + 1` after `K₀, K₁` (the non-circular order `K → K₄ → K₀ → K₁ → K_d → c₀`).
4. *Positivity* (`Step 2`): `f ≥ 0` on `[T, ∞)`, `T = T₁ + 2K_d β₁⁻¹ c^{-3/4}`, `|T₁ - Δ₅| ≤ C c^{-1}`; hence
   `T_c^ε ≤ T ≤ Δ₅ + C₊ c^{-3/4}` (the lower bound `hb_thresholds_lower` makes the feasible-threshold set bounded below).

**Conditional on the fields of `FctMainHankelInputs`.**  Each field is the output of the named TeX lemma(s) in the form the proof of
`fct:main-hankel` consumes it; the data (`Wwarp`, `Wg1`, `Wfl`, `Wbump`, `T1`) are the multipliers and the zero `T₁` of the paper's
construction, to be supplied by the lemmas that define them.  Proved lemmas (`uct:admiss` = `uct_admiss_full`, `mat:T7`,
`hb_thresholds_lower`, `fct:bump-5`, `uct:airy-trans`, `uct:pos-floor`, `uct:seed-asymp` (1), `fct:moment-solver`, `fct:phikill`,
`fct:edge-ibp`) are used directly or enter through the discharge of a field, not as fields.

**Satisfiability.** The fields are statements about abstract data (`Wwarp`, ..., `T1`), so they are satisfiable only by the
paper's actual multipliers; no field has been shown consistent in Lean.  Doubtful points: `warp_zero` and `admissible` hide
the whole of `fct:comp-D`/`fct:comp-cfu`/`fct:inner-symbols`/`fct:splitting`; `physical_positive` hides the five-term positivity
(`fct:physical-positive` and its inputs) and is the field most likely to need a sharper form (for instance a split of the
five regimes of `L ≥ L_T`) once its proof is formalised.  The `T_c^{ε}` set is bounded below by `hb_thresholds_lower`, so no field
is needed for that.

Class: proved under the explicit hypothesis structure `FctMainHankelInputs` (not discharged).
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

/-! ### Step 1 of the assembly: the lift of an admissible multiplier is a feasible Hankel eigenfunction -/

/-- A strip multiplier with `(M1)`-`(M3)` at `α = 1/2`, `W̃(1-ζ) = ε W̃(ζ)`, `Re W̃(0) < 0` whose lift is nonnegative on
`[T, ∞)` gives a feasible Hankel eigenfunction at threshold `T` (`uct:admiss`, `mat:T7`). -/
theorem hankel_feasible_of_strip {c ε T : ℝ} {W : ℂ → ℂ} (hc : 2 ≤ c) (hε : ε = 1 ∨ ε = -1)
    (hW : StripAdmissFullData (1 / 2) W) (hsym : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → W (1 - ζ) = (ε : ℂ) * W ζ)
    (hvac : (W 0).re < 0) (hpos : ∀ Δ : ℝ, T ≤ Δ → 0 ≤ admissF c W Δ) :
    IsHankelFeasible c ε T (admissF c W) := by
  have h := (uct_admiss_full hc (by norm_num) (by norm_num) hW).2.2.2.2.2.2.2 ε hε hsym
  obtain ⟨heig, h0⟩ := h
  refine ⟨heig, ⟨0, le_refl 0 |> fun h => Set.mem_Ici.mpr h, ?_⟩, ?_, hpos⟩
  · intro hz
    rw [hz, mul_zero] at h0
    linarith
  · rw [h0]; exact hvac.le

/-- info: 'FormalResearch.SignUncertainty.hankel_feasible_of_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_feasible_of_strip

/-! ### The inputs -/

/-- The multiplier `W̃_c^ε` of `(fct:Wtot-hankel)`:
`W̃^warp - d W̃_{g₁} + η₀ W̃^fl + W̃^bump`, `d = K_d c^{-13/12}`, `η₀ = K₀ c^{-4/3}`. -/
noncomputable def ctWtot (Wwarp Wg1 Wfl : ℝ → ℝ → ℂ → ℂ) (Wbump : ℝ → ℝ → ℝ → ℂ → ℂ) (ε c K0 K1 Kd : ℝ) (ζ : ℂ) : ℂ :=
  Wwarp ε c ζ - ((Kd * c ^ (-(13 / 12 : ℝ)) : ℝ) : ℂ) * Wg1 ε c ζ + ((K0 * c ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * Wfl ε c ζ +
    Wbump ε c K1 ζ

/-- **The open inputs of `fct:main-hankel`**, one block per TeX lemma (the paper's non-circular order of constants
`K → K₄ → K₀ → K₁ → K_d → c₀` is built into the quantifiers).

Data: the Langer-warped multiplier `Wwarp` (`(fct:Wwarp-hankel)`), the `g₁` multiplier `Wg1` (`(fct:Wg1-exact)`), the floor
multiplier `Wfl` (`uct:pos-floor` (2), `K = K_*`, `U = 1`), the bump multiplier `Wbump ε c K₁` (`(fct:B-five-def)` with
`η(L) = K₁(c^{-2}L^{-2} + c^{-1})`, symmetrised), and the zero `T1 ε c = T₁` of `fct:warp-asymp` (1). -/
structure FctMainHankelInputs where
  /-- `W̃^{warp,ε}_c`. -/
  Wwarp : ℝ → ℝ → ℂ → ℂ
  /-- `W̃_{g₁}^{sym,ε}`. -/
  Wg1 : ℝ → ℝ → ℂ → ℂ
  /-- `W̃^{fl,ε}`. -/
  Wfl : ℝ → ℝ → ℂ → ℂ
  /-- `c^{-1/3}(B̂ + ε B̂(c(1 - ·)))` for the bump of constant `K₁`. -/
  Wbump : ℝ → ℝ → ℝ → ℂ → ℂ
  /-- `T₁ = L`-position of the zero, as a threshold `Δ`. -/
  T1 : ℝ → ℝ → ℝ
  /-- `fct:comp-D`, `fct:comp-cfu`, `fct:inner-symbols`, `fct:warp-asymp` (1) (with `ct:langer-inv`, `ct:five-term-node`):
  the zero solve places the first zero at `T₁ = Δ₅^ε(c) + O(c^{-1})` (`K₄ = K₄^{(0)}` fixed). -/
  warp_zero : ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |T1 ε c - ctDelta5 ε c| ≤ C * c⁻¹
  /-- `fct:splitting` (1) (`Φ̂_c(ζ) = O(ζ³)`), `fct:comp-D`: `W̃^warp(0) = 0`. -/
  warp_origin : ∀ ε c : ℝ, Wwarp ε c 0 = 0
  /-- `uct:airy-trans`, `(fct:Wg1-exact)`: `W̃_{g₁}(0) = k > 0`. -/
  g1_origin : ∃ k : ℝ, 0 < k ∧ ∀ ε c : ℝ, Wg1 ε c 0 = (k : ℂ)
  /-- `uct:pos-floor` (2): `Re W̃^fl(0) = k(1 + |a₁'|) + O(c^{-5/6})`, in particular bounded. -/
  fl_origin : ∃ C : ℝ, ∀ ε c : ℝ, 1 ≤ c → |(Wfl ε c 0).re| ≤ C
  /-- Step 1 of `fct:s4-proof` (`uct:admiss` (M1)-(M3) at `α = 1/2` and the `ε`-symmetry): every summand is admissible
  (`fct:splitting` (2), `fct:comp-D` (1), `fct:phikill`, `uct:airy-trans`, `uct:pos-floor`, `fct:bump-5` (1),
  `fct:bump-sym-check`), and each is `ε`-symmetric by construction. -/
  admissible : ∀ ε K0 K1 Kd : ℝ, (ε = 1 ∨ ε = -1) → 0 < K0 → 0 < K1 → 0 < Kd → ∃ c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c →
    StripAdmissFullData (1 / 2) (ctWtot Wwarp Wg1 Wfl Wbump ε c K0 K1 Kd) ∧
    ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 →
      ctWtot Wwarp Wg1 Wfl Wbump ε c K0 K1 Kd (1 - ζ) = (ε : ℂ) * ctWtot Wwarp Wg1 Wfl Wbump ε c K0 K1 Kd ζ
  /-- `fct:physical-budget`: `Re W̃^bump(0) = c^{-1/3}∫B + O(e^{-c' c^{1/2}}) ≤ (C₀(K₄) + b₂ K₁) c^{-13/12}`, with `C₀, b₂`
  independent of `K₁` and of the later `K_d`. -/
  physical_budget : ∃ C0 b2 : ℝ, ∀ K1 : ℝ, 0 < K1 → ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
    (Wbump ε c K1 0).re ≤ (C0 + b2 * K1) * c ^ (-(13 / 12 : ℝ))
  /-- `fct:physical-positive` (iii)-(iv) with its inputs `fct:warp-asymp` (2)-(3), `fct:splitting`, `fct:unscaled-cusp`,
  `fct:cusp-edge`, `uct:seed-asymp` (1)-(2) (`(fct:hg1-win)`-`(fct:hg1-mac)`), `fct:bump-5`, `fct:bump-sym-check`,
  `uct:pos-floor`: `K₀, K₁` can be chosen independently of `K_d` so that the density of `W̃_c^ε` is positive on
  `L ≥ L_T`, i.e. `f ≥ 0` on `Δ ≥ T₁ + (2K_d/β₁) c^{-3/4}`. -/
  physical_positive : ∃ K0 K1 : ℝ, 0 < K0 ∧ 0 < K1 ∧ ∀ Kd : ℝ, 0 < Kd → ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
    ∀ Δ : ℝ, T1 ε c + 2 * Kd / hankelBeta1 * c ^ (-(3 / 4 : ℝ)) ≤ Δ →
      0 ≤ admissF c (ctWtot Wwarp Wg1 Wfl Wbump ε c K0 K1 Kd) Δ


/-! ### The assembly -/

/-- The real part of the multiplier at the origin (vacuum condition of `Step 1`):
`Re W̃(0) = -k d + η₀ Re W̃^fl(0) + Re W̃^bump(0)`. -/
lemma ctWtot_origin_re (I : FctMainHankelInputs) {k : ℝ} (hk : ∀ ε c : ℝ, I.Wg1 ε c 0 = (k : ℂ)) (ε c K0 K1 Kd : ℝ) :
    (ctWtot I.Wwarp I.Wg1 I.Wfl I.Wbump ε c K0 K1 Kd 0).re =
      -(Kd * c ^ (-(13 / 12 : ℝ))) * k + K0 * c ^ (-(4 / 3 : ℝ)) * (I.Wfl ε c 0).re + (I.Wbump ε c K1 0).re := by
  simp [ctWtot, I.warp_origin, hk]

/-- **`fct:main-hankel`** (Paper I, `constant_terms_five.tex`): conditional on `FctMainHankelInputs`,
`T_c^ε ≤ Δ₅^ε(c) + C₊ c^{-3/4}` for `ε = ±1` and all real `c ≥ c₀`.  Proved (assembly) under the explicit hypothesis
structure; the fields are the not-yet-discharged TeX lemmas. -/
theorem fct_main_hankel (I : FctMainHankelInputs) :
    ∃ Cp c₀ : ℝ, 0 < Cp ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      hankelT ε c ≤ ctDelta5 ε c + Cp * c ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨k, hk0, hk⟩ := I.g1_origin
  obtain ⟨Cfl, hCfl⟩ := I.fl_origin
  obtain ⟨C0, b2, hbud⟩ := I.physical_budget
  obtain ⟨K0, K1, hK0, hK1, hpos⟩ := I.physical_positive
  obtain ⟨C1, cw, hwarp⟩ := I.warp_zero
  obtain ⟨Clow, clow, hlow⟩ := hb_thresholds_lower
  -- the choice of `K_d` after `K₀, K₁`
  set Kd : ℝ := (|C0| + |b2| * K1 + K0 * |Cfl|) / k + 1 with hKd
  have hKdpos : 0 < Kd := by
    have : 0 ≤ (|C0| + |b2| * K1 + K0 * |Cfl|) / k := by positivity
    linarith
  obtain ⟨cb, hcb⟩ := hbud K1 hK1
  obtain ⟨cp, hcp⟩ := hpos Kd hKdpos
  obtain ⟨ca1, hca1⟩ := I.admissible 1 K0 K1 Kd (Or.inl rfl) hK0 hK1 hKdpos
  obtain ⟨ca2, hca2⟩ := I.admissible (-1) K0 K1 Kd (Or.inr rfl) hK0 hK1 hKdpos
  have hβ := hankelBeta1_pos
  refine ⟨|C1| + 2 * Kd / hankelBeta1 + 1,
    max (max (max (max cw clow) (max cb cp)) (max ca1 ca2)) 2, by positivity, ?_⟩
  intro ε c hε hc
  simp only [max_le_iff] at hc
  obtain ⟨⟨⟨⟨hcw, hcl⟩, hcb', hcp'⟩, hcaa1, hcaa2⟩, hc2⟩ := hc
  have hc1 : 1 ≤ c := by linarith
  obtain ⟨hadm, hsym⟩ : StripAdmissFullData (1 / 2) (ctWtot I.Wwarp I.Wg1 I.Wfl I.Wbump ε c K0 K1 Kd) ∧
      ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 →
        ctWtot I.Wwarp I.Wg1 I.Wfl I.Wbump ε c K0 K1 Kd (1 - ζ) =
          (ε : ℂ) * ctWtot I.Wwarp I.Wg1 I.Wfl I.Wbump ε c K0 K1 Kd ζ := by
    rcases hε with rfl | rfl
    · exact hca1 c hcaa1
    · exact hca2 c hcaa2
  -- vacuum
  have hrpow : c ^ (-(4 / 3 : ℝ)) ≤ c ^ (-(13 / 12 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hrpos : 0 < c ^ (-(13 / 12 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  have hrpos' : 0 ≤ c ^ (-(4 / 3 : ℝ)) := (Real.rpow_pos_of_pos (by linarith) _).le
  have hvac : (ctWtot I.Wwarp I.Wg1 I.Wfl I.Wbump ε c K0 K1 Kd 0).re < 0 := by
    rw [ctWtot_origin_re I hk]
    have h1 := hcb ε c hε hcb'
    have h2 := hCfl ε c hc1
    have h3 : K0 * c ^ (-(4 / 3 : ℝ)) * (I.Wfl ε c 0).re ≤ K0 * |Cfl| * c ^ (-(13 / 12 : ℝ)) := by
      have : (I.Wfl ε c 0).re ≤ |Cfl| := le_trans (le_abs_self _) (le_trans h2 (le_abs_self _))
      calc K0 * c ^ (-(4 / 3 : ℝ)) * (I.Wfl ε c 0).re ≤ K0 * c ^ (-(4 / 3 : ℝ)) * |Cfl| :=
            mul_le_mul_of_nonneg_left this (mul_nonneg hK0.le hrpos')
        _ = K0 * |Cfl| * c ^ (-(4 / 3 : ℝ)) := by ring
        _ ≤ K0 * |Cfl| * c ^ (-(13 / 12 : ℝ)) :=
            mul_le_mul_of_nonneg_left hrpow (mul_nonneg hK0.le (abs_nonneg _))
    have h4 : (C0 + b2 * K1) * c ^ (-(13 / 12 : ℝ)) ≤ (|C0| + |b2| * K1) * c ^ (-(13 / 12 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ hrpos.le
      have : b2 * K1 ≤ |b2| * K1 := mul_le_mul_of_nonneg_right (le_abs_self _) hK1.le
      linarith [le_abs_self C0]
    have h5 : Kd * k = |C0| + |b2| * K1 + K0 * |Cfl| + k := by
      rw [hKd]; field_simp
    nlinarith [mul_pos hk0 hrpos]
  have hfeas : IsHankelFeasible c ε (I.T1 ε c + 2 * Kd / hankelBeta1 * c ^ (-(3 / 4 : ℝ))) (admissF c (ctWtot I.Wwarp I.Wg1 I.Wfl I.Wbump ε c K0 K1 Kd)) :=
    hankel_feasible_of_strip hc2 hε hadm hsym hvac (fun Δ hΔ => hcp ε c hε hcp' Δ hΔ)
  have hbdd : BddBelow {T : ℝ | ∃ f, IsHankelFeasible c ε T f} :=
    ⟨c / π ^ 2 + airyOrderCoeff * c ^ (1 / 3 : ℝ) - Clow, fun T ⟨f, hf⟩ => hlow c hcl ε hε T f hf⟩
  have h1 : hankelT ε c ≤ I.T1 ε c + 2 * Kd / hankelBeta1 * c ^ (-(3 / 4 : ℝ)) := csInf_le hbdd ⟨_, hfeas⟩
  have h2 := hwarp ε c hε hcw
  have hc34 : c ⁻¹ ≤ c ^ (-(3 / 4 : ℝ)) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hC1 : 0 ≤ C1 * c⁻¹ := le_trans (abs_nonneg _) h2
  have hcpos : 0 < c := by linarith
  have hC1' : 0 ≤ C1 := by
    by_contra h
    replace h := not_le.mp h
    have := mul_neg_of_neg_of_pos h (inv_pos.mpr hcpos)
    linarith
  have hr34 : 0 < c ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos hcpos _
  have h6 : I.T1 ε c ≤ ctDelta5 ε c + C1 * c ^ (-(3 / 4 : ℝ)) := by
    have := (abs_le.mp h2).2
    nlinarith [mul_le_mul_of_nonneg_left hc34 hC1']
  have h7 : 2 * Kd / hankelBeta1 * c ^ (-(3 / 4 : ℝ)) ≥ 0 := by positivity
  nlinarith [mul_nonneg (abs_nonneg C1) hr34.le, abs_nonneg C1, le_abs_self C1, mul_le_mul_of_nonneg_right (le_abs_self C1) hr34.le]

/-- `fct:main-hankel`, conditional on the inputs, in the `|T_c^ε - Δ₅^ε(c)|`-free upper-bound form consumed by `thm:ct-upper` (i). -/
theorem fct_main_hankel_upper (I : FctMainHankelInputs) :
    ∃ Cp c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → hankelT ε c - ctDelta5 ε c ≤ Cp * c ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨Cp, c₀, -, h⟩ := fct_main_hankel I
  exact ⟨Cp, c₀, fun ε c hε hc => by linarith [h ε c hε hc]⟩

/-- info: 'FormalResearch.SignUncertainty.fct_main_hankel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fct_main_hankel

end FormalResearch.SignUncertainty
