/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.StripAdmiss
public import FormalResearch.SignUncertainty.CtLower
public import FormalResearch.SignUncertainty.UctSeedW
public import FormalResearch.SignUncertainty.UctSeedWHolder
public import FormalResearch.SignUncertainty.UctAiryTransPhi
public import FormalResearch.SignUncertainty.UctPosFloorWpos
public import FormalResearch.SignUncertainty.UctBumpMain
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

**Concrete multipliers.** `ctWg1` (`(fct:Wg1-exact)`, from `seedT`, `uctSeedZ`, `outerHbar`, `g̃_1 = airyTwistedLaplaceC g₁`), `ctWfl` (the
`ε`-lift of `S_pos` of `uct:pos-floor` (2), `liftSymbol uctSpos`), `ctWbump` (`bumpDW`, `UctBumpMain`), `ctWwarp` (`(fct:Wwarp-hankel)`)
and `ctWtot` (`(fct:Wtot-hankel)`) are defined from the existing Lean objects.  Their origin values are proved:
`ctWg1_zero` (`= k = ceK` for large `c`, using `seedT_scale_ne`: `φ_{c,0}(1) = 1 + O(c^{-2/3})`), `ctWfl_zero_bound`
(`|Re W̃^fl(0)| ≤ C`), `ctWwarp_zero` (`= 0`; Lean's value is the junk value of `ctHG` at `ζ = 0`, equal to the paper's value because
`Φ̂_c = O(ζ³)` makes the multiplier continuous there, which the field `admissible` asserts for the total multiplier).

**Abstract parameters** (the only objects not yet in Lean, each named after its TeX label): `Dcomp` (`fct:comp-D`), `PhiHat`
(`fct:splitting`, which depends on the chart of `fct:comp-cfu`), `Bphys` (`(fct:B-physical)`), `T1` (`fct:warp-asymp` (1)).

**Conditional on the fields of `FctMainHankelInputs`** (`warp_zero`, `admissible`, `physical_budget`, `physical_positive`): each is
the output of the named TeX lemma(s), stated about the concrete multipliers and these four parameters.  Proved lemmas
(`uct:admiss` = `uct_admiss_full`, `mat:T7`, `hb_thresholds_lower`, `uct:airy-trans`, `uct:pos-floor`, `uct:outer-growth`,
`fct:bump-5`, `uct:seed-asymp` (1), `fct:moment-solver`, `fct:phikill`, `fct:edge-ibp`) are used directly or enter through the
discharge of a field, not as fields.

**Satisfiability.** The four parameters are free, so the fields are consistent only for the paper's actual `D_{τ₁}`, `Φ̂_c`, `B`, `T₁`;
no field has been shown consistent in Lean.  Doubtful points: `warp_zero` and `admissible` hide `fct:comp-D`/`fct:comp-cfu`/
`fct:inner-symbols`/`fct:splitting`; `physical_positive` hides the five-term positivity (`fct:physical-positive` and its inputs) and is
the field most likely to need a sharper form once its proof is formalised.  The `T_c^ε` set is bounded below by
`hb_thresholds_lower`, so no field is needed for that.  The `ctWfl` and `ctWg1` parts of `admissible` are provable from proved lemmas
and are to be split off when proved.

Class: proved under the explicit hypothesis structure `FctMainHankelInputs` (not discharged).
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real
open FormalResearch.CohnElkies FormalResearch.Special FormalResearch.SignUncertainty.CtOuter

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


/-! ### The concrete multipliers of `(fct:Wtot-hankel)` -/

/-- `H_*(ζ)/G_ε(ζ)`, as `Z_ε(ζ) e^{-h(ζ)} / (ζ(1-ζ))^{5/2}` (`seedW`: `ζ^{5/2}(1-ζ)^{5/2} H_*/G_ε = Z_ε e^{-h}`).  On the open strip
this is the paper's function; at `ζ = 0, 1` the quotient is Lean's junk value `0`. -/
noncomputable def ctHG (ε : ℝ) (ζ : ℂ) : ℂ :=
  uctSeedZ ε ζ * Complex.exp (-outerHbar ζ) / ((ζ : ℂ) ^ (5 / 2 : ℂ) * (1 - ζ) ^ (5 / 2 : ℂ))

/-- `g̃_1(w) = airyTwistedLaplaceC g₁ w`, `g₁ = Ai²/(u - a₁)²` (`ceG1 (airyZero 1)`); `g̃_1(0) = k` (`ctTg1_zero`). -/
noncomputable def ctTg1 (w : ℂ) : ℂ := airyTwistedLaplaceC (ceG1 (airyZero 1)) w

/-- `W̃_{g₁}^{sym,ε}` of `(fct:Wg1-exact)`; the prefactor `-c^{5/6}/(|C_Ai| φ_{c,0}(1))` is `1/F̃_*(i c_s c^{1/3})`
(`seedT 0 (seedScale c)`, as in `seedW`). -/
noncomputable def ctWg1 (ε c : ℝ) (ζ : ℂ) : ℂ :=
  (seedT 0 (seedScale c : ℂ))⁻¹ *
    (uctSeedZ ε ζ * Complex.exp (-outerHbar ζ) *
      (ctTg1 ((seedScale c : ℂ) * ζ) * seedT 0 ((seedScale c : ℂ) * (1 - ζ)) +
        seedT 0 ((seedScale c : ℂ) * ζ) * ctTg1 ((seedScale c : ℂ) * (1 - ζ))))

/-- `W̃_c^{fl,ε}`: the `ε`-lift of `S_pos = g₁ + g₁' - f₁/4` of `uct:pos-floor` (2) with spline order `m = 4` and
`δ₀ = β₁ K c^{-1/3}/2` (`K = K_*`), `W_F(c^{1/3}ζ) + ε W_D(c^{1/3}(1 - ζ))`, the main and dual symbols of
`iMain`/`iDual` in `uct_pos_floor_lift`. -/
noncomputable def ctWfl (K ε c : ℝ) (ζ : ℂ) : ℂ :=
  liftSymbol uctSpos (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ζ) +
    (ε : ℂ) * liftSymbol uctSpos (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - ζ))

/-- The bump term `c^{-1/3}(B̂(cζ) + ε B̂(c(1 - ζ)))` of `(fct:Wtot-hankel)` for a bump `B`
(`bumpDW`, `UctBumpMain`). -/
noncomputable def ctWbump (B : ℝ → ℝ) (ε c : ℝ) (ζ : ℂ) : ℂ := bumpDW c B ζ + (ε : ℂ) * bumpDW c B (1 - ζ)

/-- `W̃_c^{warp,ε}` of `(fct:Wwarp-hankel)`, `-|C_Ai| c^{-5/6} Φ̂_c(ζ) Φ̂_c(1-ζ) D_{τ₁}(ζ) H_*(ζ)/G_ε(ζ)`, for the splitting
function `Φ̂` and the compensator `D` (`-|C_Ai| = C_Ai = uctCAi`). -/
noncomputable def ctWwarp (PhiHat D : ℝ → ℝ → ℂ → ℂ) (ε c : ℝ) (ζ : ℂ) : ℂ :=
  ((uctCAi * c ^ (-(5 / 6 : ℝ)) : ℝ) : ℂ) * (PhiHat ε c ζ * PhiHat ε c (1 - ζ) * D ε c ζ * ctHG ε ζ)

/-- The total multiplier `W̃_c^ε` of `(fct:Wtot-hankel)`: `warp - d g₁ + η₀ fl + bump`, `d = K_d c^{-13/12}`, `η₀ = K₀ c^{-4/3}`;
`Kfl = K_*`, and `B` the physical bump (`K₁` inside). -/
noncomputable def ctWtot (PhiHat D : ℝ → ℝ → ℂ → ℂ) (B : ℝ → ℝ → ℝ → ℝ → ℝ) (ε c Kfl K0 K1 Kd : ℝ) (ζ : ℂ) : ℂ :=
  ctWwarp PhiHat D ε c ζ - ((Kd * c ^ (-(13 / 12 : ℝ)) : ℝ) : ℂ) * ctWg1 ε c ζ +
    ((K0 * c ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * ctWfl Kfl ε c ζ + ctWbump (B ε c K1) ε c ζ

/-! ### The origin values (proved) -/

lemma ctHG_zero (ε : ℝ) : ctHG ε 0 = 0 := by
  simp [ctHG, Complex.zero_cpow]

/-- `W̃^{warp}(0) = 0`.  (Lean's value at `0` is the junk value of `ctHG`; it is the paper's value because `Φ̂_c(ζ) = O(ζ³)` makes
the multiplier continuous there, which `FctMainHankelInputs.admissible` asserts for the total multiplier.) -/
lemma ctWwarp_zero (PhiHat D : ℝ → ℝ → ℂ → ℂ) (ε c : ℝ) : ctWwarp PhiHat D ε c 0 = 0 := by
  simp [ctWwarp, ctHG_zero]

lemma ctTg1_zero : ctTg1 0 = (ceK : ℂ) := by
  unfold ctTg1 airyTwistedLaplaceC
  have hint : ∫ u : ℝ, ((ceG1 (airyZero 1) u : ℝ) : ℂ) * Complex.exp ((0 : ℂ) * (u : ℂ)) =
      ((∫ u : ℝ, ceG1 (airyZero 1) u : ℝ) : ℂ) := by
    simp only [zero_mul, Complex.exp_zero, mul_one]
    exact integral_ofReal
  rw [hint, ceG1_integral_eq_one]
  simp

/-- `F̃_*(i c_s c^{1/3}) ≠ 0` for large `c` (`φ_{c,0}(1) = 1 + O(c^{-2/3})`, `uct:airy-trans` (2)). -/
lemma seedT_scale_ne : ∃ c₁ : ℝ, ∀ c : ℝ, c₁ ≤ c → seedT 0 (seedScale c : ℂ) ≠ 0 := by
  obtain ⟨C, hC0, hC⟩ := uct_airy_trans_phi 0
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, 8 ≤ c₁ ∧ C * c₁ ^ (-(2 / 3 : ℝ)) < 1 := by
    obtain ⟨c₂, -, hc₂⟩ := exists_rpow_neg_le (p := (2 / 3 : ℝ)) (by norm_num) (ε := 1 / (C + 1)) (by positivity)
    refine ⟨max 8 c₂, le_max_left _ _, ?_⟩
    have h1 := hc₂ (max 8 c₂) (le_max_right _ _)
    have h2 : C * (max 8 c₂) ^ (-(2 / 3 : ℝ)) ≤ C * (1 / (C + 1)) := mul_le_mul_of_nonneg_left h1 hC0
    have h3 : C * (1 / (C + 1)) < 1 := by
      rw [mul_one_div, div_lt_one (by linarith)]; linarith
    linarith
  refine ⟨c₁, fun c hc => ?_⟩
  have hc8 : 8 ≤ c := le_trans hc₁.1 hc
  have hc0 : 0 < c := by linarith
  have hcr : c ^ (-(2 / 3 : ℝ)) ≤ c₁ ^ (-(2 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hc (by norm_num)
  have hthr : 2 * c ^ (-(1 / 3 : ℝ)) ≤ ‖(1 : ℂ)‖ := by
    simp only [norm_one]
    have : c ^ (-(1 / 3 : ℝ)) ≤ 8 ^ (-(1 / 3 : ℝ)) := Real.rpow_le_rpow_of_nonpos (by norm_num) hc8 (by norm_num)
    have h8 : (8 : ℝ) ^ (-(1 / 3 : ℝ)) = 1 / 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  have h := hC c 0 hc0 le_rfl zero_le_one 1 (by simp) hthr
  simp only [iteratedDerivWithin_zero, norm_one] at h
  have hlt : ‖uctPhi c 0 1 - 1‖ < 1 := by
    refine lt_of_le_of_lt ?_ hc₁.2
    calc ‖uctPhi c 0 1 - 1‖ ≤ C * c ^ (-(2 / 3 : ℝ)) * 1 := by simpa using h
      _ ≤ C * c₁ ^ (-(2 / 3 : ℝ)) := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hcr hC0
  have hne : uctPhi c 0 1 ≠ 0 := by
    intro h0
    rw [h0] at hlt
    simp at hlt
  have e : uctPhi c 0 1 = ((c ^ (5 / 6 : ℝ) / uctCAi : ℝ) : ℂ) * (1 : ℂ) ^ (5 / 2 : ℂ) * seedT 0 (seedScale c : ℂ) := by
    unfold uctPhi seedT seedScale; rw [mul_one]
  intro h0
  apply hne
  rw [e, h0, mul_zero]

/-- `W̃_{g₁}^{sym,ε}(0) = k` (`k = g̃_1(0) = ceK`; `F̃_*(0) = 0`). -/
lemma ctWg1_zero {c : ℝ} (ε : ℝ) (hT : seedT 0 (seedScale c : ℂ) ≠ 0) : ctWg1 ε c 0 = (ceK : ℂ) := by
  have h0 : seedT 0 0 = 0 := by
    have := seedT_zero (δ := 0) le_rfl zero_le_one
    simpa using this
  unfold ctWg1
  simp only [mul_zero, sub_zero, mul_one, h0, ctTg1_zero, uctSeedZ_zero, outerHbar_zero, neg_zero, Complex.exp_zero, zero_mul,
    add_zero, one_mul]
  field_simp

/-- `|Re W̃_c^{fl,ε}(0)|` is bounded by an absolute constant (`W_F(0) = k ∫ S_pos`, `W_D(c^{1/3})` bounded by `U.2`). -/
lemma ctWfl_zero_bound : ∃ C : ℝ, ∀ K ε c : ℝ, 0 ≤ K → 0 < c → (ε = 1 ∨ ε = -1) → |(ctWfl K ε c 0).re| ≤ C := by
  obtain ⟨Cr, hCr0, hCr⟩ := hasU2_uctSpos.rhp
  refine ⟨|ceK * ∫ u : ℝ, uctSpos u| + Cr, fun K ε c hK hc hε => ?_⟩
  have hnorm : ‖ctWfl K ε c 0‖ ≤ |ceK * ∫ u : ℝ, uctSpos u| + Cr := by
    unfold ctWfl
    simp only [mul_zero, sub_zero, mul_one]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [liftSymbol_zero_eq hasU2_uctSpos]; simp
    · set δ₀ := ceBeta1 * K * liftEps c / 2
      set w : ℂ := ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ)
      have hw : 0 ≤ w.re := by simp [w]; positivity
      have h1 : ‖liftSymbol uctSpos δ₀ 4 w‖ ≤ Cr := by
        unfold liftSymbol
        rw [norm_mul]
        have hM : ‖liftMultiplier δ₀ 4 w‖ ≤ 1 := by
          refine (norm_liftMultiplier_le_pow δ₀ 4 w).trans ?_
          refine pow_le_one₀ (uctE1r_pos _).le ?_
          have hs : 0 ≤ ceCs * δ₀ / (4 : ℕ) * w.re := by
            have := ceCs_pos; have := ceBeta1_pos
            have : 0 ≤ liftEps c := by unfold liftEps; positivity
            simp only [δ₀]; positivity
          calc uctE1r _ ≤ uctE1r 0 := uctE1r_anti hs
            _ = 1 := by simp [uctE1r]
        have hX := hCr w hw
        have h5 : ‖1 + w‖ ^ (-(5 / 2 : ℝ)) ≤ 1 := by
          apply Real.rpow_le_one_of_one_le_of_nonpos _ (by norm_num)
          have := Complex.re_le_norm (1 + w)
          simp only [Complex.add_re, Complex.one_re] at this
          linarith
        calc ‖liftMultiplier δ₀ 4 w‖ * ‖airyTwistedLaplaceC uctSpos ((ceCs : ℂ) * w)‖
            ≤ 1 * (Cr * 1) := mul_le_mul hM (hX.trans (mul_le_mul_of_nonneg_left h5 hCr0.le)) (norm_nonneg _) zero_le_one
          _ = Cr := by ring
      have hε1 : |ε| = 1 := hε.elim (fun h => by simp [h]) (fun h => by simp [h])
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hε1, one_mul]
      exact h1
  exact (Complex.abs_re_le_norm _).trans hnorm

/-! ### The inputs -/

/-- **The open inputs of `fct:main-hankel`.**  The multipliers `ctWg1`, `ctWfl`, `ctWbump`, `ctWwarp`, `ctWtot` are concrete; the
only abstract parameters are the objects not yet in Lean, each named after its TeX label:

* `Dcomp ε c : ℂ → ℂ`, `D_{τ₁}(ζ) = e^{g_D(ζ)}` (`fct:comp-D`);
* `PhiHat ε c : ℂ → ℂ`, the splitting function `Φ̂_c` (`fct:splitting`, `(fct:Phihat-def)`; it depends on the chart `V` of `fct:comp-cfu`);
* `Bphys ε c K₁ : ℝ → ℝ`, the physical bump `B(L)` of `(fct:B-physical)` (`n_c`, `γ`, `I_osc^{warp}`, `I_fl`, `K₄`, `K₁`);
* `T1 ε c`, the zero `T₁` of `fct:warp-asymp` (1).

The fields are the TeX statements about these (the order of constants `K_* → K₄ → K₀ → K₁ → K_d → c₀` is built into the
quantifiers). -/
structure FctMainHankelInputs where
  /-- `D_{τ₁}` (`fct:comp-D`). -/
  Dcomp : ℝ → ℝ → ℂ → ℂ
  /-- `Φ̂_c` (`fct:splitting`). -/
  PhiHat : ℝ → ℝ → ℂ → ℂ
  /-- `B_c^ε` with the constant `K₁` (`(fct:B-physical)`, `(fct:B-five-def)`). -/
  Bphys : ℝ → ℝ → ℝ → ℝ → ℝ
  /-- `T₁` (`fct:warp-asymp` (1)). -/
  T1 : ℝ → ℝ → ℝ
  /-- `fct:comp-D`, `fct:comp-cfu`, `fct:inner-symbols`, `fct:warp-asymp` (1) (with `ct:langer-inv`, `ct:five-term-node`):
  the zero solve places the first zero at `T₁ = Δ₅^ε(c) + O(c^{-1})` (`K₄ = K₄^{(0)}` fixed). -/
  warp_zero : ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |T1 ε c - ctDelta5 ε c| ≤ C * c⁻¹
  /-- Step 1 of `fct:s4-proof` (`uct:admiss` (M1)-(M3) at `α = 1/2` and the `ε`-symmetry) for the total multiplier: `fct:splitting` (1)-(2)
  (`Φ̂_c = O(ζ³)`, `log log` growth), `fct:comp-D`, `fct:phikill`, `uct:airy-trans` and `uct:outer-growth` (for `ctWg1`; the part
  of this field about `ctWg1` and `ctWfl` is provable from them), `uct:pos-floor` (for `ctWfl`), `fct:bump-5` (1) with
  `fct:bump-sym-check` (for `ctWbump`). -/
  admissible : ∀ ε Kfl K0 K1 Kd : ℝ, (ε = 1 ∨ ε = -1) → 0 < K0 → 0 < K1 → 0 < Kd → ∃ c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c →
    StripAdmissFullData (1 / 2) (ctWtot PhiHat Dcomp Bphys ε c Kfl K0 K1 Kd) ∧
    ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 →
      ctWtot PhiHat Dcomp Bphys ε c Kfl K0 K1 Kd (1 - ζ) = (ε : ℂ) * ctWtot PhiHat Dcomp Bphys ε c Kfl K0 K1 Kd ζ
  /-- `fct:physical-budget`: `Re W̃^bump(0) = c^{-1/3}∫B + O(e^{-c' c^{1/2}}) ≤ (C₀(K₄) + b₂ K₁) c^{-13/12}`, with `C₀, b₂`
  independent of `K₁` and of the later `K_d`. -/
  physical_budget : ∃ C0 b2 : ℝ, ∀ K1 : ℝ, 0 < K1 → ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
    (ctWbump (Bphys ε c K1) ε c 0).re ≤ (C0 + b2 * K1) * c ^ (-(13 / 12 : ℝ))
  /-- `fct:physical-positive` (iii)-(iv) with its inputs `fct:warp-asymp` (2)-(3), `fct:splitting`, `fct:unscaled-cusp`,
  `fct:cusp-edge`, `uct:seed-asymp` (1)-(2) (`(fct:hg1-win)`-`(fct:hg1-mac)`), `fct:bump-5`, `fct:bump-sym-check`,
  `uct:pos-floor` (`Kfl = K_* ≥ 1`): `K₀, K₁` can be chosen independently of `K_d` so that the density of `W̃_c^ε` is positive on
  `L ≥ L_T`, i.e. `f ≥ 0` on `Δ ≥ T₁ + (2K_d/β₁) c^{-3/4}`. -/
  physical_positive : ∃ Kfl K0 K1 : ℝ, 1 ≤ Kfl ∧ 0 < K0 ∧ 0 < K1 ∧ ∀ Kd : ℝ, 0 < Kd → ∃ c₀ : ℝ,
    ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ∀ Δ : ℝ, T1 ε c + 2 * Kd / hankelBeta1 * c ^ (-(3 / 4 : ℝ)) ≤ Δ →
        0 ≤ admissF c (ctWtot PhiHat Dcomp Bphys ε c Kfl K0 K1 Kd) Δ

/-! ### The assembly -/

/-- The real part of the total multiplier at the origin (vacuum condition of `Step 1`):
`Re W̃(0) = -k d + η₀ Re W̃^fl(0) + Re W̃^bump(0)`, `k = ceK`. -/
lemma ctWtot_origin_re (PhiHat D : ℝ → ℝ → ℂ → ℂ) (B : ℝ → ℝ → ℝ → ℝ → ℝ) {ε c : ℝ} (hT : seedT 0 (seedScale c : ℂ) ≠ 0)
    (Kfl K0 K1 Kd : ℝ) :
    (ctWtot PhiHat D B ε c Kfl K0 K1 Kd 0).re =
      -(Kd * c ^ (-(13 / 12 : ℝ))) * ceK + K0 * c ^ (-(4 / 3 : ℝ)) * (ctWfl Kfl ε c 0).re +
        (ctWbump (B ε c K1) ε c 0).re := by
  simp [ctWtot, ctWwarp_zero, ctWg1_zero ε hT]

/-- **`fct:main-hankel`** (Paper I, `constant_terms_five.tex`): conditional on `FctMainHankelInputs`,
`T_c^ε ≤ Δ₅^ε(c) + C₊ c^{-3/4}` for `ε = ±1` and all real `c ≥ c₀`.  Proved (assembly) under the explicit hypothesis
structure; the fields are the not-yet-discharged TeX lemmas. -/
theorem fct_main_hankel (I : FctMainHankelInputs) :
    ∃ Cp c₀ : ℝ, 0 < Cp ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      hankelT ε c ≤ ctDelta5 ε c + Cp * c ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨cT, hcT⟩ := seedT_scale_ne
  obtain ⟨Cfl, hCfl⟩ := ctWfl_zero_bound
  obtain ⟨C0, b2, hbud⟩ := I.physical_budget
  obtain ⟨Kfl, K0, K1, hKfl, hK0, hK1, hpos⟩ := I.physical_positive
  obtain ⟨C1, cw, hwarp⟩ := I.warp_zero
  obtain ⟨Clow, clow, hlow⟩ := hb_thresholds_lower
  have hk := ceK_pos
  -- the choice of `K_d` after `K₀, K₁`
  set Kd : ℝ := (|C0| + |b2| * K1 + K0 * |Cfl|) / ceK + 1 with hKd
  have hKdpos : 0 < Kd := by
    have : 0 ≤ (|C0| + |b2| * K1 + K0 * |Cfl|) / ceK := by positivity
    linarith
  obtain ⟨cb, hcb⟩ := hbud K1 hK1
  obtain ⟨cp, hcp⟩ := hpos Kd hKdpos
  obtain ⟨ca1, hca1⟩ := I.admissible 1 Kfl K0 K1 Kd (Or.inl rfl) hK0 hK1 hKdpos
  obtain ⟨ca2, hca2⟩ := I.admissible (-1) Kfl K0 K1 Kd (Or.inr rfl) hK0 hK1 hKdpos
  have hβ := hankelBeta1_pos
  refine ⟨|C1| + 2 * Kd / hankelBeta1 + 1,
    max (max (max (max (max cw clow) (max cb cp)) (max ca1 ca2)) cT) 2, by positivity, ?_⟩
  intro ε c hε hc
  simp only [max_le_iff] at hc
  obtain ⟨⟨⟨⟨⟨hcw, hcl⟩, hcb', hcp'⟩, hcaa1, hcaa2⟩, hcT'⟩, hc2⟩ := hc
  have hc1 : 1 ≤ c := by linarith
  obtain ⟨hadm, hsym⟩ : StripAdmissFullData (1 / 2) (ctWtot I.PhiHat I.Dcomp I.Bphys ε c Kfl K0 K1 Kd) ∧
      ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 →
        ctWtot I.PhiHat I.Dcomp I.Bphys ε c Kfl K0 K1 Kd (1 - ζ) =
          (ε : ℂ) * ctWtot I.PhiHat I.Dcomp I.Bphys ε c Kfl K0 K1 Kd ζ := by
    rcases hε with rfl | rfl
    · exact hca1 c hcaa1
    · exact hca2 c hcaa2
  -- vacuum
  have hrpow : c ^ (-(4 / 3 : ℝ)) ≤ c ^ (-(13 / 12 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hrpos : 0 < c ^ (-(13 / 12 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  have hrpos' : 0 ≤ c ^ (-(4 / 3 : ℝ)) := (Real.rpow_pos_of_pos (by linarith) _).le
  have hvac : (ctWtot I.PhiHat I.Dcomp I.Bphys ε c Kfl K0 K1 Kd 0).re < 0 := by
    rw [ctWtot_origin_re _ _ _ (hcT c hcT')]
    have h1 := hcb ε c hε hcb'
    have h2 := hCfl Kfl ε c (by linarith) (by linarith) hε
    have h3 : K0 * c ^ (-(4 / 3 : ℝ)) * (ctWfl Kfl ε c 0).re ≤ K0 * |Cfl| * c ^ (-(13 / 12 : ℝ)) := by
      have : (ctWfl Kfl ε c 0).re ≤ |Cfl| := le_trans (le_abs_self _) (le_trans h2 (le_abs_self _))
      calc K0 * c ^ (-(4 / 3 : ℝ)) * (ctWfl Kfl ε c 0).re ≤ K0 * c ^ (-(4 / 3 : ℝ)) * |Cfl| :=
            mul_le_mul_of_nonneg_left this (mul_nonneg hK0.le hrpos')
        _ = K0 * |Cfl| * c ^ (-(4 / 3 : ℝ)) := by ring
        _ ≤ K0 * |Cfl| * c ^ (-(13 / 12 : ℝ)) :=
            mul_le_mul_of_nonneg_left hrpow (mul_nonneg hK0.le (abs_nonneg _))
    have h4 : (C0 + b2 * K1) * c ^ (-(13 / 12 : ℝ)) ≤ (|C0| + |b2| * K1) * c ^ (-(13 / 12 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ hrpos.le
      have : b2 * K1 ≤ |b2| * K1 := mul_le_mul_of_nonneg_right (le_abs_self _) hK1.le
      linarith [le_abs_self C0]
    have h5 : Kd * ceK = |C0| + |b2| * K1 + K0 * |Cfl| + ceK := by
      rw [hKd]; field_simp
    nlinarith [mul_pos hk hrpos]
  have hfeas : IsHankelFeasible c ε (I.T1 ε c + 2 * Kd / hankelBeta1 * c ^ (-(3 / 4 : ℝ)))
      (admissF c (ctWtot I.PhiHat I.Dcomp I.Bphys ε c Kfl K0 K1 Kd)) :=
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

/-- `fct:main-hankel`, conditional on the inputs, in the subtracted upper-bound form consumed by `thm:ct-upper` (i). -/
theorem fct_main_hankel_upper (I : FctMainHankelInputs) :
    ∃ Cp c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → hankelT ε c - ctDelta5 ε c ≤ Cp * c ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨Cp, c₀, -, h⟩ := fct_main_hankel I
  exact ⟨Cp, c₀, fun ε c hε hc => by linarith [h ε c hε hc]⟩

/-- info: 'FormalResearch.SignUncertainty.ctWg1_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctWg1_zero

/-- info: 'FormalResearch.SignUncertainty.seedT_scale_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedT_scale_ne

/-- info: 'FormalResearch.SignUncertainty.ctWfl_zero_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctWfl_zero_bound

/-- info: 'FormalResearch.SignUncertainty.fct_main_hankel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fct_main_hankel

end FormalResearch.SignUncertainty
