/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctMainHankelDefs
public import FormalResearch.SignUncertainty.FctRSymbol
public import FormalResearch.SignUncertainty.FctDcomp
public import FormalResearch.SignUncertainty.FctWarpAdmiss

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
`ctWg1_zero` (`= k = ceK` for large `c`, using `seedT_scale_ne`: `φ_{c,0}(1) = 1 + O(c^{-2/3})`) and `ctWfl_zero_bound`
(`|Re W̃^fl(0)| ≤ C`).  No fact depends on a junk value at the corners: the value `W̃_c^ε(0)` is computed as the limit along the strip
(`ctWtot_zero_eq`, from the Hölder clause (M2) of `StripAdmissFullData` and the limits of the summands; `ctWg1`, `ctWfl`,
`ctWbump` are continuous on the closed strip, `ctWg1_continuousOn` etc.), and `W̃^warp → 0` is `ctWwarp_tendsto_zero`, proved from
the corner bound `Φ̂_c = O(ζ³)` of the field `splitting` (it cancels the `ζ^{-5/2}` singularity of `H_*/G_ε`, `ctHG_bound`).  (Lean's
value of `ctHG`/`ctWwarp` at `ζ = 0` is a division-by-zero value; it is never used, and the Hölder clause of `fctWarp_admissible` is consistent
with it because the limit is `0`.)

**Data of `FctMainHankelInputs`**: `PhiHat` (`fct:splitting`, which depends on the chart of `fct:comp-cfu`), `T1`, `alpha`
(`fct:warp-asymp` (1)), `Nc` (`fct:splitting`), and the two deliberate parameters of the physical bump, the cutoff `chi` (with `IsCutoff chi`) and
`K4 ≥ 1` (`fct:comp-D`).  The physical bump `Bphys` is **not** data: `fctBphys` is the definition `(fct:B-physical)` with `H₀ = H_*`, `n_c = 1/N_c`
(`(fct:B-five-def)`).  Likewise the compensator `D_{τ₁}` is the definition `fctDcomp K4 alpha` (`FctDcomp.lean`).

**Conditional on the fields of `FctMainHankelInputs`** (`splitting`, `splitting_norm`, `warp_zero`, `physical_positive`): each is
the output of the named TeX lemma(s), stated about the concrete multipliers and these data.  The former fields `bump_profile` and `physical_budget` are
**proved** for `fctBphys` (`fctBphys_bumpProfile`, `fctBphys_physicalBudget`, from `fctMainHankel_bump_fields_concrete_of_factors`), and the former field `warp_admissible` is
**proved** (`fctWarp_admissible`, `FctWarpAdmiss.lean`: Step 1 of `fct:s4-proof` for the warp summand, from `fct:comp-D`, `uct:outer-growth` and the field `splitting`).  Proved lemmas
(`uct:admiss` = `uct_admiss_full`, `mat:T7`, `hb_thresholds_lower`, `uct:airy-trans`, `uct:pos-floor`, `uct:outer-growth`,
`fct:bump-5`, `uct:seed-asymp` (1), `fct:moment-solver`, `fct:phikill`, `fct:edge-ibp`, `fct:bump-sym-check`, `fct:physical-budget`) are used directly or enter through the
discharge of a field, not as fields.

**Satisfiability.** The data `PhiHat`, `T1`, `alpha`, `Nc` are free, so the fields are consistent only for the paper's actual `Φ̂_c`, `T₁`, `α`, `N_c`;
no field has been shown consistent in Lean.  Doubtful points: `warp_zero` hides `fct:comp-D`/`fct:comp-cfu`/
`fct:inner-symbols`, and `splitting` is `fct:splitting` (1)-(2) read as in `FctSplittingStmt` (including edge-trace derivative bounds for `Φ̂_c(iτ)`); `physical_positive` hides the five-term positivity (`fct:physical-positive` and its inputs) and is
the field most likely to need a sharper form once its proof is formalised.  The `T_c^ε` set is bounded below by
`hb_thresholds_lower`, so no field is needed for that.  The `ctWg1`, floor and bump parts of the admissibility of the total are proved (`ctWg1_stripAdmissFull`, a real combination of three
`seedW_stripAdmissFull` by polarisation; `ctWfl_stripAdmissFull`; `ctWbump_stripAdmissFull`; assembled in `ctWtot_admissible`).

Class: proved under the explicit hypothesis structure `FctMainHankelInputs` (not discharged).
-/
@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real
open FormalResearch.CohnElkies FormalResearch.Special FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctSym FormalResearch.SignUncertainty.FctCompD

namespace FormalResearch.SignUncertainty

/-! ### The physical bump -/

/-- **The physical bump `B_c^ε`** (`(fct:B-physical)` with `H₀ = H_*` and `n_c = 1/N_c`, `(fct:B-five-def)`): `physBump` with the cutoff `χ`, `K₄`, the
warp datum `O = I_osc^{warp}` built from `(T₁, α)` (`physOscDatum`, `fct:warp-asymp` (3)), `F = (L̃/(L-L₁)) I_fl(L̃)` (`physF`), `T₄ = τ₀⁴ I_fl`.  The
argument order is `(ε, c, K₁)`. -/
noncomputable def fctBphys (χ : ℝ → ℝ) (K4 : ℝ) (T1 alpha Nc : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun ε c K1 => physBump χ (1 / Nc ε c) c (physDelta c) (physShift ε c) K1 K4
    (physOscDatum StripKernelChoice.star K4 T1 alpha ε c) (physF (physShift ε c) (physL1 T1 ε c)) (fun L => tau0 L ^ 4 * uctIfl L)

/-- `fct:bump-5` (1) with `fct:bump-sym-check`, proved for `fctBphys` (the former field `bump_profile`). -/
theorem fctBphys_bumpProfile {χ : ℝ → ℝ} (hχ : IsCutoff χ) {K4 : ℝ} (hK4 : 1 ≤ K4) {T1 alpha Nc : ℝ → ℝ → ℝ}
    (hwarp : FctWarpZeroStmt T1 alpha) (hNc : FctSplittingNormStmt Nc) :
    FctBumpProfileStmt (fctBphys χ K4 T1 alpha Nc) :=
  (fctMainHankel_bump_fields_concrete_of_factors hχ StripKernelChoice.star hK4 T1 alpha Nc _ hwarp hNc (fun _ _ _ => rfl)).1

/-- `fct:physical-budget`, proved for `fctBphys` (the former field `physical_budget`). -/
theorem fctBphys_physicalBudget {χ : ℝ → ℝ} (hχ : IsCutoff χ) {K4 : ℝ} (hK4 : 1 ≤ K4) {T1 alpha Nc : ℝ → ℝ → ℝ}
    (hwarp : FctWarpZeroStmt T1 alpha) (hNc : FctSplittingNormStmt Nc) :
    FctPhysicalBudgetStmt (fctBphys χ K4 T1 alpha Nc) :=
  (fctMainHankel_bump_fields_concrete_of_factors hχ StripKernelChoice.star hK4 T1 alpha Nc _ hwarp hNc (fun _ _ _ => rfl)).2

/-! ### The inputs -/

/-- **The open inputs of `fct:main-hankel`.**  The multipliers `ctWg1`, `ctWfl`, `ctWbump`, `ctWwarp`, `ctWtot` the physical bump `fctBphys`
(`(fct:B-physical)`) and the compensator `fctDcomp` (`fct:comp-D`, built from `K4` and `alpha`) are concrete; the remaining data are the objects not yet in Lean, each named after its TeX label:

* `PhiHat ε c : ℂ → ℂ`, the splitting function `Φ̂_c` (`fct:splitting`, `(fct:Phihat-def)`; it depends on the chart `V` of `fct:comp-cfu`);
* `T1 ε c`, `alpha ε c`, the zero pair `(T₁, α)` of `fct:warp-asymp` (1) (`T₁ = (c/π²)e^{L₁}`); the zero condition `I_ε(L₁, α) = 0` and
  the IBP identity `(fct:exact-ibp)` have no Lean counterpart yet (`I_ε` is not defined in Lean), so `warp_zero` records only the two size bounds;
* `Nc ε c`, the normalisation `N_c = Φ^warp_c(1) = 1 - F₊(1)` of `fct:splitting` (`(fct:Phihat-def)`); the physical bump uses `n_c = 1/N_c`;
* the deliberate parameters `chi` (the cutoff of `(fct:B-physical)`, `IsCutoff chi`: smooth, `1` near `0`, supported in a bounded interval; the
  paper fixes no particular one) and `K4 ≥ 1` (the absolute constant of `fct:comp-D`).

The fields are the TeX statements about these (the order of constants `K_* → K₄ → K₀ → K₁ → K_d → c₀` is built into the
quantifiers). -/
structure FctMainHankelInputs where
  /-- `Φ̂_c` (`fct:splitting`). -/
  PhiHat : ℝ → ℝ → ℂ → ℂ
  /-- `T₁` (`fct:warp-asymp` (1)). -/
  T1 : ℝ → ℝ → ℝ
  /-- `α` of the zero pair `(L₁, α)` of `fct:warp-asymp` (1). -/
  alpha : ℝ → ℝ → ℝ
  /-- `N_c` (`fct:splitting`, `(fct:Phihat-def)`). -/
  Nc : ℝ → ℝ → ℝ
  /-- The cutoff `χ` of `(fct:B-physical)` (a deliberate parameter). -/
  chi : ℝ → ℝ
  /-- `χ` is a cutoff (`IsCutoff`). -/
  chi_cutoff : IsCutoff chi
  /-- The absolute constant `K₄ ≥ 1` (`fct:comp-D`; a deliberate parameter). -/
  K4 : ℝ
  /-- `K₄ ≥ 1`. -/
  K4_ge_one : 1 ≤ K4
  /-- `fct:splitting` (1)-(2) for `Φ̂_c` (`FctSplittingStmt`): holomorphic on `Re ζ > 0`, real-symmetric, `Φ̂_c = O(ζ³)` at `0`, the `log log` growth
  on `S̄` and the edge-trace derivative bounds.  With the proved `fct:comp-D` (`fctDcomp_compData`) and `H_*/G_ε` (`uct:outer-growth`) this gives Step 1 of
  `fct:s4-proof` for the warp summand (`fctWarp_admissible`) and the corner behaviour that makes `ctWwarp → 0` at `ζ = 0` (`ctWwarp_tendsto_zero`; the singularity
  `ζ^{-5/2}` of `H_*/G_ε` is cancelled). -/
  splitting : FctSplittingStmt PhiHat
  /-- `fct:splitting` (2): `N_c = 1 + O_{K₄}(c⁻¹)`. -/
  splitting_norm : FctSplittingNormStmt Nc
  /-- `fct:warp-asymp` (1): `T₁ = Δ₅^ε(c) + O(c^{-1})`, `|α| ≤ C c^{-2/3}`. -/
  warp_zero : FctWarpZeroStmt T1 alpha
  /-- `fct:physical-positive` (iii)-(iv) with its inputs `fct:warp-asymp` (2)-(3), `fct:splitting`, `fct:unscaled-cusp`,
  `fct:cusp-edge`, `uct:seed-asymp` (1)-(2) (`(fct:hg1-win)`-`(fct:hg1-mac)`), `fct:bump-5`, `fct:bump-sym-check`,
  `uct:pos-floor` (`Kfl = K_* ≥ 1`): `K₀, K₁` can be chosen independently of `K_d` so that the density of `W̃_c^ε` is positive on
  `L ≥ L_T`, i.e. `f ≥ 0` on `Δ ≥ T₁ + (2K_d/β₁) c^{-3/4}`. -/
  physical_positive : ∃ Kfl K0 K1 : ℝ, 1 ≤ Kfl ∧ 0 < K0 ∧ 0 < K1 ∧ ∀ Kd : ℝ, 0 < Kd → ∃ c₀ : ℝ,
    ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ∀ Δ : ℝ, T1 ε c + 2 * Kd / hankelBeta1 * c ^ (-(3 / 4 : ℝ)) ≤ Δ →
        0 ≤ admissF c (ctWtot PhiHat (fctDcomp K4 alpha) (fctBphys chi K4 T1 alpha Nc) ε c Kfl K0 K1 Kd) Δ

/-- `D_{τ₁}` of the inputs (`fct:comp-D`). -/
noncomputable abbrev FctMainHankelInputs.Dcomp (I : FctMainHankelInputs) : ℝ → ℝ → ℂ → ℂ :=
  fctDcomp I.K4 I.alpha

/-- The physical bump `B_c^ε` of the inputs (`(fct:B-five-def)`). -/
noncomputable abbrev FctMainHankelInputs.Bphys (I : FctMainHankelInputs) : ℝ → ℝ → ℝ → ℝ → ℝ :=
  fctBphys I.chi I.K4 I.T1 I.alpha I.Nc

/-- `bump_profile` (former field), proved. -/
theorem FctMainHankelInputs.bump_profile (I : FctMainHankelInputs) : FctBumpProfileStmt I.Bphys :=
  fctBphys_bumpProfile I.chi_cutoff I.K4_ge_one I.warp_zero I.splitting_norm

/-- `physical_budget` (former field), proved. -/
theorem FctMainHankelInputs.physical_budget (I : FctMainHankelInputs) : FctPhysicalBudgetStmt I.Bphys :=
  fctBphys_physicalBudget I.chi_cutoff I.K4_ge_one I.warp_zero I.splitting_norm

/-! ### The assembly -/

/-- **`fct:main-hankel`** (Paper I, `constant_terms_five.tex`): conditional on `FctMainHankelInputs`,
`T_c^ε ≤ Δ₅^ε(c) + C₊ c^{-3/4}` for `ε = ±1` and all real `c ≥ c₀`.  Proved (assembly) under the explicit hypothesis
structure; the fields are the not-yet-discharged TeX lemmas (the physical bump is the concrete `fctBphys`). -/
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
  obtain ⟨cbp, hcbp⟩ := I.bump_profile K1 hK1
  obtain ⟨cwa, hcwa⟩ := fctWarp_admissible I.K4_ge_one (alpha := I.alpha) ⟨C1, cw, fun ε c hε hc => (hwarp ε c hε hc).2⟩ I.splitting
  obtain ⟨cs, hcs⟩ := I.splitting
  obtain ⟨CD, cD, hD⟩ := fctDcomp_bound I.K4_ge_one (alpha := I.alpha) ⟨C1, cw, fun ε c hε hc => (hwarp ε c hε hc).2⟩
  have hβ := hankelBeta1_pos
  refine ⟨|C1| + 2 * Kd / hankelBeta1 + 1,
    max (max (max (max (max (max (max cw clow) (max cb cp)) (max cwa 8)) (max cT cbp)) 2) cD) cs, by positivity, ?_⟩
  intro ε c hε hc
  simp only [max_le_iff] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨hcw, hcl⟩, hcb', hcp'⟩, hcwa', hcfl'⟩, hcT', hcbp'⟩, hc2⟩, hcD⟩, hcs'⟩ := hc
  have hc1 : 1 ≤ c := by linarith
  obtain ⟨δ, M, α, β, K, hδ, hδ1, hβ, hM, hprof⟩ := hcbp ε c hε hcbp'
  obtain ⟨hadm, hsym⟩ := ctWtot_admissible I.PhiHat I.Dcomp I.Bphys (Kfl := Kfl) (K0 := K0) (K1 := K1) (Kd := Kd) hε
    (by linarith : 0 < c) (hcT c hcT') (hcwa ε c hε hcwa').1 (hcwa ε c hε hcwa').2 (ctWfl_stripAdmissFull (by linarith) ε hcfl') hδ hδ1 hβ hM hprof
  -- vacuum
  have hrpow : c ^ (-(4 / 3 : ℝ)) ≤ c ^ (-(13 / 12 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hrpos : 0 < c ^ (-(13 / 12 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  have hrpos' : 0 ≤ c ^ (-(4 / 3 : ℝ)) := (Real.rpow_pos_of_pos (by linarith) _).le
  have hvac : (ctWtot I.PhiHat I.Dcomp I.Bphys ε c Kfl K0 K1 Kd 0).re < 0 := by
    have hbump := ctWbump_continuousOn hprof (by positivity) (by linarith) (by linarith) ε (by linarith : 0 < c)
    have hzero := ctWtot_zero_eq I.PhiHat I.Dcomp I.Bphys (by linarith : 0 < c) (hcT c hcT' 0 le_rfl zero_le_one) hadm
      (ctWwarp_tendsto_zero _ _ ε c (by
        obtain ⟨Cφ, hφ⟩ := (hcs ε c hε hcs').corner
        refine ⟨max Cφ CD, 1, one_pos, fun ζ h0 h1 hζ => ⟨?_, ?_, ?_⟩⟩
        · exact (hφ ζ h0 h1 hζ).1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        · exact (hφ ζ h0 h1 hζ).2.trans (le_max_left _ _)
        · exact (hD ε c hε hcD ζ ⟨h0, h1⟩).trans (le_max_right _ _))) hbump
    rw [hzero]
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
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
  have h2 := (hwarp ε c hε hcw).1
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


/-- info: 'FormalResearch.SignUncertainty.fct_main_hankel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fct_main_hankel

/-- info: 'FormalResearch.SignUncertainty.fctBphys_bumpProfile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctBphys_bumpProfile

/-- info: 'FormalResearch.SignUncertainty.fctBphys_physicalBudget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctBphys_physicalBudget

end FormalResearch.SignUncertainty