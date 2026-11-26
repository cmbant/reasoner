/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.StripAdmiss
public import FormalResearch.SignUncertainty.CtLower
public import FormalResearch.SignUncertainty.UctSeedW
public import FormalResearch.SignUncertainty.UctSeedWHolder
public import FormalResearch.SignUncertainty.UctSeedAdmiss
public import FormalResearch.SignUncertainty.UctSeedEdgeV
public import FormalResearch.SignUncertainty.UctFloorAdmiss
public import FormalResearch.SignUncertainty.UctAiryTransPhi
public import FormalResearch.SignUncertainty.UctPosFloorWpos
public import FormalResearch.SignUncertainty.UctBumpMain
public import FormalResearch.SignUncertainty.UctBumpEdge
public import FormalResearch.SignUncertainty.HankelThresholds

/-!
# `fct:main-hankel`: concrete multipliers and the lift (F2a skeleton, definitions part)

The concrete multipliers `ctWg1`, `ctWfl`, `ctWbump`, `ctWwarp`, `ctWtot` of the five-term Hankel witness `(fct:Wtot-hankel)`, the lift
`hankel_feasible_of_strip`, their admissibility and symmetry (`ctWtot_admissible`), the corner value `ctWtot_zero_eq`, and the statements of
the fields of `FctMainHankelInputs` that are about one datum only (`FctWarpZeroStmt`, `FctSplittingNormStmt`, `FctBumpProfileStmt`,
`FctPhysicalBudgetStmt`).  The hypothesis structure and the headline `fct_main_hankel` are in `FctMainHankel` (they need the proofs of the
bump fields, which import this file).
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

lemma ctTg1_zero : ctTg1 0 = (ceK : ℂ) := by
  unfold ctTg1 airyTwistedLaplaceC
  have hint : ∫ u : ℝ, ((ceG1 (airyZero 1) u : ℝ) : ℂ) * Complex.exp ((0 : ℂ) * (u : ℂ)) =
      ((∫ u : ℝ, ceG1 (airyZero 1) u : ℝ) : ℂ) := by
    simp only [zero_mul, Complex.exp_zero, mul_one]
    exact integral_ofReal
  rw [hint, ceG1_integral_eq_one]
  simp

/-- `F̃_{*,δ}(i c_s c^{1/3}) ≠ 0` for large `c`, uniformly in `0 ≤ δ ≤ 1` (`φ_{c,δ}(1) = 1 + O(c^{-2/3})`, `uct:airy-trans` (2)). -/
lemma seedT_scale_ne : ∃ c₁ : ℝ, ∀ c : ℝ, c₁ ≤ c → ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → seedT δ (seedScale c : ℂ) ≠ 0 := by
  obtain ⟨C, hC0, hC⟩ := uct_airy_trans_phi 0
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, 8 ≤ c₁ ∧ C * c₁ ^ (-(2 / 3 : ℝ)) < 1 := by
    obtain ⟨c₂, -, hc₂⟩ := exists_rpow_neg_le (p := (2 / 3 : ℝ)) (by norm_num) (ε := 1 / (C + 1)) (by positivity)
    refine ⟨max 8 c₂, le_max_left _ _, ?_⟩
    have h1 := hc₂ (max 8 c₂) (le_max_right _ _)
    have h2 : C * (max 8 c₂) ^ (-(2 / 3 : ℝ)) ≤ C * (1 / (C + 1)) := mul_le_mul_of_nonneg_left h1 hC0
    have h3 : C * (1 / (C + 1)) < 1 := by
      rw [mul_one_div, div_lt_one (by linarith)]; linarith
    linarith
  refine ⟨c₁, fun c hc δ hδ0 hδ1 => ?_⟩
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
  have h := hC c δ hc0 hδ0 hδ1 1 (by simp) hthr
  simp only [iteratedDerivWithin_zero, norm_one] at h
  have hlt : ‖uctPhi c δ 1 - 1‖ < 1 := by
    refine lt_of_le_of_lt ?_ hc₁.2
    calc ‖uctPhi c δ 1 - 1‖ ≤ C * c ^ (-(2 / 3 : ℝ)) * 1 := by simpa using h
      _ ≤ C * c₁ ^ (-(2 / 3 : ℝ)) := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hcr hC0
  have hne : uctPhi c δ 1 ≠ 0 := by
    intro h0
    rw [h0] at hlt
    simp at hlt
  have e : uctPhi c δ 1 = ((c ^ (5 / 6 : ℝ) / uctCAi : ℝ) : ℂ) * (1 : ℂ) ^ (5 / 2 : ℂ) * seedT δ (seedScale c : ℂ) := by
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

lemma re_mul_real_nonneg {a : ℝ} (ha : 0 ≤ a) {ζ : ℂ} (hζ : 0 ≤ ζ.re) : 0 ≤ (((a : ℝ) : ℂ) * ζ).re := by
  simp only [Complex.re_ofReal_mul]; exact mul_nonneg ha hζ

/-! ### Admissibility of `ctWg1`: a real combination of three seed multipliers -/

lemma seedT_lin (δ : ℝ) {w : ℂ} (hw : 0 ≤ w.re) : seedT δ w = seedT 0 w - (δ : ℂ) * ctTg1 w := by
  rw [seedT_eq_text δ hw, seedT_eq_text 0 hw]
  unfold ctTg1
  rw [uctG1Ext_eq hw]
  simp only [seedText, Complex.ofReal_zero, zero_mul, sub_zero]

/-- `F̃_{*,δ}(i c_s c^{1/3})`, a real number. -/
noncomputable def ctTr (c δ : ℝ) : ℝ := airyTwistedLaplace (uctFstarDelta δ) (seedScale c)

lemma seedT_scale_eq (c δ : ℝ) : seedT δ (seedScale c : ℂ) = (ctTr c δ : ℂ) := by
  unfold seedT ctTr; exact airyTwistedLaplaceC_ofReal _ _

/-- `ctWg1` is the real combination `(r₁/r₀) W^seed_1 - 4 (r_{1/2}/r₀) W^seed_{1/2} + 3 W^seed_0` of seed multipliers (polarisation of
`T_δ(x) T_δ(y) = T₀T₀ - δ (g T₀ + T₀ g) + δ² g g` at `δ = 0, 1/2, 1`), on the closed strip. -/
lemma ctWg1_eq (ε : ℝ) {c : ℝ} (h0 : seedT 0 (seedScale c : ℂ) ≠ 0) (h1 : seedT 1 (seedScale c : ℂ) ≠ 0)
    (hh : seedT (1 / 2) (seedScale c : ℂ) ≠ 0) (hc : 0 < c) {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    ctWg1 ε c ζ = ((ctTr c 1 / ctTr c 0 : ℝ) : ℂ) * seedW ε 1 c ζ -
      4 * ((ctTr c (1 / 2) / ctTr c 0 : ℝ) : ℂ) * seedW ε (1 / 2) c ζ + 3 * seedW ε 0 c ζ := by
  have ha := seedScale_pos hc
  have hx : 0 ≤ ((seedScale c : ℂ) * ζ).re := re_mul_real_nonneg ha.le hζ.1
  have hy : 0 ≤ ((seedScale c : ℂ) * (1 - ζ)).re := re_mul_real_nonneg ha.le (by simp; linarith [hζ.2])
  have e0 := seedT_scale_eq c 0
  have e1 := seedT_scale_eq c 1
  have eh := seedT_scale_eq c (1 / 2)
  rw [e0] at h0
  rw [e1] at h1
  rw [eh] at hh
  have h0' : (ctTr c 0 : ℂ) ≠ 0 := h0
  have h1' : (ctTr c 1 : ℂ) ≠ 0 := h1
  have hh' : (ctTr c (1 / 2) : ℂ) ≠ 0 := hh
  unfold ctWg1 seedW
  rw [seedT_lin 1 hx, seedT_lin 1 hy, seedT_lin (1 / 2) hx, seedT_lin (1 / 2) hy, e0, e1, eh]
  have e0' : seedT 0 ((seedScale c : ℂ) * ζ) = seedT 0 ((seedScale c : ℂ) * ζ) := rfl
  push_cast
  field_simp
  ring

theorem ctWg1_stripAdmissFull {ε c : ℝ} (hε : ε = 1 ∨ ε = -1) (hc : 0 < c)
    (hT : ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → seedT δ (seedScale c : ℂ) ≠ 0) : StripAdmissFullData (1 / 2) (ctWg1 ε c) := by
  have W1 := seedW_stripAdmissFull hε (δ := 1) zero_le_one le_rfl hc
  have Wh := seedW_stripAdmissFull hε (δ := 1 / 2) (by norm_num) (by norm_num) hc
  have W0 := seedW_stripAdmissFull hε (δ := 0) le_rfl zero_le_one hc
  have key := ((W1.smul_real (ctTr c 1 / ctTr c 0)).add ((Wh.smul_real (-4 * (ctTr c (1 / 2) / ctTr c 0))).add (W0.smul_real 3)))
  refine key.congr fun ζ h0 h1 => ?_
  rw [ctWg1_eq ε (hT 0 le_rfl zero_le_one) (hT 1 zero_le_one le_rfl) (hT (1 / 2) (by norm_num) (by norm_num)) hc ⟨h0, h1⟩]
  push_cast
  ring

theorem ctWg1_oneSub {ε c : ℝ} (hε : ε = 1 ∨ ε = -1) (hc : 0 < c)
    (hT : ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → seedT δ (seedScale c : ℂ) ≠ 0) {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    ctWg1 ε c (1 - ζ) = (ε : ℂ) * ctWg1 ε c ζ := by
  have hζ' : (1 - ζ) ∈ closedStrip := ⟨by simpa using hζ.2, by simpa using hζ.1⟩
  have a := hT 0 le_rfl zero_le_one
  have b := hT 1 zero_le_one le_rfl
  have c' := hT (1 / 2) (by norm_num) (by norm_num)
  rw [ctWg1_eq ε a b c' hc hζ', ctWg1_eq ε a b c' hc hζ, seedW_oneSub hε _ _ hζ, seedW_oneSub hε _ _ hζ, seedW_oneSub hε _ _ hζ]
  ring

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

/-! ### Limits at the corner `ζ = 0` (no junk values) -/

/-- The punctured closed strip at the origin. -/
lemma neBot_strip0 : (𝓝[closedStrip \ {0}] (0 : ℂ)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  intro e he
  have hm : 0 < min e 1 / 2 := by positivity
  refine ⟨((min e 1 / 2 : ℝ) : ℂ), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simpa using hm.le
  · simp; linarith [min_le_right e 1]
  · simpa using hm.ne'
  · rw [dist_zero_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
    linarith [min_le_left e 1]

/-- If `W` satisfies (M2) at `0` and tends to `v` along the strip, then `W 0 = v`: the value at the corner is the limit. -/
lemma strip_zero_eq_of_tendsto {W : ℂ → ℂ} (hW : StripAdmissFullData (1 / 2) W) {v : ℂ}
    (h : Tendsto W (𝓝[closedStrip \ {0}] 0) (𝓝 v)) : W 0 = v := by
  have := neBot_strip0
  obtain ⟨CH, hCH⟩ := hW.holder0
  have hnorm : Tendsto (fun ζ : ℂ => ‖ζ‖ ^ (1 / 2 : ℝ)) (𝓝[closedStrip \ {0}] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ζ : ℂ => ‖ζ‖) (𝓝 (0 : ℂ)) (𝓝 0) := by
      simpa using (continuous_norm.tendsto (0 : ℂ))
    have h2 : Tendsto (fun x : ℝ => x ^ (1 / 2 : ℝ)) (𝓝 0) (𝓝 0) := by
      simpa using (Real.continuousAt_rpow_const 0 (1 / 2 : ℝ) (Or.inr (by norm_num))).tendsto
    exact (h2.comp h1).mono_left nhdsWithin_le_nhds
  have hW0 : Tendsto W (𝓝[closedStrip \ {0}] 0) (𝓝 (W 0)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm' ?_ (by simpa using hnorm.const_mul CH)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))]
      with ζ hζ hb
    have := hCH ζ hζ.1.1 hζ.1.2 (by simpa using hb)
    simpa [norm_norm] using this
  exact tendsto_nhds_unique hW0 h

lemma ctHG_bound (ε : ℝ) : ∃ M : ℝ, ∀ᶠ ζ in 𝓝[closedStrip \ {0}] (0 : ℂ),
    ‖ctHG ε ζ‖ ≤ M * ‖ζ‖ ^ (-(5 / 2 : ℝ)) := by
  have hS0 : (0 : ℂ) ∈ closedStrip := ⟨by simp, by simp⟩
  have hZc : ContinuousWithinAt (uctSeedZ ε) (closedStrip \ {0}) 0 :=
    (((differentiableOn_uctSeedZ ε).continuousOn.mono fun ζ (hζ : ζ ∈ closedStrip) =>
      (⟨by linarith [hζ.1], by linarith [hζ.2]⟩ : -1 < ζ.re ∧ ζ.re < 2)).continuousWithinAt hS0).mono Set.sdiff_subset
  have hEc : ContinuousWithinAt (fun ζ => Complex.exp (-outerHbar ζ)) (closedStrip \ {0}) 0 :=
    ((continuousOn_outerHbar.continuousWithinAt hS0).neg.cexp).mono Set.sdiff_subset
  have hZ : ∀ᶠ ζ in 𝓝[closedStrip \ {0}] (0 : ℂ), ‖uctSeedZ ε ζ‖ ≤ 2 := by
    have := hZc.tendsto.eventually (Metric.closedBall_mem_nhds (uctSeedZ ε 0) (by norm_num : (0 : ℝ) < 1))
    filter_upwards [this] with ζ hζ
    rw [uctSeedZ_zero, dist_eq_norm] at hζ
    calc ‖uctSeedZ ε ζ‖ ≤ ‖(1 : ℂ)‖ + ‖uctSeedZ ε ζ - 1‖ := by
          simpa using norm_le_insert' (uctSeedZ ε ζ) 1
      _ ≤ 2 := by simp; linarith
  have hE : ∀ᶠ ζ in 𝓝[closedStrip \ {0}] (0 : ℂ), ‖Complex.exp (-outerHbar ζ)‖ ≤ 2 := by
    have h0 : Complex.exp (-outerHbar 0) = 1 := by simp [outerHbar_zero]
    have := hEc.tendsto.eventually (Metric.closedBall_mem_nhds (Complex.exp (-outerHbar 0)) (by norm_num : (0 : ℝ) < 1))
    filter_upwards [this] with ζ hζ
    rw [h0, dist_eq_norm] at hζ
    calc ‖Complex.exp (-outerHbar ζ)‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (-outerHbar ζ) - 1‖ := by
          simpa using norm_le_insert' (Complex.exp (-outerHbar ζ)) 1
      _ ≤ 2 := by simp; linarith
  have hq : (0 : ℝ) < (1 / 2 : ℝ) ^ (5 / 2 : ℝ) := by positivity
  refine ⟨4 / (1 / 2 : ℝ) ^ (5 / 2 : ℝ), ?_⟩
  filter_upwards [hZ, hE, self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))] with ζ hZ' hE' hζ hb
  have hζ0 : ζ ≠ 0 := hζ.2
  have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
  have hb' : ‖ζ‖ ≤ 1 / 2 := by simpa using hb
  have h1ζ : (1 / 2 : ℝ) ≤ ‖1 - ζ‖ := by
    have := norm_sub_norm_le (1 : ℂ) ζ
    simp at this; linarith
  have h1ne : (1 - ζ) ≠ 0 := by intro h; rw [h] at h1ζ; simp at h1ζ; linarith
  have e1 : ‖(ζ : ℂ) ^ (5 / 2 : ℂ)‖ = ‖ζ‖ ^ (5 / 2 : ℝ) := by
    rw [Complex.norm_cpow_of_ne_zero hζ0]; simp
  have e2 : ‖(1 - ζ : ℂ) ^ (5 / 2 : ℂ)‖ = ‖1 - ζ‖ ^ (5 / 2 : ℝ) := by
    rw [Complex.norm_cpow_of_ne_zero h1ne]; simp
  have e3 : (1 / 2 : ℝ) ^ (5 / 2 : ℝ) ≤ ‖1 - ζ‖ ^ (5 / 2 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) h1ζ (by norm_num)
  unfold ctHG
  rw [norm_div, norm_mul, norm_mul, e1, e2]
  have hp1 : 0 < ‖ζ‖ ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
  have hnn : ‖ζ‖ ^ (-(5 / 2 : ℝ)) = (‖ζ‖ ^ (5 / 2 : ℝ))⁻¹ := Real.rpow_neg hn.le _
  rw [hnn]
  have hnum : ‖uctSeedZ ε ζ‖ * ‖Complex.exp (-outerHbar ζ)‖ ≤ 4 := by nlinarith [norm_nonneg (uctSeedZ ε ζ), norm_nonneg (Complex.exp (-outerHbar ζ))]
  have hden : (1 / 2 : ℝ) ^ (5 / 2 : ℝ) * ‖ζ‖ ^ (5 / 2 : ℝ) ≤ ‖ζ‖ ^ (5 / 2 : ℝ) * ‖1 - ζ‖ ^ (5 / 2 : ℝ) := by
    nlinarith
  rw [div_le_iff₀ (mul_pos hp1 (lt_of_lt_of_le hq e3))]
  calc ‖uctSeedZ ε ζ‖ * ‖Complex.exp (-outerHbar ζ)‖ ≤ 4 := hnum
    _ = 4 / (1 / 2 : ℝ) ^ (5 / 2 : ℝ) * (‖ζ‖ ^ (5 / 2 : ℝ))⁻¹ * ((1 / 2 : ℝ) ^ (5 / 2 : ℝ) * ‖ζ‖ ^ (5 / 2 : ℝ)) := by
        field_simp
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left hden
        positivity

/-- `W̃^warp → 0` at the corner, from `Φ̂_c = O(ζ³)` (`fct:splitting` (1)), local boundedness of `Φ̂_c(1-ζ)` and `D_{τ₁}`:
`|ζ³| |ζ|^{-5/2} = |ζ|^{1/2}`. -/
lemma ctWwarp_tendsto_zero (PhiHat D : ℝ → ℝ → ℂ → ℂ) (ε c : ℝ)
    (h : ∃ C r : ℝ, 0 < r ∧ ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖ζ‖ ≤ r →
      ‖PhiHat ε c ζ‖ ≤ C * ‖ζ‖ ^ 3 ∧ ‖PhiHat ε c (1 - ζ)‖ ≤ C ∧ ‖D ε c ζ‖ ≤ C) :
    Tendsto (ctWwarp PhiHat D ε c) (𝓝[closedStrip \ {0}] 0) (𝓝 0) := by
  obtain ⟨C, r, hr, hC⟩ := h
  obtain ⟨M, hM⟩ := ctHG_bound ε
  have hnorm : Tendsto (fun ζ : ℂ => ‖ζ‖ ^ (1 / 2 : ℝ)) (𝓝[closedStrip \ {0}] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ζ : ℂ => ‖ζ‖) (𝓝 (0 : ℂ)) (𝓝 0) := by
      simpa using (continuous_norm.tendsto (0 : ℂ))
    have h2 : Tendsto (fun x : ℝ => x ^ (1 / 2 : ℝ)) (𝓝 0) (𝓝 0) := by
      simpa using (Real.continuousAt_rpow_const 0 (1 / 2 : ℝ) (Or.inr (by norm_num))).tendsto
    exact (h2.comp h1).mono_left nhdsWithin_le_nhds
  set Cc : ℝ := |uctCAi * c ^ (-(5 / 6 : ℝ))| with hCc
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ (by have := hnorm.const_mul (Cc * (|C| * |C| * |C|) * |M|); rwa [mul_zero] at this)
  filter_upwards [hM, self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds (0 : ℂ) hr)] with ζ hM' hζ hb
  have hζ0 : ζ ≠ 0 := hζ.2
  have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
  obtain ⟨h1, h2, h3⟩ := hC ζ hζ.1.1 hζ.1.2 (by simpa using hb)
  unfold ctWwarp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_mul, norm_mul]
  have e : ‖ζ‖ ^ 3 * ‖ζ‖ ^ (-(5 / 2 : ℝ)) = ‖ζ‖ ^ (1 / 2 : ℝ) := by
    rw [show ‖ζ‖ ^ 3 = ‖ζ‖ ^ ((3 : ℕ) : ℝ) from (Real.rpow_natCast _ 3).symm, ← Real.rpow_add hn]; norm_num
  have hA : ‖PhiHat ε c ζ‖ * ‖PhiHat ε c (1 - ζ)‖ * ‖D ε c ζ‖ ≤ |C| * ‖ζ‖ ^ 3 * |C| * |C| := by
    have a1 : ‖PhiHat ε c ζ‖ ≤ |C| * ‖ζ‖ ^ 3 := h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    have a2 : ‖PhiHat ε c (1 - ζ)‖ ≤ |C| := h2.trans (le_abs_self C)
    have a3 : ‖D ε c ζ‖ ≤ |C| := h3.trans (le_abs_self C)
    exact mul_le_mul (mul_le_mul a1 a2 (norm_nonneg _) (by positivity)) a3 (norm_nonneg _) (by positivity)
  have hH : ‖ctHG ε ζ‖ ≤ |M| * ‖ζ‖ ^ (-(5 / 2 : ℝ)) :=
    hM'.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity))
  calc Cc * (‖PhiHat ε c ζ‖ * ‖PhiHat ε c (1 - ζ)‖ * ‖D ε c ζ‖ * ‖ctHG ε ζ‖)
      ≤ Cc * ((|C| * ‖ζ‖ ^ 3 * |C| * |C|) * (|M| * ‖ζ‖ ^ (-(5 / 2 : ℝ)))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul hA hH (norm_nonneg _) (by positivity)) (abs_nonneg _)
    _ = Cc * (|C| * |C| * |C|) * |M| * (‖ζ‖ ^ 3 * ‖ζ‖ ^ (-(5 / 2 : ℝ))) := by ring
    _ = _ := by rw [e]

lemma continuousOn_liftSymbol {X : ℝ → ℝ} (hX : HasU2 X) (δ₀ : ℝ) (m : ℕ) :
    ContinuousOn (liftSymbol X δ₀ m) {w : ℂ | 0 ≤ w.re} := by
  unfold liftSymbol liftMultiplier
  refine ContinuousOn.mul ((differentiable_bsplineE1.continuous.comp (by fun_prop : Continuous fun w : ℂ => (((ceCs * δ₀ / m : ℝ) : ℂ) * w))).pow m).continuousOn ?_
  exact hX.continuousOn.comp (by fun_prop : Continuous fun w : ℂ => (ceCs : ℂ) * w).continuousOn
    fun w hw => by
      show 0 ≤ ((ceCs : ℂ) * w).re
      simp only [Complex.re_ofReal_mul]; exact mul_nonneg ceCs_pos.le hw

lemma ctWfl_continuousOn (K ε : ℝ) {c : ℝ} (hc : 0 < c) : ContinuousOn (ctWfl K ε c) closedStrip := by
  have ha : 0 ≤ c ^ (1 / 3 : ℝ) := by positivity
  have h1 : ContinuousOn (fun ζ : ℂ => liftSymbol uctSpos (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ζ)) closedStrip :=
    (continuousOn_liftSymbol hasU2_uctSpos _ 4).comp (by fun_prop : Continuous fun ζ : ℂ => (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ζ)).continuousOn
      fun ζ hζ => re_mul_real_nonneg ha hζ.1
  have h2 : ContinuousOn (fun ζ : ℂ => liftSymbol uctSpos (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - ζ))) closedStrip :=
    (continuousOn_liftSymbol hasU2_uctSpos _ 4).comp (by fun_prop : Continuous fun ζ : ℂ => (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - ζ))).continuousOn
      fun ζ hζ => re_mul_real_nonneg ha (by simp; linarith [hζ.2])
  unfold ctWfl
  exact h1.add (continuousOn_const.mul h2)

lemma ctWg1_continuousOn (ε : ℝ) {c : ℝ} (hc : 0 < c) : ContinuousOn (ctWg1 ε c) closedStrip := by
  have ha := seedScale_pos hc
  have hZ : ContinuousOn (uctSeedZ ε) closedStrip :=
    (differentiableOn_uctSeedZ ε).continuousOn.mono fun ζ (hζ : ζ ∈ closedStrip) =>
      (⟨by linarith [hζ.1], by linarith [hζ.2]⟩ : -1 < ζ.re ∧ ζ.re < 2)
  have hH : ContinuousOn outerHbar closedStrip := continuousOn_outerHbar
  have hmul : ∀ ζ ∈ closedStrip, 0 ≤ ((seedScale c : ℂ) * ζ).re := fun ζ hζ => re_mul_real_nonneg ha.le hζ.1
  have hmul1 : ∀ ζ ∈ closedStrip, 0 ≤ ((seedScale c : ℂ) * (1 - ζ)).re :=
    fun ζ hζ => re_mul_real_nonneg ha.le (by simp; linarith [hζ.2])
  have hT1 : ContinuousOn (fun ζ : ℂ => seedT 0 ((seedScale c : ℂ) * ζ)) closedStrip :=
    (seedT_continuousOn 0).comp (by fun_prop : Continuous fun ζ : ℂ => (seedScale c : ℂ) * ζ).continuousOn hmul
  have hT2 : ContinuousOn (fun ζ : ℂ => seedT 0 ((seedScale c : ℂ) * (1 - ζ))) closedStrip :=
    (seedT_continuousOn 0).comp (by fun_prop : Continuous fun ζ : ℂ => (seedScale c : ℂ) * (1 - ζ)).continuousOn hmul1
  have hg1 : ContinuousOn (fun ζ : ℂ => ctTg1 ((seedScale c : ℂ) * ζ)) closedStrip :=
    hasU2_ceG1.continuousOn.comp (by fun_prop : Continuous fun ζ : ℂ => (seedScale c : ℂ) * ζ).continuousOn hmul
  have hg2 : ContinuousOn (fun ζ : ℂ => ctTg1 ((seedScale c : ℂ) * (1 - ζ))) closedStrip :=
    hasU2_ceG1.continuousOn.comp (by fun_prop : Continuous fun ζ : ℂ => (seedScale c : ℂ) * (1 - ζ)).continuousOn hmul1
  unfold ctWg1
  exact (((hZ.mul hH.neg.cexp).mul ((hg1.mul hT2).add (hT1.mul hg2)))).const_mul _

lemma ctWbump_continuousOn {B : ℝ → ℝ} {b δ M α β : ℝ} {K : ℕ → ℝ} (hB : BumpProfile b δ M α β K B)
    (hb0 : 0 ≤ b * δ) (hbδ : b * δ ≤ 1) (hβ : 1 < β) (ε : ℝ) {c : ℝ} (hc : 0 < c) :
    ContinuousOn (ctWbump B ε c) closedStrip := by
  have hL := hB.continuousOn_laplace hb0 hbδ hβ
  have h1 : ContinuousOn (fun ζ : ℂ => bumpLaplace B ((c : ℂ) * ζ)) closedStrip :=
    hL.comp (by fun_prop : Continuous fun ζ : ℂ => (c : ℂ) * ζ).continuousOn
      fun ζ hζ => re_mul_real_nonneg hc.le hζ.1
  have h2 : ContinuousOn (fun ζ : ℂ => bumpLaplace B ((c : ℂ) * (1 - ζ))) closedStrip :=
    hL.comp (by fun_prop : Continuous fun ζ : ℂ => (c : ℂ) * (1 - ζ)).continuousOn
      fun ζ hζ => re_mul_real_nonneg hc.le (by simp; linarith [hζ.2])
  unfold ctWbump bumpDW
  exact (continuousOn_const.mul h1).add (continuousOn_const.mul (continuousOn_const.mul h2))

/-! ### Admissibility and symmetry of the summands and of the total -/

theorem ctWbump_stripAdmissFull {B : ℝ → ℝ} {δ M α β : ℝ} {K : ℕ → ℝ} (ε : ℝ) {c : ℝ} (hc : 0 < c) (hδ0 : 0 < δ)
    (hδ1 : 3 / 2 * δ ≤ 1) (hβ : 3 / 2 ≤ β) (hM : 0 ≤ M) (hB : BumpProfile (3 / 2) δ M α β K B) :
    StripAdmissFullData (1 / 2) (ctWbump B ε c) := by
  have h := bump_stripAdmissFull (b := 3 / 2) (by norm_num) hβ K hδ0 (by linarith) hδ1 hM hc hB
  have h' := (h.reflect).smul_real ε
  exact (h.add h').congr fun ζ _ _ => rfl

lemma ctWbump_oneSub {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (B : ℝ → ℝ) (c : ℝ) (ζ : ℂ) :
    ctWbump B ε c (1 - ζ) = (ε : ℂ) * ctWbump B ε c ζ := by
  unfold ctWbump
  rw [sub_sub_cancel]
  have : (ε : ℂ) * (ε : ℂ) = 1 := by rcases hε with h | h <;> simp [h]
  linear_combination (-(bumpDW c B (1 - ζ))) * this

lemma ctWfl_oneSub {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (K c : ℝ) (ζ : ℂ) :
    ctWfl K ε c (1 - ζ) = (ε : ℂ) * ctWfl K ε c ζ := by
  unfold ctWfl
  rw [sub_sub_cancel]
  have : (ε : ℂ) * (ε : ℂ) = 1 := by rcases hε with h | h <;> simp [h]
  linear_combination (-(liftSymbol uctSpos (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - ζ)))) * this

/-- **The floor summand is admissible** (Step 1 of `fct:s4-proof` for `W_pos`): `ctWfl` satisfies `(M1)`-`(M3)` at `α = 1/2` for
`K > 0` and `c ≥ 8` (the `g_1'` transform `g̃_1'(i w̃) = E₃ + w̃^{1/2} E₄` is `airySeedU2_sqForm`; the large-`|τ|` bounds are
`airySeedU2_imagAxisBounds` and the Cauchy bounds `o2_reflected_line_deriv_bound`; `liftSymbol_airySeedU2_stripAdmissFull`). -/
theorem ctWfl_stripAdmissFull {K : ℝ} (hK : 0 < K) (ε : ℝ) {c : ℝ} (hc : 8 ≤ c) :
    StripAdmissFullData (1 / 2) (ctWfl K ε c) := by
  have hc0 : 0 < c := by linarith
  have hδ : 0 < ceBeta1 * K * liftEps c / 2 := by
    have := ceBeta1_pos; have := liftEps_pos hc0; positivity
  exact liftSymbol_airySeedU2_stripAdmissFull (-1 / 4) 1 1 (ε := ε) hδ (m := 4) (by norm_num) hc

/-- The total multiplier is admissible (`(M1)`-`(M3)` at `α = 1/2`) and `ε`-symmetric, given the same for the warp and floor
summands; `ctWg1` (`ctWg1_stripAdmissFull`) and the bump (`ctWbump_stripAdmissFull`) are proved. -/
theorem ctWtot_admissible (PhiHat D : ℝ → ℝ → ℂ → ℂ) (B : ℝ → ℝ → ℝ → ℝ → ℝ) {ε c Kfl K0 K1 Kd : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hc : 0 < c) (hT : ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → seedT δ (seedScale c : ℂ) ≠ 0)
    (hwarp : StripAdmissFullData (1 / 2) (ctWwarp PhiHat D ε c))
    (hwarp_sym : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ctWwarp PhiHat D ε c (1 - ζ) = (ε : ℂ) * ctWwarp PhiHat D ε c ζ)
    (hfl : StripAdmissFullData (1 / 2) (ctWfl Kfl ε c))
    {δ M α β : ℝ} {K : ℕ → ℝ} (hδ0 : 0 < δ) (hδ1 : 3 / 2 * δ ≤ 1) (hβ : 3 / 2 ≤ β) (hM : 0 ≤ M)
    (hB : BumpProfile (3 / 2) δ M α β K (B ε c K1)) :
    StripAdmissFullData (1 / 2) (ctWtot PhiHat D B ε c Kfl K0 K1 Kd) ∧
      ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 →
        ctWtot PhiHat D B ε c Kfl K0 K1 Kd (1 - ζ) = (ε : ℂ) * ctWtot PhiHat D B ε c Kfl K0 K1 Kd ζ := by
  have hg := ctWg1_stripAdmissFull hε hc hT
  have hb := ctWbump_stripAdmissFull ε hc hδ0 hδ1 hβ hM hB
  refine ⟨?_, fun ζ h0 h1 => ?_⟩
  · have key := ((hwarp.add (hg.smul_real (-(Kd * c ^ (-(13 / 12 : ℝ)))))).add (hfl.smul_real (K0 * c ^ (-(4 / 3 : ℝ))))).add hb
    refine key.congr fun ζ _ _ => ?_
    unfold ctWtot
    push_cast
    ring
  · have hζ : ζ ∈ closedStrip := ⟨h0, h1⟩
    unfold ctWtot
    rw [hwarp_sym ζ h0 h1, ctWg1_oneSub hε hc hT hζ, ctWfl_oneSub hε, ctWbump_oneSub hε]
    ring

/-! ### Statements of the data fields -/

/-- `fct:warp-asymp` (1) (with `fct:comp-D`, `fct:comp-cfu`, `fct:inner-symbols`, `ct:langer-inv`, `ct:five-term-node`): the zero solve
gives `(L₁, α)` with `T₁ = Δ₅^ε(c) + O(c^{-1})` and `|α| ≤ C c^{-2/3}` (`K₄` fixed).  The zero condition `I_ε(L₁, α) = 0` itself is not
stated (no Lean definition of `I_ε`). -/
def FctWarpZeroStmt (T1 alpha : ℝ → ℝ → ℝ) : Prop :=
  ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
    |T1 ε c - ctDelta5 ε c| ≤ C * c⁻¹ ∧ |alpha ε c| ≤ C * c ^ (-(2 / 3 : ℝ))

/-- `fct:splitting` (2): `N_c = 1 + O_{K₄}(c⁻¹)`. -/
def FctSplittingNormStmt (Nc : ℝ → ℝ → ℝ) : Prop :=
  ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |Nc ε c - 1| ≤ C * c⁻¹

/-- `fct:bump-5` (1) with `fct:bump-sym-check`: the physical bump is a `BumpProfile` (`uct:bump-symbol`: smooth, supported in
`[3δ_L/2, ∞)`, symbol bounds), so that its Laplace transform is continuous on the closed strip. -/
def FctBumpProfileStmt (Bphys : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ K1 : ℝ, 0 < K1 → ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
    ∃ (δ M α β : ℝ) (K : ℕ → ℝ), 0 < δ ∧ 3 / 2 * δ ≤ 1 ∧ 3 / 2 ≤ β ∧ 0 ≤ M ∧ BumpProfile (3 / 2) δ M α β K (Bphys ε c K1)

/-- `fct:physical-budget`: `Re W̃^bump(0) = c^{-1/3}∫B + O(e^{-c' c^{1/2}}) ≤ (C₀(K₄) + b₂ K₁) c^{-13/12}`, with `C₀, b₂`
independent of `K₁` and of the later `K_d`. -/
def FctPhysicalBudgetStmt (Bphys : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∃ C0 b2 : ℝ, ∀ K1 : ℝ, 0 < K1 → ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
    (ctWbump (Bphys ε c K1) ε c 0).re ≤ (C0 + b2 * K1) * c ^ (-(13 / 12 : ℝ))

/-! ### The assembly -/

/-- The value of the total multiplier at the corner `0`, as the limit along the strip (no junk values: `W 0` is pinned by the Hölder
clause of `StripAdmissFullData` and the limits of the four summands): `W̃(0) = -k d + η₀ W̃^fl(0) + W̃^bump(0)`, `k = ceK`. -/
lemma ctWtot_zero_eq (PhiHat D : ℝ → ℝ → ℂ → ℂ) (B : ℝ → ℝ → ℝ → ℝ → ℝ) {ε c Kfl K0 K1 Kd : ℝ} (hc : 0 < c)
    (hT : seedT 0 (seedScale c : ℂ) ≠ 0)
    (hW : StripAdmissFullData (1 / 2) (ctWtot PhiHat D B ε c Kfl K0 K1 Kd))
    (hwarp : Tendsto (ctWwarp PhiHat D ε c) (𝓝[closedStrip \ {0}] 0) (𝓝 0))
    (hbump : ContinuousOn (ctWbump (B ε c K1) ε c) closedStrip) :
    ctWtot PhiHat D B ε c Kfl K0 K1 Kd 0 =
      -((Kd * c ^ (-(13 / 12 : ℝ)) : ℝ) : ℂ) * (ceK : ℂ) + ((K0 * c ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) * ctWfl Kfl ε c 0 +
        ctWbump (B ε c K1) ε c 0 := by
  have hS0 : (0 : ℂ) ∈ closedStrip := ⟨by simp, by simp⟩
  have t2 : Tendsto (ctWg1 ε c) (𝓝[closedStrip \ {0}] 0) (𝓝 (ctWg1 ε c 0)) :=
    (((ctWg1_continuousOn ε hc).continuousWithinAt hS0).mono Set.sdiff_subset).tendsto
  have t3 : Tendsto (ctWfl Kfl ε c) (𝓝[closedStrip \ {0}] 0) (𝓝 (ctWfl Kfl ε c 0)) :=
    (((ctWfl_continuousOn Kfl ε hc).continuousWithinAt hS0).mono Set.sdiff_subset).tendsto
  have t4 : Tendsto (ctWbump (B ε c K1) ε c) (𝓝[closedStrip \ {0}] 0) (𝓝 (ctWbump (B ε c K1) ε c 0)) :=
    ((hbump.continuousWithinAt hS0).mono Set.sdiff_subset).tendsto
  have key := ((hwarp.sub (t2.const_mul ((Kd * c ^ (-(13 / 12 : ℝ)) : ℝ) : ℂ))).add
    (t3.const_mul ((K0 * c ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ))).add t4
  have := strip_zero_eq_of_tendsto hW key
  rw [this, ctWg1_zero ε hT]
  ring


/-- info: 'FormalResearch.SignUncertainty.strip_zero_eq_of_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms strip_zero_eq_of_tendsto

/-- info: 'FormalResearch.SignUncertainty.ctWwarp_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctWwarp_tendsto_zero

/-- info: 'FormalResearch.SignUncertainty.ctWtot_zero_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctWtot_zero_eq

/-- info: 'FormalResearch.SignUncertainty.ctWg1_stripAdmissFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctWg1_stripAdmissFull

/-- info: 'FormalResearch.SignUncertainty.ctWbump_stripAdmissFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctWbump_stripAdmissFull

/-- info: 'FormalResearch.SignUncertainty.ctWtot_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctWtot_admissible

/-- info: 'FormalResearch.SignUncertainty.ctWg1_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctWg1_zero

/-- info: 'FormalResearch.SignUncertainty.seedT_scale_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedT_scale_ne

/-- info: 'FormalResearch.SignUncertainty.ctWfl_zero_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctWfl_zero_bound

end FormalResearch.SignUncertainty
