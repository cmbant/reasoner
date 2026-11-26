module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroBumpWindow
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroVacuumLobe
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroVacuumPrelim

/-!
# The deep lobe of the bumped two-zero comb at every weight (`ut:T2`, `ut:Vac`, "Absolute far-left estimate")

Source: `upper_transfer.tex`, Theorem T2 (`ut:T2`) at fixed `(w, Q)`; at `w > 1` the comb of the test is the bumped comb
`T_{χ(p)} B₁^{(p)}` (`TwoZeroDesign.bumpComb`), and the Cardy kernel carries the factor `(2x)^{w-1}` (`rem:cardy`).

* `bumpComb_ofReal`: on the real axis `B₂^{(p)}(x) = R_bump(x) B₂(x)` with `1 ≤ R ≤ C_p` and `R ≤ 1 + C'/c'` for
  `x ≤ ξ_* + r_p` (`fw:e3.3`);
* `combProfile_bump_ratio`: the same for the profile `h₂^{(p)}(t) = R(√(3t/c')) h₂(t)`;
* `cardyV_le_pow_exp`: `V(c x²/3) ≤ (2x)^{w-1} e^{c L(x)}` (`rem:cardy`, `kernelK_le_pow_mul_exp`);
* `twoZeroBump_lobe_bound`: the deep lobe `t ≤ t_S` of `|h₂^{(p)}| V` is `≤ F_{2,c} (C_L S^{-3/2} + ε)` at every weight,
  uniformly on a compact family and in the cut (the order-`p` far Cardy bound replaces `cardyFarBound_prob`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.WeightAxioms
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Holes
  FormalResearch.ModularBootstrap.Upper.Membership FormalResearch.ModularBootstrap.Upper.Window.Cardy
  FormalResearch.ModularBootstrap.Upper.Window.Tail FormalResearch.ModularBootstrap.Upper.Bump
  FormalResearch.ModularBootstrap.Upper.Positivity
open TwoZeroDesign

/-! ### 1. The bump on the real axis -/

/-- **`R_bump` for the two-zero comb, complex form** (`fw:e3.3`): for `c` large, every `d`, cut `N' ≥ n + 2` and `x ≥ 0`,
`B₂^{(p)}(x) = R · B₂(x)` with `1 ≤ R ≤ C_p` and `R ≤ 1 + C'/c` for `x ≤ ξ_* + r_p`. -/
theorem bumpComb_ofReal (bd : BumpData) {n : ℕ} :
    ∃ Cp C' : ℝ, ∀ᶠ c in atTop, ∀ d : TwoZeroDesign n, ∀ N' : ℕ, n + 2 ≤ N' → ∀ x : ℝ, 0 ≤ x →
      ∃ R : ℝ, 1 ≤ R ∧ R ≤ Cp ∧ (x ≤ xiStar + bd.r → R ≤ 1 + C' / c) ∧
        d.bumpComb bd c N' (x : ℂ) = (R : ℂ) * d.twoZeroComb c (x : ℂ) := by
  refine ⟨bumpC bd (1 / 4), bumpC' bd (1 / 4), ?_⟩
  filter_upwards [bump_lemma bd (η₀ := 1 / 4) (by norm_num) le_rfl] with c hb d N' hN' x hx
  obtain ⟨hc, hbm, h1, h2, h3⟩ := hb 2 (n + 2) N' d.sigmaSeq (fun k => lambdaComb c * d.epsHatSite k) x
    (by omega) hN' hx
  refine ⟨_, h1, h2, h3, ?_⟩
  have e1 : d.bumpComb bd c N' (x : ℂ) = (((tFac (d.chiP c) x *
      (bumpFactor bd c (1 / 4) (n + 2) N' x *
        combReal c 2 (n + 2) (1 / 4) d.sigmaSeq (fun k => lambdaComb c * d.epsHatSite k) x)) : ℝ) : ℂ) := by
    unfold bumpComb bumpedBase
    rw [hbm, tFac_eq]; push_cast; ring
  have e2 : d.twoZeroComb c (x : ℂ) = (((tFac (d.chiP c) x *
        combReal c 2 (n + 2) (1 / 4) d.sigmaSeq (fun k => lambdaComb c * d.epsHatSite k) x) : ℝ) : ℂ) := by
    unfold twoZeroComb comb
    rw [hc, tFac_eq]; push_cast; ring
  rw [e1, e2]
  push_cast
  ring

/-- `‖B₂^{(p)}(x)‖ = R ‖B₂(x)‖` for the multiplier `R` of `bumpComb_ofReal`. -/
lemma norm_bumpComb_le {n : ℕ} {bd : BumpData} {c : ℝ} {d : TwoZeroDesign n} {N' : ℕ} {x R : ℝ}
    (h : d.bumpComb bd c N' (x : ℂ) = (R : ℂ) * d.twoZeroComb c (x : ℂ)) (hR : 1 ≤ R) :
    ‖d.bumpComb bd c N' (x : ℂ)‖ = R * ‖d.twoZeroComb c (x : ℂ)‖ := by
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]

/-- **The value identity on the profile**: `h₂^{(p)}(t) = R · h₂(t)` with `R = R_bump(√(3t/c'))`, `1 ≤ R ≤ C_p`,
`R ≤ 1 + C'/c'` for `√(3t/c') ≤ ξ_* + r_p`. -/
theorem combProfile_bump_ratio (bd : BumpData) {n : ℕ} :
    ∃ Cp C' : ℝ, ∀ᶠ c in atTop, ∀ d : TwoZeroDesign n, ∀ N' : ℕ, n + 2 ≤ N' → ∀ t : ℝ,
      ∃ R : ℝ, 1 ≤ R ∧ R ≤ Cp ∧ (xOf c t ≤ xiStar + bd.r → R ≤ 1 + C' / c) ∧
        combProfile c (d.bumpComb bd c N') t = R * combProfile c (d.twoZeroComb c) t := by
  obtain ⟨Cp, C', h⟩ := re_profile_bump (n := n) bd
  refine ⟨Cp, C', ?_⟩
  filter_upwards [h] with c hc d N' hN' t
  obtain ⟨R, h1, h2, h3, h4⟩ := hc d N' hN' (xOf c t) (xOf_nonneg c t)
  exact ⟨R, h1, h2, h3, h4⟩

/-! ### 2. The Cardy weight on the lobe, at every weight -/

/-- `V(c x²/3) ≤ (2x)^{w-1} e^{c L(x)}` for `c ≥ 12 S`, `x ≥ 0` (`V ≤ K_a`, `K_a(t) ≤ (t/a)^{(w-1)/2} e^{4π√(at)}`). -/
lemma cardyV_le_pow_exp (prob : FixedWeightProblem) {c x : ℝ} (hc : 0 < c) (hcS : prob.totalShift ≤ c / 12)
    (hx : 0 ≤ x) :
    prob.cardyV (c / 12) (c * x ^ 2 / 3) ≤ (2 * x) ^ (prob.w - 1) * Real.exp (c * Bessel.besselL x) := by
  have ht : 0 ≤ c * x ^ 2 / 3 := by positivity
  have h1 := cardyV_le_kernelK prob hcS ht
  have h2 := kernelK_le_pow_mul_exp (w := prob.w) prob.hw (a := c / 12) (t := c * x ^ 2 / 3) (by positivity) ht
  refine h1.trans (h2.trans (le_of_eq ?_))
  have e1 : (c * x ^ 2 / 3) / (c / 12) = (2 * x) ^ 2 := by field_simp; ring
  have e2 : c / 12 * (c * x ^ 2 / 3) = (c * x / 6) ^ 2 := by ring
  rw [e1, e2, Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)]
  unfold Bessel.besselL
  ring_nf

/-! ### 3. The lobe integrals for an abstract comb with the pointwise lobe bound -/

/-- The pointwise lobe hypothesis (`eq:ut:T2-left`) for a comb `B` at a fixed `c`. -/
def LobePt (c K S₁ : ℝ) (B : ℂ → ℂ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → x < xiStar → lambdaComb c * S₁ ≤ xiStar - x →
    ‖B (x : ℂ)‖ * Real.exp (c * Bessel.besselL x) ≤
      K * (xiStar - x) ^ (-(5 / 2 : ℝ)) * Real.exp (c * (majorantReal x + slitL x))

/-- The part `x ≤ ξ_*/2` of the lobe at every weight: exponentially small. -/
lemma lobe_small_abs (prob : FixedWeightProblem) {c K S₁ : ℝ} {B : ℂ → ℂ} (hc : 0 < c)
    (hcS : 12 * prob.totalShift ≤ c) (hK0 : 0 ≤ K) (hsm : lambdaComb c * S₁ ≤ xiStar / 2)
    (hpt : LobePt c K S₁ B) :
    (∫ t in Ioc 0 (c * (xiStar / 2) ^ 2 / 3), |combProfile c B t| * prob.cardyV (c / 12) t) ≤
      (c * (xiStar / 2) ^ 2 / 3) *
        (K * (xiStar / 2) ^ (-(5 / 2 : ℝ)) * xiStar ^ (prob.w - 1) * Real.exp (-(c * lobeGamma))) := by
  have hξ := xiStar_pos
  have ht1 : 0 ≤ c * (xiStar / 2) ^ 2 / 3 := by positivity
  have hbound : ∀ t ∈ Ioc 0 (c * (xiStar / 2) ^ 2 / 3),
      ‖|combProfile c B t| * prob.cardyV (c / 12) t‖ ≤
        K * (xiStar / 2) ^ (-(5 / 2 : ℝ)) * xiStar ^ (prob.w - 1) * Real.exp (-(c * lobeGamma)) := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1.le
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = xOf c t := ⟨_, rfl⟩
    have hx0 : 0 ≤ x := by rw [hx]; exact xOf_nonneg c t
    have hxt : c * x ^ 2 / 3 = t := by
      rw [hx, sq_xOf hc ht0]; field_simp
    have hxle : x ≤ xiStar / 2 := by
      have : x ^ 2 ≤ (xiStar / 2) ^ 2 := by
        have h1 : c * x ^ 2 / 3 ≤ c * (xiStar / 2) ^ 2 / 3 := by rw [hxt]; exact ht.2
        have h2 : c * x ^ 2 ≤ c * (xiStar / 2) ^ 2 := by linarith
        exact le_of_mul_le_mul_left h2 hc
      exact abs_le_of_sq_le_sq' this (by positivity) |>.2
    have hxξ : x < xiStar := by linarith
    have hd2 : xiStar / 2 ≤ xiStar - x := by linarith
    have hB := hpt x hx0 hxξ (by linarith)
    have hV := cardyV_le_pow_exp prob hc (by linarith) hx0
    have hV0 : 0 ≤ prob.cardyV (c / 12) (c * x ^ 2 / 3) := prob.cardyV_nonneg (by linarith) (by positivity)
    rw [← hxt, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hV0)]
    have hcp := abs_combProfile_le_sech B hc hx0
    have hsech : 1 / Real.cosh (π * x / 2) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      have := Real.one_le_cosh (π * x / 2)
      nlinarith
    have hcp' : |combProfile c B (c * x ^ 2 / 3)| ≤ ‖B (x : ℂ)‖ :=
      hcp.trans (by
        have := norm_nonneg (B (x : ℂ))
        nlinarith)
    have hmaj := majorant_add_L_le_neg hx0 hxle
    have hpow : (xiStar - x) ^ (-(5 / 2 : ℝ)) ≤ (xiStar / 2) ^ (-(5 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hd2 (by norm_num)
    have hex : Real.exp (c * (majorantReal x + slitL x)) ≤ Real.exp (-(c * lobeGamma)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hE0 := (Real.exp_pos (c * Bessel.besselL x)).le
    have h2x : (2 * x) ^ (prob.w - 1) ≤ xiStar ^ (prob.w - 1) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have hnb : 0 ≤ ‖B (x : ℂ)‖ * Real.exp (c * Bessel.besselL x) := by positivity
    calc |combProfile c B (c * x ^ 2 / 3)| * prob.cardyV (c / 12) (c * x ^ 2 / 3)
        ≤ ‖B (x : ℂ)‖ * ((2 * x) ^ (prob.w - 1) * Real.exp (c * Bessel.besselL x)) :=
          mul_le_mul hcp' hV hV0 (norm_nonneg _)
      _ = (2 * x) ^ (prob.w - 1) * (‖B (x : ℂ)‖ * Real.exp (c * Bessel.besselL x)) := by ring
      _ ≤ xiStar ^ (prob.w - 1) *
          (K * (xiStar - x) ^ (-(5 / 2 : ℝ)) * Real.exp (c * (majorantReal x + slitL x))) :=
          mul_le_mul h2x hB hnb (by positivity)
      _ ≤ xiStar ^ (prob.w - 1) *
          (K * (xiStar / 2) ^ (-(5 / 2 : ℝ)) * Real.exp (-(c * lobeGamma))) := by gcongr
      _ = K * (xiStar / 2) ^ (-(5 / 2 : ℝ)) * xiStar ^ (prob.w - 1) * Real.exp (-(c * lobeGamma)) := by ring
  have hfin : volume (Ioc (0 : ℝ) (c * (xiStar / 2) ^ 2 / 3)) < ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have := norm_setIntegral_le_of_norm_le_const hfin hbound
  have hvol : volume.real (Ioc (0 : ℝ) (c * (xiStar / 2) ^ 2 / 3)) = c * (xiStar / 2) ^ 2 / 3 := by
    rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hvol] at this
  calc _ ≤ ‖∫ t in Ioc 0 (c * (xiStar / 2) ^ 2 / 3), |combProfile c B t| * prob.cardyV (c / 12) t‖ :=
        le_abs_self _
    _ ≤ _ := this
    _ = _ := by ring

/-- The part of the lobe near the tip, `ξ_*/2 ≤ x ≤ ξ_* - Sλ`, at every weight (`eq:ut:T2-left-tail`):
`≤ F_{2,c} C S^{-3/2}`, for a comb with the pointwise lobe bound and the far Cardy bound
`V e^{-cL} (2/3) c x ≤ C_F √c √x` on `x ≥ ξ_*/2`. -/
lemma lobe_near_abs (prob : FixedWeightProblem) {c K S₁ S CF : ℝ} {B : ℂ → ℂ} (hc : 0 < c)
    (hcS : 12 * prob.totalShift ≤ c) (hS₁0 : 0 ≤ S₁) (hS : S₁ + 1 ≤ S) (hK0 : 0 ≤ K) (hCF : 0 ≤ CF)
    (hsm : lambdaComb c * S ≤ xiStar / 2) (hpt : LobePt c K S₁ B)
    (hFb : ∀ x : ℝ, xiStar / 2 ≤ x → x ≤ xiStar → 0 ≤ prob.cardyV (c / 12) (c * x ^ 2 / 3) ∧
      prob.cardyV (c / 12) (c * x ^ 2 / 3) * Real.exp (-(c * Bessel.besselL x)) * (2 / 3 * c * x) ≤
        CF * √c * √x) :
    (∫ t in Icc (c * (xiStar / 2) ^ 2 / 3) (c * (xiStar + lambdaComb c * (-S)) ^ 2 / 3),
        |combProfile c B t| * prob.cardyV (c / 12) t) ≤
      twoZeroF prob c * (K * CF * √xiStar * (2 / 3) * kTip / twoZeroFConst prob * S ^ (-(3 / 2 : ℝ))) := by
  have hξ := xiStar_pos
  have hS1 : 0 < S := by linarith
  have hlam := lambdaComb_pos' hc
  have hlS : 0 < lambdaComb c * S := mul_pos hlam hS1
  have hab : xiStar / 2 ≤ xiStar + lambdaComb c * (-S) := by nlinarith
  have hbξ : xiStar + lambdaComb c * (-S) < xiStar := by nlinarith
  rw [integral_Icc_comp_sq hc (half_pos hξ) hab (fun t => |combProfile c B t| *
    prob.cardyV (c / 12) t)]
  set Kd : ℝ := K * CF * √c * √xiStar with hKd
  have hKd0 : 0 ≤ Kd := by positivity
  have hcont : ContinuousOn (fun x : ℝ => Kd * (xiStar - x) ^ (-(5 / 2 : ℝ)))
      (Icc (xiStar / 2) (xiStar + lambdaComb c * (-S))) := by
    refine continuousOn_const.mul ?_
    refine ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id) fun x hx => ?_
    left
    have : 0 < xiStar - x := by linarith [hx.2]
    exact this.ne'
  have hpt2 : ∀ x ∈ Icc (xiStar / 2) (xiStar + lambdaComb c * (-S)),
      (2 * c * x / 3) * (|combProfile c B (c * x ^ 2 / 3)| *
        prob.cardyV (c / 12) (c * x ^ 2 / 3)) ≤ Kd * (xiStar - x) ^ (-(5 / 2 : ℝ)) := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hxξ : x < xiStar := by linarith [hx.2]
    obtain ⟨hv0, hw'⟩ := hFb x hx.1 hxξ.le
    refine twoZero_lobe_near_pt (K := K) (CF := CF) hc hx0 hxξ hK0 ?_ hw' hv0 hCF hKd
    exact hpt x hx0.le hxξ (by nlinarith [hx.2, mul_le_mul_of_nonneg_left (show S₁ ≤ S by linarith) hlam.le])
  calc ∫ x in Icc (xiStar / 2) (xiStar + lambdaComb c * (-S)), (2 * c * x / 3) *
        (|combProfile c B (c * x ^ 2 / 3)| * prob.cardyV (c / 12) (c * x ^ 2 / 3))
      ≤ ∫ x in Icc (xiStar / 2) (xiStar + lambdaComb c * (-S)), Kd * (xiStar - x) ^ (-(5 / 2 : ℝ)) := by
        refine integral_mono_of_nonneg ?_ hcont.integrableOn_Icc ?_
        · refine (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun x hx => ?_)
          have hx0 : 0 < x := by linarith [hx.1]
          have hv0 : 0 ≤ prob.cardyV (c / 12) (c * x ^ 2 / 3) :=
            prob.cardyV_nonneg (by linarith) (by positivity)
          positivity
        · exact (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall hpt2)
    _ = Kd * ∫ x in Icc (xiStar / 2) (xiStar + lambdaComb c * (-S)), (xiStar - x) ^ (-(5 / 2 : ℝ)) :=
        integral_const_mul _ _
    _ ≤ Kd * ((xiStar - (xiStar + lambdaComb c * (-S))) ^ (1 - 5 / 2 : ℝ) / (5 / 2 - 1)) :=
        mul_le_mul_of_nonneg_left (integral_Icc_rpow_neg_le_left (by norm_num) hbξ hab) hKd0
    _ = twoZeroF prob c * (K * CF * √xiStar * (2 / 3) * kTip / twoZeroFConst prob * S ^ (-(3 / 2 : ℝ))) := by
        have hFc := twoZeroFConst_pos prob
        have e1 : xiStar - (xiStar + lambdaComb c * (-S)) = lambdaComb c * S := by ring
        have e2 : (lambdaComb c * S) ^ (1 - 5 / 2 : ℝ) = lambdaComb c ^ (-(3 / 2 : ℝ)) * S ^ (-(3 / 2 : ℝ)) := by
          rw [Real.mul_rpow hlam.le hS1.le]; norm_num
        have e3 : lambdaComb c ^ (-(3 / 2 : ℝ)) = kTip * c := by
          rw [Real.rpow_neg hlam.le, lambdaComb_rpow_three_halves hc, inv_inv]
        have e4 : c ^ (3 / 2 : ℝ) = c * √c := by
          rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hc, Real.rpow_one, ← Real.sqrt_eq_rpow]
        rw [e1, e2, e3, twoZeroF_eq_const_mul prob hc, e4, hKd]
        field_simp
        ring

/-! ### 4. The deep lobe of the bumped comb -/

/-- **The deep lobe of the bumped comb, every weight** (`eq:ut:T2-left-tail`): there are `C_L, S₀` such that for every
`S ≥ S₀` and `ε > 0`, for `c` large, all `d ∈ 𝒦` and every cut `N' ≥ n + 2`,
`∫_{0 < t ≤ t_S} |h₂^{(p)}| V dt ≤ F_{2,c} (C_L S^{-3/2} + ε)`, `t_S = c (ξ_* - λ S)²/3`. -/
theorem twoZeroBump_lobe_bound (prob : FixedWeightProblem) (bd : BumpData) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ C_L S₀ : ℝ, 0 ≤ C_L ∧ 0 < S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ ε : ℝ, 0 < ε → ∀ᶠ c in atTop, ∀ d ∈ 𝒦,
      ∀ N' : ℕ, n + 2 ≤ N' →
      (∫ t in Ioc 0 (c * (xiStar + lambdaComb c * (-S)) ^ 2 / 3),
          |combProfile c (d.bumpComb bd c N') t| * prob.cardyV (c / 12) t) ≤
        twoZeroF prob c * (C_L * S ^ (-(3 / 2 : ℝ)) + ε) := by
  obtain ⟨K, S₁, hK0, hS₁0, hpt⟩ := twoZero_lobe_pointwise hK hA
  obtain ⟨Cp, C', hbump⟩ := bumpComb_ofReal (n := n) bd
  have hξ := xiStar_pos
  obtain ⟨CF, cF, hCF, hFb⟩ := cardyFarBoundP_prob prob (x₀ := xiStar / 2) (half_pos hξ)
  have hFc := twoZeroFConst_pos prob
  obtain ⟨C'', hC''⟩ : ∃ C'' : ℝ, C'' = max C' 0 := ⟨_, rfl⟩
  have hC''0 : 0 ≤ C'' := by rw [hC'']; exact le_max_right _ _
  obtain ⟨CF', hCF'⟩ : ∃ CF' : ℝ, CF' = CF * (1 + xiStar) ^ (prob.w - 1) := ⟨_, rfl⟩
  have hCF'0 : 0 ≤ CF' := by rw [hCF']; positivity
  obtain ⟨Kb, hKb⟩ : ∃ Kb : ℝ, Kb = 2 * K := ⟨_, rfl⟩
  have hKb0 : 0 ≤ Kb := by rw [hKb]; positivity
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = Kb * (xiStar / 2) ^ (-(5 / 2 : ℝ)) * xiStar ^ (prob.w - 1) := ⟨_, rfl⟩
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  refine ⟨Kb * CF' * √xiStar * (2 / 3) * kTip / twoZeroFConst prob, S₁ + 1, ?_, by linarith, ?_⟩
  · have := kTip_pos
    positivity
  intro S hS ε hε
  have hS1 : 0 < S := by linarith
  have hexp : Tendsto (fun c : ℝ => Real.exp (-(c * lobeGamma))) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_mul_const lobeGamma_pos)
    simpa [Function.comp_def] using this
  have hev : ∀ᶠ c in atTop, (xiStar / 2) ^ 2 / 3 * (K₁ * Real.exp (-(c * lobeGamma))) ≤
      ε * twoZeroFConst prob := by
    have h := (hexp.const_mul (K₁ * ((xiStar / 2) ^ 2 / 3)))
    rw [mul_zero] at h
    filter_upwards [h.eventually_le_const (by positivity : (0 : ℝ) < ε * twoZeroFConst prob)] with c hc
    linarith [show (xiStar / 2) ^ 2 / 3 * (K₁ * Real.exp (-(c * lobeGamma))) =
      K₁ * ((xiStar / 2) ^ 2 / 3) * Real.exp (-(c * lobeGamma)) by ring]
  filter_upwards [hpt, hbump, hev, lambda_mul_le S (half_pos hξ), twoZeroBump_innerCombHyp bd hK hA,
    eventually_gt_atTop (1 : ℝ), eventually_ge_atTop (12 * prob.totalShift), eventually_ge_atTop cF,
    eventually_ge_atTop C''] with c hpt hbm hev hsm hI hc1 hcS hcF hcC d hd N' hN'
  have hc : 0 < c := by linarith
  have hlam := lambdaComb_pos' hc
  have hlpt : LobePt c Kb S₁ (d.bumpComb bd c N') := by
    intro x hx0 hxξ hdx
    obtain ⟨R, hR1, -, hRn, hRe⟩ := hbm d N' hN' x hx0
    have hR2 : R ≤ 2 := by
      have h1 := hRn (by linarith [bd.r_pos])
      have h2 : C' / c ≤ C'' / c :=
        div_le_div_of_nonneg_right (by rw [hC'']; exact le_max_left _ _) hc.le
      have h3 : C'' / c ≤ 1 := by rw [div_le_one hc]; exact hcC
      linarith
    rw [norm_bumpComb_le hRe hR1, hKb]
    have h4 := hpt d hd x hx0 hxξ hdx
    have hkp : 0 ≤ K * (xiStar - x) ^ (-(5 / 2 : ℝ)) * Real.exp (c * (majorantReal x + slitL x)) := by
      have : 0 < xiStar - x := by linarith
      positivity
    calc R * ‖d.twoZeroComb c (x : ℂ)‖ * Real.exp (c * Bessel.besselL x)
        = R * (‖d.twoZeroComb c (x : ℂ)‖ * Real.exp (c * Bessel.besselL x)) := by ring
      _ ≤ R * (K * (xiStar - x) ^ (-(5 / 2 : ℝ)) * Real.exp (c * (majorantReal x + slitL x))) :=
          mul_le_mul_of_nonneg_left h4 (by linarith)
      _ ≤ 2 * (K * (xiStar - x) ^ (-(5 / 2 : ℝ)) * Real.exp (c * (majorantReal x + slitL x))) :=
          mul_le_mul_of_nonneg_right hR2 hkp
      _ = 2 * K * (xiStar - x) ^ (-(5 / 2 : ℝ)) * Real.exp (c * (majorantReal x + slitL x)) := by ring
  have hsmS₁ : lambdaComb c * S₁ ≤ xiStar / 2 :=
    (mul_le_mul_of_nonneg_left (by linarith : S₁ ≤ S) hlam.le).trans hsm
  have hsmall := lobe_small_abs prob hc hcS hKb0 hsmS₁ hlpt
  have hnear := lobe_near_abs prob (S₁ := S₁) (S := S) (CF := CF') hc hcS hS₁0 hS hKb0 hCF'0 hsm hlpt
    (fun x hx hxξ => by
      obtain ⟨hv0, hv⟩ := hFb c hcF x hx
      refine ⟨hv0, hv.trans ?_⟩
      have hp : (1 + x) ^ (prob.w - 1) ≤ (1 + xiStar) ^ (prob.w - 1) :=
        pow_le_pow_left₀ (by linarith [(half_pos hξ).trans_le hx]) (by linarith) _
      calc CF * √c * √x * (1 + x) ^ (prob.w - 1) ≤ CF * √c * √x * (1 + xiStar) ^ (prob.w - 1) :=
            mul_le_mul_of_nonneg_left hp (by positivity)
        _ = CF' * √c * √x := by rw [hCF']; ring)
  have hc' := hI d hd N' hN'
  have hKe : Kb * (xiStar / 2) ^ (-(5 / 2 : ℝ)) * xiStar ^ (prob.w - 1) = K₁ := hK₁.symm
  rw [hKe] at hsmall
  have ht1 : c * (xiStar / 2) ^ 2 / 3 ≤ c * (xiStar + lambdaComb c * (-S)) ^ 2 / 3 := by
    have h1 : xiStar / 2 ≤ xiStar + lambdaComb c * (-S) := by nlinarith
    have : (xiStar / 2) ^ 2 ≤ (xiStar + lambdaComb c * (-S)) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have := mul_le_mul_of_nonneg_left this hc.le
    linarith
  have hcont : ContinuousOn (fun t => |combProfile c (d.bumpComb bd c N') t| * prob.cardyV (c / 12) t)
      (Ici 0) :=
    (hc'.continuousOn_combProfile hc).abs.mul (Crossing.continuous_cardyV prob (c / 12)).continuousOn
  have hint : IntegrableOn (fun t => |combProfile c (d.bumpComb bd c N') t| * prob.cardyV (c / 12) t)
      (Ioc 0 (c * (xiStar + lambdaComb c * (-S)) ^ 2 / 3)) := by
    refine (ContinuousOn.integrableOn_Icc (hcont.mono (fun t ht => ?_))).mono_set Ioc_subset_Icc_self
    exact ((show (0 : ℝ) ≤ t from ht.1))
  have hsplit : (∫ t in Ioc 0 (c * (xiStar + lambdaComb c * (-S)) ^ 2 / 3),
      |combProfile c (d.bumpComb bd c N') t| * prob.cardyV (c / 12) t) =
      (∫ t in Ioc 0 (c * (xiStar / 2) ^ 2 / 3),
        |combProfile c (d.bumpComb bd c N') t| * prob.cardyV (c / 12) t) +
      ∫ t in Ioc (c * (xiStar / 2) ^ 2 / 3) (c * (xiStar + lambdaComb c * (-S)) ^ 2 / 3),
        |combProfile c (d.bumpComb bd c N') t| * prob.cardyV (c / 12) t := by
    rw [← setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hint.mono_set (Ioc_subset_Ioc_right ht1)) (hint.mono_set (Ioc_subset_Ioc_left (by positivity))),
      Ioc_union_Ioc_eq_Ioc (by positivity) ht1]
  have hnear' : (∫ t in Ioc (c * (xiStar / 2) ^ 2 / 3) (c * (xiStar + lambdaComb c * (-S)) ^ 2 / 3),
      |combProfile c (d.bumpComb bd c N') t| * prob.cardyV (c / 12) t) ≤
      ∫ t in Icc (c * (xiStar / 2) ^ 2 / 3) (c * (xiStar + lambdaComb c * (-S)) ^ 2 / 3),
        |combProfile c (d.bumpComb bd c N') t| * prob.cardyV (c / 12) t := by
    refine setIntegral_mono_set ?_ ?_ Ioc_subset_Icc_self.eventuallySubset
    · exact (ContinuousOn.integrableOn_Icc (hcont.mono (fun t ht => by
        have : (0 : ℝ) ≤ c * (xiStar / 2) ^ 2 / 3 := by positivity
        exact (show (0 : ℝ) ≤ t from this.trans ht.1))))
    · refine (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun t ht => ?_)
      have h0 : (0 : ℝ) ≤ c * (xiStar / 2) ^ 2 / 3 := by positivity
      exact mul_nonneg (abs_nonneg _) (prob.cardyV_nonneg (by linarith) (h0.trans ht.1))
  rw [hsplit]
  have hc32 : c ≤ c ^ (3 / 2 : ℝ) := by
    have h1 : 1 ≤ √c := by
      rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hc1.le
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hc, Real.rpow_one, ← Real.sqrt_eq_rpow]
    nlinarith
  have hsmall' : (∫ t in Ioc 0 (c * (xiStar / 2) ^ 2 / 3),
      |combProfile c (d.bumpComb bd c N') t| * prob.cardyV (c / 12) t) ≤ ε * twoZeroF prob c := by
    refine hsmall.trans ?_
    rw [twoZeroF_eq_const_mul prob hc]
    have h1 := mul_le_mul_of_nonneg_left hev hc.le
    have h2 : ε * twoZeroFConst prob * c ≤ ε * (twoZeroFConst prob * c ^ (3 / 2 : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hc32 (mul_pos hε hFc).le
      linarith
    calc c * (xiStar / 2) ^ 2 / 3 * (K₁ * Real.exp (-(c * lobeGamma)))
        = c * ((xiStar / 2) ^ 2 / 3 * (K₁ * Real.exp (-(c * lobeGamma)))) := by ring
      _ ≤ c * (ε * twoZeroFConst prob) := h1
      _ ≤ _ := by linarith
  calc _ ≤ ε * twoZeroF prob c + twoZeroF prob c * (Kb * CF' * √xiStar * (2 / 3) * kTip /
          twoZeroFConst prob * S ^ (-(3 / 2 : ℝ))) :=
        add_le_add hsmall' (hnear'.trans hnear)
    _ = _ := by ring

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroBump_lobe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_lobe_bound

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.bumpComb_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumpComb_ofReal

end FormalResearch.ModularBootstrap.TwoLevel
