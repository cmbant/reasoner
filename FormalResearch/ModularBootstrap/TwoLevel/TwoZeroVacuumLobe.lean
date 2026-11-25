module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroVacuumRatio
public import FormalResearch.ModularBootstrap.Upper.Holes.BandLobe
public import FormalResearch.ModularBootstrap.SlitStrip.EntropyAndDeficit
public import FormalResearch.ModularBootstrap.WeightAxioms.KernelAndPositivity
public import FormalResearch.ModularBootstrap.Upper.Window.Tail

/-!
# The deep lobe of the two-zero comb: the absolute estimate (`upper_transfer.tex`, `ut:T2`, "Absolute far-left estimate")

At `f = 2` the deep lobe `x < ξ_* - Sλ` is **positive** (`T_{χ(p)} < 0` and `B₁ < 0` below both zeros), so it cannot be
dropped as in the `f = 1` vacuum proof (`design_lobe_nonpos`); it is bounded absolutely:

* `twoZero_lobe_pointwise` (`eq:ut:T2-left`): for `0 ≤ x < ξ_*` with `λ S₁ ≤ ξ_* - x` (`S₁ ≥ sup |σ_p|`),
  `|B₂(x)| e^{c' L(x)} ≤ K (ξ_* - x)^{-5/2} e^{c'(U+L)(x)}`; this is `K6`(b) at `f = 2` (`2n₁ = 7/2`,
  `lobe_upper_K6b_blaschke`), the ratio `|B₁/B_ref^{(2)}| ≤ C_𝒦` (`twoZero_comb_le_ref_lobe`) and
  `|T_{χ(p)}(x)| ≤ π(ξ_* - x)`;
* `majorant_add_L_le_zero`, `majorant_add_L_le_neg`: `U + L ≤ 0` on `[0, ξ_*]` and `U + L ≤ -γ₀` on `[0, ξ_*/2]`
  (`slitDeficit_ge`);
* `cardyV_le_exp`: `V(c x²/3) ≤ e^{c L(x)}` (`V ≤ K_a ≤ e^{4π√(at)}` at `w = 1`);
* `integral_Icc_rpow_neg_le_left`: `∫_a^b (ξ - x)^{-p} dx ≤ (ξ - b)^{1-p}/(p - 1)`.

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
  FormalResearch.ModularBootstrap.Upper.Window.Tail
open TwoZeroDesign

/-! ### The majorant deficit on the lobe -/

/-- `U + L ≤ 0` on `[0, ξ_*]` (the harmonic majorant lies below `-L`). -/
lemma majorant_add_L_le_zero {x : ℝ} (hx0 : 0 ≤ x) (hxξ : x ≤ xiStar) :
    majorantReal x + slitL x ≤ 0 := by
  have habs : |x| = x := abs_of_nonneg hx0
  have h := majorant_add_L_eq_neg_slitDeficit (x := x) (by rw [habs]; exact hxξ)
  rw [habs] at h
  rw [h]
  have := slitDeficit_ge (δ := xiStar - x) (by linarith) (by linarith [xiStar_pos])
  have h2 : 0 ≤ (2.228 : ℝ) * (xiStar - x) ^ ((3 : ℝ) / 2) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)
  linarith

/-- The deficit constant `γ₀ = 2.228 (ξ_*/2)^{3/2} > 0`. -/
noncomputable def lobeGamma : ℝ := (2.228 : ℝ) * (xiStar / 2) ^ ((3 : ℝ) / 2)

lemma lobeGamma_pos : 0 < lobeGamma := by
  have := xiStar_pos
  unfold lobeGamma
  positivity

/-- `U + L ≤ -γ₀` on `[0, ξ_*/2]`. -/
lemma majorant_add_L_le_neg {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ xiStar / 2) :
    majorantReal x + slitL x ≤ -lobeGamma := by
  have hξ := xiStar_pos
  have habs : |x| = x := abs_of_nonneg hx0
  have h := majorant_add_L_eq_neg_slitDeficit (x := x) (by rw [habs]; linarith)
  rw [habs] at h
  rw [h]
  have h1 := slitDeficit_ge (δ := xiStar - x) (by linarith) (by linarith)
  have h2 : (xiStar / 2) ^ ((3 : ℝ) / 2) ≤ (xiStar - x) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  unfold lobeGamma
  nlinarith

/-! ### The Cardy weight on the lobe -/

/-- `V(c x²/3) ≤ e^{c L(x)}` for `w = 1`, `c ≥ 12 S`, `x ≥ 0` (`V ≤ K_a ≤ e^{4π√(a t)}`, `a = c/12`, `t = c x²/3`). -/
lemma cardyV_le_exp (prob : FixedWeightProblem) (hw : prob.w = 1) {c x : ℝ} (hc : 0 < c)
    (hcS : prob.totalShift ≤ c / 12) (hx : 0 ≤ x) :
    prob.cardyV (c / 12) (c * x ^ 2 / 3) ≤ Real.exp (c * Bessel.besselL x) := by
  have ht : 0 ≤ c * x ^ 2 / 3 := by positivity
  have h1 := cardyV_le_kernelK prob hcS ht
  have h2 := kernelK_le_pow_mul_exp (w := prob.w) prob.hw (a := c / 12) (t := c * x ^ 2 / 3) (by positivity) ht
  rw [hw] at h1 h2
  simp only [Nat.sub_self, pow_zero, one_mul] at h2
  refine h1.trans (h2.trans (le_of_eq ?_))
  congr 1
  have e : c / 12 * (c * x ^ 2 / 3) = (c * x / 6) ^ 2 := by ring
  rw [e, Real.sqrt_sq (by positivity)]
  unfold Bessel.besselL
  ring

/-! ### A power integral to the left of the tip -/

/-- `∫_a^b (ξ - x)^{-p} dx ≤ (ξ - b)^{1-p}/(p - 1)` for `p > 1` and `a ≤ b < ξ`. -/
lemma integral_Icc_rpow_neg_le_left {ξ a b p : ℝ} (hp : 1 < p) (hbξ : b < ξ) (hab : a ≤ b) :
    ∫ x in Icc a b, (ξ - x) ^ (-p) ≤ (ξ - b) ^ (1 - p) / (p - 1) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_sub_left (fun y : ℝ => y ^ (-p)) ξ,
    integral_rpow (Or.inr ⟨by linarith, by
      rw [Set.mem_uIcc]; push Not; constructor <;> intro h <;> linarith⟩)]
  have ha : 0 < ξ - a := by linarith
  have h1 : 0 ≤ (ξ - a) ^ (-p + 1) := (Real.rpow_pos_of_pos ha _).le
  have hp1 : 0 < p - 1 := by linarith
  rw [show -p + 1 = 1 - p by ring] at h1 ⊢
  generalize (ξ - a) ^ (1 - p) = X at h1 ⊢
  generalize (ξ - b) ^ (1 - p) = Y at h1 ⊢
  rw [show (1 - p) = -(p - 1) by ring, div_neg, ← neg_div, neg_sub]
  exact div_le_div_of_nonneg_right (by linarith) hp1.le

/-! ### The pointwise bound on the lobe -/

/-- **`eq:ut:T2-left`**: for `0 ≤ x < ξ_*` with `λ S₁ ≤ ξ_* - x`,
`|B₂(x)| e^{c' L(x)} ≤ K (ξ_* - x)^{-5/2} e^{c'(U+L)(x)}`, uniformly on a compact family. -/
theorem twoZero_lobe_pointwise {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ K S₁ : ℝ, 0 ≤ K ∧ 0 ≤ S₁ ∧ ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ, 0 ≤ x → x < xiStar →
      lambdaComb c * S₁ ≤ xiStar - x →
      ‖d.twoZeroComb c (x : ℂ)‖ * Real.exp (c * Bessel.besselL x) ≤
        K * (xiStar - x) ^ (-(5 / 2 : ℝ)) * Real.exp (c * (majorantReal x + slitL x)) := by
  obtain ⟨C6, hC6, h6⟩ := lobe_upper_K6b_blaschke
  obtain ⟨Cr, hCr0, hr⟩ := twoZero_comb_le_ref_lobe hK hA
  obtain ⟨S₁, hS₁0, hS₁⟩ := hK.exists_sigmaP_bound
  have hπ := Real.pi_pos
  have hcl := lobeCLin_pos
  refine ⟨π * Cr * C6 * lobeCLin ^ (-(7 / 2 : ℝ)), S₁, by positivity, hS₁0, ?_⟩
  filter_upwards [h6, hr, eventually_gt_atTop (0 : ℝ)] with c h6 hr hc d hd x hx0 hxξ hdx
  have hlam := lambdaComb_pos' hc
  have hd0 : 0 < xiStar - x := by linarith
  -- the factor T
  have hTb : |tFac (d.chiP c) x| ≤ π * (xiStar - x) := by
    refine (abs_tFac_le _ _).trans ?_
    have hσ := hS₁ d hd
    have h1 : x - d.chiP c = -(xiStar - x) - lambdaComb c * d.sigmaP := by unfold chiP; ring
    have h2 : |x - d.chiP c| ≤ 2 * (xiStar - x) := by
      rw [h1]
      refine (abs_sub _ _).trans ?_
      rw [abs_neg, abs_of_pos hd0, abs_mul, abs_of_pos hlam]
      have := mul_le_mul_of_nonneg_left hσ hlam.le
      nlinarith
    nlinarith
  have hB1 := hr d hd x hx0 hxξ.le
  have hK6 := h6 2 (1 / 4) x (by norm_num) (by norm_num) le_rfl ⟨hx0, hxξ⟩
  have hn1 : 2 * n1Comb 2 = 7 / 2 := by unfold n1Comb; norm_num
  rw [hn1] at hK6
  have hsl : slitL x = Bessel.besselL x := slitL_eq_besselL hx0
  have hlow := abs_tFac_ge (χ := xiStar) hx0 hxξ.le le_rfl (by linarith)
  have hTx : ‖blaschkeT (xiStar : ℂ) (x : ℂ)‖ = |tFac xiStar x| := by
    rw [tFac_eq, Complex.norm_real, Real.norm_eq_abs]
  have hTpos : 0 < lobeCLin * (xiStar - x) := mul_pos hcl hd0
  have hpow : ‖blaschkeT (xiStar : ℂ) (x : ℂ)‖ ^ (-(7 / 2 : ℝ)) ≤ (lobeCLin * (xiStar - x)) ^ (-(7 / 2 : ℝ)) := by
    rw [hTx]
    exact Real.rpow_le_rpow_of_nonpos hTpos hlow (by norm_num)
  have hexp : 0 < Real.exp (c * (majorantReal x + slitL x)) := Real.exp_pos _
  have hmain : ‖refComb c 2 (1 / 4) (x : ℂ)‖ * Real.exp (c * Bessel.besselL x) ≤
      C6 * (lobeCLin * (xiStar - x)) ^ (-(7 / 2 : ℝ)) * Real.exp (c * (majorantReal x + slitL x)) := by
    rw [← hsl]
    refine hK6.1.trans (hK6.2.trans ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC6.le) hexp.le
  rw [norm_twoZeroComb_ofReal]
  have hE0 := (Real.exp_pos (c * Bessel.besselL x)).le
  calc |tFac (d.chiP c) x| * ‖d.comb c (x : ℂ)‖ * Real.exp (c * Bessel.besselL x)
      ≤ (π * (xiStar - x)) * (Cr * ‖refComb c 2 (1 / 4) (x : ℂ)‖) * Real.exp (c * Bessel.besselL x) := by
        gcongr
    _ = (π * (xiStar - x)) * Cr * (‖refComb c 2 (1 / 4) (x : ℂ)‖ * Real.exp (c * Bessel.besselL x)) := by ring
    _ ≤ (π * (xiStar - x)) * Cr * (C6 * (lobeCLin * (xiStar - x)) ^ (-(7 / 2 : ℝ)) *
          Real.exp (c * (majorantReal x + slitL x))) := by gcongr
    _ = π * Cr * C6 * lobeCLin ^ (-(7 / 2 : ℝ)) * (xiStar - x) ^ (-(5 / 2 : ℝ)) *
          Real.exp (c * (majorantReal x + slitL x)) := by
        rw [Real.mul_rpow hcl.le hd0.le]
        have e : (xiStar - x) * (xiStar - x) ^ (-(7 / 2 : ℝ)) = (xiStar - x) ^ (-(5 / 2 : ℝ)) := by
          rw [show (-(5 / 2 : ℝ)) = 1 + (-(7 / 2 : ℝ)) by norm_num, Real.rpow_add hd0, Real.rpow_one]
        calc _ = π * Cr * C6 * lobeCLin ^ (-(7 / 2 : ℝ)) * ((xiStar - x) * (xiStar - x) ^ (-(7 / 2 : ℝ))) *
            Real.exp (c * (majorantReal x + slitL x)) := by ring
          _ = _ := by rw [e]

/-! ### The lobe integral -/

/-- The part `x ≤ ξ_*/2` of the lobe (`t ≤ c ξ_*²/12`): exponentially small. -/
theorem twoZero_lobe_small (prob : FixedWeightProblem) (hw : prob.w = 1) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ᶠ c in atTop, ∀ d ∈ 𝒦,
      (∫ t in Ioc 0 (c * (xiStar / 2) ^ 2 / 3),
          |combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t) ≤
        (c * (xiStar / 2) ^ 2 / 3) * (K₁ * Real.exp (-(c * lobeGamma))) := by
  obtain ⟨K, S₁, hK0, hS₁0, hpt⟩ := twoZero_lobe_pointwise hK hA
  have hξ := xiStar_pos
  refine ⟨K * (xiStar / 2) ^ (-(5 / 2 : ℝ)), by positivity, ?_⟩
  have hsm : ∀ᶠ c in atTop, lambdaComb c * S₁ ≤ xiStar / 2 := by
    have h := tendsto_lambdaComb_atTop.mul_const S₁
    rw [zero_mul] at h
    exact h.eventually_le_const (by positivity)
  filter_upwards [hpt, hsm, eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (12 * prob.totalShift)]
    with c hpt hsm hc hcS d hd
  have ht1 : 0 ≤ c * (xiStar / 2) ^ 2 / 3 := by positivity
  have hbound : ∀ t ∈ Ioc 0 (c * (xiStar / 2) ^ 2 / 3),
      ‖|combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t‖ ≤
        K * (xiStar / 2) ^ (-(5 / 2 : ℝ)) * Real.exp (-(c * lobeGamma)) := by
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
    have hB := hpt d hd x hx0 hxξ (by linarith)
    have hV := cardyV_le_exp prob hw hc (by linarith) hx0
    have hV0 : 0 ≤ prob.cardyV (c / 12) (c * x ^ 2 / 3) := prob.cardyV_nonneg (by linarith) (by positivity)
    rw [← hxt, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hV0)]
    have hcp := abs_combProfile_le_sech (d.twoZeroComb c) hc hx0
    have hsech : 1 / Real.cosh (π * x / 2) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      have := Real.one_le_cosh (π * x / 2)
      nlinarith
    have hcp' : |combProfile c (d.twoZeroComb c) (c * x ^ 2 / 3)| ≤ ‖d.twoZeroComb c (x : ℂ)‖ :=
      hcp.trans (by
        have := norm_nonneg (d.twoZeroComb c (x : ℂ))
        nlinarith)
    have hmaj := majorant_add_L_le_neg hx0 hxle
    have hpow : (xiStar - x) ^ (-(5 / 2 : ℝ)) ≤ (xiStar / 2) ^ (-(5 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hd2 (by norm_num)
    have hex : Real.exp (c * (majorantReal x + slitL x)) ≤ Real.exp (-(c * lobeGamma)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hE0 := (Real.exp_pos (c * Bessel.besselL x)).le
    calc |combProfile c (d.twoZeroComb c) (c * x ^ 2 / 3)| * prob.cardyV (c / 12) (c * x ^ 2 / 3)
        ≤ ‖d.twoZeroComb c (x : ℂ)‖ * Real.exp (c * Bessel.besselL x) :=
          mul_le_mul hcp' hV hV0 (norm_nonneg _)
      _ ≤ K * (xiStar - x) ^ (-(5 / 2 : ℝ)) * Real.exp (c * (majorantReal x + slitL x)) := hB
      _ ≤ K * (xiStar / 2) ^ (-(5 / 2 : ℝ)) * Real.exp (-(c * lobeGamma)) := by gcongr
  have hfin : volume (Ioc (0 : ℝ) (c * (xiStar / 2) ^ 2 / 3)) < ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have := norm_setIntegral_le_of_norm_le_const hfin hbound
  have hvol : volume.real (Ioc (0 : ℝ) (c * (xiStar / 2) ^ 2 / 3)) = c * (xiStar / 2) ^ 2 / 3 := by
    rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hvol] at this
  calc _ ≤ ‖∫ t in Ioc 0 (c * (xiStar / 2) ^ 2 / 3),
          |combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t‖ := le_abs_self _
    _ ≤ _ := this
    _ = _ := by ring

/-- The pointwise integrand bound of the lobe near the tip, `ξ_*/2 ≤ x ≤ ξ_* - Sλ`
(`(2/3) c x |h₂| V ≤ K C_F √c √ξ_* (ξ_* - x)^{-5/2}`). -/
lemma twoZero_lobe_near_pt {prob : FixedWeightProblem} {c x K CF Kd : ℝ} {B : ℂ → ℂ}
    (hc : 0 < c) (hx0 : 0 < x) (hxξ : x < xiStar) (hK0 : 0 ≤ K)
    (hB : ‖B (x : ℂ)‖ * Real.exp (c * Bessel.besselL x) ≤
      K * (xiStar - x) ^ (-(5 / 2 : ℝ)) * Real.exp (c * (majorantReal x + slitL x)))
    (hFb : prob.cardyV (c / 12) (c * x ^ 2 / 3) * Real.exp (-(c * Bessel.besselL x)) * (2 / 3 * c * x) ≤
      CF * √c * √x) (hV0 : 0 ≤ prob.cardyV (c / 12) (c * x ^ 2 / 3)) (hCF : 0 ≤ CF)
    (hKd : Kd = K * CF * √c * √xiStar) :
    (2 * c * x / 3) * (|combProfile c B (c * x ^ 2 / 3)| * prob.cardyV (c / 12) (c * x ^ 2 / 3)) ≤
      Kd * (xiStar - x) ^ (-(5 / 2 : ℝ)) := by
  have hd0 : 0 < xiStar - x := by linarith
  have hcp := abs_combProfile_le_sech B hc hx0.le
  have hsech : 1 / Real.cosh (π * x / 2) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    have := Real.one_le_cosh (π * x / 2)
    nlinarith
  have hcp' : |combProfile c B (c * x ^ 2 / 3)| ≤ ‖B (x : ℂ)‖ :=
    hcp.trans (by have := norm_nonneg (B (x : ℂ)); nlinarith)
  have hexpL : Real.exp (c * Bessel.besselL x) * Real.exp (-(c * Bessel.besselL x)) = 1 := by
    rw [← Real.exp_add]; simp
  have hmaj : Real.exp (c * (majorantReal x + slitL x)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := majorant_add_L_le_zero hx0.le hxξ.le
    nlinarith
  have hB' : ‖B (x : ℂ)‖ * Real.exp (c * Bessel.besselL x) ≤ K * (xiStar - x) ^ (-(5 / 2 : ℝ)) := by
    refine hB.trans ?_
    have hp : 0 ≤ K * (xiStar - x) ^ (-(5 / 2 : ℝ)) := by positivity
    nlinarith
  have hsx : √x ≤ √xiStar := Real.sqrt_le_sqrt hxξ.le
  have hE0 : 0 ≤ Real.exp (-(c * Bessel.besselL x)) := (Real.exp_pos _).le
  calc (2 * c * x / 3) * (|combProfile c B (c * x ^ 2 / 3)| * prob.cardyV (c / 12) (c * x ^ 2 / 3))
      ≤ (2 * c * x / 3) * (‖B (x : ℂ)‖ * prob.cardyV (c / 12) (c * x ^ 2 / 3)) := by gcongr
    _ = (‖B (x : ℂ)‖ * Real.exp (c * Bessel.besselL x)) *
          (prob.cardyV (c / 12) (c * x ^ 2 / 3) * Real.exp (-(c * Bessel.besselL x)) * (2 / 3 * c * x)) := by
        linear_combination ((2 * c * x / 3) * (‖B (x : ℂ)‖ * prob.cardyV (c / 12) (c * x ^ 2 / 3))) *
          (-hexpL)
    _ ≤ (K * (xiStar - x) ^ (-(5 / 2 : ℝ))) * (CF * √c * √x) :=
        mul_le_mul hB' hFb (by positivity) (by positivity)
    _ ≤ (K * (xiStar - x) ^ (-(5 / 2 : ℝ))) * (CF * √c * √xiStar) := by gcongr
    _ = Kd * (xiStar - x) ^ (-(5 / 2 : ℝ)) := by rw [hKd]; ring

/-- The part of the lobe near the tip, `ξ_*/2 ≤ x ≤ ξ_* - Sλ` (`eq:ut:T2-left-tail`): `≤ F_{2,c} C_L S^{-3/2}`. -/
theorem twoZero_lobe_near (prob : FixedWeightProblem) (hw : prob.w = 1) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ C_L S₀ : ℝ, 0 ≤ C_L ∧ 0 < S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ᶠ c in atTop, ∀ d ∈ 𝒦,
      (∫ t in Icc (c * (xiStar / 2) ^ 2 / 3) (c * (xiStar + lambdaComb c * (-S)) ^ 2 / 3),
          |combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t) ≤
        twoZeroF prob c * (C_L * S ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨K, S₁, hK0, hS₁0, hpt⟩ := twoZero_lobe_pointwise hK hA
  have hξ := xiStar_pos
  obtain ⟨CF, cF, hCF, hFb⟩ := cardyFarBound_prob prob hw (x₀ := xiStar / 2) (half_pos hξ)
  refine ⟨K * CF * √xiStar * (2 / 3) * kTip / twoZeroFConst prob, S₁ + 1, ?_, by linarith, ?_⟩
  · have := twoZeroFConst_pos prob
    have := kTip_pos
    positivity
  intro S hS
  have hS1 : 0 < S := by linarith
  have hsm : ∀ᶠ c in atTop, lambdaComb c * S ≤ xiStar / 2 := by
    have h := tendsto_lambdaComb_atTop.mul_const S
    rw [zero_mul] at h
    exact h.eventually_le_const (by positivity)
  filter_upwards [hpt, hsm, eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (12 * prob.totalShift),
    eventually_ge_atTop cF] with c hpt hsm hc hcS hcF d hd
  have hlam := lambdaComb_pos' hc
  have hlS : 0 < lambdaComb c * S := mul_pos hlam hS1
  have hab : xiStar / 2 ≤ xiStar + lambdaComb c * (-S) := by nlinarith
  have hbξ : xiStar + lambdaComb c * (-S) < xiStar := by nlinarith
  rw [integral_Icc_comp_sq hc (half_pos hξ) hab (fun t => |combProfile c (d.twoZeroComb c) t| *
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
      (2 * c * x / 3) * (|combProfile c (d.twoZeroComb c) (c * x ^ 2 / 3)| *
        prob.cardyV (c / 12) (c * x ^ 2 / 3)) ≤ Kd * (xiStar - x) ^ (-(5 / 2 : ℝ)) := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hxξ : x < xiStar := by linarith [hx.2]
    obtain ⟨hv0, hw'⟩ := hFb c hcF x hx.1
    refine twoZero_lobe_near_pt (K := K) (CF := CF) hc hx0 hxξ hK0 ?_ hw' hv0 hCF.le hKd
    exact hpt d hd x hx0.le hxξ (by nlinarith [hx.2, mul_le_mul_of_nonneg_left (show S₁ ≤ S by linarith) hlam.le])
  calc ∫ x in Icc (xiStar / 2) (xiStar + lambdaComb c * (-S)), (2 * c * x / 3) *
        (|combProfile c (d.twoZeroComb c) (c * x ^ 2 / 3)| * prob.cardyV (c / 12) (c * x ^ 2 / 3))
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

/-- **The deep lobe** (`eq:ut:T2-left-tail`): there are `C_L, S₀` such that for every `S ≥ S₀` and `ε > 0`, for `c` large and
all `d ∈ 𝒦`, `∫_{0 < t ≤ t_S} |h₂| V dt ≤ F_{2,c} (C_L S^{-3/2} + ε)`, `t_S = c (ξ_* - λ S)²/3`.  This applies to the
positive lobe: nothing is dropped. -/
theorem twoZero_lobe_bound (prob : FixedWeightProblem) (hw : prob.w = 1) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ C_L S₀ : ℝ, 0 ≤ C_L ∧ 0 < S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ ε : ℝ, 0 < ε → ∀ᶠ c in atTop, ∀ d ∈ 𝒦,
      (∫ t in Ioc 0 (c * (xiStar + lambdaComb c * (-S)) ^ 2 / 3),
          |combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t) ≤
        twoZeroF prob c * (C_L * S ^ (-(3 / 2 : ℝ)) + ε) := by
  obtain ⟨K₁, hK₁, hsmall⟩ := twoZero_lobe_small prob hw hK hA
  obtain ⟨C_L, S₀, hCL, hS₀, hnear⟩ := twoZero_lobe_near prob hw hK hA
  refine ⟨C_L, S₀, hCL, hS₀, fun S hS ε hε => ?_⟩
  have hξ := xiStar_pos
  have hFc := twoZeroFConst_pos prob
  have hS1 : 0 < S := hS₀.trans_le hS
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
  have hsm : ∀ᶠ c in atTop, lambdaComb c * S ≤ xiStar / 2 := by
    have h := tendsto_lambdaComb_atTop.mul_const S
    rw [zero_mul] at h
    exact h.eventually_le_const (by positivity)
  filter_upwards [hsmall, hnear S hS, twoZeroComb_innerCombHyp hK hA, hev, hsm,
    eventually_gt_atTop (1 : ℝ), eventually_ge_atTop (12 * prob.totalShift)]
    with c hsm1 hnr hI hev hsm hc1 hcS d hd
  have hc : 0 < c := by linarith
  have hlam := lambdaComb_pos' hc
  have ht1 : c * (xiStar / 2) ^ 2 / 3 ≤ c * (xiStar + lambdaComb c * (-S)) ^ 2 / 3 := by
    have h1 : xiStar / 2 ≤ xiStar + lambdaComb c * (-S) := by nlinarith
    have : (xiStar / 2) ^ 2 ≤ (xiStar + lambdaComb c * (-S)) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have := mul_le_mul_of_nonneg_left this hc.le
    linarith
  have hcont : ContinuousOn (fun t => |combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t) (Ici 0) :=
    ((hI d hd).continuousOn_combProfile hc).abs.mul (Crossing.continuous_cardyV prob (c / 12)).continuousOn
  have hint : IntegrableOn (fun t => |combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t)
      (Ioc 0 (c * (xiStar + lambdaComb c * (-S)) ^ 2 / 3)) := by
    refine (ContinuousOn.integrableOn_Icc (hcont.mono (fun t ht => ?_))).mono_set Ioc_subset_Icc_self
    exact ((show (0 : ℝ) ≤ t from ht.1))
  have hnn : ∀ t ∈ Ioc 0 (c * (xiStar + lambdaComb c * (-S)) ^ 2 / 3),
      0 ≤ |combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t := fun t ht =>
    mul_nonneg (abs_nonneg _) (prob.cardyV_nonneg (by linarith) ht.1.le)
  have hsplit : (∫ t in Ioc 0 (c * (xiStar + lambdaComb c * (-S)) ^ 2 / 3),
      |combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t) =
      (∫ t in Ioc 0 (c * (xiStar / 2) ^ 2 / 3), |combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t) +
      ∫ t in Ioc (c * (xiStar / 2) ^ 2 / 3) (c * (xiStar + lambdaComb c * (-S)) ^ 2 / 3),
        |combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t := by
    rw [← setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hint.mono_set (Ioc_subset_Ioc_right ht1)) (hint.mono_set (Ioc_subset_Ioc_left (by positivity))),
      Ioc_union_Ioc_eq_Ioc (by positivity) ht1]
  have hnear' : (∫ t in Ioc (c * (xiStar / 2) ^ 2 / 3) (c * (xiStar + lambdaComb c * (-S)) ^ 2 / 3),
      |combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t) ≤
      ∫ t in Icc (c * (xiStar / 2) ^ 2 / 3) (c * (xiStar + lambdaComb c * (-S)) ^ 2 / 3),
        |combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t := by
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
      |combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t) ≤ ε * twoZeroF prob c := by
    refine (hsm1 d hd).trans ?_
    rw [twoZeroF_eq_const_mul prob hc]
    have h1 := mul_le_mul_of_nonneg_left hev hc.le
    have h2 : ε * twoZeroFConst prob * c ≤ ε * (twoZeroFConst prob * c ^ (3 / 2 : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hc32 (mul_pos hε hFc).le
      linarith
    calc c * (xiStar / 2) ^ 2 / 3 * (K₁ * Real.exp (-(c * lobeGamma)))
        = c * ((xiStar / 2) ^ 2 / 3 * (K₁ * Real.exp (-(c * lobeGamma)))) := by ring
      _ ≤ c * (ε * twoZeroFConst prob) := h1
      _ ≤ _ := by linarith
  calc _ ≤ ε * twoZeroF prob c + twoZeroF prob c * (C_L * S ^ (-(3 / 2 : ℝ))) :=
        add_le_add hsmall' (hnear' |>.trans (hnr d hd))
    _ = _ := by ring

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_lobe_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_lobe_pointwise

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_lobe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_lobe_bound

end FormalResearch.ModularBootstrap.TwoLevel
