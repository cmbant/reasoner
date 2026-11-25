module

public import FormalResearch.SignUncertainty.UctSeedZ
public import FormalResearch.SignUncertainty.UctOuterGrowth
public import FormalResearch.SignUncertainty.UctAiryTrans
public import FormalResearch.SignUncertainty.StripAdmiss
public import FormalResearch.CohnElkies.MellinLiftIntegrals

/-!
# The seed multiplier `W^seed` of `uct:Wseed-def` and its hypothesis (M1) (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, `(uct:Wseed-def)`, `(uct:Wseed-alt)`.

With `T(w) = F̃_{*,δ}(i w) = airyTwistedLaplaceC (uctFstarDelta δ) w`, `a = c_s c^{1/3}` (`seedScale c`) and the
regularised factor `Z_ε` of `UctSeedZ` (`seed_factor_eq`), the multiplier of `(uct:Wseed-def)` is

`W^seed(ζ) = T(a)⁻¹ · Z_ε(ζ) e^{-h(ζ)} T(aζ) T(a(1-ζ))` (`seedW`),

because `-c^{5/6}/(|C_Ai| φ_{c,δ}(1)) = 1/T(a)` and `ζ^{5/2}(1-ζ)^{5/2}H_*/G_ε = Z_ε e^{-h}`.  `h` is `outerHbar`, so `W^seed`
is defined on the closed strip without branch conventions.

* `hasU2_uctFstarDelta`: `F_{*,δ}` has `HasU2` (so `T` is holomorphic on `Re > 0`, continuous on `Re ≥ 0`, bounded there);
* `seedT_bound`, `seedT_conj`;
* `seedW_stripM1`: (M1) of `uct:admiss` for `W^seed` (holomorphic on `S`, continuous on `S̄`, real-symmetric, `O((1+|τ|)⁻²)`),
  from `uctSeedZ_bound` (`e^{-π|τ|}` decay of `H_*`), `norm_exp_neg_outerHbar_le` (`uct:outer-growth`) and the bound of `T`.

**Proved.**  Not yet formalised: (M2) Hölder at `ζ=0,1` and (M3) for `W^seed`.
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

/-- `T(w) = F̃_{*,δ}(i w)`. -/
noncomputable def seedT (δ : ℝ) (w : ℂ) : ℂ := airyTwistedLaplaceC (uctFstarDelta δ) w

/-- `a = c_s c^{1/3}`. -/
noncomputable def seedScale (c : ℝ) : ℝ := ceCs * c ^ (1 / 3 : ℝ)

/-- The seed multiplier `W̃_c^{seed,ε}` of `(uct:Wseed-def)`, in the form `T(a)⁻¹ Z_ε e^{-h} T(aζ) T(a(1-ζ))`. -/
noncomputable def seedW (ε δ c : ℝ) (ζ : ℂ) : ℂ :=
  (seedT δ (seedScale c : ℂ))⁻¹ *
    (uctSeedZ ε ζ * Complex.exp (-outerHbar ζ) * seedT δ ((seedScale c : ℂ) * ζ) *
      seedT δ ((seedScale c : ℂ) * (1 - ζ)))

lemma seedScale_pos {c : ℝ} (hc : 0 < c) : 0 < seedScale c := by
  unfold seedScale; have := ceCs_pos; positivity

theorem hasU2_uctFstarDelta (δ : ℝ) : HasU2 (uctFstarDelta δ) := by
  have h := HasU2.add (hasU2_ceF1.smul (-1)) (hasU2_ceG1.smul (-δ))
  convert h using 1
  funext u
  unfold uctFstarDelta
  ring

lemma seedT_continuousOn (δ : ℝ) : ContinuousOn (seedT δ) {y : ℂ | 0 ≤ y.re} :=
  (hasU2_uctFstarDelta δ).continuousOn

lemma seedT_differentiableOn (δ : ℝ) : DifferentiableOn ℂ (seedT δ) {y : ℂ | 0 < y.re} :=
  (hasU2_uctFstarDelta δ).differentiable

theorem seedT_bound (δ : ℝ) : ∃ B : ℝ, ∀ w : ℂ, 0 ≤ w.re → ‖seedT δ w‖ ≤ B := by
  obtain ⟨C, hC, h⟩ := (hasU2_uctFstarDelta δ).rhp
  refine ⟨C, fun w hw => ?_⟩
  have hcs := ceCs_pos
  have hw' : 0 ≤ (w / (ceCs : ℂ)).re := by
    rw [Complex.div_ofReal_re]; positivity
  have := h (w / ceCs) hw'
  have hcs' : (ceCs : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcs.ne'
  have e : (ceCs : ℂ) * (w / (ceCs : ℂ)) = w := mul_div_cancel₀ w hcs'
  rw [e] at this
  have h1 : 1 ≤ ‖1 + w / (ceCs : ℂ)‖ := by
    have := Complex.re_le_norm (1 + w / (ceCs : ℂ))
    simp only [Complex.add_re, Complex.one_re] at this
    linarith
  have h2 : ‖1 + w / (ceCs : ℂ)‖ ^ (-(5 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)
  unfold seedT
  nlinarith

lemma seedT_conj (δ : ℝ) (w : ℂ) : seedT δ (starRingEnd ℂ w) = starRingEnd ℂ (seedT δ w) :=
  airyTwistedLaplaceC_conj _ _

lemma poly_exp_le : ∃ M : ℝ, ∀ x : ℝ, 0 ≤ x → (1 + x) ^ 8 * Real.exp (-(π * x)) ≤ M := by
  refine ⟨256 * (1 + 40320 / π ^ 8), fun x hx => ?_⟩
  have hπ := Real.pi_pos
  have h1 : (π * x) ^ 8 / (Nat.factorial 8 : ℝ) ≤ Real.exp (π * x) := Real.pow_div_factorial_le_exp _ (by positivity) 8
  have hf : (Nat.factorial 8 : ℝ) = 40320 := by norm_num [Nat.factorial]
  rw [hf] at h1
  have hE : 0 < Real.exp (π * x) := Real.exp_pos _
  have h2 : x ^ 8 * Real.exp (-(π * x)) ≤ 40320 / π ^ 8 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hE (by positivity)]
    have : (π * x) ^ 8 ≤ 40320 * Real.exp (π * x) := by
      rw [div_le_iff₀ (by norm_num)] at h1; linarith
    calc x ^ 8 * π ^ 8 = (π * x) ^ 8 := by ring
      _ ≤ 40320 * Real.exp (π * x) := this
  have h3 : Real.exp (-(π * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h4 : (1 + x) ^ 8 ≤ 256 * (1 + x ^ 8) := by
    have hx8 : 0 ≤ x ^ 8 := by positivity
    rcases le_or_gt x 1 with h | h
    · have : (1 + x) ^ 8 ≤ 2 ^ 8 := pow_le_pow_left₀ (by linarith) (by linarith) 8
      nlinarith
    · have : (1 + x) ^ 8 ≤ (2 * x) ^ 8 := pow_le_pow_left₀ (by linarith) (by linarith) 8
      rw [mul_pow] at this
      nlinarith
  have h5 : 0 ≤ Real.exp (-(π * x)) := (Real.exp_pos _).le
  calc (1 + x) ^ 8 * Real.exp (-(π * x)) ≤ 256 * (1 + x ^ 8) * Real.exp (-(π * x)) :=
        mul_le_mul_of_nonneg_right h4 h5
    _ = 256 * (Real.exp (-(π * x)) + x ^ 8 * Real.exp (-(π * x))) := by ring
    _ ≤ 256 * (1 + 40320 / π ^ 8) := by gcongr


lemma rpow_neg_two_eq {x : ℝ} (hx : 0 ≤ x) : x ^ (-(2 : ℝ)) = 1 / x ^ 2 := by
  rw [Real.rpow_neg hx, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]

lemma re_mul_real (a : ℝ) (ζ : ℂ) : ((a : ℂ) * ζ).re = a * ζ.re := by simp

lemma re_mul_real_one_sub (a : ℝ) (ζ : ℂ) : ((a : ℂ) * (1 - ζ)).re = a * (1 - ζ.re) := by simp

section M1

variable {ε δ c : ℝ}

lemma seedW_differentiableOn (hc : 0 < c) :
    DifferentiableOn ℂ (seedW ε δ c) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} := by
  have ha := seedScale_pos hc
  have hZ : DifferentiableOn ℂ (uctSeedZ ε) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} :=
    (differentiableOn_uctSeedZ ε).mono fun ζ hζ => ⟨by linarith [hζ.1], by linarith [hζ.2]⟩
  have hH : DifferentiableOn ℂ outerHbar {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} :=
    differentiableOn_outerH.congr fun z hz => outerHbar_of_mem_strip hz
  have hT1 : DifferentiableOn ℂ (fun ζ : ℂ => seedT δ ((seedScale c : ℂ) * ζ)) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} :=
    (seedT_differentiableOn δ).comp (by fun_prop : Differentiable ℂ fun ζ : ℂ => (seedScale c : ℂ) * ζ).differentiableOn
      fun ζ hζ => by
        show 0 < ((seedScale c : ℂ) * ζ).re
        rw [re_mul_real]; exact mul_pos ha hζ.1
  have hT2 : DifferentiableOn ℂ (fun ζ : ℂ => seedT δ ((seedScale c : ℂ) * (1 - ζ))) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} :=
    (seedT_differentiableOn δ).comp (by fun_prop : Differentiable ℂ fun ζ : ℂ => (seedScale c : ℂ) * (1 - ζ)).differentiableOn
      fun ζ hζ => by
        show 0 < ((seedScale c : ℂ) * (1 - ζ)).re
        rw [re_mul_real_one_sub]; exact mul_pos ha (by linarith [hζ.2])
  unfold seedW
  exact (((hZ.mul hH.neg.cexp).mul hT1).mul hT2).const_mul _

lemma seedW_continuousOn (hc : 0 < c) :
    ContinuousOn (seedW ε δ c) {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} := by
  have ha := seedScale_pos hc
  have hZ : ContinuousOn (uctSeedZ ε) {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} :=
    (differentiableOn_uctSeedZ ε).continuousOn.mono fun ζ hζ => ⟨by linarith [hζ.1], by linarith [hζ.2]⟩
  have hH : ContinuousOn outerHbar {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} := continuousOn_outerHbar
  have hT1 : ContinuousOn (fun ζ : ℂ => seedT δ ((seedScale c : ℂ) * ζ)) {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} :=
    (seedT_continuousOn δ).comp (by fun_prop : Continuous fun ζ : ℂ => (seedScale c : ℂ) * ζ).continuousOn
      fun ζ hζ => by
        show 0 ≤ ((seedScale c : ℂ) * ζ).re
        rw [re_mul_real]; exact mul_nonneg ha.le hζ.1
  have hT2 : ContinuousOn (fun ζ : ℂ => seedT δ ((seedScale c : ℂ) * (1 - ζ))) {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} :=
    (seedT_continuousOn δ).comp (by fun_prop : Continuous fun ζ : ℂ => (seedScale c : ℂ) * (1 - ζ)).continuousOn
      fun ζ hζ => by
        show 0 ≤ ((seedScale c : ℂ) * (1 - ζ)).re
        rw [re_mul_real_one_sub]; exact mul_nonneg ha.le (by linarith [hζ.2])
  unfold seedW
  exact (((hZ.mul hH.neg.cexp).mul hT1).mul hT2).const_mul _

lemma seedW_conj (ζ : ℂ) (hζ : 0 ≤ ζ.re) (hζ1 : ζ.re ≤ 1) :
    seedW ε δ c (starRingEnd ℂ ζ) = starRingEnd ℂ (seedW ε δ c ζ) := by
  have hcl : ζ ∈ closedStrip := ⟨hζ, hζ1⟩
  have e1 : starRingEnd ℂ ((seedScale c : ℂ) * ζ) = (seedScale c : ℂ) * starRingEnd ℂ ζ := by simp
  have e2 : starRingEnd ℂ ((seedScale c : ℂ) * (1 - ζ)) = (seedScale c : ℂ) * (1 - starRingEnd ℂ ζ) := by simp
  have e3 : starRingEnd ℂ (seedT δ (seedScale c : ℂ)) = seedT δ (seedScale c : ℂ) := by
    rw [← seedT_conj]; simp
  unfold seedW
  rw [uctSeedZ_conj, outerHbar_conj hcl, ← map_neg, Complex.exp_conj, ← e1, ← e2, seedT_conj, seedT_conj]
  simp only [map_mul, map_inv₀, e3]


lemma seedW_norm_le_far (δ ε : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ζ ∈ closedStrip, 1 / 2 ≤ |ζ.im| →
      ‖seedW ε δ c ζ‖ ≤ K * ((1 + |ζ.im|) ^ 6 * Real.exp (-(π * |ζ.im|))) := by
  obtain ⟨B, hB⟩ := seedT_bound δ
  obtain ⟨Ce, hCe⟩ := norm_exp_neg_outerHbar_le
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (by simp))
  have hCe0 : 0 ≤ max Ce 0 := le_max_right _ _
  have ha := seedScale_pos hc
  refine ⟨‖(seedT δ (seedScale c : ℂ))⁻¹‖ * (32 * π ^ 2) * max Ce 0 * B ^ 2, by positivity, fun ζ hζ hτ => ?_⟩
  have hZ := uctSeedZ_bound ε hζ hτ
  have hE := hCe ζ hζ
  set x : ℝ := |ζ.im| with hx
  have hx0 : 0 ≤ x := abs_nonneg _
  have hE' : ‖Complex.exp (-outerHbar ζ)‖ ≤ max Ce 0 * (1 + x) ^ 2 := by
    refine hE.trans ?_
    have h1 : 1 + ζ.im ^ 2 ≤ (1 + x) ^ 2 := by
      have := sq_abs ζ.im
      nlinarith
    calc Ce * (1 + ζ.im ^ 2) ≤ max Ce 0 * (1 + ζ.im ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max Ce 0 * (1 + x) ^ 2 := mul_le_mul_of_nonneg_left h1 hCe0
  have hT1 : ‖seedT δ ((seedScale c : ℂ) * ζ)‖ ≤ B :=
    hB _ (by rw [re_mul_real]; exact mul_nonneg ha.le hζ.1)
  have hT2 : ‖seedT δ ((seedScale c : ℂ) * (1 - ζ))‖ ≤ B :=
    hB _ (by rw [re_mul_real_one_sub]; exact mul_nonneg ha.le (by linarith [hζ.2]))
  unfold seedW
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have hprod : ‖uctSeedZ ε ζ‖ * ‖Complex.exp (-outerHbar ζ)‖ * ‖seedT δ ((seedScale c : ℂ) * ζ)‖ *
      ‖seedT δ ((seedScale c : ℂ) * (1 - ζ))‖ ≤
      (32 * π ^ 2 * (1 + x) ^ 4 * Real.exp (-(π * x))) * (max Ce 0 * (1 + x) ^ 2) * B * B := by
    gcongr
  calc ‖(seedT δ (seedScale c : ℂ))⁻¹‖ * (‖uctSeedZ ε ζ‖ * ‖Complex.exp (-outerHbar ζ)‖ *
        ‖seedT δ ((seedScale c : ℂ) * ζ)‖ * ‖seedT δ ((seedScale c : ℂ) * (1 - ζ))‖)
      ≤ ‖(seedT δ (seedScale c : ℂ))⁻¹‖ * ((32 * π ^ 2 * (1 + x) ^ 4 * Real.exp (-(π * x))) *
          (max Ce 0 * (1 + x) ^ 2) * B * B) := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = _ := by ring

theorem seedW_stripM1 (hc : 0 < c) : StripM1 (seedW ε δ c) where
  hol := seedW_differentiableOn hc
  cont := seedW_continuousOn hc
  real := fun ζ h0 h1 => seedW_conj ζ h0 h1
  bound := by
    obtain ⟨K, hK0, hK⟩ := seedW_norm_le_far δ ε hc
    obtain ⟨M, hM⟩ := poly_exp_le
    have hcomp : IsCompact (Icc (0 : ℝ) 1 ×ℂ Icc (-(1 / 2 : ℝ)) (1 / 2)) := isCompact_Icc.reProdIm isCompact_Icc
    obtain ⟨C0, hC0⟩ := hcomp.exists_bound_of_continuousOn
      ((seedW_continuousOn (ε := ε) (δ := δ) hc).mono (fun ζ hζ => ⟨hζ.1.1, hζ.1.2⟩))
    have hC0' : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → |ζ.im| ≤ 1 / 2 → ‖seedW ε δ c ζ‖ ≤ C0 := fun ζ h0 h1 h2 =>
      hC0 ζ ⟨⟨h0, h1⟩, abs_le.mp h2⟩
    have hC00 : 0 ≤ C0 := le_trans (norm_nonneg _) (hC0' 0 (by simp) (by simp) (by simp))
    refine ⟨max (C0 * (9 / 4)) (K * M), fun ζ h0 h1 => ?_⟩
    set x : ℝ := |ζ.im| with hx
    have hx0 : 0 ≤ x := abs_nonneg _
    have hp : 0 < (1 + x) ^ 2 := by positivity
    rw [rpow_neg_two_eq (by linarith)]
    rw [← div_eq_mul_one_div, le_div_iff₀ hp]
    rcases lt_or_ge x (1 / 2) with hlt | hge
    · have := hC0' ζ h0 h1 hlt.le
      have h2 : (1 + x) ^ 2 ≤ 9 / 4 := by nlinarith
      calc ‖seedW ε δ c ζ‖ * (1 + x) ^ 2 ≤ C0 * (9 / 4) :=
            mul_le_mul this h2 hp.le hC00
        _ ≤ _ := le_max_left _ _
    · have := hK ζ ⟨h0, h1⟩ hge
      have h3 := hM x hx0
      calc ‖seedW ε δ c ζ‖ * (1 + x) ^ 2 ≤ K * ((1 + x) ^ 6 * Real.exp (-(π * x))) * (1 + x) ^ 2 :=
            mul_le_mul_of_nonneg_right this hp.le
        _ = K * ((1 + x) ^ 8 * Real.exp (-(π * x))) := by ring
        _ ≤ K * M := mul_le_mul_of_nonneg_left h3 hK0
        _ ≤ _ := le_max_right _ _

end M1

/-- info: 'FormalResearch.SignUncertainty.seedW_stripM1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedW_stripM1

end FormalResearch.SignUncertainty
