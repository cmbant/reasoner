module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasAssembly
public import FormalResearch.SignUncertainty.CtBoasFar
public import FormalResearch.SignUncertainty.CtBoasNeg

/-!
# `ct:boas-ineq`: the field `far` of `BoasInputs` for the concrete Hankel setting (Step 1)

`constant_terms_lower.tex`, proof of `ct:boas`, Step 1 and the splitting `ℬ = ℬ_near + ℬ_far`.  With `D = c log c`,
`W = c/4`, `Δ(L) = c e^L/π²`, the Gaussian step `𝔰_far(Δ) = ∫_{x>D} G_W(Δ - x) dx` (`sFar`) and the density
`h = hankelHL c f`, this module proves the lower bound `ℬ_far ≥ -εfar` (the field `far`) with an explicit `εfar`
(`boasFarEps`) built from the finite Fejér inequality `hankel_psiT_fejer` (the harmonics sum) and the Gaussian tails.

* `gaussK_set_le`: `∫_S G_W(Δ - x) dx ≤ √2 e^{-a²/(4W²)}` if `|Δ - x| ≥ a` on `S`;
* `sFar_le`, `one_sub_sWin_le`, `sWin_add_sFar_le`: `𝔰_far(Δ) ≤ e`, `1 - 𝔰_{D,W}(Δ) ≤ e` for `0 ≤ Δ ≤ D/2`, and
  `0 ≤ 1 - 𝔰_{D,W} - 𝔰_far ≤ e'` for `Δ ≥ 0` (`e = √2 e^{-(log c)²}`, `e' = √2 e^{-4(log c)²}`);
* `integral_hankelHL_mul_eq`: the change of variables `h(L)dL = (fρ₀)(Δ)dΔ`;
* `boas_far_field`: the field `far` for `sf = 𝔰_far ∘ Δ`, with `w̃ = 1` for `Δ > D/2` and the phase `X` equal to
  `2πΔ - πc/4 + (3+ε)π/4` up to `E_ph` for `Δ > D/2` (`hphase`; discharged by `ct_phase_far` and `ct:outer`(3) in
  `CtBoasFarPhase`).

**Proved.**  The numerical bookkeeping `boasFarEps c n E_ph = O(c^{-8.8} log c)` (the sum over the harmonics) is not done.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtBoasWindow

/-- `D = c log c`, the position `Δ_far` of the Gaussian step. -/
noncomputable def farD (c : ℝ) : ℝ := c * Real.log c

/-- `W_far = c/4`, the width of the Gaussian step. -/
noncomputable def farW (c : ℝ) : ℝ := c / 4

/-- The smooth Gaussian step `𝔰_far(Δ) = ∫_{Δ_far}^∞ G_{W_far}(Δ - Δ₀) dΔ₀` of `ct:boas`. -/
noncomputable def sFar (c Δ : ℝ) : ℝ := ∫ x in Ioi (farD c), gaussK (farW c) (Δ - x)

/-- `e = √2 e^{-(log c)²}`. -/
noncomputable def farE1 (c : ℝ) : ℝ := √2 * Real.exp (-(Real.log c) ^ 2)

/-- `e' = √2 e^{-4(log c)²}`. -/
noncomputable def farE2 (c : ℝ) : ℝ := √2 * Real.exp (-(4 * Real.log c ^ 2))

/-- `G'(y) = e^{-y²/(4W²)}/(√(2π)W)`, a Gaussian of integral `√2`. -/
private lemma integral_gaussWide {W : ℝ} (hW : 0 < W) (Δ : ℝ) :
    ∫ x : ℝ, Real.exp (-(1 / (4 * W ^ 2)) * (Δ - x) ^ 2) / (√(2 * π) * W) = √2 := by
  have hb : 0 < 1 / (4 * W ^ 2) := by positivity
  have h1 : ∫ y : ℝ, Real.exp (-(1 / (4 * W ^ 2)) * y ^ 2) = √(π / (1 / (4 * W ^ 2))) := integral_gaussian _
  have h0 : ∫ x : ℝ, Real.exp (-(1 / (4 * W ^ 2)) * (Δ - x) ^ 2) =
      ∫ y : ℝ, Real.exp (-(1 / (4 * W ^ 2)) * y ^ 2) :=
    integral_sub_left_eq_self (fun y : ℝ => Real.exp (-(1 / (4 * W ^ 2)) * y ^ 2)) volume Δ
  rw [integral_div, h0, h1]
  have h2 : π / (1 / (4 * W ^ 2)) = (2 * W) ^ 2 * π := by field_simp; ring
  have h3 : √((2 * W) ^ 2 * π) = 2 * W * √π := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [h2, h3]
  have h4 : √(2 * π) = √2 * √π := Real.sqrt_mul (by norm_num) _
  rw [h4]
  have : (0 : ℝ) < √π := Real.sqrt_pos.2 Real.pi_pos
  have : (0 : ℝ) < √2 := Real.sqrt_pos.2 (by norm_num)
  field_simp
  exact (Real.sq_sqrt (by norm_num)).symm

private lemma integrable_gaussWide {W : ℝ} (hW : 0 < W) (Δ : ℝ) :
    Integrable fun x : ℝ => Real.exp (-(1 / (4 * W ^ 2)) * (Δ - x) ^ 2) / (√(2 * π) * W) := by
  have hb : 0 < 1 / (4 * W ^ 2) := by positivity
  have := (integrable_exp_neg_mul_sq hb).comp_sub_left Δ
  exact this.div_const _

/-- **Gaussian tail** on a set: if `|Δ - x| ≥ a ≥ 0` on a measurable `S` then `∫_S G_W(Δ - x) dx ≤ √2 e^{-a²/(4W²)}`. -/
lemma gaussK_set_le {W : ℝ} (hW : 0 < W) {S : Set ℝ} (hS : MeasurableSet S) (Δ a : ℝ)
    (hSa : ∀ x ∈ S, a ≤ |Δ - x|) (ha : 0 ≤ a) :
    ∫ x in S, gaussK W (Δ - x) ≤ √2 * Real.exp (-(a ^ 2 / (4 * W ^ 2))) := by
  set E : ℝ := Real.exp (-(a ^ 2 / (4 * W ^ 2))) with hE
  have hint := integrable_gaussWide hW Δ
  have hpt : ∀ x ∈ S, gaussK W (Δ - x) ≤
      E * (Real.exp (-(1 / (4 * W ^ 2)) * (Δ - x) ^ 2) / (√(2 * π) * W)) := by
    intro x hx
    have ha2 : a ^ 2 ≤ (Δ - x) ^ 2 := by
      rw [← sq_abs (Δ - x)]; exact pow_le_pow_left₀ ha (hSa x hx) 2
    unfold gaussK
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [hE, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : (1 / (2 * W ^ 2)) = 2 * (1 / (4 * W ^ 2)) := by field_simp; ring
    have h4 : 0 < 1 / (4 * W ^ 2) := by positivity
    have : a ^ 2 / (4 * W ^ 2) = a ^ 2 * (1 / (4 * W ^ 2)) := by ring
    nlinarith [mul_le_mul_of_nonneg_left ha2 h4.le]
  calc ∫ x in S, gaussK W (Δ - x)
      ≤ ∫ x in S, E * (Real.exp (-(1 / (4 * W ^ 2)) * (Δ - x) ^ 2) / (√(2 * π) * W)) := by
        refine setIntegral_mono_on ?_ (hint.const_mul E).integrableOn hS hpt
        exact ((integrable_gaussK hW).comp_sub_left Δ).integrableOn
    _ ≤ ∫ x, E * (Real.exp (-(1 / (4 * W ^ 2)) * (Δ - x) ^ 2) / (√(2 * π) * W)) := by
        refine setIntegral_le_integral (hint.const_mul E) (ae_of_all _ fun x => ?_)
        positivity
    _ = √2 * E := by rw [integral_const_mul, integral_gaussWide hW]; ring


private lemma integrableOn_gaussK_sub {W : ℝ} (hW : 0 < W) (Δ : ℝ) (S : Set ℝ) :
    IntegrableOn (fun x => gaussK W (Δ - x)) S :=
  ((integrable_gaussK hW).comp_sub_left Δ).integrableOn

/-- `1 - 𝔰_{D,W} = ∫_{x<-D} G_W + ∫_{x>D} G_W` (the two Gaussian tails). -/
lemma one_sub_sWin_eq {W : ℝ} (hW : 0 < W) {D : ℝ} (hD : 0 ≤ D) (Δ : ℝ) :
    1 - sWin D W Δ = (∫ x in Iio (-D), gaussK W (Δ - x)) + ∫ x in Ioi D, gaussK W (Δ - x) := by
  have hall : ∫ x, gaussK W (Δ - x) = 1 := by
    rw [integral_sub_left_eq_self (gaussK W) volume Δ]; exact integral_gaussK hW
  have h1 := integral_add_compl (measurableSet_Icc (a := -D) (b := D))
    ((integrable_gaussK hW).comp_sub_left Δ)
  rw [hall] at h1
  have h2 : ∫ x in (Icc (-D) D)ᶜ, gaussK W (Δ - x) =
      (∫ x in Iio (-D), gaussK W (Δ - x)) + ∫ x in Ioi D, gaussK W (Δ - x) := by
    have hc : (Icc (-D) D)ᶜ = Iio (-D) ∪ Ioi D := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
      constructor
      · intro h
        by_cases hx : -D ≤ x
        · right; exact lt_of_not_ge (fun hh => h ⟨hx, hh⟩)
        · left; exact not_le.1 hx
      · rintro (h | h) ⟨h1, h2⟩ <;> linarith
    rw [hc]
    exact setIntegral_union (Set.disjoint_left.2 fun x hx hx' => by
      simp only [Set.mem_Iio, Set.mem_Ioi] at hx hx'
      linarith) measurableSet_Ioi (integrableOn_gaussK_sub hW Δ _) (integrableOn_gaussK_sub hW Δ _)
  unfold sWin
  linarith

section farnum

variable {c : ℝ} (hc : 1 < c)

include hc in
lemma farD_pos : 0 < farD c := by
  unfold farD; exact mul_pos (by linarith) (Real.log_pos hc)

include hc in
private lemma farD_sq : (farD c / 2) ^ 2 / (4 * farW c ^ 2) = Real.log c ^ 2 := by
  unfold farD farW; field_simp; ring

include hc in
private lemma farD_sq' : farD c ^ 2 / (4 * farW c ^ 2) = 4 * Real.log c ^ 2 := by
  unfold farD farW; field_simp

include hc in
/-- `𝔰_far(Δ) ≤ e` for `Δ ≤ D/2`. -/
lemma sFar_le {Δ : ℝ} (hΔ : Δ ≤ farD c / 2) : sFar c Δ ≤ farE1 c := by
  have hD := farD_pos hc
  have hW : 0 < farW c := by unfold farW; linarith
  have := gaussK_set_le hW (measurableSet_Ioi (a := farD c)) Δ (farD c / 2)
    (fun x hx => by
      simp only [Set.mem_Ioi] at hx
      rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith) (by linarith)
  rw [farD_sq hc] at this
  exact this

include hc in
lemma sFar_nonneg (Δ : ℝ) : 0 ≤ sFar c Δ := by
  have hW : 0 < farW c := by unfold farW; linarith
  exact setIntegral_nonneg measurableSet_Ioi fun x _ => by unfold gaussK; positivity

include hc in
/-- `1 - 𝔰_{D,W}(Δ) ≤ e` for `0 ≤ Δ ≤ D/2`. -/
lemma one_sub_sWin_le {Δ : ℝ} (h0 : 0 ≤ Δ) (hΔ : Δ ≤ farD c / 2) :
    1 - sWin (farD c) (farW c) Δ ≤ 2 * farE1 c := by
  have hD := farD_pos hc
  have hW : 0 < farW c := by unfold farW; linarith
  rw [one_sub_sWin_eq hW (farD_pos hc).le]
  have h1 := gaussK_set_le hW (measurableSet_Iio (a := -farD c)) Δ (farD c / 2)
    (fun x hx => by
      simp only [Set.mem_Iio] at hx
      rw [abs_of_pos (by linarith)]; linarith) (by linarith)
  have h2 := gaussK_set_le hW (measurableSet_Ioi (a := farD c)) Δ (farD c / 2)
    (fun x hx => by
      simp only [Set.mem_Ioi] at hx
      rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith) (by linarith)
  rw [farD_sq hc] at h1 h2
  unfold farE1
  linarith

include hc in
/-- `0 ≤ 1 - 𝔰_{D,W}(Δ) - 𝔰_far(Δ) ≤ e'` for `Δ ≥ 0`. -/
lemma one_sub_sWin_sub_sFar {Δ : ℝ} (h0 : 0 ≤ Δ) :
    0 ≤ 1 - sWin (farD c) (farW c) Δ - sFar c Δ ∧ 1 - sWin (farD c) (farW c) Δ - sFar c Δ ≤ farE2 c := by
  have hD := farD_pos hc
  have hW : 0 < farW c := by unfold farW; linarith
  rw [one_sub_sWin_eq hW (farD_pos hc).le]
  unfold sFar
  have e : (∫ x in Iio (-farD c), gaussK (farW c) (Δ - x)) + (∫ x in Ioi (farD c), gaussK (farW c) (Δ - x)) -
      ∫ x in Ioi (farD c), gaussK (farW c) (Δ - x) = ∫ x in Iio (-farD c), gaussK (farW c) (Δ - x) := by ring
  rw [e]
  refine ⟨setIntegral_nonneg measurableSet_Iio fun x _ => by unfold gaussK; positivity, ?_⟩
  have := gaussK_set_le hW (measurableSet_Iio (a := -farD c)) Δ (farD c)
    (fun x hx => by
      simp only [Set.mem_Iio] at hx
      rw [abs_of_pos (by linarith)]; linarith) hD.le
  rw [farD_sq' hc] at this
  unfold farE2
  exact this

include hc in
lemma sFar_le_one (Δ : ℝ) : sFar c Δ ≤ 1 := by
  have hW : 0 < farW c := by unfold farW; linarith
  have hall : ∫ x, gaussK (farW c) (Δ - x) = 1 := by
    rw [integral_sub_left_eq_self (gaussK (farW c)) volume Δ]; exact integral_gaussK hW
  rw [← hall]
  exact setIntegral_le_integral ((integrable_gaussK hW).comp_sub_left Δ)
    (ae_of_all _ fun x => by unfold gaussK; positivity)

end farnum

/-- A bounded measurable factor times an integrable function is integrable. -/
lemma integrable_mul_bdd {g F : ℝ → ℝ} {C : ℝ} (hg : Integrable g) (hF : Measurable F)
    (hb : ∀ x, |F x| ≤ C) : Integrable fun x => F x * g x := by
  refine (hg.abs.const_mul C).mono' (hF.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _)


/-- **Change of variables** `h(L) dL = (f ρ₀)(Δ) dΔ`, `Δ = c e^L/π²`: for every `G`,
`∫_ℝ G(L) h(L) dL = ∫_{Δ>0} G(log(π²Δ/c)) (f ρ₀)(Δ) dΔ` (`h = hankelHL c f`, `hankelDensity = 1_{Δ>0} f ρ₀`). -/
lemma integral_hankelHL_mul_eq {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) (G : ℝ → ℝ) :
    ∫ L, G L * hankelHL c f L =
      ∫ Δ, G (Real.log (π ^ 2 * (Δ / c))) * hankelDensity c f Δ := by
  have hpi : (0 : ℝ) < π ^ 2 := by positivity
  set φ : ℝ → ℝ := fun L => c * (Real.exp L / π ^ 2) with hφ
  have himg : φ '' univ = Ioi 0 := by
    ext Δ
    simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_Ioi, hφ]
    constructor
    · rintro ⟨L, rfl⟩; positivity
    · intro hΔ
      refine ⟨Real.log (π ^ 2 * (Δ / c)), ?_⟩
      rw [Real.exp_log (by positivity)]; field_simp
  have hd : ∀ L ∈ (univ : Set ℝ), HasDerivWithinAt φ (c * (Real.exp L / π ^ 2)) univ L :=
    fun L _ => (((Real.hasDerivAt_exp L).div_const _).const_mul c).hasDerivWithinAt
  have hinj : InjOn φ univ := by
    intro a _ b _ hab
    simp only [hφ] at hab
    have := mul_left_cancel₀ hc.ne' hab
    exact Real.exp_injective ((div_left_inj₀ hpi.ne').1 this)
  have key := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd hinj
    (fun Δ : ℝ => G (Real.log (π ^ 2 * (Δ / c))) * (f Δ * hankelRho0 c Δ))
  rw [himg, setIntegral_univ] at key
  have hR : ∫ Δ, G (Real.log (π ^ 2 * (Δ / c))) * hankelDensity c f Δ =
      ∫ Δ in Ioi (0 : ℝ), G (Real.log (π ^ 2 * (Δ / c))) * (f Δ * hankelRho0 c Δ) := by
    rw [← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (ae_of_all _ fun Δ => ?_)
    by_cases hΔ : Δ ∈ Ioi (0 : ℝ)
    · simp [hankelDensity, Set.indicator_of_mem hΔ]
    · simp [hankelDensity, Set.indicator_of_notMem hΔ]
  rw [hR, key]
  refine integral_congr_ae (ae_of_all _ fun L => ?_)
  have hp : 0 ≤ c * (Real.exp L / π ^ 2) := by positivity
  have hl : Real.log (π ^ 2 * (φ L / c)) = L := by
    simp only [hφ]
    rw [show π ^ 2 * (c * (Real.exp L / π ^ 2) / c) = Real.exp L by field_simp, Real.log_exp]
  simp only [smul_eq_mul, hφ] at hl ⊢
  rw [hl, abs_of_nonneg hp]
  unfold hankelHL
  ring


/-- The phase `φ_∞ = π/2 - πc/4 + (3+ε)π/4` of `ct:boas` Step 1. -/
noncomputable def farPhase (c ε : ℝ) : ℝ := π / 2 - π * c / 4 + (3 + ε) * π / 4

/-- The Fejér integrand `(1 - 𝔰_{D,W}(Δ))(1 + 2cos(2πΔ + φ_∞))` of `ψ̃(1 + 2cos(2πΔ + φ_∞))`, per unit density. -/
noncomputable def farF2 (c ε x : ℝ) : ℝ :=
  (1 - sWin (farD c) (farW c) x) * (1 + 2 * Real.cos (2 * π * x + farPhase c ε))

/-- The `L`-integrand of `ℬ_far`, cut at `L_min`: `1_{L ≥ L_min} w̃ 𝔰_far (1 - 2 sin X)`. -/
noncomputable def farG1 (X wt sf : ℝ → ℝ) (Lmin : ℝ) : ℝ → ℝ :=
  (Ici Lmin).indicator fun L => wt L * sf L * boasKernel X L

lemma abs_farF2_le {c : ℝ} (hc : 1 < c) (ε x : ℝ) : |farF2 c ε x| ≤ 3 := by
  have hW : 0 < farW c := by unfold farW; linarith
  have h0 := sWin_nonneg (D := farD c) hW x
  have h1 := sWin_le_one (D := farD c) hW x
  unfold farF2
  rw [abs_mul, abs_of_nonneg (by linarith)]
  have a1 := Real.neg_one_le_cos (2 * π * x + farPhase c ε)
  have a2 := Real.cos_le_one (2 * π * x + farPhase c ε)
  have h3 : |1 + 2 * Real.cos (2 * π * x + farPhase c ε)| ≤ 3 := by rw [abs_le]; constructor <;> linarith
  calc (1 - sWin (farD c) (farW c) x) * |1 + 2 * Real.cos (2 * π * x + farPhase c ε)| ≤ 1 * 3 :=
        mul_le_mul (by linarith) h3 (abs_nonneg _) zero_le_one
    _ = 3 := by norm_num

lemma abs_farG1_le {c : ℝ} (hc : 1 < c) {X wt sf : ℝ → ℝ} (hw : ∀ L, 0 ≤ wt L ∧ wt L ≤ 1)
    (hsf : ∀ L, sf L = sFar c (c * (Real.exp L / π ^ 2))) (Lmin L : ℝ) : |farG1 X wt sf Lmin L| ≤ 3 := by
  unfold farG1
  by_cases hL : L ∈ Ici Lmin
  · rw [Set.indicator_of_mem hL, abs_mul, abs_mul]
    have h1 : |wt L| ≤ 1 := by rw [abs_of_nonneg (hw L).1]; exact (hw L).2
    have h2 : |sf L| ≤ 1 := by
      rw [hsf, abs_of_nonneg (sFar_nonneg hc _)]; exact sFar_le_one hc _
    have h3 := abs_boasKernel_le X L
    calc |wt L| * |sf L| * |boasKernel X L| ≤ 1 * 1 * 3 :=
          mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one) h3 (abs_nonneg _) (by norm_num)
      _ = 3 := by norm_num
  · rw [Set.indicator_of_notMem hL]; simp

/-- **Pointwise comparison** of `ℬ_far`'s integrand with the Fejér integrand: for `Δ > 0`,
`|1_{L ≥ L_min} w̃ 𝔰_far (1 - 2 sin X) - (1 - 𝔰_{D,W})(1 + 2cos(2πΔ + φ_∞))| ≤ 9e + 3e' + 2E_ph`. -/
lemma far_pointwise {c ε : ℝ} (hc : 1 < c) {X wt sf : ℝ → ℝ} {Lmin Eph : ℝ}
    (hw : ∀ L, 0 ≤ wt L ∧ wt L ≤ 1) (hsf : ∀ L, sf L = sFar c (c * (Real.exp L / π ^ 2)))
    (hwt1 : ∀ L, farD c / 2 < c * (Real.exp L / π ^ 2) → wt L = 1)
    (hLmin : c * (Real.exp Lmin / π ^ 2) ≤ farD c / 2) (hEph : 0 ≤ Eph)
    (hphase : ∀ L, farD c / 2 < c * (Real.exp L / π ^ 2) →
      |X L - (2 * π * (c * (Real.exp L / π ^ 2)) - π * c / 4 + (3 + ε) * π / 4)| ≤ Eph)
    {x : ℝ} (hx : 0 < x) :
    |farG1 X wt sf Lmin (Real.log (π ^ 2 * (x / c))) - farF2 c ε x| ≤
      9 * farE1 c + 3 * farE2 c + 2 * Eph := by
  have hc0 : 0 < c := by linarith
  have hpi : (0 : ℝ) < π ^ 2 := by positivity
  have hW : 0 < farW c := by unfold farW; linarith
  have he1 : 0 ≤ farE1 c := by unfold farE1; positivity
  have he2 : 0 ≤ farE2 c := by unfold farE2; positivity
  have hsW0 := sWin_nonneg (D := farD c) hW x
  have hsW1 := sWin_le_one (D := farD c) hW x
  set L : ℝ := Real.log (π ^ 2 * (x / c)) with hL
  have hexp : Real.exp L = π ^ 2 * (x / c) := Real.exp_log (by positivity)
  have hΔL : c * (Real.exp L / π ^ 2) = x := by rw [hexp]; field_simp
  have hsfL : sf L = sFar c x := by rw [hsf, hΔL]
  have a1 : ∀ y : ℝ, -1 ≤ Real.cos y := Real.neg_one_le_cos
  have a2 : ∀ y : ℝ, Real.cos y ≤ 1 := Real.cos_le_one
  rcases le_or_gt x (farD c / 2) with hxD | hxD
  · -- near region: both terms are tiny
    have hs1 := sFar_le hc hxD
    have hs0 := sFar_nonneg hc x
    have hw1 := hw L
    have hF1s : |farG1 X wt sf Lmin L| ≤ 3 * farE1 c := by
      unfold farG1
      by_cases hLm : L ∈ Ici Lmin
      · rw [Set.indicator_of_mem hLm, abs_mul, abs_mul, abs_of_nonneg hw1.1, hsfL, abs_of_nonneg hs0]
        have h3 := abs_boasKernel_le X L
        have h4 : wt L * sFar c x ≤ 1 * farE1 c := mul_le_mul hw1.2 hs1 hs0 zero_le_one
        calc wt L * sFar c x * |boasKernel X L| ≤ (1 * farE1 c) * 3 :=
              mul_le_mul h4 h3 (abs_nonneg _) (by positivity)
          _ = 3 * farE1 c := by ring
      · rw [Set.indicator_of_notMem hLm]; simp only [abs_zero]; linarith
    have hF2s : |farF2 c ε x| ≤ 6 * farE1 c := by
      have h1 := one_sub_sWin_le hc hx.le hxD
      have h4 : |1 + 2 * Real.cos (2 * π * x + farPhase c ε)| ≤ 3 := by
        rw [abs_le]; constructor <;> linarith [a1 (2 * π * x + farPhase c ε), a2 (2 * π * x + farPhase c ε)]
      unfold farF2
      rw [abs_mul, abs_of_nonneg (by linarith)]
      calc (1 - sWin (farD c) (farW c) x) * |1 + 2 * Real.cos (2 * π * x + farPhase c ε)|
          ≤ (2 * farE1 c) * 3 := mul_le_mul h1 h4 (abs_nonneg _) (by positivity)
        _ = 6 * farE1 c := by ring
    calc |farG1 X wt sf Lmin L - farF2 c ε x| ≤ |farG1 X wt sf Lmin L| + |farF2 c ε x| := abs_sub _ _
      _ ≤ 9 * farE1 c + 3 * farE2 c + 2 * Eph := by linarith
  · -- far region: phase asymptotics
    have hLmL : Lmin < L := by
      have : c * (Real.exp Lmin / π ^ 2) < c * (Real.exp L / π ^ 2) := by rw [hΔL]; linarith
      have h2 : Real.exp Lmin < Real.exp L := by
        have := lt_of_mul_lt_mul_left this hc0.le
        exact (div_lt_div_iff_of_pos_right hpi).1 this
      exact Real.exp_lt_exp.1 h2
    have hwL : wt L = 1 := hwt1 L (by rw [hΔL]; exact hxD)
    have hF1x' : farG1 X wt sf Lmin L = sFar c x * (1 - 2 * Real.sin (X L)) := by
      unfold farG1
      rw [Set.indicator_of_mem (show L ∈ Ici Lmin from hLmL.le), hwL, hsfL]
      unfold boasKernel; ring
    have hph := hphase L (by rw [hΔL]; exact hxD)
    rw [hΔL] at hph
    obtain ⟨hr0, hr1⟩ := one_sub_sWin_sub_sFar hc hx.le
    have hsin : |Real.sin (X L) + Real.cos (2 * π * x + farPhase c ε)| ≤ Eph := by
      have e : Real.cos (2 * π * x + farPhase c ε) =
          -Real.sin (2 * π * x - π * c / 4 + (3 + ε) * π / 4) := by
        have h := Real.sin_sub_pi_div_two (2 * π * x + farPhase c ε)
        have h2 : 2 * π * x + farPhase c ε - π / 2 = 2 * π * x - π * c / 4 + (3 + ε) * π / 4 := by
          unfold farPhase; ring
        rw [h2] at h
        linarith
      rw [e, ← sub_eq_add_neg]
      exact (Real.abs_sin_sub_sin_le _ _).trans hph
    have hs0 := sFar_nonneg hc x
    have hs1 := sFar_le_one hc x
    set r := 1 - sWin (farD c) (farW c) x - sFar c x with hr
    set Y := 2 * π * x + farPhase c ε with hY
    have hid : farG1 X wt sf Lmin L - farF2 c ε x =
        -(r * (1 + 2 * Real.cos Y)) - 2 * (sFar c x * (Real.sin (X L) + Real.cos Y)) := by
      rw [hF1x']; unfold farF2; rw [hr]; ring
    have h4 : |1 + 2 * Real.cos Y| ≤ 3 := by
      rw [abs_le]; constructor <;> linarith [a1 Y, a2 Y]
    have ha : |r * (1 + 2 * Real.cos Y)| ≤ 3 * farE2 c := by
      rw [abs_mul, abs_of_nonneg hr0]
      calc r * |1 + 2 * Real.cos Y| ≤ farE2 c * 3 := mul_le_mul hr1 h4 (abs_nonneg _) he2
        _ = 3 * farE2 c := by ring
    have hb : |2 * (sFar c x * (Real.sin (X L) + Real.cos Y))| ≤ 2 * Eph := by
      rw [abs_mul, abs_mul, abs_of_nonneg hs0, abs_two]
      calc 2 * (sFar c x * |Real.sin (X L) + Real.cos Y|) ≤ 2 * (1 * Eph) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hs1 hsin (abs_nonneg _) zero_le_one) (by norm_num)
        _ = 2 * Eph := by ring
    rw [hid]
    calc |-(r * (1 + 2 * Real.cos Y)) - 2 * (sFar c x * (Real.sin (X L) + Real.cos Y))|
        ≤ |-(r * (1 + 2 * Real.cos Y))| + |2 * (sFar c x * (Real.sin (X L) + Real.cos Y))| := abs_sub _ _
      _ ≤ 9 * farE1 c + 3 * farE2 c + 2 * Eph := by rw [abs_neg]; linarith

/-- The explicit `εfar` of `boas_far_field`: the Fejér errors of `hankel_psiT_fejer` for `n`, `D = c log c`, `W = c/4`
(negative part `≤ 2e`, mass `≤ 1`, the harmonics `2 ≤ k < n`) plus the pointwise difference bound
`9e + 3e' + 2E_ph` between `ℬ_far`'s integrand and `ψ̃ (1 + 2cos(2πΔ + φ_∞))`. -/
noncomputable def boasFarEps (c : ℝ) (n : ℕ) (Eph : ℝ) : ℝ :=
  n * (2 * farE1 c) + 2 / n +
    2 * ∑ k ∈ Finset.Ico 2 n, ((k : ℝ) ^ (-c) +
      2 * farD c * (((3 * (k : ℝ) / 4) ^ (-c) * √(π / (2 * π ^ 2 * farW c ^ 2)) +
        1 * Real.exp (-(2 * π ^ 2 * farW c ^ 2) * ((k : ℝ) / 4) ^ 2 / 2) *
          √(2 * π / (2 * π ^ 2 * farW c ^ 2))))) +
    (9 * farE1 c + 3 * farE2 c + 2 * Eph)

/-- **The Fejér lower bound for the far density** (`ct:boas` Step 1): for feasible `f` with `M[f] = 1`, `T ≤ D/2`,
`∫ (1 - 𝔰_{D,W}) (fρ₀) (1 + 2cos(2πΔ + φ_∞)) dΔ ≥ -(n·2e + 2/n + 2Σ_{k=2}^{n-1}(...))`
(`hankel_psiT_fejer`, the negative part of `ψ̃` supported on `Δ < T ≤ D/2` where `1 - 𝔰_{D,W} ≤ 2e`). -/
lemma far_fejer_lower {c ε T : ℝ} (hc : 1 < c) (hε : ε * ε = 1)
    {f : ℝ → ℝ} (hf : IsHankelFeasible c ε T f) (hM : hankelMass c f = 1) (hT : T ≤ farD c / 2)
    {n : ℕ} (hn : 2 ≤ n) :
    -(boasFarEps c n 0 - (9 * farE1 c + 3 * farE2 c + 2 * 0)) ≤
      ∫ x, farF2 c ε x * hankelDensity c f x := by
  have hc0 : 0 < c := by linarith
  have hD := farD_pos hc
  have hW : 0 < farW c := by unfold farW; linarith
  set gD := hankelDensity c f with hgD
  have hint : Integrable gD := (integrable_indicator_iff measurableSet_Ioi).mpr hf.int
  have habs : ∫ x, |gD x| = 1 := by
    have : ∀ x, |gD x| = (Ioi (0 : ℝ)).indicator (fun s => |f s| * hankelRho0 c s) x := by
      intro x
      by_cases hx : x ∈ Ioi (0 : ℝ)
      · simp only [hgD, hankelDensity, Set.indicator_of_mem hx]
        rw [abs_mul, abs_of_nonneg (hankelRho0_nonneg hc0 (le_of_lt hx))]
      · simp [hgD, hankelDensity, Set.indicator_of_notMem hx]
    simp_rw [this]
    rw [integral_indicator measurableSet_Ioi]
    exact hM
  have hgD0 : ∀ x, x ≤ 0 → gD x = 0 := fun x hx => by
    simp [hgD, hankelDensity,
      Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from fun h => absurd h (not_lt.2 hx))]
  have hsW0 := sWin_nonneg (D := farD c) hW
  have hsW1 := sWin_le_one (D := farD c) hW
  have hψi := integrable_psiT hint hW (D := farD c)
  have hfe := hankel_psiT_fejer (by linarith : 1 / 2 < c) hε hf.toIsHankelEigenfn hM hW hD.le hn (farPhase c ε)
  have hψpt : ∀ x, |psiT gD (farD c) (farW c) x| ≤ |gD x| := by
    intro x
    unfold psiT
    rw [abs_mul, abs_of_nonneg (by linarith [hsW1 x])]
    exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [hsW0 x])
  have hA : ∫ x, max (-psiT gD (farD c) (farW c) x) 0 ≤ 2 * farE1 c := by
    have hpt : ∀ x, max (-psiT gD (farD c) (farW c) x) 0 ≤ (2 * farE1 c) * |gD x| := by
      intro x
      by_cases hx : 0 < x
      · by_cases hxT : T ≤ x
        · have hg0 : 0 ≤ gD x := by
            simp only [hgD, hankelDensity, Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
            exact mul_nonneg (hf.tail_nonneg x hxT) (hankelRho0_nonneg hc0 hx.le)
          have : 0 ≤ psiT gD (farD c) (farW c) x := mul_nonneg (by linarith [hsW1 x]) hg0
          rw [max_eq_right (by linarith)]
          exact mul_nonneg (by unfold farE1; positivity) (abs_nonneg _)
        · have hxD : x ≤ farD c / 2 := by linarith [not_le.1 hxT]
          have h1 := one_sub_sWin_le hc hx.le hxD
          calc max (-psiT gD (farD c) (farW c) x) 0 ≤ |psiT gD (farD c) (farW c) x| := by
                rw [max_le_iff]; exact ⟨neg_le_abs _, abs_nonneg _⟩
            _ = (1 - sWin (farD c) (farW c) x) * |gD x| := by
                unfold psiT; rw [abs_mul, abs_of_nonneg (by linarith [hsW1 x])]
            _ ≤ (2 * farE1 c) * |gD x| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      · have h0 : psiT gD (farD c) (farW c) x = 0 := by
          unfold psiT; rw [hgD0 x (not_lt.1 hx)]; ring
        rw [h0, hgD0 x (not_lt.1 hx)]; simp
    calc ∫ x, max (-psiT gD (farD c) (farW c) x) 0 ≤ ∫ x, (2 * farE1 c) * |gD x| :=
          integral_mono_of_nonneg (ae_of_all _ fun x => le_max_right _ _) (hint.abs.const_mul _)
            (ae_of_all _ hpt)
      _ = 2 * farE1 c := by rw [integral_const_mul, habs]; ring
  have hB : ∫ x, |psiT gD (farD c) (farW c) x| ≤ 1 := by
    rw [← habs]
    exact integral_mono hψi.abs hint.abs hψpt
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have a1 := mul_le_mul_of_nonneg_left hA hn0.le
  have a2 := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 2 / n)
  have hTeq : ∫ x, psiT gD (farD c) (farW c) x * (1 + 2 * Real.cos (2 * π * x + farPhase c ε)) =
      ∫ x, farF2 c ε x * gD x := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [psiT, farF2]; ring
  rw [← hTeq]
  unfold boasFarEps
  linarith

/-- **`ct:boas` Step 1: the field `far`** (`ℬ_far ≥ -εfar`).  For a feasible `f` (`c > 1`, `ε² = 1`, `M[f] = 1`,
`T ≤ D/2`), the taper `w̃ ∈ [0,1]` with `w̃ = 1` for `Δ > D/2`, the step `sf = 𝔰_far(Δ(L))`, a measurable phase `X`
with `X = 2πΔ - πc/4 + (3+ε)π/4 + O(E_ph)` for `Δ > D/2` (`hphase`), and `L_min` with `Δ(L_min) ≤ D/2`:
`-boasFarEps c n E_ph ≤ ∫_{L ≥ L_min} w̃ 𝔰_far h (1 - 2 sin X) dL`.
The proof is `ℬ_far = ∫ψ̃(1 + 2cos(2πΔ + φ_∞)) + (error ≤ 9e + 3e' + 2E_ph)` (change of variables
`integral_hankelHL_mul_eq`, pointwise comparison `far_pointwise`, Gaussian tails `sFar_le` etc.) and
`hankel_psiT_fejer` (`far_fejer_lower`). -/
theorem boas_far_field {c ε T : ℝ} (hc : 1 < c) (hε : ε * ε = 1)
    {f : ℝ → ℝ} (hf : IsHankelFeasible c ε T f) (hM : hankelMass c f = 1) (hT : T ≤ farD c / 2)
    {X wt sf : ℝ → ℝ} {Lmin Eph : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hXm : Measurable X) (hwm : Measurable wt) (hsfm : Measurable sf) (hw : ∀ L, 0 ≤ wt L ∧ wt L ≤ 1)
    (hsf : ∀ L, sf L = sFar c (c * (Real.exp L / π ^ 2)))
    (hwt1 : ∀ L, farD c / 2 < c * (Real.exp L / π ^ 2) → wt L = 1)
    (hLmin : c * (Real.exp Lmin / π ^ 2) ≤ farD c / 2) (hEph : 0 ≤ Eph)
    (hphase : ∀ L, farD c / 2 < c * (Real.exp L / π ^ 2) →
      |X L - (2 * π * (c * (Real.exp L / π ^ 2)) - π * c / 4 + (3 + ε) * π / 4)| ≤ Eph) :
    -boasFarEps c n Eph ≤ ∫ L in Ici Lmin, wt L * sf L * (hankelHL c f L * boasKernel X L) := by
  have hc0 : 0 < c := by linarith
  have hint : Integrable (hankelDensity c f) := (integrable_indicator_iff measurableSet_Ioi).mpr hf.int
  set gD := hankelDensity c f with hgD
  have hgD0 : ∀ x, x ≤ 0 → gD x = 0 := fun x hx => by
    simp [hgD, hankelDensity,
      Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from fun h => absurd h (not_lt.2 hx))]
  have hlogm : Measurable fun x : ℝ => Real.log (π ^ 2 * (x / c)) :=
    Real.measurable_log.comp (measurable_const.mul (measurable_id.div_const _))
  have hKm : Measurable (boasKernel X) := measurable_boasKernel hXm
  have hG1m : Measurable (farG1 X wt sf Lmin) := ((hwm.mul hsfm).mul hKm).indicator measurableSet_Ici
  have hF1m : Measurable fun x => farG1 X wt sf Lmin (Real.log (π ^ 2 * (x / c))) := hG1m.comp hlogm
  have hF2c : Continuous (farF2 c ε) := by
    unfold farF2
    exact (continuous_const.sub (continuous_sWin _ _)).mul
      (continuous_const.add (continuous_const.mul (Real.continuous_cos.comp
        ((continuous_const.mul continuous_id).add continuous_const))))
  have hF1i : Integrable fun x => farG1 X wt sf Lmin (Real.log (π ^ 2 * (x / c))) * gD x :=
    integrable_mul_bdd hint hF1m (fun x => abs_farG1_le hc hw hsf Lmin _)
  have hF2i : Integrable fun x => farF2 c ε x * gD x :=
    integrable_mul_bdd hint hF2c.measurable (fun x => abs_farF2_le hc ε x)
  -- change of variables for the target integral
  have hI : ∫ L in Ici Lmin, wt L * sf L * (hankelHL c f L * boasKernel X L) =
      ∫ x, farG1 X wt sf Lmin (Real.log (π ^ 2 * (x / c))) * gD x := by
    rw [← integral_hankelHL_mul_eq hc0 f (farG1 X wt sf Lmin), ← integral_indicator measurableSet_Ici]
    refine integral_congr_ae (ae_of_all _ fun L => ?_)
    unfold farG1
    by_cases hL : L ∈ Ici Lmin
    · simp only [Set.indicator_of_mem hL]; ring
    · simp only [Set.indicator_of_notMem hL]; ring
  set E : ℝ := 9 * farE1 c + 3 * farE2 c + 2 * Eph with hE
  have habs : ∫ x, |gD x| = 1 := by
    have : ∀ x, |gD x| = (Ioi (0 : ℝ)).indicator (fun s => |f s| * hankelRho0 c s) x := by
      intro x
      by_cases hx : x ∈ Ioi (0 : ℝ)
      · simp only [hgD, hankelDensity, Set.indicator_of_mem hx]
        rw [abs_mul, abs_of_nonneg (hankelRho0_nonneg hc0 (le_of_lt hx))]
      · simp [hgD, hankelDensity, Set.indicator_of_notMem hx]
    simp_rw [this]
    rw [integral_indicator measurableSet_Ioi]
    exact hM
  have hdiffint : Integrable fun x =>
      (farG1 X wt sf Lmin (Real.log (π ^ 2 * (x / c))) - farF2 c ε x) * gD x := by
    refine (hF1i.sub hF2i).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.sub_apply]; ring
  have hlow : -E ≤ ∫ x, (farG1 X wt sf Lmin (Real.log (π ^ 2 * (x / c))) - farF2 c ε x) * gD x := by
    have h1 : ∫ x, (-E) * |gD x| ≤
        ∫ x, (farG1 X wt sf Lmin (Real.log (π ^ 2 * (x / c))) - farF2 c ε x) * gD x := by
      refine integral_mono (hint.abs.const_mul (-E)) hdiffint fun x => ?_
      by_cases hx : 0 < x
      · have h0 := far_pointwise hc hw hsf hwt1 hLmin hEph hphase hx
        have h2 : |(farG1 X wt sf Lmin (Real.log (π ^ 2 * (x / c))) - farF2 c ε x) * gD x| ≤ E * |gD x| := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right h0 (abs_nonneg _)
        have h3 := neg_abs_le ((farG1 X wt sf Lmin (Real.log (π ^ 2 * (x / c))) - farF2 c ε x) * gD x)
        linarith
      · rw [hgD0 x (not_lt.1 hx)]; simp
    rw [integral_const_mul, habs] at h1
    linarith
  have hT' := far_fejer_lower hc hε hf hM hT hn
  have hsplit : ∫ x, farG1 X wt sf Lmin (Real.log (π ^ 2 * (x / c))) * gD x =
      (∫ x, farF2 c ε x * gD x) +
        ∫ x, (farG1 X wt sf Lmin (Real.log (π ^ 2 * (x / c))) - farF2 c ε x) * gD x := by
    rw [← integral_add hF2i hdiffint]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    ring
  rw [hI, hsplit]
  have hEE : boasFarEps c n Eph = boasFarEps c n 0 - (9 * farE1 c + 3 * farE2 c + 2 * 0) + E := by
    unfold boasFarEps; rw [hE]; ring
  rw [hEE]
  linarith

/-- info: 'FormalResearch.SignUncertainty.boas_far_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_far_field

end FormalResearch.SignUncertainty
