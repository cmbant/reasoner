module

public import FormalResearch.SignUncertainty.FctMainHankel
public import FormalResearch.SignUncertainty.CtLowerFinal
public import FormalResearch.SignUncertainty.CeHankelPairFromEigen
public import FormalResearch.SignUncertainty.EuclidRadialProjection
public import FormalResearch.SignUncertainty.HbUpperM1
public import FormalResearch.SignUncertainty.Headlines

/-!
# `thm:ct-upper`: the five-term expansion of the Hankel thresholds and radii (Paper I)

Source: `CFT/sign_uncertainty/paper/general_theorems.tex`, `thm:ct-upper` (= `thm:ct-lower`, `thm:intro-radii`,
`gt:7.9`, `cor:fourier-radii`, `gt:7.12`, `thm:ce-radius`), parts (i) and (ii).

* `IsHankelCEFeasible c T h g`, `hankelTCE c`: the Cohn--Elkies Hankel problem of `fourier_mellin.tex` (`T_c^CE`, the
  infimum of `T` over real continuous mutual Hankel transforms `h, g` of finite `M`, with `h(0) = g(0) > 0`, `g ≥ 0`,
  `h ≤ 0` on `[T, ∞)`; `T ≥ 0` is recorded in the structure, it is forced by `h(0) > 0` and continuity).
* `CtUpperCEInputs`: the three TeX results used and not in Lean, as named fields: `main_ce` (`fct:main-ce`, the CE upper
  bound with nonemptiness), `ce_nonzero_neg` (the nonvanishing of `f = (g - h)/2` in the proof of `T_c^- ≤ T_c^CE`),
  `ce_radius` (`T_c^CE = r_CE(d)²/2`: `gt:7.9b`, radial averaging, `lem:ce-schwartz`).
* `ct_upper`: parts (i), (ii) of the theorem, proved from the unconditional `ct_lower`, `FctMainHankelInputs`
  (`fct_main_hankel`) and `CtUpperCEInputs`; the integer-`d` statements for `A_sign^±` use the proved
  `hankel_euclid_dictionary`, `hankelT0_eq_hankelT`, and the Schwartz/`L¹` radius equality is
  `ce_schwartz_radius_eq_L1_radius`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real FourierTransform

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-! ### The Cohn--Elkies Hankel threshold `T_c^CE` -/

/-- `(h, g)` is a feasible Cohn--Elkies Hankel pair at threshold `T` (`fourier_mellin.tex`): real continuous mutual
Hankel transforms of finite `M`, `h(0) = g(0) > 0`, `g ≥ 0` on `[0, ∞)` and `h ≤ 0` on `[T, ∞)`, `T ≥ 0`. -/
structure IsHankelCEFeasible (c T : ℝ) (h g : ℝ → ℝ) : Prop where
  h_cont : ContinuousOn h (Ici 0)
  g_cont : ContinuousOn g (Ici 0)
  h_int : IntegrableOn (fun Δ => h Δ * hankelRho0 c Δ) (Ioi 0)
  g_int : IntegrableOn (fun Δ => g Δ * hankelRho0 c Δ) (Ioi 0)
  g_eq : ∀ Δ ∈ Ici (0 : ℝ), besselHankelTransform c h Δ = g Δ
  h_eq : ∀ Δ ∈ Ici (0 : ℝ), besselHankelTransform c g Δ = h Δ
  origin : h 0 = g 0
  pos : 0 < g 0
  g_nonneg : ∀ Δ : ℝ, 0 ≤ Δ → 0 ≤ g Δ
  h_tail : ∀ Δ : ℝ, T ≤ Δ → h Δ ≤ 0
  T_nonneg : 0 ≤ T

/-- `T_c^CE`: the infimum of feasible thresholds of Cohn--Elkies Hankel pairs. -/
noncomputable def hankelTCE (c : ℝ) : ℝ := sInf {T : ℝ | ∃ h g, IsHankelCEFeasible c T h g}

/-- The negative projection `f = (g - h)/2` of a Cohn--Elkies Hankel pair is a `(-1)`-eigenfunction. -/
theorem ceFeasible_negProj_eigen {c T : ℝ} {h g : ℝ → ℝ} (hc : 1 / 2 < c) (H : IsHankelCEFeasible c T h g) :
    IsHankelEigenfn c (-1) (fun s => (g s + -h s) / 2) where
  cont := (H.g_cont.add H.h_cont.neg).div_const 2
  int := by
    refine ((H.g_int.add H.h_int.neg).div_const 2).congr
      (ae_restrict_of_forall_mem measurableSet_Ioi fun s _ => ?_)
    simp only [Pi.add_apply, Pi.neg_apply]; ring
  eigen Δ hΔ := by
    have hneg : besselHankelTransform c (fun s => -h s) Δ = -besselHankelTransform c h Δ := by
      unfold besselHankelTransform
      rw [← integral_neg]
      refine integral_congr_ae (ae_of_all _ fun s => ?_)
      simp only; ring
    have hni : IntegrableOn (fun s => -h s * hankelRho0 c s) (Ioi 0) :=
      H.h_int.neg.congr_fun (fun s _ => by simp only [Pi.neg_apply]; ring) measurableSet_Ioi
    rw [besselHankelTransform_half_sum hc H.g_int hni Δ, hneg, H.g_eq Δ hΔ, H.h_eq Δ hΔ]
    ring

/-- `T_c^- ≤ T_c^CE` at the level of feasible sets: a feasible pair at `T` with `g - h ≢ 0` gives a `(-1)`-feasible
eigenfunction at `T`. -/
theorem ceFeasible_negProj_feasible {c T : ℝ} {h g : ℝ → ℝ} (hc : 1 / 2 < c) (H : IsHankelCEFeasible c T h g)
    (hnz : ∃ Δ : ℝ, 0 ≤ Δ ∧ g Δ - h Δ ≠ 0) :
    IsHankelFeasible c (-1) T (fun s => (g s + -h s) / 2) where
  toIsHankelEigenfn := ceFeasible_negProj_eigen hc H
  nonzero := by
    obtain ⟨Δ, hΔ, hne⟩ := hnz
    refine ⟨Δ, hΔ, fun h0 => hne ?_⟩
    linarith
  origin_sign := by simp only [H.origin]; ring_nf; exact le_rfl
  tail_nonneg Δ hΔ := by
    have := H.g_nonneg Δ (le_trans H.T_nonneg hΔ)
    have := H.h_tail Δ hΔ
    linarith

/-! ### Sign-uncertainty radii are nonnegative -/

/-- A sign-uncertainty competitor with `ε f(0) ≤ 0` has radius `R ≥ 0` (otherwise `f ≥ 0` everywhere and
`∫ f = ε f(0) ≤ 0` force `f = 0`). -/
lemma signWitness_radius_nonneg {d : ℕ} {ε R : ℝ} {f : Euc d → ℝ} (hε : ε = 1 ∨ ε = -1)
    (hw : IsSignWitness ε d R f) (h0 : ε * f 0 ≤ 0) : 0 ≤ R := by
  by_contra hR
  push Not at hR
  have hnn : ∀ x, 0 ≤ f x := fun x => hw.tail_nonneg x (by have := norm_nonneg x; linarith)
  have hI : Integrable (fun x : Euc d => (f x : ℂ)) := Complex.ofRealCLM.integrable_comp hw.integrable
  have hεsq : ε * ε = 1 := by rcases hε with h | h <;> simp [h]
  have hre : ∀ y, ((𝓕 (fun x : Euc d => (f x : ℂ)) y).re) = ε * f y := by
    intro y
    rw [hw.fourier_eq y]
    have : (ε : ℂ) * (f y : ℂ) = ((ε * f y : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  have hfc : Continuous f := by
    have hF := continuous_fourier_of_integrable hI
    have : f = fun y => ε * (𝓕 (fun x : Euc d => (f x : ℂ)) y).re := by
      funext y; rw [hre y]; linear_combination (-(f y)) * hεsq
    rw [this]
    exact (Complex.continuous_re.comp hF).const_mul ε
  have hint : ∫ x, f x = ε * f 0 := by
    have h0F : 𝓕 (fun x : Euc d => (f x : ℂ)) 0 = ((∫ x, f x : ℝ) : ℂ) := by
      rw [Real.fourier_eq]; simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]
      exact integral_ofReal
    rw [← hre 0, h0F, Complex.ofReal_re]
  have hz : ∫ x, f x = 0 := le_antisymm (hint ▸ h0) (integral_nonneg hnn)
  have hae : f =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hnn hw.integrable).1 hz
  have hf0 : f = 0 := (Continuous.ae_eq_iff_eq volume hfc continuous_const).1 hae
  obtain ⟨x, hx⟩ := hw.nonzero
  exact hx (by simp [hf0])

/-! ### Elementary estimates -/

/-- `(d/2)^{-a} = 2^a d^{-a}`. -/
lemma half_rpow_neg {d : ℝ} (hd : 0 < d) {a : ℝ} :
    (d / 2) ^ (-a) = 2 ^ a * d ^ (-a) := by
  rw [Real.div_rpow hd.le (by norm_num), Real.rpow_neg hd.le, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  rw [div_inv_eq_mul]
  simp [mul_comm]

lemma two_rpow_le {a b : ℝ} (hab : a ≤ b) : (2 : ℝ) ^ a ≤ 2 ^ b :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) hab

/-- A linear lower bound for `Δ₅^ε(c) - C c⁻¹`. -/
lemma delta5_lin_lower_sharp {c : ℝ} (hc : 1 ≤ c) (ε C : ℝ) :
    c / π ^ 2 - (|ctKappa ε| + |ctD2star ε| + |C|) ≤ ctDelta5 ε c - C * c⁻¹ := by
  have hc0 : 0 < c := by linarith
  have hA : 0 ≤ airyOrderCoeff * c ^ (1 / 3 : ℝ) :=
    mul_nonneg airyOrderCoeff_pos.le (Real.rpow_nonneg hc0.le _)
  have hC1 : 0 ≤ ctC1Langer * c ^ (-(1 / 3) : ℝ) :=
    mul_nonneg (by unfold ctC1Langer; positivity) (Real.rpow_nonneg hc0.le _)
  have hp0 : 0 ≤ c ^ (-(2 / 3) : ℝ) := Real.rpow_nonneg hc0.le _
  have hp1 : c ^ (-(2 / 3) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hc (by norm_num)
  have hd2 : -|ctD2star ε| ≤ ctD2star ε * c ^ (-(2 / 3) : ℝ) := by
    have : |ctD2star ε * c ^ (-(2 / 3) : ℝ)| ≤ |ctD2star ε| := by
      rw [abs_mul, abs_of_nonneg hp0]
      exact mul_le_of_le_one_right (abs_nonneg _) hp1
    linarith [neg_abs_le (ctD2star ε * c ^ (-(2 / 3) : ℝ))]
  have hinv0 : 0 ≤ c⁻¹ := inv_nonneg.2 hc0.le
  have hinv1 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc
  have hCl : C * c⁻¹ ≤ |C| := by
    calc C * c⁻¹ ≤ |C| * c⁻¹ := mul_le_mul_of_nonneg_right (le_abs_self C) hinv0
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hinv1 (abs_nonneg C)
      _ = |C| := mul_one _
  unfold ctDelta5
  linarith [neg_abs_le (ctKappa ε), abs_nonneg (ctKappa ε), abs_nonneg (ctD2star ε), abs_nonneg C]

/-- `Δ₅^{+}(c) - Δ₅^{-}(c) = -1/π + π A c^{-2/3}`. -/
lemma ctDelta5_pos_sub_neg (c : ℝ) :
    ctDelta5 1 c - ctDelta5 (-1) c = -(1 / π) + π * airyOrderCoeff * c ^ (-(2 / 3) : ℝ) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  unfold ctDelta5 ctKappa ctD2star CtOuter.ctTheta1 CtOuter.ctTheta3
  have hne : (-1 : ℝ) ≠ 1 := by norm_num
  simp only [ite_true, hne, ite_false]
  field_simp
  ring

/-! ### The theorem -/

/-- **The TeX results used by `thm:ct-upper` and not in Lean** (`general_theorems.tex`, proof of `thm:ct-upper`).
* `main_ce` (`fct:main-ce`, `constant_terms_five.tex`): the Cohn--Elkies upper bound
  `T_c^CE ≤ Δ₅^-(c) + C c^{-3/4}` for real `c ≥ c₀`, together with nonemptiness of the feasible set.
* `ce_nonzero_neg`: for `c > 1/2` the negative projection `(g - h)/2` of a feasible Cohn--Elkies Hankel pair is not
  identically zero (else `h = g ≥ 0` has compact support by the terminal sign, its Hankel transform is entire,
  `ĥ = h` vanishes on a ray, hence identically, contradicting `h(0) > 0`).
* `ce_radius` (`gt:7.9b`, radial averaging, `lem:ce-schwartz`): `T_{d/2}^CE = r_CE(d)²/2` for integer `d ≥ 2`. -/
structure CtUpperCEInputs : Prop where
  main_ce : ∃ Cp c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c →
    (∃ T h g, IsHankelCEFeasible c T h g) ∧ hankelTCE c ≤ ctDelta5 (-1) c + Cp * c ^ (-(3 / 4 : ℝ))
  ce_nonzero_neg : ∀ {c T : ℝ} {h g : ℝ → ℝ}, 1 / 2 < c → IsHankelCEFeasible c T h g →
    ∃ Δ : ℝ, 0 ≤ Δ ∧ g Δ - h Δ ≠ 0
  ce_radius : ∀ d : ℕ, 2 ≤ d → optimalL1CERadius d ^ 2 / 2 = hankelTCE ((d : ℝ) / 2)

/-- The real-`c` estimates of `thm:ct-upper` (i), with one constant `S`, and the lower bound `T_c^- > c/(4π)`. -/
theorem ct_upper_real (U : FctMainHankelInputs) (E : CtUpperCEInputs) :
    ∃ c₀ S : ℝ, 1 ≤ c₀ ∧ 0 ≤ S ∧ ∀ c : ℝ, c₀ ≤ c →
      (∀ ε : ℝ, (ε = 1 ∨ ε = -1) → (∃ T f, IsHankelFeasible c ε T f) ∧
        ctDelta5 ε c - S * c⁻¹ ≤ hankelT ε c ∧
          hankelT ε c ≤ ctDelta5 ε c + S * c ^ (-(3 / 4 : ℝ))) ∧
      ctDelta5 (-1) c - S * c⁻¹ ≤ hankelTCE c ∧
        hankelTCE c ≤ ctDelta5 (-1) c + S * c ^ (-(3 / 4 : ℝ)) ∧
      hankelT (-1) c ≤ hankelTCE c ∧ hankelTCE c - hankelT (-1) c ≤ S * c ^ (-(3 / 4 : ℝ)) ∧
      c / (4 * π) < hankelT (-1) c := by
  obtain ⟨cL, CL, hL⟩ := ct_lower
  obtain ⟨Cp, cU, -, hU⟩ := fct_main_hankel U
  obtain ⟨CE, cE, hE⟩ := E.main_ce
  obtain ⟨Cu, cH, hH⟩ := hbThresholdsUpper
  set S : ℝ := |Cp| + |CE| + 4 * |CL| with hS
  have hS0 : 0 ≤ S := by positivity
  set B0 : ℝ := |ctKappa 1| + |ctKappa (-1)| + |ctD2star 1| + |ctD2star (-1)| + S with hB0
  have hB0n : 0 ≤ B0 := by positivity
  have hδ : 0 < (4 - π) / (4 * π ^ 2) := by
    have := Real.pi_lt_four
    have := Real.pi_pos
    positivity
  refine ⟨max (max (max cL cU) (max cE cH)) (max 1 (B0 / ((4 - π) / (4 * π ^ 2)) + 1)), S, le_trans (le_max_left 1 _)
    (le_max_right _ _), by positivity, fun c hc => ?_⟩
  have hc1 : 1 ≤ c := le_trans (le_trans (le_max_left 1 _) (le_max_right _ _)) hc
  have hcL : cL ≤ c := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hc
  have hcU : cU ≤ c := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hc
  have hcE : cE ≤ c := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hc
  have hcH : cH ≤ c := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hc
  have hcB : B0 / ((4 - π) / (4 * π ^ 2)) + 1 ≤ c :=
    le_trans (le_trans (le_max_right 1 _) (le_max_right _ _)) hc
  have hc0 : 0 < c := by linarith
  have hinv0 : 0 ≤ c⁻¹ := inv_nonneg.2 hc0.le
  have hinv34 : c⁻¹ ≤ c ^ (-(3 / 4 : ℝ)) := by
    rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hp0 : 0 ≤ c ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hc0.le _
  have hSCL : |CL| ≤ S := by rw [hS]; linarith [abs_nonneg Cp, abs_nonneg CE, abs_nonneg CL]
  have hne : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∃ T f, IsHankelFeasible c ε T f := fun ε hε => by
    obtain ⟨T, f, hf, -⟩ := hH c hcH ε hε; exact ⟨T, f, hf⟩
  have hlow : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ T f, IsHankelFeasible c ε T f →
      ctDelta5 ε c - S * c⁻¹ ≤ T := fun ε hε T f hf => by
    have := hL c hcL ε hε T f hf
    nlinarith [mul_le_mul_of_nonneg_right (le_trans (le_abs_self CL) hSCL) hinv0]
  have hlowT : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      ctDelta5 ε c - S * c⁻¹ ≤ hankelT ε c := fun ε hε =>
    le_csInf (by obtain ⟨T, f, hf⟩ := hne ε hε; exact ⟨T, f, hf⟩)
      fun T ⟨f, hf⟩ => hlow ε hε T f hf
  have hbdd : BddBelow {T : ℝ | ∃ f, IsHankelFeasible c (-1) T f} :=
    ⟨_, fun T ⟨f, hf⟩ => hlow (-1) (Or.inr rfl) T f hf⟩
  obtain ⟨hCEne, hCEup⟩ := hE c hcE
  have hCEne' : {T : ℝ | ∃ h g, IsHankelCEFeasible c T h g}.Nonempty := by
    obtain ⟨T, h, g, H⟩ := hCEne; exact ⟨T, h, g, H⟩
  have hhalf : 1 / 2 < c := by linarith
  have hCEfeas : ∀ T h g, IsHankelCEFeasible c T h g → IsHankelFeasible c (-1) T (fun s => (g s + -h s) / 2) :=
    fun T h g H => ceFeasible_negProj_feasible hhalf H (E.ce_nonzero_neg hhalf H)
  have hCElow : ctDelta5 (-1) c - S * c⁻¹ ≤ hankelTCE c :=
    le_csInf hCEne' fun T ⟨h, g, H⟩ => hlow (-1) (Or.inr rfl) T _ (hCEfeas T h g H)
  have hTle : hankelT (-1) c ≤ hankelTCE c :=
    csInf_le_csInf hbdd hCEne' fun T ⟨h, g, H⟩ => ⟨_, hCEfeas T h g H⟩
  have hCEup' : hankelTCE c ≤ ctDelta5 (-1) c + S * c ^ (-(3 / 4 : ℝ)) := by
    have : CE * c ^ (-(3 / 4 : ℝ)) ≤ S * c ^ (-(3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by rw [hS]; linarith [le_abs_self CE, abs_nonneg Cp, abs_nonneg CL]) hp0
    linarith
  have hT1 : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → hankelT ε c ≤ ctDelta5 ε c + S * c ^ (-(3 / 4 : ℝ)) := by
    intro ε hε
    have h := hU ε c hε hcU
    have : Cp * c ^ (-(3 / 4 : ℝ)) ≤ S * c ^ (-(3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by rw [hS]; linarith [le_abs_self Cp, abs_nonneg CE, abs_nonneg CL]) hp0
    linarith
  -- `T_c^- > c/(4π)`
  have hlin := delta5_lin_lower_sharp hc1 (-1) S
  have hS' : |ctKappa (-1)| + |ctD2star (-1)| + |S| ≤ B0 := by
    rw [hB0, abs_of_nonneg hS0]
    linarith [abs_nonneg (ctKappa 1), abs_nonneg (ctD2star 1)]
  have hδc : B0 < c * ((4 - π) / (4 * π ^ 2)) := by
    have := (div_lt_iff₀ hδ).1 (show B0 / ((4 - π) / (4 * π ^ 2)) < c by linarith)
    exact this
  have hTgt : c / (4 * π) < hankelT (-1) c := by
    have e : c / π ^ 2 - c / (4 * π) = c * ((4 - π) / (4 * π ^ 2)) := by
      have : π ≠ 0 := Real.pi_ne_zero
      field_simp
    linarith [hlowT (-1) (Or.inr rfl)]
  refine ⟨fun ε hε => ⟨hne ε hε, hlowT ε hε, hT1 ε hε⟩, hCElow, hCEup', hTle, ?_, hTgt⟩
  have := hlowT (-1) (Or.inr rfl)
  have := hT1 (-1) (Or.inr rfl)
  have hlowCL : ctDelta5 (-1) c - CL * c⁻¹ ≤ hankelT (-1) c :=
    le_csInf (by obtain ⟨T, f, hf⟩ := hne (-1) (Or.inr rfl); exact ⟨T, f, hf⟩)
      fun T ⟨f, hf⟩ => hL c hcL (-1) (Or.inr rfl) T f hf
  have h4 : CL * c⁻¹ ≤ 4 * |CL| * c ^ (-(3 / 4 : ℝ)) := by
    calc CL * c⁻¹ ≤ |CL| * c⁻¹ := mul_le_mul_of_nonneg_right (le_abs_self CL) hinv0
      _ ≤ |CL| * c ^ (-(3 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hinv34 (abs_nonneg CL)
      _ ≤ 4 * |CL| * c ^ (-(3 / 4 : ℝ)) := by nlinarith [abs_nonneg CL, hp0]
  have h5 : (|CE| + 4 * |CL|) * c ^ (-(3 / 4 : ℝ)) ≤ S * c ^ (-(3 / 4 : ℝ)) :=
    mul_le_mul_of_nonneg_right (by rw [hS]; linarith [abs_nonneg Cp]) hp0
  have h6 : CE * c ^ (-(3 / 4 : ℝ)) ≤ |CE| * c ^ (-(3 / 4 : ℝ)) :=
    mul_le_mul_of_nonneg_right (le_abs_self CE) hp0
  nlinarith

lemma mul_le_mul_right' {a C x : ℝ} (hx : 0 ≤ x) (h : a ≤ C) : a * x ≤ C * x :=
  mul_le_mul_of_nonneg_right h hx

set_option maxHeartbeats 1000000 in
/-- **`thm:ct-upper`** (i)-(ii) (`general_theorems.tex`; = `thm:intro-radii`, `thm:ct-lower`, `gt:7.9`, `cor:fourier-radii`,
`gt:7.12`, `thm:ce-radius`, parts (i), (ii)), proved from unconditional `ct_lower`, under the explicit hypotheses
`FctMainHankelInputs` (`fct_main_hankel`) and `CtUpperCEInputs` (`fct:main-ce` and the two reductions).

(i) For `ε = ±1` and real `c ≥ c₀`: `Δ₅^ε(c) - C c⁻¹ ≤ T_c^ε ≤ Δ₅^ε(c) + C c^{-3/4}`, the same for `T_c^CE` with `ε = -1`,
`0 ≤ T_c^CE - T_c^- ≤ C c^{-3/4}`, and `T_c^{+1} - T_c^{-1} = -1/π + π A c^{-2/3} + O(c^{-3/4})`.
(ii) For integer `d ≥ 2c₀`, `c = d/2`: `½ A_sign^ε(d)² = Δ₅^ε(c) + O(d^{-3/4})`, `½ r_CE(d)² = Δ₅^-(c) + O(d^{-3/4})`,
`0 ≤ r_CE(d)² - A_sign^-(d)² = O(d^{-3/4})`, `0 ≤ r_CE(d) - A_sign^-(d) = O(d^{-5/4})`; the Schwartz radius is
`r_CE(d)` (`ce_schwartz_radius_eq_L1_radius`). -/
theorem ct_upper (U : FctMainHankelInputs) (E : CtUpperCEInputs) :
    ∃ c₀ C : ℝ, 1 ≤ c₀ ∧ 0 < C ∧
    (∀ c : ℝ, c₀ ≤ c →
      (∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
        ctDelta5 ε c - C * c⁻¹ ≤ hankelT ε c ∧
          hankelT ε c ≤ ctDelta5 ε c + C * c ^ (-(3 / 4 : ℝ))) ∧
      (ctDelta5 (-1) c - C * c⁻¹ ≤ hankelTCE c ∧
        hankelTCE c ≤ ctDelta5 (-1) c + C * c ^ (-(3 / 4 : ℝ))) ∧
      (0 ≤ hankelTCE c - hankelT (-1) c ∧ hankelTCE c - hankelT (-1) c ≤ C * c ^ (-(3 / 4 : ℝ))) ∧
      |hankelT 1 c - hankelT (-1) c - (-(1 / π) + π * airyOrderCoeff * c ^ (-(2 / 3 : ℝ)))|
        ≤ C * c ^ (-(3 / 4 : ℝ))) ∧
    (∀ d : ℕ, 2 * c₀ ≤ (d : ℝ) →
      |aSignPos d ^ 2 / 2 - ctDelta5 1 ((d : ℝ) / 2)| ≤ C * (d : ℝ) ^ (-(3 / 4 : ℝ)) ∧
      |aSignNeg d ^ 2 / 2 - ctDelta5 (-1) ((d : ℝ) / 2)| ≤ C * (d : ℝ) ^ (-(3 / 4 : ℝ)) ∧
      |optimalL1CERadius d ^ 2 / 2 - ctDelta5 (-1) ((d : ℝ) / 2)| ≤ C * (d : ℝ) ^ (-(3 / 4 : ℝ)) ∧
      (0 ≤ optimalL1CERadius d ^ 2 - aSignNeg d ^ 2 ∧
        optimalL1CERadius d ^ 2 - aSignNeg d ^ 2 ≤ C * (d : ℝ) ^ (-(3 / 4 : ℝ))) ∧
      (0 ≤ optimalL1CERadius d - aSignNeg d ∧
        optimalL1CERadius d - aSignNeg d ≤ C * (d : ℝ) ^ (-(5 / 4 : ℝ))) ∧
      optimalSchwartzCERadius d = optimalL1CERadius d) := by
  obtain ⟨c₀, S, hc₀, hS, hcore⟩ := ct_upper_real U E
  refine ⟨c₀, 13 * S + 1, hc₀, by linarith, fun c hc => ?_, fun d hd => ?_⟩
  · obtain ⟨hT, hCl, hCu, hle, hdiff, -⟩ := hcore c hc
    have hc1 : 1 ≤ c := le_trans hc₀ hc
    have hc0 : 0 < c := by linarith
    have hinv0 : 0 ≤ c⁻¹ := inv_nonneg.2 hc0.le
    have hinv34 : c⁻¹ ≤ c ^ (-(3 / 4 : ℝ)) := by
      rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have hp0 : 0 ≤ c ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hc0.le _
    have hinvC : S * c⁻¹ ≤ (13 * S + 1) * c⁻¹ :=
      mul_le_mul_right' hinv0 (by linarith)
    have hCp : S * c ^ (-(3 / 4 : ℝ)) ≤ (13 * S + 1) * c ^ (-(3 / 4 : ℝ)) :=
      mul_le_mul_right' hp0 (by linarith)
    have h8 : 8 * S * c ^ (-(3 / 4 : ℝ)) ≤ (13 * S + 1) * c ^ (-(3 / 4 : ℝ)) :=
      mul_le_mul_right' hp0 (by linarith)
    obtain ⟨-, h1l, h1u⟩ := hT 1 (Or.inl rfl)
    obtain ⟨-, h2l, h2u⟩ := hT (-1) (Or.inr rfl)
    have hinvS : S * c⁻¹ ≤ 4 * S * c ^ (-(3 / 4 : ℝ)) := by
      calc S * c⁻¹ ≤ S * c ^ (-(3 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hinv34 hS
        _ ≤ 4 * S * c ^ (-(3 / 4 : ℝ)) := by nlinarith [hS, hp0]
    refine ⟨fun ε hε => ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨by linarith, by linarith⟩, ?_⟩
    · linarith [(hT ε hε).2.1]
    · linarith [(hT ε hε).2.2]
    · linarith
    · linarith
    · have := ctDelta5_pos_sub_neg c
      rw [abs_le]; constructor <;> nlinarith
  · have hc1 : 1 ≤ (d : ℝ) / 2 := by linarith
    have hd2 : 2 ≤ d := by
      have : (2 : ℝ) ≤ d := by linarith
      exact_mod_cast this
    have hd0 : (0 : ℝ) < d := by linarith
    set c : ℝ := (d : ℝ) / 2 with hcdef
    have hc : c₀ ≤ c := by rw [hcdef]; linarith
    obtain ⟨hT, hCl, hCu, hle, hdiff, hgt⟩ := hcore c hc
    have hc0 : 0 < c := by linarith
    have hinv34 : c⁻¹ ≤ c ^ (-(3 / 4 : ℝ)) := by
      rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have hp0 : 0 ≤ c ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hc0.le _
    have hinvS : S * c⁻¹ ≤ 4 * S * c ^ (-(3 / 4 : ℝ)) := by
      calc S * c⁻¹ ≤ S * c ^ (-(3 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hinv34 hS
        _ ≤ 4 * S * c ^ (-(3 / 4 : ℝ)) := by nlinarith [hS, hp0]
    -- conversion `c^{-a} = 2^a d^{-a}`
    have hc34 : c ^ (-(3 / 4 : ℝ)) ≤ 2 * (d : ℝ) ^ (-(3 / 4 : ℝ)) := by
      rw [hcdef, half_rpow_neg hd0]
      exact mul_le_mul_of_nonneg_right (by simpa using two_rpow_le (show (3 / 4 : ℝ) ≤ 1 by norm_num))
        (Real.rpow_nonneg hd0.le _)
    have hc54 : c ^ (-(5 / 4 : ℝ)) ≤ 4 * (d : ℝ) ^ (-(5 / 4 : ℝ)) := by
      rw [hcdef, half_rpow_neg hd0]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hd0.le _)
      calc (2 : ℝ) ^ (5 / 4 : ℝ) ≤ 2 ^ (2 : ℝ) := two_rpow_le (by norm_num)
        _ = 4 := by norm_num
    have hd34 : 0 ≤ (d : ℝ) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hd0.le _
    have hd54 : 0 ≤ (d : ℝ) ^ (-(5 / 4 : ℝ)) := Real.rpow_nonneg hd0.le _
    obtain ⟨-, h1l, h1u⟩ := hT 1 (Or.inl rfl)
    obtain ⟨-, h2l, h2u⟩ := hT (-1) (Or.inr rfl)
    obtain ⟨hp, hn⟩ := hankel_euclid_dictionary d hd2
    have hT0 : hankelT0 c = hankelT (-1) c := by
      refine hankelT0_eq_hankelT hc0 (bessel_kernel_data c hc1) (laguerre_odd_mode (by linarith))
        (hT (-1) (Or.inr rfl)).1 hgt
    have hrad := E.ce_radius d hd2
    rw [← hcdef] at hp hn hrad
    rw [hT0] at hn
    -- abs bounds
    have habs : ∀ x D : ℝ, D - S * c⁻¹ ≤ x → x ≤ D + S * c ^ (-(3 / 4 : ℝ)) →
        |x - D| ≤ (13 * S + 1) * (d : ℝ) ^ (-(3 / 4 : ℝ)) := by
      intro x D h1 h2
      have : 8 * S * (d : ℝ) ^ (-(3 / 4 : ℝ)) ≤ (13 * S + 1) * (d : ℝ) ^ (-(3 / 4 : ℝ)) :=
        mul_le_mul_right' hd34 (by linarith)
      have h3 : S * c ^ (-(3 / 4 : ℝ)) ≤ 2 * S * (d : ℝ) ^ (-(3 / 4 : ℝ)) := by
        calc S * c ^ (-(3 / 4 : ℝ)) ≤ S * (2 * (d : ℝ) ^ (-(3 / 4 : ℝ))) := mul_le_mul_of_nonneg_left hc34 hS
          _ = 2 * S * (d : ℝ) ^ (-(3 / 4 : ℝ)) := by ring
      have h4 : 4 * S * c ^ (-(3 / 4 : ℝ)) ≤ 8 * S * (d : ℝ) ^ (-(3 / 4 : ℝ)) := by
        calc 4 * S * c ^ (-(3 / 4 : ℝ)) ≤ 4 * S * (2 * (d : ℝ) ^ (-(3 / 4 : ℝ))) :=
              mul_le_mul_of_nonneg_left hc34 (by linarith)
          _ = 8 * S * (d : ℝ) ^ (-(3 / 4 : ℝ)) := by ring
      rw [abs_le]; constructor <;> linarith
    have hA : 0 ≤ aSignNeg d := by
      refine Real.sInf_nonneg ?_
      rintro R ⟨f, hw, hf0⟩
      exact signWitness_radius_nonneg (Or.inr rfl) hw (by rw [hf0]; simp)
    have hR : 0 ≤ optimalL1CERadius d := by
      refine Real.sInf_nonneg ?_
      rintro R ⟨h, hh⟩
      exact hh.r_pos.le
    have hsq : optimalL1CERadius d ^ 2 - aSignNeg d ^ 2 = 2 * (hankelTCE c - hankelT (-1) c) := by
      have h1 : optimalL1CERadius d ^ 2 = 2 * hankelTCE c := by linarith
      have h2 : aSignNeg d ^ 2 = 2 * hankelT (-1) c := by linarith
      rw [h1, h2]; ring
    have h2c : 2 * (S * c ^ (-(3 / 4 : ℝ))) ≤ (13 * S + 1) * (d : ℝ) ^ (-(3 / 4 : ℝ)) := by
      have : S * c ^ (-(3 / 4 : ℝ)) ≤ 2 * S * (d : ℝ) ^ (-(3 / 4 : ℝ)) := by
        calc S * c ^ (-(3 / 4 : ℝ)) ≤ S * (2 * (d : ℝ) ^ (-(3 / 4 : ℝ))) := mul_le_mul_of_nonneg_left hc34 hS
          _ = 2 * S * (d : ℝ) ^ (-(3 / 4 : ℝ)) := by ring
      have h5 : 4 * S * (d : ℝ) ^ (-(3 / 4 : ℝ)) ≤ (13 * S + 1) * (d : ℝ) ^ (-(3 / 4 : ℝ)) :=
        mul_le_mul_right' hd34 (by linarith)
      linarith
    have hsq0 : 0 ≤ optimalL1CERadius d ^ 2 - aSignNeg d ^ 2 := by rw [hsq]; linarith [hle]
    have hsq1 : optimalL1CERadius d ^ 2 - aSignNeg d ^ 2 ≤ (13 * S + 1) * (d : ℝ) ^ (-(3 / 4 : ℝ)) := by
      rw [hsq]; linarith [hdiff]
    refine ⟨?_, ?_, ?_, ⟨hsq0, hsq1⟩, ⟨?_, ?_⟩, ce_schwartz_radius_eq_L1_radius (by omega)⟩
    · rw [hp]; exact habs _ _ h1l h1u
    · rw [hn]; exact habs _ _ h2l h2u
    · rw [hrad]; exact habs _ _ hCl hCu
    · by_contra hlt
      push Not at hlt
      have := mul_self_lt_mul_self hR (by linarith : optimalL1CERadius d < aSignNeg d)
      nlinarith
    · -- `a ≥ √c / 3`
      have ha2 : c / 9 ≤ aSignNeg d ^ 2 := by
        have : c / (4 * π) < hankelT (-1) c := hgt
        have h3 : 2 * π ≤ 9 := by linarith [Real.pi_lt_four]
        have h4 : c / 9 ≤ c / (2 * π) := by
          apply div_le_div_of_nonneg_left hc0.le (by positivity) h3
        have h5 : c / (2 * π) = 2 * (c / (4 * π)) := by
          have := Real.pi_ne_zero
          field_simp; ring
        have : aSignNeg d ^ 2 = 2 * hankelT (-1) c := by linarith
        linarith
      have hsc := Real.sq_sqrt hc0.le
      have hsc0 := Real.sqrt_pos.2 hc0
      have ha3 : Real.sqrt c / 3 ≤ aSignNeg d := by
        by_contra hlt
        push Not at hlt
        have h1 := mul_self_lt_mul_self hA hlt
        have h2 := Real.mul_self_sqrt hc0.le
        linarith
      have hmain : (optimalL1CERadius d - aSignNeg d) * (2 * Real.sqrt c / 3) ≤
          2 * (S * c ^ (-(3 / 4 : ℝ))) := by
        have hrA : 0 ≤ optimalL1CERadius d - aSignNeg d := by
          by_contra hlt; push Not at hlt
          have := mul_self_lt_mul_self hR (by linarith : optimalL1CERadius d < aSignNeg d)
          nlinarith
        have : (optimalL1CERadius d - aSignNeg d) * (2 * Real.sqrt c / 3) ≤
            (optimalL1CERadius d - aSignNeg d) * (optimalL1CERadius d + aSignNeg d) :=
          mul_le_mul_of_nonneg_left (by linarith) hrA
        have h2 : (optimalL1CERadius d - aSignNeg d) * (optimalL1CERadius d + aSignNeg d) =
            optimalL1CERadius d ^ 2 - aSignNeg d ^ 2 := by ring
        rw [h2, hsq] at this
        have h6 : S * c ^ (-(3 / 4 : ℝ)) ≥ hankelTCE c - hankelT (-1) c := by linarith [hdiff]
        linarith
      have hexp : Real.sqrt c * c ^ (-(5 / 4 : ℝ)) = c ^ (-(3 / 4 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hc0]; norm_num
      have hq : optimalL1CERadius d - aSignNeg d ≤ 3 * S * c ^ (-(5 / 4 : ℝ)) := by
        by_contra hlt
        push Not at hlt
        have hpos : 0 ≤ c ^ (-(5 / 4 : ℝ)) := Real.rpow_nonneg hc0.le _
        have : 3 * S * c ^ (-(5 / 4 : ℝ)) * (2 * Real.sqrt c / 3) <
            (optimalL1CERadius d - aSignNeg d) * (2 * Real.sqrt c / 3) :=
          mul_lt_mul_of_pos_right hlt (by positivity)
        have e : 3 * S * c ^ (-(5 / 4 : ℝ)) * (2 * Real.sqrt c / 3) = 2 * (S * c ^ (-(3 / 4 : ℝ))) := by
          rw [← hexp]; ring
        linarith
      have : 3 * S * c ^ (-(5 / 4 : ℝ)) ≤ (13 * S + 1) * (d : ℝ) ^ (-(5 / 4 : ℝ)) := by
        calc 3 * S * c ^ (-(5 / 4 : ℝ)) ≤ 3 * S * (4 * (d : ℝ) ^ (-(5 / 4 : ℝ))) :=
              mul_le_mul_of_nonneg_left hc54 (by linarith)
          _ = 12 * S * (d : ℝ) ^ (-(5 / 4 : ℝ)) := by ring
          _ ≤ (13 * S + 1) * (d : ℝ) ^ (-(5 / 4 : ℝ)) := mul_le_mul_right' hd54 (by linarith)
      linarith

/-- info: 'FormalResearch.SignUncertainty.ct_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_upper

end FormalResearch.SignUncertainty
