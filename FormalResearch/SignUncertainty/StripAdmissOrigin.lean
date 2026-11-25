module

public import FormalResearch.SignUncertainty.StripAdmissLift
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import FormalResearch.SignUncertainty.MellinMajorant

/-!
# `uct:admiss`, the value at the origin

Source: `CFT/sign_uncertainty/paper/mellin_airy_toolkit.tex`, Lemma T.7 (`mat:T7`) (a), proof of the value at `0`: subtract `W̃(1) Γ(z)`, the Mellin transform of `W̃(1) e^{-Δ}`,
shift the line to `Re z = 0` (the difference is `O(|z|^{α-1})` near `z = 0`, an integrable singularity) and apply the Riemann-Lebesgue lemma.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-! ### Elementary Gamma bounds -/

/-- `|Γ(s)| ≤ Γ(Re s)` for `Re s > 0`. -/
lemma norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) : ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs, Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
  simp

lemma Gamma_add_one_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : Real.Gamma (x + 1) ≤ 1 := by
  have h := Real.convexOn_Gamma.2 (by norm_num : (1 : ℝ) ∈ Ioi 0) (by norm_num : (2 : ℝ) ∈ Ioi 0)
    (by linarith : 0 ≤ 1 - x) hx0 (by ring)
  have e : (1 - x) • (1 : ℝ) + x • (2 : ℝ) = x + 1 := by simp; ring
  rw [e] at h
  have h2 : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one one_ne_zero, Real.Gamma_one]; norm_num
  simp only [smul_eq_mul, Real.Gamma_one, h2, mul_one] at h
  linarith

lemma Gamma_add_two_le_two {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : Real.Gamma (x + 2) ≤ 2 := by
  have h1 : Real.Gamma (x + 1 + 1) = (x + 1) * Real.Gamma (x + 1) := Real.Gamma_add_one (by linarith)
  have h2 := Gamma_add_one_le_one hx0 hx1
  have h3 : 0 < Real.Gamma (x + 1) := Real.Gamma_pos_of_pos (by linarith)
  rw [show x + 2 = x + 1 + 1 by ring, h1]
  nlinarith

/-- `|Γ(z)| ≤ 1/|z|` on `0 < Re z ≤ 1`. -/
lemma norm_Gamma_le_inv {z : ℂ} (h0 : 0 < z.re) (h1 : z.re ≤ 1) : ‖Complex.Gamma z‖ ≤ 1 / ‖z‖ := by
  have hz : z ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have := Complex.Gamma_add_one z hz
  have hb := norm_Gamma_le_Gamma_re (s := z + 1) (by simp; linarith)
  simp only [Complex.add_re, Complex.one_re] at hb
  have hb2 := hb.trans (Gamma_add_one_le_one h0.le h1)
  rw [le_div_iff₀ hz0]
  have : ‖Complex.Gamma (z + 1)‖ = ‖z‖ * ‖Complex.Gamma z‖ := by rw [this, norm_mul]
  linarith

/-- `|Γ(z)| ≤ 2/(|z||z+1|)` on `0 < Re z ≤ 1`. -/
lemma norm_Gamma_le_inv_sq {z : ℂ} (h0 : 0 < z.re) (h1 : z.re ≤ 1) :
    ‖Complex.Gamma z‖ ≤ 2 / (‖z‖ * ‖z + 1‖) := by
  have hz : z ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hz1 : z + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hz10 : 0 < ‖z + 1‖ := norm_pos_iff.mpr hz1
  have e1 := Complex.Gamma_add_one z hz
  have e2 := Complex.Gamma_add_one (z + 1) hz1
  have hb := norm_Gamma_le_Gamma_re (s := z + 1 + 1) (by simp; linarith)
  simp only [Complex.add_re, Complex.one_re] at hb
  have hb2 : ‖Complex.Gamma (z + 1 + 1)‖ ≤ 2 :=
    hb.trans (by have := Gamma_add_two_le_two h0.le h1; rwa [show z.re + 2 = z.re + 1 + 1 by ring] at this)
  rw [le_div_iff₀ (mul_pos hz0 hz10)]
  have : ‖Complex.Gamma (z + 1 + 1)‖ = ‖z + 1‖ * (‖z‖ * ‖Complex.Gamma z‖) := by
    rw [e2, e1, norm_mul, norm_mul]
  nlinarith

lemma norm_le_norm_add_one {z : ℂ} (h : 0 ≤ z.re) : ‖z‖ ≤ ‖z + 1‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im]
  nlinarith

/-! ### The inverse Mellin transform of `Γ` -/

lemma continuous_Gamma_line (σ : ℝ) (hσ : 0 < σ) :
    Continuous fun y : ℝ => Complex.Gamma ((σ : ℂ) + (y : ℂ) * Complex.I) := by
  refine continuous_iff_continuousAt.mpr fun y => ?_
  have hne : ∀ m : ℕ, (σ : ℂ) + (y : ℂ) * Complex.I ≠ -m := fun m h => by
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h1 : ContinuousAt (fun y : ℝ => (σ : ℂ) + (y : ℂ) * Complex.I) y := by fun_prop
  exact (Complex.differentiableAt_Gamma _ hne).continuousAt.comp (f := fun y : ℝ => (σ : ℂ) + (y : ℂ) * Complex.I) h1

lemma integrable_Gamma_line_one : Integrable fun y : ℝ => Complex.Gamma ((1 : ℝ) + (y : ℂ) * Complex.I) := by
  have hmeas : AEStronglyMeasurable (fun y : ℝ => Complex.Gamma ((1 : ℝ) + (y : ℂ) * Complex.I)) volume :=
    (continuous_Gamma_line 1 one_pos).aestronglyMeasurable
  refine (integrable_inv_one_add_sq.const_mul 2).mono' hmeas (Eventually.of_forall fun y => ?_)
  have hz0 : 0 < ((1 : ℂ) + (y : ℂ) * Complex.I).re := by simp
  have hz1 : ((1 : ℂ) + (y : ℂ) * Complex.I).re ≤ 1 := by simp
  have h := norm_Gamma_le_inv_sq hz0 hz1
  set z : ℂ := (1 : ℂ) + (y : ℂ) * Complex.I with hz
  have hn : ‖z‖ ^ 2 = 1 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [hz]; ring
  have hge : ‖z‖ ≤ ‖z + 1‖ := norm_le_norm_add_one hz0.le
  have hzpos : 0 < ‖z‖ := by
    have : 0 < ‖z‖ ^ 2 := by rw [hn]; positivity
    exact lt_of_le_of_ne (norm_nonneg _) (fun h0 => by rw [← h0] at this; simp at this)
  refine h.trans ?_
  have : 2 / (‖z‖ * ‖z + 1‖) ≤ 2 / ‖z‖ ^ 2 := by
    refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
    rw [pow_two]; exact mul_le_mul_of_nonneg_left hge (norm_nonneg _)
  refine this.trans (le_of_eq ?_)
  rw [hn]; ring

/-- The inverse Mellin transform of `Γ` along `Re z = 1` is `e^{-Δ}` (Mellin inversion for `t ↦ e^{-t}`; used to subtract the pole `W̃(1) Γ(z)` of `Φ_W` at `z = 0`). -/
theorem mellinInv_one_Gamma {Δ : ℝ} (hΔ : 0 < Δ) : mellinInv 1 Complex.Gamma Δ = ((Real.exp (-Δ) : ℝ) : ℂ) := by
  set f : ℝ → ℂ := fun t => ((Real.exp (-t) : ℝ) : ℂ) with hf
  have hmel : ∀ s : ℂ, 0 < s.re → mellin f s = Complex.Gamma s := fun s hs => by
    rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral_eq_mellin]
  have hconv : MellinConvergent f 1 := by
    have := Complex.GammaIntegral_convergent (s := 1) (by simp)
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp [hf, mul_comm]
  have hvert : Complex.VerticalIntegrable (mellin f) 1 := by
    unfold Complex.VerticalIntegrable
    refine integrable_Gamma_line_one.congr (Eventually.of_forall fun y => ?_)
    simp only
    rw [hmel _ (by simp)]
  have hcont : ContinuousAt f Δ := by
    simp only [hf]; fun_prop
  have := mellinInv_mellin_eq 1 f hΔ hconv hvert hcont
  rw [show ((Real.exp (-Δ) : ℝ) : ℂ) = f Δ from rfl, ← this]
  unfold mellinInv
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [hmel _ (by simp)]

/-! ### The subtracted multiplier `R = Φ_W - W̃(1) Γ` -/

lemma continuousOn_Gamma_strip {b : ℝ} : ContinuousOn Complex.Gamma {z : ℂ | 0 < z.re ∧ z.re < b} := fun z hz =>
  (Complex.differentiableAt_Gamma z (fun m h => by
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith [hz.1])).continuousAt.continuousWithinAt

/-- `|Γ(z)| ≤ B (1 + |Im z|)^{-2}` on `a ≤ Re z ≤ b`, `0 < a`. -/
lemma Gamma_decay_strip {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ B : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖Complex.Gamma z‖ ≤ B * (1 + |z.im|) ^ (-(2 : ℝ)) := by
  obtain ⟨M1, hM1⟩ := exists_bound_rect (continuousOn_Gamma_strip (b := b + 1)) ha hab (by linarith)
  have hcont : ContinuousOn Real.Gamma (Icc (a + 2) (b + 2)) := fun x hx =>
    (Real.differentiableAt_Gamma (fun m h => by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith [hx.1])).continuousAt.continuousWithinAt
  obtain ⟨M2, hM2⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨4 * |M1| + 4 * |M2|, fun z hz1 hz2 => ?_⟩
  have hz0 : 0 < z.re := by linarith
  have hw0 : 0 ≤ (1 + |z.im|) ^ (-(2 : ℝ)) := by positivity
  rcases le_total |z.im| 1 with hy | hy
  · have h1 := hM1 z hz1 hz2 hy
    have h4 : (1 / 4 : ℝ) ≤ (1 + |z.im|) ^ (-(2 : ℝ)) := by
      have : (2 : ℝ) ^ (-(2 : ℝ)) ≤ (1 + |z.im|) ^ (-(2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith [abs_nonneg z.im]) (by linarith) (by norm_num)
      have e : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
        rw [Real.rpow_neg (by norm_num)]; norm_num
      rwa [e] at this
    have := le_abs_self M1
    nlinarith [abs_nonneg M1, abs_nonneg M2]
  · -- `|Γ z| ≤ Γ(Re z + 2) / (|z| |z + 1|)`
    have hz : z ≠ 0 := fun h => by rw [h] at hz0; simp at hz0
    have hz1' : z + 1 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have e1 := Complex.Gamma_add_one z hz
    have e2 := Complex.Gamma_add_one (z + 1) hz1'
    have hb := norm_Gamma_le_Gamma_re (s := z + 1 + 1) (by simp; linarith)
    simp only [Complex.add_re, Complex.one_re] at hb
    have hGM : Real.Gamma (z.re + 1 + 1) ≤ |M2| := by
      have := hM2 (z.re + 1 + 1) ⟨by linarith, by linarith⟩
      rw [Real.norm_eq_abs] at this
      exact ((le_abs_self _).trans this).trans (le_abs_self M2)
    have hy2 : 1 ≤ |z.im| := hy
    have hnz : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    have hnz1 : |z.im| ≤ ‖z + 1‖ := by simpa using Complex.abs_im_le_norm (z + 1)
    have hprod : |z.im| ^ 2 ≤ ‖z‖ * ‖z + 1‖ := by rw [pow_two]; exact mul_le_mul hnz hnz1 (abs_nonneg _) (norm_nonneg _)
    have hG : ‖Complex.Gamma (z + 1 + 1)‖ = ‖z + 1‖ * (‖z‖ * ‖Complex.Gamma z‖) := by
      rw [e2, e1, norm_mul, norm_mul]
    have hbound : ‖Complex.Gamma z‖ * |z.im| ^ 2 ≤ |M2| := by
      have h0 : 0 ≤ ‖Complex.Gamma z‖ := norm_nonneg _
      calc ‖Complex.Gamma z‖ * |z.im| ^ 2 ≤ ‖Complex.Gamma z‖ * (‖z‖ * ‖z + 1‖) :=
            mul_le_mul_of_nonneg_left hprod h0
        _ = ‖Complex.Gamma (z + 1 + 1)‖ := by rw [hG]; ring
        _ ≤ |M2| := hb.trans hGM
    have hw : (1 + |z.im|) ^ (-(2 : ℝ)) ≥ 1 / (4 * |z.im| ^ 2) := by
      have h1 : (1 + |z.im|) ≤ 2 * |z.im| := by linarith
      have : (2 * |z.im|) ^ (-(2 : ℝ)) ≤ (1 + |z.im|) ^ (-(2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
      refine le_trans (le_of_eq ?_) this
      rw [Real.rpow_neg (by positivity), Real.rpow_two, mul_pow]
      field_simp
      norm_num
    have hy0 : 0 < |z.im| ^ 2 := by positivity
    have : ‖Complex.Gamma z‖ ≤ |M2| / |z.im| ^ 2 := by rw [le_div_iff₀ hy0]; exact hbound
    calc ‖Complex.Gamma z‖ ≤ |M2| / |z.im| ^ 2 := this
      _ = 4 * |M2| * (1 / (4 * |z.im| ^ 2)) := by field_simp
      _ ≤ 4 * |M2| * (1 + |z.im|) ^ (-(2 : ℝ)) := mul_le_mul_of_nonneg_left hw (by positivity)
      _ ≤ _ := by nlinarith [abs_nonneg M1, abs_nonneg M2]

/-- `R = Φ_W - W̃(1) Γ`. -/
noncomputable def admissRem (c : ℝ) (W : ℂ → ℂ) (z : ℂ) : ℂ := admissPhi c W z - W 1 * Complex.Gamma z

lemma W_one_conj_of_W1 {η : ℝ} (hW : StripW1 η W) : starRingEnd ℂ (W 1) = W 1 := by
  have := hW.real 1 (by simp) (by simp)
  simpa using this.symm

lemma W_one_conj (hW : StripM1 W) : starRingEnd ℂ (W 1) = W 1 :=
  W_one_conj_of_W1 hW.toStripW1

/-- `R` satisfies the hypotheses of the Mellin hub under `(W1)` (`c ≥ 2`, `η > 0`). -/
theorem admissRem_mellinLiftData_of_W1 {c η : ℝ} (hc : 2 ≤ c) (hη : 0 < η) (hW : StripW1 η W) :
    MellinLiftData c (admissRem c W) where
  hol := by
    refine (admissPhi_differentiableOn_of_W1 (by linarith) hW).sub ?_
    intro z hz
    exact (((Complex.differentiableAt_Gamma z (fun m h => by
      have := congrArg Complex.re h
      simp at this
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith [hz.1])).const_mul (W 1))).differentiableWithinAt
  decay := by
    intro a b ha hab hb
    obtain ⟨p, hp, B1, hB1⟩ := (admissPhi_mellinLiftData_of_W1 (by linarith) hη hW).decay ha hab hb
    obtain ⟨B2, hB2⟩ := Gamma_decay_strip ha hab
    set q : ℝ := min p 2 with hq
    have hq1 : 1 < q := lt_min hp (by norm_num)
    refine ⟨q, hq1, |B1| + ‖W 1‖ * |B2|, fun z hz1 hz2 => ?_⟩
    unfold admissRem
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have h1 := hB1 z hz1 hz2
    have h2 := hB2 z hz1 hz2
    have hpq : (1 + |z.im|) ^ (-p) ≤ (1 + |z.im|) ^ (-q) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg z.im]) (by linarith [min_le_left p 2])
    have h2q : (1 + |z.im|) ^ (-(2 : ℝ)) ≤ (1 + |z.im|) ^ (-q) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg z.im]) (by linarith [min_le_right p 2])
    have h1' : ‖admissPhi c W z‖ ≤ |B1| * (1 + |z.im|) ^ (-q) :=
      h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self B1) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hpq (abs_nonneg B1)))
    have h2' : ‖Complex.Gamma z‖ ≤ |B2| * (1 + |z.im|) ^ (-q) :=
      h2.trans ((mul_le_mul_of_nonneg_right (le_abs_self B2) (by positivity)).trans
        (mul_le_mul_of_nonneg_left h2q (abs_nonneg B2)))
    have h2'' := mul_le_mul_of_nonneg_left h2' (norm_nonneg (W 1))
    nlinarith
  real := by
    intro z hz0 hz1
    unfold admissRem
    rw [map_sub, map_mul, W_one_conj_of_W1 hW, Complex.Gamma_conj,
      (admissPhi_mellinLiftData_of_W1 (by linarith) hη hW).real z hz0 hz1]

/-- `R` satisfies the hypotheses of the Mellin hub. -/
theorem admissRem_mellinLiftData {c : ℝ} (hc : 2 ≤ c) (hW : StripM1 W) : MellinLiftData c (admissRem c W) :=
  admissRem_mellinLiftData_of_W1 hc (by norm_num) hW.toStripW1

lemma integrable_Gamma_line_cpow {Δ : ℝ} (hΔ : 0 < Δ) :
    Integrable fun y : ℝ => (Δ : ℂ) ^ (-(((1 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) * Complex.Gamma (((1 : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
  have hcont : Continuous fun y : ℝ => (Δ : ℂ) ^ (-(((1 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) *
      Complex.Gamma (((1 : ℝ) : ℂ) + (y : ℂ) * Complex.I) :=
    (Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hΔ.ne'))).mul (continuous_Gamma_line 1 one_pos)
  refine (integrable_Gamma_line_one.norm.const_mul (Δ ^ (-(1 : ℝ)))).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [norm_mul, norm_cpow_line hΔ]

/-- For every line `0 < ε ≤ 1`: `f_W(Δ) = W(1) e^{-Δ} + (inverse Mellin transform of `R` along `Re z = ε`)` under `(W1)`. -/
theorem admiss_lift_eq_sub_of_W1 {c η : ℝ} (hc : 2 ≤ c) (hη : 0 < η) (hW : StripW1 η W)
    {Δ : ℝ} (hΔ : 0 < Δ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ((admissLift c W Δ : ℝ) : ℂ) = W 1 * ((Real.exp (-Δ) : ℝ) : ℂ) + mellinInv ε (admissRem c W) Δ := by
  have hc1 : 1 ≤ c := by linarith
  have hΦ := admissPhi_mellinLiftData_of_W1 hc1 hη hW
  have hR := admissRem_mellinLiftData_of_W1 hc hη hW
  have e1 : ((admissLift c W Δ : ℝ) : ℂ) = mellinInv 1 (admissPhi c W) Δ :=
    ofReal_liftFun hΦ (x₀ := c / 2) (x := 1) (by linarith) (by linarith) one_pos (by linarith) hΔ
  rw [e1, hR.mellinInv_indep hε0 (by linarith) one_pos (by linarith) hΔ]
  have hI1 := hΦ.integrable_line_cpow (x := 1) (Δ := Δ) one_pos (by linarith) hΔ
  have hI2 := integrable_Gamma_line_cpow hΔ
  have hGam := mellinInv_one_Gamma hΔ
  unfold mellinInv at hGam ⊢
  have key : (∫ y : ℝ, (Δ : ℂ) ^ (-(((1 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) • admissRem c W (((1 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) =
      (∫ y : ℝ, (Δ : ℂ) ^ (-(((1 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) • admissPhi c W (((1 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) -
      W 1 * ∫ y : ℝ, (Δ : ℂ) ^ (-(((1 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) * Complex.Gamma (((1 : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
    rw [← integral_const_mul, ← integral_sub hI1 (hI2.const_mul (W 1))]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [admissRem, smul_eq_mul]
    ring
  rw [key, Complex.real_smul, Complex.real_smul]
  simp only [Complex.real_smul, smul_eq_mul] at hGam ⊢
  rw [mul_sub, ← hGam]
  ring

/-- For every line `0 < ε ≤ 1`: `f_W(Δ) = W̃(1) e^{-Δ} + (inverse Mellin transform of `R = Φ_W - W̃(1) Γ` along `Re z = ε`). -/
theorem admiss_lift_eq_sub {c : ℝ} (hc : 2 ≤ c) (hW : StripM1 W) {Δ : ℝ} (hΔ : 0 < Δ) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) :
    ((admissLift c W Δ : ℝ) : ℂ) = W 1 * ((Real.exp (-Δ) : ℝ) : ℂ) + mellinInv ε (admissRem c W) Δ :=
  admiss_lift_eq_sub_of_W1 hc (by norm_num) hW.toStripW1 hΔ hε0 hε1

/-! ### The pole of `Φ_W` at `z = 0`: `Φ_W = Γ · (Ê W̃(1 - z/c))` with `Ê` holomorphic near `0` -/

/-- `Ê(z) = (2π)^{-z} e^{cℋ(z/c)}`, holomorphic on `-c < Re z < 2c`, `Ê(0) = 1`. -/
noncomputable def admissEhat (c : ℝ) (z : ℂ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) ^ (-z) * Complex.exp ((c : ℂ) * hInt (z / c))

lemma admissG_eq_Ehat {c : ℝ} (hc : 0 < c) {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < c) :
    admissG c z = Complex.Gamma z * admissEhat c z := by
  have hre0 : 0 < (z / (c : ℂ)).re := by rw [Complex.div_ofReal_re]; positivity
  have hre1 : (z / (c : ℂ)).re < 1 := by rw [Complex.div_ofReal_re]; exact (div_lt_one hc).mpr hz1
  have e : stripH (1 - z / c) = hInt (z / c) := by
    rw [stripH_one_sub hre0 hre1, hInt_eq_stripH hre0.le hre1]
  unfold admissG admissEhat
  rw [e]; ring

lemma admissEhat_zero (c : ℝ) : admissEhat c 0 = 1 := by
  simp [admissEhat, hInt_zero]

lemma admissEhat_differentiableOn {c : ℝ} (hc : 0 < c) :
    DifferentiableOn ℂ (admissEhat c) {z : ℂ | -c < z.re ∧ z.re < 2 * c} := by
  have hb : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < 2 * Real.pi := by positivity
    exact_mod_cast this.ne'
  intro z hz
  have hmem : z / (c : ℂ) ∈ hStrip := by
    rw [hStrip]
    show -1 < (z / (c : ℂ)).re ∧ (z / (c : ℂ)).re < 2
    rw [Complex.div_ofReal_re]
    constructor
    · rw [lt_div_iff₀ hc]; linarith [hz.1]
    · rw [div_lt_iff₀ hc]; linarith [hz.2]
  have h1 : DifferentiableAt ℂ (fun z : ℂ => hInt (z / c)) z :=
    DifferentiableAt.comp (g := hInt) (f := fun w : ℂ => w / (c : ℂ)) z
      (differentiableOn_hInt.differentiableAt (isOpen_hStrip.mem_nhds hmem)) (differentiableAt_id.div_const _)
  have h2 : DifferentiableAt ℂ (fun z : ℂ => ((2 * Real.pi : ℝ) : ℂ) ^ (-z)) z :=
    (differentiableAt_id.neg).const_cpow (Or.inl hb)
  exact (h2.mul (h1.const_mul (c : ℂ)).cexp).differentiableWithinAt

lemma admissEhat_continuousOn {c : ℝ} (hc : 0 < c) :
    ContinuousOn (admissEhat c) {z : ℂ | 0 ≤ z.re ∧ z.re ≤ c} :=
  (admissEhat_differentiableOn hc).continuousOn.mono fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩

/-- `Ê` is Lipschitz at `0`. -/
lemma admissEhat_lip {c : ℝ} (hc : 0 < c) : ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ < δ →
    ‖admissEhat c z - 1‖ ≤ C * ‖z‖ := by
  have hopen : IsOpen {z : ℂ | -c < z.re ∧ z.re < 2 * c} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
  have hd : DifferentiableAt ℂ (admissEhat c) 0 :=
    (admissEhat_differentiableOn hc).differentiableAt (hopen.mem_nhds (by
      show -c < (0 : ℂ).re ∧ (0 : ℂ).re < 2 * c
      simp [hc]))
  have hO := hd.hasDerivAt.isBigO_sub
  rw [Asymptotics.isBigO_iff] at hO
  obtain ⟨C, hC⟩ := hO
  rw [Metric.eventually_nhds_iff] at hC
  obtain ⟨δ, hδ, hδC⟩ := hC
  refine ⟨δ, |C|, hδ, abs_nonneg _, fun z hz => ?_⟩
  have := hδC (y := z) (by simpa [dist_eq_norm] using hz)
  simp only [admissEhat_zero, sub_zero] at this
  refine this.trans ?_
  exact mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)

/-- `K(z) = Ê(z) W̃(1 - z/c) - W̃(1)`; `R = Γ · K` on `0 < Re z < c`. -/
noncomputable def admissK (c : ℝ) (W : ℂ → ℂ) (z : ℂ) : ℂ := admissEhat c z * W (1 - z / c) - W 1

lemma admissRem_eq {c : ℝ} (hc : 0 < c) {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < c) :
    admissRem c W z = Complex.Gamma z * admissK c W z := by
  unfold admissRem admissPhi admissK
  rw [admissG_eq_Ehat hc hz0 hz1]; ring

lemma admissK_continuousOn_of_W1 {c η : ℝ} (hc : 0 < c) (hW : StripW1 η W) :
    ContinuousOn (admissK c W) {z : ℂ | 0 ≤ z.re ∧ z.re ≤ c} := by
  refine ((admissEhat_continuousOn hc).mul ?_).sub continuousOn_const
  refine hW.cont.comp ((continuousOn_const.sub (continuousOn_id.div_const _))) fun z hz => ?_
  show 0 ≤ (1 - z / (c : ℂ)).re ∧ (1 - z / (c : ℂ)).re ≤ 1
  rw [re_one_sub_div hc]
  have h1 : z.re / c ≤ 1 := (div_le_one hc).mpr hz.2
  have h2 : 0 ≤ z.re / c := by have := hz.1; positivity
  constructor <;> linarith

lemma admissK_continuousOn {c : ℝ} (hc : 0 < c) (hW : StripM1 W) :
    ContinuousOn (admissK c W) {z : ℂ | 0 ≤ z.re ∧ z.re ≤ c} :=
  admissK_continuousOn_of_W1 hc hW.toStripW1

lemma admissK_small {c α : ℝ} (hc : 0 < c) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hH : ∃ CH : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖1 - ζ‖ ≤ 1 / 2 → ‖W ζ - W 1‖ ≤ CH * ‖1 - ζ‖ ^ α) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 ≤ C ∧ ∀ z : ℂ, 0 ≤ z.re → z.re ≤ c → ‖z‖ < δ →
      ‖admissK c W z‖ ≤ C * ‖z‖ ^ α := by
  obtain ⟨δ0, C1, hδ0, hC1, hlip⟩ := admissEhat_lip hc
  obtain ⟨CH, hCH⟩ := hH
  set δ : ℝ := min δ0 (min 1 (c / 2)) with hδ
  have hδ0' : 0 < δ := lt_min hδ0 (lt_min one_pos (by linarith))
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨δ, (1 + C1) * |CH| * (c ^ α)⁻¹ + C1 * ‖W 1‖, hδ0', hδ1, by positivity, fun z hz0 hzc hz => ?_⟩
  have hzδ0 : ‖z‖ < δ0 := hz.trans_le (min_le_left _ _)
  have hz1 : ‖z‖ < 1 := hz.trans_le hδ1
  have hzc2 : ‖z‖ < c / 2 := hz.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hE := hlip z hzδ0
  have hzn0 : 0 ≤ ‖z‖ := norm_nonneg _
  set ζ : ℂ := 1 - z / (c : ℂ) with hζ
  have hζre0 : 0 ≤ ζ.re := by
    rw [hζ, re_one_sub_div hc]; have : z.re / c ≤ 1 := (div_le_one hc).mpr hzc
    linarith
  have hζre1 : ζ.re ≤ 1 := by
    rw [hζ, re_one_sub_div hc]; have : 0 ≤ z.re / c := by positivity
    linarith
  have hnorm : ‖1 - ζ‖ = ‖z‖ / c := by
    rw [hζ, sub_sub_cancel, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  have hn2 : ‖1 - ζ‖ ≤ 1 / 2 := by
    rw [hnorm, div_le_iff₀ hc]; linarith
  have hW1 := hCH ζ hζre0 hζre1 hn2
  rw [hnorm] at hW1
  have hpα : ‖z‖ ≤ ‖z‖ ^ α := by
    rcases hzn0.eq_or_lt with h0 | h0
    · rw [← h0, Real.zero_rpow hα0.ne']
    · calc ‖z‖ = ‖z‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ ‖z‖ ^ α := Real.rpow_le_rpow_of_exponent_ge h0 hz1.le hα1
  have hdiv : (‖z‖ / c) ^ α = (c ^ α)⁻¹ * ‖z‖ ^ α := by
    rw [Real.div_rpow hzn0 hc.le]; field_simp
  have hEn : ‖admissEhat c z‖ ≤ 1 + C1 := by
    have : ‖admissEhat c z‖ ≤ ‖admissEhat c z - 1‖ + 1 := by
      calc ‖admissEhat c z‖ = ‖(admissEhat c z - 1) + 1‖ := by rw [sub_add_cancel]
        _ ≤ _ := (norm_add_le _ _).trans (by simp)
    nlinarith
  have e : admissK c W z = admissEhat c z * (W ζ - W 1) + (admissEhat c z - 1) * W 1 := by
    unfold admissK; rw [← hζ]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have t1 : ‖admissEhat c z‖ * ‖W ζ - W 1‖ ≤ (1 + C1) * (|CH| * ((c ^ α)⁻¹ * ‖z‖ ^ α)) := by
    refine mul_le_mul hEn ?_ (norm_nonneg _) (by positivity)
    rw [hdiv] at hW1
    exact hW1.trans (mul_le_mul_of_nonneg_right (le_abs_self CH) (by positivity))
  have t2 : ‖admissEhat c z - 1‖ * ‖W 1‖ ≤ C1 * ‖z‖ ^ α * ‖W 1‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact hE.trans (mul_le_mul_of_nonneg_left hpα hC1)
  nlinarith [Real.rpow_nonneg hzn0 α]

lemma gamma_not_pole {z : ℂ} (hz0 : 0 ≤ z.re) (hz : z ≠ 0) : ∀ m : ℕ, z ≠ -m := by
  intro m h
  have h1 := congrArg Complex.re h
  simp at h1
  have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm : (m : ℝ) = 0 := by linarith
  have : m = 0 := by exact_mod_cast hm
  subst this
  simp at h
  exact hz h

lemma continuousAt_Gamma_of_re_nonneg {z : ℂ} (hz0 : 0 ≤ z.re) (hz : z ≠ 0) : ContinuousAt Complex.Gamma z :=
  (Complex.differentiableAt_Gamma z (gamma_not_pole hz0 hz)).continuousAt

/-- `Γ · K` is bounded on the compact part `0 ≤ Re z ≤ 1/2`, `|Im z| ≤ 1`, `|z| ≥ δ` under `(W1)`. -/
lemma admissRem_compact_bound_of_W1 {c η : ℝ} (hc : 2 ≤ c) (hW : StripW1 η W) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 / 2 → |z.im| ≤ 1 → δ ≤ ‖z‖ →
      ‖Complex.Gamma z * admissK c W z‖ ≤ M := by
  have hc0 : 0 < c := by linarith
  set S : Set ℂ := ((fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) '' (Icc (0 : ℝ) (1 / 2) ×ˢ Icc (-1 : ℝ) 1)) ∩
    {z : ℂ | δ ≤ ‖z‖} with hS
  have hSc : IsCompact S :=
    ((isCompact_Icc.prod isCompact_Icc).image (by fun_prop)).inter_right (isClosed_le continuous_const continuous_norm)
  have hKc := admissK_continuousOn_of_W1 hc0 hW
  have hcont : ContinuousOn (fun z : ℂ => Complex.Gamma z * admissK c W z) S := by
    intro z hz
    obtain ⟨⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩, hzδ⟩ := hz
    simp only at hx hy
    have hzre : 0 ≤ ((x : ℂ) + (y : ℂ) * Complex.I).re := by simpa using hx.1
    have hzδ' : δ ≤ ‖(x : ℂ) + (y : ℂ) * Complex.I‖ := hzδ
    have hzne : (x : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
      intro h; rw [h] at hzδ'; simp at hzδ'; linarith
    refine ((continuousAt_Gamma_of_re_nonneg hzre hzne).continuousWithinAt).mul ?_
    refine (hKc _ ⟨hzre, by simp; linarith [hx.2]⟩).mono ?_
    rintro w ⟨⟨⟨x', y'⟩, ⟨hx', hy'⟩, rfl⟩, _⟩
    exact ⟨by simpa using hx'.1, by simp; linarith [hx'.2]⟩
  obtain ⟨M, hM⟩ := hSc.exists_bound_of_continuousOn hcont
  refine ⟨M, fun z hz0 hz1 hz2 hz3 => ?_⟩
  refine hM z ⟨⟨(z.re, z.im), ⟨⟨hz0, hz1⟩, ⟨(abs_le.mp hz2).1, (abs_le.mp hz2).2⟩⟩, ?_⟩, hz3⟩
  simp

/-- `Γ · K` is bounded on the compact part `0 ≤ Re z ≤ 1/2`, `|Im z| ≤ 1`, `|z| ≥ δ`. -/
lemma admissRem_compact_bound {c : ℝ} (hc : 2 ≤ c) (hW : StripM1 W) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 / 2 → |z.im| ≤ 1 → δ ≤ ‖z‖ →
      ‖Complex.Gamma z * admissK c W z‖ ≤ M :=
  admissRem_compact_bound_of_W1 hc hW.toStripW1 hδ

lemma integrableOn_abs_rpow_Icc {r : ℝ} (hr : -1 < r) : IntegrableOn (fun y : ℝ => |y| ^ r) (Icc (-1) 1) := by
  have h1 : IntervalIntegrable (fun x : ℝ => x ^ r) volume 0 1 := intervalIntegral.intervalIntegrable_rpow' hr
  have h2 : IntervalIntegrable (fun x : ℝ => (-x) ^ r) volume (-0) (-1) := (IntervalIntegrable.iff_comp_neg (f := fun x : ℝ => x ^ r)).mp h1
  have e1 : IntegrableOn (fun y : ℝ => |y| ^ r) (Ioc 0 1) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h1
    exact h1.congr_fun (fun x hx => by simp only [abs_of_pos hx.1]) measurableSet_Ioc
  have e2 : IntegrableOn (fun y : ℝ => |y| ^ r) (Ioc (-1) 0) := by
    rw [neg_zero] at h2
    have h3 := h2.symm
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at h3
    exact h3.congr_fun (fun x hx => by simp only [abs_of_nonpos hx.2]) measurableSet_Ioc
  rw [integrableOn_Icc_iff_integrableOn_Ioc, ← Ioc_union_Ioc_eq_Ioc (by norm_num : (-1 : ℝ) ≤ 0) zero_le_one]
  exact e2.union e1

/-- The integrable majorant `1_{[-1,1]} |y|^{α-1} + (1+|y|)^{-(1 + min η 1)}` for `(W1)` (`η > 0`). -/
noncomputable def originMajorantW (α η : ℝ) (y : ℝ) : ℝ :=
  Set.indicator (Icc (-1 : ℝ) 1) (fun y : ℝ => |y| ^ (α - 1)) y + (1 + |y|) ^ (-(1 + min η 1))

lemma integrable_originMajorantW {α η : ℝ} (hα0 : 0 < α) (hη : 0 < η) : Integrable (originMajorantW α η) := by
  refine Integrable.add ?_ (by simpa using integrable_weight_rpow (p := 1 + min η 1) (by linarith [lt_min hη one_pos]) 1)
  exact (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_abs_rpow_Icc (by linarith))

/-- The integrable majorant `1_{[-1,1]} |y|^{α-1} + (1+|y|)^{-2}`. -/
noncomputable def originMajorant (α : ℝ) (y : ℝ) : ℝ :=
  Set.indicator (Icc (-1 : ℝ) 1) (fun y : ℝ => |y| ^ (α - 1)) y + (1 + |y|) ^ (-(2 : ℝ))

lemma integrable_originMajorant {α : ℝ} (hα0 : 0 < α) : Integrable (originMajorant α) := by
  refine Integrable.add ?_ (by simpa using integrable_weight_two 1)
  exact (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_abs_rpow_Icc (by linarith))

lemma originMajorant_nonneg (α : ℝ) (y : ℝ) : 0 ≤ originMajorant α y := by
  unfold originMajorant
  refine add_nonneg (Set.indicator_nonneg (fun y _ => by positivity) y) (by positivity)

/-- Uniform bound of `R = Φ_W - W(1) Γ` on the lines `0 < Re z ≤ 1/2` under `(W1)` (`0 < η`, `0 < α ≤ 1`). -/
theorem admissRem_line_bound_of_W1 {c η α : ℝ} (hc : 2 ≤ c) (hη : 0 < η) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hW : StripW1 η W)
    (hH : ∃ CH : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖1 - ζ‖ ≤ 1 / 2 → ‖W ζ - W 1‖ ≤ CH * ‖1 - ζ‖ ^ α) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ε y : ℝ, 0 < ε → ε ≤ 1 / 2 → y ≠ 0 →
      ‖admissRem c W ((ε : ℂ) + (y : ℂ) * Complex.I)‖ ≤ A * originMajorantW α η y := by
  have hc0 : 0 < c := by linarith
  obtain ⟨δ, Cs, hδ0, hδ1, hCs, hsmall⟩ := admissK_small hc0 hα0 hα1 hH
  obtain ⟨M, hM⟩ := admissRem_compact_bound_of_W1 hc hW hδ0
  obtain ⟨B, hB⟩ := admissPhi_bound_left_of_W1 (by linarith : (1 : ℝ) ≤ c) hη hW
  refine ⟨(Cs + |M|) + |B| + 8 * ‖W 1‖, by positivity, fun ε y hε0 hε1 hy => ?_⟩
  set z : ℂ := (ε : ℂ) + (y : ℂ) * Complex.I with hz
  have hzre : z.re = ε := by simp [hz]
  have hzim : z.im = y := by simp [hz]
  have hz0 : 0 < z.re := by rw [hzre]; exact hε0
  have hzc : z.re < c := by rw [hzre]; linarith
  have hy0 : 0 < |y| := abs_pos.mpr hy
  have hzn : |y| ≤ ‖z‖ := by rw [← hzim]; exact Complex.abs_im_le_norm z
  rcases le_or_gt |y| 1 with hy1 | hy1
  · have hind : originMajorantW α η y = |y| ^ (α - 1) + (1 + |y|) ^ (-(1 + min η 1)) := by
      unfold originMajorantW
      rw [Set.indicator_of_mem (by rw [mem_Icc]; exact abs_le.mp hy1)]
    have hw0 : 0 ≤ (1 + |y|) ^ (-(1 + min η 1)) := by positivity
    have hq1 : 1 ≤ |y| ^ (α - 1) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy0 hy1 (by linarith)
    have hq0 : 0 ≤ |y| ^ (α - 1) := by positivity
    have hbound : ‖admissRem c W z‖ ≤ (Cs + |M|) * |y| ^ (α - 1) := by
      rw [admissRem_eq hc0 hz0 hzc, norm_mul]
      by_cases hzδ : ‖z‖ < δ
      · have hK := hsmall z hz0.le hzc.le hzδ
        have hG := norm_Gamma_le_inv hz0 (by rw [hzre]; linarith)
        have hzn0 : 0 < ‖z‖ := lt_of_lt_of_le hy0 hzn
        have hpow : ‖z‖ ^ α / ‖z‖ ≤ |y| ^ (α - 1) := by
          rw [← Real.rpow_sub_one hzn0.ne']
          exact Real.rpow_le_rpow_of_nonpos hy0 hzn (by linarith)
        calc ‖Complex.Gamma z‖ * ‖admissK c W z‖ ≤ (1 / ‖z‖) * (Cs * ‖z‖ ^ α) :=
              mul_le_mul hG hK (norm_nonneg _) (by positivity)
          _ = Cs * (‖z‖ ^ α / ‖z‖) := by ring
          _ ≤ Cs * |y| ^ (α - 1) := mul_le_mul_of_nonneg_left hpow hCs
          _ ≤ (Cs + |M|) * |y| ^ (α - 1) := by nlinarith [abs_nonneg M]
      · have hzδ' : δ ≤ ‖z‖ := not_lt.mp hzδ
        have := hM z hz0.le (by rw [hzre]; exact hε1) (by rw [hzim]; exact hy1) hzδ'
        rw [← norm_mul]
        calc ‖Complex.Gamma z * admissK c W z‖ ≤ M := this
          _ ≤ |M| * 1 := by rw [mul_one]; exact le_abs_self M
          _ ≤ |M| * |y| ^ (α - 1) := mul_le_mul_of_nonneg_left hq1 (abs_nonneg _)
          _ ≤ (Cs + |M|) * |y| ^ (α - 1) := by nlinarith [abs_nonneg M]
    rw [hind]
    have hA : 0 ≤ (Cs + |M|) + |B| + 8 * ‖W 1‖ := by positivity
    nlinarith [mul_nonneg (abs_nonneg B) hw0, mul_nonneg (norm_nonneg (W 1)) hw0, mul_nonneg (abs_nonneg B) hq0,
      mul_nonneg (norm_nonneg (W 1)) hq0, mul_nonneg hCs hq0]
  · have hind : originMajorantW α η y = (1 + |y|) ^ (-(1 + min η 1)) := by
      unfold originMajorantW
      rw [Set.indicator_of_notMem (by rw [mem_Icc]; intro h; exact absurd (abs_le.mpr h) (not_le.mpr hy1)), zero_add]
    have hw0 : 0 < (1 + |y|) ^ (-(1 + min η 1)) := by positivity
    have hΦ := hB z hz0 (by rw [hzre]; linarith) (by rw [hzim]; exact hy1.le)
    rw [hzim] at hΦ
    have hΦ' : ‖admissPhi c W z‖ ≤ |B| * (1 + |y|) ^ (-(1 + min η 1)) := by
      have hp : (1 + |y|) ^ (-(1 + η)) ≤ (1 + |y|) ^ (-(1 + min η 1)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg y]) (by linarith [min_le_left η 1])
      exact hΦ.trans ((mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hp (abs_nonneg B)))
    have hG := norm_Gamma_le_inv_sq hz0 (by rw [hzre]; linarith)
    have hzn1 : |y| ≤ ‖z + 1‖ := by
      have := Complex.abs_im_le_norm (z + 1)
      simpa [hzim] using this
    have hprod : |y| ^ 2 ≤ ‖z‖ * ‖z + 1‖ := by rw [pow_two]; exact mul_le_mul hzn hzn1 (abs_nonneg _) (norm_nonneg _)
    have hy2 : 0 < |y| ^ 2 := by positivity
    have hG2 : ‖Complex.Gamma z‖ ≤ 2 / |y| ^ 2 :=
      hG.trans (div_le_div_of_nonneg_left (by norm_num) hy2 hprod)
    have hw : 1 / |y| ^ 2 ≤ 4 * (1 + |y|) ^ (-(2 : ℝ)) := by
      have h1 : (1 + |y|) ≤ 2 * |y| := by linarith
      have : (2 * |y|) ^ (-(2 : ℝ)) ≤ (1 + |y|) ^ (-(2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
      have e : (2 * |y|) ^ (-(2 : ℝ)) = 1 / (4 * |y| ^ 2) := by
        rw [Real.rpow_neg (by positivity), Real.rpow_two, mul_pow]; field_simp; norm_num
      rw [e] at this
      rw [div_le_iff₀ hy2]
      have : 1 / (4 * |y| ^ 2) * (4 * |y| ^ 2) = 1 := by field_simp
      nlinarith
    have h2q : (1 + |y|) ^ (-(2 : ℝ)) ≤ (1 + |y|) ^ (-(1 + min η 1)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg y]) (by linarith [min_le_right η 1])
    have hΓ8 : ‖Complex.Gamma z‖ ≤ 8 * (1 + |y|) ^ (-(1 + min η 1)) := by
      calc ‖Complex.Gamma z‖ ≤ 2 / |y| ^ 2 := hG2
        _ = 2 * (1 / |y| ^ 2) := by ring
        _ ≤ 2 * (4 * (1 + |y|) ^ (-(2 : ℝ))) := mul_le_mul_of_nonneg_left hw (by norm_num)
        _ = 8 * (1 + |y|) ^ (-(2 : ℝ)) := by ring
        _ ≤ 8 * (1 + |y|) ^ (-(1 + min η 1)) := mul_le_mul_of_nonneg_left h2q (by norm_num)
    have hR : ‖admissRem c W z‖ ≤ |B| * (1 + |y|) ^ (-(1 + min η 1)) + ‖W 1‖ * (8 * (1 + |y|) ^ (-(1 + min η 1))) := by
      unfold admissRem
      refine (norm_sub_le _ _).trans (add_le_add hΦ' ?_)
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left hΓ8 (norm_nonneg _)
    rw [hind]
    have hA : 0 ≤ (Cs + |M|) + |B| + 8 * ‖W 1‖ := by positivity
    nlinarith [mul_nonneg (abs_nonneg B) hw0.le, mul_nonneg (norm_nonneg (W 1)) hw0.le,
      mul_nonneg (add_nonneg hCs (abs_nonneg M)) hw0.le]

/-- Uniform bound of `R = Φ_W - W̃(1) Γ` on the lines `0 < Re z ≤ 1/2`. -/
theorem admissRem_line_bound {c α : ℝ} (hc : 2 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) (hW : StripM1 W)
    (hH : ∃ CH : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖1 - ζ‖ ≤ 1 / 2 → ‖W ζ - W 1‖ ≤ CH * ‖1 - ζ‖ ^ α) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ε y : ℝ, 0 < ε → ε ≤ 1 / 2 → y ≠ 0 →
      ‖admissRem c W ((ε : ℂ) + (y : ℂ) * Complex.I)‖ ≤ A * originMajorant α y := by
  obtain ⟨A, hA0, hA⟩ := admissRem_line_bound_of_W1 hc (by norm_num : (0 : ℝ) < 3 / 2) hα0 hα1.le hW.toStripW1 hH
  refine ⟨A, hA0, fun ε y hε0 hε1 hy => ?_⟩
  have h := hA ε y hε0 hε1 hy
  have heq : originMajorantW α (3 / 2) y = originMajorant α y := by
    unfold originMajorantW originMajorant
    have : min (3 / 2 : ℝ) 1 = 1 := min_eq_right (by norm_num)
    rw [this]; norm_num
  rwa [heq] at h

/-- The limit integrand `Δ^{-iy} Γ(iy) K(iy)` on the imaginary axis. -/
noncomputable def originLimit (c : ℝ) (W : ℂ → ℂ) (Δ : ℝ) (y : ℝ) : ℂ :=
  (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) * (Complex.Gamma ((y : ℂ) * Complex.I) * admissK c W ((y : ℂ) * Complex.I))

/-- **The value of the lift at `Δ > 0`, with the pole subtracted**, under `(W1)` (`0 < η`, `0 < α ≤ 1`):
`f(Δ) = W(1) e^{-Δ} + (2π)⁻¹ ∫ Δ^{-iy} Γ(iy) K(iy) dy`. -/
theorem admiss_lift_eq_limit_of_W1 {c η α : ℝ} (hc : 2 ≤ c) (hη : 0 < η) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hW : StripW1 η W)
    (hH : ∃ CH : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖1 - ζ‖ ≤ 1 / 2 → ‖W ζ - W 1‖ ≤ CH * ‖1 - ζ‖ ^ α)
    {Δ : ℝ} (hΔ : 0 < Δ) :
    ((admissLift c W Δ : ℝ) : ℂ) = W 1 * ((Real.exp (-Δ) : ℝ) : ℂ) +
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, originLimit c W Δ y := by
  have hc0 : 0 < c := by linarith
  have hR := admissRem_mellinLiftData_of_W1 hc hη hW
  obtain ⟨A, hA0, hA⟩ := admissRem_line_bound_of_W1 hc hη hα0 hα1 hW hH
  set F : ℝ → ℝ → ℂ := fun ε y => (Δ : ℂ) ^ (-((ε : ℂ) + (y : ℂ) * Complex.I)) *
    admissRem c W ((ε : ℂ) + (y : ℂ) * Complex.I) with hF
  have hae : ∀ᵐ y : ℝ, y ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton 0)
  have hlim : Tendsto (fun ε : ℝ => ∫ y : ℝ, F ε y) (𝓝[>] (0 : ℝ)) (𝓝 (∫ y : ℝ, originLimit c W Δ y)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => (1 + Δ ^ (-(1 / 2 : ℝ))) * (A * originMajorantW α η y)) ?_ ?_ ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT hc0] with ε hε
      have hcont : Continuous fun y : ℝ => F ε y := by
        have h1 : Continuous fun y : ℝ => (Δ : ℂ) ^ (-((ε : ℂ) + (y : ℂ) * Complex.I)) :=
          Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hΔ.ne'))
        exact h1.mul (continuous_line hR hε.1 hε.2)
      exact hcont.aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with ε hε
      filter_upwards [hae] with y hy
      have h1 := hA ε y hε.1 hε.2.le hy
      have h2 : Δ ^ (-ε) ≤ 1 + Δ ^ (-(1 / 2 : ℝ)) := by
        have := rpow_neg_le_sum (Δ := Δ) (x := 0) (x' := 1 / 2) (t := ε) hΔ hε.1.le hε.2.le
        rwa [neg_zero, Real.rpow_zero] at this
      simp only [hF]
      rw [norm_mul, norm_cpow_line hΔ]
      exact mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
    · exact ((integrable_originMajorantW hα0 hη).const_mul A).const_mul _
    · filter_upwards [hae] with y hy
      set z0 : ℂ := (y : ℂ) * Complex.I with hz0
      have hz0re : z0.re = 0 := by simp [hz0]
      have hz0ne : z0 ≠ 0 := by
        intro h; apply hy; have := congrArg Complex.im h; simpa [hz0] using this
      have hGc : ContinuousAt Complex.Gamma z0 := continuousAt_Gamma_of_re_nonneg hz0re.ge hz0ne
      have hKc := admissK_continuousOn_of_W1 hc0 hW z0 ⟨hz0re.ge, by rw [hz0re]; exact hc0.le⟩
      have hpowc : ContinuousAt (fun z : ℂ => (Δ : ℂ) ^ (-z)) z0 :=
        (Continuous.const_cpow continuous_neg (Or.inl (by exact_mod_cast hΔ.ne'))).continuousAt
      have hcw : ContinuousWithinAt (fun z : ℂ => (Δ : ℂ) ^ (-z) * (Complex.Gamma z * admissK c W z))
          {z : ℂ | 0 ≤ z.re ∧ z.re ≤ c} z0 :=
        hpowc.continuousWithinAt.mul (hGc.continuousWithinAt.mul hKc)
      have hz : Tendsto (fun ε : ℝ => (ε : ℂ) + (y : ℂ) * Complex.I) (𝓝[>] (0 : ℝ))
          (𝓝[{z : ℂ | 0 ≤ z.re ∧ z.re ≤ c}] z0) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have : Tendsto (fun ε : ℝ => (ε : ℂ) + (y : ℂ) * Complex.I) (𝓝 (0 : ℝ)) (𝓝 (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) :=
            (by fun_prop : Continuous fun ε : ℝ => (ε : ℂ) + (y : ℂ) * Complex.I).continuousAt.tendsto
          simpa [hz0] using this.mono_left nhdsWithin_le_nhds
        · filter_upwards [Ioo_mem_nhdsGT hc0] with ε hε
          exact ⟨by simp; exact hε.1.le, by simp; exact hε.2.le⟩
      have := hcw.tendsto.comp hz
      refine this.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hc0] with ε hε
      simp only [Function.comp, hF]
      have hre0 : 0 < ((ε : ℂ) + (y : ℂ) * Complex.I).re := by simpa using hε.1
      have hre1 : ((ε : ℂ) + (y : ℂ) * Complex.I).re < c := by simpa using hε.2
      rw [admissRem_eq hc0 hre0 hre1]
  have hconst : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∫ y : ℝ, F ε y = ((2 * Real.pi : ℝ) : ℂ) * (((admissLift c W Δ : ℝ) : ℂ) - W 1 * ((Real.exp (-Δ) : ℝ) : ℂ)) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with ε hε
    have h1 := admiss_lift_eq_sub_of_W1 hc hη hW hΔ hε.1 (by linarith [hε.2])
    have h2 : mellinInv ε (admissRem c W) Δ = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, F ε y := by
      unfold mellinInv
      rw [Complex.real_smul]
      simp only [hF, smul_eq_mul]
    have hπ : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < 2 * Real.pi := by positivity
      exact_mod_cast this.ne'
    have h3 : ((admissLift c W Δ : ℝ) : ℂ) - W 1 * ((Real.exp (-Δ) : ℝ) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, F ε y := by
      rw [← h2]; linear_combination h1
    rw [h3]
    push_cast
    field_simp
  have hconst' : Tendsto (fun ε : ℝ => ∫ y : ℝ, F ε y) (𝓝[>] (0 : ℝ))
      (𝓝 (((2 * Real.pi : ℝ) : ℂ) * (((admissLift c W Δ : ℝ) : ℂ) - W 1 * ((Real.exp (-Δ) : ℝ) : ℂ)))) :=
    tendsto_const_nhds.congr' (hconst.mono fun ε h => h.symm)
  have huniq := tendsto_nhds_unique hlim hconst'
  have hπ : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 2 * Real.pi := by positivity
    exact_mod_cast this.ne'
  rw [huniq]
  push_cast
  field_simp
  ring

/-- **The value of the lift at `Δ > 0`, with the pole subtracted:**
`f(Δ) = W̃(1) e^{-Δ} + (2π)⁻¹ ∫ Δ^{-iy} Γ(iy) K(iy) dy`. -/
theorem admiss_lift_eq_limit {c α : ℝ} (hc : 2 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) (hW : StripM1 W)
    (hH : ∃ CH : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖1 - ζ‖ ≤ 1 / 2 → ‖W ζ - W 1‖ ≤ CH * ‖1 - ζ‖ ^ α)
    {Δ : ℝ} (hΔ : 0 < Δ) :
    ((admissLift c W Δ : ℝ) : ℂ) = W 1 * ((Real.exp (-Δ) : ℝ) : ℂ) +
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, originLimit c W Δ y :=
  admiss_lift_eq_limit_of_W1 hc (by norm_num) hα0 hα1.le hW.toStripW1 hH hΔ

lemma cpow_imag_eq (Δ y : ℝ) (hΔ : 0 < Δ) :
    (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) = Complex.exp (2 * Real.pi * (-(y * (Real.log Δ / (2 * Real.pi)))) * Complex.I) := by
  have hΔ0 : (Δ : ℂ) ≠ 0 := by exact_mod_cast hΔ.ne'
  rw [Complex.cpow_def_of_ne_zero hΔ0, ← Complex.ofReal_log hΔ.le]
  congr 1
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- **`mat:T7` (a), the value at the origin:** `f_W(Δ) → W(1)` as `Δ ↓ 0` under `(W1)` (`0 < η`) and `(W2)` at `1` (`0 < α ≤ 1`). -/
theorem admiss_lift_tendsto_of_W1 {c η α : ℝ} (hc : 2 ≤ c) (hη : 0 < η) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hW : StripW1 η W)
    (hH : ∃ CH : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖1 - ζ‖ ≤ 1 / 2 → ‖W ζ - W 1‖ ≤ CH * ‖1 - ζ‖ ^ α) :
    Tendsto (admissLift c W) (𝓝[>] (0 : ℝ)) (𝓝 (W 1).re) := by
  set ρ : ℝ → ℂ := fun y => Complex.Gamma ((y : ℂ) * Complex.I) * admissK c W ((y : ℂ) * Complex.I) with hρ
  have hRL := Real.tendsto_integral_exp_smul_cocompact ρ
  have hw : Tendsto (fun Δ : ℝ => Real.log Δ / (2 * Real.pi)) (𝓝[>] (0 : ℝ)) (cocompact ℝ) := by
    have h1 : Tendsto (fun Δ : ℝ => Real.log Δ / (2 * Real.pi)) (𝓝[>] (0 : ℝ)) atBot :=
      Real.tendsto_log_nhdsGT_zero.atBot_div_const (by positivity)
    rw [cocompact_eq_atBot_atTop]
    exact h1.mono_right le_sup_left
  have hJ : Tendsto (fun Δ : ℝ => ∫ y : ℝ, originLimit c W Δ y) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine (hRL.comp hw).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with Δ hΔ
    have hΔ' : 0 < Δ := hΔ
    simp only [Function.comp]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [originLimit, hρ]
    rw [cpow_imag_eq Δ y hΔ', Circle.smul_def, Real.fourierChar_apply]
    simp only [smul_eq_mul]
    push_cast
    ring_nf
  have hexp : Tendsto (fun Δ : ℝ => ((Real.exp (-Δ) : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have : Continuous fun Δ : ℝ => ((Real.exp (-Δ) : ℝ) : ℂ) := by fun_prop
    have h := this.continuousAt (x := 0) |>.tendsto
    simpa using h.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun Δ : ℝ => ((admissLift c W Δ : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (W 1)) := by
    have h := (hexp.const_mul (W 1)).add ((hJ.const_mul (((1 / (2 * Real.pi) : ℝ)) : ℂ)))
    simp only [mul_one, mul_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with Δ hΔ
    exact (admiss_lift_eq_limit_of_W1 hc hη hα0 hα1 hW hH hΔ).symm
  have h2 := (Complex.continuous_re.tendsto (W 1)).comp hlim
  exact h2.congr (fun Δ => by simp)

/-- **`uct:admiss` (1), the value at the origin:** `f_W(Δ) → W̃(1)` as `Δ ↓ 0` (`mat:T7`(a)). -/
theorem admiss_lift_tendsto {c α : ℝ} (hc : 2 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) (hW : StripM1 W)
    (hH : ∃ CH : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖1 - ζ‖ ≤ 1 / 2 → ‖W ζ - W 1‖ ≤ CH * ‖1 - ζ‖ ^ α) :
    Tendsto (admissLift c W) (𝓝[>] (0 : ℝ)) (𝓝 (W 1).re) :=
  admiss_lift_tendsto_of_W1 hc (by norm_num) hα0 hα1.le hW.toStripW1 hH

/-- info: 'FormalResearch.SignUncertainty.mellinInv_one_Gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mellinInv_one_Gamma

/-- info: 'FormalResearch.SignUncertainty.admissRem_mellinLiftData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms admissRem_mellinLiftData

/-- info: 'FormalResearch.SignUncertainty.admiss_lift_eq_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms admiss_lift_eq_sub

/-- info: 'FormalResearch.SignUncertainty.admiss_lift_eq_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms admiss_lift_eq_limit

/-- info: 'FormalResearch.SignUncertainty.admiss_lift_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms admiss_lift_tendsto

end FormalResearch.SignUncertainty
