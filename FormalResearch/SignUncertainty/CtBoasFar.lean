module

public import FormalResearch.SignUncertainty.CtBoasWindow
public import FormalResearch.SignUncertainty.CtFejer
public import FormalResearch.SignUncertainty.RadialRigidity

/-!
# `ct:boas` Step 1: windowed Fourier coefficients of the far-tail density

`constant_terms_lower.tex`, proof of `ct:boas`, Step 1.  For an integrable real `h` (in the application
`h = 1_{Δ>0} f ρ₀`) with `‖Fh‖ ≤ 1` on `ℝ` and `‖Fh(x)‖ ≤ |x|^{-c}` for `|x| ≥ 1` (the exact Hankel-Gaussian
modular identity, `HankelModular.hankelF_bound`), and the window `s_{D,W}` of `CtBoasWindow`, the density
`ψ̃ = (1 - s_{D,W}) h` has Fourier coefficients

`‖ψ̃^(k)‖ ≤ k^{-c} + 2D((3k/4)^{-c}√(π/b) + e^{-b k²/32}√(2π/b))`, `b = 2π²W²`, `k ≥ 2`,

(`psiT_coeff_bound`), and the finite Fejér inequality `ct_fejer` (`ω = 2π`) gives the far-tail positivity
(`psiT_fejer`).  **Proved** (abstract in `h`; no Hankel input beyond the two hypotheses on `Fh`).
-/

@[expose] public section

open MeasureTheory Set Finset
open FormalResearch.SignUncertainty.CtFejer
open scoped Real

namespace FormalResearch.SignUncertainty.CtBoasWindow

lemma gaussK_nonneg {W : ℝ} (hW : 0 < W) (y : ℝ) : 0 ≤ gaussK W y := by
  unfold gaussK; positivity

lemma continuous_gaussK (W : ℝ) : Continuous (gaussK W) := by
  unfold gaussK; fun_prop

lemma integrable_gaussK {W : ℝ} (hW : 0 < W) : Integrable (gaussK W) := by
  unfold gaussK
  have := (integrable_exp_neg_mul_sq (b := 1 / (2 * W ^ 2)) (by positivity)).div_const (√(2 * π) * W)
  refine this.congr (ae_of_all _ fun y => ?_)
  simp only [neg_mul]

lemma integral_gaussK {W : ℝ} (hW : 0 < W) : ∫ y, gaussK W y = 1 := by
  unfold gaussK
  have hb : 0 < 1 / (2 * W ^ 2) := by positivity
  have h1 : ∫ y : ℝ, Real.exp (-(1 / (2 * W ^ 2)) * y ^ 2) = √(π / (1 / (2 * W ^ 2))) :=
    integral_gaussian _
  rw [integral_div, h1]
  have h2 : π / (1 / (2 * W ^ 2)) = (√(2 * π) * W) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; field_simp
  rw [h2, Real.sqrt_sq (by positivity)]
  field_simp

lemma sWin_nonneg {D W : ℝ} (hW : 0 < W) (Δ : ℝ) : 0 ≤ sWin D W Δ :=
  setIntegral_nonneg measurableSet_Icc fun _ _ => gaussK_nonneg hW _

lemma sWin_le_one {D W : ℝ} (hW : 0 < W) (Δ : ℝ) : sWin D W Δ ≤ 1 := by
  unfold sWin
  have hi : Integrable (fun x => gaussK W (Δ - x)) :=
    (integrable_gaussK hW).comp_sub_left Δ
  calc ∫ x in Icc (-D) D, gaussK W (Δ - x) ≤ ∫ x, gaussK W (Δ - x) :=
        setIntegral_le_integral hi (ae_of_all _ fun _ => gaussK_nonneg hW _)
    _ = ∫ y, gaussK W y := integral_sub_left_eq_self (gaussK W) volume Δ
    _ = 1 := integral_gaussK hW

lemma continuous_sWin (D W : ℝ) : Continuous (sWin D W) := by
  unfold sWin
  exact continuous_parametric_integral_of_continuous
    (f := fun Δ x => gaussK W (Δ - x)) (by
      have := (continuous_gaussK W)
      fun_prop) isCompact_Icc

/-- The far-tail density `ψ̃ = (1 - s_{D,W}) h`. -/
noncomputable def psiT (h : ℝ → ℝ) (D W : ℝ) (Δ : ℝ) : ℝ := (1 - sWin D W Δ) * h Δ

lemma integrable_psiT {h : ℝ → ℝ} (hh : Integrable h) {D W : ℝ} (hW : 0 < W) :
    Integrable (psiT h D W) := by
  refine hh.norm.mono' ?_ (ae_of_all _ fun x => ?_)
  · exact ((continuous_const.sub (continuous_sWin D W)).aestronglyMeasurable).mul hh.aestronglyMeasurable
  · unfold psiT
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by linarith [sWin_le_one (D := D) hW x])]
    have := sWin_nonneg (D := D) hW x
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)

/-- Fourier coefficients of `ψ̃` at `2πk`: `‖ψ̃^(k)‖ ≤ k^{-c} + 2D(a√(π/b) + e^{-b(k/4)²/2}√(2π/b))`,
`a = (3k/4)^{-c}`, `b = 2π²W²`, for `k ≥ 2`, `c ≥ 0`. -/
theorem psiT_coeff_bound {h : ℝ → ℝ} (hh : Integrable h) {D W : ℝ} (hW : 0 < W) (hD : 0 ≤ D) {c : ℝ}
    (hc : 0 ≤ c) (H1 : ∀ x : ℝ, ‖Fh h (x : ℂ)‖ ≤ 1)
    (H2 : ∀ x : ℝ, 1 ≤ |x| → ‖Fh h (x : ℂ)‖ ≤ |x| ^ (-c)) {k : ℝ} (hk : 2 ≤ k) :
    ‖fhat (psiT h D W) (2 * π * k)‖ ≤ k ^ (-c) +
      2 * D * ((3 * k / 4) ^ (-c) * √(π / (2 * π ^ 2 * W ^ 2)) +
        1 * Real.exp (-(2 * π ^ 2 * W ^ 2) * (k / 4) ^ 2 / 2) * √(2 * π / (2 * π ^ 2 * W ^ 2))) := by
  set e : ℝ → ℂ := fun x => Complex.exp (-(2 * π * Complex.I * k * x)) with he
  have he_norm : ∀ x, ‖e x‖ = 1 := fun x => by
    simp only [he, Complex.norm_exp]; simp
  have hecont : Continuous e := by simp only [he]; fun_prop
  have hint1 : Integrable (fun x => (h x : ℂ) * e x) := by
    refine hh.norm.mono' ?_ (ae_of_all _ fun x => ?_)
    · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hh.aestronglyMeasurable).mul
        hecont.aestronglyMeasurable
    · rw [norm_mul, he_norm, mul_one, Complex.norm_real]
  have hint2 : Integrable (fun x => (sWin D W x : ℂ) * (h x : ℂ) * e x) := by
    refine hh.norm.mono' ?_ (ae_of_all _ fun x => ?_)
    · exact ((Complex.continuous_ofReal.comp (continuous_sWin D W)).aestronglyMeasurable.mul
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hh.aestronglyMeasurable)).mul
        hecont.aestronglyMeasurable
    · rw [norm_mul, norm_mul, he_norm, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (sWin_nonneg hW x)]
      exact mul_le_of_le_one_left (norm_nonneg _) (sWin_le_one hW x)
  have eq1 : Fh h (((-k : ℝ)) : ℂ) = ∫ x, (h x : ℂ) * e x := by
    unfold Fh
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [he]
    congr 2; push_cast; ring
  have eq2 : (∫ Δ : ℝ, (sWin D W Δ : ℂ) * (h Δ : ℂ) * Complex.exp (-(2 * π * Complex.I * k * Δ))) =
      ∫ x, (sWin D W x : ℂ) * (h x : ℂ) * e x := rfl
  have hsplit : fhat (psiT h D W) (2 * π * k) =
      Fh h (((-k : ℝ)) : ℂ) -
        ∫ Δ : ℝ, (sWin D W Δ : ℂ) * (h Δ : ℂ) * Complex.exp (-(2 * π * Complex.I * k * Δ)) := by
    rw [eq1, eq2, ← integral_sub hint1 hint2]
    unfold fhat
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [psiT, he]
    have : Complex.exp (-(Complex.I * ((2 * π * k : ℝ) : ℂ) * x)) =
        Complex.exp (-(2 * π * Complex.I * k * x)) := by
      congr 2; push_cast; ring
    rw [this]
    push_cast
    ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · have := H2 (-k) (by rw [abs_neg, abs_of_nonneg (by linarith)]; linarith)
    rwa [abs_neg, abs_of_nonneg (by linarith)] at this
  · have hk0 : 0 < 3 * k / 4 := by linarith
    refine windowCoeff_bound hh hW hD k (k / 4) ((3 * k / 4) ^ (-c)) 1 (by linarith)
      (by positivity) zero_le_one H1 (fun ω hω => ?_)
    have habs : 3 * k / 4 ≤ |ω - k| := by
      have h1 := abs_le.mp hω
      rw [abs_of_nonpos (by linarith)]; linarith
    refine (H2 (ω - k) (by linarith)).trans ?_
    exact Real.rpow_le_rpow_of_nonpos hk0 habs (by linarith)

/-- **Far-tail Fejér positivity.**  For `n ≥ 2`, any phase `φ`, and `ψ̃ = (1 - s_{D,W}) h`:
`∫ ψ̃ (1 + 2cos(2πΔ + φ)) ≥ -n‖ψ̃₋‖₁ - (2/n)‖ψ̃‖₁ - 2 Σ_{k=2}^{n-1} (coefficient bound at k)`. -/
theorem psiT_fejer {h : ℝ → ℝ} (hh : Integrable h) {D W : ℝ} (hW : 0 < W) (hD : 0 ≤ D) {c : ℝ}
    (hc : 0 ≤ c) (H1 : ∀ x : ℝ, ‖Fh h (x : ℂ)‖ ≤ 1)
    (H2 : ∀ x : ℝ, 1 ≤ |x| → ‖Fh h (x : ℂ)‖ ≤ |x| ^ (-c)) {n : ℕ} (hn : 2 ≤ n) (φ : ℝ) :
    -((n : ℝ) * ∫ x, max (-psiT h D W x) 0) - (2 / n) * (∫ x, |psiT h D W x|)
        - 2 * ∑ k ∈ Ico 2 n, ((k : ℝ) ^ (-c) +
          2 * D * (((3 * (k : ℝ) / 4) ^ (-c) * √(π / (2 * π ^ 2 * W ^ 2)) +
          1 * Real.exp (-(2 * π ^ 2 * W ^ 2) * ((k : ℝ) / 4) ^ 2 / 2) *
            √(2 * π / (2 * π ^ 2 * W ^ 2)))))
      ≤ ∫ x, psiT h D W x * (1 + 2 * Real.cos (2 * π * x + φ)) := by
  have hψ := integrable_psiT hh hW (D := D)
  have := ct_fejer hψ hn (2 * π) φ
  refine le_trans ?_ this
  have hsum : ∑ k ∈ Ico 2 n, ‖fhat (psiT h D W) ((k : ℝ) * (2 * π))‖ ≤ ∑ k ∈ Ico 2 n, ((k : ℝ) ^ (-c) +
          2 * D * (((3 * (k : ℝ) / 4) ^ (-c) * √(π / (2 * π ^ 2 * W ^ 2)) +
          1 * Real.exp (-(2 * π ^ 2 * W ^ 2) * ((k : ℝ) / 4) ^ 2 / 2) *
            √(2 * π / (2 * π ^ 2 * W ^ 2))))) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Ico.mp hk).1
    have := psiT_coeff_bound hh hW hD hc H1 H2 hk2
    rwa [show (k : ℝ) * (2 * π) = 2 * π * k by ring]
  linarith

/-! ### The Hankel instance -/

open FormalResearch.SignUncertainty.HankelModular in
/-- The density `h = 1_{Δ>0} f ρ₀` of `ct:boas` Step 1. -/
noncomputable def hankelDensity (c : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  Set.indicator (Ioi (0 : ℝ)) (fun s => f s * hankelRho0 c s)

open FormalResearch.SignUncertainty.HankelModular in
lemma Fh_hankelDensity (c : ℝ) (f : ℝ → ℝ) (z : ℂ) : Fh (hankelDensity c f) z = hankelF c f z := by
  unfold Fh hankelDensity hankelF eK
  rw [← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  by_cases hs : s ∈ Ioi (0 : ℝ)
  · simp [Set.indicator_of_mem hs]
  · simp [Set.indicator_of_notMem hs]

open FormalResearch.SignUncertainty.HankelModular in
/-- **`ct:boas` Step 1, Hankel instance.**  For `f ∈ 𝒜_c^ε` (`c > 1/2`, `ε² = 1`) with `M[f] = 1`, the density
`ψ̃ = (1 - s_{D,W}) 1_{Δ>0} f ρ₀` satisfies the far-tail Fejér inequality of `psiT_fejer`, the two hypotheses on
`Fh` being `|F| ≤ M[f] = 1` and `|F(x)| ≤ |x|^{-c}` (`hankelF_bound`). -/
theorem hankel_psiT_fejer {c ε : ℝ} (hc : 1 / 2 < c) (hε : ε * ε = 1) {f : ℝ → ℝ}
    (hf : IsHankelEigenfn c ε f) (hM : hankelMass c f = 1) {D W : ℝ} (hW : 0 < W) (hD : 0 ≤ D)
    {n : ℕ} (hn : 2 ≤ n) (φ : ℝ) :
    -((n : ℝ) * ∫ x, max (-psiT (hankelDensity c f) D W x) 0) -
        (2 / n) * (∫ x, |psiT (hankelDensity c f) D W x|)
        - 2 * ∑ k ∈ Ico 2 n, ((k : ℝ) ^ (-c) +
          2 * D * (((3 * (k : ℝ) / 4) ^ (-c) * √(π / (2 * π ^ 2 * W ^ 2)) +
          1 * Real.exp (-(2 * π ^ 2 * W ^ 2) * ((k : ℝ) / 4) ^ 2 / 2) *
            √(2 * π / (2 * π ^ 2 * W ^ 2)))))
      ≤ ∫ x, psiT (hankelDensity c f) D W x * (1 + 2 * Real.cos (2 * π * x + φ)) := by
  have hc0 : 0 < c := by linarith
  have hint : Integrable (hankelDensity c f) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hf.int
  have hnorm : (∫ s in Ioi (0 : ℝ), ‖f s * hankelRho0 c s‖) = 1 := by
    rw [← hM]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    simp only [norm_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (hankelRho0_nonneg hc0 (le_of_lt hs))]
  have H2 : ∀ x : ℝ, 1 ≤ |x| → ‖Fh (hankelDensity c f) (x : ℂ)‖ ≤ |x| ^ (-c) := by
    intro x hx
    rw [Fh_hankelDensity]
    have := hankelF_bound hc hε hf (x := x) (by intro h0; simp [h0] at hx; linarith)
    rwa [hnorm, one_mul] at this
  have H1 : ∀ x : ℝ, ‖Fh (hankelDensity c f) (x : ℂ)‖ ≤ 1 := by
    intro x
    rw [Fh_hankelDensity]
    unfold hankelF
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    rw [← hnorm]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp only [norm_mul, norm_eK, Complex.ofReal_im, mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one,
      Complex.norm_real]
  exact psiT_fejer hint hW hD hc0.le H1 H2 hn φ

/-- info: 'FormalResearch.SignUncertainty.CtBoasWindow.psiT_fejer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.CtBoasWindow.psiT_fejer

/-- info: 'FormalResearch.SignUncertainty.CtBoasWindow.hankel_psiT_fejer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.CtBoasWindow.hankel_psiT_fejer

end FormalResearch.SignUncertainty.CtBoasWindow
