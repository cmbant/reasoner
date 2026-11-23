module

public import FormalResearch.ModularBootstrap.Upper.Saddle.EdgeNormalForm
public import FormalResearch.ModularBootstrap.Upper.Comb.Riesz
public import FormalResearch.ModularBootstrap.Upper.Comb.EdgePhase

/-!
# Edge phase `Φ₀` of the reference Blaschke comb (`edge_transform_sd.tex`, Lemma `SD_0`)

Lemma `SD_0` (`esd:phase`) and (SD.2): the leading continuous Blaschke potential
$\Phi_0(b)=\int_{\xi_*}^\infty\rho_U(y)\log[-\tanh\frac{\pi(b-y)}2\tanh\frac{\pi(b+y)}2]\,dy$,
with the branch `phiZeta` of `Upper.Comb.Factors` (`exp (phiZeta y b) = -tanh tanh`) used in
Lemmas `K2`/`K3`, satisfies `EdgePhaseData`:

* `edgePhi0Blaschke`: the explicit potential (equal to `Upper.Comb.phi0`).
* `edgePhi0Blaschke_hasDerivAt`: holomorphy on `|Im b - 1/2| < 17/64` by differentiation under
  the integral sign.
* `edgePhi0Blaschke_re_edge`: `Re Φ₀(v + i/2) = 0`.
* `edgePhi0Blaschke_deriv_edge`: `Φ₀'(v + i/2) = -(4πi/3) F(v)` with `F = edgeF`
  (`F(v) = π⁻¹ arsinh (cosh πv)`). The proof does not use the strip Poisson identity (SD.0a):
  by Lemma `K2` (`riesz_representation`), `Re Φ₀ = U = Im Φ_U` on `1/4 < Im b < 1/2`, hence
  `Φ₀' = -i Φ_U'= -(4πi/3) p`, where `p = pMap = π⁻¹ arsinh (-i sinh πb)` is the derivative of the
  holomorphic completion of the harmonic majorant; `p(v + i/2) = F(v)` and `Φ₀'` is continuous up to
  `E_+`.
* `edgePhaseData_blaschke`: `EdgePhaseData δ C₃ C₄ Φ₀` (all `δ ∈ (0, 1/4)`) (SD.2), the derivative bounds being
  transported from the model witness of `edgePhaseData_nonvacuous` by the identity theorem.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Upper.Saddle

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.PoissonJensen

/-! ### 1. The explicit potential and its integrability -/

/-- The leading continuous Blaschke potential
`Φ₀(b) = ∫_{ξ_*}^∞ ρ_U(y) φ_y(b) dy` of Lemma `SD_0`, where `φ_y(b) = log(-T_y(b))` is the strip
branch `phiZeta` (see `cexp_phiZeta_blaschke`). -/
noncomputable def edgePhi0Blaschke (b : ℂ) : ℂ :=
  ∫ y in Ioi xiStar, (rhoU y : ℂ) * phiZeta (y : ℂ) b

lemma edgePhi0Blaschke_eq_phi0 (b : ℂ) : edgePhi0Blaschke b = phi0 b := rfl

/-- The branch: `exp φ_y(b) = -tanh(π(b-y)/2) tanh(π(b+y)/2)` for `b ∈ 𝒩`, `y ≥ 0`. -/
lemma cexp_phiZeta_blaschke {y : ℝ} (hy : 0 ≤ y) {b : ℂ} (hb : b ∈ combN) :
    Complex.exp (phiZeta (y : ℂ) b) =
      -(Complex.tanh ((π : ℂ) * (b - y) / 2) * Complex.tanh ((π : ℂ) * (b + y) / 2)) :=
  cexp_phiZeta hb ⟨by simpa using hy, by simp⟩

private lemma rhoU_le_lin {y : ℝ} (hy : xiStar ≤ y) :
    rhoU y ≤ (4 / 3 : ℝ) * y + 4 / (3 * π) := by
  have hpi := Real.pi_pos
  rw [rhoU_eq_of_ge hy]
  have hs1 : 1 ≤ Real.sinh (π * y) := by
    rw [← sinh_pi_mul_xiStar]; exact Real.sinh_le_sinh.mpr (by nlinarith)
  have hsh_le : 2 * Real.sinh (π * y) ≤ Real.exp (π * y) := by
    rw [Real.sinh_eq]; linarith [Real.exp_pos (-(π * y))]
  have hlog_le : arccoshR (Real.sinh (π * y)) ≤ π * y := by
    unfold arccoshR
    have hsqrt : √(Real.sinh (π * y) ^ 2 - 1) ≤ Real.sinh (π * y) := by
      rw [Real.sqrt_le_left (by linarith [xiStar_pos, hy])]; nlinarith
    calc Real.log (Real.sinh (π * y) + √(Real.sinh (π * y) ^ 2 - 1))
        ≤ Real.log (2 * Real.sinh (π * y)) :=
          Real.log_le_log (by positivity) (by linarith)
      _ ≤ Real.log (Real.exp (π * y)) := Real.log_le_log (by positivity) hsh_le
      _ = π * y := Real.log_exp _
  calc (4 / (3 * π)) * arccoshR (Real.sinh (π * y))
      ≤ (4 / (3 * π)) * (π * y) := by gcongr
    _ = (4 / 3) * y := by field_simp [hpi.ne']
    _ ≤ (4 / 3) * y + 4 / (3 * π) := le_add_of_nonneg_right (by positivity)

private lemma integrableOn_rhoU_exp :
    IntegrableOn (fun y : ℝ => rhoU y * Real.exp (-π * y)) (Ioi xiStar) volume := by
  have hpi := Real.pi_pos
  have hcont : ContinuousOn (fun y : ℝ => rhoU y * Real.exp (-π * y)) (Ioi xiStar) :=
    (continuousOn_rhoU.mono Ioi_subset_Ici_self).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have h1 : IntegrableOn (fun y : ℝ => y * Real.exp (-π * y)) (Ioi (0 : ℝ)) volume := by
    have hle : ∀ y ∈ Ioi (0 : ℝ), ‖y * Real.exp (-π * y)‖ ≤ (2 / π) * Real.exp (-(π / 2) * y) := by
      intro y hy
      have hy0 : 0 < y := hy
      rw [Real.norm_of_nonneg (mul_nonneg hy0.le (Real.exp_pos _).le)]
      have hexp : (π / 2) * y ≤ Real.exp ((π / 2) * y) := by
        linarith [Real.add_one_lt_exp (show (π / 2) * y ≠ 0 by positivity)]
      calc y * Real.exp (-π * y) = (2 / π) * ((π / 2) * y) * Real.exp (-π * y) := by
            field_simp [hpi.ne']
        _ ≤ (2 / π) * Real.exp ((π / 2) * y) * Real.exp (-π * y) := by gcongr
        _ = (2 / π) * Real.exp (-(π / 2) * y) := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    exact ((integrableOn_exp_mul_Ioi (by linarith : -(π / 2) < 0) 0).const_mul (2 / π)).mono'
      (continuous_id.mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi hle)
  have h2 : IntegrableOn (fun y : ℝ => Real.exp (-π * y)) (Ioi (0 : ℝ)) volume :=
    integrableOn_exp_mul_Ioi (by linarith : -π < 0) 0
  have hdom : IntegrableOn (fun y : ℝ => ((4 / 3 : ℝ) * y + 4 / (3 * π)) * Real.exp (-π * y))
      (Ioi (0 : ℝ)) volume := by
    have heq : (fun y : ℝ => ((4 / 3 : ℝ) * y + 4 / (3 * π)) * Real.exp (-π * y)) =
        fun y => (4 / 3 : ℝ) * (y * Real.exp (-π * y)) + (4 / (3 * π)) * Real.exp (-π * y) := by
      ext y; ring
    rw [heq]; exact (h1.const_mul _).add (h2.const_mul _)
  refine (hdom.mono_set (Ioi_subset_Ioi xiStar_pos.le)).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (rhoU_nonneg y) (Real.exp_pos _).le)]
  exact mul_le_mul_of_nonneg_right (rhoU_le_lin hy.le) (Real.exp_pos _).le

private lemma ofReal_mem_combZ' {y : ℝ} (hy : 0 ≤ y) : (y : ℂ) ∈ combZ :=
  ⟨by simpa using hy, by simp⟩

private lemma ofReal_mem_combZOpen' {y : ℝ} (hy : -1 / 4 < y) : (y : ℂ) ∈ combZOpen :=
  ⟨by simpa using hy, by simp⟩

private lemma continuousOn_combPhiDeriv_real (i : ℕ) {b : ℂ} (hb : b ∈ combNMid) :
    ContinuousOn (fun y : ℝ => combPhiDeriv i 0 (y : ℂ) b) (Ioi xiStar) := by
  intro y hy
  have hζ : (y : ℂ) ∈ combZOpen := ofReal_mem_combZOpen' (by linarith [xiStar_pos, hy.out])
  exact ((hasDerivAt_combPhiDeriv_zeta (i := i) (j := 0)
    (combNMid_subset_combNOpen hb) hζ).continuousAt.comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt

/-- Domination of `ρ_U(y) ∂_b^i φ_y(b)` uniformly on a horizontal-radius-one ball in `𝒩_mid`. -/
private lemma norm_rhoU_combPhiDeriv_le {i : ℕ} (hi : i ≤ 4) :
    ∃ C > 0, ∀ {b : ℂ}, b ∈ combNMid → ∀ {y : ℝ}, xiStar < y →
      ‖(rhoU y : ℂ) * combPhiDeriv i 0 (y : ℂ) b‖ ≤
        C * Real.exp (π * |b.re|) * (rhoU y * Real.exp (-π * y)) := by
  obtain ⟨C, hC, _, hbd⟩ := combPhiDeriv_bound
  refine ⟨C, hC, fun {b} hb {y} hy => ?_⟩
  have hζ : (y : ℂ) ∈ combZ := ofReal_mem_combZ' (xiStar_pos.le.trans hy.le)
  have h1 := (hbd i 0 (by omega) hb hζ).trans
    (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
  have hexp : C * Real.exp (-π * ((y : ℂ).re - |b.re|)) =
      C * Real.exp (π * |b.re|) * Real.exp (-π * y) := by
    rw [Complex.ofReal_re, show -π * (y - |b.re|) = π * |b.re| + -π * y by ring, Real.exp_add]
    ring
  rw [hexp] at h1
  calc ‖(rhoU y : ℂ) * combPhiDeriv i 0 (y : ℂ) b‖
      = rhoU y * ‖combPhiDeriv i 0 (y : ℂ) b‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (rhoU_nonneg y)]
    _ ≤ rhoU y * (C * Real.exp (π * |b.re|) * Real.exp (-π * y)) := by
        gcongr; exact rhoU_nonneg y
    _ = C * Real.exp (π * |b.re|) * (rhoU y * Real.exp (-π * y)) := by ring

private lemma integrableOn_rhoU_combPhiDeriv {i : ℕ} (hi : i ≤ 4) {b : ℂ} (hb : b ∈ combNMid) :
    IntegrableOn (fun y : ℝ => (rhoU y : ℂ) * combPhiDeriv i 0 (y : ℂ) b) (Ioi xiStar) volume := by
  obtain ⟨C, hC, hbd⟩ := norm_rhoU_combPhiDeriv_le hi
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ => (rhoU y : ℂ) * combPhiDeriv i 0 (y : ℂ) b) (volume.restrict (Ioi xiStar)) := by
    have hcont : ContinuousOn (fun y : ℝ => (rhoU y : ℂ) * combPhiDeriv i 0 (y : ℂ) b)
        (Ioi xiStar) :=
      (Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_rhoU.mono Ioi_subset_Ici_self)).mul (continuousOn_combPhiDeriv_real i hb)
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  exact (integrableOn_rhoU_exp.const_mul (C * Real.exp (π * |b.re|))).mono' hmeas
    (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => hbd hb hy)

/-! ### 2. Holomorphy of `Φ₀` on `|Im b - 1/2| < 17/64` -/

private lemma abs_re_le_of_mem_ball {b b' : ℂ} {r : ℝ} (hr : r ≤ 1) (hb' : b' ∈ ball b r) :
    |b'.re| ≤ |b.re| + 1 := by
  have h : |b'.re - b.re| ≤ ‖b' - b‖ :=
    (Complex.abs_re_le_norm (b' - b)).trans_eq' (by simp)
  have h2 : ‖b' - b‖ < r := by simpa [dist_eq_norm] using hb'
  calc |b'.re| = |(b'.re - b.re) + b.re| := by ring_nf
    _ ≤ |b'.re - b.re| + |b.re| := abs_add_le _ _
    _ ≤ |b.re| + 1 := by linarith

/-- `Φ₀` is complex differentiable on `combNMid` with the derivative obtained by differentiating
under the integral sign. -/
lemma edgePhi0Blaschke_hasDerivAt {b : ℂ} (hb : b ∈ combNMid) :
    HasDerivAt edgePhi0Blaschke
      (∫ y in Ioi xiStar, (rhoU y : ℂ) * combPhiDeriv 1 0 (y : ℂ) b) b := by
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.isOpen_iff.mp isOpen_combNMid b hb
  obtain ⟨C, hC, hbd⟩ := norm_rhoU_combPhiDeriv_le (i := 1) (by norm_num)
  set ε : ℝ := min ε₁ 1 with hε
  have hε0 : 0 < ε := lt_min hε₁ one_pos
  have hεball : ball b ε ⊆ combNMid := (ball_subset_ball (min_le_left _ _)).trans hball
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi xiStar))
    (F := fun (b' : ℂ) (y : ℝ) => (rhoU y : ℂ) * phiZeta (y : ℂ) b')
    (F' := fun (b' : ℂ) (y : ℝ) => (rhoU y : ℂ) * combPhiDeriv 1 0 (y : ℂ) b')
    (x₀ := b)
    (bound := fun y => C * Real.exp (π * (|b.re| + 1)) * (rhoU y * Real.exp (-π * y)))
    (ball_mem_nhds b hε0) ?_ ?_ ?_ ?_ ?_ ?_
  · exact hres.2
  · refine Filter.eventually_of_mem (ball_mem_nhds b hε0) fun b' hb' => ?_
    have hmid := hεball hb'
    have := integrableOn_rhoU_combPhiDeriv (i := 0) (by norm_num) hmid
    simpa [combPhiDeriv_zero] using this.aestronglyMeasurable
  · have h : IntegrableOn (fun y : ℝ => (rhoU y : ℂ) * phiZeta (y : ℂ) b) (Ioi xiStar) volume := by
      simpa [combPhiDeriv_zero] using
        integrableOn_rhoU_combPhiDeriv (i := 0) (by norm_num) hb
    exact h
  · exact (integrableOn_rhoU_combPhiDeriv (i := 1) (by norm_num) hb).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy b' hb' => ?_
    have hmid := hεball hb'
    refine (hbd hmid hy).trans ?_
    have hre := abs_re_le_of_mem_ball (min_le_right ε₁ 1) hb'
    have : Real.exp (π * |b'.re|) ≤ Real.exp (π * (|b.re| + 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hre Real.pi_pos.le)
    have hnn : 0 ≤ rhoU y * Real.exp (-π * y) := mul_nonneg (rhoU_nonneg y) (Real.exp_pos _).le
    gcongr
  · exact integrableOn_rhoU_exp.const_mul _
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy b' hb' => ?_
    have hmid := hεball hb'
    have hζ : (y : ℂ) ∈ combZOpen := ofReal_mem_combZOpen' (by linarith [xiStar_pos, hy.out])
    have h := (hasDerivAt_combPhiDeriv_b (i := 0) (j := 0)
      (combNMid_subset_combNOpen hmid) hζ).const_mul (rhoU y : ℂ)
    simpa [combPhiDeriv_zero] using h

lemma edgePhi0Blaschke_differentiableOn : DifferentiableOn ℂ edgePhi0Blaschke combNMid :=
  fun _ hb => (edgePhi0Blaschke_hasDerivAt hb).differentiableAt.differentiableWithinAt

lemma edgePhi0Blaschke_analyticOnNhd : AnalyticOnNhd ℂ edgePhi0Blaschke combNMid :=
  edgePhi0Blaschke_differentiableOn.analyticOnNhd isOpen_combNMid

/-! ### 3. Real part: `Re Φ₀ = 0` on `E_+` and `Re Φ₀ = U` below it -/

lemma re_phiZeta_eq_log_norm {y : ℝ} (hy : 0 ≤ y) {b : ℂ} (hb : b ∈ combN) :
    (phiZeta (y : ℂ) b).re = Real.log ‖blaschkeT (y : ℂ) b‖ := by
  have h := cexp_phiZeta hb (ofReal_mem_combZ' hy)
  have h2 : Real.exp (phiZeta (y : ℂ) b).re = ‖blaschkeT (y : ℂ) b‖ := by
    rw [← Complex.norm_exp, h, norm_neg]
  rw [← h2, Real.log_exp]

private lemma re_edgePhi0Blaschke_eq {b : ℂ} (hb : b ∈ combNMid) :
    (edgePhi0Blaschke b).re = ∫ y in Ioi xiStar, rhoU y * (phiZeta (y : ℂ) b).re := by
  have hint : IntegrableOn (fun y : ℝ => (rhoU y : ℂ) * phiZeta (y : ℂ) b) (Ioi xiStar) volume := by
    simpa [combPhiDeriv_zero] using integrableOn_rhoU_combPhiDeriv (i := 0) (by norm_num) hb
  have h := Complex.reCLM.integral_comp_comm hint
  unfold edgePhi0Blaschke
  rw [← Complex.reCLM_apply, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  simp [Complex.mul_re]

/-- `Re Φ₀(v + i/2) = 0` (first claim of (SD.0)): the modulus-one fact `|T_y| = 1` on `E_+`
together with the branch `φ_y`. -/
theorem edgePhi0Blaschke_re_edge (v : ℝ) :
    (edgePhi0Blaschke ((v : ℂ) + Complex.I / 2)).re = 0 := by
  have hb_im : ((v : ℂ) + Complex.I / 2).im = 1 / 2 := by simp
  have hb : ((v : ℂ) + Complex.I / 2) ∈ combN := by
    change |((v : ℂ) + Complex.I / 2).im - 1 / 2| ≤ 1 / 4
    rw [hb_im]; norm_num
  rw [re_edgePhi0Blaschke_eq (combN_subset_combNMid hb)]
  refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
  rw [phiZeta_re_eq_zero_of_im_half (xiStar_pos.le.trans hy.out.le) hb_im, mul_zero]

/-- Below `E_+` (`1/4 < Im b < 1/2`), `Re Φ₀ = Im Φ_U`, the harmonic majorant `U = majorant2D`
(Lemma `K2`, `riesz_representation`). -/
theorem re_edgePhi0Blaschke_eq_majorant {b : ℂ} (h1 : 1 / 4 < b.im) (h2 : b.im < 1 / 2) :
    (edgePhi0Blaschke b).re = majorant2D b := by
  have hbN : b ∈ combN := by
    change |b.im - 1 / 2| ≤ 1 / 4
    rw [abs_le]; constructor <;> linarith
  have hbs : b ∈ slitStrip := by
    refine ⟨abs_lt.mpr ⟨by linarith, h2⟩, ?_⟩
    rintro ⟨him, _⟩
    linarith
  rw [re_edgePhi0Blaschke_eq (combN_subset_combNMid hbN)]
  have hK2 := riesz_representation (b := b) (abs_le.mpr ⟨by linarith, by linarith⟩)
  rw [majorantUExt_of_mem_slitStrip hbs] at hK2
  rw [← hK2]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  rw [re_phiZeta_eq_log_norm (xiStar_pos.le.trans hy.out.le) hbN]

/-! ### 4. A holomorphic function with vanishing real part has zero derivative -/

private lemma re_mul_deriv_eq_zero {f : ℂ → ℂ} {f' b : ℂ} (hf : HasDerivAt f f' b)
    (hre : ∀ᶠ w in 𝓝 b, (f w).re = 0) (c : ℂ) : (c * f').re = 0 := by
  have hh : HasDerivAt (fun t : ℝ => b + (t : ℂ) * c) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const c).const_add b
  have hcomp := hf.scomp_of_eq (x := (0 : ℝ)) hh (by simp)
  have hre_comp := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcomp
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), (Complex.reCLM ∘ (f ∘ fun t : ℝ => b + (t : ℂ) * c)) t = 0 := by
    have hcont : Tendsto (fun t : ℝ => b + (t : ℂ) * c) (𝓝 0) (𝓝 b) := by
      simpa using hh.continuousAt.tendsto
    exact hcont.eventually hre
  have h0 := (hre_comp.congr_of_eventuallyEq (f₁ := fun _ => (0 : ℝ))
    (hev.mono fun t ht => ht.symm)).unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  simpa [mul_comm, Complex.mul_re] using h0

private lemma deriv_eq_zero_of_re_eq_zero {f : ℂ → ℂ} {f' b : ℂ} (hf : HasDerivAt f f' b)
    (hre : ∀ᶠ w in 𝓝 b, (f w).re = 0) : f' = 0 := by
  have h1 := re_mul_deriv_eq_zero hf hre 1
  have h2 := re_mul_deriv_eq_zero hf hre Complex.I
  simp only [one_mul, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at h1 h2
  exact Complex.ext h1 (by simpa using h2)

/-! ### 5. `Φ₀' = -(4πi/3) p` below `E_+`, and its boundary value -/

private lemma mem_slitStrip_of_lower {b : ℂ} (h1 : 1 / 4 < b.im) (h2 : b.im < 1 / 2) :
    b ∈ slitStrip := by
  refine ⟨abs_lt.mpr ⟨by linarith, h2⟩, ?_⟩
  rintro ⟨him, _⟩
  linarith

private lemma mem_combNMid_of_lower {b : ℂ} (h1 : 1 / 4 < b.im) (h2 : b.im < 1 / 2) :
    b ∈ combNMid := by
  change |b.im - 1 / 2| < 17 / 64
  rw [abs_lt]; constructor <;> linarith

/-- For `1/4 < Im b < 1/2`: `Φ₀'(b) = -(4πi/3) p(b)` with `p = pMap`
(`p = π⁻¹ arsinh (-i sinh πb)`, the derivative of the holomorphic completion of `U`). -/
theorem hasDerivAt_edgePhi0Blaschke_lower {b : ℂ} (h1 : 1 / 4 < b.im) (h2 : b.im < 1 / 2) :
    HasDerivAt edgePhi0Blaschke (-Complex.I * ((4 * π / 3 : ℝ) : ℂ) * pMap b) b := by
  have hΦ := edgePhi0Blaschke_hasDerivAt (mem_combNMid_of_lower h1 h2)
  have hG := hasDerivAt_majorantHolomorphic (mem_slitStrip_of_lower h1 h2)
  have hf := hΦ.add (hG.const_mul Complex.I)
  have hnhds : {w : ℂ | 1 / 4 < w.im ∧ w.im < 1 / 2} ∈ 𝓝 b :=
    (isOpen_Ioo.preimage Complex.continuous_im).mem_nhds ⟨h1, h2⟩
  have hre : ∀ᶠ w in 𝓝 b, ((fun w => edgePhi0Blaschke w + Complex.I * majorantHolomorphic w) w).re
      = 0 := by
    filter_upwards [hnhds] with w hw
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_sub]
    rw [re_edgePhi0Blaschke_eq_majorant hw.1 hw.2]
    unfold majorant2D
    ring
  have h0 := deriv_eq_zero_of_re_eq_zero hf hre
  have h3 : (∫ y in Ioi xiStar, (rhoU y : ℂ) * combPhiDeriv 1 0 (y : ℂ) b) =
      -Complex.I * ((4 * π / 3 : ℝ) : ℂ) * pMap b := by
    linear_combination h0
  rw [← h3]
  exact hΦ

/-- `p(v + i/2) = F(v)`: the boundary value of `p = pMap` on `E_+` is `π⁻¹ arsinh (cosh πv)`. -/
theorem pMap_edge (v : ℝ) : pMap ((v : ℂ) + Complex.I / 2) = (edgeF v : ℂ) := by
  have hsinh : Complex.sinh ((π : ℂ) * ((v : ℂ) + Complex.I / 2)) =
      ((Real.cosh (π * v) : ℝ) : ℂ) * Complex.I := by
    have hmul : (π : ℂ) * ((v : ℂ) + Complex.I / 2) =
        ((π * v : ℝ) : ℂ) + ((π / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hmul, Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    push_cast
    ring
  have harg : -Complex.I * Complex.sinh ((π : ℂ) * ((v : ℂ) + Complex.I / 2)) =
      ((Real.cosh (π * v) : ℝ) : ℂ) := by
    rw [hsinh]
    linear_combination (-((Real.cosh (π * v) : ℝ) : ℂ)) * Complex.I_sq
  unfold pMap edgeF
  rw [harg]
  unfold complexArsinh
  set c : ℝ := Real.cosh (π * v) with hc
  have h1pos : 0 < c ^ 2 + 1 := by positivity
  have hcpow : ((c : ℂ) ^ 2 + 1) ^ (1 / 2 : ℂ) = ((√(c ^ 2 + 1) : ℝ) : ℂ) := by
    have h1c : (c : ℂ) ^ 2 + 1 = ((c ^ 2 + 1 : ℝ) : ℂ) := by push_cast; ring
    have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [h1c, hhalf, ← Complex.ofReal_cpow h1pos.le, ← Real.sqrt_eq_rpow]
  have hcpos : 0 < Real.cosh (π * v) := Real.cosh_pos _
  have harg_pos : 0 < c + √(c ^ 2 + 1) := by positivity
  rw [hcpow, ← Complex.ofReal_add, ← Complex.ofReal_log harg_pos.le]
  have h_ars : Real.arsinh c = Real.log (c + √(c ^ 2 + 1)) := by
    unfold Real.arsinh
    rw [add_comm (1 : ℝ) (c ^ 2)]
  rw [← h_ars]
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  push_cast
  field_simp

private lemma continuousAt_pMap_edge (v : ℝ) : ContinuousAt pMap ((v : ℂ) + Complex.I / 2) := by
  have hsinh : Complex.sinh ((π : ℂ) * ((v : ℂ) + Complex.I / 2)) =
      ((Real.cosh (π * v) : ℝ) : ℂ) * Complex.I := by
    have hmul : (π : ℂ) * ((v : ℂ) + Complex.I / 2) =
        ((π * v : ℝ) : ℂ) + ((π / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hmul, Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    push_cast
    ring
  have harg : -Complex.I * Complex.sinh ((π : ℂ) * ((v : ℂ) + Complex.I / 2)) =
      ((Real.cosh (π * v) : ℝ) : ℂ) := by
    rw [hsinh]
    linear_combination (-((Real.cosh (π * v) : ℝ) : ℂ)) * Complex.I_sq
  have hdom : -Complex.I * Complex.sinh ((π : ℂ) * ((v : ℂ) + Complex.I / 2)) ∈ arsinhDomain := by
    rw [harg]
    change ((Real.cosh (π * v) : ℝ) : ℂ) ^ 2 + 1 ∈ Complex.slitPlane
    have : ((Real.cosh (π * v) : ℝ) : ℂ) ^ 2 + 1 = (((Real.cosh (π * v)) ^ 2 + 1 : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.mem_slitPlane_iff]
    left
    rw [Complex.ofReal_re]
    positivity
  have hAr : ContinuousAt complexArsinh
      (-Complex.I * Complex.sinh ((π : ℂ) * ((v : ℂ) + Complex.I / 2))) :=
    (hasDerivAt_complexArsinh hdom).continuousAt
  have hin : ContinuousAt (fun z : ℂ => -Complex.I * Complex.sinh ((π : ℂ) * z))
      ((v : ℂ) + Complex.I / 2) := by fun_prop
  have hc : ContinuousAt (fun b : ℂ => complexArsinh (-Complex.I * Complex.sinh ((π : ℂ) * b)))
      ((v : ℂ) + Complex.I / 2) :=
    ContinuousAt.comp (f := fun z : ℂ => -Complex.I * Complex.sinh ((π : ℂ) * z))
      (g := complexArsinh) hAr hin
  exact continuousAt_const.mul hc

/-- Second claim of (SD.0): `Φ₀'(v + i/2) = -(4πi/3) F(v)`, `F = edgeF`
(`F(v) = π⁻¹ arsinh (cosh πv)`). -/
theorem edgePhi0Blaschke_deriv_edge (v : ℝ) :
    deriv edgePhi0Blaschke ((v : ℂ) + Complex.I / 2) =
      -(4 * (π : ℂ) * Complex.I / 3) * (edgeF v : ℂ) := by
  set b₀ : ℂ := (v : ℂ) + Complex.I / 2 with hb₀
  have hb₀_im : b₀.im = 1 / 2 := by simp [hb₀]
  have hb₀_mid : b₀ ∈ combNMid := by
    change |b₀.im - 1 / 2| < 17 / 64
    rw [hb₀_im]; norm_num
  have hcont : ContinuousAt (deriv edgePhi0Blaschke) b₀ :=
    (edgePhi0Blaschke_analyticOnNhd.deriv b₀ hb₀_mid).continuousAt
  have hp : Tendsto (fun t : ℝ => b₀ - (t : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 b₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have : Continuous fun t : ℝ => b₀ - (t : ℂ) * Complex.I := by fun_prop
    simpa using this.tendsto 0
  have hT1 : Tendsto (fun t : ℝ => deriv edgePhi0Blaschke (b₀ - (t : ℂ) * Complex.I))
      (𝓝[>] 0) (𝓝 (deriv edgePhi0Blaschke b₀)) := hcont.tendsto.comp hp
  have hT2 : Tendsto (fun t : ℝ => -Complex.I * ((4 * π / 3 : ℝ) : ℂ) *
      pMap (b₀ - (t : ℂ) * Complex.I)) (𝓝[>] 0)
      (𝓝 (-Complex.I * ((4 * π / 3 : ℝ) : ℂ) * pMap b₀)) :=
    ((continuousAt_pMap_edge v).tendsto.comp hp).const_mul _
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, deriv edgePhi0Blaschke (b₀ - (t : ℂ) * Complex.I) =
      -Complex.I * ((4 * π / 3 : ℝ) : ℂ) * pMap (b₀ - (t : ℂ) * Complex.I) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with t ht
    exact (hasDerivAt_edgePhi0Blaschke_lower (b := b₀ - (t : ℂ) * Complex.I)
      (by simp [hb₀_im]; linarith [ht.2]) (by simp [hb₀_im]; linarith [ht.1])).deriv
  have hlim := tendsto_nhds_unique (hT1.congr' hev) hT2
  rw [hlim, hb₀, pMap_edge]
  push_cast
  ring

/-! ### 6. Identity theorem and `EdgePhaseData` -/

private lemma iteratedDeriv_eq_of_eqOn {U : Set ℂ} (hU : IsOpen U) :
    ∀ (n : ℕ) {f g : ℂ → ℂ}, EqOn f g U → ∀ b ∈ U, iteratedDeriv n f b = iteratedDeriv n g b := by
  intro n
  induction n with
  | zero => intro f g h b hb; simpa using h hb
  | succ n ih =>
    intro f g h b hb
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    refine ih (fun w hw => ?_) b hb
    exact Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (hU.mem_nhds hw) h)

private def edgeNbhd : Set ℂ := {b : ℂ | |b.im - 1 / 2| < 1 / 4}

private lemma isOpen_edgeNbhd : IsOpen edgeNbhd :=
  isOpen_lt (continuous_abs.comp (Complex.continuous_im.sub continuous_const)) continuous_const

private lemma isPreconnected_edgeNbhd : IsPreconnected edgeNbhd := by
  have hconv : Convex ℝ edgeNbhd := by
    have : edgeNbhd = Complex.imLm ⁻¹' (Ioo (1 / 4 : ℝ) (3 / 4)) := by
      ext b
      simp only [edgeNbhd, mem_ofPred_eq, mem_preimage, Complex.imLm_coe, mem_Ioo, abs_lt]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [this]
    exact (convex_Ioo _ _).linear_preimage Complex.imLm
  exact hconv.isPreconnected

private lemma edgeNbhd_subset_combNMid : edgeNbhd ⊆ combNMid := fun b hb => by
  change |b.im - 1 / 2| < 17 / 64
  exact lt_trans (show |b.im - 1 / 2| < 1 / 4 from hb) (by norm_num)

private lemma edgeNbhd_subset_edgeStrip : edgeNbhd ⊆ edgeStrip (1 / 4) := fun b hb =>
  (show |b.im - 1 / 2| < 1 / 4 from hb).le

private lemma edgeStrip_subset_edgeNbhd {δ : ℝ} (hδ : δ < 1 / 4) : edgeStrip δ ⊆ edgeNbhd :=
  fun b hb => lt_of_le_of_lt (show |b.im - 1 / 2| ≤ δ from hb) hδ

/-- **Lemma `SD_0` (`esd:phase`), (SD.0) and (SD.2)**: the leading continuous Blaschke potential
`Φ₀ = edgePhi0Blaschke` satisfies `EdgePhaseData δ C₃ C₄ Φ₀` for every `δ ∈ (0, 1/4)`, with `C₃, C₄`
independent of `δ`: it is holomorphic on the neighbourhood `|Im b - 1/2| ≤ δ` of `E_+`, `Re Φ₀ = 0`
and `Φ₀' = -(4πi/3) F` on `E_+` (`F = edgeF`), and the third and fourth derivatives are bounded by
`C₃`, `C₄` there.

Not covered: the strip Poisson identity (SD.0a) is not used (the derivative is identified through
Lemma `K2` and the closed form `pMap` of the holomorphic completion of `U`); the constants
`C₃, C₄` are existential, produced by the explicit model witness of `edgePhaseData_nonvacuous`
which has the same derivative on `E_+`. -/
theorem edgePhaseData_blaschke : ∃ C₃ C₄ : ℝ, ∀ δ : ℝ, 0 < δ → δ < 1 / 4 →
    EdgePhaseData δ C₃ C₄ edgePhi0Blaschke := by
  obtain ⟨C₃, C₄, Φm, hm⟩ := edgePhaseData_nonvacuous (δ := 1 / 4) (by norm_num) le_rfl
  have hA1 : AnalyticOnNhd ℂ (deriv edgePhi0Blaschke) edgeNbhd :=
    (edgePhi0Blaschke_analyticOnNhd.mono edgeNbhd_subset_combNMid).deriv
  have hA2 : AnalyticOnNhd ℂ (deriv Φm) edgeNbhd :=
    (hm.holo.mono edgeNbhd_subset_edgeStrip).deriv
  have hz₀ : (Complex.I / 2 : ℂ) ∈ edgeNbhd := by
    change |(Complex.I / 2 : ℂ).im - 1 / 2| < 1 / 4
    simp
  have hfreq : ∃ᶠ z in 𝓝[≠] (Complex.I / 2 : ℂ),
      deriv edgePhi0Blaschke z = deriv Φm z := by
    have hT : Tendsto (fun t : ℝ => (t : ℂ) + Complex.I / 2) (𝓝[≠] 0)
        (𝓝[≠] (Complex.I / 2 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Continuous fun t : ℝ => (t : ℂ) + Complex.I / 2 := by fun_prop
        exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using this.tendsto 0)
      · filter_upwards [self_mem_nhdsWithin] with t ht h
        exact ht (by simpa using h)
    refine hT.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall fun t => ?_))
    rw [edgePhi0Blaschke_deriv_edge t, hm.deriv_edge t]
  have heq := hA1.eqOn_of_preconnected_of_frequently_eq hA2 isPreconnected_edgeNbhd hz₀ hfreq
  have hit : ∀ k : ℕ, ∀ b ∈ edgeNbhd,
      iteratedDeriv (k + 1) edgePhi0Blaschke b = iteratedDeriv (k + 1) Φm b := fun k b hb => by
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    exact iteratedDeriv_eq_of_eqOn isOpen_edgeNbhd k heq b hb
  refine ⟨C₃, C₄, fun δ _ hδ => ?_⟩
  have hsub : edgeStrip δ ⊆ edgeNbhd := edgeStrip_subset_edgeNbhd hδ
  refine ⟨?_, edgePhi0Blaschke_re_edge, edgePhi0Blaschke_deriv_edge, ?_, ?_⟩
  · exact edgePhi0Blaschke_analyticOnNhd.mono (hsub.trans edgeNbhd_subset_combNMid)
  · intro b hb
    rw [hit 2 b (hsub hb)]
    exact hm.deriv3_bound b (edgeNbhd_subset_edgeStrip (hsub hb))
  · intro b hb
    rw [hit 3 b (hsub hb)]
    exact hm.deriv4_bound b (edgeNbhd_subset_edgeStrip (hsub hb))

/-- Lemma `SD_0` in the form of the task statement: there are `δ ∈ (0, 1/4]` and constants
`C₃, C₄` such that the explicit Blaschke comb potential satisfies `EdgePhaseData δ C₃ C₄`. -/
theorem edgePhaseData_blaschke_exists :
    ∃ δ ∈ Ioc (0 : ℝ) (1 / 4), ∃ C₃ C₄ : ℝ, EdgePhaseData δ C₃ C₄ edgePhi0Blaschke := by
  obtain ⟨C₃, C₄, h⟩ := edgePhaseData_blaschke
  exact ⟨1 / 8, ⟨by norm_num, by norm_num⟩, C₃, C₄, h _ (by norm_num) (by norm_num)⟩

/-- info: 'FormalResearch.ModularBootstrap.Upper.Saddle.edgePhaseData_blaschke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Saddle.edgePhaseData_blaschke

/-- info: 'FormalResearch.ModularBootstrap.Upper.Saddle.edgePhi0Blaschke_deriv_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Saddle.edgePhi0Blaschke_deriv_edge

/-- info: 'FormalResearch.ModularBootstrap.Upper.Saddle.edgePhi0Blaschke_re_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Saddle.edgePhi0Blaschke_re_edge

end FormalResearch.ModularBootstrap.Upper.Saddle
